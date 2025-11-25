// Copyright 2023 Nathan Sizemore <nathanrsizemore@gmail.com>
//
// This Source Code Form is subject to the terms of the
// Mozilla Public License, v. 2.0. If a copy of the MPL was not
// distributed with this file, You can obtain one at
// http://mozilla.org/MPL/2.0/.

use std::{
    ffi::{CStr, CString},
    io,
    marker::PhantomData,
};

use memmap2::{MmapMut, MmapOptions};
use rustix::{
    fd::{AsFd, AsRawFd, BorrowedFd, OwnedFd},
    fs::Mode,
    io::Errno,
    shm::OFlags,
};

#[derive(Debug)]
pub struct Shm {
    fd: OwnedFd,
    // this `name` MUST always be valid utf8 - we just keep it as a CString cause that's what we
    // need to interact with the libc apis
    name: CString,
}

// for some reason, at least on my setup, I'll sometimes get errno 17 from opening an shm (errno 17
// being `AlreadyExists`), but `last_os_error` will produce an error that just says "Success (error
// code 0)", meaning (I guess) that the error somehow didn't get recorded to errno or something?
// Moral of the story: convert directly with this fn instead of with `Error::last_os_error`
fn to_io_err(e: Errno) -> io::Error {
    io::Error::from_raw_os_error(e.raw_os_error())
}

impl Shm {
    /// Opens shared memory at `name`.
    ///
    /// # Errors
    ///
    /// This can error if the underlying `shm_open` syscall fails. This can happen due to a variety
    /// of reasons, such as lack of permission, the named shm already existing when you use EXCL
    /// oflag, and more. Consult `man 3 shm_open` for more details.
    ///
    /// # Panics
    ///
    /// This can panic if `name` contains a null byte
    pub fn open(name: &str, oflags: OFlags, mode: Mode) -> io::Result<Self> {
        let cstr = CString::new(name).unwrap();
        let fd = rustix::shm::open(&*cstr, oflags, mode).map_err(to_io_err)?;

        Ok(Self { fd, name: cstr })
    }

    /// Returns the size of the shared memory reported by `fstat`.
    ///
    /// # Errors
    ///
    /// Errors if the underlying `fstat` syscall fails for whatever reason
    pub fn size(&self) -> io::Result<usize> {
        rustix::fs::fstat(&self.fd)
            .map(|stat| stat.st_size as usize)
            .map_err(to_io_err)
    }

    /// Sets the size of the shared memory with `ftruncate`.
    ///
    /// # Errors
    ///
    /// Errors if the underlying `ftruncate` syscall fails for whatever reason
    pub fn set_size(&mut self, size: usize) -> io::Result<()> {
        rustix::fs::ftruncate(&self.fd, u64::try_from(size).unwrap_or(u64::MAX)).map_err(to_io_err)
    }

    pub fn name(&self) -> &str {
        let bytes = self.name.as_bytes();
        // SAFETY: We guarantee that `name` is always valid utf8. It is created from a `&str` and
        // never mutated.
        unsafe { std::str::from_utf8_unchecked(bytes) }
    }

    /// Try to create a [`memmap2::MmapMut`] by which we can read and write to this shared memory
    /// object. The provided `offset` may not be greater than or equal to the value returned by
    /// [`Self::size`] (if it is, this function will return an error).
    ///
    /// This function is generally only useful if one has already called [`Self::set_size`]. If one
    /// hasn't, this function will return a mapped area with a length of 0, so writing to and
    /// reading from it will either fail or do nothing.
    ///
    /// # Safety
    ///
    /// This is unsafe due to the fundamental nature of memory shared between processes. The
    /// documentation for [`memmap2::MmapOptions::map_mut`] can share more details, but doesn't
    /// paint the whole picture. We aren't using this to map a file, but rather just a chunk of
    /// memory that can be shared between processes. Because this can be shared between processes
    /// and the changes from one process are immediately visible from a different process, this
    /// very easily allows one to run into use-after-free issues if they are not safe.
    ///
    /// There is no way to prevent this sort of intra-process borrow-dependency in safe rust, so
    /// one must simply be safe when using this. However, we do prevent one from easily
    /// accidentally making two mmaps from the same [`Shm`] by modeling the fact that the map
    /// borrows from the Shm in the type system with the [`BorrowedMap`] type.
    ///
    /// # Errors
    ///
    /// This can fail if:
    /// 1. We cannot retrieve the shm's size with fstat
    /// 2. The provided offset is greater than the size of the shm
    /// 3. The underlying `mmap` call fails
    pub unsafe fn map(&mut self, offset: usize) -> io::Result<BorrowedMap<'_>> {
        let size = self.size()?;

        if offset >= size {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "The provided offset must not be greater than self.size()",
            ));
        }

        let mut opts = MmapOptions::new();
        // 128-bit computers don't exist so this conversion won't lose any precision
        opts.offset(offset as u64);
        opts.len(size - offset);

        // SAFETY: Upheld by caller - see note above fn
        let map = unsafe { opts.map_mut(self.fd.as_raw_fd()) }?;

        Ok(BorrowedMap {
            map,
            _borrowed: PhantomData,
        })
    }

    /// Get the fd that represents the shm to the system
    pub fn as_fd(&self) -> BorrowedFd<'_> {
        self.fd.as_fd()
    }

    /// Unlink the shm; analogous to `shm_unlink`.
    ///
    /// # Errors
    ///
    /// This will return an error if the underlying `shm_unlink` call fails.
    pub fn unlink(self) -> io::Result<()> {
        rustix::shm::unlink(&*self.name).map_err(to_io_err)
    }

    /// Get a [`CStr`] representation of the name
    pub fn name_ptr(&self) -> &CStr {
        &self.name
    }
}

#[derive(Debug)]
pub struct UnlinkOnDrop {
    pub shm: Shm,
}

impl Drop for UnlinkOnDrop {
    fn drop(&mut self) {
        _ = rustix::shm::unlink(self.shm.name_ptr())
    }
}

/// A wrapper around an [`memmap2::MmapMut`] to prevent one from accidentally calling [`Shm::map`]
/// twice on the same Shm (which could very easily introduce memory unsoundness). To use the
/// contained map, just call [`BorrowedMap::map`]. One cannot safely move the map out of this
/// struct, as that would easily allow them to break the lifetime-dependent relationship between
/// this map and the [`Shm`] it's mapped onto.
///
/// To be clear: This risk of memory unsafety does not come from an actual borrowing of memory
/// between the [`Shm`] and the [`MmapMut`] - a [`MmapMut`] can be dropped before or after the
/// [`Shm`] which it is mapped from and nothing bad will happen. The issue comes when two
/// [`MmapMut`]s are mapped from the same [`Shm`] - this could allow e.g. something to borrow from
/// one [`MmapMut`], then the other [`MmapMut`] could be shrunk, thus invalidating the references
/// from the first map.
#[derive(Debug)]
pub struct BorrowedMap<'shm> {
    map: MmapMut,
    _borrowed: PhantomData<&'shm ()>,
}

impl BorrowedMap<'_> {
    pub fn map(&mut self) -> &mut MmapMut {
        &mut self.map
    }

    /// Take the inner [`MmapMut`] out of this wrapper.
    ///
    /// # Safety
    ///
    /// This can can unsoundness if another Mmap is created from the [`Shm`] that this was derived
    /// from. Read the struct-level documentation for more details.
    pub unsafe fn into_map(self) -> MmapMut {
        self.map
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn offset_larger_than_map_fails() {
        let mut shm = Shm::open(
            "/__psx_shm_oltmp_ahafeufhdmdhkeysmash",
            OFlags::RDWR | OFlags::CREATE,
            Mode::RUSR | Mode::WUSR,
        )
        .unwrap();
        shm.set_size(20).unwrap();
        // SAFETY: We aren't even trying to open anything here - we expect it to fail. So there's
        // no potential for memory unsafety 'cause no memory should ever be mapped
        let err = unsafe { shm.map(21) }.unwrap_err();

        assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput);
    }
}
