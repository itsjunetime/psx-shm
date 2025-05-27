// Copyright 2023 Nathan Sizemore <nathanrsizemore@gmail.com>
//
// This Source Code Form is subject to the terms of the
// Mozilla Public License, v. 2.0. If a copy of the MPL was not
// distributed with this file, You can obtain one at
// http://mozilla.org/MPL/2.0/.

use std::{ffi::CString, io, marker::PhantomData, mem, os::fd::RawFd};

use bitflags::bitflags;
use memmap2::{MmapMut, MmapOptions};

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct OpenOptions: libc::c_int {
        /// Create if not exists.
        const CREATE = libc::O_CREAT;
        /// Open for read.
        const READ = libc::O_RDONLY;
        /// Open for write.
        const WRITE = libc::O_WRONLY;
        /// Open for read+write. Note that this is not the same value as `OpenOptions::READ |
        /// OpenOptions::Write`.
        const READWRITE = libc::O_RDWR;
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct OpenMode: libc::mode_t {
        /// User read.
        const R_USR = libc::S_IRUSR;
        /// User write.
        const W_USR = libc::S_IWUSR;
        /// Group read.
        const R_GRP = libc::S_IRGRP;
        /// Group write.
        const W_GRP = libc::S_IWGRP;
        /// Other read.
        const R_OTH = libc::S_IROTH;
        /// Other write.
        const W_OTH = libc::S_IWOTH;
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Protection: libc::c_int {
        /// Pages may be executed.
        const EXEC = libc::PROT_EXEC;
        /// Pages may be read.
        const READ = libc::PROT_READ;
        /// Pages may be written.
        const WRITE = libc::PROT_WRITE;
        /// Pages may not be accessed.
        const NONE = libc::PROT_NONE;
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Mapping: libc::c_int {
        /// Share this mapping.  Updates to the mapping are visible to
        /// other processes mapping the same region, and (in the case
        /// of file-backed mappings) are carried through to the
        /// underlying file.
        const SHARED = libc::MAP_SHARED;
        /// Create a private copy-on-write mapping.  Updates to the
        /// mapping are not visible to other processes mapping the
        /// same file, and are not carried through to the underlying
        /// file.
        const PRIVATE = libc::MAP_PRIVATE;
    }
}

#[derive(Debug)]
pub struct Shm {
    fd: RawFd,
    // this `name` MUST always be valid utf8 - we just keep it as a CString cause that's what we
    // need to interact with the libc apis
    name: CString,
}

impl Shm {
    /// Opens shared memory at `name`.
    pub fn open(name: &str, oflags: OpenOptions, mode: OpenMode) -> io::Result<Self> {
        let cstr = CString::new(name).unwrap();
        #[cfg(target_os = "macos")]
        let r =
            unsafe { libc::shm_open(cstr.as_ptr(), oflags.bits(), mode.bits() as libc::c_uint) };
        #[cfg(target_os = "linux")]
        let fd = unsafe { libc::shm_open(cstr.as_ptr(), oflags.bits(), mode.bits()) };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }

        Ok(Self { fd, name: cstr })
    }

    /// Returns the size of the shared memory reported by `fstat`.
    pub fn size(&self) -> io::Result<usize> {
        let mut stat: libc::stat = unsafe { mem::zeroed() };
        let r = unsafe { libc::fstat(self.fd, &mut stat) };
        if r != 0 {
            return Err(io::Error::last_os_error());
        }

        Ok(stat.st_size as usize)
    }

    /// Sets the size of the shared memory with `ftruncate`.
    pub fn set_size(&mut self, size: usize) -> io::Result<()> {
        let r = unsafe { libc::ftruncate(self.fd, size as libc::off_t) };
        if r == 0 {
            return Ok(());
        }

        Err(io::Error::last_os_error())
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
        let map = unsafe { opts.map_mut(self.fd) }?;

        Ok(BorrowedMap { map, _borrowed: PhantomData })
    }

    pub fn unlink(self) -> io::Result<()> {
        match unsafe { libc::shm_unlink(self.name.as_ptr()) } {
            0 => Ok(()),
            _ => Err(io::Error::last_os_error()),
        }
    }
}

/// A wrapper around an [`memmap2::MmapMut`] to prevent one from accidentally calling [`Shm::map`]
/// twice on the same Shm (which could very easily introduce memory unsoundness). To use the
/// contained map, just call [`BorrowedMap::map`]. One cannot move the map out of this struct, as
/// that would easily allow them to break the lifetime-dependent relationship between this map and
/// the [`Shm`] it's mapped onto
#[derive(Debug)]
pub struct BorrowedMap<'shm> {
    map: MmapMut,
    _borrowed: PhantomData<&'shm ()>
}

impl BorrowedMap<'_> {
    pub fn map(&mut self) -> &mut MmapMut {
        &mut self.map
    }
}

impl Drop for Shm {
    fn drop(&mut self) {
        unsafe { libc::close(self.fd) };
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn offset_larger_than_map_fails() {
        let mut shm = Shm::open(
            "__psx_shm_oltmp_ahafeufhdmdhkeysmash",
            OpenOptions::READWRITE | OpenOptions::CREATE,
            OpenMode::R_USR | OpenMode::W_USR,
        )
        .unwrap();
        shm.set_size(20).unwrap();
        // SAFETY: We aren't even trying to open anything here - we expect it to fail. So there's
        // no potential for memory unsafety 'cause no memory should ever be mapped
        let err = unsafe { shm.map(21) }.unwrap_err();

        assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput);
    }
}
