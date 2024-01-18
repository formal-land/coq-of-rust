Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.vec.
Require CoqOfRust.core.result.
Require CoqOfRust.std.fs.
Require CoqOfRust.std.io.
Require CoqOfRust.std.process.


(* ********MODULES******** *)
(*
[x] fd
[x] linux
[x] raw
[x] unix
[x] wasi
[ ] windows
*)

Module fd.
  (* ********STRUCTS******** *)
  (*
  [x] BorrowedFd
  [x] OwnedFd
  *)

  (* pub struct BorrowedFd<'fd> { /* private fields */ } *)
  Module BorrowedFd.
    Parameter t : Set.
  End BorrowedFd.
  
  (* pub struct OwnedFd { /* private fields */ } *)
  Module OwnedFd.
    Parameter t : Set.
  End OwnedFd.

  (* ********TYPE DEFINITIONS******** *)
  (*
  [ ] RawFd
  *)

  (* pub type RawFd = c_int; *)
  Ltac RawFd := exact i32.t.

  (* ********TRAITS******** *)
  (*
  [x] AsFd
  [x] AsRawFd
  [x] FromRawFd
  [x] IntoRawFd
  *)

  (* 
  pub trait AsFd {
      // Required method
      fn as_fd(&self) -> BorrowedFd<'_>;
  }
  *)
  Module AsFd.
    Class Trait (Self : Set) : Set := {
      as_fd : ref Self -> M BorrowedFd.t;
    }.
  End AsFd.

  (* 
  pub trait AsRawFd {
      // Required method
      fn as_raw_fd(&self) -> RawFd;
  }
  *)
  Module AsRawFd.
    Class Trait (Self : Set) : Set := {
      as_raw_fd : ref Self -> M ltac:(RawFd);
    }.
  End AsRawFd.

  (* 
  pub trait FromRawFd {
      // Required method
      unsafe fn from_raw_fd(fd: RawFd) -> Self;
  }
  *)
  Module FromRawFd.
    Class Trait (Self : Set) : Set := {
      from_raw_fd : ltac:(RawFd) -> M Self;
    }.
  End FromRawFd.

  (* 
  pub trait IntoRawFd {
      // Required method
      fn into_raw_fd(self) -> RawFd;
  }
  *)
  Module IntoRawFd.
    Class Trait (Self : Set) : Set := {
      into_raw_fd : Self -> M ltac:(RawFd);
    }.
  End IntoRawFd.
End fd.

Module raw.
  (* ********TYPE DEFINITIONS******** *)
  (*
  [ ] c_char
  [ ] c_double
  [ ] c_float
  [ ] c_int
  [ ] c_long
  [ ] c_longlong
  [ ] c_schar
  [ ] c_short
  [ ] c_uchar
  [ ] c_uint
  [ ] c_ulong
  [ ] c_ulonglong
  [ ] c_ushort
  [ ] c_void
  *)
  
End raw.

Module unix.
  (* ********MODULES******** *)
  (*
  [x] ucred
  [x] ffi
  [x] fs
  [x] io
  [ ] net
  [x] prelude
  [ ] process
  [x] raw(Deprecated)
  [ ] thread
  *)

  Module ucred.
    Module impl_linux.
      (* ********FUNCTIONS******** *)
      (*
      [ ] peer_cred
      *)
    End impl_linux.
  End ucred.
  
  Module ffi.
    (* ********TRAITS******** *)
    (*
    [x] OsStrExt
    [x] OsStringExt
    *)

    (* 
    pub trait OsStrExt: Sealed {
        // Required methods
        fn from_bytes(slice: &[u8]) -> &Self;
        fn as_bytes(&self) -> &[u8];
    }
    *)
    Module OsStrExt.
      Class Trait (Self : Set) : Set := {
        from_bytes : ref (slice u8.t) -> M (ref Self);
        as_bytes : ref Self -> M (ref (slice u8.t));
      }.
    End OsStrExt.

    (* 
    pub trait OsStringExt: Sealed {
        // Required methods
        fn from_vec(vec: Vec<u8>) -> Self;
        fn into_vec(self) -> Vec<u8>;
    }
    *)
    Module OsStringExt.
      Class Trait (Self : Set) : Set := {
        from_vec : vec.Vec u8.t vec.Vec.Default.A -> M Self;
        into_vec : Self -> M (vec.Vec u8.t vec.Vec.Default.A);
      }.
    End OsStringExt.

  End ffi.
  
  Module fs.
    (* ********TRAITS******** *)
    (*
    [x] DirEntryExt2
    [x] DirBuilderExt
    [x] DirEntryExt
    [x] FileExt
    [x] FileTypeExt
    [x] MetadataExt
    [x] OpenOptionsExt
    [x] PermissionsExt
    *)

    (* TODO: Add dependency *)
    (* 
    pub trait DirEntryExt2: Sealed {
        // Required method
        fn file_name_ref(&self) -> &OsStr;
    }
    *)
    Module DirEntryExt2.
      Class Trait (Self : Set) : Set := {
        file_name_ref : ref Self -> ref ffi.os_str.OsStr.t;
      }.
    End DirEntryExt2.

    (* 
    pub trait DirBuilderExt {
        // Required method
        fn mode(&mut self, mode: u32) -> &mut Self;
    }
    *)
    Module DirBuilderExt.
      Class Trait (Self : Set) : Set := {
        mode : mut_ref Self -> u32.t -> M (mut_ref Self);
      }.
    End DirBuilderExt.
    
    
    (* 
    pub trait DirEntryExt {
        // Required method
        fn ino(&self) -> u64;
    }
    *)
    Module DirEntryExt.
      Class Trait (Self : Set) : Set := {
        ino : ref Self -> M u64.t;
      }.
    End DirEntryExt.

    (* 
    pub trait FileExt {
        // Required methods
        fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize>;
        fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize>;

        // Provided methods
        fn read_vectored_at(
            &self,
            bufs: &mut [IoSliceMut<'_>],
            offset: u64
        ) -> Result<usize> { ... }
        fn read_exact_at(&self, buf: &mut [u8], offset: u64) -> Result<()> { ... }
        fn write_vectored_at(
            &self,
            bufs: &[IoSlice<'_>],
            offset: u64
        ) -> Result<usize> { ... }
        fn write_all_at(&self, buf: &[u8], offset: u64) -> Result<()> { ... }
    }
    *)
    Module FileExt.
      Class Trait (Self : Set) : Set := {
        read_at :
          ref Self -> mut_ref (slice u8.t) -> u64.t -> ltac:(io.error.Result usize.t);
        write_at :
          ref Self -> ref (slice u8.t) -> u64.t -> ltac:(io.error.Result usize.t);
        read_vectored_at :
          ref Self -> mut_ref (slice io.IoSliceMut.t) -> u64.t -> ltac:(io.error.Result usize.t);
        read_exact_at :
          ref Self -> mut_ref u8.t -> u64.t -> ltac:(io.error.Result unit);
        write_vectored_at :
          ref Self -> ref (slice io.IoSlice.t) -> u64.t -> ltac:(io.error.Result usize.t);
        write_all_at :
          ref Self -> ref (slice u8.t) -> u64.t -> ltac:(io.error.Result unit);
      }.
    End FileExt.

    (* 
    pub trait FileTypeExt {
        // Required methods
        fn is_block_device(&self) -> bool;
        fn is_char_device(&self) -> bool;
        fn is_fifo(&self) -> bool;
        fn is_socket(&self) -> bool;
    }
    *)
    Module FileTypeExt.
      Class Trait (Self : Set) : Set := {
        is_block_device : ref Self -> bool;
        is_char_device : ref Self -> bool;
        is_fifo : ref Self -> bool;
        is_socket : ref Self -> bool;
      }.
    End FileTypeExt.
    
    (* 
    pub trait MetadataExt {
        // Required methods
        fn dev(&self) -> u64;
        fn ino(&self) -> u64;
        fn mode(&self) -> u32;
        fn nlink(&self) -> u64;
        fn uid(&self) -> u32;
        fn gid(&self) -> u32;
        fn rdev(&self) -> u64;
        fn size(&self) -> u64;
        fn atime(&self) -> i64;
        fn atime_nsec(&self) -> i64;
        fn mtime(&self) -> i64;
        fn mtime_nsec(&self) -> i64;
        fn ctime(&self) -> i64;
        fn ctime_nsec(&self) -> i64;
        fn blksize(&self) -> u64;
        fn blocks(&self) -> u64;
    }
    *)
    Module MetadataExt.
      Class Trait (Self : Set) : Set := {
        dev : ref Self -> M u64.t;
        ino : ref Self -> M u64.t;
        mode : ref Self -> M u32.t;
        nlink : ref Self -> M u64.t;
        uid : ref Self -> M u32.t;
        gid : ref Self -> M u32.t;
        rdev : ref Self -> M u64.t;
        size : ref Self -> M u64.t;
        atime : ref Self -> M i64.t;
        atime_nsec : ref Self -> M i64.t;
        mtime : ref Self -> M i64.t;
        mtime_nsec : ref Self -> M i64.t;
        ctime : ref Self -> M i64.t;
        ctime_nsec : ref Self -> M i64.t;
        blksize : ref Self -> M u64.t;
        blocks : ref Self -> M u64.t;
      }.
    End MetadataExt.

    (* 
    pub trait OpenOptionsExt {
        // Required methods
        fn mode(&mut self, mode: u32) -> &mut Self;
        fn custom_flags(&mut self, flags: i32) -> &mut Self;
    }
    *)
    Module OpenOptionsExt.
      Class Trait (Self : Set) : Set := {
        mode : mut_ref Self -> u32.t -> M (mut_ref Self);
        custom_flags : mut_ref Self -> i32.t -> M (mut_ref Self);
      }.
    End OpenOptionsExt.

    (* 
    pub trait PermissionsExt {
        // Required methods
        fn mode(&self) -> u32;
        fn set_mode(&mut self, mode: u32);
        fn from_mode(mode: u32) -> Self;
    }
    *)
    Module PermissionsExt.
      Class Trait (Self : Set) : Set := {
        mode : ref Self -> M u32.t;
        set_mode : mut_ref Self -> u32.t -> M unit;
        from_mode : u32.t -> M Self;
      }.
    End PermissionsExt.

    (* ********FUNCTIONS******** *)
    (*
    [ ] chown
    [ ] fchown
    [ ] lchown
    [ ] chroot
    [x] symlink
    *)

    (*
    pub fn symlink<P: AsRef<Path>, Q: AsRef<Path>>(
        original: P,
        link: Q
    ) -> Result<()>
    *)
    Parameter symlink :
      forall {P Q : Set},
      P -> Q -> M ltac:(io.error.Result unit).
  End fs.
  
  Module io.
    (* ********RE-EXPORTS******** *)
    (*
    [ ] crate::os::fd::*
    *)
    
  End io.
  
  Module net.
    (* ********RE-EXPORTS******** *)
    (*
    [ ] ucred::UCred
    *)

    (* ********STRUCTS******** *)
    (*
    [x] Messages
    [x] ScmCredentials
    [x] ScmRights
    [x] SocketAncillary
    [x] SocketCred
    [x] Incoming
    [x] SocketAddr
    [x] UnixDatagram
    [x] UnixListener
    [x] UnixStream
    *)

    (* pub struct Messages<'a> { /* private fields */ } *)
    Module Messages.
      Parameter t : Set.
    End Messages.

    (* pub struct ScmCredentials<'a>(_); *)
    Module ScmCredentials.
      Parameter t : Set.
    End ScmCredentials.
    
    (* pub struct ScmRights<'a>(_); *)
    Module ScmRights.
      Parameter t : Set.
    End ScmRights.
    
    (* pub struct SocketAncillary<'a> { /* private fields */ } *)
    Module SocketAncillary.
      Parameter t : Set.
    End SocketAncillary.
    
    (* pub struct SocketCred(_); *)
    Module SocketCred.
      Parameter t : Set.
    End SocketCred.
    
    (* pub struct Incoming<'a> { /* private fields */ } *)
    Module Incoming.
      Parameter t : Set.
    End Incoming.
    
    (* pub struct SocketAddr { /* private fields */ } *)
    Module SocketAddr.
      Parameter t : Set.
    End SocketAddr.
    
    (* pub struct UnixDatagram(_); *)
    Module UnixDatagram.
      Parameter t : Set.
    End UnixDatagram.
    
    (* pub struct UnixListener(_); *)
    Module UnixListener.
      Parameter t : Set.
    End UnixListener.
    
    (* pub struct UnixStream(_); *)
    Module UnixStream.
      Parameter t : Set.
    End UnixStream.
    
    (* ********ENUMS******** *)
    (*
    [x] AncillaryData
    [?] AncillaryError
    *)
    
    (* 
    pub enum AncillaryData<'a> {
        ScmRights(ScmRights<'a>),
        ScmCredentials(ScmCredentials<'a>),
    }
    *)
    Module AncillaryData.
      Inductive t : Set := 
      | ScmRights
      | ScmCredentials
      .
    End AncillaryData.

    (* BUGGED: unusual enum structure *)
    (* 
    #[non_exhaustive]
    pub enum AncillaryError {
        Unknown {
            cmsg_level: i32,
            cmsg_type: i32,
        },
    }
    *)
    Module AncillaryError.
      Inductive t : Set := .
    End AncillaryError.
  End net.
  
  Module prelude.
    (* ********RE-EXPORTS******** *)
    (*
    [ ] super::ffi::OsStrExt
    [ ] super::ffi::OsStringExt
    [ ] super::fs::DirEntryExt
    [ ] super::fs::FileExt
    [ ] super::fs::FileTypeExt
    [ ] super::fs::MetadataExt
    [ ] super::fs::OpenOptionsExt
    [ ] super::fs::PermissionsExt
    [ ] super::io::AsFd
    [ ] super::io::AsRawFd
    [ ] super::io::BorrowedFd
    [ ] super::io::FromRawFd
    [ ] super::io::IntoRawFd
    [ ] super::io::OwnedFd
    [ ] super::io::RawFd
    [ ] super::process::CommandExt
    [ ] super::process::ExitStatusExt
    [ ] super::thread::JoinHandleExt
    *)
  End prelude.
  
  Module process.
    (* ********TRAITS******** *)
    (*
    [?] CommandExt
    [x] ExitStatusExt
    *)

    (* BUGGED: monad function dependency *)
    (* 
    pub trait CommandExt: Sealed {
        // Required methods
        fn uid(&mut self, id: u32) -> &mut Command;
        fn gid(&mut self, id: u32) -> &mut Command;
        fn groups(&mut self, groups: &[u32]) -> &mut Command;
        unsafe fn pre_exec<F>(&mut self, f: F) -> &mut Command
          where F: FnMut() -> Result<()> + Send + Sync + 'static;
        fn exec(&mut self) -> Error;
        fn arg0<S>(&mut self, arg: S) -> &mut Command
          where S: AsRef<OsStr>;
        fn process_group(&mut self, pgroup: i32) -> &mut Command;

        // Provided method
        fn before_exec<F>(&mut self, f: F) -> &mut Command
          where F: FnMut() -> Result<()> + Send + Sync + 'static { ... }
    }
    *)
    Module CommandExt.
      Class Trait (Self : Set) : Set := {
        uid : mut_ref Self -> u32.t -> mut_ref process.Command.t;
        gid : mut_ref Self -> u32.t -> mut_ref process.Command.t;
        groups : mut_ref Self -> ref (slice u32.t) -> mut_ref process.Command.t;
        pre_exec (F : Set) :
          mut_ref Self -> F -> mut_ref process.Command.t;
        exec : mut_ref Self -> M io.error.Error.t;
        arg0 {S : Set} : mut_ref Self -> S -> mut_ref process.Command.t;
        process_group : mut_ref Self -> i32.t -> mut_ref process.Command.t;
        before_exec {F : Set} :
          mut_ref Self -> F -> M (mut_ref process.Command.t);
      }.
    End CommandExt.

    (* 
    pub trait ExitStatusExt: Sealed {
        // Required methods
        fn from_raw(raw: i32) -> Self;
        fn signal(&self) -> Option<i32>;
        fn core_dumped(&self) -> bool;
        fn stopped_signal(&self) -> Option<i32>;
        fn continued(&self) -> bool;
        fn into_raw(self) -> i32;
    }
    *)
    Module ExitStatusExt.
      Class Trait (Self : Set) : Set := {
        from_raw : i32.t -> Self;
        signal : ref Self -> option.Option.t i32.t;
        core_dumped : ref Self -> bool;
        stopped_signal : ref Self -> option.Option.t i32.t;
        continued : ref Self -> bool;
        into_raw : Self -> i32.t;
      }.
    End ExitStatusExt.
    
    

    (* ********FUNCTIONS******** *)
    (*
    [ ] parent_id
    *)
    
  End process.
  
  Module thread.

    (* ********TRAITS******** *)
    (*
    [?] JoinHandleExt
    *)

    (* BUGGED: need type definition *)
    Parameter RawPthread : Set.
    (* 
    pub trait JoinHandleExt {
        // Required methods
        fn as_pthread_t(&self) -> RawPthread;
        fn into_pthread_t(self) -> RawPthread;
    }
    *)
    Module JoinHandleExt.
      Class Trait (Self : Set) : Set := {
        as_pthread_t : ref Self -> RawPthread;
        into_pthread_t : Self -> RawPthread;
      }.
    End JoinHandleExt.
    
    (* ********TYPE DEFINITIONS******** *)
    (*
    [ ] RawPthread
    *)
    
  End thread.
End unix.

Module linux.
  (* ********MODULES******** *)
  (*
  [x] process
  [x] fs
  [x] net
  [x] raw(Deprecated)
  *)
  Module process.
    (* ********STRUCTS******** *)
    (*
    [x] PidFd
    *)

    (* pub struct PidFd { /* private fields */ } *)
    Module PidFd.
      Parameter t : Set.
    End PidFd.
    
    (* ********TRAITS******** *)
    (*
    [x] ChildExt
    [x] CommandExt
    *)

    (* 
    pub trait ChildExt: Sealed {
        // Required methods
        fn pidfd(&self) -> Result<&PidFd>;
        fn take_pidfd(&mut self) -> Result<PidFd>;
    }
    *)
    Module ChildExt.
      Class Trait (Self : Set) : Set := {
        pidfd : ref Self -> M ltac:(io.error.Result (ref PidFd.t));
        take_pidfd : mut_ref Self -> M ltac:(io.error.Result PidFd.t);
      }.
    End ChildExt.

    (* 
    pub trait CommandExt: Sealed {
        // Required method
        fn create_pidfd(&mut self, val: bool) -> &mut Command;
    }
    *)
    Module CommandExt.
      Class Trait (Self : Set) : Set := {
        create_pidfd : mut_ref Self -> bool -> M (mut_ref process.Command.t);
      }.
    End CommandExt.

  End process.

  Module raw.
    (*
    pub struct stat {
        ...
    }
    *)
    Module stat.
      Parameter t : Set.
    End stat.
  End raw.

  Module fs.
    (* ********TRAITS******** *)
    (*
    [x] MetadataExt
    *)
    (* 
    pub trait MetadataExt {
        // Required methods
        fn as_raw_stat(&self) -> &stat;
        fn st_dev(&self) -> u64;
        fn st_ino(&self) -> u64;
        fn st_mode(&self) -> u32;
        fn st_nlink(&self) -> u64;
        fn st_uid(&self) -> u32;
        fn st_gid(&self) -> u32;
        fn st_rdev(&self) -> u64;
        fn st_size(&self) -> u64;
        fn st_atime(&self) -> i64;
        fn st_atime_nsec(&self) -> i64;
        fn st_mtime(&self) -> i64;
        fn st_mtime_nsec(&self) -> i64;
        fn st_ctime(&self) -> i64;
        fn st_ctime_nsec(&self) -> i64;
        fn st_blksize(&self) -> u64;
        fn st_blocks(&self) -> u64;
    }
    *)
    Module MetadataExt.
      Class Trait (Self : Set) : Set := {
        as_raw_stat : ref Self -> M (ref raw.stat.t);
        st_dev : ref Self -> M u64.t;
        st_ino : ref Self -> M u64.t;
        st_mode : ref Self -> M u32.t;
        st_nlink : ref Self -> M u64.t;
        st_uid : ref Self -> M u32.t;
        st_gid : ref Self -> M u32.t;
        st_rdev : ref Self -> M u64.t;
        st_size : ref Self -> M u64.t;
        st_atime : ref Self -> M i64.t;
        st_atime_nsec : ref Self -> M i64.t;
        st_mtime : ref Self -> M i64.t;
        st_mtime_nsec : ref Self -> M i64.t;
        st_ctime : ref Self -> M i64.t;
        st_ctime_nsec : ref Self -> M i64.t;
        st_blksize : ref Self -> M u64.t;
        st_blocks : ref Self -> M u64.t;
      }.
    End MetadataExt.

  End fs.
  
  Module net.
    (* ********TRAITS******** *)
    (*
    [x] TcpStreamExt
    [x] SocketAddrExt
    *)

    (* 
    pub trait TcpStreamExt: Sealed {
        // Required methods
        fn set_quickack(&self, quickack: bool) -> Result<()>;
        fn quickack(&self) -> Result<bool>;
    }
    *)
    Module TcpStreamExt.
      Class Trait (Self : Set) : Set := {
        set_quickack : ref Self -> bool -> M ltac:(io.error.Result unit);
        quickack : ref Self -> M ltac:(io.error.Result bool);
      }.
    End TcpStreamExt.
    
    (* 
    pub trait SocketAddrExt: Sealed {
        // Required methods
        fn from_abstract_name<N>(name: N) -> Result<SocketAddr>
          where N: AsRef<[u8]>;
        fn as_abstract_name(&self) -> Option<&[u8]>;
    }
    *)
    Module SocketAddrExt.
      Class Trait (Self : Set) : Set := {
        from_abstract_name {N : Set} : N -> M ltac:(io.error.Result unix.net.SocketAddr.t);
        as_abstract_name : ref Self -> M (option.Option.t (ref (slice u8.t)));
      }.
    End SocketAddrExt.
  End net.
End linux.

Module wasi.
  (* ********MODULES******** *)
  (*
  [x] fs
  [x] net
  [x] ffi
  [x] io
  [x] prelude
  *)
  Module fs.
    (* ********TRAITS******** *)
    (*
    [x] DirEntryExt
    [x] FileExt
    [x] FileTypeExt
    [x] MetadataExt
    [x] OpenOptionsExt
    *)

    (* 
    pub trait DirEntryExt {
        // Required method
        fn ino(&self) -> u64;
    }
    *)
    Module DirEntryExt.
      Class Trait (Self : Set) : Set := {
        ino : ref Self -> M u64.t;
      }.
    End DirEntryExt.
    

    (* 
    pub trait FileExt {
      //...
    }
    *)
    Module FileExt.
      Class Trait (Self : Set) : Set := {
        (* 
        fn read_vectored_at(
            &self,
            bufs: &mut [IoSliceMut<'_>],
            offset: u64
        ) -> Result<usize>;
        *)
        read_vectored_at : ref Self -> mut_ref (slice io.IoSliceMut.t) -> u64.t -> M ltac:(io.error.Result usize.t);

        (* 
        fn write_vectored_at(
            &self,
            bufs: &[IoSlice<'_>],
            offset: u64
        ) -> Result<usize>;
        *)
        write_vectored_at : ref Self -> mut_ref (slice io.IoSliceMut.t) -> u64.t -> M ltac:(io.error.Result usize.t);

        (* 
        fn tell(&self) -> Result<u64>;
        fn fdstat_set_flags(&self, flags: u16) -> Result<()>;
        fn fdstat_set_rights(&self, rights: u64, inheriting: u64) -> Result<()>;
        fn advise(&self, offset: u64, len: u64, advice: u8) -> Result<()>;
        fn allocate(&self, offset: u64, len: u64) -> Result<()>;
        fn create_directory<P: AsRef<Path>>(&self, dir: P) -> Result<()>;
        fn read_link<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf>;
        *)
        tell : ref Self -> M ltac:(io.error.Result u64.t);
        fdstat_set_flags : ref Self -> u16.t -> M ltac:(io.error.Result unit);
        fdstat_set_rights : ref Self -> u64.t -> u64.t -> M ltac:(io.error.Result unit);
        advise : ref Self -> u64.t -> u64.t -> u8.t -> M ltac:(io.error.Result unit);
        allocate : ref Self -> u64.t -> u64.t -> M ltac:(io.error.Result unit);
        create_directory {P : Set} : ref Self -> P -> M ltac:(io.error.Result unit);
        read_link {P : Set} : ref Self -> P -> M ltac:(io.error.Result path.PathBuf.t);

      (* 
      fn metadata_at<P: AsRef<Path>>(
          &self,
          lookup_flags: u32,
          path: P
      ) -> Result<Metadata>;
      *)
      metadata_at {P : Set} : ref Self -> u32.t -> P -> M ltac:(io.error.Result fs.Metadata.t);

      (* 
      fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()>;
      fn remove_directory<P: AsRef<Path>>(&self, path: P) -> Result<()>;
      *)
      remove_file {P : Set} : ref Self -> P -> M ltac:(io.error.Result unit);
      remove_directory {P : Set} : ref Self -> P -> M ltac:(io.error.Result unit);

      (* 
      fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize> { ... }
      fn read_exact_at(&self, buf: &mut [u8], offset: u64) -> Result<()> { ... }
      fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize> { ... }
      fn write_all_at(&self, buf: &[u8], offset: u64) -> Result<()> { ... }
      *)
      read_at : ref Self -> mut_ref (slice u8.t) -> u64.t -> M ltac:(io.error.Result usize.t);
      read_exact_at : ref Self -> mut_ref (slice u8.t) -> u64.t -> M ltac:(io.error.Result unit);
      write_at : ref Self -> ref (slice u8.t) -> u64.t -> M ltac:(io.error.Result usize.t);
      write_all_at : ref Self -> ref (slice u8.t) -> u64.t -> M ltac:(io.error.Result unit);
    }.
    End FileExt.
    

    (* 
    pub trait FileTypeExt {
        // Required methods
        fn is_block_device(&self) -> bool;
        fn is_char_device(&self) -> bool;
        fn is_socket_dgram(&self) -> bool;
        fn is_socket_stream(&self) -> bool;

        // Provided method
        fn is_socket(&self) -> bool { ... }
    }
    *)
    Module FileTypeExt.
      Class Trait (Self : Set) : Set := {
        is_block_device : ref Self -> M bool;
        is_char_device : ref Self -> M bool;
        is_socket_dgram : ref Self -> M bool;
        is_socket_stream : ref Self -> M bool;
        is_socket : ref Self -> M bool;
      }.
    End FileTypeExt.
    

    (* 
    pub trait MetadataExt {
        // Required methods
        fn dev(&self) -> u64;
        fn ino(&self) -> u64;
        fn nlink(&self) -> u64;
        fn size(&self) -> u64;
        fn atim(&self) -> u64;
        fn mtim(&self) -> u64;
        fn ctim(&self) -> u64;
    }
    *)
    Module MetadataExt.
      Class Trait (Self : Set) : Set := {
        dev: ref Self -> M u64.t;
        ino: ref Self -> M u64.t;
        nlink: ref Self -> M u64.t;
        size: ref Self -> M u64.t;
        atim: ref Self -> M u64.t;
        mtim: ref Self -> M u64.t;
        ctim: ref Self -> M u64.t;
      }.
    End MetadataExt.

    (* 
    pub trait OpenOptionsExt {
        // Required methods
        fn lookup_flags(&mut self, flags: u32) -> &mut Self;
        fn directory(&mut self, dir: bool) -> &mut Self;
        fn dsync(&mut self, dsync: bool) -> &mut Self;
        fn nonblock(&mut self, nonblock: bool) -> &mut Self;
        fn rsync(&mut self, rsync: bool) -> &mut Self;
        fn sync(&mut self, sync: bool) -> &mut Self;
        fn fs_rights_base(&mut self, rights: u64) -> &mut Self;
        fn fs_rights_inheriting(&mut self, rights: u64) -> &mut Self;
        fn open_at<P: AsRef<Path>>(&self, file: &File, path: P) -> Result<File>;
    }
    *)
    Module OpenOptionsExt.
      Class Trait (Self : Set) : Set := {
        lookup_flags : mut_ref Self -> u32.t -> M (mut_ref Self);
        directory : mut_ref Self -> bool -> M (mut_ref Self);
        dsync : mut_ref Self -> bool -> M (mut_ref Self);
        nonblock : mut_ref Self -> bool -> M (mut_ref Self);
        rsync : mut_ref Self -> bool -> M (mut_ref Self);
        sync : mut_ref Self -> bool -> M (mut_ref Self);
        fs_rights_base : mut_ref Self -> u64.t -> M (mut_ref Self);
        fs_rights_inheriting : mut_ref Self -> u64.t -> M (mut_ref Self);
        open_at {P : Set} : mut_ref Self -> ref fs.File.t -> P -> M ltac:(io.error.Result fs.File.t);
      }.
    End OpenOptionsExt.

    (* ********FUNCTIONS******** *)
    (*
    [ ] link
    [ ] rename
    [ ] symlink
    [ ] symlink_path
    *)
  End fs.
  
  Module net.
    (* ********TRAITS******** *)
    (*
    [x] TcpListenerExt
    *)
    (* 
    pub trait TcpListenerExt {
        // Required method
        fn sock_accept(&self, flags: u16) -> Result<u32>;
    }
    *)
    Module TcpListenerExt.
      Class Trait (Self : Set) : Set := {
        sock_accept : ref Self -> u16.t -> M ltac:(io.error.Result u32.t);
      }.
    End TcpListenerExt.

  End net.
  
  Module ffi.
    (* ********TRAITS******** *)
    (*
    [x] OsStrExt
    [x] OsStringExt
    *)

    (* 
    pub trait OsStrExt: Sealed {
        // Required methods
        fn from_bytes(slice: &[u8]) -> &Self;
        fn as_bytes(&self) -> &[u8];
    }
    *)
    Module OsStrExt.
      Class Trait (Self : Set) : Set := {
        from_bytes : ref (slice u8.t) -> ref Self;
        as_bytes : ref Self -> ref (slice u8.t);
      }.
    End OsStrExt.

    (* 
    pub trait OsStringExt: Sealed {
        // Required methods
        fn from_vec(vec: Vec<u8>) -> Self;
        fn into_vec(self) -> Vec<u8>;
    }
    *)
    Module OsStringExt.
      Class Trait (Self : Set) : Set := {
        from_vec : vec.Vec u8.t vec.Vec.Default.A -> Self;
        into_vec : Self -> vec.Vec u8.t vec.Vec.Default.A;
      }.
    End OsStringExt.
    
  End ffi.
  
  Module io.
    (* ********RE-EXPORTS******** *)
    (*
    [ ] crate::os::fd::*
    *)
  End io.
  
  Module prelude.
    (* ********RE-EXPORTS******** *)
    (*
    [ ] super::ffi::OsStrExt
    [ ] super::ffi::OsStringExt
    [ ] super::fs::FileTypeExt
    [ ] super::fs::DirEntryExt
    [ ] super::fs::FileExt
    [ ] super::fs::MetadataExt
    [ ] super::fs::OpenOptionsExt
    [ ] super::io::AsFd
    [ ] super::io::AsRawFd
    [ ] super::io::BorrowedFd
    [ ] super::io::FromRawFd
    [ ] super::io::IntoRawFd
    [ ] super::io::OwnedFd
    [ ] super::io::RawFd
    *)
  End prelude.
  
  
End wasi.

Module windows.
  (* ********MODULES******** *)
  (*
  [x] ffi
  [x] fs
  [x] io
  [x] prelude
  [ ] process
  [x] raw
  [x] thread
  *)
  Module ffi.
    (* ********STRUCTS******** *)
    (*
    [x] EncodeWide
    *)

    (* pub struct EncodeWide<'a> { /* private fields */ } *)
    Module EncodeWide.
      Parameter t : Set.
    End EncodeWide.
    
    (* ********TRAITS******** *)
    (*
    [x] OsStrExt
    [x] OsStringExt
    *)
    
    (* 
    pub trait OsStrExt: Sealed {
        // Required method
        fn encode_wide(&self) -> EncodeWide<'_>;
    }
    *)
    Module OsStrExt.
      Class Trait (Self : Set) : Set := {
        encode_wide : ref Self -> M EncodeWide.t;
      }.
    End OsStrExt.
    
    (* 
    pub trait OsStringExt: Sealed {
        // Required method
        fn from_wide(wide: &[u16]) -> Self;
    }
    *)
    Module OsStringExt.
      Class Trait (Self : Set) : Set := {
        from_wide : ref (slice u16.t) -> M Self;
      }.
    End OsStringExt.
    
    
    
  End ffi.
  
  Module fs.
    (* ********TRAITS******** *)
    (*
    [x] FileExt
    [x] FileTypeExt
    [x] MetadataExt
    [x] OpenOptionsExt
    *)
    (* 
    pub trait FileExt {
        // Required methods
        fn seek_read(&self, buf: &mut [u8], offset: u64) -> Result<usize>;
        fn seek_write(&self, buf: &[u8], offset: u64) -> Result<usize>;
    }
    *)
    Module FileExt.
      Class Trait (Self : Set) : Set := {
        seek_read : ref Self -> mut_ref (slice u8.t) -> u64.t -> M ltac:(io.error.Result usize.t);
        seek_write : ref Self -> ref (slice u8.t) -> u64.t -> M ltac:(io.error.Result usize.t);
      }.
    End FileExt.

    (* 
    pub trait FileTypeExt: Sealed {
        // Required methods
        fn is_symlink_dir(&self) -> bool;
        fn is_symlink_file(&self) -> bool;
    }
    *)
    Module FileTypeExt.
      Class Trait (Self : Set) : Set := {
        is_symlink_dir: ref Self -> bool;
        is_symlink_file: ref Self -> bool;
      }.
    End FileTypeExt.

    (* 
    pub trait MetadataExt {
        // Required methods
        fn file_attributes(&self) -> u32;
        fn creation_time(&self) -> u64;
        fn last_access_time(&self) -> u64;
        fn last_write_time(&self) -> u64;
        fn file_size(&self) -> u64;
        fn volume_serial_number(&self) -> Option<u32>;
        fn number_of_links(&self) -> Option<u32>;
        fn file_index(&self) -> Option<u64>;
    }
    *)
    Module MetadataExt.
      Class Trait (Self : Set) : Set := {
        file_attributes : ref Self -> u32.t;
        creation_time : ref Self -> u64.t;
        last_access_time : ref Self -> u64.t;
        last_write_time : ref Self -> u64.t;
        file_size : ref Self -> u64.t;
        volume_serial_number: ref Self -> option.Option.t u32.t;
        number_of_links: ref Self -> option.Option.t u32.t;
        file_index: ref Self -> option.Option.t u64.t;
      }.
    End MetadataExt.
    
    (* 
    pub trait OpenOptionsExt {
        // Required methods
        fn access_mode(&mut self, access: u32) -> &mut Self;
        fn share_mode(&mut self, val: u32) -> &mut Self;
        fn custom_flags(&mut self, flags: u32) -> &mut Self;
        fn attributes(&mut self, val: u32) -> &mut Self;
        fn security_qos_flags(&mut self, flags: u32) -> &mut Self;
    }
    *)
    Module OpenOptionsExt.
      Class Trait (Self : Set) : Set := {
        access_mode : mut_ref Self -> u32.t -> mut_ref Self;
        share_mode : mut_ref Self -> u32.t -> mut_ref Self;
        custom_flags : mut_ref Self -> u32.t -> mut_ref Self;
        attributes : mut_ref Self -> u32.t -> mut_ref Self;
        security_qos_flags : mut_ref Self -> u32.t -> mut_ref Self;
      }.
    End OpenOptionsExt.

    (* ********FUNCTIONS******** *)
    (*
    [ ] symlink_dir
    [ ] symlink_file
    *)
    
  End fs.
  
  Module io.
    (* ********STRUCTS******** *)
    (*
    [x] BorrowedHandle
    [x] BorrowedSocket
    [x] HandleOrInvalid
    [x] HandleOrNull
    [x] InvalidHandleError
    [x] NullHandleError
    [x] OwnedHandle
    [x] OwnedSocket
    *)

    (* 
    #[repr(transparent)]
    pub struct BorrowedHandle<'handle> { /* private fields */ } 
    *)
    Module BorrowedHandle.
      Parameter t : Set.
    End BorrowedHandle.
    
    (* 
    #[repr(transparent)]
    pub struct BorrowedSocket<'socket> { /* private fields */ }
    *)
    Module BorrowedSocket.
      Parameter t : Set.
    End BorrowedSocket.
    
    (* 
    #[repr(transparent)]
    pub struct HandleOrInvalid(_);
    *)
    Module HandleOrInvalid.
      Parameter t : Set.
    End HandleOrInvalid.
    
    (* 
    #[repr(transparent)]
    pub struct HandleOrNull(_);
    *)
    Module HandleOrNull.
      Parameter t : Set.
    End HandleOrNull.
    
    (* pub struct InvalidHandleError(_); *)
    Module InvalidHandleError.
      Parameter t : Set.
    End InvalidHandleError.
    
    (* pub struct NullHandleError(_); *)
    Module NullHandleError.
      Parameter t : Set.
    End NullHandleError.
    
    (* 
    #[repr(transparent)]
    pub struct OwnedHandle { /* private fields */ }
    *)
    Module OwnedHandle.
      Parameter t : Set.
    End OwnedHandle.
    
    (* 
    #[repr(transparent)]
    pub struct OwnedSocket { /* private fields */ }
    *)
    Module OwnedSocket.
      Parameter t : Set.
    End OwnedSocket.

    (* ********TYPE DEFINITIONS******** *)
    (*
    [ ] RawHandle
    [ ] RawSocket
    *)

    Parameter RawHandle : Set.
    Ltac RawHandle := exact RawHandle.

    Parameter RawSocket : Set.
    Ltac RawSocket := exact RawSocket.

    (* ********TRAITS******** *)
    (*
    [ ] AsHandle
    [ ] AsRawHandle
    [ ] AsRawSocket
    [ ] AsSocket
    [ ] FromRawHandle
    [ ] FromRawSocket
    [ ] IntoRawHandle
    [ ] IntoRawSocket
    *)

    (* 
    pub trait AsHandle {
        // Required method
        fn as_handle(&self) -> BorrowedHandle<'_>;
    }
    *)
    Module AsHandle.
      Class Trait (Self : Set) : Set := {
        as_handle : ref Self -> M BorrowedHandle.t;
      }.
    End AsHandle.

    (* 
    pub trait AsRawHandle {
        // Required method
        fn as_raw_handle(&self) -> RawHandle;
    }
    *)
    Module AsRawHandle.
      Class Trait (Self : Set) : Set := {
        as_raw_handle : ref Self -> M ltac:(RawHandle);
      }.
    End AsRawHandle.

    (* 
    pub trait AsRawSocket {
        // Required method
        fn as_raw_socket(&self) -> RawSocket;
    }
    *)
    Module AsRawSocket.
      Class Trait (Self : Set) : Set := {
        as_raw_socket : ref Self -> M ltac:(RawSocket);
      }.
    End AsRawSocket.

    (* 
    pub trait AsSocket {
        // Required method
        fn as_socket(&self) -> BorrowedSocket<'_>;
    }
    *)
    Module AsSocket.
      Class Trait (Self : Set) : Set := {
        as_socket : ref Self -> M BorrowedSocket.t;
      }.
    End AsSocket.
    
    (* 
    pub trait FromRawHandle {
        // Required method
        unsafe fn from_raw_handle(handle: RawHandle) -> Self;
    }
    *)
    Module FromRawHandle.
      Class Trait (Self : Set) : Set := {
        from_raw_handle : M ltac:(RawHandle) -> Self;
      }.
    End FromRawHandle.

    (* 
    pub trait FromRawSocket {
        // Required method
        unsafe fn from_raw_socket(sock: RawSocket) -> Self;
    }
    *)
    Module FromRawSocket.
      Class Trait (Self : Set) : Set := {
        from_raw_socket : RawSocket -> Self;
      }.
    End FromRawSocket.
    
    (* 
    pub trait IntoRawHandle {
        // Required method
        fn into_raw_handle(self) -> RawHandle;
    }
    *)
    Module IntoRawHandle.
      Class Trait (Self : Set) : Set := {
        into_raw_handle : Self -> RawHandle;
      }.
    End IntoRawHandle.
    
    (* 
    pub trait IntoRawSocket {
        // Required method
        fn into_raw_socket(self) -> RawSocket;
    }
    *)
    Module IntoRawSocket.
      Class Trait (Self : Set) : Set := {
        into_raw_socket : Self -> RawSocket;
      }.
    End IntoRawSocket.
  End io.
  
  Module prelude.
    (* ********RE-EXPORTS******** *)
    (*
    [ ] super::ffi::OsStrExt
    [ ] super::ffi::OsStringExt
    [ ] super::fs::FileExt
    [ ] super::fs::MetadataExt
    [ ] super::fs::OpenOptionsExt
    [ ] super::io::AsHandle
    [ ] super::io::AsSocket
    [ ] super::io::BorrowedHandle
    [ ] super::io::BorrowedSocket
    [ ] super::io::FromRawHandle
    [ ] super::io::FromRawSocket
    [ ] super::io::HandleOrInvalid
    [ ] super::io::IntoRawHandle
    [ ] super::io::IntoRawSocket
    [ ] super::io::OwnedHandle
    [ ] super::io::OwnedSocket
    [ ] super::io::AsRawHandle
    [ ] super::io::AsRawSocket
    [ ] super::io::RawHandle
    [ ] super::io::RawSocket
    *)
    
  End prelude.
  
  Module process.
    (* ********TRAITS******** *)
    (*
    [ ] ChildExt
    [ ] ExitCodeExt
    [ ] CommandExt
    [ ] ExitStatusExt
    *)

    (* 
    pub trait ChildExt: Sealed {
        // Required method
        fn main_thread_handle(&self) -> BorrowedHandle<'_>;
    }
    *)
    Module ChildExt.
      Class Trait (Self : Set) : Set := {
        main_thread_handle : ref Self -> M io.BorrowedHandle.t;
      }.
    End ChildExt.

    (* 
    pub trait ExitCodeExt: Sealed {
        // Required method
        fn from_raw(raw: u32) -> Self;
    }
    *)
    Module ExitCodeExt.
      Class Trait (Self : Set) : Set := {
        from_raw : u32.t -> M Self;
      }.
    End ExitCodeExt.

    (* 
    pub trait CommandExt: Sealed {
        // Required methods
        fn creation_flags(&mut self, flags: u32) -> &mut Command;
        fn force_quotes(&mut self, enabled: bool) -> &mut Command;
        fn raw_arg<S: AsRef<OsStr>>(
            &mut self,
            text_to_append_as_is: S
        ) -> &mut Command;
        fn async_pipes(&mut self, always_async: bool) -> &mut Command;
    }
    *)
    Module CommandExt.
      Class Trait (Self : Set) : Set := {
        creation_flags : mut_ref Self -> u32.t -> mut_ref process.Command.t;
        force_quotes : mut_ref Self -> bool -> mut_ref process.Command.t;
        raw_arg {S : Set} : mut_ref Self -> S -> mut_ref process.Command.t;
        async_pipes : mut_ref Self -> bool -> mut_ref process.Command.t;
      }.
    End CommandExt.

    (* 
    pub trait ExitStatusExt: Sealed {
        // Required method
        fn from_raw(raw: u32) -> Self;
    }
    *)
    Module ExitStatusExt.
      Class Trait (Self : Set) : Set := {
      from_raw : u32.t -> Self;
      }.
    End ExitStatusExt.
    
  End process.
  
  Module raw.
    (* ********TYPE DEFINITIONS******** *)
    (*
    [ ] HANDLE
    [ ] SOCKET
    *)
    
  End raw.
  
  Module thread.
  End thread.
  
End windows.
