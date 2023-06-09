Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.result.
Require Import CoqOfRust.std.process.
Require Import CoqOfRust.std.vec.

(* ********MODULES******** *)
(*
[x] fd
[x] linux
[x] raw
[x] unix
[ ] wasi
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
    Record t : Set := { }.
  End BorrowedFd.
  Definition BorrowedFd := BorrowedFd.t.
  
  (* pub struct OwnedFd { /* private fields */ } *)
  Module OwnedFd.
    Record t : Set := { }.
  End OwnedFd.
  Definition OwnedFd := OwnedFd.t.

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
      as_fd : ref Self -> BorrowedFd;
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
      as_raw_fd : ref Self -> RawFd;
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
      from_raw_fd : RawFd -> Self;
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
      into_raw_fd : Self -> RawFd;
    }.
  End IntoRawFd.

  (* ********TYPE DEFINITIONS******** *)
  (*
  [ ] RawFd
  *)
End fd.

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
      Record t : Set := { }.
    End PidFd.
    Definition PidFd := PidFd.t.
    
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
        pidfd : ref Self -> Result (ref PidFd);
        take_pidfd : mut_ref Self -> Result PidFd;
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
        create_pidfd : mut_ref Self -> bool -> mut_ref Command;
      }.
    End CommandExt.

  End process.
  
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
        as_raw_stat : ref Self -> stat;
        st_dev : ref Self -> u64;
        st_ino : ref Self -> u64;
        st_mode : ref Self -> u32;
        st_nlink : ref Self -> u64;
        st_uid : ref Self -> u32;
        st_gid : ref Self -> u32;
        st_rdev : ref Self -> u64;
        st_size : ref Self -> u64;
        st_atime : ref Self -> i64;
        st_atime_nsec : ref Self -> i64;
        st_mtime : ref Self -> i64;
        st_mtime_nsec : ref Self -> i64;
        st_ctime : ref Self -> i64;
        st_ctime_nsec : ref Self -> i64;
        st_blksize : ref Self -> u64;
        st_blocks : ref Self -> u64;
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
        set_quickack : ref Self -> bool -> Result unit;
        quickack : ref Self -> Result bool;
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
        from_abstract_name (N : Set) `{AsRef.Trait N (slice u8)} : N -> Result SocketAddr;
        as_abstract_name : ref Self -> Option (ref (slice u8));
      }.
    End SocketAddrExt.
    
    
  End net.
End linux.

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
        from_bytes : ref (slice u8) -> ref Self;
        as_bytes : ref Self -> ref (slice u8);
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
        from_vec : Vec u8 -> Self;
        into_vec : Self -> Vec u8;
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
        file_name_ref : ref Self -> ref OsStr;
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
        mode : mut_ref -> u32 -> mut_ref Self;
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
        ino : ref Self -> u64;
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
        read_at : ref Self -> mut_ref (slice u8) : u64 -> Result usize;
        write_at : ref Self -> ref (slice u8) : u64 -> Result usize;
        read_vectored_at : ref Self -> mut_ref (slice IoSliceMut) : u64 -> Result usize;
        read_exact_at : ref Self -> mut_ref u8 -> u64 -> Result unit;
        write_vectored_at : ref Self -> ref (slice IoSlice) : u64 -> Result usize;
        write_all_at : ref Self -> ref (slice u8) : u64 -> Result unit;
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
        dev : ref Self -> u64;
        ino : ref Self -> u64;
        mode : ref Self -> u32;
        nlink : ref Self -> u64;
        uid : ref Self -> u32;
        gid : ref Self -> u32;
        rdev : ref Self -> u64;
        size : ref Self -> u64;
        atime : ref Self -> i64;
        atime_nsec : ref Self -> i64;
        mtime : ref Self -> i64;
        mtime_nsec : ref Self -> i64;
        ctime : ref Self -> i64;
        ctime_nsec : ref Self -> i64;
        blksize : ref Self -> u64;
        blocks : ref Self -> u64;
      
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
        mode : mut_ref Self -> u32 -> mut_ref Self;
        custom_flags : mut_ref Self -> i32 -> mut_ref Self;
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
        mode : ref Self -> u32;
        set_mode : mut_ref Self -> u32 -> unit;
        from_mode : u32 -> Self;
      }.
    End PermissionsExt.

    (* ********FUNCTIONS******** *)
    (*
    [ ] chown
    [ ] fchown
    [ ] lchown
    [ ] chroot
    [ ] symlink
    *)
    
    
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
      Record t : Set := { }.
    End Messages.
    Definition Messages := Messages.t.

    (* pub struct ScmCredentials<'a>(_); *)
    Module ScmCredentials.
      Record t : Set := { }.
    End ScmCredentials.
    Definition ScmCredentials := ScmCredentials.t.
    
    (* pub struct ScmRights<'a>(_); *)
    Module ScmRights.
      Record t : Set := { }.
    End ScmRights.
    Definition ScmRights := ScmRights.t.
    
    (* pub struct SocketAncillary<'a> { /* private fields */ } *)
    Module SocketAncillary.
      Record t : Set := { }.
    End SocketAncillary.
    Definition SocketAncillary := SocketAncillary.t.
    
    (* pub struct SocketCred(_); *)
    Module SocketCred.
      Record t : Set := { }.
    End SocketCred.
    Definition SocketCred := SocketCred.t.
    
    (* pub struct Incoming<'a> { /* private fields */ } *)
    Module Incoming.
      Record t : Set := { }.
    End Incoming.
    Definition Incoming := Incoming.t.
    
    (* pub struct SocketAddr { /* private fields */ } *)
    Module SocketAddr.
      Record t : Set := { }.
    End SocketAddr.
    Definition SocketAddr := SocketAddr.t.
    
    (* pub struct UnixDatagram(_); *)
    Module UnixDatagram.
      Record t : Set := { }.
    End UnixDatagram.
    Definition UnixDatagram := UnixDatagram.t.
    
    (* pub struct UnixListener(_); *)
    Module UnixListener.
      Record t : Set := { }.
    End UnixListener.
    Definition UnixListener := UnixListener.t.
    
    (* pub struct UnixStream(_); *)
    Module UnixStream.
      Record t : Set := { }.
    End UnixStream.
    Definition UnixStream := UnixStream.t.
    
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
    Definition AncillaryData := AncillaryData.t.

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
    Definition AncillaryError := AncillaryError.t.

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
        uid : mut_ref Self -> u32 -> mut_ref Command;
        gid : mut_ref Self -> u32 -> mut_ref Command;
        groups : mut_ref Self -> ref (slice u32) -> mut_ref Command;
        pre_exec (F : Set) 
          `{Send.Trait F}
          `{Sync.Trait F}
        : mut_ref Self -> F -> mut_ref Command;
        exec : mut_ref Self -> Error;
        arg0 (S : Set) `{AsRef.Trait S OsStr} : mut_ref Self -> S -> mut_ref Command;
        process_group : mut_ref Self -> i32 -> mut_ref Command;
        before_exec (F : Set) 
          `{Send.Trait F}
          `{Sync.Trait F}
        mut_ref Self -> F -> mut_ref Command;
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
        from_raw : i32 -> Self;
        signal : ref Self -> Option i32;
        core_dumped : ref Self -> bool;
        stopped_signal : ref Self -> Option i32;
        continued : ref Self -> bool;
        into_raw : Self -> i32;
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

Module wasi.
  (* ********MODULES******** *)
  (*
  [ ] fs
  [ ] net
  [ ] ffi
  [ ] io
  [ ] prelude
  *)
  
End wasi.

Module windows.
  (* ********MODULES******** *)
  (*
  [ ] ffi
  [ ] fs
  [ ] io
  [ ] prelude
  [ ] process
  [ ] raw
  [ ] thread
  *)
End windows.
