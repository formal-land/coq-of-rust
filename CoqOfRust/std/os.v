Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.result.
Require Import CoqOfRust.std.process.



(* ********MODULES******** *)
(*
[x] fd
[x] linux
[x] raw
[ ] unix
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
  [ ] ucred
  [ ] ffi
  [ ] fs
  [ ] io
  [ ] net
  [ ] prelude
  [ ] process
  [x] raw(Deprecated)
  [ ] thread
  *)
  
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
