Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[ ] BorrowedBuf
[ ] BorrowedCursor
[ ] BufReader
[ ] BufWriter
[ ] Bytes
[ ] Chain
[ ] Cursor
[ ] Empty
[ ] Error
[ ] IntoInnerError
[ ] IoSlice
[ ] IoSliceMut
[ ] LineWriter
[ ] Lines
[ ] Repeat
[ ] Sink
[ ] Split
[ ] Stderr
[ ] StderrLock
[ ] Stdin
[ ] StdinLock
[ ] Stdout
[ ] StdoutLock
[ ] Take
[ ] WriterPanicked
*)

(* ********ENUMS******** *)

(* 
[x] ErrorKind
[x] SeekFrom
*)

(* 
pub enum ErrorKind {
    NotFound,
    PermissionDenied,
    ConnectionRefused,
    ConnectionReset,
    HostUnreachable,
    NetworkUnreachable,
    ConnectionAborted,
    NotConnected,
    AddrInUse,
    AddrNotAvailable,
    NetworkDown,
    BrokenPipe,
    AlreadyExists,
    WouldBlock,
    NotADirectory,
    IsADirectory,
    DirectoryNotEmpty,
    ReadOnlyFilesystem,
    FilesystemLoop,
    StaleNetworkFileHandle,
    InvalidInput,
    InvalidData,
    TimedOut,
    WriteZero,
    StorageFull,
    NotSeekable,
    FilesystemQuotaExceeded,
    FileTooLarge,
    ResourceBusy,
    ExecutableFileBusy,
    Deadlock,
    CrossesDevices,
    TooManyLinks,
    InvalidFilename,
    ArgumentListTooLong,
    Interrupted,
    Unsupported,
    UnexpectedEof,
    OutOfMemory,
    Other,
    // some variants omitted
}
*)
Module ErrorKind.
  Inductive t :=
  | NotFound
  | PermissionDenied
  | ConnectionRefused
  | ConnectionReset
  | HostUnreachable
  | NetworkUnreachable
  | ConnectionAborted
  | NotConnected
  | AddrInUse
  | AddrNotAvailable
  | NetworkDown
  | BrokenPipe
  | AlreadyExists
  | WouldBlock
  | NotADirectory
  | IsADirectory
  | DirectoryNotEmpty
  | ReadOnlyFilesystem
  | FilesystemLoop
  | StaleNetworkFileHandle
  | InvalidInput
  | InvalidData
  | TimedOut
  | WriteZero
  | StorageFull
  | NotSeekable
  | FilesystemQuotaExceeded
  | FileTooLarge
  | ResourceBusy
  | ExecutableFileBusy
  | Deadlock
  | CrossesDevices
  | TooManyLinks
  | InvalidFilename
  | ArgumentListTooLong
  | Interrupted
  | Unsupported
  | UnexpectedEof
  | OutOfMemory
  | Other
  .
End ErrorKind.
Definition ErrorKind := ErrorKind.t.

(* 
pub enum SeekFrom {
    Start(u64),
    End(i64),
    Current(i64),
}
*)
Module SeekFrom.
  Inductive t : Set :=
  | Start : u64 -> t
  | End : i64 -> t
  | Current : i64 -> t
  .
End SeekFrom.
Definition SeekFrom := SeekFrom.t.

(* ********TRAITS******** *)
(* 
[ ]IsTerminal
[ ]BufRead
[ ]Read
[ ]Seek
[ ]Write 
*)