Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.vec.
Require CoqOfRust.alloc.string.
Require CoqOfRust.core.fmt.
Require CoqOfRust.core.result_types.

(* ********STRUCTS******** *)
(* 
[x] BorrowedBuf
[x] BorrowedCursor
[x] BufReader
[x] BufWriter
[x] Bytes
[x] Chain
[x] Cursor
[x] Empty
[x] Error
[x] IntoInnerError
[x] IoSlice
[x] IoSliceMut
[x] LineWriter
[x] Lines
[x] Repeat
[x] Sink
[x] Split
[x] Stderr
[x] StderrLock
[x] Stdin
[x] StdinLock
[x] Stdout
[x] StdoutLock
[x] Take
[x] WriterPanicked
*)

(* pub struct Error { /* private fields */ } *)
Module Error.
  Parameter t : Set.
End Error.
Definition Error : Set :=
  M.Val Error.t.

Definition Result (T : Set) : Set :=
  core.result_types.Result T Error.t.

(* pub struct BorrowedBuf<'data> { /* private fields */ } *)
Module BorrowedBuf.
  Parameter t : Set.
End BorrowedBuf.
Definition BorrowedBuf := BorrowedBuf.t.

(* pub struct BorrowedCursor<'a> { /* private fields */ } *)
Module BorrowedCursor.
  Parameter t : Set.
End BorrowedCursor.
Definition BorrowedCursor := BorrowedCursor.t.

(* pub struct BufReader<R> { /* private fields */ } *)
Module BufReader.
  Parameter t : Set -> Set.
End BufReader.
Definition BufReader := BufReader.t.

(* pub struct IoSlice<'a>(_); *)
Module IoSlice.
  Parameter t : Set.
End IoSlice.
Definition IoSlice := IoSlice.t.

(* 
pub trait Write {
    // Required methods
    fn write(&mut self, buf: &[u8]) -> Result<usize>;
    fn flush(&mut self) -> Result<()>;

    // Provided methods
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> Result<usize> { ... }
    fn is_write_vectored(&self) -> bool { ... }
    fn write_all(&mut self, buf: &[u8]) -> Result<()> { ... }
    fn write_all_vectored(&mut self, bufs: &mut [IoSlice<'_>]) -> Result<()> { ... }
    fn write_fmt(&mut self, fmt: Arguments<'_>) -> Result<()> { ... }
    fn by_ref(&mut self) -> &mut Self
       where Self: Sized { ... }
}
*)
Module Write.
  Class Trait (Self : Set) : Set := { 
    write : mut_ref Self -> ref (slice u8.t) -> Result usize.t;
    flush : mut_ref Self -> Result unit;
    write_vectored : mut_ref Self -> ref (slice IoSlice) -> Result usize.t;
    is_write_vectored : mut_ref Self -> bool;
    write_all : mut_ref Self -> ref (slice u8.t) -> Result unit;
    write_all_vectored : mut_ref Self -> mut_ref (slice IoSlice) -> Result unit;
    write_fmt : mut_ref Self -> fmt.Arguments.t -> Result unit;
    by_ref : mut_ref Self -> mut_ref Self;
  }.
End Write.


(* pub struct BufWriter<W: Write> { /* private fields */ } *)
Module BufWriter.
  Parameter t : forall (W : Set) `{Write.Trait W}, Set.
End BufWriter.

(* pub struct Bytes<R> { /* private fields */ } *)
Module Bytes.
  Parameter t : forall (R : Set), Set.
End Bytes.

(* pub struct Chain<T, U> { /* private fields */ } *)
Module Chain.
  Parameter t : forall (T U : Set), Set.
End Chain.

(* pub struct Cursor<T> { /* private fields */ } *)
Module Cursor.
  Parameter t : forall (T : Set), Set.
End Cursor.

(* pub struct Empty; *)
Module Empty.
  Parameter t : Set.
End Empty.

(* pub struct IntoInnerError<W>(_, _); *)
Module IntoInnerError.
  Parameter t : forall (W : Set), Set.
End IntoInnerError.

(* pub struct IoSliceMut<'a>(_); *)
Module IoSliceMut.
  Parameter t : Set.
End IoSliceMut.

(* pub struct LineWriter<W: Write> { /* private fields */ } *)
Module LineWriter.
  Parameter t : forall (W : Set) `{Write.Trait W}, Set.
End LineWriter.

(* pub struct Lines<B> { /* private fields */ } *)
Module Lines.
  Parameter t : forall (B : Set), Set.
End Lines.

(* pub struct Repeat { /* private fields */ } *)
Module Repeat.
  Parameter t : Set.
End Repeat.

(* pub struct Sink; *)
Module Sink.
  Parameter t : Set.
End Sink.

(* pub struct Split<B> { /* private fields */ } *)
Module Split.
  Parameter t : forall (B : Set), Set.
End Split.

(* pub struct Stderr { /* private fields */ } *)
Module Stderr.
  Parameter t : Set.
End Stderr.

(* pub struct StderrLock<'a> { /* private fields */ } *)
Module StderrLock.
  Parameter t : Set.
End StderrLock.

(* pub struct Stdin { /* private fields */ } *)
Module Stdin.
  Parameter t : Set.
End Stdin.

(* pub struct StdinLock<'a> { /* private fields */ } *)
Module StdinLock.
  Parameter t : Set.
End StdinLock.

(* pub struct Stdout { /* private fields */ } *)
Module Stdout.
  Parameter t : Set.
End Stdout.

(* pub struct StdoutLock<'a> { /* private fields */ } *)
Module StdoutLock.
  Parameter t : Set.
End StdoutLock.

(* pub struct Take<T> { /* private fields */ } *)
Module Take.
  Parameter t : forall (T : Set), Set.
End Take.

(* pub struct WriterPanicked { /* private fields */ } *)
Module WriterPanicked.
  Parameter t : Set.
End WriterPanicked.

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

(* 
pub enum SeekFrom {
    Start(u64),
    End(i64),
    Current(i64),
}
*)
Module SeekFrom.
  Inductive t : Set :=
  | Start : u64.t -> t
  | End : i64.t -> t
  | Current : i64.t -> t
  .
End SeekFrom.

(* ********TRAITS******** *)
(* 
[x]IsTerminal
[x]BufRead
[x]Read
[ ]Seek
[ ]Write 
*)

(* 
pub trait IsTerminal: Sealed {
    // Required method
    fn is_terminal(&self) -> bool;
}
*)
Module IsTerminal.
  Class Trait (Self : Set) : Set := { 
    is_terminal : ref Self -> bool;
  }.
End IsTerminal.

(* 
pub trait Read {
    // Required method
    fn read(&mut self, buf: &mut [u8]) -> Result<usize>;

    // Provided methods
    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> Result<usize> { ... }
    fn is_read_vectored(&self) -> bool { ... }
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize> { ... }
    fn read_to_string(&mut self, buf: &mut String) -> Result<usize> { ... }
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> { ... }
    fn read_buf(&mut self, buf: BorrowedCursor<'_>) -> Result<()> { ... }
    fn read_buf_exact(&mut self, cursor: BorrowedCursor<'_>) -> Result<()> { ... }
    fn by_ref(&mut self) -> &mut Self
       where Self: Sized { ... }
    fn bytes(self) -> Bytes<Self> ⓘ
       where Self: Sized { ... }
    fn chain<R: Read>(self, next: R) -> Chain<Self, R> ⓘ
       where Self: Sized { ... }
    fn take(self, limit: u64) -> Take<Self> ⓘ
       where Self: Sized { ... }
}
*)
Module Read.
  Class Trait (Self : Set) : Set := { 
    read : mut_ref Self -> mut_ref (slice u8.t) -> Result usize.t;
    read_vectored : mut_ref Self -> mut_ref (slice IoSliceMut.t) -> Result usize.t;
    is_read_vectored : ref Self -> bool;
    read_to_end : mut_ref Self -> mut_ref (slice u8.t) -> Result usize.t;
    read_to_string : mut_ref Self -> mut_ref alloc.string.String.t -> Result usize.t;
    read_exact : mut_ref Self -> mut_ref (slice u8.t) -> Result unit;
    read_buf : mut_ref Self -> BorrowedCursor -> Result unit;
    read_buf_exact : mut_ref Self -> BorrowedCursor -> Result unit;
    by_ref : mut_ref Self -> mut_ref Self;
    bytes : Self -> Bytes.t Self;
    chain {R : Set} : Self -> R -> Chain.t Self R;
    take : Self -> u64.t -> Take.t Self;
  }.
End Read.

(* 
pub trait BufRead: Read {
    // Required methods
    fn fill_buf(&mut self) -> Result<&[u8]>;
    fn consume(&mut self, amt: usize);

    // Provided methods
    fn has_data_left(&mut self) -> Result<bool> { ... }
    fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> Result<usize> { ... }
    fn read_line(&mut self, buf: &mut String) -> Result<usize> { ... }
    fn split(self, byte: u8) -> Split<Self>
       where Self: Sized { ... }
    fn lines(self) -> Lines<Self>
       where Self: Sized { ... }
}
*)
Module BufRead.
  Class Trait (Self : Set) `{Read.Trait Self}: Set := { 
    fill_buf : mut_ref Self -> Result (ref (slice u8.t));
    consume : mut_ref Self -> usize.t -> unit;
    has_data_left : mut_ref Self -> Result bool;
    read_until :
      mut_ref Self -> u8.t -> mut_ref (vec.Vec u8.t vec.Vec.Default.A) -> Result usize.t;
    read_line : mut_ref Self -> mut_ref alloc.string.String.t -> Result usize.t;
    split : Self -> u8.t -> Split.t Self;
    lines : mut_ref Self -> Lines.t Self;
  }.
End BufRead.

(* 
pub trait Seek {
    // Required method
    fn seek(&mut self, pos: SeekFrom) -> Result<u64>;

    // Provided methods
    fn rewind(&mut self) -> Result<()> { ... }
    fn stream_len(&mut self) -> Result<u64> { ... }
    fn stream_position(&mut self) -> Result<u64> { ... }
}
*)
Module Seek.
  Class Trait (Self : Set) : Set := { 
    seek : mut_ref Self -> SeekFrom.t -> Result u64.t;
    rewind : mut_ref Self -> Result unit;
    stream_len : mut_ref Self -> Result u64.t;
    stream_position : mut_ref Self -> Result u64.t;
  }.
End Seek.

(* ********FUNCTIONS******** *)
(*
[ ] copy
[ ] empty
[ ] read_to_string
[ ] repeat
[ ] sink
[ ] stderr
[ ] stdin
[ ] stdout
*)

(* ********TYPE DEFINITIONS******** *)
(*
[ ] RawOsError
[ ] Result
*)

Module stdio.
  Parameter _print : fmt.Arguments.t -> M unit.
End stdio.
