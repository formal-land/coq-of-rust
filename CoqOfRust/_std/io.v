Require Import CoqOfRust.Monad.

Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust._std.fmt.
Require Import CoqOfRust._std.vec.
Require Import CoqOfRust.core.result.

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
Definition Error := Error.t.

Definition Result (T : Set) := core.result.Result T Error.t.

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
    write : mut_ref Self -> ref (slice u8) -> Result usize;
    flush : mut_ref Self -> Result unit;
    write_vectored : mut_ref Self -> ref (slice IoSlice) -> Result usize;
    is_write_vectored : mut_ref Self -> bool;
    write_all : mut_ref Self -> ref (slice u8) -> Result unit;
    write_all_vectored : mut_ref Self -> mut_ref (slice IoSlice) -> Result unit;
    write_fmt : mut_ref Self -> Arguments -> Result unit;
    by_ref : mut_ref Self -> mut_ref Self;
  }.
End Write.


(* pub struct BufWriter<W: Write> { /* private fields */ } *)
Module BufWriter.
  Parameter t : forall (W : Set) `{Write.Trait W}, Set.
End BufWriter.
Definition BufWriter := BufWriter.t.

(* pub struct Bytes<R> { /* private fields */ } *)
Module Bytes.
  Parameter t : forall (R : Set), Set.
End Bytes.
Definition Bytes := Bytes.t.

(* pub struct Chain<T, U> { /* private fields */ } *)
Module Chain.
  Parameter t : forall (T U : Set), Set.
End Chain.
Definition Chain := Chain.t.

(* pub struct Cursor<T> { /* private fields */ } *)
Module Cursor.
  Parameter t : forall (T : Set), Set.
End Cursor.
Definition Cursor := Cursor.t.

(* pub struct Empty; *)
Module Empty.
  Parameter t : Set.
End Empty.
Definition Empty := Empty.t.

(* pub struct IntoInnerError<W>(_, _); *)
Module IntoInnerError.
  Parameter t : forall (W : Set), Set.
End IntoInnerError.
Definition IntoInnerError := IntoInnerError.t.

(* pub struct IoSliceMut<'a>(_); *)
Module IoSliceMut.
  Parameter t : Set.
End IoSliceMut.
Definition IoSliceMut := IoSliceMut.t.

(* pub struct LineWriter<W: Write> { /* private fields */ } *)
Module LineWriter.
  Parameter t : forall (W : Set) `{Write.Trait W}, Set.
End LineWriter.
Definition LineWriter := LineWriter.t.

(* pub struct Lines<B> { /* private fields */ } *)
Module Lines.
  Parameter t : forall (B : Set), Set.
End Lines.
Definition Lines := Lines.t.

(* pub struct Repeat { /* private fields */ } *)
Module Repeat.
  Parameter t : Set.
End Repeat.
Definition Repeat := Repeat.t.

(* pub struct Sink; *)
Module Sink.
  Parameter t : Set.
End Sink.
Definition Sink := Sink.t.

(* pub struct Split<B> { /* private fields */ } *)
Module Split.
  Parameter t : forall (B : Set), Set.
End Split.
Definition Split := Split.t.

(* pub struct Stderr { /* private fields */ } *)
Module Stderr.
  Parameter t : Set.
End Stderr.
Definition Stderr := Stderr.t.

(* pub struct StderrLock<'a> { /* private fields */ } *)
Module StderrLock.
  Parameter t : Set.
End StderrLock.
Definition StderrLock := StderrLock.t.

(* pub struct Stdin { /* private fields */ } *)
Module Stdin.
  Parameter t : Set.
End Stdin.
Definition Stdin := Stdin.t.

(* pub struct StdinLock<'a> { /* private fields */ } *)
Module StdinLock.
  Parameter t : Set.
End StdinLock.
Definition StdinLock := StdinLock.t.

(* pub struct Stdout { /* private fields */ } *)
Module Stdout.
  Parameter t : Set.
End Stdout.
Definition Stdout := Stdout.t.

(* pub struct StdoutLock<'a> { /* private fields */ } *)
Module StdoutLock.
  Parameter t : Set.
End StdoutLock.
Definition StdoutLock := StdoutLock.t.

(* pub struct Take<T> { /* private fields */ } *)
Module Take.
  Parameter t : forall (T : Set), Set.
End Take.
Definition Take := Take.t.

(* pub struct WriterPanicked { /* private fields */ } *)
Module WriterPanicked.
  Parameter t : Set.
End WriterPanicked.
Definition WriterPanicked := WriterPanicked.t.




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
    read : mut_ref Self -> mut_ref (slice u8) -> Result usize;
    read_vectored : mut_ref Self -> mut_ref (slice IoSliceMut) -> Result usize;
    is_read_vectored : ref Self -> bool;
    read_to_end : mut_ref Self -> mut_ref (slice u8) -> Result usize;
    read_to_string : mut_ref Self -> mut_ref String -> Result usize;
    read_exact : mut_ref Self -> mut_ref (slice u8) -> Result unit;
    read_buf : mut_ref Self -> BorrowedCursor -> Result unit;
    read_buf_exact : mut_ref Self -> BorrowedCursor -> Result unit;
    by_ref : mut_ref Self -> mut_ref Self;
    bytes : Self -> Bytes Self;
    chain {R : Set} : Self -> R -> Chain Self R;
    take : Self -> u64 -> Take Self;
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
    fill_buf : mut_ref Self -> Result (ref (slice u8));
    consume : mut_ref Self -> usize -> unit;
    has_data_left : mut_ref Self -> Result bool;
    read_until : mut_ref Self -> u8 -> mut_ref (Vec u8 None) -> Result usize;
    read_line : mut_ref Self -> mut_ref String -> Result usize;
    split : Self -> u8 -> Split Self;
    lines : mut_ref Self -> Lines Self;
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
    seek : mut_ref Self -> SeekFrom -> Result u64;
    rewind : mut_ref Self -> Result unit;
    stream_len : mut_ref Self -> Result u64;
    stream_position : mut_ref Self -> Result u64;
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
  Parameter _print : forall `{State.Trait} {A : Set}, A -> M unit.
End stdio.
