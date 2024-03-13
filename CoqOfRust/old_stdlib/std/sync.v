Require Import CoqOfRust.lib.lib.

Require CoqOfRust.core.result.

Module mpsc.
  (* pub struct SendError<T>(pub T); *)
  Module SendError.
    Parameter t : Set -> Set.
  End SendError.

  (* pub struct Sender<T> { /* private fields */ } *)
  Module Sender.
    Parameter t : Set -> Set.

    Module  Impl.
    Section Impl.
      Context {T : Set}.

      Definition Self : Set := t T.

      (* pub fn send(&self, t: T) -> Result<(), SendError<T>> *)
      Parameter send :
        ref Self -> T -> M (result.Result.t unit (SendError.t T)).

      Global Instance AF_send : Notations.DoubleColon Self "send" := {
        Notations.double_colon := send;
      }.
    End Impl.
    End Impl.
  End Sender.

  (* pub struct RecvError; *)
  Module RecvError.
    Parameter t : Set.
  End RecvError.

  (* pub struct Receiver<T> { /* private fields */ } *)
  Module Receiver.
    Parameter t : Set -> Set.

    Module  Impl.
    Section Impl.
      Context {T : Set}.

      Definition Self : Set := t T.

      (* pub fn recv(&self) -> Result<T, RecvError> *)
      Parameter recv : ref Self -> M (result.Result.t T RecvError.t).

      Global Instance AF_recv : Notations.DoubleColon Self "recv" := {
        Notations.double_colon := recv;
      }.
    End Impl.
    End Impl.
  End Receiver.

  (* pub fn channel<T>() -> (Sender<T>, Receiver<T>) *)
  Parameter channel : forall {T : Set}, M (Sender.t T * Receiver.t T).
End mpsc.
