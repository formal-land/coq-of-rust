Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.result.


(* ********STRUCTS******** *)
(*
[x] IntoIncoming
[x] AddrParseError
[x] Incoming
[x] Ipv4Addr
[x] Ipv6Addr
[x] SocketAddrV4
[x] SocketAddrV6
[x] TcpListener
[x] TcpStream
[x] UdpSocket
*)

(* pub struct IntoIncoming { /* private fields */ } *)
Module IntoIncoming.
  Record t : Set := { }.
End IntoIncoming.
Definition IntoIncoming := IntoIncoming.t.

(* pub struct AddrParseError(_); *)
Module AddrParseError.
  Record t : Set := { }.
End AddrParseError.
Definition AddrParseError := AddrParseError.t.

(* pub struct Incoming<'a> { /* private fields */ } *)
Module Incoming.
  Record t : Set := { }.
End Incoming.
Definition Incoming := Incoming.t.

(* pub struct Ipv4Addr { /* private fields */ } *)
Module Ipv4Addr.
  Record t : Set := { }.
End Ipv4Addr.
Definition Ipv4Addr := Ipv4Addr.t.

(* pub struct Ipv6Addr { /* private fields */ } *)
Module Ipv6Addr.
  Record t : Set := { }.
End Ipv6Addr.
Definition Ipv6Addr := Ipv6Addr.t.

(* pub struct SocketAddrV4 { /* private fields */ } *)
Module SocketAddrV4.
  Record t : Set := { }.
End SocketAddrV4.
Definition SocketAddrV4 := SocketAddrV4.t.

(* pub struct SocketAddrV6 { /* private fields */ } *)
Module SocketAddrV6.
  Record t : Set := { }.
End SocketAddrV6.
Definition SocketAddrV6 := SocketAddrV6.t.

(* pub struct TcpListener(_); *)
Module TcpListener.
  Record t : Set := { }.
End TcpListener.
Definition TcpListener := TcpListener.t.

(* pub struct TcpStream(_); *)
Module TcpStream.
  Record t : Set := { }.
End TcpStream.
Definition TcpStream := TcpStream.t.

(* pub struct UdpSocket(_); *)
Module UdpSocket.
  Record t : Set := { }.
End UdpSocket.
Definition UdpSocket := UdpSocket.t.

(* ********ENUMS******** *)
(*
[x] Ipv6MulticastScope
[x] IpAddr
[x] Shutdown
[x] SocketAddr
*)
(* 
pub enum Ipv6MulticastScope {
    InterfaceLocal,
    LinkLocal,
    RealmLocal,
    AdminLocal,
    SiteLocal,
    OrganizationLocal,
    Global,
}
*)
Module Ipv6MulticastScope.
  Inductive t : Set := 
  | InterfaceLocal
  | LinkLocal
  | RealmLocal
  | AdminLocal
  | SiteLocal
  | OrganizationLocal
  | Global
  .
End Ipv6MulticastScope.
Definition Ipv6MulticastScope := Ipv6MulticastScope.t.

(* 
pub enum IpAddr {
  V4(Ipv4Addr),
  V6(Ipv6Addr),
}
*)
Module IpAddr.
  Inductive t : Set := 
  | V4 : Ipv4Addr -> t
  | V6 : Ipv6Addr -> t
  .
End IpAddr.
Definition IpAddr := IpAddr.t.

(* 
pub enum Shutdown {
    Read,
    Write,
    Both,
}
*)
Module Shutdown.
  Inductive t : Set := 
  | Read
  | Write
  | Both
  .
End Shutdown.
Definition Shutdown := Shutdown.t.

(* 
pub enum SocketAddr {
  V4(SocketAddrV4),
  V6(SocketAddrV6),
}
*)
Module SocketAddr.
  Inductive t : Set := 
  | V4 : SocketAddrV4 -> t
  | V6 : SocketAddrV6 -> t
  .
End SocketAddr.
Definition SocketAddr := SocketAddr.t.

(* ********TRAITS******** *)
(*
[?] ToSocketAddrs
*)
(* 
pub trait ToSocketAddrs {
    type Iter: Iterator<Item = SocketAddr>;

    // Required method
    fn to_socket_addrs(&self) -> Result<Self::Iter>;
}
*)
(* BUGGED: Iterator dependency *)
Module ToSocketAddrs.
  Class Trait (Self Iter : Set) : Set := { 
    Iter := Iter;
    to_socket_addrs : ref Self -> Result Iter;
  }.
End ToSocketAddrs.
