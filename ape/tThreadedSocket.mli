open Thrift

(** Threaded socket.

    This module extends [TSocket] from [Thrift]
    with capabilities for cooperative multitasking. *)
class t : string -> int -> TSocket.t
