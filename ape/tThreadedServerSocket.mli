open Thrift

(** Threaded server socket.

    This module extends [TServerSocket] from [Thrift]
    with capabilities for cooperative multitasking.
    It also adds [SO_REUSEADDR] to the socket options,
    so that restarting the server does not raise a spurious [EADDRINUSE]. *)
class t : int -> TServerSocket.t
