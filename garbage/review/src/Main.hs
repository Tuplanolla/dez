module Main where

import MonkeySaddle_Types
import Thrift.Protocol
import Thrift.Protocol.Binary
import Thrift.Transport.Empty

main :: IO ()
main = do
  let x = Request 42 13
  print x
  let vx = from_Request x
  let y = serializeVal (BinaryProtocol EmptyTransport) vx
  print y
  let z = to_Request (deserializeVal (BinaryProtocol EmptyTransport) (getTypeOf vx) y)
  print z
