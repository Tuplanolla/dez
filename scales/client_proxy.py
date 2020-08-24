import sys
sys.path.append('gen-py')
import logging
import os
import polynomial
import thrift
from polynomial.ttypes import *
from thrift.protocol import TBinaryProtocol
from thrift.transport import TSocket
from thrift.transport import TTransport

logger = logging.getLogger('maniunfold.scales')

def start():
  '''
  Configure and start the client proxy.
  '''
  logger.info('Connecting to {}.'.format('localhorse'))
  trans = TTransport.TBufferedTransport(TSocket.TSocket('127.0.0.1', 9092))
  proto = TBinaryProtocol.TBinaryProtocol(trans)
  proto.trans.open()
  # Launch gui and wait for commands.
  req = request(coeffs={0: 42.0, 2: 13.0}, point=7.0)
  # On each command, send it to the broker, wait for the response, forward it.
  # We may block the proxy, but never the gui.
  req.write(proto)
  proto.trans.flush()
  res = response()
  res.read(proto)
  proto.trans.close()
  logger.info('Work is done.')
  print(str(res))
