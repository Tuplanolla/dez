import sys
sys.path.append('gen-py')
import component
import logging
import os
import polynomial
import thrift
from component.ttypes import *
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
  trans = TTransport.TBufferedTransport(TSocket.TSocket('127.0.0.1', 8191))
  proto = TBinaryProtocol.TBinaryProtocol(trans)
  proto.trans.open()
  id = identity(name="scales")
  id.write(proto)
  proto.trans.flush()
  req = request(coeffs={0: 42.0, 2: 13.0}, point=7.0)
  req.write(proto)
  proto.trans.flush()
  res = response()
  res.read(proto)
  proto.trans.close()
  logger.info('Work is done.')
  print(str(res))
