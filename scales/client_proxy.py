import sys
sys.path.append('gen-py')
import logging
import os
import polynomial
import thrift
from polynomial.ttypes import *
from thrift.protocol import TBinaryProtocol
from thrift.transport import TTransport
from thrift.transport import TSocket

logger = logging.getLogger('maniunfold.scales')

def start():
  logger.info('Connecting to {}.'.format('localhorse'))
  trans = TTransport.TBufferedTransport(TSocket.TSocket('127.0.0.1', 9092))
  proto = TBinaryProtocol.TBinaryProtocol(trans)
  proto.trans.open()
  req = request(coeffs={0: 42.0, 2: 13.0}, point=7.0)
  req.write(proto)
  proto.trans.flush()
  res = response()
  res.read(proto)
  proto.trans.close()
  logger.info('Work is done.')
  print(str(res))
