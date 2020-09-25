import sys
sys.path.append('gen-py')
sys.path.append('../reptile')
sys.path.append('../turtle')
import client
import component
import logging
import os
import polynomial
import re
import thrift
from component.ttypes import *
from polynomial.ttypes import *
from thrift.protocol import TBinaryProtocol
from thrift.transport import TSocket
from thrift.transport import TTransport

logger = logging.getLogger('maniunfold.shell')

class SocketSolver(client.Solver):
  def __init__(self, addr, port):
    self.addr = addr
    self.port = port
    self.proto = None

  def __enter__(self):
    logger.info('Connecting to {}:{}.'.format(self.addr, self.port))
    trans = TTransport.TBufferedTransport(TSocket.TSocket(self.addr, self.port))
    self.proto = TBinaryProtocol.TBinaryProtocol(trans)
    self.proto.trans.open()
    # TODO This identity theft works by accident.
    id = identity(name='scales')
    id.write(self.proto)
    self.proto.trans.flush()

    return self

  def __exit__(self, exc_type, exc_value, traceback):
    logger.info('Sending exit message and disconnecting.')
    req = request(type=request_type.EXIT, data=request_data())
    req.write(self.proto)
    self.proto.trans.flush()
    self.proto.trans.close()

  def solve(self, expr, pt):
    # This sucks on purpose.
    const = '([+-]? *[0-9]+)'
    var = '(?:([x])(?: *\*\* *([+]? *[0-9]+))?)'
    subs = re.findall('{} *\* *{}|{}|{}'.format(const, var, const, var), expr)
    coeffs = {}
    for c0, v0, e0, c1, v2, e2 in subs:
      if c0 and v0 and e0:
        coeffs[int(e0)] = float(c0.replace(' ', ''))
      elif c0 and v0:
        coeffs[1] = float(c0.replace(' ', ''))
      elif c1:
        coeffs[0] = float(c1.replace(' ', ''))
      elif v2 and e2:
        coeffs[int(e2.replace(' ', ''))] = 1.0
      elif v2:
        coeffs[1] = 1.0
      else:
        raise SyntaxError(expr)
    point = float(pt)

    p = poly(coeffs=coeffs, point=point)
    req = request(type=request_type.EVAL, data=request_data(eval=p))
    req.write(self.proto)
    self.proto.trans.flush()
    res = response()
    res.read(self.proto)

    logger.info('Work is done.')
    return str(res.value)

def start(addr='127.0.0.1', port=8191):
  '''
  Configure and start the client proxy.
  '''
  with SocketSolver(addr, port) as solver:
    client.start(solver)
