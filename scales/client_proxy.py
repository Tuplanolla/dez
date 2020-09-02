import sys
sys.path.append('gen-py')
sys.path.append('../reptile')
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

logger = logging.getLogger('maniunfold.scales')

def broker_port():
  '''
  See the documentation for the broker.
  '''
  return 8191

def start():
  '''
  Configure and start the client proxy.
  '''
  # TODO Open, execute, close...
  def solve(expr, pt):
    ip = '127.0.0.1'
    logger.info('Connecting to {}.'.format(ip))
    trans = TTransport.TBufferedTransport(TSocket.TSocket(ip, broker_port()))
    proto = TBinaryProtocol.TBinaryProtocol(trans)
    proto.trans.open()
    id = identity(name="scales-oneshot")
    id.write(proto)
    proto.trans.flush()

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

    req = request(coeffs=coeffs, point=point)
    req.write(proto)
    proto.trans.flush()
    res = response()
    res.read(proto)
    proto.trans.close()
    logger.info('Work is done.')
    return str(res.value)

  client.start({'solve': solve})
