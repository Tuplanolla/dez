import sys
sys.path.append('gen-py')
import thrift
import MonkeySaddle
from MonkeySaddle.ttypes import *
from thrift.protocol import TBinaryProtocol
from thrift.transport import TTransport

work = Request(42, 13)
print(str(work))
transportOut = TTransport.TMemoryBuffer()
protocolOut = TBinaryProtocol.TBinaryProtocol(transportOut)
work.write(protocolOut)
bytestring = transportOut.getvalue()
print(str(bytestring))
transportIn = TTransport.TMemoryBuffer(bytestring)
protocolIn = TBinaryProtocol.TBinaryProtocol(transportIn)
moreWork = Request()
moreWork.read(protocolIn)
print(str(moreWork))
