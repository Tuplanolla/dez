import socket
import sys
import time

server_addr = '/tmp/srsocket'

x = 42
y = 13

sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
sock.connect(server_addr)

nx = 1 + x.bit_length() // 8
nxb = nx.to_bytes(8, byteorder=sys.byteorder, signed=False)
sock.send(nxb)
xb = x.to_bytes(nx, byteorder=sys.byteorder, signed=True)
sock.send(xb)

ny = 1 + y.bit_length() // 8
nyb = ny.to_bytes(8, byteorder=sys.byteorder, signed=False)
sock.send(nyb)
yb = y.to_bytes(ny, byteorder=sys.byteorder, signed=True)
sock.send(yb)

nzb = sock.recv(8)
nz = int.from_bytes(nzb, byteorder=sys.byteorder, signed=False)
zb = sock.recv(nz)
z = int.from_bytes(zb, byteorder=sys.byteorder, signed=True)

sock.close()

print(str(z))
