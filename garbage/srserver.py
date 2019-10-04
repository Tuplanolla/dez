# SR Wrapper Python Implementation

import os
import socket
import srlib
import sys
import time

def main():
  server_addr = '/tmp/srsocket'

  if os.path.exists(server_addr):
      os.unlink(server_addr)

  lsock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
  lsock.bind(server_addr)
  lsock.listen(0)

  print('Server ready.')

  while True:
    sock, _ = lsock.accept()

    nxb = sock.recv(8)
    nx = int.from_bytes(nxb, byteorder=sys.byteorder, signed=False)
    xb = sock.recv(nx)
    x = int.from_bytes(xb, byteorder=sys.byteorder, signed=True)

    nyb = sock.recv(8)
    ny = int.from_bytes(nyb, byteorder=sys.byteorder, signed=False)
    yb = sock.recv(ny)
    y = int.from_bytes(yb, byteorder=sys.byteorder, signed=True)

    z = srlib.monkey_saddle(x, y)
    time.sleep(1)

    nz = 1 + z.bit_length() // 8
    nzb = nz.to_bytes(8, byteorder=sys.byteorder, signed=False)
    sock.send(nzb)
    zb = z.to_bytes(nz, byteorder=sys.byteorder, signed=True)
    sock.send(zb)

    print('Sent {}.'.format(str(z)))
    sock.close()

main()
