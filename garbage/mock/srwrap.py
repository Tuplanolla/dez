# SR Wrapper Python Implementation

import srlib
import sys

def main():
  # The size of unsigned integers is `(8 + x.bit_length() - 1) // 8` or
  # equivalently `(7 + x.bit_length()) // 8` and
  # the size of signed integers is `(8 + x.bit_length()) // 8` or
  # equivalently `1 + x.bit_length() // 8`.

  length = 8
  byteorder = 'little'
  signed = False

  nxb = sys.stdin.buffer.read(length)
  nx = int.from_bytes(nxb, byteorder=byteorder, signed=signed)
  xb = sys.stdin.buffer.read(nx)
  sx = -1 if xb[0] != 0 else 1
  axb = xb[1 :]
  x = sx * int.from_bytes(axb, byteorder=byteorder, signed=signed)

  nyb = sys.stdin.buffer.read(length)
  ny = int.from_bytes(nyb, byteorder=byteorder, signed=signed)
  yb = sys.stdin.buffer.read(ny)
  sy = -1 if yb[0] != 0 else 1
  ayb = yb[1 :]
  y = sy * int.from_bytes(ayb, byteorder=byteorder, signed=signed)

  z = srlib.monkey_saddle(x, y)

  nz = 1 + (7 + z.bit_length()) // 8
  nzb = nz.to_bytes(length, byteorder=byteorder, signed=signed)
  sys.stdout.buffer.write(nzb)
  sz = 1 if z < 0 else 0
  szb = sz.to_bytes(1, byteorder=byteorder, signed=signed)
  sys.stdout.buffer.write(szb)
  az = abs(z)
  azb = az.to_bytes(nz - 1, byteorder=byteorder, signed=signed)
  sys.stdout.buffer.write(azb)
  sys.stdout.buffer.flush()

main()
