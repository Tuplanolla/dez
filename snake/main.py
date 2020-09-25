# TODO Perhaps remove this.

import client
import sympy

class SympySolver(client.Solver):
  def __enter__(self):
    return self

  def __exit__(self, exc_type, exc_value, traceback):
    pass

  def solve(self, expr, pt):
    # Things go wrong with SymPy,
    # because expressions that simplify into constants
    # are not considered to be polynomials and
    # fractional exponents are quietly accepted.
    x = sympy.Symbol('x')
    p = sympy.polys.polytools.poly_from_expr(expr)[0]
    y = p.subs({x: float(pt)})
    return str(y)

def main():
  '''
  Test the client with SymPy.
  '''
  with SympySolver() as solver:
    client.start(solver)

if __name__ == '__main__':
  main()
