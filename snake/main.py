import client
import sympy

class SympySolver(client.Solver):
  def solve(self, expr, pt):
    # Things go wrong with SymPy,
    # because expressions that simplify into constants
    # are not considered to be polynomials and
    # fractional exponents are quietly accepted.
    x = sympy.Symbol('x')
    p = sympy.polys.polytools.poly_from_expr(expr)[0]
    y = p.subs({x: float(pt)})
    return str(y)

  def exit(self):
    pass

def main():
  '''
  Test the client with SymPy.
  '''
  client.start(SympySolver())

if __name__ == '__main__':
  main()
