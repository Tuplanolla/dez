# SR Library Python Implementation

def monkey_saddle(x, y):
  # We factor $x^3 - 3 x y^2$ into $x (x^2 - 3 y^2)$,
  # because the factored expression has one fewer multiplication and
  # does not contain subexpressions that are prone to overflow.
  return x * (x ** 2 - 3 * y ** 2)
