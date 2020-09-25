import logging
import sys
from abc import *

logger = logging.getLogger('maniunfold.turtle')

class Solver(ABC):
  @abstractmethod
  def solve(self, expr, pt):
    pass

def start(solver):
  '''
  Configure and start the client.
  '''
  logger.info('Opened the user interface.')
  print(str(solver.solve(sys.stdin.readline(), sys.stdin.readline())))
  logger.info('Closed the user interface.')
