import logging
import tkinter as tk
from abc import *
from queue import Queue
from threading import Thread

logger = logging.getLogger('dez.snake')

class Solver(ABC):
  @abstractmethod
  def solve(self, expr, pt):
    pass

def start(solver):
  '''
  Configure and start the client.
  '''
  # We use this dictionary to "tie the knot" with callbacks.
  func = {}

  window = tk.Tk()
  window.title('Polynomial')

  expr_label = tk.Label(window, text='Expression')
  expr_var = tk.StringVar()
  expr_var.trace('w', lambda *x: func['val'](x))
  expr = tk.Entry(window, textvariable=expr_var)
  expr.bind('<Return>', lambda *x: func['eval'](x))
  expr.bind('<KP_Enter>', lambda *x: func['eval'](x))

  pt_label = tk.Label(window, text='Point')
  pt_var = tk.StringVar()
  pt_var.trace('w', lambda *x: func['val'](x))
  pt = tk.Entry(window, textvariable=pt_var)
  pt.bind('<Return>', lambda *x: func['eval'](x))
  pt.bind('<KP_Enter>', lambda *x: func['eval'](x))

  eval = tk.Button(window, text='Evaluate', command=lambda *x: func['eval'](x))

  val_label = tk.Label(window, text='Value')
  val = tk.Entry(window, state=tk.DISABLED)

  def eval_func(event):
    try:
      q = Queue()
      def slow():
        q.put(solver.solve(expr.get(), pt.get()))
      p = Thread(target=slow)
      p.start()
      def poll():
        try:
          v = q.get_nowait()
          val.config(state=tk.NORMAL)
          val.delete(0, tk.END)
          val.insert(0, v)
          val.config(state=tk.DISABLED)
          expr['state'] = tk.NORMAL
          pt['state'] = tk.NORMAL
          eval['state'] = tk.NORMAL
        except: # raise queue.Empty
          val.config(state=tk.NORMAL)
          val.insert(tk.END, '.')
          val.config(state=tk.DISABLED)
          val.after(200, poll)
      val.config(state=tk.NORMAL)
      val.delete(0, tk.END)
      val.insert(0, 'Processing')
      val.config(state=tk.DISABLED)
      # TODO This is insufficient, because it neglects command bindings.
      expr['state'] = tk.DISABLED
      pt['state'] = tk.DISABLED
      eval['state'] = tk.DISABLED
      poll()
    except:
      logger.error(sys.exc_info()[0])
      val.config(state=tk.NORMAL)
      val.delete(0, tk.END)
      val.insert(0, 'Error')
      val.config(state=tk.DISABLED)

  def val_func(event):
    val.config(state=tk.NORMAL)
    val.delete(0, tk.END)
    val.config(state=tk.DISABLED)

  func['eval'] = eval_func
  func['val'] = val_func

  window.rowconfigure(0, weight=0)
  window.rowconfigure(1, weight=0)
  window.rowconfigure(2, weight=1)
  window.rowconfigure(3, weight=0)
  window.columnconfigure(0, weight=0)
  window.columnconfigure(1, weight=1)

  expr_label.grid(row=0, column=0, sticky=tk.E, padx=4, pady=4)
  expr.grid(row=0, column=1, sticky=tk.EW, padx=4, pady=4)
  pt_label.grid(row=1, column=0, sticky=tk.E, padx=4, pady=4)
  pt.grid(row=1, column=1, sticky=tk.EW, padx=4, pady=4)
  eval.grid(row=2, column=0, columnspan=2, sticky=tk.NSEW, padx=4, pady=4)
  val_label.grid(row=3, column=0, sticky=tk.E, padx=4, pady=4)
  val.grid(row=3, column=1, sticky=tk.EW, padx=4, pady=4)

  expr.delete(0, tk.END)
  expr.insert(0, '42 + 13 * x ** 2')

  pt.delete(0, tk.END)
  pt.insert(0, '7')

  logger.info('Opened the user interface.')
  window.mainloop()
  logger.info('Closed the user interface.')
