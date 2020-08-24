import tkinter as tk

def main():
  window = tk.Tk()

  expr_label = tk.Label(window, text='Expression')
  expr = tk.Entry(window)
  pt_label = tk.Label(window, text='Point')
  pt = tk.Entry(window)

  expr_label.grid(row=0, column=0, sticky=tk.E, padx=4, pady=4)
  pt_label.grid(row=1, column=0, sticky=tk.E, padx=4, pady=4)
  expr.grid(row=0, column=1, sticky=tk.EW, padx=4, pady=4)
  pt.grid(row=1, column=1, sticky=tk.EW, padx=4, pady=4)

  window.rowconfigure(0, weight=1)
  window.rowconfigure(1, weight=1)
  window.columnconfigure(0, weight=0)
  window.columnconfigure(1, weight=1)

  expr.insert(0, '42 + 13 x^2')
  pt.insert(0, '7')

  window.mainloop()

main()
