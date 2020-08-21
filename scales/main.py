import client_proxy
import logging

# Log messages follow a format, where
#
# * `[%(asctime)s.%(msecs)d]` mimicks `dmesg`,
# * `==%(process)d==` mimicks `valgrind`,
# * `"%(name)s"` mimicks `httpd`,
# * `<%(funcName)s>` mimicks `objdump` and
# * `%(filename)s:%(lineno)d: %(levelname)s: %(message)s` mimicks `cc`.

logging.basicConfig(
  filename='/tmp/scales.log',
  filemode='w',
  format=' '.join([
    '[%(asctime)s.%(msecs)d]',
    '==%(process)d==',
    '"%(name)s"',
    '%(filename)s:%(lineno)d: %(levelname)s: %(message)s']),
  datefmt='%s',
  level=logging.DEBUG)

client_proxy.start()
