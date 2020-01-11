# https://thrift.apache.org/tutorial/
# https://diwakergupta.github.io/thrift-missing-guide/

all:
	thrift -r --gen cpp MonkeySaddle.thrift
	thrift -r --gen ocaml MonkeySaddle.thrift
	thrift -r --gen hs MonkeySaddle.thrift

clean:
	rm -fr gen-*
