# Interprocess Communication

In order to deal with code extracted from Coq proofs
into either OCaml or Haskell and
solvers written in C++, Fortran or Python,
it is best to adopt the Erlang philosophy of
independent processes communicating via message passing.
If performance becomes a problem,
they may also pass shared memory references
with locks or leases.
The main question is thus the following.

> What protocol and serialization format should we use?

The requirements are

* suitable for interprocess communication,
* there exist libraries under GPL 3 compatible licenses,

would prefer

* both binary and text representations,
* formally specified,
* mathematically principled design,
* support for schema evolution,
* independence from machine architecture,

do not care much about

* compact storage,
* international standard,
* high performance,

The languages we care about are

* OCaml (first release 1996, official 2017),
  obtain packages via OPAM,
* Haskell (first release 1990, standard 1998, new version 2011),
  obtain packages via Hackage,
* Coq (first release 1989, new name 1991),
  obtain packages via OPAM,
* Python (first release 1991, new version 2008),
  obtain packages via PyPI,
* C++ (first release 1985, standard 1998, new version 2017),
  obtain packages via APT,
* C (first release 1972, standard 1989, new version 2018),
  obtain packages via APT,
* Fortran (first release 1957, standard 1966, new version 2018),
  obtain packages via APT,

Not applicable formats are

* XML (verbose),
* SOAP (more XML),
* JSON (underspecified),
* BSON (allegedly just binary JSON),
* YAML (underspecified),
* CSV (underspecified),
* S-Expr (underspecified),
* HDF5 (storage format),
* SQL (storage format),
* Pickle (Python only),
* Kryo (Java only),
* GHC Binary (Haskell only),
* P-List (Apple specific),

Potential candidates are

* Protocol Buffers (allegedly poorly designed like Go),
* Cap'n Proto (allegedly a worse protobuf),
* FlatBuffers (allegedly a faster protobuf),
* MessagePack (allegedly binary JSON with schemas),
* CBOR (allegedly binary JSON),
* Efficient XML Interchange EXI (allegedly XML with duct tape),
* ASN.1 (allegedly excessively complex due to age),
* Avro (allegedly tightly coupled to the JVM),
* Thrift (allegedly has bindings for everything),
* Parquet (allegedly tightly coupled to Hadoop),
* Extprot (allegedly tightly coupled to OCaml),
* Arrow (allegedly just a shared memory system),
* D-Bus (allegedly a messy Linux subsystem),
* CORBA (not sure what this is),
* XDR (not sure what this is either),

Review them at the turn of 2020, roughly as follows,
where bangs denote official bindings.

| Year | Author        | Project
|:-----|:--------------|:-------------------------------------
| 2013 | IETF          | [CBOR][cbor]
| 2008 | Google        | [Protocol Buffers][protocol-buffers]
|      | Google        | [FlatBuffers][flatbuffers]
|      | Treasure Data | [MessagePack][messagepack]
|      | Apache        | [Avro][avro]
|      | Apache        | [Parquet][parquet]
|      | Apache        | [Arrow][arrow]
|      | Sandstorm     | [Cap'n Proto][capnproto]
| 1995 | ITU-T         | [ASN.1][asn1]
|      | Apache        | [Thrift][thrift]
|      | W3C           | [EXI][exi]
|      |               | XML
|      |               | JSON
|      |               | YAML
|      |               | CSV
|      |               | HDF5
|      |               | SQL
|      |               | [OCaml extprot][extprot]
|      |               | Python Pickle
|      |               | Java Kryo
|      |               | Haskell Binary

Of these options, Thrift seems to suit our needs the best.

[cbor]: https://cbor.io/
[protocol-buffers]: https://developers.google.com/protocol-buffers
[avro]: http://avro.apache.org/
[parquet]: http://parquet.apache.org/
[arrow]: http://arrow.apache.org/
[flatbuffers]: https://google.github.io/flatbuffers/
[messagepack]: https://msgpack.org/
[capnproto]: https://capnproto.org/
[asn1]: https://www.itu.int/en/ITU-T/asn1/Pages/asn1_project.aspx
[thrift]: http://thrift.apache.org/
[exi]: https://www.w3.org/TR/exi/
[extprot]: https://github.com/mfp/extprot
