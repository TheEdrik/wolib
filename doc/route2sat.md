# API representation of hierarchical, deterministic key derivation in PKCS#11 service providers

Visegrady, Tamas ```<tamas@visegrady.ch>```

# Introduction

Protocol-relevant content of HD key-derivation schemes does not
fit the base set of key derivation functions (KDFs) supported by

# Preprocessing before SAT/CNF construction

The primary PKCS#11 service of an HD derivation scheme would be an
extended form on ```DeriveKey()``` [PK31, 5.18.5]. This polymorphic

# Data representation

Our data representation is somewhat redundant, simplifying SAT problem
formulation. We organize variables around (delivery, time unit, vehicle)
tuples:

1. for ```N``` vehicles, use an ```M```-bit, 1-based binary encoding
as index which can represent ```N+``` possibilities; the value is the
index of the vehicle which makes the delivery.

The all-```0``` index is reserved to indicate no delivery. ```M``` is
minimal; we reject ```M```-bit values over ```N+1```.

2. XXX

TODO: would aggregate CNF simplify if all-```1``` was used to indicate
no delivery?

# Auxiliary concepts

In addition to the base ```DeriveKey()``` invocation, a number of
additional concepts need to be represented in PKCS11 for a complete HD

# References

[BCD14]
Benadjila, Calderon, Daubignard: Caml Crush: A PKCS#11 filtering proxy
2014
eprint.iacr.org/2015/063.pdf  [accessed 2023-02-27]

