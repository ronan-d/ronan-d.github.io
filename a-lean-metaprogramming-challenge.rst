A Lean metaprogramming challenge
--------------------------------

Lean has a reputation for having really powerful metaprogramming capabilities. I'm particularly interested
in functions that take in inductive types and output something that depends on the definition of the type.

A proof of concept of this would be to write something that does what ``#print T`` does, where ``T`` is an inductive type.

One of the more ambitious idea would be an "automatic zipper generator", that takes in a set of mutually recursive types
and outputs a "zipper" for them.
