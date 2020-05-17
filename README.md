# A Dependently-Typed Linear π-Calculus in Agda

DLπ is an Agda formalization of the **linear π-calculus** with
**dependent pairs**. It allows for the modeling of structured
conversations in which processes and types depend on the content of
exchanged messages.

## DLPi

This folder contains the full formalization of DLπ. Here is an
outline of the files and of their purpose:

* [Language.agda](DLPi/Language.agda) Data types for representing
  `Term`s and `Process`es.

## Encodings

This folder contains encoding functions from three representative
session type languages, two of which use dependent types explicitly,
to DLπ types. Decoding functions are also provided in all cases.
