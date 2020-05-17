# A Dependently-Typed Linear π-Calculus in Agda

DLπ is an Agda formalization of the **linear π-calculus** with
**dependent pairs**. It allows for the modeling of structured
conversations in which processes and types depend on the content of
exchanged messages.

## DLPi

This folder contains the full formalization of DLπ. Here is an
outline of the files and of their purpose:

* [Common.agda](DLPi/Common.agda) Some general purpose functions,
  properties and axioms (extensionality). These are very likely to
  be found somewhere in the standard library, but so far we've been
  too lazy to look them up.
* [Context.agda](DLPi/Context.agda) Definition of **contexts** and
  related properties, including `CNull`, `CScale` and `CSplit`.
* [HasType.agda](DLPi/HasType.agda) Proof that a name not occurring
  in a well-typed process has a type that satisfies `TNull`, hence
  it is unrestricted.
* [Language.agda](DLPi/Language.agda) Data types for representing
  **terms** and **processes**. Look no further if you want to see
  `Var`, `Term` and `Process`.
* [Macros.agda](DLPi/Macros.agda) Some syntactic sugar for pair
  splitting and conditional processes. Just for fun, not used
  anywhere.
* [Main.agda](DLPi/Main.agda) Container for a few **examples**, but
  mostly useful as root file that requires the type checking of
  everything.
* [Multiplicity.agda](DLPi/Multiplicity.agda) Representation of
  **multiplicities** and their properties, including `MScale` and
  `MSplit`.
* [PrefixNormalForm.agda](DLPi/PrefixNormalForm.agda) Proof that
  every process can be rewritten in prefix-normal-form using
  structural pre-congruence.
* [PrefixedBy.agda](DLPi/PrefixedBy.agda) Predicate that holds when
  a process has an unguarded input/output prefix for a given channel.
* [ReducibleNormalForm.agda](DLPi/ReducibleNormalForm.agda) Proof
  that every process with both an input and an output prefix for a
  given channel can be rewritten in reducible normal form using
  structural pre-congruence. In this normal form, the two prefixes
  sit next to each other, so the process is ready to reduce.
* [Scaling.agda](DLPi/Scaling.agda) Some auxiliary properties on
  scaling.
* [Semantics.agda](DLPi/Semantics.agda) The **operational
  semantics** of DLπ, including structural pre-congruence and
  labelled reduction. Both definitions embed the property that they
  preserve typing.
* [Substitution.agda](DLPi/Substitution.agda) **Substitution** of
  terms for variables in processes.
* [Swapping.agda](DLPi/Swapping.agda) Some auxiliary properties on
  swapping names in a context.
* [Type.agda](DLPi/Type.agda) Definition of DLπ **types** and their
  properties, including `TNull`, `TScale` and `TSplit`.
* [Weakening.agda](DLPi/Weakening.agda) Definition of `Weaken` and
  weakening property for terms and processes.

## Encodings

This folder contains encoding functions from three representative
session type languages, two of which use dependent types explicitly,
to DLπ types. Decoding functions are also provided in all cases.
