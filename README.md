# A Dependently Typed Linear π-Calculus in Agda

DLπ is an Agda formalization of the **linear π-calculus** with
**dependent pairs**. It allows for the modeling of structured
conversations in which processes and types depend on the content of
exchanged messages.

## DLPi

This folder contains the full formalization of DLπ. Below is an
outline of the files and of their purpose. While looking at the
code, use of [Fira Code](https://github.com/tonsky/FiraCode) is
recommended as it contains several ligatures that make the Agda code
much more pleasant to read.

### Primary modules

* [Language.agda](DLPi/Language.agda) Data types for representing
  **terms** and **processes**. Search no further if you're looking
  for `Name`, `Term` and `Process`. This module also includes the
  definition of `Multiplicity`, `Type` and `Context`, as well as the
  `Null` predicate and the `Scale` and `Split` relations for
  multiplicities, types and contexts.
* [Congruence.agda](DLPi/Congruence.agda) Definition of **structural
  pre-congruence** and related type preservation result.
* [Reduction.agda](DLPi/Reduction.agda) Definition of **labelled
  reduction** and corresponding typing preservation result.

### Auxiliary modules

* [Common.agda](DLPi/Common.agda) Some general purpose functions,
  properties and axioms (extensionality).
* [Split.agda](DLPi/Split.agda) Properties of splitting for
  multiplicities, types and contexts.
* [Scale.agda](DLPi/Scale.agda) Properties of scaling for
  multiplicities, types and contexts.
* [Swap.agda](DLPi/Swap.agda) Some auxiliary properties about
  swapping names in a context.
* [Weaken.agda](DLPi/Weaken.agda) Definition of `Weaken`,
  **weakening** and **strengthening** properties for terms and
  processes.
* [Substitution.agda](DLPi/Substitution.agda) Type-preserving
  **substitution** of terms for variables in processes.
* [Lookup.agda](DLPi/Lookup.agda) Proof that a name not occurring in
  a well-typed process has an unrestricted type.
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
* [Results.agda](DLPi/Results.agda) This module collects all the
  **properties** stated in Section 4 of the paper. Compared to their
  formulation in the paper, the statements are slightly differnt
  and/or simpler to account for the fact that terms and processes
  are intrinsically typed.
* [Main.agda](DLPi/Main.agda) Container for a few **examples**, but
  mostly useful as root file that triggers the type checking of
  everything.

## SessionTypes

This folder contains **encoding** functions from (dependent) session
type languages to DLπ types. The folder is organized as follows:

* [Common.agda](SessionTypes/Common.agda) imports the extensionality
  principle and defines the `Type` data type for representing
  **finite DLπ types**.
* [FinLabels](SessionTypes/FinLabels) contains the encoding of
  non-dependent, labeled session types with n-ary branches and
  choices. Labels are elements of the `Fin n` data type.
* [LinearLogic](SessionTypes/LinearLogic) contains the encoding of
  dependent session types *à la* [Toninho, Caires & Pfenning
  2011](https://doi.org/10.1145/2003476.2003499). These session
  types subsume the original non-dependent ones by
  [Honda](https://doi.org/10.1007/3-540-57208-2_35).
* [LabelDependent](SessionTypes/LabelDependent) contains the
  encoding of label-dependent session types defined by [Thiemann &
  Vasconcelos 2020](https://doi.org/10.1145/3371135).

Each subfolder is organized as follows:

* `Types.agda` defines **session types** and auxiliary data types,
  including the notion of bisimilarity used for proving that
  decoding is the inverse of encoding.
* `Encoding.agda` defines a predicate on `Type` that characterizes
  the image of the encoding.
* `Encode.agda` defines the **encoding** function and proves that it
  satisfies the `Encoding` predicate.
* `Decode.agda` defines the **decoding** function.
* `Proofs.agda` contains the proofs that encoding and decoding are
  one the **inverse** of the other modulo bisimilarity.
* `Equalities.agda`, if present, contains examples illustrating
  the fact that the encoding function is **not injective**.

## References

The formalization of DLπ is described in the paper **A Dependently
Typed Linear π-Calculus in Agda**, which appears in the proceedings
of [PPDP 2020](http://www.cse.chalmers.se/~abela/ppdp20/). A
preprint version of the paper can be found
[here](http://hdl.handle.net/2318/1739403).
