
# Lessons learned

## de Brujin indexes in variable types

* Since the same variables may have different types, and it is often
  the case that it's necessary to refer within the same type to
  *different* occurrences of the same variables, it is handy to have
  the index of the variable in the type. See `sync` function in
  `Semantics.agda`
* The alternative is to carry around equality proofs on variables
  indexes, which is cumbersome and lets Agda discover fewer things
  about those variables.

## Indexed families

* Easier to work with compared to functions, but they are (partial)
  functions and still cumbersome.

## Splitting

* Better to split contexts so that they keep the same length, or
  else we would have problems swapping elements. However, sigma
  types are difficult to split, so we treat these linear and instead
  of splitting them we combine them with the trivial (unit)
  type.
* Multiplicities are easier to deal with compared to the usual
  polarities of the linear pi calculus.

## Irrefutable patterns

* Irrefutable patterns along with Σ types they are invaluable in the
  formalization, especially for dealing with relations
  (e.g. `CSplit`) for which elements cannot be computed by functions
* Not documented anywhere except mentioned
  [here](https://lists.chalmers.se/pipermail/agda/2019/010854.html)
  and [here](https://github.com/agda/agda/issues/2298)
* Is there a better alternative?
* It is frustrating not being able to give types to the components
  of an irrefutable pattern

Mystery solved:
* Irrefutable patterns are in fact [**record
  patterns**](https://agda.readthedocs.io/en/v2.6.0.1/language/let-and-where.html#let-binding-record-patterns)
* Σ types are defined as a
  [record](https://agda.github.io/agda-stdlib/Agda.Builtin.Sigma.html)

# Questions

* ["one rarely uses Sigma types in
  Agda"](https://lists.chalmers.se/pipermail/agda/2010/002367.html)
  why?

# Properties that could be proved

1. Existence and uniqueness of **normal form** (up to structural
   precongruence). A process is in normal form if

   P = New ... New (Q1 | Q2 | ... | Qn)

   and all Qi are **guarded** (or replicated guarded processes).
2. Confluence of structural precongruence <=: if P <= P1 and P <=
   P2, then there exists Q such that P1 <= Q and P2 <= Q
3. Communication on linear channels is deterministic: if P ~~x~> P1
   and P ~~x~> P2 where x is a linear channel, then there exists Q
   such that P1 <= Q and P2 <= Q.
4. Partial confluence of reduction, when one reduction is a
   communication on a linear channel: if P ~~x~> P1 and P ~~l~> P2
   where x is a linear channel, then there exists Q such that either
   P1 <= Q and P2 <= Q or P1 ~~l~> Q and P2 ~~x~> Q.

