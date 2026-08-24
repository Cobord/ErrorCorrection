# ErrorCorrection

Lean 4 / Mathlib formalization of linear error-correcting codes, and a
graph-theoretic structure ("chromotopology") built from them.

## Contents

- [`LinearECC.lean`](LinearECC.lean) — Core theory of linear codes `[n, k, d]_q`:
  `k`-dimensional subspaces of `F_q^n`, with Hamming weight/distance, the
  bilinear dot product and dual code, evenness/doubly-evenness, extension by
  an overall parity bit, and the quotient of `F_q^n` by a code's coordinate
  shifts (`qi`).
- [`LinearECC_Binary.lean`](LinearECC_Binary.lean) — Specializes to `F_2` and
  builds concrete families: Hadamard codes (including the Sylvester-type
  construction and its Hadamard-matrix property) and Hamming codes, with
  their parameters and minimum-distance bounds.
- [`CommutingInvolutions.lean`](CommutingInvolutions.lean) — From a family of
  pairwise-commuting involutions `q : Fin N → Equiv.Perm V`, builds the
  induced `MulAction` of `(ZMod 2)^N` on `V`.
- [`Chromotopology.lean`](Chromotopology.lean) — A chromotopology is a simple
  graph whose vertices are colored by `Fq` and which has `N` differently
  colored edges at each vertex, such that the edges of any two colors form a
  disjoint union of 4-cycles. Shows that quotienting `F_q^n` by the
  coordinate-shift action of a suitable `LinearECC` (no weight-1 codewords,
  and no codewords of the form `e_i - e_j`) produces such a chromotopology.

## Building

```
lake build ErrorCorrection
```
