# Supersymmetric

Lean 4 / Mathlib formalization of Lie `1 | N` superalgebras.

## Contents

- [`Basic.lean`](Basic.lean) — Defines `SuperVectorSpace` (a module with an
  internal `ZMod 2`-grading decomposing it into even and odd parts) and
  `LieSuperAlgebra` (a bracket satisfying graded antisymmetry and the graded
  Jacobi identity on homogeneous elements), together with `Representation`s
  of a Lie superalgebra.
- [`OneN.lean`](OneN.lean) — Over a ring where `2` is invertible, builds the
  `1 | N`-dimensional Lie superalgebra on `Space := 𝕜 × M` from a symmetric
  bilinear form `B` and a skew-adjoint endomorphism `A` on `M` satisfying the
  `OddJacobi` constraint (the `Q,Q,Q` Jacobi identity), and shows this
  recovers a genuine `LieSuperAlgebra` instance.
- [`OneNDichotomy.lean`](OneNDichotomy.lean) — Shows that whenever `3` is not
  a zero divisor and `M` has no zero `SMul`-divisors, the odd Jacobi identity
  forces a dichotomy: `A` and `B` can never both be nonzero. Includes the
  characteristic-`3` counterexample (`char3A`, `char3B`) showing the `3 ≠ 0`
  hypothesis is necessary.
- [`Translation.lean`](Translation.lean) — The translation Lie superalgebra,
  the `A = 0` specialization of the `1 | N` construction, whose only nonzero
  bracket is `[(0,m),(0,n)] = (B m n, 0)`.
- [`SuperFields.lean`](SuperFields.lean) — Bundled smooth maps `ℝ → F` into a
  real normed space, as a building block for superfields.

## Building

```
lake build Supersymmetric
```
