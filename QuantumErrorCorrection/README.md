# QuantumErrorCorrection

Lean 4 / Mathlib formalization of the generalized Pauli group, the Clifford group, and
quasi-local algebras built from them on a finite (or arbitrary) set of qudits.

## Contents

- [`RegionCat.lean`](RegionCat.lean) — `RegionCat X`, the category `B(X)` of finite subsets
  ("regions") of a site set `X` ordered by inclusion, bundled as its own structure with its own
  `Category` instance (morphisms are exactly the propositional witnesses of `S.carrier ⊆
  T.carrier`). The indexing category for every region-net construction below.
- [`GrpInclCat.lean`](GrpInclCat.lean) — `GrpInclCat`, the category of groups whose morphisms are
  only the *injective* homomorphisms, so that any functor into it is automatically an isotonic
  net of groups.
- [`Pauli.lean`](Pauli.lean) — `PauliGroup Qudits d`, the generalized (Weyl-Heisenberg) Pauli
  group on a finite set of qudits of dimension `d`, built directly as the central extension of
  symplectic shift/clock exponent vectors by a `ZMod d` phase (no matrices, no roots of unity),
  together with the symplectic form its commutators realize.
- [`PauliFunctor.lean`](PauliFunctor.lean) — `PauliGroup.quditInclusionFunctor : RegionCat X ⥤
  GrpInclCat`, sending a region to its Pauli group and a region inclusion to "extend by the
  identity on the new qudits"; `commute_of_disjoint_range` shows Pauli operators on disjoint
  regions always commute.
- [`GroupAlgebraStar.lean`](GroupAlgebraStar.lean) — Makes the group algebra `MonoidAlgebra 𝕜 G`
  into a (trivially graded) `SuperStarAlgebra 𝕜`, with `star` extending group inversion, and
  functorially turns an injective group homomorphism into an injective, grading-preserving
  `*`-algebra homomorphism.
- [`QuasiLocalAlgebra.lean`](QuasiLocalAlgebra.lean) — The abstract notion of a *quasi-local
  superalgebra*: a functor `RegionCat X ⥤ SuperStarAlgCat 𝕜` (a net of `ZMod 2`-graded
  `*`-algebras) satisfying isotony and the disjoint super-commuting (microcausality) condition,
  with Koszul sign.
- [`PauliQuasiLocalAlgebra.lean`](PauliQuasiLocalAlgebra.lean) — Assembles the group algebra of
  the Pauli group net into a concrete `QuasiLocalAlgebra` instance; super-commutation lifts
  `commute_of_disjoint_range` from individual group elements to arbitrary linear combinations by
  bilinearity.
- [`CliffordGroup.lean`](CliffordGroup.lean) — `PauliGroup.CliffordGroup Qudits d`, the subgroup
  of `MulAut (PauliGroup Qudits d)` fixing every phase pointwise; conjugation by any Pauli
  element is always Clifford (`toClifford`).
- [`PauliCliffordFunctor.lean`](PauliCliffordFunctor.lean) — Proves `PauliGroup` on a union of
  disjoint regions is a *central product* of the two sub-`PauliGroup`s (`centralProdHom` and its
  surjectivity), uses this to extend a Clifford automorphism of a subregion trivially onto new
  qudits (`cliffordExtend`, `cliffordInclusionHom`), and assembles
  `PauliGroup.cliffordInclusionFunctor : RegionCat X ⥤ GrpInclCat` sending a region to its
  Clifford group. Also proves `commute_of_disjoint_cliffordInclusionHom`, the Clifford analogue
  of `commute_of_disjoint_range`.
- [`PauliCliffordQuasiLocalAlgebra.lean`](PauliCliffordQuasiLocalAlgebra.lean) — Assembles the
  group algebra of the Clifford group net into a concrete `QuasiLocalAlgebra` instance, mirroring
  `PauliQuasiLocalAlgebra.lean` with `CliffordGroup` in place of `PauliGroup`.
- [`PointedConeCat.lean`](PointedConeCat.lean) — `PointedConeCat R`, the category of modules over
  an ordered ring `R` equipped with a distinguished `PointedCone R`, whose morphisms are the
  `R`-linear maps carrying one cone into the other (so a functor into it is a net of cones). The
  explicit name avoids collision with `CategoryTheory.Limits.Cone`.
- [`PointedConeAlgCat.lean`](PointedConeAlgCat.lean) — `PointedConeAlgCat R`, the algebra-valued
  refinement of `PointedConeCat R`: objects are `R`-algebras with a distinguished `PointedCone R`
  and morphisms are cone-preserving `R`-*algebra* homomorphisms. The intended target for the
  stoquastic net, whose objects are matrix algebras and whose structure maps `A ↦ A ⊗ 1` are
  unital algebra maps, not merely linear ones. `forgetMul : PointedConeAlgCat R ⥤
  PointedConeCat R` is the (faithful) forgetful functor discarding the multiplication.
- [`Stoquastic.lean`](Stoquastic.lean) — `isStoquastic`: a matrix on the qudit configurations
  `S.carrier → Fin d` of a region has non-positive off-diagonal entries (so the associated
  quantum Monte Carlo is sign-problem free). Stoquastic matrices on a region form a convex cone
  (`isStoquastic_add`, `isStoquastic_smul`, `isStoquastic_sum_smul`: conic — in particular
  positive — combinations of stoquastic terms stay stoquastic). `extendAlongRegion` views such a
  matrix on a larger
  region along a morphism of `RegionCat X`, acting as the identity on the new qudits `T \ S`
  (i.e. `A ⊗ 1`), functorially (`extendAlongRegion_id`, `extendAlongRegion_comp`); by
  `isStoquastic_extendAlongRegion` this preserves stoquasticity. Over a commutative `R` the
  extension is an algebra map (`extendAlongRegionₐ`: `1 ⊗ 1 = 1` and
  `(A ⊗ 1)(B ⊗ 1) = (A B) ⊗ 1`) and not just linear (`extendAlongRegionₗ`), so these assemble
  into `stoquasticFunctor : RegionCat X ⥤ PointedConeAlgCat R`, the net of stoquastic cones in
  the region matrix algebras; `stoquasticFunctorₗ` is the same net composed with `forgetMul`,
  valued in `PointedConeCat R`.

## Building

```
lake build QuantumErrorCorrection
```
