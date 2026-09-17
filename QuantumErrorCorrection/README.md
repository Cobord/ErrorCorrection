# QuantumErrorCorrection

Lean 4 / Mathlib formalization of the generalized Pauli group, the Clifford automorphism group, and
quasi-local algebras built from them on a finite (or arbitrary) set of qudits, together with
stoquastic Hamiltonians on regions of those qudits.

Both halves are region-indexed *nets*: functors out of `RegionCat X`, the poset of finite
regions of the site set `X`, sending each region to the algebra (resp. cone) of observables
supported there and each inclusion of regions to "act trivially on the new qudits". The target
categories — `GrpInclCat`, `SuperStarAlgCat`, `PointedConeCat`, `PointedConeAlgCat` — are each
bundled with their own explicit morphism type, so that what a net's structure maps must respect
(injectivity, the grading, the distinguished cone) is carried by them as data rather than
checked after the fact.

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
- [`PauliRepresentation.lean`](PauliRepresentation.lean) — `WeylSystem.equiv` identifies the
  abstract Pauli group with its concrete subgroup of `U(d^|Qudits|)`, for any chosen clock/shift
  powers satisfying the Weyl relation and any primitive phase character (`d ≠ 0`). Includes
  computational-basis matrices, constructors from arbitrary complex primitive roots, and
  compatibility with cyclotomic reparameterization and entrywise Galois action.
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
- [`CliffordAutGroup.lean`](CliffordAutGroup.lean) — `PauliGroup.CliffordAutGroup Qudits d`, the subgroup
  of `MulAut (PauliGroup Qudits d)` fixing every phase pointwise. `toCliffordAut` sends Pauli
  elements to inner automorphisms and has the pure phases as its kernel. For a primitive Weyl
  realization with `d > 0`, this abstract group is the unitary normalizer modulo scalar
  unitaries. The module documents the distinction and the dependence of its quotient by
  inner automorphisms on the dimension and phase convention.
- [`PauliCliffordAutFunctor.lean`](PauliCliffordAutFunctor.lean) — Proves `PauliGroup` on a union of
  disjoint regions is a *central product* of the two sub-`PauliGroup`s (`centralProdHom` and its
  surjectivity), uses this to extend a Clifford automorphism of a subregion trivially onto new
  qudits (`cliffordAutExtend`, `cliffordAutInclusionHom`), and assembles
  `PauliGroup.cliffordAutInclusionFunctor : RegionCat X ⥤ GrpInclCat` sending a region to its
  Clifford automorphism group. Also proves `commute_of_disjoint_cliffordAutInclusionHom`, the Clifford analogue
  of `commute_of_disjoint_range`.
- [`PauliCliffordAutQuasiLocalAlgebra.lean`](PauliCliffordAutQuasiLocalAlgebra.lean) — Assembles the
  group algebra of the Clifford automorphism group net into a concrete `QuasiLocalAlgebra` instance, mirroring
  `PauliQuasiLocalAlgebra.lean` with `CliffordAutGroup` in place of `PauliGroup`.
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
  `S.carrier → Fin d` of a region has non-positive off-diagonal entries, so that `exp (-t A)`
  has non-negative entries and the associated quantum Monte Carlo is sign-problem free. Three
  layers:
  - *Conic combinations.* Stoquasticity is an entrywise condition off the diagonal, hence
    preserved by sums and by non-negative (in particular positive) rescalings
    (`isStoquastic_add`, `isStoquastic_smul`, `isStoquastic_sum_smul`): a Hamiltonian built from
    stoquastic local terms is stoquastic. `stoquasticCone` bundles this as a `PointedCone`.
  - *Extension along a region inclusion.* `extendAlongRegion` views a matrix on `S` as one on a
    larger region `T` along a morphism of `RegionCat X`, acting as the identity on the new
    qudits `T \ S` — that is, `A ⊗ 1`. It is functorial (`extendAlongRegion_id`,
    `extendAlongRegion_comp`), preserves stoquasticity (`isStoquastic_extendAlongRegion`), and
    over a commutative `R` is an algebra map (`extendAlongRegionₐ`: `1 ⊗ 1 = 1` and
    `(A ⊗ 1)(B ⊗ 1) = (A B) ⊗ 1`) and not merely linear (`extendAlongRegionₗ`).
  - *The net.* `stoquasticFunctor : RegionCat X ⥤ PointedConeAlgCat R` assembles the two,
    sending a region to its matrix algebra with the stoquastic cone inside it and an inclusion
    to `A ↦ A ⊗ 1`. `stoquasticFunctorₗ` is that net composed with `forgetMul`, valued in
    `PointedConeCat R`.

## Building

```
lake build QuantumErrorCorrection
```
