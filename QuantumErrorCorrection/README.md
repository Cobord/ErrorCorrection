# QuantumErrorCorrection

Lean 4 / Mathlib formalization of the generalized Pauli group, the Clifford automorphism group, and
quasi-local algebras built from them on a finite (or arbitrary) set of qudits, together with
stoquastic Hamiltonians on regions of those qudits.

On a metric site set, quasi-local algebras form a symmetric monoidal category
`BoundedSpreadCat` whose morphisms are bounded-spread homomorphisms. The tensor product is
*stacking* of systems (the Koszul-signed super tensor product, region by region). Its
automorphisms are the quantum cellular automata, which contain the finite-depth circuits as a
subgroup. QCAs and circuits stack.

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
- [`RegionNbhd.lean`](RegionNbhd.lean) — For a metric site set `X` whose closed balls are
  finite (`FiniteClosedBalls X`, automatic for finite `X` and for proper discrete spaces such as
  `ℤ^d`), `RegionCat.metricNbhd l S` is the `l`-neighborhood of a region, assembled into an
  endofunctor `metricNbhdFunctor l : RegionCat X ⥤ RegionCat X`, together with the natural
  transformations `𝟭 ⟶ N_l`, `N_l ⟶ N_l'` (`l ≤ l'`) and `N_l ⋙ N_l' ⟶ N_(l+l')` (triangle
  inequality).
- [`GrpInclCat.lean`](GrpInclCat.lean) — `GrpInclCat`, the category of groups whose morphisms are
  only the *injective* homomorphisms, so that any functor into it is automatically an isotonic
  net of groups.
- [`Pauli.lean`](Pauli.lean) — `PauliGroup Qudits d`, the generalized (Weyl-Heisenberg) Pauli
  group on a finite set of qudits of dimension `d`, built directly as the central extension of
  symplectic shift/clock exponent vectors by a `ZMod d` phase (no matrices, no roots of unity),
  together with the symplectic form its commutators realize.
- [`PauliRepresentation.lean`](PauliRepresentation.lean) — `WeylSystem.equiv` identifies the
  abstract Pauli group with its concrete subgroup of unitary matrices over any coefficient
  field `k` with `[StarRing k]`, for chosen clock/shift powers satisfying the Weyl relation
  and a primitive unitary phase character (`d ≠ 0`). Includes computational-basis matrices,
  a constructor from a primitive root satisfying `star ω = ω⁻¹`, and compatibility with
  field embeddings, cyclotomic reparameterization, and Galois automorphisms.
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
- [`SuperStarTensor.lean`](SuperStarTensor.lean) — The super tensor product
  `SuperTensor 𝕜 A B` of two super `*`-algebras.
  - The underlying module is `A ⊗[𝕜] B`, and the product is
    `(a ⊗ b)(c ⊗ d) = koszulSign |b| |c| • (ac ⊗ bd)`.
  - The Koszul sign is built in explicitly from `koszulSign`, not taken from Mathlib's
    `GradedTensorProduct`: `ZMod 2`-graded modules carry both the trivial and the Koszul
    symmetric structure, so the sign is a choice.
  - Includes the grading (`a ⊗ b` has parity `|a| + |b|`) and the signed star
    `star (a ⊗ b) = koszulSign |a| |b| • (star a ⊗ star b)`, making it a `SuperStarAlgebra`.
  - Includes the structure maps `map`, `assoc`, `lid`, `rid` and the Koszul braiding `comm`,
    all grading-preserving `*`-algebra maps; the unit is `𝕜`, trivially graded.
  - Also proves that `1` is even in any `SuperStarAlgebra` (`one_mem_grading_zero`).
- [`SuperStarAlgCatMonoidal.lean`](SuperStarAlgCatMonoidal.lean) — `SuperStarAlgCat 𝕜` is a
  `MonoidalCategory` under the super tensor product. Coherence is induced along the faithful
  forgetful functor to `ModuleCat 𝕜` (`Monoidal.induced`). It is also a `SymmetricCategory`
  with the Koszul braiding; the hexagons and symmetry are proved on homogeneous pure tensors.
- [`Stacking.lean`](Stacking.lean) — Stacking quasi-local algebras.
  - `QuasiLocalAlgebra.stack` has local algebras `A(S) ⊗ˢ B(S)`, i.e. its net is the pointwise
    tensor product of nets.
  - Isotony holds when the local algebras are flat `𝕜`-modules (tensor products of injective
    maps stay injective), and the stack is flat again.
  - Microcausality follows from that of the factors via a Koszul sign identity.
  - `stackUnit` is the trivial system: `𝕜` on every region.
- [`BoundedSpreadHom.lean`](BoundedSpreadHom.lean) — `BoundedSpreadHom l 𝒜 𝒜'`, homomorphisms
  of spread at most `l` between quasi-local algebras on a metric site set.
  - These are natural transformations `𝒜.net ⟶ metricNbhdFunctor l ⋙ 𝒜'.net`, sending
    observables on `S` to observables on its `l`-neighborhood (e.g. finite-depth local
    circuits).
  - Identities have spread `0`, spread can be weakened, and spreads add under composition.
  - `BoundedSpreadCat X 𝕜` is the resulting category. Its objects are quasi-local algebras
    with flat local algebras (automatic over a field; needed for stacking). Its morphisms are
    germs of bounded-spread homomorphisms of *any* spread, identified when they agree after
    weakening to a common spread.
  - `HasSpread f l` records the spread of a morphism.
- [`BoundedSpreadMonoidal.lean`](BoundedSpreadMonoidal.lean) — Stacking makes
  `BoundedSpreadCat X 𝕜` a symmetric monoidal category.
  - Morphisms are stacked by representing both at a common spread and tensoring
    componentwise (`tensorBSH`, `stackHom`).
  - The associator, unitors and braiding are those of the functor category of nets, included
    as spread-`0` morphisms (`homOfNet`).
  - Pentagon, triangle, hexagons and symmetry reduce to the net-level ones.
  - Stacking morphisms of spreads `l`, `l'` gives spread `max l l'`.
- [`QCA.lean`](QCA.lean) — Quantum cellular automata: the automorphisms of `BoundedSpreadCat`,
  `QCA A := Aut A` (a group).
  - `QCA.ofInverse` builds one from mutually inverse bounded-spread homomorphisms.
    `QCA.HasSpread` is the light-cone radius: additive under products and preserved by
    inversion.
  - `QCA.circuitSubgroup A` is the subgroup generated by layers (gates of bounded diameter on
    disjoint blocks). It equals the finite-depth circuits (`mem_circuitSubgroup_iff`), and a
    depth-`d`, range-`r` circuit has spread at most `d * r`.
  - Stacking: `QCA.stackMonoidHom : QCA A × QCA B →* QCA (A ⊗ B)` has spread
    `max l l'` for inputs of spreads `l`, `l'`, and maps circuits to circuits
    (`stack_mem_circuitSubgroup`).
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
