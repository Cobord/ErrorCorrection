# AlgebraicCategories

The operator-algebraic categories that the region-indexed nets of
[`QuantumErrorCorrection/`](../README.md) take values in, together with their monoidal structure
and base change of coefficients. Nothing here refers to sites, regions or qudits.

Each category is bundled with its own explicit morphism type, so that what a net's structure maps
must respect (the grading, injectivity, the distinguished cone, flatness) is carried by them as
data rather than checked after the fact.

## Contents

- [`StarAlgCat.lean`](StarAlgCat.lean) — `StarAlgCat 𝕜`, the category of `𝕜`-algebras with a
  `star` conjugate-linear over the base `*`-ring `𝕜`, and `*`-algebra homomorphisms.
- [`SuperStarAlgCat.lean`](SuperStarAlgCat.lean) — `SuperStarAlgebra 𝕜 A`, a `ZMod 2`-graded
  `*`-algebra (multiplication adds parities, `star` preserves them), and `SuperStarAlgCat 𝕜`, the
  category of these with grading-preserving `*`-algebra homomorphisms.
  `StarAlgCat.toPurelyEvenSuperStarAlgCat` is the fully faithful functor viewing an ungraded
  `*`-algebra as concentrated in degree `0`.
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
- [`FlatCommStarRingCat.lean`](FlatCommStarRingCat.lean) — `FlatCommStarRingCat`, the category of
  commutative `*`-rings whose morphisms are ring homomorphisms commuting with `star` and making
  the target flat over the source (`RingHom.Flat`). These are the coefficient changes along
  which extending scalars keeps a net of local `*`-algebras isotonic. Identities and
  composites stay flat (`RingHom.Flat.id`, `RingHom.Flat.comp`). It is symmetric monoidal under
  `⊗[ℤ]` with unit `ℤ`: tensor products of flat maps are flat (`RingHom.Flat.tensorProductMap`),
  and the structure is induced from `CommAlgCat ℤ` through the faithful forgetful functor.
- [`SuperStarBaseChange.lean`](SuperStarBaseChange.lean) — Base change of super `*`-algebras
  along an `R`-algebra `S` whose star is compatible with the scalars.
  - `S ⊗[R] A` is a super `*`-algebra over `S`, graded by `(A_i).baseChange S`.
  - Grading-preserving `*`-homomorphisms base change (`baseChangeHom`). Injectivity is preserved
    when `S` is flat over `R`.
  - Base change commutes with the super tensor product (`stackBaseChange`) and sends the unit to
    the unit (`unitBaseChange`).
  - Base change along the identity is trivial (`lidBaseChange : R ⊗[R] A ≃ A`), and along a
    composite it is iterated base change
    (`cancelBaseChangeStar : T ⊗[S] (S ⊗[R] A) ≃ T ⊗[R] A`).
  - Along a morphism of `FlatCommStarRingCat` this gives a functor
    `SuperStarAlgCat.baseChange σ : SuperStarAlgCat R ⥤ SuperStarAlgCat S` preserving
    injectivity of morphisms.
- [`GroupAlgebraStar.lean`](GroupAlgebraStar.lean) — Makes the group algebra `MonoidAlgebra 𝕜 G`
  into a (trivially graded) `SuperStarAlgebra 𝕜`, with `star` extending group inversion.
  `SuperStarAlgInclCat 𝕜` is the category of super `*`-algebras with *injective*
  grading-preserving `*`-homomorphisms, and `groupAlgebraFunctor : GrpInclCat ⥤
  SuperStarAlgInclCat 𝕜` turns injective group homomorphisms into such maps.
- [`TrivSqZeroExtStar.lean`](TrivSqZeroExtStar.lean) — The square-zero extension
  `TrivSqZeroExt R M = R ⊕ M` as a commutative `*`-algebra, with componentwise `star`, and
  `starMap` turning a star-compatible linear map into a `*`-algebra map. Over a reduced ring every
  algebra map `R ⊕ M → R ⊕ N` sends `M` into `N` (its image squares to zero). So it is `map` of
  its `linearPart`, and taking linear parts is functorial.
- [`PointedConeCat.lean`](PointedConeCat.lean) — `PointedConeCat R`, the category of modules over
  an ordered ring `R` equipped with a distinguished `PointedCone R`, whose morphisms are the
  `R`-linear maps carrying one cone into the other (so a functor into it is a net of cones). The
  explicit name avoids collision with `CategoryTheory.Limits.Cone`.
- [`PointedConeAlgCat.lean`](PointedConeAlgCat.lean) — `PointedConeAlgCat R`, the algebra-valued
  refinement of `PointedConeCat R`: objects are `R`-`*`-algebras with a distinguished
  `PointedCone R` and morphisms are cone-preserving `*`-algebra homomorphisms. The intended
  target for the stoquastic net, whose objects are matrix algebras and whose structure maps
  `A ↦ A ⊗ 1` are unital algebra maps, not merely linear ones. The faithful forgetful functors
  `forgetMul : PointedConeAlgCat R ⥤ PointedConeCat R` and `forgetCone : PointedConeAlgCat R ⥤
  StarAlgCat R` discard the multiplication and the cone respectively.

## Building

```
lake build QuantumErrorCorrection
```
