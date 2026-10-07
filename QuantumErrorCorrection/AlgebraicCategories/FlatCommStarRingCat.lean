/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative star rings with flat star ring maps

`FlatCommStarRingCat` is the category whose objects are commutative `*`-rings and whose morphisms
`σ : 𝕜 ⟶ 𝕜'` are ring homomorphisms that commute with `star` and make `𝕜'` a flat `𝕜`-module
(`RingHom.Flat`).

These are the coefficient changes along which extending scalars behaves well for nets of local
algebras:
* compatibility with `star` makes `𝕜' ⊗_𝕜 A` a `*`-algebra again;
* flatness makes `𝕜' ⊗_𝕜 -` preserve injectivity, and so preserves isotony.

It is a category because the identity is flat (`RingHom.Flat.id`) and flatness is transitive
(`RingHom.Flat.comp`). Compatibility with `star` is likewise preserved by identities and
composition. Mathlib has no bundled unital star ring homomorphism, so the morphisms are their
own structure `FlatCommStarRingCat.Hom`: a `RingHom` together with the two properties.
-/

@[expose] public section

open CategoryTheory

universe u

/-- A commutative `*`-ring, as an object of the category of commutative `*`-rings with flat
star ring maps. -/
structure FlatCommStarRingCat : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [starRing : StarRing carrier]

namespace FlatCommStarRingCat

instance : CoeSort FlatCommStarRingCat.{u} (Type u) := ⟨carrier⟩

attribute [instance] commRing starRing

/-- Bundle a commutative `*`-ring as an object of `FlatCommStarRingCat`. -/
abbrev of (R : Type u) [CommRing R] [StarRing R] : FlatCommStarRingCat.{u} := ⟨R⟩

/-- A morphism `R ⟶ S`: a ring homomorphism commuting with `star` and making `S` a flat
`R`-module. -/
@[ext]
structure Hom (R S : FlatCommStarRingCat.{u}) where
  /-- The underlying ring homomorphism. -/
  hom : R →+* S
  /-- The ring homomorphism commutes with `star`. -/
  map_star : ∀ r : R, hom (star r) = star (hom r)
  /-- The target is flat over the source. -/
  flat : hom.Flat

instance : Category FlatCommStarRingCat.{u} where
  Hom := Hom
  id R := ⟨RingHom.id R, fun _ => rfl, RingHom.Flat.id R⟩
  comp f g := ⟨g.hom.comp f.hom, fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply, f.map_star, g.map_star],
    RingHom.Flat.comp f.flat g.flat⟩
  id_comp f := Hom.ext (RingHom.comp_id f.hom)
  comp_id f := Hom.ext (RingHom.id_comp f.hom)
  assoc f g h := Hom.ext (RingHom.comp_assoc f.hom g.hom h.hom).symm

@[ext] theorem hom_ext {R S : FlatCommStarRingCat.{u}} {f g : R ⟶ S} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h

/-- Build a morphism from a star-compatible flat ring homomorphism. -/
abbrev ofHom {R S : Type u} [CommRing R] [StarRing R] [CommRing S] [StarRing S] (σ : R →+* S)
    (hσ : ∀ r : R, σ (star r) = star (σ r)) (hflat : σ.Flat) : of R ⟶ of S :=
  ⟨σ, hσ, hflat⟩

@[simp] theorem id_hom (R : FlatCommStarRingCat.{u}) : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

@[simp] theorem comp_hom {R S T : FlatCommStarRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

theorem hom_star {R S : FlatCommStarRingCat.{u}} (f : R ⟶ S) (r : R) :
    f.hom (star r) = star (f.hom r) :=
  f.map_star r

theorem hom_flat {R S : FlatCommStarRingCat.{u}} (f : R ⟶ S) : f.hom.Flat :=
  f.flat

/-! ### The symmetric monoidal structure: tensor product over `ℤ` -/

noncomputable section Monoidal

open MonoidalCategory TensorProduct

section StarLemmas

variable {A B C A' B' : Type*} [CommRing A] [StarRing A] [CommRing B] [StarRing B] [CommRing C]
  [StarRing C] [CommRing A'] [StarRing A'] [CommRing B'] [StarRing B']

/-- Star ring maps tensor to a star ring map. -/
theorem tensorMap_star (σ : A →+* A') (τ : B →+* B') (hσ : ∀ a, σ (star a) = star (σ a))
    (hτ : ∀ b, τ (star b) = star (τ b)) (x : A ⊗[ℤ] B) :
    Algebra.TensorProduct.map σ.toIntAlgHom τ.toIntAlgHom (star x) =
      star (Algebra.TensorProduct.map σ.toIntAlgHom τ.toIntAlgHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show σ (star a) ⊗ₜ[ℤ] τ (star b) = star (σ a) ⊗ₜ[ℤ] star (τ b)
    rw [hσ, hτ]
  | add x y hx hy => rw [star_add, map_add, hx, hy, map_add, star_add]

theorem tensorAssoc_star : ∀ x, Algebra.TensorProduct.assoc ℤ ℤ ℤ A B C (star x) =
      star (Algebra.TensorProduct.assoc ℤ ℤ ℤ A B C x) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add y y' hy hy' =>
      rw [TensorProduct.add_tmul, star_add, map_add, hy, hy', map_add, star_add]
  | add x y hx hy => rw [star_add, map_add, hx, hy, map_add, star_add]

theorem tensorLid_star (x : ℤ ⊗[ℤ] A) :
    Algebra.TensorProduct.lid ℤ A (star x) = star (Algebra.TensorProduct.lid ℤ A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n a => rw [TensorProduct.star_tmul, Algebra.TensorProduct.lid_tmul,
      Algebra.TensorProduct.lid_tmul, star_trivial, star_zsmul]
  | add x y hx hy => rw [star_add, map_add, hx, hy, map_add, star_add]

theorem tensorRid_star (x : A ⊗[ℤ] ℤ) :
    Algebra.TensorProduct.rid ℤ ℤ A (star x) = star (Algebra.TensorProduct.rid ℤ ℤ A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => rw [TensorProduct.star_tmul, Algebra.TensorProduct.rid_tmul,
      Algebra.TensorProduct.rid_tmul, star_trivial, star_zsmul]
  | add x y hx hy => rw [star_add, map_add, hx, hy, map_add, star_add]

theorem tensorComm_star (x : A ⊗[ℤ] B) :
    Algebra.TensorProduct.comm ℤ A B (star x) = star (Algebra.TensorProduct.comm ℤ A B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [star_add, map_add, hx, hy, map_add, star_add]

end StarLemmas

/-- A star-compatible ring isomorphism is an isomorphism of `FlatCommStarRingCat`: bijective ring
maps are flat. -/
def isoOfStarRingEquiv {R S : FlatCommStarRingCat.{u}} (e : R ≃+* S)
    (he : ∀ r : R, e (star r) = star (e r)) : R ≅ S where
  hom := ⟨e.toRingHom, he, RingHom.Flat.of_bijective e.bijective⟩
  inv := ⟨e.symm.toRingHom, fun s => by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e.symm_apply_eq, he,
        RingEquiv.apply_symm_apply],
    RingHom.Flat.of_bijective e.symm.bijective⟩
  hom_inv_id := hom_ext (RingHom.ext e.symm_apply_apply)
  inv_hom_id := hom_ext (RingHom.ext e.apply_symm_apply)

variable {R R' S S' T : FlatCommStarRingCat.{0}}

/-- The forgetful functor to commutative `ℤ`-algebras. -/
def forgetToCommAlgCat : FlatCommStarRingCat.{0} ⥤ CommAlgCat.{0} ℤ where
  obj R := CommAlgCat.of ℤ R
  map σ := CommAlgCat.ofHom σ.hom.toIntAlgHom

instance : forgetToCommAlgCat.Faithful where
  map_injective h := hom_ext (RingHom.ext fun x => congrArg (fun φ => φ.hom x) h)

/-- The tensor product of two morphisms. -/
def tensorHomZ (σ : R ⟶ R') (τ : S ⟶ S') :
    of (R ⊗[ℤ] S) ⟶ of (R' ⊗[ℤ] S') :=
  ⟨(Algebra.TensorProduct.map σ.hom.toIntAlgHom τ.hom.toIntAlgHom).toRingHom,
    tensorMap_star σ.hom τ.hom σ.map_star τ.map_star, RingHom.Flat.tensorProductMap σ.flat τ.flat⟩

instance monoidalCategoryStruct : MonoidalCategoryStruct FlatCommStarRingCat.{0} where
  tensorObj R S := of (R ⊗[ℤ] S)
  whiskerLeft R _ _ τ := tensorHomZ (𝟙 R) τ
  whiskerRight σ S := tensorHomZ σ (𝟙 S)
  tensorHom := tensorHomZ
  tensorUnit := of ℤ
  associator R S T :=
    isoOfStarRingEquiv (Algebra.TensorProduct.assoc ℤ ℤ ℤ R S T).toRingEquiv tensorAssoc_star
  leftUnitor R := isoOfStarRingEquiv (Algebra.TensorProduct.lid ℤ R).toRingEquiv tensorLid_star
  rightUnitor R :=
    isoOfStarRingEquiv (Algebra.TensorProduct.rid ℤ ℤ R).toRingEquiv tensorRid_star

/-- The forgetful functor preserves all the monoidal data on the nose. -/
def inducingData : Monoidal.InducingFunctorData forgetToCommAlgCat where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq _ _ _ _ := CommAlgCat.hom_ext (AlgHom.toLinearMap_injective
    (TensorProduct.ext' fun _ _ => rfl))
  whiskerRight_eq _ _ := CommAlgCat.hom_ext (AlgHom.toLinearMap_injective
    (TensorProduct.ext' fun _ _ => rfl))
  tensorHom_eq _ _ := CommAlgCat.hom_ext (AlgHom.toLinearMap_injective
    (TensorProduct.ext' fun _ _ => rfl))
  εIso := Iso.refl _
  associator_eq _ _ _ := CommAlgCat.hom_ext (AlgHom.toLinearMap_injective
    (TensorProduct.ext_threefold fun _ _ _ => rfl))
  leftUnitor_eq _ := CommAlgCat.hom_ext (AlgHom.toLinearMap_injective
    (TensorProduct.ext' fun _ _ => rfl))
  rightUnitor_eq _ := CommAlgCat.hom_ext (AlgHom.toLinearMap_injective
    (TensorProduct.ext' fun _ _ => rfl))

/-- Commutative `*`-rings with flat star ring maps form a monoidal category under `⊗[ℤ]`. -/
instance monoidalCategory : MonoidalCategory FlatCommStarRingCat.{0} :=
  Monoidal.induced forgetToCommAlgCat inducingData

/-- The forgetful functor to `CommAlgCat ℤ` is monoidal. -/
instance forgetToCommAlgCatMonoidal : forgetToCommAlgCat.Monoidal :=
  (Monoidal.fromInducedCoreMonoidal forgetToCommAlgCat inducingData).toMonoidal

/-- The swap of tensor factors. -/
def braidingZ (R S : FlatCommStarRingCat.{0}) : R ⊗ S ≅ S ⊗ R :=
  isoOfStarRingEquiv (Algebra.TensorProduct.comm ℤ R S).toRingEquiv tensorComm_star

/-- The monoidal structure is braided by swapping tensor factors. -/
instance braidedCategory : BraidedCategory FlatCommStarRingCat.{0} :=
  .ofFaithful forgetToCommAlgCat braidingZ fun _ _ =>
    CommAlgCat.hom_ext (AlgHom.toLinearMap_injective (TensorProduct.ext' fun _ _ => rfl))

/-- The braiding is symmetric. -/
instance symmetricCategory : SymmetricCategory FlatCommStarRingCat.{0} where
  symmetry R S := hom_ext (RingHom.ext fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rfl
    | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy)))

end Monoidal

end FlatCommStarRingCat
