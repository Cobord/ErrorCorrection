/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Commutative groups with injective homomorphisms, symmetric monoidal under products

`CommGrpInclCat` has commutative groups as objects and *injective* group homomorphisms as
morphisms (the commutative analogue of `GrpInclCat`). Products of injective homomorphisms are
injective, so the product `G × H` makes it a symmetric monoidal category. The unit is the
trivial group; the associator, unitors and braiding are the canonical isomorphisms of
products. All coherence laws hold pointwise by definition.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

/-- An object of `CommGrpInclCat`: a commutative group. -/
structure CommGrpInclCat : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [commGroup : CommGroup carrier]

namespace CommGrpInclCat

attribute [instance] CommGrpInclCat.commGroup

instance : CoeSort CommGrpInclCat (Type u) := ⟨carrier⟩

/-- Bundle a `CommGroup` as a `CommGrpInclCat` object. -/
abbrev of (G : Type u) [CommGroup G] : CommGrpInclCat := ⟨G⟩

/-- Morphisms `G ⟶ H` are exactly the injective group homomorphisms. -/
instance : Category CommGrpInclCat.{u} where
  Hom G H := {f : G.carrier →* H.carrier // Function.Injective f}
  id G := ⟨MonoidHom.id G.carrier, Function.injective_id⟩
  comp f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

theorem hom_ext {G H : CommGrpInclCat.{u}} {f g : G ⟶ H} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (MonoidHom.ext h)

/-- A group isomorphism is an isomorphism of `CommGrpInclCat`. -/
def isoOfMulEquiv {G H : CommGrpInclCat.{u}} (e : G ≃* H) : G ≅ H where
  hom := ⟨e.toMonoidHom, e.injective⟩
  inv := ⟨e.symm.toMonoidHom, e.symm.injective⟩
  hom_inv_id := hom_ext e.symm_apply_apply
  inv_hom_id := hom_ext e.apply_symm_apply

/-! ### The symmetric monoidal structure -/

/-- The product of two injective homomorphisms. -/
def prodHom {G G' H H' : CommGrpInclCat.{u}} (f : G ⟶ G') (g : H ⟶ H') :
    of (G × H) ⟶ of (G' × H') :=
  ⟨f.1.prodMap g.1, f.2.prodMap g.2⟩

/-- `1 × G ≃ G`. -/
def unitProdEquiv (G : Type u) [CommGroup G] : PUnit.{u + 1} × G ≃* G where
  toFun := Prod.snd
  invFun g := (1, g)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- `G × 1 ≃ G`. -/
def prodUnitEquiv (G : Type u) [CommGroup G] : G × PUnit.{u + 1} ≃* G where
  toFun := Prod.fst
  invFun g := (g, 1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

instance monoidalCategoryStruct : MonoidalCategoryStruct CommGrpInclCat.{u} where
  tensorObj G H := of (G × H)
  whiskerLeft G _ _ g := prodHom (𝟙 G) g
  whiskerRight f H := prodHom f (𝟙 H)
  tensorHom := prodHom
  tensorUnit := of PUnit
  associator G H K := isoOfMulEquiv (MulEquiv.prodAssoc : (G × H) × K ≃* G × (H × K))
  leftUnitor G := isoOfMulEquiv (unitProdEquiv G)
  rightUnitor G := isoOfMulEquiv (prodUnitEquiv G)

/-- Commutative groups with injective homomorphisms form a monoidal category under products. -/
instance monoidalCategory : MonoidalCategory CommGrpInclCat.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => hom_ext fun _ => rfl)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => hom_ext fun _ => rfl)
    (associator_naturality := fun _ _ _ => hom_ext fun _ => rfl)
    (leftUnitor_naturality := fun _ => hom_ext fun _ => rfl)
    (rightUnitor_naturality := fun _ => hom_ext fun _ => rfl)
    (pentagon := fun _ _ _ _ => hom_ext fun _ => rfl)
    (triangle := fun _ _ => hom_ext fun _ => rfl)

/-- The symmetric structure: swapping the factors of a product. -/
instance symmetricCategory : SymmetricCategory CommGrpInclCat.{u} where
  braiding G H := isoOfMulEquiv (MulEquiv.prodComm : G × H ≃* H × G)
  braiding_naturality_right _ _ _ _ := hom_ext fun _ => rfl
  braiding_naturality_left _ _ := hom_ext fun _ => rfl
  hexagon_forward _ _ _ := hom_ext fun _ => rfl
  hexagon_reverse _ _ _ := hom_ext fun _ => rfl
  symmetry _ _ := hom_ext fun _ => rfl

end CommGrpInclCat
