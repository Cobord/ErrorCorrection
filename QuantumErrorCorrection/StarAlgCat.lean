/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of `*`-algebras

`StarAlgCat 𝕜` has as objects `𝕜`-algebras with a `star` that is conjugate-linear over the base
`*`-ring `𝕜` (`StarModule 𝕜`), and as morphisms `*`-algebra homomorphisms. Mathlib has no
bundled category of `*`-algebras, so this is its own structure with its own `Category`
instance, like `RegionCat` and `PointedConeCat`.

It sits between `PointedConeAlgCat` (which forgets its cone to it) and `SuperStarAlgCat` in
`QuasiLocalAlgebra.lean` (which receives it as the purely even super `*`-algebras). It lives in
its own module-style file so that both can import it.
-/

@[expose] public section

open CategoryTheory

universe u

/-- The bundled category of `*`-algebras over a fixed base `*`-ring `𝕜`. -/
public structure StarAlgCat (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜] : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [ring : Ring carrier]
  [starRing : StarRing carrier]
  [algebra : Algebra 𝕜 carrier]
  [starModule : StarModule 𝕜 carrier]

namespace StarAlgCat

variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]

attribute [instance] ring starRing algebra starModule

public instance : CoeSort (StarAlgCat 𝕜) (Type u) := ⟨carrier⟩

/-- Bundle a `*`-algebra as an object of `StarAlgCat 𝕜`. -/
public abbrev of (A : Type u) [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A] :
    StarAlgCat 𝕜 := ⟨A⟩

/-- Morphisms `X ⟶ Y` are exactly the `*`-algebra homomorphisms `X.carrier →⋆ₐ[𝕜] Y.carrier`,
wrapped in a one-field structure so that the category does not borrow any ambient instance. -/
public structure Hom (X Y : StarAlgCat 𝕜) where
  /-- The underlying `*`-algebra homomorphism. -/
  toStarAlgHom : X.carrier →⋆ₐ[𝕜] Y.carrier

public instance : Category (StarAlgCat 𝕜) where
  Hom X Y := Hom X Y
  id X := ⟨StarAlgHom.id 𝕜 X.carrier⟩
  comp f g := ⟨g.toStarAlgHom.comp f.toStarAlgHom⟩

/-- Build the morphism `X ⟶ Y` from a `*`-algebra homomorphism. -/
public def ofHom {X Y : StarAlgCat 𝕜} (f : X.carrier →⋆ₐ[𝕜] Y.carrier) : X ⟶ Y := ⟨f⟩

@[simp] public lemma toStarAlgHom_ofHom {X Y : StarAlgCat 𝕜} (f : X.carrier →⋆ₐ[𝕜] Y.carrier) :
    (ofHom f).toStarAlgHom = f := rfl

@[simp] public lemma toStarAlgHom_id (X : StarAlgCat 𝕜) :
    (𝟙 X : X ⟶ X).toStarAlgHom = StarAlgHom.id 𝕜 X.carrier := rfl

@[simp] public lemma toStarAlgHom_comp {X Y Z : StarAlgCat 𝕜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toStarAlgHom = g.toStarAlgHom.comp f.toStarAlgHom := rfl

/-- Two morphisms agreeing on every point are equal. -/
@[ext] public theorem hom_ext {X Y : StarAlgCat 𝕜} {f g : X ⟶ Y}
    (h : ∀ x, f.toStarAlgHom x = g.toStarAlgHom x) : f = g := by
  cases f; cases g; exact congrArg Hom.mk (StarAlgHom.ext h)

end StarAlgCat
