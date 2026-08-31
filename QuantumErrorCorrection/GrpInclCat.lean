/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Basic

/-!
# The category of groups and injective homomorphisms

`GrpInclCat` bundles groups together with only the *injective* group homomorphisms
("inclusions") as morphisms — unlike Mathlib's `GrpCat`, whose morphisms are arbitrary group
homomorphisms. It is bundled as its own structure with its own explicit `Category` instance
(the same pattern as `RegionCat`, see `RegionCat.lean`), rather than as a subcategory of
`GrpCat`, so that a morphism `X ⟶ Y` carries its injectivity proof as data: any functor into
`GrpInclCat` is, by construction, an *isotonic* net of groups, exactly the source shape needed
for `PauliGroup.quditInclusionFunctor` in `PauliFunctor.lean` (each `quditInclusionHom` really
is injective) and for group-algebra functors built on top of it later.
-/

@[expose] public section

open CategoryTheory

universe u

/-- An object of `GrpInclCat`: a group. -/
public structure GrpInclCat : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [group : Group carrier]

namespace GrpInclCat

attribute [instance] GrpInclCat.group

public instance : CoeSort GrpInclCat (Type u) := ⟨carrier⟩

/-- Bundle a `Group` as a `GrpInclCat` object. -/
public abbrev of (G : Type u) [Group G] : GrpInclCat := ⟨G⟩

/-- Morphisms `X ⟶ Y` are exactly the injective group homomorphisms `X.carrier →* Y.carrier`. -/
public instance : Category GrpInclCat.{u} where
  Hom X Y := {f : X.carrier →* Y.carrier // Function.Injective f}
  id X := ⟨MonoidHom.id X.carrier, Function.injective_id⟩
  comp f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

/-- Build the morphism `X ⟶ Y` from an injective group homomorphism. -/
public def homOfInjective {X Y : GrpInclCat} (f : X.carrier →* Y.carrier)
    (hf : Function.Injective f) : X ⟶ Y := ⟨f, hf⟩

/-- The underlying group homomorphism of a morphism `X ⟶ Y`. -/
public def toMonoidHom {X Y : GrpInclCat} (f : X ⟶ Y) : X.carrier →* Y.carrier := f.1

public theorem injective_toMonoidHom {X Y : GrpInclCat} (f : X ⟶ Y) :
    Function.Injective (toMonoidHom f) := f.2

@[simp] public lemma toMonoidHom_homOfInjective {X Y : GrpInclCat} (f : X.carrier →* Y.carrier)
    (hf : Function.Injective f) : toMonoidHom (homOfInjective f hf) = f := rfl

@[simp] public lemma homOfInjective_toMonoidHom {X Y : GrpInclCat} (f : X ⟶ Y) :
    homOfInjective (toMonoidHom f) (injective_toMonoidHom f) = f := rfl

end GrpInclCat
