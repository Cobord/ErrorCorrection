/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Finset.Basic

/-!
# `B(X)`: the poset of finite regions of a site set, as a category

`RegionCat X` is `B(X)`: the category of finite subsets ("regions") of a site set `X`,
ordered by inclusion. It is bundled as its own structure, rather than treating `Finset X`
itself as a category via a generic order-to-category instance (`Preorder.smallCategory`):
that would make the category structure a borrowed, ambient instance on `Finset X` at large,
rather than data owned by `RegionCat` alone. Here morphisms `S ⟶ T` are *exactly* the
(propositional, unique) witnesses of `S.carrier ⊆ T.carrier` — no other data, so in particular
not an arbitrary map between the finite sets `S.carrier` and `T.carrier`.

This is the natural indexing category for a net of local algebras (a quasi-local algebra, see
`QuasiLocalAlgebra.lean`) or any other qudit-region-indexed construction, such as
`PauliGroup.quditInclusionFunctor` in `PauliFunctor.lean`.
-/

@[expose] public section

open CategoryTheory

universe u

/-- An object of `B(X)`: a finite region (subset) of a site set `X`. -/
public structure RegionCat (X : Type u) where
  /-- The underlying finite region. -/
  carrier : Finset X

namespace RegionCat

variable {X : Type u}

/-- Bundle a `Finset X` as a `RegionCat X` object. -/
public abbrev of (S : Finset X) : RegionCat X := ⟨S⟩

/-- Morphisms `S ⟶ T` are exactly the witnesses of `S.carrier ⊆ T.carrier`; there is no other
morphism data, so this is a thin (poset) category. -/
public instance : Category (RegionCat X) where
  Hom S T := PLift (S.carrier ⊆ T.carrier)
  id S := ⟨Finset.Subset.refl S.carrier⟩
  comp f g := ⟨Finset.Subset.trans f.down g.down⟩

/-- Build the morphism `S ⟶ T` witnessing `S.carrier ⊆ T.carrier`. -/
public def homOfSubset {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) : S ⟶ T := ⟨h⟩

/-- Extract the inclusion `S.carrier ⊆ T.carrier` witnessed by a morphism `S ⟶ T`. -/
public theorem subsetOfHom {S T : RegionCat X} (f : S ⟶ T) : S.carrier ⊆ T.carrier := f.down

@[simp] public lemma subsetOfHom_homOfSubset {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    subsetOfHom (homOfSubset h) = h := rfl

@[simp] public lemma homOfSubset_subsetOfHom {S T : RegionCat X} (f : S ⟶ T) :
    homOfSubset (subsetOfHom f) = f := rfl

end RegionCat
