/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.CategoryTheory.Category.Basic
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

end FlatCommStarRingCat
