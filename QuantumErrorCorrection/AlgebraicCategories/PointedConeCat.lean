/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# The category of pointed cones in modules

`PointedConeCat R` is the category whose objects are modules over an ordered ring `R` equipped
with a distinguished `PointedCone R` — a subset containing `0` and closed under addition and
under scaling by non-negative scalars, i.e. a `Submodule` over `{c : R // 0 ≤ c}` — and whose
morphisms are the `R`-linear maps of the ambient modules that carry the source cone into the
target cone.

Note the deliberately explicit name: `Cone` in a category-theoretic file otherwise means a
limit cone (`CategoryTheory.Limits.Cone`), which is a different notion entirely.

Like `RegionCat` and `GrpInclCat`, this is bundled as its own structure with its own `Category`
instance, so that a morphism carries its cone-preservation proof as data: a functor into
`PointedConeCat R` is automatically a net of cones, each structure map preserving the
distinguished cone. Keeping the ambient module in the object (rather than only the cone, which
is already a `{c : R // 0 ≤ c}`-module on its own) is what lets a structure map be an honest
linear map of the ambient spaces, as for `stoquasticFunctor` in `Stoquastic.lean`: extending a
matrix to a larger region is linear on all matrices, and preserving stoquasticity is then a
genuine condition on that linear map rather than a tautology.
-/

@[expose] public section

open CategoryTheory

universe u

/-- An object of `PointedConeCat R`: a module over `R` with a distinguished pointed cone. -/
public structure PointedConeCat (R : Type u) [Ring R] [PartialOrder R] [IsOrderedRing R] :
    Type (u + 1) where
  /-- The ambient module. -/
  carrier : Type u
  [isAddCommMonoid : AddCommMonoid carrier]
  [isModule : Module R carrier]
  /-- The distinguished pointed cone inside the ambient module. -/
  cone : PointedCone R carrier

namespace PointedConeCat

variable {R : Type u} [Ring R] [PartialOrder R] [IsOrderedRing R]

attribute [instance] isAddCommMonoid isModule

public instance : CoeSort (PointedConeCat R) (Type u) := ⟨carrier⟩

/-- Bundle a pointed cone in a module as an object of `PointedConeCat R`. -/
public abbrev of (E : Type u) [AddCommMonoid E] [Module R E] (C : PointedCone R E) :
    PointedConeCat R := ⟨E, C⟩

/-- Morphisms `M ⟶ N` are exactly the `R`-linear maps `M.carrier →ₗ[R] N.carrier` mapping
`M.cone` into `N.cone`. -/
public instance : Category (PointedConeCat R) where
  Hom M N := {f : M.carrier →ₗ[R] N.carrier // ∀ x ∈ M.cone, f x ∈ N.cone}
  id M := ⟨LinearMap.id, fun _ hx => hx⟩
  comp f g := ⟨g.1.comp f.1, fun x hx => g.2 _ (f.2 x hx)⟩

/-- Build the morphism `M ⟶ N` from a linear map carrying `M.cone` into `N.cone`. -/
public def homOfMapsTo {M N : PointedConeCat R} (f : M.carrier →ₗ[R] N.carrier)
    (hf : ∀ x ∈ M.cone, f x ∈ N.cone) : M ⟶ N := ⟨f, hf⟩

/-- The underlying linear map of a morphism `M ⟶ N`. -/
public def toLinearMap {M N : PointedConeCat R} (f : M ⟶ N) : M.carrier →ₗ[R] N.carrier := f.1

public theorem mapsTo_toLinearMap {M N : PointedConeCat R} (f : M ⟶ N) :
    ∀ x ∈ M.cone, toLinearMap f x ∈ N.cone := f.2

@[simp] public lemma toLinearMap_homOfMapsTo {M N : PointedConeCat R}
    (f : M.carrier →ₗ[R] N.carrier) (hf : ∀ x ∈ M.cone, f x ∈ N.cone) :
    toLinearMap (homOfMapsTo f hf) = f := rfl

@[simp] public lemma homOfMapsTo_toLinearMap {M N : PointedConeCat R} (f : M ⟶ N) :
    homOfMapsTo (toLinearMap f) (mapsTo_toLinearMap f) = f := rfl

@[simp] public lemma toLinearMap_id (M : PointedConeCat R) :
    toLinearMap (𝟙 M) = LinearMap.id := rfl

@[simp] public lemma toLinearMap_comp {M N P : PointedConeCat R} (f : M ⟶ N) (g : N ⟶ P) :
    toLinearMap (f ≫ g) = (toLinearMap g).comp (toLinearMap f) := rfl

/-- Two morphisms agreeing on every point of the ambient module are equal: a morphism carries
no data beyond its underlying linear map. -/
@[ext] public theorem hom_ext {M N : PointedConeCat R} {f g : M ⟶ N}
    (h : ∀ x, toLinearMap f x = toLinearMap g x) : f = g :=
  Subtype.ext (LinearMap.ext h)

end PointedConeCat
