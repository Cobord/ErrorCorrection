/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.PointedConeCat
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# The category of pointed cones in algebras

`PointedConeAlgCat R` is the algebra-valued refinement of `PointedConeCat R` (see
`PointedConeCat.lean`): an object is an `R`-algebra equipped with a distinguished
`PointedCone R` inside it, and a morphism is an `R`-algebra homomorphism — not merely an
`R`-linear map — carrying the source cone into the target cone.

The motivating example is the stoquastic net (`Stoquastic.lean`): every object there is a matrix
algebra `Matrix (S.carrier → Fin d) (S.carrier → Fin d) R` and every structure map is
`A ↦ A ⊗ 1`, extension by the identity on the new qudits, which is not just linear but a unital
algebra map — `(A ⊗ 1) (B ⊗ 1) = (A B) ⊗ 1`. Recording that multiplicativity in the morphisms is
what makes a functor into this category a net of *algebras* of observables, comparable to the
`SuperStarAlgCat`-valued nets of `QuasiLocalAlgebra.lean`, rather than merely a net of modules.

The base ring `R` is required to be commutative (as `Algebra R A` demands) and ordered, since it
is simultaneously the ring of scalars of the algebras and the ring whose non-negative elements
`{c : R // 0 ≤ c}` the cones are modules over.

Like `RegionCat`, `GrpInclCat` and `PointedConeCat`, this is bundled as its own structure with
its own `Category` instance, so a morphism carries its cone-preservation proof as data.

`forgetMul : PointedConeAlgCat R ⥤ PointedConeCat R` forgets the multiplication, keeping the
ambient module, its cone, and the linearity of each structure map; it is faithful.
-/

@[expose] public section

open CategoryTheory

universe u

/-- An object of `PointedConeAlgCat R`: an `R`-algebra with a distinguished pointed cone. -/
public structure PointedConeAlgCat (R : Type u) [CommRing R] [PartialOrder R] [IsOrderedRing R] :
    Type (u + 1) where
  /-- The underlying type of the ambient algebra. -/
  carrier : Type u
  [ring : Ring carrier]
  [algebra : Algebra R carrier]
  /-- The distinguished pointed cone inside the ambient algebra. -/
  cone : PointedCone R carrier

namespace PointedConeAlgCat

variable {R : Type u} [CommRing R] [PartialOrder R] [IsOrderedRing R]

attribute [instance] ring algebra

public instance : CoeSort (PointedConeAlgCat R) (Type u) := ⟨carrier⟩

/-- Bundle a pointed cone in an `R`-algebra as an object of `PointedConeAlgCat R`. -/
public abbrev of (A : Type u) [Ring A] [Algebra R A] (C : PointedCone R A) :
    PointedConeAlgCat R := ⟨A, C⟩

/-- Morphisms `M ⟶ N` are exactly the `R`-algebra homomorphisms `M.carrier →ₐ[R] N.carrier`
mapping `M.cone` into `N.cone`. -/
public instance : Category (PointedConeAlgCat R) where
  Hom M N := {f : M.carrier →ₐ[R] N.carrier // ∀ x ∈ M.cone, f x ∈ N.cone}
  id M := ⟨AlgHom.id R M.carrier, fun _ hx => hx⟩
  comp f g := ⟨g.1.comp f.1, fun x hx => g.2 _ (f.2 x hx)⟩

/-- Build the morphism `M ⟶ N` from an algebra homomorphism carrying `M.cone` into `N.cone`. -/
public def homOfMapsTo {M N : PointedConeAlgCat R} (f : M.carrier →ₐ[R] N.carrier)
    (hf : ∀ x ∈ M.cone, f x ∈ N.cone) : M ⟶ N := ⟨f, hf⟩

/-- The underlying algebra homomorphism of a morphism `M ⟶ N`. -/
public def toAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) : M.carrier →ₐ[R] N.carrier := f.1

public theorem mapsTo_toAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    ∀ x ∈ M.cone, toAlgHom f x ∈ N.cone := f.2

@[simp] public lemma toAlgHom_homOfMapsTo {M N : PointedConeAlgCat R}
    (f : M.carrier →ₐ[R] N.carrier) (hf : ∀ x ∈ M.cone, f x ∈ N.cone) :
    toAlgHom (homOfMapsTo f hf) = f := rfl

@[simp] public lemma homOfMapsTo_toAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    homOfMapsTo (toAlgHom f) (mapsTo_toAlgHom f) = f := rfl

@[simp] public lemma toAlgHom_id (M : PointedConeAlgCat R) :
    toAlgHom (𝟙 M) = AlgHom.id R M.carrier := rfl

@[simp] public lemma toAlgHom_comp {M N P : PointedConeAlgCat R} (f : M ⟶ N) (g : N ⟶ P) :
    toAlgHom (f ≫ g) = (toAlgHom g).comp (toAlgHom f) := rfl

/-- Two morphisms agreeing on every point of the ambient algebra are equal: a morphism carries
no data beyond its underlying algebra homomorphism. -/
@[ext] public theorem hom_ext {M N : PointedConeAlgCat R} {f g : M ⟶ N}
    (h : ∀ x, toAlgHom f x = toAlgHom g x) : f = g :=
  Subtype.ext (AlgHom.ext h)

/-- The forgetful functor to `PointedConeCat R`: keep the ambient module and its cone, forget
the multiplication, and remember of each structure map only that it is linear. It is the
identity on objects and on underlying functions, so nothing but the multiplicative structure is
discarded — whence `Faithful` below. -/
public def forgetMul : PointedConeAlgCat R ⥤ PointedConeCat R where
  obj M := PointedConeCat.of M.carrier M.cone
  map f := PointedConeCat.homOfMapsTo (toAlgHom f).toLinearMap (mapsTo_toAlgHom f)
  map_id _ := PointedConeCat.hom_ext fun _ => rfl
  map_comp _ _ := PointedConeCat.hom_ext fun _ => rfl

/-- Forgetting the multiplication loses no morphisms: an algebra homomorphism is determined by
its underlying function, hence by its underlying linear map. -/
public instance : (forgetMul (R := R)).Faithful where
  map_injective h :=
    hom_ext fun x => congrFun (congrArg (fun k => ⇑(PointedConeCat.toLinearMap k)) h) x

@[simp] public lemma forgetMul_obj_cone (M : PointedConeAlgCat R) :
    (forgetMul.obj M).cone = M.cone := rfl

@[simp] public lemma toLinearMap_forgetMul_map {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    PointedConeCat.toLinearMap (forgetMul.map f) = (toAlgHom f).toLinearMap := rfl

end PointedConeAlgCat
