/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.AlgebraicCategories.PointedConeCat
public import QuantumErrorCorrection.AlgebraicCategories.StarAlgCat
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# The category of pointed cones in `*`-algebras

`PointedConeAlgCat R` is the algebra-valued refinement of `PointedConeCat R` (see
`PointedConeCat.lean`): an object is an `R`-`*`-algebra equipped with a distinguished
`PointedCone R` inside it, and a morphism is a `*`-algebra homomorphism — not merely an
`R`-linear map — carrying the source cone into the target cone.

The motivating example is the stoquastic net (`Stoquastic.lean`): every object there is a matrix
algebra `Matrix (S.carrier → Fin d) (S.carrier → Fin d) R` and every structure map is
`A ↦ A ⊗ 1`, extension by the identity on the new qudits, which is not just linear but a unital
`*`-algebra map — `(A ⊗ 1) (B ⊗ 1) = (A B) ⊗ 1` and `(A ⊗ 1)ᴴ = Aᴴ ⊗ 1`. Recording that
structure in the morphisms is what makes a functor into this category a net of *algebras* of
observables, comparable to the `SuperStarAlgCat`-valued nets of `QuasiLocalAlgebra.lean`
(`SuperStarAlgCat` receives this category through `forgetCone` and the purely even functor of
`SuperStarAlgCat.lean`), rather than merely a net of modules.

The base ring `R` is required to be commutative (as `Algebra R A` demands) and ordered, since it
is simultaneously the ring of scalars of the algebras and the ring whose non-negative elements
`{c : R // 0 ≤ c}` the cones are modules over. Being ordered, it plays the role of `ℝ`, so its
`star` is required to be trivial (`TrivialStar R`), and given explicitly rather than assumed of
whatever `StarRing R` instance is around. The algebras themselves carry a nontrivial `star`
(for matrices over `R`, the transpose), conjugate-linear over `R` (`StarModule R`), hence
`R`-linear.

Like `RegionCat`, `GrpInclCat` and `PointedConeCat`, this is bundled as its own structure with
its own `Category` instance, so a morphism carries its cone-preservation proof as data.

`forgetMul : PointedConeAlgCat R ⥤ PointedConeCat R` forgets the multiplication and `star`,
keeping the ambient module, its cone, and the linearity of each structure map; it is faithful.
`forgetCone : PointedConeAlgCat R ⥤ StarAlgCat R` instead forgets the cone, keeping the
`*`-algebra; it is also faithful.
-/

@[expose] public section

open CategoryTheory

universe u

/-- An object of `PointedConeAlgCat R`: an `R`-`*`-algebra with a distinguished pointed cone. -/
public structure PointedConeAlgCat (R : Type u) [CommRing R] [PartialOrder R] [IsOrderedRing R]
    [StarRing R] [TrivialStar R] : Type (u + 1) where
  /-- The underlying type of the ambient algebra. -/
  carrier : Type u
  [ring : Ring carrier]
  [starRing : StarRing carrier]
  [algebra : Algebra R carrier]
  [starModule : StarModule R carrier]
  /-- The distinguished pointed cone inside the ambient algebra. -/
  cone : PointedCone R carrier

namespace PointedConeAlgCat

variable {R : Type u} [CommRing R] [PartialOrder R] [IsOrderedRing R] [StarRing R] [TrivialStar R]

attribute [instance] ring starRing algebra starModule

public instance : CoeSort (PointedConeAlgCat R) (Type u) := ⟨carrier⟩

/-- Bundle a pointed cone in an `R`-`*`-algebra as an object of `PointedConeAlgCat R`. -/
public abbrev of (A : Type u) [Ring A] [StarRing A] [Algebra R A] [StarModule R A]
    (C : PointedCone R A) : PointedConeAlgCat R := ⟨A, C⟩

/-- Morphisms `M ⟶ N` are exactly the `*`-algebra homomorphisms `M.carrier →⋆ₐ[R] N.carrier`
mapping `M.cone` into `N.cone`. -/
public instance : Category (PointedConeAlgCat R) where
  Hom M N := {f : M.carrier →⋆ₐ[R] N.carrier // ∀ x ∈ M.cone, f x ∈ N.cone}
  id M := ⟨StarAlgHom.id R M.carrier, fun _ hx => hx⟩
  comp f g := ⟨g.1.comp f.1, fun x hx => g.2 _ (f.2 x hx)⟩

/-- Build the morphism `M ⟶ N` from a `*`-algebra homomorphism carrying `M.cone` into
`N.cone`. -/
public def homOfMapsTo {M N : PointedConeAlgCat R} (f : M.carrier →⋆ₐ[R] N.carrier)
    (hf : ∀ x ∈ M.cone, f x ∈ N.cone) : M ⟶ N := ⟨f, hf⟩

/-- The underlying `*`-algebra homomorphism of a morphism `M ⟶ N`. -/
public def toStarAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    M.carrier →⋆ₐ[R] N.carrier := f.1

/-- The underlying algebra homomorphism of a morphism `M ⟶ N`. -/
public def toAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) : M.carrier →ₐ[R] N.carrier :=
  (toStarAlgHom f).toAlgHom

@[simp] public lemma coe_toAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    ⇑(toAlgHom f) = ⇑(toStarAlgHom f) := rfl

public theorem mapsTo_toStarAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    ∀ x ∈ M.cone, toStarAlgHom f x ∈ N.cone := f.2

public theorem mapsTo_toAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    ∀ x ∈ M.cone, toAlgHom f x ∈ N.cone := f.2

@[simp] public lemma toStarAlgHom_homOfMapsTo {M N : PointedConeAlgCat R}
    (f : M.carrier →⋆ₐ[R] N.carrier) (hf : ∀ x ∈ M.cone, f x ∈ N.cone) :
    toStarAlgHom (homOfMapsTo f hf) = f := rfl

@[simp] public lemma homOfMapsTo_toStarAlgHom {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    homOfMapsTo (toStarAlgHom f) (mapsTo_toStarAlgHom f) = f := rfl

@[simp] public lemma toStarAlgHom_id (M : PointedConeAlgCat R) :
    toStarAlgHom (𝟙 M) = StarAlgHom.id R M.carrier := rfl

@[simp] public lemma toStarAlgHom_comp {M N P : PointedConeAlgCat R} (f : M ⟶ N) (g : N ⟶ P) :
    toStarAlgHom (f ≫ g) = (toStarAlgHom g).comp (toStarAlgHom f) := rfl

@[simp] public lemma toAlgHom_id (M : PointedConeAlgCat R) :
    toAlgHom (𝟙 M) = AlgHom.id R M.carrier := rfl

@[simp] public lemma toAlgHom_comp {M N P : PointedConeAlgCat R} (f : M ⟶ N) (g : N ⟶ P) :
    toAlgHom (f ≫ g) = (toAlgHom g).comp (toAlgHom f) := rfl

/-- Two morphisms agreeing on every point of the ambient algebra are equal: a morphism carries
no data beyond its underlying `*`-algebra homomorphism. -/
@[ext] public theorem hom_ext {M N : PointedConeAlgCat R} {f g : M ⟶ N}
    (h : ∀ x, toStarAlgHom f x = toStarAlgHom g x) : f = g :=
  Subtype.ext (StarAlgHom.ext h)

/-- The forgetful functor to `PointedConeCat R`: keep the ambient module and its cone, forget
the multiplication and `star`, and remember of each structure map only that it is linear. It is
the identity on objects and on underlying functions, so nothing but the multiplicative and
`*`-structure is discarded — whence `Faithful` below. -/
public def forgetMul : PointedConeAlgCat R ⥤ PointedConeCat R where
  obj M := PointedConeCat.of M.carrier M.cone
  map f := PointedConeCat.homOfMapsTo (toAlgHom f).toLinearMap (mapsTo_toAlgHom f)
  map_id _ := PointedConeCat.hom_ext fun _ => rfl
  map_comp _ _ := PointedConeCat.hom_ext fun _ => rfl

/-- Forgetting the multiplication loses no morphisms: a `*`-algebra homomorphism is determined
by its underlying function, hence by its underlying linear map. -/
public instance : (forgetMul (R := R)).Faithful where
  map_injective h :=
    hom_ext fun x => congrFun (congrArg (fun k => ⇑(PointedConeCat.toLinearMap k)) h) x

@[simp] public lemma forgetMul_obj_cone (M : PointedConeAlgCat R) :
    (forgetMul.obj M).cone = M.cone := rfl

@[simp] public lemma toLinearMap_forgetMul_map {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    PointedConeCat.toLinearMap (forgetMul.map f) = (toAlgHom f).toLinearMap := rfl

/-- The forgetful functor to `StarAlgCat R`: keep the ambient `*`-algebra, forget the
distinguished cone and that each structure map preserves it. It is the identity on underlying
`*`-algebra homomorphisms, so it is faithful. It is not full, since a `*`-algebra homomorphism
need not carry one cone into the other. -/
public def forgetCone : PointedConeAlgCat R ⥤ StarAlgCat R where
  obj M := StarAlgCat.of M.carrier
  map f := StarAlgCat.ofHom (toStarAlgHom f)

/-- Forgetting the cone loses no morphisms: a morphism is determined by its `*`-algebra
homomorphism. -/
public instance : (forgetCone (R := R)).Faithful where
  map_injective h := hom_ext fun x => congrArg (fun k => StarAlgCat.Hom.toStarAlgHom k x) h

@[simp] public lemma toStarAlgHom_forgetCone_map {M N : PointedConeAlgCat R} (f : M ⟶ N) :
    (forgetCone.map f).toStarAlgHom = toStarAlgHom f := rfl

end PointedConeAlgCat
