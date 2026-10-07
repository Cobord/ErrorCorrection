import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import QuantumErrorCorrection.AlgebraicCategories.StarAlgCat
import Supersymmetric.Basic

/-!
# The category of super `*`-algebras

A *super `*`-algebra* (`SuperStarAlgebra`) is a `ZMod 2`-graded `*`-algebra: a
`SuperVectorSpace` (from `Supersymmetric.Basic`) whose multiplication adds parities and whose
`star` preserves them. It is the abstract algebraic skeleton standing in for a "von Neumann
superalgebra": a genuine realization as a weakly-closed `*`-subalgebra of bounded operators on a
graded Hilbert space is future work.

`SuperStarAlgCat 𝕜` is the bundled category of these, with grading-preserving `*`-algebra
homomorphisms as morphisms. It is the target category of the nets in `QuasiLocalAlgebra`.

Every ungraded `*`-algebra is a super `*`-algebra concentrated in degree `0`, giving the fully
faithful functor `StarAlgCat.toPurelyEvenSuperStarAlgCat : StarAlgCat 𝕜 ⥤ SuperStarAlgCat 𝕜`.
-/

open CategoryTheory

universe u

section SuperStarAlgebraDef

variable (𝕜 : Type u) (A : Type u) [CommRing 𝕜] [StarRing 𝕜] [Ring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A]

/-- A `ZMod 2`-graded `*`-algebra: a `SuperVectorSpace` whose multiplication and `star`
operation both respect the grading (`A_i * A_j ⊆ A_{i+j}` and `star A_i ⊆ A_i`). The base ring
`𝕜` is itself required to be a `*`-ring, and `star` is required to be conjugate-linear over it
(`StarModule 𝕜 A`, i.e. `star (r • a) = star r • star a`), so that `A` is a genuine `*`-algebra
over `𝕜` and not merely a ring with an unrelated `star` and an unrelated `𝕜`-module structure. -/
class SuperStarAlgebra extends SuperVectorSpace 𝕜 A where
  /-- Multiplication adds parities. -/
  grading_mul_mem : ∀ {i j : ZMod 2} {x y : A},
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := A) i →
      y ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := A) j →
        x * y ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := A) (i + j)
  /-- `star` preserves parity. -/
  grading_star_mem : ∀ {i : ZMod 2} {x : A},
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := A) i →
      star x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := A) i

end SuperStarAlgebraDef

/-- The bundled category of `ZMod 2`-graded `*`-algebras over a fixed base `*`-ring `𝕜`. -/
structure SuperStarAlgCat (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜] : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [ring : Ring carrier]
  [starRing : StarRing carrier]
  [algebra : Algebra 𝕜 carrier]
  [starModule : StarModule 𝕜 carrier]
  [superStar : SuperStarAlgebra 𝕜 carrier]

namespace SuperStarAlgCat

variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]

instance : CoeSort (SuperStarAlgCat 𝕜) (Type u) := ⟨carrier⟩

attribute [instance] ring starRing algebra starModule superStar

/-- Construct a bundled `SuperStarAlgCat` from a type with the relevant structure. -/
abbrev of (A : Type u) [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A]
    [SuperStarAlgebra 𝕜 A] : SuperStarAlgCat 𝕜 := ⟨A⟩

/-- A morphism `X ⟶ Y` of `SuperStarAlgCat 𝕜` is a `*`-algebra homomorphism that also
preserves the `ZMod 2` grading. -/
instance : Category (SuperStarAlgCat 𝕜) where
  Hom X Y := {f : X.carrier →⋆ₐ[𝕜] Y.carrier //
    ∀ {i : ZMod 2} {x : X.carrier}, x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := X.carrier) i →
      f x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := Y.carrier) i}
  id X := ⟨StarAlgHom.id 𝕜 X.carrier, fun hx => hx⟩
  comp f g := ⟨g.1.comp f.1, fun hx => g.2 (f.2 hx)⟩

end SuperStarAlgCat

/-! ### Ungraded `*`-algebras as purely even super `*`-algebras -/

section PurelyEven

variable (𝕜 : Type u) (A : Type u) [CommRing 𝕜] [StarRing 𝕜] [Ring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A]

/-- The purely even grading: everything in degree `0`, nothing in degree `1`. -/
private def purelyEvenGrading : ZMod 2 → Submodule 𝕜 A := fun i => if i = 0 then ⊤ else ⊥

private lemma purelyEvenGrading_zmod_two_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  revert i; decide

omit [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] in
private lemma purelyEvenGrading_isInternal : DirectSum.IsInternal (purelyEvenGrading 𝕜 A) := by
  apply (DirectSum.isInternal_submodule_iff_isCompl (purelyEvenGrading 𝕜 A) (i := 0) (j := 1)
    (by decide) (by
      ext i
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      exact purelyEvenGrading_zmod_two_cases i)).2
  constructor
  · simp [purelyEvenGrading]
  · simp [purelyEvenGrading]

/-- The purely even `SuperStarAlgebra` structure on a `*`-algebra. Not an instance: a type may
carry a different, nontrivial grading. -/
@[instance_reducible]
private noncomputable def purelyEvenSuperStarAlgebra : SuperStarAlgebra 𝕜 A where
  grading := purelyEvenGrading 𝕜 A
  decomposition := (purelyEvenGrading_isInternal 𝕜 A).chooseDecomposition
  grading_mul_mem {i j x y} hx hy := by
    change x ∈ purelyEvenGrading 𝕜 A i at hx
    change y ∈ purelyEvenGrading 𝕜 A j at hy
    change x * y ∈ purelyEvenGrading 𝕜 A (i + j)
    rcases purelyEvenGrading_zmod_two_cases i with rfl | rfl <;>
      rcases purelyEvenGrading_zmod_two_cases j with rfl | rfl <;>
      simp_all [purelyEvenGrading]
  grading_star_mem {i x} hx := by
    change x ∈ purelyEvenGrading 𝕜 A i at hx
    change star x ∈ purelyEvenGrading 𝕜 A i
    rcases purelyEvenGrading_zmod_two_cases i with rfl | rfl <;> simp_all [purelyEvenGrading]

end PurelyEven

namespace StarAlgCat

variable (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜]

/-- A `*`-algebra, with its own (possibly nontrivial) `star`, as a super `*`-algebra
concentrated in degree `0`. Every `*`-algebra homomorphism preserves this grading, since the
degree-`0` part is everything and the degree-`1` part is `0`. The functor is the identity on
underlying `*`-algebra homomorphisms, hence fully faithful. -/
noncomputable def toPurelyEvenSuperStarAlgCat : StarAlgCat 𝕜 ⥤ SuperStarAlgCat 𝕜 where
  obj X := { carrier := X.carrier, superStar := purelyEvenSuperStarAlgebra 𝕜 X.carrier }
  map {X Y} f := ⟨f.toStarAlgHom, fun {i x} hx => by
    change x ∈ purelyEvenGrading 𝕜 X.carrier i at hx
    change f.toStarAlgHom x ∈ purelyEvenGrading 𝕜 Y.carrier i
    rcases purelyEvenGrading_zmod_two_cases i with rfl | rfl
    · simp [purelyEvenGrading]
    · have hx0 : x = 0 := by
        have hx' : x ∈ (⊥ : Submodule 𝕜 X.carrier) := by simpa [purelyEvenGrading] using hx
        exact (Submodule.mem_bot 𝕜).1 hx'
      rw [hx0, map_zero]
      exact zero_mem _⟩

theorem toPurelyEvenSuperStarAlgCat_map_apply {X Y : StarAlgCat 𝕜} (f : X ⟶ Y) (x : X) :
    ((toPurelyEvenSuperStarAlgCat 𝕜).map f).1 x = f.toStarAlgHom x := rfl

theorem mem_grading_zero_toPurelyEvenSuperStarAlgCat (X : StarAlgCat 𝕜) (x : X) :
    x ∈ SuperVectorSpace.grading (𝕜 := 𝕜)
      (V := ((toPurelyEvenSuperStarAlgCat 𝕜).obj X).carrier) 0 := by
  change x ∈ purelyEvenGrading 𝕜 X.carrier 0
  simp [purelyEvenGrading]

theorem eq_zero_of_mem_grading_one_toPurelyEvenSuperStarAlgCat (X : StarAlgCat 𝕜) {x : X}
    (hx : x ∈ SuperVectorSpace.grading (𝕜 := 𝕜)
      (V := ((toPurelyEvenSuperStarAlgCat 𝕜).obj X).carrier) 1) : x = 0 := by
  have hx' : x ∈ (⊥ : Submodule 𝕜 X.carrier) := by
    change x ∈ purelyEvenGrading 𝕜 X.carrier 1 at hx
    simpa [purelyEvenGrading] using hx
  exact (Submodule.mem_bot 𝕜).1 hx'

instance : (toPurelyEvenSuperStarAlgCat 𝕜).Faithful where
  map_injective h := hom_ext fun x => congrArg (fun k => k.1 x) h

instance : (toPurelyEvenSuperStarAlgCat 𝕜).Full where
  map_surjective g := ⟨ofHom g.1, rfl⟩

end StarAlgCat
