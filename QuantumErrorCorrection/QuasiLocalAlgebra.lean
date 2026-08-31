import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Finset.Basic
import QuantumErrorCorrection.RegionCat
import Supersymmetric.Basic

/-!
# Quasi-local superalgebras

A *quasi-local algebra* on a set `X` of sites (qudits) is a net of local algebras: to every
finite region `S ⊆ X` one assigns an algebra `𝒜(S)` of observables supported on `S`, and to
every inclusion of regions `S ⊆ T` an embedding `𝒜(S) ↪ 𝒜(T)`, compatibly with composition.
This is exactly a functor from `B(X)`, the poset of finite subsets of `X` ordered by inclusion
(viewed as a category), to a category of algebras.

Here the target category is that of `ZMod 2`-graded `*`-algebras (`SuperStarAlgebra`), the
abstract algebraic skeleton standing in for a "von Neumann superalgebra": a genuine realization
as a weakly-closed `*`-subalgebra of bounded operators on a graded Hilbert space is future work.
On top of the net structure we require *isotony* (every structure map is injective, so each
local algebra really does embed in every larger one) and can state the *disjoint
super-commuting* condition: local observables on disjoint regions graded-commute once compared
inside any common larger region, with a sign `(-1)^(i j)` for parities `i, j` (Koszul sign,
reusing `koszulSign` from `Supersymmetric.Basic`). This is the graded generalization of
microcausality / Einstein locality for lattice systems with fermionic (odd) degrees of freedom.
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

/-- A *quasi-local superalgebra* on a site set `X`: a functor from `B(X)` (finite regions,
ordered by inclusion) to `ZMod 2`-graded `*`-algebras, satisfying

* *isotony*: every structure map is injective, so the algebra of a smaller region really does
  embed in that of every larger one, and
* the *disjoint super-commuting* (microcausality) condition: homogeneous local observables
  supported on disjoint regions graded-commute (with Koszul sign `(-1)^(i j)`) once compared
  inside any common region containing both — here, their union.

For purely even (bosonic) observables the super-commuting condition reduces to ordinary
commutation of disjointly-supported operators. -/
structure QuasiLocalAlgebra (X : Type u) [DecidableEq X] (𝕜 : Type u) [CommRing 𝕜]
    [StarRing 𝕜] where
  /-- The net of local algebras: the functor `B(X) ⥤ SuperStarAlgCat 𝕜`. -/
  net : RegionCat X ⥤ SuperStarAlgCat 𝕜
  /-- Isotony: the structure map for every inclusion of regions is injective. -/
  isotony : ∀ {S T : RegionCat X} (h : S.carrier ⊆ T.carrier),
    Function.Injective (net.map (RegionCat.homOfSubset h)).1
  /-- Disjoint regions super-commute (with Koszul sign) once compared inside their union. -/
  superCommuting : ∀ {S T : RegionCat X}, Disjoint S.carrier T.carrier →
    ∀ {i j : ZMod 2} {x : net.obj S} {y : net.obj T},
      x ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := net.obj S) i →
        y ∈ SuperVectorSpace.grading (𝕜 := 𝕜) (V := net.obj T) j →
          let U : RegionCat X := RegionCat.of (S.carrier ∪ T.carrier)
          let hS : S.carrier ⊆ U.carrier := Finset.subset_union_left
          let hT : T.carrier ⊆ U.carrier := Finset.subset_union_right
          let x' := (net.map (RegionCat.homOfSubset hS)).1 x
          let y' := (net.map (RegionCat.homOfSubset hT)).1 y
          x' * y' = koszulSign 𝕜 i j • (y' * x')
