import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Finset.Basic
import QuantumErrorCorrection.RegionCat
import QuantumErrorCorrection.AlgebraicCategories.SuperStarAlgCat

/-!
# Quasi-local superalgebras

A *quasi-local algebra* on a set `X` of sites (qudits) is a net of local algebras: to every
finite region `S ⊆ X` one assigns an algebra `𝒜(S)` of observables supported on `S`, and to
every inclusion of regions `S ⊆ T` an embedding `𝒜(S) ↪ 𝒜(T)`, compatibly with composition.
This is exactly a functor from `B(X)`, the poset of finite subsets of `X` ordered by inclusion
(viewed as a category), to a category of algebras.

Here the target category is `SuperStarAlgCat 𝕜`, that of `ZMod 2`-graded `*`-algebras
(`SuperStarAlgebra`, see `AlgebraicCategories/SuperStarAlgCat.lean`).
On top of the net structure we require *isotony* (every structure map is injective, so each
local algebra really does embed in every larger one) and can state the *disjoint
super-commuting* condition: local observables on disjoint regions graded-commute once compared
inside any common larger region, with a sign `(-1)^(i j)` for parities `i, j` (Koszul sign,
reusing `koszulSign` from `Supersymmetric.Basic`). This is the graded generalization of
microcausality / Einstein locality for lattice systems with fermionic (odd) degrees of freedom.
-/

open CategoryTheory

universe u

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
