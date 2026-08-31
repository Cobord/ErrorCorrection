import QuantumErrorCorrection.GroupAlgebraStar
import QuantumErrorCorrection.PauliFunctor
import QuantumErrorCorrection.QuasiLocalAlgebra

/-!
# The Pauli quasi-local algebra

Assembles a `QuasiLocalAlgebra` out of the Pauli group net (`PauliGroup.quditInclusionFunctor`
in `PauliFunctor.lean`) and the group-algebra construction (`GroupAlgebraStar.lean`): to a
finite region `S` of qudits it assigns the group algebra of its Pauli group, `MonoidAlgebra 𝕜
(PauliGroup ↥S.carrier d)`, with the trivial (purely bosonic) grading. Isotony is inherited
from the injectivity of `quditInclusionHom` and `groupAlgebraMapStarAlgHom`. The disjoint
super-commuting condition reduces, since everything is even, to plain commutation of
disjointly-supported Pauli operators (`PauliGroup.commute_of_disjoint_range`), lifted from
individual group elements to arbitrary linear combinations by bilinearity of multiplication.
-/

open CategoryTheory

universe u

namespace PauliGroup

variable {X : Type u} [DecidableEq X] {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜] {d : ℕ}

private lemma zmod2_eq_zero_or_one (i : ZMod 2) : i = 0 ∨ i = 1 := by revert i; decide

/-- The net of Pauli group algebras: the functor `B(X) ⥤ SuperStarAlgCat 𝕜` sending a region
`S` to the group algebra of its Pauli group. -/
noncomputable def pauliNet (X : Type u) [DecidableEq X] (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜]
    (d : ℕ) : RegionCat X ⥤ SuperStarAlgCat 𝕜 where
  obj S := SuperStarAlgCat.of (MonoidAlgebra 𝕜 (PauliGroup ↥S.carrier d))
  map {S T} f := ⟨groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom (RegionCat.subsetOfHom f)),
    fun hx => groupAlgebraMapStarAlgHom_grading_mem _ hx⟩
  map_id S := by
    apply Subtype.ext
    show groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom (RegionCat.subsetOfHom (𝟙 S)))
        = StarAlgHom.id 𝕜 (MonoidAlgebra 𝕜 (PauliGroup ↥S.carrier d))
    rw [show RegionCat.subsetOfHom (𝟙 S) = Finset.Subset.refl S.carrier from rfl,
      quditInclusionHom_refl, groupAlgebraMapStarAlgHom_id]
  map_comp {S T U} f g := by
    apply Subtype.ext
    show groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom (RegionCat.subsetOfHom (f ≫ g)))
        = (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom (RegionCat.subsetOfHom g))).comp
          (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom (RegionCat.subsetOfHom f)))
    rw [show RegionCat.subsetOfHom (f ≫ g)
          = Finset.Subset.trans (RegionCat.subsetOfHom f) (RegionCat.subsetOfHom g) from rfl,
      quditInclusionHom_trans, groupAlgebraMapStarAlgHom_comp]

/-! ### Isotony -/

lemma pauliNet_isotony {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    Function.Injective ((pauliNet X 𝕜 d).map (RegionCat.homOfSubset h)).1 :=
  groupAlgebraMapStarAlgHom_injective (quditInclusionHom_injective h)

/-! ### Disjoint super-commutation

Lift `commute_of_disjoint_range` (commutation of individual Pauli group elements) to arbitrary
linear combinations, by bilinearity of multiplication in the group algebra. -/

omit [DecidableEq X] in
private lemma pauliNet_commute_single_single {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (g : PauliGroup ↥S.carrier d) (c : 𝕜) (h : PauliGroup ↥T.carrier d) (c' : 𝕜) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS) (MonoidAlgebra.single g c) *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT) (MonoidAlgebra.single h c')
      = groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT) (MonoidAlgebra.single h c') *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS) (MonoidAlgebra.single g c) := by
  simp only [groupAlgebraMapStarAlgHom_apply, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single]
  rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
    commute_of_disjoint_range hS hT hdisj g h, mul_comm c c']

omit [DecidableEq X] in
private lemma pauliNet_commute_single_left {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (g : PauliGroup ↥S.carrier d) (c : 𝕜) (y : MonoidAlgebra 𝕜 (PauliGroup ↥T.carrier d)) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS) (MonoidAlgebra.single g c) *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT) y
      = groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT) y *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS) (MonoidAlgebra.single g c) := by
  have key : (AddMonoidHom.mulLeft (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS)
        (MonoidAlgebra.single g c))).comp
        (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT)).toRingHom.toAddMonoidHom
      = (AddMonoidHom.mulRight (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS)
        (MonoidAlgebra.single g c))).comp
        (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT)).toRingHom.toAddMonoidHom := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro h c'
    simpa using pauliNet_commute_single_single hS hT hdisj g c h c'
  simpa using DFunLike.congr_fun key y

omit [DecidableEq X] in
/-- Disjointly-supported Pauli group algebra elements commute: the images (in the group
algebra of a common enclosing region `U`) of *arbitrary* elements of the group algebras of two
disjoint regions `S`, `T` commute, not just individual Pauli group elements. -/
lemma pauliNet_commute_of_disjoint {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (x : MonoidAlgebra 𝕜 (PauliGroup ↥S.carrier d)) (y : MonoidAlgebra 𝕜 (PauliGroup ↥T.carrier d)) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS) x *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT) y
      = groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT) y *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS) x := by
  have key : (AddMonoidHom.mulRight (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT)
        y)).comp (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS)).toRingHom.toAddMonoidHom
      = (AddMonoidHom.mulLeft (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hT)
        y)).comp (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (quditInclusionHom hS)).toRingHom.toAddMonoidHom := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro g c
    simpa using pauliNet_commute_single_left hS hT hdisj g c y
  simpa using DFunLike.congr_fun key x

/-- The Pauli quasi-local algebra on a site set `X` at qudit dimension `d`: to each finite
region assigns the group algebra of its Pauli group. Isotony is inherited from injectivity of
`quditInclusionHom` and `groupAlgebraMapStarAlgHom`; super-commutation of disjoint regions
reduces to `commute_of_disjoint_range` since every Pauli group algebra element is even
(`koszulSign` is always `1`). -/
noncomputable def pauliQuasiLocalAlgebra (X : Type u) [DecidableEq X] (𝕜 : Type u) [CommRing 𝕜]
    [StarRing 𝕜] (d : ℕ) : QuasiLocalAlgebra X 𝕜 where
  net := pauliNet X 𝕜 d
  isotony h := pauliNet_isotony h
  superCommuting {S T} hdisj {i j x y} hx hy := by
    obtain rfl | rfl := zmod2_eq_zero_or_one i <;> obtain rfl | rfl := zmod2_eq_zero_or_one j
    · simp only [koszulSign_zero_left, one_smul]
      exact pauliNet_commute_of_disjoint _ _ hdisj x y
    · have hy0 : y = 0 := (MonoidAlgebra.mem_trivialGrading_one_iff y).mp hy
      simp [hy0]
    · have hx0 : x = 0 := (MonoidAlgebra.mem_trivialGrading_one_iff x).mp hx
      simp [hx0]
    · have hx0 : x = 0 := (MonoidAlgebra.mem_trivialGrading_one_iff x).mp hx
      simp [hx0]

end PauliGroup
