import QuantumErrorCorrection.GroupAlgebraStar
import QuantumErrorCorrection.PauliCliffordFunctor
import QuantumErrorCorrection.QuasiLocalAlgebra

/-!
# The Clifford quasi-local algebra

Assembles a `QuasiLocalAlgebra` out of the Clifford group net (`PauliGroup.cliffordInclusionHom`
in `PauliCliffordFunctor.lean`) and the group-algebra construction (`GroupAlgebraStar.lean`): to
a finite region `S` of qudits it assigns the group algebra of its Clifford group,
`MonoidAlgebra 𝕜 (CliffordGroup ↥S.carrier d)`, with the trivial (purely bosonic) grading.
Isotony is inherited from the injectivity of `cliffordInclusionHom` and
`groupAlgebraMapStarAlgHom`. The disjoint super-commuting condition reduces, since everything is
even, to plain commutation of Clifford automorphisms extended from disjoint regions
(`PauliGroup.commute_of_disjoint_cliffordInclusionHom`), lifted from individual group elements to
arbitrary linear combinations by bilinearity of multiplication — the same argument as
`PauliQuasiLocalAlgebra.lean`, with `CliffordGroup` in place of `PauliGroup` throughout.
-/

open CategoryTheory

universe u

namespace PauliGroup

variable {X : Type u} [DecidableEq X] {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜] {d : ℕ}

private lemma zmod2_eq_zero_or_one' (i : ZMod 2) : i = 0 ∨ i = 1 := by revert i; decide

/-- The net of Clifford group algebras: the functor `B(X) ⥤ SuperStarAlgCat 𝕜` sending a region
`S` to the group algebra of its Clifford group. -/
noncomputable def cliffordNet (X : Type u) [DecidableEq X] (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜]
    (d : ℕ) : RegionCat X ⥤ SuperStarAlgCat 𝕜 where
  obj S := SuperStarAlgCat.of (MonoidAlgebra 𝕜 (CliffordGroup ↥S.carrier d))
  map {S T} f := ⟨groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom (RegionCat.subsetOfHom f)),
    fun hx => groupAlgebraMapStarAlgHom_grading_mem _ hx⟩
  map_id S := by
    apply Subtype.ext
    show groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom (RegionCat.subsetOfHom (𝟙 S)))
        = StarAlgHom.id 𝕜 (MonoidAlgebra 𝕜 (CliffordGroup ↥S.carrier d))
    rw [show RegionCat.subsetOfHom (𝟙 S) = Finset.Subset.refl S.carrier from rfl,
      cliffordInclusionHom_refl, groupAlgebraMapStarAlgHom_id]
  map_comp {S T U} f g := by
    apply Subtype.ext
    show groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom (RegionCat.subsetOfHom (f ≫ g)))
        = (groupAlgebraMapStarAlgHom (𝕜 := 𝕜)
            (cliffordInclusionHom (RegionCat.subsetOfHom g))).comp
          (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom (RegionCat.subsetOfHom f)))
    rw [show RegionCat.subsetOfHom (f ≫ g)
          = Finset.Subset.trans (RegionCat.subsetOfHom f) (RegionCat.subsetOfHom g) from rfl,
      cliffordInclusionHom_trans (RegionCat.subsetOfHom f) (RegionCat.subsetOfHom g),
      groupAlgebraMapStarAlgHom_comp]

/-! ### Isotony -/

lemma cliffordNet_isotony {S T : RegionCat X} (h : S.carrier ⊆ T.carrier) :
    Function.Injective ((cliffordNet X 𝕜 d).map (RegionCat.homOfSubset h)).1 :=
  groupAlgebraMapStarAlgHom_injective (cliffordInclusionHom_injective h)

/-! ### Disjoint super-commutation

Lift `commute_of_disjoint_cliffordInclusionHom` (commutation of individual extended Clifford
automorphisms) to arbitrary linear combinations, by bilinearity of multiplication in the group
algebra. -/

private lemma cliffordNet_commute_single_single {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (hcov : U.carrier ⊆ S.carrier ∪ T.carrier) (g : CliffordGroup ↥S.carrier d) (c : 𝕜)
    (h : CliffordGroup ↥T.carrier d) (c' : 𝕜) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS) (MonoidAlgebra.single g c) *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hT) (MonoidAlgebra.single h c')
      = groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hT) (MonoidAlgebra.single h c') *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS) (MonoidAlgebra.single g c) := by
  simp only [groupAlgebraMapStarAlgHom_apply, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single]
  rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
    (commute_of_disjoint_cliffordInclusionHom hS hT hdisj hcov g h : _ = _), mul_comm c c']

private lemma cliffordNet_commute_single_left {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (hcov : U.carrier ⊆ S.carrier ∪ T.carrier) (g : CliffordGroup ↥S.carrier d) (c : 𝕜)
    (y : MonoidAlgebra 𝕜 (CliffordGroup ↥T.carrier d)) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS) (MonoidAlgebra.single g c) *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hT) y
      = groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hT) y *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS) (MonoidAlgebra.single g c) := by
  have key : (AddMonoidHom.mulLeft (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS)
        (MonoidAlgebra.single g c))).comp
        (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hT)).toRingHom.toAddMonoidHom
      = (AddMonoidHom.mulRight (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS)
        (MonoidAlgebra.single g c))).comp
        (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hT)).toRingHom.toAddMonoidHom := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro h c'
    simpa using cliffordNet_commute_single_single hS hT hdisj hcov g c h c'
  simpa using DFunLike.congr_fun key y

/-- Disjointly-extended Clifford group algebra elements commute: the images (in the group
algebra of a common enclosing region `U`) of *arbitrary* elements of the group algebras of two
disjoint regions `S`, `T` commute, not just individual Clifford group elements. -/
lemma cliffordNet_commute_of_disjoint {S T U : RegionCat X} (hS : S.carrier ⊆ U.carrier)
    (hT : T.carrier ⊆ U.carrier) (hdisj : Disjoint S.carrier T.carrier)
    (hcov : U.carrier ⊆ S.carrier ∪ T.carrier)
    (x : MonoidAlgebra 𝕜 (CliffordGroup ↥S.carrier d))
    (y : MonoidAlgebra 𝕜 (CliffordGroup ↥T.carrier d)) :
    groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS) x *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hT) y
      = groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hT) y *
        groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS) x := by
  have key : (AddMonoidHom.mulRight (groupAlgebraMapStarAlgHom (𝕜 := 𝕜)
        (cliffordInclusionHom hT) y)).comp
        (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS)).toRingHom.toAddMonoidHom
      = (AddMonoidHom.mulLeft (groupAlgebraMapStarAlgHom (𝕜 := 𝕜)
        (cliffordInclusionHom hT) y)).comp
        (groupAlgebraMapStarAlgHom (𝕜 := 𝕜) (cliffordInclusionHom hS)).toRingHom.toAddMonoidHom := by
    apply MonoidAlgebra.addMonoidHom_ext
    intro g c
    simpa using cliffordNet_commute_single_left hS hT hdisj hcov g c y
  simpa using DFunLike.congr_fun key x

/-- The Clifford quasi-local algebra on a site set `X` at qudit dimension `d`: to each finite
region assigns the group algebra of its Clifford group. Isotony is inherited from injectivity of
`cliffordInclusionHom` and `groupAlgebraMapStarAlgHom`; super-commutation of disjoint regions
reduces to `commute_of_disjoint_cliffordInclusionHom` since every Clifford group algebra element
is even (`koszulSign` is always `1`). -/
noncomputable def cliffordQuasiLocalAlgebra (X : Type u) [DecidableEq X] (𝕜 : Type u) [CommRing 𝕜]
    [StarRing 𝕜] (d : ℕ) : QuasiLocalAlgebra X 𝕜 where
  net := cliffordNet X 𝕜 d
  isotony h := cliffordNet_isotony h
  superCommuting {S T} hdisj {i j x y} hx hy := by
    obtain rfl | rfl := zmod2_eq_zero_or_one' i <;> obtain rfl | rfl := zmod2_eq_zero_or_one' j
    · simp only [koszulSign_zero_left, one_smul]
      exact cliffordNet_commute_of_disjoint _ _ hdisj Finset.Subset.rfl x y
    · have hy0 : y = 0 := (MonoidAlgebra.mem_trivialGrading_one_iff y).mp hy
      simp [hy0]
    · have hx0 : x = 0 := (MonoidAlgebra.mem_trivialGrading_one_iff x).mp hx
      simp [hx0]
    · have hx0 : x = 0 := (MonoidAlgebra.mem_trivialGrading_one_iff x).mp hx
      simp [hx0]

end PauliGroup
