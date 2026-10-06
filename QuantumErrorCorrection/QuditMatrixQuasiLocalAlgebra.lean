import QuantumErrorCorrection.QuasiLocalAlgebra
import QuantumErrorCorrection.Stoquastic

/-!
# The quasi-local algebra of qudit matrices

Assembles a `QuasiLocalAlgebra` out of the net of all matrices on qudit configurations
(`quditMatrixFunctor` in `Stoquastic.lean`): to a finite region the `*`-algebra of all matrices
on its configurations, with the conjugate transpose as `star`, placed in degree `0`
(`StarAlgCat.toPurelyEvenSuperStarAlgCat`); to a region inclusion `A ↦ A ⊗ 1`.

This is where the stoquastic net lands once its cones are forgotten
(`stoquasticFunctor_forgetCone`), but nothing here refers to stoquasticity or to an order on
`R`.

* *Isotony* is `extendAlongRegion_injective`: `A ↦ A ⊗ 1` is injective as long as each qudit has
  at least one level (`NeZero d`). For `d = 0` it fails: the empty region has one configuration
  and a nonempty region has none.
* *Microcausality* reduces, since everything is even, to plain commutation of matrices extended
  from disjoint regions, `extendAlongRegion_commute`.
-/

open CategoryTheory

universe u

private lemma quditMatrixQuasiLocalAlgebra_zmod_two_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  revert i; decide

/-- The quasi-local algebra of all qudit matrices on a site set `X` with `d`-level qudits: to
each finite region the matrices on its configurations, purely even, with the conjugate transpose
as `star`; to each inclusion `A ↦ A ⊗ 1`. -/
noncomputable def quditMatrixQuasiLocalAlgebra (X : Type u) [DecidableEq X] (d : ℕ) [NeZero d]
    (R : Type u) [CommRing R] [StarRing R] : QuasiLocalAlgebra X R where
  net := quditMatrixFunctor X d R ⋙ StarAlgCat.toPurelyEvenSuperStarAlgCat R
  isotony h := extendAlongRegion_injective (RegionCat.homOfSubset h)
  superCommuting {S T} hST {i j x y} hx _ := by
    rcases quditMatrixQuasiLocalAlgebra_zmod_two_cases i with rfl | rfl
    · simp only [koszulSign_zero_left, one_smul]
      exact extendAlongRegion_commute hST _ _ x y
    · have hx0 : x = 0 :=
        StarAlgCat.eq_zero_of_mem_grading_one_toPurelyEvenSuperStarAlgCat R _ hx
      subst hx0
      simp

/-- The stoquastic net, with its cones forgotten and everything placed in degree `0`, is the net
of `quditMatrixQuasiLocalAlgebra`. -/
theorem stoquasticFunctor_forgetCone_toPurelyEven (X : Type u) [DecidableEq X] (d : ℕ)
    [NeZero d] (R : Type u) [CommRing R] [PartialOrder R] [IsOrderedRing R] [StarRing R]
    [TrivialStar R] :
    stoquasticFunctor X d R ⋙ PointedConeAlgCat.forgetCone ⋙
      StarAlgCat.toPurelyEvenSuperStarAlgCat R = (quditMatrixQuasiLocalAlgebra X d R).net := by
  rw [← Functor.assoc, stoquasticFunctor_forgetCone]
  rfl
