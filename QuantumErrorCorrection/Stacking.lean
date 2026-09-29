import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.RingTheory.Flat.Basic
import QuantumErrorCorrection.SuperStarAlgCatMonoidal

/-!
# Stacking quasi-local algebras

Two quasi-local algebras `A`, `B` on the same sites *stack* to the quasi-local algebra with local
algebras `A(S) ⊗ˢ B(S)`, the super tensor product. Its net is the pointwise tensor product
`A.net ⊗ B.net` in the functor category `RegionCat X ⥤ SuperStarAlgCat 𝕜`, which is monoidal
(and symmetric) because `SuperStarAlgCat 𝕜` is.

* *Isotony* of the stacked net needs the tensor product of two injective maps to be injective.
  Over a general commutative ring this can fail, so it is proved under flatness of the local
  algebras (`TensorProduct.map_injective_of_flat_flat`). The stacked algebras are again flat.
* *Microcausality* reduces to homogeneous pure tensors. For `a ⊗ b` on `S` and `c ⊗ d` on a
  disjoint `T`, the super-commutation of each factor gives
  `(a ⊗ b)(c ⊗ d) = koszulSign |a ⊗ b| |c ⊗ d| • (c ⊗ d)(a ⊗ b)`.

The unit for stacking, `QuasiLocalAlgebra.stackUnit`, is the trivial system: `𝕜`, purely even,
on every region.
-/

noncomputable section

open CategoryTheory MonoidalCategory SuperStarAlgebra SuperTensor SuperStarAlgCat RegionCat

universe u

variable {X : Type u} [DecidableEq X] {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]

omit [DecidableEq X] [StarRing 𝕜] in
/-- The sign bookkeeping behind microcausality of a stacked net. -/
private lemma stack_sign (i₁ j₁ i₂ j₂ : ZMod 2) :
    koszulSign 𝕜 j₁ i₂ * koszulSign 𝕜 i₁ i₂ * koszulSign 𝕜 j₁ j₂ =
      koszulSign 𝕜 (i₁ + j₁) (i₂ + j₂) * koszulSign 𝕜 j₂ i₁ := by
  rcases zmod_two_cases i₁ with rfl | rfl <;> rcases zmod_two_cases j₁ with rfl | rfl <;>
    rcases zmod_two_cases i₂ with rfl | rfl <;> rcases zmod_two_cases j₂ with rfl | rfl <;>
    simp [koszulSign, zmod_two_one_add_one]

section SuperCommute

variable {A₁ : Type u} [Ring A₁] [StarRing A₁] [Algebra 𝕜 A₁] [StarModule 𝕜 A₁]
  [SuperStarAlgebra 𝕜 A₁]
variable {A₂ : Type u} [Ring A₂] [StarRing A₂] [Algebra 𝕜 A₂] [StarModule 𝕜 A₂]
  [SuperStarAlgebra 𝕜 A₂]
variable {A₃ : Type u} [Ring A₃] [StarRing A₃] [Algebra 𝕜 A₃] [StarModule 𝕜 A₃]
  [SuperStarAlgebra 𝕜 A₃]
variable {B₁ : Type u} [Ring B₁] [StarRing B₁] [Algebra 𝕜 B₁] [StarModule 𝕜 B₁]
  [SuperStarAlgebra 𝕜 B₁]
variable {B₂ : Type u} [Ring B₂] [StarRing B₂] [Algebra 𝕜 B₂] [StarModule 𝕜 B₂]
  [SuperStarAlgebra 𝕜 B₂]
variable {B₃ : Type u} [Ring B₃] [StarRing B₃] [Algebra 𝕜 B₃] [StarModule 𝕜 B₃]
  [SuperStarAlgebra 𝕜 B₃]

omit [DecidableEq X] in
/-- If two pairs of grading-preserving maps into `A₃` and `B₃` have super-commuting images, then
so do their super tensor products. -/
private theorem map_superCommute (f : A₁ →⋆ₐ[𝕜] A₃) (f' : A₂ →⋆ₐ[𝕜] A₃)
    (g : B₁ →⋆ₐ[𝕜] B₃) (g' : B₂ →⋆ₐ[𝕜] B₃)
    (hf : ∀ {i : ZMod 2} {x : A₁}, x ∈ superGrading 𝕜 A₁ i → f x ∈ superGrading 𝕜 A₃ i)
    (hf' : ∀ {i : ZMod 2} {x : A₂}, x ∈ superGrading 𝕜 A₂ i → f' x ∈ superGrading 𝕜 A₃ i)
    (hg : ∀ {i : ZMod 2} {x : B₁}, x ∈ superGrading 𝕜 B₁ i → g x ∈ superGrading 𝕜 B₃ i)
    (hg' : ∀ {i : ZMod 2} {x : B₂}, x ∈ superGrading 𝕜 B₂ i → g' x ∈ superGrading 𝕜 B₃ i)
    (hA : ∀ {i j : ZMod 2} {a : A₁} {c : A₂}, a ∈ superGrading 𝕜 A₁ i →
      c ∈ superGrading 𝕜 A₂ j → f a * f' c = koszulSign 𝕜 i j • (f' c * f a))
    (hB : ∀ {i j : ZMod 2} {b : B₁} {d : B₂}, b ∈ superGrading 𝕜 B₁ i →
      d ∈ superGrading 𝕜 B₂ j → g b * g' d = koszulSign 𝕜 i j • (g' d * g b))
    {i j : ZMod 2} {x : SuperTensor 𝕜 A₁ B₁} {y : SuperTensor 𝕜 A₂ B₂}
    (hx : x ∈ superGrading 𝕜 (SuperTensor 𝕜 A₁ B₁) i)
    (hy : y ∈ superGrading 𝕜 (SuperTensor 𝕜 A₂ B₂) j) :
    SuperTensor.map f g hf hg x * SuperTensor.map f' g' hf' hg' y =
      koszulSign 𝕜 i j • (SuperTensor.map f' g' hf' hg' y * SuperTensor.map f g hf hg x) := by
  refine tensorGrading_induction (P := fun x =>
      SuperTensor.map f g hf hg x * SuperTensor.map f' g' hf' hg' y =
        koszulSign 𝕜 i j • (SuperTensor.map f' g' hf' hg' y * SuperTensor.map f g hf hg x)) hx
    (by simp) (fun x x' h h' => by rw [map_add, add_mul, mul_add, smul_add, h, h'])
    fun {i₁ j₁} a b ha hb hab => ?_
  refine tensorGrading_induction (P := fun y =>
      SuperTensor.map f g hf hg (a ⊗ˢ[𝕜] b) * SuperTensor.map f' g' hf' hg' y =
        koszulSign 𝕜 i j • (SuperTensor.map f' g' hf' hg' y *
          SuperTensor.map f g hf hg (a ⊗ˢ[𝕜] b))) hy
    (by simp) (fun y y' h h' => by rw [map_add, add_mul, mul_add, smul_add, h, h'])
    fun {i₂ j₂} c d hc hd hcd => ?_
  rw [map_tmul, map_tmul, tmul_mul_tmul _ _ (hg hb) (hf' hc), tmul_mul_tmul _ _ (hg' hd) (hf ha),
    hA ha hc, hB hb hd, ← smul_tmul', tmul_smul, smul_smul, smul_smul, smul_smul, ← hab, ← hcd,
    stack_sign]

end SuperCommute

namespace QuasiLocalAlgebra

variable (A B : QuasiLocalAlgebra X 𝕜)

/-- The stack of two quasi-local algebras with flat local algebras: the local algebra on `S` is
`A(S) ⊗ˢ B(S)`, the super tensor product. -/
def stack (hA : ∀ S, Module.Flat 𝕜 (A.net.obj S)) (hB : ∀ S, Module.Flat 𝕜 (B.net.obj S)) :
    QuasiLocalAlgebra X 𝕜 where
  net := A.net ⊗ B.net
  isotony {S T} h := by
    have := hA T
    have := hB S
    exact TensorProduct.map_injective_of_flat_flat _ _ (A.isotony h) (B.isotony h)
  superCommuting {S T} hST {i j} {x} {y} hx hy :=
    map_superCommute (A.net.map (homOfSubset Finset.subset_union_left)).1
      (A.net.map (homOfSubset Finset.subset_union_right)).1
      (B.net.map (homOfSubset Finset.subset_union_left)).1
      (B.net.map (homOfSubset Finset.subset_union_right)).1
      (A.net.map _).2 (A.net.map _).2 (B.net.map _).2 (B.net.map _).2
      (fun ha hc => A.superCommuting hST ha hc) (fun hb hd => B.superCommuting hST hb hd) hx hy

theorem stack_flat (hA : ∀ S, Module.Flat 𝕜 (A.net.obj S))
    (hB : ∀ S, Module.Flat 𝕜 (B.net.obj S)) (S : RegionCat X) :
    Module.Flat 𝕜 ((A.stack B hA hB).net.obj S) := by
  have := hA S
  have := hB S
  show Module.Flat 𝕜 (SuperTensor 𝕜 (A.net.obj S) (B.net.obj S))
  exact Module.Flat.of_linearEquiv (SuperTensor.of 𝕜 (A.net.obj S) (B.net.obj S)).symm

variable (X 𝕜) in
/-- The unit for stacking: the trivial system, with the base ring `𝕜` (purely even) on every
region. -/
def stackUnit : QuasiLocalAlgebra X 𝕜 where
  net := 𝟙_ (RegionCat X ⥤ SuperStarAlgCat 𝕜)
  isotony _ := Function.injective_id
  superCommuting {S T} _ {i j} {x} {y} hx hy := by
    dsimp only
    let x' : 𝕜 := x
    let y' : 𝕜 := y
    have hx' : x' ∈ superGrading 𝕜 𝕜 i := hx
    have hy' : y' ∈ superGrading 𝕜 𝕜 j := hy
    show x' * y' = koszulSign 𝕜 i j • (y' * x')
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · rw [hi, hj, koszulSign_zero_left, one_smul, mul_comm]
      · rw [eq_zero_of_mem_unitGrading 𝕜 hy' hj, mul_zero, zero_mul, smul_zero]
    · rw [eq_zero_of_mem_unitGrading 𝕜 hx' hi, mul_zero, zero_mul, smul_zero]

theorem stackUnit_flat (S : RegionCat X) : Module.Flat 𝕜 ((stackUnit X 𝕜).net.obj S) :=
  Module.Flat.self

end QuasiLocalAlgebra
