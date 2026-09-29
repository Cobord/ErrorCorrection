import Mathlib.RingTheory.TensorProduct.Basic
import QuantumErrorCorrection.QuasiLocalAlgebra

/-!
# Super tensor products of super `*`-algebras

The super tensor product `A ⊗ˢ B` of two `ZMod 2`-graded `*`-algebras: the module `A ⊗[𝕜] B`
with the Koszul-signed multiplication

  `(a ⊗ b) (c ⊗ d) = koszulSign |b| |c| • (a c ⊗ b d)`

for homogeneous `b`, `c`. The sign is built in explicitly from the project's `koszulSign`.
The grading alone does not determine it: `ZMod 2`-graded modules carry both the Koszul and the
trivial symmetric structure, and the choice here is the Koszul (super) one, matching the
microcausality axiom of `QuasiLocalAlgebra`. Concretely, the product is
`x * y = ∑ j i, koszulSign j i • ((1 ⊗ π_j) x) ((π_i ⊗ 1) y)`, where `π_i` are the parity
projections and the product on the right is the ordinary (unsigned) one of
`Algebra.TensorProduct`.

## Main definitions

* `SuperStarAlgebra.parityProj i`: the projection onto the parity-`i` part.
* `SuperStarAlgebra.one_mem_grading_zero`: `1` is even. This follows from the other axioms.
* `SuperTensor 𝕜 A B`: the super tensor product, with its `Ring` and `Algebra 𝕜` structure.
-/

noncomputable section

open DirectSum TensorProduct

universe u

/-! ### Parity projections -/

namespace SuperStarAlgebra

variable {𝕜 : Type u} {A : Type u} [CommRing 𝕜] [StarRing 𝕜] [Ring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A] [SuperStarAlgebra 𝕜 A]

/-- The `ZMod 2`-grading of a super `*`-algebra. -/
abbrev superGrading (𝕜 : Type u) (A : Type u) [CommRing 𝕜] [StarRing 𝕜] [Ring A] [StarRing A]
    [Algebra 𝕜 A] [StarModule 𝕜 A] [SuperStarAlgebra 𝕜 A] : ZMod 2 → Submodule 𝕜 A :=
  SuperVectorSpace.grading (𝕜 := 𝕜) (V := A)

variable (𝕜) in
/-- The projection of a super `*`-algebra onto its parity-`i` part. -/
def parityProj (i : ZMod 2) : A →ₗ[𝕜] A :=
  (superGrading 𝕜 A i).subtype ∘ₗ DirectSum.component 𝕜 (ZMod 2) (fun i => superGrading 𝕜 A i) i ∘ₗ
    (decomposeLinearEquiv (superGrading 𝕜 A)).toLinearMap

theorem parityProj_apply (i : ZMod 2) (a : A) :
    parityProj 𝕜 i a = (decompose (superGrading 𝕜 A) a i : A) :=
  rfl

theorem parityProj_mem (i : ZMod 2) (a : A) : parityProj 𝕜 i a ∈ superGrading 𝕜 A i :=
  (decompose (superGrading 𝕜 A) a i).2

theorem parityProj_of_mem {i : ZMod 2} {a : A} (ha : a ∈ superGrading 𝕜 A i) :
    parityProj 𝕜 i a = a :=
  decompose_of_mem_same _ ha

theorem parityProj_of_mem_ne {i j : ZMod 2} {a : A} (ha : a ∈ superGrading 𝕜 A i) (h : i ≠ j) :
    parityProj 𝕜 j a = 0 :=
  decompose_of_mem_ne _ ha h

/-- A sum over the two parities. -/
theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ i : ZMod 2, f i = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- Every element is the sum of its even and odd parts. -/
theorem parityProj_add_parityProj (a : A) : parityProj 𝕜 0 a + parityProj 𝕜 1 a = a := by
  classical
  rw [← sum_zmod_two (fun i => parityProj 𝕜 i a)]
  simp only [parityProj_apply]
  conv_rhs => rw [← DirectSum.sum_support_decompose (superGrading 𝕜 A) a]
  exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simpa using hi).symm

private lemma add_one_ne (i : ZMod 2) : i + 1 ≠ i := by
  rcases zmod_two_cases i with rfl | rfl <;> decide

/-- The unit of a super `*`-algebra is even. Write `1 = e₀ + e₁`; for homogeneous `x` of degree
`i`, comparing parity-`(i + 1)` parts of `x = x e₀ + x e₁` gives `x e₁ = 0`, hence
`e₁ = (e₀ + e₁) e₁ = 0`. -/
theorem one_mem_grading_zero : (1 : A) ∈ superGrading 𝕜 A 0 := by
  set e₀ : A := parityProj 𝕜 0 (1 : A)
  set e₁ : A := parityProj 𝕜 1 (1 : A)
  have h1 : e₀ + e₁ = 1 := parityProj_add_parityProj (1 : A)
  have he₀ : e₀ ∈ superGrading 𝕜 A 0 := parityProj_mem 0 1
  have he₁ : e₁ ∈ superGrading 𝕜 A 1 := parityProj_mem 1 1
  have key : ∀ (i : ZMod 2) (x : A), x ∈ superGrading 𝕜 A i → x * e₁ = 0 := by
    intro i x hx
    have hx₀ : x * e₀ ∈ superGrading 𝕜 A (i + 0) := grading_mul_mem hx he₀
    have hx₁ : x * e₁ ∈ superGrading 𝕜 A (i + 1) := grading_mul_mem hx he₁
    rw [add_zero] at hx₀
    have hsplit : x = x * e₀ + x * e₁ := by rw [← mul_add, h1, mul_one]
    have := congrArg (parityProj 𝕜 (i + 1)) hsplit
    rwa [map_add, parityProj_of_mem_ne hx (add_one_ne i).symm,
      parityProj_of_mem_ne hx₀ (add_one_ne i).symm, parityProj_of_mem hx₁, zero_add,
      eq_comm] at this
  have he₁0 : e₁ = 0 := by
    calc e₁ = (e₀ + e₁) * e₁ := by rw [h1, one_mul]
      _ = 0 := by rw [add_mul, key 0 e₀ he₀, key 1 e₁ he₁, add_zero]
  rw [← h1, he₁0, add_zero]
  exact he₀

end SuperStarAlgebra

/-! ### The Koszul-signed product on `A ⊗[𝕜] B` -/

namespace SuperTensor

open SuperStarAlgebra

variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]
variable {A : Type u} [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A] [SuperStarAlgebra 𝕜 A]
variable {B : Type u} [Ring B] [StarRing B] [Algebra 𝕜 B] [StarModule 𝕜 B] [SuperStarAlgebra 𝕜 B]

/-- Induction over homogeneous pure tensors: an additively closed property holding on every
`a ⊗ b` with `a`, `b` homogeneous holds on all of `A ⊗[𝕜] B`. -/
theorem induction_homogeneous {P : A ⊗[𝕜] B → Prop} (x : A ⊗[𝕜] B) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (tmul : ∀ {i j : ZMod 2} (a : A) (b : B), a ∈ superGrading 𝕜 A i →
      b ∈ superGrading 𝕜 B j → P (a ⊗ₜ[𝕜] b)) : P x := by
  induction x using TensorProduct.induction_on with
  | zero => exact zero
  | tmul a b =>
    rw [← parityProj_add_parityProj (𝕜 := 𝕜) a, ← parityProj_add_parityProj (𝕜 := 𝕜) b,
      add_tmul, tmul_add, tmul_add]
    exact add _ _ (add _ _ (tmul _ _ (parityProj_mem _ _) (parityProj_mem _ _))
        (tmul _ _ (parityProj_mem _ _) (parityProj_mem _ _)))
      (add _ _ (tmul _ _ (parityProj_mem _ _) (parityProj_mem _ _))
        (tmul _ _ (parityProj_mem _ _) (parityProj_mem _ _)))
  | add x y hx hy => exact add _ _ hx hy

variable (𝕜 A B) in
/-- The Koszul-signed product on `A ⊗[𝕜] B`:
`x * y = ∑ j i, koszulSign j i • ((1 ⊗ π_j) x) ((π_i ⊗ 1) y)`. -/
def superMul : A ⊗[𝕜] B →ₗ[𝕜] A ⊗[𝕜] B →ₗ[𝕜] A ⊗[𝕜] B :=
  ∑ j : ZMod 2, ∑ i : ZMod 2, koszulSign 𝕜 j i •
    (LinearMap.mul 𝕜 (A ⊗[𝕜] B)).compl₁₂ ((parityProj 𝕜 j).lTensor A) ((parityProj 𝕜 i).rTensor B)

/-- The Koszul sign rule on homogeneous pure tensors. -/
theorem superMul_tmul {i j : ZMod 2} (a : A) {b : B} {c : A} (d : B)
    (hb : b ∈ superGrading 𝕜 B j) (hc : c ∈ superGrading 𝕜 A i) :
    superMul 𝕜 A B (a ⊗ₜ b) (c ⊗ₜ d) = koszulSign 𝕜 j i • ((a * c) ⊗ₜ (b * d)) := by
  simp only [superMul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
    LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.mul_apply',
    Algebra.TensorProduct.tmul_mul_tmul]
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [parityProj_of_mem_ne hb (Ne.symm hj')])
    (by simp), Finset.sum_eq_single i (fun i' _ hi' => by
      simp [parityProj_of_mem_ne hc (Ne.symm hi')]) (by simp), parityProj_of_mem hb,
    parityProj_of_mem hc]

theorem superMul_one_left (x : A ⊗[𝕜] B) : superMul 𝕜 A B 1 x = x := by
  induction x using induction_homogeneous with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | tmul c d hc _ =>
    rw [Algebra.TensorProduct.one_def, superMul_tmul _ _ one_mem_grading_zero hc,
      koszulSign_zero_left, one_smul, one_mul, one_mul]

theorem superMul_one_right (x : A ⊗[𝕜] B) : superMul 𝕜 A B x 1 = x := by
  induction x using induction_homogeneous with
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy]
  | tmul a b _ hb =>
    rw [Algebra.TensorProduct.one_def, superMul_tmul _ _ hb one_mem_grading_zero,
      koszulSign_zero_right, one_smul, mul_one, mul_one]

theorem superMul_assoc (x y z : A ⊗[𝕜] B) :
    superMul 𝕜 A B (superMul 𝕜 A B x y) z = superMul 𝕜 A B x (superMul 𝕜 A B y z) := by
  induction x using induction_homogeneous with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a b ha hb =>
  induction y using induction_homogeneous with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | tmul c d hc hd =>
  induction z using induction_homogeneous with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul e f he hf =>
    rw [superMul_tmul _ _ hb hc, LinearMap.map_smul₂,
      superMul_tmul _ _ (grading_mul_mem hb hd) he, superMul_tmul _ _ hd he, map_smul,
      superMul_tmul _ _ hb (grading_mul_mem hc he), smul_smul, smul_smul, mul_assoc a,
      mul_assoc b, koszulSign_add_left, koszulSign_add_right]
    congr 1
    ring

end SuperTensor

/-! ### The super tensor product as a ring -/

open SuperStarAlgebra

variable (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜]
variable (A : Type u) [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A] [SuperStarAlgebra 𝕜 A]
variable (B : Type u) [Ring B] [StarRing B] [Algebra 𝕜 B] [StarModule 𝕜 B] [SuperStarAlgebra 𝕜 B]

/-- The super tensor product `A ⊗ˢ B` of two super `*`-algebras: a type synonym for
`A ⊗[𝕜] B`, carrying the Koszul-signed multiplication `SuperTensor.superMul`. -/
def SuperTensor : Type u := A ⊗[𝕜] B

namespace SuperTensor

instance : AddCommGroupWithOne (SuperTensor 𝕜 A B) :=
  inferInstanceAs (AddCommGroupWithOne (A ⊗[𝕜] B))

instance : Module 𝕜 (SuperTensor 𝕜 A B) := inferInstanceAs (Module 𝕜 (A ⊗[𝕜] B))

/-- The identification of the underlying module with `A ⊗[𝕜] B`. -/
def of : A ⊗[𝕜] B ≃ₗ[𝕜] SuperTensor 𝕜 A B := LinearEquiv.refl _ _

variable {A B}

/-- The pure tensor `a ⊗ b` in the super tensor product. -/
def tmul (a : A) (b : B) : SuperTensor 𝕜 A B := of 𝕜 A B (a ⊗ₜ b)

@[inherit_doc] scoped notation:100 a " ⊗ˢ[" 𝕜 "] " b:100 => SuperTensor.tmul 𝕜 a b

variable {𝕜}

instance : Mul (SuperTensor 𝕜 A B) where
  mul x y := of 𝕜 A B (superMul 𝕜 A B ((of 𝕜 A B).symm x) ((of 𝕜 A B).symm y))

theorem mul_def (x y : SuperTensor 𝕜 A B) :
    x * y = of 𝕜 A B (superMul 𝕜 A B ((of 𝕜 A B).symm x) ((of 𝕜 A B).symm y)) :=
  rfl

omit [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [SuperStarAlgebra 𝕜 A] [StarRing B]
  [StarModule 𝕜 B] [SuperStarAlgebra 𝕜 B] in
theorem one_def : (1 : SuperTensor 𝕜 A B) = (1 : A) ⊗ˢ[𝕜] (1 : B) := rfl

/-- The Koszul sign rule: `(a ⊗ b)(c ⊗ d) = koszulSign |b| |c| • (a c ⊗ b d)`. -/
theorem tmul_mul_tmul {i j : ZMod 2} (a : A) {b : B} {c : A} (d : B)
    (hb : b ∈ superGrading 𝕜 B j) (hc : c ∈ superGrading 𝕜 A i) :
    a ⊗ˢ[𝕜] b * c ⊗ˢ[𝕜] d = koszulSign 𝕜 j i • ((a * c) ⊗ˢ[𝕜] (b * d)) :=
  superMul_tmul a d hb hc

instance : Monoid (SuperTensor 𝕜 A B) where
  one_mul x := superMul_one_left (𝕜 := 𝕜) x
  mul_one x := superMul_one_right (𝕜 := 𝕜) x
  mul_assoc x y z := superMul_assoc (𝕜 := 𝕜) x y z

instance : Ring (SuperTensor 𝕜 A B) where
  left_distrib x y z := map_add (superMul 𝕜 A B x) y z
  right_distrib x y z := LinearMap.map_add₂ (superMul 𝕜 A B) x y z
  zero_mul x := LinearMap.map_zero₂ (superMul 𝕜 A B) x
  mul_zero x := map_zero (superMul 𝕜 A B x)

instance : Algebra 𝕜 (SuperTensor 𝕜 A B) :=
  Algebra.ofModule (fun r x y => LinearMap.map_smul₂ (superMul 𝕜 A B) r x y)
    (fun r x y => map_smul (superMul 𝕜 A B x) r y)

/-- Induction over homogeneous pure tensors in the super tensor product. -/
theorem induction_on {P : SuperTensor 𝕜 A B → Prop} (x : SuperTensor 𝕜 A B) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (tmul : ∀ {i j : ZMod 2} (a : A) (b : B), a ∈ superGrading 𝕜 A i →
      b ∈ superGrading 𝕜 B j → P (a ⊗ˢ[𝕜] b)) : P x :=
  induction_homogeneous (P := fun y => P (of 𝕜 A B y)) ((of 𝕜 A B).symm x) zero
    (fun _ _ hx hy => add _ _ hx hy) tmul

theorem smul_tmul' (r : 𝕜) (a : A) (b : B) : r • (a ⊗ˢ[𝕜] b) = (r • a) ⊗ˢ[𝕜] b := rfl

theorem tmul_add (a : A) (b b' : B) : a ⊗ˢ[𝕜] (b + b') = a ⊗ˢ[𝕜] b + a ⊗ˢ[𝕜] b' :=
  congrArg (of 𝕜 A B) (TensorProduct.tmul_add a b b')

@[simp] theorem tmul_zero (a : A) : a ⊗ˢ[𝕜] (0 : B) = 0 :=
  congrArg (of 𝕜 A B) (TensorProduct.tmul_zero B a)

/-! #### The grading: `a ⊗ b` has parity `|a| + |b|` -/

/-- The parity-`k` projection of `A ⊗ˢ B`: `∑ i, π_i ⊗ π_{k - i}`. -/
def tensorProj (k : ZMod 2) : SuperTensor 𝕜 A B →ₗ[𝕜] SuperTensor 𝕜 A B :=
  ∑ i : ZMod 2, (of 𝕜 A B).toLinearMap ∘ₗ
    TensorProduct.map (parityProj 𝕜 i) (parityProj 𝕜 (k - i)) ∘ₗ (of 𝕜 A B).symm.toLinearMap

theorem tensorProj_tmul (k : ZMod 2) {i j : ZMod 2} {a : A} {b : B}
    (ha : a ∈ superGrading 𝕜 A i) (hb : b ∈ superGrading 𝕜 B j) :
    tensorProj k (a ⊗ˢ[𝕜] b) = if i + j = k then a ⊗ˢ[𝕜] b else 0 := by
  simp only [tensorProj, tmul, LinearMap.sum_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
  rw [Finset.sum_eq_single i (fun i' _ h => by simp [parityProj_of_mem_ne ha (Ne.symm h)])
    (by simp), parityProj_of_mem ha]
  split_ifs with hk
  · rw [show k - i = j by rw [← hk]; ring, parityProj_of_mem hb]
  · rw [parityProj_of_mem_ne hb (fun h => hk (by rw [h]; ring)), TensorProduct.tmul_zero,
      map_zero]

theorem sum_tensorProj (x : SuperTensor 𝕜 A B) : ∑ k : ZMod 2, tensorProj k x = x := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | tmul a b ha hb =>
    simp only [tensorProj_tmul _ ha hb, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem tensorProj_tensorProj (k k' : ZMod 2) (x : SuperTensor 𝕜 A B) :
    tensorProj k (tensorProj k' x) = if k = k' then tensorProj k x else 0 := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]; split_ifs <;> simp
  | @tmul i j a b ha hb =>
    by_cases h : k = k'
    · subst h
      simp only [↓reduceIte, tensorProj_tmul _ ha hb]
      split_ifs with h1
      · rw [tensorProj_tmul _ ha hb]
        simp only [h1, ↓reduceIte]
      · rw [map_zero]
    · simp only [h, ↓reduceIte, tensorProj_tmul _ ha hb]
      split_ifs with h1
      · have h2 : ¬ i + j = k := fun h2 => h (h2.symm.trans h1)
        rw [tensorProj_tmul _ ha hb]
        simp only [h2, ↓reduceIte]
      · rw [map_zero]

/-- The parity-`k` part of `A ⊗ˢ B`. -/
def tensorGrading (k : ZMod 2) : Submodule 𝕜 (SuperTensor 𝕜 A B) :=
  LinearMap.range (tensorProj k)

theorem mem_tensorGrading_iff {k : ZMod 2} {x : SuperTensor 𝕜 A B} :
    x ∈ tensorGrading k ↔ tensorProj k x = x := by
  refine ⟨?_, fun h => ⟨x, h⟩⟩
  rintro ⟨y, rfl⟩
  simp only [tensorProj_tensorProj, ↓reduceIte]

theorem tmul_mem_tensorGrading {i j : ZMod 2} {a : A} {b : B}
    (ha : a ∈ superGrading 𝕜 A i) (hb : b ∈ superGrading 𝕜 B j) :
    a ⊗ˢ[𝕜] b ∈ tensorGrading (i + j) :=
  mem_tensorGrading_iff.2 (by simp only [tensorProj_tmul _ ha hb, ↓reduceIte])

/-- Induction over a graded piece: an additively closed property holding on homogeneous pure
tensors of parity `k` holds on all of `tensorGrading k`. -/
theorem tensorGrading_induction {k : ZMod 2} {P : SuperTensor 𝕜 A B → Prop}
    {x : SuperTensor 𝕜 A B} (hx : x ∈ tensorGrading k) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (tmul : ∀ {i j : ZMod 2} (a : A) (b : B), a ∈ superGrading 𝕜 A i →
      b ∈ superGrading 𝕜 B j → i + j = k → P (a ⊗ˢ[𝕜] b)) : P x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using induction_on with
  | zero => simpa using zero
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy
  | tmul a b ha hb =>
    rw [tensorProj_tmul _ ha hb]
    split_ifs with h
    · exact tmul a b ha hb h
    · exact zero

/-- The parity components of an element, as an element of the direct sum. -/
private def tensorDecompose :
    SuperTensor 𝕜 A B →ₗ[𝕜] ⨁ k, tensorGrading (𝕜 := 𝕜) (A := A) (B := B) k :=
  ∑ k : ZMod 2,
    DirectSum.lof 𝕜 (ZMod 2) (fun k => tensorGrading (𝕜 := 𝕜) (A := A) (B := B) k) k ∘ₗ
      LinearMap.codRestrict (tensorGrading k) (tensorProj k) fun x => LinearMap.mem_range_self _ x

private lemma tensorDecompose_apply (x : SuperTensor 𝕜 A B) :
    tensorDecompose x = ∑ k : ZMod 2, DirectSum.lof 𝕜 (ZMod 2)
      (fun k => tensorGrading (𝕜 := 𝕜) (A := A) (B := B) k) k
        ⟨tensorProj k x, LinearMap.mem_range_self _ x⟩ := by
  simp only [tensorDecompose, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

/-- The decomposition of `A ⊗ˢ B` into its parity parts. -/
instance tensorDecomposition : Decomposition (tensorGrading (𝕜 := 𝕜) (A := A) (B := B)) :=
  Decomposition.ofLinearMap _ tensorDecompose
    (by
      ext x
      rw [LinearMap.comp_apply, tensorDecompose_apply, map_sum]
      simp only [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of, LinearMap.id_apply]
      exact sum_tensorProj x)
    (by
      refine DirectSum.linearMap_ext _ fun k => LinearMap.ext fun ⟨x, hx⟩ => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, DirectSum.lof_eq_of,
        DirectSum.coeLinearMap_of, tensorDecompose_apply]
      rw [Finset.sum_eq_single k]
      · congr 1
        exact Subtype.ext (mem_tensorGrading_iff.1 hx)
      · intro k' _ hk'
        have : tensorProj k' x = 0 := by
          rw [← mem_tensorGrading_iff.1 hx, tensorProj_tensorProj]
          simp only [hk', ↓reduceIte]
        rw [show (⟨tensorProj k' x, LinearMap.mem_range_self _ x⟩ :
          tensorGrading (𝕜 := 𝕜) (A := A) (B := B) k') = 0 from Subtype.ext this, map_zero]
      · simp)

theorem mul_mem_tensorGrading {k k' : ZMod 2} {x y : SuperTensor 𝕜 A B}
    (hx : x ∈ tensorGrading k) (hy : y ∈ tensorGrading k') :
    x * y ∈ tensorGrading (k + k') := by
  refine tensorGrading_induction (P := fun x => x * y ∈ tensorGrading (k + k')) hx
    (by rw [zero_mul]; exact zero_mem _) (fun x x' hx hx' => by rw [add_mul]; exact add_mem hx hx')
    fun {i j} a b ha hb hab => ?_
  refine tensorGrading_induction (P := fun y => a ⊗ˢ[𝕜] b * y ∈ tensorGrading (k + k')) hy
    (by rw [mul_zero]; exact zero_mem _) (fun y y' hy hy' => by rw [mul_add]; exact add_mem hy hy')
    fun {i' j'} c d hc hd hcd => ?_
  rw [tmul_mul_tmul a d hb hc]
  refine Submodule.smul_mem _ _ ?_
  have e : (i + i') + (j + j') = k + k' := by rw [← hab, ← hcd]; ring
  rw [← e]
  exact tmul_mem_tensorGrading (grading_mul_mem ha hc) (grading_mul_mem hb hd)

/-! #### The Koszul-signed star: `star (a ⊗ b) = koszulSign |a| |b| • (star a ⊗ star b)` -/

/-- The biadditive map `(a, b) ↦ ∑ i j, koszulSign i j • (star (π_i a) ⊗ star (π_j b))`. -/
private def starBiadd : A →+ B →+ A ⊗[𝕜] B :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
      (fun b => ∑ i : ZMod 2, ∑ j : ZMod 2,
        koszulSign 𝕜 i j • (star (parityProj 𝕜 i a) ⊗ₜ[𝕜] star (parityProj 𝕜 j b)))
      fun b b' => by
        simp only [map_add, star_add, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib])
    fun a a' => by
      ext b
      simp only [map_add, star_add, TensorProduct.add_tmul, smul_add, Finset.sum_add_distrib,
        AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]

private def starAux : A ⊗[𝕜] B →+ A ⊗[𝕜] B :=
  TensorProduct.liftAddHom starBiadd fun r a b => by
    simp only [starBiadd, AddMonoidHom.mk'_apply, map_smul, star_smul, TensorProduct.smul_tmul]

instance : Star (SuperTensor 𝕜 A B) where
  star x := of 𝕜 A B (starAux ((of 𝕜 A B).symm x))

private lemma star_def (x : SuperTensor 𝕜 A B) :
    star x = of 𝕜 A B (starAux ((of 𝕜 A B).symm x)) :=
  rfl

theorem star_tmul {i j : ZMod 2} {a : A} {b : B} (ha : a ∈ superGrading 𝕜 A i)
    (hb : b ∈ superGrading 𝕜 B j) :
    star (a ⊗ˢ[𝕜] b) = koszulSign 𝕜 i j • (star a ⊗ˢ[𝕜] star b) := by
  rw [star_def, tmul, LinearEquiv.symm_apply_apply, starAux, TensorProduct.liftAddHom_tmul]
  simp only [starBiadd, AddMonoidHom.mk'_apply]
  rw [Finset.sum_eq_single i (fun i' _ h => by simp [parityProj_of_mem_ne ha (Ne.symm h)])
    (by simp), Finset.sum_eq_single j (fun j' _ h => by
      simp [parityProj_of_mem_ne hb (Ne.symm h)]) (by simp), parityProj_of_mem ha,
    parityProj_of_mem hb, map_smul]
  rfl

theorem star_add' (x y : SuperTensor 𝕜 A B) : star (x + y) = star x + star y := by
  simp only [star_def, map_add]

theorem star_zero' : star (0 : SuperTensor 𝕜 A B) = 0 := by
  simp only [star_def, map_zero]

theorem star_smul' (r : 𝕜) (x : SuperTensor 𝕜 A B) : star (r • x) = star r • star x := by
  induction x using induction_on with
  | zero => rw [smul_zero, star_zero', smul_zero]
  | add x y hx hy => rw [smul_add, star_add', star_add', hx, hy, smul_add]
  | tmul a b ha hb =>
    rw [smul_tmul', star_tmul (Submodule.smul_mem _ r ha) hb, star_tmul ha hb, star_smul,
      smul_comm (star r) (koszulSign 𝕜 _ _)]
    rfl

private lemma star_star_sign (i j : ZMod 2) :
    star (koszulSign 𝕜 i j) * koszulSign 𝕜 i j = 1 := by
  rw [star_koszulSign, koszulSign_mul_self]

theorem star_star' (x : SuperTensor 𝕜 A B) : star (star x) = x := by
  induction x using induction_on with
  | zero => rw [star_zero', star_zero']
  | add x y hx hy => rw [star_add', star_add', hx, hy]
  | tmul a b ha hb =>
    rw [star_tmul ha hb, star_smul', star_tmul (grading_star_mem ha) (grading_star_mem hb),
      star_star, star_star, smul_smul, star_star_sign, one_smul]

omit [StarRing 𝕜] in
/-- The sign bookkeeping behind `star (x y) = star y star x`. -/
private lemma star_mul_sign (i j i' j' : ZMod 2) :
    koszulSign 𝕜 j i' * koszulSign 𝕜 (i + i') (j + j') =
      koszulSign 𝕜 i' j' * koszulSign 𝕜 i j * koszulSign 𝕜 j' i := by
  rcases zmod_two_cases i with rfl | rfl <;> rcases zmod_two_cases j with rfl | rfl <;>
    rcases zmod_two_cases i' with rfl | rfl <;> rcases zmod_two_cases j' with rfl | rfl <;>
    simp [koszulSign, zmod_two_one_add_one]

theorem star_mul' (x y : SuperTensor 𝕜 A B) : star (x * y) = star y * star x := by
  induction x using induction_on with
  | zero => rw [zero_mul, star_zero', mul_zero]
  | add x x' hx hx' => rw [add_mul, star_add', star_add', hx, hx', mul_add]
  | tmul a b ha hb =>
  induction y using induction_on with
  | zero => rw [mul_zero, star_zero', zero_mul]
  | add y y' hy hy' => rw [mul_add, star_add', star_add', hy, hy', add_mul]
  | tmul c d hc hd =>
    rw [tmul_mul_tmul a d hb hc, star_smul', star_koszulSign,
      star_tmul (grading_mul_mem ha hc) (grading_mul_mem hb hd), star_tmul hc hd, star_tmul ha hb,
      smul_mul_smul_comm, tmul_mul_tmul _ _ (grading_star_mem hd) (grading_star_mem ha),
      smul_smul, smul_smul, star_mul, star_mul, star_mul_sign]

instance : StarRing (SuperTensor 𝕜 A B) where
  star_involutive := star_star'
  star_mul := star_mul'
  star_add := star_add'

instance : StarModule 𝕜 (SuperTensor 𝕜 A B) where
  star_smul := star_smul'

theorem star_mem_tensorGrading {k : ZMod 2} {x : SuperTensor 𝕜 A B}
    (hx : x ∈ tensorGrading k) : star x ∈ tensorGrading k := by
  refine tensorGrading_induction (P := fun x => star x ∈ tensorGrading k) hx
    (by rw [star_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [star_add]; exact add_mem hx hy) fun {i j} a b ha hb hab => ?_
  rw [star_tmul ha hb, ← hab]
  exact Submodule.smul_mem _ _
    (tmul_mem_tensorGrading (grading_star_mem ha) (grading_star_mem hb))

/-- The super tensor product of two super `*`-algebras is a super `*`-algebra. -/
instance superStarAlgebra : SuperStarAlgebra 𝕜 (SuperTensor 𝕜 A B) where
  grading := tensorGrading
  decomposition := tensorDecomposition
  grading_mul_mem := mul_mem_tensorGrading
  grading_star_mem := star_mem_tensorGrading

theorem zero_tmul (b : B) : (0 : A) ⊗ˢ[𝕜] b = 0 :=
  congrArg (of 𝕜 A B) (TensorProduct.zero_tmul A b)

theorem add_tmul (a a' : A) (b : B) : (a + a') ⊗ˢ[𝕜] b = a ⊗ˢ[𝕜] b + a' ⊗ˢ[𝕜] b :=
  congrArg (of 𝕜 A B) (TensorProduct.add_tmul a a' b)

theorem tmul_smul (r : 𝕜) (a : A) (b : B) : a ⊗ˢ[𝕜] (r • b) = r • (a ⊗ˢ[𝕜] b) :=
  congrArg (of 𝕜 A B) (TensorProduct.tmul_smul r a b)

end SuperTensor

/-! ### The unit: the base ring, trivially graded -/

namespace SuperTensor

section Unit

variable (𝕜 : Type u) [CommRing 𝕜] [StarRing 𝕜]

/-- The trivial grading on the base ring: everything is even. -/
def unitGrading (i : ZMod 2) : Submodule 𝕜 𝕜 := if i = 0 then ⊤ else ⊥

omit [StarRing 𝕜] in
private lemma unitGrading_isInternal : DirectSum.IsInternal (unitGrading 𝕜) := by
  apply (DirectSum.isInternal_submodule_iff_isCompl (unitGrading 𝕜) (i := 0) (j := 1)
    (by decide) (by
      ext i
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      exact zmod_two_cases i)).2
  constructor
  · simp [unitGrading]
  · simp [unitGrading]

/-- The base ring as a (purely even) super vector space over itself. -/
instance unitSuperVectorSpace : SuperVectorSpace 𝕜 𝕜 where
  grading := unitGrading 𝕜
  decomposition := (unitGrading_isInternal 𝕜).chooseDecomposition

/-- The base ring is a (purely even) super `*`-algebra over itself. -/
instance unitSuperStarAlgebra : SuperStarAlgebra 𝕜 𝕜 where
  grading_mul_mem {i j x y} hx hy := by
    have hx' : x ∈ unitGrading 𝕜 i := hx
    have hy' : y ∈ unitGrading 𝕜 j := hy
    show x * y ∈ unitGrading 𝕜 (i + j)
    rcases zmod_two_cases i with rfl | rfl <;> rcases zmod_two_cases j with rfl | rfl <;>
      simp_all [unitGrading]
  grading_star_mem {i x} hx := by
    have hx' : x ∈ unitGrading 𝕜 i := hx
    show star x ∈ unitGrading 𝕜 i
    rcases zmod_two_cases i with rfl | rfl <;> simp_all [unitGrading]

theorem mem_unitGrading_zero (r : 𝕜) : r ∈ superGrading 𝕜 𝕜 0 := by
  show r ∈ unitGrading 𝕜 0
  simp [unitGrading]

theorem eq_zero_of_mem_unitGrading {i : ZMod 2} {r : 𝕜} (hr : r ∈ superGrading 𝕜 𝕜 i)
    (hi : i ≠ 0) : r = 0 := by
  have hr' : r ∈ unitGrading 𝕜 i := hr
  simpa [unitGrading, hi] using hr'

end Unit

/-! ### Structure maps: tensoring morphisms, associator, unitors -/

section Maps

variable {𝕜 : Type u} [CommRing 𝕜] [StarRing 𝕜]
variable {A : Type u} [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A] [SuperStarAlgebra 𝕜 A]
variable {B : Type u} [Ring B] [StarRing B] [Algebra 𝕜 B] [StarModule 𝕜 B] [SuperStarAlgebra 𝕜 B]
variable {C : Type u} [Ring C] [StarRing C] [Algebra 𝕜 C] [StarModule 𝕜 C] [SuperStarAlgebra 𝕜 C]
variable {A' : Type u} [Ring A'] [StarRing A'] [Algebra 𝕜 A'] [StarModule 𝕜 A']
  [SuperStarAlgebra 𝕜 A']
variable {B' : Type u} [Ring B'] [StarRing B'] [Algebra 𝕜 B'] [StarModule 𝕜 B']
  [SuperStarAlgebra 𝕜 B']

/-- An injective, grading-preserving linear map also reflects the grading. -/
theorem mem_of_map_mem (f : A →ₗ[𝕜] A') (hf_inj : Function.Injective f)
    (hf : ∀ {i : ZMod 2} {x : A}, x ∈ superGrading 𝕜 A i → f x ∈ superGrading 𝕜 A' i)
    {k : ZMod 2} {x : A} (hx : f x ∈ superGrading 𝕜 A' k) : x ∈ superGrading 𝕜 A k := by
  have hproj : ∀ i, parityProj 𝕜 i (f x) = f (parityProj 𝕜 i x) := by
    intro i
    conv_lhs => rw [← parityProj_add_parityProj (𝕜 := 𝕜) x, map_add, map_add]
    rcases zmod_two_cases i with rfl | rfl
    · rw [parityProj_of_mem (hf (parityProj_mem 0 x)),
        parityProj_of_mem_ne (hf (parityProj_mem 1 x)) (by decide), add_zero]
    · rw [parityProj_of_mem_ne (hf (parityProj_mem 0 x)) (by decide),
        parityProj_of_mem (hf (parityProj_mem 1 x)), zero_add]
  have hzero : ∀ i, i ≠ k → parityProj 𝕜 i x = 0 := fun i hi =>
    hf_inj (by rw [← hproj, parityProj_of_mem_ne hx (Ne.symm hi), map_zero])
  rw [← parityProj_add_parityProj (𝕜 := 𝕜) x]
  rcases zmod_two_cases k with rfl | rfl
  · rw [hzero 1 (by decide), add_zero]; exact parityProj_mem 0 x
  · rw [hzero 0 (by decide), zero_add]; exact parityProj_mem 1 x

/-- The underlying linear map of `f ⊗ g`. -/
def mapₗ (f : A →ₗ[𝕜] A') (g : B →ₗ[𝕜] B') : SuperTensor 𝕜 A B →ₗ[𝕜] SuperTensor 𝕜 A' B' :=
  (of 𝕜 A' B').toLinearMap ∘ₗ TensorProduct.map f g ∘ₗ (of 𝕜 A B).symm.toLinearMap

@[simp] theorem mapₗ_tmul (f : A →ₗ[𝕜] A') (g : B →ₗ[𝕜] B') (a : A) (b : B) :
    mapₗ f g (a ⊗ˢ[𝕜] b) = f a ⊗ˢ[𝕜] g b :=
  rfl

variable (f : A →⋆ₐ[𝕜] A') (g : B →⋆ₐ[𝕜] B')
  (hf : ∀ {i : ZMod 2} {x : A}, x ∈ superGrading 𝕜 A i → f x ∈ superGrading 𝕜 A' i)
  (hg : ∀ {i : ZMod 2} {x : B}, x ∈ superGrading 𝕜 B i → g x ∈ superGrading 𝕜 B' i)

include hf hg in
private lemma mapₗ_mul (x y : SuperTensor 𝕜 A B) :
    mapₗ f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap (x * y) =
      mapₗ f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap x *
        mapₗ f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap y := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul a b ha hb =>
  induction y using induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | tmul c d hc hd =>
    rw [tmul_mul_tmul a d hb hc, map_smul]
    simp only [mapₗ_tmul, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, map_mul]
    rw [tmul_mul_tmul _ _ (hg hb) (hf hc)]

include hf hg in
private lemma mapₗ_star (x : SuperTensor 𝕜 A B) :
    mapₗ f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap (star x) =
      star (mapₗ f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap x) := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [star_add, map_add, hx, hx']
  | tmul a b ha hb =>
    rw [star_tmul ha hb, map_smul]
    simp only [mapₗ_tmul, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, map_star]
    rw [star_tmul (hf ha) (hg hb)]

/-- The super tensor product `f ⊗ g` of two grading-preserving `*`-algebra homomorphisms. -/
def map : SuperTensor 𝕜 A B →⋆ₐ[𝕜] SuperTensor 𝕜 A' B' :=
  { AlgHom.ofLinearMap (mapₗ f.toAlgHom.toLinearMap g.toAlgHom.toLinearMap)
      (by rw [one_def, mapₗ_tmul]; simp only [AlgHom.toLinearMap_apply, map_one]; rfl)
      (mapₗ_mul f g hf hg) with
    map_star' := mapₗ_star f g hf hg }

@[simp] theorem map_tmul (a : A) (b : B) : map f g hf hg (a ⊗ˢ[𝕜] b) = f a ⊗ˢ[𝕜] g b :=
  rfl

include hf hg in
theorem map_mem {k : ZMod 2} {x : SuperTensor 𝕜 A B}
    (hx : x ∈ superGrading 𝕜 (SuperTensor 𝕜 A B) k) :
    map f g hf hg x ∈ superGrading 𝕜 (SuperTensor 𝕜 A' B') k := by
  refine tensorGrading_induction (P := fun x => map f g hf hg x ∈ tensorGrading k) hx
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy) fun {i j} a b ha hb hab => ?_
  rw [map_tmul, ← hab]
  exact tmul_mem_tensorGrading (hf ha) (hg hb)

/-! #### The associator -/

/-- Induction over homogeneous triple tensors `(a ⊗ b) ⊗ c`. -/
theorem induction_on₃ {P : SuperTensor 𝕜 (SuperTensor 𝕜 A B) C → Prop}
    (x : SuperTensor 𝕜 (SuperTensor 𝕜 A B) C) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (tmul : ∀ {i j k : ZMod 2} (a : A) (b : B) (c : C), a ∈ superGrading 𝕜 A i →
      b ∈ superGrading 𝕜 B j → c ∈ superGrading 𝕜 C k → P ((a ⊗ˢ[𝕜] b) ⊗ˢ[𝕜] c)) : P x := by
  induction x using induction_on with
  | zero => exact zero
  | add x y hx hy => exact add _ _ hx hy
  | tmul u c hu hc =>
    exact tensorGrading_induction (P := fun u => P (u ⊗ˢ[𝕜] c)) hu
      (by rw [zero_tmul]; exact zero) (fun u u' h h' => by rw [add_tmul]; exact add _ _ h h')
      fun a b ha hb _ => tmul a b c ha hb hc

variable (𝕜 A B C) in
/-- The underlying linear equivalence of the associator,
`(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)`. -/
def assocₗ :
    SuperTensor 𝕜 (SuperTensor 𝕜 A B) C ≃ₗ[𝕜] SuperTensor 𝕜 A (SuperTensor 𝕜 B C) :=
  (of 𝕜 (SuperTensor 𝕜 A B) C).symm ≪≫ₗ
    TensorProduct.congr (of 𝕜 A B).symm (LinearEquiv.refl 𝕜 C) ≪≫ₗ
    TensorProduct.assoc 𝕜 A B C ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl 𝕜 A) (of 𝕜 B C) ≪≫ₗ of 𝕜 A (SuperTensor 𝕜 B C)

@[simp] theorem assocₗ_tmul (a : A) (b : B) (c : C) :
    assocₗ 𝕜 A B C ((a ⊗ˢ[𝕜] b) ⊗ˢ[𝕜] c) = a ⊗ˢ[𝕜] (b ⊗ˢ[𝕜] c) :=
  rfl

private lemma assocₗ_mul (x y : SuperTensor 𝕜 (SuperTensor 𝕜 A B) C) :
    assocₗ 𝕜 A B C (x * y) = assocₗ 𝕜 A B C x * assocₗ 𝕜 A B C y := by
  induction x using induction_on₃ with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul a b c ha hb hc =>
  induction y using induction_on₃ with
  | zero => simp
  | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | tmul a' b' c' ha' hb' hc' =>
    rw [tmul_mul_tmul _ _ hc (tmul_mem_tensorGrading ha' hb'), tmul_mul_tmul _ _ hb ha',
      ← smul_tmul', smul_smul, map_smul, assocₗ_tmul, assocₗ_tmul, assocₗ_tmul,
      tmul_mul_tmul _ _ (tmul_mem_tensorGrading hb hc) ha', tmul_mul_tmul _ _ hc hb', tmul_smul,
      smul_smul, koszulSign_add_right, koszulSign_add_left]
    congr 1
    ring

private lemma assocₗ_star (x : SuperTensor 𝕜 (SuperTensor 𝕜 A B) C) :
    assocₗ 𝕜 A B C (star x) = star (assocₗ 𝕜 A B C x) := by
  induction x using induction_on₃ with
  | zero => simp
  | add x x' hx hx' => simp only [star_add, map_add, hx, hx']
  | tmul a b c ha hb hc =>
    rw [star_tmul (tmul_mem_tensorGrading ha hb) hc, star_tmul ha hb, ← smul_tmul', smul_smul,
      map_smul, assocₗ_tmul, assocₗ_tmul, star_tmul ha (tmul_mem_tensorGrading hb hc),
      star_tmul hb hc, tmul_smul, smul_smul, koszulSign_add_left, koszulSign_add_right]
    congr 1
    ring

theorem assocₗ_mem {n : ZMod 2} {x : SuperTensor 𝕜 (SuperTensor 𝕜 A B) C}
    (hx : x ∈ superGrading 𝕜 (SuperTensor 𝕜 (SuperTensor 𝕜 A B) C) n) :
    assocₗ 𝕜 A B C x ∈ superGrading 𝕜 (SuperTensor 𝕜 A (SuperTensor 𝕜 B C)) n := by
  refine tensorGrading_induction (P := fun x => assocₗ 𝕜 A B C x ∈ tensorGrading n) hx
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy) fun {i k} u c hu hc hik => ?_
  refine tensorGrading_induction (P := fun u => assocₗ 𝕜 A B C (u ⊗ˢ[𝕜] c) ∈ tensorGrading n) hu
    (by rw [zero_tmul, map_zero]; exact zero_mem _)
    (fun u u' h h' => by rw [add_tmul, map_add]; exact add_mem h h') fun {i' j'} a b ha hb hab => ?_
  rw [assocₗ_tmul, ← hik, ← hab, add_assoc]
  exact tmul_mem_tensorGrading ha (tmul_mem_tensorGrading hb hc)

theorem assocₗ_symm_mem {n : ZMod 2} {y : SuperTensor 𝕜 A (SuperTensor 𝕜 B C)}
    (hy : y ∈ superGrading 𝕜 (SuperTensor 𝕜 A (SuperTensor 𝕜 B C)) n) :
    (assocₗ 𝕜 A B C).symm y ∈ superGrading 𝕜 (SuperTensor 𝕜 (SuperTensor 𝕜 A B) C) n :=
  mem_of_map_mem (assocₗ 𝕜 A B C).toLinearMap (assocₗ 𝕜 A B C).injective assocₗ_mem
    (by rwa [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])

variable (𝕜 A B C) in
/-- The associator `(A ⊗ˢ B) ⊗ˢ C ≃ A ⊗ˢ (B ⊗ˢ C)` as a `*`-algebra isomorphism. -/
def assoc : SuperTensor 𝕜 (SuperTensor 𝕜 A B) C ≃⋆ₐ[𝕜] SuperTensor 𝕜 A (SuperTensor 𝕜 B C) :=
  { AlgEquiv.ofLinearEquiv (assocₗ 𝕜 A B C) (assocₗ_tmul 1 1 1) assocₗ_mul with
    map_star' := assocₗ_star
    map_smul' := map_smul (assocₗ 𝕜 A B C) }

@[simp] theorem assoc_tmul (a : A) (b : B) (c : C) :
    assoc 𝕜 A B C ((a ⊗ˢ[𝕜] b) ⊗ˢ[𝕜] c) = a ⊗ˢ[𝕜] (b ⊗ˢ[𝕜] c) :=
  rfl

/-! #### The unitors -/

variable (𝕜 A) in
/-- The underlying linear equivalence of the left unitor, `r ⊗ a ↦ r • a`. -/
def lidₗ : SuperTensor 𝕜 𝕜 A ≃ₗ[𝕜] A := (of 𝕜 𝕜 A).symm ≪≫ₗ TensorProduct.lid 𝕜 A

@[simp] theorem lidₗ_tmul (r : 𝕜) (a : A) : lidₗ 𝕜 A (r ⊗ˢ[𝕜] a) = r • a :=
  TensorProduct.lid_tmul a r

private lemma lidₗ_mul (x y : SuperTensor 𝕜 𝕜 A) :
    lidₗ 𝕜 A (x * y) = lidₗ 𝕜 A x * lidₗ 𝕜 A y := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul r a _ ha =>
  induction y using induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | tmul s c _ _ =>
    rw [tmul_mul_tmul r c ha (mem_unitGrading_zero 𝕜 s), koszulSign_zero_right, one_smul,
      lidₗ_tmul, lidₗ_tmul, lidₗ_tmul, smul_mul_smul_comm]

private lemma lidₗ_star (x : SuperTensor 𝕜 𝕜 A) : lidₗ 𝕜 A (star x) = star (lidₗ 𝕜 A x) := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => rw [star_add', map_add, hx, hx', map_add, star_add]
  | tmul r a _ ha =>
    rw [star_tmul (mem_unitGrading_zero 𝕜 r) ha, koszulSign_zero_left, one_smul, lidₗ_tmul,
      lidₗ_tmul, star_smul]

theorem lidₗ_mem {n : ZMod 2} {x : SuperTensor 𝕜 𝕜 A}
    (hx : x ∈ superGrading 𝕜 (SuperTensor 𝕜 𝕜 A) n) : lidₗ 𝕜 A x ∈ superGrading 𝕜 A n := by
  refine tensorGrading_induction (P := fun x => lidₗ 𝕜 A x ∈ superGrading 𝕜 A n) hx
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy) fun {i j} r a hr ha hij => ?_
  rw [lidₗ_tmul]
  by_cases hi : i = 0
  · subst hi
    rw [zero_add] at hij
    subst hij
    exact Submodule.smul_mem _ r ha
  · rw [eq_zero_of_mem_unitGrading 𝕜 hr hi, zero_smul]
    exact zero_mem _

variable (𝕜 A) in
/-- The left unitor `𝕜 ⊗ˢ A ≃ A` as a `*`-algebra isomorphism. -/
def lid : SuperTensor 𝕜 𝕜 A ≃⋆ₐ[𝕜] A :=
  { AlgEquiv.ofLinearEquiv (lidₗ 𝕜 A) (by rw [one_def, lidₗ_tmul, one_smul]) lidₗ_mul with
    map_star' := lidₗ_star
    map_smul' := map_smul (lidₗ 𝕜 A) }

@[simp] theorem lid_tmul (r : 𝕜) (a : A) : lid 𝕜 A (r ⊗ˢ[𝕜] a) = r • a :=
  lidₗ_tmul r a

variable (𝕜 A) in
/-- The underlying linear equivalence of the right unitor, `a ⊗ r ↦ r • a`. -/
def ridₗ : SuperTensor 𝕜 A 𝕜 ≃ₗ[𝕜] A := (of 𝕜 A 𝕜).symm ≪≫ₗ TensorProduct.rid 𝕜 A

@[simp] theorem ridₗ_tmul (a : A) (r : 𝕜) : ridₗ 𝕜 A (a ⊗ˢ[𝕜] r) = r • a :=
  TensorProduct.rid_tmul a r

private lemma ridₗ_mul (x y : SuperTensor 𝕜 A 𝕜) :
    ridₗ 𝕜 A (x * y) = ridₗ 𝕜 A x * ridₗ 𝕜 A y := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul a r _ _ =>
  induction y using induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | tmul c s hc _ =>
    rw [tmul_mul_tmul a s (mem_unitGrading_zero 𝕜 r) hc, koszulSign_zero_left, one_smul,
      ridₗ_tmul, ridₗ_tmul, ridₗ_tmul, smul_mul_smul_comm]

private lemma ridₗ_star (x : SuperTensor 𝕜 A 𝕜) : ridₗ 𝕜 A (star x) = star (ridₗ 𝕜 A x) := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => rw [star_add', map_add, hx, hx', map_add, star_add]
  | tmul a r ha _ =>
    rw [star_tmul ha (mem_unitGrading_zero 𝕜 r), koszulSign_zero_right, one_smul, ridₗ_tmul,
      ridₗ_tmul, star_smul]

theorem ridₗ_mem {n : ZMod 2} {x : SuperTensor 𝕜 A 𝕜}
    (hx : x ∈ superGrading 𝕜 (SuperTensor 𝕜 A 𝕜) n) : ridₗ 𝕜 A x ∈ superGrading 𝕜 A n := by
  refine tensorGrading_induction (P := fun x => ridₗ 𝕜 A x ∈ superGrading 𝕜 A n) hx
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy) fun {i j} a r ha hr hij => ?_
  rw [ridₗ_tmul]
  by_cases hj : j = 0
  · subst hj
    rw [add_zero] at hij
    subst hij
    exact Submodule.smul_mem _ r ha
  · rw [eq_zero_of_mem_unitGrading 𝕜 hr hj, zero_smul]
    exact zero_mem _

variable (𝕜 A) in
/-- The right unitor `A ⊗ˢ 𝕜 ≃ A` as a `*`-algebra isomorphism. -/
def rid : SuperTensor 𝕜 A 𝕜 ≃⋆ₐ[𝕜] A :=
  { AlgEquiv.ofLinearEquiv (ridₗ 𝕜 A) (by rw [one_def, ridₗ_tmul, one_smul]) ridₗ_mul with
    map_star' := ridₗ_star
    map_smul' := map_smul (ridₗ 𝕜 A) }

@[simp] theorem rid_tmul (a : A) (r : 𝕜) : rid 𝕜 A (a ⊗ˢ[𝕜] r) = r • a :=
  ridₗ_tmul a r

/-! #### The Koszul braiding: `a ⊗ b ↦ koszulSign |a| |b| • (b ⊗ a)` -/

variable (𝕜 A B) in
/-- The underlying linear map of the Koszul braiding:
`∑ i j, koszulSign i j • (τ ∘ (π_i ⊗ π_j))` with `τ` the unsigned swap. -/
def commₗ : SuperTensor 𝕜 A B →ₗ[𝕜] SuperTensor 𝕜 B A :=
  ∑ i : ZMod 2, ∑ j : ZMod 2, koszulSign 𝕜 i j •
    ((of 𝕜 B A).toLinearMap ∘ₗ (TensorProduct.comm 𝕜 A B).toLinearMap ∘ₗ
      TensorProduct.map (parityProj 𝕜 i) (parityProj 𝕜 j) ∘ₗ (of 𝕜 A B).symm.toLinearMap)

theorem commₗ_tmul {i j : ZMod 2} {a : A} {b : B} (ha : a ∈ superGrading 𝕜 A i)
    (hb : b ∈ superGrading 𝕜 B j) :
    commₗ 𝕜 A B (a ⊗ˢ[𝕜] b) = koszulSign 𝕜 i j • (b ⊗ˢ[𝕜] a) := by
  simp only [commₗ, tmul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
    TensorProduct.map_tmul, TensorProduct.comm_tmul]
  rw [Finset.sum_eq_single i (fun i' _ h => by simp [parityProj_of_mem_ne ha (Ne.symm h)])
    (by simp), Finset.sum_eq_single j (fun j' _ h => by
      simp [parityProj_of_mem_ne hb (Ne.symm h)]) (by simp), parityProj_of_mem ha,
    parityProj_of_mem hb]

theorem commₗ_commₗ (x : SuperTensor 𝕜 A B) : commₗ 𝕜 B A (commₗ 𝕜 A B x) = x := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | @tmul i j a b ha hb =>
    rw [commₗ_tmul ha hb, map_smul, commₗ_tmul hb ha, smul_smul, koszulSign_comm 𝕜 j,
      koszulSign_mul_self, one_smul]

omit [StarRing 𝕜] in
/-- The sign bookkeeping behind the multiplicativity of the braiding. -/
private lemma comm_mul_sign (i j i' j' : ZMod 2) :
    koszulSign 𝕜 j i' * koszulSign 𝕜 (i + i') (j + j') =
      koszulSign 𝕜 i j * koszulSign 𝕜 i' j' * koszulSign 𝕜 i j' := by
  rcases zmod_two_cases i with rfl | rfl <;> rcases zmod_two_cases j with rfl | rfl <;>
    rcases zmod_two_cases i' with rfl | rfl <;> rcases zmod_two_cases j' with rfl | rfl <;>
    simp [koszulSign, zmod_two_one_add_one]

private lemma commₗ_mul (x y : SuperTensor 𝕜 A B) :
    commₗ 𝕜 A B (x * y) = commₗ 𝕜 A B x * commₗ 𝕜 A B y := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul a b ha hb =>
  induction y using induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | tmul c d hc hd =>
    rw [tmul_mul_tmul a d hb hc, map_smul,
      commₗ_tmul (grading_mul_mem ha hc) (grading_mul_mem hb hd), commₗ_tmul ha hb,
      commₗ_tmul hc hd, smul_mul_smul_comm, tmul_mul_tmul b c ha hd, smul_smul, smul_smul,
      comm_mul_sign]

private lemma commₗ_star (x : SuperTensor 𝕜 A B) :
    commₗ 𝕜 A B (star x) = star (commₗ 𝕜 A B x) := by
  induction x using induction_on with
  | zero => simp
  | add x x' hx hx' => rw [star_add', map_add, hx, hx', map_add, star_add']
  | @tmul i j a b ha hb =>
    rw [star_tmul ha hb, map_smul, commₗ_tmul (grading_star_mem ha) (grading_star_mem hb),
      commₗ_tmul ha hb, star_smul', star_koszulSign, star_tmul hb ha, koszulSign_comm 𝕜 j i]

theorem commₗ_mem {n : ZMod 2} {x : SuperTensor 𝕜 A B}
    (hx : x ∈ superGrading 𝕜 (SuperTensor 𝕜 A B) n) :
    commₗ 𝕜 A B x ∈ superGrading 𝕜 (SuperTensor 𝕜 B A) n := by
  refine tensorGrading_induction (P := fun x => commₗ 𝕜 A B x ∈ tensorGrading n) hx
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy) fun {i j} a b ha hb hij => ?_
  rw [commₗ_tmul ha hb, ← hij, add_comm]
  exact Submodule.smul_mem _ _ (tmul_mem_tensorGrading hb ha)

variable (𝕜 A B) in
/-- The Koszul braiding `A ⊗ˢ B ≃ B ⊗ˢ A`, `a ⊗ b ↦ koszulSign |a| |b| • (b ⊗ a)`, as a
`*`-algebra isomorphism. -/
def comm : SuperTensor 𝕜 A B ≃⋆ₐ[𝕜] SuperTensor 𝕜 B A :=
  { AlgEquiv.ofLinearEquiv
      (LinearEquiv.ofLinearMap (commₗ 𝕜 A B) (commₗ 𝕜 B A) (LinearMap.ext commₗ_commₗ)
        (LinearMap.ext commₗ_commₗ))
      (by
        show commₗ 𝕜 A B ((1 : A) ⊗ˢ[𝕜] (1 : B)) = 1
        rw [commₗ_tmul one_mem_grading_zero one_mem_grading_zero, koszulSign_zero_left,
          one_smul]
        rfl)
      commₗ_mul with
    map_star' := commₗ_star
    map_smul' := map_smul (commₗ 𝕜 A B) }

theorem comm_tmul {i j : ZMod 2} {a : A} {b : B} (ha : a ∈ superGrading 𝕜 A i)
    (hb : b ∈ superGrading 𝕜 B j) :
    comm 𝕜 A B (a ⊗ˢ[𝕜] b) = koszulSign 𝕜 i j • (b ⊗ˢ[𝕜] a) :=
  commₗ_tmul ha hb

theorem comm_symm_apply (x : SuperTensor 𝕜 B A) : (comm 𝕜 A B).symm x = comm 𝕜 B A x :=
  rfl

end Maps

end SuperTensor
