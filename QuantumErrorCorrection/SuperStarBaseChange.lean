import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import QuantumErrorCorrection.FlatCommStarRingCat
import QuantumErrorCorrection.SuperStarTensor

/-!
# Base change of super `*`-algebras

For an `R`-algebra `S` of commutative `*`-rings with `star` compatible with the scalar action
(`StarModule R S`), a super `*`-algebra `A` over `R` base changes to the super `*`-algebra
`S ⊗[R] A` over `S`:

* its ring, `S`-algebra and `*`-structure (`star (s ⊗ a) = star s ⊗ star a`) are Mathlib's;
* its grading is `(A_i).baseChange S`, with the decomposition and multiplicativity of
  `GradedAlgebra.baseChange`. Every super `*`-algebra is a `GradedAlgebra`, since `1` is even
  (`SuperStarAlgebra.one_mem_grading_zero`);
* `S` is purely even, so no Koszul sign enters.

Grading-preserving `*`-homomorphisms base change to grading-preserving `*`-homomorphisms
(`SuperStarAlgebra.baseChangeHom`), and when `S` is flat over `R` injective ones stay injective.

Base change is compatible with the rest of the structure:
* with the super tensor product (`stackBaseChange`) and the unit (`unitBaseChange`);
* with the identity (`lidBaseChange : R ⊗[R] A ≃ A`) and composites
  (`cancelBaseChangeStar : T ⊗[S] (S ⊗[R] A) ≃ T ⊗[R] A`).

All of these are grading-preserving `*`-algebra isomorphisms.
-/

noncomputable section

open TensorProduct DirectSum

universe u

/-- Ring homomorphisms map Koszul signs to Koszul signs. -/
theorem map_koszulSign {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (i j : ZMod 2) :
    f (koszulSign R i j) = koszulSign S i j := by
  unfold koszulSign
  split_ifs <;> simp

namespace SuperStarAlgebra

variable {R : Type u} [CommRing R] [StarRing R]
variable {A : Type u} [Ring A] [StarRing A] [Algebra R A] [StarModule R A] [SuperStarAlgebra R A]

/-- A super `*`-algebra is a `ZMod 2`-graded algebra in Mathlib's sense. -/
instance gradedAlgebra : GradedAlgebra (superGrading R A) :=
  { SuperVectorSpace.decomposition (𝕜 := R) (V := A) with
    one_mem := one_mem_grading_zero
    mul_mem := fun _ _ _ _ hx hy => grading_mul_mem hx hy }

variable {S : Type u} [CommRing S] [StarRing S] [Algebra R S] [StarModule R S]
variable {B : Type u} [Ring B] [StarRing B] [Algebra R B] [StarModule R B] [SuperStarAlgebra R B]

/-- Scalars from `S` are conjugated by `star` on the base change. -/
instance baseChangeStarModule : StarModule S (S ⊗[R] A) where
  star_smul s x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t a =>
      rw [smul_tmul', star_tmul, star_tmul, smul_tmul', smul_eq_mul, smul_eq_mul, star_mul']
    | add x y hx hy => rw [smul_add, star_add, star_add, hx, hy, smul_add]

omit [StarRing R] [StarRing A] [StarModule R A] [SuperStarAlgebra R A] [StarRing S]
  [StarModule R S] in
/-- Membership in a base-changed submodule, by induction over generators `1 ⊗ a`. -/
theorem baseChange_induction {p : Submodule R A} {P : S ⊗[R] A → Prop} {x : S ⊗[R] A}
    (hx : x ∈ p.baseChange S) (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (s : S) x, P x → P (s • x)) (tmul : ∀ a ∈ p, P (1 ⊗ₜ[R] a)) : P x := by
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact tmul a ha
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul s x _ hx => exact smul s x hx

/-- The base change `S ⊗[R] A` of a super `*`-algebra is a super `*`-algebra over `S`, graded by
`(A_i).baseChange S`. -/
instance baseChangeSuperStarAlgebra : SuperStarAlgebra S (S ⊗[R] A) where
  grading i := (superGrading R A i).baseChange S
  decomposition := DirectSum.Decomposition.baseChange (superGrading R A)
  grading_mul_mem hx hy := (GradedAlgebra.baseChange (S := S) (superGrading R A)).mul_mem hx hy
  grading_star_mem {i x} hx := by
    refine baseChange_induction (P := fun x => star x ∈ (superGrading R A i).baseChange S) hx
      (by rw [star_zero]; exact zero_mem _)
      (fun x y hx hy => by rw [star_add]; exact add_mem hx hy)
      (fun s x hx => by rw [star_smul]; exact Submodule.smul_mem _ _ hx) fun a ha => ?_
    rw [star_tmul, star_one]
    exact Submodule.tmul_mem_baseChange_of_mem _ (grading_star_mem ha)

theorem tmul_mem_baseChange_grading {i : ZMod 2} (s : S) {a : A} (ha : a ∈ superGrading R A i) :
    s ⊗ₜ[R] a ∈ superGrading S (S ⊗[R] A) i :=
  Submodule.tmul_mem_baseChange_of_mem s ha

variable (S) in
/-- Base change of a grading-preserving `*`-algebra homomorphism: `id_S ⊗ g`. -/
def baseChangeHom (g : A →⋆ₐ[R] B) : S ⊗[R] A →⋆ₐ[S] S ⊗[R] B :=
  { Algebra.TensorProduct.map (AlgHom.id S S) g.toAlgHom with
    map_star' := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s a =>
        simp only [AlgHom.toFun_eq_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          StarAlgHom.coe_toAlgHom, star_tmul, map_star]
      | add x y hx hy => simp only [AlgHom.toFun_eq_coe, star_add, map_add] at hx hy ⊢; rw [hx, hy] }

omit [SuperStarAlgebra R A] [SuperStarAlgebra R B] in
@[simp] theorem baseChangeHom_tmul (g : A →⋆ₐ[R] B) (s : S) (a : A) :
    baseChangeHom S g (s ⊗ₜ[R] a) = s ⊗ₜ[R] g a :=
  rfl

theorem baseChangeHom_mem (g : A →⋆ₐ[R] B)
    (hg : ∀ {i : ZMod 2} {x : A}, x ∈ superGrading R A i → g x ∈ superGrading R B i)
    {i : ZMod 2} {x : S ⊗[R] A} (hx : x ∈ superGrading S (S ⊗[R] A) i) :
    baseChangeHom S g x ∈ superGrading S (S ⊗[R] B) i := by
  refine baseChange_induction (P := fun x => baseChangeHom S g x ∈ superGrading S (S ⊗[R] B) i)
    hx (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    (fun s x hx => by rw [map_smul]; exact Submodule.smul_mem _ _ hx) fun a ha => ?_
  rw [baseChangeHom_tmul]
  exact tmul_mem_baseChange_grading 1 (hg ha)

omit [SuperStarAlgebra R A] in
theorem baseChangeHom_id : baseChangeHom S (StarAlgHom.id R A) = StarAlgHom.id S (S ⊗[R] A) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [SuperStarAlgebra R A] [SuperStarAlgebra R B] in
theorem baseChangeHom_comp {C : Type u} [Ring C] [StarRing C] [Algebra R C] [StarModule R C]
    [SuperStarAlgebra R C] (g : A →⋆ₐ[R] B) (h : B →⋆ₐ[R] C) :
    baseChangeHom S (h.comp g) = (baseChangeHom S h).comp (baseChangeHom S g) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [SuperStarAlgebra R A] [SuperStarAlgebra R B] in
/-- Over a flat extension, base change preserves injectivity. -/
theorem baseChangeHom_injective [Module.Flat R S] {g : A →⋆ₐ[R] B}
    (hg : Function.Injective g) : Function.Injective (baseChangeHom S g) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := S) g.toAlgHom.toLinearMap hg

/-- If two maps into `C` have super-commuting images, so do their base changes. -/
theorem baseChangeHom_superCommute {C : Type u} [Ring C] [StarRing C] [Algebra R C]
    [StarModule R C] [SuperStarAlgebra R C] (f : A →⋆ₐ[R] C) (f' : B →⋆ₐ[R] C)
    (hA : ∀ {i j : ZMod 2} {a : A} {c : B}, a ∈ superGrading R A i →
      c ∈ superGrading R B j → f a * f' c = koszulSign R i j • (f' c * f a))
    {i j : ZMod 2} {x : S ⊗[R] A} {y : S ⊗[R] B}
    (hx : x ∈ superGrading S (S ⊗[R] A) i) (hy : y ∈ superGrading S (S ⊗[R] B) j) :
    baseChangeHom S f x * baseChangeHom S f' y =
      koszulSign S i j • (baseChangeHom S f' y * baseChangeHom S f x) := by
  refine baseChange_induction (P := fun x => baseChangeHom S f x * baseChangeHom S f' y =
      koszulSign S i j • (baseChangeHom S f' y * baseChangeHom S f x)) hx
    (by simp) (fun x x' h h' => by rw [map_add, add_mul, mul_add, smul_add, h, h'])
    (fun s x h => by rw [map_smul, smul_mul_assoc, mul_smul_comm, h, smul_comm]) fun a ha => ?_
  refine baseChange_induction (P := fun y => baseChangeHom S f (1 ⊗ₜ[R] a) * baseChangeHom S f' y =
      koszulSign S i j • (baseChangeHom S f' y * baseChangeHom S f (1 ⊗ₜ[R] a))) hy
    (by simp) (fun y y' h h' => by rw [map_add, add_mul, mul_add, smul_add, h, h'])
    (fun s y h => by rw [map_smul, mul_smul_comm, smul_mul_assoc, h, smul_comm]) fun c hc => ?_
  rw [baseChangeHom_tmul, baseChangeHom_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, hA ha hc, tmul_smul, ← map_koszulSign (algebraMap R S),
    algebraMap_smul]

/-! #### Base change commutes with the super tensor product -/

omit [StarRing S] [StarModule R S] in
open SuperTensor in
/-- Induction over pure homogeneous tensors `s ⊗ (a ⊗ b)` in `S ⊗[R] (A ⊗ˢ B)`. -/
theorem baseChangeSuperTensor_induction {P : S ⊗[R] SuperTensor R A B → Prop}
    (x : S ⊗[R] SuperTensor R A B) (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (tmul : ∀ {i j : ZMod 2} (s : S) (a : A) (b : B), a ∈ superGrading R A i →
      b ∈ superGrading R B j → P (s ⊗ₜ[R] (a ⊗ˢ[R] b))) : P x := by
  induction x using TensorProduct.induction_on with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | tmul s z =>
    induction z using SuperTensor.induction_on with
    | zero => rw [TensorProduct.tmul_zero]; exact zero
    | add z z' hz hz' => rw [TensorProduct.tmul_add]; exact add _ _ hz hz'
    | tmul a b ha hb => exact tmul s a b ha hb

variable (R S A B) in
/-- The underlying linear equivalence of `S ⊗[R] (A ⊗ˢ B) ≃ (S ⊗[R] A) ⊗ˢ (S ⊗[R] B)`,
`s ⊗ (a ⊗ b) ↦ (s ⊗ a) ⊗ (1 ⊗ b)`. -/
def stackBaseChangeₗ :
    S ⊗[R] SuperTensor R A B ≃ₗ[S] SuperTensor S (S ⊗[R] A) (S ⊗[R] B) :=
  AlgebraTensorModule.congr (LinearEquiv.refl S S) (SuperTensor.of R A B).symm ≪≫ₗ
    AlgebraTensorModule.distribBaseChange R S A B ≪≫ₗ SuperTensor.of S (S ⊗[R] A) (S ⊗[R] B)

open SuperTensor in
@[simp] theorem stackBaseChangeₗ_tmul (s : S) (a : A) (b : B) :
    stackBaseChangeₗ R A S B (s ⊗ₜ[R] (a ⊗ˢ[R] b)) =
      (s ⊗ₜ[R] a) ⊗ˢ[S] ((1 : S) ⊗ₜ[R] b) :=
  rfl

open SuperTensor in
private lemma stackBaseChangeₗ_mul (x y : S ⊗[R] SuperTensor R A B) :
    stackBaseChangeₗ R A S B (x * y) =
      stackBaseChangeₗ R A S B x * stackBaseChangeₗ R A S B y := by
  induction x using baseChangeSuperTensor_induction with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul s a b ha hb =>
  induction y using baseChangeSuperTensor_induction with
  | zero => simp
  | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | tmul t c d hc hd =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, SuperTensor.tmul_mul_tmul a d hb hc,
      TensorProduct.tmul_smul, ← algebraMap_smul S, map_smul, stackBaseChangeₗ_tmul,
      stackBaseChangeₗ_tmul,
      stackBaseChangeₗ_tmul, SuperTensor.tmul_mul_tmul _ _ (tmul_mem_baseChange_grading 1 hb)
        (tmul_mem_baseChange_grading t hc),
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      map_koszulSign]

open SuperTensor in
private lemma stackBaseChangeₗ_star (x : S ⊗[R] SuperTensor R A B) :
    stackBaseChangeₗ R A S B (star x) = star (stackBaseChangeₗ R A S B x) := by
  induction x using baseChangeSuperTensor_induction with
  | zero => simp
  | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, SuperTensor.star_add']
  | tmul s a b ha hb =>
    rw [TensorProduct.star_tmul, SuperTensor.star_tmul ha hb, TensorProduct.tmul_smul,
      ← algebraMap_smul S, map_smul, stackBaseChangeₗ_tmul, stackBaseChangeₗ_tmul,
      SuperTensor.star_tmul (tmul_mem_baseChange_grading s ha) (tmul_mem_baseChange_grading 1 hb),
      TensorProduct.star_tmul, TensorProduct.star_tmul, star_one, map_koszulSign]

open SuperTensor in
theorem stackBaseChangeₗ_mem {k : ZMod 2} {x : S ⊗[R] SuperTensor R A B}
    (hx : x ∈ superGrading S (S ⊗[R] SuperTensor R A B) k) :
    stackBaseChangeₗ R A S B x ∈ superGrading S (SuperTensor S (S ⊗[R] A) (S ⊗[R] B)) k := by
  refine baseChange_induction (P := fun x =>
      stackBaseChangeₗ R A S B x ∈ superGrading S (SuperTensor S (S ⊗[R] A) (S ⊗[R] B)) k) hx
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    (fun s x hx => by rw [map_smul]; exact Submodule.smul_mem _ _ hx) fun z hz => ?_
  refine tensorGrading_induction (P := fun z => stackBaseChangeₗ R A S B ((1 : S) ⊗ₜ[R] z) ∈
      superGrading S (SuperTensor S (S ⊗[R] A) (S ⊗[R] B)) k) hz
    (by rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem _)
    (fun z z' h h' => by rw [TensorProduct.tmul_add, map_add]; exact add_mem h h')
    fun a b ha hb hab => ?_
  rw [stackBaseChangeₗ_tmul, ← hab]
  exact tmul_mem_tensorGrading (tmul_mem_baseChange_grading 1 ha)
    (tmul_mem_baseChange_grading 1 hb)

variable (R S A B) in
/-- Base change commutes with the super tensor product:
`S ⊗[R] (A ⊗ˢ B) ≃ (S ⊗[R] A) ⊗ˢ (S ⊗[R] B)` as `*`-algebras over `S`. -/
def stackBaseChange : S ⊗[R] SuperTensor R A B ≃⋆ₐ[S] SuperTensor S (S ⊗[R] A) (S ⊗[R] B) :=
  { AlgEquiv.ofLinearEquiv (stackBaseChangeₗ R A S B) rfl stackBaseChangeₗ_mul with
    map_star' := stackBaseChangeₗ_star
    map_smul' := map_smul (stackBaseChangeₗ R A S B) }

open SuperTensor in
@[simp] theorem stackBaseChange_tmul (s : S) (a : A) (b : B) :
    stackBaseChange R A S B (s ⊗ₜ[R] (a ⊗ˢ[R] b)) = (s ⊗ₜ[R] a) ⊗ˢ[S] ((1 : S) ⊗ₜ[R] b) :=
  rfl

theorem stackBaseChange_symm_mem {k : ZMod 2}
    {y : SuperTensor S (S ⊗[R] A) (S ⊗[R] B)}
    (hy : y ∈ superGrading S (SuperTensor S (S ⊗[R] A) (S ⊗[R] B)) k) :
    (stackBaseChange R A S B).symm y ∈ superGrading S (S ⊗[R] SuperTensor R A B) k :=
  SuperTensor.mem_of_map_mem (stackBaseChangeₗ R A S B).toLinearMap
    (stackBaseChangeₗ R A S B).injective stackBaseChangeₗ_mem
    (by rwa [LinearEquiv.coe_coe, show stackBaseChangeₗ R A S B ((stackBaseChange R A S B).symm y)
      = y from (stackBaseChange R A S B).apply_symm_apply y])

/-! #### Base change of the unit -/

variable (R S) in
/-- Base change of the trivially graded unit: `S ⊗[R] R ≃ S`. -/
def unitBaseChange : S ⊗[R] R ≃⋆ₐ[S] S :=
  { Algebra.TensorProduct.rid R S S with
    map_star' := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s r =>
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, star_tmul,
          Algebra.TensorProduct.rid_tmul, star_smul]
      | add x y hx hy =>
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe] at hx hy ⊢
        rw [star_add, map_add, hx, hy, map_add, star_add]
    map_smul' := map_smul (Algebra.TensorProduct.rid R S S) }

theorem unitBaseChange_mem {i : ZMod 2} {x : S ⊗[R] R}
    (hx : x ∈ superGrading S (S ⊗[R] R) i) : unitBaseChange R S x ∈ superGrading S S i := by
  rcases zmod_two_cases i with rfl | rfl
  · exact SuperTensor.mem_unitGrading_zero S _
  · have hx' : x ∈ (SuperTensor.unitGrading R 1).baseChange S := hx
    rw [show SuperTensor.unitGrading R 1 = ⊥ by simp [SuperTensor.unitGrading],
      Submodule.baseChange_bot,
      Submodule.mem_bot] at hx'
    rw [hx', map_zero]
    exact zero_mem _

/-! #### Base change along the identity and along a composite -/

omit [StarRing S] [StarModule R S] [SuperStarAlgebra R A] [SuperStarAlgebra R B] in
theorem baseChangeHom_lid_naturality (g : A →⋆ₐ[R] B) (x : R ⊗[R] A) :
    Algebra.TensorProduct.lid R B (baseChangeHom R g x) = g (Algebra.TensorProduct.lid R A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [baseChangeHom_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (R A) in
/-- Base change along the identity: `R ⊗[R] A ≃ A`. -/
def lidBaseChange : R ⊗[R] A ≃⋆ₐ[R] A :=
  { Algebra.TensorProduct.lid R A with
    map_star' := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r a =>
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, star_tmul,
          Algebra.TensorProduct.lid_tmul, star_smul]
      | add x y hx hy =>
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe] at hx hy ⊢
        rw [star_add, map_add, hx, hy, map_add, star_add]
    map_smul' := map_smul (Algebra.TensorProduct.lid R A) }

omit [SuperStarAlgebra R A] in
@[simp] theorem lidBaseChange_tmul (r : R) (a : A) : lidBaseChange R A (r ⊗ₜ[R] a) = r • a :=
  rfl

theorem lidBaseChange_mem {i : ZMod 2} {x : R ⊗[R] A}
    (hx : x ∈ superGrading R (R ⊗[R] A) i) : lidBaseChange R A x ∈ superGrading R A i := by
  refine baseChange_induction (P := fun x => lidBaseChange R A x ∈ superGrading R A i) hx
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    (fun r x hx => by rw [map_smul]; exact Submodule.smul_mem _ _ hx) fun a ha => ?_
  rw [lidBaseChange_tmul, one_smul]
  exact ha

theorem lidBaseChange_symm_mem {i : ZMod 2} {a : A} (ha : a ∈ superGrading R A i) :
    (lidBaseChange R A).symm a ∈ superGrading R (R ⊗[R] A) i := by
  rw [show (lidBaseChange R A).symm a = (1 : R) ⊗ₜ[R] a from
    (lidBaseChange R A).symm_apply_eq.2 (by rw [lidBaseChange_tmul, one_smul])]
  exact tmul_mem_baseChange_grading 1 ha

section Cancel

variable {T : Type u} [CommRing T] [StarRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [StarModule S T] [StarModule R T]

omit [StarRing R] [StarRing A] [StarModule R A] [SuperStarAlgebra R A] [StarRing S]
  [StarModule R S] [StarRing T] [StarModule S T] [StarModule R T] [Algebra R T]
  [IsScalarTower R S T] in
/-- Induction over pure tensors `t ⊗ (s ⊗ a)` in `T ⊗[S] (S ⊗[R] A)`. -/
theorem baseChangeBaseChange_induction {P : T ⊗[S] (S ⊗[R] A) → Prop}
    (x : T ⊗[S] (S ⊗[R] A)) (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (tmul : ∀ (t : T) (s : S) (a : A), P (t ⊗ₜ[S] (s ⊗ₜ[R] a))) : P x := by
  induction x using TensorProduct.induction_on with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | tmul t z =>
    induction z using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero]; exact zero
    | add z z' hz hz' => rw [TensorProduct.tmul_add]; exact add _ _ hz hz'
    | tmul s a => exact tmul t s a

omit [StarRing R] [StarRing A] [StarModule R A] [SuperStarAlgebra R A] [StarRing S]
  [StarModule R S] [StarRing T] [StarModule S T] [StarModule R T] in
variable (R S T A) in
/-- The underlying linear equivalence of `T ⊗[S] (S ⊗[R] A) ≃ T ⊗[R] A`,
`t ⊗ (s ⊗ a) ↦ (s • t) ⊗ a`. -/
def cancelBaseChangeₗ : T ⊗[S] (S ⊗[R] A) ≃ₗ[T] T ⊗[R] A :=
  AlgebraTensorModule.cancelBaseChange R S T T A

omit [StarRing R] [StarRing A] [StarModule R A] [SuperStarAlgebra R A] [StarRing S]
  [StarModule R S] [StarRing T] [StarModule S T] [StarModule R T] in
@[simp] theorem cancelBaseChangeₗ_tmul (t : T) (s : S) (a : A) :
    cancelBaseChangeₗ R A S T (t ⊗ₜ[S] (s ⊗ₜ[R] a)) = (s • t) ⊗ₜ[R] a :=
  rfl

omit [StarRing R] [StarRing A] [StarModule R A] [SuperStarAlgebra R A] [StarRing S]
  [StarModule R S] [StarRing T] [StarModule S T] [StarModule R T] in
private lemma cancelBaseChangeₗ_mul (x y : T ⊗[S] (S ⊗[R] A)) :
    cancelBaseChangeₗ R A S T (x * y) =
      cancelBaseChangeₗ R A S T x * cancelBaseChangeₗ R A S T y := by
  induction x using baseChangeBaseChange_induction with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul t s a =>
  induction y using baseChangeBaseChange_induction with
  | zero => simp
  | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | tmul t' s' a' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      cancelBaseChangeₗ_tmul, cancelBaseChangeₗ_tmul, cancelBaseChangeₗ_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, smul_mul_smul_comm]

omit [SuperStarAlgebra R A] in
private lemma cancelBaseChangeₗ_star (x : T ⊗[S] (S ⊗[R] A)) :
    cancelBaseChangeₗ R A S T (star x) = star (cancelBaseChangeₗ R A S T x) := by
  induction x using baseChangeBaseChange_induction with
  | zero => simp
  | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add]
  | tmul t s a =>
    rw [TensorProduct.star_tmul, TensorProduct.star_tmul, cancelBaseChangeₗ_tmul,
      cancelBaseChangeₗ_tmul, TensorProduct.star_tmul, star_smul]

theorem cancelBaseChangeₗ_mem {i : ZMod 2} {x : T ⊗[S] (S ⊗[R] A)}
    (hx : x ∈ superGrading T (T ⊗[S] (S ⊗[R] A)) i) :
    cancelBaseChangeₗ R A S T x ∈ superGrading T (T ⊗[R] A) i := by
  refine baseChange_induction (P := fun x =>
      cancelBaseChangeₗ R A S T x ∈ superGrading T (T ⊗[R] A) i) hx
    (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
    (fun t x hx => by rw [map_smul]; exact Submodule.smul_mem _ _ hx) fun y hy => ?_
  refine baseChange_induction (P := fun y =>
      cancelBaseChangeₗ R A S T ((1 : T) ⊗ₜ[S] y) ∈ superGrading T (T ⊗[R] A) i) hy
    (by rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem _)
    (fun y y' h h' => by rw [TensorProduct.tmul_add, map_add]; exact add_mem h h')
    (fun s y h => by
      rw [TensorProduct.tmul_smul, ← algebraMap_smul T, map_smul]
      exact Submodule.smul_mem _ _ h) fun a ha => ?_
  rw [cancelBaseChangeₗ_tmul]
  exact tmul_mem_baseChange_grading _ ha

variable (R S T A) in
/-- Base change along a composite: `T ⊗[S] (S ⊗[R] A) ≃ T ⊗[R] A`. -/
def cancelBaseChangeStar : T ⊗[S] (S ⊗[R] A) ≃⋆ₐ[T] T ⊗[R] A :=
  { AlgEquiv.ofLinearEquiv (cancelBaseChangeₗ R A S T)
      (by rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def,
        cancelBaseChangeₗ_tmul, one_smul]; rfl) cancelBaseChangeₗ_mul with
    map_star' := cancelBaseChangeₗ_star
    map_smul' := map_smul (cancelBaseChangeₗ R A S T) }

omit [SuperStarAlgebra R A] in
@[simp] theorem cancelBaseChangeStar_tmul (t : T) (s : S) (a : A) :
    cancelBaseChangeStar R A S T (t ⊗ₜ[S] (s ⊗ₜ[R] a)) = (s • t) ⊗ₜ[R] a :=
  rfl

theorem cancelBaseChangeStar_symm_mem {i : ZMod 2} {y : T ⊗[R] A}
    (hy : y ∈ superGrading T (T ⊗[R] A) i) :
    (cancelBaseChangeStar R A S T).symm y ∈ superGrading T (T ⊗[S] (S ⊗[R] A)) i :=
  SuperTensor.mem_of_map_mem (cancelBaseChangeₗ R A S T).toLinearMap
    (cancelBaseChangeₗ R A S T).injective cancelBaseChangeₗ_mem
    (by rwa [LinearEquiv.coe_coe, show cancelBaseChangeₗ R A S T
      ((cancelBaseChangeStar R A S T).symm y) = y from
        (cancelBaseChangeStar R A S T).apply_symm_apply y])

end Cancel

theorem unitBaseChange_symm_mem {i : ZMod 2} {y : S} (hy : y ∈ superGrading S S i) :
    (unitBaseChange R S).symm y ∈ superGrading S (S ⊗[R] R) i := by
  rcases zmod_two_cases i with rfl | rfl
  · change _ ∈ (SuperTensor.unitGrading R 0).baseChange S
    rw [show SuperTensor.unitGrading R 0 = ⊤ by simp [SuperTensor.unitGrading],
      Submodule.baseChange_top]
    exact Submodule.mem_top
  · rw [SuperTensor.eq_zero_of_mem_unitGrading S hy (by decide), map_zero]
    exact zero_mem _

end SuperStarAlgebra

/-! ### Base change along a morphism of `FlatCommStarRingCat` -/

open CategoryTheory SuperStarAlgebra

namespace FlatCommStarRingCat.Hom

variable {R S : FlatCommStarRingCat.{u}} (σ : R ⟶ S)

/-- The `R`-algebra structure on `S` given by `σ`. -/
abbrev toAlgebra : Algebra R S := σ.hom.toAlgebra

/-- `star` on `S` is compatible with the `R`-action given by `σ`. -/
theorem starModule : letI := σ.toAlgebra; StarModule R S := by
  let _ := σ.toAlgebra
  exact ⟨fun r s => by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', RingHom.algebraMap_toAlgebra,
      σ.map_star]⟩

/-- `S` is flat over `R` via `σ`. -/
theorem moduleFlat : letI := σ.toAlgebra; Module.Flat R S := σ.flat

end FlatCommStarRingCat.Hom

namespace SuperStarAlgCat

variable {R S : FlatCommStarRingCat.{u}} (σ : R ⟶ S)

/-- Base change of super `*`-algebras along `σ`: `A ↦ S ⊗[R] A`. -/
def baseChange : SuperStarAlgCat R ⥤ SuperStarAlgCat S :=
  letI := σ.toAlgebra
  haveI := σ.starModule
  { obj A := SuperStarAlgCat.of (S ⊗[R] A)
    map f := ⟨baseChangeHom S f.1, baseChangeHom_mem f.1 f.2⟩
    map_id _ := Subtype.ext baseChangeHom_id
    map_comp f g := Subtype.ext (baseChangeHom_comp f.1 g.1) }

theorem baseChange_map_tmul {A B : SuperStarAlgCat R} (f : A ⟶ B) (s : S) (a : A) :
    letI := σ.toAlgebra
    ((baseChange σ).map f).1 (s ⊗ₜ[R] a) = s ⊗ₜ[R] f.1 a :=
  rfl

theorem baseChange_map_injective {A B : SuperStarAlgCat R} {f : A ⟶ B}
    (hf : Function.Injective f.1) : Function.Injective ((baseChange σ).map f).1 := by
  let _ := σ.toAlgebra
  have := σ.starModule
  have := σ.moduleFlat
  exact baseChangeHom_injective hf

end SuperStarAlgCat

namespace QuasiLocalAlgebra

variable {X : Type u} [DecidableEq X] {R S : FlatCommStarRingCat.{u}} (σ : R ⟶ S)

/-- Base change of a quasi-local algebra along a flat star ring map `σ`: the local algebra on `T`
is `S ⊗[R] A(T)`. Isotony survives because `S` is flat over `R`. Microcausality is checked on
generators `1 ⊗ a`, using that `σ` maps Koszul signs to Koszul signs. -/
def baseChange (A : QuasiLocalAlgebra X R) : QuasiLocalAlgebra X S where
  net := A.net ⋙ SuperStarAlgCat.baseChange σ
  isotony h := SuperStarAlgCat.baseChange_map_injective σ (A.isotony h)
  superCommuting {T₁ T₂} hT {i j} {x} {y} hx hy := by
    let _ := σ.toAlgebra
    have := σ.starModule
    exact baseChangeHom_superCommute (A.net.map (RegionCat.homOfSubset Finset.subset_union_left)).1
      (A.net.map (RegionCat.homOfSubset Finset.subset_union_right)).1
      (fun ha hc => A.superCommuting hT ha hc) hx hy

theorem baseChange_flat (A : QuasiLocalAlgebra X R) (hA : ∀ T, Module.Flat R (A.net.obj T))
    (T : RegionCat X) : Module.Flat S ((A.baseChange σ).net.obj T) := by
  let _ := σ.toAlgebra
  have := hA T
  exact Module.Flat.baseChange R S (A.net.obj T)

end QuasiLocalAlgebra
