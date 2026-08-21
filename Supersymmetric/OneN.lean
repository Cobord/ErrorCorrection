import Supersymmetric.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Lie superalgebras of dimension `1 | N`

Over a commutative ring in which `2` is invertible, a bracket on `𝕜 ⊕ ΠM` is constructed
from an endomorphism `A` of `M` and a symmetric bilinear form `B`.  The two hypotheses below are
exactly the `Q,Q,H` and `Q,Q,Q` Jacobi constraints.
-/

open LinearMap

universe u v

namespace LieSuperAlgebra.OneN

variable (𝕜 : Type u) (M : Type v) [CommRing 𝕜] [Invertible (2 : 𝕜)]
  [AddCommGroup M] [Module 𝕜 M]

/-- The underlying supermodule `𝕜 ⊕ ΠM`. -/
abbrev Space := 𝕜 × M

/-- The grading with `𝕜` even and `M` odd. -/
def grading (i : ZMod 2) : Submodule 𝕜 (Space 𝕜 M) :=
  if i = 0 then LinearMap.ker (LinearMap.snd 𝕜 𝕜 M)
  else LinearMap.ker (LinearMap.fst 𝕜 𝕜 M)

private theorem parity_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] private theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

omit [Invertible (2 : 𝕜)] in
private theorem grading_isInternal : DirectSum.IsInternal (grading 𝕜 M) := by
  apply (DirectSum.isInternal_submodule_iff_isCompl (grading 𝕜 M) (i := 0) (j := 1)
    (by decide) (by
      ext i
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl)).2
  constructor
  · rw [disjoint_iff]
    ext x
    simp [grading, Prod.ext_iff, and_comm]
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    have he : (x.1, 0) ∈ grading 𝕜 M 0 := by simp [grading]
    have ho : (0, x.2) ∈ grading 𝕜 M 1 := by simp [grading]
    simpa using Submodule.add_mem_sup he ho

noncomputable instance : SuperVectorSpace 𝕜 (Space 𝕜 M) where
  grading := grading 𝕜 M
  decomposition := (grading_isInternal 𝕜 M).chooseDecomposition

set_option linter.unnecessarySeqFocus false in
/-- The bracket associated to `A` and `B`:
`[(a,x),(b,y)] = (B(x,y), a • A(y) - b • A(x))`. -/
def bracket (B : LinearMap.BilinForm 𝕜 M) (A : Module.End 𝕜 M) :
    Space 𝕜 M →ₗ[𝕜] Space 𝕜 M →ₗ[𝕜] Space 𝕜 M :=
  LinearMap.mk₂ 𝕜
    (fun x y ↦ (B x.2 y.2, x.1 • A y.2 - y.1 • A x.2))
    (fun _ _ _ ↦ by ext <;> simp [add_smul] <;> module)
    (fun _ _ _ ↦ by ext <;> simp [smul_sub] <;> module)
    (fun _ _ _ ↦ by ext <;> simp [add_smul] <;> module)
    (fun _ _ _ ↦ by ext <;> simp [smul_sub] <;> module)

omit [Invertible (2 : 𝕜)] in
@[simp] theorem bracket_apply (B : LinearMap.BilinForm 𝕜 M) (A : Module.End 𝕜 M)
    (x y : Space 𝕜 M) :
    bracket 𝕜 M B A x y = (B x.2 y.2, x.1 • A y.2 - y.1 • A x.2) := rfl

/-- `A` is skew-adjoint with respect to `B`.  This is the `Q,Q,H` Jacobi constraint. -/
def IsSkewAdjoint (B : LinearMap.BilinForm 𝕜 M) (A : Module.End 𝕜 M) : Prop :=
  ∀ x y, B (A x) y + B x (A y) = 0

/-- The Jacobi constraint on three odd vectors. -/
def OddJacobi (B : LinearMap.BilinForm 𝕜 M) (A : Module.End 𝕜 M) : Prop :=
  ∀ x y z, B y z • A x + B z x • A y + B x y • A z = 0

/-- The Lie superalgebra structure on `𝕜 ⊕ ΠM` determined by compatible `B` and `A`. -/
@[instance_reducible]
noncomputable def lieSuperAlgebra (B : LinearMap.BilinForm 𝕜 M) (A : Module.End 𝕜 M)
    (hB : B.IsSymm) (hA : IsSkewAdjoint 𝕜 M B A) (hxyz : OddJacobi 𝕜 M B A) :
    LieSuperAlgebra 𝕜 (Space 𝕜 M) where
  bracket := bracket 𝕜 M B A
  bracket_mem := by
    intro i j x y hx hy
    change x ∈ grading 𝕜 M i at hx
    change y ∈ grading 𝕜 M j at hy
    change bracket 𝕜 M B A x y ∈ grading 𝕜 M (i + j)
    obtain rfl | rfl := parity_cases i
    all_goals obtain rfl | rfl := parity_cases j
    all_goals
      norm_num [grading, bracket] at hx hy ⊢
      try simp_all
  graded_skew := by
    intro i j x y hx hy
    change x ∈ grading 𝕜 M i at hx
    change y ∈ grading 𝕜 M j at hy
    obtain rfl | rfl := parity_cases i
    all_goals obtain rfl | rfl := parity_cases j
    all_goals
      norm_num [grading, bracket, koszulSign, hB.eq] at hx hy ⊢
      try simp_all
  graded_jacobi := by
    intro i j k x y z hx hy hz
    change x ∈ grading 𝕜 M i at hx
    change y ∈ grading 𝕜 M j at hy
    change z ∈ grading 𝕜 M k at hz
    have hxy : B x.2 (A y.2) + B y.2 (A x.2) = 0 := by
      rw [hB.eq y.2 (A x.2), add_comm]
      exact hA x.2 y.2
    have hyz : B y.2 (A z.2) + B z.2 (A y.2) = 0 := by
      rw [hB.eq z.2 (A y.2), add_comm]
      exact hA y.2 z.2
    have hzx : B z.2 (A x.2) + B x.2 (A z.2) = 0 := by
      rw [hB.eq x.2 (A z.2), add_comm]
      exact hA z.2 x.2
    have hodd : B x.2 y.2 • A z.2 +
        (B y.2 z.2 • A x.2 + B z.2 x.2 • A y.2) = 0 := by
      simpa [add_assoc, add_comm, add_left_comm] using hxyz x.2 y.2 z.2
    obtain rfl | rfl := parity_cases i
    all_goals obtain rfl | rfl := parity_cases j
    all_goals obtain rfl | rfl := parity_cases k
    all_goals
      norm_num [grading, bracket, koszulSign] at hx hy hz ⊢
      try simp_all
    · module
    · module
    · rw [← neg_add, ← mul_add, hyz, mul_zero, neg_zero]
    · module
    · rw [← neg_add, ← mul_add, add_comm, hzx, mul_zero, neg_zero]
    · rw [← neg_add, ← mul_add, hxy, mul_zero, neg_zero]
    · rw [add_comm
        (B y.2 z.2 • A x.2 + B z.2 x.2 • A y.2)
        (B x.2 y.2 • A z.2)]
      exact hodd

section Converse

/-!
### Every Lie superalgebra structure on `Space 𝕜 M` comes from an `(B, A)` pair

`lieSuperAlgebra` builds a `LieSuperAlgebra` instance on `Space 𝕜 M` out of `B`, `A` and the three
Jacobi-type hypotheses.  This section proves the converse: given *any* `LieSuperAlgebra` instance
on `Space 𝕜 M` (for the specific grading fixed above), reading off `[H,Q_s]` and `[Q_s,Q_t]`
recovers an `A` and a `B` satisfying exactly those same hypotheses.  So the `(B, A)`-parametrized
family already exhausts every Lie superalgebra structure on this superspace; there is nothing more
general to write down. -/

variable [lsa : LieSuperAlgebra 𝕜 (Space 𝕜 M)]

/-- The distinguished even generator `H = (1,0)`. -/
def evenGen : Space 𝕜 M := (1, 0)

/-- The odd generators `Q_s = (0,s)`, as a linear inclusion `M ↪ Space 𝕜 M`. -/
def oddIncl : M →ₗ[𝕜] Space 𝕜 M := LinearMap.inr 𝕜 𝕜 M

omit [Invertible (2 : 𝕜)] [LieSuperAlgebra 𝕜 (Space 𝕜 M)] in
@[simp] theorem oddIncl_apply (s : M) : oddIncl 𝕜 M s = (0, s) := rfl

omit [Invertible (2 : 𝕜)] [LieSuperAlgebra 𝕜 (Space 𝕜 M)] in
theorem evenGen_mem_grading_zero : evenGen 𝕜 M ∈ grading 𝕜 M 0 := by
  simp [grading, evenGen]

omit [Invertible (2 : 𝕜)] [LieSuperAlgebra 𝕜 (Space 𝕜 M)] in
theorem oddIncl_mem_grading_one (s : M) : oddIncl 𝕜 M s ∈ grading 𝕜 M 1 := by
  simp [grading]

omit [Invertible (2 : 𝕜)] in
/-- `[Q_s,Q_t]` is purely even: its `M`-component vanishes. -/
theorem bracket_oddIncl_oddIncl_snd (s t : M) :
    (lsa.bracket (oddIncl 𝕜 M s) (oddIncl 𝕜 M t)).2 = 0 := by
  have h := lsa.bracket_mem (oddIncl_mem_grading_one 𝕜 M s) (oddIncl_mem_grading_one 𝕜 M t)
  change lsa.bracket (oddIncl 𝕜 M s) (oddIncl 𝕜 M t) ∈ grading 𝕜 M (1 + 1) at h
  simpa [grading, show (1 + 1 : ZMod 2) = 0 from by decide] using h

omit [Invertible (2 : 𝕜)] in
/-- `[H,Q_s]` is purely odd: its `𝕜`-component vanishes. -/
theorem bracket_evenGen_oddIncl_fst (s : M) :
    (lsa.bracket (evenGen 𝕜 M) (oddIncl 𝕜 M s)).1 = 0 := by
  have h := lsa.bracket_mem (evenGen_mem_grading_zero 𝕜 M) (oddIncl_mem_grading_one 𝕜 M s)
  change lsa.bracket (evenGen 𝕜 M) (oddIncl 𝕜 M s) ∈ grading 𝕜 M (0 + 1) at h
  simpa [grading, show (0 + 1 : ZMod 2) = 1 from by decide] using h

/-- The odd--odd pairing recovered from `[Q_s,Q_t]`. -/
noncomputable def ofLieSuperAlgebra_B : LinearMap.BilinForm 𝕜 M :=
  (lsa.bracket.compr₂ (LinearMap.fst 𝕜 𝕜 M)).compl₁₂ (oddIncl 𝕜 M) (oddIncl 𝕜 M)

omit [Invertible (2 : 𝕜)] in
@[simp] theorem ofLieSuperAlgebra_B_apply (s t : M) :
    ofLieSuperAlgebra_B 𝕜 M s t = (lsa.bracket (oddIncl 𝕜 M s) (oddIncl 𝕜 M t)).1 := rfl

/-- The action of the even generator recovered from `[H,Q_s]`. -/
noncomputable def ofLieSuperAlgebra_A : Module.End 𝕜 M :=
  (LinearMap.snd 𝕜 𝕜 M).comp ((lsa.bracket (evenGen 𝕜 M)).comp (oddIncl 𝕜 M))

omit [Invertible (2 : 𝕜)] in
@[simp] theorem ofLieSuperAlgebra_A_apply (s : M) :
    ofLieSuperAlgebra_A 𝕜 M s = (lsa.bracket (evenGen 𝕜 M) (oddIncl 𝕜 M s)).2 := rfl

omit [Invertible (2 : 𝕜)] in
theorem bracket_oddIncl_oddIncl (s t : M) :
    lsa.bracket (oddIncl 𝕜 M s) (oddIncl 𝕜 M t) = (ofLieSuperAlgebra_B 𝕜 M s t, 0) := by
  ext
  · rfl
  · exact bracket_oddIncl_oddIncl_snd 𝕜 M s t

omit [Invertible (2 : 𝕜)] in
theorem bracket_evenGen_oddIncl (s : M) :
    lsa.bracket (evenGen 𝕜 M) (oddIncl 𝕜 M s) = (0, ofLieSuperAlgebra_A 𝕜 M s) := by
  ext
  · exact bracket_evenGen_oddIncl_fst 𝕜 M s
  · rfl

omit [Invertible (2 : 𝕜)] [LieSuperAlgebra 𝕜 (Space 𝕜 M)] in
/-- A constant even element is a scalar multiple of `H`. -/
theorem const_smul_evenGen (c : 𝕜) : (c, (0 : M)) = c • evenGen 𝕜 M := by
  ext <;> simp [evenGen]

theorem bracket_evenGen_evenGen : lsa.bracket (evenGen 𝕜 M) (evenGen 𝕜 M) = 0 := by
  have h := lsa.graded_skew (evenGen_mem_grading_zero 𝕜 M) (evenGen_mem_grading_zero 𝕜 M)
  rw [koszulSign_zero_left, neg_one_smul, eq_neg_iff_add_eq_zero] at h
  have h2 : (2 : 𝕜) • lsa.bracket (evenGen 𝕜 M) (evenGen 𝕜 M) = 0 := by rw [two_smul]; exact h
  have h3 : lsa.bracket (evenGen 𝕜 M) (evenGen 𝕜 M) =
      ⅟(2 : 𝕜) • ((2 : 𝕜) • lsa.bracket (evenGen 𝕜 M) (evenGen 𝕜 M)) := by
    rw [← mul_smul, invOf_mul_self, one_smul]
  rw [h3, h2, smul_zero]

omit [Invertible (2 : 𝕜)] in
theorem bracket_oddIncl_evenGen (s : M) :
    lsa.bracket (oddIncl 𝕜 M s) (evenGen 𝕜 M) = (0, -(ofLieSuperAlgebra_A 𝕜 M s)) := by
  have h := lsa.graded_skew (oddIncl_mem_grading_one 𝕜 M s) (evenGen_mem_grading_zero 𝕜 M)
  rw [koszulSign_zero_right, neg_one_smul, bracket_evenGen_oddIncl] at h
  simpa using h

omit [Invertible (2 : 𝕜)] in
/-- Symmetry of `B` is exactly graded skew-symmetry of `[Q_s,Q_t]`, since
`koszulSign 1 1 = -1` cancels the sign. -/
theorem ofLieSuperAlgebra_B_isSymm : (ofLieSuperAlgebra_B 𝕜 M).IsSymm := by
  refine ⟨fun s t => ?_⟩
  have h := lsa.graded_skew (oddIncl_mem_grading_one 𝕜 M s) (oddIncl_mem_grading_one 𝕜 M t)
  rw [koszulSign_one_one, neg_neg, one_smul] at h
  simpa using congrArg Prod.fst h

theorem bracket_evenGen_bracket_oddIncl_oddIncl (s t : M) :
    lsa.bracket (evenGen 𝕜 M) (lsa.bracket (oddIncl 𝕜 M s) (oddIncl 𝕜 M t)) = 0 := by
  rw [bracket_oddIncl_oddIncl, const_smul_evenGen, map_smul, bracket_evenGen_evenGen, smul_zero]

omit [Invertible (2 : 𝕜)] in
theorem bracket_oddIncl_bracket_oddIncl_evenGen (s t : M) :
    lsa.bracket (oddIncl 𝕜 M s) (lsa.bracket (oddIncl 𝕜 M t) (evenGen 𝕜 M)) =
      (-(ofLieSuperAlgebra_B 𝕜 M s (ofLieSuperAlgebra_A 𝕜 M t)), 0) := by
  rw [bracket_oddIncl_evenGen]
  show lsa.bracket (oddIncl 𝕜 M s) (oddIncl 𝕜 M (-(ofLieSuperAlgebra_A 𝕜 M t))) = _
  rw [bracket_oddIncl_oddIncl, map_neg]

omit [Invertible (2 : 𝕜)] in
theorem bracket_oddIncl_bracket_evenGen_oddIncl (t s : M) :
    lsa.bracket (oddIncl 𝕜 M t) (lsa.bracket (evenGen 𝕜 M) (oddIncl 𝕜 M s)) =
      (ofLieSuperAlgebra_B 𝕜 M t (ofLieSuperAlgebra_A 𝕜 M s), 0) := by
  rw [bracket_evenGen_oddIncl, ← oddIncl_apply, bracket_oddIncl_oddIncl]

/-- The `Q,Q,H` Jacobi constraint, i.e. skew-adjointness of `A`, is exactly the graded Jacobi
identity on `(H, Q_s, Q_t)`. -/
theorem ofLieSuperAlgebra_A_isSkewAdjoint :
    IsSkewAdjoint 𝕜 M (ofLieSuperAlgebra_B 𝕜 M) (ofLieSuperAlgebra_A 𝕜 M) := by
  intro s t
  have h := lsa.graded_jacobi (evenGen_mem_grading_zero 𝕜 M) (oddIncl_mem_grading_one 𝕜 M s)
    (oddIncl_mem_grading_one 𝕜 M t)
  rw [koszulSign_zero_left, koszulSign_zero_right, koszulSign_one_one, one_smul, one_smul,
    neg_one_smul, bracket_evenGen_bracket_oddIncl_oddIncl,
    bracket_oddIncl_bracket_oddIncl_evenGen, bracket_oddIncl_bracket_evenGen_oddIncl] at h
  have h1 := congrArg Prod.fst h
  simp only [Prod.fst_add, Prod.fst_neg, Prod.fst_zero, zero_add] at h1
  have hsymm := (ofLieSuperAlgebra_B_isSymm 𝕜 M).eq t (ofLieSuperAlgebra_A 𝕜 M s)
  rw [hsymm] at h1
  linear_combination -h1

omit [Invertible (2 : 𝕜)] in
theorem bracket_oddIncl_bracket_oddIncl_oddIncl (s t u : M) :
    lsa.bracket (oddIncl 𝕜 M s) (lsa.bracket (oddIncl 𝕜 M t) (oddIncl 𝕜 M u)) =
      (0, -(ofLieSuperAlgebra_B 𝕜 M t u • ofLieSuperAlgebra_A 𝕜 M s)) := by
  rw [bracket_oddIncl_oddIncl, const_smul_evenGen, map_smul, bracket_oddIncl_evenGen]
  simp

omit [Invertible (2 : 𝕜)] in
/-- The `Q,Q,Q` Jacobi constraint, `OddJacobi`, is exactly the graded Jacobi identity on
`(Q_s, Q_t, Q_u)`, using `koszulSign 1 1 = -1` on all three terms. -/
theorem ofLieSuperAlgebra_oddJacobi :
    OddJacobi 𝕜 M (ofLieSuperAlgebra_B 𝕜 M) (ofLieSuperAlgebra_A 𝕜 M) := by
  intro s t u
  have h := lsa.graded_jacobi (oddIncl_mem_grading_one 𝕜 M s) (oddIncl_mem_grading_one 𝕜 M t)
    (oddIncl_mem_grading_one 𝕜 M u)
  rw [koszulSign_one_one,
    bracket_oddIncl_bracket_oddIncl_oddIncl, bracket_oddIncl_bracket_oddIncl_oddIncl,
    bracket_oddIncl_bracket_oddIncl_oddIncl] at h
  have h1 := congrArg Prod.snd h
  simp only [Prod.snd_add, Prod.snd_zero, Prod.snd_neg, neg_one_smul, neg_neg] at h1
  exact h1

omit [Invertible (2 : 𝕜)] [LieSuperAlgebra 𝕜 (Space 𝕜 M)] in
/-- Every element of `Space 𝕜 M` decomposes as an even multiple of `H` plus an odd part. -/
theorem space_eq_smul_evenGen_add_oddIncl (x : Space 𝕜 M) :
    x = x.1 • evenGen 𝕜 M + oddIncl 𝕜 M x.2 := by
  ext <;> simp [evenGen]

/-- The round trip `lsa ↦ (B,A) ↦ bracket B A` reproduces `lsa`'s own bracket: expanding both
arguments in the `H`, `Q_s` basis and using the four atomic bracket identities recovers exactly
`bracket`'s defining formula. -/
theorem lsa_bracket_eq (x y : Space 𝕜 M) :
    lsa.bracket x y = (ofLieSuperAlgebra_B 𝕜 M x.2 y.2,
      x.1 • ofLieSuperAlgebra_A 𝕜 M y.2 - y.1 • ofLieSuperAlgebra_A 𝕜 M x.2) := by
  conv_lhs => rw [space_eq_smul_evenGen_add_oddIncl 𝕜 M x, space_eq_smul_evenGen_add_oddIncl 𝕜 M y]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    bracket_evenGen_evenGen, smul_zero, bracket_evenGen_oddIncl, bracket_oddIncl_evenGen,
    bracket_oddIncl_oddIncl]
  ext <;> simp [sub_eq_add_neg]
  abel

theorem ofLieSuperAlgebra_bracket_eq :
    bracket 𝕜 M (ofLieSuperAlgebra_B 𝕜 M) (ofLieSuperAlgebra_A 𝕜 M) = lsa.bracket := by
  apply LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [bracket_apply, lsa_bracket_eq]

/-- The converse construction is a genuine two-sided inverse to `lieSuperAlgebra`: the `(B,A)`
data read off from `lsa` builds back the very same `LieSuperAlgebra` instance, not merely one
satisfying the same hypotheses. This is the precise sense in which the `(B,A)`-parametrized family
is the *most general* Lie superalgebra structure on `Space 𝕜 M`. -/
theorem lieSuperAlgebra_ofLieSuperAlgebra :
    lieSuperAlgebra 𝕜 M (ofLieSuperAlgebra_B 𝕜 M) (ofLieSuperAlgebra_A 𝕜 M)
      (ofLieSuperAlgebra_B_isSymm 𝕜 M) (ofLieSuperAlgebra_A_isSkewAdjoint 𝕜 M)
      (ofLieSuperAlgebra_oddJacobi 𝕜 M) = lsa := by
  have key : ∀ L1 L2 : LieSuperAlgebra 𝕜 (Space 𝕜 M), L1.bracket = L2.bracket → L1 = L2 := by
    intro L1 L2 h
    cases L1; cases L2; congr 1
  exact key _ lsa (ofLieSuperAlgebra_bracket_eq 𝕜 M)

omit [Invertible (2 : 𝕜)] [LieSuperAlgebra 𝕜 (Space 𝕜 M)] in
/-- The other half of the round trip: reading `B` back off the `LieSuperAlgebra` instance built
from `(B,A)` returns `B` itself. -/
theorem ofLieSuperAlgebra_B_lieSuperAlgebra_eq
    (B : LinearMap.BilinForm 𝕜 M) (A : Module.End 𝕜 M) (hB : B.IsSymm)
    (hA : IsSkewAdjoint 𝕜 M B A) (hxyz : OddJacobi 𝕜 M B A) :
    letI := lieSuperAlgebra 𝕜 M B A hB hA hxyz
    ofLieSuperAlgebra_B 𝕜 M = B := by
  let := lieSuperAlgebra 𝕜 M B A hB hA hxyz
  apply LinearMap.ext fun s => LinearMap.ext fun t => ?_
  rfl

omit [Invertible (2 : 𝕜)] [LieSuperAlgebra 𝕜 (Space 𝕜 M)] in
/-- The other half of the round trip: reading `A` back off the `LieSuperAlgebra` instance built
from `(B,A)` returns `A` itself. -/
theorem ofLieSuperAlgebra_A_lieSuperAlgebra_eq
    (B : LinearMap.BilinForm 𝕜 M) (A : Module.End 𝕜 M) (hB : B.IsSymm)
    (hA : IsSkewAdjoint 𝕜 M B A) (hxyz : OddJacobi 𝕜 M B A) :
    letI := lieSuperAlgebra 𝕜 M B A hB hA hxyz
    ofLieSuperAlgebra_A 𝕜 M = A := by
  let := lieSuperAlgebra 𝕜 M B A hB hA hxyz
  apply LinearMap.ext fun s => ?_
  show (bracket 𝕜 M B A (evenGen 𝕜 M) (oddIncl 𝕜 M s)).2 = A s
  rw [bracket_apply]
  simp [evenGen]

end Converse

end LieSuperAlgebra.OneN
