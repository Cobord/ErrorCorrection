import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Instances.Int
import QuantumErrorCorrection.QCAClass
import QuantumErrorCorrection.SquareZeroQuasiLocalAlgebra

/-!
# The shift on `ℤ` is not a circuit

On the square-zero system over `X = ℤ` with coefficients in a field `𝕜`
(`SquareZero.obj ℤ 𝕜`), the translation by one site is a QCA that is not a finite-depth circuit,
so QCAs modulo circuits form a nontrivial set: `Nontrivial (QCAClass (SquareZero.obj ℤ 𝕜))`.

The invariant is a *flow across a cut*, the linear analogue of the GNVW index. A QCA of the
square-zero system is a banded linear automorphism `T` of `ℤ →₀ 𝕜`
(`SquareZero.linEquiv`). Let `L n` be the functions supported on `(-∞, n]` (`ShiftIndex.half`).
Banding means `L (n - k) ≤ T (L n) ≤ L (n + k)`, so `T (L 0)` and `L 0` differ by finitely many
dimensions near the cut, and the index is their relative dimension
`[T (L 0) : L 0] = dim (T (L 0) / L (-k)) - dim (L 0 / L (-k))` (`ShiftIndex.indexAt`).

* It does not depend on `k` (`indexAt_eq`) and is additive under composition (`indexAt_trans`),
  so it is a homomorphism `QCA → Multiplicative ℤ` (`qcaIndexHom`).
* A layer preserves the functions supported on the union `P` of the blocks meeting `(-∞, 0]`,
  which is sandwiched between `L 0` and `L r`, so its index is `[L 0 : P] + [P : L 0] = 0`
  (`qcaIndex_eq_zero_of_isLayer`). Hence circuits have index `0`.
* The shift maps `L 0` onto `L 1`, so its index is `1` (`qcaIndex_shift`).

Relative dimensions are cardinals `codim D A = rank (A / D)` for `D ≤ A`, which are additive in
towers without finiteness hypotheses (`codim_add`) and invariant under linear automorphisms
(`codim_map`). They are converted to natural numbers only once they are known to be finite.
-/

noncomputable section

open CategoryTheory NNReal Cardinal SquareZero

namespace ShiftIndex

/-! ### Relative dimension -/

section Codim

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The dimension of `A / D`, computed as the image of `A` in `V ⧸ D`; meaningful for `D ≤ A`. -/
def codim (D A : Submodule 𝕜 V) : Cardinal := Module.rank 𝕜 (A.map D.mkQ)

theorem codim_mono {D A A' : Submodule 𝕜 V} (h : A ≤ A') : codim D A ≤ codim D A' :=
  Submodule.rank_mono (Submodule.map_mono h)

theorem codim_eq_zero_of_le {D A : Submodule 𝕜 V} (h : A ≤ D) : codim D A = 0 := by
  have : A.map D.mkQ = ⊥ := le_bot_iff.1 (Submodule.map_le_iff_le_comap.2 (by
    rwa [Submodule.comap_bot, Submodule.ker_mkQ]))
  rw [codim, this, rank_bot]

theorem ker_factor {D' D : Submodule 𝕜 V} (h : D' ≤ D) :
    LinearMap.ker (Submodule.factor h) = D.map D'.mkQ := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    change Submodule.factor h (D'.mkQ v) = 0 ↔ D'.mkQ v ∈ D.map D'.mkQ
    rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · exact fun hv => ⟨v, hv, rfl⟩
    · rintro ⟨d, hd, hdv⟩
      have hdv' : d - v ∈ D := h ((Submodule.Quotient.eq D').1 hdv)
      simpa using D.sub_mem hd hdv'

/-- Relative dimensions add in towers `D' ≤ D ≤ A`. -/
theorem codim_add {D' D A : Submodule 𝕜 V} (hD : D' ≤ D) (hA : D ≤ A) :
    codim D' A = codim D A + codim D' D := by
  have key := LinearMap.rank_range_add_rank_ker
    (Submodule.factor hD ∘ₗ (A.map D'.mkQ).subtype)
  have hrange : LinearMap.range (Submodule.factor hD ∘ₗ (A.map D'.mkQ).subtype) =
      A.map D.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, ← Submodule.map_comp,
      Submodule.factor_comp_mk]
  have hker : LinearMap.ker (Submodule.factor hD ∘ₗ (A.map D'.mkQ).subtype) =
      (D.map D'.mkQ).comap (A.map D'.mkQ).subtype := by
    rw [LinearMap.ker_comp, ker_factor]
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe (Submodule.map_mono hA)).rank_eq] at key
  exact key.symm

/-- Relative dimensions are invariant under linear automorphisms. -/
theorem codim_map (e : V ≃ₗ[𝕜] V) (D A : Submodule 𝕜 V) :
    codim (D.map e.toLinearMap) (A.map e.toLinearMap) = codim D A := by
  let q : (V ⧸ D) ≃ₗ[𝕜] V ⧸ D.map e.toLinearMap := Submodule.Quotient.equiv D _ e rfl
  have hq : (q : (V ⧸ D) →ₗ[𝕜] _) ∘ₗ D.mkQ = (D.map e.toLinearMap).mkQ ∘ₗ e.toLinearMap :=
    LinearMap.ext fun _ => rfl
  have hmap : (A.map e.toLinearMap).map (D.map e.toLinearMap).mkQ =
      (A.map D.mkQ).map (q : (V ⧸ D) →ₗ[𝕜] _) :=
    calc (A.map e.toLinearMap).map (D.map e.toLinearMap).mkQ
        = A.map ((D.map e.toLinearMap).mkQ ∘ₗ e.toLinearMap) := (Submodule.map_comp _ _ _).symm
      _ = A.map ((q : (V ⧸ D) →ₗ[𝕜] _) ∘ₗ D.mkQ) := by rw [hq]
      _ = (A.map D.mkQ).map (q : (V ⧸ D) →ₗ[𝕜] _) := Submodule.map_comp _ _ _
  rw [codim, codim, hmap]
  exact LinearEquiv.rank_map_eq q _

/-- The relative dimension as a natural number (`0` if infinite). -/
def fc (D A : Submodule 𝕜 V) : ℕ := (codim D A).toNat

theorem fc_add {D' D A : Submodule 𝕜 V} (hD : D' ≤ D) (hA : D ≤ A) (hfin : codim D' A < ℵ₀) :
    fc D' A = fc D A + fc D' D := by
  rw [codim_add hD hA] at hfin
  obtain ⟨h1, h2⟩ := Cardinal.add_lt_aleph0_iff.1 hfin
  rw [fc, codim_add hD hA, Cardinal.toNat_add h1 h2]
  rfl

theorem fc_map (e : V ≃ₗ[𝕜] V) (D A : Submodule 𝕜 V) :
    fc (D.map e.toLinearMap) (A.map e.toLinearMap) = fc D A := by
  rw [fc, fc, codim_map]

end Codim

/-! ### Half-lines -/

section Half

variable (𝕜 : Type*) [Field 𝕜]

/-- The functions supported on `(-∞, n]`. -/
def half (n : ℤ) : Submodule 𝕜 (ℤ →₀ 𝕜) := Finsupp.supported 𝕜 𝕜 (Set.Iic n)

variable {𝕜}

theorem mem_half {n : ℤ} {v : ℤ →₀ 𝕜} : v ∈ half 𝕜 n ↔ ∀ x, n < x → v x = 0 := by
  rw [half, Finsupp.mem_supported']
  simp [not_le]

theorem half_mono {m n : ℤ} (h : m ≤ n) : half 𝕜 m ≤ half 𝕜 n :=
  Finsupp.supported_mono (Set.Iic_subset_Iic.2 h)

theorem codim_half_succ (n : ℤ) : codim (half 𝕜 n) (half 𝕜 (n + 1)) = 1 := by
  have hne : (half 𝕜 n).mkQ (Finsupp.single (n + 1) 1) ≠ 0 := by
    rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero, mem_half]
    intro h
    simpa using h (n + 1) (lt_add_one n)
  have hspan : (half 𝕜 (n + 1)).map (half 𝕜 n).mkQ =
      𝕜 ∙ (half 𝕜 n).mkQ (Finsupp.single (n + 1) 1) := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨v (n + 1), ?_⟩
      rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, mem_half]
      intro x hx
      rcases (show x = n + 1 ∨ n + 1 < x by omega) with rfl | hx'
      · simp
      · simp [(show n + 1 ≠ x by omega), mem_half.1 hv x hx']
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_map_of_mem (Finsupp.single_mem_supported 𝕜 _ (Set.mem_Iic.2 le_rfl))
  rw [codim, hspan, ← Module.finrank_eq_rank, finrank_span_singleton hne, Nat.cast_one]

theorem codim_half {m n : ℤ} (h : m ≤ n) :
    codim (half 𝕜 m) (half 𝕜 n) = ((n - m).toNat : Cardinal) := by
  induction n, h using Int.leInduction with
  | base => rw [codim_eq_zero_of_le le_rfl, sub_self, Int.toNat_zero, Nat.cast_zero]
  | succ n hmn ih =>
    rw [codim_add (half_mono hmn) (half_mono (by omega)), codim_half_succ, ih,
      show (n + 1 - m).toNat = (n - m).toNat + 1 by omega, Nat.cast_add, Nat.cast_one, add_comm]

theorem fc_half {m n : ℤ} (h : m ≤ n) : fc (half 𝕜 m) (half 𝕜 n) = (n - m).toNat := by
  rw [fc, codim_half h, Cardinal.toNat_natCast]

theorem codim_half_lt (m n : ℤ) : codim (half 𝕜 m) (half 𝕜 n) < ℵ₀ := by
  rcases le_total m n with h | h
  · rw [codim_half h]; exact Cardinal.natCast_lt_aleph0
  · rw [codim_eq_zero_of_le (half_mono h)]; exact Cardinal.aleph0_pos

/-- A subspace sandwiched between two half-lines has finite relative dimension over anything
in between. -/
theorem codim_lt_aleph0 {m n : ℤ} {D A : Submodule 𝕜 (ℤ →₀ 𝕜)} (hmD : half 𝕜 m ≤ D)
    (hDA : D ≤ A) (hA : A ≤ half 𝕜 n) : codim D A < ℵ₀ := by
  have h := codim_add hmD (hDA.trans hA)
  exact (codim_mono hA).trans_lt
    ((self_le_add_right _ _).trans_lt (h ▸ codim_half_lt m n))

end Half

/-! ### Banded automorphisms and their index -/

section Index

variable {𝕜 : Type*} [Field 𝕜]

/-- `T` and its inverse move half-lines by at most `k`. -/
def IsBanded (T : (ℤ →₀ 𝕜) ≃ₗ[𝕜] (ℤ →₀ 𝕜)) (k : ℕ) : Prop :=
  ∀ n : ℤ, (half 𝕜 n).map T.toLinearMap ≤ half 𝕜 (n + k) ∧
    (half 𝕜 n).map T.symm.toLinearMap ≤ half 𝕜 (n + k)

variable {S T : (ℤ →₀ 𝕜) ≃ₗ[𝕜] (ℤ →₀ 𝕜)} {k k' a b : ℕ}

theorem IsBanded.map_le (hT : IsBanded T k) (n : ℤ) :
    (half 𝕜 n).map T.toLinearMap ≤ half 𝕜 (n + k) :=
  (hT n).1

theorem IsBanded.half_le_map (hT : IsBanded T k) (n : ℤ) :
    half 𝕜 (n - k) ≤ (half 𝕜 n).map T.toLinearMap := fun v hv => by
  have h := (hT (n - k)).2 (Submodule.mem_map_of_mem hv)
  rw [sub_add_cancel] at h
  exact ⟨T.symm v, h, T.apply_symm_apply v⟩

theorem IsBanded.mono (hT : IsBanded T k) (h : k ≤ k') : IsBanded T k' := fun n =>
  ⟨(hT n).1.trans (half_mono (by omega)), (hT n).2.trans (half_mono (by omega))⟩

/-- First `T`, then `S`. -/
theorem IsBanded.trans (hT : IsBanded T b) (hS : IsBanded S a) :
    IsBanded (T.trans S) (a + b) := fun n => by
  refine ⟨?_, ?_⟩ <;> rintro _ ⟨v, hv, rfl⟩
  · have h1 := (hT n).1 (Submodule.mem_map_of_mem hv)
    have h2 := (hS (n + b)).1 (Submodule.mem_map_of_mem h1)
    exact half_mono (m := n + b + a) (by push_cast; omega) h2
  · have h1 := (hS n).2 (Submodule.mem_map_of_mem hv)
    have h2 := (hT (n + a)).2 (Submodule.mem_map_of_mem h1)
    exact half_mono (m := n + a + b) (by push_cast; omega) h2

/-- The flow of `T` across the cut between `0` and `1`, measured against the floor `L (-k)`. -/
def indexAt (T : (ℤ →₀ 𝕜) ≃ₗ[𝕜] (ℤ →₀ 𝕜)) (k : ℕ) : ℤ :=
  (fc (half 𝕜 (-(k : ℤ))) ((half 𝕜 0).map T.toLinearMap) : ℤ) - k

theorem IsBanded.codim_lt (hT : IsBanded T k) :
    codim (half 𝕜 (-(k : ℤ))) ((half 𝕜 0).map T.toLinearMap) < ℵ₀ :=
  codim_lt_aleph0 le_rfl (by simpa using hT.half_le_map 0) (by simpa using hT.map_le 0)

theorem indexAt_mono (hT : IsBanded T k) (h : k ≤ k') : indexAt T k' = indexAt T k := by
  unfold indexAt
  rw [fc_add (half_mono (show -(k' : ℤ) ≤ -k by omega)) (by simpa using hT.half_le_map 0)
    (hT.mono h).codim_lt, fc_half (by omega)]
  push_cast
  omega

/-- The index does not depend on the band width used to compute it. -/
theorem indexAt_eq (hT : IsBanded T k) (hT' : IsBanded T k') : indexAt T k = indexAt T k' := by
  rw [← indexAt_mono hT (le_max_left k k'), ← indexAt_mono hT' (le_max_right k k')]

theorem map_trans (P : Submodule 𝕜 (ℤ →₀ 𝕜)) :
    P.map (T.trans S).toLinearMap = (P.map T.toLinearMap).map S.toLinearMap := by
  rw [LinearEquiv.coe_trans, Submodule.map_comp]

/-- The index is additive under composition. -/
theorem indexAt_trans (hT : IsBanded T b) (hS : IsBanded S a) :
    indexAt (T.trans S) (a + b) = indexAt S a + indexAt T b := by
  have hDE : half 𝕜 (-((a + b : ℕ) : ℤ)) ≤ (half 𝕜 (-(b : ℤ))).map S.toLinearMap := by
    have := hS.half_le_map (-(b : ℤ))
    rwa [show -(b : ℤ) - a = -((a + b : ℕ) : ℤ) by push_cast; ring] at this
  have hbT : half 𝕜 (-(b : ℤ)) ≤ (half 𝕜 0).map T.toLinearMap := by
    simpa using hT.half_le_map 0
  have hET := Submodule.map_mono (f := S.toLinearMap) hbT
  have hEL := Submodule.map_mono (f := S.toLinearMap) (half_mono (𝕜 := 𝕜) (show -(b : ℤ) ≤ 0 by omega))
  have hDa : half 𝕜 (-((a + b : ℕ) : ℤ)) ≤ half 𝕜 (-(a : ℤ)) := half_mono (by push_cast; omega)
  have haS : half 𝕜 (-(a : ℤ)) ≤ (half 𝕜 0).map S.toLinearMap := by
    simpa using hS.half_le_map 0
  have hfin1 := (hT.trans hS).codim_lt
  rw [map_trans] at hfin1
  have hfin2 : codim (half 𝕜 (-((a + b : ℕ) : ℤ))) ((half 𝕜 0).map S.toLinearMap) < ℵ₀ :=
    codim_lt_aleph0 le_rfl (hDa.trans haS) (hS.map_le 0)
  have e1 := fc_add hDE hET hfin1
  have e2 := fc_add hDE hEL hfin2
  have e3 := fc_add hDa haS hfin2
  rw [fc_map] at e1 e2
  rw [fc_half (by omega)] at e2
  rw [fc_half (by push_cast; omega)] at e3
  unfold indexAt
  rw [map_trans, e1]
  push_cast at e1 e2 e3 ⊢
  omega

/-- An automorphism preserving a subspace sandwiched between two half-lines has index `0`. -/
theorem indexAt_eq_zero_of_invariant (hT : IsBanded T k) {P : Submodule 𝕜 (ℤ →₀ 𝕜)} {r : ℤ}
    (hP : P.map T.toLinearMap = P) (h0 : half 𝕜 0 ≤ P) (hr : P ≤ half 𝕜 r) :
    indexAt T k = 0 := by
  have hDT : half 𝕜 (-(k : ℤ)) ≤ (half 𝕜 0).map T.toLinearMap := by
    simpa using hT.half_le_map 0
  have hTP : (half 𝕜 0).map T.toLinearMap ≤ P := hP ▸ Submodule.map_mono h0
  have hDL : half 𝕜 (-(k : ℤ)) ≤ half 𝕜 0 := half_mono (by omega)
  have hfin : codim (half 𝕜 (-(k : ℤ))) P < ℵ₀ := codim_lt_aleph0 le_rfl (hDL.trans h0) hr
  have e1 := fc_add hDT hTP hfin
  have e2 := fc_add hDL h0 hfin
  have e3 : fc ((half 𝕜 0).map T.toLinearMap) P = fc (half 𝕜 0) P := by
    conv_lhs => rw [← hP]
    exact fc_map T _ _
  rw [fc_half (by omega)] at e2
  unfold indexAt
  omega

end Index

/-! ### The index of a QCA of the square-zero system on `ℤ` -/

section QCA

variable {𝕜 : Type} [Field 𝕜] [StarRing 𝕜]

/-- Functions supported on `(-∞, n]` go to functions supported on `(-∞, n + ⌈l⌉]` under a
homomorphism of spread `l`. -/
theorem linPart_mem_half {l : ℝ≥0} (α : BoundedSpreadHom l (qla ℤ 𝕜) (qla ℤ 𝕜)) {n : ℤ}
    {v : ℤ →₀ 𝕜} (hv : v ∈ half 𝕜 n) : linPart α v ∈ half 𝕜 (n + ⌈(l : ℝ)⌉₊) := by
  have hv' : v ∈ Finsupp.supported 𝕜 𝕜 ((RegionCat.of v.support).carrier : Set ℤ) :=
    (Finsupp.mem_supported 𝕜 v).2 subset_rfl
  refine Finsupp.supported_mono ?_ (linPart_mem_supported α _ hv')
  intro y hy
  obtain ⟨s, hs, hys⟩ := RegionCat.mem_metricNbhd.1 hy
  have hsn : s ≤ n := by
    by_contra h
    exact (Finsupp.mem_support_iff.1 hs) (mem_half.1 hv s (not_le.1 h))
  rw [Int.dist_eq] at hys
  have h1 : ((y - s : ℤ) : ℝ) ≤ (⌈(l : ℝ)⌉₊ : ℝ) := by
    push_cast
    linarith [le_abs_self ((y : ℝ) - s), Nat.le_ceil (l : ℝ)]
  have h2 : y - s ≤ (⌈(l : ℝ)⌉₊ : ℤ) := by exact_mod_cast h1
  simp only [Set.mem_Iic]
  omega

theorem isBanded_linEquiv (u : QCA (obj ℤ 𝕜)) : ∃ k, IsBanded (linEquiv u) k := by
  obtain ⟨l, ⟨α, hα⟩, ⟨β, hβ⟩⟩ := u.exists_hasSpread
  refine ⟨⌈(l : ℝ)⌉₊, fun n => ⟨?_, ?_⟩⟩ <;> rintro _ ⟨v, hv, rfl⟩
  · change linHom u.hom v ∈ _
    rw [← hα, linHom_homMk]
    exact linPart_mem_half α hv
  · change linHom u.inv v ∈ _
    rw [← hβ, linHom_homMk]
    exact linPart_mem_half β hv

/-- The index of a QCA: the flow of its linear part across a cut. -/
def qcaIndex (u : QCA (obj ℤ 𝕜)) : ℤ :=
  indexAt (linEquiv u) (isBanded_linEquiv u).choose

theorem qcaIndex_eq {u : QCA (obj ℤ 𝕜)} {k : ℕ} (hk : IsBanded (linEquiv u) k) :
    qcaIndex u = indexAt (linEquiv u) k :=
  indexAt_eq (isBanded_linEquiv u).choose_spec hk

theorem qcaIndex_mul (u v : QCA (obj ℤ 𝕜)) : qcaIndex (u * v) = qcaIndex u + qcaIndex v := by
  obtain ⟨a, ha⟩ := isBanded_linEquiv u
  obtain ⟨b, hb⟩ := isBanded_linEquiv v
  have h := hb.trans ha
  rw [← linEquiv_mul] at h
  rw [qcaIndex_eq h, qcaIndex_eq ha, qcaIndex_eq hb, linEquiv_mul, indexAt_trans hb ha]

/-- The index as a homomorphism to `Multiplicative ℤ`. -/
def qcaIndexHom : QCA (obj ℤ 𝕜) →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (qcaIndex u)
  map_one' := by
    have h := qcaIndex_mul (1 : QCA (obj ℤ 𝕜)) 1
    rw [mul_one] at h
    simp only [ofAdd_eq_one]
    omega
  map_mul' u v := by rw [qcaIndex_mul, ofAdd_add]

/-- A layer has index `0`: it preserves the functions supported on the blocks meeting
`(-∞, 0]`, a subspace sandwiched between `L 0` and `L ⌈r⌉`. -/
theorem qcaIndex_eq_zero_of_isLayer {u : QCA (obj ℤ 𝕜)} {r : ℝ≥0} (hu : u.IsLayer r) :
    qcaIndex u = 0 := by
  classical
  obtain ⟨blocks, hd, α, β, hα, hβ, hB⟩ := hu
  set k : ℕ := ⌈(r : ℝ)⌉₊
  have hdist : ∀ x y, blocks x y → x - y ≤ k ∧ y - x ≤ k := fun x y h => by
    have h' := hd x y h
    rw [Int.dist_eq, abs_le] at h'
    have h1 : ((x - y : ℤ) : ℝ) ≤ (k : ℝ) := by
      push_cast; linarith [Nat.le_ceil (r : ℝ)]
    have h2 : ((y - x : ℤ) : ℝ) ≤ (k : ℝ) := by
      push_cast; linarith [Nat.le_ceil (r : ℝ)]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  let U : Set ℤ := {x | ∃ y ≤ 0, blocks x y}
  let P : Submodule 𝕜 (ℤ →₀ 𝕜) := Finsupp.supported 𝕜 𝕜 U
  -- the block closure of a finite set is a finite union of blocks
  have hclosure : ∀ v ∈ P, ∀ γ : BoundedSpreadHom r (qla ℤ 𝕜) (qla ℤ 𝕜),
      (∀ B : RegionCat ℤ, (∀ x ∈ B.carrier, ∀ y, blocks x y → y ∈ B.carrier) →
        γ.PreservesRegion B) → linPart γ v ∈ P := by
    intro v hv γ hγ
    let B : RegionCat ℤ := RegionCat.of
      ((v.support.biUnion fun y => Finset.Icc (y - k) (y + k)).filter
        fun x => ∃ y ∈ v.support, blocks x y)
    have hmemB : ∀ x, x ∈ B.carrier ↔ ∃ y ∈ v.support, blocks x y := fun x => by
      simp only [B, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc,
        and_iff_right_iff_imp]
      rintro ⟨y, hy, hxy⟩
      have := hdist x y hxy
      exact ⟨y, hy, by omega, by omega⟩
    have hBclosed : ∀ x ∈ B.carrier, ∀ z, blocks x z → z ∈ B.carrier := fun x hx z hxz => by
      obtain ⟨y, hy, hxy⟩ := (hmemB x).1 hx
      exact (hmemB z).2 ⟨y, hy, blocks.iseqv.trans (blocks.iseqv.symm hxz) hxy⟩
    have hvB : v ∈ Finsupp.supported 𝕜 𝕜 (B.carrier : Set ℤ) :=
      (Finsupp.mem_supported 𝕜 v).2 fun x hx => (hmemB x).2 ⟨x, hx, blocks.iseqv.refl x⟩
    refine Finsupp.supported_mono ?_
      (linPart_mem_supported_of_preservesRegion γ (hγ B hBclosed) hvB)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (hmemB x).1 hx
    obtain ⟨y', hy', hyy'⟩ := (Finsupp.mem_supported 𝕜 v).1 hv hy
    exact ⟨y', hy', blocks.iseqv.trans hxy hyy'⟩
  have hTP : P.map (linEquiv u).toLinearMap ≤ P := by
    rintro _ ⟨v, hv, rfl⟩
    change linHom u.hom v ∈ P
    rw [← hα, linHom_homMk]
    exact hclosure v hv α fun B hBc => (hB B hBc).1
  have hTP' : P.map (linEquiv u).symm.toLinearMap ≤ P := by
    rintro _ ⟨v, hv, rfl⟩
    change linHom u.inv v ∈ P
    rw [← hβ, linHom_homMk]
    exact hclosure v hv β fun B hBc => (hB B hBc).2
  have hP : P.map (linEquiv u).toLinearMap = P := le_antisymm hTP fun v hv =>
    ⟨(linEquiv u).symm v, hTP' (Submodule.mem_map_of_mem hv), (linEquiv u).apply_symm_apply v⟩
  have h0 : half 𝕜 0 ≤ P :=
    Finsupp.supported_mono fun x hx => ⟨x, hx, blocks.iseqv.refl x⟩
  have hr : P ≤ half 𝕜 k := Finsupp.supported_mono fun x ⟨y, hy, hxy⟩ => by
    have := hdist x y hxy
    simp only [Set.mem_Iic] at hy ⊢
    omega
  obtain ⟨k₀, hk₀⟩ := isBanded_linEquiv u
  rw [qcaIndex_eq hk₀]
  exact indexAt_eq_zero_of_invariant hk₀ hP h0 hr

/-- Circuits have index `0`. -/
theorem circuitSubgroup_le_ker : QCA.circuitSubgroup (obj ℤ 𝕜) ≤ (qcaIndexHom (𝕜 := 𝕜)).ker :=
  (Subgroup.closure_le _).2 fun _ ⟨_, hu⟩ => by
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    change Multiplicative.ofAdd _ = 1
    rw [qcaIndex_eq_zero_of_isLayer hu, ofAdd_zero]

end QCA

/-! ### The shift -/

section Shift

variable {𝕜 : Type} [Field 𝕜] [StarRing 𝕜]

theorem mem_metricNbhd_of_sub_mem {c : ℤ} {S : RegionCat ℤ} {t : ℤ} (h : t - c ∈ S.carrier) :
    t ∈ (RegionCat.metricNbhd (c.natAbs : ℝ≥0) S).carrier :=
  RegionCat.mem_metricNbhd.2 ⟨t - c, h, by
    rw [Int.dist_eq]
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs]
    simp⟩

/-- Translation by `c` on the functions on a region. -/
def translateLin (c : ℤ) (S : RegionCat ℤ) :
    (S.carrier → 𝕜) →ₗ[𝕜] ((RegionCat.metricNbhd (c.natAbs : ℝ≥0) S).carrier → 𝕜) where
  toFun m t := if h : t.1 - c ∈ S.carrier then m ⟨t.1 - c, h⟩ else 0
  map_add' m m' := funext fun t => by by_cases h : t.1 - c ∈ S.carrier <;> simp [h]
  map_smul' a m := funext fun t => by by_cases h : t.1 - c ∈ S.carrier <;> simp [h]

/-- Translation by `c` sites, a bounded-spread homomorphism of spread `|c|`. -/
def translate (c : ℤ) : BoundedSpreadHom (c.natAbs : ℝ≥0) (qla ℤ 𝕜) (qla ℤ 𝕜) :=
  ofLinear (translateLin c)
    (fun S m => funext fun t => by
      by_cases h : t.1 - c ∈ S.carrier <;> simp [translateLin, h])
    (fun {S T} hST m => funext fun t => by
      by_cases h : t.1 - c ∈ S.carrier
      · simp [translateLin, extendZero_apply, h, hST h, mem_metricNbhd_of_sub_mem h]
      · by_cases ht : t.1 ∈ (RegionCat.metricNbhd (c.natAbs : ℝ≥0) S).carrier <;>
          by_cases hT : t.1 - c ∈ T.carrier <;>
          simp [translateLin, extendZero_apply, h, ht, hT])

theorem linPart_translate_single (c x : ℤ) (a : 𝕜) :
    linPart (translate (𝕜 := 𝕜) c) (Finsupp.single x a) = Finsupp.single (x + c) a := by
  rw [single_eq_embed, translate, linPart_ofLinear_embed]
  refine Finsupp.ext fun y => ?_
  rw [embed_apply]
  by_cases hy : y = x + c
  · subst hy
    have hmem : x + c - c ∈ (RegionCat.of {x}).carrier := by simp
    simp only [mem_metricNbhd_of_sub_mem hmem, ↓reduceDIte]
    simp [translateLin]
  · have hne : y - c ≠ x := fun h => hy (by omega)
    rw [Finsupp.single_eq_of_ne hy]
    by_cases hy' : y ∈ (RegionCat.metricNbhd (c.natAbs : ℝ≥0) (RegionCat.of {x})).carrier
    · simp only [hy', ↓reduceDIte]
      simp [translateLin, hne]
    · simp only [hy', ↓reduceDIte]

theorem map_half_translate (c n : ℤ) :
    (half 𝕜 n).map (linPart (translate (𝕜 := 𝕜) c)) = half 𝕜 (n + c) := by
  rw [half, half, Finsupp.supported_eq_span_single, Finsupp.supported_eq_span_single,
    Submodule.map_span, Set.image_image]
  simp only [linPart_translate_single]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_Iic]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i + c, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j - c, by omega, by simp⟩

theorem linPart_translate_comp (c c' : ℤ) :
    linPart ((translate (𝕜 := 𝕜) c).comp (translate c')) = linPart (translate (𝕜 := 𝕜) (c + c')) :=
  Finsupp.lhom_ext fun x a => by
    rw [linPart_comp, LinearMap.comp_apply, linPart_translate_single, linPart_translate_single,
      linPart_translate_single, add_assoc]

theorem linPart_translate_zero : linPart (translate (𝕜 := 𝕜) 0) = LinearMap.id :=
  Finsupp.lhom_ext fun x a => by rw [linPart_translate_single, add_zero, LinearMap.id_apply]

/-- The shift by one site, as a QCA of the square-zero system on `ℤ`. -/
def shift : QCA (obj ℤ 𝕜) :=
  QCA.ofInverse (translate 1) (translate (-1))
    (linPart_injective (by
      rw [linPart_translate_comp, linPart_weaken, linPart_id, add_neg_cancel,
        linPart_translate_zero]))
    (linPart_injective (by
      rw [linPart_translate_comp, linPart_weaken, linPart_id, neg_add_cancel,
        linPart_translate_zero]))

theorem isBanded_shift : IsBanded (linEquiv (shift (𝕜 := 𝕜))) 1 := fun n => by
  refine ⟨?_, ?_⟩
  · change (half 𝕜 n).map (linPart (translate 1)) ≤ _
    rw [map_half_translate]
    exact_mod_cast le_rfl
  · change (half 𝕜 n).map (linPart (translate (-1))) ≤ _
    rw [map_half_translate]
    exact half_mono (by omega)

/-- The shift moves exactly one dimension across the cut. -/
theorem qcaIndex_shift : qcaIndex (shift (𝕜 := 𝕜)) = 1 := by
  rw [qcaIndex_eq isBanded_shift, indexAt]
  change ((fc (half 𝕜 (-((1 : ℕ) : ℤ))) ((half 𝕜 0).map (linPart (translate 1))) : ℕ) : ℤ) - _ = _
  rw [map_half_translate, fc_half (by norm_num)]
  norm_num

/-- **The shift on `ℤ` is not a finite-depth circuit.** -/
theorem shift_not_mem_circuitSubgroup : shift (𝕜 := 𝕜) ∉ QCA.circuitSubgroup (obj ℤ 𝕜) := by
  intro h
  have h' := MonoidHom.mem_ker.1 (circuitSubgroup_le_ker h)
  change Multiplicative.ofAdd (qcaIndex shift) = 1 at h'
  rw [qcaIndex_shift] at h'
  exact one_ne_zero (Multiplicative.ofAdd.injective (h'.trans ofAdd_zero.symm))

/-- **QCAs modulo circuits are nontrivial on `ℤ`**: the shift is not a circuit. -/
instance : Nontrivial (QCAClass (obj ℤ 𝕜)) :=
  ⟨⟨QuotientGroup.mk 1, QuotientGroup.mk shift, fun h =>
    shift_not_mem_circuitSubgroup (by simpa using QuotientGroup.eq.1 h)⟩⟩

end Shift

end ShiftIndex
