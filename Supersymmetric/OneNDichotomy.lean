import Supersymmetric.OneN
import Mathlib.Algebra.Algebra.Bilinear

/-!
# A dichotomy between `A` and `B`

If `𝕜` acts on `M` without zero `SMul`-divisors and `3` is not a zero divisor in `𝕜`, the odd
Jacobi identity forces a dichotomy: `A` and `B` can never both be nonzero.

Every lemma about a bare `(B, A)` pair (before `section Converse`, and most of what's inside it) is
`private`: each takes only the one or two hypotheses (`B.IsSymm`, `IsSkewAdjoint`, `OddJacobi`) its
proof actually needs, and serves only as a stepping stone toward the file's two genuinely public
results, `ofLieSuperAlgebra_B_eq_zero_of_ne_zero` and `ofLieSuperAlgebra_A_eq_zero_or_B_eq_zero`
(plus the independent orthogonality fact `ofLieSuperAlgebra_apply_apply_eq_zero_of_apply_eq_zero`).
All public theorems take a `LieSuperAlgebra 𝕜 (Space 𝕜 M)` instance `lsa` and nothing else, reading
off `ofLieSuperAlgebra_B` and `ofLieSuperAlgebra_A` via the round trip of
`LieSuperAlgebra.OneN.Converse` — since `lsa` already guarantees all three hypotheses at once, a
caller never has to assemble them by hand.

The mechanism: `OddJacobi` at `(x,x,x)` gives `3 • (B x x • A x) = 0`, which cancels (under the
hypotheses above) to `B x x • A x = 0`, i.e. `B x x = 0 ∨ A x = 0` for every `x`.  Separately,
`OddJacobi` at `(v,w,z)` with `A v = A w = 0 ≠ A z` collapses to `B v w • A z = 0`, so `B` vanishes
on `ker A × ker A` as soon as `A` is nonzero anywhere.  Combining these two facts and specializing
`w := v` shows `B v v ≠ 0` is impossible whenever `A ≠ 0` — so `A ≠ 0` alone (no injectivity needed)
already forces `B` to vanish on the whole diagonal, hence (by polarization, using
`Invertible (2 : 𝕜)`) everywhere. -/

universe u v

namespace LieSuperAlgebra.OneN

variable {𝕜 : Type u} {M : Type v} [CommRing 𝕜] [Invertible (2 : 𝕜)]
  [AddCommGroup M] [Module 𝕜 M]

private theorem polarize_symm {B : LinearMap.BilinForm 𝕜 M} (hB : B.IsSymm)
    (h0 : ∀ x, B x x = 0) : B = 0 := by
  ext x y
  have hxy := h0 (x + y)
  simp only [map_add, LinearMap.add_apply, h0 x, h0 y, zero_add, add_zero, hB.eq y x] at hxy
  have h2 : (2 : 𝕜) • B x y = 0 := by rw [two_smul]; exact hxy
  have h3 : B x y = ⅟(2 : 𝕜) • ((2 : 𝕜) • B x y) := by
    rw [← mul_smul, invOf_mul_self, one_smul]
  rw [h3, h2, smul_zero, LinearMap.zero_apply, LinearMap.zero_apply]

omit [Invertible (2 : 𝕜)] in
private theorem smul_self_smul_eq_zero {B : LinearMap.BilinForm 𝕜 M} {A : Module.End 𝕜 M}
    (hxyz : OddJacobi 𝕜 M B A) (h3 : (3 : 𝕜) ≠ 0) [NoZeroSMulDivisors 𝕜 M] (x : M) :
    B x x • A x = 0 := by
  have h := hxyz x x x
  have h3' : (3 : 𝕜) • (B x x • A x) = 0 := by
    have e : (3 : 𝕜) • (B x x • A x) = B x x • A x + B x x • A x + B x x • A x := by module
    rw [e]; exact h
  exact (eq_zero_or_eq_zero_of_smul_eq_zero h3').resolve_left h3

omit [Invertible (2 : 𝕜)] in
/-- The pointwise dichotomy: at every odd generator, either `B` degenerates on it or `A` kills
it. -/
private theorem dichotomy_core {B : LinearMap.BilinForm 𝕜 M} {A : Module.End 𝕜 M}
    (hxyz : OddJacobi 𝕜 M B A) (h3 : (3 : 𝕜) ≠ 0) [NoZeroSMulDivisors 𝕜 M] (x : M) :
    B x x = 0 ∨ A x = 0 :=
  eq_zero_or_eq_zero_of_smul_eq_zero (smul_self_smul_eq_zero hxyz h3 x)

omit [Invertible (2 : 𝕜)] in
/-- Skew-adjointness says `ker A` is `B`-orthogonal to `range A`: no `OddJacobi`, no domain
hypotheses needed. -/
private theorem ker_orthogonal_range {B : LinearMap.BilinForm 𝕜 M} {A : Module.End 𝕜 M}
    (hA : IsSkewAdjoint 𝕜 M B A) {v : M} (hv : A v = 0) (y : M) :
    B v (A y) = 0 := by
  have h := hA v y
  rw [hv, map_zero, LinearMap.zero_apply, zero_add] at h
  exact h

omit [Invertible (2 : 𝕜)] in
/-- If `A` doesn't kill `z`, `OddJacobi` at `(v,w,z)` collapses to `B v w • A z = 0`, so as long
as `A` is nonzero somewhere, `B` vanishes on any two kernel vectors of `A`. -/
private theorem ker_pairing_eq_zero_of_apply_ne_zero {B : LinearMap.BilinForm 𝕜 M}
    {A : Module.End 𝕜 M} (hxyz : OddJacobi 𝕜 M B A) [NoZeroSMulDivisors 𝕜 M]
    {v w z : M} (hv : A v = 0) (hw : A w = 0) (hz : A z ≠ 0) :
    B v w = 0 := by
  have h := hxyz v w z
  rw [hv, hw, smul_zero, smul_zero, zero_add, zero_add] at h
  exact (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_right hz

omit [Invertible (2 : 𝕜)] in
/-- `B` vanishes on `ker A × ker A` as soon as `A ≠ 0` (as an operator, not requiring injectivity
anywhere in particular). -/
private theorem eq_zero_of_apply_eq_zero_of_ne_zero {B : LinearMap.BilinForm 𝕜 M}
    {A : Module.End 𝕜 M} (hxyz : OddJacobi 𝕜 M B A) [NoZeroSMulDivisors 𝕜 M]
    {v w : M} (hv : A v = 0) (hw : A w = 0) (hA0 : A ≠ 0) :
    B v w = 0 := by
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hA0
  simp only [LinearMap.zero_apply] at hz
  exact ker_pairing_eq_zero_of_apply_ne_zero hxyz hv hw hz

section Converse

variable [lsa : LieSuperAlgebra 𝕜 (Space 𝕜 M)]

/-- The kernel of the recovered even action is `B`-orthogonal to its range, for any Lie
superalgebra structure on `Space 𝕜 M`. -/
theorem ofLieSuperAlgebra_apply_apply_eq_zero_of_apply_eq_zero
    {v : M} (hv : ofLieSuperAlgebra_A 𝕜 M v = 0) (y : M) :
    ofLieSuperAlgebra_B 𝕜 M v (ofLieSuperAlgebra_A 𝕜 M y) = 0 :=
  ker_orthogonal_range (ofLieSuperAlgebra_A_isSkewAdjoint 𝕜 M) hv y

omit [Invertible (2 : 𝕜)] in
/-- As soon as the recovered even action is nonzero, it kills the recovered pairing on any two of
its own kernel vectors.  (Subsumed by `ofLieSuperAlgebra_B_eq_zero_of_ne_zero` below, which drops
the `Av = 0`/`Aw = 0` hypotheses entirely; kept private as a stepping stone to it.) -/
private theorem ofLieSuperAlgebra_B_eq_zero_of_apply_eq_zero [NoZeroSMulDivisors 𝕜 M]
    {v w : M} (hv : ofLieSuperAlgebra_A 𝕜 M v = 0) (hw : ofLieSuperAlgebra_A 𝕜 M w = 0)
    (hA0 : ofLieSuperAlgebra_A 𝕜 M ≠ 0) :
    ofLieSuperAlgebra_B 𝕜 M v w = 0 :=
  eq_zero_of_apply_eq_zero_of_ne_zero (ofLieSuperAlgebra_oddJacobi 𝕜 M) hv hw hA0

omit [Invertible (2 : 𝕜)] in
/-- The pointwise dichotomy itself, read off any Lie superalgebra structure on `Space 𝕜 M`: at
every odd generator `v`, either the recovered pairing degenerates on `v` or the recovered even
action kills it.  This is the degenerate `w = v` case of the kernel-pairing story above — the
`OddJacobi` triple at `(v,v,v)` rather than the general `(v,w,z)` one.  (Subsumed by
`ofLieSuperAlgebra_B_eq_zero_of_ne_zero`; kept private as a stepping stone to it.) -/
private theorem ofLieSuperAlgebra_apply_self_eq_zero_or_apply_eq_zero (h3 : (3 : 𝕜) ≠ 0)
    [NoZeroSMulDivisors 𝕜 M] (v : M) :
    ofLieSuperAlgebra_B 𝕜 M v v = 0 ∨ ofLieSuperAlgebra_A 𝕜 M v = 0 :=
  dichotomy_core (ofLieSuperAlgebra_oddJacobi 𝕜 M) h3 v

omit [Invertible (2 : 𝕜)] in
/-- Contrapositing `ofLieSuperAlgebra_B_eq_zero_of_apply_eq_zero` and feeding the result back into
the pointwise dichotomy at `v` and at `w`: if `A ≠ 0` and `v`, `w` pair nontrivially under the
recovered `B`, at least one of them must be isotropic for `B`.  (Subsumed by
`ofLieSuperAlgebra_B_eq_zero_of_ne_zero`, whose proof is exactly the `w = v` case of this one; kept
private as that proof's key step.) -/
private theorem ofLieSuperAlgebra_self_eq_zero_or_self_eq_zero_of_ne_zero (h3 : (3 : 𝕜) ≠ 0)
    [NoZeroSMulDivisors 𝕜 M] (hA0 : ofLieSuperAlgebra_A 𝕜 M ≠ 0) {v w : M}
    (hBvw : ofLieSuperAlgebra_B 𝕜 M v w ≠ 0) :
    ofLieSuperAlgebra_B 𝕜 M v v = 0 ∨ ofLieSuperAlgebra_B 𝕜 M w w = 0 := by
  by_cases hAv : ofLieSuperAlgebra_A 𝕜 M v = 0
  · by_cases hAw : ofLieSuperAlgebra_A 𝕜 M w = 0
    · exact absurd (ofLieSuperAlgebra_B_eq_zero_of_apply_eq_zero hAv hAw hA0) hBvw
    · exact Or.inr ((ofLieSuperAlgebra_apply_self_eq_zero_or_apply_eq_zero h3 w).resolve_right hAw)
  · exact Or.inl ((ofLieSuperAlgebra_apply_self_eq_zero_or_apply_eq_zero h3 v).resolve_right hAv)

/-- Specializing `ofLieSuperAlgebra_self_eq_zero_or_self_eq_zero_of_ne_zero` to `w = v` turns its
conclusion into `B v v = 0 ∨ B v v = 0`, i.e. `B v v = 0` outright — directly contradicting a
hypothesis `B v v ≠ 0`.  So `A ≠ 0` alone (not injectivity) already forces `B` to vanish on the
whole diagonal, hence (`polarize_symm`) everywhere: nonzero `A` and nonzero `B` are simply
incompatible. -/
theorem ofLieSuperAlgebra_B_eq_zero_of_ne_zero (h3 : (3 : 𝕜) ≠ 0) [NoZeroSMulDivisors 𝕜 M]
    (hA0 : ofLieSuperAlgebra_A 𝕜 M ≠ 0) : ofLieSuperAlgebra_B 𝕜 M = 0 := by
  apply polarize_symm (ofLieSuperAlgebra_B_isSymm 𝕜 M)
  intro v
  by_contra hv
  exact (ofLieSuperAlgebra_self_eq_zero_or_self_eq_zero_of_ne_zero h3 hA0 hv).elim hv hv

/-- The full dichotomy in one line: for any Lie superalgebra structure on `Space 𝕜 M`, the
recovered even action and the recovered odd--odd pairing can never both be nonzero. -/
public theorem ofLieSuperAlgebra_A_eq_zero_or_B_eq_zero (h3 : (3 : 𝕜) ≠ 0) [NoZeroSMulDivisors 𝕜 M] :
    ofLieSuperAlgebra_A 𝕜 M = 0 ∨ ofLieSuperAlgebra_B 𝕜 M = 0 := by
  by_cases hA0 : ofLieSuperAlgebra_A 𝕜 M = 0
  · exact Or.inl hA0
  · exact Or.inr (ofLieSuperAlgebra_B_eq_zero_of_ne_zero h3 hA0)

end Converse

/-! ### Characteristic `3` defeats the dichotomy

Every argument above cancels a `3 •` appearing in `OddJacobi (x,x,x)`; that step needs
`(3 : 𝕜) ≠ 0`.  When `(3 : 𝕜) = 0` the dichotomy genuinely fails: here is an explicit `(B, A)` pair
on `𝕜 × 𝕜`, for *any* `𝕜` of characteristic `3`, with both `A` and `B` nonzero. -/

section CharThreeExample

variable (𝕜 : Type u) [CommRing 𝕜] [Invertible (2 : 𝕜)] [Nontrivial 𝕜]

/-- The nilpotent shift `(x,y) ↦ (0,x)` on `𝕜 × 𝕜`. -/
def char3A : Module.End 𝕜 (𝕜 × 𝕜) := (LinearMap.inr 𝕜 𝕜 𝕜).comp (LinearMap.fst 𝕜 𝕜 𝕜)

omit [Invertible (2 : 𝕜)] [Nontrivial 𝕜] in
@[simp] theorem char3A_apply (x : 𝕜 × 𝕜) : char3A 𝕜 x = (0, x.1) := rfl

/-- The (highly degenerate) form `B (x,y) (x',y') = x x'` on `𝕜 × 𝕜`. -/
def char3B : LinearMap.BilinForm 𝕜 (𝕜 × 𝕜) :=
  (LinearMap.mul 𝕜 𝕜).compl₁₂ (LinearMap.fst 𝕜 𝕜 𝕜) (LinearMap.fst 𝕜 𝕜 𝕜)

omit [Invertible (2 : 𝕜)] [Nontrivial 𝕜] in
@[simp] theorem char3B_apply (x y : 𝕜 × 𝕜) : char3B 𝕜 x y = x.1 * y.1 := rfl

omit [Invertible (2 : 𝕜)] [Nontrivial 𝕜] in
theorem char3B_isSymm : (char3B 𝕜).IsSymm := ⟨fun x y => by simp [mul_comm]⟩

omit [Invertible (2 : 𝕜)] [Nontrivial 𝕜] in
theorem char3A_isSkewAdjoint :
    LieSuperAlgebra.OneN.IsSkewAdjoint 𝕜 (𝕜 × 𝕜) (char3B 𝕜) (char3A 𝕜) := by
  intro x y; simp

omit [Invertible (2 : 𝕜)] [Nontrivial 𝕜] in
/-- `char3A` and `char3B` satisfy `OddJacobi` exactly when `(3 : 𝕜) = 0`: the diagonal triple
`((1,0),(1,0),(1,0))` produces `3 • (0,1)`, so it forces `(3 : 𝕜) = 0`, and conversely
`(3 : 𝕜) = 0` collapses every instance of the identity, whose second coordinate is always a
multiple of `3 * x.1 * y.1 * z.1`. -/
theorem char3_oddJacobi_iff :
    LieSuperAlgebra.OneN.OddJacobi 𝕜 (𝕜 × 𝕜) (char3B 𝕜) (char3A 𝕜) ↔ (3 : 𝕜) = 0 := by
  constructor
  · intro h
    have h1 := h (1, 0) (1, 0) (1, 0)
    simp only [char3B_apply, char3A_apply, mul_one, Prod.smul_mk, smul_eq_mul, mul_zero,
      Prod.mk_add_mk, add_zero, Prod.mk_eq_zero] at h1
    linear_combination h1.2
  · intro h3 x y z
    ext
    · simp
    · have e : y.1 * z.1 * x.1 + z.1 * x.1 * y.1 + x.1 * y.1 * z.1 =
          (3 : 𝕜) * (x.1 * y.1 * z.1) := by ring
      simp only [char3B_apply, char3A_apply, Prod.smul_snd, Prod.snd_add, smul_eq_mul,
        Prod.snd_zero]
      rw [e, h3, zero_mul]

omit [Invertible (2 : 𝕜)] in
/-- Over any characteristic-`3` field (e.g. `ZMod 3`), `char3A ≠ 0` and `char3B ≠ 0` both hold, so
the dichotomy `ofLieSuperAlgebra_A_eq_zero_or_B_eq_zero` is not just narrowly stated but actually
sharp: it is false without the `(3 : 𝕜) ≠ 0` hypothesis. -/
theorem char3A_ne_zero : char3A 𝕜 ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (1, 0)
  simp only [char3A_apply, LinearMap.zero_apply, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h1
  exact one_ne_zero h1.2

omit [Invertible (2 : 𝕜)] in
theorem char3B_ne_zero : char3B 𝕜 ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (1, 0)
  have h2 := DFunLike.congr_fun h1 (1, 0)
  simp only [char3B_apply, LinearMap.zero_apply, mul_one] at h2
  exact one_ne_zero h2

end CharThreeExample

section CharThreeInstance

variable {𝕜 : Type u} [CommRing 𝕜] [Invertible (2 : 𝕜)] [Nontrivial 𝕜] (h3 : (3 : 𝕜) = 0)

/-- The actual `LieSuperAlgebra` instance built from `char3B`/`char3A`, for *any* `𝕜` of
characteristic `3` (`(3 : 𝕜) = 0`). -/
@[instance_reducible]
noncomputable def char3lsa : LieSuperAlgebra 𝕜 (Space 𝕜 (𝕜 × 𝕜)) :=
  lieSuperAlgebra 𝕜 (𝕜 × 𝕜) (char3B 𝕜) (char3A 𝕜) (char3B_isSymm 𝕜) (char3A_isSkewAdjoint 𝕜)
    ((char3_oddJacobi_iff 𝕜).mpr h3)

omit [Invertible (2 : 𝕜)] [Nontrivial 𝕜] in
theorem ofLieSuperAlgebra_B_char3lsa_eq :
    letI := char3lsa h3
    ofLieSuperAlgebra_B 𝕜 (𝕜 × 𝕜) = char3B 𝕜 := by
  let := char3lsa h3
  apply LinearMap.ext fun s => LinearMap.ext fun t => ?_
  rfl

omit [Invertible (2 : 𝕜)] [Nontrivial 𝕜] in
theorem ofLieSuperAlgebra_A_char3lsa_eq :
    letI := char3lsa h3
    ofLieSuperAlgebra_A 𝕜 (𝕜 × 𝕜) = char3A 𝕜 := by
  let := char3lsa h3
  apply LinearMap.ext fun s => ?_
  show (bracket 𝕜 (𝕜 × 𝕜) (char3B 𝕜) (char3A 𝕜) (evenGen 𝕜 (𝕜 × 𝕜)) (0, s)).2 = char3A 𝕜 s
  rw [bracket_apply]
  simp [evenGen]

omit [Invertible (2 : 𝕜)] in
/-- The dichotomy is sharp: for *any* `𝕜` of characteristic `3`, the `LieSuperAlgebra` instance
`char3lsa` has both its recovered even action and its recovered odd--odd pairing nonzero — exactly
the conclusion `ofLieSuperAlgebra_A_eq_zero_or_B_eq_zero` rules out, and exactly why that theorem
needs `(3 : 𝕜) ≠ 0`. -/
theorem char3lsa_A_ne_zero_and_B_ne_zero :
    letI := char3lsa h3
    ofLieSuperAlgebra_A 𝕜 (𝕜 × 𝕜) ≠ 0 ∧ ofLieSuperAlgebra_B 𝕜 (𝕜 × 𝕜) ≠ 0 := by
  let := char3lsa h3
  rw [ofLieSuperAlgebra_A_char3lsa_eq, ofLieSuperAlgebra_B_char3lsa_eq]
  exact ⟨char3A_ne_zero 𝕜, char3B_ne_zero 𝕜⟩

end CharThreeInstance

end LieSuperAlgebra.OneN
