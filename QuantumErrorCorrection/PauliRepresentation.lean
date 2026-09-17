/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.Pauli
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Unitary realizations of the Pauli group

The coefficient field `k` has an involution (`[Field k] [StarRing k]`). The phase character
is a parameter with values in `unitary k`: no distinguished primitive root is chosen.
A field-valued primitive root can be used when `star ω = ω⁻¹`. No analytic or algebraic
closure assumptions are required; the construction applies to algebraic and cyclotomic
fields equipped with an appropriate involution.
The computational basis is indexed by `Qudits → ZMod d`, hence has dimension
`d ^ Fintype.card Qudits`. Our convention is
`ρ(c,a,b)|j⟩ = χ(c + ⟨j,b⟩)|j+a⟩`.
-/

@[expose] public section

namespace PauliGroup

/-- A faithful phase character with values in the unitary elements of the coefficient field. -/
structure PhaseCharacter (k : Type*) [Field k] [StarRing k] (d : ℕ) where
  hom : Multiplicative (ZMod d) →* unitary k
  injective : Function.Injective hom

variable {k : Type*} [Field k] [StarRing k]

namespace PhaseCharacter

variable {d : ℕ}

/-- Every chosen primitive unitary root supplies a phase character. -/
noncomputable def ofPrimitiveRoot [NeZero d] (ω : unitary k) (hω : IsPrimitiveRoot ω d) :
    PhaseCharacter k d where
  hom :=
    { toFun := fun c => ω ^ c.toAdd.val
      map_one' := by simp
      map_mul' := by
        intro a b
        change ω ^ (a.toAdd + b.toAdd).val = _
        rw [ZMod.val_add, ← pow_eq_pow_mod _ hω.pow_eq_one, pow_add] }
  injective := by
    intro a b h
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective
    exact hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h

/-- The phase in the coefficient field corresponding to an exponent. -/
noncomputable def value (χ : PhaseCharacter k d) (c : ZMod d) : k :=
  χ.hom (Multiplicative.ofAdd c)

@[simp] lemma value_zero (χ : PhaseCharacter k d) : χ.value 0 = 1 := by
  exact congrArg Subtype.val χ.hom.map_one

@[simp] lemma value_add (χ : PhaseCharacter k d) (a b : ZMod d) :
    χ.value (a + b) = χ.value a * χ.value b := by
  exact congrArg Subtype.val (χ.hom.map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

lemma value_injective (χ : PhaseCharacter k d) : Function.Injective χ.value := by
  intro a b h
  exact Multiplicative.ofAdd.injective (χ.injective (Subtype.ext h))

lemma value_natCast (χ : PhaseCharacter k d) (n : ℕ) :
    χ.value (n : ZMod d) = χ.value 1 ^ n := by
  induction n with
  | zero => simp
  | succ n hn => simp [Nat.cast_add, hn, pow_succ]

lemma value_eq_pow [NeZero d] (χ : PhaseCharacter k d) (c : ZMod d) :
    χ.value c = χ.value 1 ^ c.val := by
  simpa using χ.value_natCast c.val

/-- A primitive root in the coefficient field supplies a phase character when the involution
sends it to its inverse. This compatibility is an explicit hypothesis on the chosen root. -/
noncomputable def ofPrimitiveRootOfStar [NeZero d] (ω : k) (hω : IsPrimitiveRoot ω d)
    (hstar : star ω = ω⁻¹) : PhaseCharacter k d := by
  have hu : ω ∈ unitary k := by
    apply Unitary.mem_iff_self_mul_star.mpr
    rw [hstar, mul_inv_cancel₀ (hω.ne_zero (NeZero.ne d))]
  exact ofPrimitiveRoot ⟨ω, hu⟩
    ((IsPrimitiveRoot.map_iff_of_injective (f := (unitary k).subtype)
      Subtype.val_injective).mp hω)

@[simp] lemma ofPrimitiveRoot_value [NeZero d] (ω : unitary k)
    (hω : IsPrimitiveRoot ω d) (c : ZMod d) :
    (ofPrimitiveRoot ω hω).value c = (ω : k) ^ c.val := rfl

@[simp] lemma ofPrimitiveRootOfStar_value [NeZero d] (ω : k)
    (hω : IsPrimitiveRoot ω d) (hstar : star ω = ω⁻¹) (c : ZMod d) :
    (ofPrimitiveRootOfStar ω hω hstar).value c = ω ^ c.val := rfl

/-- A field endomorphism preserves unitarity on these roots: its image of a primitive root
is a power of that root. It need not commute with star elsewhere in the field. -/
lemma star_map_primitiveRoot [NeZero d] (ω : k) (hω : IsPrimitiveRoot ω d)
    (hstar : star ω = ω⁻¹) (σ : k →+* k) : star (σ ω) = (σ ω)⁻¹ := by
  obtain ⟨n, _, hn⟩ := hω.eq_pow_of_pow_eq_one
    (show (σ ω) ^ d = 1 by rw [← map_pow, hω.pow_eq_one, map_one])
  rw [← hn, star_pow, hstar, inv_pow]

lemma value_ne_zero (χ : PhaseCharacter k d) (c : ZMod d) : χ.value c ≠ 0 := by
  have h := (χ.hom (Multiplicative.ofAdd c)).property.2
  intro hz
  change χ.value c * star (χ.value c) = 1 at h
  simp [hz] at h

@[simp] lemma value_neg (χ : PhaseCharacter k d) (c : ZMod d) :
    χ.value (-c) = star (χ.value c) := by
  change ((χ.hom ((Multiplicative.ofAdd c)⁻¹) : unitary k) : k) = _
  rw [map_inv]
  rfl

section Matrices

variable {Qudits : Type*} [Fintype Qudits] [DecidableEq Qudits]
variable {d : ℕ} [NeZero d] (χ : PhaseCharacter k d)

/-- Clock, shift, and phase in the computational basis for the chosen phase character. -/
noncomputable def matrix (g : PauliGroup Qudits d) :
    Matrix (Qudits → ZMod d) (Qudits → ZMod d) k :=
  fun i j => if i = j + g.shift then χ.value (g.phase + pairing j g.clock) else 0

omit [DecidableEq Qudits] [NeZero d] in
@[simp] lemma matrix_one : χ.matrix (1 : PauliGroup Qudits d) = 1 := by
  ext i j
  simp [matrix, Matrix.one_apply]

lemma matrix_mul (g h : PauliGroup Qudits d) :
    χ.matrix (g * h) = χ.matrix g * χ.matrix h := by
  ext i j
  simp only [Matrix.mul_apply, matrix]
  rw [Finset.sum_eq_single (j + h.shift)]
  · simp only [ite_true, mul_phase, mul_shift, mul_clock]
    rw [pairing_add_left, pairing_add_right]
    by_cases hij : i = j + (g.shift + h.shift)
    · have hij' : i = j + h.shift + g.shift := by rw [hij]; abel
      rw [ite_eq_left hij, ite_eq_left hij']
      rw [← χ.value_add]
      congr 1
      ring
    · have hij' : i ≠ j + h.shift + g.shift := by
        intro hi; apply hij; rw [hi]; abel
      simp [hij, hij']
  · intro k _ hk
    simp [hk]
  · simp

omit [DecidableEq Qudits] [NeZero d] in
lemma matrix_inv (g : PauliGroup Qudits d) :
    χ.matrix g⁻¹ = star (χ.matrix g) := by
  ext i j
  change (if i = j + -g.shift then
    χ.value (pairing g.shift g.clock - g.phase + pairing j (-g.clock)) else 0) =
    star (if j = i + g.shift then χ.value (g.phase + pairing i g.clock) else 0)
  by_cases hij : j = i + g.shift
  · have hi : i = j + -g.shift := by rw [hij]; abel
    rw [ite_eq_left hi, ite_eq_left hij, hij, pairing_neg_right, pairing_add_left]
    rw [← χ.value_neg]
    congr 1
    ring
  · have hi : i ≠ j + -g.shift := by
      intro hi; apply hij; rw [hi]; abel
    simp [hi, hij]

/-- The unitary representation for the chosen phase character. -/
noncomputable def unitaryHom :
    PauliGroup Qudits d →* Matrix.unitaryGroup (Qudits → ZMod d) k where
  toFun g := ⟨χ.matrix g, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [← matrix_inv, ← matrix_mul, mul_inv_cancel, matrix_one])⟩
  map_one' := Subtype.ext χ.matrix_one
  map_mul' g h := Subtype.ext (χ.matrix_mul g h)

omit [NeZero d] in
lemma matrix_injective : Function.Injective (χ.matrix (Qudits := Qudits)) := by
  intro g h heq
  have hs : g.shift = h.shift := by
    have hh := congrFun (congrFun heq g.shift) 0
    by_contra hn
    simp [matrix, hn, χ.value_ne_zero] at hh
  have hp : g.phase = h.phase := by
    apply χ.value_injective
    have hh := congrFun (congrFun heq g.shift) 0
    simpa [matrix, hs] using hh
  have hb : g.clock = h.clock := by
    funext q
    have hh := congrFun (congrFun heq (Pi.single q 1 + g.shift)) (Pi.single q 1)
    have hh' : g.phase + g.clock q = h.phase + h.clock q := by
      apply χ.value_injective
      simpa [matrix, hs, pairing, Pi.single_apply] using hh
    exact add_left_cancel (hp ▸ hh')
  exact PauliGroup.ext hp hs hb

lemma unitaryHom_injective : Function.Injective (χ.unitaryHom (Qudits := Qudits)) := by
  intro g h heq
  exact χ.matrix_injective (congrArg Subtype.val heq)

/-- The concrete subgroup consisting of phase times shift times clock matrices. -/
noncomputable def concreteSubgroup : Subgroup (Matrix.unitaryGroup (Qudits → ZMod d) k) :=
  χ.unitaryHom.range

/-- The abstract cocycle presentation is isomorphic to its concrete unitary subgroup. -/
noncomputable def unitaryEquiv : PauliGroup Qudits d ≃* χ.concreteSubgroup (Qudits := Qudits) :=
  MonoidHom.ofInjective χ.unitaryHom_injective

end Matrices

end PhaseCharacter

/-- Scalar phases as unitary matrices. -/
noncomputable def scalarUnitaryHom (ι : Type*) [Fintype ι] [DecidableEq ι] :
    unitary k →* Matrix.unitaryGroup ι k where
  toFun z := ⟨Matrix.scalar ι (z : k), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    have hs : star (Matrix.scalar ι (z : k)) = Matrix.scalar ι (star (z : k)) := by
      ext i j
      by_cases h : i = j <;>
        simp [Matrix.scalar_apply, Matrix.star_apply, h, eq_comm]
    rw [hs, ← map_mul, z.property.2, map_one]⟩
  map_one' := Subtype.ext (map_one (Matrix.scalar ι))
  map_mul' z w := Subtype.ext (map_mul (Matrix.scalar ι) (z : k) (w : k))

lemma scalarUnitaryHom_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : unitary k) (g : Matrix.unitaryGroup ι k) : Commute (scalarUnitaryHom ι z) g := by
  apply Subtype.ext
  exact Matrix.scalar_comm _ (fun _ => Commute.all _ _) _

lemma scalarUnitaryHom_injective {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Injective (scalarUnitaryHom (k := k) ι) := by
  intro z w h
  exact Subtype.ext (Matrix.scalar_inj.mp (congrArg Subtype.val h))

variable {Qudits : Type*} [Fintype Qudits] [DecidableEq Qudits] {d : ℕ}

namespace PhaseCharacter

variable [NeZero d] (χ : PhaseCharacter k d)

@[simp] lemma matrix_phaseGen (c : ZMod d) :
    χ.matrix (phaseGen c : PauliGroup Qudits d) =
      Matrix.scalar (Qudits → ZMod d) (χ.value c) := by
  ext i j
  simp [matrix, phaseGen, Matrix.scalar_apply, Matrix.diagonal_apply]

end PhaseCharacter

/-- Faithfulness on the central phase group implies faithfulness on the entire Pauli group. -/
lemma hom_injective_of_phase {G : Type*} [Group G] (f : PauliGroup Qudits d →* G)
    (hf : Function.Injective (fun c => f (phaseGen c))) : Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  intro g hg
  have hc (k : PauliGroup Qudits d) : symplecticForm (vec k) (vec g) = 0 := by
    apply hf
    change f (phaseGen (symplecticForm (vec k) (vec g))) = f (phaseGen 0)
    rw [← commutatorElement_eq]
    simp [commutatorElement_def, hg, show phaseGen (0 : ZMod d) = (1 : PauliGroup Qudits d) from rfl]
  have hs : g.shift = 0 := by
    funext q
    have h := hc (clockGen q)
    simpa [symplecticForm, vec, clockGen, pairing] using h
  have hb : g.clock = 0 := by
    funext q
    have h := hc (shiftGen q)
    simpa [symplecticForm, vec, shiftGen, pairing] using h
  have he : g = phaseGen g.phase := PauliGroup.ext rfl hs hb
  have hp : g.phase = 0 := hf (by
    change f (phaseGen g.phase) = f (1 : PauliGroup Qudits d)
    rw [← he, hg]
    exact f.map_one.symm)
  exact PauliGroup.ext hp hs hb

namespace PhaseCharacter

variable [NeZero d]

/-- The chosen phase character acting by scalar matrices. -/
noncomputable def scalarHom (χ : PhaseCharacter k d) :
    Multiplicative (ZMod d) →* Matrix.unitaryGroup (Qudits → ZMod d) k :=
  (scalarUnitaryHom _).comp χ.hom

lemma scalarHom_injective (χ : PhaseCharacter k d) :
    Function.Injective (χ.scalarHom (Qudits := Qudits)) :=
  scalarUnitaryHom_injective.comp χ.injective

lemma scalarHom_commute (χ : PhaseCharacter k d) (c : Multiplicative (ZMod d))
    (A : Matrix.unitaryGroup (Qudits → ZMod d) k) : Commute (χ.scalarHom c) A :=
  scalarUnitaryHom_commute _ _

end PhaseCharacter

/-- A choice of shift and clock powers satisfying the Weyl relation for `χ`.
The homomorphisms encode addition of exponents (including their order dividing `d`).
No particular matrices or computational basis are prescribed. -/
structure WeylSystem (Qudits : Type*) [Fintype Qudits] [DecidableEq Qudits]
    (d : ℕ) [NeZero d] (χ : PhaseCharacter k d) where
  shift : Multiplicative (Qudits → ZMod d) →* Matrix.unitaryGroup (Qudits → ZMod d) k
  clock : Multiplicative (Qudits → ZMod d) →* Matrix.unitaryGroup (Qudits → ZMod d) k
  weyl (a b : Multiplicative (Qudits → ZMod d)) :
    clock b * shift a = χ.scalarHom (Multiplicative.ofAdd (pairing a.toAdd b.toAdd)) *
      shift a * clock b

namespace WeylSystem

variable [NeZero d] {χ : PhaseCharacter k d} (W : WeylSystem Qudits d χ)

/-- Extract a clock/shift system from any representation with the prescribed scalar phases. -/
noncomputable def ofHom (f : PauliGroup Qudits d →* Matrix.unitaryGroup (Qudits → ZMod d) k)
    (hphase : ∀ c, f (phaseGen c) = χ.scalarHom (Multiplicative.ofAdd c)) :
    WeylSystem Qudits d χ where
  shift := f.comp
    { toFun := fun a => ⟨0, a.toAdd, 0⟩
      map_one' := rfl
      map_mul' := by intro a b; ext <;> simp }
  clock := f.comp
    { toFun := fun b => ⟨0, 0, b.toAdd⟩
      map_one' := rfl
      map_mul' := by intro a b; ext <;> simp }
  weyl a b := by
    change f ⟨0, 0, b.toAdd⟩ * f ⟨0, a.toAdd, 0⟩ =
      χ.scalarHom (Multiplicative.ofAdd (pairing a.toAdd b.toAdd)) *
        f ⟨0, a.toAdd, 0⟩ * f ⟨0, 0, b.toAdd⟩
    rw [← hphase, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp [phaseGen]

/-- Realize an abstract element using the chosen phase, shift powers, and clock powers. -/
noncomputable def hom : PauliGroup Qudits d →* Matrix.unitaryGroup (Qudits → ZMod d) k where
  toFun g := χ.scalarHom (Multiplicative.ofAdd g.phase) *
    W.shift (Multiplicative.ofAdd g.shift) * W.clock (Multiplicative.ofAdd g.clock)
  map_one' := by change χ.scalarHom 1 * W.shift 1 * W.clock 1 = 1; simp
  map_mul' g h := by
    let P := χ.scalarHom (Qudits := Qudits)
    let X := W.shift
    let Z := W.clock
    let c := Multiplicative.ofAdd g.phase
    let e := Multiplicative.ofAdd h.phase
    let a := Multiplicative.ofAdd g.shift
    let b := Multiplicative.ofAdd g.clock
    let a' := Multiplicative.ofAdd h.shift
    let b' := Multiplicative.ofAdd h.clock
    let t := Multiplicative.ofAdd (pairing h.shift g.clock)
    change P (c * e * t) * X (a * a') * Z (b * b') =
      P c * X a * Z b * (P e * X a' * Z b')
    simp only [map_mul]
    have he : Commute (X a * Z b) (P e) := (χ.scalarHom_commute e (X a * Z b)).symm
    have ht : Commute (P t) (X a) := χ.scalarHom_commute t (X a)
    have hw : Z b * X a' = P t * X a' * Z b := W.weyl a' b
    calc
      P c * P e * P t * (X a * X a') * (Z b * Z b') =
          P c * P e * (X a * (P t * X a' * Z b)) * Z b' := by
        simp only [mul_assoc]
        rw [ht.left_comm]
      _ = P c * P e * (X a * (Z b * X a')) * Z b' := by rw [← hw]
      _ = P c * X a * Z b * (P e * X a' * Z b') := by
        have hh := he.eq
        calc
          _ = P c * (P e * (X a * Z b)) * (X a' * Z b') := by simp only [mul_assoc]
          _ = _ := by rw [← hh]; simp only [mul_assoc]

@[simp] lemma hom_phaseGen (c : ZMod d) :
    W.hom (phaseGen c) = χ.scalarHom (Multiplicative.ofAdd c) := by
  change χ.scalarHom (Multiplicative.ofAdd c) * W.shift 1 * W.clock 1 = _
  simp

@[simp] lemma ofHom_hom
    (f : PauliGroup Qudits d →* Matrix.unitaryGroup (Qudits → ZMod d) k)
    (hphase : ∀ c, f (phaseGen c) = χ.scalarHom (Multiplicative.ofAdd c)) :
    (ofHom f hphase).hom = f := by
  apply MonoidHom.ext
  intro g
  change χ.scalarHom (Multiplicative.ofAdd g.phase) *
    f ⟨0, g.shift, 0⟩ * f ⟨0, 0, g.clock⟩ = f g
  rw [← hphase, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp [phaseGen]

/-- Primitivity of the phase forces every Weyl system to be faithful. -/
lemma hom_injective : Function.Injective W.hom :=
  hom_injective_of_phase W.hom (by
    intro a b h
    simp only [W.hom_phaseGen] at h
    exact Multiplicative.ofAdd.injective (χ.scalarHom_injective h))

/-- The concrete subgroup for the chosen clock and shift powers. -/
noncomputable def subgroup : Subgroup (Matrix.unitaryGroup (Qudits → ZMod d) k) := W.hom.range

lemma mem_subgroup_iff (A : Matrix.unitaryGroup (Qudits → ZMod d) k) :
    A ∈ W.subgroup ↔ ∃ (c : ZMod d) (a b : Qudits → ZMod d),
      χ.scalarHom (Multiplicative.ofAdd c) * W.shift (Multiplicative.ofAdd a) *
        W.clock (Multiplicative.ofAdd b) = A := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.phase, g.shift, g.clock, rfl⟩
  · rintro ⟨c, a, b, h⟩
    exact ⟨⟨c, a, b⟩, h⟩

/-- The desired isomorphism, parameterized by the clock/shift system and primitive phase. -/
noncomputable def equiv : PauliGroup Qudits d ≃* W.subgroup :=
  MonoidHom.ofInjective W.hom_injective

end WeylSystem

namespace PhaseCharacter

variable [NeZero d] (χ : PhaseCharacter k d)

/-- The computational-basis clock and shift system for any chosen primitive phase. -/
noncomputable def weylSystem : WeylSystem Qudits d χ :=
  WeylSystem.ofHom χ.unitaryHom (fun c => Subtype.ext (χ.matrix_phaseGen c))

end PhaseCharacter

/-- Cyclotomic reparameterization: `ω ↦ ω^u` scales phases and clock exponents.
It scales the symplectic form as well, so in general it does not fix the center pointwise. -/
def galoisEquiv (u : (ZMod d)ˣ) : PauliGroup Qudits d ≃* PauliGroup Qudits d where
  toFun g := ⟨u * g.phase, g.shift, fun q => u * g.clock q⟩
  invFun g := ⟨↑u⁻¹ * g.phase, g.shift, fun q => ↑u⁻¹ * g.clock q⟩
  left_inv g := by ext <;> simp [← mul_assoc]
  right_inv g := by ext <;> simp [← mul_assoc]
  map_mul' g h := by
    ext
    · simp only [mul_phase, pairing, mul_add, Finset.mul_sum]
      congr 2
      funext q
      ring
    · rfl
    · simp [mul_add]

omit [DecidableEq Qudits] in
@[simp] lemma galoisEquiv_one :
    galoisEquiv (Qudits := Qudits) (1 : (ZMod d)ˣ) = MulEquiv.refl _ := by
  ext g <;> simp [galoisEquiv]

omit [DecidableEq Qudits] in
lemma galoisEquiv_mul (u v : (ZMod d)ˣ) :
    galoisEquiv (Qudits := Qudits) (u * v) = (galoisEquiv v).trans (galoisEquiv u) := by
  ext g <;> simp [galoisEquiv, mul_assoc]

/-- The cyclotomic unit group acts by automorphisms of the abstract Pauli group. -/
def galoisAction : (ZMod d)ˣ →* MulAut (PauliGroup Qudits d) where
  toFun := galoisEquiv
  map_one' := galoisEquiv_one
  map_mul' u v := galoisEquiv_mul u v

namespace PhaseCharacter

/-- Changing the primitive phase by a unit exponent. -/
def twist (χ : PhaseCharacter k d) (u : (ZMod d)ˣ) : PhaseCharacter k d where
  hom := χ.hom.comp
    { toFun := fun c => Multiplicative.ofAdd (u * c.toAdd)
      map_one' := by simp
      map_mul' := by intro a b; exact congrArg Multiplicative.ofAdd (mul_add _ _ _) }
  injective := by
    intro a b h
    have hh := congrArg Multiplicative.toAdd (χ.injective h)
    apply Multiplicative.toAdd.injective
    exact (Units.mul_right_inj u).mp hh

@[simp] lemma twist_value (χ : PhaseCharacter k d) (u : (ZMod d)ˣ) (c : ZMod d) :
    (χ.twist u).value c = χ.value (u * c) := rfl

omit [DecidableEq Qudits] in
/-- Compatibility of the concrete realization with cyclotomic reparameterization. -/
lemma matrix_twist (χ : PhaseCharacter k d) (u : (ZMod d)ˣ) (g : PauliGroup Qudits d) :
    (χ.twist u).matrix g = χ.matrix (galoisEquiv u g) := by
  ext i j
  simp only [matrix, twist_value, galoisEquiv, MulEquiv.coe_mk]
  congr 1
  congr 1
  simp only [mul_add, pairing, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  change ↑u * (j q * g.clock q) = j q * (↑u * g.clock q)
  ring

variable {K : Type*} [Field K] [StarRing K]

omit [DecidableEq Qudits] in
/-- Entrywise compatibility with coefficient-field maps, assuming compatibility of the chosen
phase characters. The field map need not preserve star on all coefficients. -/
lemma matrix_map (χ : PhaseCharacter k d) (ψ : PhaseCharacter K d) (σ : k →+* K)
    (hσ : ∀ c, σ (χ.value c) = ψ.value c) (g : PauliGroup Qudits d) :
    (χ.matrix g).map σ = ψ.matrix g := by
  ext i j
  simp only [Matrix.map_apply, matrix]
  split_ifs <;> simp [hσ]

omit [DecidableEq Qudits] in
/-- It suffices to specify the Galois action on the primitive phase itself. -/
lemma matrix_map_of_root [NeZero d] (χ : PhaseCharacter k d)
    (ψ : PhaseCharacter K d) (σ : k →+* K)
    (hσ : σ (χ.value 1) = ψ.value 1) (g : PauliGroup Qudits d) :
    (χ.matrix g).map σ = ψ.matrix g :=
  matrix_map χ ψ σ (fun c => by rw [χ.value_eq_pow, ψ.value_eq_pow, map_pow, hσ]) g

omit [DecidableEq Qudits] in
/-- A field map transports the realization to the image primitive root, provided the
involution in each field inverts its chosen root. No preservation of star away from those
roots is needed, so this applies to Galois automorphisms as well as field embeddings. -/
lemma matrix_map_primitiveRoot [NeZero d] (ω : k) (hω : IsPrimitiveRoot ω d)
    (hstar : star ω = ω⁻¹) (σ : k →+* K) (hstar' : star (σ ω) = (σ ω)⁻¹)
    (g : PauliGroup Qudits d) :
    ((ofPrimitiveRootOfStar ω hω hstar).matrix g).map σ =
      (ofPrimitiveRootOfStar (σ ω) (hω.map_of_injective σ.injective) hstar').matrix g := by
  apply matrix_map
  intro c
  simp

omit [DecidableEq Qudits] in
/-- Galois automorphisms transport the realization without any additional hypothesis about
their action on star: unitarity of the conjugate primitive root follows automatically. -/
lemma matrix_galois_primitiveRoot [NeZero d] (ω : k) (hω : IsPrimitiveRoot ω d)
    (hstar : star ω = ω⁻¹) (σ : k ≃+* k) (g : PauliGroup Qudits d) :
    ((ofPrimitiveRootOfStar ω hω hstar).matrix g).map σ =
      (ofPrimitiveRootOfStar (σ ω) (hω.map_of_injective σ.injective)
        (star_map_primitiveRoot ω hω hstar σ.toRingHom)).matrix g :=
  matrix_map_primitiveRoot ω hω hstar σ.toRingHom _ g

end PhaseCharacter

namespace WeylSystem

variable [NeZero d] {χ : PhaseCharacter k d} (W : WeylSystem Qudits d χ)

/-- Transport any chosen Weyl system under the cyclotomic change `ω ↦ ω^u`. -/
noncomputable def twist (u : (ZMod d)ˣ) : WeylSystem Qudits d (χ.twist u) :=
  ofHom (W.hom.comp (galoisEquiv u).toMonoidHom) (fun c => by
    change W.hom (galoisEquiv u (phaseGen c)) = _
    have hg : galoisEquiv u (phaseGen c : PauliGroup Qudits d) =
        phaseGen ((u : ZMod d) * c) := by
      ext <;> simp [galoisEquiv, phaseGen]
    rw [hg, W.hom_phaseGen]
    rfl)

/-- Galois reparameterization intertwines the realizations for arbitrary clock/shift choices. -/
lemma twist_hom (u : (ZMod d)ˣ) :
    (W.twist u).hom = W.hom.comp (galoisEquiv u).toMonoidHom :=
  ofHom_hom _ _

end WeylSystem

end PauliGroup
