/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# The Pauli Group on a Finite Set of Qudits

The generalized (Weyl-Heisenberg) Pauli group on a finite set `Qudits` of qudits of dimension
`d` is presented abstractly as the central extension

  `1 → ZMod d → PauliGroup Qudits d → (Qudits → ZMod d) × (Qudits → ZMod d) → 1`

of the additive group of *symplectic vectors* `(shift exponents, clock exponents)` by the
phase group `ZMod d`. Concretely, on a single qudit with computational basis `|j⟩`, `j : ZMod d`,
the shift ("X") and clock ("Z") operators act by

  `X|j⟩ = |j+1⟩`, `Z|j⟩ = ω^j|j⟩`,

for `ω` a primitive `d`-th root of unity, satisfying `Z X = ω X Z`. Writing a general element
as `ω^phase X^shift Z^clock` for `shift clock : Qudits → ZMod d` a vector of exponents (one per
qudit) and `phase : ZMod d` an overall phase, multiplication picks up the Weyl commutation
cocycle `⟨a, b⟩ = ∑ i, a i * b i`:

  `(ω^c X^a Z^b) (ω^c' X^a' Z^b') = ω^(c + c' + ⟨a', b⟩) X^(a+a') Z^(b+b')`.

This file builds `PauliGroup Qudits d` directly as this cocycle extension (no matrices, no
roots of unity in `ℂ`: the phase just lives in `ZMod d`), proves it is a group, and relates
commutators of Pauli elements to the symplectic form on `(Qudits → ZMod d) × (Qudits → ZMod d)`,
`Ω((a,b),(a',b')) = ⟨a,b'⟩ - ⟨a',b⟩`, which is the key fact stabilizer codes are built from.
-/

@[expose] public section

open scoped commutatorElement

section Pairing

variable {Qudits : Type*} [Fintype Qudits] {d : ℕ}

/-- The standard bilinear pairing on `Qudits → ZMod d`, `⟨a, b⟩ = ∑ i, a i * b i`. This is the
pairing entering the Weyl commutation cocycle for `PauliGroup`; antisymmetrized, it gives the
symplectic form on the underlying `(Qudits → ZMod d) × (Qudits → ZMod d)`. -/
public def pairing (a b : Qudits → ZMod d) : ZMod d := ∑ i, a i * b i

@[simp] public lemma pairing_add_left (a a' b : Qudits → ZMod d) :
    pairing (a + a') b = pairing a b + pairing a' b := by
  simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp] public lemma pairing_add_right (a b b' : Qudits → ZMod d) :
    pairing a (b + b') = pairing a b + pairing a b' := by
  simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp] public lemma pairing_neg_left (a b : Qudits → ZMod d) :
    pairing (-a) b = -pairing a b := by
  simp only [pairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

@[simp] public lemma pairing_neg_right (a b : Qudits → ZMod d) :
    pairing a (-b) = -pairing a b := by
  simp only [pairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

@[simp] public lemma pairing_zero_left (b : Qudits → ZMod d) :
    pairing (0 : Qudits → ZMod d) b = 0 := by simp [pairing]

@[simp] public lemma pairing_zero_right (a : Qudits → ZMod d) :
    pairing a (0 : Qudits → ZMod d) = 0 := by simp [pairing]

end Pairing

/-- An element of the (generalized, Weyl-Heisenberg) Pauli group on a finite set `Qudits` of
qudits of dimension `d`, presented as `ω^phase X^shift Z^clock` for `ω` a primitive `d`-th root
of unity. -/
@[ext] public structure PauliGroup (Qudits : Type*) (d : ℕ) where
  /-- The overall phase: the exponent of `ω`. -/
  phase : ZMod d
  /-- The exponents of the shift ("X") generators, one per qudit. -/
  shift : Qudits → ZMod d
  /-- The exponents of the clock ("Z") generators, one per qudit. -/
  clock : Qudits → ZMod d

namespace PauliGroup

variable {Qudits : Type*} [Fintype Qudits] [DecidableEq Qudits] {d : ℕ}

public instance : Mul (PauliGroup Qudits d) where
  mul g h := ⟨g.phase + h.phase + pairing h.shift g.clock, g.shift + h.shift, g.clock + h.clock⟩

public instance : One (PauliGroup Qudits d) := ⟨⟨0, 0, 0⟩⟩

public instance : Inv (PauliGroup Qudits d) where
  inv g := ⟨pairing g.shift g.clock - g.phase, -g.shift, -g.clock⟩

omit [DecidableEq Qudits] in
@[simp] public lemma mul_phase (g h : PauliGroup Qudits d) :
    (g * h).phase = g.phase + h.phase + pairing h.shift g.clock := rfl

omit [DecidableEq Qudits] in
@[simp] public lemma mul_shift (g h : PauliGroup Qudits d) : (g * h).shift = g.shift + h.shift :=
  rfl

omit [DecidableEq Qudits] in
@[simp] public lemma mul_clock (g h : PauliGroup Qudits d) : (g * h).clock = g.clock + h.clock :=
  rfl

omit [Fintype Qudits] [DecidableEq Qudits] in
@[simp] public lemma one_phase : (1 : PauliGroup Qudits d).phase = 0 := rfl
omit [Fintype Qudits] [DecidableEq Qudits] in
@[simp] public lemma one_shift : (1 : PauliGroup Qudits d).shift = 0 := rfl
omit [Fintype Qudits] [DecidableEq Qudits] in
@[simp] public lemma one_clock : (1 : PauliGroup Qudits d).clock = 0 := rfl

omit [DecidableEq Qudits] in
@[simp] public lemma inv_phase (g : PauliGroup Qudits d) :
    g⁻¹.phase = pairing g.shift g.clock - g.phase := rfl
omit [DecidableEq Qudits] in
@[simp] public lemma inv_shift (g : PauliGroup Qudits d) : g⁻¹.shift = -g.shift := rfl
omit [DecidableEq Qudits] in
@[simp] public lemma inv_clock (g : PauliGroup Qudits d) : g⁻¹.clock = -g.clock := rfl

/-- `PauliGroup Qudits d` really is a group: multiplication is the Weyl cocycle extension of
`(Qudits → ZMod d) × (Qudits → ZMod d)` by the phase group `ZMod d`, which is associative
because the cocycle `⟨a', b⟩` is bilinear, and every element `⟨c, a, b⟩` has inverse
`⟨⟨a,b⟩ - c, -a, -b⟩`. -/
public instance : Group (PauliGroup Qudits d) where
  mul_assoc g1 g2 g3 := by
    ext
    · simp only [mul_phase, mul_shift, mul_clock, pairing_add_left, pairing_add_right]
      ring
    · simp only [mul_shift, Pi.add_apply]; ring
    · simp only [mul_clock, Pi.add_apply]; ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    ext
    · simp only [mul_phase, inv_phase, inv_clock, one_phase, pairing_neg_right]
      ring
    · simp only [mul_shift, inv_shift, one_shift, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring
    · simp only [mul_clock, inv_clock, one_clock, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring

/-- A pure phase element `ω^c`, with trivial shift and clock exponents. These are exactly the
central elements of `PauliGroup Qudits d`, see `phaseGen_commute`. -/
public def phaseGen (c : ZMod d) : PauliGroup Qudits d := ⟨c, 0, 0⟩

/-- The shift ("X") generator acting on qudit `i`. -/
public def shiftGen (i : Qudits) : PauliGroup Qudits d := ⟨0, fun j => if i = j then 1 else 0, 0⟩

/-- The clock ("Z") generator acting on qudit `i`. -/
public def clockGen (i : Qudits) : PauliGroup Qudits d := ⟨0, 0, fun j => if i = j then 1 else 0⟩

omit [DecidableEq Qudits] in
/-- Pure phase elements are central: they commute with every element of `PauliGroup Qudits d`. -/
public lemma phaseGen_commute (c : ZMod d) (g : PauliGroup Qudits d) :
    Commute (phaseGen c) g := by
  show phaseGen c * g = g * phaseGen c
  ext
  · simp [phaseGen, add_comm]
  · simp [phaseGen]
  · simp [phaseGen]

/-- The underlying symplectic vector of a Pauli element: its shift and clock exponents,
forgetting the phase. This is the quotient map onto `(Qudits → ZMod d) × (Qudits → ZMod d)` by
the central subgroup of pure phases. -/
public def vec (g : PauliGroup Qudits d) : (Qudits → ZMod d) × (Qudits → ZMod d) :=
  (g.shift, g.clock)

omit [DecidableEq Qudits] in
@[simp] public lemma vec_mul (g h : PauliGroup Qudits d) : vec (g * h) = vec g + vec h := by
  ext <;> simp [vec]

omit [Fintype Qudits] [DecidableEq Qudits] in
@[simp] public lemma vec_one : vec (1 : PauliGroup Qudits d) = 0 := by
  ext <;> simp [vec]

/-- The symplectic form on `(Qudits → ZMod d) × (Qudits → ZMod d)`, the vector space of
symplectic vectors underlying `PauliGroup Qudits d`:
`Ω((a,b),(a',b')) = ⟨a,b'⟩ - ⟨a',b⟩`. -/
public def symplecticForm (v w : (Qudits → ZMod d) × (Qudits → ZMod d)) : ZMod d :=
  pairing v.1 w.2 - pairing w.1 v.2

omit [DecidableEq Qudits] in
/-- Two Pauli elements commute up to exactly the phase given by the symplectic form applied to
their underlying symplectic vectors: `⁅g, h⁆` is always a pure phase, and that phase is
`Ω(vec h, vec g)`. This is the key fact making the symplectic form the "classical shadow" of
non-commutativity in the Pauli group, which is what stabilizer codes are built from. -/
public lemma commutatorElement_eq (g h : PauliGroup Qudits d) :
    ⁅g, h⁆ = phaseGen (symplecticForm (vec h) (vec g)) := by
  rw [commutatorElement_def]
  ext
  · simp only [mul_phase, mul_clock, inv_phase, inv_shift, inv_clock, phaseGen,
      symplecticForm, vec, pairing_neg_left, pairing_neg_right, pairing_add_right]
    ring
  · simp only [mul_shift, inv_shift, phaseGen, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring
  · simp only [mul_clock, inv_clock, phaseGen, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring

end PauliGroup
