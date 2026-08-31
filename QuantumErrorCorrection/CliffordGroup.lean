/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.Pauli
public import Mathlib.Algebra.Group.End

/-!
# The Clifford group

Physically, the Clifford group is the normalizer of the Pauli group inside the unitary group:
unitaries `U` such that conjugation `P ↦ U P U†` sends Pauli operators to Pauli operators
*without introducing an overall change of phase*. Since `PauliGroup` here is built as an
abstract group (no ambient unitary group), we take the analogous abstract characterization: the
Clifford group is the subgroup of `MulAut (PauliGroup Qudits d)` consisting of automorphisms
that fix every phase (central element) pointwise.

`PauliGroup` itself embeds into `CliffordGroup` via inner automorphisms (`toClifford`), since
phases are central (`phaseGen_commute`) and so are fixed by any conjugation. Physically this
recovers the standard picture: `CliffordGroup` modulo the inner automorphisms coming from
`PauliGroup` is the symplectic group acting on the shift/clock vector space.
-/

@[expose] public section

universe u

variable {Qudits : Type u} [Fintype Qudits] {d : ℕ}

namespace PauliGroup

/-- The Clifford group on qudits `Qudits` of dimension `d`: the subgroup of automorphisms of
`PauliGroup Qudits d` that fix every phase pointwise. -/
public def CliffordGroup (Qudits : Type u) [Fintype Qudits] (d : ℕ) :
    Subgroup (MulAut (PauliGroup Qudits d)) where
  carrier := {φ | ∀ c : ZMod d, φ (phaseGen c) = phaseGen c}
  one_mem' _ := rfl
  mul_mem' {φ ψ} hφ hψ c := by rw [MulAut.mul_apply, hψ c, hφ c]
  inv_mem' {φ} hφ c := by
    have h : φ (phaseGen c) = phaseGen c := hφ c
    calc φ⁻¹ (phaseGen c) = φ⁻¹ (φ (phaseGen c)) := by rw [h]
      _ = phaseGen c := MulAut.inv_apply_self _ φ (phaseGen c)

/-- Conjugation by a Pauli group element is always a Clifford automorphism: since phases are
central (`phaseGen_commute`), conjugation fixes them pointwise. This realizes `PauliGroup
Qudits d` as (a quotient map onto) the inner automorphisms inside `CliffordGroup Qudits d`. -/
public def toClifford (g : PauliGroup Qudits d) : CliffordGroup Qudits d :=
  ⟨MulAut.conj g, fun c => by
    have h : g * phaseGen c = phaseGen c * g := (phaseGen_commute c g).symm
    rw [MulAut.conj_apply, h, mul_assoc, mul_inv_cancel, mul_one]⟩

end PauliGroup
