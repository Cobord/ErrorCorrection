/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import QuantumErrorCorrection.Pauli
public import Mathlib.Algebra.Group.End

/-!
# The Clifford automorphism group

`CliffordAutGroup Qudits d` is the subgroup of `MulAut (PauliGroup Qudits d)` consisting of
automorphisms that fix every pure phase pointwise. Fixing phases means fixing each central
element `phaseGen c`; images of shift and clock generators may still acquire phase factors.

The name distinguishes these abstract automorphisms from the unitary Clifford normalizer.
For `d > 0`, choose a primitive phase character and a Weyl realization
`ρ : P → U(D)`, where `P = PauliGroup Qudits d` and `D = d ^ Fintype.card Qudits`.
Finite Stone–von Neumann uniqueness and Schur's lemma give the exact sequence

  `1 → U(1) → N_{U(D)}(ρ(P)) → CliffordAutGroup Qudits d → 1`.

Thus every Clifford automorphism has a unitary implementer, unique up to a scalar phase.
The abstract group records the conjugation action with this scalar ambiguity forgotten.

`toCliffordAut` sends a Pauli element to its inner automorphism. Its kernel consists of the
pure phases, which form `Z(P)`. Consequently `P / Z(P)` embeds as the subgroup of inner
automorphisms of `CliffordAutGroup`.

The quotient by inner automorphisms depends on the phase convention. For odd `d > 1`, it is
the symplectic group of the exponent module `(ZMod d)^(2n)`, with `n = Fintype.card Qudits`.
For `d = 2` and `n > 0`, the present phase group is only `{±1}`: the identity
`(X^a Z^b)^2 = (-1)^(a · b) I` forces automorphisms to preserve the quadratic form
`q(a,b) = a · b`. The quotient is then `O⁺(2n, 2)`. The usual full qubit symplectic quotient
uses the larger Pauli group with phases `{±1, ±i}`. In general even dimension one must
account for power relations as well as the commutator form.

The normalizer and quotient identifications above are mathematical context. This file
defines the abstract automorphism group and the map `toCliffordAut`; it does not formalize
those identifications.
-/

@[expose] public section

universe u

variable {Qudits : Type u} [Fintype Qudits] {d : ℕ}

namespace PauliGroup

/-- The Clifford automorphism group on qudits `Qudits` of dimension `d`: the subgroup of automorphisms of
`PauliGroup Qudits d` that fix every phase pointwise. -/
public def CliffordAutGroup (Qudits : Type u) [Fintype Qudits] (d : ℕ) :
    Subgroup (MulAut (PauliGroup Qudits d)) where
  carrier := {φ | ∀ c : ZMod d, φ (phaseGen c) = phaseGen c}
  one_mem' _ := rfl
  mul_mem' {φ ψ} hφ hψ c := by rw [MulAut.mul_apply, hψ c, hφ c]
  inv_mem' {φ} hφ c := by
    have h : φ (phaseGen c) = phaseGen c := hφ c
    calc φ⁻¹ (phaseGen c) = φ⁻¹ (φ (phaseGen c)) := by rw [h]
      _ = phaseGen c := MulAut.inv_apply_self _ φ (phaseGen c)

/-- Conjugation by a Pauli group element fixes every phase (`phaseGen_commute`), so defines
a Clifford automorphism. This map has the pure phases as its kernel and the inner
automorphisms as its image; it induces an embedding of the Pauli group modulo its center. -/
public def toCliffordAut (g : PauliGroup Qudits d) : CliffordAutGroup Qudits d :=
  ⟨MulAut.conj g, fun c => by
    have h : g * phaseGen c = phaseGen c * g := (phaseGen_commute c g).symm
    rw [MulAut.conj_apply, h, mul_assoc, mul_inv_cancel, mul_one]⟩

end PauliGroup
