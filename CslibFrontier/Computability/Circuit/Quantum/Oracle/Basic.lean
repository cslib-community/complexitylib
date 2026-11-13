/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Basic
public import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Logic.Equiv.Fin.Basic
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Coherent XOR queries as placed circuit gates

`xorQuery H A` queries a fixed function `H` coherently on the wires `A`: the first `a` wires
hold its argument, the following `b` wires hold its XOR accumulator, and all other wires are
untouched. `xorQuery_eval_apply` describes its action on every amplitude. No measurement or
resampling occurs during a query. `Oracle/ValueQuery` connects it to the value-query model.

This is an operational building block, not an efficiency certificate or a random-oracle
security theorem. In particular, the implementation cost of `H` is not charged here: an oracle
circuit must count this gate as an oracle call separately from its elementary gates.
The constructions and elementary identities below are original formalization infrastructure.
The query convention is the one in [Boneh et al.][BonehEtAl2012], §2.1, p. 7; injective wire
placement also permits other register layouts. Their efficiency and random-oracle assumptions
are separate from the gate action formalized here.

## Main definitions

* `Cslib.Quantum.queryRegisters`: split a register into query, response and unused wires.
* `Cslib.Quantum.xorQuery`: the placed coherent XOR-query gate.

## Main results

* `Cslib.Quantum.xorQuery_eval_ket`: the action on computational-basis states.
* `Cslib.Quantum.xorQuery_eval_apply`: the action on arbitrary amplitudes.
* `Cslib.Quantum.xorQuery_eval_twice`: two queries cancel, including on superpositions.

## References

* [Boneh et al., *Random Oracles in a Quantum World*][BonehEtAl2012],
  arXiv:1008.0931v2, §2.1, p. 7.
-/

public section

namespace Cslib.Quantum

variable {a b m : ℕ}

/-- Split the register along `A`: its first `a` wires are the query, its next `b` wires are the
response, and the remaining register retains its original wire indices. -/
noncomputable def queryRegisters (A : Fin (a + b) ↪ Fin m) :
    (Fin m → Bool) ≃
      (Fin a → Bool) × (Fin b → Bool) × ({j // ¬∃ i, A i = j} → Bool) :=
  (splitEquiv A).trans
    ((Equiv.prodCongr (Fin.appendEquiv a b).symm (Equiv.refl _)).trans
      (Equiv.prodAssoc _ _ _))

/-- Splitting a basis string reads the selected query and response wires and retains the unused
wire indices for the workspace. -/
@[simp] theorem queryRegisters_apply (A : Fin (a + b) ↪ Fin m) (z : Fin m → Bool) :
    queryRegisters A z =
      (fun i => z (A (Fin.castAdd b i)), fun i => z (A (Fin.natAdd a i)), fun j => z j.1) := by
  unfold queryRegisters
  rfl

/-- Reassembling the registers recovers a query bit at its selected wire. -/
@[simp] theorem queryRegisters_symm_query (A : Fin (a + b) ↪ Fin m)
    (x : Fin a → Bool) (y : Fin b → Bool) (w : {j // ¬∃ i, A i = j} → Bool) (i : Fin a) :
    (queryRegisters A).symm (x, y, w) (A (Fin.castAdd b i)) = x i := by
  change (splitEquiv A).symm ((Fin.appendEquiv a b) (x, y), w) (A (Fin.castAdd b i)) = _
  rw [splitEquiv_symm_apply_wire]
  exact Fin.append_left _ _ _

/-- Reassembling the registers recovers a response bit at its selected wire. -/
@[simp] theorem queryRegisters_symm_response (A : Fin (a + b) ↪ Fin m)
    (x : Fin a → Bool) (y : Fin b → Bool) (w : {j // ¬∃ i, A i = j} → Bool) (i : Fin b) :
    (queryRegisters A).symm (x, y, w) (A (Fin.natAdd a i)) = y i := by
  change (splitEquiv A).symm ((Fin.appendEquiv a b) (x, y), w) (A (Fin.natAdd a i)) = _
  rw [splitEquiv_symm_apply_wire]
  exact Fin.append_right _ _ _

/-- Reassembling the registers recovers every unused workspace bit. -/
theorem queryRegisters_symm_workspace (A : Fin (a + b) ↪ Fin m)
    (x : Fin a → Bool) (y : Fin b → Bool) (w : {j // ¬∃ i, A i = j} → Bool)
    (j : Fin m) (hj : ¬∃ i, A i = j) : (queryRegisters A).symm (x, y, w) j = w ⟨j, hj⟩ :=
  splitEquiv_symm_apply_of_not A _ _ j hj

private def xorPerm (H : (Fin a → Bool) → Fin b → Bool) :
    Equiv.Perm (Fin (a + b) → Bool) :=
  (Fin.appendEquiv a b).symm.trans
    ((Equiv.prodCongrRight fun x => Equiv.addRight (H x)).trans (Fin.appendEquiv a b))

/-- A coherent function query on the chosen wires: `|x, y, w⟩ ↦ |x, y + H x, w⟩`.
The addition on bit strings is XOR. -/
noncomputable def xorQuery (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) : PlacedGate m :=
  ⟨a + b, Gate.ofPerm (xorPerm H), A⟩

/-- A query preserves the argument and unused wires, and XORs the answer into the response. -/
theorem xorQuery_eval_ket (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) (x : Fin a → Bool) (y : Fin b → Bool)
    (w : {j // ¬∃ i, A i = j} → Bool) :
    (xorQuery H A).eval (ket ((queryRegisters A).symm (x, y, w))) =
      ket ((queryRegisters A).symm (x, y + H x, w)) := by
  unfold xorQuery
  rw [PlacedGate.eval_ofPerm_ket]
  congr 1
  simp [queryRegisters, xorPerm, ← splitEquiv_apply_fst]

private noncomputable def queryPerm (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) : Equiv.Perm (Fin m → Bool) :=
  (queryRegisters A).trans
    ((Equiv.prodCongrRight fun x =>
      Equiv.prodCongr (Equiv.addRight (H x)) (Equiv.refl _)).trans (queryRegisters A).symm)

private theorem queryPerm_involutive (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) : Function.Involutive (queryPerm H A) := by
  intro z
  obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters A).symm.surjective z
  apply (queryRegisters A).injective
  simp [queryPerm, Equiv.prodCongr, Equiv.addRight]

/-- The query acts by permuting amplitudes, without observing or discarding a query register. -/
theorem xorQuery_eval_apply (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) (ψ : Qubits m) (x : Fin a → Bool) (y : Fin b → Bool)
    (w : {j // ¬∃ i, A i = j} → Bool) :
    ((xorQuery H A).eval ψ).ofLp ((queryRegisters A).symm (x, y, w)) =
      ψ.ofLp ((queryRegisters A).symm (x, y + H x, w)) := by
  have hket : ∀ z, (xorQuery H A).eval (ket z) = ket (queryPerm H A z) := by
    intro z
    obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters A).symm.surjective z
    simpa only [queryPerm, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.prodCongrRight_apply, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.coe_addRight, Equiv.refl_apply] using
      xorQuery_eval_ket H A x y w
  simpa only [queryPerm, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongrRight_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.coe_addRight, Equiv.refl_apply] using
    (xorQuery H A).eval_apply_of_involutive (queryPerm_involutive H A) hket ψ
      ((queryRegisters A).symm (x, y, w))

/-- Two calls to the same XOR oracle cancel on every state. -/
theorem xorQuery_eval_twice (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) (ψ : Qubits m) :
    (xorQuery H A).eval ((xorQuery H A).eval ψ) = ψ := by
  ext z
  obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters A).symm.surjective z
  simp [xorQuery_eval_apply]

end Cslib.Quantum
