/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Card

/-!
# Counting accepted and satisfying inputs of Boolean circuits

Defines exact acceptance and satisfying-input counts (`Circuit.acceptCount`, `Circuit.satCount`)
for circuits interpreted over `Bool` under an arbitrary signature `σ`.

## Main definitions

* `Cslib.Circuits.Circuit.acceptCount`: number of inputs `x : Fin n → Bool` on which every output
  `o` satisfies `acc o`.
* `Cslib.Circuits.Circuit.satCount`: number of satisfying inputs `x : Fin n → Bool` of a
  single-output Boolean circuit (`c.eval I x 0 = true`).

## Main results

* `Cslib.Circuits.Circuit.satCount_eq_acceptCount`: `satCount` is `acceptCount` accepting `true`
  at output `0`.
* `Cslib.Circuits.Circuit.acceptCount_eq_ncard`: `acceptCount` agrees with `Set.ncard` of the
  accepted input set.
* `Cslib.Circuits.Circuit.satCount_pos_iff`: `satCount` is positive if and only if the circuit has
  a satisfying input.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Circuit

universe v

variable {σ : Signature.{v}}

/-- Number of inputs `x : Fin n → Bool` on which every output `o` satisfies `acc o`. -/
def acceptCount {n m : ℕ} (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Bool => ∀ o : Fin m, acc o (c.eval I x o) = true).card

/-- Number of satisfying inputs `x : Fin n → Bool` of a single-output Boolean circuit
(`c.eval I x 0 = true`). -/
def satCount {n : ℕ} (c : Circuit σ n 1) (I : Interpretation σ Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Bool => c.eval I x 0 = true).card

/-- Single-output `satCount` is `acceptCount` accepting `true` at output `0`. -/
theorem satCount_eq_acceptCount {n : ℕ} (c : Circuit σ n 1) (I : Interpretation σ Bool) :
    c.satCount I = c.acceptCount I (fun _ b => b) := by
  simp only [satCount, acceptCount]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h o => Subsingleton.elim (0 : Fin 1) o ▸ h, fun h => h 0⟩

/-- `acceptCount` agrees with `Set.ncard` of the accepted input set. -/
theorem acceptCount_eq_ncard {n m : ℕ} (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) :
    c.acceptCount I acc = {x : Fin n → Bool | ∀ o, acc o (c.eval I x o) = true}.ncard := by
  have heq : {x : Fin n → Bool | ∀ o, acc o (c.eval I x o) = true} =
      ↑(Finset.univ.filter fun x : Fin n → Bool =>
        ∀ o : Fin m, acc o (c.eval I x o) = true) := by
    ext x
    simp
  rw [heq, Set.ncard_coe_finset]
  rfl

/-- `satCount` is positive iff the circuit has a satisfying input. -/
theorem satCount_pos_iff {n : ℕ} (c : Circuit σ n 1) (I : Interpretation σ Bool) :
    0 < c.satCount I ↔ ∃ x : Fin n → Bool, c.eval I x 0 = true := by
  simp [satCount, Finset.card_pos, Finset.filter_nonempty_iff]

end Cslib.Circuits.Circuit
