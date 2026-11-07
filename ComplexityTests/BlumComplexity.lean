/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.BlumComplexity.Fuel
import Complexity.Computability.BlumComplexity.Gap
import Complexity.Computability.BlumComplexity.RecursiveRelatedness

/-!
# Blum complexity measure clients

The fuel of the constant-zero program is computed exactly. For the fuel measure, the class of the
bound `id` is empty, while the bound `n + 1` admits the constant-zero function. The class
convention is almost everywhere: a bound that fails at finitely many inputs still admits a
function. The gap theorem is instantiated with `g n = n * n` and a lower bound, and the resulting
gap class is inhabited. Recursive relatedness is instantiated for the fuel measure against itself.
-/

namespace ComplexityTests.BlumComplexity

open Cslib.BlumComplexity Cslib.BlumComplexity.BlumMeasure Nat.Partrec Filter

/-- The constant-zero program needs fuel exactly `n + 1` on input `n`. -/
theorem evalnFuel_zero (n : ℕ) : evalnFuel Code.zero n = Part.some (n + 1) := by
  rw [Part.eq_some_iff, mem_evalnFuel_iff]
  refine ⟨by simp [Code.evaln], fun j hj => ?_⟩
  cases j with
  | zero => simp [Code.evaln]
  | succ j =>
    have hnj : ¬ n ≤ j := by omega
    simp [Code.evaln, hnj]

example : evalnFuel Code.zero 4 = Part.some 5 :=
  evalnFuel_zero 4

private theorem mem_eval_zero (n : ℕ) : 0 ∈ Code.zero.eval n := by
  rw [Code.eval]
  exact Part.mem_some 0

/-- The bound `id` is below the fuel at every input, so its class is empty. -/
example : fuelMeasure.complexityClass id = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun f hf => ?_
  obtain ⟨c, hc, hev⟩ := mem_complexityClass.1 hf
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨k, hk⟩ :=
    Part.dom_iff_mem.1 ((dom_evalnFuel_iff c n).2 (Part.dom_iff_mem.2 ⟨_, hc n⟩))
  exact absurd (hn k hk) (not_le.2 (lt_of_mem_evalnFuel hk))

/-- The constant-zero function lies in the class of the bound `n + 1`. -/
example : (fun _ => 0) ∈ fuelMeasure.complexityClass (· + 1) := by
  refine mem_complexityClass.2 ⟨Code.zero, mem_eval_zero, Eventually.of_forall fun n m hm => ?_⟩
  rw [fuelMeasure_cost, evalnFuel_zero, Part.mem_some_iff] at hm
  exact hm.le

/-- Almost-everywhere convention: the bound `if n < 10 then 0 else n + 1` fails at the first ten
inputs for every program, yet its class still contains the constant-zero function. -/
example : (fun _ => 0) ∈ fuelMeasure.complexityClass (fun n => if n < 10 then 0 else n + 1) := by
  refine mem_complexityClass.2 ⟨Code.zero, mem_eval_zero, ?_⟩
  filter_upwards [eventually_ge_atTop 10] with n hn m hm
  rw [fuelMeasure_cost, evalnFuel_zero, Part.mem_some_iff] at hm
  have hn' : ¬ n < 10 := by omega
  simp only [hn', ↓reduceIte]
  exact hm.le

/-- The gap theorem for `g n = n * n` and the lower bound `a n = n + 1`: there is a computable
strictly increasing `t ≥ a` such that `C_{t * t} = C_t` for the fuel measure, and this class
contains the constant-zero function. -/
example : ∃ t : ℕ → ℕ, Computable t ∧ StrictMono t ∧
    fuelMeasure.complexityClass (fun n => t n * t n) = fuelMeasure.complexityClass t ∧
    (fun _ => 0) ∈ fuelMeasure.complexityClass t := by
  obtain ⟨t, ht, hmono, hat, hgap⟩ := fuelMeasure.gap_theorem (g := fun n => n * n)
    (Primrec.nat_mul.comp Primrec.id Primrec.id).to_comp Nat.le_mul_self Computable.succ
  refine ⟨t, ht, hmono, hgap, mem_complexityClass.2 ⟨Code.zero, mem_eval_zero,
    Eventually.of_forall fun n m hm => ?_⟩⟩
  rw [fuelMeasure_cost, evalnFuel_zero, Part.mem_some_iff] at hm
  exact hm.trans_le (hat n)

/-- The explicit form of the gap: past the code index, no fuel lies in `(t n, t n * t n]`. -/
example : ∃ t : ℕ → ℕ, Computable t ∧
    ∀ c : Code, ∀ n, Encodable.encode c ≤ n →
      ∀ m ∈ evalnFuel c n, m ≤ t n ∨ t n * t n < m := by
  obtain ⟨t, ht, -, -, hgap⟩ := fuelMeasure.exists_gap (g := fun n => n * n)
    (Primrec.nat_mul.comp Primrec.id Primrec.id).to_comp (Computable.const 0)
  exact ⟨t, ht, hgap⟩

/-- Recursive relatedness, instantiated for the fuel measure against itself. -/
example : ∃ r : ℕ → ℕ → ℕ, Computable₂ r ∧
    ∀ᶠ n in atTop, ∀ m ∈ evalnFuel Code.zero n, m ≤ r n m := by
  obtain ⟨r, hr, hrel⟩ := recursively_related fuelMeasure fuelMeasure
  exact ⟨r, hr, (hrel Code.zero).mono fun n hn m hm => (hn m hm m hm).1⟩

end ComplexityTests.BlumComplexity
