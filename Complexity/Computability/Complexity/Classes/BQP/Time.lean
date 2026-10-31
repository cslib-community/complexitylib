/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# Bounded-error quantum time

`BQTIME enc t` (`Cslib.Complexity.BQTIME`) is the class of problems decided with bounded error by
the polynomial-time uniform families of quantum circuits of `Cslib.Complexity.BQP` whose circuits
for inputs of length `n` have at most `c₁ t n + c₂` gates, for constants `c₁` and `c₂`. The gate
count plays the role of running time.

The families are polynomial-time uniform, so every circuit has polynomially many gates anyway, and
`BQTIME enc t` is only meaningful for polynomially bounded `t`: it always lies in `BQP`
(`Cslib.Complexity.BQTIME_subset_BQP`), and the gate bound no longer constrains the family once `t`
dominates every polynomial. `BQP` is the union of the classes `BQTIME[n ^ k]`
(`Cslib.Complexity.BQP_eq_iUnion_BQTIME`).

## Main definitions

* `Cslib.Complexity.BQTIME`.

## Main results

* `Cslib.Complexity.BQTIME_subset_BQP`: every `BQTIME` class lies in `BQP`.
* `Cslib.Complexity.BQP_eq_iUnion_BQTIME`: `BQP = ⋃ k, BQTIME[n ^ k]`.
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type}

/-- **Bounded-error quantum time** `t`: the problems decided with bounded error, with respect to
the encoding `enc` of instances, by a polynomial-time uniform family of quantum circuits over the
Hadamard, NOT, CNOT and Toffoli gates (`Cslib.Quantum.UniformCircuitFamily`) whose circuit for
inputs of length `n` has at most `c₁ t n + c₂` gates. Members are accepted with probability at
least `2 / 3` and other instances with probability at most `1 / 3`.

Since the families are polynomial-time uniform, their circuits have polynomially many gates in any
case, so the class is only meaningful for polynomially bounded `t`. -/
def BQTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (F : UniformCircuitFamily) (c₁ c₂ : ℕ), (∀ n, (F.gates n).length ≤ c₁ * t n + c₂) ∧
    ∀ a, (a ∈ A → 2 / 3 ≤ F.acceptProb (enc a)) ∧ (a ∉ A → F.acceptProb (enc a) ≤ 1 / 3)}

variable {enc : α ↪ List Bool}

/-- Every `BQTIME` class lies in `BQP`. -/
theorem BQTIME_subset_BQP (t : ℕ → ℕ) : BQTIME enc t ⊆ BQP enc :=
  fun _ ⟨F, _, _, _, hF⟩ => ⟨F, hF⟩

private theorem length_le_length_encList {β : Type} (e : β ↪ List Bool) (l : List β) :
    l.length ≤ (encList e l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

/-- **`BQP` is the union of the polynomial quantum time classes** `BQTIME[n ^ k]`: the circuits of
a polynomial-time uniform family have polynomially many gates. -/
theorem BQP_eq_iUnion_BQTIME : BQP enc = ⋃ k : ℕ, BQTIME enc fun n => n ^ k := by
  refine Set.Subset.antisymm (fun A ⟨F, hF⟩ => ?_)
    (Set.iUnion_subset fun k => BQTIME_subset_BQP _)
  obtain ⟨c, d, hc⟩ := F.computableInPolyTime_gates.polyBounded_length.exists_le
  refine Set.mem_iUnion.mpr ⟨d, F, c * 2 ^ d, c, fun n => ?_, hF⟩
  have h1 := (length_le_length_encList encGateCode (F.gates n)).trans (hc n)
  rw [encUnary_apply, List.length_replicate] at h1
  have h2 : (n + 1) ^ d ≤ 2 ^ d * n ^ d + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · simp [Nat.zero_pow hd]
    · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
        _ = 2 ^ d * n ^ d := mul_pow 2 n d
        _ ≤ _ := Nat.le_succ _
  calc (F.gates n).length ≤ c * (n + 1) ^ d := h1
    _ ≤ c * (2 ^ d * n ^ d + 1) := Nat.mul_le_mul_left _ h2
    _ = c * 2 ^ d * n ^ d + c := by ring

end Cslib.Complexity
