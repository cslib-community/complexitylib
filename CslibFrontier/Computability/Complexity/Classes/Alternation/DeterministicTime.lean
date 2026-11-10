/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation
public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Complexity.Classes.Time.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DeterministicTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Alternating space within deterministic exponential time

An alternating machine within space `s` is simulated deterministically within time
`2 ^ O(log₂ n + s)` [Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: list the reachable views by breadth-first search until no new
view appears, then mark them bottom-up (`Turing.MultiTapeATM.reachableAccepts`). The simulation
holds for recognizers (`Turing.MultiTapeATM.RecognizesInSpace`), whose branches need not halt,
which is the space-bounded acceptance of Chandra, Kozen and Stockmeyer. Acceptance is the least
fixed point of the labelling, so an infinite branch never helps a view accept. The class
`Cslib.Complexity.ASPACE` uses the deciding form, in which every branch also halts, so the
inclusion holds for it a fortiori. The space bound need not be constructible: the search stops by
itself, and the bound enters only the analysis.

## Main results

* `Turing.MultiTapeATM.RecognizesInSpace.mem_DTIME`: a problem recognized within space `s` is in
  `DTIME (2 ^ (c * (log₂ n + s n + 1)))`.
* `Cslib.Complexity.exists_mem_DTIME_of_mem_ASPACE`: `ASPACE s ⊆ DTIME (2 ^ O(log₂ n + s n))`.
* `Cslib.Complexity.exists_mem_DTIME_of_mem_ASPACE_of_log2_le`: `ASPACE s ⊆ DTIME (2 ^ O(s n))`
  when `log₂ n ≤ s n`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*,
  Section 3][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 10.3][Sipser2013]
-/

public section

namespace Turing.MultiTapeATM

open MultiTapeTM Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {State : Type} [Finite State]
  {atm : MultiTapeATM k Bool State} {A : Set α}

/-- **Space-bounded alternating recognizers are within exponential time**
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]: a problem recognized by an
alternating machine within space `s n`, whose branches need not halt, is decided deterministically
within time `2 ^ (c * (log₂ n + s n + 1))` for a constant `c` of the machine. The space bound need
not be constructible. -/
theorem RecognizesInSpace.mem_DTIME {s : ℕ → ℕ}
    (h : atm.RecognizesInSpace enc A fun a => s (enc a).length) :
    ∃ c, A ∈ DTIME enc fun n => 2 ^ (c * (Nat.log2 n + s n + 1)) := by
  obtain ⟨c, hc⟩ := exists_computableInTimeAndSpace_reachableAccepts fun a => (h a).1
  exact ⟨c, 1, 0, fun n => 2 ^ (c * (Nat.log2 n + s n + 1)), decidableInTimeAndSpace_iff.mpr
    ⟨_, hc.mono (fun _ => by simp) fun _ => le_rfl,
      fun a => (h a).2.trans (reachableAccepts_iff (h a).1).symm⟩⟩

end Turing.MultiTapeATM

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool}

/-- **Alternating space is within deterministic exponential time**
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: `ASPACE s ⊆ DTIME (2 ^ O(log₂ n + s n))`. The space bound need
not be constructible. -/
theorem exists_mem_DTIME_of_mem_ASPACE {s : ℕ → ℕ} {A : Set α} (h : A ∈ ASPACE enc s) :
    ∃ c, A ∈ DTIME enc fun n => 2 ^ (c * (Nat.log2 n + s n + 1)) := by
  obtain ⟨k, State, _, atm, c₁, c₂, hA⟩ := h
  obtain ⟨c, hc⟩ := hA.recognizesInSpace.mem_DTIME (s := fun n => c₁ * s n + c₂)
  exact ⟨_, DTIME_two_pow_log2_add_mul_add_subset c c₁ c₂ s hc⟩

/-- **Alternating space is within deterministic exponential time** above logarithmic space
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: `ASPACE s ⊆ DTIME (2 ^ O(s n))` when `log₂ n ≤ s n`. -/
theorem exists_mem_DTIME_of_mem_ASPACE_of_log2_le {s : ℕ → ℕ} {A : Set α}
    (hs : ∀ n, Nat.log2 n ≤ s n) (h : A ∈ ASPACE enc s) :
    ∃ c, A ∈ DTIME enc fun n => 2 ^ (c * s n) := by
  obtain ⟨c, hc⟩ := exists_mem_DTIME_of_mem_ASPACE h
  exact ⟨_, DTIME_two_pow_log2_add_subset hs hc⟩

end Cslib.Complexity
