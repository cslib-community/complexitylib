/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.PP.Time
import Complexity.Computability.Probabilistic.PPT.Clock
import Complexity.Tactic.PPT

/-! Unbounded-error probabilistic time: members obtained from `P` through `BPP`, `PP` and
`BPTIME`, and a halting fair-coin machine that outputs `[true]` with probability exactly `1 / 2`,
which decides `∅` by strict majority but not `Set.univ`. -/

namespace ComplexityTests.PPTime

open Cslib Cslib.Complexity Cslib.Probability Turing Turing.MultiTapeTM
open scoped ENNReal

/-- Everything is decided by the constant `true`. -/
theorem univ_mem_P : (Set.univ : Set (List Bool)) ∈ P encBits :=
  ⟨fun _ => true, .const true, fun _ => by simp⟩

/-- The words starting with `true`: neither empty nor everything. -/
theorem headD_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- `Set.univ` and the words starting with `true` are decided by strict majority in polynomial
time, through `PP`, and for the latter also through `BPTIME`. -/
example :
    (∃ k, (Set.univ : Set (List Bool)) ∈ PPTIME encBits (· ^ k)) ∧
    (∃ k, {w : List Bool | w.headD false = true} ∈ PPTIME encBits (· ^ k)) ∧
    (∃ k, {w : List Bool | w.headD false = true} ∈ PPTIME encBits (· ^ k)) :=
  ⟨mem_PP_iff_exists_mem_PPTIME.mp (BPP_subset_PP (P_subset_BPP univ_mem_P)),
    mem_PP_iff_exists_mem_PPTIME.mp (BPP_subset_PP (P_subset_BPP headD_mem_P)),
    let ⟨k, hk⟩ := mem_BPP_iff_exists_mem_BPTIME.mp (P_subset_BPP headD_mem_P)
    ⟨k, BPTIME_subset_PPTIME hk⟩⟩

/-- A membership in `PPTIME (n ^ k)` gives back `PP`. -/
example {A : Set (List Bool)} {k : ℕ} (h : A ∈ PPTIME encBits (· ^ k)) : A ∈ PP encBits :=
  mem_PP_iff_exists_mem_PPTIME.mpr ⟨k, h⟩

/-- **Strictness matters.** A halting fair-coin machine that outputs `[true]` with probability
exactly `1 / 2` decides `∅` by strict majority, and does not decide `Set.univ`. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State)
    (t : List Bool → ℕ), machine.DecidesByMajorityInTime encBits ∅ t ∧
      ¬ machine.DecidesByMajorityInTime encBits Set.univ t := by
  have hcoin : IsPPTOn encBits encBool (fun _ => ProbComp.uniform Bool) := by fun_prop
  obtain ⟨k, State, hfinite, machine, c, d, heval, hhalt⟩ := hcoin.exists_halting_machine
  have hhalf (w : List Bool) :
      ProbComp.eval (machine.runClosed (c * ((encBits w).length + 1) ^ d) (encBits w)) [true] =
        1 / 2 := by
    rw [← heval w]
    simp [PMF.map_apply, encBool_apply]
  refine ⟨k, State, hfinite, machine, fun w => c * ((encBits w).length + 1) ^ d,
    fun w => ⟨hhalt w, ?_⟩, fun h => ?_⟩
  · rw [hhalf]
    simp
  · have := ((h []).2.mp (Set.mem_univ _))
    rw [hhalf] at this
    exact lt_irrefl _ this

/-- The count form of the majority condition: a machine deciding `Set.univ` by strict majority
accepts more than half of the coin strings of clock length on every word. -/
example {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State) {t : List Bool → ℕ}
    (h : machine.DecidesByMajorityInTime encBits Set.univ t) (w : List Bool) :
    2 ^ t w < 2 * acceptCount
      (fun x : List Bool × List Bool => decide (machine.runClosedCoins x.2 x.1 = [true])) w (t w) :=
  ((MultiTapePTM.decidesByMajorityInTime_iff.mp h) w).2.mp (Set.mem_univ w)

end ComplexityTests.PPTime
