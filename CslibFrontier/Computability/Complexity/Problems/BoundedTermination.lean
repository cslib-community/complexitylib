/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.BoundedHalting
import CslibFrontier.Computability.Complexity.Classes.EXP.Decidable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partialize
import CslibFrontier.Foundations.Data.BitString.List.Binary.Clock
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Any-output bounded termination with a binary clock

Every word is interpreted as a framed description, framed input and most-significant-bit-first
binary clock via `BoundedComputation`. The language accepts any computation halted within that
clock, regardless of its output. On canonical native-machine triples this is exactly native
halting by the given step bound. Total decoders also fix the meaning of noncanonical words.

The language is in `E` and is EXP-complete under polynomial-time many-one reductions, hence is
outside `P`. These are [Goldreich2007DraftR2], Exercises 4.6–4.7, in the chosen representation.
The existing `BoundedHalting` language instead requires the specific output `[true]`. Its
completeness is reused through one fixed complement decider and exact-step partialization.
No sharp universal-simulator lower bound or encoding-independent `E` invariance is asserted.

## Main definitions

* `Cslib.Complexity.BoundedTermination`: any-output bounded halting on bit words.

## Main results

* `Cslib.Complexity.BoundedTermination.mk_desc_mem_iff`: exact native-machine halting semantics.
* `Cslib.Complexity.BoundedTermination.mem_E`: membership in linear exponential time.
* `Cslib.Complexity.BoundedTermination.polyTimeComplete_EXP`: exponential-time completeness.
* `Cslib.Complexity.BoundedTermination.notMem_P`: separation from polynomial time.

## References

* [Goldreich2007DraftR2], Exercises 4.6–4.7, printed page 152 / PDF page 36; the bounded
  universal function is defined on printed page 144 / PDF page 28, with the clock in binary.
-/

public section

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.BitString

namespace Cslib.Complexity

open BoundedComputation

/-- The decoded machine halts within the binary step bound, with any output word allowed. -/
noncomputable def BoundedTermination : Set (List Bool) := {w | (run w).2 = true}

namespace BoundedTermination

/-- Membership tests only the halted flag of the shared bounded computation. -/
theorem mem_iff {w : List Bool} : w ∈ BoundedTermination ↔ (run w).2 = true := Iff.rfl

/-- Total decoding gives every word the same termination behavior as its canonical re-encoding. -/
theorem mem_reencode_iff (w : List Bool) :
    mk (descOf w) (inputOf w) (clockOf w) ∈ BoundedTermination ↔ w ∈ BoundedTermination := by
  rw [mem_iff, mem_iff, run_reencode]

/-- Canonical triples use exactly the supplied description, input and binary clock. -/
theorem mk_mem_iff {d : Desc} {x c : List Bool} :
    mk d x c ∈ BoundedTermination ↔ (universal (d, x.map eBit, binaryValue c)).2 = true := by
  rw [mem_iff, run_mk]

/-- A canonical instance halts exactly when the native finite machine has halted at the
specified step bound. Its output may be empty, false, true, or a longer word. -/
theorem mk_desc_mem_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x c : List Bool) :
    mk (desc eS eBit tm) x c ∈ BoundedTermination ↔
      (tm.runFrom (tm.initCfg x) (binaryValue c)).Halted := by
  rw [mk_mem_iff, universal_desc, Cfg.Halted, Option.isNone_iff_eq_none]

/-- Any-output bounded termination is decidable in linear exponential time on all words. -/
theorem mem_E : BoundedTermination ∈ E encBits :=
  BoundedComputation.setOf_run_mem_E (p := Prod.snd) (by fun_prop)

/-- Any-output bounded termination is also in EXP. -/
theorem mem_EXP : BoundedTermination ∈ EXP encBits := E_subset_EXP mem_E

/-- Any-output bounded termination has a total native decider. -/
theorem isDecidable : IsDecidable BoundedTermination encBits := isDecidable_of_mem_E mem_E

/-- The existing accepting-output-`[true]` language reduces to the any-output halting language.
The reduction emits canonical framed triples, while its equivalence holds for every source
word interpreted by the documented total decoders. -/
theorem boundedHalting_polyTimeReducible :
    PolyTimeReducible encBits encBits BoundedHalting BoundedTermination := by
  obtain ⟨k, c₁, c₂, s, hdec⟩ :=
    mem_E_iff.mp (compl_mem_E BoundedHalting.mem_E)
  obtain ⟨g, ⟨kt, State, hfin, tm, htm⟩, hg⟩ :=
    decidableInTimeAndSpace_iff.mp hdec
  have := Fintype.ofFinite State
  let eS : (Option State × Option Bool) ↪ ℕ :=
    (Fintype.equivFin (Option State × Option Bool)).toEmbedding.trans Fin.valEmbedding
  let d : Desc := desc eS eBit tm.partialize
  refine ⟨fun w => mk d w (List.replicate (k * w.length + c₁ + c₂ + 1) true),
    ?_, fun w => ?_⟩
  · fun_prop
  · have hc : c₁ * 2 ^ (k * w.length) + c₂ ≤
        binaryValue (List.replicate (k * w.length + c₁ + c₂ + 1) true) :=
      le_binaryValue_replicate_true (k * w.length) c₁ c₂
    obtain ⟨hhalt, hout⟩ := (htm w).runFrom_of_le hc
    change _ = [g w] at hout
    simp only [encBits_apply] at hhalt hout
    -- The wrapper's halting test is exact at this SAME step count, with no simulation loss.
    -- True is the complement-decider's yes verdict, hence is precisely the looping branch.
    change w ∈ BoundedHalting ↔
      mk (desc eS eBit tm.partialize) w
        (List.replicate (k * w.length + c₁ + c₂ + 1) true) ∈ BoundedTermination
    rw [mk_desc_mem_iff, runFrom_partialize, Partialize.liftCfg_halted_iff]
    simpa only [Cfg.Halted, hhalt, hout, true_and, Partialize.verdict, List.head?_cons, ne_eq,
      Option.some.injEq,
      Set.mem_compl_iff, not_not] using not_congr (hg w)

/-- Every E problem reduces to bounded termination, by composing existing bounded-acceptance
hardness with the exact-verdict bridge. -/
theorem polyTimeHard_E : PolyTimeHard @E encBits BoundedTermination :=
  fun _ enc A hA => (BoundedHalting.polyTimeHard_E enc A hA).trans
    boundedHalting_polyTimeReducible

/-- Goldreich Exercise 4.7: every EXP problem Karp-reduces to bounded termination. -/
theorem polyTimeHard_EXP : PolyTimeHard @EXP encBits BoundedTermination :=
  fun _ enc A hA => (BoundedHalting.polyTimeHard_EXP enc A hA).trans
    boundedHalting_polyTimeReducible

/-- Any-output bounded termination is E-complete under polynomial-time many-one reductions. -/
theorem polyTimeComplete_E : PolyTimeComplete @E encBits BoundedTermination :=
  ⟨mem_E, polyTimeHard_E⟩

/-- Any-output bounded termination is EXP-complete under polynomial-time many-one reductions. -/
theorem polyTimeComplete_EXP : PolyTimeComplete @EXP encBits BoundedTermination :=
  ⟨E_subset_EXP mem_E, polyTimeHard_EXP⟩

/-- Goldreich Exercise 4.6's strict lower bound follows from the existing complete acceptance
problem: a P decider here would decide that problem in P as well. -/
theorem notMem_P : BoundedTermination ∉ P encBits := fun h =>
  BoundedHalting.notMem_P (boundedHalting_polyTimeReducible.mem_P h)

end BoundedTermination
end Cslib.Complexity
