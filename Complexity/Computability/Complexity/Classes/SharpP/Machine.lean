/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Checker

/-!
# Native machine terminal counts belong to #P

For each fixed finite-control list-choice machine and polynomial clock, both accepting and
rejecting terminal-branch counts belong to the verifier-defined `#P`. The binary verifiers are
the actual certified replay programs from `MultiTape.Counting.Checker`, with one fixed-width
code per occurrence index and uniquely forced terminal padding. Invalid codes count on neither
side. The result does not identify choices with equal actions or equal successor configurations.

The clock counts native transitions. Only branches halted by that clock are counted; the existing
`HaltsWithin` hypothesis additionally guarantees that every branch halts without getting stuck,
and makes both counts stable at larger clocks. No all-branch halting assumption is needed merely
to count bounded terminal branches. The machine, finite control, number of tapes and block width
are fixed before the input is supplied. `Classes.SharpP.Characterization` supplies the reverse
verifier construction and the bidirectional #P characterization. `Classes.SharpP.GapMachine`
supplies balanced signed routing and the bidirectional GapP characterization.

## Main results

* `Turing.MultiTapeCTM.Checker.acceptCount_checkBinary`: exact transfer of either terminal count
  to the corresponding fixed-length binary verifier count.
* `Turing.MultiTapeCTM.acceptCount_mem_SharpP`: polynomial-clock accepting counts belong to #P.
* `Turing.MultiTapeCTM.rejectCount_mem_SharpP`: polynomial-clock rejecting counts belong to #P.
* `Turing.MultiTapeCTM.gapCount_mem_GapP`: their integer difference belongs to GapP.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]

This is the forward counting-machine construction. The shared native machine, binary encoding,
finite-storage simulation and certified calculus retain their source credits in their modules.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib MultiTapeTM

variable {k : ℕ} {State α : Type}

/-- Every accepting binary word corresponds to exactly one canonical occurrence certificate,
for either requested terminal verdict. Invalid words contribute to neither count. -/
theorem Checker.acceptCount_checkBinary (machine : MultiTapeCTM k Bool State)
    {width : ℕ} (hwidth : 0 < width) (input : List Bool)
    (hbound : ∀ cfg : Cfg k Bool State input, (machine.actions cfg).length ≤ 2 ^ width)
    (count : ℕ) (verdict : Bool) :
    Complexity.acceptCount (Checker.checkBinary machine width verdict) input (count * width) =
      machine.branchCount (fun out => (out == [true]) == verdict) count
        (Cfg.init machine.initial input) := by
  unfold Complexity.acceptCount
  have heq (word : BitString (count * width)) :=
    Checker.checkBinary_eq_certificateAccepts machine hwidth verdict input
      (word := List.ofFn word) List.length_ofFn
  simp_rw [heq]
  exact machine.card_binaryCertificateAccepts _ hbound count _

private theorem verdictCount_mem_SharpP [Finite State]
    (machine : MultiTapeCTM k Bool State) (enc : α ↪ List Bool) (clock : Polynomial ℕ)
    (verdict : Bool) :
    (fun a => machine.branchCount (fun out => (out == [true]) == verdict)
      (clock.eval (enc a).length) (Cfg.init machine.initial (enc a))) ∈ Complexity.SharpP enc := by
  obtain ⟨bound, hbound⟩ := machine.exists_branchBound
  let width := bound + 1
  have hwidth : 0 < width := Nat.zero_lt_succ _
  have hcodes (input : List Bool) (cfg : Cfg k Bool State input) :
      (machine.actions cfg).length ≤ 2 ^ width :=
    (hbound input cfg).trans ((Nat.le_succ bound).trans
      (show width < 2 ^ width from Nat.lt_two_pow_self).le)
  refine ⟨clock * Polynomial.C width,
    fun p => Checker.checkBinary machine width verdict (enc p.1, p.2), ?_, ?_⟩
  · exact (Checker.computableInPolyTime_checkBinary machine width verdict).comp (by fun_prop)
  · intro a
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    exact (Checker.acceptCount_checkBinary machine hwidth (enc a) (hcodes (enc a))
      (clock.eval (enc a).length) verdict).symm

/-- For a fixed finite-control native list-choice machine, the number of accepting branches
halted by a polynomial clock is in #P. A complete all-branch computation additionally uses
`HaltsWithin`; neither stuck nor unfinished branches are counted. -/
theorem acceptCount_mem_SharpP [Finite State] (machine : MultiTapeCTM k Bool State)
    (enc : α ↪ List Bool) (clock : Polynomial ℕ) :
    (fun a => machine.acceptCount (clock.eval (enc a).length)
      (Cfg.init machine.initial (enc a))) ∈ Complexity.SharpP enc := by
  simpa [acceptCount] using verdictCount_mem_SharpP machine enc clock true

/-- Rejecting terminal branches have their own valid-certificate #P verifier. It complements
the output verdict while retaining validity, so invalid binary words are never counted. -/
theorem rejectCount_mem_SharpP [Finite State] (machine : MultiTapeCTM k Bool State)
    (enc : α ↪ List Bool) (clock : Polynomial ℕ) :
    (fun a => machine.rejectCount (clock.eval (enc a).length)
      (Cfg.init machine.initial (enc a))) ∈ Complexity.SharpP enc := by
  simpa [rejectCount] using verdictCount_mem_SharpP machine enc clock false

/-- The difference of accepting and rejecting polynomial-clock terminal counts is in GapP.
This is the forward implication; the reverse construction is in `Classes.SharpP.GapMachine`. -/
theorem gapCount_mem_GapP [Finite State] (machine : MultiTapeCTM k Bool State)
    (enc : α ↪ List Bool) (clock : Polynomial ℕ) :
    (fun a => (machine.acceptCount (clock.eval (enc a).length)
      (Cfg.init machine.initial (enc a)) : ℤ) - machine.rejectCount
        (clock.eval (enc a).length) (Cfg.init machine.initial (enc a))) ∈ Complexity.GapP enc :=
  Complexity.GapP.natCast_sub_natCast_mem (machine.acceptCount_mem_SharpP enc clock)
    (machine.rejectCount_mem_SharpP enc clock)

end Turing.MultiTapeCTM
