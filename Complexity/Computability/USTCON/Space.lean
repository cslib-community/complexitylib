/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.USTCON.Reader.Cert
public import Complexity.Computability.USTCON.Reader.Invariant
public import Complexity.Computability.Machines.ReadMachine.StepMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace

/-!
# Undirected connectivity in logarithmic space

**Reingold's theorem**: deciding undirected `s`–`t` connectivity on the encodings
`Cslib.Complexity.encUSTCON` is computable in logarithmic space
(`Cslib.USTCON.computableInLogSpace_decide`) [Reingold, Theorem 4.1][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09].

The step machine simulating the read machine `Cslib.USTCON.Reader.machine` is tidy within the space
of its states and the position of its head (`Cslib.USTCON.Reader.tidy_machine`). It computes the
output of the read machine (`Turing.ReadMachine.computes_toStepMachine`), which halts on an encoded
instance with the answer (`Cslib.USTCON.Reader.exists_run_eq`), and its states along the run are
states of the read machine together with a head position at most `m + 1`
(`Turing.ReadMachine.exists_state_run`), which have `O(log m)` bits on encodings of length `m`
(`Cslib.USTCON.Reader.length_encState_run_le`). Correctness is claimed only on encodings of
instances; recognising which bit strings are encodings is not formalised.

## Main results

* `Cslib.USTCON.computableInBigO_decide`: the decision in space `O(log n)`, with the output not
  charged to the space bound (`Turing.MultiTapeTM.ComputableInBigO`).
* `Cslib.USTCON.computableInLogSpace_decide`: the decision is computable in logarithmic space.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.USTCON

open Turing MultiTapeTM Reader Cslib.Complexity

open scoped Classical in
/-- **Undirected connectivity in space `O(log n)`**: the decision of undirected `s`–`t`
connectivity is computable from the encoded instance in space linear in the logarithm of its
length. -/
theorem computableInBigO_decide : ∃ t, ComputableInBigO
    (fun I : USTCONInstance ↦ decide (I ∈ USTCON)) encUSTCON encBool t
    fun I ↦ Nat.log2 (encUSTCON I).length + 1 := by
  obtain ⟨T, hT⟩ := tidy_machine
  have hc (I : USTCONInstance) :
      machine.toStepMachine.Computes (encUSTCON I) [decide (I ∈ USTCON)] := by
    obtain ⟨k, hhalt, hout⟩ := exists_run_eq I
    have := ReadMachine.computes_toStepMachine (m := machine) (x := I.encode) (n := k) hhalt
    rwa [hout] at this
  choose rounds hr ho using hc
  let tS := ReadMachine.stateT encState T stateBudget
  let tMax (I : USTCONInstance) : ℕ := ∑ i ∈ Finset.range (rounds I + 1),
    tS (machine.toStepMachine.run (encUSTCON I) i).state
  refine ⟨_, ComputableTidilyInBigO.computableInBigO <|
    (hT.computableTidilyInTimeAndSpace (fun I : USTCONInstance ↦ decide (I ∈ USTCON))
    rounds hr (fun I ↦ by rw [encBool_apply, ho]) (tMax := tMax)
    (sMax := fun I ↦ 6 * stateConst * (Nat.log2 (encUSTCON I).length + 2) +
      2 * (Nat.log2 (encUSTCON I).length + 2) + 12) fun I i hi ↦ ⟨?_, ?_⟩).weaken
    (.refl _) (.of_le_linear (12 * stateConst + 4) (12 * stateConst + 16) fun I ↦ by nlinarith)⟩
  · exact Finset.single_le_sum (f := fun i ↦ tS (machine.toStepMachine.run (encUSTCON I) i).state)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.2 (by omega))
  · obtain ⟨j, hq, hpos⟩ := ReadMachine.exists_state_run (m := machine) (encUSTCON I) i
    rw [hq]
    have hs : (encState (machine.run (encUSTCON I) j).state).length ≤
        stateConst * (Nat.log2 (encUSTCON I).length + 2) :=
      length_encState_run_le (I := I) j
    have hp : (encNat ((machine.toStepMachine.run (encUSTCON I) i).state.2)).length ≤
        Nat.log2 (encUSTCON I).length + 2 := by
      rw [length_encNat_eq_size]
      refine Nat.size_le.2 (hpos.trans_lt ?_)
      have := Nat.lt_log2_self (n := (encUSTCON I).length)
      rw [pow_succ]
      omega
    have hb : stateBudget (machine.run (encUSTCON I) j).state =
        2 * (encState (machine.run (encUSTCON I) j).state).length + 2 := by
      simp only [stateBudget, stepBudget, length_encPair, encBool_apply, List.length_singleton,
        encState_apply]
    simp only [ReadMachine.stateS, length_encPair, hb]
    nlinarith

open scoped Classical in
/-- **Reingold's theorem**: deciding undirected `s`–`t` connectivity is computable in logarithmic
space, on encodings of instances by their adjacency matrices. -/
theorem computableInLogSpace_decide :
    ComputableInLogSpace (fun I : USTCONInstance ↦ decide (I ∈ USTCON)) encUSTCON encBool := by
  obtain ⟨t, c, hc⟩ := computableInBigO_decide
  exact ⟨_, 2 * c, hc.mono (fun _ ↦ le_rfl) fun I ↦ by nlinarith⟩

end Cslib.USTCON
