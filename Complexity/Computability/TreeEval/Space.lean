/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Instance
public import Complexity.Computability.TreeEval.Reader.Size

/-!
# Tree Evaluation in small space

**Cook and Mertz**: Tree Evaluation of value length `ℓ` and height `H` is computable on
multi-tape Turing machines in space `O((ℓ + H + 1) · log (ℓ + 2) + log (n + 2))`, where `n`
is the length of the encoded instance. On nontrivial instances (`1 ≤ ℓ` and `1 ≤ H`), both `2 ^ ℓ`
and `2 ^ H` are at most `n`, so `ℓ, H < |n|` and `|ℓ| ≤ ||n||` (writing `|m|` for the binary length
of `m`), which yields the headline input-size space bound `O(|n| · ||n||) = O(log n · log log n)`.

The step machine simulating the read machine `Cslib.TreeEval.Reader.machine` is tidy, its run on an
instance halts with the value of the tree, and its states along the run, which follow the states
of the read machine together with the position of the head, stay within the space bound.

## Main definitions

* `Cslib.TreeEval.NontrivialInstance`: Tree Evaluation instances with `1 ≤ ℓ` and `1 ≤ H`.
* `Cslib.TreeEval.encNontrivialInstance`: the encoding of nontrivial instances.

## Main results

* `Cslib.TreeEval.computableInSpace_eval`: Tree Evaluation in space
  `O(spaceBound ℓ H + log (n + 2))`, with the value not charged to the space bound
  (`Turing.MultiTapeTM.ComputableInBigO`).
* `Cslib.TreeEval.spaceBound_add_length_le_log_mul_log_log`: on nontrivial instances,
  `spaceBound ℓ H + |n + 1| ≤ 6 · |n| · ||n||`.
* `Cslib.TreeEval.computableInSpace_eval_log_mul_log_log`: Tree Evaluation on nontrivial
  instances in space `O(|n| · ||n||) = O(log n · log log n)`.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024]
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval]
-/

@[expose] public section

namespace Cslib.TreeEval

open Turing MultiTapeTM Reader

/-- A nontrivial Tree Evaluation instance: both the value length `ℓ` and the height `H` are
positive. -/
abbrev NontrivialInstance : Type := {I : Instance // 1 ≤ I.ell ∧ 1 ≤ I.height}

/-- The encoding of nontrivial Tree Evaluation instances. -/
def encNontrivialInstance : NontrivialInstance ↪ List Bool :=
  (Function.Embedding.subtype _).trans encInstance

@[simp] theorem encNontrivialInstance_apply (I : NontrivialInstance) :
    encNontrivialInstance I = encInstance I.1 := rfl

/-- **Tree Evaluation in small space** (Cook–Mertz): the value of the tree of an instance of value
length `ℓ` and height `H` is computable from its encoding in space
`O((ℓ + H + 1) · log (ℓ + 2) + log (n + 2))`; the value is not charged to the space bound. -/
theorem computableInSpace_eval : ∃ t, ComputableInBigO
    (fun I : Instance => List.ofFn I.tree.eval) encInstance encBits t
    fun I => spaceBound I.ell I.height + (encNat ((encInstance I).length + 1)).length := by
  obtain ⟨T, hT⟩ := tidy_machine
  have hc (I : Instance) :
      machine.toStepMachine.Computes (encInstance I) (List.ofFn I.tree.eval) := by
    obtain ⟨n, s, hrun, hhalt⟩ := exists_run_eq I.tree
    have := ReadMachine.computes_toStepMachine (m := machine) (x := I.tree.encode) (n := n)
      (by rw [hrun]; exact hhalt)
    rwa [hrun] at this
  choose rounds hr ho using hc
  let tS := ReadMachine.stateT encState T stateBudget
  let tMax (I : Instance) : ℕ := ∑ i ∈ Finset.range (rounds I + 1),
    tS (machine.toStepMachine.run (encInstance I) i).state
  refine ⟨_, ComputableTidilyInBigO.computableInBigO <|
    (hT.computableTidilyInTimeAndSpace (fun I : Instance => List.ofFn I.tree.eval)
    rounds hr (fun I => by rw [encBits_apply, ho]) (tMax := tMax)
    (sMax := fun I => 5 * 2 ^ 12 * spaceBound I.ell I.height +
      2 * (encNat ((encInstance I).length + 1)).length + 6) fun I i hi => ⟨?_, ?_⟩).weaken
    (.refl _) (.of_le_linear (5 * 2 ^ 12 + 2) 6 fun I => by omega)⟩
  · exact Finset.single_le_sum (f := fun i => tS (machine.toStepMachine.run
    (encInstance I) i).state)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  · obtain ⟨j, hq, hpos⟩ := ReadMachine.exists_state_run (m := machine) (encInstance I) i
    rw [hq]
    have hb : stateBudget (machine.run
    (encInstance I) j).state ≤ 2 ^ 12 * spaceBound I.ell I.height :=
      stateBudget_le (bounds_of_inv (inv_run (T := I.tree) j))
    have hs : (encState (machine.run (encInstance I) j).state).length ≤
        stateBudget (machine.run (encInstance I) j).state := by
      simp only [stateBudget, stepBudget, encStepInT, length_encPair, encState_apply]; omega
    have hp := ComputableTidilyInO.length_encNat_mono hpos
    simp only [ReadMachine.stateS, length_encPair]
    change _ + 2 * (2 * (encState (machine.run (encInstance I) j).state).length + 1 + _) + 4 ≤ _
    omega

/-- On a nontrivial instance (`1 ≤ ℓ` and `1 ≤ H`), the parameter space bound plus the head-counter
length is at most `6 · |n| · ||n||`, where `n = (encInstance I).length` and
`|m| = (encNat m).length`. -/
theorem spaceBound_add_length_le_log_mul_log_log {I : Instance}
    (hℓ : 1 ≤ I.ell) (hH : 1 ≤ I.height) :
    spaceBound I.ell I.height + (encNat ((encInstance I).length + 1)).length ≤
      6 * ((encNat (encInstance I).length).length *
        (encNat (encNat (encInstance I).length).length).length) := by
  set n := (encInstance I).length with hn
  set L := (encNat n).length with hL
  set M := (encNat L).length with hM
  have hn2 : 2 ≤ n := two_le_length_encInstance I
  have hL2 : 2 ≤ L := by
    rw [hL, length_encNat_eq_size]
    exact Nat.lt_size.mpr (by omega)
  have hM2 : 2 ≤ M := by
    rw [hM, length_encNat_eq_size]
    exact Nat.lt_size.mpr (by omega)
  have hℓL : I.ell < L := ell_lt_length_encNat_length_encInstance hH
  have hHL : I.height < L := height_lt_length_encNat_length_encInstance hℓ
  have hℓM : (encNat I.ell).length ≤ M :=
    ComputableTidilyInO.length_encNat_mono hℓL.le
  have hsp : spaceBound I.ell I.height ≤ (2 * L) * (2 * M) := by
    rw [spaceBound]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hn1 : (encNat (n + 1)).length ≤ L + 1 := by
    rw [length_encNat_eq_size, hL, length_encNat_eq_size]
    refine Nat.size_le.mpr ?_
    have := Nat.lt_size_self n
    have : 2 ≤ 2 ^ n.size := by omega
    rw [pow_succ]
    omega
  nlinarith

/-- **Tree Evaluation in space `O(log n · log log n)`** (Cook–Mertz): on nontrivial instances
(`1 ≤ ℓ` and `1 ≤ H`), the value of the tree is computable from its encoding in space
`O(|n| · ||n||)`, where `n` is the length of the encoded instance and `|m| = (encNat m).length`;
the value is not charged to the space bound. -/
theorem computableInSpace_eval_log_mul_log_log : ∃ t, ComputableInBigO
    (fun I : NontrivialInstance => List.ofFn I.1.tree.eval) encNontrivialInstance encBits t
    fun I => (encNat (encNontrivialInstance I).length).length *
      (encNat (encNat (encNontrivialInstance I).length).length).length := by
  obtain ⟨t, c, k, State, hfinite, tm, htm⟩ := computableInSpace_eval
  have hN : ComputableInBigO (fun I : NontrivialInstance => List.ofFn I.1.tree.eval)
      encNontrivialInstance encBits (fun I => t I.1)
      (fun I => spaceBound I.1.ell I.1.height + (encNat ((encInstance I.1).length + 1)).length) :=
    ⟨c, k, State, hfinite, tm, fun I => htm I.1⟩
  exact ⟨fun I => t I.1, hN.weaken (.refl _) (.of_le_linear 6 0 fun I => by
    simpa only [encNontrivialInstance_apply, Nat.add_zero] using
      spaceBound_add_length_le_log_mul_log_log I.2.1 I.2.2)⟩

end Cslib.TreeEval
