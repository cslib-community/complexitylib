/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.InputTime
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.NavigationFeatures
import CslibFrontier.Tactic.Synthesis

/-!
# Circuit synthesis for reachability and first hitting times

This module synthesizes the navigation word `(reaches f x y, hittingTime f x y)` on pair inputs
`z : BitString (n + n)` in two ways:
* `synthesis_navigation_given_flag`: when a circuit `transientReach` already decides reachability on
  transient targets (`0 < transientDepth f y`), we combine two depth circuits, two cycle-label
  circuits, a streaming modular difference (`synthesis_subMod`), and word arithmetic to output
  `navigationBits f (inputLeft z) (inputRight z)` without evaluating a variable-time iterate;
* `synthesis_navigation`: when no external transient-reachability circuit is supplied, we evaluate
  `f^[transientDepth f x - transientDepth f y] x` by binary powering (`synthesis_binary_powering`)
  to decide transient reachability directly.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_navigation_given_flag`: synthesizes `navigationBits`
  using an external transient-reachability circuit.
* `Cslib.Circuits.Boolean.Iteration.synthesis_navigation`: synthesizes `navigationBits` using
  binary powering for the transient check.

## References

* Adapted from lean/Proofs/NavigationSynthesis.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n : ℕ}

/-- Combine depth, cycle-label, and a supplied transient-reachability flag into the exact
reachability bit and first hitting time. -/
theorem synthesis_navigation_given_flag (f : BitString n → BitString n)
    (depth : Circuit signature n (n + 2))
    (hd : ∀ x, word (depth.eval interpretation x) =
      BitVec.ofNat (n + 2) (transientDepth f x))
    (label : Circuit signature n (labelWidth n))
    (hl : ∀ x, label.eval interpretation x = canonicalLabel f x)
    (transientReach : Circuit signature (n + n) 1)
    (htr : ∀ z, 0 < transientDepth f (inputRight z) →
      (transientReach.eval interpretation z 0 = true ↔
        ∃ t, f^[t] (inputLeft z) = inputRight z)) :
    Synthesis interpretation (inputs (n + n))
      (Set.range fun i z => navigationBits f (inputLeft z) (inputRight z) i)
      (2 + 2 * depth.size + 2 * label.size + transientReach.size +
        50 * (n + 4) ^ 2 + (49 * n + 138)) := by
  -- The builder retains each stage's wires for the rest of the construction.
  let b := Synthesis.Builder.start interpretation (inputs (n + n))
  let b := b.add ((Synthesis.const false).union (Synthesis.const true))
  synthesis_step b using synthesis_depthWord f depth hd b.wires inputLeft
  synthesis_step b using synthesis_depthWord f depth hd b.wires inputRight
  synthesis_step b using synthesis_label_parts f label hl b.wires inputLeft
  synthesis_step b using synthesis_label_parts f label hl b.wires inputRight
  let diff := fun z => navigationGap f (inputLeft z) (inputRight z)
  synthesis_step b using Synthesis.word_sub
    (fun z => depthWord f (inputLeft z)) (fun z => depthWord f (inputRight z))
  synthesis_step b using Synthesis.word_eq_const (v := 0)
    (fun z => depthWord f (inputRight z))
  synthesis_step b using synthesis_bits_eq b.wires
    (fun z => canonicalCycle f (inputLeft z)) (fun z => canonicalCycle f (inputRight z))
  synthesis_step b using Synthesis.circuit transientReach (fun i z => z i)
  let sumx := fun z => phaseWord f (inputLeft z) + depthWord f (inputLeft z)
  synthesis_step b using Synthesis.word_add
    (fun z => phaseWord f (inputLeft z)) (fun z => depthWord f (inputLeft z))
  let cycDist := fun z => navigationDistance f (inputLeft z) (inputRight z)
  synthesis_step b using synthesis_subMod b.wires (fun z => phaseWord f (inputRight z)) sumx
    (fun z => lengthWord f (inputLeft z))
  let cycTime := fun z => depthWord f (inputLeft z) + cycDist z
  synthesis_step b using Synthesis.word_add (fun z => depthWord f (inputLeft z)) cycDist
  have hflagMux : Synthesis interpretation b.wires
      {fun z => if decide (depthWord f (inputRight z) = 0)
        then decide (canonicalCycle f (inputLeft z) = canonicalCycle f (inputRight z))
        else transientReach.eval interpretation z 0} 4 :=
    Synthesis.mux (by synthesis_available) (by synthesis_available) (by synthesis_available)
  have htimeMux := Synthesis.word_mux (s := b.wires) cycTime diff
    (fun z => decide (depthWord f (inputRight z) = 0))
    (by synthesis_available) (by synthesis_available) (by synthesis_available)
  have hflagEq : (fun z => if decide (depthWord f (inputRight z) = 0)
      then decide (canonicalCycle f (inputLeft z) = canonicalCycle f (inputRight z))
      else transientReach.eval interpretation z 0) =
      fun z => navigationFlag f (inputLeft z) (inputRight z) := by
    funext z
    rw [navigationFlag_eq_reaches]
    simp only [decide_eq_true_eq, depthWord_eq_zero_iff]
    by_cases hz : transientDepth f (inputRight z) = 0
    · simp only [hz, ite_true, reaches]
      exact decide_eq_decide.mpr Iff.rfl
    · simp only [hz, ite_false]
      apply Bool.eq_iff_iff.mpr
      rw [htr z (Nat.pos_of_ne_zero hz), ← reaches_iff]
  have htimeEq : (fun z => if decide (depthWord f (inputRight z) = 0) then cycTime z else diff z) =
      fun z => navigationTime f (inputLeft z) (inputRight z) := by
    funext z
    simp only [navigationTime, cycTime, cycDist, diff, decide_eq_true_eq]
  rw [hflagEq] at hflagMux
  rw [htimeEq] at htimeMux
  let b := b.add (hflagMux.union htimeMux)
  apply b.finish
  · rintro _ ⟨i, rfl⟩
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i
    · simpa only [navigationBits, Fin.append_left, Fin.isValue, Fin.elim0, Fin.cons_zero] using
        (show (fun z => navigationFlag f (inputLeft z) (inputRight z)) ∈ b.wires from
          by synthesis_available)
    · have h := show (fun z => (navigationTime f (inputLeft z) (inputRight z)).getLsbD
          (⟨j.val, by omega⟩ : Fin (n + 3)).val) ∈ b.wires from by synthesis_available
      simpa only [navigationBits, Fin.append_right] using h
  · dsimp +zetaDelta [Synthesis.Builder.add, Synthesis.Builder.start]
    rw [show n + 3 + 1 = n + 4 from rfl]
    omega

/-- Combine depth, cycle-label, and binary-powering circuits into the navigation word. -/
theorem synthesis_navigation (f : BitString n → BitString n) (K : ℕ)
    (hpowers : ∀ j < n + 1, ∃ pow : Circuit signature n n,
      pow.Computes interpretation f^[2 ^ j] ∧ pow.size ≤ K)
    (depth : Circuit signature n (n + 2))
    (hd : ∀ x, word (depth.eval interpretation x) =
      BitVec.ofNat (n + 2) (transientDepth f x))
    (label : Circuit signature n (labelWidth n))
    (hl : ∀ x, label.eval interpretation x = canonicalLabel f x) :
    Synthesis interpretation (inputs (n + n))
      (Set.range fun i z => navigationBits f (inputLeft z) (inputRight z) i)
      (4 + 4 * depth.size + 2 * label.size + (n + 1) * (K + 4 * n) +
        50 * (n + 4) ^ 2 + (73 * n + 198)) := by
  let b := Synthesis.Builder.start interpretation (inputs (n + n))
  let b := b.add ((Synthesis.const false).union (Synthesis.const true))
  synthesis_step b using synthesis_depthWord f depth hd b.wires inputLeft
  synthesis_step b using synthesis_depthWord f depth hd b.wires inputRight
  let diff := fun z => navigationGap f (inputLeft z) (inputRight z)
  synthesis_step b using Synthesis.word_sub
      (fun z => depthWord f (inputLeft z)) (fun z => depthWord f (inputRight z))
  synthesis_step b using Synthesis.word_ult
      (fun z => depthWord f (inputLeft z)) (fun z => depthWord f (inputRight z))
  have hleSynth : Synthesis interpretation b.wires
      {fun z => !(depthWord f (inputLeft z)).ult (depthWord f (inputRight z))} 1 :=
    (Synthesis.of_mem (by synthesis_available)).not
  let b := b.add hleSynth
  let diffBits : BitString (n + n) → BitString (n + 1) :=
    fun z i => (diff z).getLsbD i.val
  have hdiffBits : wires diffBits ⊆ wordWires diff := by
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  synthesis_step b using
    synthesis_binary_powering (m := n + 1) f K hpowers b.wires inputLeft diffBits
  synthesis_step b using synthesis_bits_eq b.wires
      (fun z => f^[(word (diffBits z)).toNat] (inputLeft z)) inputRight
  let transientFlag := fun z => (!(depthWord f (inputLeft z)).ult (depthWord f (inputRight z))) &&
    decide (f^[(word (diffBits z)).toNat] (inputLeft z) = inputRight z)
  have htrFlag : Synthesis interpretation b.wires {transientFlag} 1 :=
    (Synthesis.of_mem (by synthesis_available)).and (Synthesis.of_mem (by synthesis_available))
  let b := b.add htrFlag
  have htrAll := b.finish (t := {transientFlag}) (by synthesis_available) le_rfl
  obtain ⟨transientReach, htrEval, htrSize⟩ := htrAll.exists_circuit
  have htrSpec (z : BitString (n + n)) (hy : 0 < transientDepth f (inputRight z)) :
      transientReach.eval interpretation z 0 = true ↔
        ∃ t, f^[t] (inputLeft z) = inputRight z := by
    rw [htrEval z]
    change ((!(depthWord f (inputLeft z)).ult (depthWord f (inputRight z))) &&
      decide (f^[(word (diffBits z)).toNat] (inputLeft z) = inputRight z)) = true ↔ _
    rw [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not, not_lt,
      toNat_depthWord, toNat_depthWord, decide_eq_true_eq]
    have hnotper : inputRight z ∉ Function.periodicPts f :=
      fun h => ne_of_gt hy ((transientDepth_eq_zero_iff f (inputRight z)).mpr h)
    rw [exists_iterate_eq_iff_of_not_mem_periodicPts f (inputLeft z) (inputRight z) hnotper]
    have hdiffToNat (hle : transientDepth f (inputRight z) ≤ transientDepth f (inputLeft z)) :
        (word (diffBits z)).toNat =
          transientDepth f (inputLeft z) - transientDepth f (inputRight z) := by
      have hw : word (diffBits z) = (diff z).setWidth (n + 1) := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [getLsbD_word _ ⟨i, hi⟩]
        simp [diffBits, hi]
      have hlt :
          transientDepth f (inputLeft z) - transientDepth f (inputRight z) < 2 ^ (n + 1) := by
        have := transientDepth_lt_two_pow f (inputLeft z)
        have hpow1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
        lia
      rw [hw, BitVec.toNat_setWidth, toNat_navigationGap f _ _ hle, Nat.mod_eq_of_lt hlt]
    constructor
    · rintro ⟨hle, he⟩
      exact ⟨hle, by rwa [hdiffToNat hle] at he⟩
    · rintro ⟨hle, he⟩
      exact ⟨hle, by rwa [hdiffToNat hle]⟩
  have hmain := synthesis_navigation_given_flag f depth hd label hl transientReach htrSpec
  refine hmain.mono Set.Subset.rfl Set.Subset.rfl ?_
  dsimp +zetaDelta [Synthesis.Builder.add, Synthesis.Builder.start] at htrSize
  omega

end Cslib.Circuits.Boolean.Iteration
