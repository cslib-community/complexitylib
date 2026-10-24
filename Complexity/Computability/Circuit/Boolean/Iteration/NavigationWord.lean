/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Label

/-!
# First hitting times from words of bounded width

For `n`-bit states, transient depths, phases and cycle lengths are below `2 ^ n`, so they fit in
`n + 3` bits with room for one addition (`depthWord`, `phaseWord`, `lengthWord`). The closed forms
for reachability and first hitting times (`FunctionalGraph.reaches`,
`FunctionalGraph.hittingTime`) are then word computations from the depths, labels and phases of
the two states: a comparison and a difference of depths for a transient target, a modular
difference of phases for a periodic one (`navigationFlag_eq_reaches`,
`toNat_navigationTime`). The output format is one reachability bit and `n + 1` time bits
(`navigationBits`); the time is specified only when the target is reachable, where it is below
`2 ^ n` (`navigationBits_time`).

These are word-level identities. The circuits that compute depths and labels are in
`Iteration.Depth` and `Iteration.LabelCircuit`.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.navigationFlag`, `navigationTime`: reachability and first
  hitting time as word computations.
* `Cslib.Circuits.Boolean.Iteration.navigationBits`: one flag bit and `n + 1` time bits.

## Main results

* `Cslib.Circuits.Boolean.Iteration.navigationFlag_eq_reaches`,
  `Cslib.Circuits.Boolean.Iteration.toNat_navigationTime`: agreement with the closed forms.
* `Cslib.Circuits.Boolean.Iteration.navigationBits_flag`,
  `Cslib.Circuits.Boolean.Iteration.navigationBits_time`: the output format.

## References

* Adapted from lean/Proofs/NavigationEncoding.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n : ℕ} (f : BitString n → BitString n)

/-- The transient depth of `x` in `n + 3` bits. -/
noncomputable def depthWord (x : BitString n) : BitVec (n + 3) :=
  BitVec.ofNat (n + 3) (transientDepth f x)

/-- The phase of `x` in `n + 3` bits. -/
noncomputable def phaseWord (x : BitString n) : BitVec (n + 3) :=
  BitVec.ofNat (n + 3) (phase f x)

/-- The cycle length of `x` in `n + 3` bits. -/
noncomputable def lengthWord (x : BitString n) : BitVec (n + 3) :=
  BitVec.ofNat (n + 3) (cycleLength f x)

theorem transientDepth_lt_two_pow (x : BitString n) : transientDepth f x < 2 ^ n := by
  simpa using transientDepth_lt_card f x

@[simp] theorem toNat_depthWord (x : BitString n) : (depthWord f x).toNat = transientDepth f x := by
  have h := transientDepth_lt_two_pow f x
  rw [depthWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simp only [Nat.pow_succ]
  omega

@[simp] theorem toNat_phaseWord (x : BitString n) : (phaseWord f x).toNat = phase f x :=
  toNat_ofNat_phase f x

@[simp] theorem toNat_lengthWord (x : BitString n) : (lengthWord f x).toNat = cycleLength f x :=
  toNat_ofNat_cycleLength f x

/-- The difference of the transient depths of `x` and `y`. -/
noncomputable def navigationGap (x y : BitString n) : BitVec (n + 3) :=
  depthWord f x - depthWord f y

/-- The phase of `y` minus the phase of `x` at the end of its transient, modulo the cycle length
of `x`. -/
noncomputable def navigationDistance (x y : BitString n) : BitVec (n + 3) :=
  subMod (phaseWord f y) (phaseWord f x + depthWord f x) (lengthWord f x)

/-- Reachability as a word computation: equal representatives for a periodic target, and a
depth comparison and one state comparison for a transient target. -/
noncomputable def navigationFlag (x y : BitString n) : Bool :=
  if depthWord f y = 0 then decide (canonicalCycle f x = canonicalCycle f y)
  else !(depthWord f x).ult (depthWord f y) && decide (f^[(navigationGap f x y).toNat] x = y)

/-- The first hitting time as a word computation. -/
noncomputable def navigationTime (x y : BitString n) : BitVec (n + 3) :=
  if depthWord f y = 0 then depthWord f x + navigationDistance f x y else navigationGap f x y

theorem toNat_navigationGap (x y : BitString n)
    (hle : transientDepth f y ≤ transientDepth f x) :
    (navigationGap f x y).toNat = transientDepth f x - transientDepth f y := by
  rw [navigationGap, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using hle),
    toNat_depthWord, toNat_depthWord]

private theorem toNat_navigationDistance (x y : BitString n) :
    (navigationDistance f x y).toNat = cyclicDistance f x y := by
  have hμ := transientDepth_lt_two_pow f x
  have hpx := (phase_lt f x).trans_le (cycleLength_le_two_pow f x)
  have hl := cycleLength_le_two_pow f x
  have hsum : phase f x + transientDepth f x < 2 ^ (n + 3) := by
    simp only [Nat.pow_succ]
    omega
  rw [navigationDistance, toNat_subMod _ _ _ (by simpa using cycleLength_pos f x)
    (by simp only [toNat_lengthWord, Nat.pow_succ]; omega), BitVec.toNat_add,
    toNat_phaseWord, toNat_phaseWord, toNat_depthWord, toNat_lengthWord, Nat.mod_eq_of_lt hsum]
  rfl

theorem depthWord_eq_zero_iff (x : BitString n) : depthWord f x = 0 ↔ transientDepth f x = 0 := by
  rw [← BitVec.toNat_inj, toNat_depthWord]
  rfl

theorem navigationFlag_eq_reaches (x y : BitString n) : navigationFlag f x y = reaches f x y := by
  unfold navigationFlag reaches
  simp only [depthWord_eq_zero_iff]
  split_ifs with hy
  · exact decide_eq_decide.mpr Iff.rfl
  · by_cases hle : transientDepth f y ≤ transientDepth f x
    · simp only [BitVec.ult, toNat_depthWord, show ¬transientDepth f x < transientDepth f y by
        omega, decide_false, Bool.not_false, Bool.true_and, hle, decide_true,
        toNat_navigationGap f x y hle]
      exact decide_eq_decide.mpr Iff.rfl
    · simp only [BitVec.ult, toNat_depthWord, show transientDepth f x < transientDepth f y by
        omega, decide_true, Bool.not_true, Bool.false_and, hle, decide_false]

theorem toNat_navigationTime (x y : BitString n) (h : reaches f x y = true) :
    (navigationTime f x y).toNat = hittingTime f x y := by
  unfold navigationTime hittingTime
  simp only [depthWord_eq_zero_iff]
  split_ifs with hy
  · rw [BitVec.toNat_add, toNat_depthWord, toNat_navigationDistance]
    apply Nat.mod_eq_of_lt
    have hd : cyclicDistance f x y < cycleLength f x := Nat.mod_lt _ (cycleLength_pos f x)
    have hμ := transientDepth_lt_two_pow f x
    have hl := cycleLength_le_two_pow f x
    simp only [Nat.pow_succ]
    omega
  · apply toNat_navigationGap
    exact ((exists_iterate_eq_iff_of_not_mem_periodicPts f x y fun hp =>
      hy ((transientDepth_eq_zero_iff f y).mpr hp)).mp ((reaches_iff f x y).mp h)).1

/-- One reachability bit followed by `n + 1` bits of the first hitting time. -/
noncomputable def navigationBits (x y : BitString n) : BitString (1 + (n + 1)) :=
  Fin.append (fun _ => navigationFlag f x y) fun i => (navigationTime f x y).getLsbD i.val

theorem navigationBits_flag (x y : BitString n) :
    navigationBits f x y 0 = true ↔ ∃ t, f^[t] x = y := by
  change navigationFlag f x y = true ↔ _
  rw [navigationFlag_eq_reaches, reaches_iff]

/-- **The output format.** When `y` is reachable from `x`, the time bits of `navigationBits` are
the first hitting time, which is below `2 ^ n`. -/
theorem navigationBits_time (x y : BitString n) (h : ∃ t, f^[t] x = y) :
    let t := (word fun i : Fin (n + 1) => navigationBits f x y (Fin.natAdd 1 i)).toNat
    f^[t] x = y ∧ (∀ j < t, f^[j] x ≠ y) ∧ t < 2 ^ n := by
  have hr := (reaches_iff f x y).mpr h
  have ht := hittingTime_spec f x y hr
  have hb : hittingTime f x y < 2 ^ n := by simpa using ht.2.2
  have he : (word fun i : Fin (n + 1) => navigationBits f x y (Fin.natAdd 1 i)) =
      (navigationTime f x y).setWidth (n + 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_word _ ⟨i, hi⟩]
    simp only [navigationBits, Fin.append_right, BitVec.getLsbD_setWidth, hi, decide_true,
      Bool.true_and]
  dsimp only
  rw [he, BitVec.toNat_setWidth, toNat_navigationTime f x y hr,
    Nat.mod_eq_of_lt (hb.trans (Nat.pow_lt_pow_right (by decide) (by omega)))]
  exact ⟨ht.1, ht.2.1, hb⟩

end Cslib.Circuits.Boolean.Iteration
