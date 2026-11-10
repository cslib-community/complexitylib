/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Shared output routines for first-order interpretation transducers

The order-free and canonical ordered transducers share coordinate extraction, framing, and
malformed-output emission. Coordinates are written in increasing digit order; a client chooses
its logical coordinate order through the formula's variable-to-register map.

## Main definitions

* `Cslib.Logic.Vocabulary.ModelChecker.Writer.tupleReg`: a coordinate block register.
* `Cslib.Logic.Vocabulary.ModelChecker.Writer.coordinatesCode`: write the digits of an index.
* `Cslib.Logic.Vocabulary.ModelChecker.Writer.rejectCode`: emit a fixed malformed target.

## Main results

* `Cslib.Logic.Vocabulary.ModelChecker.Writer.reaches_coordinatesCode`: exact digit semantics.
* `Cslib.Logic.Vocabulary.ModelChecker.Writer.reachesOut_rejectCode`: exact rejection output.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]. These routines are extracted from the
  existing order-free interpretation transducer, with its author and framing conventions retained.
-/

@[expose] public section

open FirstOrder Language Turing Turing.CounterProgram

namespace Cslib.Logic.Vocabulary.ModelChecker.Writer

open Expr

/-- The register of the coordinate `i` of the tuple in block `m`, for tuples of `d` coordinates. -/
def tupleReg (d m i : ℕ) : ℕ := 8 + d * m + i

/-- The code writing the coordinates of the tuple whose index is in register `4` into block `m`,
placed at the label `b`; it continues at `b + d`. -/
def coordinatesCode (d m b : ℕ) : List Instr :=
  List.ofFn fun i : Fin d =>
    .assign (tupleReg d m i) (mod (div (reg 4) (pow (reg 0) i)) (reg 0)) (b + i + 1)

/-- The coordinate writer uses one instruction per digit. -/
theorem length_coordinatesCode (d m b : ℕ) : (coordinatesCode d m b).length = d := by
  simp [coordinatesCode]

variable {P : CounterProgram} {w : List Bool} {B : ℕ}

/-- **Writing the coordinates of a tuple**: from the code at `b`, with the index `u < n ^ d` of a
tuple in register `4` and `n` in register `0`, the program writes the coordinates `u / n ^ i % n`
of the tuple into block `m`, changing no other register. -/
theorem reaches_coordinatesCode {d m b n u : ℕ} (hP : P.CodeAt b (coordinatesCode d m b))
    (hu : u < n ^ d) (hnB : n ≤ B) (regs : List ℕ) (h0 : regs.getD 0 0 = n)
    (h4 : regs.getD 4 0 = u) (hlen : tupleReg d m d ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.Reaches w (P.Running B) (b, regs) (b + d, regs') ∧
      regs'.length = regs.length ∧ (∀ i < d, regs'.getD (tupleReg d m i) 0 = u / n ^ i % n) ∧
      (∀ r, (∀ i < d, r ≠ tupleReg d m i) → regs'.getD r 0 = regs.getD r 0) ∧
      ∀ r ∈ regs', r ≤ B := by
  have key : ∀ k ≤ d, ∃ regs', P.Reaches w (P.Running B) (b, regs) (b + k, regs') ∧
      regs'.length = regs.length ∧ (∀ i < k, regs'.getD (tupleReg d m i) 0 = u / n ^ i % n) ∧
      (∀ r, (∀ i < k, r ≠ tupleReg d m i) → regs'.getD r 0 = regs.getD r 0) ∧
      ∀ r ∈ regs', r ≤ B := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨regs, Reaches.refl _, rfl, fun _ h => absurd h (by omega),
        fun _ _ => rfl, hB⟩
    | succ k ih =>
      intro hk
      obtain ⟨regs₁, hreach, hlen₁, hset, hkeep, hB₁⟩ := ih (by omega)
      have hc : P.instr (b + k) =
          .assign (tupleReg d m k) (mod (div (reg 4) (pow (reg 0) k)) (reg 0)) (b + k + 1) := by
        rw [hP k (by rw [length_coordinatesCode]; omega)]
        simp [coordinatesCode]
      have h0₁ : regs₁.getD 0 0 = n := by rw [hkeep 0 (fun i _ => by unfold tupleReg; omega), h0]
      have h4₁ : regs₁.getD 4 0 = u := by rw [hkeep 4 (fun i _ => by unfold tupleReg; omega), h4]
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · rw [zero_pow (by omega)] at hu
          omega
        · exact h
      refine ⟨regs₁.set (tupleReg d m k) (u / n ^ k % n), hreach.trans (Reaches.assign hc hB₁ ?_),
        by rw [List.length_set, hlen₁], fun i hi => ?_, fun r hr => ?_,
        List.forall_mem_set_of_forall_mem hB₁ ((Nat.mod_lt _ hn).le.trans hnB)⟩
      · simp only [eval_mod, eval_div, eval_pow, eval_reg, h4₁, h0₁]
        exact Reaches.refl _
      · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi | rfl
        · rw [List.getD_set_ne (by unfold tupleReg; omega), hset i hi]
        · exact List.getD_set_self (by rw [hlen₁]; simp only [tupleReg] at hlen ⊢; omega)
      · rw [List.getD_set_ne (Ne.symm (hr k (by omega))), hkeep r fun i hi => hr i (by omega)]
  exact key d le_rfl

/-- Distinct blocks have disjoint coordinate registers. -/
theorem tupleReg_ne {d m m' i i' : ℕ} (h : m ≠ m') (hi : i < d) (hi' : i' < d) :
    tupleReg d m i ≠ tupleReg d m' i' := by
  unfold tupleReg
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have : d * (m + 1) ≤ d * m' := Nat.mul_le_mul_left d hlt
    rw [Nat.mul_succ] at this
    omega
  · have : d * (m' + 1) ≤ d * m := Nat.mul_le_mul_left d hgt
    rw [Nat.mul_succ] at this
    omega

/-- Emitting `true` and a bit for every number below `N`, then `false`, frames the bits. -/
theorem flatMap_range_pair_append_false (N : ℕ) (f : Fin N → Bool) :
    ((List.range N).flatMap fun t => [true, if h : t < N then f ⟨t, h⟩ else false]) ++ [false] =
      MultiTapeTM.frame (List.ofFn f) := by
  rw [MultiTapeTM.frame, ← List.map_coe_finRange_eq_range, List.flatMap_map, List.ofFn_eq_map,
    List.flatMap_map]
  congr 1
  refine List.flatMap_congr fun i _ => ?_
  simp [i.2]

variable {L' : Language} (v' : Vocabulary L')

/-- The code emitting `encStructure (0, [[], …, []])`, a malformed input with one table too many,
then halting; placed at `b`. -/
def rejectCode (b : ℕ) : List Instr :=
  List.ofFn (fun i : Fin (v'.count + 2) => .emit false (b + i + 1)) ++ [.halt List.nil]

variable {v'} in
/-- The rejection routine emits exactly the fixed malformed target and halts. -/
theorem reachesOut_rejectCode {b : ℕ} (hP : P.CodeAt b (rejectCode v' b)) (regs : List ℕ)
    (hB : ∀ r ∈ regs, r ≤ B) :
    P.ReachesOut w (P.Active B) (b, regs) (b + (v'.count + 2), regs)
      (List.replicate (v'.count + 2) false) ∧ P.instr (b + (v'.count + 2)) = .halt [] := by
  rw [rejectCode, codeAt_append, List.length_ofFn] at hP
  refine ⟨?_, (codeAt_cons.mp hP.2).1⟩
  have key : ∀ k ≤ v'.count + 2, P.ReachesOut w (P.Active B)
      (b + (v'.count + 2 - k), regs) (b + (v'.count + 2), regs) (List.replicate k false) := by
    intro k
    induction k with
    | zero => exact fun _ => by simpa using ReachesOut.refl _
    | succ k ih =>
      intro hk
      have hc : P.instr (b + (v'.count + 2 - (k + 1))) =
          .emit false (b + (v'.count + 2 - (k + 1)) + 1) := by
        rw [hP.1 (v'.count + 2 - (k + 1)) (by rw [List.length_ofFn]; omega)]
        simp only [List.getElem_ofFn]
      refine ReachesOut.emit hc hB ?_
      rw [show b + (v'.count + 2 - (k + 1)) + 1 = b + (v'.count + 2 - k) by omega]
      exact ih (by omega)
  simpa using key (v'.count + 2) le_rfl

variable {v'} in
/-- The fixed malformed target has one empty table too many. -/
theorem encStructure_reject :
    encStructure ((0, List.replicate (v'.count + 1) []) : EncodedStructure) =
      List.replicate (v'.count + 2) false := by
  have h (n : ℕ) : (List.replicate n ([] : List Bool)).flatMap MultiTapeTM.frame =
      List.replicate n false := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, List.flatMap_cons,
        MultiTapeTM.frame, List.flatMap_nil, List.nil_append, List.singleton_append, ih]
  rw [encStructure_eq, h]
  simp only [List.replicate_zero, MultiTapeTM.frame, List.flatMap_nil, List.nil_append,
    List.singleton_append]
  rfl

end Cslib.Logic.Vocabulary.ModelChecker.Writer
