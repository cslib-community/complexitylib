/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Ladner

/-! Words by index, padding and its inverse on boundary words, capped powers, decoding formulas,
short satisfiability by certificates, concrete members and non-members of Ladner's language, a
concrete machine agreeing and disagreeing with it, the padding reduction and the rounds of the
self-reduction on concrete formulas, the unconditional form, and the axioms of the polynomial-time
certificates, the two holes and Ladner's theorem. -/

namespace ComplexityTests.Ladner

open Cslib Cslib.Complexity Cslib.Complexity.Ladner Cslib.Logic.PL Turing Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal

/-! ### Words by index -/

example : word 0 = [] := by decide
example : word 1 = [false] := by decide
example : word 2 = [true] := by decide
example : word 3 = [false, false] := by decide
example : word 6 = [true, true] := by decide

example : index [] = 0 := by decide
example : index [true, false] = 4 := by decide
example : word (index [true, false, true]) = [true, false, true] := word_index _

/-- The word with index `j` is no longer than `log₂ (j + 1)`. -/
example : 2 ^ (word 6).length ≤ 7 := two_pow_length_word_le 6

/-! ### Padding -/

example : pad [true] 2 = [true, false, true, true] := rfl
example : unpad [true, false, true, true] = ([true], 2) := by decide

/-- Only the last `false` separates: an earlier `false` belongs to the padded word. -/
example : unpad [false, false, true] = ([false], 1) := by decide

/-- Without a `false`, the second component is the length, so the word is not padded. -/
example : unpad [true, true] = ([], 2) := by decide

example (u : List Bool) (k : ℕ) : unpad (pad u k) = (u, k) := unpad_pad u k

/-! ### Capped powers -/

example : capPow 3 2 100 = 9 := by decide
example : capPow 2 10 100 = 100 := by decide
example : capPow 0 0 5 = 1 := by decide
example : capPow 7 3 0 = 0 := by decide

/-! ### Formulas and short satisfiability -/

example : decodeCNF (encCNF [[(3, true)], []]) = [[(3, true)], []] := decodeCNF_encCNF _

/-- The empty word decodes to the empty formula. -/
example : decodeCNF [] = [] := by simp [decodeCNF, Complexity.cnfDecoder, Decoder.list]

/-- A satisfying certificate among the words with indices below `3`. -/
example : bruteSAT 3 [[(5, false)]] = true := by decide

/-- A formula with an empty clause has no satisfying certificate. -/
example : bruteSAT 8 [[]] = false := by decide

/-! ### Ladner's language -/

theorem H_zero : H 0 = 0 := Nat.le_zero.mp (H_le 0)

/-- The empty formula, padded with `0 ^ H 0 = 1` one, is in Ladner's language. -/
theorem false_true_mem_SATH : [false, true] ∈ SATH := by
  have h : [false, true] = pad (encCNF []) ((encCNF []).length ^ H (encCNF []).length) := by
    simp [encCNF, pad, H_zero]
  rw [h]
  exact ⟨[], ⟨fun _ => true, rfl⟩, rfl⟩

/-- A word without a separating `false` is not in Ladner's language. -/
example : [true, true] ∉ SATH := by
  rintro ⟨φ, -, h⟩
  have : false ∈ pad (encCNF φ) ((encCNF φ).length ^ H (encCNF φ).length) := by simp [pad]
  rw [← h] at this
  simp at this

/-- An unsatisfiable formula is not in Ladner's language, however it is padded. -/
example (k : ℕ) : pad (encCNF [[]]) k ∉ SATH := by
  rw [SATH, pad_mem_padSAT_iff]
  rintro ⟨⟨σ, hσ⟩, -⟩
  simp [CNF.eval, Clause.eval] at hσ

example : SATH ∈ NP encBits := SATH_mem_NP

/-- `H` grows slowly. -/
example : H (2 ^ 2 ^ 3) ≤ 3 :=
  (H_le _).trans (by rw [Nat.log_pow one_lt_two, Nat.log_pow one_lt_two])

/-! ### A concrete machine -/

/-- Halt at once with output `[b]`. -/
private def answer (b : Bool) : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }

/-- After its first step, the answering machine has halted with output `[b]`. -/
private theorem runFrom_answer (b : Bool) (x : List Bool) :
    ((answer b).runFrom ((answer b).initCfg x) 1).Halted ∧
      ((answer b).runFrom ((answer b).initCfg x) 1).output = [b] := by
  change ((answer b).step _).state = none ∧ ((answer b).step _).output = [b]
  rw [MultiTapeTM.step_of_state (q := ()) rfl]
  simp [answer, Action.apply]

/-- The numbering of the single state. -/
private def unitNum : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- An index of the machine answering `false`. -/
private noncomputable def iFalse : ℕ := index (frame (eDesc (desc unitNum eBit (answer false))))

private theorem run_iFalse (w : List Bool) {t : ℕ} (ht : 1 ≤ t) :
    runIndexed iFalse w t = ([eBit false], true) := by
  rw [runIndexed, iFalse, word_index, unframe_frame, decodeDesc_eDesc]
  exact universal_desc_of_halted unitNum (answer false) (t := fun _ => 1)
    (fun x => runFrom_answer false x) ht

/-- The machine answering `false` agrees with every padded language on the empty word. -/
example (e : ℕ → ℕ) {cap : ℕ} (hcap : 1 ≤ cap) : Agrees e cap iFalse 0 := by
  refine ⟨false, run_iFalse _ (le_min (one_le_clock _ _) hcap), ?_⟩
  · simp only [Bool.false_eq_true, false_iff]
    rintro ⟨φ, -, h⟩
    have : false ∈ pad (encCNF φ) ((encCNF φ).length ^ e (encCNF φ).length) := by simp [pad]
    rw [← h] at this
    revert this
    decide

/-- It disagrees with Ladner's language on a member. -/
example {cap : ℕ} (hcap : 1 ≤ cap) : ¬Agrees H cap iFalse (index [false, true]) := by
  rintro ⟨b, hb, hiff⟩
  rw [word_index] at hiff hb
  rw [run_iFalse _ (le_min (one_le_clock _ _) hcap)] at hb
  have hb' : b = false := by
    cases b
    · rfl
    · exact absurd hb (by decide)
  exact absurd (hiff.mpr false_true_mem_SATH) (by simp [hb'])

/-! ### The holes -/

example : P encBits ⊆ NP encBits := P_subset_NP

/-- The padding reduction on the empty formula. -/
example (C : ℕ) : padBounded C [] = [false, true] := by
  simp [padBounded, encCNF, capPow, H_zero, pad]

example : falseCNF ∉ SAT := falseCNF_notMem_SAT

/-- A round of the self-reduction keeps short formulas. -/
example (R : CNF ℕ → List Bool) : shrink R 1 [] = [] := by
  simp [shrink, encCNF]

/-- The empty formula is decided by the finite table. -/
example : encCNF [] ∈ smallSAT 1 :=
  (mem_smallSAT (by simp [encCNF])).mpr ⟨fun _ => true, rfl⟩

/-- An unsatisfiable formula is not in the finite table. -/
example : encCNF falseCNF ∉ smallSAT 10 := fun h =>
  falseCNF_notMem_SAT ((mem_smallSAT (by decide)).mp h)

/-- The unconditional form: Ladner's language is in `NP`, in `P` only if `SAT` is, and
`NP`-complete only if `P = NP`. -/
example : SATH ∈ NP encBits ∧ (SATH ∈ P encBits → SAT ∈ P encCNF) ∧
    (NPComplete encBits SATH → P encBits = NP encBits) :=
  ⟨SATH_mem_NP, SAT_mem_P_of_SATH_mem_P, fun h => P_eq_NP_of_npComplete_SATH h encBits⟩

/-- Ladner's theorem for the canonical encoding of languages. -/
example (h : P encBits ≠ NP encBits) :
    ∃ L : Set (List Bool), L ∈ NP encBits ∧ L ∉ P encBits ∧ ¬NPComplete encBits L :=
  exists_NP_not_P_not_npComplete h

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.Ladner.computableInPolyTime_H' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.computableInPolyTime_H

/--
info: 'Cslib.Complexity.Ladner.SATH_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.SATH_mem_NP

/--
info: 'Cslib.Complexity.Ladner.exists_H_le_of_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.exists_H_le_of_mem_P

/--
info: 'Cslib.Complexity.Ladner.SAT_mem_P_of_SATH_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.SAT_mem_P_of_SATH_mem_P

/--
info: 'Cslib.Complexity.Ladner.SAT_mem_P_of_npHard_SATH' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.SAT_mem_P_of_npHard_SATH

/--
info: 'Cslib.Complexity.Ladner.SAT_mem_P_of_reducible_of_tendsto' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.SAT_mem_P_of_reducible_of_tendsto

/--
info: 'Cslib.Complexity.Ladner.P_eq_NP_of_SATH_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.P_eq_NP_of_SATH_mem_P

/--
info: 'Cslib.Complexity.Ladner.P_eq_NP_of_npComplete_SATH' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.P_eq_NP_of_npComplete_SATH

/--
info: 'Cslib.Complexity.Ladner.exists_NP_not_P_not_npComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Ladner.exists_NP_not_P_not_npComplete

end ComplexityTests.Ladner
