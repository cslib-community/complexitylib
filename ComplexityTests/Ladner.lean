/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Ladner

/-! Words by index, padding and its inverse on boundary words, capped powers, decoding formulas,
short satisfiability by certificates, concrete members and non-members of Ladner's language, a
concrete machine agreeing and disagreeing with it, the padding reduction and the rounds of the
self-reduction on concrete formulas. -/

namespace ComplexityTests.Ladner

open Cslib Cslib.Complexity Cslib.Complexity.Ladner Cslib.Logic.PL Turing Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal

/-! ### Words by index -/

example :
    word 0 = [] ∧
      word 1 = [false] ∧
      word 2 = [true] ∧
      word 3 = [false, false] ∧
      word 6 = [true, true] ∧
      index [] = 0 ∧
      index [true, false] = 4 ∧
      word (index [true, false, true]) = [true, false, true] ∧
      2 ^ (word 6).length ≤ 7 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, word_index _, two_pow_length_word_le 6⟩

/-! ### Padding -/

/-- Only the last `false` separates; without a `false`, the second component is the length; and
`unpad` inverts `pad`. -/
example :
    pad [true] 2 = [true, false, true, true] ∧
      unpad [true, false, true, true] = ([true], 2) ∧
      unpad [false, false, true] = ([false], 1) ∧
      unpad [true, true] = ([], 2) ∧
      unpad (pad [true, false] 3) = ([true, false], 3) :=
  ⟨rfl, by decide, by decide, by decide, unpad_pad [true, false] 3⟩

/-! ### Capped powers -/

example :
    capPow 3 2 100 = 9 ∧
      capPow 2 10 100 = 100 ∧
      capPow 0 0 5 = 1 ∧
      capPow 7 3 0 = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### Formulas and short satisfiability -/

/-- Decoding round-trips on encoded formulas and maps `[]` to `[]`; `bruteSAT` finds short
certificates when they exist. -/
example :
    decodeCNF (encCNF [[(3, true)], []]) = [[(3, true)], []] ∧
      decodeCNF [] = [] ∧
      bruteSAT 3 [[(5, false)]] = true ∧
      bruteSAT 8 [[]] = false :=
  ⟨decodeCNF_encCNF _, by simp [decodeCNF, Complexity.cnfDecoder, Decoder.list],
    by decide, by decide⟩

/-! ### Ladner's language -/

theorem H_zero : H 0 = 0 := Nat.le_zero.mp (H_le 0)

/-- The empty formula, padded with `0 ^ H 0 = 1` one, is in Ladner's language. -/
theorem false_true_mem_SATH : [false, true] ∈ SATH := by
  have h : [false, true] = pad (encCNF []) ((encCNF []).length ^ H (encCNF []).length) := by
    simp [encCNF, pad, H_zero]
  rw [h]
  exact ⟨[], ⟨fun _ => true, rfl⟩, rfl⟩

/-- Words without a separating `false` and padded unsatisfiable formulas lie outside `SATH`, while
`H (2 ^ 2 ^ 3) ≤ 3`. -/
example (k : ℕ) :
    [true, true] ∉ SATH ∧
      pad (encCNF [[]]) k ∉ SATH ∧
      H (2 ^ 2 ^ 3) ≤ 3 := by
  refine ⟨?_, ?_,
    (H_le _).trans (by rw [Nat.log_pow one_lt_two, Nat.log_pow one_lt_two])⟩
  · rintro ⟨φ, -, h⟩
    have : false ∈ pad (encCNF φ) ((encCNF φ).length ^ H (encCNF φ).length) := by simp [pad]
    rw [← h] at this
    simp at this
  · rw [SATH, pad_mem_padSAT_iff]
    rintro ⟨⟨σ, hσ⟩, -⟩
    simp [CNF.eval, Clause.eval] at hσ

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

/-! ### Boundary cases of the padding reduction and finite table -/

/-- The padding reduction on the empty formula, for every exponent bound. -/
example (C : ℕ) : padBounded C [] = [false, true] := by
  simp [padBounded, encCNF, capPow, H_zero, pad]

/-- A round of the self-reduction keeps short formulas for every candidate reduction. -/
example (R : CNF ℕ → List Bool) : shrink R 1 [] = [] := by
  simp [shrink, encCNF]

/-- The empty formula is accepted and an unsatisfiable formula is rejected by the finite table. -/
example :
    falseCNF ∉ SAT ∧
      encCNF [] ∈ smallSAT 1 ∧
      encCNF falseCNF ∉ smallSAT 10 :=
  ⟨falseCNF_notMem_SAT,
    (mem_smallSAT (by simp [encCNF])).mpr ⟨fun _ => true, rfl⟩,
    fun h => falseCNF_notMem_SAT ((mem_smallSAT (by decide)).mp h)⟩

end ComplexityTests.Ladner
