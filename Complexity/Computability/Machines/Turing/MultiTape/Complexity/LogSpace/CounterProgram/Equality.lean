/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# Equality in logarithmic space

Compare two encoded words by rereading their bits with two counters, without storing either
word. The counters are bounded by the input length. This supplies equality for the active
self-query test in bounded truth-table autoreductions.

## Main results

* `Turing.MultiTapeTM.ComputableInLogSpace.equal`: equality of two computed encoded instances.
-/

public section

namespace Turing.CounterProgram

open Instr Expr MultiTapeTM

private def equalityProgram : CounterProgram where
  code :=
    [read (mul (const 2) (reg 0)) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0,
     read (mul (const 2) (reg 1)) 3 6 6,
     read (add (mul (const 2) (reg 1)) (const 1)) 4 5 9,
     read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 7 9 9,
     read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 9 7 9,
     read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 9 9 8,
     assign 1 (add (reg 1) (const 1)) 2,
     accept, reject]
  registers := 2

private theorem marker (u v : List Bool) {i : ℕ} (hi : i < u.length) :
    (frame u ++ v)[2 * i]? = some true := by
  rw [List.getElem?_append_left (by rw [length_frame]; omega), getElem?_frame_two_mul hi]

private theorem ending (u v : List Bool) :
    (frame u ++ v)[2 * u.length]? = some false := by
  rw [List.getElem?_append_left (by rw [length_frame]; omega), getElem?_frame_two_mul_length]

private theorem bit (u v : List Bool) {i : ℕ} (hi : i < u.length) :
    (frame u ++ v)[2 * i + 1]? = u[i]? := by
  rw [List.getElem?_append_left (by rw [length_frame]; omega), getElem?_frame_two_mul_add_one hi]

private theorem tailBit (u v : List Bool) (i : ℕ) :
    (frame u ++ v)[2 * u.length + 1 + i]? = v[i]? := by
  rw [List.getElem?_append_right (by rw [length_frame]; omega)]
  simp [length_frame]

private theorem bounded {a b B : ℕ} (ha : a ≤ B) (hb : b ≤ B) :
    ∀ r ∈ [a, b], r ≤ B := by simp_all

private theorem equality_run (u v : List Bool) {B : ℕ}
    (hB : u.length + 1 ≤ B) :
    ∃ s, equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
      equalityProgram.init s ∧
      equalityProgram.instr s.1 = .halt (encBool (decide (u = v))) ∧
      ∀ r ∈ s.2, r ≤ B := by
  have scan : ∀ i ≤ u.length,
      equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
        (0, [i, 0]) (2, [u.length, 0]) := by
    intro i hi
    induction h : u.length - i generalizing i with
    | zero =>
      have : i = u.length := by omega
      subst i
      apply Reaches.read (by rfl) (bounded (by omega) (by omega))
      simpa [ending, readLabel] using Reaches.refl (2, [u.length, 0])
    | succ n ih =>
      apply Reaches.read (by rfl) (bounded (by omega) (by omega))
      simp only [eval_mul, eval_const, eval_reg, List.getD_cons_zero,
        marker u v (show i < u.length by omega), readLabel]
      apply Reaches.assign (by rfl) (bounded (by omega) (by omega))
      simpa using ih (i + 1) (by omega) (by omega)
  have loop : ∀ i ≤ u.length, ∃ s,
      equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
        (2, [u.length, i]) s ∧
      equalityProgram.instr s.1 = .halt (encBool (decide (u.drop i = v.drop i))) ∧
      ∀ r ∈ s.2, r ≤ B := by
    intro i hi
    induction h : u.length - i generalizing i with
    | zero =>
      have heq : i = u.length := by omega
      subst i
      have hregs := bounded (B := B) (a := u.length) (b := u.length) (by omega) (by omega)
      by_cases hv : u.length < v.length
      · refine ⟨(9, [u.length, u.length]), ?_, ?_, hregs⟩
        · apply Reaches.read (by rfl) hregs
          simp only [eval_mul, eval_const, eval_reg, List.getD_cons_succ, List.getD_cons_zero,
            ending, readLabel]
          apply Reaches.read (by rfl) hregs
          simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
            List.getD_cons_succ, tailBit]
          rw [List.getElem?_eq_getElem hv]
          cases v[u.length] <;> exact Reaches.refl _
        · have : v.drop u.length ≠ [] := by simp [List.drop_eq_nil_iff, hv.not_ge]
          simp [List.drop_length, this, equalityProgram, instr, Instr.reject, encBool_apply]
      · refine ⟨(8, [u.length, u.length]), ?_, ?_, hregs⟩
        · apply Reaches.read (by rfl) hregs
          simp only [eval_mul, eval_const, eval_reg, List.getD_cons_succ, List.getD_cons_zero,
            ending, readLabel]
          apply Reaches.read (by rfl) hregs
          simpa [tailBit, List.getElem?_eq_none (by omega : v.length ≤ u.length), readLabel]
            using (Reaches.refl (P := equalityProgram) (w := frame u ++ v)
              (Q := equalityProgram.Running B) (8, [u.length, u.length]))
        · simp [List.drop_eq_nil_iff.mpr (by omega : v.length ≤ u.length), equalityProgram,
            instr, Instr.accept, encBool_apply]
    | succ n ih =>
      have hiu : i < u.length := by omega
      have hregs := bounded (B := B) (a := u.length) (b := i) (by omega) (by omega)
      have hstep : equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
          (2, [u.length, i])
          (if u[i] then 4 else 5, [u.length, i]) := by
        apply Reaches.read (by rfl) hregs
        simp only [eval_mul, eval_const, eval_reg, List.getD_cons_succ, List.getD_cons_zero,
          marker u v hiu, readLabel]
        apply Reaches.read (by rfl) hregs
        simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_succ,
          List.getD_cons_zero, bit u v hiu, List.getElem?_eq_getElem hiu]
        cases u[i] <;> exact Reaches.refl _
      by_cases hv : i < v.length
      · by_cases heq : u[i] = v[i]
        · obtain ⟨s, hs, hout, hb⟩ := ih (i + 1) (by omega) (by omega)
          refine ⟨s, hstep.trans ?_, ?_, hb⟩
          · have hnext : equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
                (7, [u.length, i]) s := by
              apply Reaches.assign (by rfl) hregs
              simpa using hs
            cases hu : u[i] <;> simp only [Bool.false_eq_true, ↓reduceIte]
            all_goals
              apply Reaches.read (by rfl) hregs
              simpa [tailBit, List.getElem?_eq_getElem hv, ← heq, hu, readLabel] using hnext
          · have hd : u.drop i = v.drop i ↔ u.drop (i + 1) = v.drop (i + 1) := by
              rw [← List.cons_getElem_drop_succ (l := u) (n := i) (h := hiu),
                ← List.cons_getElem_drop_succ (l := v) (n := i) (h := hv)]
              rw [List.cons.injEq]
              exact and_iff_right heq
            simpa only [hd] using hout
        · refine ⟨(9, [u.length, i]), hstep.trans ?_, ?_, hregs⟩
          · cases hu : u[i] <;> simp only [Bool.false_eq_true, ↓reduceIte]
            all_goals
              apply Reaches.read (by rfl) hregs
              have hvb : v[i] = !u[i] := by
                apply Bool.eq_not_iff.mpr
                exact Ne.symm heq
              simpa [tailBit, List.getElem?_eq_getElem hv, hvb, hu, readLabel]
                using (Reaches.refl (P := equalityProgram) (w := frame u ++ v)
                  (Q := equalityProgram.Running B) (9, [u.length, i]))
          · have hd : u.drop i ≠ v.drop i := by
              rw [← List.cons_getElem_drop_succ (l := u) (n := i) (h := hiu),
                ← List.cons_getElem_drop_succ (l := v) (n := i) (h := hv)]
              intro hdrop
              exact heq (List.cons.inj hdrop).1
            simp [hd, equalityProgram, instr, Instr.reject, encBool_apply]
      · refine ⟨(9, [u.length, i]), hstep.trans ?_, ?_, hregs⟩
        · cases hu : u[i] <;> simp only [Bool.false_eq_true, ↓reduceIte]
          all_goals
            apply Reaches.read (by rfl) hregs
            simpa [tailBit, List.getElem?_eq_none (by omega : v.length ≤ i), readLabel]
              using (Reaches.refl (P := equalityProgram) (w := frame u ++ v)
                (Q := equalityProgram.Running B) (9, [u.length, i]))
        · have hd : u.drop i ≠ v.drop i := by
            rw [List.drop_eq_nil_iff.mpr (by omega : v.length ≤ i)]
            simp [List.drop_eq_nil_iff, hiu.not_ge]
          simp [hd, equalityProgram, instr, Instr.reject, encBool_apply]
  obtain ⟨s, hs, hout, hb⟩ := loop 0 (Nat.zero_le _)
  exact ⟨s, (scan 0 (Nat.zero_le _)).trans hs, by simpa using hout, hb⟩

private theorem equality_logspace :
    ComputableInLogSpace (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool := by
  apply equalityProgram.computableInLogSpace_of_reaches 1
  intro p
  apply equality_run p.1 p.2
  rw [pow_one, encPair_apply]
  change p.1.length + 1 ≤ (frame p.1 ++ p.2).length + 1
  rw [List.length_append, length_frame]
  omega

end Turing.CounterProgram

namespace Turing.MultiTapeTM.ComputableInLogSpace

/-- Equality of two logspace-computed instances, by injectivity of their common encoding. -/
@[fun_prop]
theorem equal {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool} [DecidableEq β]
    {f g : α → β} (hf : ComputableInLogSpace f encIn enc)
    (hg : ComputableInLogSpace g encIn enc) :
    ComputableInLogSpace (fun a => decide (f a = g a)) encIn encBool := by
  have hw := CounterProgram.equality_logspace.comp (pair
    (hf.congr (g := fun a => enc (f a)) fun _ => rfl)
    (hg.congr (g := fun a => enc (g a)) fun _ => rfl))
  exact hw.congr_fun fun a => by simp [enc.injective.eq_iff]

end Turing.MultiTapeTM.ComputableInLogSpace
