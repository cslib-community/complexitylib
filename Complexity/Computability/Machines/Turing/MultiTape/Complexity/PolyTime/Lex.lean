/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Mathlib.Data.List.Lex
import Complexity.Foundations.Data.List.Lex
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Lexicographic comparison of bit strings in polynomial time

Mathlib's lexicographic order on `List Bool` (`false < true`, and a proper prefix comes first) is
decidable in polynomial time on raw bit strings (`encBits`): find the first position where the
strings differ, and compare there, or compare the lengths if there is none.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bits_lex_le`,
  `Turing.MultiTapeTM.ComputableInPolyTime.bits_lex_le`: `decide (x ≤ y)` for the lexicographic
  order on bit strings is polynomial-time.
-/

public section

namespace Turing.MultiTapeTM

/-- Lexicographic comparison: at the first position where `x` and `y` differ, `x ≤ y` when `x`
has `false`; if they agree up to the shorter length, `x ≤ y` when `x` is no longer. -/
private def lexLe (x y : List Bool) : Bool :=
  ((x.zip y).find? fun p => p.1 != p.2).elim (decide (x.length ≤ y.length)) fun p => !p.1

private theorem lexLe_eq_decide (x y : List Bool) : lexLe x y = decide (x ≤ y) := by
  induction x generalizing y with
  | nil =>
    simp only [lexLe, List.zip_nil_left, List.find?_nil, Option.elim_none, List.length_nil,
      Nat.zero_le, decide_true]
    exact (decide_eq_true (List.isPrefix_le List.nil_prefix)).symm
  | cons a x ih =>
    cases y with
    | nil =>
      simp only [lexLe, List.zip_nil_right, List.find?_nil, Option.elim_none, List.length_cons,
        List.length_nil, Nat.le_zero, Nat.add_one_ne_zero, decide_false]
      symm
      rw [decide_eq_false_iff_not, not_le]
      exact List.Lex.nil
    | cons b y =>
      rw [Bool.eq_iff_iff, decide_eq_true_iff, List.cons_le_cons_iff',
        ← decide_eq_true_iff (p := x ≤ y), ← ih y]
      simp only [lexLe, List.zip_cons_cons, List.find?_cons, List.length_cons,
        Nat.add_le_add_iff_right]
      cases a <;> cases b <;> simp

namespace ComputableTidilyInPolyTime

/-- **Lexicographic comparison of bit strings** is polynomial-time. -/
theorem bits_lex_le :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => decide (p.1 ≤ p.2))
      (encPair encBits encBits) encBool := by
  have hzip : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => p.1.zip p.2)
      (encPair encBits encBits) (encList (encPair encBool encBool)) :=
    (zip encBool encBool).comp ((bitsToList.comp (fst _ _)).prod (bitsToList.comp (snd _ _)))
  have hfind := findWithInput (test := fun (_ : List Bool × List Bool) (q : Bool × Bool) =>
    q.1 != q.2) hzip ((of_finite fun q : Bool × Bool => q.1 != q.2).comp (snd _ _))
  have hlen : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length))
      (encPair encBits encBits) encBool := by
    fun_prop
  have h := optionElimWithInput (body := fun _ q => !q.1) hfind hlen
    ((of_finite fun q : Bool × Bool => !q.1).comp (snd _ _))
  convert h using 2 with p
  rw [← lexLe_eq_decide, lexLe]

end ComputableTidilyInPolyTime

/-- **Lexicographic comparison of bit strings** is polynomial-time. -/
theorem ComputableInPolyTime.bits_lex_le :
    ComputableInPolyTime (fun p : List Bool × List Bool => decide (p.1 ≤ p.2))
      (encPair encBits encBits) encBool :=
  .of_tidy ComputableTidilyInPolyTime.bits_lex_le

end Turing.MultiTapeTM
