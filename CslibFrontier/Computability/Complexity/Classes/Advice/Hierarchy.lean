/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Advice.LengthComparison
import CslibFrontier.Computability.Complexity.Classes.P.Countable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Data.Fintype.Card

/-!
# Strict exact-advice hierarchies

Strict pointwise growth of arbitrary advice lengths gives strict containment when the upper
length is eventually at most the number of inputs. The bounds and advice need not be computable.
A fixed native polynomial-time decoder reads a bit of the advice at the zero-based,
most-significant-bit-first binary input index. This reindexes the source's `1..2^n` inputs.
Its unary index accumulator is capped by the advice length, so even very large binary indices
cost polynomial time in the full encoded advice/input pair.

This generalizes the fixed-one-bit argument of the official tighter Theorem 4.1 addendum
[GoldreichAdviceHierarchyAddendum]. A countable enumeration of native P predicates replaces
machine enumeration. Each predicate fails at one assigned length, sufficient for the exact
(no exceptional inputs) convention explicitly discussed in the addendum. The capacity condition
is only eventual; no restriction on the empty-input slice is needed. Strict positivity of the
length increase is explicit, as required by the exact-length model qualification in
[Goldreich2007DraftR2], Exercise 3.3 / Theorem 4.1. Exercise 3.3 places the upper-capacity
restriction in its guideline; this theorem does not drop that restriction.

## Main results

* `Cslib.Complexity.PWithAdvice_ssubset_of_lt`: a strict hierarchy under eventual capacity.
* `Cslib.Complexity.PWithAdvice_pred_ssubset`: the positive fixed-one-bit hierarchy.
* `Cslib.Complexity.PWithAdvice_const_ssubset_succ`: strictness at every constant advice length.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Strictly larger exact advice bounds give strict containment when the upper bound is
at most the truth-table size at all sufficiently large lengths. Neither bound is assumed
computable. The running-time convention is polynomial in the complete advice/input pair. -/
theorem PWithAdvice_ssubset_of_lt {lower upper : ℕ → ℕ}
    (hlt : ∀ n, lower n < upper n)
    (hcap : ∀ᶠ n in Filter.atTop, upper n ≤ 2 ^ n) :
    PWithAdvice lower ⊂ PWithAdvice upper := by
  classical
  obtain ⟨N, hcap⟩ := Filter.eventually_atTop.mp hcap
  obtain ⟨predicates, hpredicates⟩ :=
    (countable_P (encPair encBits encBits)).exists_eq_range ⟨∅, empty_mem_P⟩
  let observations (j : ℕ) (a : Fin (lower (j + N)) → Bool)
      (i : Fin (upper (j + N))) : Bool :=
    decide ((List.ofFn a, BitString.binaryWord (j + N) i.val) ∈ predicates j)
  have hmissing (j : ℕ) : ∃ b : Fin (upper (j + N)) → Bool,
      ∀ a, observations j a ≠ b := by
    by_contra! h
    have hc := Fintype.card_le_of_surjective (observations j) h
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
    exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (hlt (j + N))).not_ge hc
  choose missing hmissing using hmissing
  let advice (n : ℕ) : List Bool :=
    if h : N ≤ n then List.ofFn (missing (n - N)) else List.replicate (upper n) false
  have hlength (n : ℕ) : (advice n).length = upper n := by
    dsimp only [advice]
    split_ifs with h
    · simp only [List.length_ofFn]
      congr 1
      omega
    · exact List.length_replicate
  let lookup (p : List Bool × List Bool) : Bool :=
    p.1.getD (BitString.boundedBinaryValue p.1.length p.2) false
  have hlookup : ComputableInPolyTime lookup (encPair encBits encBits) encBool := by
    exact ComputableInPolyTime.bitsGetDWithInput (by fun_prop)
      (ComputableInPolyTime.bitsBoundedBinaryValueWithInput
        (ComputableInPolyTime.length_bits_comp (by fun_prop)) (by fun_prop)) false
  let L : Set (List Bool) := {x | lookup (advice x.length, x) = true}
  have hL : L ∈ PWithAdvice upper :=
    ⟨advice, hlength, {p | lookup p = true},
      ⟨lookup, hlookup, fun _ => Iff.rfl⟩, fun _ => Iff.rfl⟩
  have hnot : L ∉ PWithAdvice lower := by
    rintro ⟨otherAdvice, hother, A, hA, hLA⟩
    rw [hpredicates] at hA
    obtain ⟨j, hj⟩ := hA
    let a : Fin (lower (j + N)) → Bool := fun i =>
      (otherAdvice (j + N))[i.val]'(by rw [hother]; exact i.isLt)
    have ha : List.ofFn a = otherAdvice (j + N) := by
      apply List.ext_getElem (by simp [hother])
      intro i hi hi'
      simp [a]
    apply hmissing j a
    funext i
    have hi : i.val < 2 ^ (j + N) := i.isLt.trans_le (hcap _ (by omega))
    have hw := BitString.length_binaryWord hi
    have hadvice : advice (j + N) = List.ofFn (missing j) := by
      dsimp only [advice]
      rw [dite_eq_left (show N ≤ j + N by omega), Nat.add_sub_cancel]
    have heval : lookup (advice (j + N), BitString.binaryWord (j + N) i.val) =
        decide ((otherAdvice (j + N), BitString.binaryWord (j + N) i.val) ∈ predicates j) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [L, Set.mem_ofPred_eq, hw, ← hj, decide_eq_true_eq] using
        hLA (BitString.binaryWord (j + N) i.val)
    simpa [observations, ha, lookup, hadvice, BitString.boundedBinaryValue_eq,
      Nat.min_eq_right i.isLt.le] using heval.symm
  exact Set.ssubset_iff_subset_ne.mpr ⟨PWithAdvice_subset_of_lt hlt,
    fun heq => hnot (heq.symm ▸ hL)⟩

/-- The official fixed-one-bit hierarchy, with positivity explicit so natural subtraction
really removes a bit. The truth-table capacity is needed only eventually. -/
theorem PWithAdvice_pred_ssubset {length : ℕ → ℕ} (hpos : ∀ n, 0 < length n)
    (hcap : ∀ᶠ n in Filter.atTop, length n ≤ 2 ^ n) :
    PWithAdvice (fun n => length n - 1) ⊂ PWithAdvice length :=
  PWithAdvice_ssubset_of_lt (fun n => Nat.sub_lt (hpos n) (by decide)) hcap

/-- Every fixed number of advice bits is strictly weaker than one more bit. This includes
zero bits, and imposes no truth-table-capacity condition on the finitely many short lengths. -/
theorem PWithAdvice_const_ssubset_succ (k : ℕ) :
    PWithAdvice (fun _ => k) ⊂ PWithAdvice (fun _ => k + 1) :=
  PWithAdvice_ssubset_of_lt (fun _ => Nat.lt_succ_self _) <|
    Filter.eventually_atTop.mpr ⟨k + 1, fun _ hn => hn.trans (Nat.lt_two_pow_self.le)⟩

end Cslib.Complexity
