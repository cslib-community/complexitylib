/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AWPP
import Complexity.Computability.Complexity.Classes.AWPP.Amplification
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Uniform AWPP weights for bounded oracle queries

Amplify an AWPP numerator and pad its denominator to depend only on the original input.
Truncating every query gives uniform bounds even on replay states containing longer words.

## Main results

* `exists_AWPP_queryWeights`: amplified GapP query weights with an input-dependent common
  dyadic denominator and a polynomial-time unary denominator exponent.

## References

* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003].
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- AWPP query numerators can have a common denominator depending only on the original input.
Every query is truncated to the certified unary length cap, so the bounds hold for all words,
including arbitrary words occurring in a replay state. The requested error exponent is also
computed in unary and may be zero. -/
theorem exists_AWPP_queryWeights {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}
    (hA : A ∈ AWPP encBits) {T e : α → ℕ}
    (hT : ComputableInPolyTime T enc encUnary)
    (he : ComputableInPolyTime e enc encUnary) :
    ∃ H ∈ GapP (encPair enc encBits), ∃ R : α → ℕ,
      ComputableInPolyTime R enc encUnary ∧ ∀ a w,
        let D := (2 : ℤ) ^ R a
        (0 ≤ H (a, w) ∧ H (a, w) ≤ D) ∧
          (w.take (T a) ∈ A → (2 : ℤ) ^ e a * (D - H (a, w)) ≤ D) ∧
          (w.take (T a) ∉ A → (2 : ℤ) ^ e a * H (a, w) ≤ D) := by
  obtain ⟨g, hg, p, hA⟩ := hA
  let query : α × List Bool → List Bool := fun x => x.2.take (T x.1)
  have hquery : ComputableInPolyTime query (encPair enc encBits) encBits := by
    dsimp [query]
    fun_prop
  have he' : ComputableInPolyTime (fun x : α × List Bool => e x.1)
      (encPair enc encBits) encUnary := he.comp (.fst enc encBits)
  let H₀ : α × List Bool → ℤ := fun x => AWPPAmplification.majorityPolynomial
    (g (query x)) ((2 : ℤ) ^ p.eval (query x).length) (6 * e x.1)
  have hH₀ : H₀ ∈ GapP (encPair enc encBits) := by
    apply AWPPAmplification.majorityPolynomial_mem (GapP.comp_mem hg hquery)
    · simpa only [Function.comp_def, encBits_apply] using
        GapP.comp_mem (GapP.two_pow_mem (enc := encBits) p) hquery
    · fun_prop
  let padding : α × List Bool → ℕ := fun x =>
    12 * e x.1 * (p.eval (T x.1) - p.eval (query x).length)
  have hpadding : ComputableInPolyTime padding (encPair enc encBits) encUnary := by
    dsimp [padding]
    fun_prop
  have hpow : ComputableInPolyTime (fun x => 2 ^ padding x)
      (encPair enc encBits) encNat := by fun_prop
  let H : α × List Bool → ℤ := fun x => H₀ x * (2 : ℤ) ^ padding x
  have hH : H ∈ GapP (encPair enc encBits) := by
    convert GapP.mul_mem hH₀
      (SharpP.natCast_mem_GapP (mem_SharpP_of_polyTime hpow)) using 1
    ext x
    simp [H]
  refine ⟨H, hH, fun a => 12 * e a * p.eval (T a), by fun_prop, fun a w => ?_⟩
  obtain ⟨hb, hy, hn⟩ := hA (query (a, w))
  simp only [encBits_apply] at hb hy hn
  obtain ⟨hb', hy', hn'⟩ := AWPPAmplification.majorityPolynomial_bounds
    (e := e a) hb.1 hb.2
  let d : ℤ := 2 ^ (2 * (6 * e a) * p.eval (query (a, w)).length)
  let P : ℤ := 2 ^ padding (a, w)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hD : (2 : ℤ) ^ (12 * e a * p.eval (T a)) = d * P := by
    dsimp [d, P, padding]
    rw [← pow_add]
    congr 1
    have hlen : p.eval (query (a, w)).length ≤ p.eval (T a) :=
      p.eval_mono (List.length_take_le _ _)
    calc
      12 * e a * p.eval (T a) =
          12 * e a * (p.eval (query (a, w)).length +
            (p.eval (T a) - p.eval (query (a, w)).length)) := by
        rw [Nat.add_sub_of_le hlen]
      _ = _ := by ring
  change (0 ≤ H₀ (a, w) * P ∧ H₀ (a, w) * P ≤ _) ∧ _
  rw [hD]
  refine ⟨⟨mul_nonneg hb'.1 hP, mul_le_mul_of_nonneg_right hb'.2 hP⟩, ?_, ?_⟩
  · intro ha
    have h := mul_le_mul_of_nonneg_right (hy' (hy ha)) hP
    change (2 : ℤ) ^ e a * (d * P - H₀ (a, w) * P) ≤ d * P
    calc
      (2 : ℤ) ^ e a * (d * P - H₀ (a, w) * P) =
          ((2 : ℤ) ^ e a * (d - H₀ (a, w))) * P := by ring
      _ ≤ d * P := h
  · intro ha
    have h := mul_le_mul_of_nonneg_right (hn' (hn ha)) hP
    change (2 : ℤ) ^ e a * (H₀ (a, w) * P) ≤ d * P
    calc
      (2 : ℤ) ^ e a * (H₀ (a, w) * P) = ((2 : ℤ) ^ e a * H₀ (a, w)) * P :=
        (mul_assoc _ _ _).symm
      _ ≤ d * P := h

end Cslib.Complexity
