/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.ContractionCounting
import Complexity.Computability.Complexity.Problems.SharpThreeSAT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds

/-!
# Model counting by tensor contraction for unbounded clause width

One native machine computes the number of satisfying assignments `CNF.modelCount φ` of **every**
formula `φ` in conjunctive normal form, with no bound on the width of its clauses, in time
`2 ^ (A (N + 1) / √⌊log₂ (N + 2)⌋)` times a polynomial in the encoding length and in polynomial
space, where `N` is the number of literal occurrences of `φ` (`φ.vars.length`)
(`ContractionCounting.exists_modelCounter_unboundedWidth`). For formulas with at most `D n` literal
occurrences on `n` variables this is `2 ^ O_D(n / √log n)` times a polynomial
(`ContractionCounting.exists_modelCounter_unboundedWidth_linearLength`), so sparse formulas are
counted in time `2 ^ o(n)` even when their clauses are long.

**The machine.** It splits every clause into binary OR gates (`Cslib.Complexity.toSharpThreeSAT`,
the count-preserving split of §2.8 of [OpenAI2026ETH], p. 18). The result has clauses of at most
three literals, the same number of satisfying assignments, and between `N` and `7 N` literal
occurrences (`Cslib.Complexity.length_vars_toSharpThreeSAT`). Then it runs the contraction counter
for width three (`ContractionCounting.exists_modelCounter_occurrences`), whose exponent is
`O(N / √log N)` in the number of literal occurrences.

After the split, every vertex of the contracted network has at most four ports and an explicit
table, so the form of Theorem D.1 with entries computed by procedures, which allows degree
`⌈s ^ (9/10)⌉`, is not needed; without a split it would not cover clauses wider than that bound
either.

**Source relation.** Theorem 1.1 of [OpenAI2026ETH] (p. 2) is stated for `k`-CNF with fixed `k`,
in terms of the numbers of variables and clauses; its fixed-density case is proved in Appendix D.2
(p. 54) from Theorem D.1 (p. 53). The bound here, for unbounded width and in terms of the number of
literal occurrences, combines that proof with the split of §2.8; the combination is a library
extension, not a statement of the manuscript.

## Main results

* `Cslib.Complexity.ContractionCounting.exists_modelCounter_unboundedWidth`: the counter for every
  formula, with exponent `A (N + 1) / √⌊log₂ (N + 2)⌋`.
* `Cslib.Complexity.ContractionCounting.exists_modelCounter_unboundedWidth_linearLength`: for each
  `D`, exponent `A (n + 1) / √⌊log₂ (n + 2)⌋` on formulas with at most `D n` literal occurrences.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem 1.1 (p. 2),
  §2.8 (p. 18), Theorem D.1 (p. 53) and Appendix D.2 (p. 54).
-/

public section

namespace Cslib.Complexity.ContractionCounting

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The exponent after splitting: between `N` and `7 N` literal occurrences, the exponent
`A (N' + 1) / √⌊log₂ (N' + 2)⌋` is at most `7 A (N + 1) / √⌊log₂ (N + 2)⌋`. -/
private theorem exponent_le_of_le {A N N' : ℕ} (h₁ : N ≤ N') (h₂ : N' ≤ 7 * N) :
    A * (N' + 1) / Nat.sqrt (Nat.log 2 (N' + 2)) ≤
      7 * A * (N + 1) / Nat.sqrt (Nat.log 2 (N + 2)) := by
  refine Nat.div_le_div ?_ (Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega))) ?_
  · have : A * (N' + 1) ≤ A * (7 * (N + 1)) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · exact Nat.sqrt_eq_zero.not.mpr (Nat.log_pos (by norm_num) (by omega)).ne'

/-- **Model counting by tensor contraction for unbounded clause width.** One machine computes
`φ.modelCount` on every formula `φ`, in time `2 ^ (A (N + 1) / √⌊log₂ (N + 2)⌋)` times a
polynomial in the encoding length and in polynomial space, where `N` is the number of literal
occurrences of `φ`. -/
theorem exists_modelCounter_unboundedWidth :
    ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CNF ℕ, count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat
        (fun φ => 2 ^ (A * (φ.vars.length + 1) / Nat.sqrt (Nat.log 2 (φ.vars.length + 2))) *
          ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_modelCounter_occurrences 3
  obtain ⟨d, _, hdeg⟩ := computableInPolyTime_toSharpThreeSAT.exists_degree
  obtain ⟨p, q, hlen⟩ := computableInPolyTime_toSharpThreeSAT.polyBounded_length.exists_le
  refine ⟨fun φ => count (toSharpThreeSAT φ), 7 * A, d + q * e, d + q * b,
    fun φ => (hcount _ fun _ hc => length_le_three_of_mem_toSharpThreeSAT hc).trans
      (modelCount_toSharpThreeSAT φ),
    (hc.comp' hdeg.inO).mono ((p + 1) ^ e + (p + 1) ^ b + 1) (fun φ => ?_) (fun φ => ?_)⟩
  all_goals
    obtain ⟨Y, hY⟩ : ∃ Y, Y = (encCNF φ).length + 1 := ⟨_, rfl⟩
    have hY1 : 1 ≤ Y := by omega
    have hψ : (encCNF (toSharpThreeSAT φ)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encCNF (toSharpThreeSAT φ)).length ≤ p * Y ^ q := by rw [hY]; exact hlen φ
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      nlinarith
    have hψpow (c : ℕ) : ((encCNF (toSharpThreeSAT φ)).length + 1) ^ c ≤
        (p + 1) ^ c * Y ^ (q * c) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ c := Nat.pow_le_pow_left hψ c
        _ = _ := by rw [mul_pow, pow_mul]
    simp only [← hY]
  · -- time
    obtain ⟨E, hE⟩ : ∃ E, E = 7 * A * (φ.vars.length + 1) / Nat.sqrt (Nat.log 2
      (φ.vars.length + 2)) := ⟨_, rfl⟩
    rw [← hE]
    obtain ⟨hN₁, hN₂⟩ := length_vars_toSharpThreeSAT φ
    have hexp := hE ▸ exponent_le_of_le (A := A) hN₁ hN₂
    have h2E : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    have hd : Y ^ d ≤ 2 ^ E * Y ^ (d + q * e) :=
      (Nat.pow_le_pow_right hY1 (by omega)).trans (Nat.le_mul_of_pos_left _ h2E)
    have hc' : 2 ^ (A * ((toSharpThreeSAT φ).vars.length + 1) /
        Nat.sqrt (Nat.log 2 ((toSharpThreeSAT φ).vars.length + 2))) *
          ((encCNF (toSharpThreeSAT φ)).length + 1) ^ e ≤
        (p + 1) ^ e * (2 ^ E * Y ^ (d + q * e)) :=
      calc _ ≤ 2 ^ E * ((p + 1) ^ e * Y ^ (q * e)) :=
            Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hexp) (hψpow e)
        _ ≤ 2 ^ E * ((p + 1) ^ e * Y ^ (d + q * e)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega)))
        _ = (p + 1) ^ e * (2 ^ E * Y ^ (d + q * e)) := by ring
    calc _ ≤ 2 ^ E * Y ^ (d + q * e) + (p + 1) ^ e * (2 ^ E * Y ^ (d + q * e)) :=
          Nat.add_le_add hd hc'
      _ = (1 + (p + 1) ^ e) * (2 ^ E * Y ^ (d + q * e)) := by ring
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.le_succ _)
  · -- space
    have hd : Y ^ d ≤ Y ^ (d + q * b) := Nat.pow_le_pow_right hY1 (by omega)
    have hb : ((encCNF (toSharpThreeSAT φ)).length + 1) ^ b ≤ (p + 1) ^ b * Y ^ (d + q * b) :=
      (hψpow b).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega)))
    calc _ ≤ Y ^ (d + q * b) + (p + 1) ^ b * Y ^ (d + q * b) := Nat.add_le_add hd hb
      _ = (1 + (p + 1) ^ b) * Y ^ (d + q * b) := by ring
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.le_succ _)

/-- **Linearly many literal occurrences.** One machine computes `φ.modelCount` on every formula
`φ`, in polynomial space, and for each `D` its time on formulas with at most `D n` literal
occurrences, for `n` variables, is `2 ^ (A (n + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the
encoding length. The machine, its time and space functions and the degree `e` of the polynomial
are fixed before `D`; only `A` depends on `D`. -/
theorem exists_modelCounter_unboundedWidth_linearLength :
    ∃ (count : CNF ℕ → ℕ) (T S : CNF ℕ → ℕ) (e b : ℕ),
      (∀ φ : CNF ℕ, count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat T S ∧
      (∀ φ, S φ = ((encCNF φ).length + 1) ^ b) ∧
      ∀ D : ℕ, ∃ A : ℕ, ∀ φ : CNF ℕ, φ.vars.length ≤ D * φ.numVars →
        T φ ≤ 2 ^ (A * (φ.numVars + 1) / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) *
          ((encCNF φ).length + 1) ^ e := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_modelCounter_unboundedWidth
  refine ⟨count, _, _, e, b, hcount, hc, fun _ => rfl, fun D => ⟨A * (D + 1), fun φ hφ => ?_⟩⟩
  refine Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) ?_)
  have hn := CNF.numVars_le_length_vars φ
  refine Nat.div_le_div ?_ (Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega)))
    (Nat.sqrt_eq_zero.not.mpr (Nat.log_pos (by norm_num) (by omega)).ne')
  have : φ.vars.length + 1 ≤ (D + 1) * (φ.numVars + 1) := by nlinarith
  calc A * (φ.vars.length + 1) ≤ A * ((D + 1) * (φ.numVars + 1)) := Nat.mul_le_mul_left _ this
    _ = A * (D + 1) * (φ.numVars + 1) := by ring

end Cslib.Complexity.ContractionCounting
