/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
import CslibFrontier.Computability.Circuit.Complexity

/-!
# The Nisan–Wigderson generator fools small circuits

This file adds circuit sizes to the reconstruction of
`Cslib.Crypto.PRG.NisanWigderson.exists_dependsOn_half_add_div_le_card_nextBitGuess_eq`. The
function reconstructed from a deterministic test runs the test on `i` functions of at most `a`
input bits each, on constants, and possibly negates the result. A function of at most `a` input
bits costs at most `2 ^ a (2 a + 3) + 1` De Morgan gates
(`Cslib.Circuits.Boolean.complexity_le_of_dependsOn`), so if the test is computed with `S` gates,
the reconstructed function is computed with at most `S + m (2 ^ a (2 a + 3) + 1) + 1` gates
(`exists_complexity_le_half_add_div_le_card_eq`). Contrapositively, if no circuit of that size
agrees with `f` on a `1 / 2 + ε / m` fraction of the inputs, then no test computed with `S` gates
accepts outputs of the generator with probability `ε` more than uniform strings
(`toReal_realExperiment_sub_toReal_idealExperiment_lt`). Gates are counted as in
`Cslib.Circuits.complexity` over the De Morgan basis, constants and negations included.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.exists_complexity_le_half_add_div_le_card_eq`: a test of
  circuit complexity `S` distinguishing the generator with advantage `ε` yields a circuit of
  complexity at most `S + m (2 ^ a (2 a + 3) + 1) + 1` agreeing with `f` on a `1 / 2 + ε / m`
  fraction of the inputs.
* `Cslib.Crypto.PRG.NisanWigderson.toReal_realExperiment_sub_toReal_idealExperiment_lt`: the
  generator fools circuits with `S` gates if `f` is hard to approximate with
  `S + m (2 ^ a (2 a + 3) + 1) + 1` gates.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 20
-/

@[expose] public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Cslib.Circuits Cslib.Circuits.Boolean Finset

variable {ℓ n a m : ℕ}

/-- The guess of the predictor built from a test, with fixed random choices and with the first
`i` bits computed by functions of complexity at most `B ≥ 1`, costs at most the test, `m * B`, and
one gate. -/
private theorem complexity_nextBitGuess_le (test : BooleanFunction m) (i : Fin m) (r : Bool)
    (u : Fin m → Bool) (bit : Fin i → BooleanFunction n) {B : ℕ} (hB : 1 ≤ B)
    (hbit : ∀ j, complexity interpretation (single (bit j)) ≤ B) :
    complexity interpretation (single fun x => nextBitGuess test i r u fun j => bit j x) ≤
      complexity interpretation (single test) + m * B + 1 := by
  let q : Fin m → BooleanFunction n := fun j x =>
    if h : (j : ℕ) < i then bit ⟨j, h⟩ x else if j = i then r else u j
  have hq (j : Fin m) : complexity interpretation (single (q j)) ≤ B := by
    by_cases h : (j : ℕ) < i
    · simpa only [q, dite_eq_left h] using hbit ⟨j, h⟩
    · simp only [q, dite_eq_right h]
      exact (Synthesis.const _).complexity_le.trans hB
  have htest : complexity interpretation (single fun x => test fun j => q j x) ≤
      complexity interpretation (single test) + m * B := by
    calc _ ≤ complexity interpretation (fun x j => q j x) +
          complexity interpretation (single test) := complexity_comp_le _ (single test)
      _ ≤ m * B + complexity interpretation (single test) := by
          gcongr
          refine (complexity_pi_le q).trans ?_
          calc _ ≤ ∑ _j : Fin m, B := sum_le_sum fun j _ => hq j
            _ = m * B := by simp
      _ = _ := add_comm _ _
  cases r
  · have e : (fun x => nextBitGuess test i false u fun j => bit j x) =
        fun x => !test fun j => q j x := funext fun x => by
      simp only [nextBitGuess, q]
      cases test _ <;> rfl
    rw [e]
    exact (complexity_not_le _).trans (Nat.add_le_add_right htest 1)
  · have e : (fun x => nextBitGuess test i true u fun j => bit j x) =
        fun x => test fun j => q j x := funext fun x => by
      simp only [nextBitGuess, q]
      cases test _ <;> rfl
    rw [e]
    exact htest.trans (Nat.le_succ _)

/-- **The Nisan–Wigderson reconstruction with circuits**
[Arora and Barak, Chapter 20][AroraBarak09]. If `0 < m` and a deterministic test accepts outputs of
the generator with probability at least `ε` more than uniform strings, then some function `g` on `n`
bits agrees with `f` on at least a `1 / 2 + ε / m` fraction of the inputs and has De Morgan circuit
complexity at most that of the test plus `m * (2 ^ a * (2 * a + 3) + 1) + 1`. -/
theorem exists_complexity_le_half_add_div_le_card_eq (D : Design ℓ n a m)
    (f : BooleanFunction n) (test : BooleanFunction m) (hm : 0 < m) {ε : ℝ}
    (hε : ε ≤ ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal) :
    ∃ g : BooleanFunction n, complexity interpretation (single g) ≤
        complexity interpretation (single test) + m * (2 ^ a * (2 * a + 3) + 1) + 1 ∧
      1 / 2 + ε / m ≤ (#{x | g x = f x} : ℝ) / 2 ^ n := by
  obtain ⟨i, s, bit, r, u, hs, hbit, h⟩ :=
    exists_dependsOn_half_add_div_le_card_nextBitGuess_eq D f test hm hε
  refine ⟨_, complexity_nextBitGuess_le test i r u bit (Nat.le_add_left 1 _) fun j => ?_, h⟩
  refine (complexity_le_of_dependsOn (hbit j)).trans ?_
  have := hs j
  gcongr

/-- **The Nisan–Wigderson generator fools small circuits**
[Arora and Barak, Chapter 20][AroraBarak09]. Let `0 < m`. If every function on `n` bits of
complexity at most `S + m * (2 ^ a * (2 * a + 3) + 1) + 1` agrees with `f` on less than a
`1 / 2 + ε / m` fraction of the inputs, then every test of complexity at most `S` accepts outputs of
the generator with probability less than `ε` more than uniform strings. -/
theorem toReal_realExperiment_sub_toReal_idealExperiment_lt (D : Design ℓ n a m)
    (f : BooleanFunction n) (hm : 0 < m) {ε : ℝ} {S : ℕ}
    (hf : ∀ g : BooleanFunction n,
      complexity interpretation (single g) ≤ S + m * (2 ^ a * (2 * a + 3) + 1) + 1 →
        (#{x | g x = f x} : ℝ) / 2 ^ n < 1 / 2 + ε / m)
    (test : BooleanFunction m) (htest : complexity interpretation (single test) ≤ S) :
    ((generator D f).realExperiment (fun y => PMF.pure (test y)) true).toReal -
      (Generator.idealExperiment (fun y => PMF.pure (test y)) true).toReal < ε := by
  by_contra hlt
  obtain ⟨g, hg, hfg⟩ := exists_complexity_le_half_add_div_le_card_eq D f test hm (not_lt.1 hlt)
  exact (hf g (by omega)).not_ge hfg

end Cslib.Crypto.PRG.NisanWigderson
