/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.AntiChecker.Generator
public import CslibFrontier.Computability.MCSP.AntiChecker.Oracle.PolyTime
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
import CslibFrontier.Computability.Circuit.Boolean.AtLeast
import CslibFrontier.Foundations.Analysis.SpecificLimits.PolyLtPow
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The efficient anti-checker

[Oliveira, Pich and Santhanam, Lemma 4.1][OliveiraPichSanthanam2019] (ECCC TR18-158, Lemma 17)
states: if `NP ⊆ Circuit[poly]`, there is a constant `k` such that for every small enough `β > 0`
there is a circuit `C` of size at most `2 ^ (n + k β n)` that, given the truth table of
`f : {0,1}^n → {0,1}`, outputs `t = 2 ^ (10 β n)` strings `y₁, …, y_t ∈ {0,1}^n` such that if
`f ∉ Circuit[2 ^ (β n)]`, every circuit of size at most `s = 2 ^ (β n) / 10 n` fails to compute
`f` on one of them. This is `Cslib.MCSP.AntiChecker.exists_antiChecker_circuit_of_NP_subset_PPoly`.

The circuit is the anti-checker generator (`Cslib.MCSP.AntiChecker.generator`) with its oracle
gates replaced by `P/poly` circuits for a language that agrees with the anti-checker oracle on its
queries (`Cslib.MCSP.AntiChecker.exists_mem_PPoly_agrees_antiCheckerOracle`), followed by wires
that copy the input bits of each sample into `t` output blocks of `n` bits. The explicit form
`Cslib.MCSP.AntiChecker.exists_antiChecker_circuit_le_of_NP_subset_PPoly` bounds the size by
`2 ^ n · c (n + s + 1) ^ c` for every `n > 0`, every `s` and every `t` at least the number of
rounds, and makes the hardness assumption explicit: `f` needs more gates than `n` circuits with `s`
gates and their strict majority.

**Proof route.** The statement is OPS's; the proof is not. The anti-checker is the library's
deterministic greedy against the hash threshold oracle (`Cslib.MCSP.AntiChecker.greedy`), whose
termination uses the good-string lemma with constant `1/16` and the tensor-power amplification of
[Chen, Hirahara, Oliveira, Pich, Rajgopal and
Santhanam][ChenHiraharaOliveiraPichRajgopalSanthanam2020].
OPS select samples by approximate counting instead.

**Translation.** Sizes count all De Morgan gates. `f ∉ Circuit[2 ^ (β n)]` is
`⌊2 ^ (β n)⌋₊ < complexity f`, which is equivalent because complexity is a natural number, and the
size bound `2 ^ (β n) / 10 n` is rounded down. The `t` strings are the `t` blocks of `n` outputs of
one circuit, read with `Cslib.BitString.block`. The statement holds for every `β > 0` and all large
`n`, which is stronger than "every sufficiently small `β`".

## Main results

* `Cslib.MCSP.AntiChecker.exists_antiChecker_circuit_le_of_NP_subset_PPoly`: the explicit form.
* `Cslib.MCSP.AntiChecker.exists_antiChecker_circuit_of_NP_subset_PPoly`: OPS Lemma 4.1.

## References

* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness magnification near state-of-the-art lower
  bounds*][OliveiraPichSanthanam2019]
* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond natural
  proofs: hardness magnification and locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.MCSP.AntiChecker

open Circuits Circuits.Boolean Complexity Turing.MultiTapeTM Filter

/-- The output wiring: output bit `b` of block `i` copies input bit `b` of the sample in block
`min i (R - 1)`. -/
private def blockSelect {n R : ℕ} (hR : 0 < R) (t : ℕ) (p : Fin (t * n)) :
    Fin (2 ^ n + (n + 1) * R) :=
  blockWire ⟨min (finProdFinEquiv.symm p).1 (R - 1), by omega⟩ (finProdFinEquiv.symm p).2.castSucc

/-- **The efficient anti-checker, explicit form.** If `NP ⊆ P/poly`, there is `c` such that for all
`n > 0`, `s`, and `t` at least the number of rounds of the anti-checker generator, a De Morgan
circuit with at most `2 ^ n · c (n + s + 1) ^ c` gates maps the truth table of `f` to `t` blocks of
`n` bits that form an anti-checker for the circuits with at most `s` gates, whenever `f` needs more
gates than `n` such circuits and their strict majority. -/
theorem exists_antiChecker_circuit_le_of_NP_subset_PPoly (hNP : NP encBits ⊆ PPolyOn encBits) :
    ∃ c : ℕ, ∀ n s t : ℕ, 0 < n → antiCheckerRounds n s ≤ t →
      ∃ C : Circuit signature (2 ^ n) (t * n), C.size ≤ 2 ^ n * c * (n + s + 1) ^ c ∧
        ∀ f : BooleanFunction n, n * s + complexity interpretation (single (strictMajority n)) <
            complexity interpretation (single f) →
          IsAntiChecker (computableFunctions n s) f
            (Set.range fun i =>
              BitString.block (C.eval interpretation (MCSP.truthTable n f)) i) := by
  obtain ⟨O, hO, hagree⟩ := exists_mem_PPoly_agrees_antiCheckerOracle hNP
  obtain ⟨c₀, hc₀⟩ := mem_PPoly_iff_exists_mem_SIZE.1 hO
  choose D hD hDsize using fun q =>
    exists_computes_size_eq_complexity (I := interpretation) (f := single (O.slice q))
  refine ⟨4270 * ((c₀ + 1) * 5001 ^ c₀) + 5 + 5 * c₀, fun n s t hn hRt => ?_⟩
  set R := antiCheckerRounds n s
  set ℓ := antiCheckerPower n s
  have hR0 : 0 < R := antiCheckerRounds_pos n s
  set G := generator n s ℓ R
  refine ⟨(Circuit.wiring signature (blockSelect hR0 t)).comp (inlineOracle G D), ?_, ?_⟩
  · -- Size.
    set m := n + s + 1 with hmdef
    have hm1 : 1 ≤ m := Nat.le_add_left 1 _
    have hq : queryLength n s ℓ R R ≤ 5000 * m ^ 5 := queryLength_antiChecker_le n s
    have hDle : ∀ q ≤ queryLength n s ℓ R R, (D q).size ≤ c₀ * (5001 * m ^ 5) ^ c₀ := by
      intro q hqr
      rw [hDsize]
      refine (hc₀ q).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      have : 1 ≤ m ^ 5 := Nat.one_le_pow _ _ hm1
      omega
    have hinl := size_inlineOracle_le G D (fanInAtMost_generator n s ℓ R) hDle
    have hmax : max 1 (c₀ * (5001 * m ^ 5) ^ c₀) ≤ (c₀ + 1) * 5001 ^ c₀ * m ^ (5 * c₀) := by
      have h1 : 1 ≤ 5001 ^ c₀ * m ^ (5 * c₀) :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by positivity))
      rw [mul_pow, ← pow_mul]
      refine max_le ?_ ?_
      · nlinarith
      · nlinarith
    have hG : G.size ≤ 4270 * 2 ^ n * m ^ 5 := by
      rw [size_generator]
      have hR : R ≤ 610 * m ^ 4 := antiCheckerRounds_le n s
      have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h7 : 2 + 2 ^ n * (3 * n + 5) ≤ 2 ^ n * (7 * m) :=
        calc 2 + 2 ^ n * (3 * n + 5) ≤ 2 ^ n * (3 * n + 7) := by nlinarith
          _ ≤ 2 ^ n * (7 * m) := Nat.mul_le_mul_left _ (by omega)
      calc R * (2 + 2 ^ n * (3 * n + 5)) ≤ 610 * m ^ 4 * (2 ^ n * (7 * m)) := by gcongr
        _ = 4270 * 2 ^ n * m ^ 5 := by ring
    rw [Circuit.size_comp, Circuit.size_wiring, Nat.add_zero]
    set A := 4270 * ((c₀ + 1) * 5001 ^ c₀)
    calc (inlineOracle G D).size
        ≤ 4270 * 2 ^ n * m ^ 5 * ((c₀ + 1) * 5001 ^ c₀ * m ^ (5 * c₀)) :=
          hinl.trans (Nat.mul_le_mul hG hmax)
      _ = 2 ^ n * A * m ^ (5 + 5 * c₀) := by rw [pow_add]; ring
      _ ≤ 2 ^ n * (A + 5 + 5 * c₀) * m ^ (A + 5 + 5 * c₀) := by
          gcongr <;> omega
  · -- Correctness: every sample's input appears as a block.
    intro f hf
    have hac := isAntiChecker_samplesOf_generator hn hagree hf
    intro g hg
    obtain ⟨x, hx, hgx⟩ := hac g hg
    refine ⟨x, ?_, hgx⟩
    rw [Set.mem_ofPred_eq, map_fst_samplesOf, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    have hjt : (j : ℕ) < t := lt_of_lt_of_le j.isLt hRt
    refine ⟨⟨j, hjt⟩, funext fun b => ?_⟩
    simp only [BitString.block_apply, Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply,
      eval_inlineOracle G fun q => hD q, blockSelect, Equiv.symm_apply_apply]
    congr 2
    exact Fin.ext (min_eq_left (by omega))

/-- **The parameters of OPS Lemma 4.1 leave room for the hardness assumption.** For `β > 0` and
all large `n`, `n ⌊2 ^ (β n) / 10 n⌋₊ + 2 + 2 n (n + 2) ≤ ⌊2 ^ (β n)⌋₊`. So a function with no
circuit of `⌊2 ^ (β n)⌋₊` gates needs more gates than `n` circuits with `⌊2 ^ (β n) / 10 n⌋₊` gates
and their strict majority. -/
theorem eventually_mul_floor_div_add_le_floor {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop,
      n * ⌊(2 : ℝ) ^ (β * n) / (10 * n)⌋₊ + 2 + 2 * n * (n + 2) ≤ ⌊(2 : ℝ) ^ (β * n)⌋₊ := by
  have ha : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  filter_upwards [eventually_mul_add_one_pow_lt_pow 4 2 ha, eventually_gt_atTop 0] with n hpoly hn
  have hXβ : (2 : ℝ) ^ (β * n) = ((2 : ℝ) ^ β) ^ n := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [← hXβ] at hpoly
  set X := (2 : ℝ) ^ (β * n)
  have hX0 : 0 < X := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine Nat.le_floor ?_
  have hs : (⌊X / (10 * n)⌋₊ : ℝ) ≤ X / (10 * n) := Nat.floor_le (by positivity)
  have hns : (n : ℝ) * ⌊X / (10 * n)⌋₊ ≤ X / 10 :=
    calc (n : ℝ) * ⌊X / (10 * n)⌋₊ ≤ n * (X / (10 * n)) := by gcongr
      _ = X / 10 := by field_simp
  push_cast
  nlinarith

/-- **The efficient anti-checker** [Oliveira, Pich and Santhanam, Lemma 4.1]
[OliveiraPichSanthanam2019] (OPS ToC 2021 Lemma 4.1; ECCC TR18-158 Lemma 17). If
`NP ⊆ P/poly`, there is `k` such that for every `β > 0` and all large `n`, a De Morgan circuit with
at most `2 ^ (n + k β n)` gates maps the truth table of `f : {0,1}^n → {0,1}` to
`t = ⌊2 ^ (10 β n)⌋₊` strings of `n` bits such that if `f` has no circuit with `⌊2 ^ (β n)⌋₊`
gates, every circuit with at most `⌊2 ^ (β n) / 10 n⌋₊` gates fails to compute `f` on one of them.

OPS state this for every sufficiently small `β`; it holds here for every `β > 0`, which is a
genuine strengthening. The proof is the library's hash-threshold greedy (see the module
docstring), not OPS's approximate counting. -/
theorem exists_antiChecker_circuit_of_NP_subset_PPoly (hNP : NP encBits ⊆ PPolyOn encBits) :
    ∃ k : ℕ, ∀ β : ℝ, 0 < β → ∀ᶠ n : ℕ in atTop,
      ∃ C : Circuit signature (2 ^ n) (⌊(2 : ℝ) ^ (10 * β * n)⌋₊ * n),
        (C.size : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + k * β * n) ∧
        ∀ f : BooleanFunction n, ⌊(2 : ℝ) ^ (β * n)⌋₊ < complexity interpretation (single f) →
          IsAntiChecker (computableFunctions n ⌊(2 : ℝ) ^ (β * n) / (10 * n)⌋₊) f
            (Set.range fun i =>
              BitString.block (C.eval interpretation (MCSP.truthTable n f)) i) := by
  obtain ⟨c, hc⟩ := exists_antiChecker_circuit_le_of_NP_subset_PPoly hNP
  refine ⟨c + 1, fun β hβ => ?_⟩
  set a : ℝ := (2 : ℝ) ^ β with ha_def
  have ha : 1 < a := Real.one_lt_rpow (by norm_num) hβ
  have ha0 : 0 < a := by linarith
  filter_upwards [eventually_mul_add_one_pow_lt_pow 4 2 ha,
    eventually_mul_add_one_pow_lt_pow (10 + c * 2 ^ c) 0 ha, eventually_gt_atTop 0,
    eventually_mul_floor_div_add_le_floor hβ] with n hpoly hconst hn hgap
  -- `X = 2 ^ (β n)`.
  set X : ℝ := a ^ n with hX_def
  have hpow (x : ℝ) : (2 : ℝ) ^ (x * n) = ((2 : ℝ) ^ x) ^ n := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hXβ : (2 : ℝ) ^ (β * n) = X := hpow β
  have hX10 : (2 : ℝ) ^ (10 * β * n) = X ^ 10 := by
    rw [show 10 * β * n = β * n * (10 : ℕ) by push_cast; ring,
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), hXβ]
  have hX0 : 0 < X := pow_pos ha0 n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnX : 4 * ((n : ℝ) + 1) ^ 2 < X := hpoly
  have hcX : 10 + (c : ℝ) * 2 ^ c < X := by simpa using hconst
  have hX10le : (10 : ℝ) ≤ X := by
    have : (0 : ℝ) ≤ c * 2 ^ c := by positivity
    linarith
  have hn1X : (n : ℝ) + 1 ≤ X := by nlinarith
  -- The parameters.
  set s := ⌊(2 : ℝ) ^ (β * n) / (10 * n)⌋₊
  set t := ⌊(2 : ℝ) ^ (10 * β * n)⌋₊
  have hs : (s : ℝ) ≤ X / (10 * n) := by
    rw [← hXβ]
    exact Nat.floor_le (by positivity)
  have hsX : (s : ℝ) ≤ X := hs.trans (div_le_self hX0.le (by nlinarith))
  have hm : ((n + s + 1 : ℕ) : ℝ) ≤ 2 * X := by push_cast; linarith
  -- Enough rounds.
  have hRt : antiCheckerRounds n s ≤ t := by
    rw [Nat.le_floor_iff (by rw [hX10]; positivity), hX10]
    have hR := antiCheckerRounds_le n s
    have hR' : (antiCheckerRounds n s : ℝ) ≤ 610 * ((n + s + 1 : ℕ) : ℝ) ^ 4 := by exact_mod_cast hR
    have hm0 : (0 : ℝ) ≤ ((n + s + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (antiCheckerRounds n s : ℝ) ≤ 610 * ((n + s + 1 : ℕ) : ℝ) ^ 4 := hR'
      _ ≤ 610 * (2 * X) ^ 4 := by gcongr
      _ = 9760 * X ^ 4 := by ring
      _ ≤ X ^ 6 * X ^ 4 := by
          gcongr
          calc (9760 : ℝ) ≤ 10 ^ 6 := by norm_num
            _ ≤ X ^ 6 := by gcongr
      _ = X ^ 10 := by ring
  obtain ⟨C, hsize, hanti⟩ := hc n s t hn hRt
  refine ⟨C, ?_, fun f hf => hanti f ?_⟩
  · -- Size: `2 ^ n c (n + s + 1) ^ c ≤ 2 ^ n (c 2 ^ c) X ^ c ≤ 2 ^ n X ^ (c + 1)`.
    have hsize' : (C.size : ℝ) ≤ 2 ^ n * c * ((n + s + 1 : ℕ) : ℝ) ^ c := by exact_mod_cast hsize
    have hRHS : (2 : ℝ) ^ ((n : ℝ) + (c + 1 : ℕ) * β * n) = 2 ^ n * X ^ (c + 1) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast,
        show ((c + 1 : ℕ) : ℝ) * β * n = β * n * (c + 1 : ℕ) by ring,
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), hXβ]
    rw [hRHS]
    have hm0 : (0 : ℝ) ≤ ((n + s + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (C.size : ℝ) ≤ 2 ^ n * c * ((n + s + 1 : ℕ) : ℝ) ^ c := hsize'
      _ ≤ 2 ^ n * c * (2 * X) ^ c := by gcongr
      _ = 2 ^ n * (c * 2 ^ c) * X ^ c := by ring
      _ ≤ 2 ^ n * X * X ^ c := by gcongr; linarith
      _ = 2 ^ n * X ^ (c + 1) := by ring
  · -- Hardness: `n s + complexity (strictMajority n) ≤ n s + 2 + 2 n (n + 2) ≤ ⌊X⌋₊`.
    have hmaj : complexity interpretation (single (strictMajority n)) ≤ 2 + n * (2 * (n + 2)) :=
      complexity_threshold_le n (n / 2 + 1)
    have hring : n * (2 * (n + 2)) = 2 * n * (n + 2) := by ring
    omega

end Cslib.MCSP.AntiChecker
