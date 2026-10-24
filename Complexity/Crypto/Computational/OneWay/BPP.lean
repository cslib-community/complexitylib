/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP.Amplification
public import Complexity.Crypto.Computational.OneWay.NP
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Complexity.Classes.BPP.Reduction
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Map
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# One-way functions put NP outside BPP

If one-way functions exist then `NP ⊄ BPP` [Goldreich, Chapter 2][Goldreich2001]: the
preimage-prefix problem of a one-way function (`Cslib.Crypto.preimagePrefix`) is not in `BPP`
(`Cslib.Crypto.OneWay.preimagePrefix_notMem_BPP`).

A decider with error at most `2 ^ (-(L + 1))` on instances of encoded length `L` exists for every
problem in `BPP` (`Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent`). The randomized
search (`Cslib.Crypto.randomizedPreimageSearch`) samples one string of coins and runs the
deterministic bit-by-bit search, answering each query with the decider on a prefix of the coins of
the length the decider expects. The search with exact answers asks `n` fixed queries, each with
encoded length at least `n`; whenever the decider answers these correctly, the randomized search
follows the exact one (`Cslib.Crypto.preimageSearch_congr`) and finds a preimage. Each of them is
answered wrongly with probability at most `2 ^ (-(n + 1))`, so by a union bound the randomized
search inverts with probability at least `1 / 2`
(`Cslib.Crypto.half_le_succProbability_inversionGame`), and it is a uniform strict PPT inverter.
Since `BPP` is closed under polynomial-time reductions
(`Cslib.Complexity.PolyTimeReducible.mem_BPP`), the Cook–Levin theorem puts `SAT` outside `BPP`
as well (`Cslib.Crypto.OneWay.SAT_notMem_BPP`).

## Main definitions

* `Cslib.Crypto.randomizedPreimageSearch`: the search answering queries with a randomized decider
  on shared coins.

## Main results

* `Cslib.Crypto.isPPT_randomizedPreimageSearch`: the randomized search is a uniform strict PPT
  inverter.
* `Cslib.Crypto.half_le_succProbability_inversionGame`: with a decider of error
  `2 ^ (-(L + 1))`, the randomized search inverts with probability at least `1 / 2`.
* `Cslib.Crypto.exists_inverter_of_preimagePrefix_mem_BPP`: if the preimage-prefix problem is in
  `BPP`, some uniform strict PPT inverter succeeds with probability at least `1 / 2`.
* `Cslib.Crypto.OneWay.preimagePrefix_notMem_BPP`, `Cslib.Crypto.OneWay.not_NP_subset_BPP`,
  `Cslib.Crypto.OneWay.SAT_notMem_BPP`, `Cslib.Crypto.not_oneWay_of_SAT_mem_BPP`: one-way
  functions imply `NP ⊄ BPP`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 1*][Goldreich2001]
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {f : List Bool → List Bool}

/-- The coins read by the randomized search for a preimage of length `q.1` of `q.2`: enough for
the decider on every query, whose prefix has at most `q.1` bits. -/
def searchCoinLength (p : Polynomial ℕ) (q : ℕ × List Bool) : ℕ :=
  p.eval (encPreimagePrefix (q.1, q.2, List.replicate q.1 false)).length

/-- **The randomized search**: sample `searchCoinLength p (n, y)` coins once, and run the
bit-by-bit search, answering every query with `V` on the prefix of the coins of the length
`p (L)` that `V` expects on an instance of encoded length `L`. -/
noncomputable def randomizedPreimageSearch (p : Polynomial ℕ)
    (V : (ℕ × List Bool × List Bool) × List Bool → Bool) (n : ℕ) (y : List Bool) :
    ProbComp (List Bool) :=
  (fun coins => preimageSearch
      (fun x => V (x, coins.take (p.eval (encPreimagePrefix x).length))) (n, y)) <$>
    BitString.sampleList (searchCoinLength p (n, y))

/-- The randomized search is a uniform strict PPT inverter when `V` is polynomial-time. -/
theorem isPPT_randomizedPreimageSearch {p : Polynomial ℕ}
    {V : (ℕ × List Bool × List Bool) × List Bool → Bool}
    (hV : ComputableTidilyInPolyTime V (encPair encPreimagePrefix encBits) encBool) :
    IsPPT encBits (randomizedPreimageSearch p V) := by
  apply IsPPTOn.isPPT
  have hlen : ComputableTidilyInPolyTime (fun q : ℕ × List Bool => searchCoinLength p q)
      (encPair encUnary encBits) encUnary := by
    unfold searchCoinLength
    exact (unary_eval p).comp ((encoding_length encPreimagePrefix).comp
      ((fst _ _).prod ((snd _ _).prod ((bitsReplicate false).comp (fst _ _)))))
  refine IsPPTOn.map_with hlen.sampleList
    (.of_tidy (computableTidilyInPolyTime_preimageSearch_of_input ?_ (fst _ _)))
  exact hV.comp ((snd _ _).prod (bitsTakeWithInput (fst _ _).snd'
    ((unary_eval p).comp ((encoding_length encPreimagePrefix).comp (snd _ _)))))

/-- A decider with error at most `2 ^ (-q(L))` errs on a uniformly random prefix of a coin
string with probability at most `2 ^ (-q(L))`. -/
private theorem toOuterMeasure_take_wrong_le {α : Type} {enc : α ↪ List Bool}
    {q p : Polynomial ℕ} {V : α × List Bool → Bool} {A : Set α}
    (hV : DecidesWithErrorExponent enc q p V A) (a : α) [Decidable (a ∈ A)] {R : ℕ}
    (hR : p.eval (enc a).length ≤ R) :
    (BitString.uniformList R).toOuterMeasure
        {coins | V (a, coins.take (p.eval (enc a).length)) ≠ decide (a ∈ A)} ≤
      1 / 2 ^ q.eval (enc a).length := by
  set k := p.eval (enc a).length
  have hpre : {coins : List Bool | V (a, coins.take k) ≠ decide (a ∈ A)} =
      List.take k ⁻¹' ((fun coins => V (a, coins)) ⁻¹' {!decide (a ∈ A)}) := by
    ext coins
    cases V (a, coins.take k) <;> cases decide (a ∈ A) <;> simp
  rw [hpre, ← PMF.toOuterMeasure_map_apply, BitString.uniformList_take hR,
    ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton, BitString.uniformList,
    PMF.map_comp, PMF.uniformOfFintype_map_apply, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hcount : 2 ^ q.eval (enc a).length * (Finset.univ.filter fun w : Fin k → Bool =>
      ((fun coins => V (a, coins)) ∘ List.ofFn) w = !decide (a ∈ A)).card ≤ 2 ^ k := by
    by_cases ha : a ∈ A
    · simpa [ha] using (hV a).1 ha
    · simpa [ha] using (hV a).2 ha
  rw [ENNReal.div_le_iff (by simp) (by simp), one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (by simp) (by simp)]
  exact_mod_cast (by rw [Nat.mul_comm]; exact hcount)

/-- **The randomized search inverts with probability at least `1 / 2`**, for a decider of the
preimage-prefix problem with error at most `2 ^ (-(L + 1))` on instances of encoded length `L`.
The union bound runs over the `n` queries of the exact search, each of encoded length at least
`n`. -/
theorem half_le_succProbability_inversionGame {p : Polynomial ℕ}
    {V : (ℕ × List Bool × List Bool) × List Bool → Bool}
    (hV : DecidesWithErrorExponent encPreimagePrefix (Polynomial.X + 1) p V (preimagePrefix f))
    (n : ℕ) :
    1 / 2 ≤ Game.succProbability
      (ProbComp.eval (inversionGame f (randomizedPreimageSearch p V) n)) := by
  classical
  set D : ℕ × List Bool × List Bool → Bool := fun x => decide (x ∈ preimagePrefix f)
  have hD : ∀ x, x ∈ preimagePrefix f ↔ D x = true := fun x => decide_eq_true_iff.symm
  have hgame : ProbComp.eval (inversionGame f (randomizedPreimageSearch p V) n) =
      (BitString.uniformList n).bind fun x =>
        (BitString.uniformList (searchCoinLength p (n, f x))).map fun coins =>
          f (preimageSearch (fun inst =>
            V (inst, coins.take (p.eval (encPreimagePrefix inst).length))) (n, f x)) == f x := by
    simp [inversionGame, randomizedPreimageSearch]
  have hhalf : (1 / 2 : ENNReal) ≤
      ProbComp.eval (inversionGame f (randomizedPreimageSearch p V) n) true := by
    rw [hgame]
    refine PMF.le_bind_apply_on_support _ fun x hx => ?_
    have hxn := BitString.length_of_mem_support_uniformList hx
    set μ := BitString.uniformList (searchCoinLength p (n, f x))
    set g : List Bool → Bool := fun coins => f (preimageSearch (fun inst =>
      V (inst, coins.take (p.eval (encPreimagePrefix inst).length))) (n, f x)) == f x
    -- The exact search and its queries.
    set query : ℕ → ℕ × List Bool × List Bool :=
      fun j => (n, f x, (preimageSearchStep D (n, f x))^[j] [] ++ [false])
    set bad : ℕ → Set (List Bool) := fun j => {coins |
      V (query j, coins.take (p.eval (encPreimagePrefix (query j)).length)) ≠ D (query j)}
    have hfalse : {coins | g coins = false} ⊆ ⋃ j ∈ Finset.range n, bad j := by
      intro coins hcoins
      by_contra hgood
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, not_exists, not_not,
        bad] at hgood
      have hsame := preimageSearch_congr (D := D) (q := (n, f x))
        (D' := fun inst => V (inst, coins.take (p.eval (encPreimagePrefix inst).length)))
        fun j hj => hgood j hj
      have := apply_preimageSearch hD x
      rw [hxn] at this
      simp only [Set.mem_ofPred_eq, g, hsame, this, beq_self_eq_true, Bool.true_eq_false] at hcoins
    have hlen (j : ℕ) (hj : j < n) :
        n ≤ (encPreimagePrefix (query j)).length ∧
          p.eval (encPreimagePrefix (query j)).length ≤ searchCoinLength p (n, f x) := by
      have hj' := length_iterate_preimageSearchStep D (n, f x) j
      constructor
      · simp only [query, length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
        omega
      · refine Polynomial.eval_mono p ?_
        simp only [query, length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
          List.length_append, hj', List.length_singleton]
        omega
    have hbad (j : ℕ) (hj : j < n) : μ.toOuterMeasure (bad j) ≤ 1 / 2 ^ (n + 1) := by
      refine (toOuterMeasure_take_wrong_le hV (query j) (hlen j hj).2).trans ?_
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      gcongr
      · norm_num
      · exact (hlen j hj).1
    have hfail : (μ.map g) false ≤ 1 / 2 := by
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      calc μ.toOuterMeasure (g ⁻¹' {false})
          ≤ μ.toOuterMeasure (⋃ j ∈ Finset.range n, bad j) :=
            MeasureTheory.measure_mono hfalse
        _ ≤ ∑ j ∈ Finset.range n, μ.toOuterMeasure (bad j) :=
            MeasureTheory.measure_biUnion_finset_le _ _
        _ ≤ ∑ _j ∈ Finset.range n, (1 / 2 ^ (n + 1) : ENNReal) :=
            Finset.sum_le_sum fun j hj => hbad j (Finset.mem_range.1 hj)
        _ ≤ 1 / 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
            calc (n : ENNReal) * (1 / (2 ^ n * 2)) ≤ 2 ^ n * (1 / (2 ^ n * 2)) := by
                  gcongr
                  exact_mod_cast Nat.lt_two_pow_self.le
              _ = 1 / 2 := by
                  rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]
    have hsum : (μ.map g) true + (μ.map g) false = 1 := by
      rw [add_comm, ← tsum_bool, PMF.tsum_coe]
    calc (1 / 2 : ENNReal) = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - (μ.map g) false := tsub_le_tsub_left hfail 1
      _ = (μ.map g) true := by
          rw [← hsum, ENNReal.add_sub_cancel_right (PMF.apply_ne_top _ _)]
  have h12 : ((1 / 2 : NNReal) : ENNReal) = 1 / 2 := by norm_num
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _), h12]
  exact hhalf

/-- **Inversion from `BPP`.** If the preimage-prefix problem of `f` is in `BPP`, a uniform strict
PPT inverter, told the length of the input, inverts `f` with probability at least `1 / 2` at every
length. -/
theorem exists_inverter_of_preimagePrefix_mem_BPP
    (h : preimagePrefix f ∈ BPP encPreimagePrefix) :
    ∃ inverter : Inverter, IsPPT encBits inverter ∧
      ∀ n, 1 / 2 ≤ Game.succProbability (ProbComp.eval (inversionGame f inverter n)) := by
  obtain ⟨p, V, hV, herr⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.1 h (Polynomial.X + 1)
  exact ⟨randomizedPreimageSearch p V, isPPT_randomizedPreimageSearch hV.tidy,
    half_le_succProbability_inversionGame herr⟩

/-- **One-way functions have preimage-prefix problems outside `BPP`.** -/
theorem OneWay.preimagePrefix_notMem_BPP (hf : OneWay f) :
    preimagePrefix f ∉ BPP encPreimagePrefix := fun h =>
  let ⟨inverter, hPPT, hhalf⟩ := exists_inverter_of_preimagePrefix_mem_BPP h
  not_oneWay_of_le_succProbability (by norm_num) inverter hPPT hhalf hf

/-- **One-way functions imply `NP ⊄ BPP`**, for instances of the preimage-prefix problem. -/
theorem OneWay.not_NP_subset_BPP (hf : OneWay f) :
    ¬ NP encPreimagePrefix ⊆ BPP encPreimagePrefix := fun h =>
  hf.preimagePrefix_notMem_BPP (h (preimagePrefix_mem_NP hf.polyTime.tidy))

/-- **One-way functions imply `SAT ∉ BPP`**: by the Cook–Levin theorem the preimage-prefix problem
reduces to `SAT`, and `BPP` is closed under polynomial-time reductions. -/
theorem OneWay.SAT_notMem_BPP (hf : OneWay f) : SAT ∉ BPP encCNF := fun h =>
  hf.preimagePrefix_notMem_BPP
    ((CookLevin.SAT_npComplete.2 encPreimagePrefix _
      (preimagePrefix_mem_NP hf.polyTime.tidy)).mem_BPP h)

/-- If `SAT` is in `BPP`, no function is one-way. -/
theorem not_oneWay_of_SAT_mem_BPP (h : SAT ∈ BPP encCNF) : ¬ OneWay f := fun hf =>
  hf.SAT_notMem_BPP h

end Cslib.Crypto
