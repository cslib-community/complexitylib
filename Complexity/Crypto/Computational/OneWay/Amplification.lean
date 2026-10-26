/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.OneWay.Weak
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Analysis.BernoulliInequality
import Complexity.Foundations.Data.Finset.Sampling
import Complexity.Languages.Probabilistic.BitString
import Complexity.Probability.BitString.List.All
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.Product
import Complexity.Probability.Uniform
import Complexity.Tactic.PPT

/-!
# Yao's Weak-to-Strong One-Way Function Hardness Amplification

This module formalizes Yao's hardness amplification theorem ([Yao1982];
[Goldreich, Vol. 1, §2.3, Theorem 2.3.2][Goldreich2001];
[Liu and Pass, Theorem 2.3, §2.1, p. 8 of `arXiv:2009.11514v1`][LiuPass2020]):
if there exists a weak one-way function (`WeakOneWay`), then there exists a strong one-way
function (`OneWay`).

## Construction Overview

1. **Output-length normalization:** Given `hf : WeakOneWay f`, apply
   `WeakOneWay.exists_fixedOutputLength` to obtain a weak one-way function $g$ with a
   polynomial-time unary output-length schedule `outLen : ℕ → ℕ`
   (`∀ x, (g x).length = outLen x.length`) and a polynomial $q : \mathbb{N}[X]$
   ($\forall N,\, 0 < q(N)$) such that `WeakOneWayAt g (fun N => 1 / (q.eval N : ℝ))`.
2. **Parallel direct product on schedule $m(n)$:** At parameter $n \in \mathbb{N}$, set block width
   $w(n) := n + 1$, block count $k(n) := 2 \cdot q(w(n)) \cdot w(n)$, and input length
   $m(n) := k(n) \cdot w(n)$. On an input $X \in \{0, 1\}^{m(n)}$, `parallelCore k w g n X` splits
   $X$ into $k(n)$ blocks $x_0, \dots, x_{k(n)-1} \in \{0, 1\}^{w(n)}$ via `BitString.listRow` and
   concatenates $g(x_0) \mathbin{\Vert} \dots \mathbin{\Vert} g(x_{k(n)-1})$.
3. **Direct reduction and probability bound:** For any uniform strict PPT inverter $\mathcal{A}$
   against `familyInversionGame m (parallelCore k w g)` and any target polynomial degree
   $d \in \mathbb{N}$, running $t_d(n) := 4 \cdot q(w(n)) \cdot k(n) \cdot p_d(n)$ independent
   planted-slot trials (where $p_d(n) = (n + 1)^{d + 1}$) defines a uniform strict PPT inverter
   $B_d$ against $g$. Using `BitString.uniformList_all_listRow_true` twice—once across the $k(n)$
   input blocks of $X$ and once across the $t_d(n)$ independent seed blocks of $B_d$—together with
   the exact single-slot planting law `BitString.uniformList_replaceRow`, the weak one-wayness bound
   on $g$ forces $\mathcal{A}$'s inversion probability at parameter $n$ to be at most
   $(1/2)^{n+1} + \frac{1}{2 p_d(n)} \le \frac{1}{p_d(n)}$ for all sufficiently large $n$.
4. **Length-universal extension:** Applying `OneWayReindex.oneWay` to the schedule $m(n)$
   ($m(n) \ge n + 1$) extends `parallelCore k w g` to a single strong one-way function on all
   binary strings.

## Main definitions

* `Cslib.Crypto.OneWayAmplification.parallelCore`: evaluate $f$ in parallel on $k(n)$ blocks of
  width $w(n)$ and concatenate the outputs.
* `Cslib.Crypto.OneWayAmplification.plantedImage`: form the $k(n)$-block parallel output with a
  challenge $y$ planted in slot $j$.

## Main results

* `Cslib.Crypto.OneWayAmplification.familyInversionGame_parallelCore_negligible`: any uniform strict
  PPT adversary has negligible inversion probability against `parallelCore` on schedule
  $m(n) = 2 q(n+1) (n+1)^2$.
* `Cslib.Crypto.WeakOneWay.exists_oneWay`: every weak one-way function yields a strong one-way
  function ([Liu and Pass, Theorem 2.3, §2.1, p. 8 of `arXiv:2009.11514v1`][LiuPass2020];
  [Yao1982]).
* `Cslib.Crypto.exists_oneWay_of_exists_weakOneWay`: existential form of Theorem 2.3.
* `Cslib.Crypto.exists_oneWay_iff_exists_weakOneWay`: equivalence of weak and strong one-way
  functions ([Goldreich, Vol. 1, §2.3, Theorem 2.3.2][Goldreich2001]).

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Section 2.1, Theorem 2.3, p. 8).
* [A. C. Yao, *Theory and Application of Trapdoor Functions*][Yao1982].
* [O. Goldreich, *Foundations of Cryptography, Volume 1*][Goldreich2001],
  Section 2.3, Theorem 2.3.2.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability BitString Filter Turing.MultiTapeTM
open scoped NNReal BigOperators

namespace OneWayAmplification

/-! ### Geometric amplification bounds -/

private theorem pow_one_sub_inv_two_mul_le {q : ℕ} (hq : 0 < q) (r : ℕ) :
    (1 - 1 / (2 * (q : ℝ))) ^ (2 * q * r) ≤ (1 / 2 : ℝ) ^ r := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hα1 : 1 / (2 * (q : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hbase : (1 - 1 / (2 * (q : ℝ))) ^ (2 * q) ≤ 1 / 2 :=
    one_sub_pow_le_half (by positivity) hα1 (by push_cast; field_simp; rfl)
  rw [pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg (by linarith) _) hbase r

private theorem pow_one_sub_le_inv_two_mul {q m : ℕ} (hq : 0 < q) (hm : 0 < m) :
    (1 - 1 / (2 * (m : ℝ))) ^ (4 * q * m) ≤ 1 / (2 * (q : ℝ)) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hα1 : 1 / (2 * (m : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h := Real.one_sub_pow_le_one_div_one_add_mul (by positivity) hα1 (4 * q * m)
  have hmul : ((4 * q * m : ℕ) : ℝ) * (1 / (2 * (m : ℝ))) = 2 * (q : ℝ) := by
    push_cast
    field_simp
    ring
  rw [hmul] at h
  exact h.trans (one_div_le_one_div_of_le (by positivity) (by linarith))

/-! ### Parallel evaluation and planted challenges -/

/-- Evaluate `f` in parallel on `k n` blocks of width `w n` extracted from `X` via
`BitString.listRow`, concatenating the resulting bit strings. -/
def parallelCore (k w : ℕ → ℕ) (f : List Bool → List Bool) (n : ℕ) (X : List Bool) :
    List Bool :=
  (List.range (k n)).flatMap (fun j => f (BitString.listRow (w n) j X))

/-- When `f` has fixed output length `outLen |x|` on inputs of length `|x|`, `parallelCore`
produces outputs of exact length `k n * outLen (w n)`. -/
theorem length_parallelCore {k w outLen : ℕ → ℕ} {f : List Bool → List Bool}
    (hlen : ∀ x, (f x).length = outLen x.length) (n : ℕ) (X : List Bool) :
    (parallelCore k w f n X).length = k n * outLen (w n) := by
  simp [parallelCore, List.length_flatMap, hlen, BitString.length_listRow]

/-- Extracting the `j`-th output block of width `outLen (w n)` from `parallelCore` recovers
`f (BitString.listRow (w n) j X)`. -/
theorem listRow_parallelCore {k w outLen : ℕ → ℕ} {f : List Bool → List Bool}
    (hlen : ∀ x, (f x).length = outLen x.length) (n : ℕ) (X : List Bool)
    {j : ℕ} (hj : j < k n) :
    BitString.listRow (outLen (w n)) j (parallelCore k w f n X) =
      f (BitString.listRow (w n) j X) := by
  have h := BitString.listRow_flatMap_append
    (width := outLen (w n))
    (fun i => f (BitString.listRow (w n) i X))
    (List.range (k n))
    (fun i _ => by simp [hlen])
    [] j (by simpa using hj)
  simpa [parallelCore] using h

/-- Any preimage under `parallelCore k w f n` must invert every individual block `j < k n`. -/
theorem parallelCore_eq_imp_row_eq {k w outLen : ℕ → ℕ} {f : List Bool → List Bool}
    (hlen : ∀ x, (f x).length = outLen x.length) {n : ℕ} {X X' : List Bool}
    (heq : parallelCore k w f n X' = parallelCore k w f n X) {j : ℕ} (hj : j < k n) :
    f (BitString.listRow (w n) j X') = f (BitString.listRow (w n) j X) := by
  rw [← listRow_parallelCore hlen n X' hj, ← listRow_parallelCore hlen n X hj, heq]

/-- Truncating the input of `parallelCore k w f n` to `k n * w n` bits leaves the output
unchanged. -/
theorem parallelCore_take (k w : ℕ → ℕ) (f : List Bool → List Bool) (n : ℕ) (X : List Bool) :
    parallelCore k w f n (X.take (k n * w n)) = parallelCore k w f n X := by
  unfold parallelCore
  refine List.flatMap_congr fun j hj => congrArg f ?_
  have hj_lt : j < k n := List.mem_range.mp hj
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [BitString.length_listRow] at hi
  rw [BitString.getElem_listRow hi, BitString.getElem_listRow hi]
  have hlt : j * w n + i < k n * w n := by
    have hstep : j * w n + i < (j + 1) * w n := by ring_nf; omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right (w n) hj_lt)
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt]

/-- Construct the `k n`-block output of `parallelCore` with a challenge `y` planted in slot `j`
and the remaining slots filled by `f (BitString.listRow (w n) i Z)`. -/
def plantedImage (k w : ℕ → ℕ) (f : List Bool → List Bool) (n j : ℕ)
    (y Z : List Bool) : List Bool :=
  (List.range (k n)).flatMap (fun i =>
    if i = j then y else f (BitString.listRow (w n) i Z))

/-- When `y` has length `outLen (w n)`, `plantedImage` has length `k n * outLen (w n)`. -/
theorem length_plantedImage {k w outLen : ℕ → ℕ} {f : List Bool → List Bool}
    (hlen : ∀ x, (f x).length = outLen x.length) (n j : ℕ) {y : List Bool}
    (hy : y.length = outLen (w n)) (Z : List Bool) :
    (plantedImage k w f n j y Z).length = k n * outLen (w n) := by
  have hmap : List.map (fun i =>
      (if i = j then y else f (BitString.listRow (w n) i Z)).length) (List.range (k n)) =
        List.replicate (k n) (outLen (w n)) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun len hlen_mem => ?_⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hlen_mem
    split_ifs <;> simp [hy, hlen]
  rw [plantedImage, List.length_flatMap, hmap, List.sum_replicate, smul_eq_mul]

/-- Evaluating `parallelCore` on `BitString.replaceRow (w n) (k n) j x Z` produces `plantedImage`
with `y = f x` planted in slot `j`. -/
theorem parallelCore_replaceRow {k w : ℕ → ℕ} (f : List Bool → List Bool)
    (n j : ℕ) {x : List Bool} (hx : x.length = w n) (Z : List Bool) :
    parallelCore k w f n (BitString.replaceRow (w n) (k n) j x Z) =
      plantedImage k w f n j (f x) Z := by
  unfold parallelCore plantedImage
  refine List.flatMap_congr fun i hi => ?_
  rw [BitString.listRow_replaceRow hx Z (List.mem_range.mp hi)]
  split_ifs <;> rfl

/-! ### Candidate selection, mega-trials, and repeated trials -/

private def pickPreimage (f : List Bool → List Bool) (y : List Bool)
    (cands : List (List Bool)) : List Bool :=
  (cands.filter (fun z => f z == y)).headD []

private theorem eval_pickPreimage {f : List Bool → List Bool} {y : List Bool}
    {cands : List (List Bool)} {x' : List Bool} (hx' : x' ∈ cands) (heq : f x' = y) :
    f (pickPreimage f y cands) = y := by
  have hmem : x' ∈ cands.filter (fun z => f z == y) :=
    List.mem_filter.mpr ⟨hx', beq_iff_eq.mpr heq⟩
  unfold pickPreimage
  cases h : cands.filter (fun z => f z == y) with
  | nil => simp [h] at hmem
  | cons a l =>
    have ha : a ∈ cands.filter (fun z => f z == y) := h ▸ List.mem_cons_self ..
    simpa [List.headD] using beq_iff_eq.mp (List.mem_filter.mp ha).2

private def slotCand (k w : ℕ → ℕ) (f : List Bool → List Bool)
    (evalA : (ℕ × List Bool) → List Bool → List Bool)
    (n : ℕ) (y seed : List Bool) (j : ℕ) : List Bool :=
  BitString.listRow (w n) j
    (evalA (n, plantedImage k w f n j y (seed.take (k n * w n)))
      (seed.drop (k n * w n)))

private def megaTrial (k w : ℕ → ℕ) (f : List Bool → List Bool)
    (evalA : (ℕ × List Bool) → List Bool → List Bool)
    (n : ℕ) (y seed : List Bool) : List Bool :=
  pickPreimage f y ((List.range (k n)).map (slotCand k w f evalA n y seed))

private theorem eval_megaTrial_of_slotCand {k w : ℕ → ℕ} {f : List Bool → List Bool}
    {evalA : (ℕ × List Bool) → List Bool → List Bool}
    {n : ℕ} {y seed : List Bool} {j : ℕ} (hj : j < k n)
    (h : f (slotCand k w f evalA n y seed j) = y) :
    f (megaTrial k w f evalA n y seed) = y :=
  eval_pickPreimage (List.mem_map_of_mem (List.mem_range.mpr hj)) h

private def runTrials (k w t seedLen : ℕ → ℕ) (f : List Bool → List Bool)
    (evalA : (ℕ × List Bool) → List Bool → List Bool)
    (n : ℕ) (y allSeeds : List Bool) : List Bool :=
  pickPreimage f y
    ((List.range (t n)).map (fun r =>
      megaTrial k w f evalA n y (BitString.listRow (seedLen n) r allSeeds)))

private theorem runTrials_fail_imp_all_fail {k w t seedLen : ℕ → ℕ} {f : List Bool → List Bool}
    {evalA : (ℕ × List Bool) → List Bool → List Bool}
    {n : ℕ} {y allSeeds : List Bool}
    (hfail : (f (runTrials k w t seedLen f evalA n y allSeeds) == y) = false) :
    ((List.range (t n)).all (fun r =>
      !(f (megaTrial k w f evalA n y (BitString.listRow (seedLen n) r allSeeds)) == y))) =
      true := by
  rw [List.all_eq_true]
  intro r hr
  rw [Bool.not_eq_true']
  by_cases h : f (megaTrial k w f evalA n y (BitString.listRow (seedLen n) r allSeeds)) == y
  · have hrun : f (runTrials k w t seedLen f evalA n y allSeeds) = y :=
      eval_pickPreimage (List.mem_map_of_mem hr) (beq_iff_eq.mp h)
    exact False.elim (Bool.false_ne_true (hfail.symm.trans (beq_iff_eq.mpr hrun)))
  · exact Bool.eq_false_iff.mpr h

/-! ### Polynomial-time certificates for the reduction -/

private theorem computableTidily_pickPreimage {α : Type} {input : α ↪ List Bool}
    {f : List Bool → List Bool} {y : α → List Bool} {cands : α → List (List Bool)}
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hy : ComputableTidilyInPolyTime y input encBits)
    (hcands : ComputableTidilyInPolyTime cands input (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => pickPreimage f (y a) (cands a)) input encBits := by
  unfold pickPreimage
  have hfilt : ComputableTidilyInPolyTime
      (fun a => (cands a).filter (fun z => f z == y a)) input (encList encBits) := by
    apply ComputableTidilyInPolyTime.filterWithInput hcands
    exact (hf.comp (ComputableTidilyInPolyTime.snd input encBits)).beq
      (hy.comp (ComputableTidilyInPolyTime.fst input encBits))
  exact (ComputableTidilyInPolyTime.headD []).comp hfilt

private theorem computableTidily_plantedImage {α : Type} {input : α ↪ List Bool}
    {k w : ℕ → ℕ} {f : List Bool → List Bool}
    {n j : α → ℕ} {y Z : α → List Bool}
    (hk : ComputableTidilyInPolyTime k encUnary encUnary)
    (hw : ComputableTidilyInPolyTime w encUnary encUnary)
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hj : ComputableTidilyInPolyTime j input encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits)
    (hZ : ComputableTidilyInPolyTime Z input encBits) :
    ComputableTidilyInPolyTime
      (fun a => plantedImage k w f (n a) (j a) (y a) (Z a)) input encBits := by
  unfold plantedImage
  apply ComputableTidilyInPolyTime.flatMapToBitsWithInput
    (ComputableTidilyInPolyTime.range.comp (hk.comp hn))
  have hfst := ComputableTidilyInPolyTime.fst input encUnary
  have hsnd := ComputableTidilyInPolyTime.snd input encUnary
  have hrow := ComputableTidilyInPolyTime.bitsRowWithInput
    ((hw.comp hn).comp hfst) hsnd (hZ.comp hfst)
  exact ComputableTidilyInPolyTime.ite_decide
    (ComputableTidilyInPolyTime.unary_beq hsnd (hj.comp hfst))
    (hy.comp hfst) (hf.comp hrow)

private theorem computableTidily_slotCand {α : Type} {input : α ↪ List Bool}
    {k w : ℕ → ℕ} {f : List Bool → List Bool}
    {evalA : (ℕ × List Bool) → List Bool → List Bool}
    {n j : α → ℕ} {y seed : α → List Bool}
    (hk : ComputableTidilyInPolyTime k encUnary encUnary)
    (hw : ComputableTidilyInPolyTime w encUnary encUnary)
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hevalA : ComputableTidilyInPolyTime (fun p : (ℕ × List Bool) × List Bool => evalA p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBits)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hj : ComputableTidilyInPolyTime j input encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits)
    (hseed : ComputableTidilyInPolyTime seed input encBits) :
    ComputableTidilyInPolyTime
      (fun a => slotCand k w f evalA (n a) (y a) (seed a) (j a)) input encBits := by
  unfold slotCand
  have hkw : ComputableTidilyInPolyTime (fun a => k (n a) * w (n a)) input encUnary :=
    ComputableTidilyInPolyTime.unary_mul.comp ((hk.comp hn).prod (hw.comp hn))
  have hZ : ComputableTidilyInPolyTime (fun a => (seed a).take (k (n a) * w (n a)))
      input encBits :=
    ComputableTidilyInPolyTime.bitsTakeWithInput hseed hkw
  have hcoins : ComputableTidilyInPolyTime (fun a => (seed a).drop (k (n a) * w (n a)))
      input encBits :=
    ComputableTidilyInPolyTime.bitsDropWithInput hseed hkw
  have hplant := computableTidily_plantedImage hk hw hf hn hj hy hZ
  have hout := hevalA.comp ((hn.prod hplant).prod hcoins)
  exact ComputableTidilyInPolyTime.bitsRowWithInput (hw.comp hn) hj hout

private theorem computableTidily_megaTrial {α : Type} {input : α ↪ List Bool}
    {k w : ℕ → ℕ} {f : List Bool → List Bool}
    {evalA : (ℕ × List Bool) → List Bool → List Bool}
    {n : α → ℕ} {y seed : α → List Bool}
    (hk : ComputableTidilyInPolyTime k encUnary encUnary)
    (hw : ComputableTidilyInPolyTime w encUnary encUnary)
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hevalA : ComputableTidilyInPolyTime (fun p : (ℕ × List Bool) × List Bool => evalA p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBits)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits)
    (hseed : ComputableTidilyInPolyTime seed input encBits) :
    ComputableTidilyInPolyTime
      (fun a => megaTrial k w f evalA (n a) (y a) (seed a)) input encBits := by
  unfold megaTrial
  apply computableTidily_pickPreimage hf hy
  apply ComputableTidilyInPolyTime.mapWithInput (encA := encUnary)
    (ComputableTidilyInPolyTime.range.comp (hk.comp hn))
  have hfst := ComputableTidilyInPolyTime.fst input encUnary
  have hsnd := ComputableTidilyInPolyTime.snd input encUnary
  exact computableTidily_slotCand hk hw hf hevalA
    (hn.comp hfst) hsnd (hy.comp hfst) (hseed.comp hfst)

private theorem computableTidily_runTrials {α : Type} {input : α ↪ List Bool}
    {k w t seedLen : ℕ → ℕ} {f : List Bool → List Bool}
    {evalA : (ℕ × List Bool) → List Bool → List Bool}
    {n : α → ℕ} {y allSeeds : α → List Bool}
    (hk : ComputableTidilyInPolyTime k encUnary encUnary)
    (hw : ComputableTidilyInPolyTime w encUnary encUnary)
    (ht : ComputableTidilyInPolyTime t encUnary encUnary)
    (hseedLen : ComputableTidilyInPolyTime seedLen encUnary encUnary)
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hevalA : ComputableTidilyInPolyTime (fun p : (ℕ × List Bool) × List Bool => evalA p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBits)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits)
    (hallSeeds : ComputableTidilyInPolyTime allSeeds input encBits) :
    ComputableTidilyInPolyTime
      (fun a => runTrials k w t seedLen f evalA (n a) (y a) (allSeeds a)) input encBits := by
  unfold runTrials
  apply computableTidily_pickPreimage hf hy
  apply ComputableTidilyInPolyTime.mapWithInput (encA := encUnary)
    (ComputableTidilyInPolyTime.range.comp (ht.comp hn))
  have hfst := ComputableTidilyInPolyTime.fst input encUnary
  have hsnd := ComputableTidilyInPolyTime.snd input encUnary
  have hrow := ComputableTidilyInPolyTime.bitsRowWithInput
    ((hseedLen.comp hn).comp hfst) hsnd (hallSeeds.comp hfst)
  exact computableTidily_megaTrial hk hw hf hevalA (hn.comp hfst) (hy.comp hfst) hrow

/-! ### Quantitative probability bounds at a fixed security parameter -/

private theorem slot_event_eq_planted {k w : ℕ → ℕ} {f : List Bool → List Bool}
    {evalA : (ℕ × List Bool) → List Bool → List Bool}
    (n B : ℕ) (good : List Bool → Bool) {j : ℕ} (hj : j < k n) :
    (((BitString.uniformList (k n * w n)).bind (fun X =>
      (BitString.uniformList B).map (fun coins =>
        !good (BitString.listRow (w n) j X) &&
          (f (BitString.listRow (w n) j (evalA (n, parallelCore k w f n X) coins)) ==
            f (BitString.listRow (w n) j X))))) true) =
    (((BitString.uniformList (w n)).bind (fun x =>
      (BitString.uniformList (k n * w n + B)).map (fun seed =>
        !good x && (f (slotCand k w f evalA n (f x) seed j) == f x)))) true) := by
  congr 1
  conv_lhs =>
    rw [← BitString.uniformList_replaceRow (w n) (k n) ⟨j, hj⟩, PMF.bind_bind]
  apply PMF.bind_congr_on_support
  intro x hx
  have hx_len : x.length = w n := BitString.length_of_mem_support_uniformList hx
  rw [PMF.bind_map]
  simp only [Function.comp_def, PMF.map]
  rw [← BitString.uniformList_bind_split (k n * w n) B]
  simp only [BitString.listRow_replaceRow hx_len _ hj, ↓reduceIte,
    parallelCore_replaceRow f n j hx_len, slotCand]

private theorem parallelCore_inversion_le {k w outLen : ℕ → ℕ} {f : List Bool → List Bool}
    (hlen : ∀ x, (f x).length = outLen x.length)
    {evalA : (ℕ × List Bool) → List Bool → List Bool}
    (n B : ℕ) (good : List Bool → Bool) {c : ENNReal}
    (hc : ∀ j < k n, ∀ x, x.length = w n → good x = false →
      (((BitString.uniformList (k n * w n + B)).map (fun seed =>
        f (slotCand k w f evalA n (f x) seed j) == f x)) true) ≤ c) :
    (((BitString.uniformList (k n * w n)).bind (fun X =>
      (BitString.uniformList B).map (fun coins =>
        parallelCore k w f n (evalA (n, parallelCore k w f n X) coins) ==
          parallelCore k w f n X))) true) ≤
      (((BitString.uniformList (w n)).map good) true) ^ (k n) + (k n : ENNReal) * c := by
  let joint : PMF (List Bool × List Bool) :=
    (BitString.uniformList (k n * w n)).bind (fun X =>
      (BitString.uniformList B).map (fun coins => (X, coins)))
  let E (p : List Bool × List Bool) : Bool :=
    parallelCore k w f n (evalA (n, parallelCore k w f n p.1) p.2) ==
      parallelCore k w f n p.1
  let E₀ (p : List Bool × List Bool) : Bool :=
    (List.range (k n)).all (fun j => good (BitString.listRow (w n) j p.1))
  let F (j : ℕ) (p : List Bool × List Bool) : Bool :=
    !good (BitString.listRow (w n) j p.1) &&
      (f (BitString.listRow (w n) j (evalA (n, parallelCore k w f n p.1) p.2)) ==
        f (BitString.listRow (w n) j p.1))
  have hjoint_map (G : List Bool × List Bool → Bool) :
      (joint.map G) true =
        ((BitString.uniformList (k n * w n)).bind (fun X =>
          (BitString.uniformList B).map (fun coins => G (X, coins)))) true := by
    simp [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hsplit : ∀ p ∈ joint.support, E p = true →
      E₀ p = true ∨ ((List.range (k n)).any (fun j => F j p)) = true := by
    rintro ⟨X, coins⟩ _ hE
    by_cases h0 : E₀ (X, coins) = true
    · exact Or.inl h0
    · right
      have h0_false :
          ((List.range (k n)).all (fun j => good (BitString.listRow (w n) j X))) = false :=
        Bool.eq_false_iff.mpr h0
      obtain ⟨j, hj_mem, hj_bad⟩ := List.all_eq_false.mp h0_false
      rw [List.any_eq_true]
      refine ⟨j, hj_mem, ?_⟩
      have hrow_eq := parallelCore_eq_imp_row_eq hlen (beq_iff_eq.mp hE)
        (List.mem_range.mp hj_mem)
      simp [F, Bool.eq_false_iff.mpr hj_bad, hrow_eq]
  have hle1 : (joint.map E) true ≤
      (joint.map E₀) true + ∑ j ∈ Finset.range (k n), (joint.map (F j)) true :=
    (PMF.map_true_le_add joint hsplit).trans
      (add_le_add_right (PMF.map_any_range_true_le_sum joint (k n) F) _)
  have hE0_eq : (joint.map E₀) true =
      (((BitString.uniformList (w n)).map good) true) ^ (k n) := by
    rw [hjoint_map E₀]
    have hbind : ((BitString.uniformList (k n * w n)).bind (fun X =>
        (BitString.uniformList B).map (fun coins => E₀ (X, coins)))) =
      (BitString.uniformList (k n * w n)).map (fun X =>
        (List.range (k n)).all (fun j => good (BitString.listRow (w n) j X))) := by
      simp only [E₀, PMF.map, Function.comp_def, PMF.bind_const]
    rw [hbind, BitString.uniformList_all_listRow_true]
  have hF_le : ∀ j ∈ Finset.range (k n), (joint.map (F j)) true ≤ c := by
    intro j hj
    have hj_lt : j < k n := Finset.mem_range.mp hj
    rw [hjoint_map (F j), slot_event_eq_planted n B good hj_lt]
    refine PMF.bind_apply_le_on_support _ fun x hx => ?_
    have hx_len : x.length = w n := BitString.length_of_mem_support_uniformList hx
    by_cases hgx : good x = true
    · simp [hgx]
    · have hgf : good x = false := Bool.eq_false_iff.mpr hgx
      simpa [hgf] using hc j hj_lt x hx_len hgf
  have hsum_le : ∑ j ∈ Finset.range (k n), (joint.map (F j)) true ≤ (k n : ENNReal) * c := by
    calc ∑ j ∈ Finset.range (k n), (joint.map (F j)) true
      _ ≤ ∑ _ ∈ Finset.range (k n), c := Finset.sum_le_sum hF_le
      _ = (k n : ENNReal) * c := by simp
  rw [← hjoint_map E]
  exact hle1.trans (by rw [hE0_eq]; exact add_le_add_right hsum_le _)

private theorem good_prob_le_runTrials {k w t seedLen : ℕ → ℕ} {f : List Bool → List Bool}
    {evalA : (ℕ × List Bool) → List Bool → List Bool}
    (n : ℕ) (good : List Bool → Bool) {c : ENNReal}
    (hc : ∀ x, x.length = w n → good x = true → ∃ j < k n,
      c ≤ ((BitString.uniformList (seedLen n)).map (fun seed =>
        f (slotCand k w f evalA n (f x) seed j) == f x)) true) :
    (((BitString.uniformList (w n)).map good) true) ≤
      (((BitString.uniformList (w n)).bind (fun x =>
        (BitString.uniformList (t n * seedLen n)).map (fun allSeeds =>
          f (runTrials k w t seedLen f evalA n (f x) allSeeds) == f x))) true) +
        (1 - c) ^ (t n) := by
  let joint : PMF (List Bool × List Bool) :=
    (BitString.uniformList (w n)).bind (fun x =>
      (BitString.uniformList (t n * seedLen n)).map (fun allSeeds => (x, allSeeds)))
  let G (p : List Bool × List Bool) : Bool := good p.1
  let S (p : List Bool × List Bool) : Bool :=
    f (runTrials k w t seedLen f evalA n (f p.1) p.2) == f p.1
  let R (p : List Bool × List Bool) : Bool :=
    good p.1 && !(f (runTrials k w t seedLen f evalA n (f p.1) p.2) == f p.1)
  have hjoint_map (H : List Bool × List Bool → Bool) :
      (joint.map H) true =
        ((BitString.uniformList (w n)).bind (fun x =>
          (BitString.uniformList (t n * seedLen n)).map
            (fun allSeeds => H (x, allSeeds)))) true := by
    simp [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hsplit : ∀ p ∈ joint.support, G p = true → S p = true ∨ R p = true := by
    rintro ⟨x, allSeeds⟩ _ hG
    by_cases hS : S (x, allSeeds) = true
    · exact Or.inl hS
    · right
      dsimp [G, R, S] at hG hS ⊢
      simp [hG, Bool.eq_false_iff.mpr hS]
  have hG_eq : (joint.map G) true = ((BitString.uniformList (w n)).map good) true := by
    rw [hjoint_map G]
    simp only [G, PMF.map, Function.comp_def, PMF.bind_const]
  have hR_le : (joint.map R) true ≤ (1 - c) ^ (t n) := by
    rw [hjoint_map R]
    refine PMF.bind_apply_le_on_support _ fun x hx => ?_
    have hx_len : x.length = w n := BitString.length_of_mem_support_uniformList hx
    by_cases hgx : good x = true
    · obtain ⟨j, hj_lt, hj_c⟩ := hc x hx_len hgx
      let succSeed (seed : List Bool) : Bool :=
        f (megaTrial k w f evalA n (f x) seed) == f x
      let failSeed (seed : List Bool) : Bool := !succSeed seed
      have hle_all :
          ((BitString.uniformList (t n * seedLen n)).map (fun allSeeds => R (x, allSeeds))) true ≤
            ((BitString.uniformList (t n * seedLen n)).map (fun allSeeds =>
              (List.range (t n)).all (fun r =>
                failSeed (BitString.listRow (seedLen n) r allSeeds)))) true := by
        refine PMF.map_true_mono _ fun allSeeds _ hR_true => ?_
        dsimp [R] at hR_true
        rw [Bool.and_eq_true, Bool.not_eq_true'] at hR_true
        exact runTrials_fail_imp_all_fail hR_true.2
      rw [BitString.uniformList_all_listRow_true] at hle_all
      refine hle_all.trans (pow_le_pow_left' ?_ (t n))
      have hsucc_ge : c ≤ ((BitString.uniformList (seedLen n)).map succSeed) true :=
        hj_c.trans (PMF.map_true_mono _ fun seed _ hs =>
          beq_iff_eq.mpr (eval_megaTrial_of_slotCand hj_lt (beq_iff_eq.mp hs)))
      rw [show failSeed = fun seed => !succSeed seed from rfl, PMF.map_not_true]
      exact tsub_le_tsub_left hsucc_ge 1
    · have hgf : good x = false := Bool.eq_false_iff.mpr hgx
      simp [R, hgf]
  have h1 := PMF.map_true_le_add joint hsplit
  rw [hG_eq, hjoint_map S] at h1
  exact h1.trans (add_le_add_right hR_le _)

/-- Any uniform strict PPT adversary has negligible inversion probability against `parallelCore`
on schedule `m n = (2 * q.eval (n + 1) * (n + 1)) * (n + 1)` when `f` has fixed output length
`outLen` and is `(1 / q(·))`-weak one-way. -/
theorem familyInversionGame_parallelCore_negligible {f : List Bool → List Bool}
    {outLen : ℕ → ℕ} (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hlen : ∀ x, (f x).length = outLen x.length)
    {q : Polynomial ℕ} (hq_pos : ∀ N, 0 < q.eval N)
    (hweak : WeakOneWayAt f (fun N => 1 / ((q.eval N : ℕ) : ℝ)))
    (A : Inverter) (hA : IsPPT encBits A) :
    Negligible (fun n =>
      Game.succProbability (ProbComp.eval
        (OneWayReindex.familyInversionGame
          (fun n => (2 * q.eval (n + 1) * (n + 1)) * (n + 1))
          (parallelCore (fun n => 2 * q.eval (n + 1) * (n + 1)) (fun n => n + 1) f) A n))) := by
  classical
  let w : ℕ → ℕ := fun n => n + 1
  let k : ℕ → ℕ := fun n => 2 * q.eval (w n) * w n
  change Negligible (fun n =>
    Game.succProbability (ProbComp.eval
      (OneWayReindex.familyInversionGame (fun n => k n * w n)
        (parallelCore k w f) A n)))
  apply negligible_iff_coe.mpr
  intro deg
  let p : ℕ → ℕ := fun n => (n + 1) ^ (deg + 1)
  have hp_pos : ∀ n, 0 < p n := fun n => by dsimp [p]; positivity
  have hk_pos : ∀ n, 0 < k n := fun n => by
    have := hq_pos (w n)
    dsimp [k, w]
    positivity
  obtain ⟨cA, dA, evalA, hevalA, _, hlawA⟩ := hA.on.exists_total_seeded_evaluator
  let B : ℕ → ℕ := fun n => cA * (2 * n + k n * outLen (w n) + 2) ^ dA
  let seedLen : ℕ → ℕ := fun n => k n * w n + B n
  let t : ℕ → ℕ := fun n => 4 * q.eval (w n) * (k n * p n)
  let B_inv (N : ℕ) (y : List Bool) : ProbComp (List Bool) :=
    runTrials k w t seedLen f evalA (N - 1) y <$>
      BitString.sampleList (t (N - 1) * seedLen (N - 1))
  have hB_ppt : IsPPT encBits B_inv := by
    apply IsPPTOn.isPPT
    have hfst := ComputableTidilyInPolyTime.fst encUnary encBits
    have hsnd := ComputableTidilyInPolyTime.snd encUnary encBits
    have hw : ComputableTidilyInPolyTime w encUnary encUnary := by dsimp [w]; fun_prop
    have hq : ComputableTidilyInPolyTime (fun N => q.eval N) encUnary encUnary :=
      ComputableTidilyInPolyTime.unary_eval q
    have hk : ComputableTidilyInPolyTime k encUnary encUnary := by dsimp [k]; fun_prop
    have hp : ComputableTidilyInPolyTime p encUnary encUnary := by dsimp [p]; fun_prop
    have ht : ComputableTidilyInPolyTime t encUnary encUnary := by dsimp [t]; fun_prop
    have hout_tidy := houtLen.tidy
    have hB : ComputableTidilyInPolyTime B encUnary encUnary := by dsimp [B]; fun_prop
    have hseedLen : ComputableTidilyInPolyTime seedLen encUnary encUnary := by
      dsimp [seedLen]; fun_prop
    have hn : ComputableTidilyInPolyTime (fun pair : ℕ × List Bool => pair.1 - 1)
        (encPair encUnary encBits) encUnary := by fun_prop
    have hsample_len : ComputableTidilyInPolyTime
        (fun pair : ℕ × List Bool => t (pair.1 - 1) * seedLen (pair.1 - 1))
        (encPair encUnary encBits) encUnary :=
      ComputableTidilyInPolyTime.unary_mul.comp ((ht.comp hn).prod (hseedLen.comp hn))
    have hfst2 := ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encBits
    have hsnd2 := ComputableTidilyInPolyTime.snd (encPair encUnary encBits) encBits
    have hrun := computableTidily_runTrials hk hw ht hseedLen hweak.polyTime.tidy hevalA
      (hn.comp hfst2) (hsnd.comp hfst2) hsnd2
    exact IsPPTOn.map_with (ComputableInPolyTime.of_tidy hsample_len).sampleList (.of_tidy hrun)
  have hweak_w : ∀ᶠ n in atTop,
      (Game.succProbability (ProbComp.eval (inversionGame f B_inv (w n))) : ℝ) <
        1 - 1 / ((q.eval (w n) : ℕ) : ℝ) :=
    (Filter.tendsto_add_atTop_nat 1).eventually (hweak.weak B_inv hB_ppt)
  have hgeom : ∀ᶠ n in atTop, ((1 / 2 : ℝ≥0) ^ n : ℝ) ≤ 1 / (p n : ℝ) :=
    (negligible_geometric (by norm_num : (1 / 2 : ℝ≥0) < 1)).eventually_le_inv_polynomial
      (by dsimp [p]; fun_prop) hp_pos
  have hbound : ∀ᶠ n in atTop,
      (Game.succProbability (ProbComp.eval
        (OneWayReindex.familyInversionGame (fun n => k n * w n)
          (parallelCore k w f) A n)) : ℝ) ≤ 1 / (p n : ℝ) := by
    filter_upwards [hweak_w, hgeom] with n hn_weak hn_geom
    let m_np : ℕ := k n * p n
    have hm_pos : 0 < m_np := Nat.mul_pos (hk_pos n) (hp_pos n)
    let θ : ℝ := 1 / (2 * (m_np : ℝ))
    have hθ_nonneg : 0 ≤ θ := by dsimp [θ]; positivity
    have hθ_le_one : θ ≤ 1 := by
      dsimp [θ]
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ m_np := by exact_mod_cast hm_pos
      linarith
    let c : ENNReal := ENNReal.ofReal θ
    let good (x : List Bool) : Bool :=
      decide (∃ j < k n, c ≤
        ((BitString.uniformList (seedLen n)).map (fun seed =>
          f (slotCand k w f evalA n (f x) seed j) == f x)) true)
    have hfam_eq :
        (ProbComp.eval (OneWayReindex.familyInversionGame (fun n => k n * w n)
          (parallelCore k w f) A n)) true =
          (((BitString.uniformList (k n * w n)).bind (fun X =>
            (BitString.uniformList (B n)).map (fun coins =>
              parallelCore k w f n (evalA (n, parallelCore k w f n X) coins) ==
                parallelCore k w f n X))) true) := by
      unfold OneWayReindex.familyInversionGame
      simp only [ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
      congr 1
      apply PMF.bind_congr_on_support
      intro X _
      have hbudget :
          cA * ((encPair encUnary encBits (n, parallelCore k w f n X)).length + 1) ^ dA ≤ B n := by
        rw [length_encPair]
        simp only [encUnary_apply, List.length_replicate, encBits_apply, length_parallelCore hlen,
          B]
        have heq : 2 * n + 1 + k n * outLen (w n) + 1 = 2 * n + k n * outLen (w n) + 2 := by omega
        rw [heq]
      rw [hlawA (n, parallelCore k w f n X) (B n) hbudget, PMF.bind_map]
      simp only [PMF.map, Function.comp_def, parallelCore_take]
    have hinv_eq :
        (ProbComp.eval (inversionGame f B_inv (w n))) true =
          (((BitString.uniformList (w n)).bind (fun x =>
            (BitString.uniformList (t n * seedLen n)).map (fun allSeeds =>
              f (runTrials k w t seedLen f evalA n (f x) allSeeds) == f x))) true) := by
      simp [inversionGame, B_inv, w, PMF.map]
    have hc_bad : ∀ j < k n, ∀ x, x.length = w n → good x = false →
        (((BitString.uniformList (k n * w n + B n)).map (fun seed =>
          f (slotCand k w f evalA n (f x) seed j) == f x)) true) ≤ c := by
      intro j hj x _ hgf
      have hnot : ¬ ∃ i < k n, c ≤
          ((BitString.uniformList (seedLen n)).map (fun seed =>
            f (slotCand k w f evalA n (f x) seed i) == f x)) true :=
        decide_eq_false_iff_not.mp hgf
      by_contra hlt
      exact hnot ⟨j, hj, le_of_not_ge hlt⟩
    have hc_good : ∀ x, x.length = w n → good x = true → ∃ j < k n,
        c ≤ ((BitString.uniformList (seedLen n)).map (fun seed =>
          f (slotCand k w f evalA n (f x) seed j) == f x)) true := by
      intro x _ hgt
      exact of_decide_eq_true hgt
    have hpar_le := parallelCore_inversion_le hlen n (B n) good hc_bad
    have hgood_le := good_prob_le_runTrials (t := t) n good hc_good
    rw [← hfam_eq] at hpar_le
    rw [← hinv_eq] at hgood_le
    have h1mc_ne_top : (1 - c) ^ (t n) ≠ ⊤ :=
      ENNReal.pow_ne_top ((tsub_le_self.trans_lt ENNReal.one_lt_top).ne)
    have hgood_real :
        (((BitString.uniformList (w n)).map good) true).toReal ≤
          (Game.succProbability (ProbComp.eval (inversionGame f B_inv (w n))) : ℝ) +
            (1 - θ) ^ (t n) := by
      have hle := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨((PMF.coe_le_one _ _).trans_lt ENNReal.one_lt_top).ne,
          h1mc_ne_top⟩) hgood_le
      rw [ENNReal.toReal_add ((PMF.coe_le_one _ _).trans_lt ENNReal.one_lt_top).ne h1mc_ne_top,
        ENNReal.toReal_pow, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub 1 hθ_nonneg,
        ENNReal.toReal_ofReal (by linarith)] at hle
      exact hle
    have ht_pow : (1 - θ) ^ (t n) ≤ 1 / (2 * ((q.eval (w n) : ℕ) : ℝ)) :=
      pow_one_sub_le_inv_two_mul (hq_pos (w n)) hm_pos
    have hgood_lt :
        (((BitString.uniformList (w n)).map good) true).toReal ≤
          1 - 1 / (2 * ((q.eval (w n) : ℕ) : ℝ)) := by
      have hhalf :
          1 - 1 / ((q.eval (w n) : ℕ) : ℝ) + 1 / (2 * ((q.eval (w n) : ℕ) : ℝ)) =
            1 - 1 / (2 * ((q.eval (w n) : ℕ) : ℝ)) := by ring
      linarith
    have hgood_pow_le :
        ((((BitString.uniformList (w n)).map good) true).toReal) ^ (k n) ≤
          (1 / 2 : ℝ) ^ (w n) := by
      have hpow1 :
          ((((BitString.uniformList (w n)).map good) true).toReal) ^ (k n) ≤
            (1 - 1 / (2 * ((q.eval (w n) : ℕ) : ℝ))) ^ (k n) :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg hgood_lt (k n)
      exact hpow1.trans (pow_one_sub_inv_two_mul_le (hq_pos (w n)) (w n))
    have hk_ne_top : (k n : ENNReal) * c ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top (k n)) ENNReal.ofReal_ne_top
    have hpar_real :
        (Game.succProbability (ProbComp.eval
          (OneWayReindex.familyInversionGame (fun n => k n * w n)
            (parallelCore k w f) A n)) : ℝ) ≤
          ((((BitString.uniformList (w n)).map good) true).toReal) ^ (k n) +
            (k n : ℝ) * θ := by
      have hg_pow_ne_top : (((BitString.uniformList (w n)).map good) true) ^ (k n) ≠ ⊤ :=
        ENNReal.pow_ne_top ((PMF.coe_le_one _ _).trans_lt ENNReal.one_lt_top).ne
      have hle := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hg_pow_ne_top, hk_ne_top⟩) hpar_le
      rw [ENNReal.toReal_add hg_pow_ne_top hk_ne_top, ENNReal.toReal_pow,
        ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hθ_nonneg] at hle
      exact hle
    have hk_θ : (k n : ℝ) * θ = 1 / (2 * (p n : ℝ)) := by
      dsimp [θ, m_np]
      have hkR : (k n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hk_pos n).ne'
      have hpR : (p n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hp_pos n).ne'
      push_cast
      field_simp
    have hgeom_w : (1 / 2 : ℝ) ^ (w n) ≤ 1 / (2 * (p n : ℝ)) := by
      have h1 : ((1 / 2 : ℝ≥0) ^ n : ℝ) = (1 / 2 : ℝ) ^ n := by push_cast; rfl
      rw [h1] at hn_geom
      have h2 : (1 / 2 : ℝ) ^ (w n) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
        dsimp [w]
        rw [pow_succ']
      rw [h2]
      have h3 : (1 / 2 : ℝ) * (1 / (p n : ℝ)) = 1 / (2 * (p n : ℝ)) := by ring
      linarith
    have hhalf2 : 1 / (2 * (p n : ℝ)) + 1 / (2 * (p n : ℝ)) = 1 / (p n : ℝ) := by ring
    linarith
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hzero
  filter_upwards [hbound] with n hn
  have h1 : (n : ℝ) ^ deg ≤ ((n + 1 : ℕ) : ℝ) ^ deg := by
    gcongr
    exact_mod_cast Nat.le_succ n
  calc (n : ℝ) ^ deg *
        (Game.succProbability (ProbComp.eval
          (OneWayReindex.familyInversionGame (fun n => k n * w n)
            (parallelCore k w f) A n)) : ℝ)
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ deg * (1 / (p n : ℝ)) :=
        mul_le_mul h1 hn (by positivity) (by positivity)
    _ = 1 / ((n : ℝ) + 1) := by
        dsimp [p]
        have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        rw [pow_succ]
        field_simp

end OneWayAmplification

/-- **Yao's Weak-to-Strong One-Way Function Hardness Amplification**
([Liu and Pass, Theorem 2.3, §2.1, p. 8 of `arXiv:2009.11514v1`][LiuPass2020];
[Yao1982]; [Goldreich, Vol. 1, §2.3, Theorem 2.3.2][Goldreich2001]):
if `f` is a weak one-way function (`WeakOneWay f`), then there exists a strong one-way function
`F : List Bool → List Bool` (`OneWay F`). -/
theorem WeakOneWay.exists_oneWay {f : List Bool → List Bool} (hf : WeakOneWay f) :
    ∃ F : List Bool → List Bool, OneWay F := by
  obtain ⟨g, outLen, hg_weak, hlen, houtLen⟩ := hf.exists_fixedOutputLength
  obtain ⟨q, hq_pos, hg_at⟩ := hg_weak
  let w : ℕ → ℕ := fun n => n + 1
  let k : ℕ → ℕ := fun n => 2 * q.eval (w n) * w n
  let m : ℕ → ℕ := fun n => k n * w n
  have hm_ge : ∀ n, n + 1 ≤ m n := fun n => by
    have hk1 : 1 ≤ k n := by
      have hq1 : 1 ≤ q.eval (w n) := hq_pos (w n)
      have hw1 : 1 ≤ w n := by dsimp [w]; omega
      dsimp [k]
      nlinarith
    calc n + 1 = 1 * w n := by dsimp [w]; omega
      _ ≤ k n * w n := Nat.mul_le_mul_right (w n) hk1
  have hw_comp : ComputableTidilyInPolyTime w encUnary encUnary := by dsimp [w]; fun_prop
  have hq_comp : ComputableTidilyInPolyTime (fun N => q.eval N) encUnary encUnary :=
    ComputableTidilyInPolyTime.unary_eval q
  have hk_comp : ComputableTidilyInPolyTime k encUnary encUnary := by dsimp [k]; fun_prop
  have hm_comp : ComputableInPolyTime m encUnary encUnary := by
    apply ComputableInPolyTime.of_tidy
    dsimp [m]
    fun_prop
  have hcore_comp : ComputableInPolyTime
      (fun p : ℕ × List Bool => OneWayAmplification.parallelCore k w g p.1 p.2)
      (encPair encUnary encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    unfold OneWayAmplification.parallelCore
    have hfst := ComputableTidilyInPolyTime.fst encUnary encBits
    have hsnd := ComputableTidilyInPolyTime.snd encUnary encBits
    apply ComputableTidilyInPolyTime.flatMapToBitsWithInput
      (ComputableTidilyInPolyTime.range.comp (hk_comp.comp hfst))
    have hfst2 := ComputableTidilyInPolyTime.fst (encPair encUnary encBits) encUnary
    have hsnd2 := ComputableTidilyInPolyTime.snd (encPair encUnary encBits) encUnary
    have hrow := ComputableTidilyInPolyTime.bitsRowWithInput
      ((hw_comp.comp hfst).comp hfst2) hsnd2 (hsnd.comp hfst2)
    exact hg_at.polyTime.tidy.comp hrow
  refine ⟨OneWayReindex.reindex m (OneWayAmplification.parallelCore k w g), ?_⟩
  exact OneWayReindex.oneWay hm_comp hm_ge hcore_comp fun A hA =>
    OneWayAmplification.familyInversionGame_parallelCore_negligible
      houtLen hlen hq_pos hg_at A hA

/-- **Existential Form of Yao's Hardness Amplification**
([Liu and Pass, Theorem 2.3, §2.1, p. 8 of `arXiv:2009.11514v1`][LiuPass2020]):
if there exists a weak one-way function, then there exists a strong one-way function. -/
theorem exists_oneWay_of_exists_weakOneWay
    (h : ∃ f : List Bool → List Bool, WeakOneWay f) :
    ∃ F : List Bool → List Bool, OneWay F := by
  obtain ⟨f, hf⟩ := h
  exact hf.exists_oneWay

/-- **Equivalence of Weak and Strong One-Way Functions**
([Goldreich, Vol. 1, §2.3, Theorem 2.3.2][Goldreich2001]; weak-to-strong direction
[Liu and Pass, Theorem 2.3, §2.1, p. 8 of `arXiv:2009.11514v1`][LiuPass2020] and [Yao1982];
strong-to-weak direction `OneWay.weakOneWay`):
strong one-way functions exist if and only if weak one-way functions exist. -/
theorem exists_oneWay_iff_exists_weakOneWay :
    (∃ F : List Bool → List Bool, OneWay F) ↔
      (∃ f : List Bool → List Bool, WeakOneWay f) :=
  ⟨fun ⟨F, hF⟩ => ⟨F, hF.weakOneWay⟩, exists_oneWay_of_exists_weakOneWay⟩

end Cslib.Crypto
