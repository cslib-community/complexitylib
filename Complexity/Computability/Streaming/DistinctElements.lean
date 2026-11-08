/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Streaming.Basic
public import Complexity.Computability.Streaming.Frequency
public import Complexity.Foundations.Data.Finset.Lowest
public import Complexity.Foundations.Data.Finset.Median
public import Complexity.Probability.PairwiseIndependentHash
public import Mathlib.Order.Prod.Lex.Basic
import Complexity.Foundations.Combinatorics.SmallSubsets
import Complexity.Foundations.Data.Finset.LowestInsert
import Complexity.Foundations.Data.Nat.Choose.Sum
import Complexity.Probability.MedianOfMeans
import Complexity.Probability.PairwiseIndependentHash.Retention
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The k-minimum-values sketch for the number of distinct elements

The number of distinct items of a stream is `F₀ = #s.toFinset` (`Cslib.Streaming.freqMoment_zero`).
Bar-Yossef, Jayram, Kumar, Sivakumar and Trevisan estimate it in small space
[BarYossefJayramKumarSivakumarTrevisan2002, Theorem 1]. Hash the items by a pairwise independent
family `h θ : α → Fin M` and keep the `t` smallest hash values seen. If `d` distinct items have been
read, the `t`-th smallest of their `d` hash values is near `t M / d`, so `t M` divided by it
estimates `d`.

**The sketch.** Each copy (`Cslib.Streaming.kmvSketch`) keeps the `t` smallest keys
`(h θ a, a)` (`Cslib.Streaming.kmvKey`) in lexicographic order, selected by `Finset.lowest`. Each
item is inserted into the selection, and the selection is cut back to `t` keys. Since selection can
be maintained online (`Finset.lowest_insert_lowest`), after the stream `s` the copy holds the `t`
lowest keys of the distinct items of `s` (`Cslib.Streaming.state_kmvSketch`). Ties between hash
values are broken by the item, so collisions never merge two distinct items. While it holds fewer
than `t` keys, a copy reports their number, which is then exactly `F₀`. Otherwise it reports
`t M / (v + 1)`, where `v` is the largest hash value it keeps (`Cslib.Streaming.kmvEstimate`); hash
values are counted from `0`, so `v + 1` is the source's `t`-th smallest value in `[1, M]`. The
sketch answers the median of the estimates of its copies.

**Accuracy.** The `t` lowest hash values of `d ≥ t` items are all below `K` exactly when at least
`t` items hash below `K` (`Finset.forall_mem_lowest_iff`). The number of items hashing below `K`
has mean `d K / M` and variance at most its mean
(`Cslib.Probability.IsPairwiseIndependentHash.dens_le_abs_card_filter_apply_mem_sub_le`), and
Chebyshev's inequality bounds each side. For `0 < ε ≤ 1` and `d ≤ M`, one copy misses `d` by more
than `ε d` for at most a `2 / (t ε²)` fraction of seeds
(`Cslib.Streaming.dens_abs_kmvEstimate_sub_gt_le`). The two tails contribute `(1 + ε) / (t ε²)` and
`(1 - ε) / (t ε²)`; the source bounds each by `1 / 6` with `t = ⌈96 / ε²⌉`. For `6 ≤ t ε²` one
copy thus fails with probability at most `1 / 3`. The median trick
(`Cslib.Probability.dens_abs_median_sub_gt_le`, [Chakrabarti2025, Section 2.4]) brings the failure
probability of the median of `2 r` copies down to `(8 / 9) ^ r`
(`Cslib.Streaming.dens_kmvSketch_error_le`), so `kmv h t (2 r)` solves `F₀` estimation with
relative error `ε` and error probability `δ ≥ (8 / 9) ^ r` on streams of length at most `M`
(`Cslib.Streaming.solves_kmv`).

**Memory.** For fixed seeds, the reachable states are determined by the at most `t` items behind
each copy's keys. Their number is at most `(n + 1) ^ t` for a universe of `n` items. Under the
public-coin convention of `Cslib.Streaming.Randomized`, every sketch with `c` copies uses at most
`b` bits as soon as `(n + 1) ^ (c t) ≤ 2 ^ b` (`Cslib.Streaming.spaceLE_kmv`), on streams of any
length.
With the seeds stored as well, `(|ι| (n + 1) ^ t) ^ c ≤ 2 ^ b` suffices
(`Cslib.Streaming.exists_injOn_iUnion_reachable_kmvSketch`). With `t = ⌈6 / ε²⌉` and `c` of order
`log (1 / δ)` this is `O(ε⁻² log (1 / δ) log n)` bits, the bound of
[BarYossefJayramKumarSivakumarTrevisan2002, Theorem 1] (the source writes `m` for the size of the
universe).

**Differences from the source.** The source keeps bare hash values in `[1, m³]` and pays a `1 / m`
probability that `h` is not injective on the stream. Keeping the item beside the hash removes that
failure, and needs only `d ≤ M` rather than `M = m³`. The memory is still `O(log n)` bits per key,
since the key is determined by the item and the seed. The seeds are drawn as public coins and are
not charged by `Cslib.Streaming.spaceLE_kmv`.

This upper bound complements the `Ω(n)` lower bounds for computing `F₀` exactly with bounded error
and for approximating it deterministically (`Cslib.Streaming.le_of_solves_freqMoment`,
`Cslib.Streaming.Algorithm.le_of_approx_freqMoment` with `k = 0`): randomness together with
approximation brings the memory down to `O(ε⁻² log n)` bits for constant error. The matching
`Ω(ε⁻²)` lower bound is not formalized.

## Main definitions

* `Cslib.Streaming.kmvKey`, `Cslib.Streaming.kmvEstimate`: the sort key of an item and the estimate
  of one copy.
* `Cslib.Streaming.kmvSketch`: the k-minimum-values sketch with given seeds.
* `Cslib.Streaming.kmv`: the randomized sketch with uniform seeds.

## Main results

* `Cslib.Streaming.state_kmvSketch`: each copy holds the `t` lowest keys of the distinct items.
* `Cslib.Streaming.run_kmvSketch_of_card_lt`: with fewer than `t` distinct items the answer is
  exactly `F₀`.
* `Cslib.Streaming.dens_abs_kmvEstimate_sub_gt_le`: one copy misses `d` by more than `ε d` with
  probability at most `2 / (t ε²)`.
* `Cslib.Streaming.errorProb_kmv`: the error of the randomized sketch is the fraction of bad seeds.
* `Cslib.Streaming.dens_kmvSketch_error_le`: the median of `2 r` copies misses `F₀` by more than
  `ε F₀` with probability at most `(8 / 9) ^ r` when `6 ≤ t ε²`.
* `Cslib.Streaming.solves_kmv`: the randomized sketch solves `F₀` estimation.
* `Cslib.Streaming.spaceLE_kmv`: its memory under the public-coin convention.
* `Cslib.Streaming.exists_injOn_iUnion_reachable_kmvSketch`: its memory with the seeds stored.

## References

* [Z. Bar-Yossef, T. S. Jayram, R. Kumar, D. Sivakumar, L. Trevisan, *Counting distinct elements
  in a data stream*, Theorem 1][BarYossefJayramKumarSivakumarTrevisan2002]
* [A. Chakrabarti, *Data Stream Algorithms*, Section 2.4][Chakrabarti2025]
-/

public section

namespace Cslib.Streaming

open Finset Probability

variable {ι α : Type*} [LinearOrder α] {M t c : ℕ}

/-! ### The sketch -/

/-- The sort key of the item `a` under the seed `θ`: its hash value, ties broken by the item. -/
@[expose] def kmvKey (h : ι → α → Fin M) (θ : ι) (a : α) : Fin M ×ₗ α :=
  toLex (h θ a, a)

/-- The largest hash value among a set of keys (zero for the empty set). -/
@[expose] def kmvMaxHash (S : Finset (Fin M ×ₗ α)) : ℕ :=
  S.sup fun p => (ofLex p).1.val

/-- The estimate of `F₀` from a set `S` of at most `t` keys: their number if there are fewer than
`t`, and otherwise `t M / (v + 1)`, where `v` is the largest hash value in `S`. -/
noncomputable def kmvEstimate (M t : ℕ) (S : Finset (Fin M ×ₗ α)) : ℝ :=
  if S.card < t then S.card else t * M / ((kmvMaxHash S : ℝ) + 1)

/-- The memory of the k-minimum-values sketch with `c` copies: a seed and a set of keys for each
copy. -/
abbrev KMVState (ι α : Type*) (M c : ℕ) : Type _ :=
  (Fin c → ι) × (Fin c → Finset (Fin M ×ₗ α))

/-- The **k-minimum-values sketch** [BarYossefJayramKumarSivakumarTrevisan2002, Theorem 1] with
seeds `ω`: each copy `i` keeps the `t` lowest keys `kmvKey h (ω i) a` of the items read, and the
answer is the median over the copies of their estimates `Cslib.Streaming.kmvEstimate`. The seeds
are written in the initial memory and read back by the update, which does not otherwise depend on
`ω` (`Cslib.Streaming.update_kmvSketch`). -/
noncomputable def kmvSketch (h : ι → α → Fin M) (t c : ℕ) (ω : Fin c → ι) :
    Algorithm (KMVState ι α M c) α ℝ where
  init := (ω, fun _ => ∅)
  update q a := (q.1, fun i => lowest t (insert (kmvKey h (q.1 i) a) (q.2 i)))
  output q := median fun i => kmvEstimate M t (q.2 i)

/-- The randomized **k-minimum-values sketch**: the sketch with independent uniform seeds. -/
noncomputable def kmv [Fintype ι] [Nonempty ι] (h : ι → α → Fin M) (t c : ℕ) :
    Randomized (KMVState ι α M c) α ℝ :=
  (PMF.uniformOfFintype (Fin c → ι)).map (kmvSketch h t c)

variable {h : ι → α → Fin M}

omit [LinearOrder α] in
theorem kmvKey_injective (h : ι → α → Fin M) (θ : ι) : Function.Injective (kmvKey h θ) :=
  fun _ _ hab => (Prod.mk.inj (toLex_inj.1 hab)).2

omit [LinearOrder α] in
/-- With fewer than `t` keys, the estimate is their number. -/
theorem kmvEstimate_of_card_lt {S : Finset (Fin M ×ₗ α)} (hS : S.card < t) :
    kmvEstimate M t S = S.card :=
  ite_eq_left hS

omit [LinearOrder α] in
/-- With at least `t` keys, the estimate is `t M / (v + 1)` for the largest hash value `v`. -/
theorem kmvEstimate_of_le_card {S : Finset (Fin M ×ₗ α)} (hS : t ≤ S.card) :
    kmvEstimate M t S = t * M / ((kmvMaxHash S : ℝ) + 1) :=
  ite_eq_right (not_lt.2 hS)

/-- The sketch starts with its seeds and no keys. -/
theorem init_kmvSketch (ω : Fin c → ι) : (kmvSketch h t c ω).init = (ω, fun _ => ∅) := by
  simp only [kmvSketch]

/-- The update of the sketch reads the seeds from the memory: it does not depend on `ω`. -/
theorem update_kmvSketch (ω : Fin c → ι) (q : KMVState ι α M c) (a : α) :
    (kmvSketch h t c ω).update q a =
      (q.1, fun i => lowest t (insert (kmvKey h (q.1 i) a) (q.2 i))) := by
  simp only [kmvSketch]

/-- The output of the sketch does not depend on its seeds. -/
theorem output_kmvSketch (ω : Fin c → ι) (q : KMVState ι α M c) :
    (kmvSketch h t c ω).output q = median fun i => kmvEstimate M t (q.2 i) := by
  simp only [kmvSketch]

/-- From a memory holding the `t` lowest keys of the sets `T i`, reading `s` leads to the `t`
lowest keys of `T i` together with the keys of the items of `s`. -/
theorem stateFrom_kmvSketch (ω : Fin c → ι) (T : Fin c → Finset (Fin M ×ₗ α)) (s : List α) :
    (kmvSketch h t c ω).stateFrom (ω, fun i => lowest t (T i)) s =
      (ω, fun i => lowest t (s.toFinset.image (kmvKey h (ω i)) ∪ T i)) := by
  induction s generalizing T with
  | nil => simp only [Algorithm.stateFrom_nil, List.toFinset_nil, image_empty, empty_union]
  | cons a s ih =>
    rw [Algorithm.stateFrom_cons, update_kmvSketch]
    simp only [lowest_insert_lowest]
    refine (ih fun i => insert (kmvKey h (ω i) a) (T i)).trans ?_
    simp only [List.toFinset_cons, image_insert, union_insert, insert_union]

/-- **The state of the sketch**: after the stream `s`, the copy with seed `ω i` holds the `t` lowest
keys of the distinct items of `s`. -/
theorem state_kmvSketch (ω : Fin c → ι) (s : List α) :
    (kmvSketch h t c ω).state s = (ω, fun i => lowest t (s.toFinset.image (kmvKey h (ω i)))) := by
  have h0 : (kmvSketch h t c ω).init = (ω, fun _ => lowest t (∅ : Finset (Fin M ×ₗ α))) := by
    rw [init_kmvSketch, lowest_eq_self (by simp only [card_empty, zero_le])]
  rw [Algorithm.state, h0, stateFrom_kmvSketch]
  simp only [union_empty]

/-- The answer of the sketch is the median over the copies of the estimate from the `t` lowest keys
of the distinct items. -/
theorem run_kmvSketch (ω : Fin c → ι) (s : List α) :
    (kmvSketch h t c ω).run s =
      median fun i => kmvEstimate M t (lowest t (s.toFinset.image (kmvKey h (ω i)))) := by
  rw [Algorithm.run, state_kmvSketch, output_kmvSketch]

/-- Distinct items have distinct keys, so a set of `d` items has `d` keys. -/
theorem card_image_kmvKey (θ : ι) (D : Finset α) : (D.image (kmvKey h θ)).card = D.card :=
  card_image_of_injective _ (kmvKey_injective h θ)

private theorem card_lowest_image_kmvKey (θ : ι) (D : Finset α) :
    (lowest t (D.image (kmvKey h θ))).card = min t D.card := by
  rw [card_lowest, card_image_kmvKey]

/-- **Exactness on few distinct items**: on a stream with fewer than `t` distinct items, every copy
holds all their keys, so the sketch answers `F₀` exactly. -/
theorem run_kmvSketch_of_card_lt [NeZero c] (ω : Fin c → ι) {s : List α}
    (hs : s.toFinset.card < t) : (kmvSketch h t c ω).run s = s.toFinset.card := by
  have hex (i : Fin c) :
      kmvEstimate M t (lowest t (s.toFinset.image (kmvKey h (ω i)))) = s.toFinset.card := by
    have hc := card_lowest_image_kmvKey (h := h) (t := t) (ω i) s.toFinset
    rw [min_eq_right hs.le] at hc
    rw [kmvEstimate_of_card_lt (hc ▸ hs), hc]
  rw [run_kmvSketch]
  simp only [hex, median_const]

/-! ### Accuracy of one copy -/

section Error

variable [Fintype ι] {D : Finset α}

omit [LinearOrder α] [Fintype ι] in
private theorem kmvMaxHash_lt (hM : 0 < M) (S : Finset (Fin M ×ₗ α)) : kmvMaxHash S < M :=
  (Finset.sup_lt_iff (by simpa only [bot_eq_zero'] using hM)).2 fun p _ => (ofLex p).1.isLt

omit [Fintype ι] in
private theorem forall_mem_lowest_kmvKey_iff (θ : ι) (hD : t ≤ D.card) (K : ℕ) :
    (∀ p ∈ lowest t (D.image (kmvKey h θ)), (ofLex p).1.val < K) ↔
      t ≤ (D.filter fun a => (h θ a).val < K).card := by
  rw [forall_mem_lowest_iff ((card_image_kmvKey θ D).symm ▸ hD)
    (fun p : Fin M ×ₗ α => (ofLex p).1.val < K)
    (fun p q hpq hq => (Fin.le_iff_val_le_val.1 (Prod.Lex.monotone_fst_ofLex hpq)).trans_lt hq),
    filter_image, card_image_of_injective _ (kmvKey_injective h θ)]
  rfl

omit [LinearOrder α] in
/-- Chebyshev's inequality for the number of items hashing below `K`. -/
private theorem dens_le_abs_card_filter_val_lt_sub_le (hh : IsPairwiseIndependentHash h)
    (D : Finset α) {K : ℕ} (hK : K < M) {r : ℝ} (hr : 0 < r) :
    (dens {θ | r ≤ |((D.filter fun a => (h θ a).val < K).card : ℝ) - D.card * (K / M)|} : ℝ) ≤
      D.card * (K / M) / r ^ 2 := by
  have := hh.dens_le_abs_card_filter_apply_mem_sub_le D (Iio (⟨K, hK⟩ : Fin M)) hr
  have hfil (θ : ι) : (D.filter fun a => h θ a ∈ Iio (⟨K, hK⟩ : Fin M)) =
      D.filter fun a => (h θ a).val < K := by
    ext a
    simp only [mem_filter, mem_Iio, Fin.lt_def]
  simp only [hfil, Fin.card_Iio, Fintype.card_fin] at this
  exact this

/-- The upper tail: the estimate exceeds `(1 + ε) d` only if at least `t` items hash below
`t M / ((1 + ε) d) - 1`, which is a deviation of at least `t ε / (1 + ε)` from the mean. -/
private theorem dens_lt_kmvEstimate_le (hh : IsPairwiseIndependentHash h) {ε : ℝ} (hε : 0 < ε)
    (ht : 0 < t) (hD : t ≤ D.card) (hDM : D.card ≤ M) :
    (dens {θ | (1 + ε) * D.card <
      (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1)} : ℝ) ≤
      (1 + ε) / (t * ε ^ 2) := by
  set d : ℝ := (D.card : ℝ) with hd
  have htR : (0 : ℝ) < t := Nat.cast_pos.2 ht
  have htd : (t : ℝ) ≤ d := Nat.cast_le.2 hD
  have hdM : d ≤ M := Nat.cast_le.2 hDM
  have hd0 : 0 < d := htR.trans_le htd
  have hM0 : (0 : ℝ) < M := hd0.trans_le hdM
  set x : ℝ := t * M / ((1 + ε) * d) with hx
  have hx0 : 0 < x := by positivity
  have hxM : x < M := by
    rw [hx, div_lt_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left htd hM0.le, mul_pos hM0 (mul_pos hε hd0)]
  set K : ℕ := ⌈x⌉₊ - 1 with hK
  have hceil : 0 < ⌈x⌉₊ := Nat.ceil_pos.2 hx0
  have hKR : (K : ℝ) = ⌈x⌉₊ - 1 := by rw [hK, Nat.cast_sub hceil, Nat.cast_one]
  have hKx : (K : ℝ) < x := by
    rw [hKR]
    linarith [Nat.ceil_lt_add_one hx0.le]
  have hKM : K < M := by exact_mod_cast hKx.trans hxM
  set μ : ℝ := d * (K / M) with hμ
  have hμt : μ * (1 + ε) < t := by
    calc d * (K / M) * (1 + ε) < d * (x / M) * (1 + ε) := by gcongr
      _ = t := by
        rw [hx]
        field_simp
  have hμ0 : 0 ≤ μ := by positivity
  have htμ : 0 < t - μ := by nlinarith
  have hsub : ({θ | (1 + ε) * d <
      (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1)} : Finset ι) ⊆
      ({θ | (t : ℝ) - μ ≤ |((D.filter fun a => (h θ a).val < K).card : ℝ) - μ|} : Finset ι) := by
    intro θ hθ
    simp only [mem_filter, mem_univ, true_and] at hθ ⊢
    set v := kmvMaxHash (lowest t (D.image (kmvKey h θ)))
    have hv : (v : ℝ) + 1 < x := by
      rw [hx, lt_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ (by positivity)] at hθ
      linarith
    have hvK : v < K := by
      have : (v : ℝ) < K := by
        rw [hKR]
        linarith [Nat.le_ceil x]
      exact_mod_cast this
    have hall : ∀ p ∈ lowest t (D.image (kmvKey h θ)), (ofLex p).1.val < K := fun p hp =>
      (le_sup (f := fun p : Fin M ×ₗ α => (ofLex p).1.val) hp).trans_lt hvK
    have hXR : (t : ℝ) ≤ (D.filter fun a => (h θ a).val < K).card := by
      exact_mod_cast (forall_mem_lowest_kmvKey_iff θ hD K).1 hall
    rw [le_abs]
    left
    linarith
  calc _ ≤ (dens ({θ | (t : ℝ) - μ ≤
        |((D.filter fun a => (h θ a).val < K).card : ℝ) - μ|} : Finset ι) : ℝ) := by
        exact_mod_cast dens_le_dens hsub
    _ ≤ μ / (t - μ) ^ 2 := dens_le_abs_card_filter_val_lt_sub_le hh D hKM htμ
    _ ≤ (1 + ε) / (t * ε ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 0 < t - (1 + ε) * μ := by linarith
      have h2 : 0 < (t - μ) + t * ε := by positivity
      nlinarith [mul_pos h1 h2]

/-- The lower tail: for `ε < 1` the estimate is below `(1 - ε) d` only if fewer than `t` items
hash below `⌊t M / ((1 - ε) d)⌋`, which is a deviation of more than `t ε / (1 - ε)` from the
mean. -/
private theorem dens_kmvEstimate_lt_le (hh : IsPairwiseIndependentHash h) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (ht : 0 < t) (hD : t ≤ D.card) (hDM : D.card ≤ M) :
    (dens {θ | (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) <
      (1 - ε) * D.card} : ℝ) ≤ (1 - ε) / (t * ε ^ 2) := by
  set d : ℝ := (D.card : ℝ) with hd
  have htR : (0 : ℝ) < t := Nat.cast_pos.2 ht
  have htd : (t : ℝ) ≤ d := Nat.cast_le.2 hD
  have hdM : d ≤ M := Nat.cast_le.2 hDM
  have hd0 : 0 < d := htR.trans_le htd
  have hM0 : (0 : ℝ) < M := hd0.trans_le hdM
  have hMN : 0 < M := by exact_mod_cast hM0
  have hε' : 0 < 1 - ε := by linarith
  set y : ℝ := t * M / ((1 - ε) * d) with hy
  have hy0 : 0 ≤ y := by positivity
  set K : ℕ := ⌊y⌋₊ with hK
  have hKv (θ : ι) (hθ : (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) <
      (1 - ε) * d) : K ≤ kmvMaxHash (lowest t (D.image (kmvKey h θ))) := by
    set v := kmvMaxHash (lowest t (D.image (kmvKey h θ)))
    have hyv : y < v + 1 := by
      rw [hy, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hθ
      linarith
    have h2 : K < v + 1 := by exact_mod_cast (Nat.floor_le hy0).trans_lt hyv
    omega
  rcases lt_or_ge K M with hKM | hKM
  swap
  · -- The threshold is beyond every hash value: the estimate is never that small.
    have hempty : ({θ | (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) <
        (1 - ε) * d} : Finset ι) = ∅ := by
      refine filter_false_of_mem fun θ _ hθ => ?_
      have := hKv θ hθ
      have := kmvMaxHash_lt hMN (lowest t (D.image (kmvKey h θ)))
      omega
    rw [hempty, dens_empty, NNRat.cast_zero]
    positivity
  set μ : ℝ := d * (K / M) with hμ
  have hμ1 : t / (1 - ε) - 1 < μ := by
    have hK1 : y - 1 < K := by linarith [Nat.lt_floor_add_one y]
    have h1 : d * ((y - 1) / M) < μ := by
      rw [hμ]
      gcongr
    have h2 : d * ((y - 1) / M) = t / (1 - ε) - d / M := by
      rw [hy]
      field_simp
    have h3 : d / M ≤ 1 := div_le_one_of_le₀ hdM hM0.le
    linarith
  set w : ℝ := μ - (t - 1) with hw
  have hwε : t * ε < (1 - ε) * w := by
    have : t < (1 - ε) * (μ + 1) := by
      have := (div_lt_iff₀ hε').1 (by linarith : t / (1 - ε) < μ + 1)
      linarith
    nlinarith
  have hw0 : 0 < w := by
    have : 0 < (1 - ε) * w := by linarith [mul_pos htR hε]
    exact pos_of_mul_pos_right this hε'.le
  have hsub : ({θ | (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) <
        (1 - ε) * d} : Finset ι) ⊆
      ({θ | w ≤ |((D.filter fun a => (h θ a).val < K).card : ℝ) - μ|} : Finset ι) := by
    intro θ hθ
    simp only [mem_filter, mem_univ, true_and] at hθ ⊢
    have hKv' := hKv θ hθ
    have hne : (lowest t (D.image (kmvKey h θ))).Nonempty := by
      rw [← card_pos, card_lowest_image_kmvKey, min_eq_left hD]
      exact ht
    obtain ⟨p, hp, hpv⟩ := exists_mem_eq_sup _ hne fun p : Fin M ×ₗ α => (ofLex p).1.val
    have hnot : ¬ ∀ q ∈ lowest t (D.image (kmvKey h θ)), (ofLex q).1.val < K := fun hall => by
      have := hall p hp
      simp only [kmvMaxHash] at hKv'
      omega
    have hX : (D.filter fun a => (h θ a).val < K).card < t := by
      by_contra hge
      exact hnot ((forall_mem_lowest_kmvKey_iff θ hD K).2 (not_lt.1 hge))
    have hXR : ((D.filter fun a => (h θ a).val < K).card : ℝ) + 1 ≤ t := by exact_mod_cast hX
    rw [le_abs]
    right
    linarith
  calc _ ≤ (dens ({θ | w ≤ |((D.filter fun a => (h θ a).val < K).card : ℝ) - μ|} :
        Finset ι) : ℝ) := by exact_mod_cast dens_le_dens hsub
    _ ≤ μ / w ^ 2 := dens_le_abs_card_filter_val_lt_sub_le hh D hKM hw0
    _ ≤ (1 - ε) / (t * ε ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 0 < (1 - ε) * w - t * ε := by linarith
      have h2 : 0 < w + t * ε := by positivity
      have h3 : μ ≤ w + t := by linarith
      nlinarith [mul_pos h1 h2,
        mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ t * ε ^ 2)]

/-- **One copy estimates `F₀`** [BarYossefJayramKumarSivakumarTrevisan2002, proof of Theorem 1]:
for a pairwise independent family `h θ : α → Fin M`, a set `D` of `d ≤ M` items, `0 < ε ≤ 1` and
`t > 0`, the estimate from the `t` lowest keys of `D` misses `d` by more than `ε d` for at most a
`2 / (t ε²)` fraction of the seeds. The source proves `1 / 6 + 1 / 6` for `t = ⌈96 / ε²⌉`, plus a
`1 / m` term for hash collisions, which the tie-breaking keys avoid. -/
theorem dens_abs_kmvEstimate_sub_gt_le (hh : IsPairwiseIndependentHash h) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ht : 0 < t) (hDM : D.card ≤ M) :
    (dens {θ | ε * D.card < |kmvEstimate M t (lowest t (D.image (kmvKey h θ))) - D.card|} : ℝ) ≤
      2 / (t * ε ^ 2) := by
  classical
  have htR : (0 : ℝ) < t := Nat.cast_pos.2 ht
  rcases lt_or_ge D.card t with hDt | hD
  · -- Fewer than `t` items: the estimate is exact.
    have hex (θ : ι) : kmvEstimate M t (lowest t (D.image (kmvKey h θ))) = D.card := by
      have hc := card_lowest_image_kmvKey (h := h) (t := t) θ D
      rw [min_eq_right hDt.le] at hc
      rw [kmvEstimate_of_card_lt (hc ▸ hDt), hc]
    simp only [hex, sub_self, abs_zero]
    rw [filter_false_of_mem (fun θ _ => not_lt.2 (by positivity)), dens_empty, NNRat.cast_zero]
    positivity
  have hest (θ : ι) : kmvEstimate M t (lowest t (D.image (kmvKey h θ))) =
      t * M / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) := by
    have hc := card_lowest_image_kmvKey (h := h) (t := t) θ D
    rw [min_eq_left hD] at hc
    exact kmvEstimate_of_le_card hc.ge
  simp only [hest]
  have hsub : ({θ | ε * D.card <
      |(t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) - D.card|} : Finset ι) ⊆
      ({θ | (1 + ε) * D.card <
        (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1)} : Finset ι) ∪
      ({θ | (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) <
        (1 - ε) * D.card} : Finset ι) := by
    intro θ hθ
    simp only [mem_union, mem_filter, mem_univ, true_and] at hθ ⊢
    rcases lt_abs.1 hθ with h' | h'
    · left
      linarith
    · right
      linarith
  have hunder : (dens {θ | (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) <
      (1 - ε) * D.card} : ℝ) ≤ (1 - ε) / (t * ε ^ 2) := by
    rcases hε1.lt_or_eq with hlt | rfl
    · exact dens_kmvEstimate_lt_le hh hε hlt ht hD hDM
    · -- For `ε = 1` the estimate is never negative.
      rw [filter_false_of_mem (fun θ _ => by simp only [sub_self, zero_mul, not_lt]; positivity),
        dens_empty, NNRat.cast_zero, sub_self, zero_div]
  calc _ ≤ (dens (({θ | (1 + ε) * D.card <
        (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1)} : Finset ι) ∪
        ({θ | (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) <
          (1 - ε) * D.card} : Finset ι)) : ℝ) := by exact_mod_cast dens_le_dens hsub
    _ ≤ (dens {θ | (1 + ε) * D.card <
        (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1)} : ℝ) +
        dens {θ | (t * M : ℝ) / (kmvMaxHash (lowest t (D.image (kmvKey h θ))) + 1) <
          (1 - ε) * D.card} := by exact_mod_cast dens_union_le _ _
    _ ≤ (1 + ε) / (t * ε ^ 2) + (1 - ε) / (t * ε ^ 2) :=
        add_le_add (dens_lt_kmvEstimate_le hh hε ht hD hDM) hunder
    _ = 2 / (t * ε ^ 2) := by ring

end Error

/-- The error of the randomized sketch is the fraction of bad seeds. -/
theorem errorProb_kmv [Fintype ι] [Nonempty ι] (R : List α → ℝ → Prop) (s : List α)
    [DecidablePred fun ω : Fin c → ι => ¬R s ((kmvSketch h t c ω).run s)] :
    (kmv h t c).errorProb R s = dens {ω : Fin c → ι | ¬R s ((kmvSketch h t c ω).run s)} :=
  Randomized.errorProb_map_uniformOfFintype _ R s

/-! ### Amplification -/

/-- **The median of `2 r` copies misses `F₀` by more than `ε F₀` for at most an `(8 / 9) ^ r`
fraction of seeds** once `6 ≤ t ε²` [BarYossefJayramKumarSivakumarTrevisan2002, Theorem 1]: one
copy fails for at most a third of the seeds, and the median trick
(`Cslib.Probability.dens_abs_median_sub_gt_le`) amplifies this. -/
theorem dens_kmvSketch_error_le [Fintype ι] [Nonempty ι] (hh : IsPairwiseIndependentHash h)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 6 ≤ t * ε ^ 2) {s : List α}
    (hsM : s.toFinset.card ≤ M) (r : ℕ) :
    (dens {ω : Fin (2 * r) → ι |
      ε * s.toFinset.card < |(kmvSketch h t (2 * r) ω).run s - s.toFinset.card|} : ℝ) ≤
      (8 / 9) ^ r := by
  classical
  have htpos : 0 < t := Nat.pos_of_ne_zero fun h0 => by norm_num [h0] at ht
  have h3 : 2 / ((t : ℝ) * ε ^ 2) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  simp only [run_kmvSketch]
  exact dens_abs_median_sub_gt_le (fun θ => kmvEstimate M t (lowest t (s.toFinset.image
    (kmvKey h θ)))) ((dens_abs_kmvEstimate_sub_gt_le hh hε hε1 htpos hsM).trans h3) r

/-- **The randomized sketch with `2 r` copies solves `F₀` estimation** with relative error `ε` and
failure probability `δ ≥ (8 / 9) ^ r` on streams of length at most `M`
[BarYossefJayramKumarSivakumarTrevisan2002, Theorem 1]. -/
theorem solves_kmv [Fintype ι] [Nonempty ι] (hh : IsPairwiseIndependentHash h) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 6 ≤ t * ε ^ 2) {r : ℕ} (hδ : (8 / 9 : ℝ) ^ r ≤ δ) {m : ℕ}
    (hm : m ≤ M) :
    (kmv h t (2 * r)).Solves δ (fun s Y => |Y - freqMoment 0 s| ≤ ε * freqMoment 0 s) m := by
  classical
  intro s hs
  rw [errorProb_kmv]
  simp only [freqMoment_zero, not_le]
  exact (dens_kmvSketch_error_le hh hε hε1 ht
    ((List.toFinset_card_le s).trans (hs.trans hm)) r).trans hδ

/-! ### Memory -/

/-- The `t` lowest keys of a set of items are the keys of at most `t` of them. -/
private theorem exists_card_le_image_eq_lowest (θ : ι) (D : Finset α) :
    ∃ E : Finset α, E.card ≤ t ∧ E.image (kmvKey h θ) = lowest t (D.image (kmvKey h θ)) := by
  classical
  refine ⟨D.filter fun a => kmvKey h θ a ∈ lowest t (D.image (kmvKey h θ)), ?_, ?_⟩
  · have himg : (D.filter fun a => kmvKey h θ a ∈ lowest t (D.image (kmvKey h θ))).image
        (kmvKey h θ) = lowest t (D.image (kmvKey h θ)) := by
      ext p
      simp only [mem_image, mem_filter]
      constructor
      · rintro ⟨a, ⟨-, ha⟩, rfl⟩
        exact ha
      · intro hp
        obtain ⟨a, ha, rfl⟩ := mem_image.1 (lowest_subset _ _ hp)
        exact ⟨a, ⟨ha, hp⟩, rfl⟩
    rw [← card_image_kmvKey (h := h) θ, himg, card_lowest]
    exact min_le_left _ _
  · ext p
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨a, ⟨-, ha⟩, rfl⟩
      exact ha
    · intro hp
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (lowest_subset _ _ hp)
      exact ⟨a, ⟨ha, hp⟩, rfl⟩

/-- The states reachable from the seeds in `Ω` have an injective `b`-bit encoding as soon as
`#Ω (n + 1) ^ (c t) ≤ 2 ^ b`, on streams of any length. -/
private theorem exists_injOn_biUnion_reachable_kmvSketch [Fintype α] (Ω : Finset (Fin c → ι))
    {m b : ℕ} (hb : Ω.card * (Fintype.card α + 1) ^ (c * t) ≤ 2 ^ b) :
    ∃ enc : KMVState ι α M c → BitString b,
      Set.InjOn enc (⋃ ω ∈ Ω, (kmvSketch h t c ω).reachable m) := by
  classical
  let small : Finset (Finset α) := {E | E.card ≤ t}
  let T : Finset (KMVState ι α M c) := (Ω ×ˢ Fintype.piFinset fun _ : Fin c => small).image
    fun p => (p.1, fun i => (p.2 i).image (kmvKey h (p.1 i)))
  refine Algorithm.exists_injOn_of_subset_finset (T := T) ?_ ?_
  · rintro _ ⟨_, ⟨ω, rfl⟩, _, ⟨hω, rfl⟩, s, -, rfl⟩
    choose E hE hEeq using fun i : Fin c => exists_card_le_image_eq_lowest (h := h) (t := t)
      (ω i) s.toFinset
    rw [mem_coe, mem_image]
    refine ⟨(ω, E), mem_product.2 ⟨hω, Fintype.mem_piFinset.2 fun i => ?_⟩, ?_⟩
    · simp only [small, mem_filter, mem_univ, true_and]
      exact hE i
    · rw [state_kmvSketch]
      simp only [hEeq]
  · have hsmall : small.card ≤ (Fintype.card α + 1) ^ t := by
      simp only [small]
      rw [card_filter_card_le_eq_sum_choose]
      exact Cslib.sum_range_choose_le_add_one_pow _ t
    calc T.card ≤ (Ω ×ˢ Fintype.piFinset fun _ : Fin c => small).card := card_image_le
      _ = Ω.card * small.card ^ c := by
        rw [card_product, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
      _ ≤ Ω.card * ((Fintype.card α + 1) ^ t) ^ c := by gcongr
      _ = Ω.card * (Fintype.card α + 1) ^ (c * t) := by rw [← pow_mul, mul_comm t]
      _ ≤ 2 ^ b := hb

/-- **The memory of the randomized sketch** [BarYossefJayramKumarSivakumarTrevisan2002,
Theorem 1]: over a universe of `n` items, every sketch it draws uses at most `b` bits of memory on
streams of any length `m` as soon as `(n + 1) ^ (c t) ≤ 2 ^ b`. Under the public-coin convention of
`Cslib.Streaming.Randomized` the seeds are not charged; each copy is charged for the at most `t`
items behind its keys. For the count with the seeds stored see
`Cslib.Streaming.exists_injOn_iUnion_reachable_kmvSketch`. -/
theorem spaceLE_kmv [Fintype ι] [Nonempty ι] [Fintype α] {m b : ℕ}
    (hb : (Fintype.card α + 1) ^ (c * t) ≤ 2 ^ b) : (kmv h t c).SpaceLE m b := by
  intro A hA
  rw [kmv, PMF.support_map] at hA
  obtain ⟨ω, -, rfl⟩ := hA
  obtain ⟨enc, henc⟩ := exists_injOn_biUnion_reachable_kmvSketch (h := h) (t := t) {ω} (m := m)
    (b := b) (by rwa [card_singleton, one_mul])
  exact ⟨enc, henc.mono fun q hq => Set.mem_biUnion (mem_singleton_self ω) hq⟩

/-- **The memory of the sketch with its seeds stored** [BarYossefJayramKumarSivakumarTrevisan2002,
Theorem 1]: over a universe of `n` items, the states reachable from all seeds together have a
single injective encoding by `b` bits as soon as `(|ι| (n + 1) ^ t) ^ c ≤ 2 ^ b`. Since only the
initial memory depends on the seeds (`Cslib.Streaming.update_kmvSketch`,
`Cslib.Streaming.output_kmvSketch`), this is the memory of one algorithm whose initial memory is
random, with the seeds charged. -/
theorem exists_injOn_iUnion_reachable_kmvSketch [Fintype ι] [Fintype α] {m b : ℕ}
    (hb : (Fintype.card ι * (Fintype.card α + 1) ^ t) ^ c ≤ 2 ^ b) :
    ∃ enc : KMVState ι α M c → BitString b,
      Set.InjOn enc (⋃ ω, (kmvSketch h t c ω).reachable m) := by
  classical
  obtain ⟨enc, henc⟩ := exists_injOn_biUnion_reachable_kmvSketch (h := h) (t := t)
    (univ : Finset (Fin c → ι)) (m := m) (b := b) (by
      rwa [card_univ, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, mul_comm c t,
        pow_mul, ← mul_pow])
  refine ⟨enc, henc.mono fun q hq => ?_⟩
  obtain ⟨_, ⟨ω, rfl⟩, hq⟩ := hq
  exact Set.mem_biUnion (mem_univ ω) hq

end Cslib.Streaming
