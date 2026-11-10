/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Streaming.Basic
public import CslibFrontier.Computability.Streaming.GraphStream
import CslibFrontier.Computability.Communication.Disjointness
import CslibFrontier.Computability.Communication.Randomized
import CslibFrontier.Computability.Streaming.Communication
import CslibFrontier.Foundations.Data.Code.HammingBound
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Probability.PMF.Event
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Linear memory for deterministic approximation and randomized exact computation of `F_k`

Alon, Matias and Szegedy showed that for every `k ≠ 1` both randomness and approximation are needed
to compute the frequency moment `F_k` (`Cslib.Streaming.freqMoment`) in sublinear memory
[AlonMatiasSzegedy1999, §3.3–3.4]. Both bounds compare `F_k` on two concatenated graph streams
(`Cslib.Streaming.graphStream`).

**Deterministic approximation** [AlonMatiasSzegedy1999, Proposition 3.7]. There is a code of length
`L` over `16` letters with `2 ^ L` words, any two differing in at least half of the positions
(`Cslib.Code.exists_two_pow_le_card_and_le_two_mul_hammingDist`, by the Gilbert–Varshamov bound).
The graphs of its words are sets of size `L` in a universe of size `16 L`, any two meeting in at
most `L / 2` items; this is the family of the source, which uses sets of size `n / 4` meeting in at
most `n / 8` items in a universe of size `n`. With fewer than `L` bits of memory, two different
words `x ≠ y` lead to the same memory state, so the algorithm answers alike on the graph streams of
`x x` and `y x`. But `F₀` is `L` on the first and at least `3 L / 2` on the second, and for `k ≥ 2`
`F_k` is `2 ^ k L` on the first and at most `(2 ^ k + 2) L / 2` on the second, so no answer is
within `η F_k` of both when `7 η < 1`, which covers the source's `η = 0.1`
(`Cslib.Streaming.Algorithm.le_of_approx_freqMoment`). Embedding the items into `Fin N` gives
`N / 16 ≤ b` for streams of at most `2 ⌊N / 16⌋ ≤ N / 8` items
(`Cslib.Streaming.Algorithm.div_le_of_approx_freqMoment`); the source states the bound for streams
of `n / 2` items.

**Randomized exact computation** [AlonMatiasSzegedy1999, Proposition 3.8]. Alice streams `(i, 1)`
for her ones and `(i, 0)` for her zeros, Bob `(i, 1)` for his ones and `(i, 2)` for his zeros. The
graphs agree exactly at the common ones, so for `k ≠ 1` the moment `F_k` of the concatenated stream
is `2 n` exactly when the supports are disjoint
(`Cslib.Streaming.disjointness_eq_decide_freqMoment_eq`). An algorithm computing `F_k` with error
`ε` thus gives a one-way protocol for disjointness through
`Cslib.Streaming.Randomized.ecomplexityFun_le_of_spaceLE`, and the `Ω(n)` lower bound for
disjointness [KalyanasundaramSchnitger1992][Razborov1992] bounds its memory. The source applies the
reduction of its Proposition 3.1 instead, which streams the positions of the ones of both players.
Then `F_k` decides disjointness only by comparing it with the number of ones `|x| + |y|`, which
depends on both inputs, whereas the answer map of
`Cslib.Streaming.Randomized.ecomplexityFun_le_of_spaceLE` is fixed (Alice could send `|x|` in
`O(log n)` more bits). The graph streams make the threshold `2 n` independent of the inputs, at the
price of the universe `Fin n × Fin 3` of size `3 n`.
* For error `ε ≤ 1 / 2`: `n ≤ 2 ^ 10 r (b + 1) + 2 ^ 12` whenever `(4 ε (1 - ε)) ^ r ≤ 1 / 64`
  (`Cslib.Streaming.le_of_solves_freqMoment`); for error `1 / 3`, `n ≤ 36864 (b + 1) + 2 ^ 12`
  (`Cslib.Streaming.le_of_solves_freqMoment_one_third`).
* Deterministically: `n ≤ b` (`Cslib.Streaming.Algorithm.le_of_run_eq_freqMoment`), from the exact
  deterministic complexity `n + 1` of disjointness.
* Over the universe `Fin N` and streams of at most `2 ⌊N / 3⌋` items:
  `Cslib.Streaming.div_le_of_solves_freqMoment`,
  `Cslib.Streaming.Algorithm.div_le_of_run_eq_freqMoment`.

In all bounds `b` bounds the memory on the first half of the stream only, which is all the proofs
use.

## Main results

* `Cslib.Streaming.Algorithm.le_of_approx_freqMoment`,
  `Cslib.Streaming.Algorithm.div_le_of_approx_freqMoment`: approximating `F_k` deterministically
  needs `Ω(n)` bits [AlonMatiasSzegedy1999, Proposition 3.7].
* `Cslib.Streaming.le_of_solves_freqMoment`, `Cslib.Streaming.le_of_solves_freqMoment_one_third`,
  `Cslib.Streaming.div_le_of_solves_freqMoment`: computing `F_k` exactly with bounded error needs
  `Ω(n)` bits [AlonMatiasSzegedy1999, Proposition 3.8].
* `Cslib.Streaming.Algorithm.le_of_run_eq_freqMoment`,
  `Cslib.Streaming.Algorithm.div_le_of_run_eq_freqMoment`: computing `F_k` exactly and
  deterministically needs `n` bits.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Propositions 3.7 and 3.8][AlonMatiasSzegedy1999]
* [B. Kalyanasundaram and G. Schnitger, *The probabilistic communication complexity of set
  intersection*][KalyanasundaramSchnitger1992]
* [A. A. Razborov, *On the distributional complexity of disjointness*][Razborov1992]
-/

public section

namespace Cslib.Streaming

open Finset Communication

/-! ### Deterministic approximation -/

/-- **Approximating `F_k` deterministically needs `Ω(n)` bits of memory** for `k ≠ 1`
[AlonMatiasSzegedy1999, Proposition 3.7]: a deterministic streaming algorithm whose answer on every
stream of at most `2 L` items of `Fin L × Fin 16` is within `η F_k` of `F_k`, for some `η < 1 / 7`,
and which uses at most `b` bits of memory on streams of at most `L` items, has `L ≤ b`. -/
theorem Algorithm.le_of_approx_freqMoment {σ : Type*} {L b k : ℕ} {η : ℝ} (hk : k ≠ 1)
    (hη : 7 * η < 1) (A : Algorithm σ (Fin L × Fin 16) ℝ)
    (hA : ∀ s : List (Fin L × Fin 16), s.length ≤ 2 * L →
      |A.run s - freqMoment k s| ≤ η * freqMoment k s)
    (hspace : A.SpaceLE L b) : L ≤ b := by
  by_contra hb
  push Not at hb
  obtain ⟨enc, henc⟩ := hspace
  obtain ⟨C, hC, hCd⟩ := Code.exists_two_pow_le_card_and_le_two_mul_hammingDist L
  -- two codewords whose graph streams lead to the same memory state
  have hcard : (univ : Finset (BitString b)).card < #C := by
    rw [card_univ, BitString.card]
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hb) hC
  obtain ⟨x, hx, y, hy, hxy, hcoll⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun z => enc (A.state (graphStream z))) fun _ _ => mem_coe.2 (mem_univ _)
  have hreach (z : Fin L → Fin 16) : A.state (graphStream z) ∈ A.reachable L :=
    A.state_mem_reachable (by rw [length_graphStream])
  have hstate : A.state (graphStream x) = A.state (graphStream y) :=
    henc (hreach x) (hreach y) hcoll
  have hrun : A.run (graphStream x ++ graphStream x) = A.run (graphStream y ++ graphStream x) := by
    simp only [run, state_append, hstate]
  have hlen (z : Fin L → Fin 16) : (graphStream z ++ graphStream x).length ≤ 2 * L := by
    rw [List.length_append, length_graphStream, length_graphStream]
    omega
  have h1 := hA _ (hlen x)
  have h2 := hA _ (hlen y)
  rw [hrun] at h1
  set Y := A.run (graphStream y ++ graphStream x)
  -- the two moments
  have hd := hCd y hy x hx (Ne.symm hxy)
  have hsum := card_filter_eq_add_hammingDist y x
  rw [Fintype.card_fin] at hsum
  have hF1 : (freqMoment k (graphStream x ++ graphStream x) : ℝ) = 2 ^ k * L := by
    rw [freqMoment_graphStream_append_eq]
    have hc := card_filter_eq_add_hammingDist x x
    rw [Fintype.card_fin, hammingDist_self] at hc
    rw [hammingDist_self]
    push_cast
    rw [show ((#{i | x i = x i} : ℕ) : ℝ) = L by exact_mod_cast hc]
    ring
  have hF2 : (freqMoment k (graphStream y ++ graphStream x) : ℝ) =
      2 ^ k * (#{i | y i = x i} : ℕ) + 2 * (hammingDist y x : ℕ) := by
    rw [freqMoment_graphStream_append_eq]
    push_cast
    ring
  rw [hF1] at h1
  rw [hF2] at h2
  have hsum' : ((#{i | y i = x i} : ℕ) : ℝ) + (hammingDist y x : ℕ) = L := by exact_mod_cast hsum
  have hd' : (L : ℝ) ≤ 2 * (hammingDist y x : ℕ) := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_le_of_lt (Nat.zero_le b) hb
    exact_mod_cast this
  generalize ((#{i | y i = x i} : ℕ) : ℝ) = c at hsum' h2
  generalize ((hammingDist y x : ℕ) : ℝ) = δ at hsum' hd' h2
  rw [abs_le] at h1 h2
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- `F₀`: `L` against `L + δ ≥ 3 L / 2`
    norm_num at h1l h1r h2l h2r
    nlinarith
  · -- `F_k` for `k ≥ 2`: `P L` against at most `(P + 2) L / 2`, where `P = 2 ^ k ≥ 4`
    have hP : (4 : ℝ) ≤ 2 ^ k := by
      have : 2 ≤ k := by omega
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) this
    set P : ℝ := 2 ^ k
    have hPL : 0 < P * L := by positivity
    have hη0 : 0 ≤ η := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hPL
      linarith
    have hc : c = L - δ := by linarith
    subst hc
    have hF2le : 2 * (P * (L - δ) + 2 * δ) ≤ (P + 2) * L := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ P - 2) (by linarith : (0 : ℝ) ≤ 2 * δ - L)]
    have hq : 0 < P - 2 - η * (3 * P + 2) := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - 7 * η) (by linarith : (0 : ℝ) < 3 * P + 2)]
    nlinarith [mul_pos hLpos hq, mul_nonneg hη0 (by linarith : (0 : ℝ) ≤
      (P + 2) * L - 2 * (P * (L - δ) + 2 * δ))]

/-- The embedding of `Fin (N / k) × Fin k` into `Fin N` by consecutive blocks of `k` items,
which transfers the lower bounds over product universes to the universe `Fin N`. -/
private def blockEmbedding (N k : ℕ) : Fin (N / k) × Fin k ↪ Fin N :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (Nat.div_mul_le_self N k))

/-- **Approximating `F_k` deterministically needs `Ω(n)` bits of memory** for `k ≠ 1`, over the
universe `Fin N` [AlonMatiasSzegedy1999, Proposition 3.7]: a deterministic streaming algorithm whose
answer on every stream of at most `2 ⌊N / 16⌋` items of `Fin N` is within `η F_k` of `F_k`, for some
`η < 1 / 7`, and which uses at most `b` bits of memory on streams of at most `N / 16` items, has
`N / 16 ≤ b`. -/
theorem Algorithm.div_le_of_approx_freqMoment {σ : Type*} {N b k : ℕ} {η : ℝ} (hk : k ≠ 1)
    (hη : 7 * η < 1) (A : Algorithm σ (Fin N) ℝ)
    (hA : ∀ s : List (Fin N), s.length ≤ 2 * (N / 16) →
      |A.run s - freqMoment k s| ≤ η * freqMoment k s)
    (hspace : A.SpaceLE (N / 16) b) : N / 16 ≤ b := by
  let e := blockEmbedding N 16
  refine (A.reduce [] e id).le_of_approx_freqMoment hk hη (fun s hs => ?_)
    (Algorithm.SpaceLE.reduce [] (by rwa [List.length_nil, Nat.zero_add]) e id)
  rw [Algorithm.run_reduce, List.nil_append, id, ← freqMoment_map e.injective]
  exact hA _ (by rwa [List.length_map])

/-! ### Exact computation -/

/-- Alice's graph `(i, 1)` for `x i` and `(i, 0)` otherwise, and Bob's `(i, 1)` for `y i` and
`(i, 2)` otherwise, agree exactly at the common ones: for `k ≠ 1`, `F_k` of the concatenated
stream is `2 n` exactly when `x` and `y` have disjoint supports. -/
theorem disjointness_eq_decide_freqMoment_eq {n k : ℕ} (hk : k ≠ 1) (x y : BitString n) :
    disjointness x y = decide (freqMoment k
      (graphStream (fun i => if x i then (1 : Fin 3) else 0) ++
        graphStream (fun i => if y i then (1 : Fin 3) else 2)) = 2 * n) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, freqMoment_graphStream_append_eq_two_mul_iff hk]
  simp only [disjointness, decide_eq_true_eq]
  refine forall_congr' fun i => ?_
  cases x i <;> cases y i <;> decide

/-- **Computing `F_k` exactly needs `Ω(n)` bits of memory, even with randomness**, for `k ≠ 1`
[AlonMatiasSzegedy1999, Proposition 3.8]: a randomized streaming algorithm that computes `F_k` with
error at most `ε ≤ 1 / 2` on streams of at most `2 n` items of `Fin n × Fin 3`, and whose
algorithms use at most `b` bits of memory on streams of at most `n` items, has
`n ≤ 2 ^ 10 r (b + 1) + 2 ^ 12` for every `r` with `(4 ε (1 - ε)) ^ r ≤ 1 / 64`. For `ε < 1 / 2`
such an `r` exists. -/
theorem le_of_solves_freqMoment {σ : Type*} {n b r k : ℕ} {ε : ℝ} (hk : k ≠ 1)
    (hε : ε ≤ 1 / 2) (hr : (4 * ε * (1 - ε)) ^ r ≤ 1 / 64) (μ : Randomized σ (Fin n × Fin 3) ℕ)
    (hμ : μ.Solves ε (fun s c => c = freqMoment k s) (2 * n)) (hspace : μ.SpaceLE n b) :
    n ≤ 2 ^ 10 * r * (b + 1) + 2 ^ 12 := by
  let u : BitString n → List (Fin n × Fin 3) := fun x =>
    graphStream fun i => if x i then (1 : Fin 3) else 0
  let v : BitString n → List (Fin n × Fin 3) := fun y =>
    graphStream fun i => if y i then (1 : Fin 3) else 2
  have hcc := μ.ecomplexityFun_le_of_spaceLE hspace u v
    (fun x => (length_graphStream _).le) (fun c => decide (c = 2 * n))
    disjointness (ε := ε) fun x y => by
      have hlen : (u x ++ v y).length ≤ 2 * n := by
        simp only [u, v, List.length_append, length_graphStream]
        omega
      refine le_trans ?_ (hμ _ hlen)
      unfold Randomized.errorProb
      refine ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
        (μ.toOuterMeasure.mono fun A hA => ?_)
      simp only [Set.mem_ofPred_eq] at hA ⊢
      intro h
      exact hA (by rw [h, disjointness_eq_decide_freqMoment_eq hk])
  exact PublicCoin.le_of_ecomplexityFun_disjointness_le hε hr (by exact_mod_cast hcc)

/-- **Computing `F_k` exactly needs `Ω(n)` bits of memory, even with randomness**
[AlonMatiasSzegedy1999, Proposition 3.8], for error `1 / 3`: `n ≤ 36864 (b + 1) + 2 ^ 12`. -/
theorem le_of_solves_freqMoment_one_third {σ : Type*} {n b k : ℕ} (hk : k ≠ 1)
    (μ : Randomized σ (Fin n × Fin 3) ℕ)
    (hμ : μ.Solves (1 / 3) (fun s c => c = freqMoment k s) (2 * n)) (hspace : μ.SpaceLE n b) :
    n ≤ 36864 * (b + 1) + 2 ^ 12 :=
  le_of_solves_freqMoment (r := 36) hk (by norm_num) (by norm_num) μ hμ hspace

/-- **Computing `F_k` exactly needs `Ω(n)` bits of memory, even with randomness**, for `k ≠ 1`,
over the universe `Fin N` [AlonMatiasSzegedy1999, Proposition 3.8]: with error at most `ε ≤ 1 / 2`
on streams of at most `2 ⌊N / 3⌋` items and at most `b` bits of memory on streams of at most
`N / 3` items, `N / 3 ≤ 2 ^ 10 r (b + 1) + 2 ^ 12` for every `r` with
`(4 ε (1 - ε)) ^ r ≤ 1 / 64`. -/
theorem div_le_of_solves_freqMoment {σ : Type*} {N b r k : ℕ} {ε : ℝ} (hk : k ≠ 1)
    (hε : ε ≤ 1 / 2) (hr : (4 * ε * (1 - ε)) ^ r ≤ 1 / 64) (μ : Randomized σ (Fin N) ℕ)
    (hμ : μ.Solves ε (fun s c => c = freqMoment k s) (2 * (N / 3)))
    (hspace : μ.SpaceLE (N / 3) b) : N / 3 ≤ 2 ^ 10 * r * (b + 1) + 2 ^ 12 := by
  let e := blockEmbedding N 3
  refine le_of_solves_freqMoment hk hε hr (μ.map fun A => A.reduce [] e id) (fun s hs => ?_)
    (Randomized.SpaceLE.map_reduce [] (by rwa [List.length_nil, Nat.zero_add]) e id)
  refine (μ.errorProb_map_reduce_le [] e id s fun c hc => ?_).trans
    (hμ _ (by rwa [List.nil_append, List.length_map]))
  rw [hc, List.nil_append, freqMoment_map e.injective]
  rfl

/-- **Computing `F_k` exactly and deterministically needs `n` bits of memory**, for `k ≠ 1`: a
deterministic streaming algorithm computing `F_k` on every stream of at most `2 n` items of
`Fin n × Fin 3`, with at most `b` bits of memory on streams of at most `n` items, has `n ≤ b`. -/
theorem Algorithm.le_of_run_eq_freqMoment {σ : Type*} {n b k : ℕ} (hk : k ≠ 1)
    (A : Algorithm σ (Fin n × Fin 3) ℕ)
    (hA : ∀ s : List (Fin n × Fin 3), s.length ≤ 2 * n → A.run s = freqMoment k s)
    (hspace : A.SpaceLE n b) : n ≤ b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have h := A.ecomplexityFun_le_of_spaceLE hspace
    (fun x : BitString n => graphStream fun i => if x i then (1 : Fin 3) else 0)
    (fun y : BitString n => graphStream fun i => if y i then (1 : Fin 3) else 2)
    (fun x => (length_graphStream _).le) (fun c => decide (c = 2 * n))
    disjointness fun x y => by
      rw [hA _ (by rw [List.length_append, length_graphStream, length_graphStream]; omega),
        disjointness_eq_decide_freqMoment_eq hk]
  have h2 := ecomplexity_disjointness hn
  unfold Protocol.ecomplexityFun at h
  rw [h2] at h
  have h3 : n + 1 ≤ b + 1 := by exact_mod_cast h
  omega

/-- **Computing `F_k` exactly and deterministically needs `Ω(n)` bits of memory**, for `k ≠ 1`, over
the universe `Fin N`: with at most `b` bits of memory on streams of at most `N / 3` items, a
deterministic algorithm computing `F_k` on streams of at most `2 ⌊N / 3⌋` items has `N / 3 ≤ b`. -/
theorem Algorithm.div_le_of_run_eq_freqMoment {σ : Type*} {N b k : ℕ} (hk : k ≠ 1)
    (A : Algorithm σ (Fin N) ℕ)
    (hA : ∀ s : List (Fin N), s.length ≤ 2 * (N / 3) → A.run s = freqMoment k s)
    (hspace : A.SpaceLE (N / 3) b) : N / 3 ≤ b := by
  let e := blockEmbedding N 3
  refine (A.reduce [] e id).le_of_run_eq_freqMoment hk (fun s hs => ?_)
    (Algorithm.SpaceLE.reduce [] (by rwa [List.length_nil, Nat.zero_add]) e id)
  rw [Algorithm.run_reduce, List.nil_append, id, ← freqMoment_map e.injective]
  exact hA _ (by rwa [List.length_map])

end Cslib.Streaming
