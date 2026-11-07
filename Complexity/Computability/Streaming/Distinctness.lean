/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Functions
public import Complexity.Computability.Streaming.Basic
import Complexity.Computability.Communication.Amplification
import Complexity.Computability.Communication.Disjointness
import Complexity.Computability.Streaming.Communication
import Complexity.Probability.PMF.Event
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Streaming lower bounds for distinctness and the largest frequency

Splitting the stream into the positions of Alice's ones followed by the positions of Bob's ones
(`Cslib.Streaming.positions`), the items are distinct exactly when the two bit strings have
disjoint supports (`Cslib.Streaming.nodup_positions_append`). A streaming algorithm deciding
whether the items of a stream are distinct thus gives a one-way protocol for disjointness
(`Cslib.Streaming.Randomized.ecomplexityFun_le_of_spaceLE`), and the `Ω(n)` lower bound for
disjointness [KalyanasundaramSchnitger1992][Razborov1992] becomes an `Ω(n)` lower bound on the
memory.

* A randomized streaming algorithm deciding whether at most `2 n` items of `Fin n` are distinct with
  error `ε ≤ 1 / 2` needs `Ω(n)` bits of memory, with a constant depending only on `ε`
  (`Cslib.Streaming.le_of_solves_nodup`); for error `1 / 3`, `n ≤ 36864 (b + 1) + 2 ^ 12`
  (`Cslib.Streaming.le_of_solves_nodup_one_third`).
* The largest frequency `F∞` of a stream (`Cslib.Streaming.maxFreq`) is `1` on nonempty streams of
  distinct items and at least `2` otherwise, so an estimate within less than a third of `F∞`
  decides distinctness, and approximating `F∞` needs `Ω(n)` bits too
  (`Cslib.Streaming.le_of_solves_maxFreq`, `Cslib.Streaming.le_of_solves_maxFreq_one_third`). This
  is [AlonMatiasSzegedy1999, Proposition 3.1]. The reduction prefixes a fixed item to make the
  stream nonempty, so the bound is stated for `Fin (n + 1)` and streams of `2 n + 1` items.
* A deterministic streaming algorithm deciding distinctness exactly, or computing `F∞` exactly,
  needs `n` bits (`Cslib.Streaming.Algorithm.le_of_run_eq_decide_nodup`,
  `Cslib.Streaming.Algorithm.le_of_run_eq_maxFreq`), from the exact deterministic complexity
  `n + 1` of disjointness. Storing the set of items seen and a flag shows that `n + 1` bits
  suffice.

## Main definitions

* `Cslib.Streaming.positions`: the positions of the ones of a bit string, as a stream.
* `Cslib.Streaming.maxFreq`: the largest frequency `F∞` of a stream.

## Main results

* `Cslib.Streaming.le_of_solves_nodup`, `Cslib.Streaming.le_of_solves_nodup_one_third`:
  randomized distinctness needs `Ω(n)` bits.
* `Cslib.Streaming.le_of_solves_maxFreq`, `Cslib.Streaming.le_of_solves_maxFreq_one_third`:
  approximating `F∞` needs `Ω(n)` bits [AlonMatiasSzegedy1999, Proposition 3.1].
* `Cslib.Streaming.Algorithm.le_of_run_eq_decide_nodup`,
  `Cslib.Streaming.Algorithm.le_of_run_eq_maxFreq`: the deterministic exact bounds `n ≤ b`.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Proposition 3.1][AlonMatiasSzegedy1999]
* [B. Kalyanasundaram and G. Schnitger, *The probabilistic communication complexity of set
  intersection*][KalyanasundaramSchnitger1992]
* [A. A. Razborov, *On the distributional complexity of disjointness*][Razborov1992]
-/

public section

namespace Cslib.Streaming

open Communication

/-! ### Detecting a repeated item -/

/-- The positions where a bit string is `true`, in increasing order. -/
def positions {n : ℕ} (x : BitString n) : List (Fin n) :=
  (List.finRange n).filter fun i => x i

theorem length_positions_le {n : ℕ} (x : BitString n) : (positions x).length ≤ n :=
  (List.length_filter_le _ _).trans (List.length_finRange).le

/-- The positions of the ones of `x` followed by those of `y` are distinct exactly when `x` and `y`
have disjoint supports. -/
theorem nodup_positions_append {n : ℕ} (x y : BitString n) :
    (positions x ++ positions y).Nodup ↔ disjointness x y = true := by
  have hx : (positions x).Nodup := (List.nodup_finRange n).filter _
  have hy : (positions y).Nodup := (List.nodup_finRange n).filter _
  rw [List.nodup_append]
  simp only [hx, hy, true_and]
  simp only [positions, List.mem_filter, List.mem_finRange, true_and, disjointness,
    decide_eq_true_eq, Bool.and_eq_false_iff]
  constructor
  · intro h i
    by_contra hi
    simp only [not_or, Bool.not_eq_false] at hi
    exact h i hi.1 i hi.2 rfl
  · rintro h i hi j hj rfl
    rcases h i with h | h <;> simp_all

/-- **Detecting a repeated item needs `Ω(n)` bits of memory**: a randomized streaming algorithm that
decides, with error at most `ε ≤ 1 / 2` on streams of at most `2 n` items of `Fin n`, whether all
items are distinct, and whose algorithms use at most `b` bits of memory on streams of at most `n`
items, has `n ≤ 2 ^ 10 r (b + 1) + 2 ^ 12` for every `r` with `(4 ε (1 - ε)) ^ r ≤ 1 / 64`. For
`ε < 1 / 2` such an `r` exists. -/
theorem le_of_solves_nodup {σ : Type*} {n b r : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 2)
    (hr : (4 * ε * (1 - ε)) ^ r ≤ 1 / 64) (μ : Randomized σ (Fin n) Bool)
    (hμ : μ.Solves ε (fun s c => c = decide s.Nodup) (2 * n)) (hspace : μ.SpaceLE n b) :
    n ≤ 2 ^ 10 * r * (b + 1) + 2 ^ 12 := by
  have hcc := μ.ecomplexityFun_le_of_spaceLE hspace positions positions length_positions_le id
    disjointness (ε := ε) fun x y => by
      have hlen : (positions x ++ positions y).length ≤ 2 * n := by
        rw [List.length_append]
        have := length_positions_le x
        have := length_positions_le y
        omega
      refine le_of_eq_of_le ?_ (hμ _ hlen)
      unfold Randomized.errorProb
      congr 2
      ext A
      have hd : disjointness x y = decide (positions x ++ positions y).Nodup := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, nodup_positions_append]
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, id, hd]
  have h1 := PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le hr n
  have h2 := PublicCoin.ecomplexityFun_le_two_mul_mul
    (f := (disjointness : BitString n → BitString n → Bool)) hε r
  have h3 : (n : ℕ∞) ≤ ((2 ^ 10 * r * (b + 1) + 2 ^ 12 : ℕ) : ℕ∞) := by
    refine h1.trans ?_
    calc 2 ^ 9 * PublicCoin.ecomplexityFun ((4 * ε * (1 - ε)) ^ r)
          (disjointness : BitString n → BitString n → Bool) + 2 ^ 12
        ≤ 2 ^ 9 * (2 * r * ((b + 1 : ℕ) : ℕ∞)) + 2 ^ 12 := by
          gcongr
          exact h2.trans (by gcongr; exact_mod_cast hcc)
      _ = ((2 ^ 10 * r * (b + 1) + 2 ^ 12 : ℕ) : ℕ∞) := by
          push_cast
          ring
  exact_mod_cast h3

/-- **Detecting a repeated item needs `Ω(n)` bits of memory**, for error `1 / 3`:
`n ≤ 36864 (b + 1) + 2 ^ 12`. -/
theorem le_of_solves_nodup_one_third {σ : Type*} {n b : ℕ} (μ : Randomized σ (Fin n) Bool)
    (hμ : μ.Solves (1 / 3) (fun s c => c = decide s.Nodup) (2 * n)) (hspace : μ.SpaceLE n b) :
    n ≤ 36864 * (b + 1) + 2 ^ 12 :=
  le_of_solves_nodup (r := 36) (by norm_num) (by norm_num) μ hμ hspace

/-- **Deterministic detection of a repeated item needs `n` bits of memory**: a deterministic
streaming algorithm deciding whether at most `2 n` items of `Fin n` are distinct, with at most
`b` bits of memory on streams of at most `n` items, has `n ≤ b`. -/
theorem Algorithm.le_of_run_eq_decide_nodup {σ : Type*} {n b : ℕ}
    (A : Algorithm σ (Fin n) Bool) (hA : ∀ s : List (Fin n), s.length ≤ 2 * n →
      A.run s = decide s.Nodup) (hspace : A.SpaceLE n b) : n ≤ b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have h := A.ecomplexityFun_le_of_spaceLE hspace positions positions length_positions_le id
    disjointness fun x y => by
      rw [id, hA _ (by
        rw [List.length_append]
        have := length_positions_le x
        have := length_positions_le y
        omega)]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, nodup_positions_append]
  have h2 := ecomplexity_disjointness hn
  unfold Protocol.ecomplexityFun at h
  rw [h2] at h
  have h3 : n + 1 ≤ b + 1 := by exact_mod_cast h
  omega

/-! ### The largest frequency -/

/-- The largest number of occurrences of an item in the stream `s` (`F∞`; zero for the empty
stream). -/
@[expose] def maxFreq {α : Type*} [DecidableEq α] (s : List α) : ℕ :=
  s.toFinset.sup fun a => s.count a

theorem maxFreq_le_one_of_nodup {α : Type*} [DecidableEq α] {s : List α} (hs : s.Nodup) :
    maxFreq s ≤ 1 :=
  Finset.sup_le fun a _ => List.nodup_iff_count_le_one.1 hs a

theorem one_le_maxFreq {α : Type*} [DecidableEq α] {s : List α} (hs : s ≠ []) : 1 ≤ maxFreq s := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil s hs
  exact (List.count_pos_iff.2 ha).trans_le (Finset.le_sup (f := fun a => s.count a)
    (List.mem_toFinset.2 ha))

theorem two_le_maxFreq_of_not_nodup {α : Type*} [DecidableEq α] {s : List α} (hs : ¬s.Nodup) :
    2 ≤ maxFreq s := by
  rw [List.nodup_iff_count_le_one] at hs
  push Not at hs
  obtain ⟨a, ha⟩ := hs
  have hmem : a ∈ s := List.count_pos_iff.1 (by omega)
  exact ha.trans_le (Finset.le_sup (f := fun a => s.count a) (List.mem_toFinset.2 hmem))

/-- The items of a stream are distinct exactly when no item occurs twice. -/
theorem maxFreq_le_one_iff {α : Type*} [DecidableEq α] {s : List α} :
    maxFreq s ≤ 1 ↔ s.Nodup :=
  ⟨fun h => by_contra fun hs => absurd (two_le_maxFreq_of_not_nodup hs) (by omega),
    maxFreq_le_one_of_nodup⟩

/-- On a nonempty stream, an estimate within less than a third of `F∞` decides whether the items
are distinct by comparing it with `4 / 3`. -/
theorem decide_lt_four_thirds_eq {α : Type*} [DecidableEq α] {s : List α} (hs : s ≠ []) {Y : ℝ}
    (hY : |Y - maxFreq s| < maxFreq s / 3) : decide (Y < 4 / 3) = decide s.Nodup := by
  rw [abs_lt] at hY
  by_cases hnd : s.Nodup
  · have h1 : (maxFreq s : ℝ) = 1 := by
      exact_mod_cast le_antisymm (maxFreq_le_one_of_nodup hnd) (one_le_maxFreq hs)
    rw [h1] at hY
    simp only [hnd, decide_true, decide_eq_true_eq]
    linarith
  · have h2 : (2 : ℝ) ≤ maxFreq s := by exact_mod_cast two_le_maxFreq_of_not_nodup hnd
    simp only [hnd, decide_false, decide_eq_false_iff_not, not_lt]
    linarith

/-- **Approximating `F∞` needs `Ω(n)` bits of memory** [AlonMatiasSzegedy1999, Proposition 3.1]:
a randomized streaming algorithm that estimates the largest frequency of a nonempty stream of at
most `2 n + 1` items of `Fin (n + 1)` within less than a third of it, except with probability at
most `ε ≤ 1 / 2`, and whose algorithms use at most `b` bits of memory on streams of at most `n + 1`
items, has `n ≤ 2 ^ 10 r (b + 1) + 2 ^ 12` for every `r` with `(4 ε (1 - ε)) ^ r ≤ 1 / 64`. An
estimate within `λ F∞` for a fixed `λ < 1 / 3` is in particular within less than a third. -/
theorem le_of_solves_maxFreq {σ : Type*} {n b r : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 2)
    (hr : (4 * ε * (1 - ε)) ^ r ≤ 1 / 64) (μ : Randomized σ (Fin (n + 1)) ℝ)
    (hμ : μ.Solves ε (fun s Y => s ≠ [] → |Y - maxFreq s| < maxFreq s / 3) (2 * n + 1))
    (hspace : μ.SpaceLE (n + 1) b) : n ≤ 2 ^ 10 * r * (b + 1) + 2 ^ 12 := by
  classical
  let p : List (Fin (n + 1)) := [Fin.last n]
  let d : ℝ → Bool := fun Y => decide (Y < 4 / 3)
  have hspace' : Randomized.SpaceLE (μ.map fun A => A.reduce p Fin.castSucc d) n b :=
    Randomized.SpaceLE.map_reduce p (by rwa [List.length_singleton, Nat.add_comm 1 n])
      Fin.castSucc d
  refine le_of_solves_nodup hε hr (μ.map fun A => A.reduce p Fin.castSucc d) (fun s hs => ?_)
    hspace'
  refine (μ.errorProb_map_reduce_le p Fin.castSucc _ s fun Y hY => ?_).trans
    (hμ _ (by simp only [p, List.length_append, List.length_singleton, List.length_map]; omega))
  have hne : p ++ s.map Fin.castSucc ≠ [] := by simp [p]
  change decide (Y < 4 / 3) = decide s.Nodup
  rw [decide_lt_four_thirds_eq hne (hY hne)]
  have hnd : (p ++ s.map Fin.castSucc).Nodup ↔ s.Nodup := by
    simp only [p, List.singleton_append, List.nodup_cons, List.mem_map, not_exists, not_and,
      List.nodup_map_iff (Fin.castSucc_injective n)]
    exact ⟨fun h => h.2, fun h => ⟨fun a _ => Fin.castSucc_ne_last a, h⟩⟩
  exact decide_eq_decide.2 hnd

/-- **Approximating `F∞` needs `Ω(n)` bits of memory** [AlonMatiasSzegedy1999, Proposition 3.1],
for error `1 / 3`: `n ≤ 36864 (b + 1) + 2 ^ 12`. -/
theorem le_of_solves_maxFreq_one_third {σ : Type*} {n b : ℕ} (μ : Randomized σ (Fin (n + 1)) ℝ)
    (hμ : μ.Solves (1 / 3) (fun s Y => s ≠ [] → |Y - maxFreq s| < maxFreq s / 3) (2 * n + 1))
    (hspace : μ.SpaceLE (n + 1) b) : n ≤ 36864 * (b + 1) + 2 ^ 12 :=
  le_of_solves_maxFreq (r := 36) (by norm_num) (by norm_num) μ hμ hspace

/-- **Computing `F∞` exactly needs `n` bits of memory** deterministically: a deterministic
streaming algorithm computing the largest frequency of every stream of at most `2 n` items of
`Fin n`, with at most `b` bits of memory on streams of at most `n` items, has `n ≤ b`. -/
theorem Algorithm.le_of_run_eq_maxFreq {σ : Type*} {n b : ℕ} (A : Algorithm σ (Fin n) ℕ)
    (hA : ∀ s : List (Fin n), s.length ≤ 2 * n → A.run s = maxFreq s) (hspace : A.SpaceLE n b) :
    n ≤ b := by
  refine (A.reduce [] id fun c => decide (c ≤ 1)).le_of_run_eq_decide_nodup (fun s hs => ?_)
    (Algorithm.SpaceLE.reduce [] (by rwa [List.length_nil, Nat.zero_add]) id _)
  rw [Algorithm.run_reduce, List.nil_append, List.map_id, hA s hs]
  exact decide_eq_decide.2 maxFreq_le_one_iff

end Cslib.Streaming
