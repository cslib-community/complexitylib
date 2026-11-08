/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.SingleTape.BoundedCrossings
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Single-tape machines in time `o(n log n)` decide only regular languages

The `n log n` gap for deterministic single-tape machines `Cslib.Turing.SingleTapeTM`: a machine
that decides a language within time `T(n) ≤ n ⌊log₂ n⌋ / (8 d)` for all large `n`, where
`d = ⌈log₂ (|Q| + 2)⌉` and `Q` is its state set, decides a regular language. In particular every
language decided in time `o(n log n)` is regular.

The proof bounds the crossing sequences at the input boundaries and then applies
`isRegular_of_crossings_le`. Fix a large `K` and suppose some input has a crossing sequence
longer than `K` at a boundary `b` inside it. Take such an input `w` of minimal length `n`. If two
boundaries `i < j` on the same side of `b` had the same crossing sequence, cutting out the letters
between them (`cut_and_paste_run`) would leave a shorter input that keeps the long crossing
sequence. So the crossing sequences at the boundaries `1, …, b` are pairwise distinct, and so are
those at `b, …, n`. One of these families has at least `(n + 1) / 2` members. Fewer than half of
them can be shorter than about `log₂ n / d`, so the run on `w` crosses these boundaries about
`n log₂ n / (4 d)` times in total. This exceeds `T(n)` once `n` is large, and `K` is chosen so
that a crossing sequence longer than `K` forces `n` to be large.

The boundaries used are all inside the input. Crossings in the blank regions to the left and right
of the input count towards the running time but are never cut.

The constant `1 / (8 d)` is this formalization's own; it is not claimed to match a published
constant.

Hennie [Hennie1965] proved that linear-time single-tape machines accept only regular languages.
The `n log n` bound was obtained independently by Trakhtenbrot (1964), by Hartmanis
[Hartmanis1968] and by Kobayashi [Kobayashi1985]; this attribution follows
[Pighizzini2009, §1 and §4]. The proof above is the minimal-counterexample argument from the proof
of [Pighizzini2009, Theorem 3], specialized to deterministic machines. That proof, for
nondeterministic machines, shows that a crossing sequence occurs at most twice in a shortest
witness; the version here shows instead that the crossing sequences on each side of the long one
are pairwise distinct.

## Main results

* `Cslib.Turing.SingleTapeTM.isRegular_of_time_le_mul_log`: if `8 d T(n) ≤ n ⌊log₂ n⌋` for all
  `n ≥ N`, the decided language is regular.
* `Cslib.Turing.SingleTapeTM.isRegular_of_isLittleO`: if `T(n) = o(n log n)`, the decided language
  is regular.

## References

* [F. C. Hennie, *One-tape, off-line Turing machine computations*][Hennie1965]
* [J. Hartmanis, *Computational complexity of one-tape Turing machine computations*][Hartmanis1968]
* [K. Kobayashi, *On proving time constructibility of functions*][Kobayashi1985]
* [G. Pighizzini, *Nondeterministic one-tape off-line Turing machines and their time
  complexity*][Pighizzini2009]
-/

public section

open Cslib Cslib.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}
  {α : Type*} {ι : α → Symbol} {L : Language α} {yes : Symbol} {T : ℕ → ℕ}

/-- **Cutting out a segment.** If the boundaries `i < j` of `w` have the same crossing sequence,
deleting the letters between them gives an input whose crossing sequence at every boundary
`b ≤ i` is that of `w` at `b`, and at every boundary `b ≥ i` that of `w` at `b + (j - i)`. -/
private lemma crossings_cut (hdec : tm.DecidesByHeadInTime ι L yes T) {w : List α} {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ w.length)
    (h : (tm.absInit (w.map ι)).crossings (i : ℤ) (T w.length) =
      (tm.absInit (w.map ι)).crossings (j : ℤ) (T w.length)) :
    (∀ b : ℕ, b ≤ i →
      (tm.absInit ((w.take i ++ w.drop j).map ι)).crossings (b : ℤ)
          (T (w.take i ++ w.drop j).length) =
        (tm.absInit (w.map ι)).crossings (b : ℤ) (T w.length)) ∧
    (∀ b : ℕ, i ≤ b →
      (tm.absInit ((w.take i ++ w.drop j).map ι)).crossings (b : ℤ)
          (T (w.take i ++ w.drop j).length) =
        (tm.absInit (w.map ι)).crossings ((b + (j - i) : ℕ) : ℤ) (T w.length)) := by
  obtain ⟨hw, -⟩ := hdec.absRun w
  obtain ⟨hw', -⟩ := hdec.absRun (w.take i ++ w.drop j)
  have e₁ : w.map ι = (w.take i).map ι ++ (w.drop i).map ι := by
    rw [← List.map_append, List.take_append_drop]
  have e₂ : w.map ι = (w.take j).map ι ++ (w.drop j).map ι := by
    rw [← List.map_append, List.take_append_drop]
  have e₃ : (w.take i).map ι ++ (w.drop j).map ι = (w.take i ++ w.drop j).map ι :=
    (List.map_append ..).symm
  have l₁ : ((w.take i).map ι).length = i := by
    simp only [List.length_map, List.length_take]; omega
  have l₂ : ((w.take j).map ι).length = j := by
    simp only [List.length_map, List.length_take]; omega
  have hne : (w.take i).map ι = [] ↔ (w.take j).map ι = [] := by
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, l₁, l₂]
    omega
  have hL : ((tm.absInit ((w.take i).map ι ++ (w.drop i).map ι)).run (T w.length)).state =
      none := by
    rw [← e₁]; exact hw
  have hR : ((tm.absInit ((w.take j).map ι ++ (w.drop j).map ι)).run (T w.length)).state =
      none := by
    rw [← e₂]; exact hw
  have hx : (tm.absInit ((w.take i).map ι ++ (w.drop i).map ι)).crossings
      ((w.take i).map ι).length (T w.length) =
      (tm.absInit ((w.take j).map ι ++ (w.drop j).map ι)).crossings
      ((w.take j).map ι).length (T w.length) := by
    rw [← e₁, ← e₂, l₁, l₂]; exact h
  obtain ⟨hC, hcL, hcR, -⟩ := cut_and_paste_run hne hL hR hx
  rw [e₃] at hC hcL hcR
  rw [← e₁] at hcL
  rw [← e₂] at hcR
  have heq (b : ℤ) : (tm.absInit ((w.take i ++ w.drop j).map ι)).crossings b
      (T (w.take i ++ w.drop j).length) =
      (tm.absInit ((w.take i ++ w.drop j).map ι)).crossings b (T w.length + T w.length) :=
    AbsCfg.crossings_eq_of_halted _ b hw' hC
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rw [heq]
    exact hcL b (by rw [l₁]; exact_mod_cast hb)
  · rw [heq, hcR b (by rw [l₁]; exact_mod_cast hb), l₁, l₂]
    congr 1
    omega

/-- In a shortest input with a crossing sequence longer than `K` at a boundary `b`, two
boundaries `i < j` with `b ≤ i` or `j ≤ b` have different crossing sequences: otherwise cutting
out the letters between them leaves a shorter input with the same long crossing sequence. -/
private lemma crossings_ne_of_minimal (hdec : tm.DecidesByHeadInTime ι L yes T) {K : ℕ}
    {w : List α} {b : ℕ} (hb1 : 1 ≤ b) (hbn : b ≤ w.length)
    (hlong : K < ((tm.absInit (w.map ι)).crossings (b : ℤ) (T w.length)).length)
    (hmin : ∀ w' : List α, w'.length < w.length → ∀ b' : ℕ, 1 ≤ b' → b' ≤ w'.length →
      ((tm.absInit (w'.map ι)).crossings (b' : ℤ) (T w'.length)).length ≤ K)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ w.length) (hb : b ≤ i ∨ j ≤ b) :
    (tm.absInit (w.map ι)).crossings (i : ℤ) (T w.length) ≠
      (tm.absInit (w.map ι)).crossings (j : ℤ) (T w.length) := by
  intro h
  obtain ⟨hcL, hcR⟩ := crossings_cut hdec hi hij hj h
  have hlen : (w.take i ++ w.drop j).length = i + (w.length - j) := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  have hshort : (w.take i ++ w.drop j).length < w.length := by omega
  rcases hb with hb | hb
  · have h' := hmin _ hshort b hb1 (by omega)
    rw [hcL b hb] at h'
    omega
  · have h' := hmin _ hshort (b - (j - i)) (by omega) (by omega)
    rw [hcR (b - (j - i)) (by omega), show b - (j - i) + (j - i) = b by omega] at h'
    omega

/-- If the crossing sequences of a run during `t` steps at the boundaries in `S` are pairwise
distinct, then `|S| ⌊(⌊log₂ |S|⌋ - 1) / d⌋ ≤ 2 t`, where `d = ⌈log₂ (|Q| + 2)⌉`. -/
private lemma card_mul_le_of_injOn (a : tm.AbsCfg) (t : ℕ) {S : Finset ℕ}
    (hS : Set.InjOn (fun b : ℕ => a.crossings (b : ℤ) t) S) :
    S.card * ((Nat.log 2 S.card - 1) / Nat.clog 2 (Fintype.card tm.State + 2)) ≤ 2 * t := by
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.clog 2 (Fintype.card tm.State + 2) := ⟨_, rfl⟩
  rw [← hd_def]
  have hd : 0 < d := hd_def ▸ Nat.clog_pos one_lt_two (by omega)
  have hsum : ∑ b ∈ S, (a.crossings (b : ℤ) t).length ≤ t := by
    have h := a.sum_length_crossings_le (S.image fun b : ℕ => (b : ℤ)) t
    rwa [Finset.sum_image fun i _ j _ hij => by exact_mod_cast hij] at h
  obtain ⟨m, hm⟩ : ∃ m, m = S.card := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = (Nat.log 2 m - 1) / d := ⟨_, rfl⟩
  have hcnt := card_sub_pow_mul_le_sum_length hS L
  rw [← hm] at hcnt ⊢
  rw [← hL]
  have hpow : Fintype.card (Option tm.State) + 1 ≤ 2 ^ d := by
    rw [Fintype.card_option, hd_def]
    exact Nat.le_pow_clog one_lt_two _
  have hP : (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ (d * L) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hpow L
  rcases Nat.eq_zero_or_pos L with h0 | hLpos
  · rw [h0, Nat.mul_zero]
    exact Nat.zero_le _
  · have hdiv : d * L + (Nat.log 2 m - 1) % d = Nat.log 2 m - 1 := hL ▸ Nat.div_add_mod _ d
    have hdL : 1 ≤ d * L := Nat.mul_pos hd hLpos
    have hlog : d * L + 1 ≤ Nat.log 2 m := by omega
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hlog
    have h2P : 2 * 2 ^ (d * L) ≤ m :=
      calc 2 * 2 ^ (d * L) = 2 ^ (d * L + 1) := by ring
        _ ≤ 2 ^ Nat.log 2 m := Nat.pow_le_pow_right two_pos hlog
        _ ≤ m := Nat.pow_log_le_self 2 hm0
    have hmP : m ≤ 2 * (m - (Fintype.card (Option tm.State) + 1) ^ L) := by omega
    calc m * L ≤ 2 * (m - (Fintype.card (Option tm.State) + 1) ^ L) * L :=
          Nat.mul_le_mul_right _ hmP
      _ = 2 * ((m - (Fintype.card (Option tm.State) + 1) ^ L) * L) := by ring
      _ ≤ 2 * t := Nat.mul_le_mul_left _ (hcnt.trans hsum)

/-- The arithmetic core: `m ≥ (n + 1) / 2` boundaries with pairwise distinct crossing sequences
are incompatible with `8 d t ≤ n ⌊log₂ n⌋` once `n ≥ 2 ^ (2 d + 3)`. -/
private lemma gap_arith {d n m t : ℕ} (hd : 0 < d) (hm : n + 1 ≤ 2 * m)
    (hn : 2 ^ (2 * d + 3) ≤ n) (hcount : m * ((Nat.log 2 m - 1) / d) ≤ 2 * t)
    (hT : 8 * d * t ≤ n * Nat.log 2 n) : False := by
  obtain ⟨l, hl⟩ : ∃ l, l = Nat.log 2 m := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.log 2 n := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = (l - 1) / d := ⟨_, rfl⟩
  rw [← hl, ← hL] at hcount
  rw [← hg] at hT
  have hg1 : 2 * d + 3 ≤ g := hg ▸ Nat.le_log_of_pow_le one_lt_two hn
  have hpos : 0 < 2 ^ (2 * d + 3) := by positivity
  have hg2 : g ≤ l + 1 := by
    rw [hg, hl, ← Nat.log_mul_base one_lt_two (by omega : m ≠ 0)]
    exact Nat.log_mono_right (by omega)
  have hdiv : d * L + (l - 1) % d = l - 1 := hL ▸ Nat.div_add_mod (l - 1) d
  have hmod := Nat.mod_lt (l - 1) hd
  have h3 : g + 1 ≤ 2 * (d * L) := by omega
  have h1 : 2 * m * (d * L) ≤ 4 * d * t :=
    calc 2 * m * (d * L) = 2 * d * (m * L) := by ring
      _ ≤ 2 * d * (2 * t) := Nat.mul_le_mul_left _ hcount
      _ = 4 * d * t := by ring
  have h4 : (n + 1) * (g + 1) ≤ n * g :=
    calc (n + 1) * (g + 1) ≤ (n + 1) * (2 * (d * L)) := Nat.mul_le_mul_left _ h3
      _ = 2 * ((n + 1) * (d * L)) := by ring
      _ ≤ 2 * (2 * m * (d * L)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm)
      _ ≤ 2 * (4 * d * t) := Nat.mul_le_mul_left _ h1
      _ = 8 * d * t := by ring
      _ ≤ n * g := hT
  nlinarith

/-- **The `n log n` gap for single-tape machines.** Let `d = ⌈log₂ (|Q| + 2)⌉` where `Q` is the
state set. If `tm` decides `L` within time `T`, answering under the head, and
`8 d T(n) ≤ n ⌊log₂ n⌋` for all `n ≥ N`, then `L` is regular. That is, time
`T(n) ≤ ε n ⌊log₂ n⌋` for large `n` with `ε = 1 / (8 d)` suffices. -/
theorem isRegular_of_time_le_mul_log (hdec : tm.DecidesByHeadInTime ι L yes T) {N : ℕ}
    (hT : ∀ n, N ≤ n → 8 * Nat.clog 2 (Fintype.card tm.State + 2) * T n ≤ n * Nat.log 2 n) :
    L.IsRegular := by
  classical
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.clog 2 (Fintype.card tm.State + 2) := ⟨_, rfl⟩
  rw [← hd_def] at hT
  have hd : 0 < d := hd_def ▸ Nat.clog_pos one_lt_two (by omega)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, N₀ = max N (2 ^ (2 * d + 3)) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = ∑ n ∈ Finset.range N₀, T n := ⟨_, rfl⟩
  refine isRegular_of_crossings_le hdec K ?_
  by_contra hbad
  push Not at hbad
  have hex : ∃ n, ∃ w : List α, w.length = n ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ n ∧
      K < ((tm.absInit (w.map ι)).crossings (b : ℤ) (T n)).length := by
    obtain ⟨w, b, h1, h2, h3⟩ := hbad
    exact ⟨_, w, rfl, b, h1, h2, h3⟩
  obtain ⟨w, hwn, b, hb1, hbn, hlong⟩ := Nat.find_spec hex
  have hmin : ∀ w' : List α, w'.length < Nat.find hex → ∀ b' : ℕ, 1 ≤ b' → b' ≤ w'.length →
      ((tm.absInit (w'.map ι)).crossings (b' : ℤ) (T w'.length)).length ≤ K := by
    intro w' hw' b' hb1' hb2'
    by_contra hc
    push Not at hc
    exact Nat.find_min hex hw' ⟨w', rfl, b', hb1', hb2', hc⟩
  rw [← hwn] at hbn hlong hmin
  have hN : N₀ ≤ w.length := by
    by_contra h
    push Not at h
    have h1 : T w.length ≤ K :=
      hK ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr h)
    have h2 := AbsCfg.length_crossings_le (tm.absInit (w.map ι)) (b : ℤ) (T w.length)
    omega
  have hinjL : Set.InjOn (fun i : ℕ => (tm.absInit (w.map ι)).crossings (i : ℤ) (T w.length))
      (Finset.Icc 1 b) := by
    intro i hi j hj hij
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact crossings_ne_of_minimal hdec hb1 hbn hlong hmin hi.1 h (by omega) (Or.inr hj.2) hij
    · exact crossings_ne_of_minimal hdec hb1 hbn hlong hmin hj.1 h (by omega) (Or.inr hi.2)
        hij.symm
  have hinjR : Set.InjOn (fun i : ℕ => (tm.absInit (w.map ι)).crossings (i : ℤ) (T w.length))
      (Finset.Icc b w.length) := by
    intro i hi j hj hij
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact crossings_ne_of_minimal hdec hb1 hbn hlong hmin (by omega) h hj.2 (Or.inl hi.1) hij
    · exact crossings_ne_of_minimal hdec hb1 hbn hlong hmin (by omega) h hi.2 (Or.inl hj.1)
        hij.symm
  have hsplit : (Finset.Icc 1 b).card + (Finset.Icc b w.length).card = w.length + 1 := by
    simp only [Nat.card_Icc]
    omega
  obtain ⟨S, hS, hcard⟩ : ∃ S : Finset ℕ,
      Set.InjOn (fun i : ℕ => (tm.absInit (w.map ι)).crossings (i : ℤ) (T w.length)) S ∧
        w.length + 1 ≤ 2 * S.card := by
    by_cases hc : (Finset.Icc b w.length).card ≤ (Finset.Icc 1 b).card
    · exact ⟨_, hinjL, by omega⟩
    · exact ⟨_, hinjR, by omega⟩
  have hc := card_mul_le_of_injOn (tm.absInit (w.map ι)) (T w.length) hS
  rw [← hd_def] at hc
  exact gap_arith hd hcard (by omega) hc (hT _ (by omega))

/-- **Single-tape machines in time `o(n log n)` decide only regular languages.** If `tm` decides
`L` within time `T`, answering under the head, and `T(n) = o(n log n)`, then `L` is regular. -/
theorem isRegular_of_isLittleO (hdec : tm.DecidesByHeadInTime ι L yes T)
    (hT : (fun n : ℕ => (T n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ) * Real.log n) :
    L.IsRegular := by
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.clog 2 (Fintype.card tm.State + 2) := ⟨_, rfl⟩
  have hd : 0 < d := hd_def ▸ Nat.clog_pos one_lt_two (by omega)
  have hlog2 := Real.log_pos one_lt_two
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : (0 : ℝ) < 1 / (16 * d * Real.log 2) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hT.bound hc)
  refine isRegular_of_time_le_mul_log hdec (N := max N 2) fun n hn => ?_
  rw [← hd_def]
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have h1 := hN n (le_of_max_le_left hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hn1))] at h1
  have hlog : Real.log n ≤ 2 * Real.log 2 * (Nat.log 2 n : ℝ) := by
    have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self one_lt_two n
    have hpos : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast Nat.log_pos one_lt_two hn2
    calc Real.log n ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hlt.le)
      _ = ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
          rw [Real.log_pow]
          push_cast
          ring
      _ ≤ 2 * Real.log 2 * (Nat.log 2 n : ℝ) := by nlinarith
  have key : (8 * d * T n : ℝ) ≤ n * (Nat.log 2 n : ℝ) :=
    calc (8 * d * T n : ℝ) ≤ 8 * d * (1 / (16 * d * Real.log 2) * (n * Real.log n)) := by
          gcongr
      _ = n * Real.log n / (2 * Real.log 2) := by
          field_simp
          ring
      _ ≤ n * (2 * Real.log 2 * (Nat.log 2 n : ℝ)) / (2 * Real.log 2) := by gcongr
      _ = n * (Nat.log 2 n : ℝ) := by
          field_simp
  exact_mod_cast key

end Cslib.Turing.SingleTapeTM
