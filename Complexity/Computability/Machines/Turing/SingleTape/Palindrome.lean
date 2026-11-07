/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.SingleTape.CrossingSequence
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-tape machines need quadratic time for palindromes

The classical quadratic lower bound for palindromes, proved with Hennie's crossing-sequence
method: a deterministic single-tape Turing machine (`Cslib.Turing.SingleTapeTM`) that decides
palindromes needs `Ω(n²)` steps on some input of each large length `n`.

The proof uses crossing sequences (`CrossingSequence.lean`). Fix `m` and `r` and consider the
`2 ^ m` hard inputs `palWord a b r x = x ++ aʳ ++ reverse x` for bit strings `x` of length `m`,
written with the letters `a ≠ b`. All of them are palindromes. If two distinct hard inputs had
the same crossing sequence at a boundary inside the middle block, the cut-and-paste lemma would
make the machine accept a non-palindrome. So at every such boundary the `2 ^ m` crossing
sequences are distinct. Fewer than half of them can be shorter than about `m / log |Q|`. Since
the crossing sequences of one run have total length at most its running time, some hard input
needs time proportional to `r · m / log |Q|`.

## Main definitions

* `Cslib.Turing.SingleTapeTM.DecidesPalindromesInTime tm a b yes T`: on every word over the
  letters `a, b`, `tm` halts within `T n` steps and its output begins with `yes` exactly when
  the input is a palindrome.
* `Cslib.Turing.SingleTapeTM.palWord a b r x`: the hard inputs.

## Main results

* `Cslib.Turing.SingleTapeTM.crossings_palWord_injective`: distinct hard inputs have distinct
  crossing sequences at every boundary inside the middle block.
* `Cslib.Turing.SingleTapeTM.crossing_bound`: if `2 (|Q| + 2) ^ L ≤ 2 ^ m`, then
  `(r + 1) L ≤ 2 T (2m + r)`.
* `Cslib.Turing.SingleTapeTM.palindrome_lower_bound`: with `d = ⌈log₂ (|Q| + 2)⌉`, every
  `n ≥ 8d` satisfies `n² ≤ 64 d T(n)`.
* `Cslib.Turing.SingleTapeTM.not_decidesPalindromesInTime_linear`: no single-tape machine
  decides palindromes within time `c (n + 1)`.

## References

* [F. C. Hennie, *One-tape, off-line Turing machine computations*][Hennie1965]
* [M. Li and P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019], Chapter 6 (an incompressibility version of the same argument)
-/

public section

open Cslib Cslib.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma palindrome_append_replicate_append_reverse {u : List Symbol} {c : Symbol} {r : ℕ}
    {w : List Symbol} (hw : w.length = u.length) :
    (u ++ List.replicate r c ++ w.reverse).Palindrome ↔ w = u := by
  rw [List.Palindrome.iff_reverse_eq]
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.append_assoc]
  constructor
  · intro h
    exact (List.append_inj h hw).1
  · rintro rfl
    rfl

variable (tm) in
/-- `tm` decides palindromes over the letters `a, b` within time `T`: on every word over
`{a, b}` of length `n` it halts within `T n` steps, and its output begins with `yes` exactly
when the word is a palindrome. Symbols other than `a` and `b` may occur in the alphabet and on
the tape; inputs containing them are unconstrained. -/
@[expose] def DecidesPalindromesInTime (a b yes : Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ w : List Symbol, (∀ x ∈ w, x = a ∨ x = b) →
    ∃ o, tm.OutputsWithinTime w o (T w.length) ∧ (o.head? = some yes ↔ w.Palindrome)

/-- Bit strings written with the letters `a` (for `false`) and `b` (for `true`). -/
@[expose] def encodeBits (a b : Symbol) (x : List Bool) : List Symbol :=
  x.map fun β => if β then b else a

omit [Inhabited Symbol] [Fintype Symbol] in
lemma encodeBits_injective {a b : Symbol} (hab : a ≠ b) : Function.Injective (encodeBits a b) := by
  refine List.map_injective_iff.mpr fun β γ h => ?_
  cases β <;> cases γ <;> simp_all [eq_comm]

omit [Inhabited Symbol] [Fintype Symbol] in
@[simp] lemma length_encodeBits (a b : Symbol) (x : List Bool) :
    (encodeBits a b x).length = x.length := List.length_map _

/-- The hard inputs: `x`, a block of `r` copies of `a`, then `x` reversed. -/
@[expose] def palWord (a b : Symbol) (r : ℕ) (x : List Bool) : List Symbol :=
  encodeBits a b x ++ List.replicate r a ++ (encodeBits a b x).reverse

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma palWord_split (a b : Symbol) (x : List Bool) {i r : ℕ} (hi : i ≤ r) :
    palWord a b r x = (encodeBits a b x ++ List.replicate i a) ++
      (List.replicate (r - i) a ++ (encodeBits a b x).reverse) := by
  rw [palWord, List.append_assoc, List.append_assoc, ← List.append_assoc (List.replicate i a),
    ← List.replicate_add, Nat.add_sub_cancel' hi]

omit [Inhabited Symbol] [Fintype Symbol] in
lemma mem_palWord {a b : Symbol} {r : ℕ} {x : List Bool} :
    ∀ c ∈ palWord a b r x, c = a ∨ c = b := by
  intro c hc
  simp only [palWord, encodeBits, List.mem_append, List.mem_map, List.mem_replicate,
    List.mem_reverse] at hc
  rcases hc with (⟨β, -, rfl⟩ | ⟨-, rfl⟩) | ⟨β, -, rfl⟩
  · cases β <;> simp
  · simp
  · cases β <;> simp

omit [Inhabited Symbol] [Fintype Symbol] in
@[simp] lemma length_palWord (a b : Symbol) (r : ℕ) (x : List Bool) :
    (palWord a b r x).length = 2 * x.length + r := by
  simp [palWord]; omega

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma mem_mixWord {a b : Symbol} {r : ℕ} {x y : List Bool} :
    ∀ c ∈ encodeBits a b x ++ List.replicate r a ++ (encodeBits a b y).reverse,
      c = a ∨ c = b := by
  intro c hc
  simp only [encodeBits, List.mem_append, List.mem_map, List.mem_replicate,
    List.mem_reverse] at hc
  rcases hc with (⟨β, -, rfl⟩ | ⟨-, rfl⟩) | ⟨β, -, rfl⟩
  · cases β <;> simp
  · simp
  · cases β <;> simp

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma palindrome_mixWord_iff {a b : Symbol} (hab : a ≠ b) {r : ℕ} {x y : List Bool}
    (hxy : y.length = x.length) :
    (encodeBits a b x ++ List.replicate r a ++ (encodeBits a b y).reverse).Palindrome ↔
      y = x := by
  rw [palindrome_append_replicate_append_reverse (by simp [hxy])]
  exact (encodeBits_injective hab).eq_iff

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma mixWord_split (a b : Symbol) (x y : List Bool) {i r : ℕ} (hi : i ≤ r) :
    (encodeBits a b x ++ List.replicate i a) ++
      (List.replicate (r - i) a ++ (encodeBits a b y).reverse) =
    encodeBits a b x ++ List.replicate r a ++ (encodeBits a b y).reverse := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc (List.replicate i a),
    ← List.replicate_add, Nat.add_sub_cancel' hi]

/-- Distinct hard inputs have distinct crossing sequences at every boundary inside the middle
block. -/
theorem crossings_palWord_injective {a b yes : Symbol} (hab : a ≠ b) {T : ℕ → ℕ}
    (hdec : DecidesPalindromesInTime tm a b yes T) {r i : ℕ} (hi : i ≤ r) {x y : List Bool}
    (hxy : y.length = x.length)
    (h : (tm.absInit (palWord a b r x)).crossings ((x.length + i : ℕ) : ℤ) (T (2 * x.length + r)) =
      (tm.absInit (palWord a b r y)).crossings ((x.length + i : ℕ) : ℤ) (T (2 * x.length + r))) :
    x = y := by
  obtain ⟨o₁, h₁, hy₁⟩ := hdec (palWord a b r x) mem_palWord
  obtain ⟨o₂, h₂, hy₂⟩ := hdec (palWord a b r y) mem_palWord
  have hp₁ : o₁.head? = some yes := hy₁.mpr ((palindrome_mixWord_iff hab rfl).mpr rfl)
  have hp₂ : o₂.head? = some yes := hy₂.mpr ((palindrome_mixWord_iff hab rfl).mpr rfl)
  rw [length_palWord] at h₁ h₂
  rw [hxy] at h₂
  rw [palWord_split a b x hi] at h₁ h
  rw [palWord_split a b y hi] at h₂ h
  have hk : x.length + i = (encodeBits a b x ++ List.replicate i a).length := by simp
  rw [hk] at h
  have hu : (encodeBits a b x ++ List.replicate i a).length =
      (encodeBits a b y ++ List.replicate i a).length := by simp [hxy]
  obtain ⟨-, -, hout⟩ := cut_and_paste hu h₁ h₂ h
  rw [mixWord_split a b x y hi] at hout
  obtain ⟨o, ho, hyo⟩ := hdec _ mem_mixWord
  have hpo : o.head? = some yes := by
    rcases hout ho with h' | h' <;> rw [h'] <;> assumption
  exact ((palindrome_mixWord_iff hab hxy).mp (hyo.mp hpo)).symm

omit [Inhabited Symbol] [Fintype Symbol] in
/-- At most `(|α| + 1) ^ L` elements have pairwise distinct images that are lists of length
`< L` over `α`. -/
private lemma card_filter_length_lt_le {ι α : Type*} [Fintype α] {s : Finset ι} {f : ι → List α}
    (hf : Set.InjOn f s) (L : ℕ) :
    (s.filter fun x => (f x).length < L).card ≤ (Fintype.card α + 1) ^ L := by
  classical
  have h := Finset.card_le_card_of_injOn (s := s.filter fun x => (f x).length < L)
    (t := (Finset.univ : Finset (Fin L → Option α))) (fun x j => (f x)[(j : ℕ)]?)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  · simpa [Fintype.card_option] using h
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    refine hf hx.1 hy.1 (List.ext_getElem? fun j => ?_)
    by_cases hj : j < L
    · exact congrFun hxy ⟨j, hj⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **Averaging step.** If at most half of the `2 ^ m` hard inputs can have a crossing sequence
shorter than `L` at any boundary, some hard input of length `2m + r` crosses the `r + 1` middle
boundaries at least `(r + 1) L / 2` times in total. -/
theorem crossing_bound {a b yes : Symbol} (hab : a ≠ b) {T : ℕ → ℕ}
    (hdec : DecidesPalindromesInTime tm a b yes T) (m r L : ℕ)
    (hL : 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ m) :
    (r + 1) * L ≤ 2 * T (2 * m + r) := by
  classical
  set P := (Fintype.card (Option tm.State) + 1) ^ L
  set t := T (2 * m + r)
  let cs : ℕ → (Fin m → Bool) → List (Option tm.State) := fun i x =>
    (tm.absInit (palWord a b r (List.ofFn x))).crossings ((m + i : ℕ) : ℤ) t
  have hinj (i : ℕ) (hi : i ≤ r) : Set.InjOn (cs i) (Finset.univ : Finset (Fin m → Bool)) := by
    intro x _ y _ hxy
    have h := crossings_palWord_injective hab hdec hi
      (x := List.ofFn x) (y := List.ofFn y) (by simp) (by simpa [cs, t] using hxy)
    exact List.ofFn_injective h
  have hgood (i : ℕ) (hi : i ≤ r) : (2 ^ m - P) * L ≤ ∑ x, (cs i x).length := by
    have hbad := card_filter_length_lt_le (hinj i hi) L
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m → Bool))) (fun x => (cs i x).length < L)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hsplit
    calc (2 ^ m - P) * L
        ≤ ((Finset.univ : Finset (Fin m → Bool)).filter fun x => ¬ (cs i x).length < L).card
          * L := Nat.mul_le_mul_right _ (by omega)
      _ ≤ ∑ x ∈ Finset.univ.filter fun x => ¬ (cs i x).length < L, (cs i x).length := by
          rw [← smul_eq_mul]
          exact Finset.card_nsmul_le_sum _ _ _ fun x hx => by
            rw [Finset.mem_filter] at hx
            omega
      _ ≤ ∑ x, (cs i x).length :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
            Nat.zero_le _
  have hupper (x : Fin m → Bool) : ∑ i ∈ Finset.range (r + 1), (cs i x).length ≤ t := by
    have h := AbsCfg.sum_length_crossings_le
      ((Finset.range (r + 1)).image fun i : ℕ => ((m + i : ℕ) : ℤ))
      (tm.absInit (palWord a b r (List.ofFn x))) t
    rwa [Finset.sum_image fun i _ j _ hij => by omega] at h
  have key : (r + 1) * ((2 ^ m - P) * L) ≤ 2 ^ m * t := by
    calc (r + 1) * ((2 ^ m - P) * L)
        = ∑ _i ∈ Finset.range (r + 1), (2 ^ m - P) * L := by simp
      _ ≤ ∑ i ∈ Finset.range (r + 1), ∑ x, (cs i x).length :=
          Finset.sum_le_sum fun i hi => hgood i (by simpa [Nat.lt_succ_iff] using hi)
      _ = ∑ x, ∑ i ∈ Finset.range (r + 1), (cs i x).length := Finset.sum_comm
      _ ≤ ∑ _x : Fin m → Bool, t := Finset.sum_le_sum fun x _ => hupper x
      _ = 2 ^ m * t := by simp
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have h2 : 2 ^ m ≤ 2 * (2 ^ m - P) := by omega
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc 2 ^ m * ((r + 1) * L)
      ≤ 2 * (2 ^ m - P) * ((r + 1) * L) := Nat.mul_le_mul_right _ h2
    _ = 2 * ((r + 1) * ((2 ^ m - P) * L)) := by ring
    _ ≤ 2 * (2 ^ m * t) := Nat.mul_le_mul_left _ key
    _ = 2 ^ m * (2 * t) := by ring

/-- **Hennie's quadratic lower bound for palindromes.** Let `d = ⌈log₂ (|Q| + 2)⌉` where `Q` is
the state set. If a single-tape machine decides palindromes over two letters `a ≠ b` within
time `T`, then `n ^ 2 ≤ 64 d T(n)` for every `n ≥ 8 d`. -/
theorem palindrome_lower_bound {a b yes : Symbol} (hab : a ≠ b) {T : ℕ → ℕ}
    (hdec : DecidesPalindromesInTime tm a b yes T) {n : ℕ}
    (hn : 8 * Nat.clog 2 (Fintype.card tm.State + 2) ≤ n) :
    n ^ 2 ≤ 64 * Nat.clog 2 (Fintype.card tm.State + 2) * T n := by
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.clog 2 (Fintype.card tm.State + 2) := ⟨_, rfl⟩
  rw [← hd_def] at hn ⊢
  have hd : 0 < d := hd_def ▸ Nat.clog_pos one_lt_two (by omega)
  obtain ⟨m, hm⟩ : ∃ m, m = n / 4 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = n - 2 * m := ⟨_, rfl⟩
  obtain ⟨L, hL_def⟩ : ∃ L, L = (m - 1) / d := ⟨_, rfl⟩
  have hpow : Fintype.card (Option tm.State) + 1 ≤ 2 ^ d := by
    rw [Fintype.card_option, hd_def]
    exact Nat.le_pow_clog one_lt_two _
  have hdiv : d * L + (m - 1) % d = m - 1 := hL_def ▸ Nat.div_add_mod (m - 1) d
  have hmod := Nat.mod_lt (m - 1) hd
  have hm2 : 2 * d ≤ m := by omega
  have hL : 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ m := by
    calc 2 * (Fintype.card (Option tm.State) + 1) ^ L
        ≤ 2 * (2 ^ d) ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow L)
      _ = 2 ^ (d * L + 1) := by rw [← pow_mul]; ring
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 := crossing_bound hab hdec m r L hL
  have hn' : 2 * m + r = n := by omega
  rw [hn'] at h1
  have h2 : m ≤ 2 * (d * L) := by omega
  have h3 : (r + 1) * m ≤ 4 * d * T n :=
    calc (r + 1) * m ≤ (r + 1) * (2 * (d * L)) := Nat.mul_le_mul_left _ h2
      _ = 2 * d * ((r + 1) * L) := by ring
      _ ≤ 2 * d * (2 * T n) := Nat.mul_le_mul_left _ h1
      _ = 4 * d * T n := by ring
  have h4 : n + 2 ≤ 2 * (r + 1) := by omega
  have h5 : n ≤ 4 * m + 3 := by omega
  have h6 : 8 ≤ n := by omega
  have F1 := Nat.mul_le_mul_right (4 * m) h4
  have F2 := Nat.mul_le_mul_left (n + 2) h5
  have F3 := Nat.mul_le_mul_right (n + 6) h6
  nlinarith [F1, F2, F3, h3]

/-- No single-tape machine decides palindromes over two letters in linear time. -/
theorem not_decidesPalindromesInTime_linear {a b yes : Symbol} (hab : a ≠ b) (c : ℕ) :
    ¬ DecidesPalindromesInTime tm a b yes fun n => c * (n + 1) := by
  intro hdec
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.clog 2 (Fintype.card tm.State + 2) := ⟨_, rfl⟩
  have hd : 0 < d := hd_def ▸ Nat.clog_pos one_lt_two (by omega)
  have h := palindrome_lower_bound hab hdec (n := 8 * d + 64 * d * c + 2) (by omega)
  rw [← hd_def] at h
  have key : ∀ M N : ℕ, M + 2 ≤ N → N ^ 2 ≤ M * (N + 1) → False := fun M N h1 h2 => by
    have := Nat.mul_le_mul_right N h1
    nlinarith
  refine key (64 * d * c) (8 * d + 64 * d * c + 2) (by omega) ?_
  calc (8 * d + 64 * d * c + 2) ^ 2 ≤ 64 * d * (c * (8 * d + 64 * d * c + 2 + 1)) := h
    _ = 64 * d * c * (8 * d + 64 * d * c + 2 + 1) := by ring

end Cslib.Turing.SingleTapeTM
