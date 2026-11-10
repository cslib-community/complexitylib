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
`2 ^ m` hard inputs `palWord r x = x ++ falseʳ ++ reverse x` for bit strings `x` of length `m`.
All of them are palindromes. If two distinct hard inputs had the same crossing sequence at a
boundary inside the middle block, the cut-and-paste lemma would make the machine accept a
non-palindrome. So at every such boundary the `2 ^ m` crossing sequences are distinct. Fewer than
half of them can be shorter than about `m / log |Q|`. Since the crossing sequences of one run have
total length at most its running time, some hard input needs time proportional to
`r · m / log |Q|`.

The lower bound is stated for deciders that answer under the head (`DecidesByHeadInTime`): the
machine halts within the time bound, and the cell under the head then holds `yes` exactly on
palindromes. The rest of the final tape is unconstrained. Deciders in cslib's canonical output
form (`DecidesPalindromesInTime`) are a special case.

## Main definitions

* `Cslib.Turing.SingleTapeTM.DecidesPalindromesInTime tm a b yes T`: on every word over the
  letters `a, b`, `tm` halts within `T n` steps and its output begins with `yes` exactly when
  the input is a palindrome. Halting goes through `OutputsWithinTime`, so the final tape holds
  only the output, with the head on its first cell.
* `Cslib.Turing.SingleTapeTM.bitSymbol a b`: the letter map writing `false, true` as `a, b`.
* `Cslib.Turing.SingleTapeTM.palWord r x`: the hard inputs.

## Main results

* `Cslib.Turing.SingleTapeTM.DecidesPalindromesInTime.decidesByHeadInTime`: a canonical-output
  palindrome decider answers under the head, through `bitSymbol a b`.
* `Cslib.Turing.SingleTapeTM.crossings_palWord_injective`: distinct hard inputs have distinct
  crossing sequences at every boundary inside the middle block.
* `Cslib.Turing.SingleTapeTM.crossing_bound`: if `2 (|Q| + 2) ^ L ≤ 2 ^ m`, then
  `(r + 1) L ≤ 2 T (2m + r)`.
* `Cslib.Turing.SingleTapeTM.palindrome_lower_bound`: with `d = ⌈log₂ (|Q| + 2)⌉`, every
  `n ≥ 8d` satisfies `n² ≤ 64 d T(n)`.
* `Cslib.Turing.SingleTapeTM.not_decidesByHeadInTime_palindromes_linear` and
  `Cslib.Turing.SingleTapeTM.not_decidesPalindromesInTime_linear`: no single-tape machine
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
the tape; inputs containing them are unconstrained.

The output is in cslib's canonical form: `OutputsWithinTime w o` requires reaching
`haltCfg o`, so the machine must erase everything except `o` and halt with the head on the first
cell of `o`. This is narrower than acceptance by state; a decider that halts with other symbols
left on the tape is not covered. -/
@[expose] def DecidesPalindromesInTime (a b yes : Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ w : List Symbol, (∀ x ∈ w, x = a ∨ x = b) →
    ∃ o, tm.OutputsWithinTime w o (T w.length) ∧ (o.head? = some yes ↔ w.Palindrome)

/-- The letter map writing `false` as `a` and `true` as `b`. -/
@[expose] def bitSymbol (a b : Symbol) (β : Bool) : Symbol := if β then b else a

omit [Inhabited Symbol] [Fintype Symbol] in
lemma bitSymbol_injective {a b : Symbol} (hab : a ≠ b) : Function.Injective (bitSymbol a b) := by
  intro β γ h
  cases β <;> cases γ <;> simp_all [bitSymbol, eq_comm]

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma palindrome_map_iff {β γ : Type*} {f : β → γ} (hf : Function.Injective f)
    {w : List β} : (w.map f).Palindrome ↔ w.Palindrome := by
  rw [List.Palindrome.iff_reverse_eq, List.Palindrome.iff_reverse_eq, ← List.map_reverse]
  exact (List.map_injective_iff.mpr hf).eq_iff

/-- A palindrome decider in canonical output form also decides palindromes over `Bool`, written
with the letters `a ≠ b`, answering under the head. -/
theorem DecidesPalindromesInTime.decidesByHeadInTime {a b yes : Symbol} (hab : a ≠ b)
    {T : ℕ → ℕ} (h : tm.DecidesPalindromesInTime a b yes T) :
    tm.DecidesByHeadInTime (bitSymbol a b) {w : List Bool | w.Palindrome} yes T := by
  intro w
  obtain ⟨o, ho, hyes⟩ := h (w.map (bitSymbol a b)) fun x hx => by
    obtain ⟨β, -, rfl⟩ := List.mem_map.mp hx
    cases β <;> simp [bitSymbol]
  rw [List.length_map] at ho
  refine ⟨tm.haltCfg o, ho, rfl, ?_⟩
  simp only [haltCfg, BiTape.head_mk₁]
  rw [hyes]
  exact palindrome_map_iff (bitSymbol_injective hab)

/-- The hard inputs: `x`, a block of `r` copies of `false`, then `x` reversed. -/
@[expose] def palWord (r : ℕ) (x : List Bool) : List Bool :=
  x ++ List.replicate r false ++ x.reverse

@[simp] lemma length_palWord (r : ℕ) (x : List Bool) :
    (palWord r x).length = 2 * x.length + r := by
  simp [palWord]; omega

private lemma mixWord_split (x y : List Bool) {i r : ℕ} (hi : i ≤ r) :
    (x ++ List.replicate i false) ++ (List.replicate (r - i) false ++ y.reverse) =
      x ++ List.replicate r false ++ y.reverse := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc (List.replicate i false),
    ← List.replicate_add, Nat.add_sub_cancel' hi]

private lemma palindrome_mixWord_iff {r : ℕ} {x y : List Bool} (hxy : y.length = x.length) :
    (x ++ List.replicate r false ++ y.reverse).Palindrome ↔ y = x :=
  palindrome_append_replicate_append_reverse hxy

/-- Distinct hard inputs have distinct crossing sequences at every boundary inside the middle
block. -/
theorem crossings_palWord_injective {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes T) {r i : ℕ}
    (hi : i ≤ r) {x y : List Bool} (hxy : y.length = x.length)
    (h : (tm.absInit ((palWord r x).map ι)).crossings ((x.length + i : ℕ) : ℤ)
        (T (2 * x.length + r)) =
      (tm.absInit ((palWord r y).map ι)).crossings ((x.length + i : ℕ) : ℤ)
        (T (2 * x.length + r))) :
    x = y := by
  obtain ⟨hL, hLy⟩ := hdec.absRun (palWord r x)
  obtain ⟨hR, hRy⟩ := hdec.absRun (palWord r y)
  rw [length_palWord] at hL hLy
  rw [length_palWord, hxy] at hR hRy
  have hLp := hLy.mpr ((palindrome_mixWord_iff rfl).mpr rfl)
  have hRp := hRy.mpr ((palindrome_mixWord_iff rfl).mpr rfl)
  have hsx : (palWord r x).map ι = (x ++ List.replicate i false).map ι ++
      (List.replicate (r - i) false ++ x.reverse).map ι := by
    rw [← List.map_append, mixWord_split x x hi, palWord]
  have hsy : (palWord r y).map ι = (y ++ List.replicate i false).map ι ++
      (List.replicate (r - i) false ++ y.reverse).map ι := by
    rw [← List.map_append, mixWord_split y y hi, palWord]
  rw [hsx] at hL hLp h
  rw [hsy] at hR hRp h
  have hk₁ : ((x ++ List.replicate i false).map ι).length = x.length + i := by simp
  have hk₂ : ((y ++ List.replicate i false).map ι).length = x.length + i := by simp [hxy]
  have hu : (x ++ List.replicate i false).map ι = [] ↔
      (y ++ List.replicate i false).map ι = [] := by
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hk₁, hk₂]
  have hx : (tm.absInit ((x ++ List.replicate i false).map ι ++
        (List.replicate (r - i) false ++ x.reverse).map ι)).crossings
        ((x ++ List.replicate i false).map ι).length (T (2 * x.length + r)) =
      (tm.absInit ((y ++ List.replicate i false).map ι ++
        (List.replicate (r - i) false ++ y.reverse).map ι)).crossings
        ((y ++ List.replicate i false).map ι).length (T (2 * x.length + r)) := by
    rw [hk₁, hk₂]
    exact h
  obtain ⟨hC, -, -, hhead⟩ := cut_and_paste_run hu hL hR hx
  rw [← List.map_append, mixWord_split x y hi] at hC hhead
  obtain ⟨hM, hMy⟩ := hdec.absRun (x ++ List.replicate r false ++ y.reverse)
  have hMp : ((tm.absInit ((x ++ List.replicate r false ++ y.reverse).map ι)).run
      (T (x ++ List.replicate r false ++ y.reverse).length)).scanned = some yes := by
    rw [AbsCfg.run_eq_of_halted _ hM hC]
    rcases hhead with h' | h' <;> rw [h'] <;> assumption
  exact ((palindrome_mixWord_iff hxy).mp (hMy.mp hMp)).symm

/-- **Averaging step.** If at most half of the `2 ^ m` hard inputs can have a crossing sequence
shorter than `L` at any boundary, some hard input of length `2m + r` crosses the `r + 1` middle
boundaries at least `(r + 1) L / 2` times in total. -/
theorem crossing_bound {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes T) (m r L : ℕ)
    (hL : 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ m) :
    (r + 1) * L ≤ 2 * T (2 * m + r) := by
  classical
  set P := (Fintype.card (Option tm.State) + 1) ^ L
  set t := T (2 * m + r)
  let cs : ℕ → (Fin m → Bool) → List (Option tm.State) := fun i x =>
    (tm.absInit ((palWord r (List.ofFn x)).map ι)).crossings ((m + i : ℕ) : ℤ) t
  have hinj (i : ℕ) (hi : i ≤ r) : Set.InjOn (cs i) (Finset.univ : Finset (Fin m → Bool)) := by
    intro x _ y _ hxy
    have h := crossings_palWord_injective hdec hi
      (x := List.ofFn x) (y := List.ofFn y) (by simp) (by simpa [cs, t] using hxy)
    exact List.ofFn_injective h
  have hgood (i : ℕ) (hi : i ≤ r) : (2 ^ m - P) * L ≤ ∑ x, (cs i x).length := by
    have h := card_sub_pow_mul_le_sum_length (hinj i hi) L
    rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at h
  have hupper (x : Fin m → Bool) : ∑ i ∈ Finset.range (r + 1), (cs i x).length ≤ t := by
    have h := AbsCfg.sum_length_crossings_le
      ((Finset.range (r + 1)).image fun i : ℕ => ((m + i : ℕ) : ℤ))
      (tm.absInit ((palWord r (List.ofFn x)).map ι)) t
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

/-- **Quadratic lower bound for palindromes** (via Hennie's crossing sequences). Let
`d = ⌈log₂ (|Q| + 2)⌉` where `Q` is the state set. If a single-tape machine decides the
palindromes over `Bool` within time `T`, answering under the head (`DecidesByHeadInTime`, with any
letter map `ι`), then `n ^ 2 ≤ 64 d T(n)` for every `n ≥ 8 d`. Canonical-output deciders are
covered through `DecidesPalindromesInTime.decidesByHeadInTime`. -/
theorem palindrome_lower_bound {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes T) {n : ℕ}
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
  have h1 := crossing_bound hdec m r L hL
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

/-- No single-tape machine decides the palindromes over `Bool` in linear time, even answering
under the head. -/
theorem not_decidesByHeadInTime_palindromes_linear (ι : Bool → Symbol) (yes : Symbol) (c : ℕ) :
    ¬ tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes fun n => c * (n + 1) := by
  intro hdec
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.clog 2 (Fintype.card tm.State + 2) := ⟨_, rfl⟩
  have hd : 0 < d := hd_def ▸ Nat.clog_pos one_lt_two (by omega)
  have h := palindrome_lower_bound hdec (n := 8 * d + 64 * d * c + 2) (by omega)
  rw [← hd_def] at h
  have key : ∀ M N : ℕ, M + 2 ≤ N → N ^ 2 ≤ M * (N + 1) → False := fun M N h1 h2 => by
    have := Nat.mul_le_mul_right N h1
    nlinarith
  refine key (64 * d * c) (8 * d + 64 * d * c + 2) (by omega) ?_
  calc (8 * d + 64 * d * c + 2) ^ 2 ≤ 64 * d * (c * (8 * d + 64 * d * c + 2 + 1)) := h
    _ = 64 * d * c * (8 * d + 64 * d * c + 2 + 1) := by ring

/-- No single-tape machine decides palindromes over two letters in linear time. -/
theorem not_decidesPalindromesInTime_linear {a b yes : Symbol} (hab : a ≠ b) (c : ℕ) :
    ¬ DecidesPalindromesInTime tm a b yes fun n => c * (n + 1) := fun hdec =>
  not_decidesByHeadInTime_palindromes_linear _ _ c (hdec.decidesByHeadInTime hab)

end Cslib.Turing.SingleTapeTM
