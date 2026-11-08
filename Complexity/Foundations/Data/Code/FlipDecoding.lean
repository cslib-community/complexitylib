/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.ExpanderCode
public import Complexity.Foundations.Data.BitString.Flip
public import Cslib.Foundations.Relation.RelatesInSteps
import Complexity.Foundations.Data.BitString.Hamming

/-!
# Flip decoding of expander codes

The *flip decoder* of Sipser and Spielman [SipserSpielman1996] corrects errors in the expander code
of a bipartite graph `G` (`Cslib.BitString.ExpanderCode.code`) by local moves. While some variable
has more violated than satisfied checks among its neighbours
(`Cslib.BitString.ExpanderCode.IsFlippable`), flip it. This is the algorithm of
[GuruswamiSharma2010, §1.1], and the procedure GEN-FLIP of [GuruswamiRudraSudan2025, §18.2.2,
Algorithm 18.2.1] with exact check bits.

* **Each flip removes a violated check** (`Cslib.BitString.ExpanderCode.card_unsat_flipOn_lt`):
  flipping variable `i` exchanges its violated and satisfied neighbouring checks. So a run of `t`
  flips from `x` has `t ≤ #unsat(x) ≤ c · d(x, w)`
  (`Cslib.BitString.ExpanderCode.add_card_unsat_le_of_relatesInSteps`), and at most the number
  `m` of checks.
* **Progress** [GuruswamiSharma2010, Lemma 5] (`Cslib.BitString.ExpanderCode.exists_isFlippable`):
  if left degrees are at most `c`, sets of at most `k` variables expand by `α` with `3 c < 4 α`, and
  `y ≠ w` is within distance `k` of a codeword `w`, some variable is flippable. The errors have
  more than `c |E| / 2` unique neighbours, all violated, so some error sees more than `c / 2`
  violated checks.
* **Invariant** [GuruswamiSharma2010, Lemma 6]
  (`Cslib.BitString.ExpanderCode.hammingDist_lt_and_card_unsat_le`): if
  `c · d(x, w) < (2 α - c) k`, every word reached by flips stays at distance `< k` from `w`. At
  distance exactly `k` the unique neighbours of the errors would give at least `(2 α - c) k`
  violated checks, more than the `c · d(x, w)` we started with.
* **Correctness** (`Cslib.BitString.ExpanderCode.decode_eq`): the deterministic decoder
  `Cslib.BitString.ExpanderCode.decode`, run with any pivot rule that returns a flippable variable
  whenever one exists (`Cslib.BitString.ExpanderCode.IsFlipRule`), recovers `w` within
  `#unsat(x)` rounds. In particular, when `3 c < 4 α` and `0 < k`, it corrects every error
  pattern of weight at most `k / 2` within `c · d(x, w)` rounds
  (`Cslib.BitString.ExpanderCode.decode_eq_of_two_mul_le`).

For a lossless expander, `α = c (1 - ε)` with `ε < 1 / 4` and `k = γ n`, the hypothesis
`c · d(x, w) < (2 α - c) k` reads `d(x, w) < (1 - 2 ε) γ n`, as in [GuruswamiSharma2010, §1.1.1].
The source assumes `c`-left-regularity; we only need left degrees at most `c`. The number of rounds
is counted abstractly: we do not formalize the `O(n)` data-structure implementation of
[GuruswamiSharma2010, §1.1.2] on a machine model.

## Main definitions

* `Cslib.BitString.ExpanderCode.IsFlippable`: a variable with more violated than satisfied checks.
* `Cslib.BitString.ExpanderCode.FlipStep`: one move of the flip decoder.
* `Cslib.BitString.ExpanderCode.IsFlipRule`, `Cslib.BitString.ExpanderCode.firstFlippable`: pivot
  rules.
* `Cslib.BitString.ExpanderCode.decode`: the flip decoder with a bounded number of rounds.

## Main results

* `Cslib.BitString.flipOn_eq_add`, `Cslib.BitString.flipOn_singleton_eq_add_single`: flips as
  additions.
* `Cslib.BitString.ExpanderCode.card_unsat_flipOn_lt`: flips decrease the number of violated
  checks.
* `Cslib.BitString.ExpanderCode.add_card_unsat_le_of_relatesInSteps`: the number of flips.
* `Cslib.BitString.ExpanderCode.exists_isFlippable`: progress.
* `Cslib.BitString.ExpanderCode.hammingDist_lt_and_card_unsat_le`: flips stay close to the
  codeword.
* `Cslib.BitString.ExpanderCode.eq_of_flip_stuck`: a word with no flippable variable reached from
  `x` is the codeword.
* `Cslib.BitString.ExpanderCode.decode_eq`: correctness of flip decoding.
* `Cslib.BitString.ExpanderCode.decode_eq_of_two_mul_le`: flip decoding corrects up to half the
  expansion radius.

## References

* [M. Sipser, D. A. Spielman, *Expander codes*][SipserSpielman1996]
* [V. Guruswami, A. Sharma, *Expander codes and their decoding*][GuruswamiSharma2010], §1.1
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2025], §18.2
-/

@[expose] public section

namespace Cslib.BitString.ExpanderCode

open Finset Matrix Cslib.Bipartite

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {G : ι → κ → Prop} [∀ i j, Decidable (G i j)]

variable (G) in
/-- Variable `i` is *flippable* in `x`: it has more violated than satisfied neighbouring checks. -/
def IsFlippable (x : ι → Bool) (i : ι) : Prop :=
  #{j | G i j ∧ syndrome G x j = false} < #{j | G i j ∧ syndrome G x j = true}

instance (x : ι → Bool) (i : ι) : Decidable (IsFlippable G x i) :=
  inferInstanceAs (Decidable (_ < _))

/-- **Progress** [GuruswamiSharma2010, Lemma 5]. If left degrees are at most `c`, sets of at most
`k` variables expand by `α` with `3 c < 4 α`, and `y ≠ w` is within distance `k` of a codeword
`w`, some variable is flippable in `y`. -/
theorem exists_isFlippable {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c)
    (hE : IsVertexExpander G k α) (hα : 3 * c < 4 * α) {y w : ι → Bool} (hw : w ∈ code G)
    (hyw : y ≠ w) (hk : hammingDist y w ≤ k) : ∃ i, IsFlippable G y i := by
  set E : Finset ι := {i | y i ≠ w i}
  set U := uniqueNeighbors G E
  have hE0 : 0 < #E := hammingDist_pos.2 hyw
  have hU : (2 * α - c) * #E ≤ #U := hE.le_card_uniqueNeighbors hG hk
  have hcU : c * #E < 2 * #U := by
    have hE0' : (0 : ℝ) < #E := by exact_mod_cast hE0
    have : (c : ℝ) * #E < 2 * #U := by nlinarith
    exact_mod_cast this
  have hsum : ∑ i ∈ E, #(U.bipartiteAbove G i) = #U := by
    rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc ∑ j ∈ U, #(E.bipartiteBelow G j) = ∑ j ∈ U, 1 :=
          sum_congr rfl fun j hj => mem_uniqueNeighbors.1 hj
      _ = #U := by rw [sum_const, smul_eq_mul, mul_one]
  have hlt : ∑ i ∈ E, c < ∑ i ∈ E, 2 * #(U.bipartiteAbove G i) := by
    rw [← mul_sum, hsum, sum_const, smul_eq_mul, mul_comm]
    exact hcU
  obtain ⟨i, -, hi⟩ := exists_lt_of_sum_lt hlt
  refine ⟨i, ?_⟩
  have hUi : #(U.bipartiteAbove G i) ≤ #{j | G i j ∧ syndrome G y j = true} := by
    refine card_le_card fun j hj => ?_
    rw [mem_bipartiteAbove] at hj
    have := uniqueNeighbors_subset_unsat hw hj.1
    simp only [unsat, mem_filter, mem_univ, true_and] at this ⊢
    exact ⟨hj.2, this⟩
  have hdeg : #{j | G i j ∧ syndrome G y j = false} + #{j | G i j ∧ syndrome G y j = true} ≤ c := by
    refine le_trans (le_of_eq ?_) (hG i)
    rw [← card_filter_add_card_filter_not (s := univ.bipartiteAbove G i)
      (fun j => syndrome G y j = false)]
    congr 2 <;> ext j <;> simp [mem_bipartiteAbove]
  unfold IsFlippable
  omega

variable (G) in
/-- A *pivot rule* for the flip decoder: it returns only flippable variables, and returns none only
when no variable is flippable. -/
def IsFlipRule (pick : (ι → Bool) → Option ι) : Prop :=
  ∀ x, (∀ i, pick x = some i → IsFlippable G x i) ∧ (pick x = none → ∀ i, ¬ IsFlippable G x i)

variable (G) in
/-- The pivot rule that returns the first flippable variable of a list. -/
def firstFlippable (l : List ι) (x : ι → Bool) : Option ι :=
  l.find? fun i => decide (IsFlippable G x i)

/-- Taking the first flippable variable of a list of all variables is a pivot rule. -/
theorem isFlipRule_firstFlippable {l : List ι} (hl : ∀ i, i ∈ l) :
    IsFlipRule G (firstFlippable G l) := by
  intro x
  refine ⟨fun i hi => ?_, fun hn i hi => ?_⟩
  · simpa using List.find?_some hi
  · rw [firstFlippable, List.find?_eq_none] at hn
    exact hn i (hl i) (by simpa using hi)

variable [DecidableEq ι]

variable (G) in
/-- One move of the flip decoder: flip a flippable variable. -/
def FlipStep (x y : ι → Bool) : Prop :=
  ∃ i, IsFlippable G x i ∧ y = flipOn {i} x

omit [Fintype ι] in
/-- Flipping the bits at `T` adds the indicator of `T`. -/
theorem _root_.Cslib.BitString.flipOn_eq_add (T : Finset ι) (x : ι → Bool) :
    flipOn T x = x + fun l => decide (l ∈ T) := by
  funext l
  rw [flipOn_apply, Pi.add_apply]
  by_cases h : l ∈ T <;> simp [h, Bool.add_eq_xor]

omit [Fintype ι] in
/-- Flipping one bit adds the corresponding unit vector. -/
theorem _root_.Cslib.BitString.flipOn_singleton_eq_add_single (x : ι → Bool) (i : ι) :
    flipOn {i} x = x + Pi.single i true := by
  rw [flipOn_eq_add]
  congr 1
  funext l
  by_cases h : l = i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]
    exact decide_eq_false (by simpa using h)

omit [Fintype κ] in
/-- Flipping variable `i` toggles exactly the checks adjacent to `i`. -/
theorem syndrome_flipOn (x : ι → Bool) (i : ι) (j : κ) :
    syndrome G (flipOn {i} x) j = (syndrome G x j ^^ decide (G i j)) := by
  rw [flipOn_singleton_eq_add_single, syndrome_add, Pi.add_apply]
  congr 1
  rw [syndrome, show (Pi.single i true : ι → Bool) = Pi.single i 1 from rfl, mulVec_single_one]
  rfl

/-- Flipping variable `i` exchanges its violated and satisfied neighbouring checks. -/
theorem card_unsat_flipOn_add (x : ι → Bool) (i : ι) :
    #(unsat G (flipOn {i} x)) + #{j | G i j ∧ syndrome G x j = true} =
      #(unsat G x) + #{j | G i j ∧ syndrome G x j = false} := by
  have key : ∀ y : ι → Bool, #(unsat G y) =
      #{j | ¬ G i j ∧ syndrome G y j = true} + #{j | G i j ∧ syndrome G y j = true} := by
    intro y
    rw [unsat, ← card_filter_add_card_filter_not (s := filter _ univ) (G i ·), filter_filter,
      filter_filter]
    rw [add_comm]
    congr 2 <;> ext j <;> simp only [mem_filter, mem_univ, true_and] <;> tauto
  rw [key x, key (flipOn {i} x)]
  have h1 : (filter (fun j => ¬ G i j ∧ syndrome G (flipOn {i} x) j = true) univ) =
      filter (fun j => ¬ G i j ∧ syndrome G x j = true) univ := by
    ext j
    simp only [mem_filter, mem_univ, true_and, syndrome_flipOn]
    by_cases h : G i j <;> simp [h]
  have h2 : (filter (fun j => G i j ∧ syndrome G (flipOn {i} x) j = true) univ) =
      filter (fun j => G i j ∧ syndrome G x j = false) univ := by
    ext j
    simp only [mem_filter, mem_univ, true_and, syndrome_flipOn]
    by_cases h : G i j <;> simp [h]
  rw [h1, h2]
  omega

/-- Flipping a flippable variable decreases the number of violated checks. -/
theorem card_unsat_flipOn_lt {x : ι → Bool} {i : ι} (h : IsFlippable G x i) :
    #(unsat G (flipOn {i} x)) < #(unsat G x) := by
  have := card_unsat_flipOn_add (G := G) x i
  unfold IsFlippable at h
  omega

/-- A move of the flip decoder decreases the number of violated checks. -/
theorem FlipStep.card_unsat_lt {x y : ι → Bool} (h : FlipStep G x y) :
    #(unsat G y) < #(unsat G x) := by
  obtain ⟨i, hi, rfl⟩ := h
  exact card_unsat_flipOn_lt hi

/-- **Number of flips**: a run of `t` moves from `x` to `y` has `t + #unsat(y) ≤ #unsat(x)`. In
particular the flip decoder stops after at most `#unsat(x) ≤ c · d(x, w)` moves
(`card_unsat_le`), and at most the number of checks. -/
theorem add_card_unsat_le_of_relatesInSteps {x y : ι → Bool} {t : ℕ}
    (h : Relation.RelatesInSteps (FlipStep G) x y t) : t + #(unsat G y) ≤ #(unsat G x) := by
  induction h with
  | refl => simp
  | tail _ _ _ _ hstep ih =>
    have := hstep.card_unsat_lt
    omega

/-- **Invariant** [GuruswamiSharma2010, Lemma 6]. If `c · d(x, w) < (2 α - c) k`, every word
reached from `x` by moves of the flip decoder is at distance less than `k` from the codeword `w`
and violates at most as many checks as `x`. -/
theorem hammingDist_lt_and_card_unsat_le {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c)
    (hE : IsVertexExpander G k α) {x w : ι → Bool} (hw : w ∈ code G)
    (hx : c * hammingDist x w < (2 * α - c) * k)
    {y : ι → Bool} (hy : Relation.ReflTransGen (FlipStep G) x y) :
    hammingDist y w < k ∧ #(unsat G y) ≤ #(unsat G x) := by
  induction hy with
  | refl =>
    refine ⟨?_, le_rfl⟩
    rcases Nat.eq_zero_or_pos (hammingDist x w) with h0 | hpos
    · rw [h0] at hx ⊢
      by_contra hk
      push Not at hk
      have : k = 0 := by omega
      subst this
      simp at hx
    · by_contra hk
      push Not at hk
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        have : (0 : ℝ) ≤ c * hammingDist x w := by positivity
        simp only [Nat.cast_zero, mul_zero] at hx
        linarith
      obtain ⟨i, hi⟩ := card_pos.1 hpos
      have h1 := hE {i} (by rw [card_singleton]; omega)
      have h2 := card_neighbors_le hG {i}
      rw [card_singleton, Nat.cast_one, mul_one] at h1
      rw [card_singleton, mul_one] at h2
      have hαc : α ≤ c := h1.trans (by exact_mod_cast h2)
      have hk' : (k : ℝ) ≤ hammingDist x w := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
  | tail _ hstep ih =>
    rename_i y z _
    obtain ⟨ihd, ihu⟩ := ih
    have hz : #(unsat G z) ≤ #(unsat G x) := (hstep.card_unsat_lt).le.trans ihu
    refine ⟨?_, hz⟩
    obtain ⟨i, -, rfl⟩ := hstep
    have hd := hammingDist_flip_le_add_one y w i
    rcases Nat.lt_or_ge (hammingDist (flipOn {i} y) w) k with h | h
    · exact h
    · exfalso
      have hdk : hammingDist (flipOn {i} y) w = k := by omega
      have h1 := hE.le_card_uniqueNeighbors hG hdk.le
      have h2 := card_le_card (uniqueNeighbors_subset_unsat (y := flipOn {i} y) hw)
      have h3 := card_unsat_le hG (y := x) hw
      have h4 : (#(uniqueNeighbors G {l | flipOn {i} y l ≠ w l}) : ℝ) ≤ c * hammingDist x w := by
        exact_mod_cast h2.trans (hz.trans h3)
      change (2 * α - c) * (hammingDist (flipOn {i} y) w : ℝ) ≤ _ at h1
      rw [hdk] at h1
      linarith

/-- **Correctness of flip decoding** [GuruswamiSharma2010, §1.1.1]. Under the hypotheses of
`exists_isFlippable` and `hammingDist_lt_and_card_unsat_le`, a word reached from `x` in which no
variable is flippable is the codeword `w`. -/
theorem eq_of_flip_stuck {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c)
    (hE : IsVertexExpander G k α) (hα : 3 * c < 4 * α) {x w : ι → Bool} (hw : w ∈ code G)
    (hx : c * hammingDist x w < (2 * α - c) * k) {y : ι → Bool}
    (hy : Relation.ReflTransGen (FlipStep G) x y) (hstuck : ∀ i, ¬ IsFlippable G y i) :
    y = w := by
  by_contra hyw
  obtain ⟨i, hi⟩ :=
    exists_isFlippable hG hE hα hw hyw (hammingDist_lt_and_card_unsat_le hG hE hw hx hy).1.le
  exact hstuck i hi

/-- The flip decoder with pivot rule `pick`, run for at most `n` rounds: it flips the variable
returned by `pick` and stops when `pick` returns none. -/
def decode (pick : (ι → Bool) → Option ι) : ℕ → (ι → Bool) → ι → Bool
  | 0, x => x
  | n + 1, x =>
    match pick x with
    | none => x
    | some i => decode pick n (flipOn {i} x)

/-- `decode_eq` for every word reached from `x`. -/
theorem decode_eq_of_reflTransGen {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c)
    (hE : IsVertexExpander G k α) (hα : 3 * c < 4 * α) {x w : ι → Bool} (hw : w ∈ code G)
    (hx : c * hammingDist x w < (2 * α - c) * k) {pick : (ι → Bool) → Option ι}
    (hpick : IsFlipRule G pick) (n : ℕ) :
    ∀ y, Relation.ReflTransGen (FlipStep G) x y → #(unsat G y) ≤ n → decode pick n y = w := by
  induction n with
  | zero =>
    intro y hy hn
    rw [decode]
    refine eq_of_flip_stuck hG hE hα hw hx hy fun i hi => ?_
    have := card_unsat_flipOn_lt hi
    omega
  | succ n ih =>
    intro y hy hn
    rw [decode]
    rcases hp : pick y with _ | i
    · exact eq_of_flip_stuck hG hE hα hw hx hy ((hpick y).2 hp)
    · have hi := (hpick y).1 i hp
      have hstep : FlipStep G y (flipOn {i} y) := ⟨i, hi, rfl⟩
      exact ih _ (hy.tail hstep) (by have := card_unsat_flipOn_lt hi; omega)

/-- **Flip decoding** [SipserSpielman1996] [GuruswamiSharma2010, §1.1]. If left degrees are at
most `c`, sets of at most `k` variables expand by `α` with `3 c < 4 α`, `w` is a codeword and
`c · d(x, w) < (2 α - c) k`, then the flip decoder with any pivot rule, run for any number
`n ≥ #unsat(x)` of rounds, returns `w`. Since `#unsat(x) ≤ c · d(x, w)` (`card_unsat_le`),
`n = c · d(x, w)` rounds suffice. -/
theorem decode_eq {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c)
    (hE : IsVertexExpander G k α) (hα : 3 * c < 4 * α) {x w : ι → Bool} (hw : w ∈ code G)
    (hx : c * hammingDist x w < (2 * α - c) * k) {pick : (ι → Bool) → Option ι}
    (hpick : IsFlipRule G pick) {n : ℕ} (hn : #(unsat G x) ≤ n) : decode pick n x = w :=
  decode_eq_of_reflTransGen hG hE hα hw hx hpick n x .refl hn

private theorem mul_lt_of_two_mul_le {c k : ℕ} {α : ℝ} (hα : 3 * c < 4 * α) (hk : 0 < k)
    {e : ℕ} (he : 2 * e ≤ k) : c * e < (2 * α - c) * k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have he' : (2 * e : ℝ) ≤ k := by exact_mod_cast he
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith

/-- **Flip decoding up to half the expansion radius.** If left degrees are at most `c`, sets of at
most `k > 0` variables expand by `α` with `3 c < 4 α` (`ε < 1 / 4` for `α = c (1 - ε)`), and
`x` differs from the codeword `w` in at most `k / 2` positions, then the flip decoder with any
pivot rule recovers `w` within `c · d(x, w)` rounds. -/
theorem decode_eq_of_two_mul_le {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c)
    (hE : IsVertexExpander G k α) (hα : 3 * c < 4 * α) (hk : 0 < k) {x w : ι → Bool}
    (hw : w ∈ code G) (hx : 2 * hammingDist x w ≤ k) {pick : (ι → Bool) → Option ι}
    (hpick : IsFlipRule G pick) : decode pick (c * hammingDist x w) x = w :=
  decode_eq hG hE hα hw (mul_lt_of_two_mul_le hα hk hx) hpick (card_unsat_le hG hw)

end Cslib.BitString.ExpanderCode
