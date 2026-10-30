/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.Randomized
public import Complexity.Foundations.LinearAlgebra.Matrix.CoinStep

/-!
# The configuration matrix of a fair-coin machine

A fair-coin machine moves each running view (`Turing.FiniteCfg`, the configuration with its work
tapes stored relative to their heads and its output summarized) to one of two views, selected by
the coin (`Turing.MultiTapePTM.viewCoinStep`); a halted view stays put. On a finite set `V` of
views closed under these steps, this gives two matrices indexed by `V`:

* the *configuration matrix* `Turing.MultiTapePTM.configMatrix`, whose entry `(x, y)` counts the
  coins moving `x` to `y`, so that half of it is the stochastic matrix of the run, with halted
  views absorbing;
* the *live configuration matrix* `Turing.MultiTapePTM.liveConfigMatrix`, the same rows at
  running views and zero rows at halted views, so that half of it is substochastic.

With `e` the indicator of the accepting halted views (`Turing.FiniteCfg.acceptVec`), the number of
accepting coin strings of length `t` is the entry at the initial view of `N ^ t *ᵥ e`
(`Turing.MultiTapePTM.acceptCoins_eq_configMatrix_pow_mulVec`), so the acceptance probability is
`((N / 2) ^ t *ᵥ e)(start)`. Splitting the coin strings by the time they halt gives the
substochastic form `∑ t ≤ T, ((S / 2) ^ t *ᵥ e)(start)`
(`Turing.MultiTapePTM.acceptCoins_div_eq_sum_liveConfigMatrix`). When every view of `V` is
reachable and every branch halts within `T` steps, `S / 2` is nilpotent, and the acceptance
probability is `((1 - S / 2)⁻¹ *ᵥ e)(start)`
(`Turing.MultiTapePTM.acceptCoins_div_eq_inv_mulVec`).

The reachable views form such a set (`Turing.MultiTapePTM.exists_finset_reachable`), with at most
`2 ^ (2 * coreLengthBound k State n s + 1)` elements under a space bound `s`, polynomially many
under a logarithmic one. So a `BPL` language is decided by the entry at the initial view of
`(1 - S / 2)⁻¹ *ᵥ e` for a polynomial-size matrix `S`
(`Cslib.Complexity.exists_configMatrix_of_mem_BPL`). This is the Markov chain of a probabilistic
machine on its configurations [Gill][Gill1977]. Borodin, Cook and Pippenger compute its powers
and inverse in parallel [Borodin, Cook and Pippenger][BorodinCookPippenger1983], which gives
`BPSPACE(S) ⊆ DSPACE(S²)` [Hoza, Section 4.3][Hoza2022]; the inverse of `1 - W` as the sum
`W⁰ + W¹ + …` of transition-matrix powers is the picture of [Hoza, Section 3.2][Hoza2022].
Exact evaluation of the polynomial-size matrix also gives `BPL ⊆ P`. None of these algorithms is
formalized here.

The matrices are indexed by an arbitrary closed set of views rather than a set of
configurations of bounded size, and have no time layers: the model of `Cslib.Complexity.BPL`
requires every branch to halt, which already makes the live matrix nilpotent on the reachable
views. The form `N ^ t` with absorbing halted views is the one repeated squaring computes; the
form `(1 - S / 2)⁻¹` with a nilpotent substochastic matrix is the one of matrix inversion.

## Main definitions

* `Turing.MultiTapePTM.viewCoinStep`: the view reached under one coin.
* `Turing.FiniteCfg.acceptVec`: the indicator of the accepting halted views.
* `Turing.MultiTapePTM.configMatrix`, `Turing.MultiTapePTM.liveConfigMatrix`: the configuration
  matrix and its rows at running views.

## Main results

* `Turing.MultiTapePTM.viewRep_foldl_viewCoinStep`: coin steps of views follow coin replays.
* `Turing.MultiTapePTM.reflTransGen_viewStep_toNTM_iff`: the reachable views are those reached by
  coin strings.
* `Turing.MultiTapePTM.acceptCoins_eq_configMatrix_pow_mulVec`: accepting coin strings are an
  entry of a power of the configuration matrix.
* `Turing.MultiTapePTM.acceptCoins_div_eq_configMatrix_pow_mulVec`: the acceptance probability
  is an entry of a power of the stochastic matrix.
* `Turing.MultiTapePTM.acceptCoins_div_eq_sum_liveConfigMatrix`: the substochastic form.
* `Turing.MultiTapePTM.liveConfigMatrix_pow_eq_zero`: under a halting time, the live matrix is
  nilpotent on reachable views.
* `Turing.MultiTapePTM.acceptCoins_div_eq_inv_mulVec`: the acceptance probability is an entry of
  `(1 - S / 2)⁻¹ *ᵥ e`.
* `Turing.MultiTapePTM.exists_finset_reachable`: the reachable views form a small closed set.
* `Cslib.Complexity.exists_configMatrix_of_mem_BPL`: `BPL` through polynomial-size configuration
  matrices.

## References

* [A. Borodin, S. Cook, N. Pippenger, *Parallel computation for well-endowed rings and
  space-bounded probabilistic machines*][BorodinCookPippenger1983]
* [W. Hoza, *Recent progress on derandomizing space-bounded computation*][Hoza2022]
* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
-/

@[expose] public section

open Cslib.Turing

namespace Turing

open scoped Classical in
/-- The indicator of the accepting halted views in a set `V` of views: `1` at the halted views
with output `[true]`, `0` elsewhere. -/
noncomputable def FiniteCfg.acceptVec {k : ℕ} {State : Type} (R : Type*) [Zero R] [One R]
    (V : Finset (FiniteCfg k Bool State)) : V → R :=
  fun v => if (v : FiniteCfg k Bool State).state = none ∧
    (v : FiniteCfg k Bool State).output = [true] then 1 else 0

namespace MultiTapePTM

open MultiTapeMachine Matrix

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)

/-- **The view reached under one coin**: a halted view stays put; a running view takes the action
selected by the coin, and its output is summarized. -/
noncomputable def viewCoinStep (finite : FiniteCfg k Bool State) (bit : Bool) :
    FiniteCfg k Bool State :=
  match finite.state with
  | none => finite
  | some state => (finite.step ((machine.withCoin bit).toTM.tr state finite.inputSymbol
      finite.workTapeSymbols)).summarizeOutput

open scoped Classical in
/-- **The configuration matrix** on a set `V` of views: the entry at `(x, y)` counts the coins
that move `x` to `y`. Half of it is the stochastic matrix of the run, with halted views
absorbing. -/
noncomputable def configMatrix (R : Type*) [CommSemiring R] (V : Finset (FiniteCfg k Bool State)) :
    Matrix V V R :=
  Matrix.coinStepMatrix machine.viewCoinStep V

open scoped Classical in
/-- **The live configuration matrix**: the rows of `Turing.MultiTapePTM.configMatrix` at running
views, and zero rows at halted views. Half of it is substochastic. -/
noncomputable def liveConfigMatrix (R : Type*) [CommSemiring R]
    (V : Finset (FiniteCfg k Bool State)) : Matrix V V R :=
  Matrix.liveCoinStepMatrix machine.viewCoinStep V fun finite => finite.state ≠ none

variable {machine}

/-- A halted view stays put. -/
theorem viewCoinStep_of_halted {finite : FiniteCfg k Bool State} (h : finite.state = none)
    (bit : Bool) : machine.viewCoinStep finite bit = finite := by
  simp only [viewCoinStep, h]

/-- **Coin steps of views follow coin steps of configurations.** -/
theorem viewRep_viewCoinStep {input : List Bool} {finite : FiniteCfg k Bool State}
    {cfg : Cfg k Bool State input} (h : MultiTapeNTM.ViewRep finite cfg) (bit : Bool) :
    MultiTapeNTM.ViewRep (machine.viewCoinStep finite bit)
      ((machine.withCoin bit).toTM.step cfg) := by
  rcases hs : cfg.state with _ | state
  · rw [MultiTapeTM.step_of_halt hs, viewCoinStep_of_halted (h.state.trans hs)]
    exact h
  · obtain ⟨hin, hwork⟩ := h.symbols
    rw [MultiTapeTM.step_of_state hs]
    simp only [MultiTapePTM.viewCoinStep, h.state.trans hs, hin, hwork]
    exact h.step _

/-- **Coin strings replay on views as on configurations.** -/
theorem viewRep_foldl_viewCoinStep {input : List Bool} {finite : FiniteCfg k Bool State}
    {cfg : Cfg k Bool State input} (h : MultiTapeNTM.ViewRep finite cfg) (coins : List Bool) :
    MultiTapeNTM.ViewRep (coins.foldl machine.viewCoinStep finite)
      (machine.stepCoins coins cfg) := by
  induction coins generalizing finite cfg with
  | nil => exact h
  | cons bit coins ih => exact ih (viewRep_viewCoinStep h bit)

/-- The steps of the views of the nondeterministic view are the coin steps. -/
theorem viewStep_toNTM_iff {finite next : FiniteCfg k Bool State} :
    machine.toNTM.ViewStep finite next ↔ ∃ bit, machine.viewCoinStep finite bit = next := by
  rcases hs : finite.state with _ | state
  · simp only [MultiTapeNTM.ViewStep, hs, viewCoinStep_of_halted hs, exists_const]
    exact eq_comm
  · simp only [MultiTapeNTM.ViewStep, hs, viewCoinStep, tr_toNTM_iff, MultiTapeTM.tr_iff]
    constructor
    · rintro ⟨action, ⟨bit, rfl⟩, rfl⟩
      exact ⟨bit, rfl⟩
    · rintro ⟨bit, rfl⟩
      exact ⟨_, ⟨bit, rfl⟩, rfl⟩

/-- **The reachable views are those reached by coin strings.** -/
theorem reflTransGen_viewStep_toNTM_iff {finite next : FiniteCfg k Bool State} :
    Relation.ReflTransGen machine.toNTM.ViewStep finite next ↔
      ∃ coins : List Bool, coins.foldl machine.viewCoinStep finite = next := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hstep ih =>
      obtain ⟨coins, rfl⟩ := ih
      obtain ⟨bit, rfl⟩ := viewStep_toNTM_iff.mp hstep
      exact ⟨coins ++ [bit], by simp⟩
  · rintro ⟨coins, rfl⟩
    induction coins using List.reverseRecOn with
    | nil => exact .refl
    | append_singleton coins bit ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact ih.tail (viewStep_toNTM_iff.mpr ⟨bit, rfl⟩)

/-- The accepting coin strings are those whose replay on views ends in an accepting halted
view. -/
private theorem acceptCoins_eq_card_views (input : List Bool) (t : ℕ) :
    machine.acceptCoins input t = (Finset.univ.filter fun w : Fin t → Bool =>
      ((List.ofFn w).foldl machine.viewCoinStep (machine.toNTM.initView input)).state = none ∧
        ((List.ofFn w).foldl machine.viewCoinStep (machine.toNTM.initView input)).output =
          [true]).card := by
  classical
  unfold acceptCoins
  congr 1
  refine Finset.filter_congr fun w _ => ?_
  have h := viewRep_foldl_viewCoinStep (machine := machine)
    (MultiTapeNTM.viewRep_init (ntm := machine.toNTM) input) (List.ofFn w)
  rw [h.state, h.output, MultiTapeNTM.outputClass_eq_true_iff]

open scoped Classical in
/-- **Accepting coin strings are an entry of a power of the configuration matrix**: on a set `V`
of views that contains the initial view and is closed under coin steps, the number of accepting
coin strings of length `t` is the entry at the initial view of `N ^ t *ᵥ e`. -/
theorem acceptCoins_eq_configMatrix_pow_mulVec (R : Type*) [CommSemiring R] {input : List Bool}
    {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) (t : ℕ) :
    (machine.acceptCoins input t : R) =
      (machine.configMatrix R V ^ t *ᵥ FiniteCfg.acceptVec R V) ⟨_, hinit⟩ := by
  classical
  have := Matrix.coinStepMatrix_pow_mulVec (R := R) hV
    (fun finite : FiniteCfg k Bool State =>
      if finite.state = none ∧ finite.output = [true] then 1 else 0) t ⟨_, hinit⟩
  rw [configMatrix]
  convert this.symm using 1
  · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_one,
      acceptCoins_eq_card_views]
  · rfl

open scoped Classical in
/-- **The acceptance probability is an entry of a power of the stochastic matrix**: with
`P = N / 2` the stochastic matrix of the run, `acceptCoins input t / 2 ^ t` is the entry at the
initial view of `P ^ t *ᵥ e`. -/
theorem acceptCoins_div_eq_configMatrix_pow_mulVec (R : Type*) [Field R] {input : List Bool}
    {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) (t : ℕ) :
    (machine.acceptCoins input t : R) / 2 ^ t =
      (((2 : R)⁻¹ • machine.configMatrix R V) ^ t *ᵥ FiniteCfg.acceptVec R V) ⟨_, hinit⟩ := by
  rw [smul_pow, Matrix.smul_mulVec, Pi.smul_apply,
    ← acceptCoins_eq_configMatrix_pow_mulVec R hV hinit, smul_eq_mul, inv_pow, div_eq_inv_mul]

open scoped Classical in
/-- **The substochastic form**: splitting the coin strings by the time the run halts,
`acceptCoins input T / 2 ^ T` is the entry at the initial view of `∑ t ≤ T, (S / 2) ^ t *ᵥ e`,
with `S` the live configuration matrix. No halting time is needed. -/
theorem acceptCoins_div_eq_sum_liveConfigMatrix (R : Type*) [Field R] [CharZero R]
    {input : List Bool} {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) (T : ℕ) :
    (machine.acceptCoins input T : R) / 2 ^ T = ∑ t ∈ Finset.range (T + 1),
      (((2 : R)⁻¹ • machine.liveConfigMatrix R V) ^ t *ᵥ FiniteCfg.acceptVec R V) ⟨_, hinit⟩ := by
  classical
  have h := Matrix.coinStepMatrix_pow_mulVec_eq_sum (R := R) hV
    (live := fun finite : FiniteCfg k Bool State => finite.state ≠ none)
    (fun finite hfinite => viewCoinStep_of_halted (not_not.mp hfinite))
    (f := fun finite : FiniteCfg k Bool State =>
      if finite.state = none ∧ finite.output = [true] then 1 else 0)
    (fun finite hfinite => ite_eq_right_iff.mpr fun h => absurd h.1 hfinite) T ⟨_, hinit⟩
  have hvec : (fun v : V => if (v : FiniteCfg k Bool State).state = none ∧
      (v : FiniteCfg k Bool State).output = [true] then (1 : R) else 0) =
      FiniteCfg.acceptVec R V := rfl
  rw [hvec] at h
  rw [acceptCoins_eq_configMatrix_pow_mulVec R hV hinit, configMatrix]
  convert congrArg (· / (2 : R) ^ T) h using 1
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htT : t ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [smul_pow, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, liveConfigMatrix]
    have h2 : (2 : R) ^ T = 2 ^ (T - t) * 2 ^ t := by rw [← pow_add, Nat.sub_add_cancel htT]
    rw [h2, inv_pow, mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero), div_eq_inv_mul]

open scoped Classical in
/-- **The live matrix is nilpotent on reachable views**: if every view of `V` is reachable and
every branch halts within `T` steps, then `S ^ (T + 1) = 0`. -/
theorem liveConfigMatrix_pow_eq_zero (R : Type*) [CommSemiring R] {input : List Bool} {T : ℕ}
    (ht : machine.toNTM.RunsInTime input T) {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hreach : ∀ finite ∈ V,
      Relation.ReflTransGen machine.toNTM.ViewStep (machine.toNTM.initView input) finite) :
    machine.liveConfigMatrix R V ^ (T + 1) = 0 := by
  classical
  refine Matrix.liveCoinStepMatrix_pow_eq_zero hV fun x hx w => ⟨Fin.last T, ?_⟩
  obtain ⟨coins, hcoins⟩ := reflTransGen_viewStep_toNTM_iff.mp (hreach x hx)
  have h := viewRep_foldl_viewCoinStep (machine := machine)
    (MultiTapeNTM.viewRep_init (ntm := machine.toNTM) input) (coins ++ (List.ofFn w).take T)
  have hhalt := halted_stepCoins machine ht (coins := coins ++ (List.ofFn w).take T)
    (by simp)
  rw [List.foldl_append, hcoins] at h
  simpa using h.state.trans hhalt

open scoped Classical in
/-- **The acceptance probability is an entry of `(1 - S / 2)⁻¹ *ᵥ e`**: if every view of `V` is
reachable and every branch halts within `T` steps, then `acceptCoins input T / 2 ^ T` is the
entry at the initial view of `(1 - S / 2)⁻¹ *ᵥ e`, with `S` the live configuration matrix. -/
theorem acceptCoins_div_eq_inv_mulVec (R : Type*) [Field R] [CharZero R] {input : List Bool}
    {T : ℕ} (ht : machine.toNTM.RunsInTime input T) {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hreach : ∀ finite ∈ V,
      Relation.ReflTransGen machine.toNTM.ViewStep (machine.toNTM.initView input) finite)
    (hinit : machine.toNTM.initView input ∈ V) :
    (machine.acceptCoins input T : R) / 2 ^ T =
      ((1 - (2 : R)⁻¹ • machine.liveConfigMatrix R V)⁻¹ *ᵥ FiniteCfg.acceptVec R V)
        ⟨_, hinit⟩ := by
  rw [Matrix.inv_one_sub_eq_sum_pow (n := T + 1) (by
      rw [smul_pow, liveConfigMatrix_pow_eq_zero R ht hV hreach, smul_zero]),
    Matrix.sum_mulVec, Finset.sum_apply, acceptCoins_div_eq_sum_liveConfigMatrix R hV hinit]

/-- **The reachable views form a small closed set**: under a space bound `s`, the views reachable
from the initial view form a finite set, closed under coin steps, with at most
`2 ^ (2 * coreLengthBound k State n s + 1)` elements. -/
theorem exists_finset_reachable [Finite State] {input : List Bool} {s : ℕ}
    (hs : machine.toNTM.RunsInSpace input s) :
    ∃ V : Finset (FiniteCfg k Bool State),
      (∀ finite, finite ∈ V ↔
        Relation.ReflTransGen machine.toNTM.ViewStep (machine.toNTM.initView input) finite) ∧
      (∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V) ∧
      V.card ≤ 2 ^ (2 * MultiTapeNTM.coreLengthBound k State input.length s + 1) := by
  set reach := {finite | Relation.ReflTransGen machine.toNTM.ViewStep
    (machine.toNTM.initView input) finite}
  have hfin : reach.Finite := by
    by_contra hinf
    obtain ⟨V, hsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (2 ^ (2 * MultiTapeNTM.coreLengthBound k State input.length s + 1) + 1)
    have := MultiTapeNTM.length_le_of_nodup_reachable hs V.nodup_toList
      fun finite hf => hsub (Finset.mem_toList.mp hf)
    rw [Finset.length_toList, hcard] at this
    omega
  refine ⟨hfin.toFinset, fun finite => hfin.mem_toFinset, fun finite hf bit => ?_, ?_⟩
  · rw [hfin.mem_toFinset] at hf ⊢
    exact Relation.ReflTransGen.tail hf (viewStep_toNTM_iff.mpr ⟨bit, rfl⟩)
  · rw [← Finset.length_toList]
    exact MultiTapeNTM.length_le_of_nodup_reachable hs (Finset.nodup_toList _)
      fun finite hf => hfin.mem_toFinset.mp (Finset.mem_toList.mp hf)

end MultiTapePTM

end Turing

namespace Cslib.Complexity

open _root_.Turing Matrix

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

open scoped Classical in
/-- **`BPL` through polynomial-size configuration matrices**: a `BPL` machine has, on every
encoded instance of length `n`, a set `V` of at most `2 * (2 * (n + 1)) ^ d` views, all reachable
from the initial view and closed under coin steps, such that every branch halts within
`T = 2 * (2 * (n + 1)) ^ d` steps, the live configuration matrix `S` on `V` satisfies
`S ^ (T + 1) = 0`, and the entry at the initial view of `(1 - S / 2)⁻¹ *ᵥ e` is at least `2/3` on
members and at most `1/3` on non-members, with `e` the indicator of the accepting halted
views. -/
theorem exists_configMatrix_of_mem_BPL (h : A ∈ BPL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (d : ℕ),
      ∀ a, ∃ (V : Finset (FiniteCfg k Bool State)) (hinit : M.toNTM.initView (enc a) ∈ V),
        V.card ≤ 2 * (2 * ((enc a).length + 1)) ^ d ∧
        (∀ finite ∈ V, ∀ bit, M.viewCoinStep finite bit ∈ V) ∧
        (∀ finite ∈ V,
          Relation.ReflTransGen M.toNTM.ViewStep (M.toNTM.initView (enc a)) finite) ∧
        M.toNTM.RunsInTime (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) ∧
        M.liveConfigMatrix ℚ V ^ (2 * (2 * ((enc a).length + 1)) ^ d + 1) = 0 ∧
        (a ∈ A → 2 / 3 ≤ ((1 - (2 : ℚ)⁻¹ • M.liveConfigMatrix ℚ V)⁻¹ *ᵥ
          FiniteCfg.acceptVec ℚ V) ⟨_, hinit⟩) ∧
        (a ∉ A → ((1 - (2 : ℚ)⁻¹ • M.liveConfigMatrix ℚ V)⁻¹ *ᵥ
          FiniteCfg.acceptVec ℚ V) ⟨_, hinit⟩ ≤ 1 / 3) := by
  obtain ⟨k, State, hfin, M, c, hM⟩ := h
  refine ⟨k, State, hfin, M, 2 * (8 + 2 * Nat.card (Option State) + 200 * k) * (c + 1),
    fun a => ?_⟩
  obtain ⟨hs, t, ht, hmem, hnot⟩ := hM a
  obtain ⟨V, hreach, hV, hcard⟩ := M.exists_finset_reachable hs
  have hinit : M.toNTM.initView (enc a) ∈ V := (hreach _).mpr .refl
  have hpoly := MultiTapeNTM.two_pow_coreLengthBound_log_le k State c (enc a).length
  have hreach' : ∀ finite ∈ V,
      Relation.ReflTransGen M.toNTM.ViewStep (M.toNTM.initView (enc a)) finite :=
    fun finite hf => (hreach _).mp hf
  have hT := (MultiTapeNTM.runsInTime_of_runsInSpace hs ht).mono hpoly
  refine ⟨V, hinit, hcard.trans hpoly, hV, hreach', hT,
    MultiTapePTM.liveConfigMatrix_pow_eq_zero ℚ hT hV hreach', fun ha => ?_, fun ha => ?_⟩
  all_goals rw [← MultiTapePTM.acceptCoins_div_eq_inv_mulVec ℚ ht hV hreach']
  · have h : ((2 * 2 ^ t : ℕ) : ℚ) ≤ ((3 * M.acceptCoins (enc a) t : ℕ) : ℚ) :=
      Nat.cast_le.mpr (hmem ha)
    push_cast at h
    rw [le_div_iff₀ (by positivity)]
    linarith
  · have h : ((3 * M.acceptCoins (enc a) t : ℕ) : ℚ) ≤ ((2 ^ t : ℕ) : ℚ) :=
      Nat.cast_le.mpr (hnot ha)
    push_cast at h
    rw [div_le_iff₀ (by positivity)]
    linarith

end Cslib.Complexity
