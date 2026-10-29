/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPSZ.AssignSL
public import Complexity.Computability.Complexity.FineGrained.PPSZ.Unique
public import Complexity.Logics.Propositional.Resolution.Restrict

/-!
# PPSZ for satisfiable formulas: frozen variables and the guess probability

A run of PPSZ on a satisfiable formula `φ` passes through partial assignments `τ`. When `τ` is the
restriction of a satisfying assignment `σ` to a set `T` of variables, an unassigned variable `x` is
*guessed* if, at its turn, the values of `σ` on `T` and on the variables placed before `x` do not
w-imply `x = σ x`. Its *guess probability* `guessProb φ w T σ x` is the fraction of the `n!`
orders in which this happens; for `T = ∅` it is the probability that `x` is not forced
(`guessProb_empty`). A variable is *frozen* under `τ` (`Frozen`) if all satisfying extensions of
`τ` (`IsSatExtension`) agree on it [Hertli, Definition 5 (p. 4)][Hertli2011].

[Hertli][Hertli2011] analyses a modified PPSZ that sets every w-implied variable as soon as it is
implied; here the algorithm is unmodified, as in [Scheder, Steinberger][SchederSteinberger2017],
and the quantities below are the analogues of Hertli's for the unmodified algorithm.

This file proves the three properties of the guess probability that the adaptation of the
analysis of [Hertli][Hertli2011] uses.

* **Monotonicity** [Hertli, Lemma 10 (p. 5)][Hertli2011]: fixing more variables of `σ` does not
  increase the guess probability (`guessProb_le_of_subset`), since w-implication is monotone.
* **The first-step identity**, the analogue for the unmodified algorithm of
  [Hertli, Lemma 11 (p. 6)][Hertli2011]: with `m` unassigned
  variables, `m * u = f + ∑ y, u_y`, where `u` is the guess probability of `x`, `f` is `1` if
  `x = σ x` is not w-implied under `τ` and `0` otherwise, and `u_y` is the guess probability after
  also fixing `y`, for the unassigned `y ≠ x` (`card_compl_mul_guessProb`,
  `sum_guessProb_sub`). Hertli conditions on the first variable of a random order of the
  unassigned variables. Here the order is on all `n` variables; the event only depends on the
  unassigned variables placed before `x`, so it is the event of independent inclusion of the
  unassigned variables (`guessProb_eq_integral`, by `bernoulliProb_union_of_forall_insert`), and
  the identity is `card_add_one_mul_integral_bernoulliProb` (original).
* **The guess bound for frozen variables**: if the clauses of `φ` have at most `k` literals,
  `w ≥ ∑ i < h, (k - 1) ^ i` and `x` is frozen, then `guessProb φ w T σ x ≤ 1 - qbar k h`
  (`guessProb_le_of_frozen`), the bound of the unique case
  (`qbar_le_card_filter_forced_div_factorial`). For the unmodified algorithm this is the
  finite-depth form of [Scheder, Steinberger, Theorem 4 (p. 9:4)][SchederSteinberger2017], which
  they attribute to Paturi, Pudlák, Saks and Zane: w-implication of depth `h` has error at most
  `1 - qbar k h` against formulas with clauses of at most `k` literals. Hertli's bound for his
  modified algorithm, [Hertli, Theorem 6 (p. 4)][Hertli2011], which he only sketches, follows
  from it by monotonicity (`guessProb_le_of_subset`), since the modified algorithm fixes more
  variables of `σ` before `x`. Here the critical clause tree is built on the restricted formula
  `φ.restrictBy τ` and rooted at `x` (`IsCriticalTreeAt`): flipping `x` and other unassigned
  variables gives an extension of `τ` that disagrees with `σ` on `x`, which falsifies `φ` since
  `x` is frozen. A w-implication in the restricted formula lifts to `φ`, one clause of `φ` for
  each restricted clause (`WImplied.of_restrictBy`). This proof is original.

The restriction of a formula by a partial assignment is `Cslib.Logic.PL.CNF.restrictBy`. Under an
assignment that extends the partial assignment, it has the value of the formula
(`Cslib.Logic.PL.CNF.eval_restrictBy`), and it has no wider clauses
(`Cslib.Logic.PL.CNF.length_le_of_mem_restrictBy`); these facts are in
`Complexity.Logics.Propositional.Resolution.Restrict`.

## Main definitions

* `Cslib.Complexity.PPSZ.Frozen`: an unassigned variable on which all satisfying extensions agree.
* `Cslib.Complexity.PPSZ.guessProb`: the fraction of the orders in which a variable is guessed.

## Main results

* `Cslib.Complexity.PPSZ.satLit_iff_of_frozen`: a frozen variable carries a single satisfying
  literal.
* `Cslib.Complexity.PPSZ.WImplied.of_restrictBy`: w-implication lifts from the restricted formula.
* `Cslib.Complexity.PPSZ.guessProb_le_of_subset`: the guess probability is antitone in the set of
  fixed variables [Hertli, Lemma 10][Hertli2011].
* `Cslib.Complexity.PPSZ.guessProb_eq_integral`: the guess probability as an integral of
  independent inclusion of the unassigned variables.
* `Cslib.Complexity.PPSZ.card_compl_mul_guessProb`,
  `Cslib.Complexity.PPSZ.sum_guessProb_sub`: the first-step identity
  [Hertli, Lemma 11][Hertli2011], for the unmodified algorithm.
* `Cslib.Complexity.PPSZ.guessProb_le_of_frozen`: frozen variables are guessed with probability at
  most `1 - qbar k h` [Scheder, Steinberger, Theorem 4][SchederSteinberger2017].

## References

* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
* [D. Scheder, J. Steinberger, *PPSZ for general k-SAT*][SchederSteinberger2017]
* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL Cslib.BitString
open Finset hiding restrict
open Cslib.Complexity.PPZ (restrict)

variable {n : ℕ}

/-! ### Lifting w-implication -/

/-- **w-implication lifts from a restricted formula** (original): if a value is w-implied in
`φ.restrictBy ρ` under `τ`, it is w-implied in `φ` under every `τ'` that extends both `ρ` and `τ`.
Each clause of the restricted formula is replaced by a clause of `φ` it comes from. -/
theorem WImplied.of_restrictBy {φ : CNF (Fin n)} {w : ℕ} {ρ τ τ' : Fin n → Option Bool}
    {x : Fin n} {b : Bool} (h : WImplied (φ.restrictBy ρ) w τ x b)
    (hρ : ∀ y c, ρ y = some c → τ' y = some c) (hτ : ∀ y c, τ y = some c → τ' y = some c) :
    WImplied φ w τ' x b := by
  obtain ⟨ψ, hψ, hlen, himp⟩ := h
  obtain ⟨χ, hχ, hχlen, heval⟩ := CNF.exists_preimage_restrictBy hψ
  refine ⟨χ, hχ, hχlen ▸ hlen, fun γ hγ hχγ => himp γ (fun y c hy => hγ y c (hτ y c hy)) ?_⟩
  rwa [← heval γ fun y c hy => hγ y c (hρ y c hy)]

/-- A restriction to a smaller set is extended by the restriction to a larger set. -/
private theorem restrict_eq_some_of_subset {σ : Fin n → Bool} {D E : Finset (Fin n)} (hDE : D ⊆ E)
    {y : Fin n} {c : Bool} (h : restrict σ D y = some c) : restrict σ E y = some c := by
  unfold restrict at h ⊢
  split_ifs at h with hy
  rw [ite_eq_left (hDE hy), h]

/-! ### Frozen variables -/

/-- `x` is **frozen** under the partial assignment `τ`
[Hertli, Definition 5 (p. 4)][Hertli2011]: it is unassigned, and all satisfying extensions of `τ`
give it the same value. Hertli defines frozen variables of the restricted formula; its satisfying
assignments are the satisfying extensions of `τ` (`Cslib.Logic.PL.CNF.eval_restrictBy`). -/
def Frozen (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) : Prop :=
  τ x = none ∧ ∀ σ σ', IsSatExtension φ τ σ → IsSatExtension φ τ σ' → σ x = σ' x

/-- A satisfying assignment is a satisfying extension of each of its restrictions. -/
theorem isSatExtension_restrict {φ : CNF (Fin n)} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    (T : Finset (Fin n)) : IsSatExtension φ (restrict σ T) σ :=
  ⟨fun _ _ => PPZ.eq_of_restrict_eq_some, hσ⟩

/-- A frozen variable stays frozen when another unassigned variable is assigned. -/
theorem Frozen.update {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x y : Fin n}
    (h : Frozen φ τ x) (hxy : x ≠ y) (hy : τ y = none) (b : Bool) :
    Frozen φ (Function.update τ y (some b)) x := by
  have hext : ∀ σ, IsSatExtension φ (Function.update τ y (some b)) σ → IsSatExtension φ τ σ :=
    fun σ hσ => ((isSatExtension_update_iff hy).1 hσ).1
  refine ⟨?_, fun σ σ' hσ hσ' => h.2 σ σ' (hext σ hσ) (hext σ' hσ')⟩
  rw [Function.update_of_ne hxy]
  exact h.1

/-- An unassigned variable that is not frozen takes both values among the satisfying
extensions. -/
theorem exists_ne_of_not_frozen {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n}
    (hx : τ x = none) (h : ¬ Frozen φ τ x) :
    ∃ σ σ', IsSatExtension φ τ σ ∧ IsSatExtension φ τ σ' ∧ σ x ≠ σ' x :=
  by_contra fun hc => h ⟨hx, fun σ σ' hσ hσ' => by_contra fun hne => hc ⟨σ, σ', hσ, hσ', hne⟩⟩

/-- **Satisfying literals on a frozen variable**: if `y` is frozen under `τ`, which has the
satisfying extension `σ`, the only satisfying literal on `y` is `y = σ y`. -/
theorem satLit_iff_of_frozen {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {σ : Fin n → Bool}
    (hσ : IsSatExtension φ τ σ) {y : Fin n} (hfr : Frozen φ τ y) {b : Bool} :
    SatLit φ τ y b ↔ b = σ y := by
  constructor
  · rintro ⟨-, σ', hσ', rfl⟩
    exact hfr.2 σ' σ hσ' hσ
  · rintro rfl
    exact ⟨hfr.1, σ, hσ, rfl⟩

/-! ### The guess probability -/

/-- **The guess probability** of `x` after fixing the variables of `T` to their values in `σ`: the
fraction of the `n!` orders `π` in which the values of `σ` on `T` and on the variables placed
before `x` do not w-imply `x = σ x`, with the order taken on all variables; the variables of `T`
placed before `x` change nothing. This is the analogue for the unmodified algorithm of
`p_guessed` of [Hertli, Definition 4 (p. 4)][Hertli2011], for the formula with the variables of
`T` fixed. For frozen `x` it is `E_π[J_x(π, σ)]` of
[Scheder, Steinberger, p. 9:4][SchederSteinberger2017] for that formula. -/
noncomputable def guessProb (φ : CNF (Fin n)) (w : ℕ) (T : Finset (Fin n)) (σ : Fin n → Bool)
    (x : Fin n) : ℝ :=
  (#(univ.filter fun π : Equiv.Perm (Fin n) =>
    ¬ WImplied φ w (restrict σ (T ∪ placedBefore π x)) x (σ x)) : ℝ) / n.factorial

variable {φ : CNF (Fin n)} {w : ℕ} {T T' : Finset (Fin n)} {σ : Fin n → Bool} {x : Fin n}

/-- The guess probability is nonnegative. -/
theorem guessProb_nonneg : 0 ≤ guessProb φ w T σ x := by
  unfold guessProb
  positivity

/-- The guess probability is at most `1`. -/
theorem guessProb_le_one : guessProb φ w T σ x ≤ 1 := by
  unfold guessProb
  rw [div_le_one (by exact_mod_cast Nat.factorial_pos n)]
  have := card_le_univ (univ.filter fun π : Equiv.Perm (Fin n) =>
    ¬ WImplied φ w (restrict σ (T ∪ placedBefore π x)) x (σ x))
  rw [Fintype.card_perm, Fintype.card_fin] at this
  exact_mod_cast this

/-- **Monotonicity of the guess probability** [Hertli, Lemma 10 (p. 5)][Hertli2011]: fixing more
variables of `σ` does not increase the guess probability, since w-implication is monotone
(`WImplied.mono`). Hertli removes the new variable from the order; here the order is on all
variables, so the statement is a comparison of events for each order. -/
theorem guessProb_le_of_subset (hTT' : T ⊆ T') : guessProb φ w T' σ x ≤ guessProb φ w T σ x := by
  unfold guessProb
  refine div_le_div_of_nonneg_right (Nat.cast_le.2 (card_le_card fun π hπ => ?_))
    (Nat.cast_nonneg _)
  rw [mem_filter] at hπ ⊢
  exact ⟨hπ.1, fun h => hπ.2 (h.mono (fun c hc => hc) le_rfl fun y c =>
    restrict_eq_some_of_subset (union_subset_union_left hTT'))⟩

/-- If `x = σ x` is w-implied under `σ` restricted to `T`, then `x` is never guessed. -/
theorem guessProb_eq_zero_of_wImplied (h : WImplied φ w (restrict σ T) x (σ x)) :
    guessProb φ w T σ x = 0 := by
  unfold guessProb
  rw [div_eq_zero_iff, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
  exact Or.inl fun π _ => not_not.2 (h.mono (fun c hc => hc) le_rfl fun y c =>
    restrict_eq_some_of_subset subset_union_left)

/-- An assigned variable is never guessed. -/
theorem guessProb_of_mem (hx : x ∈ T) : guessProb φ w T σ x = 0 :=
  guessProb_eq_zero_of_wImplied ⟨[], by simp, by simp, fun γ hγ _ =>
    hγ x (σ x) (by simp [restrict, hx])⟩

/-- With no fixed variables, `x` is guessed exactly when it is not forced: the guess probability
is `1` minus the forcing probability of `round_apply_ge`. -/
theorem guessProb_empty (hσ : φ.eval σ = true) :
    guessProb φ w ∅ σ x =
      1 - (#(univ.filter fun π : Equiv.Perm (Fin n) => Forced φ w σ π x) : ℝ) / n.factorial := by
  classical
  have hN : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Equiv.Perm (Fin n))))
    fun π => Forced φ w σ π x
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h
  have hcongr : (univ.filter fun π : Equiv.Perm (Fin n) =>
      ¬ WImplied φ w (restrict σ (∅ ∪ placedBefore π x)) x (σ x)) =
      univ.filter fun π => ¬ Forced φ w σ π x := by
    refine filter_congr fun π _ => ?_
    rw [empty_union, forced_iff_wImplied hσ, placedBefore_eq_prefixSet]
  unfold guessProb
  rw [hcongr, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hN.ne', ← Nat.cast_add,
    add_comm, h]

/-- **The guess probability as an integral** (original). The event that `x` is guessed depends
only on the unassigned variables placed before `x`, so the guess probability is the average over
`r ∈ [0, 1]` of the probability of the event when each unassigned variable other than `x` is fixed
independently with probability `r`. -/
theorem guessProb_eq_integral (φ : CNF (Fin n)) (w : ℕ) (T : Finset (Fin n)) (σ : Fin n → Bool)
    (x : Fin n) :
    guessProb φ w T σ x = ∫ r in (0 : ℝ)..1, bernoulliProb (Tᶜ.erase x) r fun S =>
      ¬ WImplied φ w (restrict σ (T ∪ S)) x (σ x) := by
  unfold guessProb
  rw [card_filter_placedBefore_div_factorial_eq_integral x
    fun S => ¬ WImplied φ w (restrict σ (T ∪ S)) x (σ x)]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have hU : univ.erase x = Tᶜ.erase x ∪ T.erase x := by
    ext y
    by_cases hy : y ∈ T <;> simp [hy]
  have hdisj : Disjoint (Tᶜ.erase x) (T.erase x) :=
    disjoint_left.2 fun y hy hy' => (mem_compl.1 (mem_erase.1 hy).2) (mem_erase.1 hy').2
  rw [hU]
  refine bernoulliProb_union_of_forall_insert hdisj fun v hv S => ?_
  rw [union_insert, insert_eq_of_mem (mem_union_left S (mem_erase.1 hv).2)]

/-- **The first-step identity**, the analogue for the unmodified algorithm of
[Hertli, Lemma 11 (p. 6)][Hertli2011], in the form `m * u = f + ∑ y, u_y` (original, by
`card_add_one_mul_integral_bernoulliProb`). Let `x ∉ T`,
let `m = |Tᶜ|` be the number of unassigned variables, `u` the guess probability of `x`, and
`f = 0` if `x = σ x` is w-implied under `σ` restricted to `T` and `f = 1` otherwise. Then `m * u`
is `f` plus the sum, over the unassigned `y ≠ x`, of the guess probability `u_y` after also
fixing `y`. Hertli assumes that `x` is not w-implied, so that `f = 1`. -/
theorem card_compl_mul_guessProb (hx : x ∉ T) :
    (#Tᶜ : ℝ) * guessProb φ w T σ x =
      (if WImplied φ w (restrict σ T) x (σ x) then 0 else 1) +
        ∑ y ∈ Tᶜ.erase x, guessProb φ w (insert y T) σ x := by
  rw [← card_erase_add_one (mem_compl.2 hx), Nat.cast_add_one, guessProb_eq_integral,
    card_add_one_mul_integral_bernoulliProb, union_empty, ite_not]
  congr 1
  refine sum_congr rfl fun y _ => ?_
  rw [guessProb_eq_integral, show (insert y T)ᶜ.erase x = (Tᶜ.erase x).erase y by
    ext z
    simp only [mem_erase, mem_compl, mem_insert, not_or]
    tauto]
  simp only [union_insert, insert_union]

/-- **The first-step identity, as a sum of decreases**, the analogue for the unmodified algorithm
of [Hertli, Lemma 11 (p. 6)][Hertli2011]: with
`u`, `u_y` and `f` as in `card_compl_mul_guessProb`, `∑ y ≠ x unassigned, (u - u_y) = f - u`. -/
theorem sum_guessProb_sub (hx : x ∉ T) :
    ∑ y ∈ Tᶜ.erase x, (guessProb φ w T σ x - guessProb φ w (insert y T) σ x) =
      (if WImplied φ w (restrict σ T) x (σ x) then 0 else 1) - guessProb φ w T σ x := by
  have h := card_compl_mul_guessProb (φ := φ) (w := w) (σ := σ) hx
  rw [← card_erase_add_one (mem_compl.2 hx), Nat.cast_add_one] at h
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith

/-! ### The guess bound for frozen variables -/

/-- **Critical clause trees for frozen variables** (original). If `σ` satisfies `φ` and `x` is
frozen under `σ` restricted to `T`, then the restricted formula has a critical clause tree of every
height rooted at `x` for `σ`: flipping any set of variables that contains `x` falsifies a clause of
the restricted formula. -/
theorem exists_isCriticalTreeAt_restrictBy (hσ : φ.eval σ = true) (hfr : Frozen φ (restrict σ T) x)
    (h : ℕ) : ∃ C, IsCriticalTreeAt (φ.restrictBy (restrict σ T)) σ x h C := by
  classical
  have key : ∀ p : List (Fin n), x ∈ p →
      ∃ c ∈ φ.restrictBy (restrict σ T), c.eval (flipOn p.toFinset σ) = false := by
    intro p hxp
    have hxT : x ∉ T := fun hxT => by
      have := hfr.1
      simp [restrict, hxT] at this
    set γ := flipOn (p.toFinset \ T) σ with hγ
    have hγT : ∀ y c, restrict σ T y = some c → γ y = c := fun y c hy => by
      have hyT : y ∈ T := by
        by_contra hyT
        simp [restrict, hyT] at hy
      rw [hγ, flipOn_apply_of_notMem (fun h => (mem_sdiff.1 h).2 hyT)]
      exact PPZ.eq_of_restrict_eq_some hy
    by_contra hall
    push Not at hall
    have hψ : (φ.restrictBy (restrict σ T)).eval γ = true := by
      refine (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_
      obtain ⟨l, hl, hls⟩ := (Clause.eval_eq_true_iff _ _).1 (by simpa using hall c hc)
      have hlT : l.1 ∉ T := fun hlT => by
        have := CNF.eq_none_of_mem_restrictBy hc hl
        simp [restrict, hlT] at this
      refine (Clause.eval_eq_true_iff _ _).2 ⟨l, hl, ?_⟩
      rw [← hls]
      exact flipOn_apply_eq_of_iff (by simp [hlT])
    rw [CNF.eval_restrictBy hγT] at hψ
    have := hfr.2 γ σ ⟨hγT, hψ⟩ (isSatExtension_restrict hσ T)
    rw [hγ, flipOn_apply_of_mem (mem_sdiff.2 ⟨List.mem_toFinset.2 hxp, hxT⟩)] at this
    cases hσx : σ x <;> simp [hσx] at this
  have key' : ∀ p : List (Fin n), ∃ c : Clause (Fin n), x ∈ p →
      c ∈ φ.restrictBy (restrict σ T) ∧ c.eval (flipOn p.toFinset σ) = false := by
    intro p
    by_cases hxp : x ∈ p
    · obtain ⟨c, hc, hce⟩ := key p hxp
      exact ⟨c, fun _ => ⟨hc, hce⟩⟩
    · exact ⟨[], fun h => absurd h hxp⟩
  choose C hC using key'
  exact ⟨C, fun p hxp _ => hC p hxp⟩

/-- **The guess bound for frozen variables**, for the unmodified algorithm the finite-depth form of
[Scheder, Steinberger, Theorem 4 (p. 9:4)][SchederSteinberger2017], which they attribute to
Paturi, Pudlák, Saks and Zane; Hertli's bound for his modified algorithm,
[Hertli, Theorem 6 (p. 4)][Hertli2011], follows from it by `guessProb_le_of_subset`. Let `σ`
satisfy `φ`, whose clauses have at most `k` literals, let `w ≥ ∑ i < h, (k - 1) ^ i`, and let `x`
be frozen under `σ` restricted to `T`. Then `x` is guessed in at most a `1 - qbar k h` fraction of
the orders, as in the unique case (`qbar_le_card_filter_forced_div_factorial`). The proof,
through a critical clause tree of the restricted formula rooted at `x`
(`exists_isCriticalTreeAt_restrictBy`) and the lifting of w-implication
(`WImplied.of_restrictBy`), is original. -/
theorem guessProb_le_of_frozen {k h : ℕ} (hσ : φ.eval σ = true) (hfr : Frozen φ (restrict σ T) x)
    (hlen : ∀ c ∈ φ, c.length ≤ k) (hw : ∑ i ∈ range h, (k - 1) ^ i ≤ w) :
    guessProb φ w T σ x ≤ 1 - qbar k h := by
  classical
  set ψ := φ.restrictBy (restrict σ T)
  have hψσ : ψ.eval σ = true := by
    rw [CNF.eval_restrictBy fun _ _ => PPZ.eq_of_restrict_eq_some]
    exact hσ
  have hψlen := CNF.length_le_of_mem_restrictBy (ρ := restrict σ T) hlen
  obtain ⟨C, hC⟩ := exists_isCriticalTreeAt_restrictBy hσ hfr h
  have hq := qbar_le_card_filter_placedBefore_div_factorial (E := fun A => Cut C A h [x])
    fun r hr => hC.Q_le_bernoulliProb_cut hψσ hψlen hr
  have hN : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Equiv.Perm (Fin n))))
    fun π => Cut C (placedBefore π x) h [x]
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  have hsub : (univ.filter fun π : Equiv.Perm (Fin n) =>
      ¬ WImplied φ w (restrict σ (T ∪ placedBefore π x)) x (σ x)) ⊆
      univ.filter fun π => ¬ Cut C (placedBefore π x) h [x] := by
    intro π hπ
    rw [mem_filter] at hπ ⊢
    refine ⟨hπ.1, fun hcut => hπ.2 ?_⟩
    exact (hC.wImplied_of_cut hψσ hψlen hw hcut).of_restrictBy
      (fun y c => restrict_eq_some_of_subset subset_union_left)
      (fun y c => restrict_eq_some_of_subset subset_union_right)
  have hle : guessProb φ w T σ x ≤
      (#(univ.filter fun π : Equiv.Perm (Fin n) => ¬ Cut C (placedBefore π x) h [x]) : ℝ) /
        n.factorial := by
    unfold guessProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) hN.le
  have hsplit : (#(univ.filter fun π : Equiv.Perm (Fin n) =>
      ¬ Cut C (placedBefore π x) h [x]) : ℝ) / n.factorial =
      1 - (#(univ.filter fun π : Equiv.Perm (Fin n) => Cut C (placedBefore π x) h [x]) : ℝ) /
        n.factorial := by
    rw [eq_sub_iff_add_eq, ← add_div, ← Nat.cast_add, add_comm, hsum,
      div_self hN.ne']
  linarith

end Cslib.Complexity.PPSZ
