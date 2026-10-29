/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Complexity.Probability.PMF
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Data.BitString.Isolation
import Complexity.Probability.PMF.Event
import Mathlib.Analysis.MeanInequalities

/-!
# The satisfiability coding lemma and PPZ for k-SAT

The PPZ algorithm of Paturi, Pudlák and Zane processes the variables of a CNF formula in a uniformly
random order. A variable is *forced* if, after substituting the values already chosen, some clause
becomes a unit clause on it; the algorithm then sets the variable to satisfy that clause. Otherwise
it chooses the value uniformly (`Cslib.Complexity.PPZ.round`) [Paturi, Pudlák, Zane][PPZ1997].

Let `σ` be the only satisfying assignment of the formula. Along a run that agrees with `σ`, forced
values are correct (`forced_eq`), so the run produces `σ` with probability `2^{-u}`, where `u` is
the number of unforced variables (`run_apply_restrict`). Flipping a variable `x` of `σ` falsifies
some clause; in this *critical clause* the literal on `x` is the only one true under `σ`
(`exists_critical`). If `x` comes after the other variables of its critical clause, then `x` is
forced. In a uniformly random order this happens with probability `1 / m` for a clause on `m`
variables (`card_isLast_mul`), so for clauses of at most `k` literals at most `(1 - 1/k) n`
variables are unforced on average. By the arithmetic–geometric mean inequality, one round finds
`σ` with probability at least `2^{-(1 - 1/k) n}` (`round_success`).

The run is defined for any oracle that proposes values for variables (`runWith`); PPZ uses unit
clauses and PPSZ (`Cslib.Complexity.PPSZ.round`) uses bounded implication. The run analysis
(`runWith_apply_restrict`, `roundWith_apply_eq`) and the averaging step (`roundWith_apply_ge`) are
proved once for every oracle whose values agree with `σ` along runs that agree with `σ`.

Without uniqueness, the same argument applies to the variables `I(σ)` whose flips falsify the
formula, and one round outputs `σ` with probability at least `2^{-(n - |I(σ)| / k)}`
(`round_apply_ge`). Since `∑_σ 2^{|I(σ)|} ≥ 2^n` over the satisfying assignments
(`Cslib.BitString.two_pow_le_sum_two_pow_isolation`), one round finds some satisfying assignment
with probability at least `2^{-(1 - 1/k) n}` (`round_success_of_satisfiable`).

## Main definitions

* `Cslib.Complexity.PPZ.forced`: the value forced on a variable by a unit clause.
* `Cslib.Complexity.PPZ.runWith`, `Cslib.Complexity.PPZ.roundWith`: a run in a fixed order and a
  round in a uniformly random order, with values proposed by an oracle.
* `Cslib.Complexity.PPZ.run`: the first `i` steps of a round in a fixed order.
* `Cslib.Complexity.PPZ.prefixSet`, `Cslib.Complexity.PPZ.EqOnPrefix`: the variables processed in
  the first `i` steps of an order, and agreement of two orders on their first `i` positions.
* `Cslib.Complexity.PPZ.round`: one round of PPZ, in a uniformly random order.

## Main results

* `Cslib.Complexity.PPZ.runWith_apply_restrict`: for a sound oracle, a run in a fixed order
  produces the solution with probability `2^{-u}`.
* `Cslib.Complexity.PPZ.roundWith_apply_ge`: for a sound oracle, a round produces the solution
  with probability at least `2^{-n + ∑ₓ Pr_π[x forced]}`.
* `Cslib.Complexity.PPZ.run_apply_restrict`: a round in a fixed order produces the solution with
  probability `2^{-u}`.
* `Cslib.Complexity.PPZ.exists_critical_of_flip`: a variable whose flip falsifies the formula
  has a critical clause.
* `Cslib.Complexity.PPZ.exists_critical`: critical clauses of a uniquely satisfiable formula.
* `Cslib.Complexity.PPZ.card_isLast_mul`: a fixed variable comes last among `m` variables in a
  `1 / m` fraction of the orders.
* `Cslib.Complexity.PPZ.round_apply_ge`: PPZ outputs a satisfying assignment `σ` with probability
  at least `2^{-(n - |I| / k)}` when the flips of the variables in `I` falsify the formula.
* `Cslib.Complexity.PPZ.round_success`: PPZ finds the unique satisfying assignment of a k-CNF
  formula with probability at least `2^{-(1 - 1/k) n}`.
* `Cslib.Complexity.PPZ.round_success_of_satisfiable`: PPZ finds a satisfying assignment of a
  satisfiable k-CNF formula with probability at least `2^{-(1 - 1/k) n}`.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PPZ1997]
* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
-/

@[expose] public section

namespace Cslib.Complexity.PPZ

open Cslib.Logic.PL Finset

variable {n : ℕ}

/-! ### The algorithm -/

/-- The clause `c` is a unit clause on `x` with polarity `b` under the partial assignment `τ`:
it has a literal `(x, b)`, every literal on `x` has polarity `b`, and `τ` falsifies every other
literal. -/
def IsUnitOn (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (c : Clause (Fin n)) : Prop :=
  (∃ l ∈ c, l.1 = x ∧ l.2 = b) ∧ ∀ l ∈ c, if l.1 = x then l.2 = b else τ l.1 = some (!l.2)

instance (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (c : Clause (Fin n)) :
    Decidable (IsUnitOn τ x b c) := by
  unfold IsUnitOn
  infer_instance

/-- The value forced on `x` under `τ` by a unit clause of `φ`, if any. -/
def forced (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) : Option Bool :=
  if ∃ c ∈ φ, IsUnitOn τ x true c then some true
  else if ∃ c ∈ φ, IsUnitOn τ x false c then some false else none

/-- One step on `x` with the oracle `O`: the value `O τ x` if there is one, and a uniform bit
otherwise. PPZ uses unit clauses as the oracle (`step`); PPSZ uses bounded implication
(`Cslib.Complexity.PPSZ.step`). -/
noncomputable def stepWith (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (τ : Fin n → Option Bool) (x : Fin n) : PMF Bool :=
  match O τ x with
  | some b => PMF.pure b
  | none => Cslib.Probability.PMF.uniformOfFintype Bool

/-- **The first `i` steps of a round with the oracle `O`** in the order `π`: the variable `π j` is
processed at step `j`. -/
noncomputable def runWith (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (π : Equiv.Perm (Fin n)) : ℕ → PMF (Fin n → Option Bool)
  | 0 => PMF.pure fun _ => none
  | i + 1 =>
    if h : i < n then
      (runWith O π i).bind fun τ =>
        (stepWith O τ (π ⟨i, h⟩)).map fun b => Function.update τ (π ⟨i, h⟩) (some b)
    else runWith O π i

/-- **One round with the oracle `O`**: process all variables in a uniformly random order. -/
noncomputable def roundWith (O : (Fin n → Option Bool) → Fin n → Option Bool) :
    PMF (Fin n → Option Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin n))).bind fun π => runWith O π n

/-- One step of PPZ on `x`: the forced value if there is one, and a uniform bit otherwise. -/
noncomputable def step (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) : PMF Bool :=
  stepWith (forced φ) τ x

/-- **The first `i` steps of a PPZ round** in the order `π`: the variable `π j` is processed at
step `j`. -/
noncomputable def run (φ : CNF (Fin n)) (π : Equiv.Perm (Fin n)) : ℕ → PMF (Fin n → Option Bool) :=
  runWith (forced φ) π

/-- **One round of PPZ**: process all variables in a uniformly random order. -/
noncomputable def round (φ : CNF (Fin n)) : PMF (Fin n → Option Bool) :=
  roundWith (forced φ)

/-- A step on a variable with an oracle value sets it to that value. -/
theorem stepWith_of_eq_some {O : (Fin n → Option Bool) → Fin n → Option Bool}
    {τ : Fin n → Option Bool} {x : Fin n} {b : Bool} (h : O τ x = some b) :
    stepWith O τ x = PMF.pure b := by
  simp only [stepWith, h]

/-- A step on a variable without an oracle value chooses a uniform bit. -/
theorem stepWith_of_eq_none {O : (Fin n → Option Bool) → Fin n → Option Bool}
    {τ : Fin n → Option Bool} {x : Fin n} (h : O τ x = none) :
    stepWith O τ x = Cslib.Probability.PMF.uniformOfFintype Bool := by
  simp only [stepWith, h]

/-- A run of no steps assigns nothing. -/
theorem runWith_zero (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (π : Equiv.Perm (Fin n)) : runWith O π 0 = PMF.pure fun _ => none := by
  simp only [runWith]

/-- Step `i` of a run processes the variable `π i`. -/
theorem runWith_succ (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (π : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    runWith O π (i + 1) = (runWith O π i).bind fun τ =>
      (stepWith O τ (π ⟨i, h⟩)).map fun b => Function.update τ (π ⟨i, h⟩) (some b) := by
  simp only [runWith, h, ↓reduceDIte]

/-- A run stops after all `n` variables are processed. -/
theorem runWith_succ_of_le (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (π : Equiv.Perm (Fin n)) {i : ℕ} (h : n ≤ i) : runWith O π (i + 1) = runWith O π i := by
  simp only [runWith, show ¬ i < n by omega, ↓reduceDIte]

/-! ### Runs that agree with the solution -/

/-- The variables processed in the first `i` steps of the order `π`. -/
def prefixSet (π : Equiv.Perm (Fin n)) (i : ℕ) : Finset (Fin n) :=
  univ.filter fun x => (π.symm x : ℕ) < i

/-- The restriction of `σ` to `D`. -/
def restrict (σ : Fin n → Bool) (D : Finset (Fin n)) : Fin n → Option Bool :=
  fun y => if y ∈ D then some (σ y) else none

/-- **Forced values are correct.** If `σ` satisfies `φ` and `τ` agrees with `σ` where defined, every
value forced under `τ` is the value of `σ`. -/
theorem forced_eq {φ : CNF (Fin n)} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    {τ : Fin n → Option Bool} (hτ : ∀ y b, τ y = some b → σ y = b) {x : Fin n} {b : Bool}
    (h : forced φ τ x = some b) : σ x = b := by
  have key : ∀ b, (∃ c ∈ φ, IsUnitOn τ x b c) → σ x = b := by
    rintro b ⟨c, hc, -, hall⟩
    obtain ⟨l, hl, hls⟩ := (Clause.eval_eq_true_iff σ c).mp ((CNF.eval_eq_true_iff σ φ).mp hσ c hc)
    have := hall l hl
    split_ifs at this with hx
    · rw [← hx, hls, this]
    · have := hτ _ _ this
      rw [hls] at this
      cases l.2 <;> simp at this
  unfold forced at h
  split_ifs at h with h1 h2
  · cases h; exact key true h1
  · cases h; exact key false h2

theorem mem_prefixSet {π : Equiv.Perm (Fin n)} {i : ℕ} {x : Fin n} :
    x ∈ prefixSet π i ↔ (π.symm x : ℕ) < i := by
  simp [prefixSet]

/-- A restriction of `σ` agrees with `σ` where it is defined. -/
theorem eq_of_restrict_eq_some {σ : Fin n → Bool} {D : Finset (Fin n)} {y : Fin n} {b : Bool}
    (h : restrict σ D y = some b) : σ y = b := by
  simp only [restrict] at h
  split_ifs at h
  exact Option.some_injective _ h

/-- Once all `n` variables are processed, the restriction of `σ` is all of `σ`. -/
theorem restrict_prefixSet_self (σ : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    restrict σ (prefixSet π n) = fun x => some (σ x) := by
  funext y
  simp [restrict, mem_prefixSet]

/-- Restricting `σ` to one more variable `x` sets `x` to `σ x`. -/
theorem restrict_insert (σ : Fin n → Bool) (D : Finset (Fin n)) (x : Fin n) :
    restrict σ (insert x D) = Function.update (restrict σ D) x (some (σ x)) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [restrict]
  · simp [restrict, hy]

/-! ### Prefixes of an order -/

/-- The variables processed in the first `i` steps are those at positions below `i`. -/
theorem mem_prefixSet_iff_exists {π : Equiv.Perm (Fin n)} {i : ℕ} {x : Fin n} :
    x ∈ prefixSet π i ↔ ∃ j : Fin n, (j : ℕ) < i ∧ π j = x := by
  rw [mem_prefixSet]
  constructor
  · intro h
    exact ⟨π.symm x, h, π.apply_symm_apply x⟩
  · rintro ⟨j, hj, rfl⟩
    rwa [Equiv.symm_apply_apply]

/-- No variable is processed in zero steps. -/
theorem prefixSet_zero (π : Equiv.Perm (Fin n)) : prefixSet π 0 = ∅ := by
  ext x
  simp [mem_prefixSet]

/-- All variables are processed in `n` steps. -/
theorem prefixSet_self (π : Equiv.Perm (Fin n)) : prefixSet π n = univ := by
  ext x
  simp [mem_prefixSet]

/-- The variable at position `i` is not processed in the first `i` steps. -/
theorem apply_notMem_prefixSet_self (π : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) :
    π ⟨i, hi⟩ ∉ prefixSet π i := by
  rw [mem_prefixSet, Equiv.symm_apply_apply]
  exact lt_irrefl i

/-- Step `i` adds the variable at position `i`. -/
theorem prefixSet_succ (π : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) :
    prefixSet π (i + 1) = insert (π ⟨i, hi⟩) (prefixSet π i) := by
  ext x
  rw [mem_insert, mem_prefixSet, mem_prefixSet, ← Equiv.symm_apply_eq, Fin.ext_iff]
  have : ((⟨i, hi⟩ : Fin n) : ℕ) = i := rfl
  omega

/-- The first `i ≤ n` steps process `i` variables. -/
theorem card_prefixSet (π : Equiv.Perm (Fin n)) : ∀ {i : ℕ}, i ≤ n → (prefixSet π i).card = i
  | 0, _ => by rw [prefixSet_zero, card_empty]
  | i + 1, hi => by
    rw [prefixSet_succ π (by omega : i < n),
      card_insert_of_notMem (apply_notMem_prefixSet_self π _), card_prefixSet π (by omega)]

/-- The order `π` agrees with `π₀` on the first `i` positions. -/
def EqOnPrefix (π π₀ : Equiv.Perm (Fin n)) (i : ℕ) : Prop :=
  ∀ j : Fin n, (j : ℕ) < i → π j = π₀ j

/-- Agreement on a prefix is decidable. -/
instance (π π₀ : Equiv.Perm (Fin n)) (i : ℕ) : Decidable (EqOnPrefix π π₀ i) :=
  inferInstanceAs (Decidable (∀ j : Fin n, (j : ℕ) < i → π j = π₀ j))

/-- Orders that agree on the first `i` positions process the same variables in the first `i`
steps. -/
theorem EqOnPrefix.prefixSet_eq {π π₀ : Equiv.Perm (Fin n)} {i : ℕ} (h : EqOnPrefix π π₀ i) :
    prefixSet π i = prefixSet π₀ i := by
  ext x
  simp only [mem_prefixSet_iff_exists]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (h j hj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, h j hj⟩

/-- An order that agrees with `π₀` on the first `i` positions has at position `i` a variable that
`π₀` does not process in its first `i` steps. -/
theorem EqOnPrefix.apply_notMem_prefixSet {π π₀ : Equiv.Perm (Fin n)} {i : ℕ}
    (h : EqOnPrefix π π₀ i) (hi : i < n) : π ⟨i, hi⟩ ∉ prefixSet π₀ i := by
  rw [← h.prefixSet_eq]
  exact apply_notMem_prefixSet_self π hi

/-- The orders that agree with `π₀` on the first `i` positions and have `y` at position `i` are
those that agree on the first `i + 1` positions with `π₀` followed by the swap of `y` with the
variable of `π₀` at position `i`. -/
theorem eqOnPrefix_swap_iff {π π₀ : Equiv.Perm (Fin n)} {i : ℕ} (hi : i < n) {y : Fin n}
    (hy : y ∉ prefixSet π₀ i) :
    EqOnPrefix π (Equiv.swap (π₀ ⟨i, hi⟩) y * π₀) (i + 1) ↔
      EqOnPrefix π π₀ i ∧ π ⟨i, hi⟩ = y := by
  have hlt : ∀ j : Fin n, (j : ℕ) < i → (Equiv.swap (π₀ ⟨i, hi⟩) y * π₀) j = π₀ j := by
    intro j hj
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne]
    · exact fun h => Nat.ne_of_lt hj (congrArg Fin.val (π₀.injective h))
    · exact fun h => hy (by rw [← h]; exact mem_prefixSet_iff_exists.2 ⟨j, hj, rfl⟩)
  have hi' : (Equiv.swap (π₀ ⟨i, hi⟩) y * π₀) ⟨i, hi⟩ = y := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  constructor
  · intro h
    exact ⟨fun j hj => (h j (by omega)).trans (hlt j hj),
      (h ⟨i, hi⟩ (Nat.lt_succ_self i)).trans hi'⟩
  · rintro ⟨h, hπ⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [h j hj, hlt j hj]
    · obtain rfl : j = ⟨i, hi⟩ := Fin.ext hj
      rw [hπ, hi']

/-- The first `i + 1` steps of `π₀` followed by the swap of `y` with the variable at position `i`
process the first `i` variables of `π₀` and `y`. -/
theorem prefixSet_swap {π₀ : Equiv.Perm (Fin n)} {i : ℕ} (hi : i < n) {y : Fin n}
    (hy : y ∉ prefixSet π₀ i) :
    prefixSet (Equiv.swap (π₀ ⟨i, hi⟩) y * π₀) (i + 1) = insert y (prefixSet π₀ i) := by
  obtain ⟨h, hπ⟩ := (eqOnPrefix_swap_iff (π := Equiv.swap (π₀ ⟨i, hi⟩) y * π₀) hi hy).1
    fun _ _ => rfl
  rw [prefixSet_succ _ hi, hπ, h.prefixSet_eq]

/-! ### Runs in a fixed order -/

/-- A run only assigns the variables it has processed. -/
theorem eq_none_of_mem_support_runWith {O : (Fin n → Option Bool) → Fin n → Option Bool}
    {π : Equiv.Perm (Fin n)} {i : ℕ} {τ : Fin n → Option Bool} (hτ : τ ∈ (runWith O π i).support)
    {y : Fin n} (hy : y ∉ prefixSet π i) : τ y = none := by
  induction i generalizing τ with
  | zero =>
    rw [runWith_zero, PMF.support_pure, Set.mem_singleton_iff] at hτ
    rw [hτ]
  | succ i ih =>
    by_cases h : i < n
    · rw [runWith_succ O π h, PMF.mem_support_bind_iff] at hτ
      obtain ⟨τ', hτ', hmap⟩ := hτ
      rw [PMF.support_map] at hmap
      obtain ⟨b, -, rfl⟩ := hmap
      have hyx : y ≠ π ⟨i, h⟩ := by
        intro e
        apply hy
        rw [mem_prefixSet, e, Equiv.symm_apply_apply]
        simp
      dsimp only
      rw [Function.update_of_ne hyx]
      exact ih hτ' fun hy' => hy (by rw [mem_prefixSet] at hy' ⊢; omega)
    · rw [runWith_succ_of_le O π (by omega)] at hτ
      exact ih hτ fun hy' => hy (by rw [mem_prefixSet] at hy' ⊢; omega)

/-- A run of PPZ only assigns the variables it has processed. -/
theorem eq_none_of_mem_support_run {φ : CNF (Fin n)} {π : Equiv.Perm (Fin n)} {i : ℕ}
    {τ : Fin n → Option Bool} (hτ : τ ∈ (run φ π i).support) {y : Fin n}
    (hy : y ∉ prefixSet π i) : τ y = none :=
  eq_none_of_mem_support_runWith hτ hy

/-- The number of variables without an oracle value among the first `i` steps of the run with the
oracle `O` that agrees with `σ`: at these steps the run chooses a uniform bit. -/
def unforcedCountWith (O : (Fin n → Option Bool) → Fin n → Option Bool) (σ : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  (univ.filter fun j : Fin n => (j : ℕ) < i ∧ O (restrict σ (prefixSet π j)) (π j) = none).card

/-- The number of unforced variables among the first `i` steps of a run that agrees with `σ`. -/
def unforcedCount (φ : CNF (Fin n)) (σ : Fin n → Bool) (π : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  unforcedCountWith (forced φ) σ π i

/-- Step `i` adds one to the count if the oracle has no value for the variable at position `i`. -/
theorem unforcedCountWith_succ (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (σ : Fin n → Bool) (π : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    unforcedCountWith O σ π (i + 1) = unforcedCountWith O σ π i +
      if O (restrict σ (prefixSet π i)) (π ⟨i, h⟩) = none then 1 else 0 := by
  unfold unforcedCountWith
  have hsplit : (univ.filter fun j : Fin n =>
      (j : ℕ) < i + 1 ∧ O (restrict σ (prefixSet π j)) (π j) = none) =
      (univ.filter fun j : Fin n =>
        (j : ℕ) < i ∧ O (restrict σ (prefixSet π j)) (π j) = none) ∪
      (univ.filter fun j : Fin n =>
        (j : ℕ) = i ∧ O (restrict σ (prefixSet π j)) (π j) = none) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : (j : ℕ) < i
      · exact Or.inl ⟨h3, h2⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by omega, h2⟩
  rw [hsplit, card_union_of_disjoint (disjoint_filter.mpr fun j _ h1 h2 => by omega)]
  congr 1
  split_ifs with hU
  · rw [card_eq_one]
    refine ⟨⟨i, h⟩, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hj, -⟩
      exact Fin.ext hj
    · rintro rfl
      exact ⟨rfl, hU⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro j - ⟨hj, hU'⟩
    obtain rfl : j = ⟨i, h⟩ := Fin.ext hj
    exact hU hU'

/-- **A run in a fixed order produces the solution with probability `2^{-u}`**, after
[Paturi, Pudlák, Saks, Zane, Lemma 1][PaturiPudlakSaksZane2005], where `u` counts the variables
without an oracle value along the run that agrees with `σ`. The oracle must be sound along `σ`:
under every partial assignment that agrees with `σ`, its values are those of `σ`. The source draws
the random bits up front and characterises the bit strings that lead to `σ`; here the bits are
drawn during the run, and the probability is computed directly. -/
theorem runWith_apply_restrict {O : (Fin n → Option Bool) → Fin n → Option Bool}
    {σ : Fin n → Bool}
    (hO : ∀ τ, (∀ y b, τ y = some b → σ y = b) → ∀ x b, O τ x = some b → σ x = b)
    (π : Equiv.Perm (Fin n)) {i : ℕ} (hi : i ≤ n) :
    runWith O π i (restrict σ (prefixSet π i)) = (2⁻¹ : ENNReal) ^ unforcedCountWith O σ π i := by
  induction i with
  | zero =>
    have : restrict σ (prefixSet π 0) = fun _ => none := by
      funext y
      simp [restrict, prefixSet_zero]
    simp [runWith_zero, this, unforcedCountWith]
  | succ i ih =>
    have h : i < n := by omega
    set x := π ⟨i, h⟩
    set T := restrict σ (prefixSet π i)
    set T' := restrict σ (prefixSet π (i + 1))
    have hxi : x ∉ prefixSet π i := apply_notMem_prefixSet_self π h
    have hT'x : T' = Function.update T x (some (σ x)) := by
      change restrict σ (prefixSet π (i + 1)) =
        Function.update (restrict σ (prefixSet π i)) (π ⟨i, h⟩) (some (σ (π ⟨i, h⟩)))
      rw [prefixSet_succ π h, restrict_insert]
    rw [runWith_succ O π h, PMF.bind_apply, tsum_eq_single T]
    · rw [PMF.map_apply, tsum_eq_single (σ x)]
      · rw [ite_eq_left hT'x, ih (by omega), unforcedCountWith_succ O σ π h, pow_add]
        congr 1
        split_ifs with hU
        · rw [stepWith_of_eq_none hU]
          simp [Cslib.Probability.PMF.uniformOfFintype_apply]
        · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hU
          rw [stepWith_of_eq_some hb, hO T (fun _ _ => eq_of_restrict_eq_some) x b hb]
          simp
      · intro b hb
        rw [ite_eq_right]
        intro e
        have := congrFun e x
        rw [hT'x, Function.update_self, Function.update_self] at this
        exact hb (Option.some_injective _ this).symm
    · intro τ hτ
      by_cases hsupp : τ ∈ (runWith O π i).support
      · rw [PMF.map_apply]
        convert mul_zero _
        refine ENNReal.tsum_eq_zero.mpr fun b => ite_eq_right fun e => hτ ?_
        funext y
        by_cases hy : y = x
        · subst hy
          rw [eq_none_of_mem_support_runWith hsupp hxi]
          simp [T, restrict, hxi]
        · have := congrFun e y
          rw [Function.update_of_ne hy, hT'x, Function.update_of_ne hy] at this
          exact this.symm
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hsupp, zero_mul]

/-- **A PPZ run in a fixed order produces the solution with probability `2^{-u}`**, where `u`
counts the unforced variables along the run that agrees with `σ`. -/
theorem run_apply_restrict {φ : CNF (Fin n)} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    (π : Equiv.Perm (Fin n)) {i : ℕ} (hi : i ≤ n) :
    run φ π i (restrict σ (prefixSet π i)) = (2⁻¹ : ENNReal) ^ unforcedCount φ σ π i :=
  runWith_apply_restrict (fun _ hτ _ _ h => forced_eq hσ hτ h) π hi

/-! ### Averaging over the orders -/

/-- **The success probability is an average over the orders**, after
[Paturi, Pudlák, Saks, Zane, Lemma 2][PaturiPudlakSaksZane2005]: for an oracle that is sound along
`σ`, one round outputs `σ` with probability `(1/n!) ∑_π 2^{-u(π)}`, where `u(π)` counts the
variables without an oracle value in the order `π`. -/
theorem roundWith_apply_eq {O : (Fin n → Option Bool) → Fin n → Option Bool} {σ : Fin n → Bool}
    (hO : ∀ τ, (∀ y b, τ y = some b → σ y = b) → ∀ x b, O τ x = some b → σ x = b) :
    ((roundWith O) fun x => some (σ x)).toReal =
      ∑ π : Equiv.Perm (Fin n),
        ((n.factorial : ℝ))⁻¹ * (1 / 2 : ℝ) ^ unforcedCountWith O σ π n := by
  rw [roundWith, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (fun π _ => ENNReal.mul_ne_top
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  refine sum_congr rfl fun π _ => ?_
  rw [← restrict_prefixSet_self σ π, runWith_apply_restrict hO π le_rfl, ENNReal.toReal_mul,
    Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_perm, Fintype.card_fin, ENNReal.toReal_pow, ENNReal.toReal_inv]
  norm_num

/-- The variables without an oracle value along a whole run are those whose predecessors in the
order, set as in `σ`, give them no oracle value. -/
theorem unforcedCountWith_eq_card (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (σ : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    unforcedCountWith O σ π n =
      (univ.filter fun x => O (restrict σ (prefixSet π (π.symm x))) x = none).card := by
  unfold unforcedCountWith
  refine card_bij' (fun j _ => π j) (fun x _ => π.symm x) (fun j hj => ?_) (fun x hx => ?_)
    (fun j _ => by simp) (fun x _ => by simp)
  · simp only [mem_filter, mem_univ, true_and] at hj ⊢
    rw [Equiv.symm_apply_apply]
    exact hj.2
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    refine ⟨(π.symm x).isLt, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact hx

/-- **The success probability in terms of forcing probabilities**, after
[Paturi, Pudlák, Saks, Zane, Lemma 3][PaturiPudlakSaksZane2005]: for an oracle that is sound
along `σ`, one round outputs `σ` with probability at least `2^{-n + ∑ₓ Pr_π[x forced]}`, where
`Pr_π[x forced]` is the fraction of the `n!` orders in which the values of `σ` on the variables
before `x` give `x` an oracle value. The proof applies the arithmetic–geometric mean inequality
to `roundWith_apply_eq`. -/
theorem roundWith_apply_ge {O : (Fin n → Option Bool) → Fin n → Option Bool} {σ : Fin n → Bool}
    (hO : ∀ τ, (∀ y b, τ y = some b → σ y = b) → ∀ x b, O τ x = some b → σ x = b) :
    (2 : ℝ) ^ (-(n : ℝ) + ∑ x : Fin n, ((univ.filter fun π : Equiv.Perm (Fin n) =>
        O (restrict σ (prefixSet π (π.symm x))) x ≠ none).card : ℝ) / n.factorial) ≤
      ((roundWith O) fun x => some (σ x)).toReal := by
  set N := n.factorial
  set c : Fin n → ℝ := fun x => ((univ.filter fun π : Equiv.Perm (Fin n) =>
    O (restrict σ (prefixSet π (π.symm x))) x ≠ none).card : ℝ)
  set u : Equiv.Perm (Fin n) → ℕ := fun π => unforcedCountWith O σ π n
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.factorial_pos n
  have hcardPerm : (univ : Finset (Equiv.Perm (Fin n))).card = N := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
  -- The average number of variables without an oracle value is `n - ∑ₓ Pr_π[x forced]`.
  have hswap : ∑ π : Equiv.Perm (Fin n), (u π : ℝ) = ∑ x : Fin n, ((N : ℝ) - c x) := by
    calc
      ∑ π : Equiv.Perm (Fin n), (u π : ℝ) = ∑ π : Equiv.Perm (Fin n),
          ((univ.filter fun x => O (restrict σ (prefixSet π (π.symm x))) x = none).card : ℝ) := by
        simp only [u, unforcedCountWith_eq_card]
      _ = ∑ x : Fin n, ((univ.filter fun π : Equiv.Perm (Fin n) =>
          O (restrict σ (prefixSet π (π.symm x))) x = none).card : ℝ) := by
        simp only [card_filter]
        push_cast
        rw [sum_comm]
      _ = ∑ x : Fin n, ((N : ℝ) - c x) := by
        refine sum_congr rfl fun x _ => ?_
        rw [eq_sub_iff_add_eq, ← Nat.cast_add, ← hcardPerm,
          ← card_filter_add_card_filter_not (s := univ)
            (fun π : Equiv.Perm (Fin n) => O (restrict σ (prefixSet π (π.symm x))) x = none)]
  have havg : ∑ π : Equiv.Perm (Fin n), (N : ℝ)⁻¹ * (u π : ℝ) =
      (n : ℝ) - ∑ x : Fin n, c x / N := by
    rw [← mul_sum, hswap, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← sum_div]
    field_simp
  -- The arithmetic–geometric mean inequality.
  have hw : ∑ _π : Equiv.Perm (Fin n), (N : ℝ)⁻¹ = 1 := by
    rw [sum_const, hcardPerm, nsmul_eq_mul]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted (univ : Finset (Equiv.Perm (Fin n)))
    (fun _ => (N : ℝ)⁻¹) (fun π => (1 / 2 : ℝ) ^ u π) (fun _ _ => by positivity) hw
    (fun _ _ => by positivity)
  have hprod : ∏ π : Equiv.Perm (Fin n), ((1 / 2 : ℝ) ^ u π) ^ (N : ℝ)⁻¹ =
      (1 / 2 : ℝ) ^ ∑ π : Equiv.Perm (Fin n), (N : ℝ)⁻¹ * u π := by
    rw [Real.rpow_sum_of_pos (by norm_num)]
    refine prod_congr rfl fun π _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  rw [roundWith_apply_eq hO]
  calc
    (2 : ℝ) ^ (-(n : ℝ) + ∑ x : Fin n, c x / N) =
        (1 / 2 : ℝ) ^ ((n : ℝ) - ∑ x : Fin n, c x / N) := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow zero_le_two,
        ← Real.rpow_neg zero_le_two, neg_sub, neg_add_eq_sub]
    _ = (1 / 2 : ℝ) ^ ∑ π : Equiv.Perm (Fin n), (N : ℝ)⁻¹ * u π := by rw [havg]
    _ ≤ _ := hprod ▸ hamgm

/-! ### Critical clauses -/

/-- The variables of a clause. -/
def vars (c : Clause (Fin n)) : Finset (Fin n) := (c.map Prod.fst).toFinset

theorem card_vars_le (c : Clause (Fin n)) : (vars c).card ≤ c.length :=
  (List.toFinset_card_le _).trans_eq (List.length_map _)

/-- `c` is a **critical clause** of `x` for `σ`: it contains `x`, the literals on `x` are true under
`σ`, and every other literal is false under `σ`. -/
def IsCritical (σ : Fin n → Bool) (x : Fin n) (c : Clause (Fin n)) : Prop :=
  (∃ l ∈ c, l.1 = x) ∧ ∀ l ∈ c, if l.1 = x then l.2 = σ x else σ l.1 ≠ l.2

/-- **Critical clauses exist** for every variable whose flip falsifies `φ`. -/
theorem exists_critical_of_flip {φ : CNF (Fin n)} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    {x : Fin n} (hflip : φ.eval (Function.update σ x (!σ x)) ≠ true) :
    ∃ c ∈ φ, IsCritical σ x c := by
  set τ := Function.update σ x (!σ x)
  obtain ⟨c, hc, hcτ⟩ : ∃ c ∈ φ, c.eval τ ≠ true := by
    by_contra hall
    push Not at hall
    exact hflip ((CNF.eval_eq_true_iff τ φ).mpr hall)
  have hfalse : ∀ l ∈ c, τ l.1 ≠ l.2 := fun l hl e =>
    hcτ ((Clause.eval_eq_true_iff τ c).mpr ⟨l, hl, e⟩)
  have hall : ∀ l ∈ c, if l.1 = x then l.2 = σ x else σ l.1 ≠ l.2 := by
    intro l hl
    have := hfalse l hl
    split_ifs with hx
    · rw [hx] at this
      simp only [τ, Function.update_self] at this
      cases h1 : l.2 <;> cases h2 : σ x <;> simp_all
    · simpa [τ, Function.update_of_ne hx] using this
  refine ⟨c, hc, ?_, hall⟩
  obtain ⟨l, hl, hls⟩ := (Clause.eval_eq_true_iff σ c).mp ((CNF.eval_eq_true_iff σ φ).mp hσ c hc)
  refine ⟨l, hl, ?_⟩
  by_contra hx
  have := hall l hl
  rw [ite_eq_right hx] at this
  exact this hls

/-- **Critical clauses exist** for every variable of the unique satisfying assignment: flipping
the variable falsifies some clause. -/
theorem exists_critical {φ : CNF (Fin n)} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    (huniq : ∀ τ, φ.eval τ = true → τ = σ) (x : Fin n) : ∃ c ∈ φ, IsCritical σ x c :=
  exists_critical_of_flip hσ fun h => by
    have := congrFun (huniq _ h) x
    simp at this

/-- `x` comes after every other variable of `S` in the order `π`. -/
def IsLast (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (x : Fin n) : Prop :=
  ∀ y ∈ S, y ≠ x → π.symm y < π.symm x

instance (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (x : Fin n) : Decidable (IsLast π S x) := by
  unfold IsLast
  infer_instance

/-- **A variable that comes last in its critical clause is forced.** -/
theorem forced_ne_none_of_isLast {φ : CNF (Fin n)} {σ : Fin n → Bool} {x : Fin n}
    {c : Clause (Fin n)} (hc : c ∈ φ) (hcrit : IsCritical σ x c) {π : Equiv.Perm (Fin n)}
    (hlast : IsLast π (vars c) x) :
    forced φ (restrict σ (prefixSet π (π.symm x))) x ≠ none := by
  have hunit : IsUnitOn (restrict σ (prefixSet π (π.symm x))) x (σ x) c := by
    obtain ⟨⟨l, hl, hlx⟩, hall⟩ := hcrit
    refine ⟨⟨l, hl, hlx, ?_⟩, fun m hm => ?_⟩
    · have := hall l hl
      rwa [ite_eq_left hlx] at this
    · have := hall m hm
      split_ifs with hmx
      · rwa [ite_eq_left hmx] at this
      · rw [ite_eq_right hmx] at this
        have hmem : m.1 ∈ prefixSet π (π.symm x) := by
          rw [mem_prefixSet]
          exact hlast m.1 (List.mem_toFinset.mpr (List.mem_map_of_mem hm)) hmx
        simp only [restrict, hmem, ite_true]
        congr 1
        cases h1 : σ m.1 <;> cases h2 : m.2 <;> simp_all
  unfold forced
  cases hσx : σ x
  · rw [hσx] at hunit
    split_ifs with h1 h2
    · simp
    · simp
    · exact absurd ⟨c, hc, hunit⟩ h2
  · rw [hσx] at hunit
    rw [ite_eq_left ⟨c, hc, hunit⟩]
    simp

/-! ### Random orders -/

/-- Swapping two variables of `S` exchanges which of them comes last. -/
private theorem isLast_trans_swap {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)} {x y : Fin n}
    (hx : x ∈ S) (hy : y ∈ S) : IsLast (π.trans (Equiv.swap x y)) S y ↔ IsLast π S x := by
  unfold IsLast
  simp only [Equiv.symm_trans_apply, Equiv.symm_swap, Equiv.swap_apply_right]
  constructor
  · intro h v hv hvx
    have := h (Equiv.swap x y v) ?_ ?_
    · rwa [Equiv.swap_apply_self] at this
    · by_cases hvy : v = y
      · subst hvy
        simpa using hx
      · rw [Equiv.swap_apply_of_ne_of_ne hvx hvy]
        exact hv
    · intro e
      apply hvx
      have := congrArg (Equiv.swap x y) e
      simpa using this
  · intro h v hv hvy
    apply h (Equiv.swap x y v)
    · by_cases hvx : v = x
      · subst hvx
        simpa using hy
      · rw [Equiv.swap_apply_of_ne_of_ne hvx hvy]
        exact hv
    · intro e
      apply hvy
      have := congrArg (Equiv.swap x y) e
      simpa using this

/-- **Each variable of `S` comes last in a `1 / |S|` fraction of the orders.** -/
theorem card_isLast_mul {S : Finset (Fin n)} {x : Fin n} (hx : x ∈ S) :
    (univ.filter fun π : Equiv.Perm (Fin n) => IsLast π S x).card * S.card = n.factorial := by
  classical
  have hinv : ∀ (π : Equiv.Perm (Fin n)) (y : Fin n),
      (π.trans (Equiv.swap x y)).trans (Equiv.swap x y) = π := by
    intro π y
    ext i
    simp
  have hequal : ∀ y ∈ S, (univ.filter fun π : Equiv.Perm (Fin n) => IsLast π S y).card =
      (univ.filter fun π : Equiv.Perm (Fin n) => IsLast π S x).card := by
    intro y hy
    refine card_bij' (fun π _ => π.trans (Equiv.swap x y)) (fun π _ => π.trans (Equiv.swap x y))
      (fun π hπ => ?_) (fun π hπ => ?_) (fun π _ => hinv π y) (fun π _ => hinv π y)
    · simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      have := isLast_trans_swap (π := π.trans (Equiv.swap x y)) hx hy
      rw [hinv] at this
      exact this.mp hπ
    · simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      exact (isLast_trans_swap hx hy).mpr hπ
  -- Every order has exactly one last variable of `S`.
  have hone : ∀ π : Equiv.Perm (Fin n), (S.filter fun y => IsLast π S y).card = 1 := by
    intro π
    obtain ⟨y, hyS, hymax⟩ := S.exists_max_image (fun v => π.symm v) ⟨x, hx⟩
    rw [card_eq_one]
    refine ⟨y, ?_⟩
    ext v
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hvS, hvlast⟩
      by_contra hvy
      have h1 := hvlast y hyS (Ne.symm hvy)
      have h2 := hymax v hvS
      exact absurd h1 (not_lt.mpr h2)
    · rintro rfl
      refine ⟨hyS, fun v hv hvy => lt_of_le_of_ne (hymax v hv) ?_⟩
      intro e
      exact hvy (π.symm.injective e)
  have hsum : ∑ y ∈ S, (univ.filter fun π : Equiv.Perm (Fin n) => IsLast π S y).card =
      n.factorial := by
    have hcard : (univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
      rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    calc
      ∑ y ∈ S, (univ.filter fun π : Equiv.Perm (Fin n) => IsLast π S y).card =
          ∑ π : Equiv.Perm (Fin n), (S.filter fun y => IsLast π S y).card := by
        simp only [card_filter]
        rw [sum_comm]
      _ = n.factorial := by
        simp only [hone, sum_const, smul_eq_mul, mul_one]
        exact hcard
  rw [sum_congr rfl hequal, sum_const, smul_eq_mul] at hsum
  rw [mul_comm]
  exact hsum

/-! ### The success probability -/

/-- With critical clauses `C` for the variables of `I`, the unforced variables of a run that agrees
with `σ` are among the variables that are not in `I` or do not come last in their critical
clause. -/
theorem unforcedCount_le {φ : CNF (Fin n)} {σ : Fin n → Bool} {I : Finset (Fin n)}
    {C : Fin n → Clause (Fin n)} (hC : ∀ x ∈ I, C x ∈ φ ∧ IsCritical σ x (C x))
    (π : Equiv.Perm (Fin n)) :
    unforcedCount φ σ π n ≤ (univ.filter fun x => ¬ (x ∈ I ∧ IsLast π (vars (C x)) x)).card := by
  unfold unforcedCount unforcedCountWith
  refine card_le_card_of_injOn (fun j => π j) (fun j hj => ?_) (fun i _ j _ h => π.injective h)
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj ⊢
  rintro ⟨hI, hlast⟩
  have := forced_ne_none_of_isLast (hC (π j) hI).1 (hC (π j) hI).2 hlast
  rw [Equiv.symm_apply_apply] at this
  exact this hj.2

/-- **One satisfying assignment.** Let `σ` satisfy a CNF formula on `n` variables whose clauses have
at most `k ≥ 1` literals, and let `I` be a set of variables whose flips falsify the formula. Then
one round of PPZ outputs `σ` with probability at least `2^{-(n - |I| / k)}`: each variable of `I`
comes last in its critical clause, and is then forced, in at least a `1 / k` fraction of the
orders. -/
theorem round_apply_ge {k : ℕ} (hk : 1 ≤ k) {φ : CNF (Fin n)} {σ : Fin n → Bool}
    (hσ : φ.eval σ = true) {I : Finset (Fin n)}
    (hI : ∀ x ∈ I, φ.eval (Function.update σ x (!σ x)) ≠ true)
    (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (2 : ℝ) ^ (-((n : ℝ) - I.card / k)) ≤ ((round φ) fun x => some (σ x)).toReal := by
  classical
  choose! C hC using fun x hx => exists_critical_of_flip hσ (hI x hx)
  have key := roundWith_apply_ge (O := forced φ) fun _ hτ _ _ h => forced_eq hσ hτ h
  set N := n.factorial
  set c : Fin n → ℝ := fun x => ((univ.filter fun π : Equiv.Perm (Fin n) =>
    forced φ (restrict σ (prefixSet π (π.symm x))) x ≠ none).card : ℝ)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.factorial_pos n
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- Each variable of `I` is forced in at least a `1 / k` fraction of the orders.
  have hterm : ∀ x ∈ I, (1 : ℝ) / k ≤ c x / N := by
    intro x hx
    have hxv : x ∈ vars (C x) := by
      obtain ⟨⟨l, hl, hlx⟩, -⟩ := (hC x hx).2
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, hlx⟩)
    have hvk : ((vars (C x)).card : ℝ) ≤ k := by
      exact_mod_cast (card_vars_le _).trans (hlen _ (hC x hx).1)
    have hmul : ((univ.filter fun π : Equiv.Perm (Fin n) =>
        IsLast π (vars (C x)) x).card : ℝ) * (vars (C x)).card = N := by
      exact_mod_cast card_isLast_mul hxv
    have hsub : (univ.filter fun π : Equiv.Perm (Fin n) => IsLast π (vars (C x)) x) ⊆
        univ.filter fun π : Equiv.Perm (Fin n) =>
          forced φ (restrict σ (prefixSet π (π.symm x))) x ≠ none := by
      intro π hπ
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      exact forced_ne_none_of_isLast (hC x hx).1 (hC x hx).2 hπ
    have hlast : ((univ.filter fun π : Equiv.Perm (Fin n) =>
        IsLast π (vars (C x)) x).card : ℝ) ≤ c x :=
      Nat.cast_le.mpr (card_le_card hsub)
    rw [div_le_div_iff₀ hk0 hN, one_mul]
    calc
      (N : ℝ) = _ * (vars (C x)).card := hmul.symm
      _ ≤ c x * k := by gcongr
  have hsum : (I.card : ℝ) / k ≤ ∑ x : Fin n, c x / N :=
    calc
      (I.card : ℝ) / k = ∑ _x ∈ I, (1 : ℝ) / k := by
        rw [sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ ∑ x ∈ I, c x / N := sum_le_sum hterm
      _ ≤ ∑ x : Fin n, c x / N :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
  refine le_trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) key
  linarith

/-- **The PPZ algorithm for unique k-SAT** [Paturi, Pudlák, Zane][PPZ1997]: if `σ` is the only
satisfying assignment of a CNF formula on `n` variables whose clauses have at most `k ≥ 1` literals,
one round of PPZ outputs `σ` with probability at least `2^{-(1 - 1/k) n}`. -/
theorem round_success {k : ℕ} (hk : 1 ≤ k) {φ : CNF (Fin n)} {σ : Fin n → Bool}
    (hσ : φ.eval σ = true) (huniq : ∀ τ, φ.eval τ = true → τ = σ)
    (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) ≤ ((round φ) fun x => some (σ x)).toReal := by
  have h := round_apply_ge hk hσ (I := univ) (fun x _ hflip => by
    have := congrFun (huniq _ hflip) x
    simp at this) hlen
  rw [card_univ, Fintype.card_fin] at h
  convert h using 2
  ring

/-- **The PPZ algorithm for k-SAT** [Paturi, Pudlák, Zane][PPZ1997]: for every satisfiable CNF
formula on `n` variables whose clauses have at most `k ≥ 1` literals, one round of PPZ outputs a
satisfying assignment with probability at least `2^{-(1 - 1/k) n}`. Each satisfying assignment `σ`
is output with probability at least `2^{-(n - I(σ)/k)}`, where `I(σ)` counts the variables whose
flips falsify the formula, and `∑_σ 2^{I(σ) - n} ≥ 1`
(`Cslib.BitString.two_pow_le_sum_two_pow_isolation`). -/
theorem round_success_of_satisfiable {k : ℕ} (hk : 1 ≤ k) {φ : CNF (Fin n)}
    (hsat : φ.Satisfiable) (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) ≤
      ((round φ).toOuterMeasure {τ | ∃ σ, φ.eval σ = true ∧ τ = fun x => some (σ x)}).toReal := by
  classical
  set S : Finset (Fin n → Bool) := univ.filter fun σ => φ.eval σ = true
  have hS : S.Nonempty := let ⟨σ, hσ⟩ := hsat; ⟨σ, by simp [S, hσ]⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set g : (Fin n → Bool) → (Fin n → Option Bool) := fun σ x => some (σ x)
  have hg : Function.Injective g := fun σ τ h => funext fun x =>
    Option.some_injective _ (congrFun h x)
  -- The event contains the images of the satisfying assignments.
  have hevent : ∑ σ ∈ S, ((round φ) (g σ)).toReal ≤
      ((round φ).toOuterMeasure {τ | ∃ σ, φ.eval σ = true ∧ τ = fun x => some (σ x)}).toReal := by
    rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal,
      ← sum_image (f := fun τ => ((round φ) τ).toReal) fun σ _ τ _ h => hg h]
    refine le_trans (le_of_eq (sum_congr rfl fun τ hτ => ?_))
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun τ _ _ => ?_)
    · obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hτ
      have : g σ ∈ {τ | ∃ σ, φ.eval σ = true ∧ τ = fun x => some (σ x)} :=
        ⟨σ, (mem_filter.mp hσ).2, rfl⟩
      simp only [this, ite_true]
    · split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
  -- Each satisfying assignment contributes `2^{-(1 - 1/k) n} · 2^{isolation - n}`.
  have hterm : ∀ σ ∈ S, (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) *
      ((2 : ℝ) ^ (Cslib.BitString.isolation S σ) / 2 ^ n) ≤ ((round φ) (g σ)).toReal := by
    intro σ hσ
    set I := univ.filter fun x => Function.update σ x (!σ x) ∉ S
    have hI : ∀ x ∈ I, φ.eval (Function.update σ x (!σ x)) ≠ true := by
      intro x hx
      simpa [I, S] using hx
    refine le_trans ?_ (round_apply_ge hk (mem_filter.mp hσ).2 hI hlen)
    have hiso : (Cslib.BitString.isolation S σ : ℝ) = I.card := rfl
    have hIn : (I.card : ℝ) ≤ n := by exact_mod_cast (card_le_univ I).trans_eq (Fintype.card_fin n)
    rw [← Real.rpow_natCast 2 (Cslib.BitString.isolation S σ), ← Real.rpow_natCast 2 n,
      ← Real.rpow_sub two_pos, ← Real.rpow_add two_pos, hiso]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have : ((I.card : ℝ) - n) ≤ ((I.card : ℝ) - n) / k := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hrw : -((n : ℝ) - I.card / k) = -((1 - 1 / (k : ℝ)) * n) + ((I.card : ℝ) - n) / k := by
      field_simp
      ring
    rw [hrw]
    linarith
  -- The isolation inequality.
  have hiso := Cslib.BitString.two_pow_le_sum_two_pow_isolation S hS
  have hisoR : (1 : ℝ) ≤ ∑ σ ∈ S, (2 : ℝ) ^ (Cslib.BitString.isolation S σ) / 2 ^ n := by
    rw [← sum_div, le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast hiso
  calc
    (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) ≤ (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) *
        ∑ σ ∈ S, (2 : ℝ) ^ (Cslib.BitString.isolation S σ) / 2 ^ n :=
      le_mul_of_one_le_right (by positivity) hisoR
    _ = ∑ σ ∈ S, (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) *
        ((2 : ℝ) ^ (Cslib.BitString.isolation S σ) / 2 ^ n) := by rw [mul_sum]
    _ ≤ ∑ σ ∈ S, ((round φ) (g σ)).toReal := sum_le_sum hterm
    _ ≤ _ := hevent

end Cslib.Complexity.PPZ
