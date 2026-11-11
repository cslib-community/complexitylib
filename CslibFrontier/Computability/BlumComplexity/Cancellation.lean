/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.Partrec
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.List.Find
import Mathlib.Order.Filter.Finite

/-!
# Priority cancellation runs

Blum's speedup theorem uses a priority construction, as do many diagonal constructions in
abstract complexity theory. Stage by stage, a run *cancels* indices. At stage `y` it cancels the
least index `i` in `[u, y]` that is *eligible* at `y` and has not been cancelled before. An
*override* predicate can suppress a stage, in which case nothing is cancelled there.

This file defines the run `canc E ov u y` for an arbitrary eligibility predicate `E i y` and
override `ov y`, and proves the facts the speedup construction needs:

* `canc_eq_some`, `canc_eq_none`: the specification of a stage.
* `computable_canc`: the run is computable whenever `E` and `ov` are.
* `canc_congr`: the run up to stage `x` depends only on `E i y` for `u ≤ i ≤ y ≤ x`.
* `eventually_not_eligible`: in a run without overrides, an index that is never cancelled is
  eligible at only finitely many stages.
* `canc_override`: a run started at `u` with overrides exactly at the stages where the run from
  `0` cancels an index below `u` cancels the same indices `≥ u` as the run from `0`.

## Main definitions

* `Cslib.BlumComplexity.Cancellation.canc`: the index cancelled at a stage, if any.

## References

* [M. Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]
-/

public section

namespace Cslib.BlumComplexity.Cancellation

open Filter

/-! ### Bounded search -/

/-- The least `i ∈ [s, s + n)` with `p i`, if any. -/
def bfind (p : ℕ → Bool) (s n : ℕ) : Option ℕ := (List.range' s n).find? p

private theorem bfind_succ (p : ℕ → Bool) (s n : ℕ) :
    bfind p s (n + 1) = match bfind p s n with
      | some i => some i
      | none => if p (s + n) then some (s + n) else none := by
  unfold bfind
  rw [List.range'_concat, List.find?_append]
  cases (List.range' s n).find? p with
  | some i => rfl
  | none => cases h : p (s + n) <;> simp [h]

theorem computable_bfind {α : Type*} [Primcodable α] {p : α → ℕ → Bool} {s n : α → ℕ}
    (hp : Computable₂ p) (hs : Computable s) (hn : Computable n) :
    Computable fun a => bfind (p a) (s a) (n a) := by
  have h : Computable fun a => Nat.rec (motive := fun _ => Option ℕ) (none : Option ℕ)
      (fun k (IH : Option ℕ) => Option.casesOn IH
        (cond (p a (s a + k)) (some (s a + k)) none) some) (n a) := by
    refine Computable.nat_rec (h := fun a (q : ℕ × Option ℕ) => Option.casesOn q.2
      (cond (p a (s a + q.1)) (some (s a + q.1)) none) some) hn
      (Computable.const (Option.none : Option ℕ)) ?_
    refine Computable.option_casesOn (Computable.snd.comp Computable.snd) ?_
      (Computable.option_some.comp Computable.snd).to₂
    refine Computable.cond (hp.comp Computable.fst (Primrec.nat_add.to_comp.comp
      (hs.comp Computable.fst) (Computable.fst.comp Computable.snd))) ?_
      (Computable.const (Option.none : Option ℕ))
    exact Computable.option_some.comp (Primrec.nat_add.to_comp.comp
      (hs.comp Computable.fst) (Computable.fst.comp Computable.snd))
  refine h.of_eq fun a => ?_
  induction n a with
  | zero => rfl
  | succ k ih =>
    rw [bfind_succ, Nat.rec_add_one, ih]
    cases bfind (p a) (s a) k with
    | some i => rfl
    | none => cases p a (s a + k) <;> rfl

theorem bfind_eq_some {p : ℕ → Bool} {s n i : ℕ} :
    bfind p s n = some i ↔ s ≤ i ∧ i < s + n ∧ p i ∧ ∀ j, s ≤ j → j < i → p j = false := by
  unfold bfind
  rw [List.find?_range'_eq_some, List.mem_range'_1]
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨h2, h3, h1, fun j hj hji => by simpa using h4 j hj hji⟩
  · rintro ⟨h2, h3, h1, h4⟩
    exact ⟨h1, ⟨h2, h3⟩, fun j hj hji => by simp [h4 j hj hji]⟩

theorem bfind_eq_none {p : ℕ → Bool} {s n : ℕ} :
    bfind p s n = none ↔ ∀ i, s ≤ i → i < s + n → p i = false := by
  unfold bfind
  rw [List.find?_range'_eq_none]
  simp

theorem bfind_congr {p q : ℕ → Bool} {s n : ℕ} (h : ∀ i, s ≤ i → i < s + n → p i = q i) :
    bfind p s n = bfind q s n := by
  unfold bfind
  exact List.find?_congr fun x hx => h x (List.mem_range'_1.1 hx).1 (List.mem_range'_1.1 hx).2

/-! ### The priority run -/

/-- One stage `y`, given the history `h` of earlier stages. If the override `ov y` is set,
nothing is cancelled. Otherwise the least `i ∈ [u, y]` that is eligible (`E i y`) and was not
cancelled earlier (`some i ∉ h`) is cancelled. -/
private def step (E : ℕ → ℕ → Bool) (ov : ℕ → Bool) (u y : ℕ) (h : List (Option ℕ)) : Option ℕ :=
  cond (ov y) none (bfind (fun i => E i y && !decide (some i ∈ h)) u (y + 1 - u))

/-- The cancellation history of the stages before `y`. -/
private def hist (E : ℕ → ℕ → Bool) (ov : ℕ → Bool) (u : ℕ) : ℕ → List (Option ℕ)
  | 0 => []
  | y + 1 => hist E ov u y ++ [step E ov u y (hist E ov u y)]

/-- The index cancelled at stage `y` of the run with eligibility `E`, override `ov` and least
index `u`, if any. -/
def canc (E : ℕ → ℕ → Bool) (ov : ℕ → Bool) (u y : ℕ) : Option ℕ :=
  step E ov u y (hist E ov u y)

private theorem length_hist (E ov u y) : (hist E ov u y).length = y := by
  induction y with
  | zero => rfl
  | succ y ih => rw [hist, List.length_append, ih, List.length_singleton]

private theorem getElem?_hist (E ov u) {y k : ℕ} (hk : k < y) :
    (hist E ov u y)[k]? = some (canc E ov u k) := by
  induction y with
  | zero => omega
  | succ y ih =>
    rw [hist]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [List.getElem?_append_left (by rw [length_hist]; exact hk), ih hk]
    · rw [List.getElem?_append_right (by rw [length_hist]), length_hist, Nat.sub_self]
      rfl

private theorem mem_hist {E ov u y i} :
    some i ∈ hist E ov u y ↔ ∃ k < y, canc E ov u k = some i := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨k, hk⟩
    have hky : k < y := by
      have := (List.getElem?_eq_some_iff.1 hk).1
      rwa [length_hist] at this
    rw [getElem?_hist E ov u hky] at hk
    exact ⟨k, hky, Option.some_injective _ hk⟩
  · rintro ⟨k, hk, hc⟩
    exact ⟨k, by rw [getElem?_hist E ov u hk, hc]⟩

/-- Stage `y` cancels `i` exactly when there is no override at `y`, `i ∈ [u, y]` is eligible at
`y` and was not cancelled earlier, and every smaller eligible index in `[u, i)` was cancelled
earlier. -/
theorem canc_eq_some {E ov u y i} :
    canc E ov u y = some i ↔ ov y = false ∧ u ≤ i ∧ i ≤ y ∧ E i y = true ∧
      (∀ k < y, canc E ov u k ≠ some i) ∧
      ∀ j, u ≤ j → j < i → E j y = true → ∃ k < y, canc E ov u k = some j := by
  change step E ov u y (hist E ov u y) = some i ↔ _
  unfold step
  cases hov : ov y
  · simp only [Bool.cond_false, bfind_eq_some, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, mem_hist, true_and]
    constructor
    · rintro ⟨h1, h2, ⟨h3, h4⟩, h5⟩
      refine ⟨h1, by omega, h3, fun k hk hc => h4 ⟨k, hk, hc⟩, fun j hj hji hE => ?_⟩
      have := h5 j hj hji
      simp only [Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at this
      rcases this with h | h
      · simp [hE] at h
      · exact h
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, by omega, ⟨h3, fun ⟨k, hk, hc⟩ => h4 k hk hc⟩, fun j hj hji => ?_⟩
      cases hE : E j y
      · simp
      · simp [h5 j hj hji hE]
  · simp

/-- Stage `y` cancels nothing exactly when there is an override at `y` or every eligible index in
`[u, y]` was cancelled earlier. -/
theorem canc_eq_none {E ov u y} :
    canc E ov u y = none ↔ ov y = true ∨
      ∀ i, u ≤ i → i ≤ y → E i y = true → ∃ k < y, canc E ov u k = some i := by
  change step E ov u y (hist E ov u y) = none ↔ _
  unfold step
  cases hov : ov y
  · simp only [Bool.cond_false, bfind_eq_none, Bool.and_eq_false_iff, Bool.not_eq_false',
      decide_eq_true_eq, mem_hist, Bool.false_eq_true, false_or]
    constructor
    · intro h i hu hy hE
      rcases h i hu (by omega) with h | h
      · simp [hE] at h
      · exact h
    · intro h i hu hy
      cases hE : E i y
      · simp
      · exact Or.inr (h i hu (by omega) hE)
  · simp

/-- Each index is cancelled at most once. -/
theorem canc_injective {E ov u y₁ y₂ i} (h₁ : canc E ov u y₁ = some i)
    (h₂ : canc E ov u y₂ = some i) : y₁ = y₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (canc_eq_some.1 h₂).2.2.2.2.1 y₁ h h₁
  · exact (canc_eq_some.1 h₁).2.2.2.2.1 y₂ h h₂

theorem canc_le {E ov u y i} (h : canc E ov u y = some i) : u ≤ i ∧ i ≤ y :=
  ⟨(canc_eq_some.1 h).2.1, (canc_eq_some.1 h).2.2.1⟩

/-- Changing `E` outside `u ≤ i ≤ y ≤ x` does not change the run up to stage `x`. -/
theorem canc_congr {E₁ E₂ : ℕ → ℕ → Bool} {ov : ℕ → Bool} {u x : ℕ}
    (h : ∀ i y, u ≤ i → i ≤ y → y ≤ x → E₁ i y = E₂ i y) :
    ∀ y ≤ x, canc E₁ ov u y = canc E₂ ov u y := by
  have hh : ∀ y ≤ x + 1, hist E₁ ov u y = hist E₂ ov u y := by
    intro y
    induction y with
    | zero => intro; rfl
    | succ y ih =>
      intro hy
      rw [hist, hist, ih (by omega)]
      congr 2
      unfold step
      congr 1
      refine bfind_congr fun i hi hiy => ?_
      rw [h i y hi (by omega) (by omega)]
  intro y hy
  unfold canc
  rw [hh y (by omega)]
  unfold step
  congr 1
  refine bfind_congr fun i hi hiy => ?_
  rw [h i y hi (by omega) hy]

/-- The run is computable, uniformly in a parameter, whenever the eligibility predicate and the
override are. -/
theorem computable_canc {α : Type*} [Primcodable α] {E : α → ℕ → ℕ → Bool}
    {ov : α → ℕ → Bool} {u y : α → ℕ}
    (hE : Computable fun p : α × ℕ × ℕ => E p.1 p.2.1 p.2.2) (hov : Computable₂ ov)
    (hu : Computable u) (hy : Computable y) :
    Computable fun a => canc (E a) (ov a) (u a) (y a) := by
  -- the step as a function of `((a, y), h)`
  have hstep : Computable fun q : (α × ℕ) × List (Option ℕ) =>
      step (E q.1.1) (ov q.1.1) (u q.1.1) q.1.2 q.2 := by
    unfold step
    refine Computable.cond (hov.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst)) (Computable.const none) ?_
    refine computable_bfind (p := fun (q : (α × ℕ) × List (Option ℕ)) i =>
        E q.1.1 i q.1.2 && !decide (some i ∈ q.2)) ?_
      (hu.comp (Computable.fst.comp Computable.fst))
      (Primrec.nat_sub.to_comp.comp (Computable.succ.comp (Computable.snd.comp Computable.fst))
        (hu.comp (Computable.fst.comp Computable.fst)))
    have hmem : Computable fun p : ((α × ℕ) × List (Option ℕ)) × ℕ =>
        decide (some p.2 ∈ p.1.2) := by
      refine (Primrec.nat_lt.decide.comp ((Primrec.list_idxOf (α := Option ℕ)).comp
        (Primrec.option_some.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))).to_comp.of_eq fun p => ?_
      exact decide_eq_decide.2 (@List.idxOf_lt_length_iff _ instBEqOfDecidableEq _ _ _)
    exact (Primrec.and.to_comp.comp (hE.comp (Computable.pair
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.pair Computable.snd (Computable.snd.comp (Computable.fst.comp
        Computable.fst))))) (Primrec.not.to_comp.comp hmem)).to₂
  have hhist : Computable fun p : α × ℕ => hist (E p.1) (ov p.1) (u p.1) p.2 := by
    have : Computable fun p : α × ℕ => Nat.rec (motive := fun _ => List (Option ℕ)) []
        (fun k (IH : List (Option ℕ)) => IH ++ [step (E p.1) (ov p.1) (u p.1) k IH]) p.2 := by
      refine Computable.nat_rec (h := fun (p : α × ℕ) (q : ℕ × List (Option ℕ)) =>
        q.2 ++ [step (E p.1) (ov p.1) (u p.1) q.1 q.2]) Computable.snd (Computable.const []) ?_
      refine (Computable.list_append.comp (Computable.snd.comp Computable.snd)
        (Computable.list_cons.comp (hstep.comp (Computable.pair (Computable.pair
          (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
          (Computable.snd.comp Computable.snd))) (Computable.const []))).to₂
    refine this.of_eq fun p => ?_
    induction p.2 with
    | zero => rfl
    | succ k ih => rw [hist, ← ih]
  exact hstep.comp (Computable.pair (Computable.pair Computable.id hy)
    (hhist.comp (Computable.pair Computable.id hy)))

/-- An eligible index that has not been cancelled yet forces a cancellation at or below it. -/
theorem exists_canc_le {E ov u y j} (hov : ov y = false) (hu : u ≤ j) (hj : j ≤ y)
    (hE : E j y = true) (hnc : ∀ k < y, canc E ov u k ≠ some j) :
    ∃ j' ≤ j, canc E ov u y = some j' := by
  cases h : canc E ov u y with
  | none =>
    rcases canc_eq_none.1 h with h' | h'
    · simp [hov] at h'
    · obtain ⟨k, hk, hc⟩ := h' j hu hj hE
      exact absurd hc (hnc k hk)
  | some j' =>
    refine ⟨j', ?_, rfl⟩
    by_contra hlt
    obtain ⟨k, hk, hc⟩ := (canc_eq_some.1 h).2.2.2.2.2 j hu (by omega) hE
    exact hnc k hk hc

/-- Eventually, no index below `i` is cancelled any more. -/
theorem eventually_canc_ne (E ov u i) : ∀ᶠ y in atTop, ∀ j < i, canc E ov u y ≠ some j := by
  have h : ∀ j, ∀ᶠ y in atTop, canc E ov u y ≠ some j := by
    intro j
    by_cases hex : ∃ y₀, canc E ov u y₀ = some j
    · obtain ⟨y₀, hy₀⟩ := hex
      filter_upwards [eventually_gt_atTop y₀] with y hy hc
      exact absurd (canc_injective hy₀ hc) (Nat.ne_of_lt hy)
    · push Not at hex
      exact Eventually.of_forall hex
  have := (Filter.eventually_all_finset (Finset.range i)).2 fun j _ => h j
  filter_upwards [this] with y hy j hj
  exact hy j (Finset.mem_range.2 hj)

/-- In a run without overrides from `0`, an index that is never cancelled is eligible at only
finitely many stages. -/
theorem eventually_not_eligible {E : ℕ → ℕ → Bool} {i : ℕ}
    (hi : ∀ y, canc E (fun _ => false) 0 y ≠ some i) :
    ∀ᶠ y in atTop, E i y = false := by
  filter_upwards [eventually_canc_ne E (fun _ => false) 0 i, eventually_ge_atTop i]
    with y hy hiy
  by_contra hE
  rw [Bool.not_eq_false] at hE
  obtain ⟨j, hj, hc⟩ := exists_canc_le rfl (Nat.zero_le i) hiy hE fun k _ => hi k
  rcases Nat.lt_or_eq_of_le hj with hj | rfl
  · exact hy j hj hc
  · exact hi y hc

/-- Starting at `u`, with an override exactly at the stages where the run from `0` cancels an
index below `u`, reproduces the cancellations `≥ u` of the run from `0`. -/
theorem canc_override {E : ℕ → ℕ → Bool} {u : ℕ} {ov : ℕ → Bool}
    (hov : ∀ y, ov y = true ↔ ∃ j < u, canc E (fun _ => false) 0 y = some j) :
    ∀ y j, u ≤ j → (canc E ov u y = some j ↔ canc E (fun _ => false) 0 y = some j) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro j hj
  constructor
  · intro h
    obtain ⟨hovy, -, hjy, hE, hnc, hmin⟩ := canc_eq_some.1 h
    refine canc_eq_some.2 ⟨rfl, Nat.zero_le _, hjy, hE, fun k hk hc => hnc k hk
      ((ih k hk j hj).2 hc), fun j' _ hj' hE' => ?_⟩
    rcases le_or_gt u j' with hu | hu
    · obtain ⟨k, hk, hc⟩ := hmin j' hu hj' hE'
      exact ⟨k, hk, (ih k hk j' hu).1 hc⟩
    · by_contra hne
      push Not at hne
      obtain ⟨j'', hj'', hc⟩ := exists_canc_le rfl (Nat.zero_le _) (by omega) hE' hne
      have : ov y = true := (hov y).2 ⟨j'', by omega, hc⟩
      simp [hovy] at this
  · intro h
    obtain ⟨-, -, hjy, hE, hnc, hmin⟩ := canc_eq_some.1 h
    have hovy : ov y = false := by
      by_contra hc
      rw [Bool.not_eq_false, hov] at hc
      obtain ⟨j'', hj'', hc⟩ := hc
      rw [h] at hc
      cases hc
      omega
    refine canc_eq_some.2 ⟨hovy, hj, hjy, hE, fun k hk hc => hnc k hk ((ih k hk j hj).1 hc),
      fun j' hu hj' hE' => ?_⟩
    obtain ⟨k, hk, hc⟩ := hmin j' (Nat.zero_le _) hj' hE'
    exact ⟨k, hk, (ih k hk j' hu).2 hc⟩

end Cslib.BlumComplexity.Cancellation
