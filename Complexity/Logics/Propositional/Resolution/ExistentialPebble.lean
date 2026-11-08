/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Proof

/-!
# The Boolean existential pebble game

**The existential pebble game characterizes resolution width** [Atserias and Dalmau, Lemmas 2 and 3
and Theorem 2][AtseriasDalmau2008]. Atserias and Dalmau characterize resolution width by the Boolean
existential pebble game on a CNF formula `φ`. Spoiler places pebbles on variables, Duplicator
answers with truth values, and Spoiler wins when the pebbled partial assignment falsifies a clause
of `φ`. A **winning strategy for Duplicator with `k` pebbles**
(`Cslib.Logic.PL.CNF.DuplicatorStrategy`, their Definition 2) is a nonempty family of partial
assignments on at most `k` variables that falsify no clause of `φ`, closed under restriction, and
such that each assignment on fewer than `k` variables extends to any further variable.

A partial assignment is a total assignment `σ` read only on a finite set `d` of variables, and
`Cslib.Logic.PL.CNF.Falsifies σ d c` says that every literal of `c` is on a variable of `d` and
false under `σ`.

If Duplicator has a winning strategy with `w + 1` pebbles, then `φ` has no refutation of width `w`
(`Cslib.Logic.PL.CNF.DuplicatorStrategy.not_refutableInWidth`, their Lemma 3). By induction along a
proof of width `w`, no position of the strategy falsifies a line: a position falsifying a resolvent
restricts to the at most `w` variables of the resolvent and extends to the resolved variable, and
the extension falsifies one of the two premises. Since the strategy is nonempty and every position
falsifies the empty clause, the proof is not a refutation.

Conversely, if `φ` has no clause of width exactly `w + 1` and no refutation of width `w`, then
Duplicator wins with `w + 1` pebbles
(`Cslib.Logic.PL.CNF.DuplicatorStrategy.ofNotRefutableInWidth`, their Lemma 2). The positions are
the partial assignments on at most `w + 1` variables that falsify no clause derivable within width
`w`. The empty assignment is one of them. A position on at most `w` variables extends to any
further variable, since if both extensions falsified derivable clauses, their resolvent would be a
derivable clause of width at most `w` falsified by the position. The clauses of `φ` of width at
most `w` are derivable within width `w`, and those of width more than `w + 1` cannot be falsified on
at most `w + 1` variables, so no position falsifies a clause of `φ`. Together, for formulas without
clauses of width `w + 1`, Duplicator wins with `w + 1` pebbles exactly when there is no refutation
of width `w` (`Cslib.Logic.PL.CNF.DuplicatorStrategy.nonempty_iff_not_refutableInWidth`, their
Theorem 2). Clauses of width `w + 1` must be excluded: `(x₀ ∨ x₁ ∨ x₂) ∧ ¬x₀ ∧ ¬x₁ ∧ ¬x₂` has no
refutation of width `2`, but Spoiler wins with `3` pebbles. Duplicator strategies also give
clause-space lower bounds, in `Complexity.Logics.Propositional.Resolution.SpaceWidth`.

The mathematical symbols of the available copy of Atserias and Dalmau's paper do not extract, so
neither the side conditions nor the pebble counts of their statements are quoted. The statements
here are ours, with the off-by-one conventions of the library's
`Cslib.Logic.PL.CNF.RefutableInWidth`. The game is unrelated to the black pebble game of
`Complexity.Computability.Pebbling`.

## Main definitions

* `Cslib.Logic.PL.CNF.Falsifies`: a partial assignment falsifies a clause.
* `Cslib.Logic.PL.CNF.DuplicatorStrategy`: a winning strategy for Duplicator in the Boolean
  existential `k`-pebble game.
* `Cslib.Logic.PL.CNF.DuplicatorStrategy.ofNotRefutableInWidth`: the strategy with `w + 1` pebbles
  on a formula without clauses of width `w + 1` and without refutations of width `w`.

## Main results

* `Cslib.Logic.PL.CNF.DuplicatorStrategy.exists_extend_union`: a position extends to further
  variables, up to the number of pebbles.
* `Cslib.Logic.PL.CNF.DuplicatorStrategy.not_falsifies_of_isProof`: no position falsifies a line of
  a proof of width `w`, for `w + 1` pebbles.
* `Cslib.Logic.PL.CNF.DuplicatorStrategy.not_refutableInWidth`: **a Duplicator strategy with
  `w + 1` pebbles rules out refutations of width `w`**.
* `Cslib.Logic.PL.CNF.DuplicatorStrategy.nonempty_iff_not_refutableInWidth`: **the existential
  pebble game characterizes width**, for formulas without clauses of width `w + 1`.

## References

* [A. Atserias, V. Dalmau, *A combinatorial characterization of resolution
  width*][AtseriasDalmau2008]
-/

public section

namespace Cslib.Logic.PL

open scoped Finset

namespace CNF

variable {V : Type*}

/-- The assignment `σ`, read on `d`, **falsifies** `c`: every literal of `c` is on a variable of
`d` and false under `σ`. -/
@[expose] def Falsifies (σ : V → Bool) (d : Finset V) (c : Clause V) : Prop :=
  ∀ l ∈ c, l.1 ∈ d ∧ σ l.1 ≠ l.2

/-- Falsifying on `d` depends only on the values on `d`. -/
theorem Falsifies.congr {σ τ : V → Bool} {d : Finset V} {c : Clause V} (h : Falsifies σ d c)
    (hστ : ∀ x ∈ d, τ x = σ x) : Falsifies τ d c := fun l hl =>
  ⟨(h l hl).1, by rw [hστ _ (h l hl).1]; exact (h l hl).2⟩

/-- Every partial assignment falsifies the empty clause. -/
@[simp] theorem falsifies_nil (σ : V → Bool) (d : Finset V) : Falsifies σ d [] := by
  simp [Falsifies]

/-- A **winning strategy for Duplicator in the Boolean existential `k`-pebble game** on `φ`
[Atserias and Dalmau, Definition 2][AtseriasDalmau2008]: a nonempty family of partial assignments
`(σ, d)`, read on at most `k` variables, that falsify no clause of `φ`, closed under restriction,
and such that every assignment on fewer than `k` variables extends to any further variable. -/
structure DuplicatorStrategy [DecidableEq V] (φ : CNF V) (k : ℕ) where
  /-- The positions of the strategy: `σ` read on `d`. -/
  Mem : (V → Bool) → Finset V → Prop
  /-- There is a position. -/
  nonempty : ∃ σ d, Mem σ d
  /-- Positions are read on at most `k` variables. -/
  card_le {σ : V → Bool} {d : Finset V} : Mem σ d → #d ≤ k
  /-- Positions are closed under restriction. -/
  restrict {σ : V → Bool} {d e : Finset V} : Mem σ d → e ⊆ d → Mem σ e
  /-- A position on fewer than `k` variables extends to any further variable. -/
  extend {σ : V → Bool} {d : Finset V} : Mem σ d → #d < k → ∀ v, ∃ τ : V → Bool,
    (∀ x ∈ d, τ x = σ x) ∧ Mem τ (insert v d)
  /-- No position falsifies a clause of `φ`. -/
  not_falsifies {σ : V → Bool} {d : Finset V} : Mem σ d → ∀ c ∈ φ, ¬ Falsifies σ d c

namespace DuplicatorStrategy

variable [DecidableEq V] {φ : CNF V} {w : ℕ}

/-- **Extension to a set of variables**: a position of a `k`-pebble strategy on `d` extends to a
position on `d ∪ e` agreeing with it on `d`, provided `|d| + |e| ≤ k`. -/
theorem exists_extend_union {k : ℕ} (S : DuplicatorStrategy φ k) {σ : V → Bool} {d : Finset V}
    (hσ : S.Mem σ d) (e : Finset V) (hde : #d + #e ≤ k) :
    ∃ σ', S.Mem σ' (d ∪ e) ∧ ∀ x ∈ d, σ' x = σ x := by
  induction e using Finset.induction_on with
  | empty => exact ⟨σ, by simpa using hσ, fun _ _ => rfl⟩
  | @insert x e hxe ih =>
    rw [Finset.card_insert_of_notMem hxe] at hde
    obtain ⟨σ', hσ', hag⟩ := ih (by omega)
    by_cases hx : x ∈ d ∪ e
    · refine ⟨σ', ?_, hag⟩
      rwa [Finset.union_insert, Finset.insert_eq_of_mem hx]
    · have hcard : #(d ∪ e) < k :=
        lt_of_le_of_lt (Finset.card_union_le _ _) (by omega)
      obtain ⟨τ, hτ, hτm⟩ := S.extend hσ' hcard x
      exact ⟨τ, by rwa [Finset.union_insert], fun y hy =>
        (hτ y (Finset.mem_union_left _ hy)).trans (hag y hy)⟩

/-- **No position falsifies a line of a narrow proof** [Atserias and Dalmau, Lemma 3]
[AtseriasDalmau2008]: for a strategy with `w + 1` pebbles, no position falsifies a line of a proof
from `φ` whose lines have width at most `w`. -/
theorem not_falsifies_of_isProof (S : DuplicatorStrategy φ (w + 1)) {ls : List (Clause V)}
    (hp : φ.IsProof ls) (hw : ∀ c ∈ ls, c.width ≤ w) :
    ∀ c ∈ ls, ∀ σ d, S.Mem σ d → ¬ Falsifies σ d c := by
  induction hp with
  | nil => simp
  | mem h hc ih =>
    intro c' hc' σ d hσ
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact S.not_falsifies hσ _ hc
    · exact ih (fun c h => hw c (List.mem_cons_of_mem _ h)) c' hc' σ d hσ
  | @resolvent ls c₁ c₂ v h h₁ h₂ hv₁ hv₂ ih =>
    intro c' hc' σ d hσ hf
    have ih' := ih (fun c h => hw c (List.mem_cons_of_mem _ h))
    rcases List.mem_cons.1 hc' with rfl | hc'
    · -- restrict to the variables of the resolvent and extend to `v`
      set R := c₁.resolvent c₂ v
      set d₀ := R.toFinset.image Prod.fst
      have hd₀ : d₀ ⊆ d := by
        intro x hx
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
        exact (hf l (List.mem_toFinset.1 hl)).1
      have hcard : #d₀ < w + 1 :=
        Nat.lt_succ_of_le (Finset.card_image_le.trans (hw R List.mem_cons_self))
      obtain ⟨τ, hτ, hτm⟩ := S.extend (S.restrict hσ hd₀) hcard v
      have hfR : Falsifies τ d₀ R := fun l hl =>
        ⟨Finset.mem_image_of_mem _ (List.mem_toFinset.2 hl),
          by rw [hτ _ (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hl))]; exact (hf l hl).2⟩
      -- the extension falsifies the premise whose literal on `v` it makes false
      cases hτv : τ v
      · refine ih' c₁ h₁ τ _ hτm fun l hl => ?_
        by_cases hl' : l = (v, true)
        · subst hl'
          exact ⟨Finset.mem_insert_self _ _, by simp [hτv]⟩
        · have := hfR l (Clause.mem_resolvent.2 (Or.inl ⟨hl, hl'⟩))
          exact ⟨Finset.mem_insert_of_mem this.1, this.2⟩
      · refine ih' c₂ h₂ τ _ hτm fun l hl => ?_
        by_cases hl' : l = (v, false)
        · subst hl'
          exact ⟨Finset.mem_insert_self _ _, by simp [hτv]⟩
        · have := hfR l (Clause.mem_resolvent.2 (Or.inr ⟨hl, hl'⟩))
          exact ⟨Finset.mem_insert_of_mem this.1, this.2⟩
    · exact ih' c' hc' σ d hσ hf

/-- **A Duplicator strategy with `w + 1` pebbles rules out refutations of width `w`** [Atserias and
Dalmau, Lemma 3][AtseriasDalmau2008]. -/
theorem not_refutableInWidth (S : DuplicatorStrategy φ (w + 1)) : ¬ φ.RefutableInWidth w := by
  rintro ⟨ls, hp, hnil, hw⟩
  obtain ⟨σ, d, hσ⟩ := S.nonempty
  exact S.not_falsifies_of_isProof hp hw [] hnil σ d hσ (falsifies_nil σ d)

/-! ### A strategy from the absence of narrow refutations -/

/-- `c` is a line of some proof from `φ` whose lines have width at most `w`. -/
private def WDerives (φ : CNF V) (w : ℕ) (c : Clause V) : Prop :=
  ∃ ls, φ.IsProof ls ∧ c ∈ ls ∧ ∀ c' ∈ ls, c'.width ≤ w

/-- The assignment `σ`, read on `d`, is **good**: it falsifies no clause derivable within width
`w`. -/
private def Good (φ : CNF V) (w : ℕ) (σ : V → Bool) (d : Finset V) : Prop :=
  ∀ c, WDerives φ w c → ¬ Falsifies σ d c

/-- A clause falsified on `d` has width at most `|d|`. -/
private theorem width_le_of_falsifies {σ : V → Bool} {d : Finset V} {c : Clause V}
    (h : Falsifies σ d c) : c.width ≤ #d := by
  refine Finset.card_le_card_of_injOn Prod.fst (fun l hl => (h l (List.mem_toFinset.1 hl)).1) ?_
  intro l₁ hl₁ l₂ hl₂ he
  have h₁ := (h l₁ (List.mem_toFinset.1 hl₁)).2
  have h₂ := (h l₂ (List.mem_toFinset.1 hl₂)).2
  rcases l₁ with ⟨v₁, b₁⟩
  rcases l₂ with ⟨v₂, b₂⟩
  simp only at he h₁ h₂
  subst he
  cases hσ : σ v₁ <;> cases b₁ <;> cases b₂ <;> simp_all

/-- If `φ` has no refutation of width `w`, the empty assignment is good. -/
private theorem good_empty (h : ¬ φ.RefutableInWidth w) (σ : V → Bool) : Good φ w σ ∅ := by
  rintro c ⟨ls, hp, hc, hw⟩ hf
  have : c = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => by simpa using (hf l hl).1
  exact h ⟨ls, hp, this ▸ hc, hw⟩

/-- A literal, other than `(x, !b)`, of a clause falsified by `σ` updated at `x` to `b` and read on
`insert x d`, is falsified by `σ` read on `d`. -/
private theorem falsifies_update {σ : V → Bool} {d : Finset V} {x : V} {b : Bool} {c : Clause V}
    (h : Falsifies (Function.update σ x b) (insert x d) c) {l : Literal V} (hl : l ∈ c)
    (hlx : l ≠ (x, !b)) : l.1 ∈ d ∧ σ l.1 ≠ l.2 := by
  obtain ⟨h₁, h₂⟩ := h l hl
  rcases l with ⟨v, b'⟩
  by_cases hv : v = x
  · subst hv
    simp only [Function.update_self] at h₂
    cases b <;> cases b' <;> simp_all
  · rw [Function.update_of_ne hv] at h₂
    exact ⟨(Finset.mem_insert.1 h₁).resolve_left hv, h₂⟩

/-- **One-variable extension**: a good assignment on at most `w` variables extends to a good
assignment on one more variable. If both extensions falsified derivable clauses, their resolvent
would be a derivable clause of width at most `w` falsified by the original assignment. -/
private theorem Good.extend {σ : V → Bool} {d : Finset V} (h : Good φ w σ d) (hd : #d ≤ w)
    (x : V) : ∃ b, Good φ w (Function.update σ x b) (insert x d) := by
  by_contra hne
  have hb (b : Bool) : ∃ c, WDerives φ w c ∧ Falsifies (Function.update σ x b) (insert x d) c := by
    by_contra hc
    exact hne ⟨b, fun c hw hf => hc ⟨c, hw, hf⟩⟩
  obtain ⟨c₀, ⟨ls₀, hp₀, hc₀, hw₀⟩, hf₀⟩ := hb false
  obtain ⟨c₁, ⟨ls₁, hp₁, hc₁, hw₁⟩, hf₁⟩ := hb true
  -- each clause contains the literal of `x` that its extension falsifies
  have hx₀ : (x, true) ∈ c₀ := by
    by_contra hx₀
    exact h c₀ ⟨ls₀, hp₀, hc₀, hw₀⟩ fun l hl =>
      falsifies_update hf₀ hl fun he => hx₀ (he ▸ hl)
  have hx₁ : (x, false) ∈ c₁ := by
    by_contra hx₁
    exact h c₁ ⟨ls₁, hp₁, hc₁, hw₁⟩ fun l hl =>
      falsifies_update hf₁ hl fun he => hx₁ (he ▸ hl)
  -- so their resolvent is a derivable clause falsified by `σ` on `d`
  have hf : Falsifies σ d (c₀.resolvent c₁ x) := by
    intro l hl
    rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
    exacts [falsifies_update hf₀ hl hne, falsifies_update hf₁ hl hne]
  refine h _ ⟨_, (hp₀.append hp₁).resolvent x (List.mem_append_left _ hc₀)
    (List.mem_append_right _ hc₁) hx₀ hx₁, List.mem_cons_self, fun c hc => ?_⟩ hf
  rcases List.mem_cons.1 hc with rfl | hc
  · exact (width_le_of_falsifies hf).trans hd
  · rcases List.mem_append.1 hc with hc | hc
    exacts [hw₀ c hc, hw₁ c hc]

/-- **A Duplicator strategy from the absence of narrow refutations** [Atserias and Dalmau,
Lemma 2][AtseriasDalmau2008]: if `φ` has no clause of width exactly `w + 1` and no refutation of
width `w`, then Duplicator wins the existential `(w + 1)`-pebble game. The positions are the partial
assignments on at most `w + 1` variables that falsify no clause derivable from `φ` within width
`w`. Clauses of width more than `w + 1` play no role, since they cannot be falsified on at most
`w + 1` variables.

Clauses of width `w + 1` must be excluded: `(x₀ ∨ x₁ ∨ x₂) ∧ ¬x₀ ∧ ¬x₁ ∧ ¬x₂` has no refutation of
width `2`, but Spoiler wins with `3` pebbles by pebbling `x₀`, `x₁` and `x₂`. From a bound
`hk : ∀ c ∈ φ, c.width ≤ w`, the hypothesis is `fun c hc => (Nat.lt_succ_of_le (hk c hc)).ne`. -/
def ofNotRefutableInWidth (hk : ∀ c ∈ φ, c.width ≠ w + 1) (h : ¬ φ.RefutableInWidth w) :
    DuplicatorStrategy φ (w + 1) where
  Mem σ d := #d ≤ w + 1 ∧ Good φ w σ d
  nonempty := ⟨fun _ => false, ∅, by simp, good_empty h _⟩
  card_le h := h.1
  restrict h hed := ⟨(Finset.card_le_card hed).trans h.1,
    fun c hc hf => h.2 c hc fun l hl => ⟨hed (hf l hl).1, (hf l hl).2⟩⟩
  extend {σ d} h hd v := by
    by_cases hv : v ∈ d
    · exact ⟨σ, fun _ _ => rfl, by rwa [Finset.insert_eq_of_mem hv]⟩
    · obtain ⟨b, hb⟩ := h.2.extend (Nat.lt_succ_iff.1 hd) v
      refine ⟨Function.update σ v b, fun x hx => Function.update_of_ne ?_ _ _, ?_, hb⟩
      · rintro rfl
        exact hv hx
      · rw [Finset.card_insert_of_notMem hv]
        exact hd
  not_falsifies h c hc hf := by
    -- a falsified clause has width at most `w + 1`, so at most `w`
    have hcw : c.width ≤ w :=
      Nat.le_of_lt_succ (lt_of_le_of_ne ((width_le_of_falsifies hf).trans h.1) (hk c hc))
    exact h.2 c ⟨[c], IsProof.nil.mem hc, List.mem_singleton_self _, by simpa using hcw⟩ hf

/-- **The existential pebble game characterizes width** [Atserias and Dalmau,
Theorem 2][AtseriasDalmau2008]: for a formula without clauses of width `w + 1`, Duplicator wins
the existential `(w + 1)`-pebble game exactly when there is no refutation of width `w`. -/
theorem nonempty_iff_not_refutableInWidth (hk : ∀ c ∈ φ, c.width ≠ w + 1) :
    Nonempty (DuplicatorStrategy φ (w + 1)) ↔ ¬ φ.RefutableInWidth w :=
  ⟨fun ⟨S⟩ => S.not_refutableInWidth, fun h => ⟨ofNotRefutableInWidth hk h⟩⟩

end DuplicatorStrategy

end CNF

end Cslib.Logic.PL
