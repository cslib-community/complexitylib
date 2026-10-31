/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Approximator
public import Complexity.Foundations.Combinatorics.Sunflower.Implication

/-!
# Closed clique approximators

Alon and Boppana sharpen Razborov's method of approximations by replacing sunflower plucking with
a closure [Alon and Boppana, Section 3][AlonBoppana1987]. An approximator is a family of vertex
sets of at most `l` vertices, read as the disjunction of the indicators "all edges inside `W`"
(`Cslib.Circuits.Monotone.Accepts`), that is *closed*: it contains every set of at most `l` vertices
containing the pairwise intersections of `r` of its members (`Cslib.ImpliedBy`). As a convention,
a closed family with a set of at most one vertex, which has all edges inside on every input, also
contains `∅` (`Cslib.Circuits.Monotone.Closure.Derives`).

A disjunction of approximators is the closure of the union of their families, and a conjunction
the closure of their intersection; the constants are the closures of `{∅}` and `∅`. The closure is
reached by adding derived sets one at a time, so it takes at most as many steps as there are sets of
at most `l` vertices (`Cslib.Circuits.Monotone.Closure.relatesInSteps_closure`).

The minimal sets of a closed family form an implication-minimal family, so a closed family has
at most `(r - 1) ^ j` minimal sets of at most `j ≤ l` vertices
(`Cslib.Circuits.Monotone.Closure.card_filter_minimals_le`), by the Alon–Boppana family bound
(`Cslib.card_le_pow_of_isImplicationMinimal`). This replaces the Erdős–Rado bound
`(p - 1) ^ w * w!` of the sunflower approximators (`Cslib.Circuits.Monotone.Approximator`).

## Main definitions

* `Cslib.Circuits.Monotone.Closure.Derives`, `Cslib.Circuits.Monotone.Closure.IsClosed`,
  `Cslib.Circuits.Monotone.Closure.Step`, `Cslib.Circuits.Monotone.Closure.closure`: derived sets,
  closed families, closure steps and the closure.
* `Cslib.Circuits.Monotone.Closure.minimals`: the minimal sets of a family.
* `Cslib.Circuits.Monotone.Closure.Approximator`,
  `Cslib.Circuits.Monotone.Closure.Approximator.input`,
  `Cslib.Circuits.Monotone.Closure.Approximator.interpretation`: closed approximators and the
  approximate interpretation of the monotone basis.

## Main results

* `Cslib.Circuits.Monotone.Closure.relatesInSteps_closure`: the closure is reached in at most as
  many steps as there are sets of at most `l` vertices.
* `Cslib.Circuits.Monotone.Closure.card_filter_minimals_le`: a closed family has at most
  `(r - 1) ^ j` minimal sets of at most `j` vertices.

## References

* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*][AlonBoppana1987]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone.Closure

open Cslib.Circuits.Clique Finset Relation

variable {n r l : ℕ}

/-! ### Closed families -/

/-- `W` is *derived* from `F`: it has at most `l` vertices, and it is implied by `r` members of `F`,
or it is empty and `F` has a member of at most one vertex. -/
def Derives (r l : ℕ) (F : Finset (Finset (Fin n))) (W : Finset (Fin n)) : Prop :=
  W.card ≤ l ∧ (ImpliedBy r F W ∨ (W = ∅ ∧ ∃ V ∈ F, V.card ≤ 1))

/-- A family is *closed* when it contains every set derived from it. -/
def IsClosed (r l : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ W, Derives r l F W → W ∈ F

/-- A closed family contains every set of at most `l` vertices containing one of its members. -/
theorem IsClosed.mem_of_subset {F : Finset (Finset (Fin n))} (hF : IsClosed r l F)
    {V W : Finset (Fin n)} (hV : V ∈ F) (hVW : V ⊆ W) (hW : W.card ≤ l) : W ∈ F :=
  hF W ⟨hW, Or.inl (impliedBy_of_subset hV hVW)⟩

/-- A closed family with a member of at most one vertex contains `∅`. -/
theorem IsClosed.empty_mem {F : Finset (Finset (Fin n))} (hF : IsClosed r l F)
    {V : Finset (Fin n)} (hV : V ∈ F) (hV1 : V.card ≤ 1) : ∅ ∈ F :=
  hF ∅ ⟨by simp, Or.inr ⟨rfl, V, hV, hV1⟩⟩

/-- The sets of at most `l` vertices. -/
def smallSets (n l : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter (·.card ≤ l)

/-- A closure step: add one derived set. -/
def Step (r l : ℕ) (F G : Finset (Finset (Fin n))) : Prop :=
  ∃ W, W ∉ F ∧ Derives r l F W ∧ G = insert W F

/-- A closure step adds a set of at most `l` vertices, so it lowers the number of such sets that
are missing. -/
theorem Step.card_lt {F G : Finset (Finset (Fin n))} (h : Step r l F G) :
    (smallSets n l \ G).card < (smallSets n l \ F).card := by
  obtain ⟨W, hWF, hW, rfl⟩ := h
  refine card_lt_card ⟨sdiff_subset_sdiff subset_rfl (subset_insert _ _), fun hsub => ?_⟩
  have hW' : W ∈ smallSets n l \ F := mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, hW.1⟩, hWF⟩
  exact (mem_sdiff.1 (hsub hW')).2 (mem_insert_self _ _)

/-- A family can be closed in at most as many steps as it misses sets of at most `l` vertices. -/
theorem exists_relatesInSteps_isClosed (r l : ℕ) (F : Finset (Finset (Fin n))) :
    ∃ G m, m ≤ (smallSets n l \ F).card ∧ RelatesInSteps (Step r l) F G m ∧ IsClosed r l G := by
  induction F using (measure fun F => (smallSets n l \ F).card).wf.induction with
  | h F ih =>
    by_cases hF : IsClosed r l F
    · exact ⟨F, 0, Nat.zero_le _, RelatesInSteps.refl F, hF⟩
    · simp only [IsClosed, not_forall] at hF
      obtain ⟨W, hW, hWF⟩ := hF
      have hstep : Step r l F (insert W F) := ⟨W, hWF, hW, rfl⟩
      obtain ⟨G, m, hm, hG, hclosed⟩ := ih _ hstep.card_lt
      exact ⟨G, m + 1, by have := hstep.card_lt; omega,
        RelatesInSteps.head _ _ _ _ hstep hG, hclosed⟩

/-- The closure of a family: a closed family reached from it by closure steps. -/
noncomputable def closure (r l : ℕ) (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (exists_relatesInSteps_isClosed r l F).choose

/-- The closure is closed. -/
theorem isClosed_closure (F : Finset (Finset (Fin n))) : IsClosed r l (closure r l F) :=
  (exists_relatesInSteps_isClosed r l F).choose_spec.choose_spec.2.2

/-- The closure is reached in at most as many steps as there are sets of at most `l` vertices. -/
theorem relatesInSteps_closure (F : Finset (Finset (Fin n))) :
    ∃ m ≤ (smallSets n l).card, RelatesInSteps (Step r l) F (closure r l F) m := by
  obtain ⟨m, hm, h, -⟩ := (exists_relatesInSteps_isClosed r l F).choose_spec
  exact ⟨m, hm.trans (card_le_card sdiff_subset), h⟩

/-- Closure steps only add sets. -/
theorem subset_of_relatesInSteps_step {F G : Finset (Finset (Fin n))} {m : ℕ}
    (h : RelatesInSteps (Step r l) F G m) : F ⊆ G := by
  induction h with
  | refl => exact subset_rfl
  | tail _ _ _ _ h ih =>
    obtain ⟨W, -, -, rfl⟩ := h
    exact ih.trans (subset_insert _ _)

/-- Closure steps keep the sets of at most `l` vertices. -/
theorem forall_card_le_of_relatesInSteps_step {F G : Finset (Finset (Fin n))} {m : ℕ}
    (h : RelatesInSteps (Step r l) F G m) (hF : ∀ s ∈ F, s.card ≤ l) : ∀ s ∈ G, s.card ≤ l := by
  induction h with
  | refl => exact hF
  | tail _ _ _ _ h ih =>
    obtain ⟨W, -, hW, rfl⟩ := h
    intro s hs
    rcases mem_insert.1 hs with rfl | hs
    exacts [hW.1, ih s hs]

/-- A family is contained in its closure. -/
theorem subset_closure (F : Finset (Finset (Fin n))) : F ⊆ closure r l F :=
  let ⟨_, _, h⟩ := relatesInSteps_closure (r := r) (l := l) F
  subset_of_relatesInSteps_step h

/-- The closure of a family of sets of at most `l` vertices has sets of at most `l` vertices. -/
theorem forall_card_le_closure {F : Finset (Finset (Fin n))} (hF : ∀ s ∈ F, s.card ≤ l) :
    ∀ s ∈ closure r l F, s.card ≤ l :=
  let ⟨_, _, h⟩ := relatesInSteps_closure (r := r) (l := l) F
  forall_card_le_of_relatesInSteps_step h hF

/-! ### Minimal sets -/

/-- The minimal sets of a family. -/
def minimals (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  F.filter fun W => ∀ U ∈ F, U ⊆ W → U = W

/-- Every member of a family contains a minimal set of the family. -/
theorem exists_mem_minimals_subset {F : Finset (Finset (Fin n))} {W : Finset (Fin n)}
    (hW : W ∈ F) : ∃ X ∈ minimals F, X ⊆ W := by
  obtain ⟨X, hX, hmin⟩ := (F.filter (· ⊆ W)).exists_minimal ⟨W, mem_filter.2 ⟨hW, subset_rfl⟩⟩
  obtain ⟨hXF, hXW⟩ := mem_filter.1 hX
  refine ⟨X, mem_filter.2 ⟨hXF, fun U hU hUX => ?_⟩, hXW⟩
  exact subset_antisymm hUX (hmin (mem_filter.2 ⟨hU, hUX.trans hXW⟩) hUX)

/-- **Minimal sets of a closed family** [Alon and Boppana, Corollary 3.3][AlonBoppana1987]. For
`r ≥ 2` and `j ≤ l`, a closed family has at most `(r - 1) ^ j` minimal sets of at most `j`
vertices. -/
theorem card_filter_minimals_le (hr : 2 ≤ r) {F : Finset (Finset (Fin n))} (hF : IsClosed r l F)
    {j : ℕ} (hj : j ≤ l) : ((minimals F).filter (·.card ≤ j)).card ≤ (r - 1) ^ j := by
  refine card_le_pow_of_isImplicationMinimal hr (fun W hW => (mem_filter.1 hW).2) ?_
  intro W hW U hUW hU
  obtain ⟨hWmin, hWj⟩ := mem_filter.1 hW
  obtain ⟨hWF, hmin⟩ := mem_filter.1 hWmin
  have hsub : (minimals F).filter (·.card ≤ j) ⊆ F := fun _ h =>
    (mem_filter.1 (mem_filter.1 h).1).1
  have hUF : U ∈ F := hF U ⟨by have := card_lt_card hUW; omega, Or.inl (hU.mono hsub)⟩
  exact hUW.ne (hmin U hUF hUW.subset)

/-! ### Approximators -/

/-- A closed approximator: a closed family of sets of at most `l` vertices. -/
structure Approximator (n r l : ℕ) where
  /-- The vertex sets. -/
  terms : Finset (Finset (Fin n))
  card_le_of_mem : ∀ s ∈ terms, s.card ≤ l
  isClosed : IsClosed r l terms

namespace Approximator

/-- The truth value of an approximator on an input: whether one of its sets has all edges
inside. -/
noncomputable def decode (A : Approximator n r l) (x : Fin (edgeCount n) → Bool) : Bool :=
  decide (Accepts A.terms x)

/-- An approximator `A` decodes to `true` on `x` if and only if `Accepts A.terms x`. -/
@[simp] theorem decode_eq_true {A : Approximator n r l} {x : Fin (edgeCount n) → Bool} :
    A.decode x = true ↔ Accepts A.terms x :=
  decide_eq_true_iff

/-- A closed family accepts the complete graph on a set `c` exactly when one of its sets lies in
`c`. -/
theorem accepts_ofFinset_iff {F : Finset (Finset (Fin n))} (hF : IsClosed r l F)
    {c : Finset (Fin n)} : Accepts F (ofFinset c) ↔ ∃ W ∈ F, W ⊆ c := by
  refine ⟨fun ⟨W, hW, hWc⟩ => ?_, fun ⟨W, hW, hWc⟩ => ⟨W, hW, (contains_ofFinset c).mono hWc⟩⟩
  by_cases h : 2 ≤ W.card
  · exact ⟨W, hW, subset_of_contains_ofFinset h hWc⟩
  · exact ⟨∅, hF.empty_mem hW (by omega), empty_subset _⟩

/-- The family of sets produced at a gate from the families of its arguments, before closing:
`{∅}` or `∅` for the constants, the union for a disjunction and the intersection for a
conjunction. -/
def gateTerms :
    (op : Op) → (Fin (signature.Arity op) → Finset (Finset (Fin n))) → Finset (Finset (Fin n))
  | .const b, _ => if b then {∅} else ∅
  | .or, F => F 0 ∪ F 1
  | .and, F => F 0 ∩ F 1

/-- Every set in `gateTerms op` of families of sets of at most `l` vertices has at most `l`
vertices. -/
theorem card_le_of_mem_gateTerms {op : Op} (A : Fin (signature.Arity op) → Approximator n r l)
    {s : Finset (Fin n)} (hs : s ∈ gateTerms op fun i => (A i).terms) : s.card ≤ l := by
  cases op with
  | const b => cases b <;> simp_all [gateTerms]
  | or =>
    rcases mem_union.1 hs with hs | hs
    exacts [(A 0).card_le_of_mem s hs, (A 1).card_le_of_mem s hs]
  | and => exact (A 0).card_le_of_mem s (mem_inter.1 hs).1

/-- The approximate interpretation of the monotone basis: close the family produced at the gate
(`gateTerms`). -/
noncomputable def interpretation : Interpretation signature (Approximator n r l) := fun op A =>
  { terms := closure r l (gateTerms op fun i => (A i).terms)
    card_le_of_mem := forall_card_le_closure fun _ => card_le_of_mem_gateTerms A
    isClosed := isClosed_closure _ }

/-- The vertex sets of `interpretation op A` are the closure of `gateTerms op`. -/
theorem terms_interpretation (op : Op) (A : Fin (signature.Arity op) → Approximator n r l) :
    (interpretation op A).terms = closure r l (gateTerms op fun i => (A i).terms) :=
  rfl

variable [Fact (2 ≤ r)]

/-- The approximator of an input variable: the sets of at most `l` vertices containing its edge. -/
noncomputable def input (i : Fin (edgeCount n)) : Approximator n r l where
  terms := (smallSets n l).filter (((edgeEquiv n).symm i).1.toFinset ⊆ ·)
  card_le_of_mem _ hs := (mem_filter.1 (mem_filter.1 hs).1).2
  isClosed W hW := by
    have hr : 2 ≤ r := Fact.out
    have he := Sym2.card_toFinset_of_not_isDiag _ ((edgeEquiv n).symm i).2
    refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hW.1⟩, ?_⟩
    obtain ⟨-, ⟨V, hV, hVW⟩ | ⟨-, V, hV, hV1⟩⟩ := hW
    · have h0 := (mem_filter.1 (hV ⟨0, by omega⟩)).2
      have h1 := (mem_filter.1 (hV ⟨1, by omega⟩)).2
      exact (subset_inter h0 h1).trans (hVW _ _ (by simp))
    · have := card_le_card (mem_filter.1 hV).2
      omega

/-- When `2 ≤ l`, the input approximator `input i` decodes to `x i`. -/
theorem decode_input (hl : 2 ≤ l) (i : Fin (edgeCount n)) (x : Fin (edgeCount n) → Bool) :
    (input i : Approximator n r l).decode x = x i := by
  have he := Sym2.card_toFinset_of_not_isDiag _ ((edgeEquiv n).symm i).2
  rw [Bool.eq_iff_iff, decode_eq_true]
  constructor
  · rintro ⟨W, hW, hxW⟩
    have := contains_toFinset_iff.1 (hxW.mono (mem_filter.1 hW).2)
    rwa [Equiv.apply_symm_apply] at this
  · intro hx
    refine ⟨_, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, by omega⟩, subset_rfl⟩, ?_⟩
    rw [contains_toFinset_iff, Equiv.apply_symm_apply]
    exact hx

end Approximator

end Cslib.Circuits.Monotone.Closure
