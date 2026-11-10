/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Logics.Propositional.DNF

/-!
# The canonical decision tree of a restricted formula

Let `F` be a formula in disjunctive normal form and `ρ` a restriction (partial assignment). The
*canonical decision tree* of `F` under `ρ` finds the first term of `F` that `ρ` does not falsify
(`DNF.firstTerm`), queries its free variables (`DNF.queried`), and continues under `ρ` extended by
the answers; when nothing is left to query, `F` is constant under `ρ` and the tree outputs its value
(`DNF.canonicalTree`, `DNF.eval_canonicalTree`). Its depth is at most the largest number of
queries it makes on an input (`DNF.depth_canonicalTree_le`, `DNF.pathLength`), which is what
the switching lemma bounds [Hastad1986], [Razborov1995], [Jukna, Chapter 12][Jukna2012].

## Main definitions

* `Cslib.Logic.PL.DNF.firstTerm`, `Cslib.Logic.PL.DNF.queried`.
* `Cslib.Logic.PL.DNF.canonicalTree`, `Cslib.Logic.PL.DNF.pathLength`.

## Main results

* `Cslib.Logic.PL.DNF.eval_canonicalTree`: the canonical tree computes the restricted formula.
* `Cslib.Logic.PL.DNF.complexity_lt_of_forall_pathLength_lt`: short query paths give shallow
  decision trees.

## References

* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [A. A. Razborov, *Bounded arithmetic and lower bounds in Boolean complexity*][Razborov1995]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.BitString Cslib.DecisionTree Finset

variable {ι : Type*}

namespace Term

/-- The restriction `ρ` falsifies the term `t`: it fixes one of its variables to the other value. -/
def FalsifiedBy (t : Term ι) (ρ : PartialAssignment ι) : Prop :=
  ∃ l ∈ t, ρ l.1 = some !l.2

instance (t : Term ι) (ρ : PartialAssignment ι) : Decidable (t.FalsifiedBy ρ) :=
  inferInstanceAs (Decidable (∃ l ∈ t, _))

/-- The variables of the term `t` left free by `ρ`, in order. -/
def freeVars (t : Term ι) (ρ : PartialAssignment ι) : List ι :=
  (t.filter fun l => (ρ l.1).isNone).map Prod.fst

variable {t : Term ι} {ρ : PartialAssignment ι}

theorem mem_freeVars {v : ι} : v ∈ t.freeVars ρ ↔ ∃ b, (v, b) ∈ t ∧ ρ v = none := by
  simp [freeVars, Option.isNone_iff_eq_none]

/-- A falsified term is false on every input filled from the restriction. -/
theorem eval_fill_of_falsifiedBy (h : t.FalsifiedBy ρ) (x : ι → Bool) :
    Term.eval (ρ.fill x) t = false := by
  obtain ⟨l, hl, hρ⟩ := h
  rw [Bool.eq_false_iff, ne_eq, Term.eval_eq_true_iff, not_forall]
  exact ⟨l, fun h' => by simpa [PartialAssignment.fill_of_eq_some hρ] using h' hl⟩

/-- A term that is not falsified and has no free variable is true on every input filled from the
restriction. -/
theorem eval_fill_of_freeVars_eq_nil (h : ¬ t.FalsifiedBy ρ) (hV : t.freeVars ρ = [])
    (x : ι → Bool) : Term.eval (ρ.fill x) t = true := by
  rw [Term.eval_eq_true_iff]
  intro l hl
  cases hρ : ρ l.1 with
  | none => exact absurd (mem_freeVars.2 ⟨l.2, hl, hρ⟩) (by simp [hV])
  | some b =>
    rw [PartialAssignment.fill_of_eq_some hρ]
    by_contra hb
    exact h ⟨l, hl, Bool.eq_not_iff.2 hb ▸ hρ⟩

end Term

namespace DNF

variable (F : DNF ι)

/-- The first term of `F` not falsified by `ρ`. -/
def firstTerm (ρ : PartialAssignment ι) : Option (Term ι) :=
  F.find? fun t => !decide (t.FalsifiedBy ρ)

/-- The variables queried at `ρ`: the free variables of the first term not falsified by `ρ`. -/
def queried (ρ : PartialAssignment ι) : List ι :=
  ((F.firstTerm ρ).map (·.freeVars ρ)).getD []

variable {F} {ρ : PartialAssignment ι}

theorem free_of_mem_queried {v : ι} (hv : v ∈ F.queried ρ) : ρ v = none := by
  unfold queried at hv
  cases h : F.firstTerm ρ with
  | none => simp [h] at hv
  | some t =>
    simp only [h, Option.map_some, Option.getD_some] at hv
    obtain ⟨b, -, hρ⟩ := Term.mem_freeVars.1 hv
    exact hρ

/-- When nothing is queried, the formula is constant under the restriction: true exactly when some
term is not falsified. -/
theorem eval_fill_of_queried_eq_nil (h : F.queried ρ = []) (x : ι → Bool) :
    DNF.eval (ρ.fill x) F = (F.firstTerm ρ).isSome := by
  unfold queried at h
  cases hf : F.firstTerm ρ with
  | none =>
    rw [firstTerm, List.find?_eq_none] at hf
    rw [Option.isSome_none, Bool.eq_false_iff, ne_eq, DNF.eval_eq_true_iff, not_exists]
    intro t ⟨ht, hte⟩
    exact absurd hte (by simp [Term.eval_fill_of_falsifiedBy (by simpa using hf t ht)])
  | some t =>
    simp only [hf, Option.map_some, Option.getD_some] at h
    have ht := List.mem_of_find?_eq_some hf
    have hnf : ¬ t.FalsifiedBy ρ := by simpa using List.find?_some hf
    rw [Option.isSome_some, DNF.eval_eq_true_iff]
    exact ⟨t, ht, Term.eval_fill_of_freeVars_eq_nil hnf h x⟩

variable [Fintype ι] [DecidableEq ι]

theorem toFinset_queried_subset_free : (F.queried ρ).toFinset ⊆ ρ.free := fun _ hv =>
  PartialAssignment.mem_free.2 (free_of_mem_queried (List.mem_toFinset.1 hv))

/-- Answering the queried variables frees fewer variables, as long as something is queried. -/
theorem card_free_assign_lt (h : F.queried ρ ≠ []) (a : ι → Bool) :
    #(ρ.assign (F.queried ρ).toFinset a).free < #ρ.free := by
  rw [PartialAssignment.free_assign]
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ h
  exact card_lt_card (sdiff_ssubset toFinset_queried_subset_free ⟨v, List.mem_toFinset.2 hv⟩)

variable (F)

/-- The canonical decision tree of `F` under `ρ`: query the free variables of the first term not
falsified by `ρ`, and continue under `ρ` extended by the answers. -/
def canonicalTree (ρ : PartialAssignment ι) : DecisionTree ι Bool :=
  if h : F.queried ρ = [] then leaf (DNF.eval (ρ.fill fun _ => false) F)
  else graft (F.queried ρ) (fun a =>
    have := card_free_assign_lt h a
    canonicalTree (ρ.assign (F.queried ρ).toFinset a)) fun _ => false
termination_by #ρ.free
decreasing_by exact this

/-- The number of queries the canonical tree makes on the input `x`: the sum of the lengths of
`DNF.queried` over the successive restrictions. A free variable occurring several times in the
queried term is counted once per occurrence. -/
def pathLength (ρ : PartialAssignment ι) (x : ι → Bool) : ℕ :=
  if h : F.queried ρ = [] then 0
  else
    have := card_free_assign_lt h x
    (F.queried ρ).length + pathLength (ρ.assign (F.queried ρ).toFinset x) x
termination_by #ρ.free
decreasing_by exact this

variable {F}

theorem canonicalTree_of_queried_eq_nil (h : F.queried ρ = []) :
    F.canonicalTree ρ = leaf (DNF.eval (ρ.fill fun _ => false) F) := by
  rw [canonicalTree, dite_eq_left h]

theorem canonicalTree_of_queried_ne_nil (h : F.queried ρ ≠ []) :
    F.canonicalTree ρ = graft (F.queried ρ)
      (fun a => F.canonicalTree (ρ.assign (F.queried ρ).toFinset a)) fun _ => false := by
  rw [canonicalTree, dite_eq_right h]

theorem pathLength_of_queried_eq_nil (h : F.queried ρ = []) (x : ι → Bool) :
    F.pathLength ρ x = 0 := by
  rw [pathLength, dite_eq_left h]

theorem pathLength_of_queried_ne_nil (h : F.queried ρ ≠ []) (x : ι → Bool) :
    F.pathLength ρ x =
      (F.queried ρ).length + F.pathLength (ρ.assign (F.queried ρ).toFinset x) x := by
  rw [pathLength, dite_eq_right h]

/-- The canonical tree computes the formula restricted by `ρ`. -/
theorem eval_canonicalTree (ρ : PartialAssignment ι) (x : ι → Bool) :
    (F.canonicalTree ρ).eval x = DNF.eval (ρ.fill x) F := by
  by_cases h : F.queried ρ = []
  · rw [canonicalTree_of_queried_eq_nil h, eval_leaf, eval_fill_of_queried_eq_nil h,
      eval_fill_of_queried_eq_nil h]
  · rw [canonicalTree_of_queried_ne_nil h, eval_graft,
      eval_canonicalTree _ x]
    exact congrArg (DNF.eval · F) (PartialAssignment.fill_assign toFinset_queried_subset_free
      fun i hi => by simp [List.mem_toFinset.1 hi])
termination_by #ρ.free
decreasing_by exact card_free_assign_lt h _

/-- The query path depends only on the free bits of the input. -/
private theorem pathLength_congr {ρ : PartialAssignment ι} {x y : ι → Bool}
    (h : ∀ i ∈ ρ.free, x i = y i) :
    F.pathLength ρ x = F.pathLength ρ y := by
  by_cases hq : F.queried ρ = []
  · rw [pathLength_of_queried_eq_nil hq, pathLength_of_queried_eq_nil hq]
  · have hassign : ρ.assign (F.queried ρ).toFinset x = ρ.assign (F.queried ρ).toFinset y := by
      funext i
      by_cases hi : i ∈ (F.queried ρ).toFinset
      · simp [hi, h i (toFinset_queried_subset_free hi)]
      · simp [hi]
    rw [pathLength_of_queried_ne_nil hq, pathLength_of_queried_ne_nil hq, hassign,
      pathLength_congr (ρ := ρ.assign (F.queried ρ).toFinset y) fun i hi => h i (by
        rw [PartialAssignment.free_assign] at hi
        exact (mem_sdiff.1 hi).1)]
termination_by #ρ.free
decreasing_by exact card_free_assign_lt hq y

/-- The canonical tree is no deeper than its longest query path. -/
theorem depth_canonicalTree_le (ρ : PartialAssignment ι) :
    (F.canonicalTree ρ).depth ≤ univ.sup (F.pathLength ρ) := by
  by_cases h : F.queried ρ = []
  · simp [canonicalTree_of_queried_eq_nil h]
  rw [canonicalTree_of_queried_ne_nil h]
  set V := F.queried ρ
  have hV : V.length ≤ univ.sup (F.pathLength ρ) :=
    le_sup_of_le (mem_univ fun _ => false)
      ((pathLength_of_queried_ne_nil h _).symm ▸ Nat.le_add_right _ _)
  refine (depth_graft_le V _ _ (d := univ.sup (F.pathLength ρ) - V.length) fun a => ?_).trans
    (by omega)
  refine (depth_canonicalTree_le (ρ.assign V.toFinset a)).trans ?_
  obtain ⟨y, -, hy⟩ := exists_mem_eq_sup univ univ_nonempty
    (F.pathLength (ρ.assign V.toFinset a))
  rw [hy]
  -- The input reading `a` on `V` and `y` elsewhere has a query path through `V`.
  set x : ι → Bool := fun j => if j ∈ V then a j else y j
  have hxa : ρ.assign V.toFinset x = ρ.assign V.toFinset a := by
    funext i
    by_cases hi : i ∈ V <;> simp [x, hi]
  have hpath : F.pathLength ρ x = V.length + F.pathLength (ρ.assign V.toFinset a) y := by
    rw [pathLength_of_queried_ne_nil h, hxa]
    refine congrArg (V.length + ·) (pathLength_congr fun i hi => ?_)
    rw [PartialAssignment.free_assign] at hi
    simp [x, show i ∉ V from fun h' => (mem_sdiff.1 hi).2 (List.mem_toFinset.2 h')]
  have := le_sup (f := F.pathLength ρ) (mem_univ x)
  omega
termination_by #ρ.free
decreasing_by exact card_free_assign_lt h a

/-- If every query path is shorter than `s`, the restricted formula has decision tree depth less
than `s`. -/
theorem complexity_lt_of_forall_pathLength_lt {s : ℕ} (h : ∀ x, F.pathLength ρ x < s) :
    complexity (fun x => DNF.eval (ρ.fill x) F) < s := by
  have hs : 0 < s := (Nat.zero_le _).trans_lt (h fun _ => false)
  refine (complexity_le_depth (t := F.canonicalTree ρ) fun x => eval_canonicalTree ρ x).trans_lt
    ((depth_canonicalTree_le ρ).trans_lt ?_)
  exact (Finset.sup_lt_iff hs).2 fun x _ => h x

end DNF

end Cslib.Logic.PL
