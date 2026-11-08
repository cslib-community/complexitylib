/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Alternating.Views
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.BoundedSearch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Space-bounded alternating acceptance by marking

The configuration graph of a space-bounded alternating machine is evaluated bottom-up
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]. Starting from no views, a round of marking
(`Turing.MultiTapeATM.markStep`) keeps the views of a list that are halted with output `[true]`, or
running with one (existential state) or all (universal state) of their successors already marked
(`Turing.MultiTapeATM.markGood`). On a list closed under successors, `i + 1` rounds mark exactly the
views of the list that accept within `i` moves (`Turing.MultiTapeATM.mem_markStep_iterate_iff`).

Acceptance (`Turing.MultiTapeATM.Accepts`) is the least fixed point of the labelling, acceptance
within some finite number of moves, so an infinite branch never helps a configuration accept. The
marking computes exactly this least fixed point. Each round adds the views accepting within one
more move, and by stabilization on the finite list
(`Turing.MultiTapeATM.viewAcceptsWithin_length`) a view accepting within some number of moves
accepts within as many moves as the list has entries. So after that many rounds plus one, the
marked views are those accepting within some number of moves
(`Turing.MultiTapeATM.markAccepts_iff`). A view whose acceptance would rely on an infinite branch is
never marked, because the marking only ever adds views witnessed by finitely many moves.

The views are found by truncated breadth-first search
(`Turing.MultiTapeNTM.boundedSearch`). Once `N` bounds the number of reachable views, the search of
`N` rounds finds them all, and marking them decides acceptance
(`Turing.MultiTapeATM.boundedAccepts_iff`). When the space bound is polynomial in the instance,
`N` lists of at most `N + 1` views of polynomial size are processed, so the decision is
polynomial-time in the instance and the unary `N`
(`Turing.MultiTapeATM.computableInPolyTime_boundedAccepts`).

## Main definitions

* `Turing.MultiTapeATM.markGood`, `Turing.MultiTapeATM.markStep`: a round of marking.
* `Turing.MultiTapeATM.markAccepts`: whether a view is marked after enough rounds.
* `Turing.MultiTapeATM.boundedAccepts`: marking the views found by truncated breadth-first search.

## Main results

* `Turing.MultiTapeATM.mem_markStep_iterate_iff`: `i + 1` rounds mark the views accepting within
  `i` moves.
* `Turing.MultiTapeATM.markAccepts_iff`: marking decides acceptance on a closed list of views.
* `Turing.MultiTapeATM.boundedAccepts_iff`: under a space bound, marking the views found by enough
  rounds of search decides acceptance.
* `Turing.MultiTapeATM.computableInPolyTime_markGood`: the marking test is polynomial-time.
* `Turing.MultiTapeATM.computableInPolyTime_boundedAccepts`: under a polynomial space bound,
  marking is polynomial-time in the instance and the unary number of views.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*,
  Section 3][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 10.3][Sipser2013]
-/

public section

open Cslib.Turing

namespace Turing.MultiTapeATM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] {atm : MultiTapeATM k Bool State}

/-! ### Marking -/

section Marking

variable (atm)

open scoped Classical in
/-- Whether a view accepts within one more move, given the list `marked` of views accepting within
the current number of moves: a halted view with output `[true]`, or a running view one of whose
successors (existential state) or all of whose successors (universal state) are marked. -/
noncomputable def markGood (marked : List (FiniteCfg k Bool State)) (v : FiniteCfg k Bool State) :
    Bool :=
  (decide (v.state = none) && decide (v.output = [true])) ||
    if v.state.any atm.universal then (atm.toPTM.toNTM.viewSucc v).all fun w => decide (w ∈ marked)
    else (atm.toPTM.toNTM.viewSucc v).any fun w => decide (w ∈ marked)

/-- One round of marking: the views of `found` accepting within one more move. -/
noncomputable def markStep (found marked : List (FiniteCfg k Bool State)) :
    List (FiniteCfg k Bool State) :=
  found.filter (atm.markGood marked)

open scoped Classical in
/-- **Marking acceptance**: whether `start` is marked after as many rounds of marking as `found`
has entries, plus one. -/
noncomputable def markAccepts (found : List (FiniteCfg k Bool State))
    (start : FiniteCfg k Bool State) : Bool :=
  decide (start ∈ (atm.markStep found)^[found.length + 1] [])

variable {atm}

/-- Marking against the views accepting within `n` moves gives the views accepting within
`n + 1`. -/
theorem markGood_iff {found marked : List (FiniteCfg k Bool State)}
    (hclosed : ∀ v ∈ found, ∀ w ∈ atm.toPTM.toNTM.viewSucc v, w ∈ found) {n : ℕ}
    (hmarked : ∀ w ∈ found, (w ∈ marked ↔ atm.ViewAcceptsWithin n w))
    {v : FiniteCfg k Bool State} (hv : v ∈ found) :
    atm.markGood marked v = true ↔ atm.ViewAcceptsWithin (n + 1) v := by
  classical
  have hsucc {w} (hw : w ∈ atm.toPTM.toNTM.viewSucc v) :
      decide (w ∈ marked) = true ↔ atm.ViewAcceptsWithin n w := by
    rw [decide_eq_true_iff]
    exact hmarked w (hclosed v hv w hw)
  rcases hs : v.state with _ | q
  · rw [viewAcceptsWithin_of_halted hs]
    simp [markGood, hs, MultiTapeNTM.viewSucc]
  · cases hq : atm.universal q
    · rw [viewAcceptsWithin_succ_of_existential hs hq]
      simp only [markGood, hs, reduceCtorEq, decide_false, Bool.false_and, Bool.false_or,
        Option.any_some, hq, Bool.false_eq_true, ↓reduceIte, List.any_eq_true]
      exact exists_congr fun w => and_congr_right fun hw => hsucc hw
    · rw [viewAcceptsWithin_succ_of_universal hs hq]
      simp only [markGood, hs, reduceCtorEq, decide_false, Bool.false_and, Bool.false_or,
        Option.any_some, hq, ↓reduceIte, List.all_eq_true]
      exact forall_congr' fun w => forall_congr' fun hw => hsucc hw

/-- Marking against no views gives the views accepting within `0` moves: a running view has a
successor, which is not marked. -/
theorem markGood_nil_iff {v : FiniteCfg k Bool State} :
    atm.markGood [] v = true ↔ atm.ViewAcceptsWithin 0 v := by
  classical
  rcases hs : v.state with _ | q
  · rw [viewAcceptsWithin_zero_iff]
    simp [markGood, hs]
  · rw [viewAcceptsWithin_zero_iff, hs]
    have hne := viewSucc_ne_nil (atm := atm) hs
    cases hq : atm.universal q
    · simp [markGood, hs, hq]
    · simp only [markGood, hs, reduceCtorEq, decide_false, Bool.false_and, Bool.false_or,
        Option.any_some, hq, ↓reduceIte, List.mem_nil_iff, decide_false, List.all_eq_true,
        Bool.false_eq_true, imp_false, false_and, iff_false]
      intro h
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
      exact h w hw

/-- **Marking rounds.** On a list of views closed under successors, after `i + 1` rounds of
marking the marked views are those of the list accepting within `i` moves. -/
theorem mem_markStep_iterate_iff {found : List (FiniteCfg k Bool State)}
    (hclosed : ∀ v ∈ found, ∀ w ∈ atm.toPTM.toNTM.viewSucc v, w ∈ found) (i : ℕ)
    {v : FiniteCfg k Bool State} :
    v ∈ (atm.markStep found)^[i + 1] [] ↔ v ∈ found ∧ atm.ViewAcceptsWithin i v := by
  induction i generalizing v with
  | zero =>
    rw [zero_add, Function.iterate_one, markStep, List.mem_filter]
    exact and_congr_right fun _ => markGood_nil_iff
  | succ i ih =>
    rw [Function.iterate_succ_apply', markStep, List.mem_filter]
    refine and_congr_right fun hv => markGood_iff hclosed (fun w hw => ?_) hv
    rw [ih]
    exact and_iff_right hw

/-- **Marking computes the least fixed point** on a list of views closed under successors
containing the start: the start is marked exactly when it accepts within some number of moves. -/
theorem markAccepts_iff {found : List (FiniteCfg k Bool State)}
    (hclosed : ∀ v ∈ found, ∀ w ∈ atm.toPTM.toNTM.viewSucc v, w ∈ found)
    {start : FiniteCfg k Bool State} (hstart : start ∈ found) :
    atm.markAccepts found start = true ↔ ∃ n, atm.ViewAcceptsWithin n start := by
  classical
  rw [markAccepts, decide_eq_true_iff, mem_markStep_iterate_iff hclosed]
  exact ⟨fun h => ⟨_, h.2⟩, fun ⟨_, h⟩ => ⟨hstart, viewAcceptsWithin_length hclosed hstart h⟩⟩

end Marking

/-! ### Marking the reachable views -/

variable (atm) in
/-- **Space-bounded acceptance by marking**: mark the views found by the truncated breadth-first
search of `N` rounds, and test the initial view. -/
noncomputable def boundedAccepts (input : List Bool) (N : ℕ) : Bool :=
  atm.markAccepts (atm.toPTM.toNTM.boundedSearch input N N) (atm.toPTM.toNTM.initView input)

/-- **Marking decides acceptance under a space bound**, once `N` bounds the number of reachable
views. -/
theorem boundedAccepts_iff {input : List Bool} {s N : ℕ}
    (hs : atm.toPTM.toNTM.RunsInSpace input s)
    (hN : 2 ^ (2 * MultiTapeNTM.coreLengthBound k State input.length s + 1) ≤ N) :
    atm.boundedAccepts input N = true ↔ atm.Accepts input := by
  rw [accepts_iff_exists_viewAcceptsWithin, boundedAccepts]
  refine markAccepts_iff (fun v hv w hw => ?_)
    ((MultiTapeNTM.mem_boundedSearch_iff hs hN).mpr .refl)
  rw [MultiTapeNTM.mem_boundedSearch_iff hs hN] at hv ⊢
  exact hv.tail (MultiTapeNTM.viewStep_of_mem_viewSucc hw)

/-! ### Polynomial time -/

open scoped Classical in
/-- **The marking test is polynomial-time** in the marked views and the view. -/
theorem computableInPolyTime_markGood :
    ComputableInPolyTime (fun p : List (FiniteCfg k Bool State) × FiniteCfg k Bool State =>
      atm.markGood p.1 p.2) (encPair (encList encFiniteCfg) encFiniteCfg) encBool := by
  have hv : ComputableInPolyTime (fun p : List (FiniteCfg k Bool State) × FiniteCfg k Bool State =>
      p.2) (encPair (encList encFiniteCfg) encFiniteCfg) encFiniteCfg :=
    ComputableInPolyTime.snd _ _
  have hsucc := (MultiTapeNTM.computableInPolyTime_viewSucc (ntm := atm.toPTM.toNTM)).comp hv
  have hmem : ComputableInPolyTime
      (fun q : (List (FiniteCfg k Bool State) × FiniteCfg k Bool State) × FiniteCfg k Bool State =>
        decide (q.2 ∈ q.1.1))
      (encPair (encPair (encList encFiniteCfg) encFiniteCfg) encFiniteCfg) encBool :=
    ComputableInPolyTime.decide_mem ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _)
  have hhalt : ComputableInPolyTime
      (fun p : List (FiniteCfg k Bool State) × FiniteCfg k Bool State =>
        decide (p.2.state = none) && decide (p.2.output = [true]))
      (encPair (encList encFiniteCfg) encFiniteCfg) encBool :=
    ComputableInPolyTime.bool_and.comp
      (((ComputableInPolyTime.of_finite fun state : Option State =>
          decide (state = none)).comp (ComputableInPolyTime.finiteCfg_state.comp hv)).prod
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.finiteCfg_output.comp hv)
        (ComputableInPolyTime.const [true])))
  have huniv : ComputableInPolyTime
      (fun p : List (FiniteCfg k Bool State) × FiniteCfg k Bool State =>
        p.2.state.any atm.universal)
      (encPair (encList encFiniteCfg) encFiniteCfg) encBool :=
    (ComputableInPolyTime.of_finite fun state : Option State => state.any atm.universal).comp
      (ComputableInPolyTime.finiteCfg_state.comp hv)
  exact ComputableInPolyTime.bool_or.comp (hhalt.prod (ComputableInPolyTime.ite huniv
    (ComputableInPolyTime.allWithInput hsucc hmem) (ComputableInPolyTime.anyWithInput hsucc hmem)))

open scoped Classical in
/-- **Space-bounded acceptance by marking is polynomial-time** in the instance and the unary
number `N` of views, when the space bound is polynomial in the instance: the found and marked views
are at most `N + 1` views of polynomial size, and there are at most `N + 2` rounds of marking. -/
theorem computableInPolyTime_boundedAccepts {α : Type} {enc : α ↪ List Bool} {s : α → ℕ}
    (hs : ∀ a, atm.toPTM.toNTM.RunsInSpace (enc a) (s a))
    (hpoly : PolyBounded (fun a => (enc a).length) s) :
    ComputableInPolyTime (fun x : α × ℕ => atm.boundedAccepts (enc x.1) x.2)
      (encPair enc encUnary) encBool := by
  set ntm := atm.toPTM.toNTM
  have hinit : ComputableInPolyTime (fun x : α × ℕ => ntm.initView (enc x.1))
      (encPair enc encUnary) encFiniteCfg :=
    ComputableInPolyTime.finiteCfg_init ((ComputableInPolyTime.of_eq (encIn := enc)
      (encOut := encBits) (f := fun a => enc a) fun _ => rfl).comp (ComputableInPolyTime.fst _ _))
      ntm.q₀
  have hfound := MultiTapeNTM.computableInPolyTime_boundedSearch (ntm := ntm) hs hpoly
  -- the number of rounds of marking
  have hcount : ComputableInPolyTime
      (fun x : α × ℕ => (ntm.boundedSearch (enc x.1) x.2 x.2).length + 1)
      (encPair enc encUnary) encUnary :=
    ComputableInPolyTime.unary_add.comp (((ComputableInPolyTime.length_list _).comp hfound).prod
      (ComputableInPolyTime.const 1))
  -- a round of marking
  have hmark : ComputableInPolyTime (fun p : List (FiniteCfg k Bool State) ×
      List (FiniteCfg k Bool State) => atm.markStep p.1 p.2)
      (encPair (encList encFiniteCfg) (encList encFiniteCfg)) (encList encFiniteCfg) :=
    ComputableInPolyTime.filterWithInput (ComputableInPolyTime.fst _ _)
      (computableInPolyTime_markGood.comp (((ComputableInPolyTime.snd _ _).comp
        (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)))
  -- the marked views are a sublist of the found views
  have hmarked : ComputableInPolyTime (fun x : α × ℕ =>
      (atm.markStep (ntm.boundedSearch (enc x.1) x.2 x.2))^[(ntm.boundedSearch (enc x.1) x.2
        x.2).length + 1] []) (encPair enc encUnary) (encList encFiniteCfg) := by
    refine ComputableInPolyTime.iterateWith hfound hcount (ComputableInPolyTime.const []) hmark
      (hfound.polyBounded_length.add (.const 1)) fun x i _ => ?_
    have hsub : ∀ j, ((atm.markStep (ntm.boundedSearch (enc x.1) x.2 x.2))^[j] []).Sublist
        (ntm.boundedSearch (enc x.1) x.2 x.2) := by
      intro j
      cases j with
      | zero => exact List.nil_sublist _
      | succ j =>
        rw [Function.iterate_succ_apply']
        exact List.filter_sublist
    exact (length_encList_sublist _ (hsub i)).trans (Nat.le_succ _)
  exact ComputableInPolyTime.decide_mem hmarked hinit

end Turing.MultiTapeATM
