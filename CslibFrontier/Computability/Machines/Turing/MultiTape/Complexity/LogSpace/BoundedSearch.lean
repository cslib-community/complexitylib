/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Truncated breadth-first search through the views

Breadth-first search through the views of a nondeterministic machine
(`Cslib.Reachability.search`, along `Turing.MultiTapeNTM.viewSucc`) finds every reachable view once
it has run for as many rounds as there are reachable views (`Turing.MultiTapeNTM.mem_search_iff`).
Under a space bound `s` there are at most `2 ^ (2 * coreLengthBound k State n s + 1)` of them. For a
polynomial `s` that is exponential, and a polynomial-time analysis must then be relative to the
number of rounds. The truncated search `Turing.MultiTapeNTM.boundedSearch` keeps at most `cap` views
after each round, so its lists have at most `cap + 1` views of size polynomial in the instance and
the space bound (`Turing.MultiTapeNTM.length_boundedSearch_le`). With the cap and the number of
rounds given in unary, it is polynomial-time
(`Turing.MultiTapeNTM.computableInPolyTime_boundedSearch`). Truncation never discards a view once
`cap` bounds the number of reachable views (`Turing.MultiTapeNTM.boundedSearch_eq_search`), so it
then finds exactly the reachable views (`Turing.MultiTapeNTM.mem_boundedSearch_iff`). This is the
configuration-graph construction of [Sipser, Section 8.4][Sipser2013], with the graph size passed as
a unary parameter.

## Main definitions

* `Turing.MultiTapeNTM.boundedSearch`: breadth-first search through the views, truncated to a cap.

## Main results

* `Turing.MultiTapeNTM.length_boundedSearch_le`: the truncated search keeps at most `cap + 1`
  views.
* `Turing.MultiTapeNTM.reflTransGen_of_mem_boundedSearch`: it finds only reachable views.
* `Turing.MultiTapeNTM.boundedSearch_eq_search`, `Turing.MultiTapeNTM.mem_boundedSearch_iff`: once
  the cap bounds the number of reachable views, truncation changes nothing and enough rounds find
  exactly the reachable views.
* `Turing.MultiTapeNTM.computableInPolyTime_boundedSearch`: under a polynomial space bound, the
  truncated search is polynomial-time in the instance and the unary cap.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

public section

open Cslib.Turing

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State}

variable (ntm) in
open scoped Classical in
/-- Breadth-first search through the views for `rounds` rounds, keeping at most `cap` views after
each round. Truncation changes nothing once `cap` bounds the number of reachable views, and keeps
the search polynomial in `cap` otherwise. -/
noncomputable def boundedSearch (input : List Bool) (cap rounds : ℕ) :
    List (FiniteCfg k Bool State) :=
  (fun found => (Cslib.Reachability.expand ntm.viewSucc found).take cap)^[rounds]
    [ntm.initView input]

/-- The truncated search keeps at most `cap + 1` views. -/
theorem length_boundedSearch_le (input : List Bool) (cap rounds : ℕ) :
    (ntm.boundedSearch input cap rounds).length ≤ cap + 1 := by
  cases rounds with
  | zero => simp [boundedSearch]
  | succ i =>
    rw [boundedSearch, Function.iterate_succ_apply']
    exact (List.length_take_le _ _).trans (Nat.le_succ _)

open scoped Classical in
/-- The truncated search finds only reachable views. -/
theorem reflTransGen_of_mem_boundedSearch {input : List Bool} {cap rounds : ℕ}
    {finite : FiniteCfg k Bool State} (h : finite ∈ ntm.boundedSearch input cap rounds) :
    Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite := by
  induction rounds generalizing finite with
  | zero =>
    rw [boundedSearch, Function.iterate_zero_apply, List.mem_singleton] at h
    exact h ▸ .refl
  | succ i ih =>
    rw [boundedSearch, Function.iterate_succ_apply'] at h
    rcases Cslib.Reachability.mem_expand.mp (List.mem_of_mem_take h) with hf | ⟨g, hg, hfg⟩
    · exact ih hf
    · exact (ih hg).tail (viewStep_of_mem_viewSucc hfg)

open scoped Classical in
/-- **Truncation changes nothing** once `cap` bounds the number of reachable views: under a space
bound `s`, `2 ^ (2 * coreLengthBound k State n s + 1)` of them. -/
theorem boundedSearch_eq_search {input : List Bool} {s cap : ℕ} (hs : ntm.RunsInSpace input s)
    (hcap : 2 ^ (2 * coreLengthBound k State input.length s + 1) ≤ cap) (rounds : ℕ) :
    ntm.boundedSearch input cap rounds =
      Cslib.Reachability.search ntm.viewSucc rounds (ntm.initView input) := by
  induction rounds with
  | zero => rfl
  | succ i ih =>
    rw [boundedSearch, Function.iterate_succ_apply', ← boundedSearch, ih,
      ← Cslib.Reachability.search_succ]
    exact List.take_of_length_le ((length_le_of_nodup_reachable hs
      (Cslib.Reachability.nodup_search _ _) fun f hf => reflTransGen_viewSucc_iff.mp
        (Cslib.Reachability.reflTransGen_of_mem_search hf)).trans hcap)

/-- **The truncated search finds the reachable views** once `N`, as both the cap and the number of
rounds, bounds their number. -/
theorem mem_boundedSearch_iff {input : List Bool} {s N : ℕ} (hs : ntm.RunsInSpace input s)
    (hN : 2 ^ (2 * coreLengthBound k State input.length s + 1) ≤ N)
    {finite : FiniteCfg k Bool State} :
    finite ∈ ntm.boundedSearch input N N ↔
      Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite := by
  classical
  rw [boundedSearch_eq_search hs hN, mem_search_iff hs hN]

open scoped Classical in
/-- **The truncated search is polynomial-time** in the instance and the unary number `N`, used as
both the cap and the number of rounds, when the space bound is polynomial in the instance: each
list holds at most `N + 1` views of size polynomial in the instance. -/
theorem computableInPolyTime_boundedSearch {α : Type} {enc : α ↪ List Bool} {s : α → ℕ}
    (hs : ∀ a, ntm.RunsInSpace (enc a) (s a))
    (hpoly : PolyBounded (fun a => (enc a).length) s) :
    ComputableInPolyTime (fun x : α × ℕ => ntm.boundedSearch (enc x.1) x.2 x.2)
      (encPair enc encUnary) (encList encFiniteCfg) := by
  have hN : ComputableInPolyTime (fun x : α × ℕ => x.2) (encPair enc encUnary) encUnary :=
    ComputableInPolyTime.snd _ _
  have hinit : ComputableInPolyTime (fun x : α × ℕ => ntm.initView (enc x.1))
      (encPair enc encUnary) encFiniteCfg :=
    ComputableInPolyTime.finiteCfg_init ((ComputableInPolyTime.of_eq (encIn := enc)
      (encOut := encBits) (f := fun a => enc a) fun _ => rfl).comp (ComputableInPolyTime.fst _ _))
      ntm.q₀
  -- a truncated round
  have hstep : ComputableInPolyTime (fun p : ℕ × List (FiniteCfg k Bool State) =>
      (Cslib.Reachability.expand ntm.viewSucc p.2).take p.1)
      (encPair encUnary (encList encFiniteCfg)) (encList encFiniteCfg) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput
      ((ComputableInPolyTime.expand computableInPolyTime_viewSucc).comp
        (ComputableInPolyTime.snd _ _)).tidy (ComputableInPolyTime.fst _ _).tidy)
  -- the size of the lists of views
  have hlen : PolyBounded (fun x : α × ℕ => (encPair enc encUnary x).length)
      fun x => (enc x.1).length :=
    (ComputableInPolyTime.fst enc encUnary).polyBounded_length
  have hbound : PolyBounded (fun x : α × ℕ => (encPair enc encUnary x).length) fun x =>
      (x.2 + 1) * (2 * viewLengthBound k State (enc x.1).length (s x.1) + 1) := by
    refine (hN.polyBounded.add (.const 1)).mul (((PolyBounded.const 2).mul ?_).add (.const 1))
    exact (PolyBounded.const _).mul ((hlen.add (hpoly.comp hlen)).add (.const 1))
  refine ComputableInPolyTime.iterateWith (step := fun N found =>
    (Cslib.Reachability.expand ntm.viewSucc found).take N) hN hN
    (ComputableInPolyTime.cons' hinit (ComputableInPolyTime.const [])) hstep hbound ?_
  intro x i _
  refine (length_encList_le encFiniteCfg (ntm.boundedSearch (enc x.1) x.2 i) fun f hf =>
    length_encFiniteCfg_le (hs x.1) (reflTransGen_of_mem_boundedSearch hf)).trans ?_
  exact Nat.mul_le_mul_right _ (length_boundedSearch_le _ _ _)

end Turing.MultiTapeNTM
