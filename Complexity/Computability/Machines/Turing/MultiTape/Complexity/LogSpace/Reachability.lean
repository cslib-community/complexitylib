/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.BreadthFirst
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Configurations
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# Acceptance in logarithmic space by breadth-first search in polynomial time

A nondeterministic machine accepts exactly when a halted view with output `[true]` is reachable
from its initial view (`Turing.MultiTapeNTM.accepts_iff_reflTransGen_viewStep`). Breadth-first
search through the views (`Cslib.Reachability.search`, along `Turing.MultiTapeNTM.viewSucc`)
decides this once it has run for as many rounds as there are reachable views
(`Turing.MultiTapeNTM.searchAccepts_iff`). Under a logarithmic space bound there are polynomially
many (`Turing.MultiTapeNTM.length_le_of_nodup_reachable`), so a polynomial number of rounds
suffices, each round is polynomial-time in the views found so far, and these are polynomially
many views of linear size. The decision is therefore polynomial-time
(`Turing.MultiTapeNTM.exists_computableInPolyTime_searchAccepts`): reachability in the
configuration graph, which has polynomially many vertices [Sipser, Section 8.4][Sipser2013].

## Main definitions

* `Turing.MultiTapeNTM.viewSucc`: the views a running view steps to.
* `Turing.MultiTapeNTM.searchAccepts`: breadth-first search for an accepting view.

## Main results

* `Turing.MultiTapeNTM.reflTransGen_viewSucc_iff`: the successor lists give the reachable views.
* `Turing.MultiTapeNTM.searchAccepts_iff`: enough rounds decide acceptance.
* `Turing.MultiTapeNTM.computableTidilyInPolyTime_viewSucc`: the successors in polynomial time.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.expand`: a round in polynomial time.
* `Turing.MultiTapeNTM.exists_computableInPolyTime_searchAccepts`: under a logarithmic space
  bound, enough rounds of breadth-first search run in polynomial time.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.1][AroraBarak09]
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)

/-- The views a view steps to, other than itself: none for a halted view, and for a running view
the summarized results of the actions its transition relation permits. -/
noncomputable def viewSucc (finite : FiniteCfg k Bool State) : List (FiniteCfg k Bool State) :=
  match finite.state with
  | none => []
  | some state => (ntm.actions state finite.inputSymbol finite.workTapeSymbols).map
      fun action => (finite.step action).summarizeOutput

open scoped Classical in
/-- **Breadth-first acceptance**: run `rounds` rounds of breadth-first search through the views
from the initial view on `input`, and test for a halted view with output `[true]`. -/
noncomputable def searchAccepts (rounds : ℕ) (input : List Bool) : Bool :=
  (Cslib.Reachability.search ntm.viewSucc rounds (ntm.initView input)).any
    fun finite => decide (finite.state = none) && decide (finite.output = [true])

variable {ntm}

/-- A view steps to each of its successors. -/
theorem viewStep_of_mem_viewSucc {finite next : FiniteCfg k Bool State}
    (h : next ∈ ntm.viewSucc finite) : ntm.ViewStep finite next := by
  unfold viewSucc at h
  unfold ViewStep
  rcases hs : finite.state with _ | state
  · simp [hs] at h
  · simp only [hs, List.mem_map, mem_actions] at h ⊢
    obtain ⟨action, htr, rfl⟩ := h
    exact ⟨action, htr, rfl⟩

/-- **The successor lists give the reachable views**: a halted view steps only to itself, which
adds nothing to reachability. -/
theorem reflTransGen_viewSucc_iff {finite next : FiniteCfg k Bool State} :
    Relation.ReflTransGen (fun a b => b ∈ ntm.viewSucc a) finite next ↔
      Relation.ReflTransGen ntm.ViewStep finite next := by
  constructor
  · exact Relation.ReflTransGen.mono (r := fun a b => b ∈ ntm.viewSucc a)
      (fun _ _ h => viewStep_of_mem_viewSucc h) _ _
  · intro h
    induction h with
    | refl => exact .refl
    | @tail view next _ hstep ih =>
      unfold ViewStep at hstep
      rcases hs : view.state with _ | state
      · simp only [hs] at hstep
        exact hstep ▸ ih
      · simp only [hs] at hstep
        obtain ⟨action, htr, rfl⟩ := hstep
        refine ih.tail ?_
        simp only [viewSucc, hs, List.mem_map, mem_actions]
        exact ⟨action, htr, rfl⟩

/-- **Enough rounds decide acceptance**: under a space bound `s`, breadth-first search for at least
`2 ^ (2 * coreLengthBound k State n s + 1)` rounds finds an accepting view exactly when the
machine accepts. -/
theorem searchAccepts_iff {input : List Bool} {s rounds : ℕ} (hs : ntm.RunsInSpace input s)
    (hrounds : 2 ^ (2 * coreLengthBound k State input.length s + 1) ≤ rounds) :
    ntm.searchAccepts rounds input = true ↔ ntm.Accepts input := by
  classical
  have hmem (finite : FiniteCfg k Bool State) :
      finite ∈ Cslib.Reachability.search ntm.viewSucc rounds (ntm.initView input) ↔
        Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite := by
    rw [Cslib.Reachability.mem_search_iff (fun views hnodup hreach =>
      length_le_of_nodup_reachable hs hnodup fun f hf =>
        reflTransGen_viewSucc_iff.mp (hreach f hf)) hrounds, reflTransGen_viewSucc_iff]
  rw [accepts_iff_reflTransGen_viewStep, searchAccepts]
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, hmem]

end Turing.MultiTapeNTM

/-! ### Breadth-first search in polynomial time -/

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α : Type} [DecidableEq α] {enc : α ↪ List Bool}

/-- Appending an element unless it is already in the list is polynomial-time. -/
theorem insertNew : ComputableTidilyInPolyTime
    (fun p : List α × α => Cslib.Reachability.insertNew p.1 p.2) (encPair (encList enc) enc)
    (encList enc) := by
  have hmem (l : List α) (a : α) : decide (a ∈ l) = l.any fun b => decide (b = a) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true]
    simp only [decide_eq_true_eq, exists_eq_right]
  have hfst := fst (encList enc) enc
  have hsnd := snd (encList enc) enc
  unfold Cslib.Reachability.insertNew
  refine ite_decide ?_ hfst (listAppend' hfst (cons' hsnd (const [])))
  simp only [hmem]
  exact anyWithInput hfst (decide_eq' (snd _ _) (hsnd.comp (fst _ _)))

/-- **A round of breadth-first search is polynomial-time** when the successors are: the found
elements and their successors are at most polynomially many and long. -/
theorem expand {succ : α → List α} (hsucc : ComputableTidilyInPolyTime succ enc (encList enc)) :
    ComputableTidilyInPolyTime (Cslib.Reachability.expand succ) (encList enc) (encList enc) := by
  have hlist : ComputableTidilyInPolyTime (fun found : List α => found.flatMap succ)
      (encList enc) (encList enc) :=
    flatMapWithInput id' (hsucc.comp (snd _ _))
  have hstep : ComputableTidilyInPolyTime
      (fun p : (List α × List α) × α => Cslib.Reachability.insertNew p.1.2 p.2)
      (encPair (encPair (encList enc) (encList enc)) enc) (encList enc) :=
    insertNew.comp (((snd _ _).comp (fst _ _)).prod (snd _ _))
  refine foldlWithInput_of_bounded_growth
    (step := fun _ acc a => Cslib.Reachability.insertNew acc a) id'
    ⟨hlist, hstep, inferInstance, inferInstance⟩
    (growth := fun found => 2 * (encList enc (found.flatMap succ)).length + 1)
    ⟨((PolyBounded.const 2).mul hlist.polyBounded_length).add (.const 1), ?_⟩
  intro found acc a ha
  unfold Cslib.Reachability.insertNew
  split_ifs
  · omega
  · have := SizedListEncoding.length_elem_le (encA := enc) (encL := encList enc) _ a ha
    simp only [encList_append, encList_cons, encList_nil, List.append_nil, List.length_append,
      length_frame]
    omega

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State}

/-- **The successors of a view are polynomial-time.** -/
theorem computableTidilyInPolyTime_viewSucc :
    ComputableTidilyInPolyTime ntm.viewSucc encFiniteCfg (encList encFiniteCfg) := by
  classical
  let key (finite : FiniteCfg k Bool State) : Option State × Option Bool × (Fin k → Option Bool) :=
    (finite.state, finite.inputSymbol, finite.workTapeSymbols)
  let branch (tag : Option State × Option Bool × (Fin k → Option Bool))
      (finite : FiniteCfg k Bool State) : List (FiniteCfg k Bool State) :=
    match tag.1 with
    | none => []
    | some state => (ntm.actions state tag.2.1 tag.2.2).map
        fun action => (finite.step action).summarizeOutput
  have heq : ntm.viewSucc = fun finite => branch (key finite) finite := by
    funext finite
    rfl
  rw [heq]
  refine ComputableTidilyInPolyTime.finite_cases
    (tagEncoding := encPair (encFinite _) (encPair (encFinEnum _) (encFinEnum _))) ?_ fun tag => ?_
  · exact ComputableTidilyInPolyTime.finiteCfg_state.prod
      (ComputableTidilyInPolyTime.finiteCfg_inputSymbol.prod
        ComputableTidilyInPolyTime.finiteCfg_workTapeSymbols)
  · rcases tag with ⟨_ | state, symbol, work⟩
    · exact ComputableTidilyInPolyTime.const []
    · exact ComputableTidilyInPolyTime.mapConst _ fun action _ =>
        ComputableInPolyTime.finiteCfg_summarizeOutput.tidy.comp
          (ComputableTidilyInPolyTime.finiteCfg_step action)

/-- Under a logarithmic space bound, the number of rounds that decides acceptance is at most a
polynomial in the input length. -/
private theorem rounds_le (k : ℕ) (State : Type) (c n : ℕ) :
    2 ^ (2 * coreLengthBound k State n (c * (Nat.log2 n + 1)) + 1) ≤
      2 * 2 ^ (2 * (8 + 2 * Nat.card (Option State) + 200 * k) * (c + 1)) *
        (n + 1) ^ (2 * (8 + 2 * Nat.card (Option State) + 200 * k) * (c + 1)) := by
  set M := 8 + 2 * Nat.card (Option State) + 200 * k
  set D := 2 * M * (c + 1)
  have hexp : 2 * coreLengthBound k State n (c * (Nat.log2 n + 1)) + 1 ≤
      (Nat.log2 n + 1) * D + 1 := by
    simp only [coreLengthBound, D]
    rw [← show M = 8 + 2 * Nat.card (Option State) + 200 * k from rfl]
    nlinarith
  calc 2 ^ (2 * coreLengthBound k State n (c * (Nat.log2 n + 1)) + 1)
      ≤ 2 ^ ((Nat.log2 n + 1) * D + 1) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 2 * (2 ^ (Nat.log2 n + 1)) ^ D := by rw [pow_succ, pow_mul, mul_comm]
    _ ≤ 2 * (2 * (n + 1)) ^ D :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.two_pow_log2_succ_le n) D)
    _ = 2 * 2 ^ D * (n + 1) ^ D := by rw [mul_pow, mul_assoc]

open scoped Classical in
/-- **Acceptance within logarithmic space is decided by breadth-first search in polynomial time.**
If every computation prefix of `ntm` on every encoded instance `enc a` stays within space
`c * (Nat.log2 n + 1)`, then some polynomial number of rounds suffices for
`Turing.MultiTapeNTM.searchAccepts_iff`, and breadth-first search for that many rounds is
polynomial-time in the encoded instance. -/
theorem exists_computableInPolyTime_searchAccepts {α : Type} {enc : α ↪ List Bool} {c : ℕ}
    (hs : ∀ a, ntm.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1))) :
    ∃ rounds : α → ℕ, (∀ a, 2 ^ (2 * coreLengthBound k State (enc a).length
        (c * (Nat.log2 (enc a).length + 1)) + 1) ≤ rounds a) ∧
      ComputableInPolyTime (fun a => ntm.searchAccepts (rounds a) (enc a)) enc encBool := by
  set D := 2 * (8 + 2 * Nat.card (Option State) + 200 * k) * (c + 1)
  set rounds : α → ℕ := fun a => 2 * 2 ^ D * ((enc a).length + 1) ^ D
  refine ⟨rounds, fun a => rounds_le k State c _,
    ComputableTidilyInPolyTime.computableInPolyTime ?_⟩
  -- the number of rounds in unary
  have hcount : ComputableTidilyInPolyTime rounds enc encUnary :=
    ComputableTidilyInPolyTime.unary_mul.comp ((ComputableTidilyInPolyTime.const _).prod
      ((ComputableTidilyInPolyTime.unary_pow D).comp (ComputableTidilyInPolyTime.unary_add.comp
        ((ComputableTidilyInPolyTime.encoding_length enc).prod
          (ComputableTidilyInPolyTime.const 1)))))
  have hinit : ComputableTidilyInPolyTime (fun a => [ntm.initView (enc a)]) enc
      (encList encFiniteCfg) :=
    ComputableTidilyInPolyTime.cons' (ComputableTidilyInPolyTime.finiteCfg_init
      (ComputableTidilyInPolyTime.of_eq (encIn := enc) (encMid := encBits) (f := fun a => enc a)
        fun _ => rfl) ntm.q₀)
      (ComputableTidilyInPolyTime.const [])
  -- the found views are polynomially many, each of linear length
  set bound : α → ℕ := fun a => rounds a *
    (2 * viewLengthBound k State (enc a).length (c * (Nat.log2 (enc a).length + 1)) + 1)
  have hbound : PolyBounded (fun a => (enc a).length) bound := by
    refine (PolyBounded.of_forall_le (2 * 2 ^ D) D fun a => le_rfl).mul ?_
    refine .of_forall_le (2 * (10 + 2 * Nat.card (Option State) + 200 * k) * (c + 2) + 1) 1
      fun a => ?_
    have hlog := Nat.mul_le_mul_left ((10 + 2 * Nat.card (Option State) + 200 * k) * c)
      (Nat.log2_le_self (enc a).length)
    simp only [viewLengthBound, pow_one]
    generalize 10 + 2 * Nat.card (Option State) + 200 * k = B at *
    nlinarith
  have hstates : ∀ a, ∀ i ≤ rounds a, (encList encFiniteCfg
      ((Cslib.Reachability.expand ntm.viewSucc)^[i] [ntm.initView (enc a)])).length ≤ bound a := by
    intro a i _
    have hreach (finite) (hf : finite ∈ Cslib.Reachability.search ntm.viewSucc i
        (ntm.initView (enc a))) :
        Relation.ReflTransGen ntm.ViewStep (ntm.initView (enc a)) finite :=
      reflTransGen_viewSucc_iff.mp (Cslib.Reachability.reflTransGen_of_mem_search hf)
    have hlen := (length_le_of_nodup_reachable (hs a) (Cslib.Reachability.nodup_search i _)
      hreach).trans (rounds_le k State c _)
    refine (length_encList_le encFiniteCfg _ fun finite hf =>
      length_encFiniteCfg_le (hs a) (hreach finite hf)).trans ?_
    exact Nat.mul_le_mul_right _ hlen
  have hsearch := ComputableTidilyInPolyTime.iterate hcount hinit
    (ComputableTidilyInPolyTime.expand computableTidilyInPolyTime_viewSucc) hbound hstates
  have htest : ComputableTidilyInPolyTime
      (fun finite : FiniteCfg k Bool State =>
        decide (finite.state = none) && decide (finite.output = [true])) encFiniteCfg encBool :=
    ComputableTidilyInPolyTime.bool_and.comp
      (((ComputableTidilyInPolyTime.of_finite fun state : Option State =>
          decide (state = none)).comp ComputableTidilyInPolyTime.finiteCfg_state).prod
      (ComputableTidilyInPolyTime.decide_eq' ComputableTidilyInPolyTime.finiteCfg_output
        (ComputableTidilyInPolyTime.const [true])))
  exact ComputableTidilyInPolyTime.anyWithInput hsearch
    (htest.comp (ComputableTidilyInPolyTime.snd _ _))

end Turing.MultiTapeNTM
