/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TwoSAT
public import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
public import CslibFrontier.Computability.Complexity.Classes.P
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

/-!
# Polynomial-time decision and witness construction for 2SAT

Native multi-tape Turing-machine polynomial-time decision and satisfying-assignment construction
for `Cslib.Complexity.TwoSAT` under the binary CNF encoding `encCNF`, following the
implication-graph characterization of [Aspvall, Plass and Tarjan][AspvallPlassTarjan1979].

Every intermediate literal list is filtered from `lits φ` (the list of both polarities of all
variable occurrences in `φ`), keeping tape representations occurrence-bounded even when binary
variable names are exponentially large:
1. `reach φ ℓ₀` computes the literals reachable from `ℓ₀` in `φ.Implies` by
   `φ.numVars + φ.numVars + 1` simultaneous breadth-first passes;
2. `chosenLiterals φ` folds over `φ.vars`, choosing for each still-undecided variable `v` the
   polarity `(v, false)` when `(v, true)` reaches `(v, false)` and `(v, true)` otherwise, then
   closing under `reach φ`;
3. `assignment φ v` reads whether `(v, true) ∈ chosenLiterals φ`, and `solve φ` checks width at
   most `2` together with `φ.eval (assignment φ)`.

## Main definitions

* `Cslib.Complexity.TwoSAT.reach`: implication-graph reachability list from a literal.
* `Cslib.Complexity.TwoSAT.assignment`: polynomial-time satisfying-assignment constructor.
* `Cslib.Complexity.TwoSAT.solve`: polynomial-time `TwoSAT` decider.

## Main results

* `Cslib.Complexity.TwoSAT.eval_assignment_of_satisfiable`,
  `Cslib.Complexity.TwoSAT.eval_assignment_of_mem`: `assignment φ` satisfies every satisfiable
  width-at-most-2 formula.
* `Cslib.Complexity.TwoSAT.solve_eq_true_iff`, `Cslib.Complexity.TwoSAT.solve_eq_true_iff_mem`:
  correctness of `solve`.
* `Cslib.Complexity.TwoSAT.computableInPolyTime_assignment`,
  `Cslib.Complexity.TwoSAT.computableInPolyTime_solve`: native multi-tape polynomial-time
  certificates.
* `Cslib.Complexity.TwoSAT.mem_P`: `TwoSAT ∈ P encCNF`.

## References

* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
-/

public section

namespace Cslib.Complexity.TwoSAT

open scoped List
open Cslib.Logic.PL Turing.MultiTapeTM

section Pure

variable {V : Type*} [DecidableEq V]

/-- Both polarities of every variable occurrence in `φ`. -/
@[expose] def lits (φ : CNF V) : Clause V :=
  φ.vars.map (·, false) ++ φ.vars.map (·, true)

/-- Boolean test for the implication-graph arc `φ.Implies ℓ ℓ'`. -/
@[expose] def hasImpEdge (φ : CNF V) (ℓ ℓ' : Literal V) : Bool :=
  φ.any fun c =>
    c.contains ℓ.negate && c.contains ℓ' && c.all fun m => m == ℓ.negate || m == ℓ'

/-- One simultaneous reachability pass on `lits φ`. -/
@[expose] def stepReach (φ : CNF V) (s : Clause V) : Clause V :=
  (lits φ).filter fun ℓ' => s.contains ℓ' || s.any fun ℓ => hasImpEdge φ ℓ ℓ'

/-- Reachable literals from `ℓ₀` after `n` passes. -/
@[expose] def reachFrom (φ : CNF V) (ℓ₀ : Literal V) (n : ℕ) : Clause V :=
  (stepReach φ)^[n] ((lits φ).filter (· == ℓ₀))

/-- Implication-closed reachable literal list from `ℓ₀`. -/
@[expose] def reach (φ : CNF V) (ℓ₀ : Literal V) : Clause V :=
  reachFrom φ ℓ₀ (φ.numVars + φ.numVars + 1)

/-- Extend a consistent closed literal list `s` to decide `v`, choosing `(v, false)` if `(v, true)`
reaches `(v, false)` and `(v, true)` otherwise, then closing under `reach φ`. -/
@[expose] def chooseStep (φ : CNF V) (s : Clause V) (v : V) : Clause V :=
  if s.contains (v, true) || s.contains (v, false) then
    s
  else
    let ℓ : Literal V := (v, !(reach φ (v, true)).contains (v, false))
    (lits φ).filter fun m => s.contains m || (reach φ ℓ).contains m

/-- Consistent implication-closed literal list deciding every occurring variable of `φ`. -/
@[expose] def chosenLiterals (φ : CNF V) : Clause V :=
  φ.vars.foldl (chooseStep φ) []

/-- Candidate satisfying assignment extracted from `chosenLiterals φ`. -/
@[expose] def assignment (φ : CNF V) (v : V) : Bool :=
  (chosenLiterals φ).contains (v, true)

/-- Executable 2-SAT decider: check clause width at most `2` and evaluate `assignment φ`. -/
@[expose] def solve (φ : CNF V) : Bool :=
  φ.all (fun c => decide (c.length ≤ 2)) && φ.eval (assignment φ)

omit [DecidableEq V] in
theorem mem_lits_iff (φ : CNF V) (ℓ : Literal V) : ℓ ∈ lits φ ↔ ℓ.1 ∈ φ.vars := by
  rcases ℓ with ⟨v, b⟩
  cases b <;> simp [lits]

private theorem card_lits_toFinset_le (φ : CNF V) :
    (lits φ).toFinset.card ≤ φ.numVars + φ.numVars := by
  have hsub : (lits φ).toFinset ⊆ φ.vars.toFinset ×ˢ (Finset.univ : Finset Bool) := by
    intro ℓ hℓ
    rw [Finset.mem_product]
    exact ⟨List.mem_toFinset.mpr ((mem_lits_iff φ ℓ).mp (List.mem_toFinset.mp hℓ)),
      Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, ← CNF.numVars] at hle
  omega

theorem hasImpEdge_eq_true_iff (φ : CNF V) (ℓ ℓ' : Literal V) :
    hasImpEdge φ ℓ ℓ' = true ↔ φ.Implies ℓ ℓ' := by
  simp only [hasImpEdge, CNF.Implies, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc]

theorem mem_stepReach (φ : CNF V) (s : Clause V) (ℓ' : Literal V) :
    ℓ' ∈ stepReach φ s ↔
      ℓ'.1 ∈ φ.vars ∧ (ℓ' ∈ s ∨ ∃ ℓ ∈ s, φ.Implies ℓ ℓ') := by
  simp only [stepReach, List.mem_filter, mem_lits_iff, Bool.or_eq_true, List.contains_iff_mem,
    List.any_eq_true, hasImpEdge_eq_true_iff]

/-- Every pass produces a sublist of `lits φ`. -/
theorem reachFrom_sublist (φ : CNF V) (ℓ₀ : Literal V) (n : ℕ) :
    reachFrom φ ℓ₀ n <+ lits φ := by
  cases n with
  | zero => exact List.filter_sublist
  | succ n =>
    rw [reachFrom, Function.iterate_succ_apply']
    exact List.filter_sublist

theorem reachFrom_subset_succ (φ : CNF V) (ℓ₀ : Literal V) (n : ℕ) :
    reachFrom φ ℓ₀ n ⊆ reachFrom φ ℓ₀ (n + 1) := by
  intro m hm
  rw [reachFrom, Function.iterate_succ_apply']
  exact (mem_stepReach φ _ m).mpr
    ⟨(mem_lits_iff φ m).mp ((reachFrom_sublist φ ℓ₀ n).subset hm), Or.inl hm⟩

private theorem stepReach_congr (φ : CNF V) {s t : Clause V} (h : ∀ m, m ∈ s ↔ m ∈ t) :
    stepReach φ s = stepReach φ t := by
  have hc : ∀ m, s.contains m = t.contains m := by
    intro m
    rw [Bool.eq_iff_iff]
    simp only [List.contains_iff_mem, h]
  have ha : ∀ ℓ', (s.any fun ℓ => hasImpEdge φ ℓ ℓ') = (t.any fun ℓ => hasImpEdge φ ℓ ℓ') := by
    intro ℓ'
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, h]
  simp only [stepReach, hc, ha]

theorem reachFrom_fixed (φ : CNF V) (ℓ₀ : Literal V) :
    stepReach φ (reach φ ℓ₀) = reach φ ℓ₀ := by
  let s (n : ℕ) := (reachFrom φ ℓ₀ n).toFinset
  have hincl (n : ℕ) : s n ⊆ s (n + 1) := fun m hm =>
    List.mem_toFinset.mpr (reachFrom_subset_succ φ ℓ₀ n (List.mem_toFinset.mp hm))
  have hmono : Monotone fun n => (s n).card :=
    monotone_nat_of_le_succ fun n => Finset.card_le_card (hincl n)
  have hbound (n : ℕ) : (s n).card ≤ φ.numVars + φ.numVars := by
    have hsub : s n ⊆ (lits φ).toFinset := fun m hm =>
      List.mem_toFinset.mpr ((reachFrom_sublist φ ℓ₀ n).subset (List.mem_toFinset.mp hm))
    exact (Finset.card_le_card hsub).trans (card_lits_toFinset_le φ)
  have heq (n : ℕ) (h : (s n).card = (s (n + 1)).card) : s n = s (n + 1) :=
    Finset.eq_of_subset_of_card_le (hincl n) h.ge
  have hnext (n : ℕ) (h : (s n).card = (s (n + 1)).card) :
      reachFrom φ ℓ₀ (n + 1) = reachFrom φ ℓ₀ (n + 2) := by
    have hm (m : Literal V) : m ∈ reachFrom φ ℓ₀ n ↔ m ∈ reachFrom φ ℓ₀ (n + 1) := by
      have hm := Finset.ext_iff.mp (heq n h) m
      simpa only [s, List.mem_toFinset] using hm
    simpa only [reachFrom, Function.iterate_succ_apply'] using stepReach_congr φ hm
  have hstab (n : ℕ) (h : (s n).card = (s (n + 1)).card) :
      (s (n + 1)).card = (s (n + 2)).card := by
    simp only [s, hnext n h]
  have hc :=
    Nat.stabilises_of_monotone hmono hbound hstab (n := φ.numVars + φ.numVars + 1) (by omega)
  have hl := hnext (φ.numVars + φ.numVars) hc.symm
  simpa only [reach, reachFrom, Function.iterate_succ_apply'] using hl.symm

private theorem reachFrom_sound (φ : CNF V) (ℓ₀ : Literal V) :
    ∀ (n : ℕ) {m : Literal V}, m ∈ reachFrom φ ℓ₀ n →
      m.1 ∈ φ.vars ∧ Relation.ReflTransGen φ.Implies ℓ₀ m
  | 0, m, hm => by
    simp only [reachFrom, Function.iterate_zero_apply, List.mem_filter, beq_iff_eq,
      mem_lits_iff] at hm
    rcases hm with ⟨hmv, rfl⟩
    exact ⟨hmv, .refl⟩
  | n + 1, m, hm => by
    rw [reachFrom, Function.iterate_succ_apply'] at hm
    obtain ⟨hmv, hm | ⟨ℓ, hℓ, himp⟩⟩ := (mem_stepReach φ _ m).mp hm
    · exact reachFrom_sound φ ℓ₀ n hm
    · exact ⟨hmv, (reachFrom_sound φ ℓ₀ n hℓ).2.tail himp⟩

omit [DecidableEq V] in
private theorem mem_vars_of_implies {φ : CNF V} {ℓ ℓ' : Literal V} (h : φ.Implies ℓ ℓ') :
    ℓ.1 ∈ φ.vars ∧ ℓ'.1 ∈ φ.vars := by
  obtain ⟨c, hc, h₁, h₂, -⟩ := h
  have hneg : ℓ.negate.1 = ℓ.1 := by rcases ℓ with ⟨v, b⟩; rfl
  exact ⟨hneg ▸ CNF.mem_vars.mpr ⟨c, hc, ℓ.negate.2, h₁⟩,
    CNF.mem_vars.mpr ⟨c, hc, ℓ'.2, h₂⟩⟩

omit [DecidableEq V] in
private theorem mem_vars_of_reach {φ : CNF V} {ℓ₀ m : Literal V} (h₀ : ℓ₀.1 ∈ φ.vars)
    (h : Relation.ReflTransGen φ.Implies ℓ₀ m) : m.1 ∈ φ.vars := by
  induction h with
  | refl => exact h₀
  | tail _ hab _ => exact (mem_vars_of_implies hab).2

/-- Exact reachability characterization from any literal whose variable occurs in `φ`. -/
theorem mem_reach_iff {φ : CNF V} {ℓ₀ : Literal V} (hℓ₀ : ℓ₀.1 ∈ φ.vars) (m : Literal V) :
    m ∈ reach φ ℓ₀ ↔ Relation.ReflTransGen φ.Implies ℓ₀ m := by
  constructor
  · exact fun hm => (reachFrom_sound φ ℓ₀ _ hm).2
  · intro h
    induction h with
    | refl =>
      have h₀ : ℓ₀ ∈ reachFrom φ ℓ₀ 0 := by
        simp [reachFrom, mem_lits_iff, hℓ₀]
      have hmono : ∀ k, ℓ₀ ∈ reachFrom φ ℓ₀ k := by
        intro k
        induction k with
        | zero => exact h₀
        | succ k ih => exact reachFrom_subset_succ φ ℓ₀ k ih
      exact hmono _
    | tail _ hbc ih =>
      have hstep : _ ∈ stepReach φ (reach φ ℓ₀) :=
        (mem_stepReach φ _ _).mpr ⟨(mem_vars_of_implies hbc).2, Or.inr ⟨_, ih, hbc⟩⟩
      rwa [reachFrom_fixed] at hstep

/-- Every prefix of the greedy literal-selection fold stays a sublist of `lits φ`. -/
theorem foldl_chooseStep_sublist (φ : CNF V) :
    ∀ (vs : List V) (s : Clause V), s <+ lits φ → vs.foldl (chooseStep φ) s <+ lits φ
  | [], s, hs => hs
  | v :: vs, s, hs => by
    rw [List.foldl_cons]
    refine foldl_chooseStep_sublist φ vs _ ?_
    dsimp only [chooseStep]
    split_ifs
    · exact hs
    · exact List.filter_sublist

/-- Invariant maintained by `chooseStep`: occurring variables, consistency, and implication
closure. -/
private structure GoodSet (φ : CNF V) (s : Clause V) : Prop where
  vars : ∀ m ∈ s, m.1 ∈ φ.vars
  consistent : ∀ m ∈ s, m.negate ∉ s
  closed : ∀ m ∈ s, ∀ m', φ.Implies m m' → m' ∈ s

omit [DecidableEq V] in
private theorem GoodSet.reach_mem {φ : CNF V} {s : Clause V} (hg : GoodSet φ s)
    {m m' : Literal V} (hm : m ∈ s) (h : Relation.ReflTransGen φ.Implies m m') : m' ∈ s := by
  induction h with
  | refl => exact hm
  | tail _ hab ih => exact hg.closed _ ih _ hab

private theorem extendGoodSet {φ : CNF V} {s : Clause V} (hg : GoodSet φ s)
    {ℓ : Literal V} (hℓv : ℓ.1 ∈ φ.vars) (hnneg_s : ℓ.negate ∉ s)
    (hnreach : ¬ Relation.ReflTransGen φ.Implies ℓ ℓ.negate) :
    let s' := (lits φ).filter fun m => s.contains m || (reach φ ℓ).contains m
    GoodSet φ s' ∧ s ⊆ s' ∧ ℓ ∈ s' := by
  intro s'
  have hmem_s' : ∀ m, m ∈ s' ↔ m ∈ s ∨ Relation.ReflTransGen φ.Implies ℓ m := by
    intro m
    simp only [s', List.mem_filter, mem_lits_iff, Bool.or_eq_true, List.contains_iff_mem,
      mem_reach_iff hℓv]
    exact ⟨fun h => h.2, fun h => ⟨h.elim (hg.vars m) (mem_vars_of_reach hℓv), h⟩⟩
  refine ⟨⟨?_, ?_, ?_⟩, fun m hm => (hmem_s' m).mpr (.inl hm), (hmem_s' ℓ).mpr (.inr .refl)⟩
  · intro m hm
    exact ((hmem_s' m).mp hm).elim (hg.vars m) (mem_vars_of_reach hℓv)
  · intro m hm hmn
    rcases (hmem_s' m).mp hm with hms | hrm <;> rcases (hmem_s' m.negate).mp hmn with hmns | hrmn
    · exact hg.consistent m hms hmns
    · have hrev := CNF.reach_negate hrmn
      rw [negate_negate] at hrev
      exact hnneg_s (hg.reach_mem hms hrev)
    · have hrev := CNF.reach_negate hrm
      exact hnneg_s (hg.reach_mem hmns hrev)
    · have hrev := CNF.reach_negate hrmn
      rw [negate_negate] at hrev
      exact hnreach (hrm.trans hrev)
  · intro m hm m' himp
    refine (hmem_s' m').mpr ?_
    rcases (hmem_s' m).mp hm with hms | hrm
    · exact .inl (hg.closed m hms m' himp)
    · exact .inr (hrm.tail himp)

private theorem chooseStep_good {φ : CNF V}
    (hnocyc : ∀ x, ¬ (Relation.ReflTransGen φ.Implies (x, true) (x, false) ∧
      Relation.ReflTransGen φ.Implies (x, false) (x, true)))
    {s : Clause V} (hg : GoodSet φ s) {v : V} (hv : v ∈ φ.vars) :
    GoodSet φ (chooseStep φ s v) ∧ s ⊆ chooseStep φ s v ∧
      ((v, true) ∈ chooseStep φ s v ∨ (v, false) ∈ chooseStep φ s v) := by
  dsimp only [chooseStep]
  split_ifs with hdec
  · simp only [Bool.or_eq_true, List.contains_iff_mem] at hdec
    exact ⟨hg, fun _ h => h, hdec⟩
  · simp only [Bool.or_eq_true, List.contains_iff_mem, not_or] at hdec
    obtain ⟨hnt, hnf⟩ := hdec
    cases htf : (reach φ (v, true)).contains (v, false)
    · have hnreach : ¬ Relation.ReflTransGen φ.Implies (v, true) (v, false) := by
        intro h₁
        have hm := List.contains_iff_mem.mpr
          ((mem_reach_iff (φ := φ) (ℓ₀ := (v, true)) hv (v, false)).mpr h₁)
        exact Bool.false_ne_true (htf.symm.trans hm)
      obtain ⟨hg', hsub', hmem'⟩ := extendGoodSet (ℓ := (v, true)) hg hv
        (by simpa [Std.Sat.Literal.negate] using hnf)
        (by simpa [Std.Sat.Literal.negate] using hnreach)
      exact ⟨hg', hsub', .inl hmem'⟩
    · have h₁ : Relation.ReflTransGen φ.Implies (v, true) (v, false) :=
        (mem_reach_iff (φ := φ) (ℓ₀ := (v, true)) hv (v, false)).mp
          (List.contains_iff_mem.mp htf)
      have hnreach : ¬ Relation.ReflTransGen φ.Implies (v, false) (v, true) :=
        fun h₂ => hnocyc v ⟨h₁, h₂⟩
      obtain ⟨hg', hsub', hmem'⟩ := extendGoodSet (ℓ := (v, false)) hg hv
        (by simpa [Std.Sat.Literal.negate] using hnt)
        (by simpa [Std.Sat.Literal.negate] using hnreach)
      exact ⟨hg', hsub', .inr hmem'⟩

private theorem foldl_chooseStep_good {φ : CNF V}
    (hnocyc : ∀ x, ¬ (Relation.ReflTransGen φ.Implies (x, true) (x, false) ∧
      Relation.ReflTransGen φ.Implies (x, false) (x, true))) :
    ∀ (vs : List V) (s : Clause V),
      (∀ v ∈ vs, v ∈ φ.vars) →
      GoodSet φ s →
      GoodSet φ (vs.foldl (chooseStep φ) s) ∧
        s ⊆ vs.foldl (chooseStep φ) s ∧
        ∀ v ∈ vs, (v, true) ∈ vs.foldl (chooseStep φ) s ∨ (v, false) ∈ vs.foldl (chooseStep φ) s
  | [], s, _, hg => ⟨hg, fun _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | v :: vs, s, hvs, hg => by
    obtain ⟨hg₁, hsub₁, hv₁⟩ := chooseStep_good hnocyc hg (hvs v List.mem_cons_self)
    obtain ⟨hg₂, hsub₂, hvs₂⟩ := foldl_chooseStep_good hnocyc vs (chooseStep φ s v)
      (fun u hu => hvs u (List.mem_cons_of_mem v hu)) hg₁
    refine ⟨hg₂, fun u hu => hsub₂ (hsub₁ hu), fun u hu => ?_⟩
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hv₁.imp (fun h => hsub₂ h) (fun h => hsub₂ h)
    · exact hvs₂ u hu

/-- **Witness soundness**: whenever `φ` has width at most `2` and is satisfiable, `assignment φ`
satisfies `φ`. -/
theorem eval_assignment_of_satisfiable {φ : CNF V} (hw : ∀ c ∈ φ, c.length ≤ 2)
    (hsat : φ.Satisfiable) : φ.eval (assignment φ) = true := by
  have hnot := mt (CNF.not_satisfiable_iff_of_width_le_two hw).mpr (not_not.mpr hsat)
  push Not at hnot
  obtain ⟨hnil, hnocyc⟩ := hnot
  have hnocyc' : ∀ x, ¬ (Relation.ReflTransGen φ.Implies (x, true) (x, false) ∧
      Relation.ReflTransGen φ.Implies (x, false) (x, true)) :=
    fun x ⟨h₁, h₂⟩ => hnocyc x h₁ h₂
  have hbase : GoodSet φ [] :=
    ⟨fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  have hgood :
      GoodSet φ (chosenLiterals φ) ∧
        ∀ v ∈ φ.vars, (v, true) ∈ chosenLiterals φ ∨ (v, false) ∈ chosenLiterals φ := by
    obtain ⟨hg, -, hdec⟩ := foldl_chooseStep_good hnocyc' φ.vars [] (fun _ h => h) hbase
    exact ⟨hg, hdec⟩
  obtain ⟨hg, hdec⟩ := hgood
  have hlits_eval : ∀ m : Literal V, m ∈ chosenLiterals φ → assignment φ m.1 = m.2 := by
    rintro ⟨v, b⟩ hm
    cases b
    · have hnt : (v, true) ∉ chosenLiterals φ :=
        fun ht => hg.consistent (v, false) hm (by simpa [Std.Sat.Literal.negate] using ht)
      simp [assignment, hnt]
    · simp [assignment, hm]
  refine (CNF.eval_eq_true_iff _ _).mpr fun c hc => ?_
  have hc2 : c.length ≤ 2 := hw c hc
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
  · exact absurd hc hnil
  · have hav : a.1 ∈ φ.vars := CNF.mem_vars.mpr ⟨[a], hc, a.2, List.mem_singleton_self a⟩
    have ha_mem : a ∈ chosenLiterals φ := by
      rcases hdec a.1 hav with ht | hf
      · rcases a with ⟨v, p⟩
        cases p
        · have himp : φ.Implies (v, true) (v, false) :=
            ⟨[(v, false)], hc, by simp [Std.Sat.Literal.negate], by simp,
              fun m hm => .inl (by simpa [Std.Sat.Literal.negate] using hm)⟩
          exact hg.closed (v, true) ht (v, false) himp
        · exact ht
      · rcases a with ⟨v, p⟩
        cases p
        · exact hf
        · have himp : φ.Implies (v, false) (v, true) :=
            ⟨[(v, true)], hc, by simp [Std.Sat.Literal.negate], by simp,
              fun m hm => .inl (by simpa [Std.Sat.Literal.negate] using hm)⟩
          exact hg.closed (v, false) hf (v, true) himp
    exact (Clause.eval_eq_true_iff _ _).mpr ⟨a, List.mem_singleton_self a, hlits_eval a ha_mem⟩
  · have hav : a.1 ∈ φ.vars := CNF.mem_vars.mpr ⟨[a, b], hc, a.2, by simp⟩
    by_cases ha_mem : a ∈ chosenLiterals φ
    · exact (Clause.eval_eq_true_iff _ _).mpr ⟨a, by simp, hlits_eval a ha_mem⟩
    · have hna_mem : a.negate ∈ chosenLiterals φ := by
        rcases a with ⟨v, p⟩
        rcases hdec v hav with ht | hf
        · cases p
          · exact ht
          · exact absurd ht ha_mem
        · cases p
          · exact absurd hf ha_mem
          · exact hf
      have himp : φ.Implies a.negate b :=
        ⟨[a, b], hc, by simp [negate_negate], by simp,
          fun m hm => by simpa [negate_negate] using hm⟩
      have hb_mem : b ∈ chosenLiterals φ := hg.closed a.negate hna_mem b himp
      exact (Clause.eval_eq_true_iff _ _).mpr ⟨b, by simp, hlits_eval b hb_mem⟩
  · simp at hc2

/-- Correctness of the executable `solve` decider. -/
theorem solve_eq_true_iff (φ : CNF V) :
    solve φ = true ↔ (∀ c ∈ φ, c.length ≤ 2) ∧ φ.Satisfiable := by
  simp only [solve, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨hw, heval⟩ => ⟨hw, assignment φ, heval⟩,
    fun ⟨hw, hsat⟩ => ⟨hw, eval_assignment_of_satisfiable hw hsat⟩⟩

end Pure

/-! ### Multi-tape Turing-machine polynomial-time certificates on `CNF ℕ` -/

/-- `assignment φ` satisfies every formula `φ ∈ TwoSAT`. -/
theorem eval_assignment_of_mem {φ : CNF ℕ} (hφ : φ ∈ TwoSAT) :
    φ.eval (assignment φ) = true :=
  eval_assignment_of_satisfiable hφ.1 hφ.2

/-- `solve` decides `TwoSAT`. -/
theorem solve_eq_true_iff_mem (φ : CNF ℕ) : solve φ = true ↔ φ ∈ TwoSAT :=
  solve_eq_true_iff φ

@[fun_prop]
theorem computableInPolyTime_lits {α : Type} {encIn : α ↪ List Bool} {φ : α → CNF ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF) :
    ComputableInPolyTime (fun a => lits (φ a)) encIn (encClause encNat) := by
  unfold lits
  fun_prop

@[fun_prop]
theorem computableInPolyTime_hasImpEdge {α : Type} {encIn : α ↪ List Bool}
    {φ : α → CNF ℕ} {ℓ ℓ' : α → Literal ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF)
    (hℓ : ComputableInPolyTime ℓ encIn (encPair encNat encBool))
    (hℓ' : ComputableInPolyTime ℓ' encIn (encPair encNat encBool)) :
    ComputableInPolyTime (fun a => hasImpEdge (φ a) (ℓ a) (ℓ' a)) encIn encBool := by
  simp only [hasImpEdge, List.contains_eq_mem]
  fun_prop

@[fun_prop]
theorem computableInPolyTime_stepReach :
    ComputableInPolyTime (fun p : CNF ℕ × Clause ℕ => stepReach p.1 p.2)
      (encPair encCNF (encClause encNat)) (encClause encNat) := by
  simp only [stepReach, List.contains_eq_mem]
  fun_prop

private theorem computableInPolyTime_reachPair :
    ComputableInPolyTime (fun p : CNF ℕ × Literal ℕ => reach p.1 p.2)
      (encPair encCNF (encPair encNat encBool)) (encClause encNat) := by
  have hcount :
      ComputableInPolyTime (fun p : CNF ℕ × Literal ℕ => p.1.numVars + p.1.numVars + 1)
        (encPair encCNF (encPair encNat encBool)) encUnary := by
    fun_prop
  have hinit :
      ComputableInPolyTime (fun p : CNF ℕ × Literal ℕ => (lits p.1).filter (· == p.2))
        (encPair encCNF (encPair encNat encBool)) (encClause encNat) := by
    fun_prop
  exact ComputableInPolyTime.iterateWith
    (.fst encCNF (encPair encNat encBool))
    hcount
    hinit
    computableInPolyTime_stepReach
    (computableInPolyTime_lits (.fst encCNF (encPair encNat encBool))).polyBounded_length
    (fun p i _ => length_encList_sublist (encPair encNat encBool) (reachFrom_sublist p.1 p.2 i))

/-- Computing reachable literals from `ℓ₀` in `φ` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_reach {α : Type} {encIn : α ↪ List Bool}
    {φ : α → CNF ℕ} {ℓ₀ : α → Literal ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF)
    (hℓ₀ : ComputableInPolyTime ℓ₀ encIn (encPair encNat encBool)) :
    ComputableInPolyTime (fun a => reach (φ a) (ℓ₀ a)) encIn (encClause encNat) :=
  computableInPolyTime_reachPair.comp (hφ.prod hℓ₀)

@[fun_prop]
theorem computableInPolyTime_chooseStep :
    ComputableInPolyTime (fun p : (CNF ℕ × Clause ℕ) × ℕ => chooseStep p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF (encClause encNat)) encNat) (encClause encNat) := by
  have hcond :
      ComputableInPolyTime
        (fun p : (CNF ℕ × Clause ℕ) × ℕ =>
          p.1.2.contains (p.2, true) || p.1.2.contains (p.2, false))
        (encPair (encPair encCNF (encClause encNat)) encNat) encBool := by
    simp only [List.contains_eq_mem]
    fun_prop
  have helse :
      ComputableInPolyTime
        (fun p : (CNF ℕ × Clause ℕ) × ℕ =>
          let ℓ : Literal ℕ := (p.2, !(reach p.1.1 (p.2, true)).contains (p.2, false))
          (lits p.1.1).filter fun m => p.1.2.contains m || (reach p.1.1 ℓ).contains m)
        (encPair (encPair encCNF (encClause encNat)) encNat) (encClause encNat) := by
    simp only [List.contains_eq_mem]
    fun_prop
  exact ComputableInPolyTime.ite hcond
    ((ComputableInPolyTime.snd encCNF (encClause encNat)).comp
      (.fst (encPair encCNF (encClause encNat)) encNat))
    helse

/-- Building the consistent implication-closed literal list is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_chosenLiterals :
    ComputableInPolyTime (chosenLiterals (V := ℕ)) encCNF (encClause encNat) :=
  ComputableInPolyTime.foldlWith
    .id'
    SAT.computableInPolyTime_vars
    (.const [])
    computableInPolyTime_chooseStep
    (computableInPolyTime_lits .id').polyBounded_length
    (fun φ i _ => length_encList_sublist (encPair encNat encBool)
      (foldl_chooseStep_sublist φ (φ.vars.take i) [] (List.nil_sublist _)))

/-- Evaluating the satisfying-assignment constructor on `(φ, v)` is native multi-tape
polynomial-time under `encPair encCNF encNat`. -/
@[fun_prop]
theorem computableInPolyTime_assignment :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => assignment p.1 p.2)
      (encPair encCNF encNat) encBool := by
  simp only [assignment, List.contains_eq_mem]
  fun_prop

/-- Native multi-tape polynomial-time certificate for the total `TwoSAT` decider. -/
@[fun_prop]
theorem computableInPolyTime_solve :
    ComputableInPolyTime (solve (V := ℕ)) encCNF encBool := by
  have hw :
      ComputableInPolyTime (fun c : Clause ℕ => decide (c.length ≤ 2))
        (encClause encNat) encBool :=
    ComputableInPolyTime.unary_le' (Clause.computableInPolyTime_length .id') (.const 2)
  unfold solve
  fun_prop

/-- **`TwoSAT` is in `P`** under the binary CNF encoding `encCNF`. -/
theorem mem_P : TwoSAT ∈ P encCNF :=
  ⟨solve, computableInPolyTime_solve, fun φ => (solve_eq_true_iff_mem φ).symm⟩

end Cslib.Complexity.TwoSAT
