/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Horn
public import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
public import CslibFrontier.Computability.Complexity.Classes.P
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Mathlib.Data.Finset.Card

/-!
# Horn satisfiability by forward chaining

The state lists forced variables in their input occurrence order. Each pass filters the input
variable list, so even exponentially large binary variable labels require no dense array.
After at most the number of distinct occurring variables plus one passes, the state is closed under
all positive Horn implications. Evaluating the original formula under this least assignment
also checks negative-only constraints, including the empty clause.

Horn recognition counts positive occurrences, including repetitions. Negative occurrences may
repeat, clauses may be tautological, and the empty formula is accepted.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Ordinary Horn satisfiability on CNF formulas with binary natural-number variable names. -/
@[expose] def HornSAT : Set (CNF ℕ) := {φ | φ.IsHorn ∧ φ.Satisfiable}

namespace HornSAT

variable {V : Type*} [DecidableEq V]

/-- Every negative antecedent is already forced. Positive literals impose no antecedent. -/
@[expose] def enabled (s : List V) (c : Clause V) : Bool :=
  c.all fun l => l.2 || s.contains l.1

/-- One simultaneous pass; the output is a sublist of the input's occurring variables. -/
@[expose] def step (φ : CNF V) (s : List V) : List V :=
  φ.vars.filter fun v => s.contains v ||
    φ.any fun c => c.contains (v, true) && enabled s c

/-- The forced variables after `n` simultaneous passes. -/
@[expose] def forced (φ : CNF V) (n : ℕ) : List V := (step φ)^[n] []

/-- The least-model candidate, with a budget determined by occurrences rather than labels. -/
@[expose] def assignment (φ : CNF V) (v : V) : Bool :=
  (forced φ (φ.numVars + 1)).contains v

/-- Check Horn syntax and the least-model candidate. -/
@[expose] def solve (φ : CNF V) : Bool :=
  φ.all (fun c => decide ((c.filter Prod.snd).length ≤ 1)) && φ.eval (assignment φ)

theorem enabled_eq_true_iff (s : List V) (c : Clause V) :
    enabled s c = true ↔ ∀ l ∈ c, l.2 = false → l.1 ∈ s := by
  simp only [enabled, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem]
  constructor
  · intro h l hl hn
    simpa [hn] using h l hl
  · intro h l hl
    cases hs : l.2
    · exact Or.inr (h l hl hs)
    · exact Or.inl rfl

theorem mem_step (φ : CNF V) (s : List V) (v : V) :
    v ∈ step φ s ↔ v ∈ φ.vars ∧
      (v ∈ s ∨ ∃ c ∈ φ, (v, true) ∈ c ∧ enabled s c = true) := by
  simp [step, List.mem_filter, List.any_eq_true]

/-- Every intermediate state has occurrence-bounded storage. -/
theorem forced_sublist (φ : CNF V) (n : ℕ) : List.Sublist (forced φ n) φ.vars := by
  cases n with
  | zero => exact List.nil_sublist _
  | succ n =>
    rw [forced, Function.iterate_succ_apply']
    exact List.filter_sublist

/-- Forward chaining is inflationary on its reachable states. -/
theorem forced_subset_succ (φ : CNF V) (n : ℕ) :
    forced φ n ⊆ forced φ (n + 1) := by
  intro v hv
  rw [forced, Function.iterate_succ_apply']
  exact (mem_step φ _ v).mpr ⟨(forced_sublist φ n).subset hv, Or.inl hv⟩

private theorem step_congr (φ : CNF V) {s t : List V} (h : ∀ v, v ∈ s ↔ v ∈ t) :
    step φ s = step φ t := by
  have he : ∀ v, s.contains v = t.contains v := by
    intro v
    apply Bool.eq_iff_iff.mpr
    simpa only [List.contains_iff_mem] using h v
  simp only [step, enabled, he]

/-- Every variable forced by any pass is true in every model. -/
theorem forced_le_model {φ : CNF V} (hφ : φ.IsHorn) {σ : V → Bool}
    (hσ : φ.eval σ = true) (n : ℕ) : ∀ v ∈ forced φ n, σ v = true := by
  induction n with
  | zero => simp [forced]
  | succ n ih =>
    intro v hv
    rw [forced, Function.iterate_succ_apply'] at hv
    obtain ⟨_, hv | ⟨c, hc, hvc, hen⟩⟩ := (mem_step φ _ v).mp hv
    · exact ih v hv
    · obtain ⟨l, hl, hsl⟩ := (Clause.eval_eq_true_iff _ _).mp
        ((CNF.eval_eq_true_iff _ _).mp hσ c hc)
      cases hs : l.2 with
      | false =>
        have hmem := (enabled_eq_true_iff _ _).mp hen l hl hs
        have ht := ih l.1 hmem
        simp_all
      | true =>
        have heq := (hφ c hc).positive_unique hl hvc hs rfl
        simpa [heq] using hsl

/-- The loop reaches a fixed point within the number of distinct occurring variables plus one
passes. The bound is independent of their numerical labels and repeated occurrences. -/
theorem forced_fixed (φ : CNF V) :
    step φ (forced φ (φ.numVars + 1)) = forced φ (φ.numVars + 1) := by
  classical
  let s (n : ℕ) := (forced φ n).toFinset
  have hincl (n : ℕ) : s n ⊆ s (n + 1) := by
    intro v hv
    exact List.mem_toFinset.mpr (forced_subset_succ φ n (List.mem_toFinset.mp hv))
  have hmono : Monotone (fun n => (s n).card) :=
    monotone_nat_of_le_succ fun n => Finset.card_le_card (hincl n)
  have hbound (n : ℕ) : (s n).card ≤ φ.numVars := by
    have hsub : s n ⊆ φ.vars.toFinset := by
      intro v hv
      exact List.mem_toFinset.mpr ((forced_sublist φ n).subset (List.mem_toFinset.mp hv))
    exact Finset.card_le_card hsub
  have heq (n : ℕ) (h : (s n).card = (s (n + 1)).card) : s n = s (n + 1) :=
    Finset.eq_of_subset_of_card_le (hincl n) h.ge
  have hnext (n : ℕ) (h : (s n).card = (s (n + 1)).card) :
      forced φ (n + 1) = forced φ (n + 2) := by
    have hm (v : V) : v ∈ forced φ n ↔ v ∈ forced φ (n + 1) := by
      have hm := Finset.ext_iff.mp (heq n h) v
      simpa only [s, List.mem_toFinset] using hm
    simpa only [forced, Function.iterate_succ_apply'] using step_congr φ hm
  have hstab (n : ℕ) (h : (s n).card = (s (n + 1)).card) :
      (s (n + 1)).card = (s (n + 2)).card := by
    simp only [s, hnext n h]
  have hc := Nat.stabilises_of_monotone hmono hbound hstab
    (n := φ.numVars + 1) (by omega)
  have hl := hnext φ.numVars hc.symm
  simpa only [forced, Function.iterate_succ_apply'] using hl.symm

/-- If a model exists, the closed forced assignment satisfies every clause. -/
theorem eval_assignment_of_satisfiable {φ : CNF V} (hφ : φ.IsHorn)
    (hsat : φ.Satisfiable) : φ.eval (assignment φ) = true := by
  obtain ⟨σ, hσ⟩ := hsat
  apply (CNF.eval_eq_true_iff _ _).mpr
  intro c hc
  obtain ⟨l, hl, hsl⟩ := (Clause.eval_eq_true_iff _ _).mp
    ((CNF.eval_eq_true_iff _ _).mp hσ c hc)
  by_cases hen : enabled (forced φ (φ.numVars + 1)) c = true
  · have hs : l.2 = true := by
      cases hs : l.2
      · have hm := (enabled_eq_true_iff _ _).mp hen l hl hs
        have ht := forced_le_model hφ hσ _ l.1 hm
        simp_all
      · rfl
    have hm : l.1 ∈ step φ (forced φ (φ.numVars + 1)) :=
      (mem_step φ _ _).mpr ⟨CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩,
        Or.inr ⟨c, hc, by simpa only [← hs, Prod.eta] using hl, hen⟩⟩
    rw [forced_fixed] at hm
    exact (Clause.eval_eq_true_iff _ _).mpr
      ⟨l, hl, by simpa [assignment, hs] using hm⟩
  · have hn : ∃ l ∈ c, l.2 = false ∧ l.1 ∉ forced φ (φ.numVars + 1) := by
      have hn := mt (enabled_eq_true_iff _ _).mpr hen
      push Not at hn
      exact hn
    obtain ⟨k, hk, hs, hm⟩ := hn
    exact (Clause.eval_eq_true_iff _ _).mpr ⟨k, hk, by simp [assignment, hs, hm]⟩

/-- Correctness of the executable decider for ordinary HornSAT. -/
theorem solve_eq_true_iff (φ : CNF V) : solve φ = true ↔ φ.IsHorn ∧ φ.Satisfiable := by
  have hsyntax : φ.all (fun c => decide ((c.filter Prod.snd).length ≤ 1)) = true ↔
      φ.IsHorn := by simp [CNF.IsHorn, Clause.IsHorn]
  simp only [solve, Bool.and_eq_true, hsyntax]
  exact ⟨fun ⟨hφ, heval⟩ => ⟨hφ, assignment φ, heval⟩,
    fun ⟨hφ, hsat⟩ => ⟨hφ, eval_assignment_of_satisfiable hφ hsat⟩⟩

/-- One pass is a native polynomial-time computation on binary variable labels. -/
@[fun_prop]
theorem computableInPolyTime_step :
    ComputableInPolyTime (fun p : CNF ℕ × List ℕ => step p.1 p.2)
      (encPair encCNF (encList encNat)) (encList encNat) := by
  simp only [step, enabled, List.contains_eq_mem]
  fun_prop

/-- The entire forward-chaining loop is polynomial-time. Every state is a filtered copy of the
occurring-variable list, whose encoding length is polynomially bounded by the input encoding. -/
@[fun_prop]
theorem computableInPolyTime_forced :
    ComputableInPolyTime (fun φ : CNF ℕ => forced φ (φ.numVars + 1))
      encCNF (encList encNat) := by
  have hcount : ComputableInPolyTime (fun φ : CNF ℕ => φ.numVars + 1)
      encCNF encUnary := by fun_prop
  exact ComputableInPolyTime.iterateWith .id' hcount (.const [])
    computableInPolyTime_step SAT.computableInPolyTime_vars.polyBounded_length
    (fun φ n _ => length_encList_sublist encNat (forced_sublist φ n))

/-- Reading a variable from the least-model candidate is polynomial-time, even for a label
larger than every label occurring in the formula. -/
@[fun_prop]
theorem computableInPolyTime_assignment :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => assignment p.1 p.2)
      (encPair encCNF encNat) encBool := by
  simp only [assignment, List.contains_eq_mem]
  exact ComputableInPolyTime.decide_mem
    (computableInPolyTime_forced.comp (.fst encCNF encNat)) (.snd encCNF encNat)

/-- Native polynomial-time certificate for the total HornSAT decider. -/
@[fun_prop]
theorem computableInPolyTime_solve :
    ComputableInPolyTime (solve (V := ℕ)) encCNF encBool := by
  fun_prop [solve, CNF.eval, Clause.eval, Literal.eval]

/-- Ordinary HornSAT is in native multi-tape polynomial time under `encCNF`. -/
theorem mem_P : HornSAT ∈ P encCNF :=
  ⟨solve, computableInPolyTime_solve, fun φ => (solve_eq_true_iff φ).symm⟩

end HornSAT

/-- Satisfiable dual Horn formulas under the same binary CNF encoding. -/
@[expose] def DualHornSAT : Set (CNF ℕ) := {φ | φ.IsDualHorn ∧ φ.Satisfiable}

namespace DualHornSAT

/-- Dual Horn satisfiability reduces to Horn satisfiability by flipping literal polarities. -/
@[expose] def solve (φ : CNF ℕ) : Bool := HornSAT.solve φ.flip

/-- Correctness of the dual Horn decider. -/
theorem solve_eq_true_iff (φ : CNF ℕ) : solve φ = true ↔ φ ∈ DualHornSAT := by
  simp only [solve, HornSAT.solve_eq_true_iff, CNF.satisfiable_flip, DualHornSAT,
    CNF.IsDualHorn, Set.mem_ofPred_eq]

/-- Polarity flipping changes no labels and is polynomial-time under the original encoding. -/
@[fun_prop]
theorem computableInPolyTime_flip :
    ComputableInPolyTime (CNF.flip (V := ℕ)) encCNF encCNF := by
  fun_prop [CNF.flip, Clause.flip]

/-- Native polynomial-time certificate for dual Horn satisfiability. -/
@[fun_prop]
theorem computableInPolyTime_solve :
    ComputableInPolyTime solve encCNF encBool := by
  fun_prop [solve]

/-- Ordinary dual HornSAT is in native multi-tape polynomial time. -/
theorem mem_P : DualHornSAT ∈ P encCNF :=
  ⟨solve, computableInPolyTime_solve, fun φ => (solve_eq_true_iff φ).symm⟩

end DualHornSAT

end Cslib.Complexity
