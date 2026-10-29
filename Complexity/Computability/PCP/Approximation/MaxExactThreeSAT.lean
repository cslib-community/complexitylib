/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.MaxThreeSAT
public import Complexity.Computability.Complexity.Problems.ExactThreeSAT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# MAX-E3SAT: NP-hardness of approximation and the `7 / 8` random-assignment bound

`GapExactThreeSAT s` is the gap problem of MAX-3SAT (`Cslib.Complexity.GapThreeSAT`) restricted
to formulas all of whose clauses have exactly three, not necessarily distinct, literals. Here
"MAX-E3SAT" (`Cslib.Complexity.GapExactThreeSAT`) allows repeated literals in a clause, as
`Cslib.Complexity.ExactThreeSAT` does. Its yes-instances are the members of
`Cslib.Complexity.ExactThreeSAT`.

The gap of MAX-3SAT transfers unchanged: repeating a literal of every clause with one or two
literals (`Cslib.Complexity.toExactThreeSAT`) changes neither the value of a clause nor the number
of clauses, so every assignment falsifies the same clauses. An empty clause cannot be padded; a
formula with one is unsatisfiable, so it is mapped to a fixed formula
(`Cslib.Complexity.GapExactThreeSAT.contradiction`) in which every assignment falsifies one of two
clauses, a no-instance for every soundness `s ≥ 1 / 2`. Hence distinguishing satisfiable formulas
with clauses of exactly three literals from those in which every assignment satisfies at most the
proportion `1 - 1 / (3 * 2 ^ 77)` of the clauses is NP-hard
(`Cslib.Complexity.GapExactThreeSAT_npHard`) [Arora, Lund, Motwani, Sudan and
Szegedy][AroraLundMotwaniSudanSzegedy1998].

In the other direction, when the three variables of every clause are distinct
(`Cslib.Logic.PL.CNF.IsExactThreeDistinct`), a uniform random assignment falsifies each clause
with probability `1 / 8` (`Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_false`), so
some assignment falsifies at most `1 / 8` of the clauses
(`Cslib.Logic.PL.CNF.IsExactThreeDistinct.unsatVal_le_one_eighth`, developed in
`Complexity.Logics.Propositional.CNF.UnsatVal` and re-exported here). Håstad showed that this
`7 / 8` threshold is optimal [Hastad2001]; that hardness result is not formalized here.

## Main definitions

* `Cslib.Complexity.GapExactThreeSAT`: the gap problem of MAX-E3SAT with perfect completeness.
* `Cslib.Complexity.GapExactThreeSAT.reduce`: the reduction from `GapThreeSAT`.

## Main results

* `Cslib.Complexity.yes_GapExactThreeSAT`, `Cslib.Complexity.mem_no_GapExactThreeSAT`: the
  instances of the gap problem.
* `Cslib.Complexity.polyTimeReducible_GapThreeSAT_GapExactThreeSAT`: MAX-3SAT reduces to
  MAX-E3SAT with the same gap, for every soundness `1 / 2 ≤ s < 1`.
* `Cslib.Complexity.GapExactThreeSAT_npHard`: MAX-E3SAT, with repeated literals allowed, is
  NP-hard to approximate within `1 - 1 / (3 * 2 ^ 77)`.
* `Cslib.Complexity.GapExactThreeSAT_notMem_PromiseP`: unless `P = NP`, no polynomial-time
  algorithm separates its gap problem.

## References

* [S. Arora, C. Lund, R. Motwani, M. Sudan, M. Szegedy, *Proof verification and the hardness of
  approximation problems*][AroraLundMotwaniSudanSzegedy1998]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The gap problem of **MAX-E3SAT** with perfect completeness and soundness `s`: the gap problem
of MAX-3SAT (`GapThreeSAT`) on the formulas all of whose clauses have exactly three literals, not
necessarily distinct. -/
noncomputable def GapExactThreeSAT (s : ℝ) : PromiseProblem (CNF ℕ) :=
  (GapThreeSAT s).restrict {φ | ∀ c ∈ φ, c.length = 3}

variable {s : ℝ} {φ : CNF ℕ}

/-- The yes-instances of `GapExactThreeSAT` are the members of `ExactThreeSAT`. -/
theorem yes_GapExactThreeSAT : (GapExactThreeSAT s).yes = ExactThreeSAT := by
  ext φ
  simp only [GapExactThreeSAT, PromiseProblem.yes_restrict, yes_GapThreeSAT, Set.mem_inter_iff,
    ThreeSAT, ExactThreeSAT, Set.mem_ofPred_eq]
  exact ⟨fun ⟨⟨_, h⟩, h3⟩ => ⟨h3, h⟩, fun ⟨h3, h⟩ => ⟨⟨fun c hc => (h3 c hc).le, h⟩, h3⟩⟩

/-- For `s < 1`, the no-instances of `GapExactThreeSAT` are the formulas with clauses of exactly
three literals in which every assignment falsifies at least the proportion `1 - s` of the
clauses. -/
theorem mem_no_GapExactThreeSAT (hs : s < 1) :
    φ ∈ (GapExactThreeSAT s).no ↔ (∀ c ∈ φ, c.length = 3) ∧ 1 - s ≤ φ.unsatVal := by
  simp only [GapExactThreeSAT, PromiseProblem.no_restrict, Set.mem_inter_iff,
    mem_no_GapThreeSAT hs, Set.mem_ofPred_eq]
  exact ⟨fun ⟨⟨_, h⟩, h3⟩ => ⟨h3, h⟩, fun ⟨h3, h⟩ => ⟨⟨fun c hc => (h3 c hc).le, h⟩, h3⟩⟩

namespace GapExactThreeSAT

/-- A formula with two clauses of three literals, `x₀ ∨ x₀ ∨ x₀` and `¬x₀ ∨ ¬x₀ ∨ ¬x₀`: every
assignment falsifies exactly one of them. -/
def contradiction : CNF ℕ :=
  [[(0, true), (0, true), (0, true)], [(0, false), (0, false), (0, false)]]

/-- Every assignment falsifies half of the clauses of `contradiction`. -/
theorem unsatVal_contradiction : contradiction.unsatVal = 1 / 2 := by
  have hcount (σ : ℕ → Bool) : contradiction.countUnsat σ = 1 := by
    cases h : σ 0 <;> simp [contradiction, CNF.countUnsat, h]
  have hlen : contradiction.length = 2 := rfl
  refine le_antisymm ?_ ((CNF.le_unsatVal_iff _).2 fun σ => ?_)
  · simpa [hcount, hlen] using contradiction.unsatVal_le fun _ => false
  · simp [hcount, hlen]

/-- **The reduction from MAX-3SAT to MAX-E3SAT**: a formula with an empty clause goes to
`contradiction`; otherwise every clause with one or two literals is padded to three by repeating a
literal (`toExactThreeSAT`). -/
def reduce (φ : CNF ℕ) : CNF ℕ :=
  if φ.any List.isEmpty then contradiction else toExactThreeSAT φ

/-- Padding the clauses does not change the number of clauses an assignment falsifies. -/
theorem countUnsat_toExactThreeSAT (σ : ℕ → Bool) (φ : CNF ℕ) :
    (toExactThreeSAT φ).countUnsat σ = φ.countUnsat σ := by
  simp only [toExactThreeSAT, CNF.countUnsat, List.countP_map, Function.comp_def,
    ExactThreeSAT.eval_padClause]

/-- Padding the clauses does not change the value of a formula. -/
theorem unsatVal_toExactThreeSAT (φ : CNF ℕ) :
    (toExactThreeSAT φ).unsatVal = φ.unsatVal := by
  unfold CNF.unsatVal
  simp only [countUnsat_toExactThreeSAT]
  rw [toExactThreeSAT, List.length_map]

/-- The reduction is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_reduce : ComputableInPolyTime reduce encCNF encCNF := by
  unfold reduce
  have hempty : ComputableInPolyTime (List.isEmpty : Clause ℕ → Bool)
      (encList (encPair encNat encBool)) encBool := by
    obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.isEmpty
      (enc₁ := encPair encNat encBool) (enc := encList (encPair encNat encBool))
    exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
      k, Q, hfin, tm, fun l => htm l⟩
  have hany : ComputableInPolyTime (fun φ : CNF ℕ => φ.any List.isEmpty) encCNF encBool :=
    ComputableInPolyTime.anyWithInput (ComputableInPolyTime.id' (encIn := encCNF))
      (hempty.comp (ComputableInPolyTime.snd _ _))
  exact ComputableInPolyTime.ite hany (.const _) computableInPolyTime_toExactThreeSAT

end GapExactThreeSAT

open GapExactThreeSAT

/-- **MAX-3SAT reduces to MAX-E3SAT with the same gap**, repeated literals allowed, for every
soundness `1 / 2 ≤ s < 1`, by `GapExactThreeSAT.reduce`. -/
theorem polyTimeReducible_GapThreeSAT_GapExactThreeSAT (hs : 1 / 2 ≤ s) (hs1 : s < 1) :
    PromiseProblem.PolyTimeReducible encCNF encCNF (GapThreeSAT s) (GapExactThreeSAT s) := by
  refine ⟨reduce, computableInPolyTime_reduce, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [yes_GapThreeSAT] at hφ
    rw [yes_GapExactThreeSAT]
    have hne : φ.any List.isEmpty = false := by
      rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
      rintro ⟨c, hc, hce⟩
      obtain ⟨σ, hσ⟩ := hφ.2
      have := (CNF.eval_eq_true_iff σ φ).1 hσ c hc
      rw [List.isEmpty_iff.1 hce, Clause.eval_nil] at this
      exact Bool.false_ne_true this
    rw [reduce, hne]
    exact (mem_ExactThreeSAT_toExactThreeSAT_iff φ).2 hφ
  · rw [mem_no_GapExactThreeSAT hs1]
    rw [mem_no_GapThreeSAT hs1] at hφ
    unfold reduce
    split_ifs with he
    · refine ⟨fun c hc => ?_, ?_⟩
      · simp only [contradiction, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl
      · rw [unsatVal_contradiction]
        linarith
    · refine ⟨fun c hc => ?_, by rw [unsatVal_toExactThreeSAT]; exact hφ.2⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      refine ExactThreeSAT.length_padClause (fun h0 => he ?_) (hφ.1 d hd)
      exact List.any_eq_true.2 ⟨d, hd, by simp [h0]⟩

/-- **MAX-E3SAT is NP-hard to approximate** [AroraLundMotwaniSudanSzegedy1998]: distinguishing
satisfiable formulas with exactly three, not necessarily distinct, literals per clause from those in
which every assignment satisfies at most the proportion `1 - 1 / (3 * 2 ^ 77)` of the clauses is
NP-hard. -/
theorem GapExactThreeSAT_npHard :
    PromiseProblem.NPHard encCNF (GapExactThreeSAT (1 - 1 / (3 * 2 ^ 77))) :=
  GapThreeSAT_npHard.trans
    (polyTimeReducible_GapThreeSAT_GapExactThreeSAT (by norm_num) (by norm_num))

/-- Unless `P = NP`, no polynomial-time algorithm distinguishes satisfiable formulas with exactly
three, not necessarily distinct, literals per clause from those in which every assignment satisfies
at most the proportion `1 - 1 / (3 * 2 ^ 77)` of the clauses. -/
theorem GapExactThreeSAT_notMem_PromiseP {β : Type} {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapExactThreeSAT (1 - 1 / (3 * 2 ^ 77)) ∉ PromiseP encCNF :=
  GapExactThreeSAT_npHard.notMem_PromiseP h

end Cslib.Complexity
