/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SubsetSum
public import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Sequencing with deadlines and penalties

`JobSequencing` is Karp's problem JOB SEQUENCING [Karp1972], the problem SEQUENCING TO MINIMIZE
TARDY TASK WEIGHT of [Garey and Johnson, Problem SS3][GareyJohnson1979]: given jobs
`(time, deadline, penalty)` and a bound `k`, some order of the jobs, run one after another from
time `0` without idle time, has total penalty at most `k`, where a job pays its penalty when it
completes after its deadline.
All numbers are natural numbers in binary (`encNat`); orders are permutations (`List.Perm`) of the
list of jobs, so repeated jobs are scheduled with multiplicity.

Karp's reduction from `SubsetSum` (his KNAPSACK) maps the numbers `a` and target `t` to the jobs
`(a, t, a)`, of time and penalty `a` and common deadline `t`, with penalty bound `a.sum - t`
(`SubsetSum.toJobSequencing`). The jobs completed on time in an order hold numbers of total at
most `t`, and the others pay their whole time as penalty, so the bound is met exactly when the
jobs on time sum to `t`. A target above `a.sum` is mapped to a fixed instance without a feasible
order, since then the subtraction would truncate.

`NP` membership uses the order itself as the witness (`Turing.MultiTapeTM.Decoder.list`): the
verifier checks that it is a permutation of the jobs by counting occurrences, and computes its
total penalty in closed form from prefix sums.

## Main definitions

* `Cslib.Complexity.JobSequencing.penaltyFrom`, `Cslib.Complexity.JobSequencing.totalPenalty`:
  the total penalty of an order.
* `Cslib.Complexity.JobSequencing`, `Cslib.Complexity.encJobSequencing`.
* `Cslib.Complexity.SubsetSum.toJobSequencing`: Karp's reduction.

## Main results

* `Cslib.Complexity.JobSequencing.penaltyFrom_append`: penalties of consecutive runs add up.
* `Cslib.Complexity.JobSequencing.computableInPolyTime_totalPenalty`: the total penalty of an
  order is polynomial-time.
* `Cslib.Complexity.JobSequencing.mem_NP`: `JobSequencing ∈ NP encJobSequencing`.
* `Cslib.Complexity.SubsetSum.toJobSequencing_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.polyTimeReducible_SubsetSum_JobSequencing`,
  `Cslib.Complexity.JobSequencing_npHard`, `Cslib.Complexity.JobSequencing_npComplete`:
  `JobSequencing` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime
open scoped List

namespace JobSequencing

/-- The total penalty of the jobs `(time, deadline, penalty)` run in the given order, one after
another without idle time, from time `s`: a job pays its penalty when it completes after its
deadline. -/
def penaltyFrom : ℕ → List (ℕ × ℕ × ℕ) → ℕ
  | _, [] => 0
  | s, (time, deadline, penalty) :: σ =>
    (if deadline < s + time then penalty else 0) + penaltyFrom (s + time) σ

/-- The total penalty of the jobs `(time, deadline, penalty)` run in the given order from
time `0`. -/
def totalPenalty (σ : List (ℕ × ℕ × ℕ)) : ℕ := penaltyFrom 0 σ

/-- The penalties of two consecutive runs add up; the second starts when the first ends. -/
theorem penaltyFrom_append (s : ℕ) (σ τ : List (ℕ × ℕ × ℕ)) :
    penaltyFrom s (σ ++ τ) = penaltyFrom s σ + penaltyFrom (s + (σ.map Prod.fst).sum) τ := by
  induction σ generalizing s with
  | nil => simp only [List.nil_append, penaltyFrom, List.map_nil, List.sum_nil, Nat.add_zero,
      Nat.zero_add]
  | cons x σ ih =>
    obtain ⟨time, deadline, penalty⟩ := x
    simp only [List.cons_append, penaltyFrom, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

end JobSequencing

/-- Instances of `JobSequencing` are encoded as a list of jobs `(time, deadline, penalty)` and a
penalty bound, all in binary. -/
abbrev encJobSequencing : List (ℕ × ℕ × ℕ) × ℕ ↪ List Bool :=
  encPair (encList (encPair encNat (encPair encNat encNat))) encNat

/-- **Sequencing with deadlines and penalties** [Karp1972]: some order of the jobs
`(time, deadline, penalty)` has total penalty at most the bound. -/
def JobSequencing : Set (List (ℕ × ℕ × ℕ) × ℕ) :=
  {x | ∃ σ, σ ~ x.1 ∧ JobSequencing.totalPenalty σ ≤ x.2}

namespace JobSequencing

/-- The total penalty in closed form: the `i`-th job completes at the sum of the times of the
first `i + 1` jobs. -/
private theorem penaltyFrom_eq (s : ℕ) (σ : List (ℕ × ℕ × ℕ)) :
    penaltyFrom s σ = ((List.range σ.length).map fun i =>
      if (σ.getD i (0, 0, 0)).2.1 < s + ((σ.take (i + 1)).map Prod.fst).sum then
        (σ.getD i (0, 0, 0)).2.2 else 0).sum := by
  induction σ generalizing s with
  | nil => rfl
  | cons x σ ih =>
    obtain ⟨time, deadline, penalty⟩ := x
    rw [penaltyFrom, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, List.getD_cons_succ, List.take_succ_cons, List.map_cons,
      List.sum_cons, Nat.add_assoc]

/-- The total penalty of an order is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_totalPenalty :
    ComputableInPolyTime totalPenalty (encList (encPair encNat (encPair encNat encNat)))
      encNat := by
  have h : totalPenalty = fun σ : List (ℕ × ℕ × ℕ) => ((List.range σ.length).map fun i =>
      if (σ.getD i (0, 0, 0)).2.1 < ((σ.take (i + 1)).map Prod.fst).sum then
        (σ.getD i (0, 0, 0)).2.2 else 0).sum := by
    funext σ
    simpa only [totalPenalty, Nat.zero_add] using penaltyFrom_eq 0 σ
  rw [h]
  fun_prop

/-- The check of an order against an instance: it is a permutation of the jobs, by counting
occurrences, and its total penalty is within the bound. -/
private def check (y : (List (ℕ × ℕ × ℕ) × ℕ) × List (ℕ × ℕ × ℕ)) : Bool :=
  ((y.2 ++ y.1.1).all fun j => decide (y.2.count j = y.1.1.count j)) &&
    decide (totalPenalty y.2 ≤ y.1.2)

private theorem check_iff (x : List (ℕ × ℕ × ℕ) × ℕ) (σ : List (ℕ × ℕ × ℕ)) :
    check (x, σ) = true ↔ σ ~ x.1 ∧ totalPenalty σ ≤ x.2 := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_append]
  refine and_congr_left fun _ => ⟨fun h => List.perm_iff_count.2 fun j => ?_,
    fun h j _ => List.perm_iff_count.1 h j⟩
  by_cases hj : j ∈ σ ∨ j ∈ x.1
  · exact h j hj
  · rw [not_or] at hj
    rw [List.count_eq_zero_of_not_mem hj.1, List.count_eq_zero_of_not_mem hj.2]

private theorem computableInPolyTime_check :
    ComputableInPolyTime check
      (encPair encJobSequencing (encList (encPair encNat (encPair encNat encNat)))) encBool := by
  unfold check
  simp only [List.count_eq_countP]
  fun_prop

/-- `JobSequencing` belongs to `NP`, with the order as the witness; a permutation of the jobs is
encoded with the length of the encoded list of jobs. -/
theorem mem_NP : JobSequencing ∈ NP encJobSequencing := by
  have h := mem_NP_of_witness (p := Polynomial.X) (.list (.pair .nat (.pair .nat .nat)))
    computableInPolyTime_check check_iff fun x σ hσ => ⟨σ, hσ, ?_⟩
  · exact h
  · rw [Polynomial.eval_X, length_encList, (hσ.1.map _).sum_eq, ← length_encList]
    simp only [length_encPair]
    omega

/-- A job of time and penalty `a` with deadline `t`. -/
private abbrev job (t a : ℕ) : ℕ × ℕ × ℕ := (a, t, a)

private theorem penaltyFrom_le (s t : ℕ) (l : List ℕ) :
    penaltyFrom s (l.map (job t)) ≤ l.sum := by
  induction l generalizing s with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, penaltyFrom, List.sum_cons]
    have := ih (s + a)
    split <;> omega

private theorem penaltyFrom_eq_zero (s t : ℕ) (l : List ℕ) (h : s + l.sum ≤ t) :
    penaltyFrom s (l.map (job t)) = 0 := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, penaltyFrom, List.sum_cons] at h ⊢
    rw [ih (s + a) (by omega), ite_eq_right (by omega)]

/-- In an order of the jobs `job t a` started at time `s`, the jobs completed on time hold a
sublist `O` of the numbers such that the total penalty and `O.sum` add up to the total time, and
`O` is empty or fits before the deadline. -/
private theorem exists_onTime (t : ℕ) (l : List ℕ) (s : ℕ) :
    ∃ O, O <+ l ∧ penaltyFrom s (l.map (job t)) + O.sum = l.sum ∧ (s + O.sum ≤ t ∨ O = []) := by
  induction l generalizing s with
  | nil => exact ⟨[], List.Sublist.slnil, rfl, Or.inr rfl⟩
  | cons a l ih =>
    simp only [List.map_cons, penaltyFrom, List.sum_cons]
    obtain ⟨O, hO, hsum, hle⟩ := ih (s + a)
    by_cases ha : t < s + a
    · refine ⟨O, hO.cons a, ?_, ?_⟩
      · rw [ite_eq_left ha]
        omega
      · rcases hle with hle | rfl
        · omega
        · exact Or.inr rfl
    · refine ⟨a :: O, hO.cons_cons a, ?_, Or.inl ?_⟩
      · rw [ite_eq_right ha, List.sum_cons]
        omega
      · rcases hle with hle | rfl
        · rw [List.sum_cons]
          omega
        · simp only [List.sum_cons, List.sum_nil]
          omega

end JobSequencing

namespace SubsetSum

/-- **Karp's reduction from `SubsetSum` to `JobSequencing`** [Karp1972]: each number `a` becomes a
job of time and penalty `a` with the target `t` as deadline, and the penalty bound is
`a.sum - t`. A target above the total is mapped to a single job that is always late. -/
def toJobSequencing (x : List ℕ × ℕ) : List (ℕ × ℕ × ℕ) × ℕ :=
  if x.2 ≤ x.1.sum then (x.1.map fun a => (a, x.2, a), x.1.sum - x.2) else ([(1, 0, 1)], 0)

open JobSequencing in
/-- **Correctness of the reduction to `JobSequencing`.** -/
theorem toJobSequencing_mem_iff (x : List ℕ × ℕ) :
    toJobSequencing x ∈ JobSequencing ↔ x ∈ SubsetSum := by
  obtain ⟨l, t⟩ := x
  rw [mem_SubsetSum_iff_sublist]
  dsimp only [toJobSequencing]
  split_ifs with ht
  · constructor
    · rintro ⟨σ, hσ, hpen⟩
      have hσ' : σ = (σ.map Prod.fst).map (job t) := by
        conv_lhs => rw [← List.map_id σ]
        rw [List.map_map]
        refine List.map_congr_left fun j hj => ?_
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 (hσ.subset hj)
        rfl
      have hperm : σ.map Prod.fst ~ l := by
        simpa only [List.map_map, Function.comp_def, List.map_id'] using hσ.map Prod.fst
      obtain ⟨O, hO, hsum, hle⟩ := exists_onTime t (σ.map Prod.fst) 0
      rw [← hσ'] at hsum
      have htot : (σ.map Prod.fst).sum = l.sum := hperm.sum_eq
      unfold totalPenalty at hpen
      have hOt : O.sum = t := by
        rcases hle with hle | rfl
        · omega
        · simp only [List.sum_nil] at hsum ⊢
          omega
      obtain ⟨O', hO'perm, hO'l⟩ := hO.subperm.trans hperm.subperm
      exact ⟨O', hO'l, hO'perm.sum_eq.trans hOt⟩
    · rintro ⟨s, hs, hsum⟩
      obtain ⟨r, hr⟩ := hs.exists_perm_append
      refine ⟨(s ++ r).map (job t), (hr.map _).symm, ?_⟩
      have htot := hr.sum_eq
      rw [List.sum_append] at htot
      unfold totalPenalty
      rw [List.map_append, penaltyFrom_append, penaltyFrom_eq_zero 0 t s (by omega)]
      have := penaltyFrom_le (0 + ((s.map (job t)).map Prod.fst).sum) t r
      omega
  · constructor
    · rintro ⟨σ, hσ, hpen⟩
      rw [List.perm_singleton] at hσ
      subst hσ
      simp [totalPenalty, penaltyFrom] at hpen
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨r, hr⟩ := hs.exists_perm_append
      have := hr.sum_eq
      rw [List.sum_append] at this
      omega

/-- The reduction `toJobSequencing` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toJobSequencing :
    ComputableInPolyTime toJobSequencing (encPair (encList encNat) encNat) encJobSequencing := by
  unfold toJobSequencing
  fun_prop

end SubsetSum

/-- `SubsetSum` reduces to `JobSequencing` in polynomial time. -/
theorem polyTimeReducible_SubsetSum_JobSequencing :
    PolyTimeReducible (encPair (encList encNat) encNat) encJobSequencing SubsetSum
      JobSequencing :=
  ⟨SubsetSum.toJobSequencing, SubsetSum.computableInPolyTime_toJobSequencing,
    fun x => (SubsetSum.toJobSequencing_mem_iff x).symm⟩

/-- `JobSequencing` is `NP`-hard. -/
theorem JobSequencing_npHard : NPHard encJobSequencing JobSequencing :=
  SubsetSum_npHard.trans polyTimeReducible_SubsetSum_JobSequencing

/-- **Sequencing with deadlines and penalties is NP-complete**, with the numbers in binary
[Karp1972]. -/
theorem JobSequencing_npComplete : NPComplete encJobSequencing JobSequencing :=
  ⟨JobSequencing.mem_NP, JobSequencing_npHard⟩

end Cslib.Complexity
