/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# Search to decision for SAT

A procedure that decides satisfiability also finds satisfying assignments
[Arora and Barak, Section 2.5][AroraBarak09]. The *self-reduction*
(`Cslib.Complexity.SAT.selfReduce`) fixes the variables of a formula `φ` one literal occurrence
at a time: it asks whether `φ`, with the values chosen so far as unit clauses and the next
variable set to true, is satisfiable, and fixes the variable to the answer. If `φ` is satisfiable
and the answers are correct, the formula stays satisfiable, so at the end the chosen values
satisfy `φ` (`Cslib.Complexity.SAT.verifier_search`). The answers need only be correct on the
formulas the self-reduction asks about, whose encodings are at most `queryBound` of the length of
`φ`'s, so a procedure that is correct up to that length suffices; this is how Karp and Lipton use
circuits for `SAT`. The values are output as a certificate for `Cslib.Complexity.SAT.verifier`,
one bit for each literal occurrence.

The self-reduction makes one query for each literal occurrence, so it runs in polynomial time when
the queries are answered in polynomial time
(`Cslib.Complexity.SAT.computableInPolyTime_search`). In particular, if `SAT` is in `P`,
satisfying assignments can be found in polynomial time (`Cslib.Complexity.SAT.exists_search`).

## Main definitions

* `Cslib.Complexity.SAT.selfReduce`: the variables and values fixed by the self-reduction.
* `Cslib.Complexity.SAT.search`: the certificate found by the self-reduction.
* `Cslib.Complexity.SAT.queryBound`: a bound on the length of the queries.

## Main results

* `Cslib.Complexity.SAT.eval_units`, `Cslib.Complexity.SAT.vars_units`: unit clauses hold when
  their literals do, and have the variables of their literals.
* `Cslib.Complexity.SAT.length_encCNF_units_le`: the unit clauses fixing variables of `φ` are
  short.
* `Cslib.Complexity.SAT.verifier_search`: with answers correct up to `queryBound`, the
  self-reduction finds a satisfying assignment of every satisfiable formula.
* `Cslib.Complexity.SAT.computableInPolyTime_search`: the self-reduction is polynomial-time
  when the queries are answered in polynomial time.
* `Cslib.Complexity.SAT.exists_search`: if `SAT ∈ P`, satisfying assignments are found in
  polynomial time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.5][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The unit clauses of a list of literals. -/
def units (answers : List (Literal ℕ)) : CNF ℕ := answers.map ([·])

/-- One step of the self-reduction of `φ` with the decision procedure `D`: fix `v` to the answer
of `D` on `φ` with the values fixed so far and `v` set to true. -/
def selfReduceStep (D : CNF ℕ → Bool) (φ : CNF ℕ) (answers : List (Literal ℕ)) (v : ℕ) :
    List (Literal ℕ) :=
  answers ++ [(v, D (φ ++ units answers ++ [[(v, true)]]))]

/-- **The self-reduction** of `φ` with the decision procedure `D`: for each literal occurrence
`v` of `φ` in turn, the value fixed for `v`. -/
def selfReduce (D : CNF ℕ → Bool) (φ : CNF ℕ) : List (Literal ℕ) :=
  φ.vars.foldl (selfReduceStep D φ) []

/-- The certificate found by the self-reduction: the value fixed at each literal occurrence. -/
def search (D : CNF ℕ → Bool) (φ : CNF ℕ) : List Bool :=
  (selfReduce D φ).map Prod.snd

/-- A bound on the length of the encoded formulas that the self-reduction of a formula of encoded
length `L` asks about. -/
def queryBound (L : ℕ) : ℕ := L + (L + 1) * (8 * L + 11)

theorem queryBound_mono : Monotone queryBound := fun _ _ h => by
  unfold queryBound
  gcongr

/-! ### Correctness -/

private theorem map_fst_foldl_selfReduceStep (D : CNF ℕ → Bool) (φ : CNF ℕ) (l : List ℕ)
    (answers : List (Literal ℕ)) :
    (l.foldl (selfReduceStep D φ) answers).map Prod.fst = answers.map Prod.fst ++ l := by
  induction l generalizing answers with
  | nil => simp
  | cons v l ih => simp [ih, selfReduceStep]

/-- The self-reduction fixes the literal occurrences in order. -/
private theorem map_fst_selfReduce (D : CNF ℕ → Bool) (φ : CNF ℕ) :
    (selfReduce D φ).map Prod.fst = φ.vars := by
  rw [selfReduce, map_fst_foldl_selfReduceStep, List.map_nil, List.nil_append]

theorem length_search (D : CNF ℕ → Bool) (φ : CNF ℕ) : (search D φ).length = φ.vars.length := by
  rw [search, List.length_map, ← map_fst_selfReduce D φ, List.length_map]

/-- Unit clauses hold exactly when their literals do. -/
theorem eval_units (σ : ℕ → Bool) (answers : List (Literal ℕ)) :
    (units answers).eval σ = true ↔ ∀ l ∈ answers, σ l.1 = l.2 := by
  simp only [units, CNF.eval_eq_true_iff, List.forall_mem_map, Clause.eval_cons, Clause.eval_nil,
    Bool.or_false, Literal.eval_eq_true_iff]

/-- The variables of unit clauses are those of their literals. -/
theorem vars_units (answers : List (Literal ℕ)) : (units answers).vars = answers.map Prod.fst := by
  induction answers with
  | nil => rfl
  | cons l answers ih => simpa [units, CNF.vars] using ih

/-- A formula with unit clauses holds exactly when the formula holds and the literals do. -/
private theorem eval_append_units (σ : ℕ → Bool) (φ : CNF ℕ) (answers : List (Literal ℕ)) :
    (φ ++ units answers).eval σ = true ↔ φ.eval σ = true ∧ ∀ l ∈ answers, σ l.1 = l.2 := by
  rw [CNF.eval_append, Bool.and_eq_true, eval_units]

theorem length_encCNF_append (φ ψ : CNF ℕ) :
    (encCNF (φ ++ ψ)).length = (encCNF φ).length + (encCNF ψ).length := by
  simp [encCNF]

/-- A variable of a formula takes fewer bits than the formula. -/
theorem length_encNat_le_of_mem_vars {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) :
    (encNat v).length ≤ (encCNF φ).length := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
  obtain ⟨c, hc, hl⟩ := List.mem_flatten.1 hl
  calc (encNat l.1).length ≤ (encPair encNat encBool l).length := length_le_encPair_left _ _ _
    _ ≤ (encList (encPair encNat encBool) c).length := length_le_encList_of_mem _ hl
    _ ≤ (encCNF φ).length := length_le_encList_of_mem _ hc

/-- The unit clause of a literal on `v` takes `8 b + 11` bits, where `b` is the length of the
binary digits of `v`. -/
private theorem length_encCNF_unit (l : Literal ℕ) :
    (encCNF [[l]]).length = 8 * (encNat l.1).length + 11 := by
  simp only [encCNF, encList_cons, encList_nil, List.append_nil, length_frame, length_encPair,
    encBool_apply, List.length_singleton]
  omega

/-- The unit clause of a literal on a variable of `φ` takes at most `8 L + 11` bits, where `L`
is the length of `φ`. -/
private theorem length_encCNF_unit_le {φ : CNF ℕ} {l : Literal ℕ} (hl : l.1 ∈ φ.vars) :
    (encCNF [[l]]).length ≤ 8 * (encCNF φ).length + 11 := by
  have := length_encNat_le_of_mem_vars hl
  rw [length_encCNF_unit]
  omega

/-- Unit clauses fixing variables of `φ` take at most `8 L + 11` bits each, where `L` is the
length of `φ`. -/
theorem length_encCNF_units_le {φ : CNF ℕ} {answers : List (Literal ℕ)}
    (hanswers : ∀ l ∈ answers, l.1 ∈ φ.vars) :
    (encCNF (units answers)).length ≤ answers.length * (8 * (encCNF φ).length + 11) := by
  induction answers with
  | nil => simp [units, encCNF]
  | cons l answers ih =>
    have h₁ := length_encCNF_unit_le (hanswers l (List.mem_cons_self ..))
    have h₂ := ih fun l' hl' => hanswers l' (List.mem_cons_of_mem _ hl')
    rw [show units (l :: answers) = [[l]] ++ units answers from rfl, length_encCNF_append,
      List.length_cons, Nat.succ_mul]
    omega

/-- The formulas that the self-reduction asks about are no longer than `queryBound`. -/
private theorem length_query_le {φ : CNF ℕ} {answers : List (Literal ℕ)}
    (hanswers : ∀ l ∈ answers, l.1 ∈ φ.vars) (hlen : answers.length ≤ φ.vars.length) {v : ℕ}
    (hv : v ∈ φ.vars) :
    (encCNF (φ ++ units answers ++ [[(v, true)]])).length ≤ queryBound (encCNF φ).length := by
  have hunits := length_encCNF_units_le hanswers
  have hvars : φ.vars.length ≤ (encCNF φ).length := length_vars_le φ
  have hv' := length_encCNF_unit_le (l := (v, true)) hv
  have hmul : answers.length * (8 * (encCNF φ).length + 11) ≤
      (encCNF φ).length * (8 * (encCNF φ).length + 11) :=
    Nat.mul_le_mul_right _ (hlen.trans hvars)
  rw [length_encCNF_append, length_encCNF_append, queryBound]
  nlinarith

/-- With answers correct on the queries, the self-reduction keeps a satisfiable formula
satisfiable. -/
private theorem satisfiable_foldl_selfReduceStep {D : CNF ℕ → Bool} {φ : CNF ℕ}
    (hD : ∀ ψ, (encCNF ψ).length ≤ queryBound (encCNF φ).length → (D ψ = true ↔ ψ ∈ SAT))
    (l : List ℕ) (hl : ∀ v ∈ l, v ∈ φ.vars) (answers : List (Literal ℕ))
    (hanswers : ∀ a ∈ answers, a.1 ∈ φ.vars) (hlen : answers.length + l.length ≤ φ.vars.length)
    (hsat : (φ ++ units answers).Satisfiable) :
    (φ ++ units (l.foldl (selfReduceStep D φ) answers)).Satisfiable := by
  induction l generalizing answers with
  | nil => exact hsat
  | cons v l ih =>
    have hv := hl v (List.mem_cons_self ..)
    rw [List.length_cons] at hlen
    refine ih (fun w hw => hl w (List.mem_cons_of_mem _ hw)) _ ?_ ?_ ?_
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hanswers a ha
      · rw [List.mem_singleton.1 ha]
        exact hv
    · rw [selfReduceStep, List.length_append, List.length_singleton]
      omega
    · have hquery := hD _ (length_query_le hanswers (by omega) hv)
      rw [selfReduceStep, show ∀ b, units (answers ++ [(v, b)]) = units answers ++ [[(v, b)]] from
        fun b => List.map_append .., ← List.append_assoc]
      obtain ⟨σ, hσ⟩ := hsat
      rw [CNF.eval_append, Bool.and_eq_true] at hσ
      cases hb : D (φ ++ units answers ++ [[(v, true)]])
      · have hσv : σ v = false := by
          by_contra hσv
          rw [Bool.not_eq_false] at hσv
          rw [hb] at hquery
          exact Bool.false_ne_true (hquery.2 ⟨σ, by simp [hσ.1, hσ.2, hσv]⟩)
        exact ⟨σ, by simp [hσ.1, hσ.2, hσv]⟩
      · exact hquery.1 hb

/-- **Search to decision.** If `D` decides satisfiability correctly on the formulas of length at
most `queryBound` of the length of `φ`, and `φ` is satisfiable, the certificate found by the
self-reduction satisfies `φ`. -/
theorem verifier_search {D : CNF ℕ → Bool} {φ : CNF ℕ}
    (hD : ∀ ψ, (encCNF ψ).length ≤ queryBound (encCNF φ).length → (D ψ = true ↔ ψ ∈ SAT))
    (hφ : φ ∈ SAT) : verifier (φ, search D φ) = true := by
  obtain ⟨σ, hσ⟩ := satisfiable_foldl_selfReduceStep hD φ.vars (fun _ h => h) []
    (by simp) (by simp) (by rw [show units [] = [] from rfl, List.append_nil]; exact hφ)
  rw [← selfReduce, eval_append_units] at hσ
  rw [verifier, CNF.eval_congr fun v hv => ?_]
  · exact hσ.1
  · have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.2 hv
    have hlt' : φ.vars.idxOf v < (selfReduce D φ).length := by
      simpa [← map_fst_selfReduce D φ] using hlt
    have hfst : ((selfReduce D φ)[φ.vars.idxOf v]).1 = v := by
      have := congrArg (·[φ.vars.idxOf v]?) (map_fst_selfReduce D φ)
      simp only [List.getElem?_map, List.getElem?_eq_getElem hlt', List.getElem?_eq_getElem hlt,
        Option.map_some, Option.some.injEq] at this
      rw [this, List.getElem_idxOf hlt]
    rw [assignment, search, List.getD_eq_getElem _ _ (by simpa using hlt'), List.getElem_map,
      ← hσ.2 _ (List.getElem_mem hlt'), hfst]

/-- The self-reduction never finds a satisfying assignment of an unsatisfiable formula: the
certificate it finds is accepted exactly when the formula is satisfiable. -/
theorem verifier_search_iff {D : CNF ℕ → Bool} {φ : CNF ℕ}
    (hD : ∀ ψ, (encCNF ψ).length ≤ queryBound (encCNF φ).length → (D ψ = true ↔ ψ ∈ SAT)) :
    verifier (φ, search D φ) = true ↔ φ ∈ SAT :=
  ⟨fun h => ⟨_, h⟩, verifier_search hD⟩

/-! ### Polynomial time -/

open ComputableInPolyTime

/-- **The self-reduction is polynomial-time** when its queries are answered in polynomial time,
with a procedure `D x` that may depend on the input `x`. -/
theorem computableInPolyTime_search {γ : Type} {encIn : γ ↪ List Bool}
    {D : γ → CNF ℕ → Bool} {φ : γ → CNF ℕ}
    (hD : ComputableInPolyTime (fun p : γ × CNF ℕ => D p.1 p.2) (encPair encIn encCNF)
      encBool)
    (hφ : ComputableInPolyTime φ encIn encCNF) :
    ComputableInPolyTime (fun x => search (D x) (φ x)) encIn encBits := by
  have hvars : ComputableInPolyTime (fun x => (φ x).vars) encIn (encList encNat) :=
    computableInPolyTime_vars.comp hφ
  have hquery : ComputableInPolyTime (fun p : (γ × List (Literal ℕ)) × ℕ =>
      φ p.1.1 ++ units p.1.2 ++ [[(p.2, true)]])
      (encPair (encPair encIn (encList (encPair encNat encBool))) encNat) encCNF := by
    unfold units encCNF
    fun_prop
  have hstep : ComputableInPolyTime (fun p : (γ × List (Literal ℕ)) × ℕ =>
      selfReduceStep (D p.1.1) (φ p.1.1) p.1.2 p.2)
      (encPair (encPair encIn (encList (encPair encNat encBool))) encNat)
      (encList (encPair encNat encBool)) := by
    unfold selfReduceStep
    exact listAppend' (fst _ _).snd' (cons' ((snd _ _).prod
      (hD.comp ((fst _ _).fst'.prod hquery))) (const []))
  have hfold : ComputableInPolyTime (fun x => selfReduce (D x) (φ x)) encIn
      (encList (encPair encNat encBool)) := by
    unfold selfReduce
    refine foldlWithInput_of_bounded_growth (const []) ⟨hvars, hstep, inferInstance,
      inferInstance⟩ (growth := fun x => 4 * (encCNF (φ x)).length + 5)
      ⟨((PolyBounded.const 4).mul hφ.polyBounded_length).add (.const 5),
        fun x answers v hv => ?_⟩
    have := length_encNat_le_of_mem_vars hv
    simp only [selfReduceStep, encList_append, encList_cons, encList_nil, List.append_nil,
      List.length_append, length_frame, length_encPair, encBool_apply, List.length_singleton]
    omega
  unfold search
  exact listToBits.comp (map (snd encNat encBool) |>.comp hfold)

/-- **Search reduces to decision for `SAT`**: if `SAT` is in `P`, a polynomial-time function
finds a satisfying assignment of every satisfiable formula, as a certificate for `SAT.verifier`. -/
theorem exists_search (h : SAT ∈ P encCNF) :
    ∃ g : CNF ℕ → List Bool, ComputableInPolyTime g encCNF encBits ∧
      ∀ φ, verifier (φ, g φ) = true ↔ φ ∈ SAT := by
  obtain ⟨D, hD, hSAT⟩ := mem_P.mp h
  exact ⟨search D,
    computableInPolyTime_search (D := fun _ => D) (hD.comp (snd _ _)) id',
    fun φ => verifier_search_iff fun ψ _ => (hSAT ψ).symm⟩

end Cslib.Complexity.SAT
