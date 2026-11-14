/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DFS.SCC
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT
import CslibFrontier.Algorithms.Lean.TimeM.Loops
import CslibFrontier.Foundations.Data.List.Fold

/-!
# Linear-time 2-SAT via strongly connected components

The linear-time 2-SAT decision and witness-construction algorithm of
[Aspvall, Plass and Tarjan][AspvallPlassTarjan1979] in the `TimeM` model, built as a client of
Kosaraju's strongly connected components (`CslibFrontier.Algorithms.Lean.DFS.SCC`) and connected to
`Cslib.Complexity.TwoSAT` (`CslibFrontier.Computability.Complexity.Problems.TwoSAT`).

Given a duplicate-free list `vs` covering a finite variable type `V` and a formula `φ : CNF V`:
1. `checkClausesM φ` checks in `|φ|` steps that every clause has length `1` or `2`;
2. `implicationAdjM φ` builds the adjacency lists of `φ`'s implication graph (`a ∨ b` contributes
   `¬a → b` and `¬b → a`; a unit clause `a` contributes `¬a → a`) in `|φ|` steps with at most
   `2 * |φ|` arcs;
3. `DFS.sccsM` and `DFS.indexComponentsM` compute the topological component index `compIdx` of
   every literal in `O(|vs| + |φ|)` steps;
4. `extractAssignmentM` rejects if some variable shares a component with its negation, and
   otherwise sets `σ v := decide (compIdx (v, false) < compIdx (v, true))`.

For formulas `φ : CNF ℕ` with arbitrary binary variable labels, `solveNat` / `solveNatM` compact
occurring variables into `Fin φ.vars.length`, deciding `φ ∈ Cslib.Complexity.TwoSAT` and producing
a satisfying assignment `ℕ → Bool` in `O(|φ.vars| + |φ|)` `TimeM` steps.

## Main definitions

* `Cslib.Algorithms.Lean.TwoSAT.implicationAdj`, `Cslib.Algorithms.Lean.TwoSAT.implicationAdjM`:
  implication-graph adjacency lists of a width-at-most-2 formula.
* `Cslib.Algorithms.Lean.TwoSAT.solve`, `Cslib.Algorithms.Lean.TwoSAT.solveM`: linear-time 2-SAT
  solver over a finite variable list `vs`.
* `Cslib.Algorithms.Lean.TwoSAT.solveFin`, `Cslib.Algorithms.Lean.TwoSAT.solveFinM`: specialization
  to `CNF (Fin n)`.
* `Cslib.Algorithms.Lean.TwoSAT.solveNat`, `Cslib.Algorithms.Lean.TwoSAT.solveNatM`: solver on
  `CNF ℕ` connected to `Cslib.Complexity.TwoSAT`.

## Main results

* `Cslib.Algorithms.Lean.TwoSAT.solve_eq_some`, `Cslib.Algorithms.Lean.TwoSAT.isSome_solve_iff`:
  soundness and completeness of `solve`.
* `Cslib.Algorithms.Lean.TwoSAT.time_solveM_le`, `Cslib.Algorithms.Lean.TwoSAT.time_solveFinM_le`:
  linear `O(|V| + |φ|)` `TimeM` step bound (`≤ 12 * n + 8 * φ.length + 1`).
* `Cslib.Algorithms.Lean.TwoSAT.isSome_solveNat_iff`,
  `Cslib.Algorithms.Lean.TwoSAT.solveNat_eq_some`: exact equivalence with
  `φ ∈ Cslib.Complexity.TwoSAT` and witness validity.

## References

* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.TwoSAT

open Cslib.Logic.PL Cslib.Algorithms.Lean.DFS TimeM

variable {V : Type*}

/-! ### Clause-width guard and literal enumeration -/

/-- Predicate checking whether a clause has width `1` or `2`. -/
def isValidTwoClause (c : Clause V) : Bool :=
  decide (1 ≤ c.length ∧ c.length ≤ 2)

/-- Check that every clause of `φ` has length `1` or `2`. -/
def checkClauses (φ : CNF V) : Bool :=
  φ.foldl (fun ok c => ok && isValidTwoClause c) true

/-- `checkClauses` in `TimeM`, charging one unit per clause. -/
def checkClausesM (φ : CNF V) : TimeM ℕ Bool :=
  φ.foldlM (fun ok c => do ✓ return (ok && isValidTwoClause c)) true

theorem checkClauses_eq_true_iff (φ : CNF V) :
    checkClauses φ = true ↔ (∀ c ∈ φ, c.length ≤ 2) ∧ [] ∉ φ := by
  rw [checkClauses, foldl_and_eq_and_all, Bool.true_and, List.all_eq_true]
  simp only [isValidTwoClause]
  constructor
  · intro h
    refine ⟨fun c hc => (of_decide_eq_true (h c hc)).2, fun hnil => ?_⟩
    have := (of_decide_eq_true (h [] hnil)).1
    simp at this
  · rintro ⟨hw, hnil⟩ c hc
    refine decide_eq_true ⟨?_, hw c hc⟩
    cases c with
    | nil => exact absurd hc hnil
    | cons _ _ => simp

theorem ret_checkClausesM (φ : CNF V) : (checkClausesM φ).ret = checkClauses φ := by
  simp [checkClausesM, checkClauses, TimeM.ret_foldlM]

theorem time_checkClausesM (φ : CNF V) : (checkClausesM φ).time = φ.length := by
  simpa [checkClausesM] using TimeM.time_foldlM_of_time_eq
    (fun ok c => do ✓ return (ok && isValidTwoClause c)) φ true (c := 1) (fun _ _ => rfl)

/-- Enumerate both polarities `(v, false)` and `(v, true)` for each `v ∈ vs`. -/
def literalList : List V → List (Literal V)
  | [] => []
  | v :: vs => (v, false) :: (v, true) :: literalList vs

/-- `literalList` in `TimeM`, charging one unit per variable. -/
def literalListM : List V → TimeM ℕ (List (Literal V))
  | [] => return []
  | v :: vs => do
    ✓
    let rest ← literalListM vs
    return (v, false) :: (v, true) :: rest

theorem length_literalList (vs : List V) : (literalList vs).length = 2 * vs.length := by
  induction vs with
  | nil => rfl
  | cons _ vs ih =>
    simp only [literalList, List.length_cons, ih]
    omega

theorem mem_literalList_iff {vs : List V} {ℓ : Literal V} :
    ℓ ∈ literalList vs ↔ ℓ.1 ∈ vs := by
  induction vs with
  | nil => simp [literalList]
  | cons v vs ih =>
    rcases ℓ with ⟨u, b⟩
    simp only [literalList, List.mem_cons, Prod.mk.injEq, ih]
    cases b <;> tauto

theorem mem_literalList {vs : List V} (hvs : ∀ v, v ∈ vs) (ℓ : Literal V) :
    ℓ ∈ literalList vs :=
  mem_literalList_iff.2 (hvs ℓ.1)

theorem nodup_literalList {vs : List V} (hnd : vs.Nodup) : (literalList vs).Nodup := by
  induction vs with
  | nil => simp [literalList]
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    simp only [literalList, List.nodup_cons, List.mem_cons, Prod.mk.injEq, Bool.false_eq_true,
      and_false, false_or, mem_literalList_iff]
    exact ⟨hnd.1, hnd.1, ih hnd.2⟩

private theorem literalListM_spec :
    ∀ (vs : List V),
      (literalListM vs).ret = literalList vs ∧ (literalListM vs).time = vs.length
  | [] => by simp [literalListM, literalList]
  | v :: vs => by
    obtain ⟨hr, ht⟩ := literalListM_spec vs
    simp only [literalListM, literalList, TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick,
      TimeM.ret_pure, TimeM.time_pure, List.length_cons, hr, ht, true_and]
    omega

theorem ret_literalListM (vs : List V) : (literalListM vs).ret = literalList vs :=
  (literalListM_spec vs).1

theorem time_literalListM (vs : List V) : (literalListM vs).time = vs.length :=
  (literalListM_spec vs).2

/-! ### Implication-graph adjacency lists -/

/-- Add the implication arcs of a single clause `c` of width `1` or `2`. -/
def addClauseEdges [DecidableEq V] (adj : Literal V → List (Literal V)) :
    Clause V → Literal V → List (Literal V)
  | [] => adj
  | [a] => Function.update adj a.negate (a :: adj a.negate)
  | [a, b] =>
    let adj₁ := Function.update adj a.negate (b :: adj a.negate)
    Function.update adj₁ b.negate (a :: adj₁ b.negate)
  | _ :: _ :: _ :: _ => adj

/-- Build the implication-graph adjacency lists of `φ`. -/
def implicationAdj [DecidableEq V] (φ : CNF V) : Literal V → List (Literal V) :=
  φ.foldl addClauseEdges (fun _ => [])

/-- `implicationAdj` in `TimeM`, charging one unit per clause. -/
def implicationAdjM [DecidableEq V] (φ : CNF V) : TimeM ℕ (Literal V → List (Literal V)) :=
  φ.foldlM (fun adj c => do ✓ return addClauseEdges adj c) (fun _ => [])

section ImplicationGraph

variable [DecidableEq V]

private theorem mem_addClauseEdges {adj : Literal V → List (Literal V)} {c : Clause V}
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 2) (ℓ ℓ' : Literal V) :
    ℓ' ∈ addClauseEdges adj c ℓ ↔
      ℓ' ∈ adj ℓ ∨ (ℓ.negate ∈ c ∧ ℓ' ∈ c ∧ ∀ m ∈ c, m = ℓ.negate ∨ m = ℓ') := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
  · simp at hc1
  · dsimp only [addClauseEdges]
    simp only [List.mem_singleton]
    by_cases hℓ : ℓ = a.negate
    · subst hℓ
      rw [negate_negate, Function.update_self, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact .inr ⟨rfl, rfl, fun m hm => .inl hm⟩
        · exact .inl h
      · rintro (h | ⟨_, rfl, _⟩)
        · exact .inr h
        · exact .inl rfl
    · have hne : ℓ.negate ≠ a := fun h => hℓ (by rw [← h, negate_negate])
      have hupd : Function.update adj a.negate (a :: adj a.negate) ℓ = adj ℓ :=
        Function.update_of_ne hℓ _ _
      rw [hupd]
      simp [hne]
  · dsimp only [addClauseEdges]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    have hiff :
        (ℓ' ∈ (let adj₁ := Function.update adj a.negate (b :: adj a.negate)
            Function.update adj₁ b.negate (a :: adj₁ b.negate)) ℓ) ↔
          ℓ' ∈ adj ℓ ∨ (ℓ = a.negate ∧ ℓ' = b) ∨ (ℓ = b.negate ∧ ℓ' = a) := by
      dsimp only
      by_cases h₂ : ℓ = b.negate
      · subst h₂
        rw [Function.update_self, List.mem_cons]
        by_cases h₁ : b.negate = a.negate
        · rw [h₁, Function.update_self, List.mem_cons]
          tauto
        · rw [Function.update_of_ne h₁]
          tauto
      · rw [Function.update_of_ne h₂]
        by_cases h₁ : ℓ = a.negate
        · subst h₁
          rw [Function.update_self, List.mem_cons]
          tauto
        · rw [Function.update_of_ne h₁]
          tauto
    rw [hiff]
    refine or_congr_right ⟨?_, ?_⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rw [negate_negate]
        exact ⟨.inl rfl, .inr rfl, fun m hm => hm⟩
      · rw [negate_negate]
        exact ⟨.inr rfl, .inl rfl, fun m hm => hm.symm⟩
    · rintro ⟨hneg, hℓ', hall⟩
      rcases hall a (.inl rfl) with ha | ha
      · rcases hall b (.inr rfl) with hb | hb
        · have hℓa : ℓ = a.negate := by rw [ha, negate_negate]
          have hba : b = a := hb.trans ha.symm
          rcases hℓ' with rfl | rfl
          · exact .inl ⟨hℓa, hba.symm⟩
          · exact .inl ⟨hℓa, rfl⟩
        · exact .inl ⟨by rw [ha, negate_negate], hb.symm⟩
      · rcases hall b (.inr rfl) with hb | hb
        · exact .inr ⟨by rw [hb, negate_negate], ha.symm⟩
        · have hba : b = a := hb.trans ha.symm
          rcases hneg with hna | hnb
          · exact .inl ⟨by rw [← hna, negate_negate], ha.symm.trans hba.symm⟩
          · exact .inr ⟨by rw [← hnb, negate_negate], ha.symm⟩
  · simp at hc2

private theorem foldl_addClauseEdges_mem :
    ∀ (cs : CNF V) (adj : Literal V → List (Literal V)),
      (∀ c ∈ cs, 1 ≤ c.length ∧ c.length ≤ 2) →
      ∀ (ℓ ℓ' : Literal V),
        ℓ' ∈ cs.foldl addClauseEdges adj ℓ ↔ ℓ' ∈ adj ℓ ∨ cs.Implies ℓ ℓ'
  | [], adj, _, ℓ, ℓ' => by simp [CNF.Implies]
  | c :: cs, adj, hcs, ℓ, ℓ' => by
    have hc := hcs c List.mem_cons_self
    have hrest : ∀ c' ∈ cs, 1 ≤ c'.length ∧ c'.length ≤ 2 :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    rw [List.foldl_cons, foldl_addClauseEdges_mem cs _ hrest, mem_addClauseEdges hc.1 hc.2]
    constructor
    · rintro ((h | h) | ⟨c', hc', h⟩)
      · exact .inl h
      · exact .inr ⟨c, List.mem_cons_self, h⟩
      · exact .inr ⟨c', List.mem_cons_of_mem c hc', h⟩
    · rintro (h | ⟨c', hc', h⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact .inl (.inr h)
        · exact .inr ⟨c', hc', h⟩

/-- When `φ` has no empty clause and all clauses have width at most `2`, `implicationAdj φ`
realizes `φ.Implies`. -/
theorem edge_implicationAdj_iff {φ : CNF V} (hw : ∀ c ∈ φ, c.length ≤ 2) (hnil : [] ∉ φ)
    (ℓ ℓ' : Literal V) :
    Edge (implicationAdj φ) ℓ ℓ' ↔ φ.Implies ℓ ℓ' := by
  have hcs : ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 2 := by
    intro c hc
    refine ⟨?_, hw c hc⟩
    cases c with
    | nil => exact absurd hc hnil
    | cons _ _ => simp
  simpa [Edge, implicationAdj] using foldl_addClauseEdges_mem φ (fun _ => []) hcs ℓ ℓ'

private theorem sum_addClauseEdges_le [Fintype V] (adj : Literal V → List (Literal V))
    (c : Clause V) :
    (∑ w, (addClauseEdges adj c w).length) ≤ (∑ w, (adj w).length) + 2 := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
  · exact Nat.le_add_right _ _
  · change (∑ w, (Function.update adj a.negate (a :: adj a.negate) w).length) ≤ _
    rw [sum_length_update_cons]
    omega
  · change (∑ w, (Function.update (Function.update adj a.negate (b :: adj a.negate))
        b.negate (a :: Function.update adj a.negate (b :: adj a.negate) b.negate) w).length) ≤ _
    rw [sum_length_update_cons, sum_length_update_cons]
  · exact Nat.le_add_right _ _

private theorem sum_foldl_addClauseEdges_le [Fintype V] :
    ∀ (cs : CNF V) (adj : Literal V → List (Literal V)),
      (∑ w, (cs.foldl addClauseEdges adj w).length) ≤ (∑ w, (adj w).length) + 2 * cs.length
  | [], adj => by simp
  | c :: cs, adj => by
    rw [List.foldl_cons, List.length_cons]
    have h₁ := sum_addClauseEdges_le adj c
    have h₂ := sum_foldl_addClauseEdges_le cs (addClauseEdges adj c)
    omega

theorem sum_length_implicationAdj_le [Fintype V] (φ : CNF V) :
    (∑ w, (implicationAdj φ w).length) ≤ 2 * φ.length := by
  simpa [implicationAdj] using sum_foldl_addClauseEdges_le φ (fun _ => [])

theorem ret_implicationAdjM (φ : CNF V) : (implicationAdjM φ).ret = implicationAdj φ := by
  simp [implicationAdjM, implicationAdj, TimeM.ret_foldlM]

theorem time_implicationAdjM (φ : CNF V) : (implicationAdjM φ).time = φ.length := by
  simpa [implicationAdjM] using TimeM.time_foldlM_of_time_eq
    (fun (adj : Literal V → List (Literal V)) c => do ✓ return addClauseEdges adj c)
    φ (fun _ => []) (c := 1) (fun _ _ => rfl)

end ImplicationGraph

/-! ### Extracting the truth assignment from SCC topological indices -/

/-- Check that no variable in `vs` shares an SCC index with its negation, and return the
topological truth assignment `v ↦ decide (compIdx (v, false) < compIdx (v, true))`. -/
def extractAssignment (vs : List V) (compIdx : Literal V → ℕ) : Option (V → Bool) :=
  if vs.foldl (fun ok v => ok && decide (compIdx (v, true) ≠ compIdx (v, false))) true then
    some fun v => decide (compIdx (v, false) < compIdx (v, true))
  else
    none

/-- `extractAssignment` in `TimeM`, charging one unit per variable in `vs`. -/
def extractAssignmentM (vs : List V) (compIdx : Literal V → ℕ) : TimeM ℕ (Option (V → Bool)) :=
  TimeM.bind
    (vs.foldlM
      (fun ok v => do ✓ return (ok && decide (compIdx (v, true) ≠ compIdx (v, false)))) true)
    fun ok =>
      if ok then pure (some fun v => decide (compIdx (v, false) < compIdx (v, true)))
      else pure none

theorem ret_extractAssignmentM (vs : List V) (compIdx : Literal V → ℕ) :
    (extractAssignmentM vs compIdx).ret = extractAssignment vs compIdx := by
  dsimp only [extractAssignmentM, extractAssignment, TimeM.bind]
  simp only [TimeM.ret_foldlM, TimeM.ret_bind, TimeM.ret_pure]
  split_ifs <;> rfl

theorem time_extractAssignmentM (vs : List V) (compIdx : Literal V → ℕ) :
    (extractAssignmentM vs compIdx).time = vs.length := by
  dsimp only [extractAssignmentM, TimeM.bind]
  rw [TimeM.time_foldlM_of_time_eq _ vs true (c := 1) (fun _ _ => rfl)]
  split_ifs <;> simp

/-! ### Linear-time 2-SAT solver -/

/-- **Aspvall–Plass–Tarjan 2-SAT solver**: returns `some σ` satisfying `φ` when every clause of `φ`
has width at most `2` and `φ` is satisfiable, and `none` otherwise. -/
def solve [DecidableEq V] (vs : List V) (φ : CNF V) : Option (V → Bool) :=
  if checkClauses φ then
    let lits := literalList vs
    let adj := implicationAdj φ
    let comps := sccs adj lits
    let compIdx := indexComponents comps
    extractAssignment vs compIdx
  else
    none

/-- `solve` in `TimeM`. -/
def solveM [DecidableEq V] (vs : List V) (φ : CNF V) : TimeM ℕ (Option (V → Bool)) := do
  ✓
  TimeM.bind (checkClausesM φ) fun ok =>
    if ok then do
      let lits ← literalListM vs
      let adj ← implicationAdjM φ
      let comps ← sccsM adj lits
      let compIdx ← indexComponentsM comps
      extractAssignmentM vs compIdx
    else
      pure none

section SolveCorrectness

variable [DecidableEq V] {vs : List V} {φ : CNF V}

theorem ret_solveM (vs : List V) (φ : CNF V) : (solveM vs φ).ret = solve vs φ := by
  simp only [solveM, solve, TimeM.ret_bind]
  dsimp only [TimeM.bind]
  rw [ret_checkClausesM]
  split_ifs with hok
  · simp [ret_literalListM, ret_implicationAdjM, ret_sccsM, ret_indexComponentsM,
      ret_extractAssignmentM]
  · rfl

omit [DecidableEq V] in
private theorem literal_false_lt {compIdx : Literal V → ℕ}
    (hne : ∀ v, compIdx (v, true) ≠ compIdx (v, false)) (ℓ : Literal V)
    (hf : Literal.eval (fun v => decide (compIdx (v, false) < compIdx (v, true))) ℓ = false) :
    compIdx ℓ < compIdx ℓ.negate := by
  rcases ℓ with ⟨v, b⟩
  have hnev := hne v
  cases b
  · simp only [Literal.eval, beq_false, Bool.not_eq_false', decide_eq_true_eq] at hf
    simpa [Std.Sat.Literal.negate] using hf
  · simp only [Literal.eval, beq_true, decide_eq_false_iff_not] at hf
    have hlt : compIdx (v, true) < compIdx (v, false) := by omega
    simpa [Std.Sat.Literal.negate] using hlt

/-- **Soundness of `solve`**: whenever `solve vs φ = some σ` (with `vs` covering `V`), every clause
of `φ` has width at most `2` and `σ` satisfies `φ`. -/
theorem solve_eq_some (hvs : ∀ v, v ∈ vs) {σ : V → Bool} (h : solve vs φ = some σ) :
    (∀ c ∈ φ, c.length ≤ 2) ∧ φ.eval σ = true := by
  dsimp only [solve] at h
  split_ifs at h with hchk
  · obtain ⟨hw, hnil⟩ := (checkClauses_eq_true_iff φ).1 hchk
    set lits := literalList vs
    set adj := implicationAdj φ
    set comps := sccs adj lits
    set compIdx := indexComponents comps
    have hlits : ∀ ℓ, ℓ ∈ lits := mem_literalList hvs
    have hcond : IsSCCCondensation adj comps := isSCCCondensation_sccs hlits
    dsimp only [extractAssignment] at h
    split_ifs at h with hdist
    · injection h with hσ
      subst hσ
      have hdist_all : ∀ v, compIdx (v, true) ≠ compIdx (v, false) := by
        rw [foldl_and_eq_and_all, Bool.true_and, List.all_eq_true] at hdist
        exact fun v => of_decide_eq_true (hdist v (hvs v))
      refine ⟨hw, (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
      have hc2 : c.length ≤ 2 := hw c hc
      rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · exact absurd hc hnil
      · by_contra hceval
        have haf :
            Literal.eval (fun v => decide (compIdx (v, false) < compIdx (v, true))) a = false := by
          cases he : Literal.eval (fun v => decide (compIdx (v, false) < compIdx (v, true))) a
          · rfl
          · exact absurd (by simp [Clause.eval, he]) hceval
        have hlt := literal_false_lt hdist_all a haf
        have hedge : Edge adj a.negate a := by
          rw [edge_implicationAdj_iff hw hnil]
          exact ⟨[a], hc, by simp, by simp, fun m hm => .inl (by simpa using hm)⟩
        have hle : compIdx a.negate ≤ compIdx a := hcond.indexComponents_le_of_edge hedge
        omega
      · by_contra hceval
        have habf :
            Literal.eval (fun v => decide (compIdx (v, false) < compIdx (v, true))) a = false ∧
              Literal.eval (fun v => decide (compIdx (v, false) < compIdx (v, true))) b =
                false := by
          cases ha : Literal.eval (fun v => decide (compIdx (v, false) < compIdx (v, true))) a <;>
            cases hb : Literal.eval (fun v => decide (compIdx (v, false) < compIdx (v, true))) b
          · exact ⟨rfl, rfl⟩
          all_goals exact absurd (by simp [Clause.eval, ha, hb]) hceval
        have hlta := literal_false_lt hdist_all a habf.1
        have hltb := literal_false_lt hdist_all b habf.2
        have hedge₁ : Edge adj a.negate b := by
          rw [edge_implicationAdj_iff hw hnil]
          exact ⟨[a, b], hc, by simp, by simp, fun m hm => by simpa using hm⟩
        have hedge₂ : Edge adj b.negate a := by
          rw [edge_implicationAdj_iff hw hnil]
          refine ⟨[a, b], hc, by simp, by simp, fun m hm => ?_⟩
          rcases List.mem_cons.1 hm with rfl | hm
          · exact .inr rfl
          · exact .inl (by simpa [negate_negate] using List.mem_singleton.1 hm)
        have hle₁ : compIdx a.negate ≤ compIdx b := hcond.indexComponents_le_of_edge hedge₁
        have hle₂ : compIdx b.negate ≤ compIdx a := hcond.indexComponents_le_of_edge hedge₂
        omega
      · simp at hc2

private theorem reach_iff_implies (hw : ∀ c ∈ φ, c.length ≤ 2) (hnil : [] ∉ φ)
    {ℓ ℓ' : Literal V} :
    Relation.ReflTransGen (Edge (implicationAdj φ)) ℓ ℓ' ↔
      Relation.ReflTransGen φ.Implies ℓ ℓ' := by
  have hrel : Edge (implicationAdj φ) = φ.Implies :=
    funext fun a => funext fun b => propext (edge_implicationAdj_iff hw hnil a b)
  rw [hrel]

/-- **Completeness and characterization of `solve`**: when `vs` covers `V`, `(solve vs φ).isSome`
holds if and only if every clause of `φ` has width at most `2` and `φ` is satisfiable. -/
theorem isSome_solve_iff (hvs : ∀ v, v ∈ vs) :
    (solve vs φ).isSome ↔ (∀ c ∈ φ, c.length ≤ 2) ∧ φ.Satisfiable := by
  constructor
  · intro hs
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨hw, heval⟩ := solve_eq_some hvs hσ
    exact ⟨hw, σ, heval⟩
  · rintro ⟨hw, hsat⟩
    have hnil : [] ∉ φ := fun hnil => CNF.not_satisfiable_of_nil_mem hnil hsat
    have hchk : checkClauses φ = true := (checkClauses_eq_true_iff φ).2 ⟨hw, hnil⟩
    have hlits : ∀ ℓ, ℓ ∈ literalList vs := mem_literalList hvs
    have hcond : IsSCCCondensation (implicationAdj φ) (sccs (implicationAdj φ) (literalList vs)) :=
      isSCCCondensation_sccs hlits
    have hdist :
        vs.foldl
            (fun ok v =>
              ok && decide
                (indexComponents (sccs (implicationAdj φ) (literalList vs)) (v, true) ≠
                  indexComponents (sccs (implicationAdj φ) (literalList vs)) (v, false)))
            true = true := by
      rw [foldl_and_eq_and_all, Bool.true_and, List.all_eq_true]
      intro v _
      refine decide_eq_true fun heq => ?_
      obtain ⟨h₁, h₂⟩ := (hcond.indexComponents_eq_iff (v, true) (v, false)).1 heq
      exact CNF.not_satisfiable_of_reach (ℓ := (v, true))
        ((reach_iff_implies hw hnil).1 h₁) ((reach_iff_implies hw hnil).1 h₂) hsat
    simp only [solve, hchk, ↓reduceIte, extractAssignment, hdist, Option.isSome_some]

/-- **Linear `TimeM` step bound for `solveM`**: when `vs` lists every vertex of `V` without
repetition, `solveM vs φ` takes at most `12 * |vs| + 8 * |φ| + 1` steps. -/
theorem time_solveM_le (hvs : ∀ v, v ∈ vs) (hnd : vs.Nodup) (φ : CNF V) :
    (solveM vs φ).time ≤ 12 * vs.length + 8 * φ.length + 1 := by
  let _ : Fintype V := Fintype.ofList vs hvs
  have hlits_mem : ∀ ℓ, ℓ ∈ literalList vs := mem_literalList hvs
  have hlits_nd : (literalList vs).Nodup := nodup_literalList hnd
  have hcond : IsSCCCondensation (implicationAdj φ) (sccs (implicationAdj φ) (literalList vs)) :=
    isSCCCondensation_sccs hlits_mem
  have hcard_V : Fintype.card V = vs.length := by
    rw [← List.toFinset_card_of_nodup hnd]
    have huniv : vs.toFinset = Finset.univ := by ext v; simp [hvs v]
    rw [huniv, Finset.card_univ]
  have hcard_lit : Fintype.card (Literal V) = 2 * vs.length := by
    change Fintype.card (V × Bool) = 2 * vs.length
    rw [Fintype.card_prod, hcard_V, Fintype.card_bool]
    omega
  have hsccs_time :
      (sccsM (implicationAdj φ) (literalList vs)).time ≤ 6 * vs.length + 6 * φ.length := by
    rw [time_sccsM_of_nodup hlits_mem hlits_nd, length_literalList]
    have hsum := sum_length_implicationAdj_le φ
    omega
  have hidx_time :
      (indexComponentsM (sccs (implicationAdj φ) (literalList vs))).time ≤ 4 * vs.length := by
    rw [time_indexComponentsM, hcond.length_flatten_eq_card]
    have hlen := hcond.length_le_card
    omega
  simp only [solveM, TimeM.time_bind, TimeM.time_tick]
  dsimp only [TimeM.bind]
  rw [ret_checkClausesM, time_checkClausesM]
  split_ifs with hok
  · simp only [TimeM.time_bind, ret_literalListM, time_literalListM,
      ret_implicationAdjM, time_implicationAdjM, ret_sccsM, ret_indexComponentsM,
      time_extractAssignmentM]
    omega
  · simp only [TimeM.time_pure]
    omega

end SolveCorrectness

/-! ### Specialization to `CNF (Fin n)` and bridge to `Cslib.Complexity.TwoSAT` -/

/-- Linear-time 2-SAT solver on `CNF (Fin n)`. -/
def solveFin (n : ℕ) (φ : CNF (Fin n)) : Option (Fin n → Bool) :=
  solve (List.finRange n) φ

/-- `solveFin` in `TimeM`. -/
def solveFinM (n : ℕ) (φ : CNF (Fin n)) : TimeM ℕ (Option (Fin n → Bool)) :=
  solveM (List.finRange n) φ

theorem ret_solveFinM (n : ℕ) (φ : CNF (Fin n)) : (solveFinM n φ).ret = solveFin n φ :=
  ret_solveM (List.finRange n) φ

theorem solveFin_eq_some {n : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool}
    (h : solveFin n φ = some σ) : (∀ c ∈ φ, c.length ≤ 2) ∧ φ.eval σ = true :=
  solve_eq_some List.mem_finRange h

theorem isSome_solveFin_iff (n : ℕ) (φ : CNF (Fin n)) :
    (solveFin n φ).isSome ↔ (∀ c ∈ φ, c.length ≤ 2) ∧ φ.Satisfiable :=
  isSome_solve_iff List.mem_finRange

theorem time_solveFinM_le (n : ℕ) (φ : CNF (Fin n)) :
    (solveFinM n φ).time ≤ 12 * n + 8 * φ.length + 1 := by
  simpa [solveFinM] using time_solveM_le (V := Fin n) List.mem_finRange (List.nodup_finRange n) φ

/-- Map a natural-number variable to its compact index in `Fin (φ.vars.length + 1)`. -/
def toFinVar (φ : CNF ℕ) (v : ℕ) : Fin (φ.vars.length + 1) :=
  if h : φ.vars.idxOf v < φ.vars.length then ⟨φ.vars.idxOf v, Nat.lt_succ_of_lt h⟩ else 0

/-- Relabel `φ : CNF ℕ` into `CNF (Fin (φ.vars.length + 1))`. -/
def toFinCNF (φ : CNF ℕ) : CNF (Fin (φ.vars.length + 1)) :=
  φ.relabel (toFinVar φ)

/-- Relabel a single clause with `f` in `TimeM`, charging one unit per literal. -/
def relabelClauseM {W : Type*} (f : ℕ → W) (c : Clause ℕ) : TimeM ℕ (Clause W) :=
  c.mapM fun ℓ => do ✓ return (f ℓ.1, ℓ.2)

/-- `toFinCNF` in `TimeM`, charging one unit per clause and one per literal occurrence. -/
def toFinCNFM (φ : CNF ℕ) : TimeM ℕ (CNF (Fin (φ.vars.length + 1))) :=
  let f := toFinVar φ
  φ.mapM fun c => do
    ✓
    relabelClauseM f c

private theorem ret_relabelClauseM {W : Type*} (f : ℕ → W) (c : Clause ℕ) :
    (relabelClauseM f c).ret = Clause.relabel f c := by
  simp only [relabelClauseM, TimeM.ret_listMapM, TimeM.ret_bind, TimeM.ret_pure, Clause.relabel]
  rfl

private theorem time_relabelClauseM {W : Type*} (f : ℕ → W) (c : Clause ℕ) :
    (relabelClauseM f c).time = c.length := by
  simp [relabelClauseM]

theorem ret_toFinCNFM (φ : CNF ℕ) : (toFinCNFM φ).ret = toFinCNF φ := by
  simp only [toFinCNFM, TimeM.ret_listMapM, TimeM.ret_bind, ret_relabelClauseM]
  rfl

theorem time_toFinCNFM (φ : CNF ℕ) : (toFinCNFM φ).time = φ.length + φ.vars.length := by
  simp only [toFinCNFM, TimeM.time_listMapM, TimeM.time_bind, TimeM.time_tick,
    time_relabelClauseM, CNF.length_vars, List.sum_map_add, List.map_const', List.sum_replicate,
    smul_eq_mul, mul_one]

/-- Solve a `CNF ℕ` instance of `Cslib.Complexity.TwoSAT`, returning `some σ` when `φ ∈ TwoSAT` and
`none` otherwise. -/
def solveNat (φ : CNF ℕ) : Option (ℕ → Bool) :=
  (solveFin (φ.vars.length + 1) (toFinCNF φ)).map fun σ v => σ (toFinVar φ v)

/-- `solveNat` in `TimeM`. -/
def solveNatM (φ : CNF ℕ) : TimeM ℕ (Option (ℕ → Bool)) := do
  let ψ ← toFinCNFM φ
  let res ← solveFinM (φ.vars.length + 1) ψ
  return res.map fun σ v => σ (toFinVar φ v)

theorem ret_solveNatM (φ : CNF ℕ) : (solveNatM φ).ret = solveNat φ := by
  simp [solveNatM, solveNat, ret_toFinCNFM, ret_solveFinM]

private theorem width_toFinCNF_iff (φ : CNF ℕ) :
    (∀ c ∈ toFinCNF φ, c.length ≤ 2) ↔ ∀ c ∈ φ, c.length ≤ 2 := by
  simp [toFinCNF, CNF.relabel, Clause.relabel]

private theorem satisfiable_toFinCNF_iff (φ : CNF ℕ) :
    (toFinCNF φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ toFinVar φ, by simpa only [toFinCNF, CNF.eval_relabel] using hσ⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨fun i => φ.vars[i.val]?.elim false τ, ?_⟩
    rw [toFinCNF, CNF.eval_relabel]
    refine (CNF.eval_congr fun v hv => ?_).trans hτ
    have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_of_mem hv
    simp [toFinVar, hlt]

/-- **Soundness of `solveNat`**: any returned assignment witnesses `φ ∈ Cslib.Complexity.TwoSAT`. -/
theorem solveNat_eq_some {φ : CNF ℕ} {σ : ℕ → Bool} (h : solveNat φ = some σ) :
    (∀ c ∈ φ, c.length ≤ 2) ∧ φ.eval σ = true := by
  simp only [solveNat, Option.map_eq_some_iff] at h
  obtain ⟨σ₀, hσ₀, rfl⟩ := h
  obtain ⟨hw, heval⟩ := solveFin_eq_some hσ₀
  refine ⟨(width_toFinCNF_iff φ).1 hw, ?_⟩
  simpa only [toFinCNF, CNF.eval_relabel, Function.comp_def] using heval

/-- **Exact equivalence with `Cslib.Complexity.TwoSAT`**. -/
theorem isSome_solveNat_iff (φ : CNF ℕ) :
    (solveNat φ).isSome ↔ φ ∈ Cslib.Complexity.TwoSAT := by
  rw [solveNat, Option.isSome_map, isSome_solveFin_iff, width_toFinCNF_iff,
    satisfiable_toFinCNF_iff, Cslib.Complexity.mem_TwoSAT]

/-- **Linear `TimeM` step bound for `solveNatM`** in variable occurrences and clauses. -/
theorem time_solveNatM_le (φ : CNF ℕ) :
    (solveNatM φ).time ≤ 13 * φ.vars.length + 9 * φ.length + 13 := by
  have hfin := time_solveFinM_le (φ.vars.length + 1) (toFinCNF φ)
  have hlen : (toFinCNF φ).length = φ.length := by simp [toFinCNF, CNF.relabel]
  simp only [solveNatM, TimeM.time_bind, TimeM.time_pure, ret_toFinCNFM, time_toFinCNFM]
  omega

end Cslib.Algorithms.Lean.TwoSAT
