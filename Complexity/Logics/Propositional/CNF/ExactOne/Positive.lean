/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne.Gadgets
public import Complexity.Logics.Propositional.CNF.ExactOne.ModelCount
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.List.Sigma
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Parsimonious elimination of negative exact-one literals

Every negative literal occurrence receives its own positive proxy. A positive complement gadget
forces the proxy to be the opposite of the original variable, with a unique auxiliary extension.
Each original variable keeps exactly its original occurrence count. A clause of width at most
three yields at most thirteen clauses, and all newly added clauses are positive triples.

The construction is [Hunt, Marathe, Radhakrishnan and Stearns, Theorem 3.8, Figure 3.5]
[HuntMaratheRadhakrishnanStearns1998]. The occurrence indexing and quantitative accounting are
original.

## Main definitions

* `Variable`, `formula`: the occurrence-indexed positive compiler.
* `extend`: its canonical assignment extension.

## Main results

* `positive_formula`: every emitted literal is positive.
* `length_formula_le`: a constant-factor clause bound on bounded-width inputs.
* `oneModelCount_formula`, `assignments_agree_iff`: count preservation and unique extensions.
* `count_inl_formula`, `count_vars_formula_le`: inherited occurrences are preserved exactly,
  and the occurrence-three restriction is preserved globally.
* `nodup_formula`: distinct variables within clauses remain distinct.

## References

* [Hunt, Marathe, Radhakrishnan and Stearns][HuntMaratheRadhakrishnanStearns1998],
  Theorem 3.8, Figure 3.5 and Lemma 3.6.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PositiveExactOne

open ExactOneGadget

variable {V : Type*}

/-- Source variables and five private auxiliary slots for each negative occurrence. -/
abbrev Variable (V : Type*) := Sum V ((ℕ × ℕ) × ℕ)

/-- An auxiliary slot at one clause and literal position. Slot zero is the positive proxy. -/
def auxiliary (i j k : ℕ) : Variable V := .inr ((i, j), k)

/-- Replace a negative literal by its private positive proxy. -/
def positiveLiteral (i j : ℕ) (l : Literal V) : Literal (Variable V) :=
  (if l.2 then .inl l.1 else auxiliary i j 0, true)

/-- The positive complement constraints attached to one negative occurrence. -/
def complementBlock (i j : ℕ) (l : Literal V) : CNF (Variable V) :=
  if l.2 then [] else
    complementClauses (.inl l.1) (auxiliary i j 0) (auxiliary i j 1)
      (auxiliary i j 2) (auxiliary i j 3) (auxiliary i j 4)

/-- One source clause and the positive complement constraints for its negative occurrences. -/
def clauseClauses (i : ℕ) (c : Clause V) : CNF (Variable V) :=
  [c.zipIdx.map fun (l, j) => positiveLiteral i j l] ++
    c.zipIdx.flatMap fun (l, j) => complementBlock i j l

/-- Replace all negative literal occurrences by positive proxies and complement constraints. -/
def formula (φ : CNF V) : CNF (Variable V) :=
  φ.zipIdx.flatMap fun (c, i) => clauseClauses i c

/-- Extend a source assignment: proxies complement the source variable and the remaining
slots have the unique values of the false gadget. Unused slots are immaterial. -/
def extend (φ : CNF V) (σ : V → Bool) : Variable V → Bool
  | .inl v => σ v
  | .inr ((i, j), k) =>
    if k = 0 then
      (((φ[i]?).bind fun c => c[j]?).map fun l => !σ l.1).getD false
    else k == 3

/-- Canonical proxy values at an existing source occurrence. -/
theorem extend_auxiliary_zero (φ : CNF V) (σ : V → Bool) {i j : ℕ}
    {c : Clause V} {l : Literal V} (hc : φ[i]? = some c) (hl : c[j]? = some l) :
    extend φ σ (auxiliary i j 0) = !σ l.1 := by
  simp [extend, auxiliary, hc, hl]

/-- Canonical values of the constant gadget's four slots. -/
theorem extend_auxiliary_constants (φ : CNF V) (σ : V → Bool) (i j : ℕ) :
    extend φ σ (auxiliary i j 1) = false ∧
      extend φ σ (auxiliary i j 2) = false ∧
      extend φ σ (auxiliary i j 3) = true ∧
      extend φ σ (auxiliary i j 4) = false := by
  simp [extend, auxiliary]

/-- A negative occurrence's complement constraints hold under the canonical extension. -/
theorem evalOne_complementBlock_extend (φ : CNF V) (σ : V → Bool) {i j : ℕ}
    {c : Clause V} {l : Literal V} (hc : φ[i]? = some c) (hl : c[j]? = some l) :
    CNF.evalOne (extend φ σ) (complementBlock i j l) = true := by
  unfold complementBlock
  split
  · rfl
  · rw [evalOne_complementClauses_iff]
    have hy := extend_auxiliary_zero φ σ hc hl
    have hconst := extend_auxiliary_constants φ σ i j
    simp only [extend] at *
    exact ⟨by rw [hy, Bool.not_not], hconst⟩

/-- If every complement block holds, the inherited positive clause has the original
exact-one value under the assignment read from source variables. -/
theorem evalOne_inheritedClause (τ : Variable V → Bool) (i : ℕ) (c : Clause V)
    (hcomp : ∀ a ∈ c.zipIdx, CNF.evalOne τ (complementBlock i a.2 a.1) = true) :
    Clause.evalOne τ (c.zipIdx.map fun (l, j) => positiveLiteral i j l) =
      Clause.evalOne (fun v => τ (.inl v)) c := by
  have heval (a : Literal V × ℕ) (ha : a ∈ c.zipIdx) :
      Literal.eval τ (positiveLiteral i a.2 a.1) =
        Literal.eval (fun v => τ (.inl v)) a.1 := by
    rcases a with ⟨⟨v, b⟩, j⟩
    cases b with
    | true => simp [positiveLiteral, Literal.eval]
    | false =>
      have hh := (evalOne_complementClauses_iff τ (.inl v) (auxiliary i j 0)
        (auxiliary i j 1) (auxiliary i j 2) (auxiliary i j 3) (auxiliary i j 4)).mp
          (hcomp ((v, false), j) ha)
      have hy := congrArg Bool.not hh.1
      simpa [positiveLiteral, Literal.eval] using hy.symm
  unfold Clause.evalOne
  congr 1
  rw [List.countP_map]
  calc
    _ = c.zipIdx.countP (fun a => Literal.eval (fun v => τ (.inl v)) a.1) :=
      List.countP_congr (fun a ha => by
        change Literal.eval τ (positiveLiteral i a.2 a.1) = true ↔ _
        rw [heval a ha])
    _ = c.countP (Literal.eval (fun v => τ (.inl v))) := by
      have h := congrArg (List.countP (Literal.eval (fun v => τ (.inl v))))
        (by simp only [List.zipIdx_map_fst] : c.zipIdx.map Prod.fst = c)
      simpa only [List.countP_map, Function.comp_def] using h

/-- A compiled clause is exactly the source clause together with its complement constraints. -/
theorem evalOne_clauseClauses_iff (τ : Variable V → Bool) (i : ℕ) (c : Clause V) :
    CNF.evalOne τ (clauseClauses i c) = true ↔
      Clause.evalOne (fun v => τ (.inl v)) c = true ∧
        ∀ a ∈ c.zipIdx, CNF.evalOne τ (complementBlock i a.2 a.1) = true := by
  simp only [clauseClauses, CNF.evalOne_append, Bool.and_eq_true,
    CNF.evalOne_cons, CNF.evalOne_nil, Bool.and_true, CNF.evalOne_flatMap_eq_true_iff]
  constructor
  · rintro ⟨hmain, hcomp⟩
    exact ⟨(evalOne_inheritedClause τ i c hcomp) ▸ hmain, hcomp⟩
  · rintro ⟨hmain, hcomp⟩
    exact ⟨(evalOne_inheritedClause τ i c hcomp).symm ▸ hmain, hcomp⟩

/-- A satisfying positive output assignment restricts to a satisfying source assignment. -/
theorem evalOne_of_formula (φ : CNF V) (τ : Variable V → Bool)
    (hτ : CNF.evalOne τ (formula φ) = true) :
    CNF.evalOne (fun v => τ (.inl v)) φ = true := by
  rw [CNF.evalOne_eq_true_iff]
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hzip : (φ[i], i) ∈ φ.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  have hh := (CNF.evalOne_flatMap_eq_true_iff τ φ.zipIdx
    (fun (c, i) => clauseClauses i c)).mp hτ (φ[i], i) hzip
  exact (evalOne_clauseClauses_iff τ i φ[i]).mp hh |>.1

/-- Canonical extension preserves the exact-one value of the whole source formula. -/
theorem evalOne_formula_extend (φ : CNF V) (σ : V → Bool) :
    CNF.evalOne (extend φ σ) (formula φ) = CNF.evalOne σ φ := by
  rw [Bool.eq_iff_iff]
  constructor
  · exact evalOne_of_formula φ (extend φ σ)
  · intro hσ
    rw [formula, CNF.evalOne_flatMap_eq_true_iff]
    intro a ha
    rcases a with ⟨c, i⟩
    rw [evalOne_clauseClauses_iff]
    refine ⟨(CNF.evalOne_eq_true_iff σ φ).mp hσ c
      (List.fst_mem_of_mem_zipIdx ha), ?_⟩
    intro a ha'
    rcases a with ⟨l, j⟩
    exact evalOne_complementBlock_extend φ σ
      (List.mem_zipIdx_iff_getElem?.mp ha) (List.mem_zipIdx_iff_getElem?.mp ha')

/-- The positive output is exact-one satisfiable exactly when the source is. -/
theorem oneSatisfiable_formula_iff (φ : CNF V) :
    (formula φ).OneSatisfiable ↔ φ.OneSatisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨fun v => τ (.inl v), evalOne_of_formula φ τ hτ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨extend φ σ, (evalOne_formula_extend φ σ).trans hσ⟩

/-- Every negative-occurrence complement block is satisfied by a satisfying output assignment. -/
theorem evalOne_complementBlock_of_formula (φ : CNF V) (τ : Variable V → Bool)
    (hτ : CNF.evalOne τ (formula φ) = true) {i j : ℕ} {c : Clause V} {l : Literal V}
    (hc : φ[i]? = some c) (hl : c[j]? = some l) :
    CNF.evalOne τ (complementBlock i j l) = true := by
  have hblock := (CNF.evalOne_flatMap_eq_true_iff τ φ.zipIdx
    (fun (c, i) => clauseClauses i c)).mp hτ (c, i)
      (List.mem_zipIdx_iff_getElem?.mpr hc)
  exact (evalOne_clauseClauses_iff τ i c).mp hblock |>.2 (l, j)
    (List.mem_zipIdx_iff_getElem?.mpr hl)

/-- Every source variable remains present, even when all its occurrences are negative. -/
theorem sourceVariable_mem_formula {φ : CNF V} {v : V} (hv : v ∈ φ.vars) :
    Sum.inl v ∈ (formula φ).vars := by
  obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨j, hj, hlj⟩ := List.mem_iff_getElem.mp hl
  have hci : (φ[i], i) ∈ φ.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  have hlj' : ((v, b), j) ∈ φ[i].zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_eq_getElem hj, hlj])
  apply CNF.mem_vars.mpr
  cases b with
  | true =>
    refine ⟨φ[i].zipIdx.map (fun (l, j) => positiveLiteral i j l), ?_, true, ?_⟩
    · exact List.mem_flatMap.mpr ⟨(φ[i], i), hci,
        List.mem_append.mpr (Or.inl (List.mem_singleton_self _))⟩
    · exact List.mem_map.mpr ⟨((v, true), j), hlj', rfl⟩
  | false =>
    refine ⟨[(.inl v, true), (auxiliary i j 0, true), (auxiliary i j 1, true)], ?_,
      true, List.mem_cons_self⟩
    apply List.mem_flatMap.mpr
    refine ⟨(φ[i], i), hci, List.mem_append.mpr (Or.inr ?_)⟩
    exact List.mem_flatMap.mpr ⟨((v, false), j), hlj', List.mem_cons_self⟩

/-- Satisfying complement blocks with equal source values agree on all of their variables. -/
theorem complementBlock_assignments_agree (σ τ : Variable V → Bool) (i j : ℕ)
    (l : Literal V) (hσ : CNF.evalOne σ (complementBlock i j l) = true)
    (hτ : CNF.evalOne τ (complementBlock i j l) = true)
    (hsource : σ (.inl l.1) = τ (.inl l.1)) :
    ∀ v ∈ (complementBlock i j l).vars, σ v = τ v := by
  rcases l with ⟨a, b⟩
  cases b with
  | true => simp [complementBlock, CNF.vars]
  | false =>
    have hs := (evalOne_complementClauses_iff σ _ _ _ _ _ _).mp hσ
    have ht := (evalOne_complementClauses_iff τ _ _ _ _ _ _).mp hτ
    have hy : σ (auxiliary i j 0) = τ (auxiliary i j 0) := by
      have he := hs.1.symm.trans (hsource.trans ht.1)
      have he' := congrArg Bool.not he
      simpa using he'
    intro v hv
    simp only [complementBlock, Bool.false_eq_true, ↓reduceIte, complementClauses,
      forceFalseClauses, CNF.vars, List.flatten_cons, List.flatten_nil, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hsource
      | exact hy
      | exact hs.2.1.trans ht.2.1.symm
      | exact hs.2.2.1.trans ht.2.2.1.symm
      | exact hs.2.2.2.1.trans ht.2.2.2.1.symm
      | exact hs.2.2.2.2.trans ht.2.2.2.2.symm

/-- Satisfying output assignments agree exactly when their source restrictions agree. -/
theorem assignments_agree_iff {φ : CNF V} {σ τ : Variable V → Bool}
    (hσ : CNF.evalOne σ (formula φ) = true) (hτ : CNF.evalOne τ (formula φ) = true) :
    (∀ v ∈ (formula φ).vars, σ v = τ v) ↔
      ∀ v ∈ φ.vars, σ (.inl v) = τ (.inl v) := by
  constructor
  · intro h v hv
    exact h (.inl v) (sourceVariable_mem_formula hv)
  · intro h v hv
    obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp hv
    obtain ⟨⟨a, i⟩, ha, hc⟩ := List.mem_flatMap.mp hc
    have hσblock := (CNF.evalOne_flatMap_eq_true_iff σ φ.zipIdx
      (fun (c, i) => clauseClauses i c)).mp hσ (a, i) ha
    have hτblock := (CNF.evalOne_flatMap_eq_true_iff τ φ.zipIdx
      (fun (c, i) => clauseClauses i c)).mp hτ (a, i) ha
    have hcompσ := (evalOne_clauseClauses_iff σ i a).mp hσblock |>.2
    have hcompτ := (evalOne_clauseClauses_iff τ i a).mp hτblock |>.2
    have hsource (l : Literal V) (j : ℕ) (hl : (l, j) ∈ a.zipIdx) :
        σ (.inl l.1) = τ (.inl l.1) := by
      apply h l.1
      exact CNF.mem_vars.mpr ⟨a, List.fst_mem_of_mem_zipIdx ha, l.2,
        List.fst_mem_of_mem_zipIdx hl⟩
    rcases List.mem_append.mp hc with hc | hc
    · obtain rfl := List.mem_singleton.mp hc
      obtain ⟨⟨l, j⟩, hlj, he⟩ := List.mem_map.mp hl
      have hv : v = (positiveLiteral i j l).1 := (congrArg Prod.fst he).symm
      rw [hv]
      rcases l with ⟨w, b⟩
      cases b with
      | true => exact hsource (w, true) j hlj
      | false =>
        exact complementBlock_assignments_agree σ τ i j (w, false)
          (hcompσ ((w, false), j) hlj) (hcompτ ((w, false), j) hlj)
          (hsource (w, false) j hlj) (auxiliary i j 0) (by
            simp [complementBlock, complementClauses, forceFalseClauses, CNF.vars])
    · obtain ⟨⟨l, j⟩, hlj, hc⟩ := List.mem_flatMap.mp hc
      exact complementBlock_assignments_agree σ τ i j l
        (hcompσ (l, j) hlj) (hcompτ (l, j) hlj) (hsource l j hlj) v
        (CNF.mem_vars.mpr ⟨c, hc, b, hl⟩)

/-- Polarity elimination preserves the number of satisfying assignments on occurring variables. -/
theorem oneModelCount_formula [DecidableEq V] (φ : CNF V) :
    (formula φ).oneModelCount = φ.oneModelCount := by
  classical
  let P (a : φ.vars.toFinset → Bool) : Prop :=
    ∃ σ : V → Bool, φ.evalOne σ = true ∧ ∀ v : φ.vars.toFinset, σ v = a v
  have hsource := CNF.oneModelCount_eq_card_filter
    (φ := φ) (fun σ (v : φ.vars.toFinset) => σ v) P
    (fun σ τ _ _ => by simp [funext_iff, List.mem_toFinset])
    (fun a => by simp [P, funext_iff])
  have houtput := CNF.oneModelCount_eq_card_filter
    (φ := formula φ) (fun τ (v : φ.vars.toFinset) => τ (.inl v)) P
    (fun σ τ hσ hτ => by
      rw [funext_iff]
      constructor
      · intro hh
        apply (assignments_agree_iff hσ hτ).mpr
        intro v hv
        exact hh ⟨v, List.mem_toFinset.mpr hv⟩
      · intro hh v
        exact (assignments_agree_iff hσ hτ).mp hh v (List.mem_toFinset.mp v.property))
    (fun a => by
      constructor
      · rintro ⟨σ, hσ, ha⟩
        refine ⟨extend φ σ, (evalOne_formula_extend φ σ).trans hσ, ?_⟩
        funext v
        exact ha v
      · rintro ⟨τ, hτ, ha⟩
        exact ⟨fun v => τ (.inl v), evalOne_of_formula φ τ hτ, fun v => congrFun ha v⟩)
  exact houtput.trans hsource.symm

/-- A positive literal introduces no complement clauses. -/
theorem complementBlock_positive (i j : ℕ) (v : V) :
    complementBlock i j (v, true) = [] := rfl

/-- A negative literal introduces four clauses. -/
theorem length_complementBlock_negative (i j : ℕ) (v : V) :
    (complementBlock i j (v, false)).length = 4 := rfl

/-- An individual complement block has at most four clauses. -/
theorem length_complementBlock_le (i j : ℕ) (l : Literal V) :
    (complementBlock i j l).length ≤ 4 := by
  cases l with
  | mk v b => cases b <;> simp [complementBlock, complementClauses, forceFalseClauses]

/-- An individual source clause contributes at most four clauses per literal, plus itself. -/
theorem length_clauseClauses_le (i : ℕ) (c : Clause V) :
    (clauseClauses i c).length ≤ 1 + 4 * c.length := by
  simp only [clauseClauses, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap]
  have h : (c.zipIdx.map fun (l, j) => (complementBlock i j l).length).sum ≤
      (c.zipIdx.map fun _ => 4).sum :=
    List.sum_le_sum fun a _ => length_complementBlock_le i a.2 a.1
  simpa [Nat.mul_comm] using h

/-- Width at most `k` gives a factor `1 + 4*k` bound on the number of clauses. -/
theorem length_formula_le {k : ℕ} {φ : CNF V} (hw : ∀ c ∈ φ, c.length ≤ k) :
    (formula φ).length ≤ (1 + 4 * k) * φ.length := by
  simp only [formula, List.length_flatMap]
  have h : (φ.zipIdx.map fun (c, i) => (clauseClauses i c).length).sum ≤
      (φ.zipIdx.map fun _ => 1 + 4 * k).sum := by
    apply List.sum_le_sum
    intro a ha
    exact (length_clauseClauses_le a.2 a.1).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hw _ (List.fst_mem_of_mem_zipIdx ha))) _)
  simpa [Nat.mul_comm] using h

/-- All literals in a complement block are positive. -/
theorem positive_complementBlock (i j : ℕ) (l : Literal V) :
    ∀ c ∈ complementBlock i j l, ∀ a ∈ c, a.2 = true := by
  unfold complementBlock
  split
  · simp
  · exact positive_complementClauses _ _ _ _ _ _

/-- Every literal emitted by the compiler is positive. -/
theorem positive_formula (φ : CNF V) :
    ∀ c ∈ formula φ, ∀ l ∈ c, l.2 = true := by
  intro c hc l hl
  obtain ⟨⟨a, i⟩, _, hc⟩ := List.mem_flatMap.mp hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain rfl := List.mem_singleton.mp hc
    obtain ⟨⟨b, j⟩, _, rfl⟩ := List.mem_map.mp hl
    rfl
  · obtain ⟨⟨b, j⟩, _, hc⟩ := List.mem_flatMap.mp hc
    exact positive_complementBlock i j b c hc l hl

/-- The inherited clause retains its width and every complement clause has width three. -/
theorem width_clauseClauses {k : ℕ} (hk : 3 ≤ k) (i : ℕ) (c : Clause V)
    (hc : c.length ≤ k) : ∀ a ∈ clauseClauses i c, a.length ≤ k := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain rfl := List.mem_singleton.mp ha
    simpa [Nat.mul_comm] using hc
  · obtain ⟨⟨l, j⟩, _, ha⟩ := List.mem_flatMap.mp ha
    change a ∈ complementBlock i j l at ha
    unfold complementBlock at ha
    split at ha
    · simp at ha
    · exact (width_complementClauses _ _ _ _ _ _ a ha).le.trans hk

/-- Exact-three input clauses yield exact-three positive clauses. -/
theorem exactWidth_formula {φ : CNF V} (hw : ∀ c ∈ φ, c.length = 3) :
    ∀ c ∈ formula φ, c.length = 3 := by
  intro c hc
  obtain ⟨⟨a, i⟩, ha, hc⟩ := List.mem_flatMap.mp hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain rfl := List.mem_singleton.mp hc
    simpa [Nat.mul_comm] using hw a (List.fst_mem_of_mem_zipIdx ha)
  · obtain ⟨⟨l, j⟩, _, hc⟩ := List.mem_flatMap.mp hc
    change c ∈ complementBlock i j l at hc
    unfold complementBlock at hc
    split at hc
    · simp at hc
    · exact width_complementClauses _ _ _ _ _ _ _ hc

/-- Variable occurrences contributed by one transformed source literal, including its private
complement gadget when needed. -/
def occurrenceVariables (i j : ℕ) (l : Literal V) : List (Variable V) :=
  [(positiveLiteral i j l).1] ++ (complementBlock i j l).vars

/-- Distinct source variables remain distinct in the inherited positive clause. -/
theorem nodup_inheritedClause (i : ℕ) (c : Clause V) (hc : (c.map Prod.fst).Nodup) :
    ((c.zipIdx.map fun (l, j) => positiveLiteral i j l).map Prod.fst).Nodup := by
  have hvars : (c.zipIdx.map fun a => a.1.1).Nodup := by
    have he := congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 c)
    simp only [List.map_map, Function.comp_def] at he
    rw [he]
    exact hc
  have hidx := List.nodup_zipIdx_map_snd c
  change List.Pairwise _ _ at hvars hidx ⊢
  rw [List.map_map, List.pairwise_map]
  have hboth := (List.pairwise_map.mp hvars).and (List.pairwise_map.mp hidx)
  apply hboth.imp
  intro a b hab
  rcases a with ⟨⟨v, p⟩, j⟩
  rcases b with ⟨⟨w, q⟩, k⟩
  cases p <;> cases q <;> simp_all [positiveLiteral, auxiliary]

/-- Every complement clause has three distinct variables, regardless of its source literal. -/
theorem nodup_complementBlock (i j : ℕ) (l : Literal V) :
    ∀ c ∈ complementBlock i j l, (c.map Prod.fst).Nodup := by
  unfold complementBlock
  split
  · simp
  · simp [complementClauses, forceFalseClauses, auxiliary]

/-- Distinct variables in every source clause give distinct variables in every output clause. -/
theorem nodup_formula {φ : CNF V} (hn : ∀ c ∈ φ, (c.map Prod.fst).Nodup) :
    ∀ c ∈ formula φ, (c.map Prod.fst).Nodup := by
  intro c hc
  obtain ⟨⟨a, i⟩, ha, hc⟩ := List.mem_flatMap.mp hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain rfl := List.mem_singleton.mp hc
    exact nodup_inheritedClause i a (hn a (List.fst_mem_of_mem_zipIdx ha))
  · obtain ⟨⟨l, j⟩, _, hc⟩ := List.mem_flatMap.mp hc
    exact nodup_complementBlock i j l c hc

/-- Width at most three is preserved. -/
theorem width_formula {φ : CNF V} (hw : ∀ c ∈ φ, c.length ≤ 3) :
    ∀ c ∈ formula φ, c.length ≤ 3 := by
  intro c hc
  obtain ⟨⟨a, i⟩, ha, hc⟩ := List.mem_flatMap.mp hc
  exact width_clauseClauses (by decide) i a (hw a (List.fst_mem_of_mem_zipIdx ha)) c hc

/-- Width-three inputs have at most thirty-nine output literal occurrences per source clause. -/
theorem length_vars_formula_le {φ : CNF V} (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (formula φ).vars.length ≤ 39 * φ.length := by
  have h := CNF.length_vars_le_mul_length (width_formula hw)
  exact h.trans (by simpa [← Nat.mul_assoc] using Nat.mul_le_mul_left 3 (length_formula_le hw))

private theorem count_map_append_flatMap {α β : Type*} [BEq β]
    (as : List α) (f : α → β) (g : α → List β) (v : β) :
    (as.map f ++ as.flatMap g).count v =
      (as.map fun a => ([f a] ++ g a).count v).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.count_cons,
      List.count_append, List.sum_cons, List.count_nil] at *
    split_ifs <;> omega

/-- Clause-block variable counts are the sum of the individual occurrence contributions. -/
theorem count_vars_clauseClauses [DecidableEq V] (i : ℕ) (c : Clause V)
    (v : Variable V) :
    (clauseClauses i c).vars.count v =
      (c.zipIdx.map fun a => (occurrenceVariables i a.2 a.1).count v).sum := by
  have hv : (clauseClauses i c).vars =
      c.zipIdx.map (fun a => (positiveLiteral i a.2 a.1).1) ++
        c.zipIdx.flatMap (fun a => (complementBlock i a.2 a.1).vars) := by
    simp [clauseClauses, CNF.vars, List.flatMap_def, List.map_flatten,
      List.flatten_flatten, List.map_map, Function.comp_def]
  rw [hv]
  exact count_map_append_flatMap c.zipIdx (fun a => (positiveLiteral i a.2 a.1).1)
    (fun a => (complementBlock i a.2 a.1).vars) v

/-- An original variable contributes exactly one occurrence at its original literal position. -/
theorem count_inl_occurrenceVariables [DecidableEq V] (i j : ℕ) (l : Literal V)
    (v : V) : (occurrenceVariables i j l).count (Sum.inl v) = [l.1].count v := by
  cases hb : l.2 <;>
    simp [occurrenceVariables, positiveLiteral, complementBlock, complementClauses,
      forceFalseClauses, auxiliary, CNF.vars, List.count_cons, hb]

/-- A private occurrence contribution uses only its own clause and literal indices and has
degree at most three at each auxiliary. -/
theorem count_aux_occurrenceVariables [DecidableEq V] (i j a b k : ℕ) (l : Literal V) :
    (occurrenceVariables i j l).count (auxiliary a b k) ≤
      if a = i ∧ b = j then 3 else 0 := by
  by_cases hi : a = i
  · subst a
    by_cases hj : b = j
    · subst b
      by_cases hk : k < 5
      · interval_cases k <;> cases hb : l.2 <;>
          simp [occurrenceVariables, positiveLiteral, complementBlock, complementClauses,
            forceFalseClauses, auxiliary, CNF.vars, hb]
      · have h0 : 0 ≠ k := by omega
        have h1 : 1 ≠ k := by omega
        have h2 : 2 ≠ k := by omega
        have h3 : 3 ≠ k := by omega
        have h4 : 4 ≠ k := by omega
        cases hb : l.2 <;>
          simp [occurrenceVariables, positiveLiteral, complementBlock,
            complementClauses, forceFalseClauses, auxiliary, CNF.vars, hb,
            h0, h1, h2, h3, h4]
    · cases hb : l.2 <;>
        simp [occurrenceVariables, positiveLiteral, complementBlock, complementClauses,
          forceFalseClauses, auxiliary, CNF.vars, hb, hj, Ne.symm hj]
  · cases hb : l.2 <;>
      simp [occurrenceVariables, positiveLiteral, complementBlock, complementClauses,
        forceFalseClauses, auxiliary, CNF.vars, hb, hi, Ne.symm hi]

/-- Original variable occurrence counts are unchanged in each compiled clause block. -/
theorem count_inl_clause [DecidableEq V] (i : ℕ) (c : Clause V) (v : V) :
    (clauseClauses i c).vars.count (Sum.inl v) = (CNF.vars [c]).count v := by
  rw [count_vars_clauseClauses]
  simp only [count_inl_occurrenceVariables]
  have h : (c.zipIdx.flatMap fun a => [a.1.1]).count v =
      (c.zipIdx.map fun a => [a.1.1].count v).sum := by
    rw [List.count_flatMap]
    rfl
  rw [← h]
  have he : c.zipIdx.flatMap (fun a => [a.1.1]) = c.zipIdx.map (fun a => a.1.1) := by
    induction c.zipIdx with
    | nil => rfl
    | cons a as ih => simp [ih]
  rw [he]
  simp only [CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun ls : List (Literal V) => (ls.map Prod.fst).count v)
      (List.zipIdx_map_fst 0 c)

/-- An auxiliary contributes at most three occurrences in a clause block, and no occurrences
outside its own source clause index. -/
theorem count_aux_clause [DecidableEq V] (i a j k : ℕ) (c : Clause V) :
    (clauseClauses i c).vars.count (auxiliary a j k) ≤ if a = i then 3 else 0 := by
  rw [count_vars_clauseClauses]
  calc
    _ ≤ (c.zipIdx.map fun l => if a = i ∧ j = l.2 then 3 else 0).sum :=
      List.sum_le_sum fun l _ => count_aux_occurrenceVariables i l.2 a j k l.1
    _ ≤ if a = i then 3 else 0 := by
      by_cases hi : a = i
      · simp only [hi, true_and, ite_true]
        have he : (c.zipIdx.map fun l => if j = l.2 then 3 else 0).sum =
            (c.zipIdx.map Prod.snd).count j * 3 := by
          calc
            _ = ((c.zipIdx.map Prod.snd).map fun b => if j = b then 3 else 0).sum := by
              rw [List.map_map]
              rfl
            _ = _ := by
              rw [List.sum_map_eq_nsmul_single j _ (fun _ h _ => by simp [Ne.symm h])]
              simp
        rw [he]
        have hcount := List.nodup_iff_count_le_one.mp (List.nodup_zipIdx_map_snd c) j
        omega
      · simp [hi]

/-- Taking variable occurrences commutes with concatenating clause replacements. -/
theorem vars_formula (φ : CNF V) :
    (formula φ).vars = φ.zipIdx.flatMap fun c => (clauseClauses c.2 c.1).vars := by
  simp [formula, CNF.vars, List.flatMap_def, List.map_flatten, List.flatten_flatten,
    List.map_map, Function.comp_def]

/-- Every original variable keeps exactly its original number of literal occurrences. -/
theorem count_inl_formula [DecidableEq V] (φ : CNF V) (v : V) :
    (formula φ).vars.count (Sum.inl v) = φ.vars.count v := by
  rw [vars_formula, List.count_flatMap]
  have hlocal (c : Clause V × ℕ) :
      (clauseClauses c.2 c.1).vars.count (Sum.inl v) = (CNF.vars [c.1]).count v :=
    count_inl_clause c.2 c.1 v
  simp only [Function.comp_def]
  rw [List.map_congr_left (fun c _ => hlocal c)]
  simp only [CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.map_flatten, List.count_flatten, List.map_map, Function.comp_def]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun cs : List (Clause V) => (cs.map fun c => (c.map Prod.fst).count v).sum)
      (List.zipIdx_map_fst 0 φ)

/-- Every private auxiliary has at most three occurrences in the whole output. -/
theorem count_aux_formula [DecidableEq V] (φ : CNF V) (i j k : ℕ) :
    (formula φ).vars.count (auxiliary i j k) ≤ 3 := by
  rw [vars_formula, List.count_flatMap]
  calc
    _ ≤ (φ.zipIdx.map fun c => if i = c.2 then 3 else 0).sum :=
      List.sum_le_sum fun c _ => count_aux_clause _ _ _ _ _
    _ = (φ.zipIdx.map Prod.snd).count i * 3 := by
      calc
        _ = ((φ.zipIdx.map Prod.snd).map fun b => if i = b then 3 else 0).sum := by
          rw [List.map_map]
          rfl
        _ = _ := by
          rw [List.sum_map_eq_nsmul_single i _ (fun _ h _ => by simp [Ne.symm h])]
          simp
    _ ≤ 3 := by
      have hcount := List.nodup_iff_count_le_one.mp (List.nodup_zipIdx_map_snd φ) i
      omega

/-- The positive compiler preserves the three-occurrence restriction. -/
theorem count_vars_formula_le [DecidableEq V] (φ : CNF V)
    (ho : ∀ v, φ.vars.count v ≤ 3) (v : Variable V) :
    (formula φ).vars.count v ≤ 3 := by
  cases v with
  | inl v => rw [count_inl_formula]; exact ho v
  | inr v => exact count_aux_formula φ v.1.1 v.1.2 v.2

end Cslib.Logic.PL.CNF.PositiveExactOne
