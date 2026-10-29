/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne.Gadgets
public import Complexity.Logics.Propositional.CNF.ExactOne.ModelCount
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.IntervalCases

/-!
# Parsimonious conversion of ordinary clauses to exact-one clauses

Each clause of width at most three is replaced by the four-clause disjunction gadget of
[Hunt, Marathe, Radhakrishnan and Stearns, Theorem 3.8, Figure 3.4]
[HuntMaratheRadhakrishnanStearns1998]. Missing literals are replaced by distinct, uniquely
forced false variables. Unlike repeating a source literal, this preserves the number of
occurrences of every source variable. Even an empty clause has an exact-three, unsatisfiable
output. Clauses longer than three are truncated; correctness therefore requires the width bound.

## Main definitions

* `FromSAT.clause`: the constant-size replacement of one clause.
* `FromSAT.formula`: replace every clause with separately indexed auxiliaries.
* `FromSAT.assignment`: the canonical extension of a source assignment.

## Main results

* `FromSAT.length_clause_le`, `FromSAT.length_formula_le`: constant-factor clause bounds.

## References

* [Hunt, Marathe, Radhakrishnan and Stearns][HuntMaratheRadhakrishnanStearns1998],
  Theorem 3.8 and Lemma 3.6.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.FromSAT

open ExactOneGadget

variable {V : Type*}

/-- Source variables and clause-indexed auxiliary slots. -/
abbrev Variable (V : Type*) := Sum V (ℕ × ℕ)

/-- An auxiliary slot local to one source clause. -/
def aux (i k : ℕ) : Variable V := Sum.inr (i, k)

/-- Embed a signed source literal. -/
def lift (l : Literal V) : Literal (Variable V) := (Sum.inl l.1, l.2)

/-- A positive padding literal, used only when the corresponding source position is absent. -/
def padding (i k : ℕ) : Literal (Variable V) := (aux i k, true)

/-- The uniquely extensible disjunction gadget in local slots three through seven. -/
def core (i : ℕ) (p q r : Literal (Variable V)) : CNF (Variable V) :=
  disjunctionClauses p q r (aux i 3) (aux i 4) (aux i 5) (aux i 6) (aux i 7)

/-- Force padding slot `k` false, using its own three auxiliary slots. -/
def forcePadding (i k : ℕ) : CNF (Variable V) :=
  forceFalseClauses (aux i k) (aux i (8 + 3 * k))
    (aux i (9 + 3 * k)) (aux i (10 + 3 * k))

/-- Replace one clause by exact-three exact-one clauses, retaining every source occurrence once. -/
def clause (i : ℕ) : Clause V → CNF (Variable V)
  | [] => core i (padding i 0) (padding i 1) (padding i 2) ++
      forcePadding i 0 ++ forcePadding i 1 ++ forcePadding i 2
  | [p] => core i (lift p) (padding i 1) (padding i 2) ++
      forcePadding i 1 ++ forcePadding i 2
  | [p, q] => core i (lift p) (lift q) (padding i 2) ++ forcePadding i 2
  | p :: q :: r :: _ => core i (lift p) (lift q) (lift r)

/-- Replace the source clauses, distinguishing auxiliaries by clause position. -/
def formula (φ : CNF V) : CNF (Variable V) :=
  φ.zipIdx.flatMap fun c => clause c.2 c.1

/-- The source truth value at a clause position; absent positions are false. -/
def sourceValue (σ : V → Bool) (c : Clause V) (k : ℕ) : Bool :=
  (c[k]?).elim false (Literal.eval σ)

/-- Canonical auxiliary values, including all three possible false-padding blocks. -/
def auxiliaryValue (σ : V → Bool) (c : Clause V) (k : ℕ) : Bool :=
  let p := sourceValue σ c 0
  let q := sourceValue σ c 1
  let r := sourceValue σ c 2
  if k = 3 then firstAux p q
  else if k = 4 then secondAux p q
  else if k = 5 then thirdAux p q
  else if k = 6 then fourthAux p q
  else if k = 7 then fifthAux p q r
  else decide (k = 9 ∨ k = 12 ∨ k = 15)

/-- Extend an assignment by the uniquely determined values of all occurring auxiliaries. -/
def assignment (φ : CNF V) (σ : V → Bool) : Variable V → Bool
  | Sum.inl v => σ v
  | Sum.inr (i, k) => auxiliaryValue σ (φ[i]?.getD []) k

/-- A clause contributes between four and thirteen clauses. -/
theorem length_clause_le (i : ℕ) (c : Clause V) : (clause i c).length ≤ 13 := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩ <;>
    simp [clause, core, disjunctionClauses, forcePadding, forceFalseClauses]

/-- Every output clause has exactly three literal occurrences. -/
theorem width_clause (i : ℕ) (c : Clause V) :
    ∀ d ∈ clause i c, d.length = 3 := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩ <;>
    simp [clause, core, disjunctionClauses, forcePadding, forceFalseClauses]

/-- Clause replacement increases the number of clauses by at most a factor of thirteen. -/
theorem length_formula_le (φ : CNF V) : (formula φ).length ≤ 13 * φ.length := by
  calc
    _ = (φ.zipIdx.map fun c => (clause c.2 c.1).length).sum := List.length_flatMap
    _ ≤ (φ.zipIdx.map fun _ => 13).sum := List.sum_le_sum fun _ _ => length_clause_le _ _
    _ = _ := by simp [Nat.mul_comm]

/-- Every output clause is exact-three, including on malformed source inputs. -/
theorem width_formula (φ : CNF V) : ∀ c ∈ formula φ, c.length = 3 := by
  intro c hc
  obtain ⟨d, _, hc⟩ := List.mem_flatMap.mp hc
  exact width_clause d.2 d.1 c hc

/-- Every satisfying replacement restricts to a satisfying source clause. -/
theorem clause_sound (i : ℕ) (c : Clause V) (hc : c.length ≤ 3)
    (τ : Variable V → Bool) (hτ : (clause i c).evalOne τ = true) :
    c.eval (fun v => τ (Sum.inl v)) = true := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
  · simp only [clause, CNF.evalOne_append, Bool.and_eq_true, core,
      evalOne_disjunctionClauses_iff_canonical, forcePadding,
      evalOne_forceFalseClauses_iff] at hτ
    obtain ⟨⟨⟨hcore, h₀⟩, h₁⟩, h₂⟩ := hτ
    simpa [padding, Literal.eval, h₀.1, h₁.1, h₂.1] using hcore.1
  · simp only [clause, CNF.evalOne_append, Bool.and_eq_true, core,
      evalOne_disjunctionClauses_iff_canonical, forcePadding,
      evalOne_forceFalseClauses_iff] at hτ
    obtain ⟨⟨hcore, h₁⟩, h₂⟩ := hτ
    simpa [padding, lift, Literal.eval, h₁.1, h₂.1, Clause.eval] using hcore.1
  · simp only [clause, CNF.evalOne_append, Bool.and_eq_true, core,
      evalOne_disjunctionClauses_iff_canonical, forcePadding,
      evalOne_forceFalseClauses_iff] at hτ
    obtain ⟨hcore, h₂⟩ := hτ
    simpa [padding, lift, Literal.eval, h₂.1, Clause.eval] using hcore.1
  · have hrest : rest = [] := by simpa using hc
    subst rest
    have hcore := (evalOne_disjunctionClauses_iff_canonical τ _ _ _ _ _ _ _ _).mp hτ
    simpa [lift, Literal.eval, Clause.eval, or_assoc] using hcore.1

/-- The canonical extension satisfies a local gadget exactly when its source clause holds. -/
theorem clause_complete (φ : CNF V) (σ : V → Bool) (i : ℕ) (c : Clause V)
    (hi : φ[i]? = some c) (hc : c.length ≤ 3) :
    (clause i c).evalOne (assignment φ σ) = c.eval σ := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    exact clause_sound i c hc (assignment φ σ) h
  · intro h
    rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
    · simp at h
    · simpa [clause, core, CNF.evalOne_append, evalOne_disjunctionClauses_iff_canonical,
        forcePadding, evalOne_forceFalseClauses_iff, padding, lift, assignment, auxiliaryValue,
        sourceValue, hi, aux, Clause.eval, Literal.eval] using h
    · simpa [clause, core, CNF.evalOne_append, evalOne_disjunctionClauses_iff_canonical,
        forcePadding, evalOne_forceFalseClauses_iff, padding, lift, assignment, auxiliaryValue,
        sourceValue, hi, aux, Clause.eval, Literal.eval] using h
    · have hrest : rest = [] := by simpa using hc
      subst rest
      simpa [clause, core, CNF.evalOne_append, evalOne_disjunctionClauses_iff_canonical,
        padding, lift, assignment, auxiliaryValue, sourceValue, hi, aux, Clause.eval,
        Literal.eval, or_assoc] using h

/-- Restricting an exact-one output assignment recovers an ordinary satisfying assignment. -/
theorem formula_sound (φ : CNF V) (hw : ∀ c ∈ φ, c.length ≤ 3)
    (τ : Variable V → Bool) (hτ : (formula φ).evalOne τ = true) :
    φ.eval (fun v => τ (Sum.inl v)) = true := by
  rw [CNF.eval_eq_true_iff]
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  apply clause_sound i _ (hw _ (List.getElem_mem hi)) τ
  exact (CNF.evalOne_flatMap_eq_true_iff τ φ.zipIdx _).mp hτ (φ[i], i)
    (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi))

/-- The canonical extension satisfies the output exactly when the source assignment does. -/
theorem evalOne_formula_assignment (φ : CNF V) (σ : V → Bool)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (formula φ).evalOne (assignment φ σ) = φ.eval σ := by
  rw [Bool.eq_iff_iff, formula, CNF.evalOne_flatMap_eq_true_iff, CNF.eval_eq_true_iff]
  constructor
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    have hm : (φ[i], i) ∈ φ.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
    have hlocal := h _ hm
    rw [clause_complete φ σ i _ (List.getElem?_eq_getElem hi)
      (hw _ (List.getElem_mem hi))] at hlocal
    exact hlocal
  · intro h ⟨c, i⟩ hi
    have hic : φ[i]? = some c := List.mem_zipIdx_iff_getElem?.mp hi
    have hc : c ∈ φ := List.fst_mem_of_mem_zipIdx hi
    rw [clause_complete φ σ i c hic (hw c hc)]
    exact h c hc

/-- Width-three ordinary satisfiability is equivalent to exact-one output satisfiability. -/
theorem oneSatisfiable_formula (φ : CNF V) (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (formula φ).OneSatisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨_, formula_sound φ hw τ hτ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨assignment φ σ, (evalOne_formula_assignment φ σ hw).trans hσ⟩

/-- Three literal occurrences per output clause give a constant-factor literal bound. -/
theorem length_vars_formula_le (φ : CNF V) : (formula φ).vars.length ≤ 39 * φ.length := by
  have h := CNF.length_vars_le_mul_length (fun c hc => (width_formula φ c hc).le)
  simpa only [← Nat.mul_assoc] using h.trans (Nat.mul_le_mul_left 3 (length_formula_le φ))

/-- Every inherited variable occurs exactly as often in its clause replacement as in the
source clause. This includes repeated literals with either polarity. -/
theorem count_inl_clause [DecidableEq V] (i : ℕ) (c : Clause V) (hc : c.length ≤ 3) (v : V) :
    (clause i c).vars.count (Sum.inl v) = (CNF.vars [c]).count v := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
  · simp [clause, core, disjunctionClauses, forcePadding, forceFalseClauses, CNF.vars,
      padding, aux, Std.Sat.Literal.negate]
  · simp [clause, core, disjunctionClauses, forcePadding, forceFalseClauses, CNF.vars,
      padding, lift, aux, Std.Sat.Literal.negate, List.count_cons]
  · simp [clause, core, disjunctionClauses, forcePadding, forceFalseClauses, CNF.vars,
      padding, lift, aux, Std.Sat.Literal.negate, List.count_cons]
  · have hrest : rest = [] := by simpa using hc
    subst rest
    simp [clause, core, disjunctionClauses, CNF.vars, lift, aux, Std.Sat.Literal.negate,
      List.count_cons]

/-- The replacement uses auxiliaries only in its own clause index. -/
theorem auxiliary_index {i j k : ℕ} {c : Clause V}
    (h : Sum.inr (j, k) ∈ (clause i c).vars) : j = i := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩ <;>
    simp [clause, core, disjunctionClauses, forcePadding, forceFalseClauses,
      padding, lift, aux, CNF.vars, Std.Sat.Literal.negate] at h <;> tauto

/-- No local auxiliary exceeds three occurrences. -/
theorem count_aux_clause [DecidableEq V] (i j k : ℕ) (c : Clause V) :
    (clause i c).vars.count (Sum.inr (j, k)) ≤ 3 := by
  by_cases hji : j = i
  · subst j
    rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩ <;>
      simp only [vars, clause, core, disjunctionClauses, lift, aux, Std.Sat.Literal.negate,
        padding, Bool.not_true, forcePadding, forceFalseClauses, mul_zero, add_zero, mul_one,
        Nat.reduceAdd, Nat.reduceMul, List.cons_append, List.nil_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.map_cons, List.map_nil, ne_eq, reduceCtorEq,
        not_false_eq_true, List.count_cons_of_ne, List.count_cons,
        Sum.inr.injEq, Prod.mk.injEq,
        List.count_nil, beq_iff_eq, true_and, zero_add] <;>
      (by_cases hk : k < 17
       · interval_cases k <;> decide
       · simp (discharger := omega) only [ite_eq_right, add_zero, Nat.zero_le])
  · rw [List.count_eq_zero.mpr (fun hm => hji (auxiliary_index hm))]
    omega

/-- Every replacement clause has three distinct variable names, even when source variables
are repeated. -/
theorem nodup_clause (i : ℕ) (c : Clause V) :
    ∀ d ∈ clause i c, (d.map Prod.fst).Nodup := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩ <;>
    simp [clause, core, disjunctionClauses, forcePadding, forceFalseClauses,
      padding, lift, aux, Std.Sat.Literal.negate]

/-- Taking variable occurrences commutes with concatenating clause replacements. -/
theorem vars_formula (φ : CNF V) :
    (formula φ).vars = φ.zipIdx.flatMap fun c => (clause c.2 c.1).vars := by
  simp [formula, CNF.vars, List.flatMap_def, List.map_flatten, List.flatten_flatten,
    List.map_map, Function.comp_def]

/-- Source occurrence counts are preserved exactly by the whole replacement. -/
theorem count_inl_formula [DecidableEq V] (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (v : V) :
    (formula φ).vars.count (Sum.inl v) = φ.vars.count v := by
  rw [vars_formula, List.count_flatMap]
  have hlocal (c : Clause V × ℕ) (hc : c ∈ φ.zipIdx) :
      (clause c.2 c.1).vars.count (Sum.inl v) = (CNF.vars [c.1]).count v :=
    count_inl_clause c.2 c.1 (hw _ (List.fst_mem_of_mem_zipIdx hc)) v
  simp only [Function.comp_def]
  rw [List.map_congr_left (fun c hc => hlocal c hc)]
  simp only [CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.map_flatten, List.count_flatten, List.map_map, Function.comp_def]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun cs : List (Clause V) => (cs.map fun c => (c.map Prod.fst).count v).sum)
      (List.zipIdx_map_fst 0 φ)

/-- Each auxiliary belongs to just one source clause, so the local degree bound is global. -/
theorem count_aux_formula [DecidableEq V] (φ : CNF V) (i k : ℕ) :
    (formula φ).vars.count (Sum.inr (i, k)) ≤ 3 := by
  rw [vars_formula, List.count_flatMap]
  have hlocal (c : Clause V × ℕ) :
      (clause c.2 c.1).vars.count (Sum.inr (i, k)) ≤ if c.2 = i then 3 else 0 := by
    split_ifs with hi
    · exact count_aux_clause _ _ _ _
    · rw [List.count_eq_zero.mpr (fun hm => hi (auxiliary_index hm).symm)]
  calc
    _ ≤ (φ.zipIdx.map fun c => if c.2 = i then 3 else 0).sum :=
      List.sum_le_sum fun c _ => hlocal c
    _ = ((φ.zipIdx.map Prod.snd).map fun j => if j = i then 3 else 0).sum := by
      rw [List.map_map]
      rfl
    _ = (φ.zipIdx.map Prod.snd).count i * 3 := by
      rw [List.sum_map_eq_nsmul_single i _ (fun _ h _ => by simp [h])]
      simp
    _ ≤ 3 := by
      have h := List.nodup_iff_count_le_one.mp (List.nodup_zipIdx_map_snd φ) i
      omega

/-- A three-occurrence source produces a three-occurrence exact-one formula. -/
theorem count_vars_formula_le [DecidableEq V] (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (ho : ∀ v, φ.vars.count v ≤ 3)
    (v : Variable V) : (formula φ).vars.count v ≤ 3 := by
  cases v with
  | inl v => rw [count_inl_formula φ hw]; exact ho v
  | inr v => exact count_aux_formula φ v.1 v.2

/-- Exactly the used source variables occur among the inherited output variables. -/
theorem inl_mem_vars_formula (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (v : V) :
    Sum.inl v ∈ (formula φ).vars ↔ v ∈ φ.vars := by
  classical
  rw [← List.count_pos_iff, count_inl_formula φ hw, List.count_pos_iff]

/-- Two satisfying local assignments that agree on source variables agree everywhere used
by the replacement. This is the unique-extension property on the actual variable support. -/
theorem clause_agree (i : ℕ) (c : Clause V) (σ τ : Variable V → Bool)
    (hσ : (clause i c).evalOne σ = true) (hτ : (clause i c).evalOne τ = true)
    (hs : ∀ l ∈ c, σ (Sum.inl l.1) = τ (Sum.inl l.1)) :
    ∀ v ∈ (clause i c).vars, σ v = τ v := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩ <;>
    simp only [clause, core, CNF.evalOne_append, Bool.and_eq_true,
      evalOne_disjunctionClauses_iff_canonical, forcePadding,
      evalOne_forceFalseClauses_iff, padding, lift, Literal.eval_mk,
      aux] at hσ hτ <;>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, forall_false] at hs <;>
    simp only [vars, clause, core, disjunctionClauses, lift, padding, aux,
      Std.Sat.Literal.negate, Bool.not_true, forcePadding, forceFalseClauses,
      mul_zero, add_zero, mul_one, Nat.reduceAdd, Nat.reduceMul, List.cons_append,
      List.nil_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] <;>
    grind

/-- Satisfying output assignments are determined exactly by their source restrictions. -/
theorem assignments_agree_iff (φ : CNF V) (hw : ∀ c ∈ φ, c.length ≤ 3)
    (σ τ : Variable V → Bool) (hσ : (formula φ).evalOne σ = true)
    (hτ : (formula φ).evalOne τ = true) :
    (∀ v ∈ φ.vars, σ (Sum.inl v) = τ (Sum.inl v)) ↔
      ∀ v ∈ (formula φ).vars, σ v = τ v := by
  constructor
  · intro hs v hv
    rw [vars_formula] at hv
    obtain ⟨⟨c, i⟩, hi, hv⟩ := List.mem_flatMap.mp hv
    have hc := List.fst_mem_of_mem_zipIdx hi
    exact clause_agree i c σ τ
      ((CNF.evalOne_flatMap_eq_true_iff σ φ.zipIdx _).mp hσ _ hi)
      ((CNF.evalOne_flatMap_eq_true_iff τ φ.zipIdx _).mp hτ _ hi)
      (fun l hl => hs l.1 (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩)) v hv
  · intro hs v hv
    exact hs _ ((inl_mem_vars_formula φ hw v).mpr hv)

/-- The ordinary and exact-one counts coincide, on occurring variables on both sides. -/
theorem oneModelCount_formula [DecidableEq V] (φ : CNF V)
    (hw : ∀ c ∈ φ, c.length ≤ 3) : (formula φ).oneModelCount = φ.modelCount := by
  let f (τ : Variable V → Bool) (v : φ.vars.toFinset) : Bool := τ (Sum.inl v)
  change (formula φ).oneModelCount =
    (Finset.univ.filter fun τ : φ.vars.toFinset → Bool =>
      φ.eval (φ.extendAssignment τ) = true).card
  refine CNF.oneModelCount_eq_card_filter f
    (fun τ => φ.eval (φ.extendAssignment τ) = true) (fun σ τ hσ hτ => ?_) fun τ => ?_
  · rw [← assignments_agree_iff φ hw σ τ hσ hτ]
    exact ⟨fun h v hv => congrFun h ⟨v, List.mem_toFinset.mpr hv⟩,
      fun h => funext fun v => h v (List.mem_toFinset.mp v.2)⟩
  · constructor
    · intro hτ
      refine ⟨assignment φ (φ.extendAssignment τ), ?_, funext fun v => ?_⟩
      · exact (evalOne_formula_assignment φ _ hw).trans hτ
      · exact CNF.extendAssignment_of_mem τ (List.mem_toFinset.mp v.2)
    · rintro ⟨σ, hσ, rfl⟩
      have hs := formula_sound φ hw σ hσ
      exact (CNF.eval_congr (fun v hv =>
        CNF.extendAssignment_of_mem (f σ) hv)).trans hs

end Cslib.Logic.PL.CNF.FromSAT
