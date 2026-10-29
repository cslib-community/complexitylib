/-
Copyright (c) 2026 Erik Demaine, Stefan Langerman, GPT 5.6. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
import Mathlib.Data.List.Count
import Mathlib.Data.Bool.Basic

/-!
# Directed implication cycles

A binary implication cycle forces all its variables to have the same Boolean value. Each
listed variable contributes exactly two literal occurrences, including the two occurrences in a
singleton cycle. Repeated variables are counted with multiplicity. These are the implication
cycles used in [Papadimitriou, Proposition 9.3][Papadimitriou94].

Adapted from the cycle construction in `lean-trominoes`, revision
`6d5b36c15cec6cb18d30137b7f1c7fb92ea24332`,
[PeriodicThreeSATThree.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThree.lean),
[PeriodicThreeSATThreeCorrectness.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreeCorrectness.lean), and
[PeriodicThreeSATThreeExactSize.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreeExactSize.lean).
No periodic semantics is used here.

## Main definitions

* `Cslib.Logic.PL.CNF.implicationCycle`: binary implications around a list.

## Main results

* `Cslib.Logic.PL.CNF.eval_implicationCycle`: a cycle holds exactly when all listed values agree.
* `Cslib.Logic.PL.CNF.length_implicationCycle`: one clause per listed variable.
* `Cslib.Logic.PL.CNF.count_vars_implicationCycle`: two occurrences per listed variable.

## References

* [C. H. Papadimitriou, *Computational Complexity*, Proposition 9.3][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*}

/-- An implication path from `current` through `rest`, closed back to `first`. -/
def implicationPath (first : V) : V → List V → CNF V
  | current, [] => [[(current, false), (first, true)]]
  | current, next :: rest =>
    [(current, false), (next, true)] :: implicationPath first next rest

/-- Binary implications around a list, including a tautological clause for a singleton. -/
def implicationCycle : List V → CNF V
  | [] => []
  | first :: rest => implicationPath first first rest

private theorem eval_implication (σ : V → Bool) (a b : V) :
    Clause.eval σ [(a, false), (b, true)] = true ↔ σ a ≤ σ b := by
  cases ha : σ a <;> cases hb : σ b <;> simp [ha, hb]

private theorem path_le_first (σ : V → Bool) (first current : V) (rest : List V)
    (h : (implicationPath first current rest).eval σ = true) : σ current ≤ σ first := by
  induction rest generalizing current with
  | nil => exact (eval_implication σ current first).1 (by simpa [implicationPath] using h)
  | cons next rest ih =>
    simp only [implicationPath, eval_cons, Bool.and_eq_true] at h
    exact le_trans ((eval_implication σ current next).1 h.1) (ih next h.2)

private theorem path_each_le_first (σ : V → Bool) (first current : V) (rest : List V)
    (h : (implicationPath first current rest).eval σ = true) :
    ∀ x ∈ current :: rest, σ x ≤ σ first := by
  induction rest generalizing current with
  | nil => simpa using path_le_first σ first current [] h
  | cons next rest ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact path_le_first σ first x (next :: rest) h
    · have ht := h
      simp only [implicationPath, eval_cons, Bool.and_eq_true] at ht
      exact ih next ht.2 x hx

private theorem root_le_path (σ : V → Bool) (root first current : V) (rest : List V)
    (hr : σ root ≤ σ current) (h : (implicationPath first current rest).eval σ = true) :
    ∀ x ∈ current :: rest, σ root ≤ σ x := by
  induction rest generalizing current with
  | nil => simpa using hr
  | cons next rest ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hr
    · have h : Clause.eval σ [(current, false), (next, true)] = true ∧
          (implicationPath first next rest).eval σ = true := by
          simpa only [implicationPath, eval_cons, Bool.and_eq_true] using h
      exact ih next (le_trans hr ((eval_implication σ current next).1 h.1)) h.2 x hx

/-- A cycle holds exactly when all variables listed in it have the same value. -/
theorem eval_implicationCycle (σ : V → Bool) (vs : List V) :
    (implicationCycle vs).eval σ = true ↔ ∀ x ∈ vs, ∀ y ∈ vs, σ x = σ y := by
  cases vs with
  | nil => simp [implicationCycle]
  | cons first rest =>
    constructor
    · intro h x hx y hy
      have he (z) (hz : z ∈ first :: rest) : σ z = σ first :=
        le_antisymm (path_each_le_first σ first first rest h z hz)
          (root_le_path σ first first first rest le_rfl h z hz)
      exact (he x hx).trans (he y hy).symm
    · intro h
      have hp (current : V) (tail : List V) (hc : current ∈ first :: rest)
          (ht : ∀ x ∈ tail, x ∈ first :: rest) :
          (implicationPath first current tail).eval σ = true := by
        induction tail generalizing current with
        | nil =>
          simpa only [implicationPath, eval_cons, eval_nil, Bool.and_true,
            eval_implication] using (le_of_eq (h current hc first List.mem_cons_self))
        | cons next tail ih =>
          simp only [implicationPath, eval_cons, Bool.and_eq_true, eval_implication]
          exact ⟨(le_of_eq (h current hc next (ht next List.mem_cons_self))),
            ih next (ht next List.mem_cons_self)
              (fun x hx => ht x (List.mem_cons_of_mem _ hx))⟩
      exact hp first rest List.mem_cons_self (fun _ hx => List.mem_cons_of_mem _ hx)

/-- There is one binary clause per element of the cycle list. -/
@[simp] theorem length_implicationCycle (vs : List V) :
    (implicationCycle vs).length = vs.length := by
  have hp (first current : V) (rest : List V) :
      (implicationPath first current rest).length = rest.length + 1 := by
    induction rest generalizing current with
    | nil => rfl
    | cons next rest ih => simp [implicationPath, ih]
  cases vs <;> simp [implicationCycle, hp]

/-- Every implication-cycle clause has exactly two literals. -/
theorem length_of_mem_implicationCycle (vs : List V) {c : Clause V}
    (hc : c ∈ implicationCycle vs) : c.length = 2 := by
  have hp (first current : V) (rest : List V) :
      ∀ c ∈ implicationPath first current rest, c.length = 2 := by
    induction rest generalizing current with
    | nil => simp [implicationPath]
    | cons next rest ih => simpa [implicationPath] using ih next
  cases vs with
  | nil => simp [implicationCycle] at hc
  | cons first rest => exact hp first first rest c hc

/-- A variable occurs twice per appearance in the cycle list, including repeated entries. -/
theorem count_vars_implicationCycle [DecidableEq V] (vs : List V) (v : V) :
    (implicationCycle vs).vars.count v = 2 * vs.count v := by
  have hp (first current : V) (rest : List V) :
      (implicationPath first current rest).vars.count v =
        (if current = v then 1 else 0) + (if first = v then 1 else 0) +
          2 * rest.count v := by
    induction rest generalizing current with
    | nil => simp [implicationPath, vars, List.count_cons, beq_iff_eq, Nat.add_comm]
    | cons next rest ih =>
      simp only [implicationPath, vars, List.flatten_cons, List.map_append,
        List.count_append, List.map_cons, List.map_nil] at ih ⊢
      rw [ih next]
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> simp_all <;> omega
  cases vs with
  | nil => simp [implicationCycle, vars]
  | cons first rest =>
    rw [implicationCycle, hp]
    simp only [List.count_cons, beq_iff_eq]
    split_ifs <;> omega

end Cslib.Logic.PL.CNF
