/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.PessimisticEstimator
public import Complexity.Foundations.Data.List.EraseDupsBy
public import Complexity.Logics.Propositional.CNF.ModelCount
public import Complexity.Logics.Propositional.CNF.UnsatVal
public import Complexity.Logics.Propositional.Resolution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Johnson's algorithm for MAX-SAT

Johnson's algorithm [Johnson1974] sets the variables of a CNF formula one at a time; this file
formalizes it in the form obtained by derandomizing a uniformly random assignment with the method
of conditional expectations [Williamson and Shmoys, Sections 5.1–5.2][WilliamsonShmoys2011]. A
clause with `j` distinct literals, none of them yet set, is falsified by a uniformly
random assignment with probability `2 ^ -j`, so the weight `Σ_c 2 ^ (L - |c|)`
(`Cslib.Logic.PL.CNF.johnsonWeight`) is `2 ^ L` times the expected number of falsified clauses
when no clause contains a complementary pair. Setting a variable `v` to `b` drops the clauses
satisfied by the literal `(v, b)` and deletes `(v, !b)` from the others; this is the restriction
`Cslib.Logic.PL.CNF.restrict` used for resolution. The weights after setting `v` to `true` and
to `false` sum to at most twice the current weight
(`Cslib.Logic.PL.CNF.johnsonWeight_restrict_add_le`), with equality when no clause contains both
`(v, true)` and `(v, false)`. Setting each variable to the value of smaller weight is therefore
the method of conditional expectations with the weight as a pessimistic estimator
(`Cslib.PessimisticEstimator.greedy_spec_of_add_le`).

The algorithm (`Cslib.Logic.PL.johnson`) first removes repeated literals from each clause, then
sets the variables in order of first occurrence. When no variable is left, every remaining clause
is empty and contributes `2 ^ L` to the weight, so `2 ^ L` times the number of clauses falsified by
the output is at most the initial weight
(`Cslib.Logic.PL.two_pow_mul_countUnsat_johnsonAssignment_le`). If every clause has at least `k`
distinct literals, the output falsifies at most `2 ^ -k` of the clauses
(`Cslib.Logic.PL.two_pow_mul_countUnsat_johnsonAssignment_le_length`). This gives the `7 / 8`
guarantee for clauses with three distinct variables
(`Cslib.Logic.PL.CNF.IsExactThreeDistinct.eight_mul_countUnsat_johnsonAssignment_le`), a
constructive form of `Cslib.Logic.PL.CNF.IsExactThreeDistinct.exists_countUnsat_le_div_eight`,
and the `1 / 2` guarantee for formulas without empty clauses
(`Cslib.Logic.PL.two_mul_countUnsat_johnsonAssignment_le`).

The polynomial running time is proved in `Complexity.Logics.Propositional.CNF.Johnson.PolyTime`.

## Main definitions

* `Cslib.Logic.PL.Clause.eraseDupLits`, `Cslib.Logic.PL.CNF.eraseDupLits`: remove repeated
  literals.
* `Cslib.Logic.PL.CNF.johnsonWeight`: Johnson's weight.
* `Cslib.Logic.PL.johnson`, `Cslib.Logic.PL.johnsonAssignment`: Johnson's algorithm, as the list
  of variables it sets to `true` and as an assignment.

## Main results

* `Cslib.Logic.PL.CNF.countUnsat_restrict`: setting a variable as the assignment does keeps the
  number of falsified clauses.
* `Cslib.Logic.PL.CNF.johnsonWeight_restrict_add_le`: the averaging step.
* `Cslib.Logic.PL.two_pow_mul_countUnsat_johnsonAssignment_le`: correctness against the initial
  weight.
* `Cslib.Logic.PL.countUnsat_johnsonAssignment_le_sum`: the output falsifies at most
  `Σ_c 2 ^ -|c|` clauses, counting distinct literals.
* `Cslib.Logic.PL.two_pow_mul_countUnsat_johnsonAssignment_le_length`: the `1 - 2 ^ -k`
  guarantee.
* `Cslib.Logic.PL.CNF.IsExactThreeDistinct.eight_mul_countUnsat_johnsonAssignment_le`: the
  `7 / 8` guarantee for MAX-E3SAT.
* `Cslib.Logic.PL.two_mul_countUnsat_johnsonAssignment_le`: the `1 / 2` guarantee for MAX-SAT.
* `Cslib.Logic.PL.one_sub_inv_two_pow_mul_le_johnsonAssignment`,
  `Cslib.Logic.PL.CNF.IsExactThreeDistinct.seven_div_eight_mul_le_johnsonAssignment`,
  `Cslib.Logic.PL.one_div_two_mul_le_johnsonAssignment`: the same guarantees as approximation
  ratios against `1 - unsatVal`.

## References

* [D. S. Johnson, *Approximation algorithms for combinatorial problems*][Johnson1974]
* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*,
  Sections 5.1–5.2][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Logic.PL

open PessimisticEstimator

variable {V : Type*} [DecidableEq V]

/-! ### Repeated literals -/

/-- Remove repeated literals from a clause, keeping first occurrences. -/
@[expose] def Clause.eraseDupLits (c : Clause V) : Clause V :=
  c.eraseDupsBy fun a b => decide (a = b)

/-- Remove repeated literals from every clause of a formula. -/
@[expose] def CNF.eraseDupLits (φ : CNF V) : CNF V :=
  φ.map Clause.eraseDupLits

/-- Removing repeated literals leaves no repeated literals. -/
theorem Clause.nodup_eraseDupLits (c : Clause V) : c.eraseDupLits.Nodup :=
  List.nodup_eraseDupsBy_eq c

/-- Removing repeated literals keeps every literal. -/
@[simp] theorem Clause.mem_eraseDupLits {c : Clause V} {l : Literal V} :
    l ∈ c.eraseDupLits ↔ l ∈ c :=
  List.mem_eraseDupsBy_eq

/-- Removing repeated literals does not lengthen a clause. -/
theorem Clause.length_eraseDupLits_le (c : Clause V) : c.eraseDupLits.length ≤ c.length :=
  (List.eraseDupsBy_sublist c).length_le

/-- After removing repeated literals, the length of a clause is its number of distinct
literals. -/
theorem Clause.length_eraseDupLits (c : Clause V) : c.eraseDupLits.length = c.toFinset.card := by
  rw [← List.toFinset_card_of_nodup c.nodup_eraseDupLits]
  congr 1
  ext l
  simp

/-- Removing repeated literals does not change the value of a clause. -/
@[simp] theorem Clause.eval_eraseDupLits (σ : V → Bool) (c : Clause V) :
    c.eraseDupLits.eval σ = c.eval σ := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  simp only [Clause.mem_eraseDupLits]

/-- Removing repeated literals does not change the number of falsified clauses. -/
@[simp] theorem CNF.countUnsat_eraseDupLits (σ : V → Bool) (φ : CNF V) :
    φ.eraseDupLits.countUnsat σ = φ.countUnsat σ := by
  simp [CNF.countUnsat, CNF.eraseDupLits, List.countP_map, Function.comp_def]

/-! ### Setting a variable -/

/-- Setting a variable with `CNF.restrict`, one clause at a time. -/
theorem CNF.restrict_cons (v : V) (b : Bool) (c : Clause V) (ψ : CNF V) :
    CNF.restrict (c :: ψ) v b = if (v, b) ∈ c then ψ.restrict v b
      else c.filter (· ≠ (v, !b)) :: ψ.restrict v b := by
  by_cases h : (v, b) ∈ c <;> simp [CNF.restrict, h]

/-- Under an assignment that sets `v` to `b`, setting `v` to `b` in the formula does not change
the number of falsified clauses. -/
theorem CNF.countUnsat_restrict {σ : V → Bool} {v : V} {b : Bool} (hσ : σ v = b) (ψ : CNF V) :
    (ψ.restrict v b).countUnsat σ = ψ.countUnsat σ := by
  induction ψ with
  | nil => rfl
  | cons c ψ ih =>
    rw [CNF.restrict_cons]
    split
    · rename_i h
      have hc : c.eval σ = true :=
        (Clause.eval_eq_true_iff σ c).2 ⟨_, h, by simp [hσ]⟩
      rw [ih]
      exact (List.countP_cons_of_neg (by simp [hc])).symm
    · have hc : Clause.eval σ (c.filter (· ≠ (v, !b))) = c.eval σ := by
        rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
        constructor
        · rintro ⟨l, hl, hle⟩
          exact ⟨l, (List.mem_filter.1 hl).1, hle⟩
        · rintro ⟨l, hl, hle⟩
          refine ⟨l, List.mem_filter.2 ⟨hl, ?_⟩, hle⟩
          rw [decide_eq_true_iff]
          rintro rfl
          simp [hσ] at hle
      simp only [CNF.countUnsat, List.countP_cons, hc] at ih ⊢
      rw [ih]

/-! ### Johnson's weight -/

/-- Johnson's weight `Σ_c 2 ^ (L - |c|)`. For clauses of length at most `L` without repeated
literals and without complementary pairs, this is `2 ^ L` times the expected number of clauses
falsified by a uniformly random assignment. -/
@[expose] def CNF.johnsonWeight (L : ℕ) (ψ : CNF V) : ℕ :=
  (ψ.map fun c => 2 ^ (L - c.length)).sum

omit [DecidableEq V] in
/-- The empty formula has weight `0`. -/
@[simp] theorem CNF.johnsonWeight_nil (L : ℕ) : CNF.johnsonWeight L ([] : CNF V) = 0 := rfl

omit [DecidableEq V] in
/-- The weight of a formula, one clause at a time. -/
@[simp] theorem CNF.johnsonWeight_cons (L : ℕ) (c : Clause V) (ψ : CNF V) :
    CNF.johnsonWeight L (c :: ψ) = 2 ^ (L - c.length) + CNF.johnsonWeight L ψ := rfl

private theorem length_filter_ne_add_one {c : Clause V} (hc : c.Nodup) {a : Literal V}
    (ha : a ∈ c) : (c.filter (· ≠ a)).length + 1 = c.length := by
  induction c with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 hc
    by_cases hxa : x = a
    · subst hxa
      rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2 fun l hl => by
        simpa using fun h : l = x => hx (h ▸ hl), List.length_cons]
    · rw [List.filter_cons_of_pos (by simpa using hxa), List.length_cons, List.length_cons,
        ih hxs ((List.mem_cons.1 ha).resolve_left (Ne.symm hxa))]

private theorem filter_ne_eq_self {c : Clause V} {a : Literal V} (ha : a ∉ c) :
    c.filter (· ≠ a) = c :=
  List.filter_eq_self.2 fun l hl => by simpa using fun h : l = a => ha (h ▸ hl)

/-- **Averaging**: on clauses without repeated literals and of length at most `L`, setting a
variable to `true` and to `false` gives weights summing to at most twice the weight. -/
theorem CNF.johnsonWeight_restrict_add_le {L : ℕ} (v : V) {ψ : CNF V}
    (hψ : ∀ c ∈ ψ, c.Nodup ∧ c.length ≤ L) :
    (ψ.restrict v true).johnsonWeight L + (ψ.restrict v false).johnsonWeight L ≤
      ψ.johnsonWeight L + ψ.johnsonWeight L := by
  induction ψ with
  | nil => simp [CNF.restrict]
  | cons c ψ ih =>
    obtain ⟨hnd, hlen⟩ := hψ c List.mem_cons_self
    have ih := ih fun c hc => hψ c (List.mem_cons_of_mem _ hc)
    rw [CNF.restrict_cons, CNF.restrict_cons, CNF.johnsonWeight_cons]
    -- Deleting one literal from a nonempty clause doubles its term.
    have hdouble {a : Literal V} (ha : a ∈ c) :
        2 ^ (L - (c.filter (· ≠ a)).length) = 2 ^ (L - c.length) + 2 ^ (L - c.length) := by
      have h1 := length_filter_ne_add_one hnd ha
      rw [show L - (c.filter (· ≠ a)).length = L - c.length + 1 by omega,
        pow_succ]
      ring
    by_cases hT : (v, true) ∈ c <;> by_cases hF : (v, false) ∈ c <;>
      simp only [hT, hF, ite_true, ite_false, CNF.johnsonWeight_cons, Bool.not_true,
        Bool.not_false]
    · generalize 2 ^ (L - c.length) = p
      omega
    · rw [hdouble hT]
      generalize 2 ^ (L - c.length) = p
      omega
    · rw [hdouble hF]
      generalize 2 ^ (L - c.length) = p
      omega
    · rw [filter_ne_eq_self hT, filter_ne_eq_self hF]
      generalize 2 ^ (L - c.length) = p
      omega

omit [DecidableEq V] in
/-- A formula without variables has weight `2 ^ L` per clause, all of them falsified. -/
theorem CNF.johnsonWeight_of_vars_eq_nil {L : ℕ} {ψ : CNF V} (hψ : ∀ v, v ∉ ψ.vars)
    (σ : V → Bool) : ψ.johnsonWeight L = 2 ^ L * ψ.countUnsat σ := by
  induction ψ with
  | nil => rfl
  | cons c ψ ih =>
    have hc : c = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl =>
      hψ l.1 (CNF.mem_vars.2 ⟨c, List.mem_cons_self, l.2, hl⟩)
    have ih := ih fun v hv => hψ v (by
      obtain ⟨c', hc', b, hb⟩ := CNF.mem_vars.1 hv
      exact CNF.mem_vars.2 ⟨c', List.mem_cons_of_mem _ hc', b, hb⟩)
    subst hc
    have h1 : CNF.countUnsat σ ([] :: ψ) = CNF.countUnsat σ ψ + 1 :=
      List.countP_cons_of_pos (by simp)
    rw [CNF.johnsonWeight_cons, h1, ih, List.length_nil, Nat.sub_zero]
    ring

/-! ### Johnson's algorithm -/

/-- Fix `v` to `b`, recording `v` among the variables set to `true` when `b` is `true`. -/
@[expose] def johnsonBranch (v : V) (b : Bool) (s : CNF V × List V) : CNF V × List V :=
  (s.1.restrict v b, if b then v :: s.2 else s.2)

/-- The final state of Johnson's algorithm: the variables of `φ` are fixed in order of first
occurrence, each to the value giving the smaller weight. -/
@[expose] def johnsonState (φ : CNF V) : CNF V × List V :=
  greedy johnsonBranch (fun s => s.1.johnsonWeight φ.vars.length) φ.distinctVars
    (φ.eraseDupLits, [])

/-- **Johnson's algorithm**: the variables set to `true`. -/
@[expose] def johnson (φ : CNF V) : List V := (johnsonState φ).2

/-- The assignment computed by Johnson's algorithm. -/
@[expose] def johnsonAssignment (φ : CNF V) : V → Bool := fun v => decide (v ∈ johnson φ)

omit [DecidableEq V] in
private theorem length_le_length_vars {φ : CNF V} {c : Clause V} (hc : c ∈ φ) :
    c.length ≤ φ.vars.length := by
  rw [CNF.length_vars]
  exact List.le_sum_of_mem (List.mem_map_of_mem hc)

/-- **Correctness of Johnson's algorithm**: with `L` the number of variable occurrences, `2 ^ L`
times the number of clauses that the output falsifies is at most the initial weight. -/
theorem two_pow_mul_countUnsat_johnsonAssignment_le (φ : CNF V) :
    2 ^ φ.vars.length * φ.countUnsat (johnsonAssignment φ) ≤
      φ.eraseDupLits.johnsonWeight φ.vars.length := by
  set L := φ.vars.length
  let Inv : List V → CNF V × List V → Prop := fun rs s =>
    rs.Nodup ∧ (∀ c ∈ s.1, c.Nodup ∧ c.length ≤ L) ∧ (∀ v ∈ s.1.vars, v ∈ rs) ∧
      (∀ v ∈ s.2, v ∉ rs) ∧
      ∀ σ : V → Bool, (∀ v, v ∉ rs → σ v = decide (v ∈ s.2)) → s.1.countUnsat σ = φ.countUnsat σ
  have hbranch : ∀ r rs s b, Inv (r :: rs) s → Inv rs (johnsonBranch r b s) := by
    rintro r rs ⟨ψ, T⟩ b ⟨hnd, hcl, hvars, hT, hcount⟩
    obtain ⟨hr, hnd⟩ := List.nodup_cons.1 hnd
    refine ⟨hnd, fun c hc => ?_, fun w hw => ?_, fun w hw => ?_, fun σ hσ => ?_⟩
    · obtain ⟨c₀, hc₀, -, rfl⟩ := CNF.mem_restrict.1 hc
      obtain ⟨hnd, hlen⟩ := hcl c₀ hc₀
      exact ⟨hnd.filter _, (List.length_filter_le _ _).trans hlen⟩
    · obtain ⟨c, hc, b', hl⟩ := CNF.mem_vars.1 hw
      have hne := CNF.fst_ne_of_mem_restrict hc hl
      obtain ⟨c₀, hc₀, -, rfl⟩ := CNF.mem_restrict.1 hc
      exact (List.mem_cons.1 (hvars w (CNF.mem_vars.2 ⟨c₀, hc₀, b', (List.mem_filter.1 hl).1⟩)))
        |>.resolve_left hne
    · have hw : w = r ∨ w ∈ T := by
        cases b
        · exact .inr hw
        · exact List.mem_cons.1 hw
      rcases hw with rfl | hw
      · exact hr
      · exact fun h => hT w hw (List.mem_cons_of_mem _ h)
    · have hrσ : σ r = b := by
        rw [hσ r hr]
        cases b
        · simpa [johnsonBranch] using fun h => hT r h List.mem_cons_self
        · simp [johnsonBranch]
      have hσ' : ∀ v, v ∉ r :: rs → σ v = decide (v ∈ T) := by
        intro v hv
        rw [List.mem_cons, not_or] at hv
        rw [hσ v hv.2]
        cases b <;> simp [johnsonBranch, hv.1]
      rw [johnsonBranch, CNF.countUnsat_restrict hrσ]
      exact hcount σ hσ'
  have havg : ∀ r rs s, Inv (r :: rs) s →
      (johnsonBranch r true s).1.johnsonWeight L + (johnsonBranch r false s).1.johnsonWeight L ≤
        s.1.johnsonWeight L + s.1.johnsonWeight L :=
    fun r _ s hs => CNF.johnsonWeight_restrict_add_le r hs.2.1
  have hinit : Inv φ.distinctVars (φ.eraseDupLits, []) := by
    refine ⟨φ.nodup_distinctVars, fun c hc => ?_, fun v hv => ?_, by simp, fun σ _ => by simp⟩
    · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      exact ⟨c₀.nodup_eraseDupLits, c₀.length_eraseDupLits_le.trans (length_le_length_vars hc₀)⟩
    · obtain ⟨c', hc', b, hb⟩ := CNF.mem_vars.1 hv
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      exact CNF.mem_distinctVars.2 (CNF.mem_vars.2 ⟨c, hc, b, Clause.mem_eraseDupLits.1 hb⟩)
  obtain ⟨⟨-, -, hvars, -, hcount⟩, hle⟩ :=
    greedy_spec_of_add_le johnsonBranch (fun s => s.1.johnsonWeight L) Inv hbranch havg _ _ hinit
  have hcount := hcount (johnsonAssignment φ) fun v _ => rfl
  rw [CNF.johnsonWeight_of_vars_eq_nil (fun v hv => by simpa using hvars v hv)
    (johnsonAssignment φ), hcount] at hle
  exact hle

/-! ### Corollaries -/

/-- After removing repeated literals, the weight counts the distinct literals of each clause. -/
theorem CNF.johnsonWeight_eraseDupLits (L : ℕ) (φ : CNF V) :
    φ.eraseDupLits.johnsonWeight L = (φ.map fun c => 2 ^ (L - c.toFinset.card)).sum := by
  simp [CNF.johnsonWeight, CNF.eraseDupLits, Function.comp_def, Clause.length_eraseDupLits]

/-- **Johnson's bound**: the output of Johnson's algorithm falsifies at most `Σ_c 2 ^ -|c|`
clauses, where `|c|` is the number of distinct literals of `c`. This is the expected number of
clauses falsified by a uniformly random assignment when no clause contains a complementary pair,
and an upper bound for it otherwise. -/
theorem countUnsat_johnsonAssignment_le_sum (φ : CNF V) :
    (φ.countUnsat (johnsonAssignment φ) : ℝ) ≤
      (φ.map fun c => (2 : ℝ)⁻¹ ^ c.toFinset.card).sum := by
  set L := φ.vars.length
  have h : ((2 ^ L * φ.countUnsat (johnsonAssignment φ) : ℕ) : ℝ) ≤
      (((φ.map fun c => 2 ^ (L - c.toFinset.card)).sum : ℕ) : ℝ) := by
    exact_mod_cast CNF.johnsonWeight_eraseDupLits L φ ▸
      two_pow_mul_countUnsat_johnsonAssignment_le φ
  have hterm : ∀ c ∈ φ, ((2 ^ (L - c.toFinset.card) : ℕ) : ℝ) =
      2 ^ L * (2 : ℝ)⁻¹ ^ c.toFinset.card := by
    intro c hc
    have hle : c.toFinset.card ≤ L :=
      (Clause.length_eraseDupLits c ▸ c.length_eraseDupLits_le).trans (length_le_length_vars hc)
    rw [Nat.cast_pow, Nat.cast_ofNat, inv_pow, ← div_eq_mul_inv,
      eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel hle]
  rw [Nat.cast_list_sum, List.map_map, List.map_congr_left (fun c hc => by
    simpa only [Function.comp_apply] using hterm c hc), List.sum_map_mul_left,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  exact le_of_mul_le_mul_left h (by positivity)

/-- **Johnson's bound**: if every clause has at least `k` distinct literals, Johnson's algorithm
falsifies at most `2 ^ -k` of the clauses. -/
theorem two_pow_mul_countUnsat_johnsonAssignment_le_length {k : ℕ} {φ : CNF V}
    (hk : ∀ c ∈ φ, k ≤ c.toFinset.card) :
    2 ^ k * φ.countUnsat (johnsonAssignment φ) ≤ φ.length := by
  by_cases hne : φ = []
  · simp [hne, CNF.countUnsat]
  set L := φ.vars.length
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil φ hne
  have hkL : k ≤ L := (hk c hc).trans
    ((Clause.length_eraseDupLits c ▸ c.length_eraseDupLits_le).trans (length_le_length_vars hc))
  have h : 2 ^ L * φ.countUnsat (johnsonAssignment φ) ≤
      (φ.map fun c => 2 ^ (L - c.toFinset.card)).sum := by
    simpa only [CNF.johnsonWeight_eraseDupLits] using two_pow_mul_countUnsat_johnsonAssignment_le φ
  have hw : (φ.map fun c => 2 ^ (L - c.toFinset.card)).sum ≤ φ.length * 2 ^ (L - k) := by
    rw [← smul_eq_mul, ← List.sum_replicate, ← List.map_const']
    exact List.sum_le_sum fun c hc => Nat.pow_le_pow_right (by norm_num) (by
      have := hk c hc
      omega)
  have hsplit : 2 ^ L = 2 ^ k * 2 ^ (L - k) := by rw [← pow_add, Nat.add_sub_cancel' hkL]
  rw [hsplit, mul_right_comm] at h
  exact Nat.le_of_mul_le_mul_right (h.trans hw) (by positivity)

/-- **The `7 / 8` guarantee**: on an exact 3-CNF formula with three distinct variables per
clause, Johnson's algorithm falsifies at most `1 / 8` of the clauses. -/
theorem CNF.IsExactThreeDistinct.eight_mul_countUnsat_johnsonAssignment_le {φ : CNF V}
    (hφ : φ.IsExactThreeDistinct) : 8 * φ.countUnsat (johnsonAssignment φ) ≤ φ.length :=
  two_pow_mul_countUnsat_johnsonAssignment_le_length (k := 3) fun _ hc =>
    (hφ.card_toFinset_eq hc).ge

/-- **The `1 / 2` guarantee**: on a formula without empty clauses, Johnson's algorithm falsifies at
most half of the clauses. -/
theorem two_mul_countUnsat_johnsonAssignment_le {φ : CNF V} (hφ : ∀ c ∈ φ, c ≠ []) :
    2 * φ.countUnsat (johnsonAssignment φ) ≤ φ.length :=
  two_pow_mul_countUnsat_johnsonAssignment_le_length (k := 1) fun c hc =>
    Finset.one_le_card.2 ⟨_, List.mem_toFinset.2 (List.head_mem (hφ c hc))⟩


/-! ### Approximation ratios -/

/-- **Approximation ratio**: if every clause has at least `k` distinct literals, the proportion of
the clauses that Johnson's algorithm satisfies is at least `1 - 2 ^ -k` times the largest
proportion that an assignment satisfies, `1 - φ.unsatVal`. -/
theorem one_sub_inv_two_pow_mul_le_johnsonAssignment {k : ℕ} {φ : CNF V}
    (hk : ∀ c ∈ φ, k ≤ c.toFinset.card) :
    (1 - (2 : ℝ)⁻¹ ^ k) * (1 - φ.unsatVal) ≤
      1 - (φ.countUnsat (johnsonAssignment φ) : ℝ) / φ.length :=
  CNF.one_sub_inv_two_pow_mul_le_of_two_pow_mul_countUnsat_le
    (two_pow_mul_countUnsat_johnsonAssignment_le_length hk)

/-- **The `7 / 8` approximation ratio** for MAX-E3SAT with three distinct variables per clause. -/
theorem CNF.IsExactThreeDistinct.seven_div_eight_mul_le_johnsonAssignment {φ : CNF V}
    (hφ : φ.IsExactThreeDistinct) :
    7 / 8 * (1 - φ.unsatVal) ≤ 1 - (φ.countUnsat (johnsonAssignment φ) : ℝ) / φ.length := by
  have h := one_sub_inv_two_pow_mul_le_johnsonAssignment (k := 3) fun _ hc =>
    (hφ.card_toFinset_eq hc).ge
  rwa [show (1 : ℝ) - 2⁻¹ ^ 3 = 7 / 8 by norm_num] at h

/-- **The `1 / 2` approximation ratio** for MAX-SAT on formulas without empty clauses. -/
theorem one_div_two_mul_le_johnsonAssignment {φ : CNF V} (hφ : ∀ c ∈ φ, c ≠ []) :
    1 / 2 * (1 - φ.unsatVal) ≤ 1 - (φ.countUnsat (johnsonAssignment φ) : ℝ) / φ.length := by
  have h := one_sub_inv_two_pow_mul_le_johnsonAssignment (k := 1) fun c hc =>
    Finset.one_le_card.2 ⟨_, List.mem_toFinset.2 (List.head_mem (hφ c hc))⟩
  rwa [show (1 : ℝ) - 2⁻¹ ^ 1 = 1 / 2 by norm_num] at h

end Cslib.Logic.PL
