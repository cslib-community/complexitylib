/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ModelCount
public import Complexity.Logics.Propositional.DNF
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting satisfying assignments of formulas in disjunctive normal form

`DNF.modelCount φ` is the number of satisfying assignments of a formula `φ` in disjunctive normal
form: the assignments of the variables occurring in `φ` that satisfy it. Formulas in disjunctive
and conjunctive normal form share their representation as lists of lists of literals, so the
variables `CNF.vars φ`, their distinct listing `CNF.distinctVars φ` and their number
`CNF.numVars φ` apply to both. As a function of the formula this is the counting problem `#DNF`,
which is `#P`-complete although satisfiability of formulas in disjunctive normal form is easy
[Valiant][Valiant1979].

The satisfying assignments of a single term `t` form a subcube. A term is consistent
(`Term.consistent`) when no variable occurs in it with both signs; consistent terms are exactly
the satisfiable ones (`Term.consistent_iff_exists_eval`). Overriding an assignment `σ` by the
literals of `t` (`Term.force t σ`) gives an assignment satisfying `t` whenever `t` is consistent
(`Term.eval_force`). Reading the variables of a nodup list `vs` from a word of `|vs|` bits
(`wordAssignment`), forcing the literals of `t` is `2 ^ t.width`-to-one onto the satisfying
assignments of `t`, where `t.width` is the number of distinct variables of `t`
(`card_filter_force`). In particular a consistent term has `2 ^ (|vs| - t.width)` satisfying
assignments of the variables `vs` (`two_pow_sub_width_le_modelCount`).

Counting the satisfying assignments of `φ` by the first term that they satisfy partitions them
(`DNF.card_filter_eval_eq_sum`). These are the combinatorial facts behind the Karp–Luby–Madras
estimator [Karp, Luby and Madras][KarpLubyMadras1989], [Mitzenmacher and Upfal, Section
11.2][MitzenmacherUpfal2017].

## Main definitions

* `Cslib.Logic.PL.Term.consistent`, `Cslib.Logic.PL.Term.force`, `Cslib.Logic.PL.Term.width`:
  consistency, forcing the literals of a term, and its number of distinct variables.
* `Cslib.Logic.PL.DNF.modelCount`: the number of satisfying assignments.
* `Cslib.Logic.PL.wordAssignment`: the assignment reading the variables of a list from a word.

## Main results

* `Cslib.Logic.PL.Term.eval_force`, `Cslib.Logic.PL.Term.force_eq_of_eval`,
  `Cslib.Logic.PL.Term.consistent_iff_exists_eval`: forcing and consistency.
* `Cslib.Logic.PL.DNF.eval_congr`: a formula only depends on its variables.
* `Cslib.Logic.PL.DNF.modelCount_eq_card_filter`: the count over words of `CNF.numVars φ` bits.
* `Cslib.Logic.PL.DNF.card_filter_eval_eq_sum`: the partition by the first satisfied term.
* `Cslib.Logic.PL.card_filter_force`: forcing a term is `2 ^ t.width`-to-one.
* `Cslib.Logic.PL.two_pow_sub_width_le_modelCount`: a consistent term of `φ` contributes
  `2 ^ (CNF.numVars φ - t.width)` satisfying assignments.

## References

* [R. M. Karp, M. Luby, N. Madras, *Monte-Carlo approximation algorithms for enumeration
  problems*][KarpLubyMadras1989]
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*, Section 11.2][MitzenmacherUpfal2017]
* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-! ### Terms -/

/-- A term is **consistent** when no variable occurs in it with both signs. -/
def Term.consistent (t : Term V) : Bool :=
  t.all fun l => t.all fun l' => !(l.1 == l'.1) || l.2 == l'.2

/-- Override the assignment `σ` by the literals of `t`: a variable occurring in `t` is `true`
exactly when it occurs positively. -/
def Term.force (t : Term V) (σ : V → Bool) (v : V) : Bool :=
  if t.any (fun l => l.1 == v) then t.any (fun l => l.1 == v && l.2) else σ v

/-- The number of distinct variables of a term. -/
def Term.width (t : Term V) : ℕ := (t.map Prod.fst).toFinset.card

/-- Forcing a term does not change variables outside it. -/
theorem Term.force_of_forall_ne {t : Term V} {σ : V → Bool} {v : V} (hv : ∀ l ∈ t, l.1 ≠ v) :
    t.force σ v = σ v := by
  have hany : t.any (fun l => l.1 == v) = false := by
    simpa only [List.any_eq_false, beq_iff_eq] using hv
  simp only [Term.force, hany, Bool.false_eq_true, ite_false]

/-- Forcing a consistent term gives each of its variables the sign of its literals. -/
theorem Term.force_of_mem {t : Term V} {σ : V → Bool} {l : Literal V} (hl : l ∈ t)
    (hc : t.consistent = true) : t.force σ l.1 = l.2 := by
  have hany : t.any (fun l' => l'.1 == l.1) = true :=
    List.any_eq_true.2 ⟨l, hl, beq_self_eq_true _⟩
  simp only [Term.force, hany, ite_true]
  have hsign : ∀ l' ∈ t, l'.1 = l.1 → l'.2 = l.2 := by
    intro l' hl' heq
    have := (List.all_eq_true.1 (List.all_eq_true.1 hc l' hl')) l hl
    simpa only [heq, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] using this
  cases h2 : l.2
  · rw [List.any_eq_false]
    intro l' hl'
    by_cases heq : l'.1 = l.1
    · simp [hsign l' hl' heq, h2]
    · simp [heq]
  · exact List.any_eq_true.2 ⟨l, hl, by simp [h2]⟩

/-- Forcing a consistent term satisfies it. -/
theorem Term.eval_force {t : Term V} (hc : t.consistent = true) (σ : V → Bool) :
    t.eval (t.force σ) = true :=
  (Term.eval_eq_true_iff _ _).2 fun _ hl => Term.force_of_mem hl hc

/-- Forcing a term on an assignment that already satisfies it changes nothing. -/
theorem Term.force_eq_of_eval {t : Term V} {σ : V → Bool} (h : t.eval σ = true) :
    t.force σ = σ := by
  funext v
  have hlit := (Term.eval_eq_true_iff _ _).1 h
  by_cases hv : t.any (fun l => l.1 == v) = true
  · simp only [Term.force, hv, ite_true]
    obtain ⟨l, hl, hlv⟩ := List.any_eq_true.1 hv
    rw [beq_iff_eq] at hlv
    cases hσ : σ v
    · rw [List.any_eq_false]
      intro l' hl'
      by_cases heq : l'.1 = v
      · have hl'σ := hlit l' hl'
        rw [heq, hσ] at hl'σ
        simp [heq, ← hl'σ]
      · simp [heq]
    · exact List.any_eq_true.2 ⟨l, hl, by simp [hlv, ← hlit l hl, hσ]⟩
  · simp only [Term.force, hv, Bool.false_eq_true, ite_false]

/-- A satisfiable term is consistent. -/
theorem Term.consistent_of_eval {t : Term V} {σ : V → Bool} (h : t.eval σ = true) :
    t.consistent = true := by
  have hlit := (Term.eval_eq_true_iff _ _).1 h
  simp only [Term.consistent, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, beq_iff_eq]
  intro l hl l' hl'
  by_cases heq : l.1 = l'.1
  · exact Or.inr (by rw [← hlit l hl, ← hlit l' hl', heq])
  · exact Or.inl heq

/-- A term is consistent exactly when it is satisfiable. -/
theorem Term.consistent_iff_exists_eval {t : Term V} :
    t.consistent = true ↔ ∃ σ : V → Bool, t.eval σ = true :=
  ⟨fun hc => ⟨t.force fun _ => false, Term.eval_force hc _⟩,
    fun ⟨_, hσ⟩ => Term.consistent_of_eval hσ⟩

/-! ### Formulas -/

omit [DecidableEq V] in
/-- A formula in disjunctive normal form only depends on the variables occurring in it. -/
theorem DNF.eval_congr {σ τ : V → Bool} {φ : DNF V} (h : ∀ v ∈ CNF.vars φ, σ v = τ v) :
    DNF.eval σ φ = DNF.eval τ φ := by
  have hvars : CNF.vars (DNF.negate φ) = CNF.vars φ := by
    simp only [DNF.negate, CNF.vars, Term.negate, List.map_flatten, List.map_map,
      Function.comp_def]
  have hneg : CNF.eval σ (DNF.negate φ) = CNF.eval τ (DNF.negate φ) :=
    CNF.eval_congr fun v hv => h v (hvars ▸ hv)
  rw [DNF.eval_negate, DNF.eval_negate] at hneg
  exact Bool.not_inj hneg

/-- **The number of satisfying assignments** of a formula in disjunctive normal form: the
assignments of the variables occurring in `φ` that satisfy it. -/
def DNF.modelCount (φ : DNF V) : ℕ :=
  (Finset.univ.filter fun τ : (CNF.vars φ).toFinset → Bool =>
    DNF.eval (CNF.extendAssignment φ τ) φ = true).card

/-- The assignment reading the variable at position `i` of `vs` from bit `i` of the word `w`,
and `false` past the end of `w`. -/
def wordAssignment (vs : List V) (w : List Bool) (v : V) : Bool := w.getD (vs.idxOf v) false

/-- The assignment read from a word of `n` bits, as a function on positions. -/
private def indexAssignment (vs : List V) {n : ℕ} (x : Fin n → Bool) (v : V) : Bool :=
  if h : vs.idxOf v < n then x ⟨vs.idxOf v, h⟩ else false

private theorem wordAssignment_ofFn (vs : List V) {n : ℕ} (x : Fin n → Bool) :
    wordAssignment vs (List.ofFn x) = indexAssignment vs x := by
  funext v
  simp only [wordAssignment, indexAssignment, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

/-- **Counting over words**: the satisfying assignments of `φ` correspond to the words of
`CNF.numVars φ` bits whose assignment of the distinct variables of `φ` satisfies `φ`. -/
theorem DNF.modelCount_eq_card_filter (φ : DNF V) :
    DNF.modelCount φ = (Finset.univ.filter fun x : Fin (CNF.numVars φ) → Bool =>
      DNF.eval (wordAssignment (CNF.distinctVars φ) (List.ofFn x)) φ = true).card := by
  simp only [wordAssignment_ofFn]
  set vs := CNF.distinctVars φ
  have hnd : vs.Nodup := CNF.nodup_distinctVars φ
  have hlen : vs.length = CNF.numVars φ := CNF.length_distinctVars φ
  let e : Fin (CNF.numVars φ) ≃ (CNF.vars φ).toFinset :=
    { toFun := fun i => ⟨vs[i.1]'(by rw [hlen]; exact i.2), by
        rw [← CNF.distinctVars_toFinset, List.mem_toFinset]; exact List.getElem_mem _⟩
      invFun := fun v => ⟨vs.idxOf v.1, by
        rw [← hlen]; apply List.idxOf_lt_length_of_mem
        rw [← List.mem_toFinset, CNF.distinctVars_toFinset]; exact v.2⟩
      left_inv := fun i => by
        ext; exact hnd.idxOf_getElem _ _
      right_inv := fun v => by
        ext; exact List.getElem_idxOf _ }
  apply Finset.card_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
  intro τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply Eq.congr_left
  apply DNF.eval_congr
  intro v hv
  have hlt : vs.idxOf v < CNF.numVars φ := by
    rw [← hlen]; apply List.idxOf_lt_length_of_mem
    rw [← List.mem_toFinset, CNF.distinctVars_toFinset]; exact List.mem_toFinset.2 hv
  rw [CNF.extendAssignment_of_mem _ hv]
  simp only [indexAssignment, hlt, dite_true, Equiv.arrowCongr_apply, Equiv.symm_symm,
    Equiv.coe_refl, Function.comp_apply, id]
  congr 1
  ext
  exact (List.getElem_idxOf _).symm

omit [DecidableEq V] in
/-- **Partition by the first satisfied term.** Every satisfying assignment satisfies exactly one
term `φ[i]` that no earlier term `φ[j]`, `j < i`, satisfies. -/
theorem DNF.card_filter_eval_eq_sum {α : Type*} (σ : α → V → Bool) (φ : DNF V)
    (S : Finset α) :
    (S.filter fun a => DNF.eval (σ a) φ = true).card =
      ∑ i ∈ Finset.range φ.length, (S.filter fun a => (φ.getD i []).eval (σ a) = true ∧
        DNF.eval (σ a) (φ.take i) = false).card := by
  induction φ generalizing S with
  | nil => simp
  | cons t φ ih =>
    classical
    have hsplit : (S.filter fun a => DNF.eval (σ a) (t :: φ) = true) =
        S.filter (fun a => Term.eval (σ a) t = true) ∪
          (S.filter fun a => Term.eval (σ a) t = false).filter
            (fun a => DNF.eval (σ a) φ = true) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_union, DNF.eval_cons, Bool.or_eq_true]
      cases Term.eval (σ a) t <;>
        simp
    have hdisj : Disjoint (S.filter (fun a => Term.eval (σ a) t = true))
        ((S.filter fun a => Term.eval (σ a) t = false).filter
          (fun a => DNF.eval (σ a) φ = true)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_filter] at ha hb
      rw [ha.2] at hb
      exact Bool.noConfusion hb.1.2
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.take_zero, DNF.eval_nil, and_true, List.getD_cons_succ,
      List.take_succ_cons, DNF.eval_cons, Bool.or_eq_false_iff, Finset.filter_filter]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext a
    simp only [Finset.mem_filter]
    tauto

/-! ### Forcing a term on a word -/

/-- Fixing the coordinates in `J` to `c` is `2 ^ |J|`-to-one onto the functions agreeing with
`c` on `J`. -/
private theorem card_filter_override {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Finset ι)
    (c : ι → Bool) (P : (ι → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : ι → Bool => P (fun i => if i ∈ J then c i else x i)).card =
      2 ^ J.card *
        (Finset.univ.filter fun y : ι → Bool => (∀ i ∈ J, y i = c i) ∧ P y).card := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ J) (fun _ => Bool)
  simp only [Finset.card_filter]
  rw [← Fintype.sum_equiv e.symm _ _ (fun _ => rfl),
    ← Fintype.sum_equiv e.symm _ _ (fun _ => rfl), Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hglue (a : {i // i ∈ J} → Bool) (b : {i // i ∉ J} → Bool) :
      (fun i => if i ∈ J then c i else e.symm (a, b) i) = e.symm (fun i => c i, b) := by
    funext i
    by_cases hi : i ∈ J <;>
      simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, hi, dite_true, dite_false, ite_true,
        ite_false]
  simp only [hglue, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, nsmul_eq_mul, Nat.cast_id]
  congr 1
  symm
  rw [Finset.sum_eq_single (fun i : {i // i ∈ J} => c i.1)]
  · apply Finset.sum_congr rfl
    intro b _
    have hc : ∀ i ∈ J, e.symm ((fun i => c i), b) i = c i := by
      intro i hi
      simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, hi, dite_true]
    exact if_congr ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩ rfl rfl
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    have hne : ¬ ∀ i ∈ J, e.symm (a, b) i = c i := by
      intro h
      apply ha
      funext i
      have hi := h i.1 i.2
      simpa only [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2, dite_true] using hi
    exact ite_eq_right_iff.2 fun h => absurd h.1 hne
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Forcing a term is `2 ^ t.width`-to-one.** Reading the variables of a nodup list `vs` from
words of `|vs|` bits, the words on which forcing `t` gives an assignment satisfying `t` and `Q`
are `2 ^ t.width` times as many as the words whose assignment satisfies `t` and `Q`. -/
theorem card_filter_force {vs : List V} (hnd : vs.Nodup) {t : Term V}
    (ht : ∀ l ∈ t, l.1 ∈ vs) (Q : (V → Bool) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun x : Fin vs.length → Bool =>
        t.eval (t.force (wordAssignment vs (List.ofFn x))) = true ∧
          Q (t.force (wordAssignment vs (List.ofFn x)))).card =
      2 ^ t.width * (Finset.univ.filter fun y : Fin vs.length → Bool =>
        t.eval (wordAssignment vs (List.ofFn y)) = true ∧
          Q (wordAssignment vs (List.ofFn y))).card := by
  classical
  simp only [wordAssignment_ofFn]
  set n := vs.length
  let J : Finset (Fin n) := Finset.univ.filter fun i => t.any (fun l => l.1 == vs[i.1])
  let c : Fin n → Bool := fun i => t.any (fun l => l.1 == vs[i.1] && l.2)
  have hglue (x : Fin n → Bool) : t.force (indexAssignment vs x) =
      indexAssignment vs (fun i => if i ∈ J then c i else x i) := by
    funext v
    by_cases hv : v ∈ vs
    · have hlt : vs.idxOf v < n := List.idxOf_lt_length_of_mem hv
      have hget : vs[vs.idxOf v] = v := List.getElem_idxOf hlt
      simp only [Term.force, indexAssignment, hlt, dite_true, J, c, Finset.mem_filter,
        Finset.mem_univ, true_and, hget]
    · have hnot : ∀ l ∈ t, l.1 ≠ v := fun l hl h => hv (h ▸ ht l hl)
      have hlt : ¬ vs.idxOf v < n := by
        rw [not_lt]; exact (List.idxOf_eq_length_iff.2 hv).ge
      rw [Term.force_of_forall_ne hnot]
      simp only [indexAssignment, hlt, dite_false]
  simp only [hglue]
  rw [card_filter_override J c (fun z => t.eval (indexAssignment vs z) = true ∧
    Q (indexAssignment vs z))]
  have hJ : J.card = t.width := by
    rw [Term.width]
    refine Finset.card_bij (fun i _ => vs[i.1]) (fun i hi => ?_) (fun i _ j _ h => ?_)
      (fun v hv => ?_)
    · simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_true,
        beq_iff_eq] at hi
      obtain ⟨l, hl, hlv⟩ := hi
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨l, hl, hlv⟩
    · exact Fin.ext ((hnd.getElem_inj_iff).1 h)
    · simp only [List.mem_toFinset, List.mem_map] at hv
      obtain ⟨l, hl, rfl⟩ := hv
      have hlt : vs.idxOf l.1 < n := List.idxOf_lt_length_of_mem (ht l hl)
      refine ⟨⟨vs.idxOf l.1, hlt⟩, ?_, List.getElem_idxOf hlt⟩
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_true, beq_iff_eq]
      exact ⟨l, hl, (List.getElem_idxOf hlt).symm⟩
  rw [hJ]
  congr 1
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h => h.2, fun h => ⟨fun i hi => ?_, h⟩⟩
  have hf := congrFun (Term.force_eq_of_eval h.1) vs[i.1]
  have hiJ : t.any (fun l => l.1 == vs[i.1]) = true := by
    simpa only [J, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hidx : vs.idxOf vs[i.1] = i.1 := hnd.idxOf_getElem _ _
  simp only [Term.force, hiJ, ite_true, indexAssignment, hidx, i.2, dite_true] at hf
  exact hf.symm

/-- A term on the variables of a nodup list `vs` has at most `|vs|` variables. -/
theorem Term.width_le_length {vs : List V} (hnd : vs.Nodup) {t : Term V}
    (ht : ∀ l ∈ t, l.1 ∈ vs) : t.width ≤ vs.length := by
  rw [Term.width, ← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro v hv
  simp only [List.mem_toFinset, List.mem_map] at hv ⊢
  obtain ⟨l, hl, rfl⟩ := hv
  exact ht l hl

/-- A consistent term on the variables of a nodup list `vs` is satisfied by
`2 ^ (|vs| - t.width)` assignments of these variables. -/
theorem card_filter_eval_eq_two_pow {vs : List V} (hnd : vs.Nodup) {t : Term V}
    (ht : ∀ l ∈ t, l.1 ∈ vs) (hc : t.consistent = true) :
    (Finset.univ.filter fun y : Fin vs.length → Bool =>
      t.eval (wordAssignment vs (List.ofFn y)) = true).card = 2 ^ (vs.length - t.width) := by
  have h := card_filter_force hnd ht (fun _ => True)
  simp only [Term.eval_force hc, and_true, Finset.filter_true, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have hw := Term.width_le_length hnd ht
  have hpow : 2 ^ vs.length = 2 ^ t.width * 2 ^ (vs.length - t.width) := by
    rw [← pow_add, Nat.add_sub_cancel' hw]
  rw [hpow] at h
  exact (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h).symm

/-- A term of `φ` reads only variables of `φ`. -/
theorem DNF.mem_distinctVars_of_mem {φ : DNF V} {t : Term V} (ht : t ∈ φ) :
    ∀ l ∈ t, l.1 ∈ CNF.distinctVars φ := fun l hl =>
  CNF.mem_distinctVars.2 (CNF.mem_vars.2 ⟨t, ht, l.2, hl⟩)

/-- **A consistent term of `φ` contributes a subcube**: `φ` has at least
`2 ^ (CNF.numVars φ - t.width)` satisfying assignments. -/
theorem two_pow_sub_width_le_modelCount {φ : DNF V} {t : Term V} (ht : t ∈ φ)
    (hc : t.consistent = true) : 2 ^ (CNF.numVars φ - t.width) ≤ DNF.modelCount φ := by
  have hcount := card_filter_eval_eq_two_pow (CNF.nodup_distinctVars φ)
    (DNF.mem_distinctVars_of_mem ht) hc
  rw [DNF.modelCount_eq_card_filter, ← CNF.length_distinctVars φ, ← hcount]
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact (DNF.eval_eq_true_iff _ _).2 ⟨t, ht, hy⟩

end Cslib.Logic.PL
