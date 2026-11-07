/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ModelCount
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Splitting clauses into width three with the same number of models

`Cslib.Logic.PL.CNF.to3CNF` splits a long clause with auxiliary variables that a satisfying
assignment may choose freely, so it preserves satisfiability but not the number of satisfying
assignments. Here a clause `l₁ ∨ l₂ ∨ ⋯ ∨ lₘ` with `m > 3` is instead computed by a chain of
binary OR gates. The gate `z ↔ u ∨ v` is imposed by the three clauses

`(¬u ∨ z) ∧ (¬v ∨ z) ∧ (u ∨ v ∨ ¬z)`,

with `z₀ ↔ l₁ ∨ l₂` and `zⱼ ↔ zⱼ₋₁ ∨ lⱼ₊₂`, and the chain ends in the clause
`zₘ₋₄ ∨ lₘ₋₁ ∨ lₘ` [OpenAI2026ETH, §2.8]. Every gate is the disjunction of a prefix of the clause,
so a satisfying assignment of the original variables has exactly one satisfying extension, and the
number of satisfying assignments is unchanged (`Cslib.Logic.PL.CNF.modelCount_toExact3CNF`).
Clauses of width at most three are kept, and the empty clause stays empty.

Together with the count-preserving occurrence splitting
`Cslib.Logic.PL.CNF.modelCount_toThreeOccurrence`, this reduces counting the models of a CNF
formula to counting those of a formula of width three in which every variable occurs at most three
times.

## Main definitions

* `Cslib.Logic.PL.Clause.orChainAux`, `Cslib.Logic.PL.Clause.orSplit3`: the OR-gate chain for one
  clause.
* `Cslib.Logic.PL.CNF.toExact3CNF`: every clause split, over the variables `V ⊕ (ℕ × ℕ)`.

## Main results

* `Cslib.Logic.PL.Clause.eval_orSplit3_iff`: an assignment satisfies the chain exactly when it
  satisfies the clause and gives every gate the value of its prefix.
* `Cslib.Logic.PL.CNF.eval_toExact3CNF_iff`: the same for a whole formula, with gate `(i, k)`
  belonging to clause `i`.
* `Cslib.Logic.PL.CNF.length_le_three_of_mem_toExact3CNF`: every clause has at most three literals.
* `Cslib.Logic.PL.CNF.modelCount_toExact3CNF`: splitting preserves the number of satisfying
  assignments.
* `Cslib.Logic.PL.CNF.satisfiable_toExact3CNF`: hence it preserves satisfiability.
* `Cslib.Logic.PL.CNF.length_toExact3CNF`, `Cslib.Logic.PL.CNF.length_vars_toExact3CNF`,
  `Cslib.Logic.PL.CNF.length_vars_toExact3CNF_le`,
  `Cslib.Logic.PL.CNF.length_vars_le_length_vars_toExact3CNF`: the size, between one and seven
  times the number of literal occurrences.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V W : Type*}

/-! ### One clause -/

/-- The OR-gate chain for the clause `carry :: rest`, with gate variables `fresh j,
fresh (j + 1), …`: the gate `fresh j` is constrained to equal `carry ∨ b`, where `b` is the head of
`rest`, and then carries the remaining disjunction. Once at most two literals remain, the chain
ends in the clause `carry :: rest`. -/
def Clause.orChainAux (fresh : ℕ → W) : ℕ → Literal W → Clause W → CNF W
  | j, carry, b :: c :: d :: rest =>
    [(carry.1, !carry.2), (fresh j, true)] :: [(b.1, !b.2), (fresh j, true)] ::
      [carry, b, (fresh j, false)] ::
        Clause.orChainAux fresh (j + 1) (fresh j, true) (c :: d :: rest)
  | _, carry, rest => [carry :: rest]

/-- The OR-gate chain for a clause, with gate variables `fresh j, fresh (j + 1), …`. A clause with
at most three literals is kept as it is. -/
def Clause.orSplit3 (fresh : ℕ → W) (j : ℕ) : Clause W → CNF W
  | [] => [[]]
  | carry :: rest => Clause.orChainAux fresh j carry rest

private theorem Literal.eval_neg (σ : W → Bool) (l : Literal W) :
    Literal.eval σ (l.1, !l.2) = !Literal.eval σ l := by
  obtain ⟨v, b⟩ := l
  cases b <;> cases h : σ v <;> simp [Literal.eval, h]

/-- The chain for `carry :: rest` holds exactly when the clause holds and gate `fresh (j + i)` has
the value of the first `i + 2` literals. -/
private theorem Clause.eval_orChainAux_iff (fresh : ℕ → W) (σ : W → Bool) (j : ℕ)
    (carry : Literal W) (rest : Clause W) :
    (Clause.orChainAux fresh j carry rest).eval σ = true ↔
      Clause.eval σ (carry :: rest) = true ∧
        ∀ i < rest.length - 2, σ (fresh (j + i)) = Clause.eval σ (carry :: rest.take (i + 1)) := by
  induction j, carry, rest using Clause.orChainAux.induct fresh with
  | case1 j carry b c d rest ih =>
    have hgate : (CNF.eval σ [[(carry.1, !carry.2), (fresh j, true)],
        [(b.1, !b.2), (fresh j, true)], [carry, b, (fresh j, false)]] = true) ↔
        σ (fresh j) = (Literal.eval σ carry || Literal.eval σ b) := by
      have hz : Literal.eval σ (fresh j, true) = σ (fresh j) := by
        simp only [Literal.eval, beq_true]
      have hz' : Literal.eval σ (fresh j, false) = !σ (fresh j) := by
        simp only [Literal.eval, beq_false]
      simp only [CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil, Literal.eval_neg,
        hz, hz']
      generalize σ (fresh j) = z
      generalize Literal.eval σ carry = x
      generalize Literal.eval σ b = y
      cases z <;> cases x <;> cases y <;> decide
    have hsplit : (Clause.orChainAux fresh j carry (b :: c :: d :: rest)).eval σ =
        (CNF.eval σ [[(carry.1, !carry.2), (fresh j, true)], [(b.1, !b.2), (fresh j, true)],
          [carry, b, (fresh j, false)]] &&
          (Clause.orChainAux fresh (j + 1) (fresh j, true) (c :: d :: rest)).eval σ) := by
      simp only [Clause.orChainAux, CNF.eval_cons, CNF.eval_nil, Bool.and_true, Bool.and_assoc]
    rw [hsplit, Bool.and_eq_true, hgate, ih]
    have hz : Literal.eval σ (fresh j, true) = σ (fresh j) := by
      simp only [Literal.eval, beq_true]
    simp only [Clause.eval_cons, hz, List.length_cons]
    constructor
    · rintro ⟨hj, hcl, hi⟩
      refine ⟨by rw [← hcl, hj, Bool.or_assoc], fun i hi' => ?_⟩
      cases i with
      | zero => simp [hj]
      | succ i =>
        rw [show j + (i + 1) = j + 1 + i by omega, hi i (by omega), hj]
        simp only [List.take_succ_cons, Clause.eval_cons, Bool.or_assoc]
    · rintro ⟨hcl, hi⟩
      have hj : σ (fresh j) = (Literal.eval σ carry || Literal.eval σ b) := by
        simpa using hi 0 (by omega)
      refine ⟨hj, by rw [hj, Bool.or_assoc, hcl], fun i hi' => ?_⟩
      rw [show j + 1 + i = j + (i + 1) by omega, hi (i + 1) (by omega), hj]
      simp only [List.take_succ_cons, Clause.eval_cons, Bool.or_assoc]
  | case2 j carry rest hrest =>
    rw [Clause.orChainAux]
    · have hlen : rest.length - 2 = 0 := by
        match rest, hrest with
        | [], _ | [_], _ | [_, _], _ => rfl
        | _ :: _ :: _ :: _, hrest => exact absurd rfl (hrest _ _ _ _)
      simp [hlen]
    · exact hrest

/-- **The OR-gate chain of a clause**: an assignment satisfies `Clause.orSplit3 fresh j c` exactly
when it satisfies `c` and gives the gate `fresh (j + i)` the value of the first `i + 2` literals of
`c`, for every gate `i < c.length - 3`. -/
theorem Clause.eval_orSplit3_iff (fresh : ℕ → W) (σ : W → Bool) (j : ℕ) (c : Clause W) :
    (Clause.orSplit3 fresh j c).eval σ = true ↔
      c.eval σ = true ∧ ∀ i < c.length - 3, σ (fresh (j + i)) = Clause.eval σ (c.take (i + 2)) := by
  cases c with
  | nil => simp [Clause.orSplit3]
  | cons carry rest =>
    rw [Clause.orSplit3, Clause.eval_orChainAux_iff]
    simp only [List.length_cons, List.take_succ_cons]
    rfl

private theorem Clause.length_le_three_of_mem_orChainAux (fresh : ℕ → W) (j : ℕ)
    (carry : Literal W) (rest : Clause W) :
    ∀ d ∈ Clause.orChainAux fresh j carry rest, d.length ≤ 3 := by
  induction j, carry, rest using Clause.orChainAux.induct fresh with
  | case1 j carry b c d rest ih =>
    intro e he
    simp only [Clause.orChainAux, List.mem_cons] at he
    rcases he with rfl | rfl | rfl | he
    · simp
    · simp
    · simp
    · exact ih e he
  | case2 j carry rest hrest =>
    intro e he
    rw [Clause.orChainAux] at he
    · simp only [List.mem_singleton] at he
      subst he
      match rest, hrest with
      | [], _ | [_], _ | [_, _], _ => simp
      | _ :: _ :: _ :: _, hrest => exact absurd rfl (hrest _ _ _ _)
    · exact hrest

/-- Every clause in `Clause.orSplit3 fresh j c` has at most three literals. -/
theorem Clause.length_le_three_of_mem_orSplit3 (fresh : ℕ → W) (j : ℕ) (c : Clause W) :
    ∀ d ∈ Clause.orSplit3 fresh j c, d.length ≤ 3 := by
  cases c with
  | nil => simp [Clause.orSplit3]
  | cons carry rest => exact Clause.length_le_three_of_mem_orChainAux fresh j carry rest

/-- The variables of the chain for `carry :: rest`: those of the clause, and gate variables of
index from `j` on. -/
private theorem Clause.mem_vars_orChainAux (fresh : ℕ → W) (j : ℕ) (carry : Literal W)
    (rest : Clause W) (x : W) :
    x ∈ (Clause.orChainAux fresh j carry rest).vars →
      (∃ b, (x, b) ∈ carry :: rest) ∨ ∃ i < rest.length - 2, x = fresh (j + i) := by
  induction j, carry, rest using Clause.orChainAux.induct fresh with
  | case1 j carry b c d rest ih =>
    intro hx
    obtain ⟨e, he, s, hs⟩ := CNF.mem_vars.1 hx
    simp only [Clause.orChainAux, List.mem_cons] at he
    rcases he with rfl | rfl | rfl | he
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨h, -⟩ | ⟨h, -⟩
      · exact .inl ⟨carry.2, by rw [h]; exact List.mem_cons_self⟩
      · exact .inr ⟨0, by simp, by rw [h, Nat.add_zero]⟩
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨h, -⟩ | ⟨h, -⟩
      · exact .inl ⟨b.2, by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
      · exact .inr ⟨0, by simp, by rw [h, Nat.add_zero]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with h | h | h
      · exact .inl ⟨s, by rw [h]; exact List.mem_cons_self⟩
      · exact .inl ⟨s, by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
      · simp only [Prod.mk.injEq] at h
        exact .inr ⟨0, by simp, by rw [h.1, Nat.add_zero]⟩
    · rcases ih (CNF.mem_vars.2 ⟨e, he, s, hs⟩) with ⟨t, ht⟩ | ⟨i, hi, rfl⟩
      · rw [List.mem_cons] at ht
        rcases ht with ht | ht
        · simp only [Prod.mk.injEq] at ht
          exact .inr ⟨0, by simp, by rw [ht.1, Nat.add_zero]⟩
        · exact .inl ⟨t, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)⟩
      · exact .inr ⟨i + 1, by simp only [List.length_cons] at hi ⊢; omega,
          by rw [show j + (i + 1) = j + 1 + i by omega]⟩
  | case2 j carry rest hrest =>
    intro hx
    rw [Clause.orChainAux] at hx
    · obtain ⟨e, he, s, hs⟩ := CNF.mem_vars.1 hx
      rw [List.mem_singleton] at he
      subst he
      exact .inl ⟨s, hs⟩
    · exact hrest

/-- The variables of the chain of a clause: those of the clause, and the gate variables
`fresh (j + i)` for `i < c.length - 3`. -/
theorem Clause.mem_vars_orSplit3 (fresh : ℕ → W) (j : ℕ) (c : Clause W) {x : W}
    (hx : x ∈ (Clause.orSplit3 fresh j c).vars) :
    (∃ b, (x, b) ∈ c) ∨ ∃ i < c.length - 3, x = fresh (j + i) := by
  cases c with
  | nil => simp [Clause.orSplit3, CNF.vars] at hx
  | cons carry rest =>
    simpa using Clause.mem_vars_orChainAux fresh j carry rest x hx

private theorem Clause.vars_subset_orChainAux (fresh : ℕ → W) (j : ℕ) (carry : Literal W)
    (rest : Clause W) {x : W} {b : Bool} (h : (x, b) ∈ carry :: rest) :
    x ∈ (Clause.orChainAux fresh j carry rest).vars := by
  induction j, carry, rest using Clause.orChainAux.induct fresh with
  | case1 j carry b' c d rest ih =>
    rw [CNF.mem_vars]
    simp only [List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact ⟨[(x, b), b', (fresh j, false)], by simp [Clause.orChainAux], b, by simp⟩
    · exact ⟨[carry, (x, b), (fresh j, false)], by simp [Clause.orChainAux], b, by simp⟩
    · obtain ⟨e, he, s, hs⟩ := CNF.mem_vars.1 (ih (by simp only [List.mem_cons]; tauto))
      exact ⟨e, by simp only [Clause.orChainAux, List.mem_cons]; tauto, s, hs⟩
  | case2 j carry rest hrest =>
    rw [Clause.orChainAux]
    · exact CNF.mem_vars.2 ⟨_, List.mem_singleton_self _, b, h⟩
    · exact hrest

/-- Every variable of a clause is a variable of its chain. -/
theorem Clause.mem_vars_orSplit3_of_mem (fresh : ℕ → W) (j : ℕ) {c : Clause W} {x : W} {b : Bool}
    (h : (x, b) ∈ c) : x ∈ (Clause.orSplit3 fresh j c).vars := by
  cases c with
  | nil => simp at h
  | cons carry rest => exact Clause.vars_subset_orChainAux fresh j carry rest h

private theorem Clause.length_orChainAux (fresh : ℕ → W) (j : ℕ) (carry : Literal W)
    (rest : Clause W) :
    (Clause.orChainAux fresh j carry rest).length = 3 * (rest.length - 2) + 1 := by
  induction j, carry, rest using Clause.orChainAux.induct fresh with
  | case1 j carry b c d rest ih =>
    simp only [Clause.orChainAux, List.length_cons, ih]
    omega
  | case2 j carry rest hrest =>
    rw [Clause.orChainAux]
    · match rest, hrest with
      | [], _ | [_], _ | [_, _], _ => rfl
      | _ :: _ :: _ :: _, hrest => exact absurd rfl (hrest _ _ _ _)
    · exact hrest

/-- The chain of a clause of width `w` has `3 (w - 3) + 1` clauses: three per gate and one more.
-/
theorem Clause.length_orSplit3 (fresh : ℕ → W) (j : ℕ) (c : Clause W) :
    (Clause.orSplit3 fresh j c).length = 3 * (c.length - 3) + 1 := by
  cases c with
  | nil => rfl
  | cons carry rest =>
    rw [Clause.orSplit3, Clause.length_orChainAux, List.length_cons]
    rfl

private theorem Clause.length_vars_orChainAux (fresh : ℕ → W) (j : ℕ) (carry : Literal W)
    (rest : Clause W) :
    (Clause.orChainAux fresh j carry rest).vars.length =
      (rest.length + 1) + 6 * (rest.length - 2) := by
  induction j, carry, rest using Clause.orChainAux.induct fresh with
  | case1 j carry b c d rest ih =>
    rw [CNF.length_vars] at ih ⊢
    simp only [Clause.orChainAux, List.map_cons, List.sum_cons, List.length_cons,
      List.length_nil] at ih ⊢
    omega
  | case2 j carry rest hrest =>
    rw [Clause.orChainAux]
    · match rest, hrest with
      | [], _ | [_], _ | [_, _], _ => rfl
      | _ :: _ :: _ :: _, hrest => exact absurd rfl (hrest _ _ _ _)
    · exact hrest

/-- The chain of a clause of width `w` has `w + 6 (w - 3)` literal occurrences: seven per gate,
and the three of the last clause. -/
theorem Clause.length_vars_orSplit3 (fresh : ℕ → W) (j : ℕ) (c : Clause W) :
    (Clause.orSplit3 fresh j c).vars.length = c.length + 6 * (c.length - 3) := by
  cases c with
  | nil => rfl
  | cons carry rest =>
    rw [Clause.orSplit3, Clause.length_vars_orChainAux, List.length_cons]
    omega

/-! ### Formulas -/

/-- Split every clause of a formula into OR gates, renaming its variables into the left summand and
naming the gate variables of clause `i` by `(i, j)`. -/
def CNF.toExact3CNF (φ : CNF V) : CNF (V ⊕ (ℕ × ℕ)) :=
  φ.zipIdx.flatMap fun x =>
    Clause.orSplit3 (fun j => Sum.inr (x.2, j)) 0 (x.1.relabel Sum.inl)

/-- Every clause of `CNF.toExact3CNF φ` has at most three literals. -/
theorem CNF.length_le_three_of_mem_toExact3CNF {φ : CNF V} {c : Clause (V ⊕ (ℕ × ℕ))}
    (hc : c ∈ φ.toExact3CNF) : c.length ≤ 3 := by
  obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
  exact Clause.length_le_three_of_mem_orSplit3 _ _ _ c hc

private theorem CNF.mem_zipIdx_iff_mem {φ : CNF V} {c : Clause V} :
    (∃ i, (c, i) ∈ φ.zipIdx) ↔ c ∈ φ := by
  constructor
  · rintro ⟨i, hx⟩
    rw [List.mem_zipIdx_iff_getElem?] at hx
    exact List.mem_of_getElem? (by simpa using hx)
  · intro hc
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.1 hc
    exact ⟨i, by rw [List.mem_zipIdx_iff_getElem?]; simp [← hi.2]⟩

private theorem Clause.eval_take_relabel_inl (τ : V ⊕ (ℕ × ℕ) → Bool) (c : Clause V) (n : ℕ) :
    Clause.eval τ ((c.relabel Sum.inl).take n) = Clause.eval (τ ∘ Sum.inl) (c.take n) := by
  rw [Clause.relabel, ← List.map_take, ← Clause.relabel, Clause.eval_relabel]

/-- An assignment satisfies `CNF.toExact3CNF φ` exactly when its restriction satisfies `φ` and
every gate `(i, k)` of clause `c = φ[i]` has the value of the first `k + 2` literals of `c`. -/
theorem CNF.eval_toExact3CNF_iff (φ : CNF V) (τ : V ⊕ (ℕ × ℕ) → Bool) :
    φ.toExact3CNF.eval τ = true ↔
      φ.eval (τ ∘ Sum.inl) = true ∧
        ∀ c i, (c, i) ∈ φ.zipIdx → ∀ k < c.length - 3,
          τ (.inr (i, k)) = Clause.eval (τ ∘ Sum.inl) (c.take (k + 2)) := by
  rw [CNF.toExact3CNF, CNF.eval_flatMap_eq_true_iff, CNF.eval_eq_true_iff]
  simp only [Clause.eval_orSplit3_iff, Clause.eval_relabel, Clause.length_relabel,
    Clause.eval_take_relabel_inl, Nat.zero_add]
  constructor
  · intro h
    refine ⟨fun c hc => ?_, fun c i hx k hk => (h (c, i) hx).2 k hk⟩
    obtain ⟨i, hx⟩ := CNF.mem_zipIdx_iff_mem.2 hc
    exact (h (c, i) hx).1
  · rintro ⟨h₁, h₂⟩ ⟨c, i⟩ hx
    exact ⟨h₁ c (CNF.mem_zipIdx_iff_mem.1 ⟨i, hx⟩), h₂ c i hx⟩

/-- The variables of `CNF.toExact3CNF φ`: the variables of `φ`, and gate variables `(i, k)` with
`k < c.length - 3` for the clause `c = φ[i]`. -/
theorem CNF.mem_vars_toExact3CNF {φ : CNF V} {x : V ⊕ (ℕ × ℕ)} (hx : x ∈ φ.toExact3CNF.vars) :
    (∃ v ∈ φ.vars, x = .inl v) ∨
      ∃ c i k, (c, i) ∈ φ.zipIdx ∧ k < c.length - 3 ∧ x = .inr (i, k) := by
  obtain ⟨e, he, b, hb⟩ := CNF.mem_vars.1 hx
  obtain ⟨⟨c, i⟩, hci, he⟩ := List.mem_flatMap.1 he
  rcases Clause.mem_vars_orSplit3 _ _ _ (CNF.mem_vars.2 ⟨e, he, b, hb⟩) with
    ⟨b', hb'⟩ | ⟨k, hk, rfl⟩
  · obtain ⟨⟨v, b''⟩, hv, hvx⟩ := List.mem_map.1 hb'
    simp only [Prod.map, Prod.mk.injEq] at hvx
    exact .inl ⟨v, CNF.mem_vars.2 ⟨c, CNF.mem_zipIdx_iff_mem.1 ⟨i, hci⟩, b'', hv⟩, hvx.1.symm⟩
  · rw [Clause.length_relabel] at hk
    exact .inr ⟨c, i, k, hci, hk, by rw [Nat.zero_add]⟩

/-- Every variable of `φ` is a variable of `CNF.toExact3CNF φ`. -/
theorem CNF.inl_mem_vars_toExact3CNF {φ : CNF V} {v : V} (hv : v ∈ φ.vars) :
    (Sum.inl v : V ⊕ (ℕ × ℕ)) ∈ φ.toExact3CNF.vars := by
  obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hv
  obtain ⟨i, hci⟩ := CNF.mem_zipIdx_iff_mem.2 hc
  have hmem := Clause.mem_vars_orSplit3_of_mem (fun j => (Sum.inr (i, j) : V ⊕ (ℕ × ℕ))) 0
    (c := c.relabel Sum.inl) (b := b) (List.mem_map.2 ⟨(v, b), hb, rfl⟩)
  obtain ⟨e, he, s, hs⟩ := CNF.mem_vars.1 hmem
  exact CNF.mem_vars.2 ⟨e, List.mem_flatMap.2 ⟨(c, i), hci, he⟩, s, hs⟩

private theorem Clause.eval_take_congr {φ : CNF V} {σ τ : V → Bool}
    (h : ∀ v ∈ φ.vars, σ v = τ v) {c : Clause V} (hc : c ∈ φ) (n : ℕ) :
    Clause.eval σ (c.take n) = Clause.eval τ (c.take n) := by
  have := CNF.eval_congr (φ := [c.take n]) (σ := σ) (τ := τ) fun v hv => by
    obtain ⟨e, he, b, hb⟩ := CNF.mem_vars.1 hv
    rw [List.mem_singleton] at he
    subst he
    exact h v (CNF.mem_vars.2 ⟨c, hc, b, List.mem_of_mem_take hb⟩)
  simpa using this

/-- **Splitting into OR gates preserves the number of satisfying assignments**
[OpenAI2026ETH, §2.8]: every satisfying assignment of `φ` has exactly one extension to the gate
variables satisfying `CNF.toExact3CNF φ`. This holds for every formula, including empty formulas,
empty clauses and repeated literals. -/
theorem CNF.modelCount_toExact3CNF [DecidableEq V] (φ : CNF V) :
    φ.toExact3CNF.modelCount = φ.modelCount := by
  classical
  let f (τ : V ⊕ (ℕ × ℕ) → Bool) (v : φ.vars.toFinset) : Bool := τ (.inl v)
  refine (CNF.modelCount_eq_card_filter f (fun ρ => φ.eval (φ.extendAssignment ρ) = true)
    (fun σ τ hσ hτ => ?_) fun ρ => ?_).trans rfl
  · rw [CNF.eval_toExact3CNF_iff] at hσ hτ
    constructor
    · intro he x hx
      have hagree : ∀ v ∈ φ.vars, (σ ∘ Sum.inl) v = (τ ∘ Sum.inl) v := fun v hv =>
        congrFun he ⟨v, List.mem_toFinset.2 hv⟩
      rcases CNF.mem_vars_toExact3CNF hx with ⟨v, hv, rfl⟩ | ⟨c, i, k, hci, hk, rfl⟩
      · exact hagree v hv
      · rw [hσ.2 c i hci k hk, hτ.2 c i hci k hk]
        exact Clause.eval_take_congr hagree (CNF.mem_zipIdx_iff_mem.1 ⟨i, hci⟩) _
    · intro he
      exact funext fun v =>
        he _ (CNF.inl_mem_vars_toExact3CNF (List.mem_toFinset.1 v.2))
  · constructor
    · intro hρ
      let σ : V ⊕ (ℕ × ℕ) → Bool :=
        Sum.elim (φ.extendAssignment ρ)
          fun x => Clause.eval (φ.extendAssignment ρ) ((φ.getD x.1 []).take (x.2 + 2))
      refine ⟨σ, (CNF.eval_toExact3CNF_iff φ σ).2 ⟨hρ, fun c i hci k _ => ?_⟩, funext fun v => ?_⟩
      · rw [List.mem_zipIdx_iff_getElem?] at hci
        have hget : φ.getD i [] = c := by simp [List.getD_eq_getElem?_getD, hci]
        simp only [σ, Sum.elim_inr, hget]
        rfl
      · exact CNF.extendAssignment_of_mem _ (List.mem_toFinset.1 v.2)
    · rintro ⟨σ, hσ, rfl⟩
      rw [CNF.eval_toExact3CNF_iff] at hσ
      refine (CNF.eval_congr fun v hv => ?_).trans hσ.1
      exact CNF.extendAssignment_of_mem _ hv

/-- Splitting into OR gates preserves satisfiability. -/
theorem CNF.satisfiable_toExact3CNF (φ : CNF V) :
    φ.toExact3CNF.Satisfiable ↔ φ.Satisfiable := by
  classical
  rw [← CNF.modelCount_pos_iff, ← CNF.modelCount_pos_iff, CNF.modelCount_toExact3CNF]

/-- The number of clauses after splitting: `3 (w - 3) + 1` for a clause of width `w`. -/
theorem CNF.length_toExact3CNF (φ : CNF V) :
    φ.toExact3CNF.length = (φ.map fun c => 3 * (c.length - 3) + 1).sum := by
  rw [CNF.toExact3CNF, List.length_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 φ, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [Clause.length_orSplit3, Function.comp_apply, Clause.length_relabel]

private theorem CNF.length_vars_flatMap {ι : Type*} (l : List ι) (g : ι → CNF W) :
    (CNF.vars (l.flatMap g)).length = (l.map fun a => (g a).vars.length).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih, CNF.length_vars, CNF.length_vars,
      CNF.length_vars, List.map_append, List.sum_append]

/-- The number of literal occurrences after splitting: `w + 6 (w - 3)` for a clause of width
`w`. -/
theorem CNF.length_vars_toExact3CNF (φ : CNF V) :
    φ.toExact3CNF.vars.length = (φ.map fun c => c.length + 6 * (c.length - 3)).sum := by
  rw [CNF.toExact3CNF, CNF.length_vars_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 φ, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [Clause.length_vars_orSplit3, Function.comp_apply, Clause.length_relabel]

/-- Splitting at most multiplies the number of literal occurrences by seven. -/
theorem CNF.length_vars_toExact3CNF_le (φ : CNF V) :
    φ.toExact3CNF.vars.length ≤ 7 * φ.vars.length := by
  rw [CNF.length_vars_toExact3CNF, CNF.length_vars, ← List.sum_map_mul_left]
  exact List.sum_le_sum fun c _ => by omega

/-- Splitting keeps every literal occurrence. -/
theorem CNF.length_vars_le_length_vars_toExact3CNF (φ : CNF V) :
    φ.vars.length ≤ φ.toExact3CNF.vars.length := by
  rw [CNF.length_vars_toExact3CNF, CNF.length_vars]
  exact List.sum_le_sum fun c _ => by omega

end Cslib.Logic.PL
