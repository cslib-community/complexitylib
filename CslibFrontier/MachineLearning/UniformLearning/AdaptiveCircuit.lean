/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.MachineLearning.UniformLearning.NonadaptiveCircuit
import CslibFrontier.Computability.Circuit.Boolean.Lookup
import CslibFrontier.Computability.Circuit.Boolean.Substitution

/-!
# Adaptive learners computed by small circuits

An *adaptive* membership-query learner chooses each query from the answers to the queries before
it. Given queries `Q`, where `Q i` maps the answers to the first `i` queries to the `i`-th queried
point, and a hypothesis `H` of all `q` answers, `UniformLearning.QueryLearner.ofAdaptive Q H` is the
learner asking these queries in turn, a decision tree of depth `q`
(`UniformLearning.QueryLearner.queriesAtMost_ofAdaptive`). Run on a target `f`, it outputs `H` of
the answers of `f` (`UniformLearning.QueryLearner.eval_ofAdaptive`,
`UniformLearning.QueryLearner.answersUpTo`).

A learner *has an adaptive circuit* of size `S` with `q` queries
(`UniformLearning.QueryLearner.HasAdaptiveCircuit`) when, on every seed, each query is computed from
the earlier answers by a De Morgan circuit, and the hypothesis at `x` from all answers followed by
`x`, with at most `S` gates in all. The queries do not depend on `x`: as in
`UniformLearning.QueryLearner`, the learner outputs a hypothesis. This is learning by circuits with
adaptive membership queries, the adaptive counterpart of
`UniformLearning.QueryLearner.HasCircuit`, which is the special case of constant queries
(`UniformLearning.QueryLearner.HasCircuit.hasAdaptiveCircuit`). Such a learner agrees with one
making at most `q` queries (`UniformLearning.QueryLearner.HasAdaptiveCircuit.exists_queriesAtMost`).
The other model of adaptive queries in the library is the oracle circuit of
`CslibFrontier.Computability.Circuit.Boolean.Oracle`, one circuit whose oracle gates take arguments
computed from the answers of other oracle gates;
`UniformLearning.QueryLearner.HasCircuit.exists_oracleCircuit` turns a non-adaptive learner with a
circuit into one. Here the queries and the hypothesis are separate circuits, so that the answers
can be read from a truth table, and no adaptive counterpart of that bridge is proved.

Reading the answers from a truth table `T` of `2 ^ n` entries costs at most the gates of the
queries plus `2 ^ n (2 n + 3) + 1` gates per query, for selecting the entry at the computed address
(`UniformLearning.QueryLearner.complexity_append_answers_le`). This bounds the circuits that test a
learner on truth tables in `CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.Circuit`.

The size counts the circuits of the queries and of the hypothesis separately, so gates shared
between them are counted once for each; neither depth nor running time is certified.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.QueryLearner.answersUpTo`: the answers of a target to the
  first `k` adaptive queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.ofAdaptive`: the learner asking adaptive
  queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasAdaptiveCircuit`: on every seed, adaptive
  queries and a hypothesis computed by circuits with at most `S` gates in all.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.eval_ofAdaptive`,
  `Cslib.MachineLearning.UniformLearning.QueryLearner.queriesAtMost_ofAdaptive`: the adaptive
  learner outputs the hypothesis of the answers and makes at most `q` queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasAdaptiveCircuit.exists_queriesAtMost`: a
  learner with an adaptive circuit agrees with one making at most `q` queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit.hasAdaptiveCircuit`: a non-adaptive
  learner with a circuit of `S` gates has an adaptive circuit of `S + 2 q` gates.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.complexity_append_answers_le`: reading the
  answers from a truth table.
-/

public section

namespace Cslib.MachineLearning.UniformLearning.QueryLearner

open Cslib.Circuits Cslib.Circuits.Boolean Finset

section Adaptive

variable {ι Ω : Type*} {q : ℕ}

/-- The answers of the target `f` to the first `k` adaptive queries `Q`: the query `Q i` maps the
answers to the queries before it to the point queried next. -/
def answersUpTo (Q : (i : Fin q) → (Fin i → Bool) → ι → Bool) (f : (ι → Bool) → Bool) :
    (k : ℕ) → k ≤ q → Fin k → Bool
  | 0, _ => Fin.elim0
  | k + 1, hk =>
    let a := answersUpTo Q f k (Nat.le_of_succ_le hk)
    Fin.snoc (α := fun _ => Bool) a (f (Q ⟨k, hk⟩ a))

/-- The answers to constant queries are the values at the queried points. -/
theorem answersUpTo_const (pts : Fin q → ι → Bool) (f : (ι → Bool) → Bool) :
    ∀ (k : ℕ) (hk : k ≤ q),
      answersUpTo (fun i _ => pts i) f k hk = fun j => f (pts (Fin.castLE hk j))
  | 0, _ => funext fun j => j.elim0
  | k + 1, hk => by
    funext j
    simp only [answersUpTo, answersUpTo_const pts f k]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Fin.snoc_last]
      rfl
    · rw [Fin.snoc_castSucc]
      rfl

/-- The decision tree asking the remaining `r` adaptive queries after the answers `a` to the first
`k`, then outputting `H` of all `q` answers. -/
def adaptiveTree {β : Type*} (Q : (i : Fin q) → (Fin i → Bool) → ι → Bool)
    (H : (Fin q → Bool) → β) : (r k : ℕ) → k + r = q → (Fin k → Bool) → DecisionTree (ι → Bool) β
  | 0, _, h, a => .leaf (H fun i => a (Fin.cast h.symm i))
  | r + 1, k, h, a =>
    .node (Q ⟨k, by omega⟩ a)
      (adaptiveTree Q H r (k + 1) (by omega) (Fin.snoc (α := fun _ => Bool) a false))
      (adaptiveTree Q H r (k + 1) (by omega) (Fin.snoc (α := fun _ => Bool) a true))

/-- Run on `f` after the answers of `f` to the first `k` queries, the tree outputs `H` of all the
answers of `f`. -/
theorem eval_adaptiveTree {β : Type*} (Q : (i : Fin q) → (Fin i → Bool) → ι → Bool)
    (H : (Fin q → Bool) → β) (f : (ι → Bool) → Bool) :
    ∀ (r k : ℕ) (h : k + r = q),
      (adaptiveTree Q H r k h (answersUpTo Q f k (by omega))).eval f =
        H (answersUpTo Q f q le_rfl)
  | 0, k, h => by
    obtain rfl : k = q := h
    rfl
  | r + 1, k, h => by
    rw [← eval_adaptiveTree Q H f r (k + 1) (by omega)]
    obtain ⟨b, hb⟩ : ∃ b, f (Q ⟨k, by omega⟩ (answersUpTo Q f k (by omega))) = b := ⟨_, rfl⟩
    simp only [adaptiveTree, answersUpTo, DecisionTree.eval, hb]
    cases b <;> rfl

/-- The tree asking `r` more queries has depth at most `r`. -/
theorem depth_adaptiveTree_le {β : Type*} (Q : (i : Fin q) → (Fin i → Bool) → ι → Bool)
    (H : (Fin q → Bool) → β) :
    ∀ (r k : ℕ) (h : k + r = q) (a : Fin k → Bool), (adaptiveTree Q H r k h a).depth ≤ r
  | 0, _, _, _ => by simp [adaptiveTree]
  | r + 1, k, h, a => by
    simp only [adaptiveTree, DecisionTree.depth]
    exact Nat.succ_le_succ (max_le (depth_adaptiveTree_le Q H r (k + 1) _ _)
      (depth_adaptiveTree_le Q H r (k + 1) _ _))

/-- The adaptive learner: on the seed `ω`, it asks the queries `Q ω`, each computed from the
answers to the earlier ones, and outputs the hypothesis `H ω` of all `q` answers. -/
def ofAdaptive (Q : Ω → (i : Fin q) → (Fin i → Bool) → ι → Bool)
    (H : Ω → (Fin q → Bool) → (ι → Bool) → Bool) : QueryLearner ι Ω :=
  fun ω => adaptiveTree (Q ω) (H ω) q 0 (Nat.zero_add q) Fin.elim0

/-- Run on `f`, the adaptive learner outputs the hypothesis of the answers of `f`. -/
theorem eval_ofAdaptive (Q : Ω → (i : Fin q) → (Fin i → Bool) → ι → Bool)
    (H : Ω → (Fin q → Bool) → (ι → Bool) → Bool) (f : (ι → Bool) → Bool) (ω : Ω) :
    (ofAdaptive Q H ω).eval f = H ω (answersUpTo (Q ω) f q le_rfl) :=
  eval_adaptiveTree (Q ω) (H ω) f q 0 (Nat.zero_add q)

/-- The adaptive learner makes at most `q` queries. -/
theorem queriesAtMost_ofAdaptive (Q : Ω → (i : Fin q) → (Fin i → Bool) → ι → Bool)
    (H : Ω → (Fin q → Bool) → (ι → Bool) → Bool) : (ofAdaptive Q H).QueriesAtMost q :=
  fun ω => depth_adaptiveTree_le (Q ω) (H ω) q 0 _ _

end Adaptive

section Circuit

variable {n q S : ℕ} {Ω : Type*}

/-- **An adaptive learner computed by small circuits**: on every seed `ω`, the `i`-th query is
computed from the answers to the earlier queries by a De Morgan circuit, and the hypothesis at `x`
from all `q` answers followed by `x`, with at most `S` gates in all. Exposed: clients build and take
apart the witnesses. -/
@[expose] def HasAdaptiveCircuit (A : QueryLearner (Fin n) Ω) (q S : ℕ) : Prop :=
  ∀ ω, ∃ (Q : (i : Fin q) → BitString i → BitString n) (H : BooleanFunction (q + n)),
    ∑ i, complexity interpretation (Q i) + complexity interpretation (single H) ≤ S ∧
      ∀ (f : BooleanFunction n) x, (A ω).eval f x = H (Fin.append (answersUpTo Q f q le_rfl) x)

/-- A learner with an adaptive circuit agrees with a learner making at most `q` queries. -/
theorem HasAdaptiveCircuit.exists_queriesAtMost {A : QueryLearner (Fin n) Ω}
    (hA : A.HasAdaptiveCircuit q S) :
    ∃ B : QueryLearner (Fin n) Ω, B.QueriesAtMost q ∧ ∀ ω, (B ω).eval = (A ω).eval := by
  choose Q H _ hev using hA
  refine ⟨ofAdaptive Q fun ω a x => H ω (Fin.append a x), queriesAtMost_ofAdaptive _ _,
    fun ω => funext fun f => ?_⟩
  rw [eval_ofAdaptive]
  exact funext fun x => (hev ω f x).symm

/-- **Non-adaptive learners are adaptive.** A learner with `q` non-adaptive queries and a circuit of
`S` gates has an adaptive circuit of `S + 2 q` gates: each fixed query is a constant, of two
gates. -/
theorem HasCircuit.hasAdaptiveCircuit {A : QueryLearner (Fin n) Ω} (hA : A.HasCircuit q S) :
    A.HasAdaptiveCircuit q (S + 2 * q) := fun ω => by
  obtain ⟨pts, F, hF, hev⟩ := hA ω
  -- each fixed query is a substitution of constants
  let Q : (i : Fin q) → BitString i → BitString n := fun i =>
    substitute fun j => (Sum.inr (pts i j) : Fin i ⊕ Bool)
  refine ⟨Q, F, ?_, fun f x => ?_⟩
  · calc ∑ i, complexity interpretation (Q i) + complexity interpretation (single F)
        ≤ ∑ _i : Fin q, 2 + S :=
          add_le_add (sum_le_sum fun i _ => complexity_substitute_le_two _) hF
      _ = S + 2 * q := by
          rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  · rw [hev, show Q = fun i _ => pts i from rfl, answersUpTo_const]
    rfl

/-- The answers to the first `k` queries, read from a truth table, with the table kept. -/
private theorem complexity_append_answersUpTo_le (Q : (i : Fin q) → BitString i → BitString n) :
    ∀ (k : ℕ) (hk : k ≤ q),
      complexity interpretation (fun T : BitString (2 ^ n) =>
          Fin.append T (answersUpTo Q (fun x => T (BitString.equivFin n x)) k hk)) ≤
        ∑ i : Fin k, (complexity interpretation (Q (Fin.castLE hk i)) + (2 ^ n * (2 * n + 3) + 1))
  | 0, _ => by
    have h : (fun T : BitString (2 ^ n) =>
        Fin.append T (answersUpTo Q (fun x => T (BitString.equivFin n x)) 0 (Nat.zero_le q))) =
        fun T => T ∘ Fin.cast (Nat.add_zero _) :=
      funext fun T => Fin.append_elim0 T
    rw [h, complexity_wiring]
    exact Nat.zero_le _
  | k + 1, hk => by
    have hk' : k ≤ q := Nat.le_of_succ_le hk
    -- the answer to query `k`: the table entry at the address computed from the earlier answers
    let g : (Fin (2 ^ n + k) → Bool) → Bool := fun y =>
      y (Fin.castAdd k (BitString.equivFin n (Q ⟨k, hk⟩ fun i => y (Fin.natAdd (2 ^ n) i))))
    let inner : (Fin (2 ^ n + k) → Bool) → Fin (2 ^ n + n) → Bool := fun y =>
      Fin.append (fun j => y (Fin.castAdd k j)) (Q ⟨k, hk⟩ fun i => y (Fin.natAdd (2 ^ n) i))
    have hsel := complexity_select_le (q := 2 ^ n) (univ : Finset (Fin n))
      fun v => BitString.equivFin n fun j => v ⟨j, mem_univ j⟩
    rw [card_univ, Fintype.card_fin] at hsel
    have hinner : complexity interpretation inner ≤ complexity interpretation (Q ⟨k, hk⟩) := by
      refine (complexity_append_le (fun y : Fin (2 ^ n + k) → Bool => y ∘ Fin.castAdd k) _).trans ?_
      rw [complexity_wiring, zero_add]
      have h := complexity_comp_le (I := interpretation)
        (fun y : Fin (2 ^ n + k) → Bool => y ∘ Fin.natAdd (2 ^ n)) (Q ⟨k, hk⟩)
      rwa [complexity_wiring, zero_add] at h
    have hg : complexity interpretation (single g) ≤
        complexity interpretation (Q ⟨k, hk⟩) + (2 ^ n * (2 * n + 3) + 1) := by
      have hcomp := complexity_comp_le (I := interpretation) inner
        (single fun zx : Fin (2 ^ n + n) → Bool =>
          zx (Fin.castAdd n (BitString.equivFin n fun j => zx (Fin.natAdd (2 ^ n) j))))
      have heq : single g = (single fun zx : Fin (2 ^ n + n) → Bool =>
          zx (Fin.castAdd n (BitString.equivFin n fun j => zx (Fin.natAdd (2 ^ n) j)))) ∘
            inner := by
        funext y i
        simp [g, inner, single]
      rw [heq]
      exact hcomp.trans (add_le_add hinner hsel)
    have happ : complexity interpretation
        (fun y : Fin (2 ^ n + k) → Bool => Fin.append (y ∘ id) (single g y)) ≤
          complexity interpretation (single g) := by
      refine (complexity_append_le _ _).trans ?_
      rw [complexity_wiring, zero_add]
    have hstep : (fun T : BitString (2 ^ n) =>
        Fin.append T (answersUpTo Q (fun x => T (BitString.equivFin n x)) (k + 1) hk)) =
        (fun y : Fin (2 ^ n + k) → Bool => Fin.append (y ∘ id) (single g y)) ∘
          fun T => Fin.append T (answersUpTo Q (fun x => T (BitString.equivFin n x)) k hk') := by
      funext T
      simp only [Function.comp_apply, Function.comp_id, Fin.append_right_eq_snoc, single_apply]
      rw [← Fin.append_snoc]
      simp [answersUpTo, g]
    rw [hstep, Fin.sum_univ_castSucc]
    exact (complexity_comp_le _ _).trans
      (add_le_add (complexity_append_answersUpTo_le Q k hk') (happ.trans hg))

/-- **Reading the answers from a truth table.** Computing, from the truth table `T` of a target on
`n` bits, the table followed by the answers of the target to the adaptive queries `Q` costs at most
the gates of the queries plus `2 ^ n (2 n + 3) + 1` gates per query, for selecting the entry at the
computed address. -/
theorem complexity_append_answers_le (Q : (i : Fin q) → BitString i → BitString n) :
    complexity interpretation (fun T : BitString (2 ^ n) =>
        Fin.append T (answersUpTo Q (fun x => T (BitString.equivFin n x)) q le_rfl)) ≤
      ∑ i, complexity interpretation (Q i) + q * (2 ^ n * (2 * n + 3) + 1) := by
  refine (complexity_append_answersUpTo_le Q q le_rfl).trans_eq ?_
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rfl

end Circuit

end Cslib.MachineLearning.UniformLearning.QueryLearner
