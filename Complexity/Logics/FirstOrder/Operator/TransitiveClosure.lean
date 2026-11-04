/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Polarity
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Relation

/-!
# First-order logic with tuple transitive closure

The operator of width `k` binds two `k`-tuples in one formula body and is applied to two
`k`-tuples of terms. Its interpretation is the **reflexive** transitive closure of the relation
defined by the body. Free parameters are held fixed along the path, and bodies may contain
nested closure operators. Width zero is allowed: there is one empty tuple, even on an empty
domain, and its reflexive reachability always holds.

## Main definitions

* `shape`, `policy`, `interpretation`: tuple closure as a scoped, positive logical operator.
* `tc`: the formula constructor.
* `pair`, `left`, `right`: concatenate and split the endpoint tuples.

## Main results

* `interpretation_respects`: closure is monotone in its body relation.
* `realize_tc`: semantics in terms of Mathlib's `Relation.ReflTransGen`.
* `realize_tc_pair`: the same semantics with explicit source and target term tuples.
* `realize_tc_refl`, `realize_tc_of_body`, `realize_tc_trans`: reflexivity, edge inclusion,
  and composition of paths.

This file provides logical syntax and semantics, not a complexity-class capture theorem.

## References

* [N. Immerman, *Descriptive Complexity*, Chapter 9][Immerman1999]
-/

public section

universe u v w z

open FirstOrder Language Cslib.Logic.FO.Operator

namespace Cslib.Logic.FO.TC

/-- Concatenate equal-length tuples, with the resulting arity written as `2 * k`. -/
@[expose] def pair {A : Type*} {k : ℕ} (xs ys : Fin k → A) : Fin (2 * k) → A :=
  fun i => Fin.append xs ys (Fin.cast (Nat.two_mul k) i)

/-- The source tuple of a closure application. -/
@[expose] def left {A : Type*} {k : ℕ} (xs : Fin (2 * k) → A) : Fin k → A :=
  fun i => xs (Fin.cast (Nat.two_mul k).symm (Fin.castAdd k i))

/-- The target tuple of a closure application. -/
@[expose] def right {A : Type*} {k : ℕ} (xs : Fin (2 * k) → A) : Fin k → A :=
  fun i => xs (Fin.cast (Nat.two_mul k).symm (Fin.natAdd k i))

/-- Concatenation preserves the source tuple. -/
@[simp] theorem left_pair {A : Type*} {k : ℕ} (xs ys : Fin k → A) :
    left (pair xs ys) = xs := by
  funext i
  simp [left, pair]

/-- Concatenation preserves the target tuple. -/
@[simp] theorem right_pair {A : Type*} {k : ℕ} (xs ys : Fin k → A) :
    right (pair xs ys) = ys := by
  funext i
  simp only [right, pair, Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]

/-- Tuple closure binds two tuples and no relation variables. -/
@[expose] def shape (k : ℕ) : Shape where
  arity := 2 * k
  slots := 1
  binder := fun _ => ⟨[], 2 * k⟩

/-- Closure is positive in its single body and imposes no local relation constraints. -/
@[expose] def policy : Policy shape where
  variance := fun _ _ => .positive
  positive := fun _ _ {_} _ => false

/-- Interpret closure as reflexive reachability between endpoint tuples. -/
@[expose] def interpretation {M : Type z} : Interpretation shape M :=
  fun _ bodies args =>
    Relation.ReflTransGen (fun xs ys => bodies (0 : Fin 1) RelEnv.empty (pair xs ys))
      (left args) (right args)

/-- Enlarging the body relation preserves all paths. -/
theorem interpretation_respects {M : Type z} :
    (@interpretation M).Respects policy.variance := by
  intro k F G h args hp
  exact Relation.ReflTransGen.mono
    (fun xs ys hxy => h (0 : Fin 1) RelEnv.empty (pair xs ys) hxy) _ _ hp

variable {L : Language.{u, v}} {Γ : List ℕ} {α : Type w} {M : Type z} [L.Structure M]

/-- Apply tuple closure to a body with two locally bound endpoint tuples. -/
@[expose] def tc {k : ℕ} (body : Formula L shape Γ (α ⊕ Fin (2 * k)))
    (args : Fin (2 * k) → L.Term α) : Formula L shape Γ α :=
  .op k (fun _ => body) args

/-- Closure adds no formation condition beyond those already present in its body. -/
@[simp] theorem wellFormed_tc {k : ℕ}
    (body : Formula L shape Γ (α ⊕ Fin (2 * k))) (args : Fin (2 * k) → L.Term α) :
    (tc body args).wellFormed policy = body.wellFormed policy := by
  change decide (∀ _ : Fin 1, body.wellFormed policy = true ∧
    body.checkPolarity policy.variance true (fun {_} _ => false) = true) =
      body.wellFormed policy
  simp

/-- Closure holds exactly when a finite path connects the evaluated endpoint tuples. -/
@[simp, fo_realize] theorem realize_tc {k : ℕ}
    (body : Formula L shape Γ (α ⊕ Fin (2 * k))) (args : Fin (2 * k) → L.Term α)
    (ρ : RelEnv Γ M) (v : α → M) :
    (tc body args).Realize interpretation ρ v ↔
      Relation.ReflTransGen
        (fun xs ys => body.Realize interpretation ρ (Sum.elim v (pair xs ys)))
        (fun i => (left args i).realize v) (fun i => (right args i).realize v) := Iff.rfl

/-- Applying closure to concatenated endpoint terms realizes ordinary tuple reachability. -/
@[fo_realize] theorem realize_tc_pair {k : ℕ}
    (body : Formula L shape Γ (α ⊕ Fin (2 * k))) (xs ys : Fin k → L.Term α)
    (ρ : RelEnv Γ M) (v : α → M) :
    (tc body (pair xs ys)).Realize interpretation ρ v ↔
      Relation.ReflTransGen
        (fun us vs => body.Realize interpretation ρ (Sum.elim v (pair us vs)))
        (fun i => (xs i).realize v) (fun i => (ys i).realize v) := by
  simp only [realize_tc, left_pair, right_pair]

/-- The empty path makes every tuple reachable from itself. -/
theorem realize_tc_refl {k : ℕ} (body : Formula L shape Γ (α ⊕ Fin (2 * k)))
    (xs : Fin k → L.Term α) (ρ : RelEnv Γ M) (v : α → M) :
    (tc body (pair xs xs)).Realize interpretation ρ v :=
  (realize_tc_pair body xs xs ρ v).2 .refl

/-- Every edge defined by the body is a closure path of length one. -/
theorem realize_tc_of_body {k : ℕ} (body : Formula L shape Γ (α ⊕ Fin (2 * k)))
    (xs ys : Fin k → L.Term α) (ρ : RelEnv Γ M) (v : α → M)
    (h : body.Realize interpretation ρ
      (Sum.elim v (pair (fun i => (xs i).realize v) (fun i => (ys i).realize v)))) :
    (tc body (pair xs ys)).Realize interpretation ρ v :=
  (realize_tc_pair body xs ys ρ v).2 (.single h)

/-- Paths with a common intermediate tuple compose. -/
theorem realize_tc_trans {k : ℕ} (body : Formula L shape Γ (α ⊕ Fin (2 * k)))
    (xs ys zs : Fin k → L.Term α) (ρ : RelEnv Γ M) (v : α → M)
    (hxy : (tc body (pair xs ys)).Realize interpretation ρ v)
    (hyz : (tc body (pair ys zs)).Realize interpretation ρ v) :
    (tc body (pair xs zs)).Realize interpretation ρ v :=
  (realize_tc_pair body xs zs ρ v).2
    (((realize_tc_pair body xs ys ρ v).1 hxy).trans ((realize_tc_pair body ys zs ρ v).1 hyz))

end Cslib.Logic.FO.TC
