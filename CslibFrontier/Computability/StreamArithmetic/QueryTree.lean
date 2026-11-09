/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# Conditional query programs and regenerated gate evaluation

This module formalizes [OpenAI2026LogSpace, Section 10.1, Lemma 10.2], capturing depth-first
evaluation of bounded-fan-in conditional Boolean circuits and finite streaming residue procedures
over operand digit streams and clock-zero structural leaves.

A `QueryProg Op Struct α` represents a deterministic finite query tree that:
* queries operand stream digits `(op, j)` while charging `retainedBits` bits of live suspended
  local state across the recursive call,
* queries structural predicates `sOp` (at clock zero) while charging `retainedBits` bits of live
  suspended local state across the call,
* executes internal scratch-only computations (`scratchStep scratchBits`) that make no operand or
  structural queries, and
* returns a value of type `α`.

Sequential composition (`bindOverhead overheadBits p k`) adds `overheadBits` (recording the return
mode, branch selector, and bounded pending result of the enclosing frame) to every suspended record
and scratch step inside `p`, and releases `p`'s entire local frame as soon as `p` returns its
result to `k`.

We also formalize conditional bounded-fan-in Boolean formula trees (`CondBoolTree`) whose gate
descriptions are regenerated from root parameters in `regenScratch` shared scratch bits, proving
**Lemma 10.2** (`CondBoolTree.toQueryProg_eval`, `CondBoolTree.toQueryProg_retainedBits_le`,
`CondBoolTree.toQueryProg_intrinsic_le`): depth-first evaluation retains at most `2 * depth`
annotated local bits above any leaf query without storing absolute gate addresses along the path.

## Specification boundary

`QueryProg` and `CondBoolTree` model conditional query-tree semantics and caller-supplied bit
annotations (`retainedBits`, `scratchBits`, `regenScratch`) prior to native machine compilation.
Continuations in `QueryProg` (`queryDigit`, `queryStruct`), post-processing maps (`QueryProg.map`),
and leaf predicates (`CondBoolTree.digitBit`) are host Lean functions; uniform `O(B + d + t)`
gate/descriptor regeneration and native Turing or counter-program compilation are established by
downstream machine-realization layers rather than by arbitrary `QueryProg` closures.

## Main definitions

* `Cslib.StreamArithmetic.QueryEvent`: a single executed operand-digit or structural query together
  with the live `retainedBits` suspended across it.
* `Cslib.StreamArithmetic.QueryProg`: deterministic finite conditional query program with explicit
  suspended-record and intrinsic-scratch accounting.
* `Cslib.StreamArithmetic.QueryProg.bindOverhead`: sequential composition charging a fixed frame
  overhead during the first subprogram and releasing that frame upon completion.
* `Cslib.StreamArithmetic.QueryProg.substDigits`: substitution of subprograms for operand digit
  queries, used for stage composition in Theorem 10.9.
* `Cslib.StreamArithmetic.CondBoolTree`: conditional binary Boolean circuit unfolded from its
  output gate (**Lemma 10.2**).

## Main results

* `Cslib.StreamArithmetic.QueryProg.eval_bindOverhead`,
  `activeQueries_bindOverhead`, `maxIntrinsicBits_bindOverhead_le`: exact semantics and lifetime
  accounting of sequential composition.
* `Cslib.StreamArithmetic.QueryProg.eval_substDigits`,
  `mem_activeQueries_substDigits`, `maxIntrinsicBits_substDigits_le`: exact semantics and
  suspended/intrinsic accounting under stage composition.
* `Cslib.StreamArithmetic.CondBoolTree.toQueryProg_retainedBits_le`: **Lemma 10.2** (`2` bits per
  ancestor gate on the active path).

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 10.1, Lemma 10.2 (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.StreamArithmetic

universe u u' v w w'

/-- An oracle query event executed along the active branch of a `QueryProg`, recording the
requested operand/place (or clock-zero structural leaf) and the total local bit-length suspended
across that query. -/
inductive QueryEvent (Op : Type u) (Struct : Type v) : Type (max u v)
  | digit (op : Op) (place : ℕ) (retainedBits : ℕ)
  | struct (sOp : Struct) (retainedBits : ℕ)
  deriving DecidableEq

/-- Add `extra` enclosing-frame bits to the suspended record of a `QueryEvent`. -/
@[expose] def QueryEvent.addBits {Op : Type u} {Struct : Type v} (extra : ℕ) :
    QueryEvent Op Struct → QueryEvent Op Struct
  | .digit op j w => .digit op j (extra + w)
  | .struct sOp w => .struct sOp (extra + w)

/-- Total suspended local record length recorded in a `QueryEvent`. -/
@[expose] def QueryEvent.retained {Op : Type u} {Struct : Type v} : QueryEvent Op Struct → ℕ
  | .digit _ _ w => w
  | .struct _ w => w

@[simp]
theorem QueryEvent.retained_addBits {Op : Type u} {Struct : Type v} (extra : ℕ)
    (ev : QueryEvent Op Struct) :
    (ev.addBits extra).retained = extra + ev.retained := by
  cases ev <;> rfl

/-- Deterministic finite conditional query program over operand streams `Op` and clock-zero
structural predicates `Struct`, returning `α`. Here `retainedBits` and `scratchBits` are
caller-supplied bit annotations on query suspensions and scratch steps, while continuations are
host Lean functions prior to native machine compilation. -/
inductive QueryProg (Op : Type u) (Struct : Type v) (α : Type w) : Type (max u v w)
  | ret (val : α)
  | scratchStep (scratchBits : ℕ) (next : QueryProg Op Struct α)
  | queryDigit (op : Op) (place : ℕ) (retainedBits : ℕ) (next : ℤ → QueryProg Op Struct α)
  | queryStruct (sOp : Struct) (retainedBits : ℕ) (next : Bool → QueryProg Op Struct α)

namespace QueryProg

variable {Op : Type u} {Struct : Type v}

/-- Evaluate a `QueryProg` against operand streams `env` and structural predicates `sEnv`. -/
@[expose] def eval {α : Type w} (prog : QueryProg Op Struct α) (env : Op → ℕ → ℤ)
    (sEnv : Struct → Bool) : α :=
  match prog with
  | .ret val => val
  | .scratchStep _ next => eval next env sEnv
  | .queryDigit op j _ next => eval (next (env op j)) env sEnv
  | .queryStruct sOp _ next => eval (next (sEnv sOp)) env sEnv

/-- Ordered trace of all oracle queries actually executed along `(env, sEnv)`, each tagged with
its live `retainedBits` at the moment of suspension. -/
@[expose] def activeQueries {α : Type w} (prog : QueryProg Op Struct α) (env : Op → ℕ → ℤ)
    (sEnv : Struct → Bool) : List (QueryEvent Op Struct) :=
  match prog with
  | .ret _ => []
  | .scratchStep _ next => activeQueries next env sEnv
  | .queryDigit op j w next => .digit op j w :: activeQueries (next (env op j)) env sEnv
  | .queryStruct sOp w next => .struct sOp w :: activeQueries (next (sEnv sOp)) env sEnv

/-- Peak intrinsic local + scratch bit-length reached anywhere along the active execution path of
`prog` on `(env, sEnv)`. -/
@[expose] def maxIntrinsicBits {α : Type w} (prog : QueryProg Op Struct α) (env : Op → ℕ → ℤ)
    (sEnv : Struct → Bool) : ℕ :=
  match prog with
  | .ret _ => 0
  | .scratchStep s next => max s (maxIntrinsicBits next env sEnv)
  | .queryDigit op j w next => max w (maxIntrinsicBits (next (env op j)) env sEnv)
  | .queryStruct sOp w next => max w (maxIntrinsicBits (next (sEnv sOp)) env sEnv)

/-- Host-level post-processing of the return value; preserves `activeQueries` and
`maxIntrinsicBits` without charging additional machine scratch. -/
@[expose] def map {α : Type w} {β : Type w'} (f : α → β) :
    QueryProg Op Struct α → QueryProg Op Struct β
  | .ret a => .ret (f a)
  | .scratchStep s next => .scratchStep s (map f next)
  | .queryDigit op j w next => .queryDigit op j w (fun d => map f (next d))
  | .queryStruct sOp w next => .queryStruct sOp w (fun b => map f (next b))

/-- Sequential composition charging `overheadBits` live frame bits throughout `p`, then popping
`p`'s frame before entering `k`. -/
@[expose] def bindOverhead {α : Type w} {β : Type w'} (overheadBits : ℕ)
    (p : QueryProg Op Struct α) (k : α → QueryProg Op Struct β) : QueryProg Op Struct β :=
  match p with
  | .ret a => k a
  | .scratchStep s next =>
      .scratchStep (overheadBits + s) (bindOverhead overheadBits next k)
  | .queryDigit op j w next =>
      .queryDigit op j (overheadBits + w) (fun d => bindOverhead overheadBits (next d) k)
  | .queryStruct sOp w next =>
      .queryStruct sOp (overheadBits + w) (fun b => bindOverhead overheadBits (next b) k)

@[simp]
theorem eval_map {α : Type w} {β : Type w'} (f : α → β) (p : QueryProg Op Struct α)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.map f).eval env sEnv = f (p.eval env sEnv) := by
  induction p with
  | ret a => rfl
  | scratchStep _ _ ih => exact ih
  | queryDigit _ _ _ _ ih => exact ih _
  | queryStruct _ _ _ ih => exact ih _

@[simp]
theorem activeQueries_map {α : Type w} {β : Type w'} (f : α → β) (p : QueryProg Op Struct α)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.map f).activeQueries env sEnv = p.activeQueries env sEnv := by
  induction p with
  | ret _ => rfl
  | scratchStep _ _ ih => exact ih
  | queryDigit _ _ _ _ ih => exact congrArg (_ :: ·) (ih _)
  | queryStruct _ _ _ ih => exact congrArg (_ :: ·) (ih _)

@[simp]
theorem maxIntrinsicBits_map {α : Type w} {β : Type w'} (f : α → β) (p : QueryProg Op Struct α)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.map f).maxIntrinsicBits env sEnv = p.maxIntrinsicBits env sEnv := by
  induction p with
  | ret _ => rfl
  | scratchStep _ _ ih => exact congrArg (max _) ih
  | queryDigit _ _ _ _ ih => exact congrArg (max _) (ih _)
  | queryStruct _ _ _ ih => exact congrArg (max _) (ih _)

@[simp]
theorem eval_bindOverhead {α : Type w} {β : Type w'} (ov : ℕ) (p : QueryProg Op Struct α)
    (k : α → QueryProg Op Struct β) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.bindOverhead ov k).eval env sEnv = (k (p.eval env sEnv)).eval env sEnv := by
  induction p with
  | ret _ => rfl
  | scratchStep _ _ ih => exact ih
  | queryDigit _ _ _ _ ih => exact ih _
  | queryStruct _ _ _ ih => exact ih _

/-- **Lifetime release theorem**: `p.bindOverhead ov k` adds `ov` bits only to queries inside `p`;
queries executed later inside `k (p.eval env sEnv)` inherit zero leftover bits from `p`. -/
theorem activeQueries_bindOverhead {α : Type w} {β : Type w'} (ov : ℕ) (p : QueryProg Op Struct α)
    (k : α → QueryProg Op Struct β) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.bindOverhead ov k).activeQueries env sEnv =
      (p.activeQueries env sEnv).map (QueryEvent.addBits ov) ++
        (k (p.eval env sEnv)).activeQueries env sEnv := by
  induction p with
  | ret _ => rfl
  | scratchStep _ _ ih => exact ih
  | queryDigit _ _ _ _ ih =>
    simp only [bindOverhead, activeQueries, eval, List.map_cons, List.cons_append]
    exact congrArg (_ :: ·) (ih _)
  | queryStruct _ _ _ ih =>
    simp only [bindOverhead, activeQueries, eval, List.map_cons, List.cons_append]
    exact congrArg (_ :: ·) (ih _)

theorem maxIntrinsicBits_bindOverhead_le {α : Type w} {β : Type w'} (ov : ℕ)
    (p : QueryProg Op Struct α) (k : α → QueryProg Op Struct β)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.bindOverhead ov k).maxIntrinsicBits env sEnv ≤
      max (ov + p.maxIntrinsicBits env sEnv) ((k (p.eval env sEnv)).maxIntrinsicBits env sEnv) := by
  induction p with
  | ret a =>
    simp only [bindOverhead, eval]
    exact le_max_right _ _
  | scratchStep s next ih =>
    simp only [bindOverhead, maxIntrinsicBits, eval]
    refine max_le ?_ (ih.trans ?_)
    · exact (Nat.add_le_add_left (le_max_left _ _) ov).trans (le_max_left _ _)
    · exact max_le_max (Nat.add_le_add_left (le_max_right _ _) ov) le_rfl
  | queryDigit op j w next ih =>
    simp only [bindOverhead, maxIntrinsicBits, eval]
    refine max_le ?_ ((ih (env op j)).trans ?_)
    · exact (Nat.add_le_add_left (le_max_left _ _) ov).trans (le_max_left _ _)
    · exact max_le_max (Nat.add_le_add_left (le_max_right _ _) ov) le_rfl
  | queryStruct sOp w next ih =>
    simp only [bindOverhead, maxIntrinsicBits, eval]
    refine max_le ?_ ((ih (sEnv sOp)).trans ?_)
    · exact (Nat.add_le_add_left (le_max_left _ _) ov).trans (le_max_left _ _)
    · exact max_le_max (Nat.add_le_add_left (le_max_right _ _) ov) le_rfl

theorem retained_le_maxIntrinsicBits {α : Type w} (prog : QueryProg Op Struct α)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ prog.activeQueries env sEnv) :
    ev.retained ≤ prog.maxIntrinsicBits env sEnv := by
  induction prog with
  | ret _ => nomatch hev
  | scratchStep _ _ ih =>
    exact (ih hev).trans (le_max_right _ _)
  | queryDigit op j w next ih =>
    simp only [activeQueries, List.mem_cons] at hev
    rcases hev with rfl | hev
    · exact le_max_left _ _
    · exact (ih (env op j) hev).trans (le_max_right _ _)
  | queryStruct sOp w next ih =>
    simp only [activeQueries, List.mem_cons] at hev
    rcases hev with rfl | hev
    · exact le_max_left _ _
    · exact (ih (sEnv sOp) hev).trans (le_max_right _ _)

/-- Substitute child query programs `child op u` (plus `digitReturnBits` return overhead) for every
operand digit query `(op, u)` in `prog`. Structural queries on `Struct` pass through unchanged. -/
@[expose] def substDigits {Op₂ : Type u'} {α : Type w} (digitReturnBits : ℕ)
    (prog : QueryProg Op Struct α) (child : Op → ℕ → QueryProg Op₂ Struct ℤ) :
    QueryProg Op₂ Struct α :=
  match prog with
  | .ret a => .ret a
  | .scratchStep s next => .scratchStep s (substDigits digitReturnBits next child)
  | .queryDigit op u w next =>
      bindOverhead (w + digitReturnBits) (child op u)
        (fun d => substDigits digitReturnBits (next d) child)
  | .queryStruct sOp w next =>
      .queryStruct sOp w (fun b => substDigits digitReturnBits (next b) child)

/-- Semantic soundness of `substDigits`: evaluating the composed program equals evaluating `prog`
against the stream environment produced by `child`. -/
theorem eval_substDigits {Op₂ : Type u'} {α : Type w} (retBits : ℕ)
    (prog : QueryProg Op Struct α) (child : Op → ℕ → QueryProg Op₂ Struct ℤ)
    (env₂ : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) :
    (prog.substDigits retBits child).eval env₂ sEnv =
      prog.eval (fun op u => (child op u).eval env₂ sEnv) sEnv := by
  induction prog with
  | ret _ => rfl
  | scratchStep _ _ ih => exact ih
  | queryDigit op u w next ih =>
    simp only [substDigits, eval_bindOverhead, eval]
    exact ih _
  | queryStruct sOp w next ih =>
    simp only [substDigits, eval]
    exact ih _

/-- Characterization of every oracle query emitted by `prog.substDigits retBits child`: it is
either a pass-through structural query of `prog`, or a query emitted by `child op u` for some
active digit query `(op, u, w)` of `prog` with `w + retBits` added to its suspended record. -/
theorem mem_activeQueries_substDigits {Op₂ : Type u'} {α : Type w} (retBits : ℕ)
    (prog : QueryProg Op Struct α) (child : Op → ℕ → QueryProg Op₂ Struct ℤ)
    (env₂ : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op₂ Struct}
    (hev : ev ∈ (prog.substDigits retBits child).activeQueries env₂ sEnv) :
    (∃ sOp w, QueryEvent.struct sOp w ∈ prog.activeQueries
        (fun op u => (child op u).eval env₂ sEnv) sEnv ∧ ev = .struct sOp w) ∨
      ∃ op u w evChild,
        QueryEvent.digit op u w ∈ prog.activeQueries
          (fun op u => (child op u).eval env₂ sEnv) sEnv ∧
        evChild ∈ (child op u).activeQueries env₂ sEnv ∧
        ev = evChild.addBits (w + retBits) := by
  set env₁ : Op → ℕ → ℤ := fun op u => (child op u).eval env₂ sEnv
  induction prog with
  | ret _ => nomatch hev
  | scratchStep _ _ ih => exact ih hev
  | queryDigit op u w next ih =>
    simp only [substDigits, activeQueries_bindOverhead, List.mem_append, List.mem_map] at hev
    rcases hev with ⟨evC, hevC, rfl⟩ | hevNext
    · right
      exact ⟨op, u, w, evC, List.mem_cons_self, hevC, rfl⟩
    · rcases ih ((child op u).eval env₂ sEnv) hevNext with
        ⟨sOp, ws, hs, rfl⟩ | ⟨op', u', w', evC, hd, hevC, rfl⟩
      · left
        exact ⟨sOp, ws, List.mem_cons_of_mem _ hs, rfl⟩
      · right
        exact ⟨op', u', w', evC, List.mem_cons_of_mem _ hd, hevC, rfl⟩
  | queryStruct sOp w next ih =>
    simp only [substDigits, activeQueries, List.mem_cons] at hev
    rcases hev with rfl | hevNext
    · left
      exact ⟨sOp, w, List.mem_cons_self, rfl⟩
    · rcases ih (sEnv sOp) hevNext with
        ⟨sOp', ws, hs, rfl⟩ | ⟨op', u', w', evC, hd, hevC, rfl⟩
      · left
        exact ⟨sOp', ws, List.mem_cons_of_mem _ hs, rfl⟩
      · right
        exact ⟨op', u', w', evC, List.mem_cons_of_mem _ hd, hevC, rfl⟩

/-- Bound on peak intrinsic local + scratch bits of `prog.substDigits retBits child`. -/
theorem maxIntrinsicBits_substDigits_le {Op₂ : Type u'} {α : Type w} (retBits : ℕ)
    (prog : QueryProg Op Struct α) (child : Op → ℕ → QueryProg Op₂ Struct ℤ)
    (env₂ : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) {M : ℕ}
    (hParent : prog.maxIntrinsicBits (fun op u => (child op u).eval env₂ sEnv) sEnv ≤ M)
    (hChild : ∀ op u w,
      QueryEvent.digit op u w ∈ prog.activeQueries
        (fun op u => (child op u).eval env₂ sEnv) sEnv →
      w + retBits + (child op u).maxIntrinsicBits env₂ sEnv ≤ M) :
    (prog.substDigits retBits child).maxIntrinsicBits env₂ sEnv ≤ M := by
  induction prog with
  | ret _ => exact Nat.zero_le M
  | scratchStep s next ih =>
    simp only [maxIntrinsicBits] at hParent
    simp only [substDigits, maxIntrinsicBits]
    exact max_le ((le_max_left _ _).trans hParent)
      (ih ((le_max_right _ _).trans hParent) hChild)
  | queryDigit op u w next ih =>
    simp only [maxIntrinsicBits] at hParent
    simp only [substDigits]
    refine (maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · exact hChild op u w List.mem_cons_self
    · refine ih _ ((le_max_right _ _).trans hParent) fun op' u' w' hmem => ?_
      exact hChild op' u' w' (List.mem_cons_of_mem _ hmem)
  | queryStruct sOp w next ih =>
    simp only [maxIntrinsicBits] at hParent
    simp only [substDigits, maxIntrinsicBits]
    refine max_le ((le_max_left _ _).trans hParent) ?_
    refine ih _ ((le_max_right _ _).trans hParent) fun op' u' w' hmem => ?_
    exact hChild op' u' w' (List.mem_cons_of_mem _ hmem)

end QueryProg

section RegeneratedGateEvaluation

/-- Bounded-fan-in conditional Boolean circuit unfolded from its output gate
[OpenAI2026LogSpace, Lemma 10.2]:
* constants `const b`,
* unary negation `notGate c`,
* binary `andGate c₁ c₂` and `orGate c₁ c₂`,
* conditional selector `condGate sel onTrue onFalse` (evaluates `sel` first, then only the
  selected branch),
* digit-bit leaf `digitBit op j bitPred` testing a Boolean predicate of digit `(op, j)`,
* structural leaf `structLeaf sOp`. -/
inductive CondBoolTree (Op : Type u) (Struct : Type v) : Type (max u v)
  | const (b : Bool)
  | notGate (child : CondBoolTree Op Struct)
  | andGate (left right : CondBoolTree Op Struct)
  | orGate (left right : CondBoolTree Op Struct)
  | condGate (sel onTrue onFalse : CondBoolTree Op Struct)
  | digitBit (op : Op) (place : ℕ) (bitPred : ℤ → Bool)
  | structLeaf (sOp : Struct)

namespace CondBoolTree

variable {Op : Type u} {Struct : Type v}

/-- Direct mathematical Boolean evaluation of a `CondBoolTree`. -/
@[expose] def eval (tree : CondBoolTree Op Struct) (env : Op → ℕ → ℤ)
    (sEnv : Struct → Bool) : Bool :=
  match tree with
  | .const b => b
  | .notGate c => !(c.eval env sEnv)
  | .andGate l r => l.eval env sEnv && r.eval env sEnv
  | .orGate l r => l.eval env sEnv || r.eval env sEnv
  | .condGate sel t f => if sel.eval env sEnv then t.eval env sEnv else f.eval env sEnv
  | .digitBit op j pred => pred (env op j)
  | .structLeaf sOp => sEnv sOp

/-- Longest root-to-leaf syntactic depth of a `CondBoolTree`. -/
@[expose] def depth : CondBoolTree Op Struct → ℕ
  | .const _ => 0
  | .notGate c => c.depth + 1
  | .andGate l r => max l.depth r.depth + 1
  | .orGate l r => max l.depth r.depth + 1
  | .condGate s t f => max s.depth (max t.depth f.depth) + 1
  | .digitBit _ _ _ => 0
  | .structLeaf _ => 0

/-- Depth-first evaluation of a `CondBoolTree` annotated with `regenScratch` shared scratch bits
for path-based gate-address regeneration [OpenAI2026LogSpace, Lemma 10.2]. Each active ancestor
gate charges `2` retained bits (child mode + at most one saved Boolean value) without storing
absolute gate addresses; uniform realization of `regenScratch` and leaf predicates belongs to
downstream machine compilation. -/
@[expose] def toQueryProg (regenScratch : ℕ) :
    CondBoolTree Op Struct → QueryProg Op Struct Bool
  | .const b => .scratchStep regenScratch (.ret b)
  | .notGate c =>
      .scratchStep regenScratch ((c.toQueryProg regenScratch).bindOverhead 2 (fun b => .ret (!b)))
  | .andGate l r =>
      .scratchStep regenScratch
        ((l.toQueryProg regenScratch).bindOverhead 2 fun b₁ =>
          (r.toQueryProg regenScratch).bindOverhead 2 fun b₂ => .ret (b₁ && b₂))
  | .orGate l r =>
      .scratchStep regenScratch
        ((l.toQueryProg regenScratch).bindOverhead 2 fun b₁ =>
          (r.toQueryProg regenScratch).bindOverhead 2 fun b₂ => .ret (b₁ || b₂))
  | .condGate sel t f =>
      .scratchStep regenScratch
        ((sel.toQueryProg regenScratch).bindOverhead 2 fun b =>
          if b then
            (t.toQueryProg regenScratch).bindOverhead 2 QueryProg.ret
          else
            (f.toQueryProg regenScratch).bindOverhead 2 QueryProg.ret)
  | .digitBit op j pred =>
      .scratchStep regenScratch (.queryDigit op j 0 fun d => .ret (pred d))
  | .structLeaf sOp =>
      .scratchStep regenScratch (.queryStruct sOp 0 QueryProg.ret)

/-- **Lemma 10.2 (correctness of regenerated gate evaluation)**
[OpenAI2026LogSpace, Lemma 10.2]. -/
@[simp]
theorem toQueryProg_eval (regenScratch : ℕ) (tree : CondBoolTree Op Struct)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (tree.toQueryProg regenScratch).eval env sEnv = tree.eval env sEnv := by
  induction tree with
  | const b => rfl
  | notGate c ih => simp [toQueryProg, eval, QueryProg.eval, ih]
  | andGate l r ihl ihr | orGate l r ihl ihr => simp [toQueryProg, eval, QueryProg.eval, ihl, ihr]
  | condGate s t f ihs iht ihf =>
    simp only [toQueryProg, eval, QueryProg.eval, QueryProg.eval_bindOverhead, ihs]
    cases s.eval env sEnv <;> simp [QueryProg.eval_bindOverhead, QueryProg.eval, iht, ihf]
  | digitBit op j pred => rfl
  | structLeaf sOp => rfl

/-- **Lemma 10.2 (suspended local record bound)** [OpenAI2026LogSpace, Lemma 10.2]: every leaf
query executed during `tree.toQueryProg regenScratch` retains at most `2 * tree.depth` annotated
suspended bits (`O(1)` bits per gate along the active path, zero saved gate addresses, and zero
bits from unselected conditional branches or completed sibling subtrees). -/
theorem toQueryProg_retainedBits_le (regenScratch : ℕ) (tree : CondBoolTree Op Struct)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (tree.toQueryProg regenScratch).activeQueries env sEnv) :
    ev.retained ≤ 2 * tree.depth := by
  induction tree generalizing ev with
  | const _ => nomatch hev
  | notGate c ih =>
    simp only [toQueryProg, QueryProg.activeQueries, QueryProg.activeQueries_bindOverhead,
      List.append_nil, List.mem_map] at hev
    obtain ⟨ev₀, hev₀, rfl⟩ := hev
    rw [QueryEvent.retained_addBits, depth]
    have h := ih hev₀
    omega
  | andGate l r ihl ihr | orGate l r ihl ihr =>
    simp only [toQueryProg, QueryProg.activeQueries, QueryProg.activeQueries_bindOverhead,
      List.append_nil, List.mem_append, List.mem_map] at hev
    rw [depth]
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | ⟨ev₀, hev₀, rfl⟩
    · rw [QueryEvent.retained_addBits]
      have h := ihl hev₀
      have hle : l.depth ≤ max l.depth r.depth := le_max_left _ _
      omega
    · rw [QueryEvent.retained_addBits]
      have h := ihr hev₀
      have hle : r.depth ≤ max l.depth r.depth := le_max_right _ _
      omega
  | condGate s t f ihs iht ihf =>
    simp only [toQueryProg, QueryProg.activeQueries, QueryProg.activeQueries_bindOverhead,
      toQueryProg_eval, List.mem_append, List.mem_map] at hev
    rw [depth]
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | hevBranch
    · rw [QueryEvent.retained_addBits]
      have h := ihs hev₀
      have hle : s.depth ≤ max s.depth (max t.depth f.depth) := le_max_left _ _
      omega
    · cases hs : s.eval env sEnv
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, QueryProg.activeQueries_bindOverhead,
          QueryProg.activeQueries, List.append_nil, List.mem_map] at hevBranch
        obtain ⟨ev₀, hev₀, rfl⟩ := hevBranch
        rw [QueryEvent.retained_addBits]
        have h := ihf hev₀
        have hle : f.depth ≤ max s.depth (max t.depth f.depth) :=
          (le_max_right _ _).trans (le_max_right _ _)
        omega
      · simp only [hs, ↓reduceIte, QueryProg.activeQueries_bindOverhead,
          QueryProg.activeQueries, List.append_nil, List.mem_map] at hevBranch
        obtain ⟨ev₀, hev₀, rfl⟩ := hevBranch
        rw [QueryEvent.retained_addBits]
        have h := iht hev₀
        have hle : t.depth ≤ max s.depth (max t.depth f.depth) :=
          (le_max_left _ _).trans (le_max_right _ _)
        omega
  | digitBit op j pred | structLeaf sOp =>
    simp only [toQueryProg, QueryProg.activeQueries, List.mem_singleton] at hev
    subst hev
    simp [QueryEvent.retained, depth]

/-- **Lemma 10.2 (intrinsic local + scratch bound)** [OpenAI2026LogSpace, Lemma 10.2]: given the
caller-supplied `regenScratch` annotation, the peak annotated intrinsic local + scratch storage
during `tree.toQueryProg regenScratch` is at most `regenScratch + 2 * tree.depth`. -/
theorem toQueryProg_intrinsic_le (regenScratch : ℕ) (tree : CondBoolTree Op Struct)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (tree.toQueryProg regenScratch).maxIntrinsicBits env sEnv ≤ regenScratch + 2 * tree.depth := by
  induction tree with
  | const _ => simp [toQueryProg, QueryProg.maxIntrinsicBits, depth]
  | notGate c ih =>
    simp only [toQueryProg, QueryProg.maxIntrinsicBits, depth]
    refine max_le (Nat.le_add_right _ _) ?_
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · omega
    · simp [QueryProg.maxIntrinsicBits]
  | andGate l r ihl ihr | orGate l r ihl ihr =>
    simp only [toQueryProg, QueryProg.maxIntrinsicBits, depth]
    have hl : l.depth ≤ max l.depth r.depth := le_max_left _ _
    have hr : r.depth ≤ max l.depth r.depth := le_max_right _ _
    refine max_le (Nat.le_add_right _ _) ?_
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · omega
    · refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
      · omega
      · simp [QueryProg.maxIntrinsicBits]
  | condGate s t f ihs iht ihf =>
    simp only [toQueryProg, QueryProg.maxIntrinsicBits, depth]
    have hs_le : s.depth ≤ max s.depth (max t.depth f.depth) := le_max_left _ _
    have ht_le : t.depth ≤ max s.depth (max t.depth f.depth) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hf_le : f.depth ≤ max s.depth (max t.depth f.depth) :=
      (le_max_right _ _).trans (le_max_right _ _)
    refine max_le (Nat.le_add_right _ _) ?_
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · omega
    · rw [toQueryProg_eval]
      -- Either selected branch is a `bindOverhead` around a child bounded by its hypothesis.
      cases s.eval env sEnv <;>
        exact (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans
          (max_le (by omega) (by simp [QueryProg.maxIntrinsicBits]))
  | digitBit _ _ _ | structLeaf _ =>
    simp [toQueryProg, QueryProg.maxIntrinsicBits, depth]

end CondBoolTree

end RegeneratedGateEvaluation

end Cslib.StreamArithmetic
