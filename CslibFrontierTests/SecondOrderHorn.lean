/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Gradel
public import Mathlib.ModelTheory.Graph
import CslibFrontier.Tactic.FirstOrder

/-! # SO∃-Horn definability of an ordered parity query

`evenLoops` is an SO∃-Horn sentence over directed graphs with successor. Its clauses walk the
universe along successor and derive `R b x` when the number of self-loops at points up to `x` has
parity `b`. A goal clause rejects odd parity at the greatest point. Every guard is
quantifier-free, and the step clauses use the primitive successor. Its intended reading is "the
number of self-loops is even"; only the two instances below are checked, not that reading in
general.

On `Fin 3`, the graph with loops at `0` and `2` satisfies the sentence and the graph with one loop
at `1` does not, so the defined query is neither empty nor full. -/

@[expose] public section

namespace Cslib.Tests.SecondOrderHorn

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Cslib.Complexity

/-- The guard vocabulary: directed graphs with order, BIT, the numeric constants and successor. -/
abbrev G : Language := language (succLanguage Language.graph)

/-- `loop t` says that the point `t` carries a self-loop. -/
abbrev loop {α : Type} (t : G.Term α) : G.Formula α :=
  Relations.formula₂ ((LHom.sumInl : succLanguage Language.graph →ᴸ G).onRelation
    ((LHom.sumInl : Language.graph →ᴸ succLanguage Language.graph).onRelation Language.adj)) t t

/-- `loopIs b t` says that `t` carries a self-loop exactly when `b` is `true`. -/
abbrev loopIs {α : Type} (b : Bool) (t : G.Term α) : G.Formula α :=
  if b then loop t else (loop t).not

/-- One unary relation variable per parity. -/
abbrev arity : Bool → ℕ := fun _ => 1

/-- The atom `R b x`. -/
abbrev atom {k : ℕ} (b : Bool) (i : Fin k) : ESO.Horn.Atom arity (Fin k) := ⟨b, ![i]⟩

/-- `x = 0 ∧ loopIs b x → R b x`. -/
noncomputable def start (b : Bool) : ESO.Horn.Clause G arity where
  width := 1
  guard := Term.equal (.var 0) (zero _) ⊓ loopIs b (.var 0)
  body := []
  head := some (atom b 0)

/-- `succ x y ∧ loopIs c y ∧ R b x → R (b xor c) y`. -/
noncomputable def step (b c : Bool) : ESO.Horn.Clause G arity where
  width := 2
  guard := succ _ (.var 0) (.var 1) ⊓ loopIs c (.var 1)
  body := [atom b 0]
  head := some (atom (b ^^ c) 1)

/-- `x = max ∧ R true x → ⊥`. -/
noncomputable def goal : ESO.Horn.Clause G arity where
  width := 1
  guard := Term.equal (.var 0) (max _)
  body := [atom true 0]
  head := none

/-- The SO∃-Horn sentence intended to say "the number of self-loops is even". -/
noncomputable def evenLoops : ESO.Horn.Sentence G where
  Var := Bool
  arity := arity
  clauses := [start false, start true, step false false, step false true, step true false,
    step true true, goal]

theorem start_isQF (b : Bool) : (start b).guard.IsQF := by
  change (Term.equal (.var 0) (zero _) ⊓ loopIs b (.var 0) : G.Formula (Fin 1)).IsQF
  fo_qf

theorem step_isQF (b c : Bool) : (step b c).guard.IsQF := by
  change (succ _ (.var 0) (.var 1) ⊓ loopIs c (.var 1) : G.Formula (Fin 2)).IsQF
  fo_qf

theorem goal_isQF : goal.guard.IsQF := by
  change (Term.equal (.var 0) (max _) : G.Formula (Fin 1)).IsQF
  fo_qf

/-- Every guard of `evenLoops` is quantifier-free. -/
theorem evenLoops_isQF : evenLoops.IsQF := by
  change ∀ C ∈ [start false, start true, step false false, step false true, step true false,
    step true true, goal], C.guard.IsQF
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨start_isQF _, start_isQF _, step_isQF _ _, step_isQF _ _, step_isQF _ _, step_isQF _ _,
    goal_isQF⟩

/-! ### Concrete structures -/

/-- The directed graph on `Fin n` with a self-loop at each point selected by `s` and no other
edges. -/
def loopGraph (n : ℕ) (hn : 2 ≤ n) (s : Fin n → Bool) : Ordered.Structure Language.graph where
  size := n
  size_ge_two := hn
  input.RelMap
    | .adj, xs => xs 0 = xs 1 ∧ s (xs 0) = true

variable {n : ℕ} {hn : 2 ≤ n} {s : Fin n → Bool}

theorem realize_loop {α : Type} (t : G.Term α) (v : α → loopGraph n hn s) :
    (loop t).Realize v ↔ s (t.realize (M := loopGraph n hn s) v) = true := by
  rw [loop, Formula.realize_rel₂]
  change (Term.realize (M := loopGraph n hn s) v t = Term.realize v t ∧ _) ↔ _
  exact and_iff_right rfl

theorem realize_loopIs {α : Type} (b : Bool) (t : G.Term α) (v : α → loopGraph n hn s) :
    (loopIs b t).Realize v ↔ s (t.realize (M := loopGraph n hn s) v) = b := by
  cases b
  · change ¬(loop t).Realize v ↔ _
    rw [realize_loop, Bool.not_eq_true]
  · exact realize_loop t v

theorem holds_atom {k : ℕ} (b : Bool) (i : Fin k) (R : Bool → Set (Fin 1 → loopGraph n hn s))
    (v : Fin k → loopGraph n hn s) : (atom b i).Holds R v ↔ ![v i] ∈ R b := by
  change v ∘ ![i] ∈ R b ↔ _
  rw [show v ∘ ![i] = ![v i] from funext fun j => by fin_cases j; rfl]

theorem holds_start (b : Bool) (R : Bool → Set (Fin 1 → loopGraph n hn s)) :
    (start b).Holds R ↔ ∀ x : loopGraph n hn s, x.val = 0 → s x = b → ![x] ∈ R b := by
  change (∀ v : Fin 1 → loopGraph n hn s,
    (Term.equal (.var 0) (zero _) ⊓ loopIs b (.var 0) : G.Formula (Fin 1)).Realize v →
      (∀ a ∈ ([] : List (ESO.Horn.Atom arity (Fin 1))), a.Holds R v) → (atom b 0).Holds R v) ↔ _
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Formula.realize_inf,
    Formula.realize_equal, realize_loopIs, Term.realize_var, Fin.cons_zero, Fin.ext_iff,
    realize_zero_val, List.not_mem_nil, IsEmpty.forall_iff, implies_true, true_implies,
    holds_atom, and_imp]

theorem holds_step (b c : Bool) (R : Bool → Set (Fin 1 → loopGraph n hn s)) :
    (step b c).Holds R ↔ ∀ x y : loopGraph n hn s, x.val + 1 = y.val → s y = c →
      ![x] ∈ R b → ![y] ∈ R (b ^^ c) := by
  change (∀ v : Fin 2 → loopGraph n hn s,
    (succ _ (.var 0) (.var 1) ⊓ loopIs c (.var 1) : G.Formula (Fin 2)).Realize v →
      (∀ a ∈ [atom b 0], a.Holds R v) → (atom (b ^^ c) 1).Holds R v) ↔ _
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Formula.realize_inf,
    FO.Ordered.realize_succ, realize_loopIs, Term.realize_var, Fin.cons_zero, Fin.cons_one,
    List.mem_singleton, forall_eq, holds_atom, and_imp]

theorem holds_goal (R : Bool → Set (Fin 1 → loopGraph n hn s)) :
    goal.Holds R ↔ ∀ x : loopGraph n hn s, x.val = n - 1 → ![x] ∉ R true := by
  change (∀ v : Fin 1 → loopGraph n hn s,
    (Term.equal (.var 0) (max _) : G.Formula (Fin 1)).Realize v →
      (∀ a ∈ [atom true 0], a.Holds R v) → False) ↔ _
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Formula.realize_equal,
    Term.realize_var, Fin.cons_zero, Fin.ext_iff, realize_max_val, List.mem_singleton, forall_eq,
    holds_atom, imp_false]
  exact Iff.rfl

/-- `evenLoops` holds in a loop graph exactly when some parity relations satisfy its start, step
and goal clauses. -/
theorem realize_evenLoops_iff : evenLoops.Realize (loopGraph n hn s) ↔
    ∃ R : Bool → Set (Fin 1 → loopGraph n hn s), (∀ b, (start b).Holds R) ∧
      (∀ b c, (step b c).Holds R) ∧ goal.Holds R := by
  refine exists_congr fun R => ?_
  change (∀ C ∈ [start false, start true, step false false, step false true, step true false,
    step true true, goal], ESO.Horn.Clause.Holds C R) ↔ _
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Bool.forall_bool]
  tauto

/-! ### Both sides of the query -/

/-- Loops at `0` and `2`: an even number. -/
def twoLoops : Ordered.Structure Language.graph := loopGraph 3 (by decide) ![true, false, true]

/-- One loop, at `1`: an odd number. -/
def oneLoop : Ordered.Structure Language.graph := loopGraph 3 (by decide) ![false, true, false]

/-- The parity relations of `twoLoops`: the prefix parity is odd at `0` and `1` and even at
`2`. -/
theorem evenLoops_realize_twoLoops : evenLoops.Realize twoLoops := by
  refine realize_evenLoops_iff.2 ⟨fun b => {x | b = decide ((x 0).val < 2)}, ?_, ?_, ?_⟩
  · intro b
    rw [holds_start]
    change ∀ x : Fin 3, x.val = 0 → ![true, false, true] x = b → b = decide (x.val < 2)
    revert b
    decide
  · intro b c
    rw [holds_step]
    change ∀ x y : Fin 3, x.val + 1 = y.val → ![true, false, true] y = c →
      b = decide (x.val < 2) → (b ^^ c) = decide (y.val < 2)
    revert b c
    decide
  · rw [holds_goal]
    change ∀ x : Fin 3, x.val = 3 - 1 → ¬true = decide (x.val < 2)
    decide

theorem not_evenLoops_realize_oneLoop : ¬evenLoops.Realize oneLoop := by
  rintro h
  obtain ⟨R, hs, hst, hg⟩ := realize_evenLoops_iff.1 h
  have h0 : ![(0 : Fin 3)] ∈ R false := (holds_start false R).1 (hs false) (0 : Fin 3)
    (by decide) (by decide)
  have h1 : ![(1 : Fin 3)] ∈ R true := (holds_step false true R).1 (hst false true) (0 : Fin 3)
    (1 : Fin 3) (by decide) (by decide) h0
  have h2 : ![(2 : Fin 3)] ∈ R true := (holds_step true false R).1 (hst true false) (1 : Fin 3)
    (2 : Fin 3) (by decide) (by decide) h1
  exact (holds_goal R).1 hg (2 : Fin 3) (by decide) h2

/-- The ordered query defined by `evenLoops`. -/
def evenLoopsQuery : Query Language.graph := {M | evenLoops.Realize M}

example : HornDefinable evenLoopsQuery := ⟨evenLoops, evenLoops_isQF, fun _ => Iff.rfl⟩

example : twoLoops ∈ evenLoopsQuery := evenLoops_realize_twoLoops

example : oneLoop ∉ evenLoopsQuery := not_evenLoops_realize_oneLoop

/-! ### The upper bound and the ESO embedding -/

example : LFPDefinable evenLoopsQuery :=
  HornDefinable.lfpDefinable ⟨evenLoops, evenLoops_isQF, fun _ => Iff.rfl⟩

example : ESODefinable evenLoopsQuery :=
  HornDefinable.esoDefinable ⟨evenLoops, evenLoops_isQF, fun _ => Iff.rfl⟩

/-- The graph vocabulary with its single binary relation. -/
def graphVocabulary : Vocabulary Language.graph where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, .adj⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun ⟨_, .adj⟩ => rfl }

/-- Even loop parity is decidable in polynomial time, by Grädel's upper bound. -/
example : evenLoopsQuery.encodedLanguage graphVocabulary ∈ P encStructure :=
  HornDefinable.encodedLanguage_mem_P ⟨evenLoops, evenLoops_isQF, fun _ => Iff.rfl⟩ _

/-- The SO∃-Horn sentence and its ESO translation agree, on a model and on a non-model. -/
example : evenLoops.toESO.Realize twoLoops ∧ ¬evenLoops.toESO.Realize oneLoop := by
  rw [ESO.Horn.Sentence.realize_toESO, ESO.Horn.Sentence.realize_toESO]
  exact ⟨evenLoops_realize_twoLoops, not_evenLoops_realize_oneLoop⟩

/-- Truth is decided by the least model. -/
example : evenLoops.Consistent (evenLoops.leastModel twoLoops) :=
  evenLoops.realize_iff_leastModel.1 evenLoops_realize_twoLoops

/-- Successor elimination keeps the meaning on both structures. -/
example : evenLoops.elimSucc.Realize twoLoops ∧ ¬evenLoops.elimSucc.Realize oneLoop := by
  rw [ESO.Horn.Sentence.realize_elimSucc, ESO.Horn.Sentence.realize_elimSucc]
  exact ⟨evenLoops_realize_twoLoops, not_evenLoops_realize_oneLoop⟩

end Cslib.Tests.SecondOrderHorn
