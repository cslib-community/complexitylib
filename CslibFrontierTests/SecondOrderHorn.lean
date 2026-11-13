/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Gradel
public import CslibFrontier.Computability.Complexity.Gradel.Tableau
public import CslibFrontier.Logics.SecondOrder.Horn.GuardElimination
public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.Horn
public import Mathlib.ModelTheory.Graph
import CslibFrontier.Logics.FirstOrder.Encoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Tactic.FirstOrder

/-! # SO∃-Horn definability, guard elimination, full-tuple pullback, and Grädel's theorem

`evenLoops` is an SO∃-Horn sentence over directed graphs with successor. Its clauses walk the
universe along successor and derive `R b x` when the number of self-loops at points up to `x` has
parity `b`. A goal clause rejects odd parity at the greatest point. Every guard is
quantifier-free, and the step clauses use the primitive successor. Its intended reading is "the
number of self-loops is even"; only the instances below are checked, not that reading in general.

On `Fin 3`, the graph with loops at `0` and `2` satisfies the sentence and the graph with one loop
at `1` does not, so the defined query is neither empty nor full.

The second part tests `ESO.Horn.Sentence.elimGuards` and `hornDefinable_iff_exists_sentence` on a
sentence `sinkFreeHorn` whose guard contains nested `∀` and `∃` quantifiers (`¬ ∀ x, ∃ y, adj x y`),
checking both positive and negative structures at `n = 2` and `n = 3`. The third part tests
`FullTupleInterpretation.onHornSentence` at dimension `k = 2` on concrete positive and negative
structures. The fourth part tests `HornDefinable.of_encodedLanguage_mem_P` and
`hornDefinable_iff_encodedLanguage_mem_P` end-to-end on native polynomial-time deciders, alongside
positive and negative machine controls for `Gradel.Tableau.acceptanceHornSentence`. -/

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

section LoopGraph

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

end LoopGraph

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

/-! ### Guard elimination on nested `∀` and `∃` quantifiers -/

/-- Graph adjacency as a relation symbol of `language Language.graph`. -/
abbrev ordAdj : (language Language.graph).Relations 2 := Sum.inl Language.adj

/-- Width-`0` guard with nested `∀` and `∃` quantifiers: `¬ ∀ x, ∃ y, adj x y`. -/
noncomputable def hasSinkGuard : (language Language.graph).Formula (Fin 0) :=
  (∀' ∃' (ordAdj.boundedFormula₂ &0 &1)).not

/-- Nullary relation signature for `sinkFreeHorn` and `sinkFreeSucc`. -/
abbrev nullaryArity : Unit → ℕ := fun _ => 0

/-- An SO∃-Horn sentence over `language Language.graph` with a nullary relation variable and a
nested `∀`/`∃` guard: `hasSinkGuard → R()` and `R() → ⊥`, holding iff every vertex has an outgoing
edge. -/
noncomputable def sinkFreeHorn : ESO.Horn.Sentence (language Language.graph) where
  Var := Unit
  arity := nullaryArity
  clauses :=
    [ { width := 0
        guard := hasSinkGuard
        body := []
        head := some ⟨(), Fin.elim0⟩ },
      { width := 0
        guard := ⊤
        body := [⟨(), Fin.elim0⟩]
        head := none } ]

/-- Lift `sinkFreeHorn` to `G = language (succLanguage Language.graph)` while keeping its
quantified guard. -/
noncomputable def sinkFreeSucc : ESO.Horn.Sentence G where
  Var := Unit
  arity := nullaryArity
  clauses :=
    [ { width := 0
        guard := (succInclusion Language.graph).onFormula hasSinkGuard
        body := []
        head := some ⟨(), Fin.elim0⟩ },
      { width := 0
        guard := ⊤
        body := [⟨(), Fin.elim0⟩]
        head := none } ]

theorem realize_sinkFreeSucc_iff {m : ℕ} [Fact (2 ≤ m)] [Language.graph.Structure (Fin m)] :
    sinkFreeSucc.Realize (Fin m) ↔ sinkFreeHorn.Realize (Fin m) := by
  refine exists_congr fun R => ?_
  let R₀ : ∀ i : Unit, Set (Fin (nullaryArity i) → Fin m) := R
  change (∀ C ∈ [_, _], ESO.Horn.Clause.Holds C R₀) ↔
    ∀ C ∈ [_, _], ESO.Horn.Clause.Holds C R₀
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine and_congr ?_ Iff.rfl
  exact forall_congr' fun v => imp_congr (realize_succInclusion hasSinkGuard v) Iff.rfl

theorem realize_hasSinkGuard {m : ℕ} [Fact (2 ≤ m)] [Language.graph.Structure (Fin m)]
    (v : Fin 0 → Fin m) :
    hasSinkGuard.Realize v ↔
      ¬ ∀ x : Fin m, ∃ y : Fin m, RelMap (L := Language.graph) .adj ![x, y] := by
  simp only [hasSinkGuard, Formula.Realize, BoundedFormula.realize_not, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_rel₂]
  rfl

theorem realize_sinkFreeHorn {m : ℕ} [Fact (2 ≤ m)] [Language.graph.Structure (Fin m)] :
    sinkFreeHorn.Realize (Fin m) ↔
      ∀ x : Fin m, ∃ y : Fin m, RelMap (L := Language.graph) .adj ![x, y] := by
  constructor
  · rintro ⟨R, hR⟩
    have hdef := hR _ List.mem_cons_self
    have hgoal := hR _ (List.mem_cons_of_mem _ List.mem_cons_self)
    by_contra hnot
    have hmem : (Fin.elim0 ∘ Fin.elim0) ∈ R () :=
      hdef Fin.elim0 ((realize_hasSinkGuard Fin.elim0).mpr hnot) fun _ ha => nomatch ha
    exact hgoal Fin.elim0 (Formula.realize_top.mpr trivial)
      (List.forall_mem_singleton.mpr hmem)
  · intro hall
    refine ⟨fun _ => ∅, fun C hC => ?_⟩
    rcases List.mem_cons.mp hC with rfl | hC
    · intro v hg _
      exact False.elim (((realize_hasSinkGuard v).mp hg) hall)
    · obtain rfl := List.mem_singleton.mp hC
      intro v _ hb
      exact hb _ List.mem_cons_self

/-- Before `elimGuards`, `sinkFreeSucc` is genuinely not quantifier-free. -/
theorem not_isQF_sinkFreeSucc : ¬ sinkFreeSucc.IsQF := by
  intro hqf
  have h0 := hqf _ List.mem_cons_self
  change ((succInclusion Language.graph).onFormula hasSinkGuard).IsQF at h0
  cases h0 with
  | of_isAtomic ha => cases ha
  | imp h₁ _ =>
    cases h₁ with
    | of_isAtomic ha => cases ha

/-- `elimGuards` produces a quantifier-free SO∃-Horn sentence. -/
example : sinkFreeSucc.elimGuards.IsQF := sinkFreeSucc.isQF_elimGuards

/-- Positive `Fin 2` instance: loops at both `0` and `1`. -/
def twoLoops2 : Ordered.Structure Language.graph := loopGraph 2 (by decide) ![true, true]

/-- Negative `Fin 2` instance: loop at `0`, sink at `1`. -/
def oneLoop2 : Ordered.Structure Language.graph := loopGraph 2 (by decide) ![true, false]

/-- Positive `Fin 3` instance: loops at `0`, `1`, and `2`. -/
def allLoops3 : Ordered.Structure Language.graph := loopGraph 3 (by decide) ![true, true, true]

theorem elimGuards_sinkFreeSucc_twoLoops2 : sinkFreeSucc.elimGuards.Realize twoLoops2 := by
  rw [ESO.Horn.Sentence.realize_elimGuards, realize_sinkFreeSucc_iff, realize_sinkFreeHorn]
  intro x
  exact ⟨x, rfl, by fin_cases x <;> rfl⟩

theorem not_elimGuards_sinkFreeSucc_oneLoop2 : ¬ sinkFreeSucc.elimGuards.Realize oneLoop2 := by
  rw [ESO.Horn.Sentence.realize_elimGuards, realize_sinkFreeSucc_iff, realize_sinkFreeHorn]
  intro hall
  obtain ⟨_, _, hs⟩ := hall (1 : Fin 2)
  exact Bool.false_ne_true hs

theorem elimGuards_sinkFreeSucc_allLoops3 : sinkFreeSucc.elimGuards.Realize allLoops3 := by
  rw [ESO.Horn.Sentence.realize_elimGuards, realize_sinkFreeSucc_iff, realize_sinkFreeHorn]
  intro x
  exact ⟨x, rfl, by fin_cases x <;> rfl⟩

theorem not_elimGuards_sinkFreeSucc_twoLoops : ¬ sinkFreeSucc.elimGuards.Realize twoLoops := by
  rw [ESO.Horn.Sentence.realize_elimGuards, realize_sinkFreeSucc_iff, realize_sinkFreeHorn]
  intro hall
  obtain ⟨_, _, hs⟩ := hall (1 : Fin 3)
  exact Bool.false_ne_true hs

/-- Round-trip test: eliminating successor from `evenLoops`, lifting back to `G`, and eliminating
quantifiers yields a quantifier-free sentence agreeing on `twoLoops` and `oneLoop`. -/
example :
    let Φ := (evenLoops.elimSucc.mapGuards (succInclusion Language.graph).onFormula).elimGuards
    Φ.IsQF ∧ Φ.Realize twoLoops ∧ ¬ Φ.Realize oneLoop := by
  refine ⟨ESO.Horn.Sentence.isQF_elimGuards _, ?_, ?_⟩
  · rw [ESO.Horn.Sentence.realize_elimGuards,
      ESO.Horn.Sentence.realize_mapGuards _ fun φ v => realize_succInclusion φ v,
      ESO.Horn.Sentence.realize_elimSucc]
    exact evenLoops_realize_twoLoops
  · rw [ESO.Horn.Sentence.realize_elimGuards,
      ESO.Horn.Sentence.realize_mapGuards _ fun φ v => realize_succInclusion φ v,
      ESO.Horn.Sentence.realize_elimSucc]
    exact not_evenLoops_realize_oneLoop

/-- Ordered query defined directly by `sinkFreeHorn` (without successor, with nested
quantifiers). -/
def sinkFreeQuery : Query Language.graph := {M | sinkFreeHorn.Realize M}

/-- `hornDefinable_iff_exists_sentence` establishes `HornDefinable` from an arbitrary-guard
sentence over `language Language.graph`. -/
theorem sinkFreeQuery_hornDefinable : HornDefinable sinkFreeQuery :=
  hornDefinable_iff_exists_sentence.mpr ⟨sinkFreeHorn, fun _ => Iff.rfl⟩

example : twoLoops2 ∈ sinkFreeQuery ∧ oneLoop2 ∉ sinkFreeQuery ∧
    allLoops3 ∈ sinkFreeQuery ∧ twoLoops ∉ sinkFreeQuery := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (realize_sinkFreeHorn (m := twoLoops2.size)).mpr fun x =>
      ⟨x, rfl, by fin_cases x <;> rfl⟩
  · exact fun h => by
      obtain ⟨_, _, hs⟩ := (realize_sinkFreeHorn (m := oneLoop2.size)).mp h (1 : Fin 2)
      exact Bool.false_ne_true hs
  · exact (realize_sinkFreeHorn (m := allLoops3.size)).mpr fun x =>
      ⟨x, rfl, by fin_cases x <;> rfl⟩
  · exact fun h => by
      obtain ⟨_, _, hs⟩ := (realize_sinkFreeHorn (m := twoLoops.size)).mp h (1 : Fin 3)
      exact Bool.false_ne_true hs

example : sinkFreeQuery.encodedLanguage graphVocabulary ∈ P encStructure :=
  sinkFreeQuery_hornDefinable.encodedLanguage_mem_P graphVocabulary

/-! ### Full-tuple pullback of SO∃-Horn sentences (`k = 2`) -/

/-- Two-dimensional graph interpretation: pairs `(a₀, a₁)` and `(b₀, b₁)` are adjacent iff `a₀` and
`b₀` are adjacent in the input graph. -/
noncomputable def pairGraphInterp : FullTupleInterpretation Language.graph Language.graph 2 where
  rel
    | .adj => (LHom.sumInl : Language.graph →ᴸ language Language.graph).onFormula
        (Relations.formula₂ Language.adj (.var (0, 0)) (.var (1, 0)))

/-- Unary relation signature for `unreachMax`. -/
abbrev unreachArity : Unit → ℕ := fun _ => 1

/-- Reachability-based SO∃-Horn sentence over `language Language.graph` with a unary relation
variable (`arity () = 1`, scaled to `2` at `k = 2`): `R(0)`, `adj(x, y) ∧ R(x) → R(y)`, and
`R(max) → ⊥`, holding iff `max` is unreachable from `0`. -/
noncomputable def unreachMax : ESO.Horn.Sentence (language Language.graph) where
  Var := Unit
  arity := unreachArity
  clauses :=
    [ { width := 1
        guard := Term.equal (.var 0) (zero _)
        body := []
        head := some ⟨(), ![0]⟩ },
      { width := 2
        guard := Relations.formula₂ ordAdj (.var 0) (.var 1)
        body := [⟨(), ![0]⟩]
        head := some ⟨(), ![1]⟩ },
      { width := 1
        guard := Term.equal (.var 0) (max _)
        body := [⟨(), ![0]⟩]
        head := none } ]

theorem realize_unreachMax_iff {m : ℕ} [Fact (2 ≤ m)] [Language.graph.Structure (Fin m)] :
    unreachMax.Realize (Fin m) ↔
      ∃ S : Set (Fin m),
        (⟨0, by have : 2 ≤ m := Fact.out; omega⟩ : Fin m) ∈ S ∧
        (∀ x y : Fin m, RelMap (L := Language.graph) .adj ![x, y] → x ∈ S → y ∈ S) ∧
        (⟨m - 1, by have : 2 ≤ m := Fact.out; omega⟩ : Fin m) ∉ S := by
  have hm : 2 ≤ m := Fact.out
  let z0 : Fin m := ⟨0, by omega⟩
  let zmax : Fin m := ⟨m - 1, by omega⟩
  constructor
  · rintro ⟨R, hR⟩
    have hc0 := hR _ List.mem_cons_self
    have hc1 := hR _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hc2 := hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    refine ⟨{x | ![x] ∈ R ()}, ?_, ?_, ?_⟩
    · have h := hc0 ![z0]
        (by rw [Formula.realize_equal, Term.realize_var, Fin.ext_iff, realize_zero_val]; rfl)
        (fun _ ha => nomatch ha)
      change (![z0] ∘ ![0]) ∈ R () at h
      rwa [show ![z0] ∘ ![0] = ![z0] from funext fun j => by fin_cases j; rfl] at h
    · intro x y hadj hx
      have hg : (Relations.formula₂ ordAdj (.var 0) (.var 1) :
          (language Language.graph).Formula (Fin 2)).Realize ![x, y] := by
        rw [Formula.realize_rel₂, Term.realize_var, Term.realize_var]
        exact hadj
      have hb : ∀ a ∈ ([⟨(), ![0]⟩] : List (ESO.Horn.Atom unreachArity (Fin 2))),
          a.Holds R ![x, y] := by
        refine List.forall_mem_singleton.mpr ?_
        change (![x, y] ∘ ![0]) ∈ R ()
        rwa [show ![x, y] ∘ ![0] = ![x] from funext fun j => by fin_cases j; rfl]
      have h := hc1 ![x, y] hg hb
      change (![x, y] ∘ ![1]) ∈ R () at h
      rwa [show ![x, y] ∘ ![1] = ![y] from funext fun j => by fin_cases j; rfl] at h
    · intro hmax
      have hb : ∀ a ∈ ([⟨(), ![0]⟩] : List (ESO.Horn.Atom unreachArity (Fin 1))),
          a.Holds R ![zmax] := by
        refine List.forall_mem_singleton.mpr ?_
        change (![zmax] ∘ ![0]) ∈ R ()
        rwa [show ![zmax] ∘ ![0] = ![zmax] from funext fun j => by fin_cases j; rfl]
      exact hc2 ![zmax]
        (by rw [Formula.realize_equal, Term.realize_var, Fin.ext_iff, realize_max_val]; rfl) hb
  · rintro ⟨S, h0, hstep, hmax⟩
    let R : ∀ i : Unit, Set (Fin (unreachArity i) → Fin m) := fun _ => {u | u 0 ∈ S}
    refine ⟨R, fun C hC => ?_⟩
    rcases List.mem_cons.mp hC with rfl | hC
    · intro v hg _
      rw [Formula.realize_equal, Term.realize_var, Fin.ext_iff, realize_zero_val] at hg
      have hv : v 0 = z0 := Fin.ext hg
      change v 0 ∈ S
      rwa [hv]
    · rcases List.mem_cons.mp hC with rfl | hC
      · intro v hg hb
        have hv0 : v 0 ∈ S := hb _ List.mem_cons_self
        rw [Formula.realize_rel₂, Term.realize_var, Term.realize_var] at hg
        exact hstep (v 0) (v 1) hg hv0
      · obtain rfl := List.mem_singleton.mp hC
        intro v hg hb
        have hv0 : v 0 ∈ S := hb _ List.mem_cons_self
        rw [Formula.realize_equal, Term.realize_var, Fin.ext_iff, realize_max_val] at hg
        have hv : v 0 = zmax := Fin.ext hg
        rw [hv] at hv0
        exact hmax hv0

/-- The complete directed graph (with self-loops) on `Fin 2`. -/
def completeGraph2 : Ordered.Structure Language.graph where
  size := 2
  size_ge_two := by decide
  input.RelMap
    | .adj, _ => True

/-- Positive `k = 2` pullback instance: in `twoLoops2`, edges in `Fin (2 ^ 2)` preserve the first
coordinate, so `max = 3` (first coordinate `1`) is unreachable from `0` (first coordinate `0`). -/
theorem realize_onHornSentence_unreachMax_twoLoops2 :
    (pairGraphInterp.onHornSentence unreachMax).Realize twoLoops2 := by
  rw [pairGraphInterp.realize_onHornSentence (n := twoLoops2.size) (by decide)]
  let := pairGraphInterp.inputStructure (n := twoLoops2.size)
  let : Fact (2 ≤ twoLoops2.size ^ 2) :=
    ⟨FullTupleInterpretation.two_le_pow (n := twoLoops2.size) (by decide)⟩
  rw [realize_unreachMax_iff]
  refine ⟨{x : Fin (twoLoops2.size ^ 2) | x.val < 2},
    show 0 < 2 by decide, ?_, show ¬ (twoLoops2.size ^ 2 - 1 < 2) by decide⟩
  intro x y hadj hx
  change ((LHom.sumInl : Language.graph →ᴸ language Language.graph).onFormula
    (Relations.formula₂ Language.adj (.var (0, 0)) (.var (1, 0)))).Realize
      (fun p : Fin 2 × Fin 2 => lexEquiv.symm (![x, y] p.1) p.2) at hadj
  rw [LHom.realize_onFormula, Formula.realize_rel₂, Term.realize_var, Term.realize_var] at hadj
  obtain ⟨heq, _⟩ := hadj
  have hval : ((lexEquiv.symm x : Fin 2 → Fin twoLoops2.size) 0).val =
      ((lexEquiv.symm y : Fin 2 → Fin twoLoops2.size) 0).val := congrArg Fin.val heq
  rw [lexEquiv_symm_apply_val, lexEquiv_symm_apply_val] at hval
  change x.val / 2 % 2 = y.val / 2 % 2 at hval
  change x.val < 2 at hx
  change y.val < 2
  have hy := y.isLt
  change y.val < 4 at hy
  omega

/-- Negative `k = 2` pullback instance: in `completeGraph2`, `0` has a direct edge to `max = 3` in
`Fin (2 ^ 2)`, so `unreachMax` fails. -/
theorem not_realize_onHornSentence_unreachMax_completeGraph2 :
    ¬ (pairGraphInterp.onHornSentence unreachMax).Realize completeGraph2 := by
  rw [pairGraphInterp.realize_onHornSentence (n := completeGraph2.size) (by decide)]
  let := pairGraphInterp.inputStructure (n := completeGraph2.size)
  let : Fact (2 ≤ completeGraph2.size ^ 2) :=
    ⟨FullTupleInterpretation.two_le_pow (n := completeGraph2.size) (by decide)⟩
  rw [realize_unreachMax_iff (m := completeGraph2.size ^ 2)]
  rintro ⟨S, h0, hstep, h3⟩
  let z0 : Fin (completeGraph2.size ^ 2) := ⟨0, by decide⟩
  let z3 : Fin (completeGraph2.size ^ 2) := ⟨completeGraph2.size ^ 2 - 1, by decide⟩
  refine h3 (hstep z0 z3 ?_ h0)
  change ((LHom.sumInl : Language.graph →ᴸ language Language.graph).onFormula
    (Relations.formula₂ Language.adj (.var (0, 0)) (.var (1, 0)))).Realize
      (fun p : Fin 2 × Fin 2 =>
        (lexEquiv (n := completeGraph2.size) (k := 2)).symm (![z0, z3] p.1) p.2)
  rw [LHom.realize_onFormula, Formula.realize_rel₂]
  trivial

/-- Combining `FullTupleInterpretation.onHornSentence` with `HornDefinable.of_sentence` yields
`HornDefinable` for the pulled-back tuple query. -/
example : HornDefinable ({M | (pairGraphInterp.onHornSentence unreachMax).Realize M} :
    Query Language.graph) :=
  HornDefinable.of_sentence (pairGraphInterp.onHornSentence unreachMax) fun _ => Iff.rfl

/-! ### Grädel's theorem (`SO∃-Horn = P`) and Horn tableau controls -/

section GradelCapture

open Turing Turing.MultiTapeTM
open Cslib.Complexity.Gradel.Tableau
open Cslib.Complexity.ImmermanVardi.Tableau

/-- Client-facing capture equivalence `hornDefinable_iff_encodedLanguage_mem_P` for any relational
vocabulary. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) (K : Query L) :
    HornDefinable K ↔ K.encodedLanguage v ∈ P encStructure :=
  hornDefinable_iff_encodedLanguage_mem_P v K

/-- Round-trip of `evenLoopsQuery` through `hornDefinable_iff_encodedLanguage_mem_P`. -/
example : HornDefinable evenLoopsQuery := by
  have hP : evenLoopsQuery.encodedLanguage graphVocabulary ∈ P encStructure :=
    (hornDefinable_iff_encodedLanguage_mem_P graphVocabulary evenLoopsQuery).mp
      ⟨evenLoops, evenLoops_isQF, fun _ => Iff.rfl⟩
  exact (hornDefinable_iff_encodedLanguage_mem_P graphVocabulary evenLoopsQuery).mpr hP

/-- Empty query from a constant-`false` native decider: produces a quantifier-free Horn sentence
rejecting every canonical ordered structure. -/
example {L : Language} [L.IsRelational] (v : Vocabulary L) :
    ∃ Φ : ESO.Horn.Sentence (language (succLanguage L)),
      Φ.IsQF ∧ ∀ M : Ordered.Structure L, ¬ Φ.Realize M := by
  have hP : (∅ : Query L).encodedLanguage v ∈ P encStructure := by
    refine ⟨fun _ => false, ComputableInPolyTime.const false, fun a => ?_⟩
    simp [Query.encodedLanguage]
  obtain ⟨Φ, hqf, hΦ⟩ := HornDefinable.of_encodedLanguage_mem_P v hP
  exact ⟨Φ, hqf, fun M h => (hΦ M).mpr h⟩

/-- Non-trivial native polynomial-time query: directed graphs on `Fin 2`. Starting purely from a
native `ComputableInPolyTime` decider, `HornDefinable.of_encodedLanguage_mem_P` synthesizes a
quantifier-free `ESO.Horn.Sentence` over `G` that accepts `twoLoops2` (`size = 2`) and rejects
`twoLoops` (`size = 3`). -/
def sizeTwoGraphs : Query Language.graph := {M | M.size = 2}

theorem sizeTwoGraphs_mem_P :
    sizeTwoGraphs.encodedLanguage graphVocabulary ∈ P encStructure := by
  refine ⟨fun a => graphVocabulary.checkShape a && decide (Prod.fst a = 2),
    ComputableInPolyTime.bool_and' graphVocabulary.computableInPolyTime_checkShape
      (ComputableInPolyTime.unary_eq' (ComputableInPolyTime.fst encUnary (encList encBits))
        (ComputableInPolyTime.const 2)),
    fun a => ?_⟩
  rcases a with ⟨n, tables⟩
  simp only [Query.encodedLanguage, sizeTwoGraphs, decoded, Set.mem_ofPred_eq, Bool.and_eq_true,
    Vocabulary.checkShape_eq_true_iff, decide_eq_true_eq]
  exact ⟨fun ⟨hw, ⟨_, heq⟩⟩ => ⟨hw, heq⟩, fun ⟨hw, heq⟩ => ⟨hw, ⟨by omega, heq⟩⟩⟩

example :
    ∃ Φ : ESO.Horn.Sentence G,
      Φ.IsQF ∧ Φ.Realize twoLoops2 ∧ ¬ Φ.Realize twoLoops := by
  obtain ⟨Φ, hqf, hΦ⟩ := HornDefinable.of_encodedLanguage_mem_P graphVocabulary sizeTwoGraphs_mem_P
  refine ⟨Φ, hqf, (hΦ twoLoops2).mp rfl, fun h => ?_⟩
  have hsz : twoLoops.size = 2 := (hΦ twoLoops).mpr h
  exact absurd hsz (by decide)

/-! #### Direct positive and negative controls for `acceptanceHornSentence` -/

section TableauControls

local instance {M : Type} : Language.empty.Structure M := Language.emptyStructure
local instance : Fact (2 ≤ 4) := ⟨by decide⟩

/-- Formula family interpreting the empty input `[]` over `Ordered.language Language.empty`. -/
def nilInputFormula : Option Bool → (Ordered.language Language.empty).Formula (Fin 1)
  | none => ⊤
  | some _ => ⊥

theorem realize_nilInputFormula {B : ℕ} [Fact (2 ≤ B)] (s : Option Bool) (a : Fin B) :
    (nilInputFormula s).Realize ![a] ↔ inputAt ([] : List Bool) a.val = s := by
  cases s <;> simp [nilInputFormula, inputAt]

/-- Halts in one step outputting `[b]`. -/
def haltWith (b : Bool) : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, some b, none⟩

/-- Halts in one step with empty output `[]`. -/
def haltEmpty : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, none, none⟩

/-- Writes `true` on step 1, then loops forever in state `some true` without halting. -/
def loopAfterTrue : MultiTapeTM 0 Bool Bool :=
  ofTr false fun q _ _ =>
    if q then ⟨0, Fin.elim0, none, some true⟩
    else ⟨0, Fin.elim0, some true, some true⟩

/-- Writes `true` on step 1, then writes `false` and halts on step 2 (`output = [true, false]`). -/
def haltTrueFalse : MultiTapeTM 0 Bool Bool :=
  ofTr false fun q _ _ =>
    if q then ⟨0, Fin.elim0, some false, none⟩
    else ⟨0, Fin.elim0, some true, some true⟩

/-- Reads cell `1` of the input tape and outputs `true` iff that symbol is `some true`. -/
def echoFirstBit : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ inSym _ => ⟨0, Fin.elim0, some (inSym == some true), none⟩

private theorem haltWith_run (b : Bool) :
    ((haltWith b).runFrom ((haltWith b).initCfg []) 3).Halted ∧
      ((haltWith b).runFrom ((haltWith b).initCfg []) 3).output = [b] := by
  obtain ⟨hhalt, hout⟩ :
      ((haltWith b).runFrom ((haltWith b).initCfg []) 1).Halted ∧
        ((haltWith b).runFrom ((haltWith b).initCfg []) 1).output = [b] := by
    rw [runFrom_one, step_of_state (q := ()) rfl]
    simp [haltWith, tr_ofTr, Cfg.Halted, Action.apply_state, Action.apply_output]
  rw [runFrom_eq_of_halt (haltWith b) ((haltWith b).initCfg []) (by decide : 1 ≤ 3) hhalt]
  exact ⟨hhalt, hout⟩

private theorem haltEmpty_run :
    (haltEmpty.runFrom (haltEmpty.initCfg []) 3).Halted ∧
      (haltEmpty.runFrom (haltEmpty.initCfg []) 3).output = [] := by
  obtain ⟨hhalt, hout⟩ :
      (haltEmpty.runFrom (haltEmpty.initCfg []) 1).Halted ∧
        (haltEmpty.runFrom (haltEmpty.initCfg []) 1).output = [] := by
    rw [runFrom_one, step_of_state (q := ()) rfl]
    simp [haltEmpty, tr_ofTr, Cfg.Halted, Action.apply_state, Action.apply_output]
  rw [runFrom_eq_of_halt haltEmpty (haltEmpty.initCfg []) (by decide : 1 ≤ 3) hhalt]
  exact ⟨hhalt, hout⟩

private theorem loopAfterTrue_run :
    (loopAfterTrue.runFrom (loopAfterTrue.initCfg []) 3).state = some true ∧
      (loopAfterTrue.runFrom (loopAfterTrue.initCfg []) 3).output = [true] := by
  have h1 : (loopAfterTrue.runFrom (loopAfterTrue.initCfg []) 1).state = some true ∧
      (loopAfterTrue.runFrom (loopAfterTrue.initCfg []) 1).output = [true] := by
    rw [runFrom_one, step_of_state (q := false) rfl]
    simp [loopAfterTrue, tr_ofTr, Action.apply_state, Action.apply_output]
  obtain ⟨hs1, ho1⟩ := h1
  have h2 : (loopAfterTrue.runFrom (loopAfterTrue.initCfg []) 2).state = some true ∧
      (loopAfterTrue.runFrom (loopAfterTrue.initCfg []) 2).output = [true] := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, runFrom_succ, step_of_state (q := true) hs1]
    simp only [Action.apply_state, Action.apply_output, ho1]
    simp [loopAfterTrue, tr_ofTr]
  obtain ⟨hs2, ho2⟩ := h2
  rw [show (3 : ℕ) = 2 + 1 from rfl, runFrom_succ, step_of_state (q := true) hs2]
  simp only [Action.apply_state, Action.apply_output, ho2]
  simp [loopAfterTrue, tr_ofTr]

private theorem haltTrueFalse_run :
    (haltTrueFalse.runFrom (haltTrueFalse.initCfg []) 3).Halted ∧
      (haltTrueFalse.runFrom (haltTrueFalse.initCfg []) 3).output = [true, false] := by
  have h1 : (haltTrueFalse.runFrom (haltTrueFalse.initCfg []) 1).state = some true ∧
      (haltTrueFalse.runFrom (haltTrueFalse.initCfg []) 1).output = [true] := by
    rw [runFrom_one, step_of_state (q := false) rfl]
    simp [haltTrueFalse, tr_ofTr, Action.apply_state, Action.apply_output]
  obtain ⟨hs1, ho1⟩ := h1
  obtain ⟨hhalt, hout⟩ :
      (haltTrueFalse.runFrom (haltTrueFalse.initCfg []) 2).Halted ∧
        (haltTrueFalse.runFrom (haltTrueFalse.initCfg []) 2).output = [true, false] := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, runFrom_succ, step_of_state (q := true) hs1]
    simp only [Cfg.Halted, Action.apply_state, Action.apply_output, ho1]
    simp [haltTrueFalse, tr_ofTr]
  rw [runFrom_eq_of_halt haltTrueFalse (haltTrueFalse.initCfg []) (by decide : 2 ≤ 3) hhalt]
  exact ⟨hhalt, hout⟩

private theorem echoFirstBit_run (b₀ : Bool) :
    ((echoFirstBit.runFrom (echoFirstBit.initCfg [b₀]) 3).Halted) ∧
      ((echoFirstBit.runFrom (echoFirstBit.initCfg [b₀]) 3).output = [b₀]) := by
  obtain ⟨hhalt, hout⟩ :
      ((echoFirstBit.runFrom (echoFirstBit.initCfg [b₀]) 1).Halted) ∧
        ((echoFirstBit.runFrom (echoFirstBit.initCfg [b₀]) 1).output = [b₀]) := by
    rw [runFrom_one, step_of_state (q := ()) rfl]
    simp [echoFirstBit, tr_ofTr, Cfg.Halted, Action.apply_state, Action.apply_output]
  rw [runFrom_eq_of_halt echoFirstBit (echoFirstBit.initCfg [b₀]) (by decide : 1 ≤ 3) hhalt]
  exact ⟨hhalt, hout⟩

/-- **Positive control:** `haltWith true` halts with `[true]` by step `3`, so
`acceptanceHornSentence` holds on `Fin 4`. -/
example :
    (acceptanceHornSentence Language.empty (haltWith true) nilInputFormula).Realize (Fin 4) := by
  rw [realize_acceptanceHornSentence (haltWith true) nilInputFormula []
    realize_nilInputFormula (by decide)]
  exact haltWith_run true

/-- **Negative control (output `[false]`):** `haltWith false` halts with `[false]`, rejected by the
`OutView.one false` goal clause at `max`. -/
example :
    ¬ (acceptanceHornSentence Language.empty (haltWith false) nilInputFormula).Realize (Fin 4) := by
  rw [realize_acceptanceHornSentence (haltWith false) nilInputFormula []
    realize_nilInputFormula (by decide)]
  obtain ⟨_, hout⟩ := haltWith_run false
  rintro ⟨_, h⟩
  rw [hout] at h
  exact absurd h (by decide)

/-- **Negative control (empty output `[]`):** `haltEmpty` halts with `[]`, rejected by the
`OutView.empty` goal clause at `max`. -/
example :
    ¬ (acceptanceHornSentence Language.empty haltEmpty nilInputFormula).Realize (Fin 4) := by
  rw [realize_acceptanceHornSentence haltEmpty nilInputFormula []
    realize_nilInputFormula (by decide)]
  obtain ⟨_, hout⟩ := haltEmpty_run
  rintro ⟨_, h⟩
  rw [hout] at h
  exact absurd h (by decide)

/-- **Negative control (non-halted at bound despite output `[true]`):** `loopAfterTrue` has already
written `[true]` by step `3`, yet its state at `max = 3` is `some true`, so the halting goal clause
rejects it. -/
example :
    ((loopAfterTrue.runFrom (loopAfterTrue.initCfg []) 3).output = [true]) ∧
      ¬ (acceptanceHornSentence Language.empty loopAfterTrue nilInputFormula).Realize (Fin 4) := by
  obtain ⟨hstate, hout⟩ := loopAfterTrue_run
  refine ⟨hout, ?_⟩
  rw [realize_acceptanceHornSentence loopAfterTrue nilInputFormula []
    realize_nilInputFormula (by decide)]
  rintro ⟨hhalt, _⟩
  change (loopAfterTrue.runFrom (loopAfterTrue.initCfg []) 3).state = none at hhalt
  rw [hstate] at hhalt
  exact absurd hhalt (by decide)

/-- **Negative control (multi-bit output `[true, false]`):** `haltTrueFalse` halts at step `2` with
output `[true, false]`, rejected by the `OutView.many` goal clause even though its first output bit
is `true`. -/
example :
    ¬ (acceptanceHornSentence Language.empty haltTrueFalse nilInputFormula).Realize (Fin 4) := by
  rw [realize_acceptanceHornSentence haltTrueFalse nilInputFormula []
    realize_nilInputFormula (by decide)]
  obtain ⟨_, hout⟩ := haltTrueFalse_run
  rintro ⟨_, h⟩
  rw [hout] at h
  exact absurd h (by decide)

/-- Formula family interpreting a 1-bit input `[b₀]` over `Ordered.language Language.empty`:
position `1` carries `some b₀`, and all other positions carry `none`. -/
def oneBitInputFormula (b₀ : Bool) :
    Option Bool → (Ordered.language Language.empty).Formula (Fin 1)
  | none => ∼(Term.equal (.var 0) (Ordered.one Language.empty))
  | some b => if b = b₀ then Term.equal (.var 0) (Ordered.one Language.empty) else ⊥

theorem realize_oneBitInputFormula {B : ℕ} [Fact (2 ≤ B)] (b₀ : Bool)
    (s : Option Bool) (a : Fin B) :
    (oneBitInputFormula b₀ s).Realize ![a] ↔ inputAt [b₀] a.val = s := by
  have h1 : (Term.equal (.var 0) (Ordered.one Language.empty) :
      (Ordered.language Language.empty).Formula (Fin 1)).Realize ![a] ↔ a.val = 1 := by
    rw [Formula.realize_equal, Term.realize_var, Matrix.cons_val_zero, Fin.ext_iff,
      Ordered.realize_one_val]
  cases s with
  | none =>
    simp only [oneBitInputFormula, Formula.realize_not, h1]
    rcases hv : a.val with _ | _ | k <;> simp [inputAt]
  | some b =>
    simp only [oneBitInputFormula]
    split_ifs with hb
    · subst hb
      rw [h1]
      rcases hv : a.val with _ | _ | k <;> simp [inputAt]
    · rw [Formula.realize_bot]
      rcases hv : a.val with _ | _ | k <;> simp [inputAt, Ne.symm hb]

/-- **Input-dependent control:** `echoFirstBit` accepts `[true]` and rejects `[false]` on `Fin 4`
(`[b₀].length + 1 = 2 < 4`). -/
example :
    (acceptanceHornSentence Language.empty echoFirstBit
      (oneBitInputFormula true)).Realize (Fin 4) ∧
    ¬ (acceptanceHornSentence Language.empty echoFirstBit
      (oneBitInputFormula false)).Realize (Fin 4) := by
  constructor
  · rw [realize_acceptanceHornSentence echoFirstBit (oneBitInputFormula true) [true]
      (realize_oneBitInputFormula true) (by decide)]
    exact echoFirstBit_run true
  · rw [realize_acceptanceHornSentence echoFirstBit (oneBitInputFormula false) [false]
      (realize_oneBitInputFormula false) (by decide)]
    obtain ⟨_, hout⟩ := echoFirstBit_run false
    rintro ⟨_, h⟩
    rw [hout] at h
    exact absurd h (by decide)

end TableauControls

end GradelCapture

end Cslib.Tests.SecondOrderHorn
