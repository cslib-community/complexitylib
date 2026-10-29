/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Planar.CrossoverCounting
import Mathlib.Tactic.FinCases

/-!
# A crossover with two attachment ports per side

Each old terminal is replaced by two ports and one implication between them. Together with
its two old incidences this forms an implication chain between two equal internal copies.
Consequently both ports have the old terminal's uniquely determined value. Each port has two
internal incidences and room for one external incidence. The unchanged internal core comes from
Lichtenstein's crossover [Lichtenstein1982, Figs. 4–5], as drawn in [Tromino2025, Fig. 8(b)].

## Main definitions

* `PairedCrossover.formula`: the 57-variable, 78-clause paired-port template.
* `PairedCrossover.canonicalExtension`: its full assignment from two input bits.

## Main results

* `PairedCrossover.existsUnique_holds`: a unique full satisfying assignment for each input pair.
* `PairedCrossover.eval_formula_iff`: split-formula semantics with paired-terminal agreement.
* `PairedCrossover.eq_canonicalExtension_of_holds`: uniqueness of the full extension.
* `PairedCrossover.terminal_occurrences`: two internal incidences at each of the eight ports.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The paired-terminal replacement and its uniqueness proof are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PairedCrossover

/-- Eight boundary ports, the unsplit center, and the old 48 internal copies. -/
inductive Variable
  | port (side : Fin 4) (lane : Fin 2)
  | center
  | copy (v : Crossover.Internal) (i : Fin 6)
  deriving DecidableEq, Repr

instance : Fintype Variable where
  elems := { .center } ∪
    Finset.univ.biUnion (fun s => Finset.univ.image (Variable.port s)) ∪
    Finset.univ.biUnion (fun v => Finset.univ.image (Variable.copy v))
  complete v := by cases v <;> simp

/-- The eight attachment ports in left/right/bottom/top geometric order, with two lanes per
side. The source variables `.bTop` and `.bBottom` retain their historical names. -/
def terminal : Fin 4 → Fin 2 → Variable := Variable.port

/-- Forget the lane of a boundary port. -/
def Variable.origin : Variable → Crossover.SplitVariable
  | .port 0 _ => .aLeft
  | .port 1 _ => .aRight
  | .port 2 _ => .bTop
  | .port 3 _ => .bBottom
  | .center => .center
  | .copy v i => .copy v i

/-- Choose lane zero as the representative of each old terminal. -/
def representative : Crossover.SplitVariable → Variable
  | .aLeft => .port 0 0
  | .aRight => .port 1 0
  | .bTop => .port 2 0
  | .bBottom => .port 3 0
  | .center => .center
  | .copy v i => .copy v i

/-- Replace each old boundary literal by the port at that incidence's geometric lane. -/
def mapLiteral : Literal Crossover.SplitVariable → Literal Variable
  | (.aLeft, true) => (.port 0 0, true)
  | (.aLeft, false) => (.port 0 1, false)
  | (.aRight, false) => (.port 1 0, false)
  | (.aRight, true) => (.port 1 1, true)
  | (.bTop, false) => (.port 2 0, false)
  | (.bTop, true) => (.port 2 1, true)
  | (.bBottom, true) => (.port 3 0, true)
  | (.bBottom, false) => (.port 3 1, false)
  | (.center, b) => (.center, b)
  | (.copy v i, b) => (.copy v i, b)

/-- One directed implication joins the paired ports on each side. -/
def bridges : CNF Variable :=
  [[(.port 0 0, false), (.port 0 1, true)],
   [(.port 1 1, false), (.port 1 0, true)],
   [(.port 2 1, false), (.port 2 0, true)],
   [(.port 3 0, false), (.port 3 1, true)]]

/-- Preserve the old 74 clauses with their terminal incidences separated, then add four bridges. -/
def formula : CNF Variable :=
  Crossover.splitFormula.map (List.map mapLiteral) ++ bridges

/-- The internal copy at the start of each terminal's implication chain. -/
def chainStart : Fin 4 → Variable
  | 0 => .copy .aInnerLeft 5
  | 1 => .copy .aInnerRight 3
  | 2 => .copy .bInnerTop 1
  | 3 => .copy .bInnerBottom 4

/-- The internal copy at the end of each terminal's implication chain. -/
def chainEnd : Fin 4 → Variable
  | 0 => .copy .aInnerLeft 4
  | 1 => .copy .aInnerRight 2
  | 2 => .copy .bInnerTop 0
  | 3 => .copy .bInnerBottom 3

/-- The first lane in each directed chain. -/
def firstLane : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 0

/-- Three existing clauses form a chain between two equal internal copies. -/
def chain : Fin 4 → CNF Variable
  | 0 => [[(.port 0 0, true), (.copy .aInnerLeft 5, false)],
      [(.port 0 0, false), (.port 0 1, true)],
      [(.port 0 1, false), (.copy .aInnerLeft 4, true)]]
  | 1 => [[(.copy .aInnerRight 3, false), (.port 1 1, true)],
      [(.port 1 1, false), (.port 1 0, true)],
      [(.copy .aInnerRight 2, true), (.port 1 0, false)]]
  | 2 => [[(.port 2 1, true), (.copy .bInnerTop 1, false)],
      [(.port 2 1, false), (.port 2 0, true)],
      [(.port 2 0, false), (.copy .bInnerTop 0, true)]]
  | 3 => [[(.copy .bInnerBottom 4, false), (.port 3 0, true)],
      [(.port 3 0, false), (.port 3 1, true)],
      [(.copy .bInnerBottom 3, true), (.port 3 1, false)]]

private theorem chain_mem : ∀ s, ∀ c ∈ chain s, c ∈ formula := by decide +kernel

private theorem ring_mem : ∀ v, ∀ c ∈ (Crossover.ring v).relabel representative,
    c ∈ formula := by decide +kernel

private theorem eval_chain {σ : Variable → Bool} {s : Fin 4}
    (h : (chain s).eval σ = true) (heq : σ (chainStart s) = σ (chainEnd s)) :
    σ (terminal s 0) = σ (chainStart s) ∧
      σ (terminal s 1) = σ (chainStart s) := by
  have cert : ∀ a p q : Bool,
      ((!a || p) && (!p || q) && (!q || a)) = true → p = a ∧ q = a := by
    decide +kernel
  have h' : ((!σ (chainStart s) || σ (terminal s (firstLane s))) &&
      (!σ (terminal s (firstLane s)) || σ (terminal s (1 - firstLane s))) &&
      (!σ (terminal s (1 - firstLane s)) || σ (chainEnd s))) = true := by
    fin_cases s <;>
      simpa [chain, chainStart, chainEnd, terminal, firstLane, CNF.eval, Clause.eval,
        Literal.eval, Bool.and_assoc, Bool.or_comm] using h
  rw [← heq] at h'
  have hp := cert _ _ _ h'
  fin_cases s <;> simpa [firstLane, and_comm] using hp

private theorem eval_mapped (σ : Variable → Bool)
    (ha : ∀ s, σ (terminal s 0) = σ (terminal s 1)) :
    CNF.eval σ (Crossover.splitFormula.map (List.map mapLiteral)) =
      Crossover.splitFormula.eval (σ ∘ representative) := by
  have hl : ∀ l, Literal.eval σ (mapLiteral l) = Literal.eval (σ ∘ representative) l := by
    simp only [terminal] at ha
    rintro ⟨v, b⟩
    cases v <;> cases b <;>
      simp [mapLiteral, Literal.eval, representative, ← ha]
  simp only [CNF.eval, List.all_map, Function.comp_def, Clause.eval, List.any_map, hl]
  rfl

/-- Exact semantics: the old split formula together with agreement of each paired terminal. -/
theorem eval_formula_iff (σ : Variable → Bool) :
    formula.eval σ = true ↔
      Crossover.splitFormula.eval (σ ∘ representative) = true ∧
        ∀ s, σ (terminal s 0) = σ (terminal s 1) := by
  constructor
  · intro h
    have hc := CNF.eval_eq_true_iff σ formula |>.1 h
    have hr : ∀ v i, σ (.copy v i) = σ (.copy v 0) := by
      intro v
      apply (Crossover.eval_ring_iff (σ ∘ representative) v).1
      rw [← CNF.eval_relabel]
      exact (CNF.eval_eq_true_iff _ _).2 fun c hc' => hc c (ring_mem v c hc')
    have hp : ∀ s, σ (terminal s 0) = σ (terminal s 1) := by
      intro s
      have hchain := (CNF.eval_eq_true_iff σ (chain s)).2 fun c hc' => hc c (chain_mem s c hc')
      have heq : σ (chainStart s) = σ (chainEnd s) := by
        fin_cases s <;> exact (hr _ _).trans (hr _ _).symm
      exact (eval_chain hchain heq).1.trans (eval_chain hchain heq).2.symm
    refine ⟨?_, hp⟩
    rw [formula, CNF.eval_append, Bool.and_eq_true] at h
    rw [eval_mapped σ hp] at h
    exact h.1
  · rintro ⟨h, hp⟩
    rw [formula, CNF.eval_append, Bool.and_eq_true, eval_mapped σ hp]
    refine ⟨h, ?_⟩
    simp only [terminal] at hp
    simp [bridges, CNF.eval, Clause.eval, Literal.eval, ← hp]

/-- The explicit unique full assignment, including both lanes on every side. -/
def canonicalExtension (a b : Bool) : Variable → Bool :=
  Crossover.canonicalSplitExtension a b ∘ Variable.origin

/-- The explicit full assignment satisfies the paired-port formula. -/
theorem eval_canonicalExtension (a b : Bool) : formula.eval (canonicalExtension a b) = true := by
  apply (eval_formula_iff _).2
  constructor
  · have heq : canonicalExtension a b ∘ representative = Crossover.canonicalSplitExtension a b := by
      funext v
      cases v <;> rfl
    rw [heq]
    exact Crossover.eval_canonicalSplitExtension a b
  · intro s
    fin_cases s <;> rfl

/-- Both lanes on the left and right carry `a`; both lanes on the top and bottom carry `b`. -/
theorem terminal_values_canonicalExtension (a b : Bool) :
    ∀ s l, canonicalExtension a b (terminal s l) = if s.val < 2 then a else b := by
  intro s l
  fin_cases s <;> rfl

/-- Every satisfying full assignment is determined by the left and top lane-zero inputs. -/
theorem eq_canonicalExtension_of_holds {σ : Variable → Bool} (h : formula.eval σ = true) :
    σ = canonicalExtension (σ (terminal 0 0)) (σ (terminal 2 0)) := by
  obtain ⟨hb, hp⟩ := (eval_formula_iff σ).1 h
  have heq := Crossover.eq_canonicalSplitExtension_of_holds hb
  funext v
  cases v with
  | center => exact congrFun heq .center
  | copy v i => exact congrFun heq (.copy v i)
  | port s l =>
    have hs : σ (terminal s 0) = canonicalExtension (σ (terminal 0 0))
        (σ (terminal 2 0)) (terminal s l) := by
      fin_cases s
      · exact congrFun heq .aLeft
      · exact congrFun heq .aRight
      · exact congrFun heq .bTop
      · exact congrFun heq .bBottom
    fin_cases l
    · exact hs
    · exact (hp s).symm.trans hs

/-- All satisfying terminal values are the horizontal or vertical input value. -/
theorem terminal_value_of_holds {σ : Variable → Bool} (h : formula.eval σ = true)
    (s : Fin 4) (l : Fin 2) :
    σ (terminal s l) = if s.val < 2 then σ (terminal 0 0) else σ (terminal 2 0) :=
  (congrFun (eq_canonicalExtension_of_holds h) (terminal s l)).trans
    (terminal_values_canonicalExtension _ _ s l)

/-- Projecting a satisfying paired assignment recovers a satisfying old split assignment. -/
theorem eval_representative_of_holds {σ : Variable → Bool} (h : formula.eval σ = true) :
    Crossover.splitFormula.eval (σ ∘ representative) = true :=
  ((eval_formula_iff σ).1 h).1

/-- Every two-bit input has exactly one satisfying full assignment. -/
theorem existsUnique_holds (a b : Bool) :
    ∃! σ : Variable → Bool,
      formula.eval σ = true ∧ σ (terminal 0 0) = a ∧ σ (terminal 2 0) = b := by
  refine ⟨canonicalExtension a b, ⟨eval_canonicalExtension a b, rfl, rfl⟩, ?_⟩
  rintro σ ⟨h, ha, hb⟩
  rw [eq_canonicalExtension_of_holds h, ha, hb]

/-- The template uses exactly 57 variables. -/
theorem card_variable : Fintype.card Variable = 57 := by decide +kernel

/-- The template has exactly 78 clauses. -/
theorem length_formula : formula.length = 78 := by decide +kernel

/-- All clauses have width at most three. -/
theorem width_formula : ∀ c ∈ formula, c.length ≤ 3 := by decide +kernel

/-- No clause repeats a variable. -/
theorem distinct_variables : ∀ c ∈ formula, (c.map Prod.fst).Nodup := by decide +kernel

/-- Every variable has at most three internal incidences. -/
theorem occurrences_le_three : ∀ v, formula.occurrences v ≤ 3 := by decide +kernel

/-- Each of the eight ports has exactly two internal incidences. -/
theorem terminal_occurrences : ∀ s l, formula.occurrences (terminal s l) = 2 := by decide +kernel

end Cslib.Logic.PL.CNF.PairedCrossover
