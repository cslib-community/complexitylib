/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.ImmermanVardi.Tableau.FixedPoint
public import Complexity.Logics.FirstOrder.Operator.LeastFixedPoint.Definability
public import Complexity.Logics.FirstOrder.Operator.Definability.Finite
public import Complexity.Logics.FirstOrder.Ordered.BitArithmetic
import Complexity.Tactic.FOOperator
import Mathlib.Tactic.FinCases

/-!
# Synthesizing a positive native computation tableau

Fixed finite transition tables become fixed finite disjunctions. The three input-symbol
formulas are ordinary first-order formulas; every recursive relation occurrence is certified
positive by the shared synthesis calculus. A single resulting formula works for every input
structure and every finite domain size.

## Main results

* `traceStep_polarityDefinable`: syntactic positivity and uniform definability of the native
  tableau transformer.
* `trace_lfp_definable`: a single FO(LFP) formula for the native tableau fixed point.
-/

public section

namespace Cslib.Complexity.ImmermanVardi.Tableau

open Turing Turing.MultiTapeTM
open FirstOrder Language
open Cslib.Logic.FO
open Cslib.Logic.FO.Operator

variable {L : Language} {ι : Type} (size : ι → ℕ)
  [∀ i, L.Structure (Fin (size i))] [∀ i, Fact (2 ≤ size i)]

private abbrev Candidate := (i : ι) × Set (Fin 3 → Fin (size i))

private abbrev BodyDefinable {α : Type} (sign : Bool)
    (P : ∀ j : Candidate size, (α → Fin (size j.1)) → Prop) : Prop :=
  PolarityDefinable (L := Ordered.language L) LFP.policy LFP.headMark sign
    (fun j : Candidate size => Fin (size j.1)) (fun _ => LFP.interpretation)
    (fun j => RelEnv.cons j.2 RelEnv.empty) P

variable {size}

private theorem numeral_definable {α : Type} (sign : Bool) (n : ℕ) (a : α) :
    BodyDefinable (L := L) size sign (fun _ v => (v a).val = n) :=
  (PolarityDefinable.ofFO (Ordered.natEq L n (.var a))).congr
    fun _ _ => Ordered.realize_natEq _ _ _

private theorem successor_definable {α : Type} (sign : Bool) (a b : α) :
    BodyDefinable (L := L) size sign (fun _ v => (v a).val + 1 = (v b).val) :=
  (PolarityDefinable.ofFO (Ordered.addEq L (.var a) (Ordered.one L) (.var b))).congr
    fun _ _ => by simp only [Ordered.realize_addEq, Term.realize_var, Ordered.realize_one_val]

private theorem recursive_atom_definable {α : Type} (a b c : α) :
    BodyDefinable (L := L) size true (fun j v => ![v a, v b, v c] ∈ j.2) := by
  apply (PolarityDefinable.head_vars LFP.headMark
    (fun j : Candidate size => j.2) ![a, b, c]).congr
  intro j v
  have hv : v ∘ ![a, b, c] = ![v a, v b, v c] := by
    ext k
    fin_cases k <;> rfl
  rw [hv]

private theorem input_definable (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    {α : Type} (sign : Bool) (s : Option Bool) (a : α) :
    BodyDefinable (L := L) size sign
      (fun j v => inputAt (input j.1) (v a).val = s) := by
  apply (PolarityDefinable.ofFO ((inputFormula s).relabel (fun _ => a))).congr
  intro j v
  have hv : v ∘ (fun _ : Fin 1 => a) = ![v a] := by
    funext k
    fin_cases k
    rfl
  rw [Language.Formula.realize_relabel, hv]
  exact hinput j.1 s (v a)

variable {m : ℕ} {State : Type} [Fintype State]

private theorem traceRow_definable {α : Type} (q : Tag m State) (t a : α) :
    BodyDefinable (L := L) size true (fun j v => traceRow j.2 (v t) q (v a)) := by
  apply PolarityDefinable.ex
  exact (numeral_definable true (tagIndex q) none).conj
    (recursive_atom_definable none (some t) (some a))

attribute [local aesop safe apply (rule_sets := [FODefinable])]
  numeral_definable successor_definable recursive_atom_definable traceRow_definable

private theorem read_definable {α : Type} (i : Fin m) (s : Option Bool) (t : α) :
    BodyDefinable (L := L) size true
      (fun j v => read (traceRow (State := State) j.2 (v t)) i s) := by
  unfold read
  fo_definable

attribute [local aesop safe apply (rule_sets := [FODefinable])] read_definable

private theorem situation_definable (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    {α : Type} (y : Situation m State) (t a : α) :
    BodyDefinable (L := L) size true
      (fun j v => situation (input j.1) (traceRow j.2 (v t)) y (v a)) := by
  unfold situation
  apply PolarityDefinable.conj (traceRow_definable _ _ _)
  apply PolarityDefinable.conj
  · apply PolarityDefinable.ex
    exact (traceRow_definable .inPos (some t) none).conj
      (input_definable input inputFormula hinput true y.2.1 none)
  · exact PolarityDefinable.iAll fun i => read_definable i (y.2.2 i) t

private theorem elsewhere_definable {α : Type} (i : Fin m) (sign : Bool) (t a : α) :
    BodyDefinable (L := L) size true
      (fun j v => elsewhere (traceRow (State := State) j.2 (v t)) i sign (v a)) := by
  simp only [elsewhere, ne_eq]
  fo_definable

private theorem inputPrev_definable (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    {α : Type} (d : SignType) (t a : α) :
    BodyDefinable (L := L) size true
      (fun j v => inputPrev (m := m) (State := State)
        (input j.1) (traceRow j.2 (v t)) d (v a)) := by
  cases d with
  | zero => exact traceRow_definable .inPos t a
  | neg =>
    simp only [inputPrev]
    fo_definable
  | pos =>
    apply PolarityDefinable.disj
    · exact (numeral_definable false 0 a).neg.conj
        ((input_definable input inputFormula hinput true none a).conj
          (traceRow_definable .inPos t a))
    · apply PolarityDefinable.ex
      exact (successor_definable true none (some a)).conj
        ((traceRow_definable .inPos (some t) none).conj
          ((numeral_definable true 0 none).disj
            (input_definable input inputFormula hinput false none none).neg))

private theorem headPrev_definable {α : Type} (i : Fin m) (sign : Bool)
    (d : SignType) (t a : α) :
    BodyDefinable (L := L) size true
      (fun j v => headPrev (State := State) (traceRow j.2 (v t)) i sign d (v a)) := by
  unfold headPrev
  generalize (if sign then d else -d) = e
  cases e <;> fo_definable

omit [Fintype State] in
private theorem initial_definable (tm : MultiTapeTM m Bool State) {α : Type}
    (q : Tag m State) (a : α) :
    BodyDefinable (L := L) size true (fun _ v => initial tm q (v a)) := by
  cases q <;> simp only [initial] <;> fo_definable

private theorem rowStep_definable (tm : MultiTapeTM m Bool State) (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    {α : Type} (q : Tag m State) (t a : α) :
    BodyDefinable (L := L) size true
      (fun j v => rowStep tm (input j.1) (traceRow j.2 (v t)) q (v a)) := by
  have hs (y : Situation m State) :=
    situation_definable (size := size) input inputFormula hinput y t a
  have hi (d : SignType) :=
    inputPrev_definable (size := size) (m := m) (State := State)
      input inputFormula hinput d t a
  have hh (i : Fin m) (s : Bool) (d : SignType) :=
    headPrev_definable (L := L) (size := size) (State := State) i s d t a
  have he (i : Fin m) (s : Bool) :=
    elsewhere_definable (L := L) (size := size) (State := State) i s t a
  cases q with
  | state q =>
    exact ((traceRow_definable (.state none) t a).conj
      (PolarityDefinable.constant (q = none))).disj
      (PolarityDefinable.iEx fun y =>
        (PolarityDefinable.constant ((tm.actionOf y).state = q)).conj (hs y))
  | out o =>
    exact ((traceRow_definable (.state none) t a).conj
      (traceRow_definable (.out o) t a)).disj
      (PolarityDefinable.iEx fun y => PolarityDefinable.iEx fun o' =>
        (PolarityDefinable.constant (o'.push (tm.actionOf y).output = o)).conj
          ((hs y).conj (traceRow_definable (.out o') t a)))
  | inPos =>
    exact ((traceRow_definable (.state none) t a).conj
      (traceRow_definable .inPos t a)).disj
      (PolarityDefinable.iEx fun y => (hs y).conj (hi (tm.actionOf y).inputTape))
  | head i sign =>
    exact ((traceRow_definable (.state none) t a).conj
      (traceRow_definable (.head i sign) t a)).disj
      (PolarityDefinable.iEx fun y =>
        (hs y).conj (hh i sign ((tm.actionOf y).workTapes i).2))
  | cell i sign s =>
    exact ((traceRow_definable (.cell i sign s) t a).conj
      ((traceRow_definable (.state none) t a).disj (he i sign))).disj
      (PolarityDefinable.iEx fun y => PolarityDefinable.iEx fun s' =>
        (PolarityDefinable.constant (((tm.actionOf y).workTapes i).1.getD s' = s)).conj
          ((hs y).conj ((traceRow_definable (.head i sign) t a).conj
            (traceRow_definable (.cell i sign s') t a))))

/-- The native tableau transformer has one syntactically positive defining body, uniform over
all input structures and candidate ternary relations. -/
theorem traceStep_polarityDefinable (tm : MultiTapeTM m Bool State) (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    {α : Type} (args : Fin 3 → α) :
    PolarityDefinable (L := Ordered.language L) LFP.policy LFP.headMark true
      (fun j : (i : ι) × Set (Fin 3 → Fin (size i)) => Fin (size j.1))
      (fun _ => LFP.interpretation) (fun j => RelEnv.cons j.2 RelEnv.empty)
      (fun j v => (v ∘ args) ∈ traceStep tm (input j.1) j.2) := by
  change BodyDefinable (L := L) size true _
  simp only [traceStep, OrderHom.coe_mk, Set.mem_ofPred_eq, Function.comp_apply]
  apply PolarityDefinable.iEx
  intro q
  apply PolarityDefinable.conj (numeral_definable true (tagIndex q) (args 0))
  apply PolarityDefinable.disj
  · exact (numeral_definable true 0 (args 1)).conj (initial_definable tm q (args 2))
  · apply PolarityDefinable.ex
    exact (successor_definable true none (some (args 1))).conj
      (rowStep_definable tm input inputFormula hinput q none (some (args 2)))

/-- The native tableau least fixed point is uniformly FO(LFP)-definable. -/
theorem trace_lfp_definable (tm : MultiTapeTM m Bool State) (input : ι → List Bool)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (hinput : ∀ i s (a : Fin (size i)),
      (inputFormula s).Realize ![a] ↔ inputAt (input i) a.val = s)
    {α : Type} (args : Fin 3 → α) :
    Operator.Definable (L := Ordered.language L) LFP.policy
      (fun i => Fin (size i)) (fun _ => LFP.interpretation) (fun _ => RelEnv.empty)
      (fun i v => (v ∘ args) ∈ (traceStep tm (input i)).lfp) := by
  apply LFP.definable_lfp_vars (fun i _ => traceStep tm (input i)) args
  exact traceStep_polarityDefinable tm input inputFormula hinput Sum.inr

end Cslib.Complexity.ImmermanVardi.Tableau
