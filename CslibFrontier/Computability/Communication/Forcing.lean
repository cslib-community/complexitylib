/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Rectangle
public import CslibFrontier.Computability.Communication.Operations
import Mathlib.Tactic.Tauto

/-!
# Forcing outputs in a communication tree

Ignore the original message functions and let each player choose a child at their own nodes.
`CanForce` is backward induction for this finite perfect-information game. `steer` turns
input-dependent winning goals for both players into an actual communication protocol of the
same depth: each player's new messages depend only on that player's input.

This formalizes [ChukhinKulikovMihajlinSmal2026], Lemma 5.1 (printed p. 10; PDF p. 11),
and the deterministic protocol construction in the proof of Lemma 5.2 (printed p. 11; PDF p. 12).
Goals here are predicates on output labels; the paper uses predicates on
leaf occurrences. `labelLeaves` supplies exactly these occurrence labels, reusing `leaf` and
`leafOutput`.
The large-rectangle probability bound and the main communication lower bounds are not proved here.

## Main results

* `canForce_not_iff`: exactly one player can force a goal or its complement.
* `run_steer`: the constructed protocol meets both winning goals simultaneously.
* `depth_steer`: steering preserves the entire tree depth.
-/

public section
namespace Cslib.Communication.Protocol

variable {X Y Z A B : Type*}

/-- Run the original tree but report its leaf occurrence, numbered as in `leaf`. -/
@[expose] def labelLeaves : (p : Protocol X Y Z) → Protocol X Y (Fin p.leafCount)
  | output _ => output ⟨0, by simp⟩
  | alice send p q => alice send
      (p.labelLeaves.map (Fin.castAdd q.leafCount)) (q.labelLeaves.map (Fin.natAdd p.leafCount))
  | bob send p q => bob send
      (p.labelLeaves.map (Fin.castAdd q.leafCount)) (q.labelLeaves.map (Fin.natAdd p.leafCount))

/-- Labeling occurrences preserves communication depth. -/
@[simp] theorem depth_labelLeaves (p : Protocol X Y Z) : p.labelLeaves.depth = p.depth := by
  induction p with
  | output z => rfl
  | alice send p q ihp ihq | bob send p q ihp ihq => simp [labelLeaves, ihp, ihq]

/-- The occurrence reported by the constructed protocol is the existing rectangle API's leaf. -/
@[simp] theorem run_labelLeaves (p : Protocol X Y Z) (x : X) (y : Y) :
    p.labelLeaves.run x y = p.leaf x y := by
  induction p with
  | output z => simp [labelLeaves]
  | alice send p q ihp ihq => simp [labelLeaves, ihp, ihq]
  | bob send p q ihp ihq => simp [labelLeaves, ihp, ihq]

/-- Relabeling occurrences with their original output recovers the original execution. -/
theorem leafOutput_run_labelLeaves (p : Protocol X Y Z) (x : X) (y : Y) :
    p.leafOutput (p.labelLeaves.run x y) = p.run x y := by
  rw [run_labelLeaves, ← run_eq_leafOutput_leaf]

/-- Backward induction. `true` is Alice, `false` is Bob. At a player's own node,
one winning child suffices; at the opponent's node both children must be winning. -/
@[expose] def CanForce (player : Bool) (goal : Z → Prop) : Protocol X Y Z → Prop
  | output z => goal z
  | alice _ p q => if player then CanForce player goal p ∨ CanForce player goal q
      else CanForce player goal p ∧ CanForce player goal q
  | bob _ p q => if player then CanForce player goal p ∧ CanForce player goal q
      else CanForce player goal p ∨ CanForce player goal q

/-- Finite perfect-information determinacy, including exclusion of simultaneous wins. -/
theorem canForce_not_iff (p : Protocol X Y Z) (player : Bool) (goal : Z → Prop) :
    p.CanForce (!player) (fun z => ¬ goal z) ↔ ¬ p.CanForce player goal := by
  classical
  induction p generalizing player with
  | output z => simp [CanForce]
  | alice send p q ihp ihq | bob send p q ihp ihq =>
    have hp := ihp player
    have hq := ihq player
    cases player <;>
      simp [CanForce] at hp hq ⊢ <;> tauto

open scoped Classical in
/-- Replace message functions with winning-child choices. A player chooses the left child
when that child is winning for their own goal, and the right child otherwise. -/
noncomputable def steer (p : Protocol X Y Z) (leftGoal : A → Z → Prop)
    (rightGoal : B → Z → Prop) : Protocol A B Z :=
  match p with
  | output z => output z
  | alice _ p q => alice (fun a => decide (¬ p.CanForce true (leftGoal a)))
      (p.steer leftGoal rightGoal) (q.steer leftGoal rightGoal)
  | bob _ p q => bob (fun b => decide (¬ p.CanForce false (rightGoal b)))
      (p.steer leftGoal rightGoal) (q.steer leftGoal rightGoal)

/-- No extra communication is needed to steer a tree. -/
@[simp] theorem depth_steer (p : Protocol X Y Z) (leftGoal : A → Z → Prop)
    (rightGoal : B → Z → Prop) : (p.steer leftGoal rightGoal).depth = p.depth := by
  induction p with
  | output z => rfl
  | alice send p q ihp ihq | bob send p q ihp ihq => simp [steer, ihp, ihq]

/-- On inputs where each player can force their own goal, the actual run satisfies both. -/
theorem run_steer (p : Protocol X Y Z) (leftGoal : A → Z → Prop)
    (rightGoal : B → Z → Prop) (a : A) (b : B)
    (ha : p.CanForce true (leftGoal a)) (hb : p.CanForce false (rightGoal b)) :
    leftGoal a ((p.steer leftGoal rightGoal).run a b) ∧
      rightGoal b ((p.steer leftGoal rightGoal).run a b) := by
  classical
  induction p with
  | output z => exact ⟨ha, hb⟩
  | alice send p q ihp ihq =>
    simp only [CanForce, ↓reduceIte] at ha hb
    by_cases h : p.CanForce true (leftGoal a)
    · simpa [steer, h] using ihp h hb.1
    · simpa [steer, h] using ihq (ha.resolve_left h) hb.2
  | bob send p q ihp ihq =>
    simp only [CanForce, ↓reduceIte] at ha hb
    by_cases h : p.CanForce false (rightGoal b)
    · simpa [steer, h] using ihp ha.1 h
    · simpa [steer, h] using ihq ha.2 (hb.resolve_left h)

/-- Compatible forcing goals define a rectangle solved without increasing depth. -/
theorem steer_solves (p : Protocol X Y Z) (leftGoal : A → Z → Prop)
    (rightGoal : B → Z → Prop) (R : A → B → Z → Prop)
    (h : ∀ a b z, leftGoal a z → rightGoal b z → R a b z) :
    (p.steer leftGoal rightGoal).Solves R
      {a | p.CanForce true (leftGoal a)} {b | p.CanForce false (rightGoal b)} := by
  intro a ha b hb
  obtain ⟨hl, hr⟩ := run_steer p leftGoal rightGoal a b ha hb
  exact h a b _ hl hr

end Cslib.Communication.Protocol
