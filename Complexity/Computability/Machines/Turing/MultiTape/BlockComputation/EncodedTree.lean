/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputationTree
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding

/-!
# The explicit Boolean Tree Evaluation instance for an HPV computation

The fixed-width view codec instantiates the decreasing-dependency unfolding in the existing
`Ary.Tree`. Its root decodes to the true leaving view exactly for the actual movement schedule;
a wrong schedule decodes to FAIL. This construction supplies a concrete Boolean value width,
not an assumed encoding of an arbitrarily large alphabet.

This is the semantic Tree Evaluation reduction. Native implicit gate/leaf access and the
complete simulator resource certificate remain separate obligations.

## References

* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025], arXiv v1, §3.2,
  “Finishing”: unfold the decreasing computation into a tree. Here `q` intervals of `b` steps
  give height `q`, fan-in `3*k+1`, and the explicit `Encoding.width k s b` Boolean value width.
  The aligned three-window model and source padding are library adaptations; this wrapper
  does not claim the paper's native time-space simulation theorem.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation

open Cslib.TreeEval MultiTapeNTM.ChoiceTable

variable {k q s b : ℕ} {State : Type} [NeZero b]

/-- The concrete Boolean tree, with one linear-width encoded interval value at every node. -/
@[expose] noncomputable def encodedTree (machine : MultiTapePTM k Bool State)
    (input : List Bool) (b : ℕ) [NeZero b] (σ : Schedule k q) (e : State ≃ Fin s) :
    Ary.Tree (k * 3 + 1) (Encoding.width k s b) q :=
  tree machine input b σ (Encoding.encode e) (Encoding.decode e) q q

/-- Decoding the root recovers the actual functional computation, including FAIL. -/
theorem decode_eval_encodedTree (machine : MultiTapePTM k Bool State) (input : List Bool)
    (σ : Schedule k q) (e : State ≃ Fin s) :
    Encoding.decode e (encodedTree machine input b σ e).eval = value machine input b σ q := by
  rw [encodedTree, eval_tree machine input b σ (Encoding.encode e) (Encoding.decode e)
    (Encoding.decode_encode e) le_rfl le_rfl, Encoding.decode_encode]

/-- A successful decoded root validates the complete schedule and has the exact true view. -/
theorem decode_eval_encodedTree_eq_some_iff (machine : MultiTapePTM k Bool State)
    (input : List Bool) (σ : Schedule k q) (e : State ≃ Fin s) (v : View k State b) :
    Encoding.decode e (encodedTree machine input b σ e).eval = some v ↔
      actualSchedule machine input b (q := q) = σ ∧ v = trueView machine input b σ q := by
  rw [decode_eval_encodedTree]
  exact value_final_eq_some_iff machine input b σ v

/-- A wrong movement guess produces the distinct FAIL code at the root. -/
theorem decode_eval_encodedTree_eq_none_iff (machine : MultiTapePTM k Bool State)
    (input : List Bool) (σ : Schedule k q) (e : State ≃ Fin s) :
    Encoding.decode e (encodedTree machine input b σ e).eval = none ↔
      actualSchedule machine input b (q := q) ≠ σ := by
  rw [decode_eval_encodedTree]
  exact value_final_eq_none_iff machine input b σ

/-- Only a halted view with exactly the accepting output is accepting. -/
@[expose] def acceptingView (v : View k State b) : Bool :=
  v.1.1.isNone && decide (v.1.2.2 = OutputTrack.accept)

omit [NeZero b] in
private theorem trueView_control (machine : MultiTapePTM k Bool State) (input : List Bool)
    (σ : Schedule k q) (n : ℕ) :
    (trueView machine input b σ n).1 =
      (boundary machine input b (q := q) n).blockControl b := by
  cases n with
  | zero =>
    have hh : ∀ head : Option (Fin k),
        ((Cfg.init machine.initial input).headPos head : ZMod b) = 0 :=
      fun head => by rw [Cfg.headPos_init, Int.cast_zero]
    simp only [trueView, initialView, boundary, intervalStart_zero, Cfg.blockControl, funext hh]
    rfl
  | succ n => rfl

/-- The Boolean root test agrees with native halting/output semantics and validates all labels. -/
theorem accepting_eval_encodedTree_iff (machine : MultiTapePTM k Bool State)
    (input : List Bool) (σ : Schedule k q) (e : State ≃ Fin s) :
    (Encoding.decode e (encodedTree machine input b σ e).eval).elim false acceptingView = true ↔
      actualSchedule machine input b (q := q) = σ ∧
        (boundary machine input b (q := q) q).state = none ∧
        (boundary machine input b (q := q) q).output = [true] := by
  rw [decode_eval_encodedTree]
  cases hv : value machine input b σ q with
  | none =>
    have hwrong := (value_final_eq_none_iff machine input b σ).mp hv
    simp [hwrong]
  | some v =>
    have hgood := (value_final_eq_some_iff machine input b σ v).mp hv
    obtain ⟨hschedule, rfl⟩ := hgood
    simp only [Option.elim_some, acceptingView, trueView_control, Cfg.blockControl,
      Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq,
      OutputTrack.ofWord_eq_accept_iff, hschedule, true_and]

/-- Specializing the decoded accepting root to the original deterministic machine. -/
theorem accepting_eval_encodedTree_ofDeterministic_iff (M : MultiTapeTM k Bool State)
    (input : List Bool) (σ : Schedule k q) (e : State ≃ Fin s) :
    (Encoding.decode e (encodedTree (ofDeterministic M) input b σ e).eval).elim false
        acceptingView = true ↔
      actualSchedule (ofDeterministic M) input b (q := q) = σ ∧
        (M.runFrom (Cfg.init M.q₀ input) (q * b)).state = none ∧
        (M.runFrom (Cfg.init M.q₀ input) (q * b)).output = [true] := by
  rw [accepting_eval_encodedTree_iff (b := b) (ofDeterministic M) input σ e,
    boundary_ofDeterministic input b M le_rfl]

end Turing.MultiTapePTM.BlockComputation
