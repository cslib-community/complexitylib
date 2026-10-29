/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.UnaryMachines
import Lean.Elab.Command

/-! Binary counts, zero workspace, growing output and the original complete trajectory contract. -/

@[expose] public section
namespace ComplexityTests.Internal.OCountedIteration
open Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal.BinaryCounter

private def unitWord : Unit ↪ List Bool :=
  ⟨fun _ => [], by intro a b _; cases a; cases b; rfl⟩

-- An arbitrary binary runtime count needs no unary materialization or positive state workspace.
example {γ β : Type} [Inhabited β] {input : γ ↪ List Bool} {state : β ↪ List Bool}
    {n : γ → ℕ} {init : γ → β} {step : β → β}
    {Tn Ti Sn Si R Q B : γ → ℕ} {Ts Ss : β → ℕ}
    (hn : ComputableInO n input encNat Tn Sn)
    (hi : ComputableInO init input state Ti Si)
    (hs : ComputableInO step state state Ts Ss)
    (hr : ∀ x, ∀ j ≤ n x, Ts (step^[j] (init x)) ≤ R x)
    (hq : ∀ x, ∀ j ≤ n x, Ss (step^[j] (init x)) ≤ Q x)
    (hb : ∀ x, ∀ j ≤ n x, (state (step^[j] (init x))).length ≤ B x) :
    ComputableInO (fun x => step^[n x] (init x)) input state
      (fun x => Tn x + Ti x + (n x + 1) * (R x + B x + ((encNat (n x)).length + 1) ^ 2))
      (fun x => Sn x + Si x + Q x + B x + (encNat (n x)).length) ∧
    countStep Nat.succ (some (0, 7)) = none ∧
    countStep Nat.succ (some (1, 7)) = some (0, 8) ∧
    countStep Nat.succ none = none ∧
    (countStep Nat.succ)^[5] (some (5, 3)) = some (0, 8) ∧
    ComputableInO (fun _ : ℕ => ()) encNat unitWord
      (fun n => (encNat n).length + (encNat n).length +
        (n + 1) * (0 + 0 + ((encNat n).length + 1) ^ 2))
      (fun n => (encNat n).length + 0 + 0 + 0 + (encNat n).length) := by
  refine ⟨ComputableInO.iterate hn hi hs hr hq hb, rfl, rfl, rfl, by decide, ?_⟩
  have hn₀ : ComputableInO (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) (fun n => (encNat n).length) := .of_eq fun _ => rfl
  have hi₀ : ComputableInO (fun _ : ℕ => ()) encNat unitWord
      (fun n => (encNat n).length) (fun _ => 0) := .constZero ()
  have hs₀ : ComputableInO (fun u : Unit => u) unitWord unitWord
      (fun _ => 0) (fun _ => 0) := .of_eq fun _ => rfl
  have h := ComputableInO.iterate hn₀ hi₀ hs₀ (R := fun _ => 0) (Q := fun _ => 0)
    (B := fun _ => 0) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
    (fun _ _ _ => by change 0 ≤ 0; exact le_rfl)
  exact h.of_enc_eq (g := fun _ : ℕ => ()) fun _ => rfl

private theorem prefix_iterate (k : ℕ) :
    (fun w : List Bool => true :: w)^[k] [] = List.replicate k true := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, List.replicate_succ]

-- The state grows with the counter's VALUE. Its full output length is retained in workspace.
theorem growingOutput : ComputableInO (fun n : ℕ => List.replicate n true) encNat encBits
    (fun n => (encNat n).length + (encNat n).length +
      (n + 1) * (n + n + ((encNat n).length + 1) ^ 2))
    (fun n => (encNat n).length + 0 + n + n + (encNat n).length) := by
  have hn : ComputableInO (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) (fun n => (encNat n).length) := .of_eq fun _ => rfl
  have hi : ComputableInO (fun _ : ℕ => ([] : List Bool)) encNat encBits
      (fun n => (encNat n).length) (fun _ => 0) := .constZero []
  have hs : ComputableInO (fun w : List Bool => true :: w) encBits encBits
      List.length List.length := .of_linear (.of_transducer
        Internal.Unary.unarySuccTransducer fun w => (Internal.Unary.unarySuccRun w).1.symm)
  have h := ComputableInO.iterate hn hi hs (R := id) (Q := id) (B := id)
    (fun n j hj => by simpa only [prefix_iterate, List.length_replicate, id_eq] using hj)
    (fun n j hj => by simpa only [prefix_iterate, List.length_replicate, id_eq] using hj)
    (fun n j hj => by
      simpa only [prefix_iterate, encBits_apply, List.length_replicate, id_eq] using hj)
  simpa only [prefix_iterate, id_eq] using h

example (T : ℕ → ℕ) :
    (¬ ComputableInO (fun n : ℕ => List.replicate n true) encNat encBits T (fun _ => 0)) ∧
    ComputableInO (fun p : ℕ × ℕ => decide (p.1 < p.2))
      (encPair encNat encNat) encBool
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      (fun p => (encPair encNat encNat p).length + 1) := by
  refine ⟨?_, .natLt⟩
  rintro ⟨c, _, hlen⟩
  have h := hlen (c + 1)
  simp only [encBits_apply, List.length_replicate, Nat.zero_add, Nat.mul_one] at h
  omega

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterateWhile,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp_linear,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.exists_onWords] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

end ComplexityTests.Internal.OCountedIteration
