/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Clocking a Boolean computation to linear time

A Boolean function `f` computable within time `O(T a)` need not be computable in linear time.
On the instances where `T a` happens to be at most linear in the length of the encoded instance,
however, `f` agrees with a function computable within linear time and space: run the machine for
`f` for a linear number of steps and accept exactly when it has halted with output `[true]`.

The cut-off run is the linear saved-coin replay of the deterministic machine
(`Turing.MultiTapePTM.computableInDegree_runClosedCoins`), fed a clock of `A * (n + 1)` coins for
an input of length `n`. Replaying a deterministic machine ignores the coins and runs it for as many
steps as there are coins (`Turing.MultiTapePTM.runClosedCoins_ofDeterministic`). No
time-constructibility assumption on `T` is needed, since the clock only depends on the input
length.

Verifiers in time-bounded alternating classes use this to be linear on every input, while the
membership condition only constrains their values on certificates long enough to pay for the
verification (see `Cslib.Complexity.SigmaTwoTIME`).

## Main results

* `Turing.MultiTapeTM.ComputableInO.exists_linear_eq_of_time_le`: a Boolean function agrees with a
  linear-time function wherever its time bound is linear.
-/

public section

namespace Turing.MultiTapeTM

open MultiTapePTM

/-- `A * (n + 1)` true bits, for a word of length `n`, within linear time and space. -/
private theorem clockWord (A : ℕ) :
    ComputableInO (fun x : List Bool => List.replicate (A * (x.length + 1)) true) encBits encBits
      (fun x => x.length) fun x => x.length := by
  induction A with
  | zero =>
    simpa using (ComputableInO.const (encIn := encBits) (encMid := encBits) ([] : List Bool))
  | succ A ih =>
    have hu : ComputableInO (fun x : List Bool => x.length + 1) encBits encUnary
        (fun x => x.length) fun x => x.length :=
      (ComputableInO.unarySucc'.comp ComputableInO.lengthUnary).mono 3
        (fun x => by simp [encUnary_apply]; omega) (fun x => by simp [encUnary_apply]; omega)
    have h := ih.append hu
      (g := fun x : List Bool => List.replicate ((A + 1) * (x.length + 1)) true)
      (encOut := encBits) fun x => by
        simp only [encBits_apply, encUnary_apply, ← List.replicate_add]
        congr 1
        ring
    exact h.mono 2 (fun x => by omega) (fun x => by omega)

/-- **Clocking a Boolean computation down to linear time.** A Boolean function computable within
time `O(T a)` agrees, on the instances where `T a` is at most `K` times the encoded length plus
`K`, with a function computable within linear time and space. The latter runs the same machine for
a linear number of steps, by replay from a clock of that many coins, and accepts when it has
halted with output `[true]`. -/
theorem ComputableInO.exists_linear_eq_of_time_le {α : Type} {enc : α ↪ List Bool}
    {f : α → Bool} {T S : α → ℕ} (hf : ComputableInO f enc encBool T S) (K : ℕ) :
    ∃ g : α → Bool,
      ComputableInO g enc encBool (fun a => (enc a).length) (fun a => (enc a).length) ∧
      ∀ a, T a ≤ K * (enc a).length + K → g a = f a := by
  obtain ⟨c, ⟨k, State, hfin, tm, htm⟩, -⟩ := hf
  set A := c * (K + 1) + c
  refine ⟨fun a => decide ([true] = (ofDeterministic tm).runClosedCoins
      (List.replicate (A * ((enc a).length + 1)) true) (enc a)), ?_, fun a ha => ?_⟩
  · have hclock := (clockWord A).comp_enc enc
    have hid : ComputableInO (fun a : α => enc a) enc encBits (fun a => (enc a).length)
        (fun a => (enc a).length) := ComputableInO.of_eq fun _ => rfl
    have hrun := (ComputableInO.of_linear
      (computableInDegree_runClosedCoins (ofDeterministic tm))).comp_linear (hclock.prod hid)
    obtain ⟨cr, hcr⟩ := hrun.length_le
    have heq := ComputableInO.eqWords.comp
      ((ComputableInO.const (encIn := enc) (encMid := encBits) [true]).prod hrun)
    refine heq.mono (8 + 4 * cr) (fun a => ?_) fun a => ?_
    · have := hcr a
      simp only [Function.comp_apply, encBits_apply, List.length_singleton] at this ⊢
      nlinarith
    · have := hcr a
      simp only [Function.comp_apply, encBits_apply, List.length_singleton] at this ⊢
      nlinarith
  · dsimp only
    rw [runClosedCoins_ofDeterministic, List.length_replicate]
    have hle : c * (T a + 1) ≤ A * ((enc a).length + 1) := by
      have := Nat.mul_le_mul_left c (Nat.add_le_add_right ha 1)
      simp only [A]
      nlinarith
    rw [((htm a).runFrom_of_le hle).2]
    cases f a <;> rfl

end Turing.MultiTapeTM
