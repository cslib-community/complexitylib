/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.TrackedRun

/-!
# Extending polynomial-time Boolean functions to all bit words

A Boolean function computable in polynomial time on an explicit encoding `enc : α ↪ List Bool`
extends to a Boolean function computable in polynomial time on raw bit words `encBits` that agrees
with it on every codeword `enc a` (`Turing.MultiTapeTM.ComputableInPolyTime.exists_bool_extension`),
with no decoder hypothesis on `enc`. The extension runs the underlying machine for its polynomial
step bound via `Turing.MultiTapeTM.trackedRun` and accepts when the tracked output is `[true]`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.exists_bool_extension`: extend a polynomial-time Boolean
  function from `enc` to `encBits`.
* `Turing.MultiTapeTM.ComputableInPolyTime.exists_pair_bool_extension`: extend a polynomial-time
  pair verifier from `encPair enc encBits` to `encPair encBits encBits`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib

variable {α : Type} {enc : α ↪ List Bool}

/-- **Extension of a polynomial-time Boolean function to all words.** A Boolean function computable
in polynomial time on `enc` extends to a Boolean function computable in polynomial time on `encBits`
that agrees with it on every codeword `enc a`. -/
theorem exists_bool_extension {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) :
    ∃ g : List Bool → Bool, ComputableInPolyTime g encBits encBool ∧ ∀ a, g (enc a) = f a := by
  obtain ⟨t, _, ht, -, k, State, hfin, tm, htm⟩ := hf
  obtain ⟨c, d, ht⟩ := polynomiallyBounded_iff_le.mp ht
  let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  have hp (w : List Bool) : t w.length ≤ p.eval w.length := by
    simpa [p] using ht w.length
  refine ⟨fun w => decide ((trackedRun tm (w, p.eval w.length)).1.output = [true]), ?_,
    fun a => ?_⟩
  · have hsteps : ComputableInPolyTime (fun w : List Bool => p.eval w.length) encBits encUnary :=
      (ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length encBits)
    have hrun := (computableInPolyTime_trackedRun tm).comp (ComputableInPolyTime.id'.prod hsteps)
    exact ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.finiteCfg_output.comp (.fst' hrun)) (.const [true])
  · dsimp only
    rw [(trackedAgrees_trackedRun tm (enc a) (p.eval (enc a).length)).output,
      ((htm a).runFrom_of_le (hp (enc a))).2]
    cases f a <;> rfl

/-- **Extension of a pair verifier to raw bit words.** A Boolean function computable in polynomial
time on `encPair enc encBits` extends to one computable in polynomial time on
`encPair encBits encBits` that agrees with it on `(enc a, w)`. -/
theorem exists_pair_bool_extension {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ∃ W : List Bool × List Bool → Bool,
      ComputableInPolyTime W (encPair encBits encBits) encBool ∧
        ∀ a w, W (enc a, w) = V (a, w) := by
  obtain ⟨g, hg, hagree⟩ := hV.exists_bool_extension
  exact ⟨fun x => g (encPair encBits encBits x),
    hg.comp (ComputableInPolyTime.of_eq fun _ => rfl), fun a w => hagree (a, w)⟩

end Turing.MultiTapeTM.ComputableInPolyTime
