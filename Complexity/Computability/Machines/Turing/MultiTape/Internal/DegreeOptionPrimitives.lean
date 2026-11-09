/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.WordPredicates

/-!
# Direct degree certificates for option encoding machines

Construction and fixed-default elimination reuse the encoding capability's degree certificates.
The Boolean test retains its constant output degree. No higher tidy calculus is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree
open Internal.WordPredicates

variable {β : Type*} {enc₁ : β ↪ List Bool}

/-- Construct an optional value in an encoding with the option capability. -/
theorem optionSome {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] :
    ComputableInDegree some enc₁ enc 1 1 := OptionEncoding.some

/-- Eliminate an optional value using a fixed default. -/
theorem getD {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] (d : β) :
    ComputableInDegree (fun o => o.getD d) enc enc₁ 1 1 := OptionEncoding.getD d

/-- Whether a standard encoded option holds a value; the Boolean output has degree zero. -/
theorem isSome (enc : β ↪ List Bool) :
    ComputableInDegree (fun o : Option β => o.isSome) (encOption enc) encBool 1 0 := by
  refine ⟨⟨fun o => 2 * (encOption enc o).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, nonemptyT.toTM, fun o => ?_⟩,
    ⟨1, fun o => by simp⟩⟩
  have heq : encBool o.isSome = nonemptyT.run nonemptyT.q₀ (encOption enc o) := by
    cases o with
    | none => rfl
    | some b =>
      change [true] = [true] ++ nonemptyT.run true (enc b)
      rw [nonemptyT_run_true, List.append_nil]
  simpa only [heq] using nonemptyT.computesInTimeAndSpace_toTM (encOption enc o)

end Turing.MultiTapeTM.ComputableInDegree
