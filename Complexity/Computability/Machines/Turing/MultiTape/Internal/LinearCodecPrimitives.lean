/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate
-- vendored: codec machines retain crei/tidy-universal @7f7c0696 credit.
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.CodecWordMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Capabilities

/-! # Direct linear capabilities used by codecs

The witnesses normalize only realizing machines. No higher tidy computability rule is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Prepend the marker of the existing option encoding. -/
theorem of_cons_true {f : α → β} (h : ∀ a, encMid (f a) = true :: encIn a) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Encodings.headT none) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Drop the input word's first symbol using the existing head machine. -/
theorem of_tail {f : α → β} (h : ∀ a, encMid (f a) = (encIn a).tail) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Encodings.headT (some false)) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Keep the input word's first symbol using the existing head machine. -/
theorem of_take_one {f : α → β} (h : ∀ a, encMid (f a) = (encIn a).take 1) :
    ComputableInDegree f encIn encMid 1 1 :=
  of_transducer (Encodings.headT (some true)) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Test the encoded input for emptiness using the existing finite transducer. -/
theorem of_isEmpty {f : α → Bool} (h : ∀ a, f a = (encIn a).isEmpty) :
    ComputableInDegree f encIn encBool 1 1 :=
  of_transducer Encodings.isEmptyT fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.isEmptyT_run_true, Encodings.isEmptyT_q₀,
      Encodings.isEmptyT_step, Encodings.isEmptyT_final]

/-- A fixed default on the empty word and a linear certificate on nonempty encoded inputs. -/
theorem of_isEmpty_ite {f : α → β} (d : β) (hd : ∀ a, encIn a = [] → f a = d)
    (h : ComputableInDegree (f ∘ Subtype.val)
      ((Function.Embedding.subtype fun a => (encIn a).isEmpty = false).trans encIn) encMid 1 1) :
    ComputableInDegree f encIn encMid 1 1 := by
  convert ite (c := fun a => (encIn a).isEmpty) (of_isEmpty fun _ => rfl)
    ((const d).restrict _) h using 1
  · funext a
    split_ifs with ha <;> simp_all
  all_goals decide

end Turing.MultiTapeTM.ComputableInDegree
