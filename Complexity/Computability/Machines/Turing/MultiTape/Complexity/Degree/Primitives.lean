/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
import Mathlib.Data.Fintype.Lattice

/-!
# Direct primitives for plain degree bounds

These rules retain independent cost and encoded-output degrees. Constants have cost degree one
and output degree zero; encoded equality uses the upstream copy machine. Output and input
encoding transports reuse the same realizing machine and preserve both degrees, including zero.
No higher computability calculus is used in their proofs.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.const`: a constant encoded result.
* `Turing.MultiTapeTM.ComputableInDegree.of_finite`: a function on any finite input type.
* `Turing.MultiTapeTM.ComputableInDegree.of_eq`: copy an unchanged encoded word.
* `Turing.MultiTapeTM.ComputableInDegree.of_enc_eq`, `.of_encIn_eq`: transport encoded equality.

## References

Uses cslib's constant and copy machines and the independent degree bounds of this library.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {d e : ℕ}

/-- A fixed encoded result has linear cost and constant encoded-output growth. -/
theorem const (b : β) : ComputableInDegree (fun _ : α => b) encIn encMid 1 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encMid) b
  exact ⟨⟨fun _ => c, fun _ => 0, DegreeBounded.const c, DegreeBounded.const 0, h⟩,
    DegreeBounded.const (encMid b).length⟩

/-- A function on a finite input type has linear cost and constant output growth.
The machine has constant time and zero workspace; no inhabitedness assumption is needed. -/
theorem of_finite [Finite α] (f : α → β) : ComputableInDegree f encIn encMid 1 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encMid) f
  refine ⟨⟨fun _ => c, fun _ => 0, DegreeBounded.const c, DegreeBounded.const 0, h⟩, ?_⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, fun a => isEmptyElim a⟩
  · obtain ⟨a₀, ha₀⟩ := Finite.exists_max fun a => (encMid (f a)).length
    exact ⟨_, fun a => by simpa using ha₀ a⟩

/-- Copy a word whose output encoding is exactly its input encoding. -/
theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableInDegree f encIn encMid 1 1 := by
  obtain ⟨k, State, hfin, tm, htm⟩ := computableInTimeAndSpace_id (enc := encIn)
  refine ⟨⟨fun a => (encIn a).length + 1, fun _ => 0,
    DegreeBounded.self.add_const 1, DegreeBounded.const 0,
    k, State, hfin, tm, fun a => ?_⟩, ?_⟩
  · simpa only [h a, id_eq] using htm a
  · exact DegreeBounded.self.mono fun a => by rw [h a]

/-- Equal output words retain the realizing machine and both independent degrees. -/
theorem of_enc_eq {f : α → β} {g : α → γ}
    (hf : ComputableInDegree f encIn encMid d e) (h : ∀ a, encOut (g a) = encMid (f a)) :
    ComputableInDegree g encIn encOut d e := by
  obtain ⟨⟨t, s, ht, hs, k, State, hfin, tm, htm⟩, hl⟩ := hf
  refine ⟨⟨t, s, ht, hs, k, State, hfin, tm, fun a => ?_⟩, ?_⟩
  · simpa only [h a] using htm a
  · exact hl.mono fun a => by rw [h a]

/-- An input map preserving the complete encoded word retains the same machine and degrees.
The semantic map needs no separate computational assumption: the machine sees the same word. -/
theorem of_encIn_eq {α' : Type*} {encIn' : α' ↪ List Bool} {f : α → β}
    (map : α' → α) (henc : ∀ a, encIn' a = encIn (map a))
    (hf : ComputableInDegree f encIn encMid d e) :
    ComputableInDegree (f ∘ map) encIn' encMid d e := by
  obtain ⟨⟨t, s, ⟨ct, ht⟩, ⟨cs, hs⟩, k, State, hfin, tm, htm⟩, ⟨cl, hl⟩⟩ := hf
  refine ⟨⟨fun a => t (map a), fun a => s (map a),
    ⟨ct, fun a => ?_⟩, ⟨cs, fun a => ?_⟩, k, State, hfin, tm, fun a => ?_⟩,
    ⟨cl, fun a => ?_⟩⟩
  · simpa only [henc a] using ht (map a)
  · simpa only [henc a] using hs (map a)
  · simpa only [henc a, Function.comp_apply] using htm (map a)
  · simpa only [henc a, Function.comp_apply] using hl (map a)

end Turing.MultiTapeTM.ComputableInDegree
