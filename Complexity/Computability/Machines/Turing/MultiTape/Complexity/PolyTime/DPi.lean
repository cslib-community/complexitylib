/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi

/-!
# Polynomial-time dependent finite table operations

The types of entries may depend on the table index. Each entry has its own encoding; the encoded
words form an ordinary finite table. Construction, fixed-index lookup and update therefore reuse
the existing finite-table calculus without requiring a decoder for any entry encoding.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.dpi`: construct a dependent finite table.
* `Turing.MultiTapeTM.ComputableInPolyTime.dpi_apply`: read a fixed entry.
* `Turing.MultiTapeTM.ComputableInPolyTime.dpi_update`: replace a fixed entry.

## References

Extends the finite-table calculus in
`Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α Index : Type} {Value : Index → Type} [Fintype Index]
    {input : α ↪ List Bool} {enc : ∀ i, Value i ↪ List Bool}

/-- Construct a fixed dependent family, retaining the original input for each entry. -/
@[fun_prop]
theorem dpi {values : α → ∀ i, Value i}
    (hvalues : ∀ i, ComputableInPolyTime (fun a => values a i) input (enc i)) :
    ComputableInPolyTime values input (encDPi enc) :=
  (pi (fun i => (hvalues i).of_enc_eq (encD := encBits)
    (g := fun a => enc i (values a i)) (fun _ => rfl))).of_enc_eq (fun _ => rfl)

/-- Read a fixed dependent-table entry, charging the stored prefix and requiring no default. -/
@[fun_prop]
theorem dpi_apply (enc : ∀ i, Value i ↪ List Bool) (i : Index) :
    ComputableInPolyTime (fun values : ∀ j, Value j => values i)
      (encDPi enc) (enc i) := by
  have htable : ComputableInPolyTime
      (fun values : ∀ j, Value j => fun j => enc j (values j))
      (encDPi enc) (encPi encBits) := of_eq (fun _ => rfl)
  exact ((pi_apply encBits i).comp htable).of_enc_eq (fun _ => rfl)

/-- Update one dependent-table entry while retaining and charging all other entries. -/
@[fun_prop]
theorem dpi_update [DecidableEq Index] {values : α → ∀ i, Value i} {i : Index}
    {value : α → Value i}
    (hvalues : ComputableInPolyTime values input (encDPi enc))
    (hvalue : ComputableInPolyTime value input (enc i)) :
    ComputableInPolyTime (fun a => Function.update (values a) i (value a))
      input (encDPi enc) := by
  apply dpi
  intro j
  by_cases h : j = i
  · subst j
    simpa using hvalue
  · simpa only [Function.update_of_ne h, Function.comp_def] using (dpi_apply enc j).comp hvalues

end Turing.MultiTapeTM.ComputableInPolyTime
