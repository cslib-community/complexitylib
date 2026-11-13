/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Initial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Raw parameters for initializing an ordinary count-bit computation

The source word contains only the count limit, width, requested bit, and claim, all with binary
numeric fields. The long predicate context is stored separately. Native word functions derive
the evaluator's count, width, routing metadata, header and status fields from this source.
Binary height and unary depth are computed from the resulting count word by the existing depth
preparation machine.
-/

public section

namespace Cslib.Circuits.Boolean.CarryLookahead.Query.CountingInput

open Turing Turing.MultiTapeTM ComputableInPolyTime

/-- The raw count limit and selected ordinary count-bit claim. -/
structure Input where
  /-- The binary number of predicate values to count. -/
  count : ℕ
  /-- Binary width and bit index, followed by the claimed value. -/
  query : Initial.Input
  deriving DecidableEq

/-- A framed binary count limit followed by the raw query parameters. -/
enc_structure encInput : Input where count : encNat, query : Initial.encInput

/-- The exact physical raw-parameter word contains no precomputed height or metadata. -/
theorem encInput_eq (a : Input) :
    encInput a = frame (encNat a.count) ++ frame (encNat a.query.width) ++
      frame (encNat a.query.bit) ++ [a.query.claim] := by
  simp [encInput_apply, encInputFields, encPair_apply, List.append_assoc]

/-- The entire initializer source has logarithmic numeric fields. -/
theorem length_encInput (a : Input) :
    (encInput a).length = 2 * a.count.size + 2 * a.query.width.size +
      2 * a.query.bit.size + 4 := by
  simp only [encInput_apply, encInputFields, length_encPair, encNat_apply,
    ← Nat.size_eq_bits_len, Initial.length_encInput]
  omega

/-- A valid query needs only the binary count and width lengths in its initialization budget. -/
theorem length_encInput_le (a : Input) (hbit : a.query.bit < a.query.width) :
    (encInput a).length ≤ 2 * a.count.size + 4 * a.query.width.size + 4 := by
  rw [length_encInput]
  have hsize := Nat.size_le_size hbit.le
  omega

/-- The five fields installed before native count-depth preparation. -/
inductive Field where
  | count | width | metadata | header | status
  deriving DecidableEq

instance : Finite Field :=
  Finite.of_injective (fun field : Field => match field with
    | .count => (0 : Fin 5) | .width => 1 | .metadata => 2 | .header => 3 | .status => 4)
    (by rintro (_ | _ | _ | _ | _) (_ | _ | _ | _ | _) h <;> simp_all)

/-- Every installed field is computed from the actual raw parameter word. -/
@[expose] def word : Field → Input → List Bool
  | .count, a => encNat a.count
  | .width, a => encNat a.query.width
  | .metadata, a => Routing.encPosition (Initial.position a.query)
  | .header, a => [a.query.claim, false]
  | .status, _ => [false]

/-- One fixed native polynomial-time word function computes each field from raw parameters. -/
theorem word_polyTime (field : Field) : ComputableInPolyTime (word field) encInput encBits := by
  have hnat : ComputableInPolyTime (fun n : ℕ => encNat n) encNat encBits :=
    .of_eq fun _ => rfl
  have hposition : ComputableInPolyTime (fun p : Routing.Position => Routing.encPosition p)
      Routing.encPosition encBits := .of_eq fun _ => rfl
  cases field with
  | count => exact hnat.comp (by fun_prop)
  | width => exact hnat.comp (Initial.encInput_width_polyTime (by fun_prop))
  | metadata => exact hposition.comp (Initial.position_polyTime.comp (by fun_prop))
  | header =>
    exact (of_finite (encIn := encBool) (encOut := encBits) (fun claim => [claim, false])).comp
      (Initial.encInput_claim_polyTime (by fun_prop))
  | status => exact const [false]

end Cslib.Circuits.Boolean.CarryLookahead.Query.CountingInput
