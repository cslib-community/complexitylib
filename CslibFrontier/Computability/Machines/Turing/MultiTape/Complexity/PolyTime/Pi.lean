/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time finite table operations

Programs construct finite tables as ordinary functions and use ordinary application and update.
The certificates store the complete table using `encPi` and the existing list machinery.
The index type is fixed independently of the input; values need not be finite or inhabited.
The plain construction, access and update rules are proved in the internal primitives module and
re-exported here. This module adds lookup in a stored table/index pair, and the tidy forms of
construction and fixed-index access that tidy proofs still use.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.ofFn`, `.pi`: construct fixed finite families.
* `Turing.MultiTapeTM.ComputableInPolyTime.pi_apply`, `.pi_update`: fixed-index access.
* `Turing.MultiTapeTM.ComputableInPolyTime.pi_apply'`, `.pi_update'`: computed-index access.
* `Turing.MultiTapeTM.ComputableInPolyTime.pi_eval`: lookup from an encoded table/index pair.

## References

Adapts Computability/Probabilistic/Pi.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to plain polynomial time.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {Index Value : Type}

/-- Evaluate a stored table at a stored index. The product view is registered with `fun_prop`;
for separately computed tables and indices, apply `pi_apply'` to their certificates. -/
@[fun_prop]
theorem pi_eval [Fintype Index] (indexEncoding : Index ↪ List Bool) (enc : Value ↪ List Bool) :
    ComputableInPolyTime (fun pair : (Index → Value) × Index => pair.1 pair.2)
      (encPair (encPi enc) indexEncoding) enc := pi_apply' (fst _ _) (snd _ _)

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α Index Value : Type} {input : α ↪ List Bool} {enc : Value ↪ List Bool}

/-- Construct a list of a fixed number of efficiently computed entries. -/
@[fun_prop]
theorem ofFn {count : ℕ} {values : α → Fin count → Value}
    (hvalues : ∀ i, ComputableTidilyInPolyTime (fun a => values a i) input enc) :
    ComputableTidilyInPolyTime (fun a => List.ofFn (values a)) input (encList enc) :=
  (ComputableInPolyTime.ofFn fun i => (hvalues i).computableInPolyTime).tidy

/-- Construct a table by computing each entry, retaining the original input in each computation. -/
@[fun_prop]
theorem pi [Fintype Index] {values : α → Index → Value}
    (hvalues : ∀ i, ComputableTidilyInPolyTime (fun a => values a i) input enc) :
    ComputableTidilyInPolyTime values input (encPi enc) :=
  (ofFn (fun i => hvalues ((Fintype.equivFin Index).symm i))).of_enc_eq (fun _ => rfl)

/-- Read a fixed entry, charging for the stored prefix without requiring a default value. -/
@[fun_prop]
theorem pi_apply [Fintype Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableTidilyInPolyTime (fun values : Index → Value => values i) (encPi enc) enc :=
  (ComputableInPolyTime.pi_apply enc i).tidy

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
