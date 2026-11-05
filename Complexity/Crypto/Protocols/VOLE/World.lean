/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.VOLE.Basic
public import Complexity.Computability.Interactive.Basic
import Complexity.Languages.Probabilistic.Oracle.Interaction

/-!
# A cached ideal VOLE world

The existing ideal correlation distribution is exposed through separate sender and receiver
oracles. The first request samples one correlation; all later requests read the same cached
correlation. Neither role can query the other role's interface. Each evaluation of the world
starts a fresh session. Repeated reads do not supply fresh correlations.

## Main definitions

* `voleSenderSpec`, `voleReceiverSpec`: the two role-local setup interfaces.
* `voleWorld`: the shared, lazily sampled ideal correlation in `Interactive.World`.

## Main results

* `voleWorld_cached_sender`, `voleWorld_cached_receiver`: cached requests return the same share.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability Interactive

/-- The sender can read only its two vectors, never the receiver key or tags. -/
abbrev voleSenderSpec (F : Type) (n : ℕ) : OracleSpec Unit :=
  fun _ => (Fin n → F) × (Fin n → F)

/-- The receiver can read only its key and tag vector. -/
abbrev voleReceiverSpec (F : Type) (n : ℕ) : OracleSpec Unit :=
  fun _ => F × (Fin n → F)

/-- One ideal correlation shared between the role-local interfaces and cached for the session.
The initial state is empty, so no key or correlation is supplied as a public parameter. -/
noncomputable def voleWorld (F : Type) [CommRing F] [Fintype F] (n : ℕ) :
    World (voleSenderSpec F n) (voleReceiverSpec F n) where
  State := Option (VOLECorrelation F n)
  init := none
  impl
    | .inl () => fun cache => do
      let c ← match cache with
        | none => voleIdealDist F n
        | some c => pure c
      return (c.senderView, some c)
    | .inr () => fun cache => do
      let c ← match cache with
        | none => voleIdealDist F n
        | some c => pure c
      return (c.receiverView, some c)

variable {F : Type} [CommRing F] [Fintype F] {n : ℕ}

/-- Reading a cached sender share does not resample the correlation. -/
theorem voleWorld_cached_sender (c : VOLECorrelation F n) :
    (voleWorld F n).impl (.inl ()) (some c) = PMF.pure (c.senderView, some c) := by
  simp [voleWorld]

/-- Reading a cached receiver share does not resample the correlation. -/
theorem voleWorld_cached_receiver (c : VOLECorrelation F n) :
    (voleWorld F n).impl (.inr ()) (some c) = PMF.pure (c.receiverView, some c) := by
  simp [voleWorld]

end Cslib.Crypto.Protocols.VOLE
