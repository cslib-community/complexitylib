/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Pseudoentropy.HashPair

/-! Hashed-parity observations retain their encoded words and expose efficient named fields. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.HashPair

open Cslib Cslib.Crypto.Pseudoentropy.HashPair Turing.MultiTapeTM
open Cslib.BitString Cslib.Probability

-- The record has precisely the previous right-nested word layout, including the unary index.
example {n count : ℕ} {Image : Type*} (encodeImage : Image ↪ List Bool)
    (observation : Observation n count Image) :
    encObservation encodeImage observation =
      encPair encBits (encPair encUnary (encPair encBits (encPair encBits encBits)))
        (encodeImage observation.image, observation.index.val, List.ofFn observation.matrix,
          List.ofFn observation.digest, List.ofFn observation.query) := rfl

-- Both the finite injective encoding and the sampler's arbitrary image map have the same body.
example {n count : ℕ} {Image : Type*} (encodeImage : Image ↪ List Bool)
    (observation : Observation n count Image) :
    encObservation encodeImage observation = encodeObservation encodeImage observation := rfl

-- The named observation and hidden label recover the complete former dependent-tuple law.
example {n count : ℕ} [NeZero count] {Image : Type*} (f : BitString n → Image) :
    (joint (count := count) f).map (fun (observation, bit) =>
      ((⟨observation.index, (observation.matrix, observation.query), observation.image,
          observation.digest⟩ : Σ i : Fin count, Seed n count × Image × BitString (i.val + 1)),
        bit)) =
      (PMF.uniformOfFintype (Fin count)).bind (fun i =>
        (PMF.uniformOfFintype (Seed n count)).bind (fun seed =>
          (PMF.uniformOfFintype (BitString n)).map (fun x =>
            ((⟨i, (seed, f x, prefixHash i seed x)⟩ :
              Σ i : Fin count, Seed n count × Image × BitString (i.val + 1)), x ⬝ᵥ seed.2)))) := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]

-- Field extraction uses the generated rules, including the digest whose width is dependent.
example {n count : ℕ} {Image : Type} (encodeImage : Image ↪ List Bool) :
    ComputableInPolyTime (fun observation : Observation n count Image =>
      encodeImage observation.image) (encObservation encodeImage) encBits :=
  (encObservation_image_deg encodeImage).computableInPolyTime

example {n count : ℕ} {Image : Type} (encodeImage : Image ↪ List Bool) :
    ComputableInPolyTime (fun observation : Observation n count Image =>
      List.ofFn observation.digest) (encObservation encodeImage) encBits := by fun_prop

-- A nonempty matrix and digest exercise all five fields, with two hash bits selected.
private def twoBitObservation : Observation 1 2 Bool where
  image := true
  index := 1
  matrix := ![true, false]
  digest := ![false, true]
  query := ![true]

example : encObservation encBool twoBitObservation =
    wordObservation [true] 1 [true, false] [false, true] [true] := rfl

-- At zero input width the query and matrix are empty, but the selected digest still has a bit.
private def emptyInputObservation : Observation 0 1 Bool where
  image := false
  index := 0
  matrix := Fin.elim0
  digest := ![false]
  query := Fin.elim0

example : encObservation encBool emptyInputObservation =
    wordObservation [false] 0 [] [false] [] := rfl

end CslibFrontierTests.Crypto.HashPair
