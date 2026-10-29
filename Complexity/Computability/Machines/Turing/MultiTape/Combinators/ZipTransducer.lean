/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelZipTransducer
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds

/-!
# Zip transducers

A zip transducer (`Turing.MultiTapeTM.ZipTransducer`) reads two binary words in lockstep, least
significant digit first, padding the shorter word with `none`. In state `q`, on the pair `(x, y)`
of next digits, it moves to state `(τ.step q (x, y)).1` and emits `(τ.step q (x, y)).2`; when both
words are exhausted it emits `τ.final q`. Every emitted word has length at most two.

On a pair `(a, b)` encoded as `frame (enc₁ a) ++ enc₂ b`, the machine `τ.toTM` copies `enc₁ a` to
its work tape and then reads both words simultaneously. Every two-operand function whose encoded
value is the output of a zip transducer on the encoded operands is therefore computable in time
linear in the encoded pair and in work space linear in the first operand.

## Main results

* `Turing.MultiTapeTM.ZipTransducer.computableInTimeAndSpace`: a function computed by a zip
  transducer with finitely many states on the encoded components of a pair is computable within
  `3 * (encPair enc₁ enc₂ p).length + 1` steps and `(enc₁ p.1).length + 2` work-tape cells.
* `Turing.MultiTapeTM.ZipTransducer.computableInTimeAndSpace_run`: the same on raw words.
* `Turing.MultiTapeTM.ZipTransducer.computableInLinearTimeAndSpace`,
  `Turing.MultiTapeTM.ZipTransducer.computableInDegree`: its linear and degree-one forms.
-/

namespace Turing.MultiTapeTM

namespace ZipTransducer

universe u

variable {Q : Type} [Finite Q] (τ : ZipTransducer Q) {α β γ : Type u}
  {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool} {encOut : γ ↪ List Bool} {f : α × β → γ}

/-- **Two-operand functions computed by a zip transducer.** If the encoded value of `f p` is what
`τ` emits on the encoded components of `p`, then `f` is computable within
`3 * (encPair enc₁ enc₂ p).length + 1` steps and `(enc₁ p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace
    (hf : ∀ p, encOut (f p) = τ.run τ.q₀ (enc₁ p.1) (enc₂ p.2)) :
    ComputableInTimeAndSpace f (encPair enc₁ enc₂) encOut
      (fun p => 3 * (encPair enc₁ enc₂ p).length + 1) (fun p => (enc₁ p.1).length + 2) :=
  ⟨1, State Q, inferInstance, τ.toTM, fun p => by
    rw [hf p, encPair_apply]
    exact τ.computesInTimeAndSpace_toTM (enc₁ p.1) (enc₂ p.2)⟩

/-- `τ` on raw words: on `frame u ++ v` it emits `τ.run τ.q₀ u v` within
`3 * (frame u ++ v).length + 1` steps and `u.length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_run :
    ComputableInTimeAndSpace (fun p : List Bool × List Bool => τ.run τ.q₀ p.1 p.2)
      (encPair encBits encBits) encBits
      (fun p => 3 * (encPair encBits encBits p).length + 1) (fun p => p.1.length + 2) :=
  τ.computableInTimeAndSpace fun _ => rfl

/-- A function computed by a zip transducer is computable in linear time and work space. -/
public theorem computableInLinearTimeAndSpace
    (hf : ∀ p, encOut (f p) = τ.run τ.q₀ (enc₁ p.1) (enc₂ p.2)) :
    ComputableInLinearTimeAndSpace f (encPair enc₁ enc₂) encOut :=
  ⟨3, (τ.computableInTimeAndSpace hf).mono (fun _ => by omega) fun p => by
    have := length_le_encPair_left enc₁ enc₂ p
    omega⟩

/-- A function computed by a zip transducer has cost and output degree one. -/
public theorem computableInDegree
    (hf : ∀ p, encOut (f p) = τ.run τ.q₀ (enc₁ p.1) (enc₂ p.2)) :
    ComputableInDegree f (encPair enc₁ enc₂) encOut 1 1 :=
  let ⟨c, hc⟩ := τ.computableInLinearTimeAndSpace hf
  ComputableInDegree.of_bounds ⟨c, fun _ => by simp⟩ ⟨c, fun _ => by simp⟩ hc

end ZipTransducer

end Turing.MultiTapeTM
