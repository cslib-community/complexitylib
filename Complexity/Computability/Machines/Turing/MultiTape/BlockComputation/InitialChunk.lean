/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeDecode

/-!
# Native packed chunks of the initial block source

Only the success tag and initial finite control may contain nonzero bits in the initial label.
Reading a requested numeric chunk of this fixed prefix therefore avoids allocating the runtime
blank windows or a padded label. Chunk width and index remain binary runtime inputs.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.InitialChunk

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- The initial label's potentially nonzero prefix; the remaining head/window bits are zero. -/
@[expose] def headerWord (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) : List Bool :=
  true :: List.ofFn (Encoding.encodeState e (some M.q₀))

/-- Binary requested chunk width and index. -/
abbrev Args := ℕ × ℕ

/-- Both requested chunk coordinates are charged by actual binary storage. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool := encPair encNat encNat

/-- Read an initial-source chunk without constructing the label's blank suffix. -/
@[expose] def chunk (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) : Args → ℕ :=
  fun (m, j) => Encoding.NativeDecode.readNat (headerWord M e) (j * m) m

/-- The fixed control prefix is part of the machine; runtime chunk metadata pays only its
actual binary digits. A large binary chunk width does not allocate its numeric magnitude. -/
theorem chunk_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (chunk M e) encArgs encNat (fun a => (encArgs a).length) := by
  have hm := fst encNat encNat
  have hj := snd encNat encNat
  have hprefix := budget_const (encB := encBits) (headerWord M e)
    (show (fun a => (encArgs a).length) ≼ fun a => (encArgs a).length from .refl _)
  exact (budget_comp_linear Encoding.NativeDecode.readNat_inSpace
    (budget_prod hprefix (budget_prod (budget_natMul hj hm) hm))).of_enc_eq fun _ => rfl

end Turing.MultiTapePTM.BlockComputation.InitialChunk
