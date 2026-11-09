/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayLoad
public import
  Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeChecked
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds

/-!
# Native loading from a checked block label

The loader validates an actual serialized label before constructing a replay state. FAIL and
noncanonical labels return `none`; accepted labels supply the explicit windows used by the
existing loader. Input length, block width and both parts of the signed input origin are binary
runtime arguments. The original input word is absent from these arguments. Computing its length
and obtaining an input-dependent label and origin remain separately charged caller operations.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Load.Label

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- Original input length, block width, signed origin parts and an actual serialized label. -/
abbrev Args := ℕ × ℕ × (ℕ × ℕ) × List Bool

/-- Binary numeric metadata and the raw label word, without a copy of the original input. -/
abbrev encArgs : Args ↪ List Bool :=
  encPair encNat (encPair encNat (encPair (encPair encNat encNat) encBits))

/-- Validate the serialized block label and initialize a replay only from accepted data. -/
@[expose] noncomputable def load (e : Q ≃ Fin s) : Args → Option (Config k Q) :=
  fun (N, b, origins, word) =>
    (Encoding.NativeChecked.parse e (b, word)).map fun raw =>
      QueryReplay.Load.load (N, b, origins, raw)

variable [Finite Q]

/-- Parsing, validation and replay initialization all use native space linear in the actual
encoded arguments. The certificate is uniform in all numeric metadata and label contents. -/
theorem load_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (load (k := k) e) encArgs (encOption (encConfig (k := k) (Q := Q)))
      (fun a => (encArgs a).length) := by
  classical
  let empty : RawResult k Q := (none, fun _ => 0, .empty, fun _ => [])
  have hN := fst encNat (encPair encNat (encPair (encPair encNat encNat) encBits))
  have hrest := snd encNat (encPair encNat (encPair (encPair encNat encNat) encBits))
  have hb := hrest.fst'
  have horigins := hrest.snd'.fst'
  have hword := hrest.snd'.snd'
  have hp := budget_comp_linear (Encoding.NativeChecked.parse_inSpace (k := k) e)
    (budget_prod hb hword)
  have hget : ComputableInSpace (fun o : Option (RawResult k Q) => o.getD empty)
      (encOption (encRawResult (k := k) (Q := Q))) (encRawResult (k := k) (Q := Q))
      (fun o => (encOption (encRawResult (k := k) (Q := Q)) o).length) :=
    of_inO (ComputableInDegree.getD (enc₁ := (encRawResult (k := k) (Q := Q))) empty).inO_one
  have hraw := budget_comp_linear hget hp
  have hargs := budget_prod hN (budget_prod hb (budget_prod horigins hraw))
  have hload := budget_comp_linear (QueryReplay.Load.load_inSpace (k := k) (Q := Q)) hargs
  have hsome := budget_comp_linear
    (of_inO (ComputableInDegree.optionSome (enc₁ := (encConfig (k := k) (Q := Q)))
      (enc := encOption (encConfig (k := k) (Q := Q)))).inO_one) hload
  have hisSome := budget_comp_linear
    (of_inO (ComputableInDegree.isSome (encRawResult (k := k) (Q := Q))).inO_one) hp
  refine (budget_ite hisSome hsome
    (budget_const (encB := encOption (encConfig (k := k) (Q := Q))) none (.refl _))).of_enc_eq ?_
  intro a
  rcases a with ⟨N, b, origins, word⟩
  cases h : Encoding.NativeChecked.parse (k := k) e (b, word) <;>
    simp [load, h, empty]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Load.Label
