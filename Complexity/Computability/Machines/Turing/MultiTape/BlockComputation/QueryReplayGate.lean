/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayMotion
public import
  Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeEncode

/-!
# Native local replay gate with serialized output

The machine retains the signed input-block origin and expected schedule directions beside the
explicit replay state. Replay reads the original input through its query channel and emits no
intermediate output. At completion the motion check chooses success or FAIL, and the actual
returned local windows pay for serialization in either case.

The machine's fixed initial state contains only zeros and empty buffers. Actual local calls
start through the separately charged checked label loader and `QueryMachine.runFrom`.
No input-dependent initialization, label acquisition or original-input length computation is
provided by fixing this machine's template.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Gate

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- Positive and negative input-origin parts and the expected direction of every head. -/
abbrev Context (k : ℕ) := ℕ × ℕ × (Option (Fin k) → SignType)

/-- The retained scheduling context and the actual runtime replay configuration. -/
abbrev State (k : ℕ) (Q : Type) := Context k × Config k Q

/-- Binary origins and a fixed finite family of direction tags. -/
@[expose] noncomputable def encContext : Context k ↪ List Bool :=
  encPair encNat (encPair encNat (encPi (encFinite SignType)))

/-- Silent replay with a checked motion tag and exact serialized local output. The fixed
initial state is a template; callers separately compute actual `runFrom` starting states. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) where
  init := ((0, 0, fun _ => .zero), (QueryReplay.machine M).init)
  query := fun (_, q) => (QueryReplay.machine M).query q
  next := fun ((context, q), symbol) => (context, (QueryReplay.machine M).next (q, symbol))
  emit _ := []
  halted := fun (_, q) => (QueryReplay.machine M).halted q
  finish := fun ((positive, negative, expected), q) =>
    Encoding.NativeEncode.serialize e
      (q.width, Motion.valid (positive, negative, expected, q), rawResult q)

variable [Finite Q]

/-- Explicit binary replay storage, with the retained scheduling fields charged once. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encPair encContext encConfig

/-- The original-input query is delegated to the active replay configuration. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) := by
  have hq := snd (encContext (k := k)) (encConfig (k := k) (Q := Q))
  exact (budget_comp_linear (QueryReplay.machine_query_inSpace M) hq).of_enc_eq fun _ => rfl

/-- One replay step retains its context and charges the full current runtime storage. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) := by
  have hs := fst (encState (k := k) (Q := Q)) (encOption encBool)
  have hcontext := hs.fst'
  have hq := hs.snd'
  have hsymbol := snd (encState (k := k) (Q := Q)) (encOption encBool)
  have hstep := budget_comp_linear (QueryReplay.machine_next_inSpace M)
    (budget_prod hq hsymbol)
  exact (budget_prod hcontext hstep).of_enc_eq fun _ => rfl

/-- The gate remains silent until its final serialized result. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  budget_const [] (.refl _)

/-- Stopping depends on the actual replay duration counter. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) := by
  have hq := snd (encContext (k := k)) (encConfig (k := k) (Q := Q))
  exact (budget_comp_linear (QueryReplay.machine_halted_inSpace M) hq).of_enc_eq fun _ => rfl

/-- Final output charges motion verification, result extraction and both serialization tags.
The retained windows pay for FAIL as well as success; no callee output stream is stored. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) := by
  have hcontext := fst (encContext (k := k)) (encConfig (k := k) (Q := Q))
  have hq := snd (encContext (k := k)) (encConfig (k := k) (Q := Q))
  have hp := hcontext.fst'
  have hn := hcontext.snd'.fst'
  have hexpected := hcontext.snd'.snd'
  have hmotion := budget_comp_linear (Motion.valid_inSpace (k := k) (Q := Q))
    (budget_prod hp (budget_prod hn (budget_prod hexpected hq)))
  have hraw := budget_comp_linear (rawResult_inSpace (k := k) (Q := Q)) hq
  have hwidth := budget_comp_linear (width_inSpace (k := k) (Q := Q)) hq
  exact (budget_comp_linear (Encoding.NativeEncode.serialize_bits_inSpace (k := k) e)
    (budget_prod hwidth (budget_prod hmotion hraw))).of_enc_eq fun _ => rfl

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Gate
