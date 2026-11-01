/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteEvaluator
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.WidthSpace
public import Complexity.Computability.TreeEval.Ary.Packed.ParametersSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Streamed native initialization of the concrete evaluator

Runtime input length, block width, schedule and horizon determine the selected packed parameters.
Each subsequent clock appends one padded zero field cell. The assignment capacity grows by one
alphabet factor during each child-coordinate clock, so no binary length expands into a bank or
power in a single transition. The final state supplies the existing raw evaluator's initial call.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Initializer

open MultiTapeTM MultiTapeTM.ComputableInSpace Cslib.TreeEval.Ary.Packed

/-- Runtime input length, block width, schedule number and horizon. -/
abbrev Args := ℕ × ℕ × ℕ × ℕ

/-- Actual runtime arguments and selected chunk width/count, alphabet and field modulus. -/
abbrev Metadata := Args × (ℕ × ℕ × ℕ × ℕ)

/-- Retained metadata, cursor, accumulated padded bank and assignment capacity. -/
abbrev State := Metadata × ℕ × List ℕ × ℕ

/-- Runtime arguments are stored as four binary naturals. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))

/-- Selected parameters are charged beside the original runtime arguments. -/
@[expose] noncomputable def encMetadata : Metadata ↪ List Bool :=
  encPair encArgs encParameters

/-- Every accumulated field cell and capacity bit is charged as it is produced. -/
@[expose] noncomputable def encState : State ↪ List Bool :=
  encPair encMetadata (encPair encNat (encPair (encList encNat) encNat))

/-- Compute selected packing metadata without allocating the bank or assignment capacity. -/
@[expose] def prepare (k s : ℕ) : Args → State := fun args =>
  let (_, b, _, _) := args
  ((args, parameters (k * 3 + 1) (Encoding.width k s b)), 0, [], 1)

/-- Append one padded zero cell and grow capacity only during actual child-coordinate clocks. -/
@[expose] def step (k : ℕ) : State → State :=
  fun (metadata, cursor, bank, limit) =>
    let (_, (_, r, alphabet, p)) := metadata
    let d := k * 3 + 1
    if cursor < (d + 1) * r then
      (metadata, cursor + 1, bank ++ [p], if cursor < d * r then limit * alphabet else limit)
    else (metadata, cursor, bank, limit)

/-- Fixed empty halted template; actual runtime initialization starts through `runFrom`. -/
@[expose] def template : State := (((0, 0, 0, 0), (0, 0, 0, 0)), 0, [], 1)

/-- Silent streamed bank construction with one cell appended per physical clock. -/
@[expose] def machine (k : ℕ) : QueryMachine State where
  init := template
  query _ := 0
  next := fun (state, _) => step k state
  emit _ := []
  halted := fun (metadata, cursor, _, _) =>
    let (_, (_, r, _, _)) := metadata
    decide (((k * 3 + 1) + 1) * r ≤ cursor)
  finish _ := []

/-- Read the concrete evaluator's actual runtime initial caller from the completed bank. -/
@[expose] def result (k : ℕ) : State → RawController.Query.Context ConcreteSupplier.Context :=
  fun (((N, b, σ, q), (m, r, alphabet, p)), _, bank, limit) =>
    ((N, b, σ, q, m, alphabet, limit), (p, k * 3 + 1, r), bank, [], some (1, 0))

/-- Preparing selected runtime metadata is linear in actual binary argument storage. -/
theorem prepare_inSpace (k s : ℕ) : ComputableInSpace (prepare k s) encArgs encState
    (fun a => (encArgs a).length) := by
  have hid : ComputableInSpace (fun a : Args => a) encArgs encArgs
      (fun a => (encArgs a).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hb := (snd encNat (encPair encNat (encPair encNat encNat))).fst'
  have hwidth := budget_comp_linear (Encoding.width_inSpace k s) hb
  have hparams := budget_comp_linear parameters_inSpace
    (budget_prod (budget_const (encB := encNat) (k * 3 + 1) (.refl _)) hwidth)
  exact (budget_prod (budget_prod hid hparams) (budget_prod
    (budget_const (encB := encNat) 0 (.refl _)) (budget_prod
      (budget_const (encB := encList encNat) [] (.refl _))
      (budget_const (encB := encNat) 1 (.refl _))))).of_enc_eq fun _ => rfl

/-- Each streamed update uses space linear in its actual accumulated state. -/
theorem step_inSpace (k : ℕ) : ComputableInSpace (step k) encState encState
    (fun a => (encState a).length) := by
  have hmeta := fst encMetadata (encPair encNat (encPair (encList encNat) encNat))
  have hrest := snd encMetadata (encPair encNat (encPair (encList encNat) encNat))
  have hparams := hmeta.snd'
  have hr := hparams.snd'.fst'
  have halphabet := hparams.snd'.snd'.fst'
  have hp := hparams.snd'.snd'.snd'
  have hcursor := hrest.fst'
  have hbank := hrest.snd'.fst'
  have hlimit := hrest.snd'.snd'
  have hd := budget_const (encIn := encState) (encB := encNat) (k * 3 + 1) (.refl _)
  have htotal := budget_natMul (budget_natSucc hd) hr
  have hchildren := budget_natMul hd hr
  have hlimit' := budget_ite (budget_natLt hcursor hchildren)
    (budget_natMul hlimit halphabet) hlimit
  have hnext := budget_prod hmeta (budget_prod (budget_natSucc hcursor)
    (budget_prod (budget_snoc hbank hp) hlimit'))
  have hid : ComputableInSpace (fun a : State => a) encState encState
      (fun a => (encState a).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  refine (budget_ite (budget_natLt hcursor htotal) hnext hid).of_enc_eq ?_
  rintro ⟨⟨args, m, r, alphabet, p⟩, cursor, bank, limit⟩
  by_cases ht : cursor < (k * 3 + 1 + 1) * r <;>
    by_cases hc : cursor < (k * 3 + 1) * r <;>
      simp [step, ht, hc, encState, encPair_apply]

/-- Extract the actual evaluator header, padded bank and initial call mode natively. -/
theorem result_inSpace (k : ℕ) : ComputableInSpace (result k) encState
    (RawController.Query.encContext ConcreteSupplier.encContext)
    (fun a => (encState a).length) := by
  have hmeta := fst encMetadata (encPair encNat (encPair (encList encNat) encNat))
  have hrest := snd encMetadata (encPair encNat (encPair (encList encNat) encNat))
  have hargs := hmeta.fst'
  have hparams := hmeta.snd'
  have hN := hargs.fst'
  have hb := hargs.snd'.fst'
  have hσ := hargs.snd'.snd'.fst'
  have hq := hargs.snd'.snd'.snd'
  have hm := hparams.fst'
  have hr := hparams.snd'.fst'
  have halphabet := hparams.snd'.snd'.fst'
  have hp := hparams.snd'.snd'.snd'
  have hbank := hrest.snd'.fst'
  have hlimit := hrest.snd'.snd'
  have hcontext := budget_prod hN (budget_prod hb (budget_prod hσ (budget_prod hq
    (budget_prod hm (budget_prod halphabet hlimit)))))
  have hheader := budget_prod hp (budget_prod
    (budget_const (encB := encNat) (k * 3 + 1) (.refl _)) hr)
  have hstack := budget_const (encIn := encState) (encB := encList RawController.encFrame)
    [] (.refl _)
  have hmode := budget_const (encIn := encState)
    (encB := encOption (encPair encNat encNat)) (some (1, 0)) (.refl _)
  exact (budget_prod hcontext (budget_prod hheader
    (budget_prod hbank (budget_prod hstack hmode)))).of_enc_eq fun _ => rfl

/-- No original input bit is needed during bank construction. -/
theorem machine_query_inSpace (k : ℕ) : ComputableInSpace (machine k).query encState encNat
    (fun a => (encState a).length) := budget_const 0 (.refl _)

/-- Machine transitions use the certified streamed update. -/
theorem machine_next_inSpace (k : ℕ) : ComputableInSpace (machine k).next
    (encPair encState (encOption encBool)) encState
    (fun a => (encPair encState (encOption encBool) a).length) := by
  have h : ComputableInSpace (fun a : State × Option Bool => step k a.1)
      (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) :=
    budget_comp_linear (step_inSpace k) (fst encState (encOption encBool))
  exact h.of_enc_eq fun _ => rfl

/-- Initialization emits no word. -/
theorem machine_emit_inSpace (k : ℕ) : ComputableInSpace (machine k).emit
    (encPair encState (encOption encBool)) encBits
    (fun a => (encPair encState (encOption encBool) a).length) := budget_const [] (.refl _)

/-- The final cursor comparison uses only actual binary metadata. -/
theorem machine_halted_inSpace (k : ℕ) : ComputableInSpace (machine k).halted encState encBool
    (fun a => (encState a).length) := by
  have hmeta := fst encMetadata (encPair encNat (encPair (encList encNat) encNat))
  have hrest := snd encMetadata (encPair encNat (encPair (encList encNat) encNat))
  have hr := hmeta.snd'.snd'.fst'
  have htotal := budget_natMul
    (budget_const (encIn := encState) (encB := encNat) (k * 3 + 1 + 1) (.refl _)) hr
  exact (budget_finite (encC := encBool) Bool.not (budget_natLt hrest.fst' htotal)).of_enc_eq
    fun ⟨⟨args, m, r, alphabet, p⟩, cursor, bank, limit⟩ => by
      by_cases h : cursor < (k * 3 + 1 + 1) * r
      · simp [machine, h, Nat.not_le_of_gt h]
      · simp [machine, h, Nat.le_of_not_gt h]

/-- The completed bank is returned as state rather than an output stream. -/
theorem machine_finish_inSpace (k : ℕ) : ComputableInSpace (machine k).finish encState encBits
    (fun a => (encState a).length) := budget_const [] (.refl _)

end Turing.MultiTapePTM.BlockComputation.Initializer
