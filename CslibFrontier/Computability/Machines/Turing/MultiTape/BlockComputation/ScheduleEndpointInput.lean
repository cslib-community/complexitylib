/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleValidationNative
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.FinCases

/-!
# Linear native preparation of encoded schedule queries

The external encoding frames the raw schedule and binary selector, then appends the binary
interval index. One finite native machine extracts all three fields and computes the raw-table
validity bit. All fields are runtime input, including invalid schedules and out-of-range indices.
The cost is linear in the external encoding length; every work head and the input head is restored.

This is the input phase of the endpoint adapter. Selector dispatch and bounded interval
positioning remain separate operations; the validity bit checks the raw schedule only.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointInput

open ScheduleEndpointQuery

/-- Framed raw schedule, framed canonical binary selector, then canonical binary interval. -/
enc_structure encInput : Input where raw : encBits, selector : encNat, interval : encNat

/-- Exact external length, charging framing and both binary indices. -/
theorem length_encInput (a : Input) :
    (encInput a).length = 2 * a.raw.length + 2 * a.selector.bits.length +
      a.interval.bits.length + 2 := by
  simp [encInput_apply, encInputFields, encPair_apply, encNat_apply]
  omega

/-- The four words installed before runtime endpoint dispatch. -/
private inductive Field
  /-- The arbitrary raw schedule. -/
  | raw
  /-- The canonical binary outgoing selector. -/
  | selector
  /-- The canonical binary interval index. -/
  | interval
  /-- One bit checking only raw schedule validity. -/
  | canonical
  deriving DecidableEq

/-- The destination in the protected four-word suffix. -/
private def destination : Field → Fin 4
  | .raw => 0
  | .selector => 1
  | .interval => 2
  | .canonical => 3

/-- Runtime contents of a prepared field. -/
private def word (k : ℕ) (a : Input) : Field → List Bool
  | .raw => a.raw
  | .selector => a.selector.bits
  | .interval => a.interval.bits
  | .canonical => [ScheduleBits.validate k a.raw]

private theorem field_linear (k : ℕ) (field : Field) :
    ComputableInDegree (fun a => word k a field) encInput encBits 1 1 := by
  have hv : ComputableInDegree (ScheduleBits.validate k) encBits encBool 1 1 :=
    .of_transducer (ScheduleValidation.reader k) fun w =>
      (ScheduleValidation.run_eq_validate k w).symm
  cases field with
  | raw => exact encInput_raw_deg
  | selector => exact encInput_selector_deg.of_enc_eq (fun _ => rfl)
  | interval => exact encInput_interval_deg.of_enc_eq (fun _ => rfl)
  | canonical => exact (hv.comp encInput_raw_deg).of_enc_eq (fun _ => rfl)

private def fieldTapes {k S : ℕ} (hk : k ≤ S) (field : Field) :
    Fin (k + 1) ↪ Fin (S + 4) :=
  Fin.Embedding.snoc ((Fin.castLEEmb hk).trans (Fin.castAddEmb 4))
    (a := Fin.natAdd S (destination field)) (by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      change i.val = S + (destination field).val at hv
      have := i.isLt
      omega)

private theorem fieldTapes_last {k S : ℕ} (hk : k ≤ S) (field : Field) :
    fieldTapes hk field (Fin.last k) = Fin.natAdd S (destination field) := by
  simp [fieldTapes]

private theorem fieldTapes_blank {k S : ℕ} (hk : k ≤ S) (field : Field)
    (fields : Fin 4 → List Bool) (hblank : fields (destination field) = []) :
    ∀ j, Fin.append (fun _ : Fin S => ([] : List Bool)) fields (fieldTapes hk field j) = [] := by
  intro j
  cases j using Fin.lastCases with
  | last => simpa [fieldTapes] using hblank
  | cast j => simp [fieldTapes]

/-- Extract all encoded fields and validate the raw table in linear native time. The finite
machine and coefficient are chosen before every request, including malformed raw schedules.
The last four tapes hold raw, selector, interval and the raw validity bit, respectively. -/
theorem exists_prepare (k : ℕ) :
    ∃ (scratch : ℕ) (Q : Type) (_ : Finite Q)
      (tm : MultiTapeTM (scratch + 4) Bool Q) (c : ℕ), ∀ (a : Input) (out : List Bool),
      RunsBetween tm (tapesCfg (encInput a) (fun _ => []) 0 0 out)
        (tapesCfg (encInput a)
          (Fin.append (fun _ : Fin scratch => [])
            ![a.raw, a.selector.bits, a.interval.bits, [ScheduleBits.validate k a.raw]])
          0 0 out)
        (c * ((encInput a).length + 1))
        ((scratch + 4) * (c * ((encInput a).length + 1) + 1)) := by
  classical
  have hf (field : Field) := Internal.NormalForm.linear (field_linear k field)
  choose coeff tapes Q hQ machine hm using hf
  let (field : Field) : Finite (Q field) := hQ field
  let scratch := tapes .raw + tapes .selector + tapes .interval + tapes .canonical
  have hs (field : Field) : tapes field ≤ scratch := by
    cases field <;> dsimp only [scratch] <;> omega
  let write := fun field => (machine field).outputToWord.extendTapes (fieldTapes (hs field) field)
  let tm := (write .raw).seq ((write .selector).seq ((write .interval).seq (write .canonical)))
  let c := 2 * (coeff .raw + coeff .selector + coeff .interval + coeff .canonical) + 8
  refine ⟨scratch, _, inferInstance, tm, c, ?_⟩
  intro a out
  let cfg (fields : Fin 4 → List Bool) :=
    tapesCfg (encInput a) (Fin.append (fun _ : Fin scratch => []) fields) 0 0 out
  have hwrite (field : Field) (fields : Fin 4 → List Bool)
      (hblank : fields (destination field) = []) :
      RunsBetween (write field) (cfg fields)
        (cfg (Function.update fields (destination field) (word k a field)))
        ((2 * coeff field + 2) * ((encInput a).length + 1))
        ((scratch + 4) * ((2 * coeff field + 2) * ((encInput a).length + 1) + 1)) := by
    have h := (hm field a).outputToWord_extendTapes (fieldTapes (hs field) field)
    obtain ⟨ws', emitted, ⟨hw, he⟩, hr⟩ := RunsBetween.of_transformsTapes h
      (ws := Fin.append (fun _ : Fin scratch => []) fields)
      ⟨rfl, fieldTapes_blank (hs field) field fields hblank⟩ 0 out
    rw [hw, he, List.append_nil, fieldTapes_last, ← Fin.append_update_right] at hr
    have hl := (hm field a).length_output_le
    have ht : coeff field * ((encInput a).length + 1) + (word k a field).length + 2 ≤
        (2 * coeff field + 2) * ((encInput a).length + 1) := by
      simp only [encBits_apply] at hl
      nlinarith
    simp only [encBits_apply] at hr
    exact (RunsBetween.of_runFrom hr.1).mono ht
      (Nat.mul_le_mul_left (scratch + 4) (Nat.add_le_add_right ht 1))
  have h0 := hwrite .raw ![[], [], [], []] rfl
  have h1 := hwrite .selector ![a.raw, [], [], []] rfl
  have h2 := hwrite .interval ![a.raw, a.selector.bits, [], []] rfl
  have h3 := hwrite .canonical ![a.raw, a.selector.bits, a.interval.bits, []] rfl
  have h0' : Function.update ![[], [], [], []] (destination .raw) (word k a .raw) =
      ![a.raw, [], [], []] := by ext i; fin_cases i <;> rfl
  have h1' : Function.update ![a.raw, [], [], []] (destination .selector) (word k a .selector) =
      ![a.raw, a.selector.bits, [], []] := by ext i; fin_cases i <;> rfl
  have h2' : Function.update ![a.raw, a.selector.bits, [], []] (destination .interval)
      (word k a .interval) = ![a.raw, a.selector.bits, a.interval.bits, []] := by
    ext i; fin_cases i <;> rfl
  have h3' : Function.update ![a.raw, a.selector.bits, a.interval.bits, []] (destination .canonical)
      (word k a .canonical) =
      ![a.raw, a.selector.bits, a.interval.bits, [ScheduleBits.validate k a.raw]] := by
    ext i; fin_cases i <;> rfl
  rw [h0'] at h0
  rw [h1'] at h1
  rw [h2'] at h2
  rw [h3'] at h3
  have hr := h0.seq (h1.seq (h2.seq h3))
  have hblank : cfg ![[], [], [], []] = tapesCfg (encInput a) (fun _ => []) 0 0 out := by
    have he : (![[], [], [], []] : Fin 4 → List Bool) = fun _ => [] := by
      ext i; fin_cases i <;> rfl
    simp only [cfg, he, Fin.append_const]
  rw [hblank] at hr
  apply RunsBetween.of_runFrom
  convert hr.1 using 1
  dsimp only [c]
  congr 1
  ring

end Turing.MultiTapeTM.ScheduleEndpointInput
