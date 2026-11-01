/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateInterpolation
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierChunkTable

/-!
# Same-input interpolation of the implicit block gate

The actual numeric table supplier discharges every assignment call of the existing packed
interpolation loop. The fixed machine starts from runtime parameters, and its final accumulator
is the existing counter gate extension. Neither the gate table nor a runtime-dependent machine
is supplied by an oracle.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Interpolation

open MultiTapeTM Cslib.TreeEval.Ary
open Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- A real caller prefix initializes its table request from its stored assignment counter. -/
theorem start_sumState {p r m : ℕ} (e : Q ≃ Fin s) (N b σ i chunk stride : ℕ)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p) (table : ℕ → ℕ) (j : ℕ) :
    start (k := k) e (QueryGate.sumState
      (QueryGate.gateParams (s := 2 ^ m) (N, b, σ, i, m, chunk, stride) x) table j) =
      SupplierChunk.prepare e ((m, chunk),
        (N, b, σ, i, (2 ^ m) ^ ((k * 3 + 1) * r), j, stride)) := by
  change SupplierChunk.prepare e ((m, chunk),
    (N, b, σ, i, (2 ^ m) ^ ((k * 3 + 1) * r),
      (QueryGate.sumState
        (QueryGate.gateParams (s := 2 ^ m) (N, b, σ, i, m, chunk, stride) x) table j).2.1,
      stride)) = _
  rw [QueryGate.sumState_counter]

/-- Every actual interpolation assignment is answered by the original-input native supplier.
The contract includes the first-return clock required by the same-input call rule. -/
theorem table_supplier {p q r m : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (chunk : Fin r) :
    let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
      (Encoding.encode e) (Encoding.decode e) (i.val + 1)
    let table := QueryGate.gateTable (by positivity : 0 < 2 ^ m)
      (Packed.packBits hb) (Packed.unpackBits hb) f chunk
    let params := QueryGate.gateParams (s := 2 ^ m)
      (w.length, b, σ, i.val, m, chunk.val, r * m) x
    ∀ j < (2 ^ m) ^ ((k * 3 + 1) * r), ∃ T,
      (∀ t < T, (SupplierChunk.machine M e).halted ((SupplierChunk.machine M e).runFrom w
        (start e (QueryGate.sumState params table j)) t) = false) ∧
      (SupplierChunk.machine M e).halted ((SupplierChunk.machine M e).runFrom w
        (start e (QueryGate.sumState params table j)) T) = true ∧
      SupplierChunk.answer M e ((SupplierChunk.machine M e).runFrom w
        (start e (QueryGate.sumState params table j)) T) = table j := by
  dsimp only
  intro j _hj
  obtain ⟨T, _hle, hhalt, hpre, hstate⟩ := SupplierChunk.exists_first_return M e w
    w.length b σ i ((2 ^ m) ^ ((k * 3 + 1) * r)) j (r * m) m chunk
  refine ⟨T, ?_, ?_, ?_⟩
  · simpa only [start_sumState] using hpre
  · simpa only [start_sumState] using hhalt
  · rw [start_sumState, hstate]
    exact SupplierChunk.answer_grid_eq_codeGate M e w b σ i j hb hm chunk

/-- One fixed native machine completes the actual packed counter extension for an interval
and requested output chunk, with no external table-supplier premise. -/
theorem exists_runFrom_counterGate {p q r m : ℕ} (M : MultiTapeTM k Bool Q)
    (e : Q ≃ Fin s) (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (chunk : Fin r) :
    let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
      (Encoding.encode e) (Encoding.decode e) (i.val + 1)
    let params := QueryGate.gateParams (s := 2 ^ m)
      (w.length, b, σ, i.val, m, chunk.val, r * m) x
    ∃ T z, (machine M e).runFrom w (initial params) T =
        .inl (params, (2 ^ m) ^ ((k * 3 + 1) * r), z) ∧
      (z : ZMod p) = Packed.counterGateExtension (by positivity : 0 < 2 ^ m)
        (Packed.packBits hb) (Packed.unpackBits hb) f x chunk ∧
      (machine M e).halted ((machine M e).runFrom w (initial params) T) = true := by
  let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
    (Encoding.encode e) (Encoding.decode e) (i.val + 1)
  let params := QueryGate.gateParams (s := 2 ^ m)
    (w.length, b, σ, i.val, m, chunk.val, r * m) x
  obtain ⟨T, z, hrun, hz⟩ := QueryGate.exists_runFrom_counterGateExtension
    (by positivity : 0 < 2 ^ m)
    (w.length, b, σ, i.val, m, chunk.val, r * m)
    (Packed.packBits hb) (Packed.unpackBits hb) f x chunk
    (SupplierChunk.machine M e) (start e) (SupplierChunk.answer M e) w
    (table_supplier M e w b σ i x hb hm chunk)
  have hactual : (machine M e).runFrom w (initial params) T =
      .inl (params, (2 ^ m) ^ ((k * 3 + 1) * r), z) := by
    rw [machine_runFrom_eq_params M e params w (initial params) T]
    exact hrun
  refine ⟨T, z, hactual, hz, ?_⟩
  rw [hactual]
  change decide ((2 ^ m) ^ ((k * 3 + 1) * r) ≤
    (2 ^ m) ^ ((k * 3 + 1) * r)) = true
  simp

/-- In a selected prime field containing the unsigned chunk alphabet, actual interpolation
returns the existing packed low-degree gate extension. -/
theorem exists_runFrom_gateExtension {p q r m : ℕ} [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (chunk : Fin r)
    (hsp : 2 ^ m ≤ p) (h : Fin (2 ^ m) ↪ ZMod p)
    (hh : ∀ a, h a = (a.val : ZMod p)) :
    let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
      (Encoding.encode e) (Encoding.decode e) (i.val + 1)
    let params := QueryGate.gateParams (s := 2 ^ m)
      (w.length, b, σ, i.val, m, chunk.val, r * m) x
    ∃ T z, (machine M e).runFrom w (initial params) T =
        .inl (params, (2 ^ m) ^ ((k * 3 + 1) * r), z) ∧
      (z : ZMod p) = Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb)
        f x chunk ∧
      (machine M e).halted ((machine M e).runFrom w (initial params) T) = true := by
  obtain ⟨T, z, hrun, hz, hhalt⟩ := exists_runFrom_counterGate M e w b σ i x hb hm chunk
  refine ⟨T, z, hrun, ?_, hhalt⟩
  exact hz.trans (Packed.counterGateExtension_eq (by positivity) hsp h hh _ _ _ _ _)

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Interpolation
