/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateInterpolationCorrect

/-!
# Physical space bounds for native gate interpolation

Every assignment call is charged for its retained chunk metadata and actual local replay.
The full interpolation loop retains one caller and one callee, independent of the number of
assignments. The bound covers every physical clock, including the table subroutine's clocks.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Interpolation

open MultiTapeTM MultiTapeNTM.ChoiceTable Cslib.TreeEval.Ary
open Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type} [Finite Q]

/-- Space charged to one native table call, independent of its assignment counter. -/
@[expose] noncomputable def calleeSpace (k s : ℕ) (Q : Type) (context : Context) : ℕ :=
  let (N, b, σ, i, m, chunk, _) := context
  let (positive, negative) := ScheduleRead.origin k 0 (σ, i)
  2 * (SupplierChunk.encContext (m, chunk)).length + 1 + (Encoding.width k s b + 1) +
    (2 * (Gate.encContext (positive, negative, ScheduleRead.fullrow k (σ, i))).length + 2 +
      1024 * (k + 1) * (b + Nat.log2 N + Nat.card (Option Q) + Nat.card OutputTrack + 1))

/-- The completed native interpolation and its actual physical states share one bound. -/
theorem exists_runFrom_counterGate_bounded {p q r m : ℕ} (M : MultiTapeTM k Bool Q)
    (e : Q ≃ Fin s) (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p) (hp : 0 < p)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (chunk : Fin r) :
    let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
      (Encoding.encode e) (Encoding.decode e) (i.val + 1)
    let context : Context := (w.length, b, σ, i.val, m, chunk.val, r * m)
    let params := QueryGate.gateParams (s := 2 ^ m) context x
    ∃ T z, (machine M e).runFrom w (initial params) T =
        .inl (params, (2 ^ m) ^ ((k * 3 + 1) * r), z) ∧
      (z : ZMod p) = Packed.counterGateExtension (by positivity : 0 < 2 ^ m)
        (Packed.packBits hb) (Packed.unpackBits hb) f x chunk ∧
      (machine M e).halted ((machine M e).runFrom w (initial params) T) = true ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial params) t)).length ≤
        16 * ((QueryGate.encParams encContext params).length + 1) +
          calleeSpace k s Q context + 2 := by
  let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
    (Encoding.encode e) (Encoding.decode e) (i.val + 1)
  let context : Context := (w.length, b, σ, i.val, m, chunk.val, r * m)
  let params := QueryGate.gateParams (s := 2 ^ m) context x
  let table := QueryGate.gateTable (by positivity : 0 < 2 ^ m)
    (Packed.packBits hb) (Packed.unpackBits hb) f chunk
  have hsupplier : ∀ j < params.2.2.2, ∃ T,
      (∀ t < T, (SupplierChunk.machine M e).halted ((SupplierChunk.machine M e).runFrom w
        (start e (QueryGate.sumState params table j)) t) = false) ∧
      (SupplierChunk.machine M e).halted ((SupplierChunk.machine M e).runFrom w
        (start e (QueryGate.sumState params table j)) T) = true ∧
      SupplierChunk.answer M e ((SupplierChunk.machine M e).runFrom w
        (start e (QueryGate.sumState params table j)) T) = table j ∧
      (∀ t ≤ T, (SupplierChunk.encState ((SupplierChunk.machine M e).runFrom w
        (start e (QueryGate.sumState params table j)) t)).length ≤ calleeSpace k s Q context) := by
    intro j hj
    obtain ⟨T, hpre, hhalt, hans⟩ := table_supplier M e w b σ i x hb hm chunk j hj
    refine ⟨T, hpre, hhalt, hans, ?_⟩
    intro t _ht
    rw [start_sumState]
    exact SupplierChunk.length_runFrom_prepare_le M e w b σ i
      ((2 ^ m) ^ ((k * 3 + 1) * r)) j (r * m) m chunk t
  obtain ⟨T, hrun, hsize⟩ := QueryGate.exists_runFrom_sumState_encoding_le
    encContext (SupplierChunk.encState (k := k) (Q := Q)) params (SupplierChunk.machine M e)
    (start e) (SupplierChunk.answer M e) w table (calleeSpace k s Q context) hp hsupplier
    params.2.2.2 le_rfl
  have hfinal : QueryGate.sumState params table params.2.2.2 =
      (params, params.2.2.2,
        interpolateGrid p (2 ^ m) ((k * 3 + 1) * r) table params.2.2.1) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact QueryGate.sumState_counter params table params.2.2.2
      · rfl
  have hactual : (machine M e).runFrom w (initial params) T =
      .inl (params, params.2.2.2,
        interpolateGrid p (2 ^ m) ((k * 3 + 1) * r) table params.2.2.1) := by
    rw [machine_runFrom_eq_params M e params w (initial params) T]
    simpa only [initial, hfinal] using hrun
  refine ⟨T, _, hactual, rfl, ?_, ?_⟩
  · rw [hactual]
    change decide (params.2.2.2 ≤ params.2.2.2) = true
    simp
  · intro t ht
    rw [machine_runFrom_eq_params M e params w (initial params) t]
    exact hsize t ht

/-- The selected-field gate extension and its whole physical execution have the same bound. -/
theorem exists_runFrom_gateExtension_bounded {p q r m : ℕ} [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (chunk : Fin r)
    (hsp : 2 ^ m ≤ p) (h : Fin (2 ^ m) ↪ ZMod p)
    (hh : ∀ a, h a = (a.val : ZMod p)) :
    let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
      (Encoding.encode e) (Encoding.decode e) (i.val + 1)
    let context : Context := (w.length, b, σ, i.val, m, chunk.val, r * m)
    let params := QueryGate.gateParams (s := 2 ^ m) context x
    ∃ T z, (machine M e).runFrom w (initial params) T =
        .inl (params, (2 ^ m) ^ ((k * 3 + 1) * r), z) ∧
      (z : ZMod p) = Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb)
        f x chunk ∧
      (machine M e).halted ((machine M e).runFrom w (initial params) T) = true ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial params) t)).length ≤
        16 * ((QueryGate.encParams encContext params).length + 1) +
          calleeSpace k s Q context + 2 := by
  obtain ⟨T, z, hrun, hz, hhalt, hsize⟩ := exists_runFrom_counterGate_bounded M e w b σ i x
    (Fact.out : p.Prime).pos hb hm chunk
  refine ⟨T, z, hrun, ?_, hhalt, hsize⟩
  exact hz.trans (Packed.counterGateExtension_eq (by positivity) hsp h hh _ _ _ _ _)

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Interpolation
