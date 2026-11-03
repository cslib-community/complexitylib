/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateVector
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateInterpolationBounds
import Complexity.Foundations.Data.List.Lookup
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.FirstHalt

/-!
# Complete native gate vectors

One coordinate's interpolation is called at a time, its reduced answer is appended, and the
callee is discarded. Every prefix is realized by finitely many same-original-input calls. On
actual packed parameters the completed vector is the existing gate extension at every output
coordinate, with no external supplier premise.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.GateVector

open MultiTapeTM Cslib.TreeEval.Ary
open Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- Completed-coordinate prefixes, used only to specify the streamed execution. -/
@[expose] def prefixState (params : Params) (values : ℕ → ℕ) (j : ℕ) : CallerState :=
  let ((_, (p, _, _), _, _), _) := params
  (params, j, List.ofFn fun i : Fin j => values i % p)

/-- Returning the requested scalar extends exactly one coordinate prefix. -/
theorem resume_prefix (params : Params) (values : ℕ → ℕ) (j : ℕ)
    (returned : Interpolation.State k Q) (hanswer : answer returned = values j) :
    resume (prefixState params values j) returned = prefixState params values (j + 1) := by
  rcases params with ⟨params, count⟩
  rcases params with ⟨context, ⟨p, alphabet, coordinates⟩, point, limit⟩
  change (((context, (p, alphabet, coordinates), point, limit), count), j + 1,
      (List.ofFn fun i : Fin j => values i % p) ++ [answer returned % p]) = _
  rw [hanswer]
  simp only [prefixState, List.ofFn_succ_last, Fin.val_castSucc, Fin.val_last]

/-- A first-return interpolation call implements one vector coordinate. -/
theorem runFrom_one (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (params : Params)
    (values : ℕ → ℕ) (w : List Bool) (j T : ℕ) (hj : j < params.2)
    (hpre : ∀ t < T, (Interpolation.machine M e).halted
      ((Interpolation.machine M e).runFrom w (start (prefixState params values j)) t) = false)
    (hhalt : (Interpolation.machine M e).halted
      ((Interpolation.machine M e).runFrom w (start (prefixState params values j)) T) = true)
    (hanswer : answer ((Interpolation.machine M e).runFrom w
      (start (prefixState params values j)) T) = values j) :
    (machine M e).runFrom w (.inl (prefixState params values j)) (T + 2) =
      .inl (prefixState params values (j + 1)) := by
  rw [← resume_prefix params values j _ hanswer]
  apply QueryMachine.withCalls_runFrom_call
  · change decide (params.2 ≤ j) = false
    exact decide_eq_false (by omega)
  · change (if j < params.2 then some (start (prefixState params values j)) else none) = _
    simp only [hj, ↓reduceIte]
  · exact hpre
  · exact hhalt

/-- Every prefix of the output vector is reached through actual completed interpolation calls. -/
theorem exists_runFrom_prefix (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (params : Params)
    (w : List Bool) (values : ℕ → ℕ)
    (hsupplier : ∀ j < params.2, ∃ T,
      (∀ t < T, (Interpolation.machine M e).halted
        ((Interpolation.machine M e).runFrom w (start (prefixState params values j)) t) = false) ∧
      (Interpolation.machine M e).halted ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) T) = true ∧
      answer ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) T) = values j)
    (j : ℕ) (hj : j ≤ params.2) :
    ∃ T, (machine M e).runFrom w (initial params) T = .inl (prefixState params values j) := by
  induction j with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    obtain ⟨T, hT⟩ := ih (by omega)
    obtain ⟨U, hpre, hhalt, hans⟩ := hsupplier j (by omega)
    refine ⟨T + (U + 2), ?_⟩
    rw [QueryMachine.runFrom_add, hT]
    exact runFrom_one M e params values w j U (by omega) hpre hhalt hans

/-- Changing the requested coordinate preserves the actual field point and loop limit. -/
theorem setChunk_gateParams {p r m : ℕ} (N b σ i previous chunk stride : ℕ)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p) :
    setChunk (QueryGate.gateParams (s := 2 ^ m) (N, b, σ, i, m, previous, stride) x) chunk =
      QueryGate.gateParams (s := 2 ^ m) (N, b, σ, i, m, chunk, stride) x := rfl

/-- Every coordinate is returned at its first halt, with its actual physical state bound. -/
theorem coordinate_supplier_bounded {p q r m : ℕ} [Fact p.Prime] [Finite Q]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (chunk : Fin r)
    (hsp : 2 ^ m ≤ p) (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p)) :
    let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
      (Encoding.encode e) (Encoding.decode e) (i.val + 1)
    let context : Interpolation.Context := (w.length, b, σ, i.val, m, chunk.val, r * m)
    let params := QueryGate.gateParams (s := 2 ^ m) context x
    ∃ T z,
      (∀ t < T, (Interpolation.machine M e).halted
        ((Interpolation.machine M e).runFrom w (Interpolation.initial params) t) = false) ∧
      (Interpolation.machine M e).halted
        ((Interpolation.machine M e).runFrom w (Interpolation.initial params) T) = true ∧
      answer ((Interpolation.machine M e).runFrom w (Interpolation.initial params) T) = z ∧
      (z : ZMod p) = Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb)
        f x chunk ∧
      ∀ t ≤ T, (Interpolation.encState ((Interpolation.machine M e).runFrom w
        (Interpolation.initial params) t)).length ≤
        16 * ((QueryGate.encParams Interpolation.encContext params).length + 1) +
          Interpolation.calleeSpace k s Q context + 2 := by
  dsimp only
  obtain ⟨U, z, hrun, hz, hhalt, hsize⟩ :=
    Interpolation.exists_runFrom_gateExtension_bounded M e w b σ i x hb hm chunk hsp h hh
  obtain ⟨T, hle, hT, hpre, hstate⟩ := QueryMachine.exists_first_halt_le
    (Interpolation.machine M e) w _ U hhalt
  refine ⟨T, z, hpre, hT, ?_, hz, ?_⟩
  · rw [hstate, hrun]
    rfl
  · intro t ht
    exact hsize t (ht.trans hle)

/-- The complete selected-field vector is returned by one fixed native vector machine. -/
theorem exists_runFrom_gateExtension {p q r m : ℕ} [Fact p.Prime] [Finite Q]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m)
    (hsp : 2 ^ m ≤ p) (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p)) :
    let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
      (Encoding.encode e) (Encoding.decode e) (i.val + 1)
    let params : Params := (QueryGate.gateParams (s := 2 ^ m)
      (w.length, b, σ, i.val, m, 0, r * m) x, r)
    ∃ T values, (machine M e).runFrom w (initial params) T = .inl (params, r, values) ∧
      values.length = r ∧ (∀ value ∈ values, value < p) ∧
      (∀ j : Fin r, (values.getD j.val 0 : ZMod p) =
        Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb) f x j) ∧
      (machine M e).halted ((machine M e).runFrom w (initial params) T) = true := by
  classical
  let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
    (Encoding.encode e) (Encoding.decode e) (i.val + 1)
  let params : Params := (QueryGate.gateParams (s := 2 ^ m)
    (w.length, b, σ, i.val, m, 0, r * m) x, r)
  choose times scalars hpre hhalt hans hscalar hsize using fun j : Fin r =>
    coordinate_supplier_bounded M e w b σ i x hb hm j hsp h hh
  let values : ℕ → ℕ := fun j => if hj : j < r then scalars ⟨j, hj⟩ else 0
  have hsupplier : ∀ j < params.2, ∃ T,
      (∀ t < T, (Interpolation.machine M e).halted ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) t) = false) ∧
      (Interpolation.machine M e).halted ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) T) = true ∧
      answer ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) T) = values j := by
    intro j hj
    have hjr : j < r := hj
    refine ⟨times ⟨j, hjr⟩, ?_, ?_, ?_⟩
    · simpa only [start, prefixState, params, setChunk_gateParams] using hpre ⟨j, hjr⟩
    · simpa only [start, prefixState, params, setChunk_gateParams] using hhalt ⟨j, hjr⟩
    · simpa only [start, prefixState, params, setChunk_gateParams, values, hjr, ↓reduceDIte]
        using hans ⟨j, hjr⟩
  obtain ⟨T, hT⟩ := exists_runFrom_prefix M e params w values hsupplier r le_rfl
  refine ⟨T, _, hT, ?_, ?_, ?_, ?_⟩
  · exact List.length_ofFn
  · intro value hvalue
    change value ∈ List.ofFn (fun j : Fin r => values j % p) at hvalue
    simp only [List.mem_ofFn] at hvalue
    obtain ⟨j, rfl⟩ := hvalue
    exact Nat.mod_lt _ (Fact.out : p.Prime).pos
  · intro j
    rw [List.getD_ofFn_of_lt _ j.isLt 0, ZMod.natCast_mod]
    simpa only [values, j.isLt, ↓reduceDIte] using hscalar j
  · rw [hT]
    change decide (r ≤ r) = true
    simp

end Turing.MultiTapePTM.BlockComputation.QueryReplay.GateVector
