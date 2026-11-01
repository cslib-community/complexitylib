/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateVectorCorrect
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Foundations.Data.List.Lookup

/-!
# Physical space for complete native gate vectors

The vector caller retains its parameters once and appends one reduced field element per returned
coordinate. The bounds cover every physical clock, including interpolation and replay calls.
The number of coordinates multiplies only the encoded field-element width.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.GateVector

open MultiTapeTM Cslib.TreeEval.Ary
open Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type} [Finite Q]

/-- The modulus of the field elements retained by the vector caller. -/
@[expose] def modulus (params : Params) : ℕ :=
  let ((_, (p, _, _), _, _), _) := params
  p

/-- One retained parameter record and space for the reduced output vector. -/
@[expose] noncomputable def callerSpace (params : Params) : ℕ :=
  let ((_, (p, _, _), _, _), count) := params
  8 * ((encParams params).length + 1) + count * (2 * (encNat p).length + 1)

/-- Prefix storage charges each returned scalar at most the binary modulus width. -/
theorem prefixState_encoding_le (params : Params) (values : ℕ → ℕ) (j : ℕ)
    (hj : j ≤ params.2) (hp : 0 < modulus params) :
    (encCaller (prefixState params values j)).length ≤ callerSpace params := by
  rcases params with ⟨⟨context, ⟨p, alphabet, coordinates⟩, point, limit⟩, count⟩
  change 0 < p at hp
  have hc := length_encNat_mono hj
  have hl := length_encList_le encNat
    (List.ofFn fun i : Fin j => values i % p) (b := (encNat p).length)
    (by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact length_encNat_mono (Nat.mod_lt _ hp).le)
  simp only [List.length_ofFn] at hl
  have hmul := Nat.mul_le_mul_right (2 * (encNat p).length + 1) hj
  dsimp only at hc hmul
  simp only [prefixState, encCaller, encParams, length_encPair, callerSpace]
  omega

/-- Every clock of one call pays for one suspended vector prefix and one actual callee. -/
theorem runFrom_one_encoding_le (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (params : Params) (values : ℕ → ℕ) (w : List Bool) (j T B : ℕ)
    (hj : j < params.2) (hp : 0 < modulus params)
    (hpre : ∀ t < T, (Interpolation.machine M e).halted
      ((Interpolation.machine M e).runFrom w (start (prefixState params values j)) t) = false)
    (hhalt : (Interpolation.machine M e).halted
      ((Interpolation.machine M e).runFrom w (start (prefixState params values j)) T) = true)
    (hanswer : answer ((Interpolation.machine M e).runFrom w
      (start (prefixState params values j)) T) = values j)
    (hsize : ∀ t ≤ T, (Interpolation.encState ((Interpolation.machine M e).runFrom w
      (start (prefixState params values j)) t)).length ≤ B)
    (t : ℕ) (ht : t ≤ T + 2) :
    (encState ((machine M e).runFrom w (.inl (prefixState params values j)) t)).length ≤
      2 * callerSpace params + B + 2 := by
  have hcaller := prefixState_encoding_le params values j hj.le hp
  have hnext := prefixState_encoding_le params values (j + 1) (by omega) hp
  by_cases htzero : t = 0
  · subst t
    simp only [QueryMachine.runFrom_zero, encState, encSum_inl, List.length_cons]
    omega
  by_cases htfinal : t = T + 2
  · subst t
    rw [runFrom_one M e params values w j T hj hpre hhalt hanswer]
    simp only [encState, encSum_inl, List.length_cons]
    omega
  have htT : t - 1 ≤ T := by omega
  have hentry : (machine M e).runFrom w (.inl (prefixState params values j)) 1 =
      .inr (prefixState params values j, start (prefixState params values j)) := by
    apply QueryMachine.withCalls_step_call
    · change decide (params.2 ≤ j) = false
      exact decide_eq_false (by omega)
    · change (if j < params.2 then some (start (prefixState params values j)) else none) = _
      simp only [hj, ↓reduceIte]
  rw [show t = 1 + (t - 1) by omega, QueryMachine.runFrom_add, hentry]
  have hprefix := QueryMachine.withCalls_runFrom_subroutine_prefix
    caller (Interpolation.machine M e) request resume w
    (prefixState params values j) (start (prefixState params values j)) (t - 1)
    (fun u hu => hpre u (by omega))
  rw [show (machine M e).runFrom w
      (.inr (prefixState params values j, start (prefixState params values j))) (t - 1) =
      .inr (prefixState params values j,
        (Interpolation.machine M e).runFrom w (start (prefixState params values j)) (t - 1))
    from hprefix]
  have hcallee := hsize (t - 1) htT
  rw [show (encState (.inr (prefixState params values j,
      (Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) (t - 1)))).length =
      2 * (encCaller (prefixState params values j)).length +
        (Interpolation.encState ((Interpolation.machine M e).runFrom w
          (start (prefixState params values j)) (t - 1))).length + 2 from
    QueryMachine.withCalls_encoding_inr_length encCaller Interpolation.encState _ _]
  omega

/-- Concatenated coordinate calls obey one bound at all physical clocks. -/
theorem exists_runFrom_prefix_encoding_le (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (params : Params) (w : List Bool) (values : ℕ → ℕ) (B : ℕ)
    (hp : 0 < modulus params)
    (hsupplier : ∀ j < params.2, ∃ T,
      (∀ t < T, (Interpolation.machine M e).halted ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) t) = false) ∧
      (Interpolation.machine M e).halted ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) T) = true ∧
      answer ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) T) = values j ∧
      (∀ t ≤ T, (Interpolation.encState ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) t)).length ≤ B))
    (j : ℕ) (hj : j ≤ params.2) :
    ∃ T, (machine M e).runFrom w (initial params) T = .inl (prefixState params values j) ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial params) t)).length ≤
        2 * callerSpace params + B + 2 := by
  induction j with
  | zero =>
    refine ⟨0, rfl, ?_⟩
    intro t ht
    have : t = 0 := by omega
    subst t
    have hc := prefixState_encoding_le params values 0 (by omega) hp
    change (encCaller (prefixState params values 0)).length + 1 ≤ _
    omega
  | succ j ih =>
    obtain ⟨T, hT, hbound⟩ := ih (by omega)
    obtain ⟨U, hpre, hhalt, hans, hsize⟩ := hsupplier j (by omega)
    refine ⟨T + (U + 2), ?_, ?_⟩
    · rw [QueryMachine.runFrom_add, hT]
      exact runFrom_one M e params values w j U (by omega) hpre hhalt hans
    · intro t ht
      by_cases htT : t ≤ T
      · exact hbound t htT
      · rw [show t = T + (t - T) by omega, QueryMachine.runFrom_add, hT]
        exact runFrom_one_encoding_le M e params values w j U B (by omega) hp
          hpre hhalt hans hsize (t - T) (by omega)

/-- Only the binary chunk-index metadata grows when the requested coordinate increases. -/
theorem setChunk_encoding_mono (params : QueryGate.Params Interpolation.Context)
    {a b : ℕ} (hab : a ≤ b) :
    (QueryGate.encParams Interpolation.encContext (setChunk params a)).length ≤
      (QueryGate.encParams Interpolation.encContext (setChunk params b)).length := by
  rcases params with ⟨⟨N, block, σ, i, m, previous, stride⟩, parameters, point, limit⟩
  have h := length_encNat_mono hab
  simp only [setChunk, QueryGate.encParams, Interpolation.encContext, length_encPair]
  omega

omit [Finite Q] in
/-- The replay allowance is monotone in the binary chunk-index metadata. -/
theorem calleeSpace_chunk_mono (N block σ i m stride : ℕ) {a b : ℕ} (hab : a ≤ b) :
    Interpolation.calleeSpace k s Q (N, block, σ, i, m, a, stride) ≤
      Interpolation.calleeSpace k s Q (N, block, σ, i, m, b, stride) := by
  have h := length_encNat_mono hab
  simp only [Interpolation.calleeSpace, SupplierChunk.encContext, length_encPair]
  omega

/-- The complete selected-field vector is returned with a bound at every physical clock. -/
theorem exists_runFrom_gateExtension_bounded {p q r m : ℕ} [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (x : Fin (k * 3 + 1) → Fin r → ZMod p)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m)
    (hsp : 2 ^ m ≤ p) (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p)) :
    let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
      (Encoding.encode e) (Encoding.decode e) (i.val + 1)
    let params : Params := (QueryGate.gateParams (s := 2 ^ m)
      (w.length, b, σ, i.val, m, 0, r * m) x, r)
    let maxContext : Interpolation.Context := (w.length, b, σ, i.val, m, r, r * m)
    let maxParams := QueryGate.gateParams (s := 2 ^ m) maxContext x
    ∃ T values, (machine M e).runFrom w (initial params) T = .inl (params, r, values) ∧
      values.length = r ∧ (∀ value ∈ values, value < p) ∧
      (∀ j : Fin r, (values.getD j.val 0 : ZMod p) =
        Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb) f x j) ∧
      (machine M e).halted ((machine M e).runFrom w (initial params) T) = true ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial params) t)).length ≤
        2 * callerSpace params + 16 * ((QueryGate.encParams Interpolation.encContext
          maxParams).length + 1) + Interpolation.calleeSpace k s Q maxContext + 4 := by
  classical
  let f := codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
    (Encoding.encode e) (Encoding.decode e) (i.val + 1)
  let params : Params := (QueryGate.gateParams (s := 2 ^ m)
    (w.length, b, σ, i.val, m, 0, r * m) x, r)
  let maxContext : Interpolation.Context := (w.length, b, σ, i.val, m, r, r * m)
  let maxParams := QueryGate.gateParams (s := 2 ^ m) maxContext x
  let B := 16 * ((QueryGate.encParams Interpolation.encContext maxParams).length + 1) +
    Interpolation.calleeSpace k s Q maxContext + 2
  choose times scalars hpre hhalt hans hscalar hsize using fun j : Fin r =>
    coordinate_supplier_bounded M e w b σ i x hb hm j hsp h hh
  let values : ℕ → ℕ := fun j => if hj : j < r then scalars ⟨j, hj⟩ else 0
  have hsupplier : ∀ j < params.2, ∃ T,
      (∀ t < T, (Interpolation.machine M e).halted ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) t) = false) ∧
      (Interpolation.machine M e).halted ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) T) = true ∧
      answer ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) T) = values j ∧
      (∀ t ≤ T, (Interpolation.encState ((Interpolation.machine M e).runFrom w
        (start (prefixState params values j)) t)).length ≤ B) := by
    intro j hj
    have hjr : j < r := hj
    refine ⟨times ⟨j, hjr⟩, ?_, ?_, ?_, ?_⟩
    · simpa only [start, prefixState, params, setChunk_gateParams] using hpre ⟨j, hjr⟩
    · simpa only [start, prefixState, params, setChunk_gateParams] using hhalt ⟨j, hjr⟩
    · simpa only [start, prefixState, params, setChunk_gateParams, values, hjr, ↓reduceDIte]
        using hans ⟨j, hjr⟩
    · intro t ht
      have hpar := setChunk_encoding_mono
        (QueryGate.gateParams (s := 2 ^ m)
          (w.length, b, σ, i.val, m, 0, r * m) x) (Nat.le_of_lt hjr)
      simp only [setChunk_gateParams] at hpar
      have hcallee := calleeSpace_chunk_mono (k := k) (s := s) (Q := Q)
        w.length b σ i.val m (r * m) (Nat.le_of_lt hjr)
      have hlocal := hsize ⟨j, hjr⟩ t ht
      dsimp only at hlocal
      have hbound : (Interpolation.encState ((Interpolation.machine M e).runFrom w
          (Interpolation.initial (QueryGate.gateParams (s := 2 ^ m)
            (w.length, b, σ, i.val, m, j, r * m) x)) t)).length ≤ B := by
        dsimp only [B, maxParams, maxContext]
        omega
      simpa only [start, prefixState, params, setChunk_gateParams] using hbound
  obtain ⟨T, hT, hbound⟩ := exists_runFrom_prefix_encoding_le M e params w values B
    (Fact.out : p.Prime).pos hsupplier r le_rfl
  refine ⟨T, _, hT, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.length_ofFn
  · intro value hvalue
    change value ∈ List.ofFn (fun j : Fin r => values j % p) at hvalue
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hvalue
    exact Nat.mod_lt _ (Fact.out : p.Prime).pos
  · intro j
    rw [List.getD_ofFn_of_lt _ j.isLt 0, ZMod.natCast_mod]
    simpa only [values, j.isLt, ↓reduceDIte] using hscalar j
  · rw [hT]
    change decide (r ≤ r) = true
    simp
  · intro t ht
    have hbnd := hbound t ht
    dsimp only [B, params, maxParams, maxContext] at hbnd ⊢
    omega

end Turing.MultiTapePTM.BlockComputation.QueryReplay.GateVector
