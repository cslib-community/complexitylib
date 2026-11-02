/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialChunk
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeEncode
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import Mathlib.Data.List.OfFn

/-!
# Paid native initial-source vectors

A runtime vector length is paid by the actual binary interpolation limit. The implementation
returns at most one coordinate per stored limit bit, so malformed capacity metadata shortens
its result rather than allocating the numeric magnitude of a binary length. Each coordinate
reads only the fixed initial-control prefix.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.InitialVector

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- Actual binary capacity, requested chunk width and requested vector length. -/
abbrev Args := ℕ × ℕ × ℕ

/-- All runtime registers are charged by their actual binary storage. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair encNat (encPair encNat encNat)

/-- Initial chunks indexed by an already paid source-word prefix. -/
@[expose] def values (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) : Args → List ℕ :=
  fun (limit, m, r) => ((Encoding.NativeEncode.word limit 0).take r).mapIdx
    fun j _ => InitialChunk.chunk M e (m, j)

/-- The returned vector cannot exceed either its requested length or actual capacity. -/
theorem length_values (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (limit m r : ℕ) :
    (values M e (limit, m, r)).length = min r limit.size := by
  simp only [values, List.length_mapIdx, List.length_take, Encoding.NativeEncode.word,
    List.length_ofFn]

/-- Stored slices agree with an indexed vector of their actual, possibly truncated length. -/
theorem values_eq_ofFn (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (limit m r : ℕ) :
    values M e (limit, m, r) =
      List.ofFn (fun j : Fin (min r limit.size) => InitialChunk.chunk M e (m, j)) := by
  apply List.ext_getElem
  · simp only [length_values, List.length_ofFn]
  · intro i hi hi'
    simp only [values, List.getElem_mapIdx, List.getElem_ofFn]

private theorem length_encNat_ofBits_le (word : List Bool) :
    (encNat (ofBits word)).length ≤ word.length := by
  rw [length_encNat_eq_size, ← Nat.size_eq_bits_len, bits_ofBits]
  exact (List.rdropWhile_prefix _ _).length_le

/-- Source coordinates have bounded encoded size independently of runtime chunk metadata. -/
theorem length_chunk_le (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (m j : ℕ) :
    (encNat (InitialChunk.chunk M e (m, j))).length ≤ (InitialChunk.headerWord M e).length := by
  have h := length_encNat_ofBits_le
    (((InitialChunk.headerWord M e).drop (j * m)).take m)
  change (encNat (InitialChunk.chunk M e (m, j))).length ≤ _ at h
  have hl : (((InitialChunk.headerWord M e).drop (j * m)).take m).length ≤
      (InitialChunk.headerWord M e).length := by
    simp only [List.length_take, List.length_drop]
    omega
  exact h.trans hl

private abbrev BuildState := ℕ × ℕ × List ℕ
private noncomputable def encBuildState : BuildState ↪ List Bool :=
  encPair encNat (encPair encNat (encList encNat))

private def buildStep (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) : BuildState → BuildState :=
  fun (m, j, out) => (m, j + 1, out ++ [InitialChunk.chunk M e (m, j)])

private theorem iterate_buildStep (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (m n : ℕ) :
    (buildStep M e)^[n] (m, 0, []) =
      (m, n, List.ofFn (fun j : Fin n => InitialChunk.chunk M e (m, j))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [buildStep]
    rw [List.ofFn_succ_last]
    rfl

private theorem buildStep_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (buildStep M e) encBuildState encBuildState
      (fun a => (encBuildState a).length) := by
  have hm := fst encNat (encPair encNat (encList encNat))
  have hr := snd encNat (encPair encNat (encList encNat))
  have hj := hr.fst'
  have hout := hr.snd'
  have hchunk := budget_comp_linear (InitialChunk.chunk_inSpace M e) (budget_prod hm hj)
  exact budget_prod hm (budget_prod (budget_natSucc hj) (budget_snoc hout hchunk))

/-- Initial vector construction is native and linear in actual binary capacity storage.
The constant may depend on the fixed machine/control prefix, never on runtime lengths. -/
theorem values_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (values M e) encArgs (encList encNat)
      (fun a => (encArgs a).length) := by
  let H := (InitialChunk.headerWord M e).length
  have hlimit := fst encNat (encPair encNat encNat)
  have hr := snd encNat (encPair encNat encNat)
  have hm := hr.fst'
  have hrequested := hr.snd'
  have hsize := budget_comp_linear natSize hlimit
  have hn := budget_ite (budget_natLt hrequested hsize) hrequested hsize
  have hinit := budget_prod hm (budget_prod
    (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encList encNat) [] (.refl _)))
  have hstates (a : Args) (i : ℕ) (hi : i ≤ min a.2.2 a.1.size) :
      (encBuildState ((buildStep M e)^[i] (a.2.1, 0, []))).length ≤
        8 * (H + 2) * ((encArgs a).length + 1) := by
    rw [iterate_buildStep]
    have hout := length_encList_le encNat
      (List.ofFn (fun j : Fin i => InitialChunk.chunk M e (a.2.1, j)))
      (b := H) (fun value hv => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
        exact length_chunk_le M e _ _)
    have hj := length_encNat_le_self i
    have hpaid : i ≤ (encNat a.1).length := by
      rw [length_encNat_eq_size]
      exact hi.trans (Nat.min_le_right _ _)
    simp only [encBuildState, encArgs, length_encPair, List.length_ofFn] at *
    nlinarith
  have hrun := ComputableInSpace.iterate
    (n := fun a : Args => min a.2.2 a.1.size)
    (init := fun a : Args => (a.2.1, 0, [])) (step := buildStep M e)
    (hn.of_enc_eq fun a => by
      by_cases h : a.2.2 < a.1.size
      · simp [h, Nat.min_eq_left h.le]
      · simp [h, Nat.min_eq_right (Nat.le_of_not_gt h)])
    hinit (buildStep_inSpace M e) hstates hstates
  refine hrun.snd'.snd'.weaken
    (.of_le_linear (100 * (H + 2)) (100 * (H + 2)) fun a => by
      have hpaid : min a.2.2 a.1.size ≤ (encNat a.1).length := by
        simpa only [length_encNat_eq_size] using Nat.min_le_right a.2.2 a.1.size
      have hc := (length_encNat_le_self (min a.2.2 a.1.size)).trans hpaid
      simp only [encArgs, length_encPair] at *
      nlinarith) |>.of_enc_eq ?_
  rintro ⟨limit, m, r⟩
  rw [iterate_buildStep, values_eq_ofFn]

end Turing.MultiTapePTM.BlockComputation.InitialVector
