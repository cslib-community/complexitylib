/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Initialize
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Evaluate
public import Complexity.Computability.WordRAM.InputArray
import Mathlib.Data.List.GetD

/-!
# Actual initialized-input execution of native pruned queries

## Main definitions

* `PrunedQuery.timeBound`: the full charged prefix, including setup and duplicate reporting.

## Main results

* `PrunedQuery.exec_input`: the fixed program starts at `State.init`, computes the existing
  finite pruned values, preserves the input and outside memory, and leaves bounded native words.

The input contains ordinary depth/count headers, two canonical signed arrays and query codes.
All child lists and directories are computed. No layout, execution or timing certificate is an
input word or an admission hypothesis.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Full prefix charge: actual header/power/pointer work, root deduplication, every recursive
controller instruction, loop exit and reporting in the original supplied order. -/
def timeBound {L : ℕ} (qs : List (Fin (10 ^ L))) : ℕ :=
  4 * L + 29 * qs.length + traceWeight (requested qs) + 51

/-- Pruning gives a bound in terms of the actual contributing leaf set, retaining the setup
and duplicate-query costs. This includes one additional final halt instruction. -/
theorem timeBound_add_one_le {L : ℕ} (qs : List (Fin (10 ^ L))) :
    timeBound qs + 1 ≤
      8192 * (L + qs.length + 1 + (L + 1) * (leaves (requested qs)).card) := by
  have ht := traceWeight_le (requested qs)
  unfold timeBound
  nlinarith only [ht]

/-- Both scalar headers, both signed arrays, all query codes and the machine's unsigned length
header fit the same admitted target width. -/
theorem input_fits {w L A B : ℕ} (hw : 0 < w) (a b : Fin (10 ^ L) → ℤ)
    (qs : List (Fin (10 ^ L))) (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L qs.length)) : InputFits (w + 2) (input L a b qs) := by
  have henv := magnitudeBound_fits hw hmag
  have hp : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hsmall : L + qs.length + 10 ^ L + 16 ≤ addressBound L qs.length := by
    unfold addressBound
    nlinarith only [hp]
  refine ⟨?_, ?_⟩
  · rw [length_input]
    exact haddr.of_le (by unfold addressBound; nlinarith only [hp])
  · intro v hv
    simp only [input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (((rfl | rfl) | hv) | hv) | hv
    · exact haddr.of_le (by omega)
    · exact haddr.of_le (by omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact (encode_fits (fits_left henv (ha i))).mono (by omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact (encode_fits (fits_right henv (hb i))).mono (by omega)
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hv
      exact haddr.of_le (by have := q.isLt; omega)

/-- Execution of the complete native program on actual initialized memory. The final memory
witness is shared by execution, mathematical outputs, frame preservation and boundedness. -/
theorem exec_input {w L A B : ℕ} (hw : 0 < w) (a b : Fin (10 ^ L) → ℤ)
    (qs : List (Fin (10 ^ L))) (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L qs.length)) :
    InputFits (w + 2) (input L a b qs) ∧
    ∃ y, ExecWithin (w + 2) program (State.init (input L a b qs)).data y (timeBound qs) ∧
      y.Bounded (w + 2) ∧
      (∀ i : Fin qs.length, y.mem (outputBase L qs.length + i.val) = encode
        (Pruned.result L (fun v => a (Encoding.leafIndex v))
          (fun v => b (Encoding.leafIndex v)) (requested qs) (queryAt (qs.get i)))) ∧
      (∀ c, ¬(outputBase L qs.length ≤ c ∧ c < memoryEnd L qs.length) →
        y.mem c = (State.init (input L a b qs) : State registers).data.mem c) ∧
      y.regs output = outputBase L qs.length := by
  have hi := input_fits hw a b qs ha hb hmag haddr
  let x : Data registers := (State.init (input L a b qs)).data
  have hheaderL : x.mem 1 = L := by simp [x, State.init, Data.init, input]
  have hheaderQ : x.mem 2 = qs.length := by simp [x, State.init, Data.init, input]
  have hthree (n : ℕ) : 1 + (1 + (1 + n)) = 3 + n := by omega
  have hleft (i : Fin (10 ^ L)) : x.mem (3 + i.val) = encode (a i) := by
    have h := Data.init_realizes_append (r := registers) [L, qs.length]
      (List.ofFn (fun j => encode (a j))) (List.ofFn (fun j => encode (b j)) ++ qs.map Fin.val)
    have hr := h ⟨i.val, by simp⟩
    simpa [x, State.init, input, Block.read, List.append_assoc] using hr
  have hright (i : Fin (10 ^ L)) : x.mem (3 + 10 ^ L + i.val) = encode (b i) := by
    have h := Data.init_realizes_append (r := registers)
      ([L, qs.length] ++ List.ofFn (fun j => encode (a j)))
      (List.ofFn (fun j => encode (b j))) (qs.map Fin.val)
    have hr := h ⟨i.val, by simp⟩
    simpa [x, State.init, input, Block.read, List.append_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc, hthree] using hr
  have hqueries (i : Fin qs.length) :
      x.mem (3 + 2 * 10 ^ L + i.val) = (qs.get i).val := by
    have h := Data.init_realizes_append (r := registers)
      ([L, qs.length] ++ List.ofFn (fun j => encode (a j)) ++
        List.ofFn (fun j => encode (b j))) (qs.map Fin.val) []
    have hr := h ⟨i.val, by simp⟩
    simpa [x, State.init, input, Block.read, List.append_assoc, two_mul, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc, hthree] using hr
  have hzero (c : ℕ) (hc : (input L a b qs).length + 1 ≤ c) : x.mem c = 0 := by
    have hc0 : c ≠ 0 := by omega
    change (if c = 0 then (input L a b qs).length else (input L a b qs).getD (c - 1) 0) = 0
    rw [ite_eq_right hc0, List.getD_eq_default _ _ (by omega)]
  obtain ⟨u, humem, hregs, hQ, hqueriesReg, hout, hE, hinitialize⟩ :=
    exec_initialize x hheaderL hheaderQ haddr
  let queryList := fun i : Fin qs.length => queryAt (qs.get i)
  have hset : Finset.univ.image queryList = requested qs := by
    ext q
    simp only [Finset.mem_image, Finset.mem_univ, true_and, requested, List.mem_toFinset]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨qs.get i, List.get_mem _ i, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
      exact ⟨i, rfl⟩
  obtain ⟨y, hevaluate, hvalues, hframe, hreturn, _, _, _⟩ := exec_evaluate
    (Q := qs.length) (q0 := 3 + 2 * 10 ^ L) (o0 := outputBase L qs.length)
    (f := scratchBase L qs.length)
    (a := fun v => a (Encoding.leafIndex v)) (b := fun v => b (Encoding.leafIndex v))
    queryList u hregs hQ hqueriesReg hout hE
    (by intro i; rw [humem, queryIndex_queryAt]; exact hqueries i)
    (by intro v; rw [humem]; exact hleft _)
    (by intro v; rw [humem]; exact hright _)
    (by unfold scratchBase outputBase; omega) (by unfold scratchBase outputBase; omega)
    (by unfold outputBase; omega) (by unfold scratchBase; omega)
    (by
      intro q _
      rw [humem, hzero _ (by
        rw [length_input]
        unfold scratchBase outputBase
        omega)])
    (fun v => ha _) (fun v => hb _) hw hmag
    (haddr.of_le (evaluationBudget_input_le L qs.length))
  have he : ExecWithin (w + 2) program x y (timeBound qs) := by
    have h := hinitialize _ y _ hevaluate
    simp only [hset] at h
    exact h.mono (by unfold timeBound; omega)
  refine ⟨hi, y, he, he.bounded (Data.Bounded.init hi), ?_, ?_, hreturn⟩
  · intro i
    simpa only [hset, queryList] using hvalues i
  · intro c hc
    rw [hframe c (by
      unfold memoryEnd stampsBase valuesBase listsBase scratchBase at hc
      omega) (by
      simp only [memoryEnd, stampsBase, valuesBase, listsBase, scratchBase,
        two_mul, Nat.add_mul, Nat.add_assoc] at hc ⊢
      omega), humem]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
