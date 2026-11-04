/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Accounting
public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Controller
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.QuerySpan
public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness.Record
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Width
import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Original
import Complexity.Computability.WordRAM.RegisterFrame

/-!
# An actual record call after dirty workspace reuse

Protected producer words and registers retain their original meaning even after earlier
products have used the workspace. The caller reuses the actual full 400-register code and
derives its finite failure/success semantics from real output words. No producer rerun, clean
workspace, intermediate solver execution or scan-count certificate is assumed.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open FixedPrime (recordBank)
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Run the actual complete box backend on physical slot zero after native construction.
Only the immutable prefix is related to the standalone reference; current slot readback is
supplied by the actual one-slot writer, not by an all-record Output assertion. -/
theorem exec_record {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : FixedPrime.admissionWidth n (D m) g p A ≤ w + 2)
    (a : Data 64) (x : Data 416)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) a)
    (hmem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.output)))
    (hheap : a.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0) (D m) g p)
    (hi : x.regs (recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal)) = 0)
    (houtput : x.regs (producerBank Instances.output) = a.regs Instances.output)
    (hslotHeap : x.regs (producerBank Instances.heap) =
      a.regs Instances.output + (6 + 2 * (n * D m)))
    (hslotLe : x.regs (producerBank Instances.heap) ≤ a.regs Instances.heap)
    (hslot :
      let out := a.regs Instances.output
      let q := RecordProduct.recordQueries n (D m) p idx
      let Q := RecordProduct.recordQueryCount n (D m) p (fun k => values.getD k 0) idx
      (Block.mk out 6).Realizes x.mem
        ![idx.1.val, idx.2.2, q, Q, out + 6, out + 6 + n * D m] ∧
      (Block.mk (out + 6) (n * D m)).Realizes x.mem (fun j =>
        WriteMatrices.entry false (RecordProduct.matrixArgs n (D m) g p idx.1.val idx.2.2)
          (fun k => (values.getD (2 * (n * n) + k) 0 % (p : ℤ)).toNat) j.val) ∧
      (Block.mk (out + 6 + n * D m) (n * D m)).Realizes x.mem (fun j =>
        WriteMatrices.entry true (RecordProduct.matrixArgs n (D m) g p idx.1.val idx.2.2)
          (fun k => (values.getD (n * n + k) 0 % (p : ℤ)).toNat) j.val)) :
    let V := fun q => values.getD q 0
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let Q := RecordProduct.recordQueryCount n (D m) p V idx
    let qs := RecordProduct.decodedQueries hn a.mem (RecordProduct.recordQueries n (D m) p idx) Q
    ∃ y S, ExecWithin (w + 2) FixedPrime.record x y
        (RecordBoxProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
          (42 * pieceSize (D m) g + 28) * S + 52) ∧
      y.regs (recordBank RecordWitness.Reg.scans) = S ∧
      (y.regs (recordBank RecordWitness.Reg.found) = 0 ∨
        y.regs (recordBank RecordWitness.Reg.found) = 1) ∧
      S ≤ FixedPrime.recordFailures (m := m) (g := g) hn V a.mem idx +
        y.regs (recordBank RecordWitness.Reg.found) ∧
      S ≤ n * n + 1 ∧
      (y.regs (recordBank RecordWitness.Reg.found) = 1 ↔
        ∃ q ∈ chunkOf (fun u v : Fin n => V (pairIndex (u, v))) (D m) p idx.1 idx.2.1,
          ∃ c ∈ piece n (D m) g idx.2.2,
            V (pairIndex (q.1, q.2)) + V (n * n + pairIndex (q.2, c)) +
              V (2 * (n * n) + pairIndex (q.1, c)) = 0) ∧
      (y.regs (recordBank RecordWitness.Reg.found) = 1 →
        y.regs (recordBank RecordWitness.Reg.witnessA) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessB) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessC) < n ∧
        V (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessB)) +
          V (n * n + (y.regs (recordBank RecordWitness.Reg.witnessB) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) +
          V (2 * (n * n) + (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) = 0) ∧
      (∀ u, u < x.regs (producerBank Instances.heap) ∨
        x.regs (producerBank Instances.heap) + CallableProduct.windowSize n Q ≤ u →
          y.mem u = x.mem u) ∧
      (∀ j : Fin 64,
        y.regs (producerBank j) = x.regs (producerBank j)) ∧
      ∀ j : Fin 416, 400 ≤ j.val → y.regs j = x.regs j := by
  let V := fun q => values.getD q 0
  let AB := fun u v : ℕ => V (u * n + v)
  let BC := fun v c : ℕ => V (n * n + (v * n + c))
  let AC := fun u c : ℕ => V (2 * (n * n) + (u * n + c))
  let wAB := fun u v : Fin n => V (pairIndex (u, v))
  let wBC := fun v c : Fin n => V (n * n + pairIndex (v, c))
  let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hn : 0 < n := lt_of_lt_of_le (by omega) hDn
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
  let z := x.comap recordBank
  let heap := x.regs (producerBank Instances.heap)
  have hq := RecordProduct.query_end_le_output V hp0 (by omega) hDn idx hidx
  dsimp only at hq
  dsimp only [V] at hq
  rw [← hout.2.2.2.1] at hq
  have hinputEnd : 5 + 3 * (n * n) ≤ a.regs Instances.output := by
    rw [hout.2.2.2.1]
    omega
  obtain ⟨_, _, _, hfirst, _, hcoords, hprefix⟩ :=
    RecordWitness.record_view V _ a hout hD hDn hg hp0 idx hidx
  have mem_eq (u : ℕ) (hu : u < a.regs Instances.output) : z.mem u = a.mem u := hmem hu
  have header (u : ℕ) (hu : u < 5 + 3 * (n * n)) : z.mem u =
      (Data.init (PreparationInput.input n (D m) g p values) : Data 64).mem u :=
    (mem_eq u (lt_of_lt_of_le hu hinputEnd)).trans (hprefix u hu)
  have original (q : ℕ) (hq : q < 3 * (n * n)) : z.mem (5 + q) = Signed.encode (V q) :=
    (header (5 + q) (by omega)).trans (PreparationInput.input_word n (D m) g p values q)
  have hmatrix : ∀ u < n, ∀ v < n,
      z.mem (5 + (u * n + v)) = Signed.encode (AB u v) ∧
      z.mem (5 + n * n + (u * n + v)) = Signed.encode (BC u v) ∧
      z.mem (5 + n * n + n * n + (u * n + v)) = Signed.encode (AC u v) := by
    intro u hu v hv'
    have hrow := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hu)
    rw [Nat.succ_mul] at hrow
    refine ⟨original _ (by omega), ?_, ?_⟩
    · simpa only [Nat.add_assoc] using original (n * n + (u * n + v)) (by omega)
    · have he : 5 + n * n + n * n + (u * n + v) =
          5 + (2 * (n * n) + (u * n + v)) := by omega
      rw [he]
      exact original _ (by omega)
  have hmag : ∀ u < n, ∀ v < n,
      (AB u v).natAbs ≤ A ∧ (BC u v).natAbs ≤ A ∧ (AC u v).natAbs ≤ A := by
    intro u hu v hv'
    have hrow := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hu)
    rw [Nat.succ_mul] at hrow
    exact ⟨RecordWitness.original_magnitude values hlen hv (by omega),
      RecordWitness.original_magnitude values hlen hv (by omega),
      RecordWitness.original_magnitude values hlen hv (by omega)⟩
  let q := RecordProduct.recordQueries n (D m) p idx
  let Q := RecordProduct.recordQueryCount n (D m) p V idx
  let qs := RecordProduct.decodedQueries hn a.mem q Q
  have hQ : Q ≤ n ^ 2 := (FixedPrime.recordQueryCount_le n (D m) p V idx).trans_eq (pow_two n).symm
  have hlenQ : qs.length = Q := RecordProduct.decodedQueries_length hn a.mem q Q
  have hqs : RecordProduct.decodedQueries hn z.mem q Q = qs :=
    FixedPrime.decodedQueries_eq_of_eqOn hn z.mem a.mem hmem hq
  have hq' : q + 2 * Q ≤ a.regs Instances.output := hq
  change ∀ j < Q, a.mem (q + 2 * j) < n ∧ a.mem (q + 2 * j + 1) < n at hcoords
  have zheap : z.regs (RecordWitness.productBank 42) =
      x.regs (producerBank Instances.heap) := rfl
  have zout : z.regs (RecordWitness.productBank 39) = a.regs Instances.output := houtput
  have admitted := FixedPrime.record_admitted hW
  obtain ⟨r, S, he, rs, rf, hS, riff, answers, rwit, rframe, rregs⟩ :=
    BoxRecordWitness.exec_at_record (g := g) (p := p) (U := A) V AB BC AC z hD hN
      ((header 1 (by omega)).trans rfl) ((header 2 (by omega)).trans rfl)
      ((header 3 (by omega)).trans rfl) idx hi
      (by
        simp only [Nat.zero_mul, Nat.add_zero]
        rw [show z.regs (RecordWitness.productBank
          (RecordProduct.producerBank Instances.output)) = a.regs Instances.output from houtput]
        refine ⟨hinputEnd.trans (by rw [zheap, hslotHeap]; omega), ?_, hq.trans ?_,
          hfirst, (by
            simpa only [Block.Realizes, Block.read, z, Data.comap_mem, V] using hslot.1), ?_⟩
        · change a.regs Instances.output + 6 ≤ x.regs (producerBank Instances.heap)
          rw [hslotHeap]; omega
        · change a.regs Instances.output ≤ x.regs (producerBank Instances.heap)
          rw [hslotHeap]; omega
        · intro j hj
          exact ⟨(mem_eq _ (by have := hq'; omega)).trans_lt (hcoords j hj).1,
            (mem_eq _ (by have := hq'; omega)).trans_lt (hcoords j hj).2⟩)
      (by simp only [Nat.zero_mul, Nat.add_zero]; rw [zout, zheap, hslotHeap]; omega)
      (by dsimp only
          rw [zout]
          simpa only [Nat.zero_mul, Nat.add_zero, z, Data.comap_mem, V,
            Block.Realizes, Block.read] using hslot.2.1)
      (by dsimp only
          rw [zout]
          simpa only [Nat.zero_mul, Nat.add_zero, z, Data.comap_mem, V,
            Block.Realizes, Block.read] using hslot.2.2)
      hmatrix hmag (RecordWitness.signed_fits admitted)
      (BoxRecordWitness.physical_fits (hslotLe.trans hheap) hQ hN admitted)
  dsimp only [q, Q] at hqs
  rw [hqs] at he answers
  have hcoordinate (i : Fin qs.length) :
      z.mem (q + 2 * i.val) = (qs.get i).1.val ∧
      z.mem (q + 2 * i.val + 1) = (qs.get i).2.val := by
    have hj : i.val < Q := by simpa only [hlenQ] using i.isLt
    have hv := RecordProduct.decodedQueries_get_val hn a.mem q Q i
      (hcoords i.val hj).1 (hcoords i.val hj).2
    exact ⟨(mem_eq _ (by have := hq'; omega)).trans hv.1.symm,
      (mem_eq _ (by have := hq'; omega)).trans hv.2.symm⟩
  have hfail := RecordWitness.native_failed_count_le V AB BC AC wAB wBC wAC hD hg
    (by intro u v; rfl) (by intro u v; rfl) (by intro u v; rfl) idx qs
    (⟨0, hn⟩, ⟨0, hn⟩) (fun j => z.mem (q + 2 * j))
    (fun j => z.mem (q + 2 * j + 1)) hcoordinate r.mem
    (r.regs (RecordWitness.productBank RecordProduct.Reg.result)) answers
  rw [hlenQ] at hfail
  have hsuccess := RecordWitness.actual_success_iff V AB BC AC wAB wBC wAC hD hg hp
    (by intro u v; rfl) (by intro u v; rfl) (by intro u v; rfl)
    (by intro v c; rfl) (by intro u c; rfl) idx qs
    (FixedPrime.actual_queries_chunk hn V hout hD hDn hp0 idx hidx).2
    (fun j => z.mem (q + 2 * j)) (fun j => z.mem (q + 2 * j + 1))
    hcoordinate r.mem (r.regs (RecordWitness.productBank RecordProduct.Reg.result)) answers
  rw [hlenQ] at hsuccess
  let y := r.extend recordBank x
  have yr (j : Fin 400) : y.regs (recordBank j) = r.regs j :=
    (Fin.castLE_injective (by decide : 400 ≤ 416)).extend_apply _ _ j
  have hex : ExecWithin (w + 2) FixedPrime.record x y
      (RecordBoxProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
        (42 * pieceSize (D m) g + 28) * S + 52) := by
    apply (he.rename (Fin.castLE_injective (by decide : 400 ≤ 416))).mono
    have ht := Nat.mul_le_mul_right S (show
      42 * min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g) + 28 ≤
        42 * pieceSize (D m) g + 28 by omega)
    omega
  refine ⟨y, S, hex, (yr _).trans rs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [yr] using rf
  · have hh := hS.trans (Nat.add_le_add_right hfail _)
    simpa only [FixedPrime.recordFailures, qs, q, Q, RecordProduct.decodedQueries_length,
      yr, V, wAB, wBC, wAC] using hh
  · have hc : Nat.count (fun j =>
        r.mem (r.regs (RecordWitness.productBank RecordProduct.Reg.result) + j) ≠ 0 ∧
        ∀ c : Fin (min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g)),
          AB (z.mem (q + 2 * j)) (z.mem (q + 2 * j + 1)) +
            BC (z.mem (q + 2 * j + 1)) (idx.2.2 * pieceSize (D m) g + c.val) +
            AC (z.mem (q + 2 * j)) (idx.2.2 * pieceSize (D m) g + c.val) ≠ 0) Q ≤ Q :=
      Nat.count_le _
    have hflag : r.regs RecordWitness.Reg.found ≤ 1 := by rcases rf with h | h <;> omega
    have hQ' := FixedPrime.recordQueryCount_le n (D m) p V idx
    have hcS : S ≤ Q + r.regs RecordWitness.Reg.found :=
      hS.trans (Nat.add_le_add_right hc _)
    omega
  · simpa only [yr, wAB, wBC, wAC, weightSum] using riff.trans hsuccess
  · intro hf
    obtain ⟨ha, hb, hlo, hhi, hz, -⟩ := rwit ((yr _).symm.trans hf)
    have hlen := min_le_right (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g)
    exact ⟨by simpa only [yr] using ha, by simpa only [yr] using hb,
      by simp only [yr]; omega, by simpa only [yr] using hz⟩
  · intro u hu
    exact rframe u (by exact hu)
  · intro j
    exact (yr _).trans (rregs _ (by change j.val < 65; omega))
  · intro j hj
    exact hex.regs_eq (BoxRecordWitness.program.preserves_rename_of_offset
      (offset := 0) recordBank (fun j => (Nat.zero_add j.val).symm) j (Or.inr hj))

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
