/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Prepare
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Original
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Failures

/-!
# Initialized producer, actual product and original-weight witness recovery

The input contains only the original scalar headers and three signed arrays. The fixed native
program constructs its real catalogue, selects its first actual record, computes its product,
loads its real queries and verifies original weights. False-positive accounting is derived
from the producer's actual repetition-free chunk. This is one record, not an outer ET solver.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Actual initialized structured execution, with original-coordinate soundness and complete
coverage of the selected chunk/piece. Failed records incur no extra successful-scan charge. -/
theorem exec_input {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : admissionWidth n (D m) g p A ≤ w + 2) :
    let V := fun q => values.getD q 0
    let wAB := fun a b : Fin n => V (pairIndex (a, b))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun a c : Fin n => V (2 * (n * n) + pairIndex (a, c))
    InputFits (w + 2) (PreparationInput.input n (D m) g p values) ∧
    ∃ a : Data 64, ∃ idx : InstanceIndex p,
      ExecWithin (w + 2) Instances.program
        (.init (PreparationInput.input n (D m) g p values)) a
        (RecordProduct.preparationTime n (D m) g p values - 1) ∧
      Instances.Output n (D m) g p V
        (.init (PreparationInput.input n (D m) g p values)) a ∧
      idx ∈ instanceIndices wAB (D m) g p ∧
      RecordProduct.recordOrdinal n (D m) g p V idx = 0 ∧
      let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
        ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
      let Q := RecordProduct.recordQueryCount n (D m) p V idx
      let qs := RecordProduct.decodedQueries hn a.mem (RecordProduct.recordQueries n (D m) p idx) Q
      let length := min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g)
      ∃ y S, ExecWithin (w + 2) entryProgram
          (.init (PreparationInput.input n (D m) g p values)) y
          (RecordProduct.preparationTime n (D m) g p values +
            RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
            (42 * length + 28) * S + 52) ∧
        y.Bounded (w + 2) ∧ y.regs Reg.scans = S ∧
        (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
        S ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
        (y.regs Reg.found = 1 ↔
          ∃ q ∈ chunkOf wAB (D m) p idx.1 idx.2.1,
            ∃ c ∈ piece n (D m) g idx.2.2, weightSum wAB wBC wAC q.1 q.2 c = 0) ∧
        (y.regs Reg.found = 1 → ∃ u v c : Fin n,
          y.regs Reg.witnessA = u.val ∧ y.regs Reg.witnessB = v.val ∧
          y.regs Reg.witnessC = c.val ∧ (u, v) ∈ chunkOf wAB (D m) p idx.1 idx.2.1 ∧
          c ∈ piece n (D m) g idx.2.2 ∧ weightSum wAB wBC wAC u v c = 0) ∧
        (∀ u, u < a.regs Instances.heap ∨
          a.regs Instances.heap + CallableProduct.windowSize n Q ≤ u → y.mem u = a.mem u) ∧
        ∀ j : Fin 64, y.regs (productBank (RecordProduct.producerBank j)) = a.regs j := by
  let V := fun q => values.getD q 0
  let wAB := fun a b : Fin n => V (pairIndex (a, b))
  let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
  let wAC := fun a c : Fin n => V (2 * (n * n) + pairIndex (a, c))
  let AB := fun a b : ℕ => V (a * n + b)
  let BC := fun b c : ℕ => V (n * n + (b * n + c))
  let AC := fun a c : ℕ => V (2 * (n * n) + (a * n + c))
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hn : 0 < n := lt_of_lt_of_le (by omega) hDn
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.pos
  obtain ⟨hinput, a, idx, z, ha, hout, hidx, hord, hz, zmap, zi, zheap⟩ :=
    prepare_input values hlen hD hg hp0 hN hv hW
  let q := RecordProduct.recordQueries n (D m) p idx
  let Q := RecordProduct.recordQueryCount n (D m) p V idx
  let qs := RecordProduct.decodedQueries hn a.mem q Q
  have hlenQ : qs.length = Q := RecordProduct.decodedQueries_length hn a.mem q Q
  have zmem : z.mem = a.mem := congrArg (fun d : Data 64 => d.mem) zmap
  have hzout : Instances.Output n (D m) g p V
      (.init (PreparationInput.input n (D m) g p values))
      ((z.comap productBank).comap RecordProduct.producerBank) := by
    rw [zmap]
    exact hout
  have hQ : Q ≤ n ^ 2 := by
    unfold Q RecordProduct.recordQueryCount
    rw [pow_two]
    exact (min_le_right _ _).trans ((Nat.sub_le _ _).trans (Nat.count_le _))
  have hmem : ∀ u < n, ∀ v < n,
      z.mem (5 + (u * n + v)) = Signed.encode (AB u v) ∧
      z.mem (5 + n * n + (u * n + v)) = Signed.encode (BC u v) ∧
      z.mem (5 + n * n + n * n + (u * n + v)) = Signed.encode (AC u v) := by
    intro u hu v hv'
    have hn := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hu)
    rw [Nat.succ_mul] at hn
    refine ⟨original_word values a z hout zmap (by omega), ?_, ?_⟩
    · simpa only [Nat.add_assoc] using
        original_word (q := n * n + (u * n + v)) values a z hout zmap (by omega)
    · have he : 5 + n * n + n * n + (u * n + v) =
          5 + (2 * (n * n) + (u * n + v)) := by omega
      rw [he]
      exact original_word values a z hout zmap (by omega)
  have hmag : ∀ u < n, ∀ v < n,
      (AB u v).natAbs ≤ A ∧ (BC u v).natAbs ≤ A ∧ (AC u v).natAbs ≤ A := by
    intro u hu v hv'
    have hn := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hu)
    rw [Nat.succ_mul] at hn
    exact ⟨original_magnitude values hlen hv (by omega),
      original_magnitude values hlen hv (by omega), original_magnitude values hlen hv (by omega)⟩
  obtain ⟨y, S, he, ys, yf, hS, yiff, answers, yw, frame, regs⟩ := exec_of_output
    V AB BC AC (.init (PreparationInput.input n (D m) g p values)) z hzout hD hg
    (by omega : p ≠ 0) hN rfl rfl rfl idx hidx (by rw [zi, hord]) hmem hmag
    (signed_fits hW) (physical_fits zheap hQ hN hW)
  simp only [zmem] at he hS yiff answers yw frame
  rw [zmem] at answers
  change ∀ j : Fin qs.length,
    y.mem (y.regs (productBank RecordProduct.Reg.result) + j.val) = Signed.encode
      ((RecordProduct.leftMatrix m n g p V idx * RecordProduct.rightMatrix m n g p V idx)
        (qs.get j).1 (qs.get j).2) at answers
  change ExecWithin (w + 2) program z y (RecordProduct.timeBound (m := m) qs +
    5 * Nat.sqrt (D m) + 8 * Q +
    (42 * min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g) + 28) * S + 52) at he
  have hheap : z.regs (productBank 42) = a.regs Instances.heap :=
    congrArg (fun d : Data 64 => d.regs Instances.heap) zmap
  have hex : ExecWithin (w + 2) entryProgram
      (.init (PreparationInput.input n (D m) g p values)) y
      (RecordProduct.preparationTime n (D m) g p values +
        RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
        (42 * min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g) + 28) * S + 52) := by
    obtain ⟨t, ht, hpref⟩ := hz
    cases hpref with
    | seq hp hs => exact ((hp.within.seq (hs.within.seq he))).mono (by omega)
  obtain ⟨-, -, -, hfirst, -, hcoords, -⟩ := record_view V
    (.init (PreparationInput.input n (D m) g p values)) a hout hD hDn hg (by omega) idx hidx
  change ∀ i < Q, a.mem (q + 2 * i) < n ∧ a.mem (q + 2 * i + 1) < n at hcoords
  have card := QuerySpec.card_residueClass wAB (by omega : p ≠ 0)
    (fun q => (V q % (p : ℤ)).toNat) (by intro pair; rfl) idx.1
  obtain ⟨-, hnodup, hset⟩ := RecordProduct.decodedQueries_chunkOf V wAB hn (by omega)
    (by intro u v; rfl) (by omega) hDn hout idx.1 idx.2.1 ((mem_instanceIndices wAB idx).mp hidx).1
  rw [card] at hnodup hset
  change qs.Nodup at hnodup
  change qs.toFinset = chunkOf wAB (D m) p idx.1 idx.2.1 at hset
  let argA := fun j => a.mem (q + 2 * j)
  let argB := fun j => a.mem (q + 2 * j + 1)
  have hcoordinate (i : Fin qs.length) :
      argA i.val = (qs.get i).1.val ∧ argB i.val = (qs.get i).2.val := by
    have hi : i.val < Q := by simpa only [hlenQ] using i.isLt
    have hh := RecordProduct.decodedQueries_get_val hn a.mem q Q i
      (hcoords i.val hi).1 (hcoords i.val hi).2
    exact ⟨hh.1.symm, hh.2.symm⟩
  have hquery : ∀ pair ∈ qs, pair ∈ chunkOf wAB (D m) p idx.1 idx.2.1 := by
    intro pair hm
    rw [← hset, List.mem_toFinset]
    exact hm
  let default : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩)
  have hfail := native_failed_occurrences_le V AB BC AC wAB wBC wAC hD hg hp
    (by intro u v; rfl) (by intro u v; rfl) (by intro u v; rfl)
    (by intro u v; rfl) (by intro u v; rfl) idx hidx qs default hnodup hquery
    argA argB hcoordinate y.mem (y.regs (productBank RecordProduct.Reg.result)) answers
  have hsuccess := actual_success_iff V AB BC AC wAB wBC wAC hD hg hp
    (by intro u v; rfl) (by intro u v; rfl) (by intro u v; rfl)
    (by intro u v; rfl) (by intro u v; rfl) idx qs hset
    argA argB hcoordinate y.mem (y.regs (productBank RecordProduct.Reg.result)) answers
  rw [hlenQ] at hfail hsuccess
  refine ⟨hinput, a, idx, ha, hout, hidx, hord, y, S, hex,
    hex.bounded (Data.Bounded.init hinput), ys, yf, ?_, yiff.trans hsuccess, ?_, ?_, ?_⟩
  · exact hS.trans (Nat.add_le_add_right hfail _)
  · intro hy
    obtain ⟨ha, hb, hlo, hhi, hz, j, hj, hwa, hwb⟩ := yw hy
    have hc : y.regs Reg.witnessC < n := by
      have := min_le_right (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g)
      omega
    let u : Fin n := ⟨y.regs Reg.witnessA, ha⟩
    let v : Fin n := ⟨y.regs Reg.witnessB, hb⟩
    let c : Fin n := ⟨y.regs Reg.witnessC, hc⟩
    let i : Fin qs.length := ⟨j, by simpa only [hlenQ] using hj⟩
    have hpq : (u, v) = qs.get i := Prod.ext (Fin.ext (hwa.trans (hcoordinate i).1))
      (Fin.ext (hwb.trans (hcoordinate i).2))
    refine ⟨u, v, c, rfl, rfl, rfl, ?_, ?_, hz⟩
    · rw [hpq]
      exact hquery _ (List.get_mem _ _)
    · exact (mem_piece_iff_interval hD hg c).mpr ⟨hlo, hhi⟩
  · intro u hu
    exact frame u (by simpa only [hheap] using hu)
  · intro j
    rw [regs _ (by change j.val < 65; omega)]
    exact congrArg (fun d : Data 64 => d.regs j) zmap

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
