/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Accounting
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Controller
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Width
import Complexity.Computability.WordRAM.RegisterFrame

/-!
# An actual record call after dirty workspace reuse

Protected producer words and registers retain their original meaning even after earlier
products have used the workspace. The caller reuses the actual full 400-register code and
derives its finite failure/success semantics from real output words. No producer rerun, clean
workspace, intermediate solver execution or scan-count certificate is assumed.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

private theorem recordBank_injective : Function.Injective recordBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 416 => k.val) h)

/-- Execute the real product and verifier from protected producer readback. The explicit heap
bound is supplied by the actual one-time producer's prefix theorem in the initialized client.
All other record/counter fits follow from original input and the numerical admission. -/
theorem exec_record {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : admissionWidth n (D m) g p A ≤ w + 2)
    (a : Data 64) (x : Data 416)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) a)
    (hbank : ∀ j : Fin 64,
      x.regs (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j)
    (hmem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.heap)))
    (hheap : a.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0) (D m) g p)
    (hi : x.regs (recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal)) =
      RecordProduct.recordOrdinal n (D m) g p (fun q => values.getD q 0) idx) :
    let V := fun q => values.getD q 0
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let Q := RecordProduct.recordQueryCount n (D m) p V idx
    let qs := RecordProduct.decodedQueries hn a.mem (RecordProduct.recordQueries n (D m) p idx) Q
    ∃ y S, ExecWithin (w + 2) record x y
        (RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
          (42 * pieceSize (D m) g + 28) * S + 52) ∧
      y.regs (recordBank RecordWitness.Reg.scans) = S ∧
      (y.regs (recordBank RecordWitness.Reg.found) = 0 ∨
        y.regs (recordBank RecordWitness.Reg.found) = 1) ∧
      S ≤ recordFailures (m := m) (g := g) hn V a.mem idx +
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
      (∀ u, u < a.regs Instances.heap ∨
        a.regs Instances.heap + CallableProduct.windowSize n Q ≤ u → y.mem u = x.mem u) ∧
      (∀ j : Fin 64, y.regs
        (recordBank (RecordWitness.productBank (RecordProduct.producerBank j))) = a.regs j) ∧
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
  let z₀ := (z.comap RecordWitness.productBank).comap RecordProduct.producerBank
  have zr : z₀.regs = a.regs := funext hbank
  have zheap : z.regs (RecordWitness.productBank 42) = a.regs Instances.heap := hbank 42
  have hcurrent : Instances.Output n (D m) g p V z₀ z₀ :=
    hout.reframe V zr hmem
  obtain ⟨hend, -, hspan, -, -, hcoords, hprefix⟩ :=
    RecordWitness.record_view V _ a hout hD hDn hg hp0 idx hidx
  have mem_eq (u : ℕ) (hu : u < a.regs Instances.heap) : z.mem u = a.mem u := hmem hu
  have header (u : ℕ) (hu : u < 5 + 3 * (n * n)) : z₀.mem u =
      (Data.init (PreparationInput.input n (D m) g p values) : Data 64).mem u :=
    (mem_eq u (lt_of_lt_of_le hu hend)).trans (hprefix u hu)
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
  have hQ : Q ≤ n ^ 2 := (recordQueryCount_le n (D m) p V idx).trans_eq (pow_two n).symm
  have hlenQ : qs.length = Q := RecordProduct.decodedQueries_length hn a.mem q Q
  have hqs : RecordProduct.decodedQueries hn z.mem q Q = qs :=
    decodedQueries_eq_of_eqOn hn z.mem a.mem hmem hspan
  have admitted := record_admitted hW
  obtain ⟨r, S, he, rs, rf, hS, riff, answers, rwit, rframe, rregs⟩ :=
    RecordWitness.exec_of_output V AB BC AC z₀ z hcurrent hD hg hp0 hN
      ((header 1 (by omega)).trans rfl) ((header 2 (by omega)).trans rfl)
      ((header 3 (by omega)).trans rfl) idx hidx hi hmatrix hmag
      (RecordWitness.signed_fits admitted) (by
        rw [zheap]
        exact RecordWitness.physical_fits hheap hQ hN admitted)
  dsimp only [q, Q] at hqs
  rw [hqs] at he answers
  have hcoordinate (i : Fin qs.length) :
      z.mem (q + 2 * i.val) = (qs.get i).1.val ∧
      z.mem (q + 2 * i.val + 1) = (qs.get i).2.val := by
    have hj : i.val < Q := by simpa only [hlenQ] using i.isLt
    have hv := RecordProduct.decodedQueries_get_val hn a.mem q Q i
      (hcoords i.val hj).1 (hcoords i.val hj).2
    exact ⟨(mem_eq _ (by omega)).trans hv.1.symm,
      (mem_eq _ (by omega)).trans hv.2.symm⟩
  have hfail := RecordWitness.native_failed_count_le V AB BC AC wAB wBC wAC hD hg
    (by intro u v; rfl) (by intro u v; rfl) (by intro u v; rfl) idx qs
    (⟨0, hn⟩, ⟨0, hn⟩) (fun j => z.mem (q + 2 * j))
    (fun j => z.mem (q + 2 * j + 1)) hcoordinate r.mem
    (r.regs (RecordWitness.productBank RecordProduct.Reg.result)) answers
  rw [hlenQ] at hfail
  have hsuccess := RecordWitness.actual_success_iff V AB BC AC wAB wBC wAC hD hg hp
    (by intro u v; rfl) (by intro u v; rfl) (by intro u v; rfl)
    (by intro v c; rfl) (by intro u c; rfl) idx qs
    (actual_queries_chunk hn V hout hD hDn hp0 idx hidx).2
    (fun j => z.mem (q + 2 * j)) (fun j => z.mem (q + 2 * j + 1))
    hcoordinate r.mem (r.regs (RecordWitness.productBank RecordProduct.Reg.result)) answers
  rw [hlenQ] at hsuccess
  let y := r.extend recordBank x
  have yr (j : Fin 400) : y.regs (recordBank j) = r.regs j :=
    recordBank_injective.extend_apply _ _ j
  have hex : ExecWithin (w + 2) record x y
      (RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
        (42 * pieceSize (D m) g + 28) * S + 52) := by
    apply (he.rename recordBank_injective).mono
    have ht := Nat.mul_le_mul_right S (show
      42 * min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g) + 28 ≤
        42 * pieceSize (D m) g + 28 by omega)
    omega
  refine ⟨y, S, hex, (yr _).trans rs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [yr] using rf
  · have hh := hS.trans (Nat.add_le_add_right hfail _)
    simpa only [recordFailures, qs, q, Q, RecordProduct.decodedQueries_length,
      yr, V, wAB, wBC, wAC] using hh
  · have hc : Nat.count (fun j =>
        r.mem (r.regs (RecordWitness.productBank RecordProduct.Reg.result) + j) ≠ 0 ∧
        ∀ c : Fin (min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g)),
          AB (z.mem (q + 2 * j)) (z.mem (q + 2 * j + 1)) +
            BC (z.mem (q + 2 * j + 1)) (idx.2.2 * pieceSize (D m) g + c.val) +
            AC (z.mem (q + 2 * j)) (idx.2.2 * pieceSize (D m) g + c.val) ≠ 0) Q ≤ Q :=
      Nat.count_le _
    have hflag : r.regs RecordWitness.Reg.found ≤ 1 := by rcases rf with h | h <;> omega
    have hQ' := recordQueryCount_le n (D m) p V idx
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
    exact rframe u (by simpa only [zheap] using hu)
  · intro j
    exact (yr _).trans ((rregs _ (by change j.val < 65; omega)).trans (hbank j))
  · intro j hj
    apply hex.regs_eq
    apply Code.preserves_rename_of_forall_ne
    intro i hij
    have hv := congrArg (fun k : Fin 416 => k.val) hij
    change i.val = j.val at hv
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
