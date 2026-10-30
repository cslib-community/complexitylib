/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Header
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Queries

/-!
# Complete per-record candidate consumption

The real header reads the record and computes its piece interval. The real query loop then
loads product answers and original pairs, verifies the original signed weights and returns a
genuine original-coordinate witness when one exists among the selected pairs. All memory and
the complete earlier producer/product register bank are preserved.

The numerical component premises are discharged from original caller data by the initialized
composition. In particular the record and answer words here are read from actual memory, not
supplied witness or execution certificates.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

-- This checks the finite write sets of the fixed consumer, including the renamed scan bank.
set_option maxRecDepth 4096 in
private theorem consume_preserves : ∀ j : Fin 400, j.val < 320 → consume.Preserves j := by
  decide

/-- Execute the actual descriptor decoder and short-circuit verifier loop. The additional
scan term uses the native counter, bounded by failed accepted pairs plus one success. -/
theorem exec_consume {w U n D g i records heap out : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (a b : ℕ → ℕ) (x : Data 400) (v : Fin 6 → ℕ)
    (hD : x.mem 1 = D) (hg : x.mem 2 = g) (hn : x.mem 3 = n)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) = i)
    (hrecords : x.regs (productBank (RecordProduct.producerBank Instances.output)) = records)
    (hout : x.regs (productBank RecordProduct.Reg.result) = out)
    (hrec : records + i * (6 + 2 * (n * D)) + 6 ≤ heap)
    (hv : ∀ j : Fin 6, x.mem (records + i * (6 + 2 * (n * D)) + j.val) = v j)
    (hfirst : v 1 * pieceSize D g ≤ n)
    (hquery : ∀ j < v 3, x.mem (v 2 + 2 * j) = a j ∧
      x.mem (v 2 + 2 * j + 1) = b j ∧ a j < n ∧ b j < n)
    (hmem : ∀ u < n, ∀ z < n,
      x.mem (5 + (u * n + z)) = Signed.encode (AB u z) ∧
      x.mem (5 + n * n + (u * n + z)) = Signed.encode (BC u z) ∧
      x.mem (5 + n * n + n * n + (u * n + z)) = Signed.encode (AC u z))
    (hmag : ∀ u < n, ∀ z < n,
      (AB u z).natAbs ≤ U ∧ (BC u z).natAbs ≤ U ∧ (AC u z).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2) (heap + out + v 2 + 4 * v 3 + 4 * D +
      2 * (n * D) + 9 * (n * n) + 4 * n + g + 2048)) :
    let first := v 1 * pieceSize D g
    let length := min (pieceSize D g) (n - first)
    ∃ y S, ExecWithin (w + 2) consume x y
        (5 * Nat.sqrt D + 8 * v 3 + (42 * length + 28) * S + 52) ∧
      y.mem = x.mem ∧ y.regs Reg.scans = S ∧
      S ≤ Nat.count (fun j => x.mem (out + j) ≠ 0 ∧
        ∀ c : Fin length, AB (a j) (b j) + BC (b j) (first + c.val) +
          AC (a j) (first + c.val) ≠ 0) (v 3) + y.regs Reg.found ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      (y.regs Reg.found = 1 ↔ ∃ j < v 3, x.mem (out + j) ≠ 0 ∧
        ∃ c, first ≤ c ∧ c < first + length ∧ AB (a j) (b j) + BC (b j) c + AC (a j) c = 0) ∧
      (y.regs Reg.found = 1 → ∃ j < v 3,
        x.mem (out + j) ≠ 0 ∧ y.regs Reg.witnessA = a j ∧ y.regs Reg.witnessB = b j ∧
        first ≤ y.regs Reg.witnessC ∧ y.regs Reg.witnessC < first + length ∧
        AB (a j) (b j) + BC (b j) (y.regs Reg.witnessC) +
          AC (a j) (y.regs Reg.witnessC) = 0) ∧
      ∀ j : Fin 400, j.val < 320 → y.regs j = x.regs j := by
  let first := v 1 * pieceSize D g
  let length := min (pieceSize D g) (n - first)
  have hlength : first + length ≤ n := by
    dsimp only [length, first]
    have := min_le_right (pieceSize D g) (n - v 1 * pieceSize D g)
    omega
  obtain ⟨s, hs, sFixed, sm, sf, -, -, -, ss, si, -⟩ := exec_header x v hD hg hn hi
    hrecords hout hrec hv hfirst (hfit.of_le (by omega))
  obtain ⟨y, S, he, -, ym, -, ys, hS, yf, iffFound, yw⟩ := exec_queries
    AB BC AC a b s sFixed si ss sf (by simpa only [sm] using hquery)
    hlength (by simpa only [sm] using hmem) hmag hU
    (hfit.of_le (by omega))
  change ExecWithin (w + 2) (.loop (.lt Reg.index Reg.count) step) s y
    (8 * v 3 + (42 * length + 28) * S + 2) at he
  have hexe : ExecWithin (w + 2) consume x y
      (5 * Nat.sqrt D + 8 * v 3 + (42 * length + 28) * S + 52) :=
    (hs.seq he).mono (by omega)
  refine ⟨y, S, hexe, ym.trans sm, ys, ?_, yf, ?_, ?_, ?_⟩
  · simpa only [sm] using hS
  · simpa only [sm] using iffFound
  · simpa only [sm] using yw
  · intro j hj
    exact hexe.regs_eq (consume_preserves j hj)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
