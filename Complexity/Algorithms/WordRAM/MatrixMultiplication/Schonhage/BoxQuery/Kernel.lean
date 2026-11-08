/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Loop
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Initialize

/-!
# Reusable native sparse box-query kernel

The actual setup writes a root record above the retained table, then the actual loop
enumerates all permitted prefixes and consumes real source or table words. The caller
provides original scalar contents and pure memory readback established by the real table
constructor; no execution, timing, enumeration or intermediate-fitting oracle is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Complete reusable query charge, including scalar/root setup and actual loop exit. -/
@[expose] def queryTime {L : ℕ} (m t : ℕ) (η : OutStr L) : ℕ :=
  258 * (L + 1) * (queryLeaves m t η).card + 28

/-- Complete actual native query from original arguments and real constructed-table readback. -/
theorem exec_queryProgram {w L m t AA BB D V K A B : ℕ} (x : Data registers)
    (η : OutStr L) (hη : (innerSetO η).card = m) (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hL : x.regs BoxTable.Reg.levels = L) (ht : x.regs BoxTable.Reg.threshold = t)
    (hT : x.regs BoxTable.Reg.span = 10 ^ L)
    (hQ : x.regs Reg.query = (PrunedQuery.queryIndex η).val)
    (hA : x.regs BoxTable.Reg.arrayA = AA) (hB : x.regs BoxTable.Reg.arrayB = BB)
    (hD : x.regs BoxTable.Reg.directory = D) (hV : x.regs BoxTable.Reg.values = V)
    (hcount : x.regs BoxTable.Reg.count = K) (hK : K = (boxes L m t).card)
    (hAA : AA + 10 ^ L ≤ V + K) (hBB : BB + 10 ^ L ≤ V + K)
    (hDir : D + (m - t + 1) * 10 ^ L ≤ V + K)
    (hread : Readback m t D V AA BB a b x.mem)
    (hfit : Fits (w + 2) (queryAddressBound L t AA BB D V K))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    ∃ y, ExecWithin (w + 2) queryProgram x y (queryTime m t η) ∧
      Parameters L t (PrunedQuery.queryIndex η).val AA BB D V K (V + K) y ∧
      y.regs Reg.top = 0 ∧ y.regs Reg.answer = Signed.encode (queryValue m t η a b) ∧
      Readback m t D V AA BB a b y.mem ∧
      (∀ q, ¬(V + K ≤ q ∧ q < V + K + 5 * stackCapacity L) → y.mem q = x.mem q) := by
  obtain ⟨u, hu, up, utop, uanswer, ustack, umem⟩ :=
    exec_setup (L := L) (t := t) (Q := (PrunedQuery.queryIndex η).val)
      (AA := AA) (BB := BB) (D := D) (V := V) (K := K)
      x η hL ht hT hQ hA hB hD hV hcount
      (hfit.of_le (by unfold queryAddressBound; omega))
  have uframe (q : ℕ) (hq : ¬(V + K ≤ q ∧ q < V + K + 5 * stackCapacity L)) :
      u.mem q = x.mem q := by
    rw [umem]
    exact writeTask_frame _ _ _ _ _ _ _ _ q (by unfold stackCapacity at hq; omega)
  have uread : Readback m t D V AA BB a b u.mem :=
    hread.transport hAA hBB hDir (by rw [← hK])
      (fun q hq => uframe q (by omega))
  have uready : Ready η m t AA BB D V K (V + K) a b [] [[]] u := by
    exact ⟨up, FrontierInvariant.initial η t _, utop, ustack, uanswer, uread⟩
  obtain ⟨y, hy, yp, ytop, yanswer, yread, yframe⟩ :=
    exec_loop u η hη a b ha hb uready hK rfl hAA hBB hDir hfit hmag
  refine ⟨y, (hu.seq hy).mono (by unfold queryTime; omega),
    yp, ytop, yanswer, yread, ?_⟩
  exact fun q hq => (yframe q hq).trans (uframe q hq)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
