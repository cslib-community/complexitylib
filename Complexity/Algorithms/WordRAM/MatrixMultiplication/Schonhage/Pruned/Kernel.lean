/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Evaluate
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Powers

/-!
# Callable native pruned-query kernel

## Main results

* `PrunedQuery.exec_kernel`: compute powers/layout, deduplicate supplied queries, execute the
  complete pruned traversal and report answers using ordinary caller pointers and a fresh epoch.

Input arrays contain canonical `Signed.encode` words. Query codes, pointers, depth and count are
raw unsigned words. The caller supplies only the source arrays/list and old timestamp bound;
all frames, child lists and decisions are computed by the fixed code. The returned directory
bound permits reuse across tiles without a free dense-directory initialization per call.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The actual pointer-argument kernel, with computed powers and workspace partition, preserves
all memory outside its output and explicit scratch intervals. No initialized frame/list or child
execution premise is used. The original input magnitude envelope derives every signed fit. -/
theorem exec_kernel {w L f a0 b0 q0 o0 Q E A B : ℕ}
    (a b : Leaf L → ℤ) (qs : Fin Q → OutStr L) (x : Data registers)
    (hL : x.regs inputDepth = L) (hA : x.regs arrayA = a0) (hB : x.regs arrayB = b0)
    (hQ : x.regs queryCount = Q) (hq0 : x.regs queries = q0)
    (ho0 : x.regs output = o0) (hf : x.regs scratch = f) (hE : x.regs epoch = E)
    (hinput : ∀ i, x.mem (q0 + i.val) = (queryIndex (qs i)).val)
    (hleft : ∀ v, x.mem (a0 + (Encoding.leafIndex v).val) = encode (a v))
    (hright : ∀ v, x.mem (b0 + (Encoding.leafIndex v).val) = encode (b v))
    (hbeforeA : a0 + 10 ^ L ≤ f) (hbeforeB : b0 + 10 ^ L ≤ f)
    (hqueryOut : q0 + Q ≤ o0) (houtFrame : o0 + Q ≤ f)
    (hmarks : ∀ q < 10 ^ L,
      x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ E)
    (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hw : 0 < w) (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (kernelBudget L f a0 b0 q0 o0 Q E)) :
    ∃ y, ExecWithin (w + 2) kernel x y
        (4 * L + 29 * Q + traceWeight (Finset.univ.image qs) + 41) ∧
      (∀ i, y.mem (o0 + i.val) = encode
        (Pruned.result L a b (Finset.univ.image qs) (qs i))) ∧
      (∀ c, ¬(o0 ≤ c ∧ c < o0 + Q) →
        ¬(f ≤ c ∧ c < f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + 10 ^ L) →
          y.mem c = x.mem c) ∧ y.regs output = o0 ∧
      E + 1 ≤ y.regs epoch ∧ y.regs epoch ≤ E + 1 + epochAllowance L ∧
      (∀ q < 10 ^ L,
        y.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ y.regs epoch) := by
  obtain ⟨p, hp, hpmem, hpL, hspan, _, hnil, hone, _, hten, hnine, hfour, _⟩ :=
    exec_powers (Q := Q) x hL (hfit.of_le (by unfold kernelBudget; omega))
  have hpFrame : p.regs scratch = f :=
    (hp.regs_eq (by decide : powers.Preserves scratch)).trans hf
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hLcap : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  obtain ⟨u, hu, humem, huf, hul, huv, hus, _⟩ := exec_locate p hone hfour
    (hfit.of_le (by
      rw [hpFrame, hpL, hspan]
      unfold kernelBudget evaluationBudget nodeBudget
      nlinarith only [hpow, hLcap]))
  have fixed (i : Fin registers) (hi : locate.Preserves i) (hi' : powers.Preserves i) :
      u.regs i = x.regs i := (hu.regs_eq hi).trans (hp.regs_eq hi')
  have hregs : KernelRegs L f a0 b0 u := by
    constructor
    · exact (hu.regs_eq (by decide : locate.Preserves inputDepth)).trans hpL
    · exact (hu.regs_eq (by decide : locate.Preserves span)).trans hspan
    · exact (fixed _ (by decide) (by decide)).trans hA
    · exact (fixed _ (by decide) (by decide)).trans hB
    · exact huf.trans hpFrame
    · simpa only [hpFrame, hpL] using hul
    · simpa only [hpFrame, hpL, hspan] using huv
    · simpa only [hpFrame, hpL, hspan] using hus
    · exact (hu.regs_eq (by decide : locate.Preserves nil)).trans hnil
    · exact (hu.regs_eq (by decide : locate.Preserves one)).trans hone
    · exact (hu.regs_eq (by decide : locate.Preserves ten)).trans hten
    · exact (hu.regs_eq (by decide : locate.Preserves nine)).trans hnine
    · exact (hu.regs_eq (by decide : locate.Preserves frameWidth)).trans hfour
  have hmem : u.mem = x.mem := humem.trans hpmem
  obtain ⟨y, hy, hvalues, hframe, hout, hel, heu, htable⟩ := exec_evaluate a b qs u hregs
    ((fixed _ (by decide) (by decide)).trans hQ)
    ((fixed _ (by decide) (by decide)).trans hq0)
    ((fixed _ (by decide) (by decide)).trans ho0)
    ((fixed _ (by decide) (by decide)).trans hE)
    (by simpa only [hmem] using hinput) (by simpa only [hmem] using hleft)
    (by simpa only [hmem] using hright) hbeforeA hbeforeB hqueryOut houtFrame
    (by simpa only [hmem] using hmarks) ha hb hw hmag
    (hfit.of_le (by unfold kernelBudget; omega))
  refine ⟨y, ?_, hvalues, ?_, hout, hel, heu, htable⟩
  · exact (hp.seq (hu.seq hy)).mono (by omega)
  · simpa only [hmem] using hframe

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
