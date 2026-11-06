/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeRetain

/-!
# Read-only native backward hit probing

One opposite-side bucket hit is recovered by the full backward quarter kernel
and probed against the retained full-state dictionary. The two returned words
are a presence tag and a retained witness; no opposite-side output array is
allocated. This is a component for [WangLvShenZhang2027], Theorem 7,
PDF p. 22, not the all-class iterator or the original-input decision endpoint.
Reversed full-width operands and an existing dictionary remain prerequisites.
The sparse WordRAM model does not supply the source's multitape bit-time bound.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

private theorem pointer_bound (D ptr b c M N : ℕ) :
    ptr + 2 ≤ D + ptr + b + c + 8 * M + N + 4 := by omega

private theorem constant_bound (D ptr b c M N : ℕ) :
    1 ≤ D + ptr + b + c + 8 * M + N + 4 := by omega

private theorem slot_bound (D ptr b c M N r : ℕ) (hr : r < M) :
    D + 3 * r + 4 ≤ D + ptr + b + c + 8 * M + N + 4 := by omega

/-- Recover one backward hit and probe its complete state without stores.
The hit witness remains in `firstOperators`; `operators` is restored by the
backward kernel. `operand` and `bits` return the retained encoded witnesses. -/
@[expose] def probeBody : Code .standard 32 :=
  .seq (ram[ address ← link + one; state ← *address; address ← address + one;
    firstOperators ← *address; link ← *link ])
    (.seq backwardEvaluate (.seq (ram[ one ← #1 ]) Dictionary.get))

/-- Exact full backward-state probe on one actual linked node. Every load,
packed reversal, full-width operation and dictionary address is charged.
Neither the answer nor an execution/resource conclusion is a premise. -/
theorem probeBody_exec {W m b ptr D s u v : ℕ} (as : List (BitVec m)) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (hv : x.regs operators = v) (hfv : Fits W v)
    (hl : x.regs link = ptr) (hD : x.regs Dictionary.table = D)
    (hone : x.regs one = 1)
    (hs : x.mem (ptr + 1) = s) (hu : x.mem (ptr + 2) = u)
    (hsLt : s < 2 ^ m)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hfit : Fits W (D + ptr + b + as.length + 8 * 2 ^ m + 2 ^ as.length + 4)) :
    let result := (backward ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat
    ∃ y, ExecWithin W probeBody x y (18 * as.length + 33) ∧
      y.mem = x.mem ∧ y.regs state = result ∧
      y.regs firstOperators = u ∧ y.regs operators = v ∧
      y.regs link = x.mem ptr ∧
      y.regs operand = x.mem (Dictionary.slot D result) ∧
      y.regs bits = x.mem (Dictionary.slot D result + 1) := by
  dsimp only
  have ha2 : Fits W (ptr + 2) :=
    hfit.of_le (pointer_bound D ptr b as.length (2 ^ m) (2 ^ as.length))
  have ha1 : Fits W (ptr + 1) := ha2.of_le (by omega)
  let loaded := x.set address (ptr + 1) |>.set state s |>.set address (ptr + 2)
    |>.set firstOperators u |>.set link (x.mem ptr)
  have heLoad : ExecWithin (B := .standard) W
      (ram[ address ← link + one; state ← *address; address ← address + one;
        firstOperators ← *address; link ← *link ]) x loaded 5 := by
    ram_eval [loaded, hl, hone, hs, hu, ha1, ha2, address, link, one, state,
      firstOperators, Fin.mk.injEq, Nat.add_assoc]
  obtain ⟨z, heEval, zs, zv, zm⟩ := backwardEvaluate_exec as (BitVec.ofNatLT s hsLt) loaded
    (v := v)
    (by simpa +decide [loaded, base, address, state, firstOperators, link] using hb)
    (by simpa +decide [loaded, count, address, state, firstOperators, link] using hc)
    (by simpa +decide [loaded, modulus, address, state, firstOperators, link] using hn)
    (by simp +decide [loaded, state, address, firstOperators, link])
    (by simpa +decide [loaded, operators, address, state, firstOperators, link] using hv) hfv
    hinput (hfit.of_le (by omega))
  have frame (r : Fin 32) (hr : backwardEvaluate.Preserves r) :
      z.regs r = loaded.regs r := heEval.regs_eq hr
  let result := (backward ((decode as.length v).zip as) (BitVec.ofNat m s)).toNat
  have zr : z.regs state = result := by
    simpa only [result, BitVec.ofNatLT_eq_ofNat] using zs
  have zD : z.regs Dictionary.table = D := by
    rw [frame Dictionary.table (by decide)]
    simpa +decide [loaded, Dictionary.table, address, state, firstOperators, link] using hD
  let ready := z.set one 1
  have heOne : ExecWithin (B := .standard) W (ram[ one ← #1 ]) z ready 1 :=
    ExecWithin.const (hfit.of_le
      (constant_bound D ptr b as.length (2 ^ m) (2 ^ as.length)))
  obtain ⟨y, heGet, ym, yt, yw⟩ := Dictionary.get_exec ready
    (by simpa +decide [ready, Dictionary.table, one] using zD)
    (by simpa +decide [ready, state, one] using zr) (by simp [ready])
    (hfit.of_le (slot_bound D ptr b as.length (2 ^ m) (2 ^ as.length) result
      (backward ((decode as.length v).zip as) (BitVec.ofNat m s)).isLt))
  refine ⟨y, (heLoad.seq (heEval.seq (heOne.seq heGet))).mono (by omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ready, Data.set_mem, zm, loaded, Data.set_mem] using ym
  · exact ((heGet.regs_eq (by decide)).trans (heOne.regs_eq (by decide))).trans zr
  · rw [heGet.regs_eq (by decide), heOne.regs_eq (by decide), frame firstOperators (by decide)]
    simp +decide [loaded, firstOperators, link]
  · exact ((heGet.regs_eq (by decide)).trans (heOne.regs_eq (by decide))).trans zv
  · rw [heGet.regs_eq (by decide), heOne.regs_eq (by decide), frame link (by decide)]
    simp [loaded]
  · simpa only [ready, Data.set_mem, zm, loaded, Data.set_mem] using yt
  · simpa only [ready, Data.set_mem, zm, loaded, Data.set_mem] using yw

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
