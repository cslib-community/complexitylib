/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeBackwardRetain
import all Complexity.Cryptanalysis.AddXNORNativeBackwardRetain

/-!
# Forward queries into constructed inverse buckets

The direction-exchanged query of [WangLvShenZhang2027], Lemma 8,
PDF p. 22: evaluate forward from a class value, then load the inverse-quarter
bucket head. The native evaluator reads operands, not precomputed query keys.
This read-only component preserves a retained dictionary and all bucket records.
It does not compose the whole retention/preparation/probe pipeline or establish
Theorem 7's termination, orientation or resource bounds.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter.Backward

open Cslib.WordRAM

/-- Forward query used when exchanging the directions in the class enumerator. -/
@[expose] def queryBucket : Code .standard 32 :=
  .seq evaluate (ram[ address ← heads + state; link ← *address ])

/-- An actual forward evaluation selects the bucket. Every memory cell is framed,
including arbitrary retained dictionary contents; the packed index is preserved. -/
theorem queryBucket_exec {W p b h v : ℕ} (as : List (BitVec p)) (g : BitVec p)
    (x : Data 32) (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ p) (hg : x.regs state = g.toNat)
    (hv : x.regs operators = v) (hfv : Fits W v) (hh : x.regs heads = h)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hfit : Fits W (h + b + as.length + 2 * 2 ^ p + 4)) :
    ∃ y, ExecWithin W queryBucket x y (11 * as.length + 9) ∧
      y.regs link = x.mem (h + (eval ((decode as.length v).zip as) g).toNat) ∧
      y.regs operators = v ∧ y.mem = x.mem ∧
      (∀ r, queryBucket.Preserves r → y.regs r = x.regs r) := by
  obtain ⟨z, he, zs, _, _, zm, _, _⟩ := evaluate_exec as g x hb hc hn hg hv hfv hinput
    (hfit.of_le (by omega))
  have zh : z.regs heads = h := (he.regs_eq (by decide)).trans hh
  let key := (eval ((decode as.length v).zip as) g).toNat
  have ha : Fits W (h + key) := hfit.of_le (by
    have := (eval ((decode as.length v).zip as) g).isLt
    dsimp only [key]
    omega)
  let y := (z.set address (h + key)).set link (x.mem (h + key))
  have hr : ExecWithin (B := .standard) W
      (ram[ address ← heads + state; link ← *address ]) z y 2 := by
    ram_eval [y, key, zh, zs, zm, ha, address, heads, state, link, Fin.mk.injEq]
  have exec := he.seq hr
  exact ⟨y, exec, by simp [y, key], (exec.regs_eq (by decide)).trans hv,
    by simpa only [y, Data.set_mem] using zm, fun r hp => exec.regs_eq hp⟩

/-- Retention preserves every computed inverse bucket, not only the bucket it
consumed. No linked-record or dictionary-validity premise is required. This
layout connection applies to arbitrary widths, collisions and zero witnesses. -/
theorem retainedMemory_linked {m h f p D : ℕ}
    (as bs : List (BitVec m)) (t : BitVec m) (mem : ℕ → ℕ)
    (v : ℕ) (g k : Fin (2 ^ p))
    (hf : 0 < f) (hh : h + 2 ^ p ≤ f) (hD : f + 3 * 2 ^ as.length ≤ D) :
    let prepared := preparedMemory as t (clear mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length)
    let retained := Dictionary.filledMemory D (retainedEntries bs v (records as t p g.val))
      prepared 0
    Linked retained (f + 3 * 2 ^ as.length) (retained (h + k.val)) (records as t p k.val) := by
  dsimp only
  have frame (a : ℕ) (ha : a < D) := Dictionary.filledMemory_below D
    (retainedEntries bs v (records as t p g.val))
    (preparedMemory as t (clear mem h (2 ^ p)) h f (2 ^ p) (2 ^ as.length)) 0 a ha
  rw [frame (h + k.val) (by have := k.isLt; omega)]
  exact (preparedMemory_linked as t _ h f (2 ^ p) (2 ^ as.length) k.val k.isLt hf hh
    (clear_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left k.isLt _⟩)).frame
    (fun a ha => frame a (by omega))

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter.Backward
