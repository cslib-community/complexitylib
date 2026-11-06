/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeBuckets
public import Complexity.Cryptanalysis.AddXNORNativeReverse

/-!
# Native inverse quarter queries

For [WangLvShenZhang2027], Lemma 8, PDF pp. 21–22, a second-quarter
index is inverted on the low-bit instance and used as an actual head-array
address. Native bit reversal and complement conjugacy reuse the forward
interpreter; every bit, address, load and control instruction is charged.
The reversed projected operand array is an explicit prerequisite, constructed
by the native projection API rather than installed as a free oracle here.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Current pointer into the matching bucket; zero terminates the chain. -/
abbrev link : Fin 32 := 22
/-- Original forward-order operator index, saved during inverse evaluation. -/
abbrev queryOperators : Fin 32 := 23

/-- Invert a quarter with its original packed operator order. `base` addresses
its reversed operands. Both operand reversal and projection are external native
preprocessing operations, not hidden instructions in this code. -/
@[expose] def backwardEvaluate : Code .standard 32 :=
  .seq reverseOperators
    (.seq (ram[ queryOperators ← operators; one ← #1; mask ← modulus - one;
      state ← state ^^^ mask; operators ← reversed ])
      (.seq evaluate (ram[ state ← state ^^^ mask; operators ← queryOperators ])))

/-- The inverse kernel computes the actual backward chain and restores the
original packed index. All intermediate complement and index words fit. -/
theorem backwardEvaluate_exec {W m b v : ℕ} (as : List (BitVec m)) (t : BitVec m)
    (x : Data 32) (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ m) (ht : x.regs state = t.toNat)
    (hv : x.regs operators = v) (hfv : Fits W v)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hfit : Fits W (b + as.length + 2 * 2 ^ m + 2 ^ as.length + 4)) :
    ∃ y, ExecWithin W backwardEvaluate x y (18 * as.length + 21) ∧
      y.regs state = (backward ((decode as.length v).zip as) t).toNat ∧
      y.regs operators = v ∧ y.mem = x.mem := by
  have hQ : 0 < 2 ^ as.length := Nat.two_pow_pos _
  obtain ⟨z, heReverse, zr, zm⟩ := reverseOperators_exec x hc hv hfv
    (hfit.of_le (by omega))
  have zbase : z.regs base = b := (heReverse.regs_eq (by decide)).trans hb
  have zcount : z.regs count = as.length := (heReverse.regs_eq (by decide)).trans hc
  have zmod : z.regs modulus = 2 ^ m := (heReverse.regs_eq (by decide)).trans hn
  have zstate : z.regs state = t.toNat := (heReverse.regs_eq (by decide)).trans ht
  have zops : z.regs operators = v := (heReverse.regs_eq (by decide)).trans hv
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hm : Fits W (2 ^ m - 1) := hfit.of_le (by omega)
  have hnot : t.toNat ^^^ (2 ^ m - 1) = (~~~t).toNat := by
    have h := congrArg BitVec.toNat (show t ^^^ BitVec.allOnes m = ~~~t from BitVec.xor_allOnes)
    simpa only [List.zip, BitVec.toNat_xor, BitVec.toNat_allOnes] using h
  have hnotfit : Fits W (~~~t).toNat := hfit.of_le (by have := (~~~t).isLt; omega)
  let u := z.set queryOperators v |>.set one 1 |>.set mask (2 ^ m - 1)
    |>.set state (~~~t).toNat |>.set operators (encode (decode as.length v).reverse)
  have heSetup : ExecWithin (B := .standard) W
      (ram[ queryOperators ← operators; one ← #1; mask ← modulus - one;
        state ← state ^^^ mask; operators ← reversed ]) z u 5 := by
    ram_eval [u, zops, zmod, zstate, zr, h1, hm, hnot, hnotfit,
      queryOperators, operators, one, mask, modulus, state, reversed, Fin.mk.injEq]
  have hrevfit : Fits W (encode (decode as.length v).reverse) :=
    hfit.of_le ((encode_lt _).le.trans (by simp only [List.length_reverse, decode_length]; omega))
  obtain ⟨r, heEval, rstate, _, _, rmem, _, rmask⟩ := evaluate_exec as.reverse (~~~t) u
    (by simpa +decide [u, base, queryOperators, one, mask, state, operators] using zbase)
    (by simpa +decide [u, count, queryOperators, one, mask, state, operators] using zcount)
    (by simpa +decide [u, modulus, queryOperators, one, mask, state, operators] using zmod)
    (by simp +decide [u, state, operators]) (by simp [u]) hrevfit
    (by simpa only [u, Data.set_mem, zm] using hinput)
    (hfit.of_le (by simp only [List.length_reverse]; omega))
  have hdecode : decode as.reverse.length (encode (decode as.length v).reverse) =
      (decode as.length v).reverse := by
    simpa only [List.length_reverse, decode_length] using decode_encode (decode as.length v).reverse
  rw [hdecode] at rstate
  simp only [List.zip] at rstate
  rw [← List.reverse_zipWith (by simp : (decode as.length v).length = as.length)] at rstate
  let out := backward ((decode as.length v).zip as) t
  have rout : r.regs state ^^^ (2 ^ m - 1) = out.toNat := by
    rw [rstate]
    have h := congrArg BitVec.toNat
      (show eval (((decode as.length v).zip as).reverse) (~~~t) ^^^ BitVec.allOnes m = out by
        rw [BitVec.xor_allOnes]
        exact (backward_eq_not_eval_reverse _ _).symm)
    simpa only [List.zip, BitVec.toNat_xor, BitVec.toNat_allOnes] using h
  have rquery : r.regs queryOperators = v := by
    rw [heEval.regs_eq (by decide)]
    simp +decide [u, queryOperators, one, mask, state, operators]
  let y := (r.set state out.toNat).set operators v
  have heOut : ExecWithin (B := .standard) W
      (ram[ state ← state ^^^ mask; operators ← queryOperators ]) r y 2 := by
    have ho : Fits W out.toNat := hfit.of_le (by have := out.isLt; omega)
    ram_eval [y, rout, rmask, rquery, ho, state, operators, mask, queryOperators, Fin.mk.injEq]
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · exact (heReverse.seq (heSetup.seq (heEval.seq heOut))).mono
      (by simp only [List.length_reverse]; omega)
  · simp +decide [y, state, operators, out]
  · simp [y]
  · simpa only [y, Data.set_mem, u, zm] using rmem

/-- Evaluate the inverse and read exactly one matching bucket pointer. -/
@[expose] def queryBucket : Code .standard 32 :=
  .seq backwardEvaluate (ram[ address ← heads + state; link ← *address ])

/-- Native low-bit predicate filtering uses the computed inverse as an address.
It never scans the other first-quarter buckets. -/
theorem queryBucket_exec {W p b h v : ℕ} (as : List (BitVec p)) (g : BitVec p)
    (x : Data 32) (hb : x.regs base = b) (hc : x.regs count = as.length)
    (hn : x.regs modulus = 2 ^ p) (hg : x.regs state = g.toNat)
    (hv : x.regs operators = v) (hfv : Fits W v) (hh : x.regs heads = h)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hfit : Fits W (h + b + as.length + 2 * 2 ^ p + 2 ^ as.length + 4)) :
    ∃ y, ExecWithin W queryBucket x y (18 * as.length + 23) ∧
      y.regs link = x.mem (h + (backward ((decode as.length v).zip as) g).toNat) ∧
      y.regs operators = v ∧ y.mem = x.mem := by
  have hQ : 0 < 2 ^ as.length := Nat.two_pow_pos _
  obtain ⟨z, he, zs, zo, zm⟩ := backwardEvaluate_exec as g x hb hc hn hg hv hfv hinput
    (hfit.of_le (by omega))
  have zh : z.regs heads = h := (he.regs_eq (by decide)).trans hh
  let key := (backward ((decode as.length v).zip as) g).toNat
  have ha : Fits W (h + key) := hfit.of_le (by
    have := (backward ((decode as.length v).zip as) g).isLt;
    dsimp [key];
    omega)
  let y := (z.set address (h + key)).set link (x.mem (h + key))
  have heRead : ExecWithin (B := .standard) W (ram[ address ← heads + state; link ← *address ])
      z y 2 := by
    ram_eval [y, key, zh, zs, zm, ha, address, heads, state, link, Fin.mk.injEq]
  refine ⟨y, he.seq heRead, by simp [y, key], ?_, ?_⟩
  · simpa +decide [y, operators, address, link] using zo
  · simpa only [y, Data.set_mem] using zm

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
