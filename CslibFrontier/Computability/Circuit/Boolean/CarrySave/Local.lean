/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave

/-!
# Seven-input local carry-save queries

A bit of the existing four-to-two compressor depends on seven bits of its four input words.
The selected input positions are the requested position minus zero, one, or two, with false
below position zero. The two formulas and their source routing are fixed, independent of word
width. This is the local semantic kernel for incremental descent through an iterated-sum tree:
a branch chooses one child pair and decrements its bit position by at most two.

The results identify the formulas with the actual `csa4to2` circuit. They do not yet implement
incremental tape updates or assert an amortized native running time.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.CarrySaveLocal

open BitString

/-- One input to a local compressor formula: a word number and a downward bit offset. -/
structure Source where
  /-- One of the four words, in the two input pairs' order. -/
  word : Fin 4
  /-- Subtract zero, one, or two from the requested bit position. -/
  shift : Fin 3
  deriving DecidableEq, Fintype

/-- Port zero reads the fourth word, ports one to three the first three words, and ports four
to six their preceding bits. Carry queries shift every source one further position down. -/
def source (carry : Bool) (port : Fin 7) : Source where
  word := if port.val = 0 then 3 else if h : port.val < 4 then ⟨port.val - 1, by omega⟩
    else ⟨port.val - 4, by omega⟩
  shift := ⟨carry.toNat + (if port.val < 4 then 0 else 1), by split <;> cases carry <;> simp_all⟩

/-- Every local move changes the bit position by at most two. -/
theorem source_shift_le (carry : Bool) (port : Fin 7) : (source carry port).shift.val ≤ 2 :=
  Nat.le_of_lt_succ (source carry port).shift.isLt

/-- XOR of the three unshifted compressor inputs. -/
def xorThree : Formula signature 7 :=
  ((Formula.input 1).xor (.input 2)).xor (.input 3)

/-- Majority of the three shifted compressor inputs. -/
def carryThree : Formula signature 7 := maj3Formula 4 5 6

/-- The fixed sum/carry formula. Neither constructing it nor choosing a port depends on width. -/
def formula (carry : Bool) : Formula signature 7 :=
  if carry then
    ((Formula.input 0).and xorThree).or
      (((Formula.input 0).and carryThree).or (xorThree.and carryThree))
  else ((Formula.input 0).xor xorThree).xor carryThree

/-- Evaluate the two fixed formulas as the full-adder XOR and majority. -/
theorem eval_formula (carry : Bool) (bits : BitString 7) :
    (formula carry).eval interpretation bits =
      if carry then maj3 (bits 0) ((bits 1 ^^ bits 2) ^^ bits 3)
        (maj3 (bits 4) (bits 5) (bits 6))
      else (bits 0 ^^ ((bits 1 ^^ bits 2) ^^ bits 3)) ^^
        maj3 (bits 4) (bits 5) (bits 6) := by
  cases carry <;> simp [formula, xorThree, carryThree, maj3]

/-- Both formulas have depth at most twelve, independent of precision. -/
theorem depth_formula_le (carry : Bool) : (formula carry).depth ≤ 12 := by
  cases carry <;> decide

/-- Read a lower bit, with false padding below zero. -/
def readBelow {w : ℕ} (x : BitString w) (i : Fin w) (shift : ℕ) : Bool :=
  if h : shift ≤ i.val then x ⟨i.val - shift, by omega⟩ else false

/-- The seven input bits routed from four runtime words. -/
def inputs {w : ℕ} (words : Fin 4 → BitString w) (i : Fin w) (carry : Bool) : BitString 7 :=
  fun port => readBelow (words (source carry port).word) i (source carry port).shift.val

/-- The existing circuit first compresses the first three words and then combines the resulting
pair with the fourth word. This statement retains the circuit's actual word ordering. -/
theorem eval_compressor {w : ℕ} (a b c d : BitString w) :
    (csa4to2 w).eval interpretation (Fin.append (Fin.append a b) (Fin.append c d)) =
      Fin.append (csaSum d (csaSum a b c) (csaCarry a b c))
        (csaCarry d (csaSum a b c) (csaCarry a b c)) := by
  have hwire : Fin.append (Fin.append a b) (Fin.append c d) ∘ csa4to2FirstIn w =
      Fin.append a (Fin.append b c) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [csa4to2FirstIn, -Fin.natAdd_eq_addNat]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp [csa4to2FirstIn, -Fin.natAdd_eq_addNat]
  have hd : Fin.append (Fin.append a b) (Fin.append c d) ∘
      (Fin.natAdd (w+w) ∘ Fin.natAdd w) = d := by
    funext i
    simp [-Fin.natAdd_eq_addNat]
  simp only [csa4to2, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring,
    hwire, hd, eval_csa3to2, fstBits_append, sndBits_append]

/-- A sum-bit query reads exactly the seven indicated bits. -/
theorem eval_sum {w : ℕ} (a b c d : BitString w) (i : Fin w) :
    (formula false).eval interpretation (inputs ![a,b,c,d] i false) =
      csaSum d (csaSum a b c) (csaCarry a b c) i := by
  rw [eval_formula]
  by_cases hi : 0 < i.val <;>
    simp [inputs, source, readBelow, csaSum, csaCarry,
      show (1 ≤ i.val) ↔ 0 < i.val by omega, hi, maj3]

/-- A carry-bit query reads the same pattern one position down, with false boundary bits. -/
theorem eval_carry {w : ℕ} (a b c d : BitString w) (i : Fin w) :
    (formula true).eval interpretation (inputs ![a,b,c,d] i true) =
      csaCarry d (csaSum a b c) (csaCarry a b c) i := by
  rw [eval_formula]
  by_cases hi : 0 < i.val
  · have h1 : 1 ≤ i.val := hi
    by_cases h2 : 1 < i.val <;>
      simp [inputs, source, readBelow, csaCarry, csaSum, hi, h1, h2,
        show (2 ≤ i.val) ↔ 1 < i.val by omega,
        show (0 < i.val - 1) ↔ 1 < i.val by omega, Nat.sub_sub, maj3]
  · have hz : i.val = 0 := by omega
    simp [inputs, source, readBelow, csaCarry, hz, maj3]

/-- The local formulas agree with either output word of the actual compressor circuit. -/
theorem eval_formula_compressor {w : ℕ} (a b c d : BitString w) (i : Fin w) (carry : Bool) :
    (formula carry).eval interpretation (inputs ![a,b,c,d] i carry) =
      (csa4to2 w).eval interpretation (Fin.append (Fin.append a b) (Fin.append c d))
        (if carry then Fin.natAdd w i else Fin.castAdd w i) := by
  rw [eval_compressor]
  cases carry
  · simpa only [Bool.false_eq_true, ↓reduceIte, Fin.append_left] using eval_sum a b c d i
  · simpa only [↓reduceIte, Fin.append_right] using eval_carry a b c d i

end Cslib.Circuits.Boolean.CarrySaveLocal
