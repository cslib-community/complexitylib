/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Workspace
import Mathlib.Data.Nat.Bitwise
import all Init.Data.Nat.Bitwise.Basic

/-!
# Checked limbwise Boolean operations

Little-endian half-word digits support bitwise operations independently in each limb.
The fixed register lists determine the code. Four workspace registers are reserved as in
schoolbook multiplication.

## Main definitions

* `Cslib.WordRAM.Multiword.Bitwise.Supported`: and, or, and exclusive or.
* `Cslib.WordRAM.Multiword.Bitwise.program`: one standard instruction per limb.

## Main results

* `Cslib.WordRAM.Multiword.Bitwise.exec`: checked execution, exact reconstructed result,
  bounded output digits, and preservation of every register outside the output list.

## References

* [T. Hagerup, *Sorting and searching on the word RAM*][Hagerup1998].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Bitwise

open Workspace

variable {r : ℕ}

/-- The binary Boolean operations supported by the limbwise routine. -/
def Supported (f : BinOp) : Prop := f = .and ∨ f = .or ∨ f = .xor

private theorem exists_truthTable {f : BinOp} (hf : Supported f) :
    ∃ g : Bool → Bool → Bool, g false false = false ∧ f.eval = Nat.bitwise g := by
  rcases hf with rfl | rfl | rfl
  · exact ⟨(· && ·), rfl, rfl⟩
  · exact ⟨(· || ·), rfl, rfl⟩
  · exact ⟨(· != ·), rfl, rfl⟩

/-- Boolean operations preserve a power-of-two digit bound. -/
theorem eval_lt {f : BinOp} (hf : Supported f) {k a b : ℕ}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) : f.eval a b < 2 ^ k := by
  obtain ⟨g, _, hg⟩ := exists_truthTable hf
  rw [hg]
  exact Nat.bitwise_lt_two_pow ha hb

/-- A Boolean operation commutes with adjoining one low power-of-two digit. -/
theorem eval_cons {f : BinOp} (hf : Supported f) {k a b : ℕ}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) (A B : ℕ) :
    f.eval (a + 2 ^ k * A) (b + 2 ^ k * B) =
      f.eval a b + 2 ^ k * f.eval A B := by
  obtain ⟨g, hg, he⟩ := exists_truthTable hf
  rw [he]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.add_comm a, Nat.add_comm b, Nat.add_comm (Nat.bitwise g a b),
    Nat.testBit_two_pow_mul_add A ha, Nat.testBit_two_pow_mul_add B hb,
    Nat.testBit_two_pow_mul_add _ (Nat.bitwise_lt_two_pow ha hb),
    Nat.testBit_bitwise hg]
  split <;> rfl

/-- Unrolled limbwise code. A final workspace self-copy makes the empty program executable. -/
def program (f : BinOp) : List (Fin (r + 4)) → List (Fin (r + 4)) →
    List (Fin (r + 4)) → Code .standard (r + 4)
  | a :: as, b :: bs, d :: ds => .seq (.op (.bin f d a b)) (program f as bs ds)
  | _, _, _ => .op (.copy carry carry)

/-- Exact code size, including the final self-copy. -/
theorem size_program (f : BinOp) (as bs ds : List (Fin (r + 4)))
    (hab : as.length = bs.length) (had : as.length = ds.length) :
    (program f as bs ds).size = ds.length + 1 := by
  induction as generalizing bs ds with
  | nil => cases bs <;> cases ds <;> simp_all [program]
  | cons a as ih =>
    cases bs <;> cases ds <;> simp_all [program, Code.size, Nat.add_comm]

/-- Execute a Boolean operation on equal-length bounded digit lists. Source lists may share
registers; destinations are distinct and disjoint from both sources. All non-output registers,
including all four workspace registers, are preserved. -/
theorem exec {w : ℕ} (hw : 2 ≤ w) {f : BinOp} (hf : Supported f)
    (as bs ds : List (Fin (r + 4)))
    (hab : as.length = bs.length) (had : as.length = ds.length)
    (hin : ∀ i ∈ as ++ bs, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds (as ++ bs))
    (x : Data (r + 4)) (ha : Bounded (radix w) x as) (hb : Bounded (radix w) x bs) :
    ∃ y, Exec w (program f as bs ds) x y (ds.length + 1) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = f.eval (value (radix w) x as) (value (radix w) x bs) ∧
      Frame x y ds ∧ ∀ i ∉ ds, y.regs i = x.regs i := by
  induction as generalizing bs ds x with
  | nil =>
    cases bs with
    | cons => simp only [List.length_cons, List.length_nil] at hab; omega
    | nil =>
      cases ds with
      | cons => simp only [List.length_cons, List.length_nil] at had; omega
      | nil =>
        refine ⟨x.set carry (x.regs carry), ?_, by simp [Bounded], ?_, ?_, ?_⟩
        · ram_eval [program]
        · obtain ⟨g, _, hg⟩ := exists_truthTable hf
          change 0 = f.eval 0 0
          rw [hg, Nat.bitwise_zero]
        · exact ⟨rfl, fun i _ _ _ => by simp⟩
        · intro i _
          simp
  | cons a as ih =>
    cases bs with
    | nil => simp only [List.length_cons, List.length_nil] at hab; omega
    | cons b bs =>
      cases ds with
      | nil => simp only [List.length_cons, List.length_nil] at had; omega
      | cons d ds =>
        have hab' : as.length = bs.length := by simpa using hab
        have had' : as.length = ds.length := by simpa using had
        have hdis' : List.Disjoint ds (as ++ bs) := by
          apply List.disjoint_left.mpr
          intro i hi hj
          exact List.disjoint_left.mp hdis (List.mem_cons_of_mem d hi) (by
            simp only [List.mem_append, List.mem_cons] at hj ⊢
            tauto)
        have hdinputs (i : Fin (r + 4)) (hi : i ∈ a :: as ++ b :: bs) : i ≠ d := by
          rintro rfl
          exact List.disjoint_left.mp hdis (by simp) hi
        let z := x.set d (f.eval (x.regs a) (x.regs b))
        have hza (i : Fin (r + 4)) (hi : i ∈ a :: as ++ b :: bs) :
            z.regs i = x.regs i := by simp [z, hdinputs i hi]
        have hzlt := eval_lt hf (ha a (by simp)) (hb b (by simp))
        have hzfit : Fits w (f.eval (x.regs a) (x.regs b)) :=
          hzlt.trans (radix_fits hw)
        have hez : Exec w (.op (.bin f d a b)) x z 1 := by
          apply Exec.op
          simpa only [Op.eval_bin] using (Data.put_of_fits hzfit)
        obtain ⟨y, hey, hyb, hyv, hyf, hyp⟩ := ih bs ds hab' had'
          (fun i hi => hin i (by
            simp only [List.mem_append, List.mem_cons] at hi ⊢
            tauto)) (fun i hi => hout i (by simp [hi]))
          (List.nodup_cons.mp hnd).2 hdis' z
          (fun i hi => by rw [hza i (by simp [hi])]; exact ha i (by simp [hi]))
          (fun i hi => by rw [hza i (by simp [hi])]; exact hb i (by simp [hi]))
        have hyd : y.regs d = f.eval (x.regs a) (x.regs b) := by
          rw [hyp d (List.nodup_cons.mp hnd).1]
          simp [z]
        have hva : value (radix w) z as = value (radix w) x as :=
          value_congr fun i hi => hza i (by simp [hi])
        have hvb : value (radix w) z bs = value (radix w) x bs :=
          value_congr fun i hi => hza i (by simp [hi])
        have hp : ∀ i ∉ d :: ds, y.regs i = x.regs i := by
          intro i hi
          rw [hyp i (fun hm => hi (by simp [hm]))]
          simp [z, show i ≠ d by intro h; exact hi (by simp [h])]
        refine ⟨y, ?_, ?_, ?_, ⟨hyf.1, fun i hi _ _ => hp i hi⟩, hp⟩
        · simpa only [program, List.length_cons, Nat.add_comm 1] using hez.seq hey
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · rw [hyd]; exact hzlt
          · exact hyb i hi
        · change y.regs d + radix w * value (radix w) y ds =
            f.eval (x.regs a + radix w * value (radix w) x as)
              (x.regs b + radix w * value (radix w) x bs)
          rw [hyd, hyv, hva, hvb]
          exact (eval_cons hf (ha a (by simp)) (hb b (by simp)) _ _).symm

end Cslib.WordRAM.Multiword.Bitwise

end
