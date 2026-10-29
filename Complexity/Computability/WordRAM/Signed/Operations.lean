/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.State
public import Complexity.Computability.WordRAM.Signed.Comparison

/-!
# Translating signed RAM data operations and tests

All five operations of `GenericRAM.Signed.Arithmetic` (addition, subtraction, multiplication,
Euclidean division and Euclidean remainder), together with constants, copies, memory operations
and signed comparisons, are translated to unsigned word-RAM code. The existing source
interpreter, including its signed range and address checks, determines successful source
steps. The target blocks operate on the separate register bank and encode every memory value.

## Main definitions

* `ToWordRAM.arithmeticCode`, `ToWordRAM.compileOp`: unsigned instruction blocks.
* `ToWordRAM.compileCond`: comparison returning a Boolean word and a constant one.

## Main results

* `ToWordRAM.exec_compileOp`: successful source data operations transfer within twenty-three steps.
* `ToWordRAM.exec_compileCond`: signed comparisons transfer with a preserved source state.

## References

The translation is an original implementation using the existing signed RAM semantics.
-/

@[expose] public section

namespace Cslib.GenericRAM.Signed.ToWordRAM

open WordRAM (Code ExecWithin Exec)
open WordRAM.Signed

variable {r : ℕ}

/-- Unsigned instruction block implementing each of the five signed arithmetic operations. -/
def arithmeticCode : Arithmetic → Code .standard (r + 9)
  | .add => WordRAM.Signed.add
  | .sub => subtract
  | .mul => multiply
  | .div => divide
  | .mod => modulo

/-- Decode a nonnegative signed address into scratch register `left`. -/
def addressCode (a : Fin r) : Code .standard (r + 9) :=
  .seq (.op (.const two 2)) (.op (.bin .div left (bank a) two))

/-- Copy both operands to scratch before updating any source register. -/
def operandsCode (a b : Fin r) : Code .standard (r + 9) :=
  .seq (.op (.copy left (bank a))) (.op (.copy right (bank b)))

/-- Translate one data operation, retaining source memory addresses. -/
def compileOp : GenericRAM.Op model r → Code .standard (r + 9)
  | .const d c => .op (.const (bank d) (encode c))
  | .copy d s => .op (.copy (bank d) (bank s))
  | .alu f d args =>
      .seq (operandsCode (args 0) (args 1))
        (.seq (arithmeticCode f) (.op (.copy (bank d) result)))
  | .load d a =>
      .seq (addressCode a) (.op (.load (bank d) left))
  | .store a s =>
      .seq (addressCode a) (.op (.store left (bank s)))

/-- Translate equality or signed ordering. `result` holds zero or one and `two` holds one. -/
def compileCond : GenericRAM.Cond model r → Code .standard (r + 9)
  | .test .eq args =>
      .seq (.op (.const two 1))
        (.branch (.eq (bank (args 0)) (bank (args 1)))
          (.op (.const result 1)) (.op (.const result 0)))
  | .test .lt args =>
      .seq (operandsCode (args 0) (args 1)) (.seq less (.op (.const two 1)))

private theorem two_fits (w : ℕ) : WordRAM.Fits (w + 2) 2 :=
  (show WordRAM.Fits 2 2 from by decide).mono (by omega)

private theorem encoded_fits {w : ℕ} {v : ℤ} (h : Signed.Fits w v) :
    WordRAM.Fits (w + 2) (encode v) := (encode_fits h).mono (by omega)

private theorem exec_arithmetic {w : ℕ} {a b : ℤ} (f : Arithmetic)
    (ha : Signed.Fits w a) (hb : Signed.Fits w b) (hv : Signed.Fits w (f.eval a b))
    (x : WordRAM.Data (r + 9)) (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) (arithmeticCode f) x y 20 ∧
      y.regs result = encode (f.eval a b) ∧ Frame x y := by
  cases f with
  | add =>
    obtain ⟨y, hy, hv, hf⟩ := exec_add ha hb x hxa hxb
    exact ⟨y, hy.mono (by decide), hv, hf⟩
  | sub =>
    obtain ⟨y, hy, hv, hf⟩ := exec_subtract ha hb x hxa hxb
    exact ⟨y, hy.mono (by decide), hv, hf⟩
  | mul =>
    obtain ⟨y, hy, hv, hf⟩ := exec_multiply ha hb hv x hxa hxb
    exact ⟨y, hy.mono (by decide), hv, hf⟩
  | div => exact exec_divide ha hb x hxa hxb
  | mod =>
    obtain ⟨y, hy, hv, hf⟩ := exec_modulo ha hb x hxa hxb
    exact ⟨y, hy.mono (by decide), hv, hf⟩

/-- Nonnegative signed addresses are decoded in two instructions without changing source data. -/
theorem exec_address {w : ℕ} {s : GenericRAM.Data model r} {x : WordRAM.Data (r + 9)}
    (hx : Represents w s x) (a : Fin r) (ha : 0 ≤ s.regs a) :
    ∃ y, ExecWithin (w + 2) (addressCode a) x y 2 ∧
      y.regs left = (s.regs a).toNat ∧ Represents w s y := by
  let y := (x.set two 2).set left (s.regs a).toNat
  have hv : encode (s.regs a) / 2 = (s.regs a).toNat := by
    rw [encode_div_two]
    have := Int.eq_natAbs_of_nonneg ha
    omega
  have hf : WordRAM.Fits (w + 2) ((s.regs a).toNat) :=
    (encoded_fits (hx.fits a)).of_le (by unfold encode; split_ifs <;> omega)
  refine ⟨y, ?_, by simp [y], ?_⟩
  · let z := x.set two 2
    have hz := hx.scratch (i := two) (by dsimp [two]; omega) 2
    have hzr : z.regs (bank a) = encode (s.regs a) := hz.regs a
    have hz2 : z.regs two = 2 := by simp [z]
    have hd : WordRAM.Fits (w + 2) (WordRAM.BinOp.div.eval (z.regs (bank a)) (z.regs two)) := by
      simpa only [WordRAM.BinOp.eval, hzr, hz2, hv] using hf
    have he := Exec.bin (x := z) (d := left) hd
    have hdiv : Exec (B := .standard) (w + 2) (.op (.bin .div left (bank a) two)) z y 1 := by
      simpa only [WordRAM.BinOp.eval, hzr, hz2, hv] using he
    exact (Exec.const (x := x) (d := two) (two_fits w)).within.seq hdiv.within
  · exact (hx.scratch (i := two) (by dsimp [two]; omega) _).scratch
      (i := left) (by dsimp [left]; omega) _

/-- Copy the operands to the arithmetic workspace without changing represented source data. -/
theorem exec_operands {w : ℕ} {s : GenericRAM.Data model r} {x : WordRAM.Data (r + 9)}
    (hx : Represents w s x) (a b : Fin r) :
    ∃ y, ExecWithin (w + 2) (operandsCode a b) x y 2 ∧
      y.regs left = encode (s.regs a) ∧ y.regs right = encode (s.regs b) ∧ Represents w s y := by
  let q := x.set left (encode (s.regs a))
  let y := q.set right (encode (s.regs b))
  have hq := hx.scratch (i := left) (by dsimp [left]; omega) (encode (s.regs a))
  have hqr : q.regs (bank b) = encode (s.regs b) := hq.regs _
  have hfirst : Exec (B := .standard) (w + 2) (.op (.copy left (bank a))) x q 1 := by
    simpa only [hx.regs] using (Exec.copy (B := .standard) (w := w + 2)
      (x := x) (d := left) (s := bank a))
  have hsecond : Exec (B := .standard) (w + 2) (.op (.copy right (bank b))) q y 1 := by
    simpa only [hqr] using (Exec.copy (B := .standard) (w := w + 2)
      (x := q) (d := right) (s := bank b))
  exact ⟨y, (hfirst.seq hsecond).within, by simp [y, q, left, right], by simp [y],
    hq.scratch (i := right) (by simp) _⟩

/-- Every successful source data operation has an unsigned implementation in at most
twenty-three instructions at width `w + 2`. Aliased source/destination registers are allowed. -/
theorem exec_compileOp {w : ℕ} {s t : GenericRAM.Data model r} {x : WordRAM.Data (r + 9)}
    (o : GenericRAM.Op model r) (hx : Represents w s x)
    (he : o.eval w s = some t) :
    ∃ y, ExecWithin (w + 2) (compileOp o) x y 23 ∧ Represents w t y := by
  cases o with
  | const d c =>
    by_cases hc : Signed.Fits w c
    · have ht : s.set d c = t := by
        simpa [GenericRAM.Op.eval, model, GenericRAM.Data.put, hc] using he
      subst t
      exact ⟨_, (Exec.const (encoded_fits hc)).within.mono (by decide), hx.set d hc⟩
    · simp [GenericRAM.Op.eval, model, GenericRAM.Data.put, hc] at he
  | copy d i =>
    have hi := hx.fits i
    have ht : s.set d (s.regs i) = t := by
      simpa [GenericRAM.Op.eval, model, GenericRAM.Data.move, hi] using he
    subst t
    refine ⟨x.set (bank d) (encode (s.regs i)), ?_, hx.set d hi⟩
    simpa only [compileOp, hx.regs] using
      (Exec.copy (B := .standard) (w := w + 2) (x := x) (d := bank d) (s := bank i)).within.mono
        (by decide : 1 ≤ 23)
  | alu f d args =>
    by_cases hv : Signed.Fits w (f.eval (s.regs (args 0)) (s.regs (args 1)))
    · have ht : s.set d (f.eval (s.regs (args 0)) (s.regs (args 1))) = t := by
        simpa [GenericRAM.Op.eval, model, GenericRAM.Data.put, hv, Function.comp_def] using he
      subst t
      obtain ⟨z, hpre, hza, hzb, hz⟩ := exec_operands hx (args 0) (args 1)
      obtain ⟨y, hy, hyr, hyf⟩ := exec_arithmetic f (hx.fits _) (hx.fits _) hv z hza hzb
      have hyrep := hz.of_frame hyf
      refine ⟨y.set (bank d) (encode (f.eval (s.regs (args 0)) (s.regs (args 1)))), ?_,
        hyrep.set d hv⟩
      have hlast : Exec (B := .standard) (w + 2) (.op (.copy (bank d) result)) y
          (y.set (bank d) (encode (f.eval (s.regs (args 0)) (s.regs (args 1))))) 1 := by
        simpa only [hyr] using (Exec.copy (B := .standard) (w := w + 2) (x := y)
          (d := bank d) (s := result))
      -- The two operand copies precede the arithmetic block; the destination copy follows it.
      exact hpre.seq (hy.seq hlast.within)
    · simp [GenericRAM.Op.eval, model, GenericRAM.Data.put, hv] at he
  | load d a =>
    by_cases hn : s.regs a < 0 ∨ s.regs a ≥ ((2 : ℤ) ^ w)
    · simp [GenericRAM.Op.eval, model, hn] at he
    · have hnonneg : 0 ≤ s.regs a := le_of_not_gt (fun h => hn (Or.inl h))
      by_cases hv : Signed.Fits w (s.mem (s.regs a).toNat)
      · have ht : s.set d (s.mem (s.regs a).toNat) = t := by
          simpa [GenericRAM.Op.eval, GenericRAM.Data.move, model, hn, hv] using he
        subst t
        obtain ⟨y, hy, hya, hyr⟩ := exec_address hx a hnonneg
        have hl : Exec (B := .standard) (w + 2) (.op (.load (bank d) left)) y
            (y.set (bank d) (encode (s.mem (s.regs a).toNat))) 1 := by
          simpa only [hya, hyr.mem] using (Exec.load (B := .standard) (w := w + 2)
            (x := y) (d := bank d) (a := left))
        exact ⟨_, (hy.seq hl.within).mono (by decide), hyr.set d hv⟩
      · simp [GenericRAM.Op.eval, GenericRAM.Data.move, model, hn, hv] at he
  | store a i =>
    by_cases hn : s.regs a < 0 ∨ s.regs a ≥ ((2 : ℤ) ^ w)
    · simp [GenericRAM.Op.eval, model, hn] at he
    · have hnonneg : 0 ≤ s.regs a := le_of_not_gt (fun h => hn (Or.inl h))
      have hv := hx.fits i
      have ht : s.write (s.regs a).toNat (s.regs i) = t := by
        simpa [GenericRAM.Op.eval, model, hn, hv] using he
      subst t
      obtain ⟨y, hy, hya, hyr⟩ := exec_address hx a hnonneg
      have hl : Exec (B := .standard) (w + 2) (.op (.store left (bank i))) y
          (y.write (s.regs a).toNat (encode (s.regs i))) 1 := by
        simpa only [hya, hyr.regs] using (Exec.store (B := .standard) (w := w + 2)
          (x := y) (a := left) (s := bank i))
      exact ⟨_, (hy.seq hl.within).mono (by decide), hyr.write _ _⟩

/-- Every successful source test is implemented within fourteen instructions, returning its
Boolean result and preserving the source data. Scratch register `two` is set to one. -/
theorem exec_compileCond {w : ℕ} {s : GenericRAM.Data model r} {x : WordRAM.Data (r + 9)}
    (c : GenericRAM.Cond model r) (hx : Represents w s x) {b : Bool}
    (he : c.eval w s = some b) :
    ∃ y, ExecWithin (w + 2) (compileCond c) x y 14 ∧
      y.regs result = (if b then 1 else 0) ∧ y.regs two = 1 ∧ Represents w s y := by
  have h1 : WordRAM.Fits (w + 2) 1 := (two_fits w).of_le (by decide : 1 ≤ 2)
  cases c with
  | test f args =>
    cases f with
    | eq =>
      change some (decide (s.regs (args 0) = s.regs (args 1))) = some b at he
      have hb := Option.some.inj he
      subst b
      let q := x.set two 1
      have hq : Represents w s q := hx.scratch (i := two) (by dsimp [two]; omega) 1
      let y := q.set result (if s.regs (args 0) = s.regs (args 1) then 1 else 0)
      have hrun : ExecWithin (w + 2) (compileCond (.test .eq args)) x y 14 := by
        have hinit := Exec.const (B := .standard) (x := x) (d := two) h1
        by_cases hab : s.regs (args 0) = s.regs (args 1)
        · have hc : (WordRAM.Cond.eq (bank (args 0)) (bank (args 1))).Holds q := by
            change q.regs (bank (args 0)) = q.regs (bank (args 1))
            rw [hq.regs, hq.regs, hab]
          have hbody := ExecWithin.branch_pos (neg := .op (.const result 0)) hc
            (Exec.const (B := .standard) (x := q) (d := result) h1).within
          simpa only [compileCond, y, hab, ite_true] using
            (hinit.within.seq hbody).mono (by decide : 1 + (1 + 1) ≤ 14)
        · have hc : ¬(WordRAM.Cond.eq (bank (args 0)) (bank (args 1))).Holds q := by
            change ¬q.regs (bank (args 0)) = q.regs (bank (args 1))
            rw [hq.regs, hq.regs]
            exact fun h => hab (encode_injective h)
          have hbody := ExecWithin.branch_neg (pos := .op (.const result 1)) hc
            (Exec.const (B := .standard) (x := q) (d := result) (WordRAM.fits_zero (w + 2))).within
          simpa only [compileCond, y, hab, ite_false] using
            (hinit.within.seq hbody).mono (by decide : 1 + (1 + 2) ≤ 14)
      exact ⟨y, hrun, by simp [y], by simp [y, q, result, two, Fin.mk.injEq],
        hq.scratch (i := result) (by dsimp [result]; omega) _⟩
    | lt =>
      change some (decide (s.regs (args 0) < s.regs (args 1))) = some b at he
      have hb := Option.some.inj he
      subst b
      obtain ⟨z, hz, hza, hzb, hzr⟩ := exec_operands hx (args 0) (args 1)
      obtain ⟨y, hy, hyr, hyf⟩ := exec_less (two_fits w) z hza hzb
      let q := y.set two 1
      have hlast := Exec.const (B := .standard) (x := y) (d := two) h1
      refine ⟨q, hz.seq (hy.seq hlast.within), ?_, by simp [q],
        (hzr.of_frame hyf).scratch (i := two) (by dsimp [two]; omega) _⟩
      simpa [q, result, two, Fin.mk.injEq] using hyr

end Cslib.GenericRAM.Signed.ToWordRAM
