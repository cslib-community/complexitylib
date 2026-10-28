/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size

/-!
# Arithmetic on unary numbers, in logarithmic space

Counter programs (`Turing.CounterProgram`) that read a pair of unary numbers `a, b` into
registers with `Turing.CounterProgram.Words.headerCode` and evaluate an arithmetic expression
(`Turing.CounterProgram.Expr`) in them. The value is emitted in unary (a counting loop), in binary
(a loop over the powers of two up to the value), or compared with the value of a second
expression. A value bounded by a polynomial in `a + b` keeps the registers polynomially bounded,
so the function is computable in logarithmic space by
`Turing.CounterProgram.computableInLogSpace_of_reachesOut`; a comparison stores no value and needs
no bound.

The instances are unary multiplication, truncated subtraction, quotient, remainder, minimum and
maximum, the comparisons `<`, `≤` and `=`, and the conversion from unary to binary, stated for
functions computed in logarithmic space from a common input; all but the conversion are
registered with `fun_prop`.

## Main definitions

* `Turing.CounterProgram.Unary.unaryProgram`, `.binaryProgram`, `.ltProgram`: emitting the value
  of an expression in unary or binary, and comparing the values of two expressions.

## Main results

* `Turing.CounterProgram.Unary.computableInLogSpace_unary`,
  `Turing.CounterProgram.Unary.computableInLogSpace_binary`: a polynomially bounded function of
  two unary numbers given by an expression, with unary or binary output, in logarithmic space.
* `Turing.CounterProgram.Unary.computableInLogSpace_lt`: comparing two such functions.
* `Turing.MultiTapeTM.ComputableInLogSpace.unaryMul`, `.unarySub`, `.unaryDiv`, `.unaryMod`,
  `.unaryMin`, `.unaryMax`, `.unaryLt`, `.unaryLe`, `.unaryEq`, `.unaryToBinary`: the instances.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

namespace Turing.CounterProgram.Unary

open Instr Expr MultiTapeTM Words

/-! ### Programs -/

/-- The program emitting the value of `e` in unary: after the header, label `4` stores the value
in register `3`, and the counting loop at `5` emits a `true` for each value of register `2`
below it. -/
def unaryProgram (e : Expr) : CounterProgram where
  code := headerCode ++ [assign 3 e 5] ++ forCode 5 2 (reg 3) 8 9 ++ [emit true 7, halt []]
  registers := 4

/-- The program emitting the value of `e` in binary, least significant bit first: after the
header, label `4` stores the value `v` in register `3`; register `2` runs over the powers of two
`p ≤ v`, and for each the program emits the bit `v / p % 2`. -/
def binaryProgram (e : Expr) : CounterProgram where
  code := headerCode ++
    [assign 3 e 5,
     assign 2 (const 1) 6,
     lt (reg 3) (reg 2) 11 7,
     lt (const 0) (mod (div (reg 3) (reg 2)) (const 2)) 8 9,
     emit true 10,
     emit false 10,
     assign 2 (mul (const 2) (reg 2)) 6,
     halt []]
  registers := 4

/-- The program comparing the values of `e₁` and `e₂`: after the header, it accepts if the value
of `e₁` is less than that of `e₂`, and rejects otherwise. -/
def ltProgram (e₁ e₂ : Expr) : CounterProgram where
  code := headerCode ++ [lt e₁ e₂ 5 6, accept, reject]
  registers := 4

/-! ### Runs -/

section Runs

variable {a b B : ℕ}

private theorem encPair_unary (a b : ℕ) :
    encPair encUnary encUnary (a, b) = frame (List.replicate a true) ++ List.replicate b true :=
  rfl

private theorem length_input (a b : ℕ) :
    (encPair encUnary encUnary (a, b)).length = 2 * a + 1 + b := by
  simp [length_frame]

private theorem bounded4 {a₀ a₁ a₂ a₃ : ℕ} (h₀ : a₀ ≤ B) (h₁ : a₁ ≤ B) (h₂ : a₂ ≤ B)
    (h₃ : a₃ ≤ B) : ∀ x ∈ [a₀, a₁, a₂, a₃], x ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The header reads `a` into register `0` and `b` into register `1`. -/
private theorem reachesOut_header' {P : CounterProgram} (hP : P.CodeAt 0 headerCode)
    (hB : 2 * a + 1 + b ≤ B) :
    P.ReachesOut (encPair encUnary encUnary (a, b)) (P.Active B) (0, [0, 0, 0, 0])
      (4, [a, b, 0, 0]) [] := by
  have h := reachesOut_header (w := List.replicate a true) (k := b) hP (by simpa using hB)
  rw [List.length_replicate] at h
  exact h

private theorem reachesOut_unaryProgram (e : Expr) {v : ℕ} (hv : e.eval [a, b, 0, 0] = v)
    (hB : 2 * a + 1 + b ≤ B) (hvB : v ≤ B) :
    ∃ regs, (unaryProgram e).ReachesOut (encPair encUnary encUnary (a, b))
      ((unaryProgram e).Active B) (unaryProgram e).init (9, regs)
      ((List.range v).flatMap fun _ => [true]) ∧ ∀ r ∈ regs, r ≤ B := by
  have hhead := reachesOut_header' (P := unaryProgram e)
    (codeAt_of_code_eq (pre := []) (post := _) rfl) hB
  have hset : (unaryProgram e).ReachesOut (encPair encUnary encUnary (a, b))
      ((unaryProgram e).Active B) (4, [a, b, 0, 0]) (5, [a, b, 0, v]) [] :=
    ReachesOut.assign (show (unaryProgram e).instr 4 = _ from rfl)
      (bounded4 (by omega) (by omega) (by omega) (by omega)) (by simpa [hv] using ReachesOut.refl _)
  have hfor : (unaryProgram e).CodeAt 5 (forCode 5 2 (reg 3) 8 9) := by
    have h := codeAt_of_code_eq (P := unaryProgram e) (pre := headerCode ++ [assign 3 e 5])
      (l := forCode 5 2 (reg 3) 8 9) (post := [emit true 7, halt []]) (by simp [unaryProgram])
    simpa [headerCode] using h
  obtain ⟨regs, hloop, hinv⟩ := reachesOut_forCode (w := encPair encUnary encUnary (a, b))
    hfor (fun i regs => regs = [a, b, i, v] ∧ i ≤ v) (fun _ => [true]) hvB
    (fun i regs h => by
      obtain ⟨rfl, hi⟩ := h
      exact ⟨rfl, rfl, by simp, bounded4 (by omega) (by omega) (by omega) (by omega)⟩)
    (fun i hi regs h => by
      obtain ⟨rfl, -⟩ := h
      exact ⟨[a, b, i, v], ReachesOut.emit (show (unaryProgram e).instr 8 = _ from rfl)
        (bounded4 (by omega) (by omega) (by omega) (by omega)) (ReachesOut.refl _), rfl,
        bounded4 (by omega) (by omega) (by omega) (by omega), by simpa using hi⟩)
    [a, b, 0, v] (bounded4 (by omega) (by omega) (by omega) (by omega)) (by simp)
  obtain ⟨rfl, -⟩ := hinv
  exact ⟨_, (hhead.trans hset).trans hloop, bounded4 (by omega) (by omega) (by omega) (by omega)⟩

private theorem flatMap_range_true (n : ℕ) :
    (List.range n).flatMap (fun _ => [true]) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; rfl

/-- The binary digits of `v`, least significant first, are its bits below its size. -/
private theorem bits_eq_map_testBit (v : ℕ) : v.bits = (List.range v.size).map v.testBit := by
  refine List.ext_getElem (by simp [Nat.size_eq_bits_len]) fun i h _ => ?_
  simp [Nat.testBit_eq_inth, List.getI_eq_getElem _ h]

private theorem two_pow_size_le (v : ℕ) : 2 ^ v.size ≤ 2 * v + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · obtain ⟨s, hs⟩ : ∃ s, v.size = s + 1 := ⟨v.size - 1, by have := Nat.size_pos.mpr hv; omega⟩
    have : 2 ^ s ≤ v := Nat.lt_size.mp (by omega)
    rw [hs, pow_succ]
    omega

/-- The loop of `binaryProgram`, from the power `2 ^ i`, emits the bits of `v` from index `i` on
below its size. -/
private theorem reachesOut_binaryLoop (e : Expr) {v : ℕ} (hB : 2 * a + 1 + b ≤ B)
    (hvB : 2 * v + 1 ≤ B) :
    ∀ i ≤ v.size, (binaryProgram e).ReachesOut (encPair encUnary encUnary (a, b))
      ((binaryProgram e).Active B) (6, [a, b, 2 ^ i, v]) (11, [a, b, 2 ^ v.size, v])
      ((List.range' i (v.size - i)).map v.testBit) := by
  have hsize := two_pow_size_le v
  intro i hi
  induction h : v.size - i generalizing i with
  | zero =>
    obtain rfl : i = v.size := by omega
    refine ReachesOut.lt (show (binaryProgram e).instr 6 = _ from rfl)
      (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ, Nat.lt_size_self, ↓reduceIte,
      List.range'_zero, List.map_nil]
    exact ReachesOut.refl _
  | succ n ih =>
    have hpow : 2 ^ i ≤ v := Nat.lt_size.mp (by omega)
    have hpow' : 2 ^ (i + 1) ≤ 2 ^ v.size := Nat.pow_le_pow_right (by omega) (by omega)
    have hb := bounded4 (B := B) (a₀ := a) (a₁ := b) (a₂ := 2 ^ i) (a₃ := v) (by omega)
      (by omega) (by omega) (by omega)
    refine ReachesOut.lt (show (binaryProgram e).instr 6 = _ from rfl) hb ?_
    simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ, show ¬v < 2 ^ i by omega,
      ↓reduceIte]
    refine ReachesOut.lt (show (binaryProgram e).instr 7 = _ from rfl) hb ?_
    have hrest : (binaryProgram e).ReachesOut (encPair encUnary encUnary (a, b))
        ((binaryProgram e).Active B) (10, [a, b, 2 ^ i, v]) (11, [a, b, 2 ^ v.size, v])
        ((List.range' (i + 1) n).map v.testBit) := by
      refine ReachesOut.assign (show (binaryProgram e).instr 10 = _ from rfl) hb ?_
      have := ih (i + 1) (by omega) (by omega)
      simpa [pow_succ, Nat.mul_comm] using this
    rw [List.range'_succ, List.map_cons, Nat.testBit_eq_decide_div_mod_eq]
    simp only [eval_const, eval_mod, eval_div, eval_reg, List.getD_cons_zero, List.getD_cons_succ]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ i) with h2 | h2
    · simp only [h2, lt_irrefl, ↓reduceIte, zero_ne_one, decide_false]
      exact ReachesOut.emit (show (binaryProgram e).instr 9 = _ from rfl) hb hrest
    · simp only [h2, Nat.lt_one_iff, ↓reduceIte, decide_true]
      exact ReachesOut.emit (show (binaryProgram e).instr 8 = _ from rfl) hb hrest

private theorem reachesOut_binaryProgram (e : Expr) {v : ℕ} (hv : e.eval [a, b, 0, 0] = v)
    (hB : 2 * a + 1 + b ≤ B) (hvB : 2 * v + 1 ≤ B) :
    (binaryProgram e).ReachesOut (encPair encUnary encUnary (a, b))
      ((binaryProgram e).Active B) (binaryProgram e).init (11, [a, b, 2 ^ v.size, v]) v.bits := by
  have hhead := reachesOut_header' (P := binaryProgram e)
    (codeAt_of_code_eq (pre := []) (post := _) rfl) hB
  have hset : (binaryProgram e).ReachesOut (encPair encUnary encUnary (a, b))
      ((binaryProgram e).Active B) (4, [a, b, 0, 0]) (6, [a, b, 2 ^ 0, v]) [] := by
    refine ReachesOut.assign (show (binaryProgram e).instr 4 = _ from rfl)
      (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
    refine ReachesOut.assign (show (binaryProgram e).instr 5 = _ from rfl)
      (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
    simpa [hv] using ReachesOut.refl _
  have hloop := reachesOut_binaryLoop e hB hvB 0 (Nat.zero_le _)
  rw [Nat.sub_zero, ← List.range_eq_range', ← bits_eq_map_testBit] at hloop
  exact ((hhead.trans hset).trans hloop).of_eq (by simp)

end Runs

/-- A bound `X ≤ (n + 1) ^ d` on an input of length `n ≥ 1` leaves room for `n + 1` and `2X + 1`
below `(n + 1) ^ (d + 2)`. -/
private theorem le_pow_add_two {n X d : ℕ} (hn : 1 ≤ n) (hX : X ≤ (n + 1) ^ d) :
    n + 1 ≤ (n + 1) ^ (d + 2) ∧ 2 * X + 1 ≤ (n + 1) ^ (d + 2) := by
  have h1 : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have h4 : 4 ≤ (n + 1) * (n + 1) :=
    Nat.mul_le_mul (show 2 ≤ n + 1 by omega) (show 2 ≤ n + 1 by omega)
  rw [pow_add, pow_two]
  constructor
  · calc n + 1 ≤ 1 * (n + 1) * 1 := by omega
      _ ≤ (n + 1) ^ d * ((n + 1) * (n + 1)) := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul h1 (Nat.mul_le_mul le_rfl (by omega))
  · calc 2 * X + 1 ≤ (n + 1) ^ d * 4 := by omega
      _ ≤ (n + 1) ^ d * ((n + 1) * (n + 1)) := Nat.mul_le_mul le_rfl h4

/-! ### Logarithmic space -/

variable {F F₁ F₂ : ℕ → ℕ → ℕ}

/-- **A polynomially bounded function of two unary numbers given by an expression, with unary
output, is computable in logarithmic space.** The expression `e` is evaluated with `a` in
register `0`, `b` in register `1`, and the other registers zero. -/
theorem computableInLogSpace_unary (e : Expr) (d : ℕ) (he : ∀ a b, e.eval [a, b, 0, 0] = F a b)
    (hF : ∀ a b, F a b ≤ (a + b + 1) ^ d) :
    ComputableInLogSpace (fun p : ℕ × ℕ => F p.1 p.2) (encPair encUnary encUnary) encUnary := by
  refine (unaryProgram e).computableInLogSpace_of_reachesOut (d + 2) fun ⟨a, b⟩ => ?_
  rw [length_input]
  obtain ⟨h₁, h₂⟩ := le_pow_add_two (n := 2 * a + 1 + b) (by omega)
    ((hF a b).trans (Nat.pow_le_pow_left (by omega) d))
  obtain ⟨regs, h, hregs⟩ := reachesOut_unaryProgram (B := (2 * a + 1 + b + 1) ^ (d + 2)) e
    (he a b) (by omega) (by omega)
  exact ⟨(9, regs), _, [], h, rfl, by rw [flatMap_range_true, List.append_nil]; rfl, hregs⟩

/-- **A polynomially bounded function of two unary numbers given by an expression, with binary
output, is computable in logarithmic space.** The expression `e` is evaluated with `a` in
register `0`, `b` in register `1`, and the other registers zero. -/
theorem computableInLogSpace_binary (e : Expr) (d : ℕ) (he : ∀ a b, e.eval [a, b, 0, 0] = F a b)
    (hF : ∀ a b, F a b ≤ (a + b + 1) ^ d) :
    ComputableInLogSpace (fun p : ℕ × ℕ => F p.1 p.2) (encPair encUnary encUnary) encNat := by
  refine (binaryProgram e).computableInLogSpace_of_reachesOut (d + 2) fun ⟨a, b⟩ => ?_
  rw [length_input]
  obtain ⟨h₁, h₂⟩ := le_pow_add_two (n := 2 * a + 1 + b) (by omega)
    ((hF a b).trans (Nat.pow_le_pow_left (by omega) d))
  have hsize := two_pow_size_le (F a b)
  refine ⟨_, _, [], reachesOut_binaryProgram e (he a b) (by omega) h₂, rfl,
    by simp [encNat_apply], bounded4 (by omega) (by omega) (by omega) (by omega)⟩

/-- **Comparing two functions of two unary numbers given by expressions is computable in
logarithmic space.** No bound is needed: the values are compared, not stored. -/
theorem computableInLogSpace_lt (e₁ e₂ : Expr) (h₁ : ∀ a b, e₁.eval [a, b, 0, 0] = F₁ a b)
    (h₂ : ∀ a b, e₂.eval [a, b, 0, 0] = F₂ a b) :
    ComputableInLogSpace (fun p : ℕ × ℕ => decide (F₁ p.1 p.2 < F₂ p.1 p.2))
      (encPair encUnary encUnary) encBool := by
  refine (ltProgram e₁ e₂).computableInLogSpace_of_reachesOut 1 fun ⟨a, b⟩ => ?_
  rw [length_input, pow_one]
  have hhead := reachesOut_header' (P := ltProgram e₁ e₂)
    (codeAt_of_code_eq (pre := []) (post := _) rfl)
    (show 2 * a + 1 + b ≤ 2 * a + 1 + b + 1 by omega)
  have hb := bounded4 (B := 2 * a + 1 + b + 1) (a₀ := a) (a₁ := b) (a₂ := 0) (a₃ := 0) (by omega)
    (by omega) (by omega) (by omega)
  by_cases h : F₁ a b < F₂ a b
  · refine ⟨(5, [a, b, 0, 0]), [] ++ [], [true],
      hhead.trans (ReachesOut.lt (show (ltProgram e₁ e₂).instr 4 = _ from rfl) hb ?_), rfl,
      by simp [h], hb⟩
    simp only [h₁, h₂, h, ↓reduceIte]
    exact ReachesOut.refl _
  · refine ⟨(6, [a, b, 0, 0]), [] ++ [], [false],
      hhead.trans (ReachesOut.lt (show (ltProgram e₁ e₂).instr 4 = _ from rfl) hb ?_), rfl,
      by simp [h], hb⟩
    simp only [h₁, h₂, h, ↓reduceIte]
    exact ReachesOut.refl _

end Turing.CounterProgram.Unary

namespace Turing.MultiTapeTM.ComputableInLogSpace

open CounterProgram CounterProgram.Unary CounterProgram.Expr

variable {γ : Type} {encIn : γ ↪ List Bool} {f₁ f₂ : γ → ℕ}

/-! ### Instances -/

/-- **Multiplying unary numbers** computed in logarithmic space from a common input. -/
@[fun_prop]
theorem unaryMul (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => f₁ a * f₂ a) encIn encUnary :=
  (computableInLogSpace_unary (F := (· * ·)) (mul (reg 0) (reg 1)) 2 (fun _ _ => rfl)
    fun a b => by nlinarith).comp' (pair h₁ h₂)

/-- **Truncated subtraction of unary numbers** computed in logarithmic space from a common
input. -/
@[fun_prop]
theorem unarySub (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => f₁ a - f₂ a) encIn encUnary :=
  (computableInLogSpace_unary (F := (· - ·)) (sub (reg 0) (reg 1)) 1 (fun _ _ => rfl)
    fun a b => by simp; omega).comp' (pair h₁ h₂)

/-- **The quotient of unary numbers** computed in logarithmic space from a common input. -/
@[fun_prop]
theorem unaryDiv (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => f₁ a / f₂ a) encIn encUnary :=
  (computableInLogSpace_unary (F := (· / ·)) (div (reg 0) (reg 1)) 1 (fun _ _ => rfl)
    fun a b => by simp only [pow_one]; have := Nat.div_le_self a b; omega).comp' (pair h₁ h₂)

/-- **The remainder of unary numbers** computed in logarithmic space from a common input. -/
@[fun_prop]
theorem unaryMod (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => f₁ a % f₂ a) encIn encUnary :=
  (computableInLogSpace_unary (F := (· % ·)) (mod (reg 0) (reg 1)) 1 (fun _ _ => rfl)
    fun a b => by simp only [pow_one]; have := Nat.mod_le a b; omega).comp' (pair h₁ h₂)

/-- **The minimum of unary numbers** computed in logarithmic space from a common input. -/
@[fun_prop]
theorem unaryMin (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => min (f₁ a) (f₂ a)) encIn encUnary :=
  (computableInLogSpace_unary (F := min) (sub (reg 0) (sub (reg 0) (reg 1))) 1
    (fun _ _ => by simp; omega) fun a b => by simp; omega).comp' (pair h₁ h₂)

/-- **The maximum of unary numbers** computed in logarithmic space from a common input. -/
@[fun_prop]
theorem unaryMax (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => max (f₁ a) (f₂ a)) encIn encUnary :=
  (computableInLogSpace_unary (F := max) (add (reg 0) (sub (reg 1) (reg 0))) 1
    (fun _ _ => by simp; omega) fun a b => by simp; omega).comp' (pair h₁ h₂)

/-- **Comparing unary numbers with `<`**, computed in logarithmic space from a common input. -/
@[fun_prop]
theorem unaryLt (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => decide (f₁ a < f₂ a)) encIn encBool :=
  (computableInLogSpace_lt (F₁ := fun a _ => a) (F₂ := fun _ b => b) (reg 0) (reg 1)
    (fun _ _ => rfl) (fun _ _ => rfl)).comp' (pair h₁ h₂)

/-- **Comparing unary numbers with `≤`**, computed in logarithmic space from a common input. -/
@[fun_prop]
theorem unaryLe (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => decide (f₁ a ≤ f₂ a)) encIn encBool :=
  ((computableInLogSpace_lt (F₁ := fun a _ => a) (F₂ := fun _ b => b + 1) (reg 0)
    (add (reg 1) (Expr.const 1)) (fun _ _ => rfl) (fun _ _ => rfl)).comp' (pair h₁ h₂)).congr_fun
    fun a => by simp

/-- **Testing unary numbers for equality**, computed in logarithmic space from a common input. -/
@[fun_prop]
theorem unaryEq (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => decide (f₁ a = f₂ a)) encIn encBool :=
  ((computableInLogSpace_lt (F₁ := fun a b => a - b + (b - a)) (F₂ := fun _ _ => 1)
    (add (sub (reg 0) (reg 1)) (sub (reg 1) (reg 0))) (Expr.const 1) (fun _ _ => rfl)
    (fun _ _ => rfl)).comp' (pair h₁ h₂)).congr_fun fun a => by
    simp only [decide_eq_decide]
    omega

/-- **Converting a unary number to binary**, computed in logarithmic space. It changes only the
output encoding, so it is not registered with `fun_prop`. -/
theorem unaryToBinary {f : γ → ℕ} (hf : ComputableInLogSpace f encIn encUnary) :
    ComputableInLogSpace f encIn encNat :=
  (computableInLogSpace_binary (F := fun a _ => a) (reg 0) 1 (fun _ _ => rfl)
    fun a b => by simp only [pow_one]; omega).comp' (pair hf (ComputableInLogSpace.const 0))

end Turing.MultiTapeTM.ComputableInLogSpace
