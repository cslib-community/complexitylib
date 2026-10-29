/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# Word and list operations with counters, in logarithmic space

Counter programs (`Turing.CounterProgram`) for operations that need a counter of logarithmic
length, so that they are not finite-state transductions:

* the first `k` bits of a word, and the word without its first `k` bits, with `k` in unary after
  the framed word (`shiftProgram`);
* the list `0, …, n - 1` of a unary `n` (`rangeProgram`), with a nested counting loop;
* the element at a unary index of a list (`lookupProgram`), skipping framed elements with a
  position counter guarded by the length of the list encoding.

Each program reads the length `n` of the framed first component and the unary second component
into registers (`headerCode`), and keeps its registers below the input length, so it computes its
function in logarithmic space by `Turing.CounterProgram.computableInLogSpace_of_reachesOut`.
None of this uses logarithmic-space composition, apart from the `fun_prop` forms at the end.
The rules of `LogSpace/Words` are imported publicly, so that `fun_prop` has the full rule set.

## Main definitions

* `Turing.CounterProgram.Words.shiftProgram`: emitting a shifted segment of a framed word.
* `Turing.CounterProgram.Words.rangeProgram`: enumerating `0, …, n - 1`.
* `Turing.CounterProgram.Words.lookupProgram`: list lookup at a unary index.

## Main results

* `Turing.CounterProgram.Words.reachesOut_header`: the run of the header, for programs built on
  it.
* `Turing.MultiTapeTM.ComputableInLogSpace.bitsTake`,
  `Turing.MultiTapeTM.ComputableInLogSpace.bitsDrop`: taking and dropping bits.
* `Turing.MultiTapeTM.ComputableInLogSpace.range`: the list `0, …, n - 1`.
* `Turing.MultiTapeTM.ComputableInLogSpace.getElem?`: list lookup at a unary index.
* `Turing.MultiTapeTM.ComputableInLogSpace.bitsTake'`, `.bitsDrop'`, `.getElem?'`: the same on
  computed arguments, in the form used by `fun_prop`, with which `range` is also registered.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

namespace Turing.CounterProgram.Words

open Instr Expr MultiTapeTM

/-! ### The input `frame w ++ replicate k true` -/

section Input

variable (w : List Bool) (k : ℕ)

private theorem encPair_bits_unary :
    encPair encBits encUnary (w, k) = frame w ++ List.replicate k true :=
  rfl

private theorem length_input :
    (frame w ++ List.replicate k true).length = 2 * w.length + 1 + k := by
  simp [length_frame]

private theorem input_marker {i : ℕ} (hi : i < w.length) :
    (frame w ++ List.replicate k true)[2 * i]? = some true := by
  rw [List.getElem?_append_left (by rw [length_frame]; omega), getElem?_frame_two_mul hi]

private theorem input_end : (frame w ++ List.replicate k true)[2 * w.length]? = some false := by
  rw [List.getElem?_append_left (by rw [length_frame]; omega), getElem?_frame_two_mul_length]

private theorem input_bit {i : ℕ} (hi : i < w.length) :
    (frame w ++ List.replicate k true)[2 * i + 1]? = w[i]? := by
  rw [List.getElem?_append_left (by rw [length_frame]; omega), getElem?_frame_two_mul_add_one hi]

private theorem input_unary {j : ℕ} (hj : j < k) :
    (frame w ++ List.replicate k true)[2 * w.length + 1 + j]? = some true := by
  rw [List.getElem?_append_right (by rw [length_frame]; omega)]
  simp [length_frame, hj]

private theorem input_after :
    (frame w ++ List.replicate k true)[2 * w.length + 1 + k]? = none := by
  rw [List.getElem?_eq_none]
  rw [length_input]

end Input

/-- Emitting the defined entries of `v` at the indices below `N` gives the first `N` entries. -/
private theorem flatMap_range_getElem?_toList (v : List Bool) (N : ℕ) :
    (List.range N).flatMap (fun i => v[i]?.toList) = v.take N := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.flatMap_append, ih, List.take_add_one]; simp

private theorem bounded4 {B a₀ a₁ a₂ a₃ : ℕ} (h₀ : a₀ ≤ B) (h₁ : a₁ ≤ B) (h₂ : a₂ ≤ B)
    (h₃ : a₃ ≤ B) : ∀ x ∈ [a₀, a₁, a₂, a₃], x ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-! ### Reading the header: the length of the framed word and the unary count -/

/-- The header code: label `0` and `1` count the framed word into register `0`, labels `2` and `3`
count the unary tail into register `1`; it exits at label `4`. -/
def headerCode : List Instr :=
  [read (mul (const 2) (reg 0)) 1 2 2,
   assign 0 (add (reg 0) (const 1)) 0,
   read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 3 4 4,
   assign 1 (add (reg 1) (const 1)) 2]

variable {P : CounterProgram} {w : List Bool} {k B : ℕ}

/-- **The run of `headerCode`**: from the initial registers it stores the length of the framed
word in register `0` and the unary count in register `1`, and exits at label `4`, without
emitting. -/
theorem reachesOut_header (hP : P.CodeAt 0 headerCode)
    (hB : 2 * w.length + 1 + k ≤ B) :
    P.ReachesOut (frame w ++ List.replicate k true) (P.Active B) (0, [0, 0, 0, 0])
      (4, [w.length, k, 0, 0]) [] := by
  simp only [headerCode, codeAt_cons] at hP
  obtain ⟨h₀, h₁, h₂, h₃, -⟩ := hP
  have scanN : ∀ j ≤ w.length, P.ReachesOut (frame w ++ List.replicate k true) (P.Active B)
      (0, [j, 0, 0, 0]) (2, [w.length, 0, 0, 0]) [] := by
    intro j hj
    induction h : w.length - j generalizing j with
    | zero =>
      obtain rfl : j = w.length := by omega
      refine ReachesOut.read h₀ (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
      simp only [eval_mul, eval_const, eval_reg, List.getD_cons_zero, input_end, readLabel]
      exact ReachesOut.refl _
    | succ _ ih =>
      refine ReachesOut.read h₀ (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
      simp only [eval_mul, eval_const, eval_reg, List.getD_cons_zero,
        input_marker w k (show j < w.length by omega), readLabel]
      refine ReachesOut.assign (by simpa using h₁) (bounded4 (by omega) (by omega) (by omega)
        (by omega)) ?_
      simpa using ih (j + 1) (by omega) (by omega)
  have scanK : ∀ j ≤ k, P.ReachesOut (frame w ++ List.replicate k true) (P.Active B)
      (2, [w.length, j, 0, 0]) (4, [w.length, k, 0, 0]) [] := by
    intro j hj
    induction h : k - j generalizing j with
    | zero =>
      obtain rfl : j = k := by omega
      refine ReachesOut.read (by simpa using h₂) (bounded4 (by omega) (by omega) (by omega)
        (by omega)) ?_
      simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
        List.getD_cons_succ, input_after, readLabel]
      exact ReachesOut.refl _
    | succ _ ih =>
      refine ReachesOut.read (by simpa using h₂) (bounded4 (by omega) (by omega) (by omega)
        (by omega)) ?_
      simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
        List.getD_cons_succ, input_unary w k (show j < k by omega), readLabel]
      refine ReachesOut.assign (by simpa using h₃) (bounded4 (by omega) (by omega) (by omega)
        (by omega)) ?_
      simpa using ih (j + 1) (by omega) (by omega)
  exact (scanN 0 (Nat.zero_le _)).trans (scanK 0 (Nat.zero_le _))

/-! ### Emitting bits of the framed word -/

/-- The body emitting the bit at index `reg 2 + reg 3 · reg 1`, if any, then continuing at `7`.
With `reg 3 = 0` this is the bit at the loop index; with `reg 3 = 1` it is offset by `k`. -/
def emitCode : List Instr :=
  [lt (add (reg 2) (mul (reg 3) (reg 1))) (reg 0) 9 7,
   read (add (mul (const 2) (add (reg 2) (mul (reg 3) (reg 1)))) (const 1)) 10 11 7,
   emit true 7,
   emit false 7]

/-- A program emitting `w[i + o·k]` for `i` below the bound of its loop, where `o ∈ {0, 1}` is
the initial value of register `3`, set by the instruction at label `4`. -/
def shiftProgram (o : ℕ) (bound : Expr) : CounterProgram where
  code := headerCode ++ [assign 3 (const o) 5] ++ forCode 5 2 bound 8 12 ++ emitCode ++
    [halt []]
  registers := 4

private theorem codeAt_header (o : ℕ) (bound : Expr) : (shiftProgram o bound).CodeAt 0 headerCode :=
  codeAt_of_code_eq (pre := [])
    (post := [assign 3 (const o) 5] ++ forCode 5 2 bound 8 12 ++ emitCode ++ [halt []])
    (by simp [shiftProgram])

private theorem reachesOut_emit {o : ℕ} {bound : Expr} {i : ℕ} (hB : 2 * w.length + 1 + k ≤ B)
    (hi : i ≤ B) (ho : o ≤ 1) :
    (shiftProgram o bound).ReachesOut (frame w ++ List.replicate k true)
      ((shiftProgram o bound).Active B) (8, [w.length, k, i, o]) (7, [w.length, k, i, o])
      w[i + o * k]?.toList := by
  have hb : ∀ r ∈ [w.length, k, i, o], r ≤ B := bounded4 (by omega) (by omega) hi (by omega)
  refine ReachesOut.lt (show (shiftProgram o bound).instr 8 = _ from rfl) hb ?_
  simp only [eval_add, eval_mul, eval_reg, List.getD_cons_zero, List.getD_cons_succ]
  by_cases hlt : i + o * k < w.length
  · simp only [hlt, ↓reduceIte]
    refine ReachesOut.read (show (shiftProgram o bound).instr 9 = _ from rfl) hb ?_
    simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
      List.getD_cons_succ, input_bit w k hlt, List.getElem?_eq_getElem hlt, Option.toList_some]
    cases w[i + o * k]
    · exact ReachesOut.emit (show (shiftProgram o bound).instr 11 = _ from rfl) hb
        (ReachesOut.refl _)
    · exact ReachesOut.emit (show (shiftProgram o bound).instr 10 = _ from rfl) hb
        (ReachesOut.refl _)
  · simp only [hlt, ↓reduceIte]
    rw [List.getElem?_eq_none (by omega)]
    exact ReachesOut.refl _

/-- **The run of `shiftProgram`**: it emits `w[i + o·k]` for `i` below the value `N` of its loop
bound, and halts. -/
private theorem reachesOut_shiftProgram {o N : ℕ} {bound : Expr} (ho : o ≤ 1)
    (hbound : ∀ i, bound.eval [w.length, k, i, o] = N) (hN : N ≤ 2 * w.length + 1 + k)
    (hB : 2 * w.length + 1 + k ≤ B) :
    ∃ regs, (shiftProgram o bound).ReachesOut (frame w ++ List.replicate k true)
      ((shiftProgram o bound).Active B) (shiftProgram o bound).init (12, regs)
      ((List.range N).flatMap fun i => w[i + o * k]?.toList) ∧ ∀ r ∈ regs, r ≤ B := by
  have hfor : (shiftProgram o bound).CodeAt 5 (forCode 5 2 bound 8 12) := by
    have h := codeAt_of_code_eq (P := shiftProgram o bound)
      (pre := headerCode ++ [assign 3 (const o) 5]) (post := emitCode ++ [halt []])
      (l := forCode 5 2 bound 8 12) (by simp [shiftProgram])
    simpa [headerCode] using h
  have hhead := reachesOut_header (codeAt_header o bound) hB (P := shiftProgram o bound)
  have hset : (shiftProgram o bound).ReachesOut (frame w ++ List.replicate k true)
      ((shiftProgram o bound).Active B) (4, [w.length, k, 0, 0]) (5, [w.length, k, 0, o]) [] :=
    ReachesOut.assign (show (shiftProgram o bound).instr 4 = _ from rfl)
      (bounded4 (by omega) (by omega) (by omega) (by omega)) (by simpa using ReachesOut.refl _)
  obtain ⟨regs, hloop, hinv⟩ := reachesOut_forCode (w := frame w ++ List.replicate k true)
    hfor (fun i regs => regs = [w.length, k, i, o] ∧ i ≤ N) (fun i => w[i + o * k]?.toList)
    (show N ≤ B by omega)
    (fun i regs h => by
      obtain ⟨rfl, hi⟩ := h
      exact ⟨rfl, hbound i, by simp, bounded4 (by omega) (by omega) (by omega) (by omega)⟩)
    (fun i hi regs h => by
      obtain ⟨rfl, -⟩ := h
      exact ⟨[w.length, k, i, o], reachesOut_emit hB (by omega) ho, rfl,
        bounded4 (by omega) (by omega) (by omega) (by omega), by simpa using hi⟩)
    [w.length, k, 0, o] (bounded4 (by omega) (by omega) (by omega) (by omega)) (by simp)
  obtain ⟨rfl, -⟩ := hinv
  exact ⟨_, (hhead.trans hset).trans hloop, bounded4 (by omega) (by omega) (by omega) (by omega)⟩

/-- A function whose encoded value is emitted by `shiftProgram` is computable in logarithmic
space. -/
private theorem computableInLogSpace_shiftProgram {α : Type} {f : List Bool × ℕ → α}
    {encOut : α ↪ List Bool} {o : ℕ} (ho : o ≤ 1) {bound : Expr} (N : List Bool → ℕ → ℕ)
    (hbound : ∀ w k i, bound.eval [w.length, k, i, o] = N w k)
    (hN : ∀ w k, N w k ≤ 2 * w.length + 1 + k)
    (hf : ∀ w k, encOut (f (w, k)) = (List.range (N w k)).flatMap fun i => w[i + o * k]?.toList) :
    ComputableInLogSpace f (encPair encBits encUnary) encOut := by
  refine (shiftProgram o bound).computableInLogSpace_of_reachesOut 1 fun ⟨w, k⟩ => ?_
  rw [encPair_bits_unary, length_input, pow_one]
  obtain ⟨regs, h, hregs⟩ := reachesOut_shiftProgram (w := w) (k := k)
    (B := 2 * w.length + 1 + k + 1) ho (hbound w k) (hN w k) (by omega)
  exact ⟨(12, regs), _, [], h, rfl, by rw [hf, List.append_nil], hregs⟩

end Turing.CounterProgram.Words

namespace Turing.CounterProgram.Words

open Instr Expr MultiTapeTM

/-! ### Enumerating `0, …, n - 1` -/

/-- The program enumerating `0, …, n - 1` in unary, as a list: labels `0` and `1` count the
unary input into register `0`; the loop at `2` runs register `1` over the elements, and the inner
loop at `5` writes the framed unary digits of each element with register `2`. -/
def rangeProgram : CounterProgram where
  code :=
    [read (reg 0) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0] ++
    forCode 2 1 (reg 0) 5 11 ++ forCode 5 2 (reg 1) 8 10 ++
    [emit true 9, emit true 7, emit false 4, halt []]
  registers := 4

/-- The bits written for the element `i`: its unary digits, framed. -/
private theorem frame_replicate (i : ℕ) :
    frame (List.replicate i true) = (List.range i).flatMap (fun _ => [true, true]) ++ [false] := by
  simp only [frame, List.flatMap_replicate]
  congr 1
  induction i with
  | zero => rfl
  | succ i ih => rw [List.replicate_succ', List.flatten_append, List.range_succ,
      List.flatMap_append, ih]; simp

private theorem reachesOut_rangeProgram (n : ℕ) :
    ∃ regs, rangeProgram.ReachesOut (List.replicate n true) (rangeProgram.Active (n + 1))
      rangeProgram.init (11, regs)
      ((List.range n).flatMap fun i => (List.range i).flatMap (fun _ => [true, true]) ++ [false]) ∧
      ∀ r ∈ regs, r ≤ n + 1 := by
  set B := n + 1
  have hscan : ∀ j ≤ n, rangeProgram.ReachesOut (List.replicate n true) (rangeProgram.Active B)
      (0, [j, 0, 0, 0]) (2, [n, 0, 0, 0]) [] := by
    intro j hj
    induction h : n - j generalizing j with
    | zero =>
      obtain rfl : j = n := by omega
      refine ReachesOut.read (show rangeProgram.instr 0 = _ from rfl)
        (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
      simp only [eval_reg, List.getD_cons_zero, List.getElem?_replicate, lt_irrefl,
        ↓reduceIte, readLabel]
      exact ReachesOut.refl _
    | succ _ ih =>
      refine ReachesOut.read (show rangeProgram.instr 0 = _ from rfl)
        (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
      simp only [eval_reg, List.getD_cons_zero, List.getElem?_replicate,
        show j < n by omega, ↓reduceIte, readLabel]
      refine ReachesOut.assign (show rangeProgram.instr 1 = _ from rfl)
        (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
      simpa using ih (j + 1) (by omega) (by omega)
  have hout : rangeProgram.CodeAt 2 (forCode 2 1 (reg 0) 5 11) := by
    have h := codeAt_of_code_eq (P := rangeProgram) (l := forCode 2 1 (reg 0) 5 11)
      (pre := [read (reg 0) 1 2 2, assign 0 (add (reg 0) (const 1)) 0])
      (post := forCode 5 2 (reg 1) 8 10 ++ [emit true 9, emit true 7, emit false 4, halt []])
      (by simp [rangeProgram])
    simpa using h
  have hin : rangeProgram.CodeAt 5 (forCode 5 2 (reg 1) 8 10) := by
    have h := codeAt_of_code_eq (P := rangeProgram) (l := forCode 5 2 (reg 1) 8 10)
      (pre := [read (reg 0) 1 2 2, assign 0 (add (reg 0) (const 1)) 0] ++
        forCode 2 1 (reg 0) 5 11)
      (post := [emit true 9, emit true 7, emit false 4, halt []])
      (by simp [rangeProgram])
    simpa [forCode] using h
  obtain ⟨regs, hloop, hinv⟩ := reachesOut_forCode (w := List.replicate n true) (B := B) hout
    (N := n)
    (fun i regs => ∃ m, regs = [n, i, m, 0] ∧ i ≤ n ∧ m ≤ n)
    (fun i => (List.range i).flatMap (fun _ => [true, true]) ++ [false]) (by omega)
    (fun i regs h => by
      obtain ⟨m, rfl, hi, hm⟩ := h
      exact ⟨rfl, rfl, by simp, bounded4 (by omega) (by omega) (by omega) (by omega)⟩)
    (fun i hi regs h => by
      obtain ⟨m, rfl, -, hm⟩ := h
      obtain ⟨regs', hinner, hinv'⟩ := reachesOut_forCode (w := List.replicate n true) (B := B) hin
        (N := i)
        (fun j regs => regs = [n, i, j, 0] ∧ j ≤ i) (fun _ => [true, true]) (by omega)
        (fun j regs h => by
          obtain ⟨rfl, hj⟩ := h
          exact ⟨rfl, rfl, by simp, bounded4 (by omega) (by omega) (by omega) (by omega)⟩)
        (fun j hj regs h => by
          obtain ⟨rfl, -⟩ := h
          refine ⟨[n, i, j, 0], ?_, rfl, bounded4 (by omega) (by omega) (by omega) (by omega),
            by simpa using hj⟩
          exact ReachesOut.emit (show rangeProgram.instr 8 = _ from rfl)
            (bounded4 (by omega) (by omega) (by omega) (by omega))
            (ReachesOut.emit (show rangeProgram.instr 9 = _ from rfl)
              (bounded4 (by omega) (by omega) (by omega) (by omega)) (ReachesOut.refl _)))
        [n, i, m, 0] (bounded4 (by omega) (by omega) (by omega) (by omega)) (by simp)
      obtain ⟨rfl, -⟩ := hinv'
      refine ⟨[n, i, i, 0], hinner.trans ?_, rfl,
        bounded4 (by omega) (by omega) (by omega) (by omega), ⟨i, by simp, by omega, by omega⟩⟩
      exact ReachesOut.emit (show rangeProgram.instr 10 = _ from rfl)
        (bounded4 (by omega) (by omega) (by omega) (by omega)) (ReachesOut.refl _))
    [n, 0, 0, 0] (bounded4 (by omega) (by omega) (by omega) (by omega)) ⟨0, by simp, by omega,
      by omega⟩
  obtain ⟨m, rfl, -, hm⟩ := hinv
  exact ⟨_, (hscan 0 (Nat.zero_le _)).trans hloop,
    bounded4 (by omega) (by omega) (by omega) (by omega)⟩

end Turing.CounterProgram.Words

namespace Turing.CounterProgram.Words

open Instr Expr MultiTapeTM

/-! ### Looking up an element of a list -/

section Offsets

variable {α : Type} (enc : α ↪ List Bool)

private theorem encList_eq (l : List α) : encList enc l = l.flatMap (frame ∘ enc) := rfl

/-- The offset of the `t`-th element in a list encoding. -/
private def off (l : List α) (t : ℕ) : ℕ := (encList enc (l.take t)).length

private theorem encList_split (l : List α) {t : ℕ} (ht : t < l.length) :
    encList enc l =
      encList enc (l.take t) ++ (frame (enc l[t]) ++ encList enc (l.drop (t + 1))) := by
  simp only [encList_eq]
  conv_lhs => rw [← List.take_append_drop t l, List.drop_eq_getElem_cons ht]
  rw [List.flatMap_append, List.flatMap_cons]
  rfl

private theorem off_succ (l : List α) {t : ℕ} (ht : t < l.length) :
    off enc l (t + 1) = off enc l t + (2 * (enc l[t]).length + 1) := by
  simp only [off, encList_eq, List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    Function.comp_apply, length_frame]

private theorem off_of_le (l : List α) {t : ℕ} (ht : l.length ≤ t) :
    off enc l t = (encList enc l).length := by
  simp only [off, List.take_of_length_le ht]

private theorem off_le (l : List α) (t : ℕ) : off enc l t ≤ (encList enc l).length := by
  simp only [off, encList_eq]
  conv_rhs => rw [← List.take_append_drop t l]
  rw [List.flatMap_append, List.length_append]
  omega

private theorem getElem?_marker (l : List α) {t j : ℕ} (ht : t < l.length)
    (hj : j < (enc l[t]).length) :
    (encList enc l)[off enc l t + 2 * j]? = some true := by
  rw [encList_split enc l ht, List.getElem?_append_right (by simp [off]),
    List.getElem?_append_left (by simp [off, length_frame]; omega)]
  simpa [off] using getElem?_frame_two_mul hj

private theorem getElem?_end (l : List α) {t : ℕ} (ht : t < l.length) :
    (encList enc l)[off enc l t + 2 * (enc l[t]).length]? = some false := by
  rw [encList_split enc l ht, List.getElem?_append_right (by simp [off]),
    List.getElem?_append_left (by simp [off, length_frame])]
  simpa [off] using getElem?_frame_two_mul_length (enc l[t])

private theorem getElem?_bit (l : List α) {t j : ℕ} (ht : t < l.length)
    (hj : j < (enc l[t]).length) :
    (encList enc l)[off enc l t + 2 * j + 1]? = (enc l[t])[j]? := by
  rw [encList_split enc l ht, List.getElem?_append_right (by simp [off]; omega),
    List.getElem?_append_left (by simp [off, length_frame]; omega)]
  have := getElem?_frame_two_mul_add_one hj
  simpa [off, Nat.add_assoc] using this

end Offsets

/-- The program looking up the element at a unary index in a list: the header reads the length
`n` of the list encoding and the index `k`; the loop at `4` skips `k` framed elements with
register `2` as the position, guarded by `reg 2 < n`; if an element remains, the code at `11`
writes `true` and copies the element's digits. -/
def lookupProgram : CounterProgram where
  code := headerCode ++ forCode 4 3 (reg 1) 7 11 ++
    [lt (reg 2) (reg 0) 8 6,
     read (add (mul (const 2) (reg 2)) (const 1)) 9 10 6,
     assign 2 (add (reg 2) (const 2)) 7,
     assign 2 (add (reg 2) (const 1)) 6,
     lt (reg 2) (reg 0) 12 19,
     emit true 13,
     read (add (mul (const 2) (reg 2)) (const 1)) 14 18 18,
     read (add (mul (const 2) (reg 2)) (const 3)) 15 16 18,
     emit true 17,
     emit false 17,
     assign 2 (add (reg 2) (const 2)) 13,
     halt [],
     halt []]
  registers := 4

section Lookup

variable {α : Type} {enc : α ↪ List Bool} (l : List α) (k : ℕ)

local notation "W" => encList enc l
local notation "X" => frame (encList enc l) ++ List.replicate k true

private theorem read_W {p : ℕ} (hp : p < (encList enc l).length) :
    X[2 * p + 1]? = (encList enc l)[p]? := input_bit _ k hp

private theorem off_lt_length {t : ℕ} (ht : t < l.length) : off enc l t < (encList enc l).length :=
  lt_of_lt_of_le (by rw [off_succ enc l ht]; omega) (off_le enc l (t + 1))

variable {l k} {B : ℕ}

/-- Skipping the element at position `t`, or nothing past the end of the list. -/
private theorem reachesOut_skip (hB : 2 * (encList enc l).length + 1 + k ≤ B) {t : ℕ}
    (htk : t ≤ k) :
    lookupProgram.ReachesOut X (lookupProgram.Active B)
      (7, [(encList enc l).length, k, off enc l t, t])
      (6, [(encList enc l).length, k, off enc l (t + 1), t]) [] := by
  set n := (encList enc l).length
  by_cases ht : t < l.length
  · have hoff := off_succ enc l ht
    have hlt := off_lt_length (enc := enc) l ht
    have hle := off_le enc l (t + 1)
    have key : ∀ j ≤ (enc l[t]).length, lookupProgram.ReachesOut X (lookupProgram.Active B)
        (7, [n, k, off enc l t + 2 * j, t]) (6, [n, k, off enc l (t + 1), t]) [] := by
      intro j hj
      induction h : (enc l[t]).length - j generalizing j with
      | zero =>
        obtain rfl : j = (enc l[t]).length := by omega
        have hb := bounded4 (B := B) (a₀ := n) (a₁ := k) (a₂ := off enc l t + 2 * (enc l[t]).length)
          (a₃ := t) (by omega) (by omega) (by omega) (by omega)
        refine ReachesOut.lt (show lookupProgram.instr 7 = _ from rfl) hb ?_
        simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ,
          show off enc l t + 2 * (enc l[t]).length < n by omega, ↓reduceIte]
        refine ReachesOut.read (show lookupProgram.instr 8 = _ from rfl) hb ?_
        simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
          List.getD_cons_succ, read_W l k (show off enc l t + 2 * (enc l[t]).length < n by omega),
          getElem?_end enc l ht, readLabel]
        refine ReachesOut.assign (show lookupProgram.instr 10 = _ from rfl) hb ?_
        simp only [eval_add, eval_reg, eval_const, List.getD_cons_zero, List.getD_cons_succ]
        convert ReachesOut.refl _ using 3
        simp [hoff]; omega
      | succ _ ih =>
        have hb := bounded4 (B := B) (a₀ := n) (a₁ := k) (a₂ := off enc l t + 2 * j)
          (a₃ := t) (by omega) (by omega) (by omega) (by omega)
        refine ReachesOut.lt (show lookupProgram.instr 7 = _ from rfl) hb ?_
        simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ,
          show off enc l t + 2 * j < n by omega, ↓reduceIte]
        refine ReachesOut.read (show lookupProgram.instr 8 = _ from rfl) hb ?_
        simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
          List.getD_cons_succ, read_W l k (show off enc l t + 2 * j < n by omega),
          getElem?_marker enc l ht (show j < (enc l[t]).length by omega), readLabel]
        refine ReachesOut.assign (show lookupProgram.instr 9 = _ from rfl) hb ?_
        have := ih (j + 1) (by omega) (by omega)
        simpa [Nat.mul_add, Nat.add_assoc] using this
    simpa using key 0 (Nat.zero_le _)
  · have h₁ : off enc l t = n := off_of_le enc l (by omega)
    have h₂ : off enc l (t + 1) = n := off_of_le enc l (by omega)
    rw [h₁, h₂]
    refine ReachesOut.lt (show lookupProgram.instr 7 = _ from rfl)
      (bounded4 (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ, lt_irrefl, ↓reduceIte]
    exact ReachesOut.refl _

/-- Copying the digits of the element at position `t`, from its `j`-th digit on. -/
private theorem reachesOut_copy (hB : 2 * (encList enc l).length + 1 + k ≤ B) {t : ℕ}
    (ht : t < l.length) (htk : t ≤ k) :
    ∀ j ≤ (enc l[t]).length, lookupProgram.ReachesOut X (lookupProgram.Active B)
      (13, [(encList enc l).length, k, off enc l t + 2 * j, t])
      (18, [(encList enc l).length, k, off enc l t + 2 * (enc l[t]).length, t])
      ((enc l[t]).drop j) := by
  set n := (encList enc l).length
  have hoff := off_succ enc l ht
  have hle := off_le enc l (t + 1)
  intro j hj
  induction h : (enc l[t]).length - j generalizing j with
  | zero =>
    obtain rfl : j = (enc l[t]).length := by omega
    have hb := bounded4 (B := B) (a₀ := n) (a₁ := k) (a₂ := off enc l t + 2 * (enc l[t]).length)
      (a₃ := t) (by omega) (by omega) (by omega) (by omega)
    refine ReachesOut.read (show lookupProgram.instr 13 = _ from rfl) hb ?_
    simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
      List.getD_cons_succ, read_W l k (show off enc l t + 2 * (enc l[t]).length < n by omega),
      getElem?_end enc l ht, readLabel, List.drop_length]
    exact ReachesOut.refl _
  | succ _ ih =>
    have hb := bounded4 (B := B) (a₀ := n) (a₁ := k) (a₂ := off enc l t + 2 * j)
      (a₃ := t) (by omega) (by omega) (by omega) (by omega)
    refine ReachesOut.read (show lookupProgram.instr 13 = _ from rfl) hb ?_
    simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
      List.getD_cons_succ, read_W l k (show off enc l t + 2 * j < n by omega),
      getElem?_marker enc l ht (show j < (enc l[t]).length by omega), readLabel]
    refine ReachesOut.read (show lookupProgram.instr 14 = _ from rfl) hb ?_
    have hbit : X[2 * (off enc l t + 2 * j) + 3]? = some (enc l[t])[j] := by
      rw [show 2 * (off enc l t + 2 * j) + 3 = 2 * (off enc l t + 2 * j + 1) + 1 by omega,
        read_W l k (show off enc l t + 2 * j + 1 < n by omega), getElem?_bit enc l ht
          (show j < (enc l[t]).length by omega), List.getElem?_eq_getElem (by omega)]
    simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
      List.getD_cons_succ, hbit, List.drop_eq_getElem_cons (show j < (enc l[t]).length by omega)]
    have hrest := ih (j + 1) (by omega) (by omega)
    have hstep : lookupProgram.ReachesOut X (lookupProgram.Active B)
        (17, [n, k, off enc l t + 2 * j, t]) (18, [n, k, off enc l t + 2 * (enc l[t]).length, t])
        ((enc l[t]).drop (j + 1)) :=
      ReachesOut.assign (show lookupProgram.instr 17 = _ from rfl) hb
        (by simpa [Nat.mul_add, Nat.add_assoc] using hrest)
    cases (enc l[t])[j]
    · exact ReachesOut.emit (show lookupProgram.instr 16 = _ from rfl) hb hstep
    · exact ReachesOut.emit (show lookupProgram.instr 15 = _ from rfl) hb hstep

private theorem reachesOut_lookupProgram :
    ∃ s fin, lookupProgram.ReachesOut X
      (lookupProgram.Active (((frame (encList enc l) ++ List.replicate k true).length + 1) ^ 1))
      lookupProgram.init s
      ((l[k]?).elim [] fun a => true :: enc a) ∧ lookupProgram.instr s.1 = .halt fin ∧ fin = [] ∧
      ∀ r ∈ s.2, r ≤ ((frame (encList enc l) ++ List.replicate k true).length + 1) ^ 1 := by
  set n := (encList enc l).length
  have hlen : (frame (encList enc l) ++ List.replicate k true).length = 2 * n + 1 + k :=
    length_input _ k
  set B := ((frame (encList enc l) ++ List.replicate k true).length + 1) ^ 1
  have hB : 2 * n + 1 + k ≤ B := by simp only [B, pow_one]; omega
  have hhead := reachesOut_header (P := lookupProgram) (w := encList enc l) (k := k)
    (codeAt_of_code_eq (pre := []) (post := forCode 4 3 (reg 1) 7 11 ++ _) rfl) hB
  have hfor : lookupProgram.CodeAt 4 (forCode 4 3 (reg 1) 7 11) := by
    have h := codeAt_of_code_eq (P := lookupProgram) (pre := headerCode)
      (l := forCode 4 3 (reg 1) 7 11) (post := _) rfl
    simpa [headerCode] using h
  obtain ⟨regs, hloop, hinv⟩ := reachesOut_forCode (w := X) (B := B) hfor (N := k)
    (fun t regs => regs = [n, k, off enc l t, t] ∧ t ≤ k) (fun _ => []) (by omega)
    (fun t regs h => by
      obtain ⟨rfl, ht⟩ := h
      exact ⟨rfl, rfl, by simp, bounded4 (by omega) (by omega)
        ((off_le enc l t).trans (by omega)) (by omega)⟩)
    (fun t ht regs h => by
      obtain ⟨rfl, -⟩ := h
      exact ⟨_, reachesOut_skip hB ht.le, rfl, bounded4 (by omega) (by omega)
        ((off_le enc l _).trans (by omega)) (by omega), by simp [n], by omega⟩)
    [n, k, 0, 0] (bounded4 (by omega) (by omega) (by omega) (by omega))
    ⟨by simp [off], Nat.zero_le _⟩
  obtain ⟨rfl, -⟩ := hinv
  have hpre := hhead.trans hloop
  have hnil : (List.range k).flatMap (fun _ : ℕ => ([] : List Bool)) = [] := by simp
  rw [hnil, List.nil_append] at hpre
  have hb := bounded4 (B := B) (a₀ := n) (a₁ := k) (a₂ := off enc l k) (a₃ := k) (by omega)
    (by omega) ((off_le enc l k).trans (by omega)) (by omega)
  by_cases hk : k < l.length
  · have hlt := off_lt_length (enc := enc) l hk
    have hoff := off_succ enc l hk
    have hle := off_le enc l (k + 1)
    refine ⟨(18, [n, k, off enc l k + 2 * (enc l[k]).length, k]), [], ?_, rfl, rfl,
      bounded4 (by omega) (by omega) (by omega) (by omega)⟩
    rw [List.getElem?_eq_getElem hk]
    refine hpre.trans (ReachesOut.lt (show lookupProgram.instr 11 = _ from rfl) hb ?_)
    simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ,
      show off enc l k < n from hlt, ↓reduceIte]
    refine ReachesOut.emit (show lookupProgram.instr 12 = _ from rfl) hb ?_
    simpa using reachesOut_copy hB hk le_rfl 0 (Nat.zero_le _)
  · have hoff : off enc l k = n := off_of_le enc l (by omega)
    refine ⟨(19, [n, k, off enc l k, k]), [], ?_, rfl, rfl, hb⟩
    rw [List.getElem?_eq_none (by omega)]
    refine hpre.trans (ReachesOut.lt (show lookupProgram.instr 11 = _ from rfl) hb ?_)
    simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ, hoff, lt_irrefl, ↓reduceIte]
    exact ReachesOut.refl _

end Lookup

end Turing.CounterProgram.Words

namespace Turing.MultiTapeTM.ComputableInLogSpace

open CounterProgram CounterProgram.Words CounterProgram.Expr

/-- **The first `k` bits of a word**, with `k` in unary, in logarithmic space. -/
theorem bitsTake :
    ComputableInLogSpace (fun p : List Bool × ℕ => p.1.take p.2) (encPair encBits encUnary)
      encBits :=
  computableInLogSpace_shiftProgram (o := 0) (bound := reg 1) (by decide) (N := fun _ k => k)
    (fun _ _ _ => rfl) (fun _ _ => by omega)
    (fun w k => by simp [flatMap_range_getElem?_toList])

/-- **A word without its first `k` bits**, with `k` in unary, in logarithmic space. -/
theorem bitsDrop :
    ComputableInLogSpace (fun p : List Bool × ℕ => p.1.drop p.2) (encPair encBits encUnary)
      encBits :=
  computableInLogSpace_shiftProgram (o := 1) (bound := sub (reg 0) (reg 1)) le_rfl
    (N := fun w k => w.length - k) (fun _ _ _ => rfl) (fun _ _ => by omega)
    (fun w k => by
      have : ∀ i, w[i + 1 * k]? = (w.drop k)[i]? := fun i => by
        rw [List.getElem?_drop, Nat.one_mul, Nat.add_comm]
      simp only [this, flatMap_range_getElem?_toList, encBits_apply]
      rw [List.take_of_length_le (by simp)])

/-- **The list `0, …, n - 1`**, in unary, in logarithmic space. -/
theorem range : ComputableInLogSpace List.range encUnary (encList encUnary) := by
  refine rangeProgram.computableInLogSpace_of_reachesOut 1 fun n => ?_
  simp only [encUnary_apply, List.length_replicate, pow_one]
  obtain ⟨regs, h, hregs⟩ := reachesOut_rangeProgram n
  refine ⟨(11, regs), _, [], h, rfl, ?_, hregs⟩
  simp [encList, Function.comp_def, frame_replicate]

/-- **Looking up the element at a unary index** in a list, in logarithmic space. -/
theorem getElem? {α : Type} (enc : α ↪ List Bool) :
    ComputableInLogSpace (fun p : List α × ℕ => p.1[p.2]?) (encPair (encList enc) encUnary)
      (encOption enc) := by
  refine lookupProgram.computableInLogSpace_of_reachesOut 1 fun ⟨l, k⟩ => ?_
  obtain ⟨s, fin, h, hhalt, rfl, hs⟩ := reachesOut_lookupProgram (enc := enc) (l := l) (k := k)
  exact ⟨s, _, [], h, hhalt, by simp [encOption], hs⟩

/-! ### Automation -/

section Automation

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- The first `k` bits of a computed word, in the form used by `fun_prop`. -/
@[fun_prop]
theorem bitsTake' {w : γ → List Bool} {k : γ → ℕ} (hw : ComputableInLogSpace w encIn encBits)
    (hk : ComputableInLogSpace k encIn encUnary) :
    ComputableInLogSpace (fun a => (w a).take (k a)) encIn encBits :=
  bitsTake.comp' (pair hw hk)

/-- A computed word without its first `k` bits, in the form used by `fun_prop`. -/
@[fun_prop]
theorem bitsDrop' {w : γ → List Bool} {k : γ → ℕ} (hw : ComputableInLogSpace w encIn encBits)
    (hk : ComputableInLogSpace k encIn encUnary) :
    ComputableInLogSpace (fun a => (w a).drop (k a)) encIn encBits :=
  bitsDrop.comp' (pair hw hk)

/-- Looking up a computed unary index in a computed list, in the form used by `fun_prop`. -/
@[fun_prop]
theorem getElem?' {α : Type} {enc : α ↪ List Bool} {l : γ → List α} {k : γ → ℕ}
    (hl : ComputableInLogSpace l encIn (encList enc)) (hk : ComputableInLogSpace k encIn encUnary) :
    ComputableInLogSpace (fun a => (l a)[k a]?) encIn (encOption enc) :=
  (getElem? enc).comp' (pair hl hk)

attribute [fun_prop] range

end Automation

end Turing.MultiTapeTM.ComputableInLogSpace
