/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Notation for structured word-RAM programs

`ram[ s₁; s₂; … ]` writes a structured program (`Cslib.WordRAM.Code`) as a sequence of statements,
one per data instruction, in the style of word-RAM pseudocode. Registers are named by identifiers,
for instance local abbreviations of elements of `Fin r`. The statements are:

* `d ← #v`: set register `d` to the constant `v`;
* `d ← s`: copy register `s` into register `d`;
* `d ← i + j`, and likewise `-`, `*`, `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, `>>>`: a binary
  operation (`Cslib.WordRAM.BinOp`) on registers `i` and `j`;
* `d ← *a`, `*a ← s`: load from and store to the memory cell whose address is in register `a`;
* `d ← width%`: set register `d` to the word size;
* `if i = j then [ … ] else [ … ]`, `if i < j then [ … ] else [ … ]`: a conditional;
* `while i = j do [ … ]`, `while i < j do [ … ]`: a loop;
* `⟪c⟫`: the structured program `c`, for instance a subroutine.

The notation unfolds to the constructors of `Cslib.WordRAM.Code`, so it adds nothing to the
semantics. The binary operations and `width%` are instructions of the standard basis
(`Cslib.WordRAM.Op.bin`, `Cslib.WordRAM.Op.width`); the other statements work over every basis.
It is scoped: `open Cslib.WordRAM` enables it. Its statement forms follow the word-RAM notation of
[Algolean][Algolean2026]. Its only new tokens are `ram[`, `width%` and the
internal `ram_stmt%` and `ram_block%`, so it reserves no identifiers: `ram` and `width` remain
ordinary names.

## Main definitions

* `ram[ s₁; s₂; … ]`: scoped notation for structured word-RAM programs (`Cslib.WordRAM.Code`).

## Tactics

* `ram_eval`, `ram_eval n`: symbolic execution. On a goal `Cslib.WordRAM.ExecWithin w c x y T`
  or `Cslib.WordRAM.Exec w c x y T`, it runs the interpreter `Cslib.WordRAM.Code.eval` on `c` and
  `x` with `simp`, allowing each loop `n` iterations (default `0`, for loop-free code), and
  closes the goal when the result is `y` within (exactly, for `Exec`) `T` instructions; with `y`
  a metavariable, it determines `y`. Which constants and results fit a word is decided for
  numerals and otherwise taken from the given simp lemmas, stated with `Cslib.WordRAM.Fits`.
  Programs given by name are unfolded by passing their definitions among the simp lemmas, as in
  `ram_eval [myProgram, h]`.

## References

* [S. Srinivas et al., *Algolean*][Algolean2026]
-/

public section

namespace Cslib.WordRAM

/-- A statement of a structured word-RAM program. -/
declare_syntax_cat wramStmt

/-- A block of statements, separated by semicolons. -/
syntax wramBlock := "[" sepBy1(wramStmt, "; ") "]"

/-- A structured word-RAM program, written as a block of statements. -/
scoped syntax "ram[" sepBy1(wramStmt, "; ") "]" : term

/-- Internal: a nested block of statements, as a structured program. -/
scoped syntax "ram_block%" wramBlock : term

/-- Internal: a single statement, as a structured program. -/
scoped syntax "ram_stmt%" wramStmt : term

/-- Set a register to a constant. -/
syntax ident " ← " "#" term:max : wramStmt
/-- Copy a register. -/
syntax ident " ← " ident : wramStmt
/-- Addition. -/
syntax ident " ← " ident " + " ident : wramStmt
/-- Truncated subtraction. -/
syntax ident " ← " ident " - " ident : wramStmt
/-- Multiplication. -/
syntax ident " ← " ident " * " ident : wramStmt
/-- Division. -/
syntax ident " ← " ident " / " ident : wramStmt
/-- Remainder. -/
syntax ident " ← " ident " % " ident : wramStmt
/-- Bitwise and. -/
syntax ident " ← " ident " &&& " ident : wramStmt
/-- Bitwise or. -/
syntax ident " ← " ident " ||| " ident : wramStmt
/-- Bitwise exclusive or. -/
syntax ident " ← " ident " ^^^ " ident : wramStmt
/-- Shift left. -/
syntax ident " ← " ident " <<< " ident : wramStmt
/-- Shift right. -/
syntax ident " ← " ident " >>> " ident : wramStmt
/-- Load from the memory cell whose address is in a register. -/
syntax ident " ← " "*" ident : wramStmt
/-- Store to the memory cell whose address is in a register. -/
syntax "*" ident " ← " ident : wramStmt
/-- Read the word size. -/
syntax ident " ← " "width%" : wramStmt
/-- A conditional on the equality of two registers. -/
syntax "if " ident " = " ident " then " wramBlock " else " wramBlock : wramStmt
/-- A conditional on the comparison of two registers. -/
syntax "if " ident " < " ident " then " wramBlock " else " wramBlock : wramStmt
/-- A loop while two registers are equal. -/
syntax "while " ident " = " ident " do " wramBlock : wramStmt
/-- A loop while one register is smaller than another. -/
syntax "while " ident " < " ident " do " wramBlock : wramStmt
/-- A structured program given as a term. -/
syntax "⟪" term "⟫" : wramStmt

macro_rules
  | `(ram[ $s:wramStmt ]) => `(ram_stmt% $s)
  | `(ram[ $s:wramStmt; $ss;* ]) => `(Cslib.WordRAM.Code.seq (ram_stmt% $s) (ram[ $ss;* ]))
  | `(ram_block% [ $ss;* ]) => `(ram[ $ss;* ])

macro_rules
  | `(ram_stmt% $d:ident ← #$v) => `(Cslib.WordRAM.Code.op (.const $d $v))
  | `(ram_stmt% $d:ident ← $s:ident) => `(Cslib.WordRAM.Code.op (.copy $d $s))
  | `(ram_stmt% $d:ident ← $i:ident + $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .add $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident - $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .sub $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident * $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .mul $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident / $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .div $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident % $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .mod $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident &&& $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .and $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident ||| $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .or $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident ^^^ $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .xor $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident <<< $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .shiftLeft $d $i $j))
  | `(ram_stmt% $d:ident ← $i:ident >>> $j:ident) =>
    `(Cslib.WordRAM.Code.op (.bin .shiftRight $d $i $j))
  | `(ram_stmt% $d:ident ← *$a:ident) => `(Cslib.WordRAM.Code.op (.load $d $a))
  | `(ram_stmt% *$a:ident ← $s:ident) => `(Cslib.WordRAM.Code.op (.store $a $s))
  | `(ram_stmt% $d:ident ← width%) => `(Cslib.WordRAM.Code.op (.width $d))
  | `(ram_stmt% if $i:ident = $j:ident then $p:wramBlock else $n:wramBlock) =>
    `(Cslib.WordRAM.Code.branch (.eq $i $j) (ram_block% $p) (ram_block% $n))
  | `(ram_stmt% if $i:ident < $j:ident then $p:wramBlock else $n:wramBlock) =>
    `(Cslib.WordRAM.Code.branch (.lt $i $j) (ram_block% $p) (ram_block% $n))
  | `(ram_stmt% while $i:ident = $j:ident do $b:wramBlock) =>
    `(Cslib.WordRAM.Code.loop (.eq $i $j) (ram_block% $b))
  | `(ram_stmt% while $i:ident < $j:ident do $b:wramBlock) =>
    `(Cslib.WordRAM.Code.loop (.lt $i $j) (ram_block% $b))
  | `(ram_stmt% ⟪$c⟫) => `(($c : Cslib.WordRAM.Code _ _))

/-- Symbolically execute structured code on a goal `ExecWithin w c x y T` or `Exec w c x y T`,
allowing each loop the given number of iterations (default `0`), and deciding with the given simp
lemmas which written numbers fit a word. -/
syntax (name := ramEval) "ram_eval" (ppSpace num)? (" [" Lean.Parser.Tactic.simpArg,* "]")? :
  tactic

macro_rules
  | `(tactic| ram_eval) => `(tactic| ram_eval 0 [])
  | `(tactic| ram_eval [$args,*]) => `(tactic| ram_eval 0 [$args,*])
  | `(tactic| ram_eval $n:num) => `(tactic| ram_eval $n [])
  | `(tactic| ram_eval $n:num [$args,*]) => `(tactic|
      first
      | (apply Cslib.WordRAM.ExecWithin.of_eval (fuel := $n)
         · set_option linter.unusedSimpArgs false in
           simp +decide only [Cslib.WordRAM.Code.eval, Cslib.WordRAM.Code.evalLoop,
            Cslib.WordRAM.Op.eval_const, Cslib.WordRAM.Op.eval_copy, Cslib.WordRAM.Op.eval_alu,
            Cslib.WordRAM.Op.eval_load, Cslib.WordRAM.Op.eval_store, Cslib.WordRAM.Op.eval_bin,
            Cslib.WordRAM.Op.eval_width, Cslib.WordRAM.Basis.standard_interp_bin,
            Cslib.WordRAM.Basis.standard_interp_width, Cslib.WordRAM.Data.put,
            Cslib.WordRAM.fits_zero,
            Cslib.WordRAM.BinOp.eval, Cslib.WordRAM.Cond.holds_eq, Cslib.WordRAM.Cond.holds_lt,
            Cslib.WordRAM.Data.set_regs, Cslib.WordRAM.Data.set_mem,
            Cslib.WordRAM.Data.write_regs, Cslib.WordRAM.Data.write_mem, Function.update_self,
            Function.update_apply, bind, Option.map_some, Option.bind_some, Option.map_none,
            Option.bind_none, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
            Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.reduceAnd, Nat.reduceOr,
            Nat.reduceXor, Nat.reduceShiftLeft, Nat.reduceShiftRight, Nat.reduceLT,
            Nat.reduceLeDiff, Nat.reduceEqDiff, $args,*]
           try rfl
         · try omega)
      | (apply Cslib.WordRAM.Exec.of_eval (fuel := $n)
         set_option linter.unusedSimpArgs false in
         simp +decide only [Cslib.WordRAM.Code.eval, Cslib.WordRAM.Code.evalLoop,
          Cslib.WordRAM.Op.eval_const, Cslib.WordRAM.Op.eval_copy, Cslib.WordRAM.Op.eval_alu,
          Cslib.WordRAM.Op.eval_load, Cslib.WordRAM.Op.eval_store, Cslib.WordRAM.Op.eval_bin,
          Cslib.WordRAM.Op.eval_width, Cslib.WordRAM.Basis.standard_interp_bin,
          Cslib.WordRAM.Basis.standard_interp_width, Cslib.WordRAM.Data.put,
          Cslib.WordRAM.fits_zero,
          Cslib.WordRAM.BinOp.eval, Cslib.WordRAM.Cond.holds_eq, Cslib.WordRAM.Cond.holds_lt,
          Cslib.WordRAM.Data.set_regs, Cslib.WordRAM.Data.set_mem,
          Cslib.WordRAM.Data.write_regs, Cslib.WordRAM.Data.write_mem, Function.update_self,
          Function.update_apply, bind, Option.map_some, Option.bind_some, Option.map_none,
          Option.bind_none, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
          Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.reduceAnd, Nat.reduceOr,
          Nat.reduceXor, Nat.reduceShiftLeft, Nat.reduceShiftRight, Nat.reduceLT,
          Nat.reduceLeDiff, Nat.reduceEqDiff, $args,*]
         try rfl))

end Cslib.WordRAM

end
