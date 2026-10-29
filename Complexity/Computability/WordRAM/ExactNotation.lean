/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation

/-!
# Notation for structured word-RAM programs over the exact basis

`ram_exact[ s₁; s₂; … ]` is `ram[ s₁; s₂; … ]` over the exact basis
`Cslib.WordRAM.Basis.exact`: it has the same statements, but a binary operation `d ← i - j`,
`d ← i / j`, … is the instruction `Cslib.WordRAM.Op.exactBin`, which faults where its exact value
is undefined (subtraction below zero, division and remainder by zero), and `d ← width%` is
`Cslib.WordRAM.Op.exactWidth`. The tactic `ram_exact_eval` is `ram_eval` for such programs.

The notation, with its expansions and the tactic, is scoped to `Cslib.WordRAM`, alongside the
`wramStmt` statement syntax of `Complexity/Computability/WordRAM/Notation.lean`.

## Main definitions

* `ram_exact[ s₁; s₂; … ]`: structured word-RAM programs over the exact basis.
* `ram_exact_eval`: symbolic execution of such programs.

## Tactics

* `ram_exact_eval`, `ram_exact_eval n`: as `ram_eval`. A subtraction runs when the simp lemmas
  show that its right operand is at most its left one, and a division or remainder when they
  show that its divisor is nonzero.

## References

The statements are those of the `ram[` notation (`WordRAM.Notation`), whose forms follow the
word-RAM notation of [Algolean][Algolean2026].
-/

public section

namespace Cslib.WordRAM

/-- A structured word-RAM program over the exact basis, written as a block of statements. -/
scoped syntax "ram_exact[" sepBy1(wramStmt, "; ") "]" : term

/-- Internal: a nested block of statements, as a structured program over the exact basis. -/
scoped syntax "ram_exact_block%" Cslib.WordRAM.wramBlock : term

/-- Internal: a single statement, as a structured program over the exact basis. -/
scoped syntax "ram_exact_stmt%" wramStmt : term

scoped macro_rules
  | `(ram_exact[ $s:wramStmt ]) => `(ram_exact_stmt% $s)
  | `(ram_exact[ $s:wramStmt; $ss;* ]) =>
    `(Cslib.WordRAM.Code.seq (ram_exact_stmt% $s) (ram_exact[ $ss;* ]))
  | `(ram_exact_block% [ $ss;* ]) => `(ram_exact[ $ss;* ])

scoped macro_rules
  | `(ram_exact_stmt% $d:ident ← #$v) => `(Cslib.WordRAM.Code.op (.const $d $v))
  | `(ram_exact_stmt% $d:ident ← $s:ident) => `(Cslib.WordRAM.Code.op (.copy $d $s))
  | `(ram_exact_stmt% $d:ident ← $i:ident + $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .add $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident - $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .sub $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident * $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .mul $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident / $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .div $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident % $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .mod $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident &&& $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .and $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident ||| $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .or $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident ^^^ $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .xor $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident <<< $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .shiftLeft $d $i $j))
  | `(ram_exact_stmt% $d:ident ← $i:ident >>> $j:ident) =>
    `(Cslib.WordRAM.Code.op (.exactBin .shiftRight $d $i $j))
  | `(ram_exact_stmt% $d:ident ← *$a:ident) => `(Cslib.WordRAM.Code.op (.load $d $a))
  | `(ram_exact_stmt% *$a:ident ← $s:ident) => `(Cslib.WordRAM.Code.op (.store $a $s))
  | `(ram_exact_stmt% $d:ident ← width%) => `(Cslib.WordRAM.Code.op (.exactWidth $d))
  | `(ram_exact_stmt% if $i:ident = $j:ident then $p:wramBlock else $n:wramBlock) =>
    `(Cslib.WordRAM.Code.branch (.eq $i $j) (ram_exact_block% $p) (ram_exact_block% $n))
  | `(ram_exact_stmt% if $i:ident < $j:ident then $p:wramBlock else $n:wramBlock) =>
    `(Cslib.WordRAM.Code.branch (.lt $i $j) (ram_exact_block% $p) (ram_exact_block% $n))
  | `(ram_exact_stmt% while $i:ident = $j:ident do $b:wramBlock) =>
    `(Cslib.WordRAM.Code.loop (.eq $i $j) (ram_exact_block% $b))
  | `(ram_exact_stmt% while $i:ident < $j:ident do $b:wramBlock) =>
    `(Cslib.WordRAM.Code.loop (.lt $i $j) (ram_exact_block% $b))
  | `(ram_exact_stmt% ⟪$c⟫) => `(($c : Cslib.WordRAM.Code .exact _))

/-- Symbolically execute structured code over the exact basis on a goal `ExecWithin w c x y T` or
`Exec w c x y T`, allowing each loop the given number of iterations (default `0`), and deciding
with the given simp lemmas which written numbers fit a word, which subtractions stay at or above
zero, and which divisors are nonzero. -/
scoped syntax (name := ramExactEval)
  "ram_exact_eval" (ppSpace num)? (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

scoped macro_rules
  | `(tactic| ram_exact_eval) => `(tactic| ram_exact_eval 0 [])
  | `(tactic| ram_exact_eval [$args,*]) => `(tactic| ram_exact_eval 0 [$args,*])
  | `(tactic| ram_exact_eval $n:num) => `(tactic| ram_exact_eval $n [])
  | `(tactic| ram_exact_eval $n:num [$args,*]) => `(tactic|
      first
      | (apply Cslib.WordRAM.ExecWithin.of_eval (fuel := $n)
         · set_option linter.unusedSimpArgs false in
           simp +decide only [Cslib.WordRAM.Code.eval, Cslib.WordRAM.Code.evalLoop,
            Cslib.WordRAM.Op.eval_const, Cslib.WordRAM.Op.eval_copy, Cslib.WordRAM.Op.eval_alu,
            Cslib.WordRAM.Op.eval_load, Cslib.WordRAM.Op.eval_store,
            Cslib.WordRAM.Op.eval_exactBin, Cslib.WordRAM.Op.eval_exactWidth,
            Cslib.WordRAM.Basis.exact_interp_bin, Cslib.WordRAM.Basis.exact_interp_width,
            Cslib.WordRAM.Data.put, Cslib.WordRAM.fits_zero, Cslib.WordRAM.BinOp.evalExact,
            Cslib.WordRAM.Cond.holds_eq, Cslib.WordRAM.Cond.holds_lt,
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
          Cslib.WordRAM.Op.eval_load, Cslib.WordRAM.Op.eval_store,
          Cslib.WordRAM.Op.eval_exactBin, Cslib.WordRAM.Op.eval_exactWidth,
          Cslib.WordRAM.Basis.exact_interp_bin, Cslib.WordRAM.Basis.exact_interp_width,
          Cslib.WordRAM.Data.put, Cslib.WordRAM.fits_zero, Cslib.WordRAM.BinOp.evalExact,
          Cslib.WordRAM.Cond.holds_eq, Cslib.WordRAM.Cond.holds_lt,
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
