/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Compile

/-!
# Separating a native program's graph from its scalar literals

Extract immediate values in instruction order, erase only those values, and fill
an instruction graph from a computed value list. The roundtrip reconstructs the
actual program; code size and jump/branch targets do not change. This supports
uniform generation without duplicating a native algorithm's instruction graph.
-/

public section

namespace Cslib.WordRAM.Program

variable {B : Basis} {r : ℕ}

/-- Immediate values in instruction order; register indices and labels remain in the graph. -/
def literals : Program B r → List ℕ
  | [] => []
  | .op (.const _ v) :: rest => v :: literals rest
  | _ :: rest => literals rest

/-- Erase scalar immediate values, preserving every instruction, register and control label. -/
def eraseLiterals (p : Program B r) : Program B r :=
  p.map fun i => match i with
    | .op (.const d _) => .op (.const d 0)
    | i => i

/-- Fill successive constant instructions, consuming one value each; missing values are zero. -/
def fillLiterals : Program B r → List ℕ → Program B r
  | [], _ => []
  | .op (.const d _) :: rest, values =>
      .op (.const d (values.headD 0)) :: fillLiterals rest values.tail
  | i :: rest, values => i :: fillLiterals rest values

/-- Filling does not unroll loops or alter any instruction indices. -/
theorem length_fillLiterals (p : Program B r) (vs : List ℕ) :
    (p.fillLiterals vs).length = p.length := by
  induction p generalizing vs with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [fillLiterals, List.length_cons, ih]
    next o => cases o <;> simp [fillLiterals, ih]

/-- The erased graph and extracted values reconstruct the original executable code. -/
theorem fillLiterals_erase (p : Program B r) :
    p.eraseLiterals.fillLiterals p.literals = p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [eraseLiterals] at ih
    cases i with
    | op o => cases o <;> simp [eraseLiterals, fillLiterals, literals, ih]
    | _ => simp [eraseLiterals, fillLiterals, literals, ih]

/-- Literal extraction respects instruction-list concatenation. -/
theorem literals_append (p q : Program B r) : (p ++ q).literals = p.literals ++ q.literals := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | op o => cases o <;> simp [literals, ih]
    | _ => simp [literals, ih]

end Cslib.WordRAM.Program

namespace Cslib.WordRAM.Code

variable {B : Basis} {r : ℕ}

/-- Structured literal extraction in assembly order, visiting each loop body only once. -/
def literals : Code B r → List ℕ
  | .op (.const _ n) => [n]
  | .op _ | .rand _ _ => []
  | .seq a b => literals a ++ literals b
  | .branch _ pos neg => literals neg ++ literals pos
  | .loop _ body => literals body

/-- Structured graph erasure avoids expanding control-label arithmetic during generation. -/
def eraseLiterals : Code B r → Code B r
  | .op (.const d _) => .op (.const d 0)
  | .op o => .op o
  | .seq a b => .seq (eraseLiterals a) (eraseLiterals b)
  | .branch c a b => .branch c (eraseLiterals a) (eraseLiterals b)
  | .loop c body => .loop c (eraseLiterals body)
  | .rand d s => .rand d s

/-- Literal values are independent of register renaming. -/
theorem literals_rename {r' : ℕ} (c : Code B r) (f : Fin r → Fin r') :
    (c.rename f).literals = c.literals := by
  induction c with
  | op o => cases o <;> rfl
  | _ => simp_all [Code.rename, literals]

/-- Erasing constants leaves the complete control graph size unchanged. -/
theorem eraseLiterals_size (c : Code B r) : c.eraseLiterals.size = c.size := by
  induction c with
  | op o => cases o <;> rfl
  | _ => simp_all [eraseLiterals, size]

/-- Compilation adds control instructions but no additional scalar immediates. -/
theorem literals_assemble (c : Code B r) (pc : ℕ) :
    (c.assemble pc).literals = c.literals := by
  induction c generalizing pc with
  | op o => cases o <;> rfl
  | _ => simp_all [assemble, Program.literals_append, Program.literals, literals]

/-- The final halt has no scalar literal. -/
theorem literals_program (c : Code B r) (out : Fin r) :
    (c.program out).literals = c.literals := by
  simp [program, Program.literals_append, Program.literals, literals_assemble]

/-- Erasure commutes with compilation, including the original jump/branch labels. -/
theorem eraseLiterals_assemble (c : Code B r) (pc : ℕ) :
    (c.assemble pc).eraseLiterals = c.eraseLiterals.assemble pc := by
  induction c generalizing pc with
  | op o => cases o <;> rfl
  | _ => simp_all [assemble, Program.eraseLiterals, eraseLiterals, eraseLiterals_size]

/-- Program erasure can be computed on the smaller structured graph first. -/
theorem eraseLiterals_program (c : Code B r) (out : Fin r) :
    (c.program out).eraseLiterals = c.eraseLiterals.program out := by
  change (c.assemble 0 ++ [Instr.halt (B := B) out]).eraseLiterals =
    c.eraseLiterals.assemble 0 ++ [Instr.halt (B := B) out]
  simp only [Program.eraseLiterals, List.map_append, List.map_cons, List.map_nil]
  exact congrArg (fun p : Program B r => p ++ [Instr.halt (B := B) out])
    (eraseLiterals_assemble c 0)

end Cslib.WordRAM.Code
