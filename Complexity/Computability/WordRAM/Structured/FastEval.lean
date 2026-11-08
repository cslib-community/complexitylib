/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured
public import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

/-!
# A fast compiled interpreter for structured word-RAM programs

`Cslib.WordRAM.Code.eval` keeps the registers and memory as functions, and each write wraps the
previous function in a `Function.update`. That shape suits proofs. In compiled code, though, a
read walks back through every earlier write, so a run of `n` instructions takes `Θ(n²)` time.

`Cslib.WordRAM.Code.evalFast` is the same interpreter on `Cslib.WordRAM.FastData`, which keeps
the registers in a `Vector` and the written memory cells in a `Std.HashMap` over the initial
memory. `Cslib.WordRAM.Code.evalFast_toData` proves that it computes `Code.eval`, and the
`@[csimp]` theorem `Cslib.WordRAM.Code.eval_eq_evalImpl` makes the compiler use it for
`Code.eval`. This changes only compiled evaluation, such as `#eval` and `#guard` regressions over
concrete runs. `Code.eval`, its lemmas and kernel reduction (`decide`, `rfl`) are unchanged.

Import this module where compiled code evaluates long runs. The replacement applies only to
callers compiled with this module imported, not to callers compiled before. This module does
not certify a runtime bound.

## Main definitions

* `Cslib.WordRAM.FastData`, `Cslib.WordRAM.FastData.toData`: array-backed machine data and the
  `Cslib.WordRAM.Data` it represents.
* `Cslib.WordRAM.Code.evalFast`: the interpreter on `FastData`.
* `Cslib.WordRAM.Code.evalImpl`: `Code.eval` computed with `Code.evalFast`.

## Main results

* `Cslib.WordRAM.Code.evalFast_toData`: `Code.evalFast` computes `Code.eval`.
* `Cslib.WordRAM.Code.eval_eq_evalImpl`: proved compiler replacement of `Code.eval` by
  `Code.evalImpl`.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-- Machine data for compiled execution: the registers as a vector, and memory as the cells
written so far over the initial memory `base`. -/
structure FastData (r : ℕ) where
  /-- The contents of the registers. -/
  regs : Vector ℕ r
  /-- The memory cells written so far. -/
  written : Std.HashMap ℕ ℕ
  /-- The memory before any write. -/
  base : ℕ → ℕ

namespace FastData

/-- The contents of register `i`. -/
@[inline] def reg (x : FastData r) (i : Fin r) : ℕ := x.regs[i.val]

/-- The contents of memory at address `a`. The initial memory is only consulted for cells that
were never written. -/
@[inline] def read (x : FastData r) (a : ℕ) : ℕ :=
  match x.written[a]? with
  | some v => v
  | none => x.base a

/-- The data that `x` represents. -/
def toData (x : FastData r) : Data r := ⟨x.reg, x.read⟩

/-- Fast data for `x`, with nothing written yet. -/
def ofData (x : Data r) : FastData r := ⟨Vector.ofFn x.regs, ∅, x.mem⟩

/-- Set register `i` to `v`. -/
@[inline] def set (x : FastData r) (i : Fin r) (v : ℕ) : FastData r :=
  { x with regs := x.regs.set i v }

/-- Set register `i` to `v` if `v` fits a `w`-bit word, and fault otherwise. -/
@[inline] def put (w : ℕ) (x : FastData r) (i : Fin r) (v : ℕ) : Option (FastData r) :=
  if Fits w v then some (x.set i v) else none

/-- Set the memory cell at address `a` to `v`. -/
@[inline] def write (x : FastData r) (a v : ℕ) : FastData r :=
  { x with written := x.written.insert a v }

/-- Fast data made from `x` represents `x`. -/
@[simp]
theorem toData_ofData (x : Data r) : (ofData x).toData = x := by
  ext <;> simp [ofData, toData, reg, read]

/-- Setting a register of fast data sets it in the data represented. -/
theorem toData_set (x : FastData r) (i : Fin r) (v : ℕ) :
    (x.set i v).toData = x.toData.set i v := by
  ext j
  · simp only [toData, set, reg, Data.set_regs, Function.update_apply, Vector.getElem_set,
      Fin.val_inj]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · rfl

/-- `FastData.put` agrees with `Data.put` on the data represented. -/
theorem toData_put (w : ℕ) (x : FastData r) (i : Fin r) (v : ℕ) :
    (x.put w i v).map toData = x.toData.put w i v := by
  unfold put Data.put
  split
  · exact congrArg some (toData_set x i v)
  · rfl

/-- Writing memory of fast data writes it in the data represented. -/
theorem toData_write (x : FastData r) (a v : ℕ) :
    (x.write a v).toData = x.toData.write a v := by
  ext b
  · rfl
  · simp only [toData, write, read, Data.write_mem, Function.update_apply,
      Std.HashMap.getElem?_insert, beq_iff_eq]
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]

end FastData

/-- Whether a condition holds of fast data. -/
@[inline] def Cond.holdsFast : Cond r → FastData r → Bool
  | .eq i j, x => decide (x.reg i = x.reg j)
  | .lt i j, x => decide (x.reg i < x.reg j)

/-- `Cond.holdsFast` decides `Cond.Holds` on the data represented. -/
theorem Cond.holdsFast_eq (c : Cond r) (x : FastData r) :
    c.holdsFast x = decide (c.Holds x.toData) := by
  cases c <;> rfl

/-- The effect of a data instruction on fast data, as `Op.eval`. -/
def Op.evalFast (w : ℕ) : Op B r → FastData r → Option (FastData r)
  | .const d v, x => x.put w d v
  | .copy d s, x => some (x.set d (x.reg s))
  | .alu f d args, x => do
      let value ← B.interp w f (x.reg ∘ args)
      x.put w d value
  | .load d a, x => some (x.set d (x.read (x.reg a)))
  | .store a s, x => some (x.write (x.reg a) (x.reg s))

/-- `Op.evalFast` computes `Op.eval` on the data represented. -/
theorem Op.evalFast_toData (w : ℕ) (o : Op B r) (x : FastData r) :
    (o.evalFast w x).map FastData.toData = o.eval w x.toData := by
  cases o with
  | const d v => exact FastData.toData_put w x d v
  | copy d s => exact congrArg some (FastData.toData_set x d (x.reg s))
  | alu f d args =>
    simp only [evalFast, eval]
    change (Option.bind _ _).map _ = Option.bind (B.interp w f (x.reg ∘ args)) _
    cases B.interp w f (x.reg ∘ args) with
    | none => rfl
    | some v => exact FastData.toData_put w x d v
  | load d a => exact congrArg some (FastData.toData_set x d (x.read (x.reg a)))
  | store a s => exact congrArg some (FastData.toData_write x (x.reg a) (x.reg s))

/-- `Code.evalLoop` on fast data. -/
def Code.evalLoopFast (c : Cond r) (body : FastData r → Option (FastData r × ℕ)) :
    ℕ → FastData r → Option (FastData r × ℕ)
  | 0, x => if c.holdsFast x then none else some (x, 2)
  | fuel + 1, x =>
    if c.holdsFast x then do
      let ym ← body x
      (evalLoopFast c body fuel ym.1).map fun zn => (zn.1, ym.2 + zn.2 + 2)
    else some (x, 2)

/-- `Code.eval` on fast data. -/
def Code.evalFast (w fuel : ℕ) : Code B r → FastData r → Option (FastData r × ℕ)
  | .op o, x => (o.evalFast w x).map fun y => (y, 1)
  | .seq c₁ c₂, x => do
    let ym ← c₁.evalFast w fuel x
    (c₂.evalFast w fuel ym.1).map fun zn => (zn.1, ym.2 + zn.2)
  | .branch c pos neg, x =>
    if c.holdsFast x then (pos.evalFast w fuel x).map fun yn => (yn.1, yn.2 + 1)
    else (neg.evalFast w fuel x).map fun yn => (yn.1, yn.2 + 2)
  | .loop c body, x => evalLoopFast c (fun y => body.evalFast w fuel y) fuel x
  | .rand _ _, _ => none

/-- The fast loop computes `Code.evalLoop` when its body does. -/
theorem Code.evalLoopFast_toData (c : Cond r) {f : FastData r → Option (FastData r × ℕ)}
    {g : Data r → Option (Data r × ℕ)}
    (hfg : ∀ x, (f x).map (Prod.map FastData.toData id) = g x.toData)
    (fuel : ℕ) (x : FastData r) :
    (evalLoopFast c f fuel x).map (Prod.map FastData.toData id) = evalLoop c g fuel x.toData := by
  induction fuel generalizing x with
  | zero =>
    simp only [evalLoopFast, evalLoop, Cond.holdsFast_eq, decide_eq_true_eq]
    split <;> rfl
  | succ fuel ih =>
    simp only [evalLoopFast, evalLoop, Cond.holdsFast_eq, decide_eq_true_eq]
    split
    · rw [← hfg x]
      cases f x with
      | none => rfl
      | some ym =>
        change ((evalLoopFast c f fuel ym.1).map _).map _ = (evalLoop c g fuel ym.1.toData).map _
        rw [← ih ym.1, Option.map_map, Option.map_map]
        rfl
    · rfl

/-- `Code.evalFast` computes `Code.eval`. -/
theorem Code.evalFast_toData (w fuel : ℕ) (c : Code B r) (x : FastData r) :
    (c.evalFast w fuel x).map (Prod.map FastData.toData id) = c.eval w fuel x.toData := by
  induction c generalizing x with
  | op o =>
    simp only [evalFast, eval, ← Op.evalFast_toData, Option.map_map]
    rfl
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [evalFast, eval, ← ih₁]
    cases c₁.evalFast w fuel x with
    | none => rfl
    | some ym =>
      change ((evalFast w fuel c₂ ym.1).map _).map _ = (eval w fuel c₂ ym.1.toData).map _
      rw [← ih₂, Option.map_map, Option.map_map]
      rfl
  | branch c pos neg ihp ihn =>
    simp only [evalFast, eval, Cond.holdsFast_eq, decide_eq_true_eq]
    split
    · rw [← ihp, Option.map_map, Option.map_map]
      rfl
    · rw [← ihn, Option.map_map, Option.map_map]
      rfl
  | loop c body ih =>
    exact evalLoopFast_toData c (fun y => ih y) fuel x
  | rand dst src => rfl

/-- `Code.eval`, computed with `Code.evalFast`. -/
def Code.evalImpl (w fuel : ℕ) (c : Code B r) (x : Data r) : Option (Data r × ℕ) :=
  (c.evalFast w fuel (.ofData x)).map (Prod.map FastData.toData id)

/-- Compiled code evaluates `Code.eval` with the fast interpreter. -/
@[csimp]
theorem Code.eval_eq_evalImpl : @Code.eval = @Code.evalImpl := by
  funext B r w fuel c x
  rw [Code.evalImpl, Code.evalFast_toData, FastData.toData_ofData]

end Cslib.WordRAM
