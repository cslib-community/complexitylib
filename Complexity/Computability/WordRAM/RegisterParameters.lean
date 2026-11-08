/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Reusing immediate-parameter executions with register parameters

`Code.RegisterParameter` replaces selected immediate writes by copies of one
preserved register, including inside branches. Its execution theorem preserves
the complete final data and exact instruction count. A client can reuse an
immediate-parameter certificate after computing that parameter natively, without
rebuilding the proof of the surrounding program.
-/

public section

namespace Cslib.WordRAM

/-- A sequential or conditional context in which selected writes of `v` are supplied by `r`.
Untouched fragments must preserve `r`, so the parameter remains available. -/
inductive Code.RegisterParameter {B : Basis} {n : ℕ} (r : Fin n) (v : ℕ) :
    Code B n → Code B n → Prop
  | same (c : Code B n) : c.Preserves r → RegisterParameter r v c c
  | copy (d : Fin n) : d ≠ r → RegisterParameter r v (.op (.const d v)) (.op (.copy d r))
  | branch (cond : Cond n) {a b a' b' : Code B n} : RegisterParameter r v a a' →
      RegisterParameter r v b b' → RegisterParameter r v (.branch cond a b) (.branch cond a' b')
  | seq {a b a' b' : Code B n} : RegisterParameter r v a a' →
      RegisterParameter r v b b' → RegisterParameter r v (.seq a b) (.seq a' b')

namespace Code.RegisterParameter

variable {B : Basis} {n : ℕ} {r : Fin n} {v : ℕ} {c c' : Code B n}

/-- The original program preserves its parameter register. -/
theorem preserves (h : RegisterParameter r v c c') : c.Preserves r := by
  induction h with
  | same _ h => exact h
  | copy _ h => simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using h
  | seq _ _ ha hb | branch _ _ _ ha hb => exact ⟨ha, hb⟩

/-- Parameter substitution changes no instruction destination, hence preserves
exactly the same registers, including additional enclosing-loop state. -/
theorem preserves_iff (h : RegisterParameter r v c c') (i : Fin n) :
    c'.Preserves i ↔ c.Preserves i := by
  induction h with
  | same => rfl
  | copy => rfl
  | seq _ _ ha hb | branch _ _ _ ha hb =>
    exact and_congr ha hb

/-- Replacing constants by copies preserves compiled code size. -/
theorem size_eq (h : RegisterParameter r v c c') : c'.size = c.size := by
  induction h with
  | same | copy => rfl
  | seq _ _ ha hb => simp only [Code.size, ha, hb]
  | branch _ _ _ ha hb => simp only [Code.size, ha, hb]

/-- Substituting a computed register for an immediate preserves the exact run. -/
theorem exec (h : RegisterParameter r v c c') {W k : ℕ} {x y : Data n}
    (hr : x.regs r = v) (he : Exec W c x y k) : Exec W c' x y k := by
  induction h generalizing x y k with
  | same _ _ => exact he
  | copy d _ =>
    cases he with
    | op ho =>
      obtain ⟨_, hy⟩ := Data.put_eq_some.mp ho
      exact .op (by simpa only [Op.eval_copy, hr] using congrArg some hy)
  | branch cond _ _ iha ihb =>
    cases he with
    | branch_pos hc ha => exact .branch_pos hc (iha hr ha)
    | branch_neg hc hb => exact .branch_neg hc (ihb hr hb)
  | seq ha hb iha ihb =>
    cases he with
    | seq he₁ he₂ =>
      exact .seq (iha hr he₁) (ihb ((he₁.regs_eq ha.preserves).trans hr) he₂)

/-- The same final data and instruction bound hold after parameter substitution. -/
theorem execWithin (h : RegisterParameter r v c c') {W T : ℕ} {x y : Data n}
    (hr : x.regs r = v) (he : ExecWithin W c x y T) : ExecWithin W c' x y T :=
  let ⟨k, hk, he⟩ := he
  ⟨k, hk, h.exec hr he⟩

end Code.RegisterParameter
end Cslib.WordRAM
