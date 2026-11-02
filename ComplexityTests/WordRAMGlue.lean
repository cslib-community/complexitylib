/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import Complexity.Computability.WordRAM.Glue
import ComplexityTests.WordRAMGlueNamed
meta import Mathlib.Tactic.FunProp.Decl

/-! Concrete word-glue clients. `WordRAMBasis` separately pins the underlying basis semantics. -/

public section

namespace ComplexityTests.WordRAMGlue

open Cslib.WordRAM

-- The property must be indexed by the scalar function, not the admissibility predicate.
run_cmd Lean.Elab.Command.liftTermElabM do
  let goal ← Lean.Elab.Term.elabTerm (← `(GlueComputable .exact
    (fun v : Fin 1 → ℕ => v 0 + 1) (fun v => v 0 ≤ 10) (fun _ => 11))) none
  let some decl ← Mathlib.Meta.FunProp.getFunPropDecl? goal
    | throwError "GlueComputable was not registered"
  unless decl.funArgId == 2 do throwError "wrong GlueComputable function index"
  let some f ← Mathlib.Meta.FunProp.getFunPropFun? goal
    | throwError "GlueComputable function was not found"
  let expected ← Lean.Elab.Term.elabTerm (← `(fun v : Fin 1 → ℕ => v 0 + 1)) none
  unless ← Lean.Meta.isDefEq f expected do throwError "indexed P or the bound instead of f"

-- Costs are explicit and separate from the automation facade: two copies and one addition.
example : GlueComputes .exact (fun v : Fin 2 → ℕ => v 0 + v 1 ≤ 100)
    (fun v => v 0 + v 1) (fun _ => 100) 3 := by
  apply GlueComputes.bin_exact (GlueComputes.proj 0 ?_) (GlueComputes.proj 1 ?_) .add
  · intros; rfl
  all_goals intros; (try dsimp [BinOp.eval, Function.comp_def] at *); omega

-- A larger advertised bound is discharged once, outside fun_prop's rule search.
example : GlueComputes .exact (fun v : Fin 2 → ℕ => v 0 + v 1 ≤ 100)
    (fun v => v 0 + v 1) (fun _ => 200) 10 := by
  have h : GlueComputes .exact (fun v : Fin 2 → ℕ => v 0 + v 1 ≤ 100)
      (fun v => v 0 + v 1) (fun _ => 100) 3 := by
    apply GlueComputes.bin_exact (GlueComputes.proj 0 ?_) (GlueComputes.proj 1 ?_) .add
    · intros; rfl
    all_goals intros; (try dsimp [BinOp.eval, Function.comp_def] at *); omega
  exact h.mono (by intros; omega) (by omega)

-- Ordinary arithmetic closure needs no intermediate machine assertions or cost metavariables.
example : GlueComputable .exact (fun v => (v 0 + v 1) + v 2)
    (fun v : Fin 3 → ℕ => v 0 + v 1 + v 2 ≤ 100)
    (fun _ => 100) := by
  fun_prop (disch := intros; (try dsimp [BinOp.eval, Function.comp_def] at *); omega)

example : GlueComputable .standard (fun v => v 0 + v 1)
    (fun v : Fin 2 → ℕ => v 0 + v 1 ≤ 100)
    (fun _ => 100) := by
  fun_prop (disch := intros; (try dsimp [BinOp.eval, Function.comp_def] at *); omega)

-- Exact subtraction uses the domain, rather than totalizing an underflow.
example : GlueComputable .exact (fun v => (v 0 - v 1) / 2)
    (fun v : Fin 2 → ℕ => v 1 ≤ v 0 ∧ v 0 ≤ 100)
    (fun _ => 100) := by
  fun_prop (disch := intros; (try dsimp [BinOp.eval, Function.comp_def] at *); omega)

-- The nonselected branch is allowed to be invalid on the other branch's input domain.
example : GlueComputable .exact (fun v => if v 0 < v 1 then v 1 - v 0 else v 0 - v 1)
    (fun v : Fin 2 → ℕ => v 0 ≤ 100 ∧ v 1 ≤ 100)
    (fun _ => 100) := by
  fun_prop (disch := intros; (try dsimp [BinOp.eval, Function.comp_def] at *); omega)

-- At zero, division is not evaluated. The other branch's domain supplies a nonzero divisor.
example : GlueComputable .exact (fun v => if v 0 = v 1 then 0 else 7 / v 0)
    (fun v : Fin 2 → ℕ => v 0 ≤ 100 ∧ v 1 = 0) (fun _ => 100) := by
  fun_prop (disch := intro v hv; have := Nat.div_le_self 7 (v 0); omega)

-- Repeated source registers are supported by layout substitution, without injectivity of ρ.
example : GlueComputes .exact (fun v : Fin 1 → ℕ => 2 * v 0 ≤ 100)
    (fun v => v 0 + v 0) (fun _ => 100) 3 := by
  have h : GlueComputes .exact (fun v : Fin 2 → ℕ => v 0 + v 1 ≤ 100)
      (fun v => v 0 + v 1) (fun _ => 100) 3 := by
    apply GlueComputes.bin_exact (GlueComputes.proj 0 ?_) (GlueComputes.proj 1 ?_) .add
    · intros; rfl
    all_goals intros; (try dsimp [BinOp.eval, Function.comp_def] at *); omega
  exact h.reindex (fun _ => 0)
    (by intros; (try dsimp [BinOp.eval, Function.comp_def] at *); omega) (by intros; rfl)

-- This function's body is opaque in this importing module. Composition reuses its certificate.
example : GlueComputable .exact (fun v => WordRAMGlueNamed.twice (v 0 + v 1))
    (fun v : Fin 2 → ℕ => 2 * (v 0 + v 1) ≤ 100)
    (fun _ => 100) := by
  have ht := WordRAMGlueNamed.twice_glue
  fun_prop (disch := intros; omega)

-- Both arguments are computed locals. The outer two-input routine is opaque here; the
-- forest rule must stage both values and preserve the input/frame automatically.
example : GlueComputable .exact
    (fun v => WordRAMGlueNamed.weighted ![v 0 + 1, v 1 + v 1])
    (fun v : Fin 2 → ℕ => v 0 + 1 + 4 * v 1 ≤ 100) (fun _ => 100) := by
  have hw := WordRAMGlueNamed.weighted_glue
  fun_prop (disch := intros; (try dsimp at *); omega)

example : WordRAMGlueNamed.weighted ![(2 : ℕ) + 1, 3 + 3] = 15 :=
  WordRAMGlueNamed.weighted_three_six

-- Empty substitution executes only the outer constant routine, with no staging overhead.
example : GlueComputes .exact (fun _ : Fin 1 → ℕ => True)
    (fun _ => 7) (fun _ => 7) 1 := by
  have hf : GlueComputes .exact (fun _ : Fin 0 → ℕ => True)
      (fun _ => 7) (fun _ => 7) 1 := GlueComputes.const 7 (by intros; rfl)
  have hg : ∀ i : Fin 0, GlueComputes .exact (fun _ : Fin 1 → ℕ => True)
      (fun _ => Fin.elim0 i) (fun _ => 7) (Fin.elim0 i) := fun i => Fin.elim0 i
  exact hf.comp_many hg (by intros; trivial) (by intros; rfl)

/-- The certificate supplies one actual finite code before the initial memory is chosen. -/
theorem concrete_code : ∃ n, ∃ code : Code .exact (2 + (n + 1)), code.IsGlue ∧
    ∀ mem : ℕ → ℕ, ∃ y,
      ExecWithin 4 code ⟨Fin.addCases ![2, 3] (fun _ => 0), mem⟩ y 3 ∧
      y.regs (Fin.natAdd 2 0) = 5 ∧ y.mem = mem ∧
      y.regs (Fin.castAdd (n + 1) 0) = 2 ∧ y.regs (Fin.castAdd (n + 1) 1) = 3 := by
  have h : GlueComputes .exact (fun v : Fin 2 → ℕ => v 0 + v 1 ≤ 10)
      (fun v => v 0 + v 1) (fun _ => 10) 3 := by
    apply GlueComputes.bin_exact (GlueComputes.proj 0 ?_) (GlueComputes.proj 1 ?_) .add
    · intros; rfl
    all_goals intros; (try dsimp [BinOp.eval] at *); omega
  obtain ⟨n, code, hg, hrun⟩ := h.realize
  refine ⟨n, code, hg, ?_⟩
  intro mem
  obtain ⟨y, hy, ho, hm, hi⟩ := hrun 4 ![2, 3] mem (by decide) (by decide)
  exact ⟨y, hy, ho, hm, hi 0, hi 1⟩

-- A zero envelope cannot hide a positive returned word, including at width zero.
example : ¬GlueComputable .exact (fun _ => 1) (fun _ : Fin 0 → ℕ => True) (fun _ => 0) := by
  rintro ⟨_, h⟩
  have hh := h.1 Fin.elim0 trivial
  exact Nat.not_succ_le_zero 0 hh

-- Existing Code.eval makes failure independent of fuel exhaustion for this loop-free code.
private def sample (a b : ℕ) : Data 4 := ⟨![a, b, 0, 0], fun _ => 17⟩

example : (Code.op (Op.const (B := .exact) (2 : Fin 4) 0)).eval 0 0 (sample 0 0) =
    some ((sample 0 0).set 2 0, 1) := rfl

example : (Code.op (Op.const (B := .exact) (2 : Fin 4) 1)).eval 0 0 (sample 0 0) =
    none := by decide

example : (Code.op (Op.exactBin .sub (2 : Fin 4) 0 1)).eval 4 0 (sample 3 5) =
    none := by decide

example : (Code.op (Op.exactBin .div (2 : Fin 4) 0 1)).eval 4 0 (sample 7 0) =
    none := by decide

example : (Code.op (Op.exactBin .mod (2 : Fin 4) 0 1)).eval 4 0 (sample 7 0) =
    none := by decide

-- Fitting inputs and fitting final mathematical value do not imply intermediate fit.
example : (Code.seq (.op (.exactBin .add (2 : Fin 4) 0 1))
    (.op (.exactBin .sub 2 2 1))).eval 3 0 (sample 7 1) = none := by decide

-- A lazy branch avoids an exact zero-divisor fault and charges the actual branch overhead.
private def lazyDivide : Code .exact 4 :=
  .branch (.eq 0 1) (.op (.const 2 0)) (.op (.exactBin .div 2 3 0))

example : lazyDivide.eval 3 0 ⟨![0, 0, 0, 7], fun _ => 17⟩ =
    some ((⟨![0, 0, 0, 7], fun _ => 17⟩ : Data 4).set 2 0, 2) := rfl

example : lazyDivide.eval 3 0 ⟨![2, 0, 0, 7], fun _ => 17⟩ =
    some ((⟨![2, 0, 0, 7], fun _ => 17⟩ : Data 4).set 2 3, 3) := rfl

end ComplexityTests.WordRAMGlue
