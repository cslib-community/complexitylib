/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Assigns
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered
public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Register-machine kernel of the closure loops

The counter code compiled from transitive-closure (FO(TC)) and deterministic-transitive-closure
(FO(DTC)) formulas over the canonical ordered language shares one kernel. It evaluates a term
whose free variables sit in registers, tests whether the current tuple of a closure loop differs
from the target tuple, decodes a base-`n` code into a tuple of registers, and loads the source
tuple of a closure.

## Main definitions

* `Cslib.Logic.FO.Ordered.ClosureKernel.termE`: a term as an expression.
* `Cslib.Logic.FO.Ordered.ClosureKernel.testExpr`: positive exactly when the current tuple
  differs from the target tuple.
* `Cslib.Logic.FO.Ordered.ClosureKernel.digitE`: digit `i` of a base-`n` code.

## Main results

* `Cslib.Logic.FO.Ordered.ClosureKernel.reaches_digitsCode`: decoding a code into a tuple.
* `Cslib.Logic.FO.Ordered.ClosureKernel.reaches_loadCode`: loading the source tuple of a closure.
* `Cslib.Logic.FO.Ordered.ClosureKernel.eval_termE_of_atomic`: a compiled term computes its
  value.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorems 3.1 and 4.2][Immerman1987]
-/

public section

universe u v

open FirstOrder Language
namespace Cslib.Logic.FO.Ordered.ClosureKernel

open Turing Turing.CounterProgram Expr

variable {L : Language.{u, v}} [L.IsRelational]

/-- A term with free variables in registers, as an expression. -/
@[expose] def termE {α : Type*} (fv : α → ℕ) (t : (language L).Term α) : Expr :=
  ModelChecker.termExpr fv 0 (t.relabel (Sum.inl : α → α ⊕ Fin 0))

/-- A term compiled by `termE` computes its value, given correct atomic handlers. -/
theorem eval_termE_of_atomic {v : Vocabulary L} {a : EncodedStructure} [L.Structure (Fin a.1)]
    [Fact (2 ≤ a.1)] {w : List Bool} {α : Type} {fv : α → ℕ} {val : α → Fin a.1}
    (hC : (ModelChecker.atomicCompiler v fv 0).Correct w fv 0 val) {regs : List ℕ}
    (h0 : regs.getD 0 0 = a.1) (hv : ∀ x, regs.getD (fv x) 0 = val x)
    (t : (language L).Term α) : (termE fv t).eval regs = ((t.realize val : Fin a.1) : ℕ) := by
  have := hC.term regs (Fin.elim0 : Fin 0 → Fin a.1) h0 hv (fun i => i.elim0) (t.relabel Sum.inl)
  rw [Term.realize_relabel] at this
  exact this

/-- The test of the closure loop: positive exactly when the current tuple differs from the
target tuple. -/
@[expose] def testExpr (base k : ℕ) (z : Fin k → Expr) : Expr :=
  Expr.sum ((List.finRange k).map fun i : Fin k =>
    add (sub (reg (base + i.val)) (z i)) (sub (z i) (reg (base + i.val))))

theorem lt_eval_testExpr {base k n : ℕ} {z : Fin k → Expr} {regs : List ℕ}
    {us zs : Fin k → Fin n} (hu : ∀ i : Fin k, regs.getD (base + i) 0 = us i)
    (hz : ∀ i : Fin k, (z i).eval regs = zs i) :
    (const 0).eval regs < (testExpr base k z).eval regs ↔ us ≠ zs := by
  rw [Expr.eval_const, Nat.pos_iff_ne_zero, Ne, Ne, not_iff_not, testExpr, Expr.eval_sum,
    List.map_map, List.sum_eq_zero_iff]
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, Function.comp_apply, Expr.eval_add, Expr.eval_sub, Expr.eval_reg,
    hu, hz]
  constructor
  · intro h
    funext i
    exact Fin.ext (by have := h i; omega)
  · rintro rfl i
    omega

/-- With `n` in register `0`, the expression `n ^ k` evaluates to `n ^ k`. -/
theorem eval_pow_reg0 {regs : List ℕ} {n k : ℕ} (h0 : regs.getD 0 0 = n) :
    (pow (reg 0) k).eval regs = n ^ k := by
  simp only [Expr.eval_pow, Expr.eval_reg, h0]

/-- Digit `i` in base `n` (register `0`) of register `r`: the decoding of a code into a tuple. -/
@[expose] def digitE (r i : ℕ) : Expr := Expr.mod (Expr.div (reg r) (pow (reg 0) i)) (reg 0)

/-- With `n` in register `0` and a code `g < n ^ k` in register `r`, `digitE r i` is digit `i` of
the tuple `finFunctionFinEquiv.symm g`. -/
theorem eval_digitE {regs : List ℕ} {r k n : ℕ} (h0 : regs.getD 0 0 = n) (g : Fin (n ^ k))
    (hg : regs.getD r 0 = g) (i : Fin k) :
    (digitE r i).eval regs = finFunctionFinEquiv.symm g i := by
  rw [finFunctionFinEquiv_symm_apply_val]
  simp only [digitE, Expr.eval_mod, Expr.eval_div, Expr.eval_pow, Expr.eval_reg, hg, h0]

/-- Decoding register `r`, holding `g < n ^ k`, into registers `d + i` writes the tuple
`finFunctionFinEquiv.symm g`. -/
theorem reaches_digitsCode {P : CounterProgram} {w : List Bool} {B b r d k n : ℕ}
    (hP : P.CodeAt b (assignsCode b d k (digitE r))) (hrd : r < d ∨ d + k ≤ r) (hd : 0 < d)
    {regs : List ℕ} (hlen : d + k ≤ regs.length) (h0 : regs.getD 0 0 = n)
    (hnB : n ≤ B) (hB : ∀ x ∈ regs, x ≤ B) (g : Fin (n ^ k)) (hg : regs.getD r 0 = g) :
    ∃ regs', P.Reaches w (P.Running B) (b, regs) (b + k, regs') ∧
      regs'.length = regs.length ∧
      (∀ j, (j < d ∨ d + k ≤ j) → regs'.getD j 0 = regs.getD j 0) ∧
      (∀ i : Fin k, regs'.getD (d + i) 0 = finFunctionFinEquiv.symm g i) ∧
      ∀ x ∈ regs', x ≤ B := by
  have hdig : ∀ i : Fin k, (digitE r i).eval regs = finFunctionFinEquiv.symm g i :=
    eval_digitE h0 g hg
  obtain ⟨regs', hr, hlen', hout, hin, hB'⟩ := reaches_assignsCode (w := w) hP hlen
    (fun i hi regs' h => by
      simp only [digitE, Expr.eval_mod, Expr.eval_div, Expr.eval_pow, Expr.eval_reg]
      rw [h r (by omega), h 0 (by omega)]) hB
    (fun i hi => by
      rw [show (digitE r i).eval regs = (digitE r (⟨i, hi⟩ : Fin k)).eval regs from rfl, hdig]
      exact (Fin.isLt _).le.trans hnB)
  exact ⟨regs', hr, hlen', hout, fun i => (hin i i.isLt).trans (hdig i), hB'⟩

/-- Loading the source tuple `s₀` of a closure, denoted by expressions `src` that read only
registers below `base`, into registers `base + i`. -/
theorem reaches_loadCode {P : CounterProgram} {w : List Bool} {B b base k n : ℕ}
    {src : Fin k → Expr} (hP : P.CodeAt b
      (assignsCode b base k (fun i => if h : i < k then src ⟨i, h⟩ else const 0)))
    {regs₀ : List ℕ} (hlen : base + k ≤ regs₀.length) (hnB : n ≤ B) (hB : ∀ x ∈ regs₀, x ≤ B)
    {s₀ : Fin k → Fin n}
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ i, (src i).eval regs = s₀ i) :
    ∃ regs', P.Reaches w (P.Running B) (b, regs₀) (b + k, regs') ∧
      regs'.length = regs₀.length ∧
      (∀ j, (j < base ∨ base + k ≤ j) → regs'.getD j 0 = regs₀.getD j 0) ∧
      (∀ i : Fin k, regs'.getD (base + i) 0 = s₀ i) ∧ ∀ x ∈ regs', x ≤ B := by
  obtain ⟨regs', hr, hlen', hout, hin, hB'⟩ := reaches_assignsCode (w := w) hP hlen
    (fun i hi regs' h => by
      simp only [hi, ↓reduceDIte]
      rw [hsrc regs' (fun j hj => h j (by omega)), hsrc regs₀ (fun _ _ => rfl)]) hB
    (fun i hi => by
      simp only [hi, ↓reduceDIte]
      rw [hsrc regs₀ (fun _ _ => rfl)]
      exact (Fin.isLt _).le.trans hnB)
  refine ⟨regs', hr, hlen', hout, fun i => ?_, hB'⟩
  rw [hin i i.isLt]
  simp only [i.isLt, ↓reduceDIte]
  exact hsrc regs₀ (fun _ _ => rfl) i

private theorem pair_apply_lt {A : Type*} {k : ℕ} (xs ys : Fin k → A) (i : Fin (2 * k))
    (h : (i : ℕ) < k) : TC.pair xs ys i = xs ⟨i, h⟩ := by
  have : Fin.cast (Nat.two_mul k) i = Fin.castAdd k ⟨i, h⟩ := Fin.ext rfl
  simp only [TC.pair, this, Fin.append_left]

private theorem pair_apply_ge {A : Type*} {k : ℕ} (xs ys : Fin k → A) (i : Fin (2 * k))
    (h : k ≤ (i : ℕ)) : TC.pair xs ys i = ys ⟨i - k, by have := i.isLt; omega⟩ := by
  have : Fin.cast (Nat.two_mul k) i = Fin.natAdd k ⟨i - k, by have := i.isLt; omega⟩ :=
    Fin.ext (by simp; omega)
  simp only [TC.pair, this, Fin.append_right]

/-- The pair of a tuple in registers `base + i` and a tuple in registers `base + k + i` is in
registers `base + i`, for `i < 2 * k`. -/
theorem getD_pair {regs : List ℕ} {base k n : ℕ} {us vs : Fin k → Fin n}
    (hu : ∀ i : Fin k, regs.getD (base + i) 0 = us i)
    (hv : ∀ i : Fin k, regs.getD (base + k + i) 0 = vs i) (i : Fin (2 * k)) :
    regs.getD (base + i) 0 = ((TC.pair us vs i : Fin n) : ℕ) := by
  by_cases h : (i : ℕ) < k
  · rw [pair_apply_lt _ _ _ h]; exact hu ⟨i, h⟩
  · rw [pair_apply_ge _ _ _ (by omega), ← hv]
    congr 1
    simp only
    omega

/-- The registers of the extended assignment of an existential body: the new variable in
register `base`, the others in their registers. -/
theorem getD_elim_eq {α : Type} {fv : α → ℕ} {base : ℕ} {regs : List ℕ} {n : ℕ}
    {val : α → Fin n} (hv : ∀ x, regs.getD (fv x) 0 = val x) {c : Fin n}
    (hc : regs.getD base 0 = c) :
    ∀ y : Option α, regs.getD (y.elim base fv) 0 = (Option.elim y c val : Fin n)
  | none => hc
  | some y => hv y

end Cslib.Logic.FO.Ordered.ClosureKernel
