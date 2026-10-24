/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Circuit.Monotone.Basic
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Pi

/-!
# Monotone formulas

A *monotone formula* is a formula over the monotone basis, `Formula Monotone.signature n`,
evaluated under `Monotone.interpretation`: a tree of AND and OR gates of fan-in two whose leaves
are inputs and Boolean constants (`Monotone.const`, `Monotone.and`, `Monotone.or`). Every function
it computes is monotone (`monotone_eval`), and every monotone function has one: the disjunction,
over the inputs `z` where the function is true, of the conjunction of the bits that are one in `z`
(`exists_computes_of_monotone`). Unlike De Morgan formulas, monotone formulas thus compute only
some Boolean functions, so the least depth of a monotone formula for `f` is extended-valued:
`eformulaDepth f`, the least depth with constants free (`Formula.minDepthWith` for `binaryCost`),
is `⊤` when no monotone formula computes `f`, that is, when `f` is not monotone
(`eformulaDepth_ne_top_iff`). A monotone formula is a De Morgan formula (`Formula.mapOp` along
`toDeMorgan`), so the De Morgan formula depth is at most the monotone one
(`formulaDepth_le_eformulaDepth`).

## Main definitions

* `Cslib.Circuits.Monotone.const`, `Cslib.Circuits.Monotone.and`, `Cslib.Circuits.Monotone.or`:
  monotone formulas built from constants and smaller formulas.
* `Cslib.Circuits.Monotone.eformulaDepth`: the least depth of a monotone formula for a function,
  or `⊤` if there is none.

## Main results

* `Cslib.Circuits.Monotone.exists_computes_iff_monotone`: a Boolean function has a monotone
  formula exactly when it is monotone.
* `Cslib.Circuits.Monotone.eformulaDepth_ne_top_iff`: monotone formula depth is finite exactly for
  monotone functions.
* `Cslib.Circuits.Monotone.formulaDepth_le_eformulaDepth`: De Morgan formulas are at most as deep
  as monotone ones.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 7][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

variable {n : ℕ}

/-! ### Constructors -/

section Constructors

variable (F G : Formula signature n) (x : BitString n)

/-- The constant monotone formula. -/
def const (b : Bool) : Formula signature n :=
  .gate (.const b) Fin.elim0

/-- The conjunction of two monotone formulas. -/
def and : Formula signature n :=
  .gate .and ![F, G]

/-- The disjunction of two monotone formulas. -/
def or : Formula signature n :=
  .gate .or ![F, G]

/-- A constant monotone formula `const b` evaluates to `b`. -/
@[simp] theorem eval_const (b : Bool) : (const b : Formula signature n).eval interpretation x = b :=
  rfl

/-- `and F G` evaluates to the Boolean conjunction of the values of `F` and `G`. -/
@[simp] theorem eval_and :
    (and F G).eval interpretation x = (F.eval interpretation x && G.eval interpretation x) :=
  rfl

/-- `or F G` evaluates to the Boolean disjunction of the values of `F` and `G`. -/
@[simp] theorem eval_or :
    (or F G).eval interpretation x = (F.eval interpretation x || G.eval interpretation x) :=
  rfl

/-- A constant monotone formula `const b` has weighted depth `cost (.const b)`. -/
@[simp] theorem depthWith_const (cost : Op → ℕ) (b : Bool) :
    (const b : Formula signature n).depthWith cost = cost (.const b) := by
  simp [const]

/-- The weighted depth of `and F G` is the maximum of the weighted depths of `F` and `G` plus
`cost .and`. -/
@[simp] theorem depthWith_and (cost : Op → ℕ) :
    (and F G).depthWith cost = max (F.depthWith cost) (G.depthWith cost) + cost .and := by
  simp [and, Fin.univ_succ]

/-- The weighted depth of `or F G` is the maximum of the weighted depths of `F` and `G` plus
`cost .or`. -/
@[simp] theorem depthWith_or (cost : Op → ℕ) :
    (or F G).depthWith cost = max (F.depthWith cost) (G.depthWith cost) + cost .or := by
  simp [or, Fin.univ_succ]

end Constructors

/-! ### Monotone functions -/

/-- Monotone formulas compute monotone functions. -/
theorem monotone_eval (F : Formula signature n) : Monotone (F.eval interpretation) := by
  induction F with
  | input i => exact fun _ _ h => h i
  | gate op args ih => exact fun _ _ h => interpretation_mono op fun j => ih j h

variable {f : BooleanFunction n}

/-- Every monotone function has a monotone formula: the disjunction, over the inputs `z` where it
is true, of the conjunction of the bits that are one in `z`. -/
theorem exists_computes_of_monotone (hf : Monotone f) :
    ∃ F : Formula signature n, F.Computes interpretation f := by
  classical
  have hconj (s : Finset (Fin n)) : ∃ F : Formula signature n,
      F.Computes interpretation fun x => decide (∀ i ∈ s, x i = true) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨const true, fun x => by simp⟩
    | insert i s _ ih =>
      obtain ⟨F, hF⟩ := ih
      exact ⟨and (.input i) F, fun x => by simp [hF x]⟩
  have hdisj (T : Finset (BitString n)) : ∃ F : Formula signature n,
      F.Computes interpretation fun x => decide (∃ z ∈ T, ∀ i, z i = true → x i = true) := by
    induction T using Finset.induction_on with
    | empty => exact ⟨const false, fun x => by simp⟩
    | insert z T _ ih =>
      obtain ⟨F, hF⟩ := ih
      obtain ⟨G, hG⟩ := hconj {i | z i = true}
      exact ⟨or G F, fun x => by simp [hF x, hG x]⟩
  obtain ⟨F, hF⟩ := hdisj {z | f z = true}
  refine ⟨F, fun x => (hF x).trans ?_⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun ⟨z, hz, hzx⟩ => ?_, fun hx => ⟨x, hx, fun _ h => h⟩⟩
  exact Bool.eq_true_of_true_le (hz ▸ hf fun i => Bool.le_iff_imp.2 (hzx i))

/-- A Boolean function has a monotone formula exactly when it is monotone. -/
theorem exists_computes_iff_monotone :
    (∃ F : Formula signature n, F.Computes interpretation f) ↔ Monotone f :=
  ⟨fun ⟨F, hF⟩ => Formula.computes_iff.1 hF ▸ monotone_eval F, exists_computes_of_monotone⟩

/-! ### Depth -/

/-- The least depth of a monotone formula computing `f`, with constants free, or `⊤` if no
monotone formula computes `f`: the least depth with costs `binaryCost` (`Formula.minDepthWith`),
whose API applies to it. -/
noncomputable abbrev eformulaDepth (f : BooleanFunction n) : ℕ∞ :=
  Formula.minDepthWith interpretation binaryCost f

/-- The monotone formula depth of a function is finite exactly when the function is monotone. -/
theorem eformulaDepth_ne_top_iff : eformulaDepth f ≠ ⊤ ↔ Monotone f :=
  Formula.minDepthWith_ne_top_iff.trans exists_computes_iff_monotone

/-- A monotone formula is a De Morgan formula of the same depth, so De Morgan formulas are at most
as deep as monotone ones. -/
theorem formulaDepth_le_eformulaDepth (f : BooleanFunction n) :
    (Boolean.formulaDepth f : ℕ∞) ≤ eformulaDepth f :=
  Formula.le_minDepthWith_iff.2 fun F hF => by
    have h := Boolean.formulaDepth_le (hF.mapOp (φ := toDeMorgan))
    rw [Formula.depthWith_mapOp] at h
    exact_mod_cast h.trans_eq (congrArg F.depthWith (funext binaryCost_toDeMorgan))

end Cslib.Circuits.Monotone
