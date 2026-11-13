/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.ToBoolean
public import CslibFrontier.Logics.Propositional.CSP.ToCNF
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.Nat.Div
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Maximum constraint satisfaction problems (`Max-CSP`)

This module defines unweighted and weighted maximum constraint satisfaction problems (`Max-CSP`)
over arbitrary relation alphabets `Rel`, variable types `V`, and finite inhabited domains `D`,
using documented structures (`MaxCSPInstance`, `WeightedConstraint`,
`WeightedMaxCSP`), together with three exact semantic bridges:

1. **CNF / `MaxSAT` embedding (`clauseSem`, `Constraint.ofClause`, `MaxCSPInstance.ofCNF`):**
   views any CNF formula on `numVars` declared variables as a Boolean `MaxCSPInstance (List Bool) V`
   preserving variable occurrences, per-assignment scores, threshold counts, and optima.
2. **Forbidden-pattern Boolean `CSP → CNF` compilation (`countP_eval_toCNF_add_length`,
   `optimum_ofCNF_toCNF_add_length`):** proves that for every assignment `σ : V → Bool`, a
   constraint falsified by `σ` falsifies *exactly one* clause of `Constraint.toCNF sem c` while a
   satisfied constraint falsifies *zero* clauses, yielding the exact affine identity
   `(F.constraints.toCNF sem).countP (Clause.eval σ) + F.constraints.length =
     (F.constraints.toCNF sem).length + F.evalCount sem σ`
   with zero auxiliary variables and preserved width bound `≤ k`.
3. **Clamped binary finite-domain compilation (`clampedSem`, `MaxCSPInstance.toClampedBoolean`,
   `WeightedMaxCSP.toClampedBoolean`):** compiles any finite-domain `Max-CSP` over `Fin q` (`0 < q`)
   on `N` declared variables with all occurring variables below `N` (`∀ v ∈ F.vars, v < F.numVars`)
   to a Boolean `Max-CSP` on `N * CSP.bitWidth q` variables with the exact same number of
   constraints and identical optimum, without auxiliary penalty weights.

## Main definitions

* `Cslib.Logic.PL.MaxCSPInstance`: unweighted `Max-CSP` instances, a `CSP` with a declared
  variable count.
* `Cslib.Logic.PL.WeightedConstraint`, `Cslib.Logic.PL.WeightedMaxCSP`: weighted constraints and
  `Max-CSP` instances over an additive weight type `W`.
* `Cslib.Logic.PL.MaxCSP.assignment`: canonical extension of `Fin n → D` to `ℕ → D` via `default`.
* `Cslib.Logic.PL.MaxCSPInstance.score`, `Cslib.Logic.PL.MaxCSPInstance.thresholdCount`,
  `Cslib.Logic.PL.MaxCSPInstance.optimum`: unweighted score, cutoff count, and maximum score.
* `Cslib.Logic.PL.WeightedMaxCSP.score`, `Cslib.Logic.PL.WeightedMaxCSP.optimum`: weighted score
  and maximum score.
* `Cslib.Logic.PL.MaxCSP.clauseSem`, `Cslib.Logic.PL.MaxCSPInstance.ofCNF`: CNF-to-`Max-CSP` bridge.
* `Cslib.Logic.PL.MaxCSP.clampedSem`, `Cslib.Logic.PL.MaxCSPInstance.toClampedBoolean`:
  finite-domain `Fin q` to Boolean `Max-CSP` compilation.

## Main results

* `Cslib.Logic.PL.MaxCSPInstance.score_ofCNF`, `Cslib.Logic.PL.MaxCSPInstance.optimum_ofCNF`:
  exact agreement between CNF clause-satisfaction counts and `MaxCSPInstance.ofCNF`.
* `Cslib.Logic.PL.MaxCSP.countP_eval_toCNF_add_length`,
  `Cslib.Logic.PL.MaxCSPInstance.optimum_ofCNF_toCNF_add_length`: exact affine score and optimum
  preservation under forbidden-pattern `CSP.toCNF` compilation.
* `Cslib.Logic.PL.MaxCSPInstance.optimum_toClampedBoolean`,
  `Cslib.Logic.PL.WeightedMaxCSP.optimum_toClampedBoolean`: exact optimum preservation from `Fin q`
  (`0 < q`) to Boolean `Max-CSP` when every occurring variable is below `F.numVars`.
-/

public section

namespace Cslib.Logic.PL

open Cslib.BitString

/-! ### Unweighted `Max-CSP` structures and semantics -/

/-- An unweighted maximum constraint satisfaction instance declaring `numVars` variables and a list
of `constraints` counted with multiplicity. -/
@[ext]
structure MaxCSPInstance (Rel V : Type*) where
  /-- Number of declared variables (`0, …, numVars - 1` when `V = ℕ`). -/
  numVars : ℕ
  /-- Constraints of the instance, counted with multiplicity. -/
  constraints : CSP Rel V
  deriving DecidableEq, Repr

namespace MaxCSP

/-- Extend a finite declared assignment `x : Fin n → D` to `ℕ → D` by returning `default` outside
`0, …, n - 1`. At `D = Bool`, this agrees definitionally with `MaxSAT.assignment`. -/
@[expose] def assignment {D : Type*} [Inhabited D] (n : ℕ) (x : Fin n → D) (v : ℕ) : D :=
  if hv : v < n then x ⟨v, hv⟩ else default

@[simp]
theorem assignment_lt {D : Type*} [Inhabited D] {n : ℕ} (x : Fin n → D) {v : ℕ} (hv : v < n) :
    assignment n x v = x ⟨v, hv⟩ := by
  simp only [assignment, hv, ↓reduceDIte]

theorem assignment_ge {D : Type*} [Inhabited D] {n : ℕ} (x : Fin n → D) {v : ℕ} (hv : ¬ v < n) :
    assignment n x v = default := by
  simp only [assignment, hv, ↓reduceDIte]

end MaxCSP

namespace MaxCSPInstance

variable {Rel V D : Type*}

/-- Variable occurrences across all constraint scopes in order. -/
@[expose] def vars (F : MaxCSPInstance Rel V) : List V :=
  F.constraints.vars

/-- Structural size: total variable occurrences plus number of constraints. -/
@[expose] def workSize (F : MaxCSPInstance Rel V) : ℕ :=
  F.vars.length + F.constraints.length

/-- Number of constraints in `F` satisfied by an arbitrary assignment `σ : V → D`. -/
@[expose] def evalCount (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel V) (σ : V → D) : ℕ :=
  F.constraints.countP (Constraint.eval sem σ)

theorem evalCount_le (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel V) (σ : V → D) :
    F.evalCount sem σ ≤ F.constraints.length :=
  List.countP_le_length

theorem evalCount_congr {sem : Rel → List D → Bool} {F : MaxCSPInstance Rel V} {σ τ : V → D}
    (h : ∀ v ∈ F.vars, σ v = τ v) :
    F.evalCount sem σ = F.evalCount sem τ :=
  List.countP_congr fun c hc => by
    rw [c.eval_congr fun v hv => h v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)]

/-- Number of satisfied constraints under a declared assignment `x : Fin F.numVars → D`. -/
@[expose] def score [Inhabited D] (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel ℕ)
    (x : Fin F.numVars → D) : ℕ :=
  F.evalCount sem (MaxCSP.assignment F.numVars x)

/-- Number of declared assignments `x : Fin F.numVars → D` achieving score at least `q`. -/
@[expose] def thresholdCount [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) (q : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin F.numVars → D => q ≤ F.score sem x).card

/-- Maximum number of simultaneously satisfied constraints over `x : Fin F.numVars → D`. -/
@[expose] def optimum [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) : ℕ :=
  Finset.univ.sup (F.score sem)

theorem score_le [Inhabited D] (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel ℕ)
    (x : Fin F.numVars → D) :
    F.score sem x ≤ F.constraints.length :=
  F.evalCount_le sem _

theorem score_le_optimum [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) (x : Fin F.numVars → D) :
    F.score sem x ≤ F.optimum sem :=
  Finset.le_sup (Finset.mem_univ x)

theorem exists_score_eq_optimum [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) :
    ∃ x : Fin F.numVars → D, F.score sem x = F.optimum sem := by
  obtain ⟨x, _, hx⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin F.numVars → D))
      Finset.univ_nonempty (F.score sem)
  exact ⟨x, hx.symm⟩

theorem optimum_le [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) :
    F.optimum sem ≤ F.constraints.length :=
  Finset.sup_le fun x _ => F.score_le sem x

theorem thresholdCount_pos_iff [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) (q : ℕ) :
    0 < F.thresholdCount sem q ↔ ∃ x : Fin F.numVars → D, q ≤ F.score sem x := by
  simp only [thresholdCount, Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_univ,
    true_and]

theorem thresholdCount_pos_iff_le_optimum [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) (q : ℕ) :
    0 < F.thresholdCount sem q ↔ q ≤ F.optimum sem := by
  rw [thresholdCount_pos_iff]
  refine ⟨fun ⟨x, hx⟩ => hx.trans (F.score_le_optimum sem x), fun hq => ?_⟩
  obtain ⟨x, hx⟩ := F.exists_score_eq_optimum sem
  exact ⟨x, hx ▸ hq⟩

end MaxCSPInstance

/-! ### Weighted `Max-CSP` structures and semantics -/

/-- A weighted constraint pairing a relation symbol `rel`, variable `scope`, and `weight`. -/
@[ext]
structure WeightedConstraint (Rel V W : Type*) where
  /-- The relation symbol applied to the constraint scope. -/
  rel : Rel
  /-- The ordered list of variables read by the constraint. -/
  scope : List V
  /-- The weight earned when the constraint is satisfied. -/
  weight : W
  deriving DecidableEq, Repr

namespace WeightedConstraint

variable {Rel V W D : Type*}

/-- Weight contributed by `c` under assignment `σ`: `c.weight` when satisfied and `0` otherwise. -/
@[expose] def evalWeight [Zero W] (sem : Rel → List D → Bool) (σ : V → D)
    (c : WeightedConstraint Rel V W) : W :=
  if sem c.rel (c.scope.map σ) then c.weight else 0

/-- Map a function across the weight field of a constraint. -/
@[expose] def mapWeight {W' : Type*} (f : W → W') (c : WeightedConstraint Rel V W) :
    WeightedConstraint Rel V W' :=
  ⟨c.rel, c.scope, f c.weight⟩

theorem evalWeight_congr [Zero W] {sem : Rel → List D → Bool} {c : WeightedConstraint Rel V W}
    {σ τ : V → D} (h : ∀ v ∈ c.scope, σ v = τ v) :
    c.evalWeight sem σ = c.evalWeight sem τ := by
  simp only [evalWeight, List.map_congr_left h]

end WeightedConstraint

/-- A weighted maximum constraint satisfaction instance with `numVars` declared variables and a list
of weighted `constraints`. -/
@[ext]
structure WeightedMaxCSP (Rel V W : Type*) where
  /-- Number of declared variables. -/
  numVars : ℕ
  /-- Weighted constraints of the instance. -/
  constraints : List (WeightedConstraint Rel V W)
  deriving DecidableEq, Repr

namespace WeightedMaxCSP

variable {Rel V W D : Type*}

/-- Variable occurrences across all weighted constraint scopes in order. -/
@[expose] def vars (F : WeightedMaxCSP Rel V W) : List V :=
  F.constraints.flatMap WeightedConstraint.scope

/-- Map a function across all constraint weights. -/
@[expose] def mapWeight {W' : Type*} (f : W → W') (F : WeightedMaxCSP Rel V W) :
    WeightedMaxCSP Rel V W' :=
  ⟨F.numVars, F.constraints.map (WeightedConstraint.mapWeight f)⟩

/-- Total weight of satisfied constraints under an arbitrary assignment `σ : V → D`. -/
@[expose] def evalScore [AddCommMonoid W] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel V W) (σ : V → D) : W :=
  (F.constraints.map (WeightedConstraint.evalWeight sem σ)).sum

/-- Total weight of satisfied constraints under a declared assignment `x : Fin F.numVars → D`. -/
@[expose] def score [Inhabited D] [AddCommMonoid W] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel ℕ W) (x : Fin F.numVars → D) : W :=
  F.evalScore sem (MaxCSP.assignment F.numVars x)

/-- Maximum total weight over all declared assignments `x : Fin F.numVars → D`. Defined via
`Finset.sup'` so no `OrderBot` assumption is needed (covering `ℝ` and `ℚ` as well as `ℕ`). -/
@[expose] def optimum [Fintype D] [Inhabited D] [AddCommMonoid W] [LinearOrder W]
    (sem : Rel → List D → Bool) (F : WeightedMaxCSP Rel ℕ W) : W :=
  Finset.univ.sup' Finset.univ_nonempty (F.score sem)

theorem score_le_optimum [Fintype D] [Inhabited D] [AddCommMonoid W] [LinearOrder W]
    (sem : Rel → List D → Bool) (F : WeightedMaxCSP Rel ℕ W) (x : Fin F.numVars → D) :
    F.score sem x ≤ F.optimum sem :=
  Finset.le_sup' (F.score sem) (Finset.mem_univ x)

theorem exists_score_eq_optimum [Fintype D] [Inhabited D] [AddCommMonoid W] [LinearOrder W]
    (sem : Rel → List D → Bool) (F : WeightedMaxCSP Rel ℕ W) :
    ∃ x : Fin F.numVars → D, F.score sem x = F.optimum sem := by
  obtain ⟨x, _, hx⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin F.numVars → D)) (F.score sem)
  exact ⟨x, hx.symm⟩

theorem optimum_le_of_forall [Fintype D] [Inhabited D] [AddCommMonoid W] [LinearOrder W]
    {sem : Rel → List D → Bool} {F : WeightedMaxCSP Rel ℕ W} {B : W}
    (hB : ∀ x : Fin F.numVars → D, F.score sem x ≤ B) :
    F.optimum sem ≤ B :=
  Finset.sup'_le Finset.univ_nonempty _ fun x _ => hB x

theorem evalScore_congr [AddCommMonoid W] {sem : Rel → List D → Bool}
    {F : WeightedMaxCSP Rel V W} {σ τ : V → D} (h : ∀ v ∈ F.vars, σ v = τ v) :
    F.evalScore sem σ = F.evalScore sem τ := by
  simp only [evalScore]
  congr 1
  exact List.map_congr_left fun c hc =>
    c.evalWeight_congr fun v hv => h v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)

end WeightedMaxCSP

namespace MaxCSPInstance

variable {Rel V D : Type*}

/-- View an unweighted `MaxCSPInstance` as a unit-weight `WeightedMaxCSP` over `ℕ`. -/
@[expose] def toWeighted (F : MaxCSPInstance Rel V) : WeightedMaxCSP Rel V ℕ :=
  ⟨F.numVars, F.constraints.map fun c => ⟨c.rel, c.scope, 1⟩⟩

/-- View an unweighted `MaxCSPInstance` as a unit-weight `WeightedMaxCSP` over `ℝ`. -/
@[expose] def toRealWeighted (F : MaxCSPInstance Rel V) : WeightedMaxCSP Rel V ℝ :=
  ⟨F.numVars, F.constraints.map fun c => ⟨c.rel, c.scope, 1⟩⟩

@[simp]
theorem evalScore_toWeighted (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel V) (σ : V → D) :
    F.toWeighted.evalScore sem σ = F.evalCount sem σ := by
  rcases F with ⟨n, cs⟩
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [toWeighted, WeightedMaxCSP.evalScore, List.map_cons, List.sum_cons,
      WeightedConstraint.evalWeight, evalCount, List.countP_cons, Constraint.eval] at ih ⊢
    rw [ih]
    by_cases h : sem c.rel (c.scope.map σ) = true <;> simp only [h, ↓reduceIte] <;> omega

@[simp]
theorem score_toWeighted [Inhabited D] (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel ℕ)
    (x : Fin F.numVars → D) :
    F.toWeighted.score sem x = F.score sem x :=
  F.evalScore_toWeighted sem (MaxCSP.assignment F.numVars x)

@[simp]
theorem optimum_toWeighted [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) :
    F.toWeighted.optimum sem = F.optimum sem := by
  simp only [WeightedMaxCSP.optimum, Finset.sup'_eq_sup, optimum]
  exact Finset.sup_congr rfl fun x _ => F.score_toWeighted sem x

@[simp]
theorem evalScore_toRealWeighted (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel V)
    (σ : V → D) :
    F.toRealWeighted.evalScore sem σ = (F.evalCount sem σ : ℝ) := by
  rcases F with ⟨n, cs⟩
  induction cs with
  | nil => simp only [toRealWeighted, WeightedMaxCSP.evalScore, List.map_nil, List.sum_nil,
      evalCount, List.countP_nil, Nat.cast_zero]
  | cons c cs ih =>
    simp only [toRealWeighted, WeightedMaxCSP.evalScore, List.map_cons, List.sum_cons,
      WeightedConstraint.evalWeight, evalCount, List.countP_cons, Constraint.eval] at ih ⊢
    rw [ih]
    by_cases h : sem c.rel (c.scope.map σ) = true <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;>
      ring

@[simp]
theorem score_toRealWeighted [Inhabited D] (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel ℕ)
    (x : Fin F.numVars → D) :
    F.toRealWeighted.score sem x = (F.score sem x : ℝ) :=
  F.evalScore_toRealWeighted sem (MaxCSP.assignment F.numVars x)

@[simp]
theorem optimum_toRealWeighted [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) :
    F.toRealWeighted.optimum sem = (F.optimum sem : ℝ) := by
  apply le_antisymm
  · refine WeightedMaxCSP.optimum_le_of_forall fun x => ?_
    let x' : Fin F.numVars → D := x
    exact (F.score_toRealWeighted sem x').le.trans (Nat.cast_le.mpr (F.score_le_optimum sem x'))
  · obtain ⟨x, hx⟩ := F.exists_score_eq_optimum sem
    rw [← hx, ← F.score_toRealWeighted]
    exact F.toRealWeighted.score_le_optimum sem x

end MaxCSPInstance

/-! ### Bridge 1: CNF formulas as `Max-CSP` instances -/

namespace MaxCSP

/-- Disjunctive clause semantics over `Rel = List Bool`: a polarity list `polarities` holds on
`values` when some paired entry agrees (`p.1 == p.2`). -/
@[expose] def clauseSem (polarities values : List Bool) : Bool :=
  (polarities.zip values).any fun p => p.1 == p.2

end MaxCSP

/-- View a CNF clause `c : Clause V` as a `Constraint (List Bool) V` whose relation symbol lists
its literal polarities and whose scope lists its variable references. -/
@[expose] def Constraint.ofClause {V : Type*} (c : Clause V) : Constraint (List Bool) V :=
  ⟨c.map Prod.snd, c.map Prod.fst⟩

@[simp]
theorem Constraint.eval_ofClause {V : Type*} (σ : V → Bool) (c : Clause V) :
    (ofClause c).eval MaxCSP.clauseSem σ = Clause.eval σ c := by
  induction c with
  | nil => rfl
  | cons l cs ih =>
    rcases l with ⟨v, b⟩
    simp only [ofClause, eval, MaxCSP.clauseSem, List.map_cons, List.zip_cons_cons, List.any_cons,
      Clause.eval_cons, Literal.eval_mk] at ih ⊢
    rw [ih, Bool.beq_comm]

/-- View a CNF formula `φ : CNF V` with `numVars` declared variables as a `MaxCSPInstance`. -/
@[expose] def MaxCSPInstance.ofCNF {V : Type*} (numVars : ℕ) (φ : CNF V) :
    MaxCSPInstance (List Bool) V :=
  ⟨numVars, φ.map Constraint.ofClause⟩

namespace MaxCSPInstance

variable {V : Type*}

@[simp]
theorem length_constraints_ofCNF (numVars : ℕ) (φ : CNF V) :
    (ofCNF numVars φ).constraints.length = φ.length := by
  simp only [ofCNF, List.length_map]

@[simp]
theorem vars_ofCNF (numVars : ℕ) (φ : CNF V) :
    (ofCNF numVars φ).vars = φ.vars := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [ofCNF, vars, CSP.vars, List.map_cons, List.flatMap_cons, Constraint.ofClause,
      CNF.vars, List.flatten_cons, List.map_append] at ih ⊢
    rw [ih]

@[simp]
theorem workSize_ofCNF (numVars : ℕ) (φ : CNF V) :
    (ofCNF numVars φ).workSize = φ.vars.length + φ.length := by
  simp only [workSize, vars_ofCNF, length_constraints_ofCNF]

@[simp]
theorem evalCount_ofCNF (numVars : ℕ) (φ : CNF V) (σ : V → Bool) :
    (ofCNF numVars φ).evalCount MaxCSP.clauseSem σ = φ.countP (Clause.eval σ) := by
  simp only [ofCNF, evalCount, List.countP_map, Function.comp_def, Constraint.eval_ofClause]

@[simp]
theorem score_ofCNF (numVars : ℕ) (φ : CNF ℕ) (x : BitString numVars) :
    (ofCNF numVars φ).score MaxCSP.clauseSem x =
      φ.countP (Clause.eval (MaxCSP.assignment numVars x)) :=
  evalCount_ofCNF numVars φ (MaxCSP.assignment numVars x)

theorem thresholdCount_ofCNF (numVars : ℕ) (φ : CNF ℕ) (q : ℕ) :
    (ofCNF numVars φ).thresholdCount MaxCSP.clauseSem q =
      (Finset.univ.filter fun x : BitString numVars =>
        q ≤ φ.countP (Clause.eval (MaxCSP.assignment numVars x))).card := by
  simp only [thresholdCount]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  let x' : BitString numVars := x
  change q ≤ (ofCNF numVars φ).score MaxCSP.clauseSem x' ↔ _
  rw [score_ofCNF]

theorem optimum_ofCNF (numVars : ℕ) (φ : CNF ℕ) :
    (ofCNF numVars φ).optimum MaxCSP.clauseSem =
      Finset.univ.sup fun x : BitString numVars =>
        φ.countP (Clause.eval (MaxCSP.assignment numVars x)) :=
  Finset.sup_congr rfl fun x _ => score_ofCNF numVars φ x

end MaxCSPInstance

/-! ### Bridge 2: Exact affine score shift under forbidden-pattern `CSP.toCNF` compilation -/

namespace MaxCSP

private theorem nodup_enumList (n : ℕ) : (enumList n).Nodup :=
  (nodup_enum n).map List.ofFn_injective

/-- For every Boolean constraint `c` and assignment `σ`, `c.toCNF sem` has all clauses satisfied
when `c` holds under `σ`, and all-but-one clauses satisfied when `c` fails under `σ`. -/
theorem countP_eval_constraintToCNF_add_one {Rel V : Type*} (sem : Rel → List Bool → Bool)
    (c : Constraint Rel V) (σ : V → Bool) :
    (c.toCNF sem).countP (Clause.eval σ) + 1 =
      (c.toCNF sem).length + cond (Constraint.eval sem σ c) 1 0 := by
  set forb := (enumList c.scope.length).filter fun w => !sem c.rel w
  have hnodup : forb.Nodup := (nodup_enumList c.scope.length).filter _
  have hcount : (c.toCNF sem).countP (Clause.eval σ) =
      forb.countP (fun w => !(c.scope.map σ == w)) := by
    simp only [Constraint.toCNF, List.countP_map, Function.comp_def, forb]
    refine List.countP_congr fun w hw => ?_
    have hw_len : w.length = c.scope.length := length_of_mem_enumList (List.mem_of_mem_filter hw)
    rw [Constraint.eval_forbidClause c.scope hw_len σ]
  have hlen : (c.toCNF sem).length = forb.length := by
    simp only [Constraint.toCNF, List.length_map, forb]
  have hbeq : forb.countP (fun w => c.scope.map σ == w) = forb.count (c.scope.map σ) := by
    rw [List.count_eq_countP]
    exact List.countP_congr fun _ _ => by rw [beq_iff_eq, beq_iff_eq, eq_comm]
  have hneg : forb.countP (fun w => !(c.scope.map σ == w)) =
      forb.countP (fun w => ¬(c.scope.map σ == w)) :=
    List.countP_congr fun _ _ => by simp
  have hsplit := List.length_eq_countP_add_countP (fun w => c.scope.map σ == w) (l := forb)
  rw [hbeq, ← hneg] at hsplit
  have hmem : c.scope.map σ ∈ forb ↔ Constraint.eval sem σ c = false := by
    simp only [forb, List.mem_filter, mem_enumList, List.length_map, true_and, Constraint.eval,
      Bool.not_eq_true']
  rw [hcount, hlen]
  by_cases hev : Constraint.eval sem σ c = true
  · have hnot : c.scope.map σ ∉ forb := by
      rw [hmem]
      simp only [hev, Bool.true_eq_false, not_false_eq_true]
    rw [List.count_eq_zero_of_not_mem hnot] at hsplit
    simp only [hev, Bool.cond_true]
    omega
  · have hfalse : Constraint.eval sem σ c = false := Bool.eq_false_iff.mpr hev
    rw [List.count_eq_one_of_mem hnodup (hmem.mpr hfalse)] at hsplit
    simp only [hfalse, Bool.cond_false]
    omega

/-- **Exact affine score identity for `CSP.toCNF`.** On every assignment `σ : V → Bool`, the
number of satisfied clauses in `(F.toCNF sem)` plus `F.length` equals `(F.toCNF sem).length` plus
the number of satisfied constraints in `F`. -/
theorem countP_eval_toCNF_add_length {Rel V : Type*} (sem : Rel → List Bool → Bool)
    (F : CSP Rel V) (σ : V → Bool) :
    (F.toCNF sem).countP (Clause.eval σ) + F.length =
      (F.toCNF sem).length + F.countP (Constraint.eval sem σ) := by
  induction F with
  | nil => simp [CSP.toCNF]
  | cons c cs ih =>
    have hc := countP_eval_constraintToCNF_add_one sem c σ
    simp only [CSP.toCNF, List.flatMap_cons, List.countP_append, List.length_append,
      List.length_cons, List.countP_cons] at ih ⊢
    cases h : Constraint.eval sem σ c <;>
      simp only [h, Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ↓reduceIte] at hc ⊢ <;>
      omega

end MaxCSP

namespace MaxCSPInstance

/-- Score shift under forbidden-pattern `CSP.toCNF` compilation on declared assignments. -/
theorem score_ofCNF_toCNF_add_length {Rel : Type*} (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) (x : BitString F.numVars) :
    (ofCNF F.numVars (F.constraints.toCNF sem)).score MaxCSP.clauseSem x + F.constraints.length =
      (F.constraints.toCNF sem).length + F.score sem x := by
  rw [score_ofCNF]
  have h := MaxCSP.countP_eval_toCNF_add_length sem F.constraints (MaxCSP.assignment F.numVars x)
  have hcnt : F.constraints.countP (Constraint.eval sem (MaxCSP.assignment F.numVars x)) =
      F.score sem x := rfl
  rwa [hcnt] at h

/-- **Exact optimum shift under forbidden-pattern `CSP.toCNF` compilation.** -/
theorem optimum_ofCNF_toCNF_add_length {Rel : Type*} (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) :
    (ofCNF F.numVars (F.constraints.toCNF sem)).optimum MaxCSP.clauseSem + F.constraints.length =
      (F.constraints.toCNF sem).length + F.optimum sem := by
  apply le_antisymm
  · obtain ⟨x, hx⟩ :=
      (ofCNF F.numVars (F.constraints.toCNF sem)).exists_score_eq_optimum MaxCSP.clauseSem
    have hs := F.score_ofCNF_toCNF_add_length sem x
    have hle := F.score_le_optimum sem x
    omega
  · obtain ⟨x, hx⟩ := F.exists_score_eq_optimum sem
    have hs := F.score_ofCNF_toCNF_add_length sem x
    have hle := (ofCNF F.numVars (F.constraints.toCNF sem)).score_le_optimum MaxCSP.clauseSem x
    omega

end MaxCSPInstance

/-! ### Bridge 3: Clamped binary compilation from finite-domain `Fin q` to Boolean `Max-CSP` -/

namespace MaxCSP

/-- Clamped Boolean semantics for a finite-domain relation `sem : Rel → List (Fin q) → Bool`:
chunks of width `CSP.bitWidth q` are decoded in binary and clamped into `Fin q` via `CSP.toFin`. -/
@[expose] def clampedSem {Rel : Type*} (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (R : Rel) (bs : List Bool) : Bool :=
  let b := CSP.bitWidth q
  sem R ((CSP.decodeChunks b (bs.length / b) bs).map (CSP.toFin q hq))

/-- Decode a Boolean assignment `x : Fin (N * CSP.bitWidth q) → Bool` to `Fin N → Fin q` by reading
each `b`-bit variable block and clamping via `CSP.toFin`. -/
@[expose] def decodeFinAssign (q : ℕ) (hq : 0 < q) (N : ℕ)
    (x : Fin (N * CSP.bitWidth q) → Bool) (v : Fin N) : Fin q :=
  CSP.toFin q hq
    (lsbValue ((CSP.bitScope (CSP.bitWidth q) v.val).map (assignment (N * CSP.bitWidth q) x)))

/-- Encode a finite-domain assignment `y : Fin N → Fin q` into `Fin (N * CSP.bitWidth q) → Bool`
using `CSP.bitWidth q` low-order bits per variable. -/
@[expose] def encodeFinAssign (q N : ℕ) (y : Fin N → Fin q)
    (i : Fin (N * CSP.bitWidth q)) : Bool :=
  let b := CSP.bitWidth q
  have hv : i.val / b < N :=
    Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using i.isLt)
  (lowBits b (y ⟨i.val / b, hv⟩).val).getD (i.val % b) false

theorem decodeFinAssign_encodeFinAssign (q : ℕ) (hq : 0 < q) (N : ℕ) (y : Fin N → Fin q) :
    decodeFinAssign q hq N (encodeFinAssign q N y) = y := by
  funext v
  let b := CSP.bitWidth q
  have hbits : (CSP.bitScope b v.val).map (assignment (N * b) (encodeFinAssign q N y)) =
      lowBits b (y v).val := by
    apply List.ext_getElem
    · simp only [List.length_map, CSP.bitScope_length, length_lowBits]
    · intro j hj1 hj2
      rw [List.length_map, CSP.bitScope_length] at hj1
      have hlt : v.val * b + j < N * b :=
        (Nat.add_lt_add_left hj1 _).trans_le
          (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right b v.isLt)
      simp only [CSP.bitScope, List.getElem_map, List.getElem_range, assignment_lt _ hlt]
      dsimp only [encodeFinAssign]
      have hdiv : (v.val * b + j) / b = v.val := Nat.mul_add_div_of_lt v.val hj1
      have hmod : (v.val * b + j) % b = j := Nat.mul_add_mod_of_lt hj1
      have hfin : (⟨(v.val * b + j) / b,
          Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hlt)⟩ : Fin N) = v :=
        Fin.ext hdiv
      rw [hfin, hmod, List.getD_eq_getElem _ false hj2]
  dsimp only [decodeFinAssign]
  rw [hbits]
  have hval_lt : (y v).val < 2 ^ b := (y v).isLt.trans_le (CSP.le_two_pow_bitWidth q)
  rw [lsbValue_lowBits hval_lt, CSP.toFin_of_val hq (y v)]

theorem map_clampedScope_eq {q N : ℕ} (hq : 0 < q) [Inhabited (Fin q)]
    (x : Fin (N * CSP.bitWidth q) → Bool) {scope : List ℕ} (hscope : ∀ v ∈ scope, v < N) :
    let b := CSP.bitWidth q
    let bs := (scope.flatMap (CSP.bitScope b)).map (assignment (N * b) x)
    (CSP.decodeChunks b (bs.length / b) bs).map (CSP.toFin q hq) =
      scope.map (assignment N (decodeFinAssign q hq N x)) := by
  let b := CSP.bitWidth q
  have hb : 0 < b := CSP.one_le_bitWidth q
  let blockBits (v : ℕ) : List Bool := (CSP.bitScope b v).map (assignment (N * b) x)
  have hflat : (scope.flatMap (CSP.bitScope b)).map (assignment (N * b) x) =
      scope.flatMap blockBits := by
    simp only [List.map_flatMap, blockBits]
  have hlen : (scope.flatMap blockBits).length = scope.length * b := by
    refine List.length_flatMap_of_forall_length_eq fun v _ => ?_
    simp only [blockBits, List.length_map, CSP.bitScope_length]
  have hdiv : (scope.flatMap blockBits).length / b = scope.length := by
    rw [hlen, Nat.mul_div_cancel _ hb]
  dsimp only
  rw [hflat, hdiv, CSP.decodeChunks_flatMap b scope blockBits (fun v _ => by
    simp only [blockBits, List.length_map, CSP.bitScope_length]), List.map_map]
  refine List.map_congr_left fun v hv => ?_
  have hv_lt : v < N := hscope v hv
  simp only [Function.comp_apply, assignment_lt _ hv_lt, decodeFinAssign, blockBits]
  rfl

end MaxCSP

/-- Expand a finite-domain constraint's scope into `CSP.bitWidth q`-bit blocks. -/
@[expose] def Constraint.toClampedBoolean {Rel : Type*} (q : ℕ) (c : Constraint Rel ℕ) :
    Constraint Rel ℕ :=
  ⟨c.rel, c.scope.flatMap (CSP.bitScope (CSP.bitWidth q))⟩

/-- Expand a finite-domain `MaxCSPInstance` over `Fin q` into a Boolean `MaxCSPInstance` on
`F.numVars * CSP.bitWidth q` variables with the same number of constraints. -/
@[expose] def MaxCSPInstance.toClampedBoolean {Rel : Type*} (q : ℕ) (F : MaxCSPInstance Rel ℕ) :
    MaxCSPInstance Rel ℕ :=
  ⟨F.numVars * CSP.bitWidth q, F.constraints.map (Constraint.toClampedBoolean q)⟩

/-- Expand a weighted finite-domain constraint's scope into `CSP.bitWidth q`-bit blocks. -/
@[expose] def WeightedConstraint.toClampedBoolean {Rel W : Type*} (q : ℕ)
    (c : WeightedConstraint Rel ℕ W) : WeightedConstraint Rel ℕ W :=
  ⟨c.rel, c.scope.flatMap (CSP.bitScope (CSP.bitWidth q)), c.weight⟩

/-- Expand a weighted finite-domain `WeightedMaxCSP` over `Fin q` into a Boolean `WeightedMaxCSP`
on `F.numVars * CSP.bitWidth q` variables. -/
@[expose] def WeightedMaxCSP.toClampedBoolean {Rel W : Type*} (q : ℕ)
    (F : WeightedMaxCSP Rel ℕ W) : WeightedMaxCSP Rel ℕ W :=
  ⟨F.numVars * CSP.bitWidth q, F.constraints.map (WeightedConstraint.toClampedBoolean q)⟩

namespace MaxCSPInstance

variable {Rel : Type*}

@[simp]
theorem length_constraints_toClampedBoolean (q : ℕ) (F : MaxCSPInstance Rel ℕ) :
    (F.toClampedBoolean q).constraints.length = F.constraints.length := by
  simp only [toClampedBoolean, List.length_map]

theorem length_scope_mem_toClampedBoolean {q k : ℕ} {F : MaxCSPInstance Rel ℕ}
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k) {c : Constraint Rel ℕ}
    (hc : c ∈ (F.toClampedBoolean q).constraints) :
    c.scope.length ≤ k * CSP.bitWidth q := by
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
  dsimp only [Constraint.toClampedBoolean]
  rw [List.length_flatMap_of_forall_length_eq fun v _ => CSP.bitScope_length _ v]
  exact Nat.mul_le_mul_right _ (hk c₀ hc₀)

theorem score_toClampedBoolean {q : ℕ} (hq : 0 < q) [Inhabited (Fin q)]
    (sem : Rel → List (Fin q) → Bool) {F : MaxCSPInstance Rel ℕ}
    (hvars : ∀ v ∈ F.vars, v < F.numVars) (x : BitString (F.numVars * CSP.bitWidth q)) :
    (F.toClampedBoolean q).score (MaxCSP.clampedSem q hq sem) x =
      F.score sem (MaxCSP.decodeFinAssign q hq F.numVars x) := by
  simp only [score, evalCount, toClampedBoolean, List.countP_map, Function.comp_def]
  refine List.countP_congr fun c hc => ?_
  have hscope : ∀ v ∈ c.scope, v < F.numVars := fun v hv =>
    hvars v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)
  dsimp only [Constraint.eval, Constraint.toClampedBoolean, MaxCSP.clampedSem]
  rw [MaxCSP.map_clampedScope_eq hq x hscope]

end MaxCSPInstance

namespace WeightedMaxCSP

variable {Rel W : Type*}

theorem score_toClampedBoolean {q : ℕ} (hq : 0 < q) [Inhabited (Fin q)] [AddCommMonoid W]
    (sem : Rel → List (Fin q) → Bool) {F : WeightedMaxCSP Rel ℕ W}
    (hvars : ∀ v ∈ F.vars, v < F.numVars) (x : BitString (F.numVars * CSP.bitWidth q)) :
    (F.toClampedBoolean q).score (MaxCSP.clampedSem q hq sem) x =
      F.score sem (MaxCSP.decodeFinAssign q hq F.numVars x) := by
  simp only [score, evalScore, toClampedBoolean, List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  have hscope : ∀ v ∈ c.scope, v < F.numVars := fun v hv =>
    hvars v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)
  simp only [WeightedConstraint.evalWeight, WeightedConstraint.toClampedBoolean,
    MaxCSP.clampedSem, MaxCSP.map_clampedScope_eq hq x hscope]

/-- **Weighted optimum preservation for clamped finite-domain Boolean compilation.** -/
theorem optimum_toClampedBoolean {q : ℕ} (hq : 0 < q) [Inhabited (Fin q)]
    [AddCommMonoid W] [LinearOrder W] (sem : Rel → List (Fin q) → Bool)
    {F : WeightedMaxCSP Rel ℕ W} (hvars : ∀ v ∈ F.vars, v < F.numVars) :
    (F.toClampedBoolean q).optimum (MaxCSP.clampedSem q hq sem) = F.optimum sem := by
  apply le_antisymm
  · refine WeightedMaxCSP.optimum_le_of_forall fun x => ?_
    rw [F.score_toClampedBoolean hq sem hvars x]
    exact F.score_le_optimum sem _
  · refine WeightedMaxCSP.optimum_le_of_forall fun y => ?_
    have hy := MaxCSP.decodeFinAssign_encodeFinAssign q hq F.numVars y
    calc F.score sem y
        = F.score sem (MaxCSP.decodeFinAssign q hq F.numVars
            (MaxCSP.encodeFinAssign q F.numVars y)) := by rw [hy]
      _ = (F.toClampedBoolean q).score (MaxCSP.clampedSem q hq sem)
            (MaxCSP.encodeFinAssign q F.numVars y) :=
          (F.score_toClampedBoolean hq sem hvars _).symm
      _ ≤ (F.toClampedBoolean q).optimum (MaxCSP.clampedSem q hq sem) :=
          (F.toClampedBoolean q).score_le_optimum _ _

end WeightedMaxCSP

namespace MaxCSPInstance

/-- **Exact optimum preservation for clamped finite-domain Boolean compilation.** -/
theorem optimum_toClampedBoolean {Rel : Type*} {q : ℕ} (hq : 0 < q) [Inhabited (Fin q)]
    (sem : Rel → List (Fin q) → Bool) {F : MaxCSPInstance Rel ℕ}
    (hvars : ∀ v ∈ F.vars, v < F.numVars) :
    (F.toClampedBoolean q).optimum (MaxCSP.clampedSem q hq sem) = F.optimum sem := by
  have hwt : (F.toClampedBoolean q).toWeighted = F.toWeighted.toClampedBoolean q := by
    refine WeightedMaxCSP.ext rfl ?_
    simp only [toWeighted, toClampedBoolean, WeightedMaxCSP.toClampedBoolean, List.map_map]
    rfl
  have hvars' : ∀ v ∈ F.toWeighted.vars, v < F.toWeighted.numVars := by
    simpa only [WeightedMaxCSP.vars, toWeighted, List.flatMap_map, vars, CSP.vars] using hvars
  rw [← optimum_toWeighted, hwt, F.toWeighted.optimum_toClampedBoolean hq sem hvars',
    optimum_toWeighted]

end MaxCSPInstance

end Cslib.Logic.PL
