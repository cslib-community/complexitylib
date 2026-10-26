/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.BinaryCost
public import Complexity.Computability.Circuit.Monotone.Formula
import Complexity.Computability.Circuit.FanIn

/-!
# Positive and read-once Boolean formulas from tight binary-cost circuits

A one-output De Morgan circuit `c : Circuit Boolean.signature n 1` on `n ≥ 1` variables that
depends on all `n` inputs must use at least `n - 1` binary (`AND`/`OR`) gates
(`Circuit.card_inputSupport_le_cost_binaryCost`).
When `n ≥ 1` and this bound is tight (`c.program.cost binaryCost ≤ n - 1`, i.e.
`c.program.cost binaryCost + 1 ≤ n`), no gate in the backward cone of the
output can share wires or use a Boolean constant, so the circuit unfolds without duplication into a
constant-free negation-normal-form formula (`LitFormula`) of leaf size `n` in which each of the `n`
variables appears at a single leaf (`Circuit.exists_litFormula_of_cost_binaryCost_le`).

If moreover every coordinate `i : Fin n` is *positively essential*—meaning some pair of inputs
differing only at `i` flips the output from `false` to `true` when coordinate `i` is flipped from
`false` to `true`—then every leaf must have positive polarity, yielding a positive (monotone)
read-once formula `F : PosFormula n` of leaf size `n` and gate size `n - 1` computing the same
function (`Circuit.exists_posFormula_of_cost_binaryCost_le`) [Ilango2020FOCS, Section III.B;
ECCC TR20-183, Section 3, Claim 13, p. 24].

## Main definitions

* `Cslib.Circuits.Boolean.LitFormula`: constant-free negation-normal-form Boolean formulas built
  from literals `lit i pol` using binary `and` and `or`.
* `Cslib.Circuits.Boolean.PosFormula`: constant-free positive (monotone) Boolean formulas built
  from variables `var i` using binary `and` and `or`.
* `Cslib.Circuits.Boolean.PosFormula.IsReadOnce`: no variable appears at more than one leaf.
* `Cslib.Circuits.Boolean.PosFormula.IsSubformula`: the structural subformula relation.
* `Cslib.Circuits.Boolean.PosFormula.flipSensitive`: input coordinates in `leafSupport` whose flip
  from `w₀` to `true` changes the formula value from `false` to `true`.
* `Cslib.Circuits.Boolean.PosFormula.orFin`: right-nested disjunction of `m > 0` positive formulas.

## Main results

* `Cslib.Circuits.Program.exists_litFormula_of_card_biUnion_wireSupport_ge`: a frontier of wires
  achieving the binary-cost support bound unfolds into constant-free NNF formulas whose leaf sizes
  sum to `frontier.card + p.cost binaryCost`.
* `Cslib.Circuits.Circuit.exists_litFormula_of_cost_binaryCost_le`: a one-output De Morgan circuit
  with full support and `c.program.cost binaryCost + 1 ≤ n` unfolds into a `LitFormula` of leaf
  size `n`.
* `Cslib.Circuits.Circuit.exists_posFormula_of_cost_binaryCost_le`: when every coordinate is
  positively essential and `c.program.cost binaryCost + 1 ≤ n`, the circuit is computed by a
  read-once `PosFormula` of leaf size `n` and size `n - 1`.
* `Cslib.Circuits.Boolean.PosFormula.card_flipSensitive_le_numOr_add_one`: a read-once positive
  formula has at most `numOr + 1` flip-sensitive coordinates at any baseline input.
* `Cslib.Circuits.Boolean.PosFormula.eval_eq_of_isSubformula_of_eval_eq`: in a read-once positive
  formula, two inputs that agree outside a subformula's support and give the subformula the same
  value give the whole formula the same value.

## References

* [R. Ilango, *Constant Depth Formula and Partial Function Versions of MCSP are
  Hard*][Ilango2020FOCS]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean

variable {n g : ℕ}

namespace Boolean

private theorem bool_and_le_and {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    (a₁ && b₁) ≤ (a₂ && b₂) :=
  Bool.le_and (fun h => ha (Bool.and_le_left _ _ h)) (fun h => hb (Bool.and_le_right _ _ h))

private theorem bool_or_le_or {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    (a₁ || b₁) ≤ (a₂ || b₂) :=
  Bool.or_le (fun h => Bool.left_le_or _ _ (ha h)) (fun h => Bool.right_le_or _ _ (hb h))

/-! ### Constant-free positive (monotone) Boolean formulas -/

/-- A constant-free positive Boolean formula on `n` variables, built from input variables `var i`
using binary conjunction (`and`) and disjunction (`or`). -/
inductive PosFormula (n : ℕ) : Type where
  /-- Input variable `i`. -/
  | var (i : Fin n)
  /-- Binary conjunction. -/
  | and (L R : PosFormula n)
  /-- Binary disjunction. -/
  | or (L R : PosFormula n)
  deriving DecidableEq

namespace PosFormula

/-- Evaluate a positive formula on an `n`-bit input. -/
def eval : PosFormula n → BitString n → Bool
  | .var i, x => x i
  | .and L R, x => L.eval x && R.eval x
  | .or L R, x => L.eval x || R.eval x

@[simp] theorem eval_var (i : Fin n) (x : BitString n) : (var i).eval x = x i :=
  rfl

@[simp] theorem eval_and (L R : PosFormula n) (x : BitString n) :
    (and L R).eval x = (L.eval x && R.eval x) :=
  rfl

@[simp] theorem eval_or (L R : PosFormula n) (x : BitString n) :
    (or L R).eval x = (L.eval x || R.eval x) :=
  rfl

/-- Number of variable leaves in a positive formula. -/
def leafSize : PosFormula n → ℕ
  | .var _ => 1
  | .and L R => L.leafSize + R.leafSize
  | .or L R => L.leafSize + R.leafSize

@[simp] theorem leafSize_var (i : Fin n) : (var i).leafSize = 1 := rfl

@[simp] theorem leafSize_and (L R : PosFormula n) :
    (and L R).leafSize = L.leafSize + R.leafSize := rfl

@[simp] theorem leafSize_or (L R : PosFormula n) :
    (or L R).leafSize = L.leafSize + R.leafSize := rfl

/-- Number of binary gates (`and` and `or`) in a positive formula. -/
def size : PosFormula n → ℕ
  | .var _ => 0
  | .and L R => L.size + R.size + 1
  | .or L R => L.size + R.size + 1

@[simp] theorem size_var (i : Fin n) : (var i).size = 0 := rfl

@[simp] theorem size_and (L R : PosFormula n) : (and L R).size = L.size + R.size + 1 := rfl

@[simp] theorem size_or (L R : PosFormula n) : (or L R).size = L.size + R.size + 1 := rfl

/-- Number of `and` gates in a positive formula. -/
def numAnd : PosFormula n → ℕ
  | .var _ => 0
  | .and L R => L.numAnd + R.numAnd + 1
  | .or L R => L.numAnd + R.numAnd

@[simp] theorem numAnd_var (i : Fin n) : (var i).numAnd = 0 := rfl

@[simp] theorem numAnd_and (L R : PosFormula n) :
    (and L R).numAnd = L.numAnd + R.numAnd + 1 := rfl

@[simp] theorem numAnd_or (L R : PosFormula n) : (or L R).numAnd = L.numAnd + R.numAnd := rfl

/-- Number of `or` gates in a positive formula. -/
def numOr : PosFormula n → ℕ
  | .var _ => 0
  | .and L R => L.numOr + R.numOr
  | .or L R => L.numOr + R.numOr + 1

@[simp] theorem numOr_var (i : Fin n) : (var i).numOr = 0 := rfl

@[simp] theorem numOr_and (L R : PosFormula n) : (and L R).numOr = L.numOr + R.numOr := rfl

@[simp] theorem numOr_or (L R : PosFormula n) : (or L R).numOr = L.numOr + R.numOr + 1 := rfl

/-- The set of input variables appearing at the leaves of a positive formula. -/
def leafSupport : PosFormula n → Finset (Fin n)
  | .var i => {i}
  | .and L R => L.leafSupport ∪ R.leafSupport
  | .or L R => L.leafSupport ∪ R.leafSupport

@[simp] theorem leafSupport_var (i : Fin n) : (var i).leafSupport = {i} := rfl

@[simp] theorem leafSupport_and (L R : PosFormula n) :
    (and L R).leafSupport = L.leafSupport ∪ R.leafSupport := rfl

@[simp] theorem leafSupport_or (L R : PosFormula n) :
    (or L R).leafSupport = L.leafSupport ∪ R.leafSupport := rfl

/-- A positive formula is *read-once* when no input variable appears at more than one leaf. -/
def IsReadOnce : PosFormula n → Prop
  | .var _ => True
  | .and L R => L.IsReadOnce ∧ R.IsReadOnce ∧ Disjoint L.leafSupport R.leafSupport
  | .or L R => L.IsReadOnce ∧ R.IsReadOnce ∧ Disjoint L.leafSupport R.leafSupport

@[simp] theorem isReadOnce_var (i : Fin n) : (var i).IsReadOnce := trivial

@[simp] theorem isReadOnce_and {L R : PosFormula n} :
    (and L R).IsReadOnce ↔ L.IsReadOnce ∧ R.IsReadOnce ∧ Disjoint L.leafSupport R.leafSupport :=
  Iff.rfl

@[simp] theorem isReadOnce_or {L R : PosFormula n} :
    (or L R).IsReadOnce ↔ L.IsReadOnce ∧ R.IsReadOnce ∧ Disjoint L.leafSupport R.leafSupport :=
  Iff.rfl

theorem leafSize_pos (F : PosFormula n) : 0 < F.leafSize := by
  induction F <;> simp <;> omega

theorem leafSupport_nonempty (F : PosFormula n) : F.leafSupport.Nonempty := by
  induction F with
  | var i => exact ⟨i, Finset.mem_singleton_self i⟩
  | and L _ ihL => exact ihL.mono Finset.subset_union_left
  | or L _ ihL => exact ihL.mono Finset.subset_union_left

theorem size_add_one (F : PosFormula n) : F.size + 1 = F.leafSize := by
  induction F <;> simp <;> omega

theorem numAnd_add_numOr (F : PosFormula n) : F.numAnd + F.numOr = F.size := by
  induction F <;> simp <;> omega

theorem numAnd_add_numOr_add_one (F : PosFormula n) : F.numAnd + F.numOr + 1 = F.leafSize := by
  rw [F.numAnd_add_numOr, F.size_add_one]

theorem card_leafSupport_le_leafSize (F : PosFormula n) : F.leafSupport.card ≤ F.leafSize := by
  induction F with
  | var i => simp
  | and L R ihL ihR | or L R ihL ihR =>
    calc (L.leafSupport ∪ R.leafSupport).card
        ≤ L.leafSupport.card + R.leafSupport.card := Finset.card_union_le _ _
      _ ≤ L.leafSize + R.leafSize := Nat.add_le_add ihL ihR

/-- A positive formula is read-once if and only if its leaf support has cardinality equal to its
leaf size. -/
theorem isReadOnce_iff_card_leafSupport_eq_leafSize (F : PosFormula n) :
    F.IsReadOnce ↔ F.leafSupport.card = F.leafSize := by
  induction F with
  | var i => simp
  | and L R ihL ihR | or L R ihL ihR =>
    simp only [IsReadOnce, leafSupport, leafSize, ihL, ihR]
    have hL := L.card_leafSupport_le_leafSize
    have hR := R.card_leafSupport_le_leafSize
    have hunion := Finset.card_union_add_card_inter L.leafSupport R.leafSupport
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    omega

/-- Evaluation of a positive formula depends only on the variables in `F.leafSupport`. -/
theorem eval_eq_of_eq_on_leafSupport (F : PosFormula n) {x y : BitString n}
    (h : ∀ i ∈ F.leafSupport, x i = y i) : F.eval x = F.eval y := by
  induction F with
  | var i => exact h i (Finset.mem_singleton_self i)
  | and L R ihL ihR =>
    simp only [eval_and]
    rw [ihL fun i hi => h i (Finset.mem_union_left _ hi),
      ihR fun i hi => h i (Finset.mem_union_right _ hi)]
  | or L R ihL ihR =>
    simp only [eval_or]
    rw [ihL fun i hi => h i (Finset.mem_union_left _ hi),
      ihR fun i hi => h i (Finset.mem_union_right _ hi)]

/-- Positive formulas compute monotone Boolean functions. -/
theorem monotone_eval (F : PosFormula n) : Monotone F.eval := by
  induction F with
  | var i => exact fun _ _ h => h i
  | and L R ihL ihR => exact fun _ _ h => bool_and_le_and (ihL h) (ihR h)
  | or L R ihL ihR => exact fun _ _ h => bool_or_le_or (ihL h) (ihR h)

/-- A positive formula with no `and` gates evaluates to the disjunction of the variables in its
leaf support. -/
theorem eval_eq_decide_exists_of_numAnd_eq_zero {F : PosFormula n} (h : F.numAnd = 0)
    (x : BitString n) : F.eval x = decide (∃ i ∈ F.leafSupport, x i = true) := by
  induction F with
  | var i => simp
  | and L R => simp at h
  | or L R ihL ihR =>
    simp only [numAnd_or, Nat.add_eq_zero_iff] at h
    rw [eval_or, ihL h.1, ihR h.2, ← Bool.decide_or, leafSupport_or]
    congr 1
    simp [or_and_right, exists_or]

/-! ### Embedding into De Morgan and monotone formulas and circuits -/

/-- View a `PosFormula` as a De Morgan `Formula`. -/
def toFormula : PosFormula n → Formula Boolean.signature n
  | .var i => .input i
  | .and L R => L.toFormula.and R.toFormula
  | .or L R => L.toFormula.or R.toFormula

/-- View a `PosFormula` as a `Monotone.Formula`. -/
def toMonotoneFormula : PosFormula n → Formula Monotone.signature n
  | .var i => .input i
  | .and L R => Monotone.and L.toMonotoneFormula R.toMonotoneFormula
  | .or L R => Monotone.or L.toMonotoneFormula R.toMonotoneFormula

/-- Compile a `PosFormula` to a one-output De Morgan circuit. -/
def toCircuit (F : PosFormula n) : Circuit Boolean.signature n 1 :=
  F.toFormula.toCircuit

@[simp] theorem eval_toFormula (F : PosFormula n) (x : BitString n) :
    F.toFormula.eval interpretation x = F.eval x := by
  induction F <;> simp [toFormula, *]

@[simp] theorem eval_toMonotoneFormula (F : PosFormula n) (x : BitString n) :
    F.toMonotoneFormula.eval Monotone.interpretation x = F.eval x := by
  induction F <;> simp [toMonotoneFormula, *]

@[simp] theorem leafSize_toFormula (F : PosFormula n) : F.toFormula.leafSize = F.leafSize := by
  induction F <;> simp [toFormula, *]

@[simp] theorem size_toFormula (F : PosFormula n) : F.toFormula.size = F.size := by
  induction F <;> simp [toFormula, *]

@[simp] theorem cost_binaryCost_toFormula (F : PosFormula n) :
    F.toFormula.cost binaryCost = F.size := by
  induction F <;> simp [toFormula, Formula.and, Formula.or, Fin.sum_univ_two, *]

@[simp] theorem eval_toCircuit (F : PosFormula n) (x : BitString n) (j : Fin 1) :
    F.toCircuit.eval interpretation x j = F.eval x := by
  rw [toCircuit, Formula.eval_toCircuit, eval_toFormula]

@[simp] theorem size_toCircuit (F : PosFormula n) : F.toCircuit.size = F.size := by
  rw [toCircuit, Formula.size_toCircuit, size_toFormula]

@[simp] theorem cost_binaryCost_toCircuit (F : PosFormula n) :
    F.toCircuit.program.cost binaryCost = F.size := by
  rw [toCircuit, Formula.cost_toCircuit, cost_binaryCost_toFormula]

/-! ### Subformulas and context invariance in read-once formulas -/

/-- `IsSubformula T F` holds when `T` occurs as a syntactic subformula of `F`. -/
inductive IsSubformula : PosFormula n → PosFormula n → Prop
  | refl (T : PosFormula n) : IsSubformula T T
  | and_left {T L R : PosFormula n} : IsSubformula T L → IsSubformula T (.and L R)
  | and_right {T L R : PosFormula n} : IsSubformula T R → IsSubformula T (.and L R)
  | or_left {T L R : PosFormula n} : IsSubformula T L → IsSubformula T (.or L R)
  | or_right {T L R : PosFormula n} : IsSubformula T R → IsSubformula T (.or L R)

theorem IsSubformula.leafSupport_subset {T F : PosFormula n} (h : IsSubformula T F) :
    T.leafSupport ⊆ F.leafSupport := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | and_left _ ih | or_left _ ih => exact ih.trans Finset.subset_union_left
  | and_right _ ih | or_right _ ih => exact ih.trans Finset.subset_union_right

theorem IsSubformula.isReadOnce {T F : PosFormula n} (h : IsSubformula T F) (hF : F.IsReadOnce) :
    T.IsReadOnce := by
  induction h with
  | refl => exact hF
  | and_left _ ih | or_left _ ih => exact ih hF.1
  | and_right _ ih | or_right _ ih => exact ih hF.2.1

theorem IsSubformula.trans {N : ℕ} {A B C : PosFormula N} (hAB : PosFormula.IsSubformula A B)
    (hBC : PosFormula.IsSubformula B C) : PosFormula.IsSubformula A C := by
  induction hBC with
  | refl => exact hAB
  | or_left _ ih => exact .or_left ih
  | or_right _ ih => exact .or_right ih
  | and_left _ ih => exact .and_left ih
  | and_right _ ih => exact .and_right ih

theorem IsSubformula.of_or_left {N : ℕ} {L R F : PosFormula N}
    (h : PosFormula.IsSubformula (L.or R) F) : PosFormula.IsSubformula L F :=
  (PosFormula.IsSubformula.or_left (.refl L)).trans h

theorem IsSubformula.of_or_right {N : ℕ} {L R F : PosFormula N}
    (h : PosFormula.IsSubformula (L.or R) F) : PosFormula.IsSubformula R F :=
  (PosFormula.IsSubformula.or_right (.refl R)).trans h

theorem IsSubformula.of_and_left {N : ℕ} {L R F : PosFormula N}
    (h : PosFormula.IsSubformula (L.and R) F) : PosFormula.IsSubformula L F :=
  (PosFormula.IsSubformula.and_left (.refl L)).trans h

theorem IsSubformula.of_and_right {N : ℕ} {L R F : PosFormula N}
    (h : PosFormula.IsSubformula (L.and R) F) : PosFormula.IsSubformula R F :=
  (PosFormula.IsSubformula.and_right (.refl R)).trans h

/-- In a read-once positive formula `F`, if `T` is a subformula of `F` and two inputs `w₁, w₂`
agree on all coordinates outside `T.leafSupport` and give `T` the same Boolean value, then `F`
evaluates to the same value on `w₁` and `w₂`. -/
theorem eval_eq_of_isSubformula_of_eval_eq {T F : PosFormula n} (hsub : IsSubformula T F)
    (hro : F.IsReadOnce) {w₁ w₂ : BitString n}
    (hout : ∀ v, v ∉ T.leafSupport → w₁ v = w₂ v) (heval : T.eval w₁ = T.eval w₂) :
    F.eval w₁ = F.eval w₂ := by
  induction hsub with
  | refl => exact heval
  | @and_left L R hsub ih | @or_left L R hsub ih =>
    obtain ⟨hroL, _, hdisj⟩ := hro
    have hR : R.eval w₁ = R.eval w₂ :=
      R.eval_eq_of_eq_on_leafSupport fun v hv =>
        hout v fun hT => Finset.disjoint_right.mp hdisj hv (hsub.leafSupport_subset hT)
    simp [ih hroL, hR]
  | @and_right L R hsub ih | @or_right L R hsub ih =>
    obtain ⟨_, hroR, hdisj⟩ := hro
    have hL : L.eval w₁ = L.eval w₂ :=
      L.eval_eq_of_eq_on_leafSupport fun v hv =>
        hout v fun hT => Finset.disjoint_left.mp hdisj hv (hsub.leafSupport_subset hT)
    simp [hL, ih hroR]

/-! ### Flip-sensitivity bound on `numOr` -/

/-- The coordinates in `F.leafSupport` whose flip from `w₀` to `true` changes `F.eval` from
`false` to `true`. -/
def flipSensitive (w₀ : BitString n) (F : PosFormula n) : Finset (Fin n) :=
  F.leafSupport.filter fun v => !F.eval w₀ && F.eval (Function.update w₀ v true)

private theorem eval_update_of_notMem_leafSupport (F : PosFormula n) (w : BitString n) {v : Fin n}
    (hv : v ∉ F.leafSupport) (b : Bool) : F.eval (Function.update w v b) = F.eval w :=
  F.eval_eq_of_eq_on_leafSupport fun _ hu =>
    Function.update_of_ne (ne_of_mem_of_not_mem hu hv) _ _

private theorem mem_flipSensitive_iff {w₀ : BitString n} {F : PosFormula n} {v : Fin n} :
    v ∈ flipSensitive w₀ F ↔
      F.eval w₀ = false ∧ F.eval (Function.update w₀ v true) = true := by
  simp only [flipSensitive, Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨fun h => h.2, fun ⟨h₀, h₁⟩ => ⟨?_, h₀, h₁⟩⟩
  by_contra hv
  rw [F.eval_update_of_notMem_leafSupport w₀ hv, h₀] at h₁
  exact Bool.false_ne_true h₁

/-- **Gate-elimination bound on OR gates** [Ilango2020FOCS, Section III.B; ECCC TR20-183, Section 3,
Claim 14, p. 25]: in any read-once positive formula `F`, for any baseline input `w₀`, at most
`F.numOr + 1` coordinates in `F.leafSupport` flip `F.eval` from `false` to `true`. -/
theorem card_flipSensitive_le_numOr_add_one (w₀ : BitString n) {F : PosFormula n}
    (hro : F.IsReadOnce) : (flipSensitive w₀ F).card ≤ F.numOr + 1 := by
  induction F with
  | var i =>
    simpa [flipSensitive] using (Finset.card_filter_le ({i} : Finset (Fin n)) _)
  | and L R ihL ihR =>
    obtain ⟨hroL, hroR, _⟩ := hro
    by_cases hL₀ : L.eval w₀ = true
    · have hsub : flipSensitive w₀ (and L R) ⊆ flipSensitive w₀ R := fun v hv => by
        simp only [mem_flipSensitive_iff, eval_and, hL₀, Bool.true_and, Bool.and_eq_true] at hv ⊢
        exact ⟨hv.1, hv.2.2⟩
      exact (Finset.card_le_card hsub).trans ((ihR hroR).trans (by rw [numOr_and]; omega))
    · simp only [Bool.not_eq_true] at hL₀
      have hsub : flipSensitive w₀ (and L R) ⊆ flipSensitive w₀ L := fun v hv => by
        rw [mem_flipSensitive_iff] at hv ⊢
        exact ⟨hL₀, ((Bool.and_eq_true _ _).mp hv.2).1⟩
      exact (Finset.card_le_card hsub).trans ((ihL hroL).trans (by rw [numOr_and]; omega))
  | or L R ihL ihR =>
    obtain ⟨hroL, hroR, _⟩ := hro
    have hsub : flipSensitive w₀ (or L R) ⊆ flipSensitive w₀ L ∪ flipSensitive w₀ R :=
      fun v hv => by
        simp only [Finset.mem_union, mem_flipSensitive_iff, eval_or, Bool.or_eq_false_iff,
          Bool.or_eq_true] at hv ⊢
        exact hv.2.imp (fun hL => ⟨hv.1.1, hL⟩) (fun hR => ⟨hv.1.2, hR⟩)
    calc (flipSensitive w₀ (or L R)).card
        ≤ (flipSensitive w₀ L ∪ flipSensitive w₀ R).card := Finset.card_le_card hsub
      _ ≤ (flipSensitive w₀ L).card + (flipSensitive w₀ R).card := Finset.card_union_le _ _
      _ ≤ (L.numOr + 1) + (R.numOr + 1) := Nat.add_le_add (ihL hroL) (ihR hroR)
      _ = (or L R).numOr + 1 := by rw [numOr_or]; omega

/-! ### Indexed disjunction of positive formulas -/

/-- Right-nested disjunction of `m` positive formulas (`m > 0`). -/
def orFin {N : ℕ} : (m : ℕ) → 0 < m → (Fin m → PosFormula N) → PosFormula N
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, f => f ⟨0, Nat.zero_lt_one⟩
  | m + 2, _, f =>
    .or (f ⟨0, Nat.zero_lt_succ _⟩)
      (orFin (m + 1) (Nat.succ_pos m) (fun i => f i.succ))

theorem eval_orFin {N : ℕ} :
    ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → PosFormula N) (w : BitString N),
    (orFin m hm f).eval w = decide (∃ i : Fin m, (f i).eval w = true)
  | 0, hm, _, _ => absurd hm (Nat.lt_irrefl 0)
  | 1, _, f, w => by
    dsimp [orFin]
    rw [← Bool.decide_coe ((f 0).eval w), decide_eq_decide]
    exact ⟨fun h => ⟨0, h⟩,
      fun ⟨i, hi⟩ => by rcases Fin.eq_zero i with rfl; exact hi⟩
  | m + 2, _, f, w => by
    dsimp [orFin, PosFormula.eval]
    rw [eval_orFin (m + 1) (Nat.succ_pos m),
      ← Bool.decide_coe ((f 0).eval w), ← Bool.decide_or, decide_eq_decide]
    exact (Fin.exists_fin_succ (P := fun i => (f i).eval w = true)).symm

theorem leafSize_orFin_of_eq {N : ℕ} :
    ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → PosFormula N) (k : ℕ),
    (∀ i, (f i).leafSize = k) → (orFin m hm f).leafSize = m * k
  | 0, hm, _, _, _ => absurd hm (Nat.lt_irrefl 0)
  | 1, _, f, k, hk => by
    dsimp [orFin]
    rw [hk, Nat.one_mul]
  | m + 2, _, f, k, hk => by
    dsimp [orFin, PosFormula.leafSize]
    rw [hk, leafSize_orFin_of_eq (m + 1) (Nat.succ_pos m) _ k (fun i => hk i.succ),
      Nat.succ_mul (m + 1) k, Nat.add_comm]

theorem mem_leafSupport_orFin {N : ℕ} :
    ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → PosFormula N) (v : Fin N),
    v ∈ (orFin m hm f).leafSupport ↔ ∃ i : Fin m, v ∈ (f i).leafSupport
  | 0, hm, _, _ => absurd hm (Nat.lt_irrefl 0)
  | 1, _, f, v => by
    dsimp [orFin]
    exact ⟨fun h => ⟨0, h⟩,
      fun ⟨i, hi⟩ => by rcases Fin.eq_zero i with rfl; exact hi⟩
  | m + 2, _, f, v => by
    dsimp [orFin, PosFormula.leafSupport]
    rw [Finset.mem_union, mem_leafSupport_orFin (m + 1) (Nat.succ_pos m)]
    exact (Fin.exists_fin_succ (P := fun i => v ∈ (f i).leafSupport)).symm

end PosFormula

/-! ### Constant-free negation-normal-form Boolean formulas -/

/-- A constant-free negation-normal-form Boolean formula on `n` variables, built from literals
`lit i pol` (`x i` when `pol = true`, `!x i` when `pol = false`) using binary `and` and `or`. -/
inductive LitFormula (n : ℕ) : Type where
  /-- Literal on input variable `i` with polarity `pol`. -/
  | lit (i : Fin n) (pol : Bool)
  /-- Binary conjunction. -/
  | and (L R : LitFormula n)
  /-- Binary disjunction. -/
  | or (L R : LitFormula n)
  deriving DecidableEq

namespace LitFormula

/-- Evaluate a literal formula on an `n`-bit input. -/
def eval : LitFormula n → BitString n → Bool
  | .lit i true, x => x i
  | .lit i false, x => !x i
  | .and L R, x => L.eval x && R.eval x
  | .or L R, x => L.eval x || R.eval x

/-- Negate a literal formula by De Morgan's laws, flipping the polarity of each literal and
swapping `and` and `or`. -/
def neg : LitFormula n → LitFormula n
  | .lit i pol => .lit i (!pol)
  | .and L R => .or L.neg R.neg
  | .or L R => .and L.neg R.neg

/-- Number of literal leaves in a literal formula. -/
def leafSize : LitFormula n → ℕ
  | .lit _ _ => 1
  | .and L R => L.leafSize + R.leafSize
  | .or L R => L.leafSize + R.leafSize

/-- Number of positive literal leaves (`lit i true`) in a literal formula. -/
def posLeafCount : LitFormula n → ℕ
  | .lit _ pol => if pol then 1 else 0
  | .and L R => L.posLeafCount + R.posLeafCount
  | .or L R => L.posLeafCount + R.posLeafCount

/-- The set of input variables occurring positively (`lit i true`) at a leaf. -/
def posSupport : LitFormula n → Finset (Fin n)
  | .lit i pol => if pol then {i} else ∅
  | .and L R => L.posSupport ∪ R.posSupport
  | .or L R => L.posSupport ∪ R.posSupport

/-- Project a literal formula to a positive formula by dropping literal polarities. When all
leaves have positive polarity (`posLeafCount = leafSize`), this preserves evaluation. -/
def toPosFormula : LitFormula n → PosFormula n
  | .lit i _ => .var i
  | .and L R => .and L.toPosFormula R.toPosFormula
  | .or L R => .or L.toPosFormula R.toPosFormula

@[simp] theorem eval_neg (F : LitFormula n) (x : BitString n) : F.neg.eval x = !F.eval x := by
  induction F with
  | lit i pol => cases pol <;> simp [neg, eval]
  | and L R ihL ihR | or L R ihL ihR => simp [neg, eval, ihL, ihR]

@[simp] theorem leafSize_neg (F : LitFormula n) : F.neg.leafSize = F.leafSize := by
  induction F <;> simp [neg, leafSize, *]

@[simp] theorem leafSize_toPosFormula (F : LitFormula n) :
    F.toPosFormula.leafSize = F.leafSize := by
  induction F <;> simp [toPosFormula, leafSize, PosFormula.leafSize_var,
    PosFormula.leafSize_and, PosFormula.leafSize_or, *]

theorem posSupport_subset_leafSupport (F : LitFormula n) :
    F.posSupport ⊆ F.toPosFormula.leafSupport := by
  induction F with
  | lit i pol => cases pol <;> simp [posSupport, toPosFormula]
  | and L R ihL ihR | or L R ihL ihR =>
    exact Finset.union_subset_union ihL ihR

theorem card_posSupport_le_posLeafCount (F : LitFormula n) :
    F.posSupport.card ≤ F.posLeafCount := by
  induction F with
  | lit i pol => cases pol <;> simp [posSupport, posLeafCount]
  | and L R ihL ihR | or L R ihL ihR =>
    calc (L.posSupport ∪ R.posSupport).card
        ≤ L.posSupport.card + R.posSupport.card := Finset.card_union_le _ _
      _ ≤ L.posLeafCount + R.posLeafCount := Nat.add_le_add ihL ihR

theorem posLeafCount_le_leafSize (F : LitFormula n) : F.posLeafCount ≤ F.leafSize := by
  induction F with
  | lit i pol => cases pol <;> simp [posLeafCount, leafSize]
  | and L R ihL ihR | or L R ihL ihR => exact Nat.add_le_add ihL ihR

theorem eval_toPosFormula_of_posLeafCount_eq_leafSize {F : LitFormula n}
    (h : F.posLeafCount = F.leafSize) (x : BitString n) :
    F.toPosFormula.eval x = F.eval x := by
  induction F with
  | lit i pol =>
    cases pol
    · simp [posLeafCount, leafSize] at h
    · rfl
  | and L R ihL ihR | or L R ihL ihR =>
    have hL := L.posLeafCount_le_leafSize
    have hR := R.posLeafCount_le_leafSize
    simp only [posLeafCount, leafSize] at h
    simp [toPosFormula, eval, ihL (by omega), ihR (by omega)]

/-- If variable `i` does not occur positively in `F`, flipping `i` from `false` to `true` can only
decrease `F.eval`. -/
theorem eval_le_of_not_mem_posSupport {F : LitFormula n} {i : Fin n} (hi : i ∉ F.posSupport)
    {y₀ y₁ : BitString n} (hdiff : ∀ k, k ≠ i → y₀ k = y₁ k)
    (hy₀ : y₀ i = false) (hy₁ : y₁ i = true) : F.eval y₁ ≤ F.eval y₀ := by
  induction F with
  | lit j pol =>
    cases pol
    · by_cases hji : j = i
      · subst hji
        simp [eval, hy₁]
      · simp [eval, hdiff j hji]
    · simp only [posSupport, ↓reduceIte, Finset.mem_singleton] at hi
      simp [eval, hdiff j (Ne.symm hi)]
  | and L R ihL ihR =>
    simp only [posSupport, Finset.mem_union, not_or] at hi
    exact bool_and_le_and (ihL hi.1) (ihR hi.2)
  | or L R ihL ihR =>
    simp only [posSupport, Finset.mem_union, not_or] at hi
    exact bool_or_le_or (ihL hi.1) (ihR hi.2)

end LitFormula

end Boolean

/-! ### Unfolding tight binary-cost De Morgan programs into formulas -/

@[simp] private theorem wire_lastCases_last {α : Sort*} (last : α) (castSucc : Wire n g → α) :
    Wire.lastCases (motive := fun _ => α) last castSucc (.gate (Fin.last g)) = last := by
  simp [Wire.lastCases]

@[simp] private theorem wire_lastCases_castSucc {α : Sort*} (last : α) (castSucc : Wire n g → α)
    (w : Wire n g) :
    Wire.lastCases (motive := fun _ => α) last castSucc w.castSucc = castSucc w := by
  cases w <;> simp [Wire.lastCases]

private def priorFrontier (frontier : Finset (Wire n (g + 1))) : Finset (Wire n g) :=
  Finset.univ.filter fun w : Wire n g => w.castSucc ∈ frontier

private def openedFrontier {k : ℕ} (frontier : Finset (Wire n (g + 1)))
    (wires : Fin k → Wire n g) : Finset (Wire n g) :=
  if Wire.gate (Fin.last g) ∈ frontier then
    priorFrontier frontier ∪ Finset.univ.image wires
  else
    priorFrontier frontier

private theorem image_castSucc_priorFrontier (frontier : Finset (Wire n (g + 1))) :
    (priorFrontier frontier).image Wire.castSucc = frontier.erase (.gate (.last g)) := by
  ext w
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, priorFrontier]
  refine ⟨?_, ?_⟩
  · rintro ⟨w', hw', rfl⟩
    refine ⟨?_, hw'⟩
    cases w' <;> simp [Fin.castSucc_ne_last]
  · rintro ⟨hne, hw⟩
    induction w using Wire.lastCases with
    | last => exact absurd rfl hne
    | castSucc w' => exact ⟨w', hw, rfl⟩

private theorem card_priorFrontier (frontier : Finset (Wire n (g + 1))) :
    (priorFrontier frontier).card = (frontier.erase (.gate (.last g))).card := by
  rw [← image_castSucc_priorFrontier, Finset.card_image_of_injective _ Wire.castSucc_injective]

private theorem biUnion_wireSupport_gate_subset (p : Program signature n g) (op : Op)
    (wires : Fin (signature.Arity op) → Wire n g) (frontier : Finset (Wire n (g + 1))) :
    frontier.biUnion (p.gate ⟨op, wires⟩).wireSupport ⊆
      (openedFrontier frontier wires).biUnion p.wireSupport := by
  intro i hi
  rw [Finset.mem_biUnion] at hi ⊢
  obtain ⟨w, hw, hi⟩ := hi
  revert hw hi
  induction w using Wire.lastCases with
  | last =>
    intro hlast hi
    rw [Program.wireSupport_gate_last] at hi
    obtain ⟨arg, hi⟩ := Line.mem_inputSupport.mp hi
    exact ⟨wires arg, by simp [openedFrontier, hlast], hi⟩
  | castSucc w =>
    intro hw hi
    rw [Program.wireSupport_gate_castSucc] at hi
    refine ⟨w, ?_, hi⟩
    by_cases hlast : Wire.gate (Fin.last g) ∈ frontier <;>
      simp [openedFrontier, priorFrontier, hlast, hw]

private def lineLitFormula (hn : 0 < n) (F' : Wire n g → LitFormula n) :
    (op : Op) → (Fin (signature.Arity op) → Wire n g) → LitFormula n
  | .const _, _ => .lit ⟨0, hn⟩ true
  | .not, wires => (F' (wires 0)).neg
  | .and, wires => .and (F' (wires 0)) (F' (wires 1))
  | .or, wires => .or (F' (wires 0)) (F' (wires 1))

private theorem eval_lineLitFormula (hn : 0 < n) (F' : Wire n g → LitFormula n) (op : Op)
    (wires : Fin (signature.Arity op) → Wire n g)
    (harity : signature.Arity op = 1 + binaryCost op) (x : BitString n) :
    (lineLitFormula hn F' op wires).eval x =
      interpretation op (fun a => (F' (wires a)).eval x) := by
  cases op <;> simp [lineLitFormula, interpretation, LitFormula.eval] at harity ⊢

private theorem leafSize_lineLitFormula (hn : 0 < n) (F' : Wire n g → LitFormula n) (op : Op)
    (wires : Fin (signature.Arity op) → Wire n g)
    (harity : signature.Arity op = 1 + binaryCost op)
    (hcard : (Finset.univ.image wires).card = signature.Arity op) :
    (lineLitFormula hn F' op wires).leafSize =
      ∑ w ∈ Finset.univ.image wires, (F' w).leafSize := by
  have hinj : Set.InjOn wires ↑(Finset.univ : Finset (Fin (signature.Arity op))) :=
    Finset.card_image_iff.mp (by simpa using hcard)
  rw [Finset.sum_image hinj]
  cases op <;>
    simp [lineLitFormula, LitFormula.leafSize, Fin.sum_univ_two] at harity ⊢

private theorem openedFrontier_tight (p : Program signature n g) (op : Op)
    (wires : Fin (signature.Arity op) → Wire n g) (frontier : Finset (Wire n (g + 1)))
    (h : frontier.card + (p.gate ⟨op, wires⟩).cost binaryCost ≤
      (frontier.biUnion (p.gate ⟨op, wires⟩).wireSupport).card) :
    (openedFrontier frontier wires).card + p.cost binaryCost ≤
        ((openedFrontier frontier wires).biUnion p.wireSupport).card ∧
      (openedFrontier frontier wires).card = frontier.card + binaryCost op ∧
      (Wire.gate (Fin.last g) ∈ frontier →
        Disjoint (priorFrontier frontier) (Finset.univ.image wires) ∧
          (Finset.univ.image wires).card = signature.Arity op ∧
          signature.Arity op = 1 + binaryCost op) := by
  have hcard_sub := Finset.card_le_card (biUnion_wireSupport_gate_subset p op wires frontier)
  have hp_bound := p.card_biUnion_wireSupport_le_cost_binaryCost (openedFrontier frontier wires)
  have hprior_card := card_priorFrontier frontier
  have harity_li : (Finset.univ.image wires).card ≤ signature.Arity op := by
    simpa using (Finset.card_image_le :
      (Finset.univ.image wires).card ≤ (Finset.univ : Finset (Fin (signature.Arity op))).card)
  have harity_le := Boolean.arity_le_one_add_binaryCost op
  have hunion :=
    Finset.card_union_add_card_inter (priorFrontier frontier) (Finset.univ.image wires)
  have hcost_gate : (p.gate ⟨op, wires⟩).cost binaryCost = p.cost binaryCost + binaryCost op :=
    Program.cost_gate p ⟨op, wires⟩ binaryCost
  have hopened_le : (openedFrontier frontier wires).card ≤ frontier.card + binaryCost op := by
    by_cases hlast : Wire.gate (Fin.last g) ∈ frontier
    · have herase := Finset.card_erase_of_mem hlast
      have hpos : 1 ≤ frontier.card := Finset.one_le_card.mpr ⟨_, hlast⟩
      rw [show openedFrontier frontier wires =
        priorFrontier frontier ∪ Finset.univ.image wires by simp [openedFrontier, hlast]]
      omega
    · rw [show openedFrontier frontier wires = priorFrontier frontier by
        simp [openedFrontier, hlast], hprior_card, Finset.erase_eq_of_notMem hlast]
      omega
  refine ⟨by omega, by omega, fun hlast => ?_⟩
  have hpos : 1 ≤ frontier.card := Finset.one_le_card.mpr ⟨_, hlast⟩
  have herase := Finset.card_erase_of_mem hlast
  rw [← show openedFrontier frontier wires =
    priorFrontier frontier ∪ Finset.univ.image wires by simp [openedFrontier, hlast]] at hunion
  exact ⟨Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega)),
    by omega, by omega⟩

private theorem sum_lastCases_leafSize (hn : 0 < n) (p : Program signature n g) (op : Op)
    (wires : Fin (signature.Arity op) → Wire n g) (frontier : Finset (Wire n (g + 1)))
    (F' : Wire n g → LitFormula n)
    (h : frontier.card + (p.gate ⟨op, wires⟩).cost binaryCost ≤
      (frontier.biUnion (p.gate ⟨op, wires⟩).wireSupport).card)
    (hF'_sum : ∑ w ∈ openedFrontier frontier wires, (F' w).leafSize =
      (openedFrontier frontier wires).card + p.cost binaryCost) :
    ∑ w ∈ frontier,
      ((Wire.lastCases (lineLitFormula hn F' op wires) F' :
        Wire n (g + 1) → LitFormula n) w).leafSize =
      frontier.card + (p.gate ⟨op, wires⟩).cost binaryCost := by
  obtain ⟨_, hopened_eq, hlast_tight⟩ := openedFrontier_tight p op wires frontier h
  let lastFormula : LitFormula n := lineLitFormula hn F' op wires
  let F : Wire n (g + 1) → LitFormula n := Wire.lastCases lastFormula F'
  have hsum_prior :
      ∑ w ∈ frontier.erase (.gate (.last g)), (F w).leafSize =
        ∑ w' ∈ priorFrontier frontier, (F' w').leafSize := by
    rw [← image_castSucc_priorFrontier,
      Finset.sum_image fun a _ b _ hab => Wire.castSucc_injective hab]
    exact Finset.sum_congr rfl fun w' _ =>
      congrArg LitFormula.leafSize (wire_lastCases_castSucc lastFormula F' w')
  have hcost_gate : (p.gate ⟨op, wires⟩).cost binaryCost = p.cost binaryCost + binaryCost op :=
    Program.cost_gate p ⟨op, wires⟩ binaryCost
  by_cases hlast : Wire.gate (Fin.last g) ∈ frontier
  · obtain ⟨hdisj, hcard_li, harity_eq⟩ := hlast_tight hlast
    have hlast_leaf :
        (F (.gate (.last g))).leafSize = ∑ w ∈ Finset.univ.image wires, (F' w).leafSize := by
      rw [show F (.gate (.last g)) = lastFormula from wire_lastCases_last lastFormula F']
      exact leafSize_lineLitFormula hn F' op wires harity_eq hcard_li
    have hdef : openedFrontier frontier wires =
        priorFrontier frontier ∪ Finset.univ.image wires := by simp [openedFrontier, hlast]
    rw [← Finset.sum_erase_add _ _ hlast, hsum_prior, hlast_leaf,
      ← Finset.sum_union hdisj, ← hdef, hF'_sum, hopened_eq, hcost_gate]
    omega
  · have herase : frontier.erase (.gate (.last g)) = frontier :=
      Finset.erase_eq_of_notMem hlast
    have hsum_f : ∑ w ∈ frontier, (F w).leafSize =
        ∑ w' ∈ priorFrontier frontier, (F' w').leafSize := by
      rw [← hsum_prior, herase]
    have hdef : openedFrontier frontier wires = priorFrontier frontier := by
      simp [openedFrontier, hlast]
    rw [hsum_f, ← hdef, hF'_sum, hopened_eq, hcost_gate]
    omega

/-- When a frontier of wires in a De Morgan program achieves the binary-cost support bound
`frontier.card + p.cost binaryCost ≤ (frontier.biUnion p.wireSupport).card`, every wire in the
frontier unfolds into a constant-free NNF formula (`LitFormula`) such that the leaf sizes across the
frontier sum to `frontier.card + p.cost binaryCost`. -/
theorem Program.exists_litFormula_of_card_biUnion_wireSupport_ge (hn : 0 < n)
    (p : Program signature n g) (frontier : Finset (Wire n g))
    (h : frontier.card + p.cost binaryCost ≤ (frontier.biUnion p.wireSupport).card) :
    ∃ F : Wire n g → LitFormula n,
      (∀ w ∈ frontier, ∀ x, (F w).eval x = p.trace interpretation x w) ∧
      (∑ w ∈ frontier, (F w).leafSize) = frontier.card + p.cost binaryCost := by
  induction p with
  | empty =>
    refine ⟨fun | .input i => .lit i true | .gate j => j.elim0,
      fun | .input _, _, _ => rfl | .gate j, _, _ => j.elim0, ?_⟩
    have h1 : ∀ w ∈ frontier,
        (match w with | Wire.input i => LitFormula.lit i true | Wire.gate j => j.elim0).leafSize =
          1 := fun | .input _, _ => rfl | .gate j, _ => j.elim0
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one, Program.cost_empty,
      Nat.add_zero]
  | @gate g p line ih =>
    obtain ⟨op, wires⟩ := line
    obtain ⟨h_opened, _, hlast_tight⟩ := openedFrontier_tight p op wires frontier h
    obtain ⟨F', hF'_eval, hF'_sum⟩ := ih (openedFrontier frontier wires) h_opened
    refine ⟨Wire.lastCases (lineLitFormula hn F' op wires) F', fun w hw x => ?_,
      sum_lastCases_leafSize hn p op wires frontier F' h hF'_sum⟩
    induction w using Wire.lastCases with
    | last =>
      obtain ⟨_, _, harity_eq⟩ := hlast_tight hw
      have hmem_li (a : Fin (signature.Arity op)) : wires a ∈ openedFrontier frontier wires := by
        simp [openedFrontier, hw]
      simp only [wire_lastCases_last, Program.trace_gate_last]
      rw [eval_lineLitFormula hn F' op wires harity_eq x]
      exact congrArg (interpretation op) (funext fun a => hF'_eval (wires a) (hmem_li a) x)
    | castSucc w' =>
      have hw'_open : w' ∈ openedFrontier frontier wires := by
        by_cases hlast : Wire.gate (Fin.last g) ∈ frontier <;>
          simp [openedFrontier, priorFrontier, hlast, hw]
      simp only [wire_lastCases_castSucc, Program.trace_gate_castSucc]
      exact hF'_eval w' hw'_open x

/-- A one-output De Morgan circuit with `1 ≤ n`, full input support `n ≤ c.inputSupport.card`, and
`c.program.cost binaryCost + 1 ≤ n` unfolds into a constant-free NNF formula `F : LitFormula n` of
leaf size `n` computing `c`. -/
theorem Circuit.exists_litFormula_of_cost_binaryCost_le (hn : 0 < n) (c : Circuit signature n 1)
    (hsupp : n ≤ c.inputSupport.card) (hcost : c.program.cost binaryCost + 1 ≤ n) :
    ∃ F : LitFormula n, (∀ x, F.eval x = c.eval interpretation x 0) ∧ F.leafSize = n := by
  let frontier : Finset (Wire n c.size) := {c.outputs 0}
  have hsub : c.inputSupport ⊆ frontier.biUnion c.program.wireSupport := by
    intro i hi
    rw [Circuit.mem_inputSupport] at hi
    obtain ⟨o, ho⟩ := hi
    rw [Subsingleton.elim o 0] at ho
    exact Finset.mem_biUnion.mpr ⟨c.outputs 0, Finset.mem_singleton_self _, ho⟩
  have hcard_le := Finset.card_le_card hsub
  have hf_card : frontier.card = 1 := Finset.card_singleton _
  have hcard : frontier.card + c.program.cost binaryCost ≤
      (frontier.biUnion c.program.wireSupport).card := by
    omega
  have hcost_eq : 1 + c.program.cost binaryCost = n := by
    have := c.card_inputSupport_le_cost_binaryCost
    omega
  obtain ⟨F, hF_eval, hF_sum⟩ :=
    c.program.exists_litFormula_of_card_biUnion_wireSupport_ge hn frontier hcard
  refine ⟨F (c.outputs 0), fun x => hF_eval _ (Finset.mem_singleton_self _) x, ?_⟩
  simpa [frontier, hcost_eq] using hF_sum

/-- **Unfolding a tight binary-cost circuit into a positive read-once formula**
[Ilango2020FOCS, Section III.B; ECCC TR20-183, Section 3, Claim 13, p. 24]: if `c` is a one-output
De Morgan circuit on `n ≥ 1` inputs with `c.program.cost binaryCost + 1 ≤ n` such that every input
coordinate `i : Fin n` is positively essential for `fun x => c.eval interpretation x 0`, then there
exists a read-once positive formula `F : PosFormula n` with `F.leafSize = n`, `F.size = n - 1`,
and `F.leafSupport = Finset.univ` that computes `c`. -/
theorem Circuit.exists_posFormula_of_cost_binaryCost_le (hn : 0 < n) (c : Circuit signature n 1)
    (hcost : c.program.cost binaryCost + 1 ≤ n)
    (hpos : ∀ i : Fin n, ∃ y₀ y₁ : BitString n, (∀ k, k ≠ i → y₀ k = y₁ k) ∧
      y₀ i = false ∧ y₁ i = true ∧
      c.eval interpretation y₀ 0 = false ∧ c.eval interpretation y₁ 0 = true) :
    ∃ F : PosFormula n,
      F.IsReadOnce ∧ F.leafSize = n ∧ F.size = n - 1 ∧ F.leafSupport = Finset.univ ∧
      ∀ x, F.eval x = c.eval interpretation x 0 := by
  have hess (i : Fin n) : EssentialAt (c.eval interpretation) i := by
    obtain ⟨y₀, y₁, hdiff, _, _, hy₀, hy₁⟩ := hpos i
    refine ⟨y₀, y₁, hdiff, fun h => ?_⟩
    have h0 := congrFun h 0
    rw [hy₀, hy₁] at h0
    exact Bool.false_ne_true h0
  have hsupp_eq : c.inputSupport = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun i => (hess i).mem_support (c.dependsOn_eval interpretation)
  have hsupp : n ≤ c.inputSupport.card := by
    rw [hsupp_eq, Finset.card_univ, Fintype.card_fin]
  obtain ⟨T, hT_eval, hT_leaf⟩ := c.exists_litFormula_of_cost_binaryCost_le hn hsupp hcost
  have hpos_univ : T.posSupport = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr fun i => ?_
    by_contra hi
    obtain ⟨y₀, y₁, hdiff, hy₀, hy₁, hc₀, hc₁⟩ := hpos i
    have hle := T.eval_le_of_not_mem_posSupport hi hdiff hy₀ hy₁
    rw [hT_eval y₀, hT_eval y₁, hc₀, hc₁] at hle
    exact absurd hle (by decide)
  have hcard_pos : T.posSupport.card = n := by
    rw [hpos_univ, Finset.card_univ, Fintype.card_fin]
  have hcount_eq : T.posLeafCount = T.leafSize := by
    have := T.card_posSupport_le_posLeafCount
    have := T.posLeafCount_le_leafSize
    omega
  let F := T.toPosFormula
  have hF_leaf : F.leafSize = n := by
    rw [LitFormula.leafSize_toPosFormula, hT_leaf]
  have hF_supp : F.leafSupport = Finset.univ := by
    refine Finset.Subset.antisymm (Finset.subset_univ _) ?_
    rw [← hpos_univ]
    exact T.posSupport_subset_leafSupport
  have hF_ro : F.IsReadOnce := by
    rw [PosFormula.isReadOnce_iff_card_leafSupport_eq_leafSize, hF_supp, Finset.card_univ,
      Fintype.card_fin, hF_leaf]
  have hF_size : F.size = n - 1 := by
    have := F.size_add_one
    omega
  refine ⟨F, hF_ro, hF_leaf, hF_size, hF_supp, fun x => ?_⟩
  rw [T.eval_toPosFormula_of_posLeafCount_eq_leafSize hcount_eq x, hT_eval x]

end Cslib.Circuits
