/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.BinaryCost
public import Complexity.Computability.Circuit.Monotone.Formula

/-!
# Positive and read-once Boolean formulas from tight binary-cost circuits

A one-output De Morgan circuit `c : Circuit Boolean.signature n 1` that depends on all `n` inputs
must use at least `n - 1` binary (`AND`/`OR`) gates
(`Circuit.card_inputSupport_le_cost_binaryCost`).
When this bound is tight (`c.program.cost binaryCost ≤ n - 1`), no gate in the backward cone of the
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
    (a₁ && b₁) ≤ (a₂ && b₂) := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> revert ha hb <;> decide

private theorem bool_or_le_or {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    (a₁ || b₁) ≤ (a₂ || b₂) := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> revert ha hb <;> decide

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

/-- In a read-once positive formula `F`, if `T` is a subformula of `F` and two inputs `w₁, w₂`
agree on all coordinates outside `T.leafSupport` and give `T` the same Boolean value, then `F`
evaluates to the same value on `w₁` and `w₂`. -/
theorem eval_eq_of_isSubformula_of_eval_eq {T F : PosFormula n} (hsub : IsSubformula T F)
    (hro : F.IsReadOnce) {w₁ w₂ : BitString n}
    (hout : ∀ v, v ∉ T.leafSupport → w₁ v = w₂ v) (heval : T.eval w₁ = T.eval w₂) :
    F.eval w₁ = F.eval w₂ := by
  induction hsub with
  | refl => exact heval
  | @and_left L R hsub ih =>
    obtain ⟨hroL, _, hdisj⟩ := hro
    have hL := ih hroL
    have hR : R.eval w₁ = R.eval w₂ :=
      R.eval_eq_of_eq_on_leafSupport fun v hv =>
        hout v fun hT => Finset.disjoint_right.mp hdisj hv (hsub.leafSupport_subset hT)
    simp [hL, hR]
  | @and_right L R hsub ih =>
    obtain ⟨_, hroR, hdisj⟩ := hro
    have hR := ih hroR
    have hL : L.eval w₁ = L.eval w₂ :=
      L.eval_eq_of_eq_on_leafSupport fun v hv =>
        hout v fun hT => Finset.disjoint_left.mp hdisj hv (hsub.leafSupport_subset hT)
    simp [hL, hR]
  | @or_left L R hsub ih =>
    obtain ⟨hroL, _, hdisj⟩ := hro
    have hL := ih hroL
    have hR : R.eval w₁ = R.eval w₂ :=
      R.eval_eq_of_eq_on_leafSupport fun v hv =>
        hout v fun hT => Finset.disjoint_right.mp hdisj hv (hsub.leafSupport_subset hT)
    simp [hL, hR]
  | @or_right L R hsub ih =>
    obtain ⟨_, hroR, hdisj⟩ := hro
    have hR := ih hroR
    have hL : L.eval w₁ = L.eval w₂ :=
      L.eval_eq_of_eq_on_leafSupport fun v hv =>
        hout v fun hT => Finset.disjoint_left.mp hdisj hv (hsub.leafSupport_subset hT)
    simp [hL, hR]

/-! ### Flip-sensitivity bound on `numOr` -/

/-- The coordinates in `F.leafSupport` whose flip from `w₀` to `true` changes `F.eval` from
`false` to `true`. -/
def flipSensitive (w₀ : BitString n) (F : PosFormula n) : Finset (Fin n) :=
  F.leafSupport.filter fun v => !F.eval w₀ && F.eval (Function.update w₀ v true)

/-- **Gate-elimination bound on OR gates** [Ilango2020FOCS, Section III.B; ECCC TR20-183, Section 3,
Claim 14, p. 25]: in any read-once positive formula `F`, for any baseline input `w₀`, at most
`F.numOr + 1` coordinates in `F.leafSupport` flip `F.eval` from `false` to `true`. -/
theorem card_flipSensitive_le_numOr_add_one (w₀ : BitString n) {F : PosFormula n}
    (hro : F.IsReadOnce) : (flipSensitive w₀ F).card ≤ F.numOr + 1 := by
  induction F with
  | var i =>
    simpa [flipSensitive] using (Finset.card_filter_le ({i} : Finset (Fin n)) _)
  | and L R ihL ihR =>
    obtain ⟨hroL, hroR, hdisj⟩ := hro
    by_cases hL₀ : L.eval w₀ = true
    · have hsub : flipSensitive w₀ (and L R) ⊆ flipSensitive w₀ R := by
        intro v hv
        simp only [flipSensitive, leafSupport_and, Finset.mem_filter, Finset.mem_union,
          eval_and, hL₀, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true'] at hv ⊢
        rcases hv.1 with hvL | hvR
        · have hv_notR : v ∉ R.leafSupport := Finset.disjoint_left.mp hdisj hvL
          have hR_eq : R.eval (Function.update w₀ v true) = R.eval w₀ :=
            R.eval_eq_of_eq_on_leafSupport fun u hu =>
              Function.update_of_ne (ne_of_mem_of_not_mem hu hv_notR) _ _
          rw [hR_eq, hv.2.1] at hv
          exact absurd hv.2.2.2 Bool.false_ne_true
        · exact ⟨hvR, hv.2.1, hv.2.2.2⟩
      calc (flipSensitive w₀ (and L R)).card
          ≤ (flipSensitive w₀ R).card := Finset.card_le_card hsub
        _ ≤ R.numOr + 1 := ihR hroR
        _ ≤ L.numOr + R.numOr + 1 := by omega
    · simp only [Bool.not_eq_true] at hL₀
      have hsub : flipSensitive w₀ (and L R) ⊆ flipSensitive w₀ L := by
        intro v hv
        simp only [flipSensitive, leafSupport_and, Finset.mem_filter, Finset.mem_union,
          eval_and, hL₀, Bool.false_and, Bool.not_false, Bool.true_and,
          Bool.and_eq_true] at hv ⊢
        rcases hv.1 with hvL | hvR
        · exact ⟨hvL, hv.2.1⟩
        · have hv_notL : v ∉ L.leafSupport := Finset.disjoint_right.mp hdisj hvR
          have hL_eq : L.eval (Function.update w₀ v true) = L.eval w₀ :=
            L.eval_eq_of_eq_on_leafSupport fun u hu =>
              Function.update_of_ne (ne_of_mem_of_not_mem hu hv_notL) _ _
          rw [hL_eq, hL₀] at hv
          exact absurd hv.2.1 Bool.false_ne_true
      calc (flipSensitive w₀ (and L R)).card
          ≤ (flipSensitive w₀ L).card := Finset.card_le_card hsub
        _ ≤ L.numOr + 1 := ihL hroL
        _ ≤ L.numOr + R.numOr + 1 := by omega
  | or L R ihL ihR =>
    obtain ⟨hroL, hroR, _⟩ := hro
    have hsub : flipSensitive w₀ (or L R) ⊆ flipSensitive w₀ L ∪ flipSensitive w₀ R := by
      intro v hv
      simp only [flipSensitive, leafSupport_or, Finset.mem_filter, Finset.mem_union,
        eval_or, Bool.not_or, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hv ⊢
      rcases hv.1 with hvL | hvR
      · rcases hv.2.2 with hLv | hRv
        · exact Or.inl ⟨hvL, hv.2.1.1, hLv⟩
        · by_cases hvR' : v ∈ R.leafSupport
          · exact Or.inr ⟨hvR', hv.2.1.2, hRv⟩
          · have hR_eq : R.eval (Function.update w₀ v true) = R.eval w₀ :=
              R.eval_eq_of_eq_on_leafSupport fun u hu =>
                Function.update_of_ne (ne_of_mem_of_not_mem hu hvR') _ _
            rw [hR_eq, hv.2.1.2] at hRv
            exact absurd hRv Bool.false_ne_true
      · rcases hv.2.2 with hLv | hRv
        · by_cases hvL' : v ∈ L.leafSupport
          · exact Or.inl ⟨hvL', hv.2.1.1, hLv⟩
          · have hL_eq : L.eval (Function.update w₀ v true) = L.eval w₀ :=
              L.eval_eq_of_eq_on_leafSupport fun u hu =>
                Function.update_of_ne (ne_of_mem_of_not_mem hu hvL') _ _
            rw [hL_eq, hv.2.1.1] at hLv
            exact absurd hLv Bool.false_ne_true
        · exact Or.inr ⟨hvR, hv.2.1.2, hRv⟩
    calc (flipSensitive w₀ (or L R)).card
        ≤ (flipSensitive w₀ L ∪ flipSensitive w₀ R).card := Finset.card_le_card hsub
      _ ≤ (flipSensitive w₀ L).card + (flipSensitive w₀ R).card := Finset.card_union_le _ _
      _ ≤ (L.numOr + 1) + (R.numOr + 1) := Nat.add_le_add (ihL hroL) (ihR hroR)
      _ = (or L R).numOr + 1 := by simp; omega

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
  | and L R ihL ihR =>
    have hL := L.posLeafCount_le_leafSize
    have hR := R.posLeafCount_le_leafSize
    simp only [posLeafCount, leafSize] at h
    simp only [toPosFormula, PosFormula.eval_and, eval, ihL (by omega), ihR (by omega)]
  | or L R ihL ihR =>
    have hL := L.posLeafCount_le_leafSize
    have hR := R.posLeafCount_le_leafSize
    simp only [posLeafCount, leafSize] at h
    simp only [toPosFormula, PosFormula.eval_or, eval, ihL (by omega), ihR (by omega)]

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

private theorem wire_castSucc_injective'' :
    Function.Injective (Wire.castSucc : Wire n g → Wire n (g + 1)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Wire.castSucc]

@[simp] private theorem wire_lastCases_last {α : Sort*} (last : α) (castSucc : Wire n g → α) :
    Wire.lastCases (motive := fun _ => α) last castSucc (.gate (Fin.last g)) = last := by
  simp [Wire.lastCases]

@[simp] private theorem wire_lastCases_castSucc {α : Sort*} (last : α) (castSucc : Wire n g → α)
    (w : Wire n g) :
    Wire.lastCases (motive := fun _ => α) last castSucc w.castSucc = castSucc w := by
  cases w <;> simp [Wire.lastCases]

private def lineLitFormula (hn : 0 < n) (F' : Wire n g → LitFormula n) :
    (op : Op) → (Fin (signature.Arity op) → Wire n g) → LitFormula n
  | .const _, _ => .lit ⟨0, hn⟩ true
  | .not, wires => (F' (wires 0)).neg
  | .and, wires => .and (F' (wires 0)) (F' (wires 1))
  | .or, wires => .or (F' (wires 0)) (F' (wires 1))

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
    refine ⟨fun w => match w with
      | .input i => .lit i true
      | .gate j => j.elim0, fun w _ x => ?_, ?_⟩
    · cases w with
      | input i => rfl
      | gate j => exact j.elim0
    · have h1 : ∀ w ∈ frontier,
          (match w with | Wire.input i => LitFormula.lit i true | Wire.gate j => j.elim0).leafSize =
            1 := by
        intro w _
        cases w with
        | input _ => rfl
        | gate j => exact j.elim0
      rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one, Program.cost_empty,
        Nat.add_zero]
  | @gate g p line ih =>
    obtain ⟨op, wires⟩ := line
    let prior := Finset.univ.filter fun w : Wire n g => w.castSucc ∈ frontier
    let lineInputs := Finset.univ.image wires
    let opened :=
      if Wire.gate (Fin.last g) ∈ frontier then prior ∪ lineInputs else prior
    have hsub :
        frontier.biUnion (p.gate ⟨op, wires⟩).wireSupport ⊆ opened.biUnion p.wireSupport := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨w, hw, hi⟩ := hi
      revert hw hi
      induction w using Wire.lastCases with
      | last =>
        intro hlast hi
        rw [Program.wireSupport_gate_last] at hi
        obtain ⟨arg, hi⟩ := Line.mem_inputSupport.mp hi
        exact ⟨wires arg, by simp [opened, lineInputs, hlast], hi⟩
      | castSucc w =>
        intro hw hi
        rw [Program.wireSupport_gate_castSucc] at hi
        refine ⟨w, ?_, hi⟩
        by_cases hlast : Wire.gate (Fin.last g) ∈ frontier <;>
          simp [opened, hlast, prior, hw]
    have hcard_sub : (frontier.biUnion (p.gate ⟨op, wires⟩).wireSupport).card ≤
        (opened.biUnion p.wireSupport).card :=
      Finset.card_le_card hsub
    have hp_bound := p.card_biUnion_wireSupport_le_cost_binaryCost opened
    have hline : lineInputs.card ≤ 1 + binaryCost op := by
      calc lineInputs.card ≤ (Finset.univ : Finset (Fin (signature.Arity op))).card :=
            Finset.card_image_le
        _ = signature.Arity op := by simp
        _ ≤ 1 + binaryCost op := Boolean.arity_le_one_add_binaryCost op
    have hprior_image :
        prior.image Wire.castSucc = frontier.erase (Wire.gate (Fin.last g)) := by
      ext w
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, prior]
      constructor
      · rintro ⟨w', hw', rfl⟩
        refine ⟨?_, hw'⟩
        cases w' with
        | input _ => simp
        | gate _ => simp [Fin.castSucc_ne_last]
      · rintro ⟨hne, hw⟩
        induction w using Wire.lastCases with
        | last => exact absurd rfl hne
        | castSucc w' => exact ⟨w', hw, rfl⟩
    have hprior_card : prior.card = (frontier.erase (Wire.gate (Fin.last g))).card := by
      rw [← hprior_image, Finset.card_image_of_injective _ wire_castSucc_injective'']
    have hopened_le : opened.card ≤ frontier.card + binaryCost op := by
      by_cases hlast : Wire.gate (Fin.last g) ∈ frontier
      · have herase := Finset.card_erase_of_mem hlast
        have hpos : 1 ≤ frontier.card := Finset.one_le_card.mpr ⟨_, hlast⟩
        have hopened_eq : opened = prior ∪ lineInputs := by simp [opened, hlast]
        rw [hopened_eq]
        have hunion := Finset.card_union_le prior lineInputs
        omega
      · have herase : frontier.erase (Wire.gate (Fin.last g)) = frontier :=
          Finset.erase_eq_of_notMem hlast
        have hopened_eq : opened = prior := by simp [opened, hlast]
        rw [hopened_eq, hprior_card, herase]
        omega
    have hcost_gate : (p.gate ⟨op, wires⟩).cost binaryCost = p.cost binaryCost + binaryCost op :=
      Program.cost_gate p ⟨op, wires⟩ binaryCost
    have h_opened : opened.card + p.cost binaryCost ≤ (opened.biUnion p.wireSupport).card := by
      omega
    have hopened_eq : opened.card = frontier.card + binaryCost op := by omega
    obtain ⟨F', hF'_eval, hF'_sum⟩ := ih opened h_opened
    let lastFormula : LitFormula n := lineLitFormula hn F' op wires
    let F : Wire n (g + 1) → LitFormula n :=
      Wire.lastCases lastFormula F'
    refine ⟨F, fun w hw x => ?_, ?_⟩
    · induction w using Wire.lastCases with
      | last =>
        have hpos : 1 ≤ frontier.card := Finset.one_le_card.mpr ⟨_, hw⟩
        have herase := Finset.card_erase_of_mem hw
        have hopened_def : opened = prior ∪ lineInputs := by simp [opened, hw]
        have hunion := Finset.card_union_le prior lineInputs
        rw [← hopened_def] at hunion
        have hcard_li : lineInputs.card = 1 + binaryCost op := by omega
        have harity_li : lineInputs.card ≤ signature.Arity op := by
          simpa using (Finset.card_image_le :
            lineInputs.card ≤ (Finset.univ : Finset (Fin (signature.Arity op))).card)
        have harity_eq : signature.Arity op = 1 + binaryCost op := by
          have := Boolean.arity_le_one_add_binaryCost op
          omega
        have hmem_li (a : Fin (signature.Arity op)) : wires a ∈ opened := by
          rw [hopened_def]
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
        simp only [F, wire_lastCases_last, Program.trace_gate_last]
        change (lineLitFormula hn F' op wires).eval x =
          interpretation op fun a => p.trace interpretation x (wires a)
        cases op with
        | const b =>
          simp at harity_eq
        | not =>
          have h0 := hF'_eval (wires 0) (hmem_li 0) x
          simp [lineLitFormula, h0, interpretation]
        | and =>
          have h0 := hF'_eval (wires 0) (hmem_li 0) x
          have h1 := hF'_eval (wires 1) (hmem_li 1) x
          simp [lineLitFormula, h0, h1, interpretation, LitFormula.eval]
        | or =>
          have h0 := hF'_eval (wires 0) (hmem_li 0) x
          have h1 := hF'_eval (wires 1) (hmem_li 1) x
          simp [lineLitFormula, h0, h1, interpretation, LitFormula.eval]
      | castSucc w' =>
        have hw'_open : w' ∈ opened := by
          by_cases hlast : Wire.gate (Fin.last g) ∈ frontier <;>
            simp [opened, hlast, prior, hw]
        rw [show F w'.castSucc = F' w' from wire_lastCases_castSucc lastFormula F' w',
          Program.trace_gate_castSucc]
        exact hF'_eval w' hw'_open x
    · have hsum_prior :
          ∑ w ∈ frontier.erase (Wire.gate (Fin.last g)), (F w).leafSize =
            ∑ w' ∈ prior, (F' w').leafSize := by
        rw [← hprior_image, Finset.sum_image fun a _ b _ hab => wire_castSucc_injective'' hab]
        exact Finset.sum_congr rfl fun w' _ => by
          rw [show F w'.castSucc = F' w' from wire_lastCases_castSucc lastFormula F' w']
      by_cases hlast : Wire.gate (Fin.last g) ∈ frontier
      · have hpos : 1 ≤ frontier.card := Finset.one_le_card.mpr ⟨_, hlast⟩
        have herase := Finset.card_erase_of_mem hlast
        have hopened_def : opened = prior ∪ lineInputs := by simp [opened, hlast]
        have hunion := Finset.card_union_add_card_inter prior lineInputs
        have harity_li : lineInputs.card ≤ signature.Arity op := by
          simpa using (Finset.card_image_le :
            lineInputs.card ≤ (Finset.univ : Finset (Fin (signature.Arity op))).card)
        have harity_le := Boolean.arity_le_one_add_binaryCost op
        have h_inter_zero : (prior ∩ lineInputs).card = 0 := by
          rw [← hopened_def] at hunion
          omega
        have hdisj : Disjoint prior lineInputs :=
          Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h_inter_zero)
        have hcard_li : lineInputs.card = signature.Arity op := by
          rw [← hopened_def] at hunion
          omega
        have harity_eq : signature.Arity op = 1 + binaryCost op := by
          rw [← hopened_def] at hunion
          omega
        have hlast_leaf :
            (F (Wire.gate (Fin.last g))).leafSize = ∑ w ∈ lineInputs, (F' w).leafSize := by
          rw [show F (Wire.gate (Fin.last g)) = lineLitFormula hn F' op wires from
            wire_lastCases_last lastFormula F']
          cases op with
          | const b =>
            simp at harity_eq
          | not =>
            have hli_eq : lineInputs = {wires 0} := by
              ext w
              simp only [lineInputs, Finset.mem_image, Finset.mem_univ, true_and,
                Finset.mem_singleton]
              constructor
              · rintro ⟨a, rfl⟩
                congr 1
                exact Subsingleton.elim a 0
              · rintro rfl
                exact ⟨0, rfl⟩
            simp [lineLitFormula, hli_eq]
          | and =>
            have hli_eq : lineInputs = {wires 0, wires 1} := by
              ext w
              simp only [lineInputs, Finset.mem_image, Finset.mem_univ, true_and,
                Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨a, rfl⟩
                exact (Boolean.Op.isBinary_and.eq_or_eq (by decide) a).imp
                  (congrArg wires) (congrArg wires)
              · rintro (rfl | rfl)
                · exact ⟨0, rfl⟩
                · exact ⟨1, rfl⟩
            have hw_ne : wires 0 ≠ wires 1 := by
              intro heq
              rw [hli_eq, heq, Finset.pair_eq_singleton, Finset.card_singleton] at hcard_li
              revert hcard_li; decide
            rw [hli_eq, Finset.sum_pair hw_ne]
            rfl
          | or =>
            have hli_eq : lineInputs = {wires 0, wires 1} := by
              ext w
              simp only [lineInputs, Finset.mem_image, Finset.mem_univ, true_and,
                Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨a, rfl⟩
                exact (Boolean.Op.isBinary_or.eq_or_eq (by decide) a).imp
                  (congrArg wires) (congrArg wires)
              · rintro (rfl | rfl)
                · exact ⟨0, rfl⟩
                · exact ⟨1, rfl⟩
            have hw_ne : wires 0 ≠ wires 1 := by
              intro heq
              rw [hli_eq, heq, Finset.pair_eq_singleton, Finset.card_singleton] at hcard_li
              revert hcard_li; decide
            rw [hli_eq, Finset.sum_pair hw_ne]
            rfl
        rw [← Finset.sum_erase_add _ _ hlast, hsum_prior, hlast_leaf,
          ← Finset.sum_union hdisj, ← hopened_def, hF'_sum, hopened_eq, hcost_gate]
        omega
      · have herase : frontier.erase (Wire.gate (Fin.last g)) = frontier :=
          Finset.erase_eq_of_notMem hlast
        have hopened_def : opened = prior := by simp [opened, hlast]
        have hsum_f : ∑ w ∈ frontier, (F w).leafSize = ∑ w' ∈ prior, (F' w').leafSize := by
          rw [← herase, hsum_prior]
        rw [hsum_f, ← hopened_def, hF'_sum, hopened_eq, hcost_gate]
        omega

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
