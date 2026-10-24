/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Foundations.Data.BitString.PartialAssignment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Restrictions of De Morgan formulas

Restricting a De Morgan formula by a partial assignment `ρ` (`Formula.restrict`) replaces the
leaves of the fixed inputs by constants and simplifies bottom up: constants are propagated through
the gates, and double negations cancel. The result computes the restricted function
`F.eval ∘ ρ.fill` (`Formula.eval_restrict`) and keeps only the leaves of the free inputs
(`Formula.leafSize_restrict_le`). It is a constant or a *simplified* formula
(`Formula.IsSimplified`): one without constants or double negations, which has at most `3 L - 2`
operation nodes for `L` leaves (`Formula.IsSimplified.size_add_two_le`). In particular a formula
whose restriction has no leaves restricts to a constant (`Formula.exists_restrict_eq_const`).

The *formula size* `Boolean.formulaSize f` of a Boolean function is the least leaf size of a De
Morgan formula computing it, Jukna's `L(f)` [Jukna, Chapter 6][Jukna2012]. Restrictions do not
increase it (`Boolean.formulaSize_comp_fill_le`), and a function depending only on a set `S` of
inputs has a formula of least leaf size whose leaves all read inputs in `S`
(`Boolean.leafSizeIn_eq_leafSize_of_dependsOn`). Every function has a formula of least leaf size
with at most `3 L(f) - 2` operation nodes, or a constant (`Boolean.exists_computes_size_le`).

## Main definitions

* `Cslib.Circuits.Formula.mkNot`, `Cslib.Circuits.Formula.mkAnd`, `Cslib.Circuits.Formula.mkOr`:
  negation, conjunction and disjunction, simplifying constants and double negations.
* `Cslib.Circuits.Formula.restrict`: the restriction of a formula by a partial assignment.
* `Cslib.Circuits.Formula.IsSimplified`: formulas without constants or double negations.
* `Cslib.Circuits.Boolean.formulaSize`: the least leaf size of a De Morgan formula computing a
  function.

## Main results

* `Cslib.Circuits.Formula.eval_restrict`: a restriction computes the restricted function.
* `Cslib.Circuits.Formula.leafSize_restrict_le`: a restriction keeps only the leaves of the free
  inputs.
* `Cslib.Circuits.Formula.restrict_eq_const_or_isSimplified`: a restriction is a constant or
  simplified.
* `Cslib.Circuits.Boolean.formulaSize_le`, `Cslib.Circuits.Boolean.exists_computes_leafSize_eq`:
  the formula size is the least leaf size, and it is attained.
* `Cslib.Circuits.Boolean.formulaSize_comp_fill_le_leafSizeIn`,
  `Cslib.Circuits.Boolean.formulaSize_comp_fill_le`: restrictions do not increase the formula
  size.
* `Cslib.Circuits.Boolean.exists_computes_size_le`: a formula of least leaf size with few
  operation nodes.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Formula

open Boolean BitString

variable {n : ℕ}

/-! ### Simplifying gates -/

/-- The value of a constant formula, and `none` for every other formula. -/
def constValue? : Formula signature n → Option Bool
  | gate (.const b) _ => some b
  | _ => none

@[simp] theorem constValue?_const (b : Bool) :
    (const b : Formula signature n).constValue? = some b :=
  rfl

/-- A formula with a constant value is that constant. -/
private theorem eq_const_of_constValue? {F : Formula signature n} {b : Bool}
    (h : F.constValue? = some b) :
    F = const b := by
  match F, h with
  | gate (.const _) args, rfl => exact congrArg (gate _) (funext fun j => j.elim0)

/-- A formula is either a constant or has `constValue? = none`. -/
private theorem eq_const_or_constValue?_eq_none (F : Formula signature n) :
    (∃ b, F = const b) ∨ F.constValue? = none := by
  cases h : F.constValue? with
  | none => exact Or.inr rfl
  | some b => exact Or.inl ⟨b, eq_const_of_constValue? h⟩

/-- Negation, cancelling a double negation and evaluating a negated constant. -/
def mkNot : Formula signature n → Formula signature n
  | gate (.const b) _ => const (!b)
  | gate .not args => args 0
  | F => F.not

/-- Conjunction, simplifying constant arguments. -/
def mkAnd (F G : Formula signature n) : Formula signature n :=
  match F.constValue?, G.constValue? with
  | some false, _ => const false
  | some true, _ => G
  | none, some false => const false
  | none, some true => F
  | none, none => F.and G

/-- Disjunction, simplifying constant arguments. -/
def mkOr (F G : Formula signature n) : Formula signature n :=
  match F.constValue?, G.constValue? with
  | some true, _ => const true
  | some false, _ => G
  | none, some true => const true
  | none, some false => F
  | none, none => F.or G

/-- A unary node is the negation of its argument. -/
theorem gate_not_eq (args : Fin (signature.Arity Op.not) → Formula signature n) :
    gate Op.not args = (args 0).not := by
  unfold Formula.not
  congr 1
  funext j
  fin_cases j
  rfl

/-- A binary `.and` node is the conjunction of its arguments. -/
theorem gate_and_eq (args : Fin (signature.Arity Op.and) → Formula signature n) :
    gate Op.and args = (args 0).and (args 1) := by
  unfold Formula.and
  congr 1
  funext j
  fin_cases j <;> rfl

/-- A binary `.or` node is the disjunction of its arguments. -/
theorem gate_or_eq (args : Fin (signature.Arity Op.or) → Formula signature n) :
    gate Op.or args = (args 0).or (args 1) := by
  unfold Formula.or
  congr 1
  funext j
  fin_cases j <;> rfl

@[simp] theorem mkNot_const (b : Bool) : mkNot (const b : Formula signature n) = const (!b) :=
  rfl

@[simp] theorem mkNot_not (F : Formula signature n) : mkNot F.not = F :=
  rfl

@[simp] theorem mkNot_input (i : Fin n) : mkNot (input i : Formula signature n) = (input i).not :=
  rfl

@[simp] theorem mkNot_and (F G : Formula signature n) : mkNot (F.and G) = (F.and G).not :=
  rfl

@[simp] theorem mkNot_or (F G : Formula signature n) : mkNot (F.or G) = (F.or G).not :=
  rfl

variable (x : BitString n)

@[simp] theorem eval_mkNot (F : Formula signature n) :
    (mkNot F).eval interpretation x = !F.eval interpretation x := by
  cases F with
  | input i => rfl
  | gate op args =>
    cases op with
    | const b => rfl
    | not =>
      rw [gate_not_eq, mkNot_not, eval_not, Bool.not_not]
    | and => rw [gate_and_eq, mkNot_and, eval_not]
    | or => rw [gate_or_eq, mkNot_or, eval_not]

@[simp] theorem leafSize_mkNot (F : Formula signature n) : (mkNot F).leafSize = F.leafSize := by
  cases F with
  | input i => rfl
  | gate op args =>
    cases op with
    | const b => rfl
    | not => rw [gate_not_eq, mkNot_not, leafSize_not]
    | and => rw [gate_and_eq, mkNot_and, leafSize_not]
    | or => rw [gate_or_eq, mkNot_or, leafSize_not]

@[simp] theorem eval_mkAnd (F G : Formula signature n) :
    (mkAnd F G).eval interpretation x = (F.eval interpretation x && G.eval interpretation x) := by
  rcases eq_const_or_constValue?_eq_none F with ⟨_ | _, rfl⟩ | hF <;>
    rcases eq_const_or_constValue?_eq_none G with ⟨_ | _, rfl⟩ | hG <;>
    simp_all [mkAnd]

@[simp] theorem eval_mkOr (F G : Formula signature n) :
    (mkOr F G).eval interpretation x = (F.eval interpretation x || G.eval interpretation x) := by
  rcases eq_const_or_constValue?_eq_none F with ⟨_ | _, rfl⟩ | hF <;>
    rcases eq_const_or_constValue?_eq_none G with ⟨_ | _, rfl⟩ | hG <;>
    simp_all [mkOr]

theorem leafSize_mkAnd_le (F G : Formula signature n) :
    (mkAnd F G).leafSize ≤ F.leafSize + G.leafSize := by
  rcases eq_const_or_constValue?_eq_none F with ⟨_ | _, rfl⟩ | hF <;>
    rcases eq_const_or_constValue?_eq_none G with ⟨_ | _, rfl⟩ | hG <;>
    simp_all [mkAnd]

theorem leafSize_mkOr_le (F G : Formula signature n) :
    (mkOr F G).leafSize ≤ F.leafSize + G.leafSize := by
  rcases eq_const_or_constValue?_eq_none F with ⟨_ | _, rfl⟩ | hF <;>
    rcases eq_const_or_constValue?_eq_none G with ⟨_ | _, rfl⟩ | hG <;>
    simp_all [mkOr]

@[simp] theorem mkAnd_const_false_left (G : Formula signature n) :
    mkAnd (const false) G = const false :=
  rfl

@[simp] theorem mkAnd_const_true_left (G : Formula signature n) : mkAnd (const true) G = G :=
  rfl

@[simp] theorem mkAnd_const_false_right (F : Formula signature n) :
    mkAnd F (const false) = const false := by
  rcases eq_const_or_constValue?_eq_none F with ⟨_ | _, rfl⟩ | hF <;> simp_all [mkAnd]

@[simp] theorem mkAnd_const_true_right (F : Formula signature n) : mkAnd F (const true) = F := by
  rcases eq_const_or_constValue?_eq_none F with ⟨_ | _, rfl⟩ | hF <;> simp_all [mkAnd]

@[simp] theorem mkOr_const_true_left (G : Formula signature n) :
    mkOr (const true) G = const true :=
  rfl

@[simp] theorem mkOr_const_false_left (G : Formula signature n) : mkOr (const false) G = G :=
  rfl

@[simp] theorem mkOr_const_true_right (F : Formula signature n) :
    mkOr F (const true) = const true := by
  rcases eq_const_or_constValue?_eq_none F with ⟨_ | _, rfl⟩ | hF <;> simp_all [mkOr]

@[simp] theorem mkOr_const_false_right (F : Formula signature n) : mkOr F (const false) = F := by
  rcases eq_const_or_constValue?_eq_none F with ⟨_ | _, rfl⟩ | hF <;> simp_all [mkOr]

/-! ### Restriction -/

/-- The restriction of a formula by a partial assignment `ρ`: the leaves of the inputs fixed by
`ρ` become constants, and constants and double negations are simplified bottom up. -/
def restrict (ρ : PartialAssignment (Fin n)) : Formula signature n → Formula signature n
  | input i => (ρ i).elim (input i) const
  | gate (.const b) _ => const b
  | gate .not args => mkNot ((args 0).restrict ρ)
  | gate .and args => mkAnd ((args 0).restrict ρ) ((args 1).restrict ρ)
  | gate .or args => mkOr ((args 0).restrict ρ) ((args 1).restrict ρ)

variable (ρ : PartialAssignment (Fin n))

@[simp] theorem restrict_input (i : Fin n) :
    (input i : Formula signature n).restrict ρ = (ρ i).elim (input i) const :=
  rfl

@[simp] theorem restrict_const (b : Bool) : (const b : Formula signature n).restrict ρ = const b :=
  rfl

@[simp] theorem restrict_not (F : Formula signature n) :
    F.not.restrict ρ = mkNot (F.restrict ρ) :=
  rfl

@[simp] theorem restrict_and (F G : Formula signature n) :
    (F.and G).restrict ρ = mkAnd (F.restrict ρ) (G.restrict ρ) :=
  rfl

@[simp] theorem restrict_or (F G : Formula signature n) :
    (F.or G).restrict ρ = mkOr (F.restrict ρ) (G.restrict ρ) :=
  rfl

private theorem restrict_input_of_eq_none {i : Fin n} (h : ρ i = none) :
    (input i : Formula signature n).restrict ρ = input i := by
  simp [h]

private theorem restrict_input_of_eq_some {i : Fin n} {b : Bool} (h : ρ i = some b) :
    (input i : Formula signature n).restrict ρ = const b := by
  simp [h]

/-- A restriction computes the restricted function: it reads the fixed inputs from `ρ`. -/
@[simp] theorem eval_restrict (F : Formula signature n) :
    (F.restrict ρ).eval interpretation x = F.eval interpretation (ρ.fill x) := by
  induction F with
  | input i =>
    cases h : ρ i with
    | none => rw [restrict_input_of_eq_none ρ h, eval_input, eval_input,
        PartialAssignment.fill_of_eq_none h]
    | some b => rw [restrict_input_of_eq_some ρ h, eval_input, eval_const,
        PartialAssignment.fill_of_eq_some h]
  | gate op args ih =>
    cases op with
    | const b => rfl
    | not => rw [gate_not_eq, restrict_not, eval_mkNot, eval_not, ih 0]
    | and => rw [gate_and_eq, restrict_and, eval_mkAnd, eval_and, ih 0, ih 1]
    | or => rw [gate_or_eq, restrict_or, eval_mkOr, eval_or, ih 0, ih 1]

/-- A restriction keeps only the leaves of the free inputs. -/
theorem leafSize_restrict_le (F : Formula signature n) :
    (F.restrict ρ).leafSize ≤ F.leafSizeIn ρ.free := by
  induction F with
  | input i =>
    cases h : ρ i with
    | none => simp [restrict_input_of_eq_none ρ h, h]
    | some b => simp [restrict_input_of_eq_some ρ h]
  | gate op args ih =>
    cases op with
    | const b => simp [restrict]
    | not =>
      rw [gate_not_eq, restrict_not, leafSize_mkNot, leafSizeIn_not]
      exact ih 0
    | and =>
      rw [gate_and_eq, restrict_and, leafSizeIn_and]
      exact (leafSize_mkAnd_le _ _).trans (Nat.add_le_add (ih 0) (ih 1))
    | or =>
      rw [gate_or_eq, restrict_or, leafSizeIn_or]
      exact (leafSize_mkOr_le _ _).trans (Nat.add_le_add (ih 0) (ih 1))

/-- Restricting by an assignment of a single input removes its leaves. -/
theorem leafSize_restrict_update_le (F : Formula signature n) (i : Fin n) (b : Bool) :
    (F.restrict (Function.update PartialAssignment.empty i (some b))).leafSize + F.leafSizeIn {i} ≤
      F.leafSize := by
  have h := leafSize_restrict_le (Function.update PartialAssignment.empty i (some b)) F
  have hfree : PartialAssignment.free (Function.update PartialAssignment.empty i (some b)) =
      {i}ᶜ := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [hfree] at h
  have := leafSizeIn_add_leafSizeIn_compl {i} F
  omega

/-! ### Simplified formulas -/

/-- A De Morgan formula is *simplified* when it has no constants and no double negations: it is
built from inputs by conjunctions and disjunctions, and negations of inputs, conjunctions and
disjunctions. -/
inductive IsSimplified : Formula signature n → Prop
  /-- An input. -/
  | input (i : Fin n) : (input i).IsSimplified
  /-- A negated input. -/
  | not_input (i : Fin n) : (input i).not.IsSimplified
  /-- A conjunction of simplified formulas. -/
  | and {F G : Formula signature n} : F.IsSimplified → G.IsSimplified → (F.and G).IsSimplified
  /-- A disjunction of simplified formulas. -/
  | or {F G : Formula signature n} : F.IsSimplified → G.IsSimplified → (F.or G).IsSimplified
  /-- A negated conjunction of simplified formulas. -/
  | not_and {F G : Formula signature n} :
      F.IsSimplified → G.IsSimplified → (F.and G).not.IsSimplified
  /-- A negated disjunction of simplified formulas. -/
  | not_or {F G : Formula signature n} :
      F.IsSimplified → G.IsSimplified → (F.or G).not.IsSimplified

theorem IsSimplified.constValue?_eq_none {F : Formula signature n} (hF : F.IsSimplified) :
    F.constValue? = none := by
  cases hF <;> rfl

/-- A simplified formula has a leaf. -/
private theorem IsSimplified.one_le_leafSize {F : Formula signature n} (hF : F.IsSimplified) :
    1 ≤ F.leafSize := by
  induction hF <;> simp only [leafSize_input, leafSize_not, leafSize_and, leafSize_or] <;> omega

/-- A simplified formula with `L` leaves has at most `3 L - 2` operation nodes. -/
theorem IsSimplified.size_add_two_le {F : Formula signature n} (hF : F.IsSimplified) :
    F.size + 2 ≤ 3 * F.leafSize := by
  induction hF <;>
    simp only [size_input, size_not, size_and, size_or, leafSize_input, leafSize_not,
      leafSize_and, leafSize_or] <;> omega

/-- A formula that is a constant or simplified. -/
private def ConstOrSimplified (F : Formula signature n) : Prop :=
  (∃ b, F = const b) ∨ F.IsSimplified

private theorem constOrSimplified_mkNot {F : Formula signature n} (hF : ConstOrSimplified F) :
    ConstOrSimplified (mkNot F) := by
  rcases hF with ⟨b, rfl⟩ | hF
  · exact Or.inl ⟨!b, rfl⟩
  · refine Or.inr ?_
    cases hF with
    | input i => exact .not_input i
    | not_input i => exact .input i
    | and hF hG => exact .not_and hF hG
    | or hF hG => exact .not_or hF hG
    | not_and hF hG => exact .and hF hG
    | not_or hF hG => exact .or hF hG

private theorem constValue?_eq_none_of_constOrSimplified {F : Formula signature n}
    (hF : ConstOrSimplified F) (h : ∀ b, F.constValue? ≠ some b) : F.IsSimplified := by
  rcases hF with ⟨b, rfl⟩ | hF
  · exact absurd rfl (h b)
  · exact hF

private theorem constOrSimplified_mkAnd {F G : Formula signature n} (hF : ConstOrSimplified F)
    (hG : ConstOrSimplified G) : ConstOrSimplified (mkAnd F G) := by
  unfold mkAnd
  split
  · exact Or.inl ⟨false, rfl⟩
  · exact hG
  · exact Or.inl ⟨false, rfl⟩
  · exact hF
  · rename_i hF' hG'
    exact Or.inr (.and (constValue?_eq_none_of_constOrSimplified hF (by simp [hF']))
      (constValue?_eq_none_of_constOrSimplified hG (by simp [hG'])))

private theorem constOrSimplified_mkOr {F G : Formula signature n} (hF : ConstOrSimplified F)
    (hG : ConstOrSimplified G) : ConstOrSimplified (mkOr F G) := by
  unfold mkOr
  split
  · exact Or.inl ⟨true, rfl⟩
  · exact hG
  · exact Or.inl ⟨true, rfl⟩
  · exact hF
  · rename_i hF' hG'
    exact Or.inr (.or (constValue?_eq_none_of_constOrSimplified hF (by simp [hF']))
      (constValue?_eq_none_of_constOrSimplified hG (by simp [hG'])))

/-- A restriction is a constant or a simplified formula. -/
theorem restrict_eq_const_or_isSimplified (F : Formula signature n) :
    (∃ b, F.restrict ρ = const b) ∨ (F.restrict ρ).IsSimplified := by
  change ConstOrSimplified (F.restrict ρ)
  induction F with
  | input i =>
    cases h : ρ i with
    | none => exact Or.inr (by rw [restrict_input_of_eq_none ρ h]; exact .input i)
    | some b => exact Or.inl ⟨b, restrict_input_of_eq_some ρ h⟩
  | gate op args ih =>
    cases op with
    | const b => exact Or.inl ⟨b, rfl⟩
    | not => exact constOrSimplified_mkNot (ih 0)
    | and => exact constOrSimplified_mkAnd (ih 0) (ih 1)
    | or => exact constOrSimplified_mkOr (ih 0) (ih 1)

/-- A restriction without leaves is a constant. -/
theorem exists_restrict_eq_const {F : Formula signature n} (h : (F.restrict ρ).leafSize = 0) :
    ∃ b, F.restrict ρ = const b :=
  (restrict_eq_const_or_isSimplified ρ F).resolve_right fun hs => by
    have := hs.one_le_leafSize
    omega

end Formula

/-! ### Formula size -/

namespace Boolean

open Formula BitString

variable {n : ℕ} {f : BooleanFunction n}

/-- The *formula size* of a Boolean function: the least leaf size of a De Morgan formula computing
it, Jukna's `L(f)` [Jukna, Chapter 6][Jukna2012]. Every function has a formula
(`Formula.exists_computes`), so the least leaf size exists. -/
noncomputable def formulaSize (f : BooleanFunction n) : ℕ :=
  sInf {L | ∃ F : Formula signature n, F.Computes interpretation f ∧ F.leafSize = L}

/-- The formula size is at most the leaf size of every formula computing the function. -/
theorem formulaSize_le {F : Formula signature n} (hF : F.Computes interpretation f) :
    formulaSize f ≤ F.leafSize :=
  Nat.sInf_le ⟨F, hF, rfl⟩

/-- Some formula computing the function has the least leaf size. -/
theorem exists_computes_leafSize_eq (f : BooleanFunction n) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧ F.leafSize = formulaSize f := by
  obtain ⟨F, hF⟩ := Formula.exists_computes f
  exact Nat.sInf_mem (s := {L | ∃ F : Formula signature n, F.Computes interpretation f ∧
    F.leafSize = L}) ⟨_, F, hF, rfl⟩

/-- Lower bounds on the formula size are lower bounds on the leaf size of every formula. -/
theorem le_formulaSize_iff {k : ℕ} :
    k ≤ formulaSize f ↔ ∀ F : Formula signature n, F.Computes interpretation f → k ≤ F.leafSize :=
  ⟨fun h _ hF => h.trans (formulaSize_le hF), fun h => by
    obtain ⟨F, hF, hL⟩ := exists_computes_leafSize_eq f
    exact hL ▸ h F hF⟩

/-- A constant function has formula size zero. -/
@[simp] theorem formulaSize_const (b : Bool) : formulaSize (fun _ : BitString n => b) = 0 :=
  Nat.le_zero.1 (formulaSize_le (F := const b) fun _ => rfl)

/-- A function of no inputs has formula size zero. -/
theorem formulaSize_eq_zero_of_dependsOn_empty (hf : DependsOn f ∅) : formulaSize f = 0 := by
  have : f = fun _ => f (fun _ => false) := funext fun x => hf.empty x _
  rw [this, formulaSize_const]

/-- A restriction of a formula computing `f` computes the restriction of `f`, with only the leaves
of the free inputs. -/
theorem formulaSize_comp_fill_le_leafSizeIn {F : Formula signature n}
    (hF : F.Computes interpretation f) (ρ : PartialAssignment (Fin n)) :
    formulaSize (f ∘ ρ.fill) ≤ F.leafSizeIn ρ.free :=
  (formulaSize_le (F := F.restrict ρ) fun x => by
    rw [eval_restrict, hF]
    rfl).trans (leafSize_restrict_le ρ F)

/-- Restricting a Boolean function by a partial assignment does not increase its formula size. -/
theorem formulaSize_comp_fill_le (f : BooleanFunction n) (ρ : PartialAssignment (Fin n)) :
    formulaSize (f ∘ ρ.fill) ≤ formulaSize f := by
  obtain ⟨F, hF, hFL⟩ := exists_computes_leafSize_eq f
  exact (formulaSize_comp_fill_le_leafSizeIn hF ρ).trans
    ((leafSizeIn_le_leafSize ρ.free F).trans hFL.le)

/-- A formula of least leaf size for a function depending only on the inputs in `S` has all its
leaves in `S`. -/
theorem leafSizeIn_eq_leafSize_of_dependsOn {S : Finset (Fin n)} (hf : DependsOn f S)
    {F : Formula signature n} (hF : F.Computes interpretation f)
    (hmin : F.leafSize = formulaSize f) : F.leafSizeIn S = F.leafSize := by
  refine le_antisymm (leafSizeIn_le_leafSize S F) ?_
  have hρ : f ∘ (PartialAssignment.outside S fun _ => false).fill = f :=
    funext fun x => hf fun i hi => by
      simp only [PartialAssignment.fill_outside]
      exact Finset.piecewise_eq_of_mem _ _ _ hi
  have := formulaSize_comp_fill_le_leafSizeIn hF (PartialAssignment.outside S fun _ => false)
  rw [hρ, PartialAssignment.free_outside] at this
  omega

/-- Every function has a formula of least leaf size that is a constant or has at most `3 L - 2`
operation nodes for `L` leaves. -/
theorem exists_computes_size_le (f : BooleanFunction n) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧ F.leafSize = formulaSize f ∧
      ((∃ b, F = const b) ∨ F.size + 2 ≤ 3 * formulaSize f) := by
  obtain ⟨F, hF, hL⟩ := exists_computes_leafSize_eq f
  have hc : (F.restrict PartialAssignment.empty).Computes interpretation f := fun x => by
    rw [eval_restrict, PartialAssignment.fill_empty, hF]
  have hle : (F.restrict PartialAssignment.empty).leafSize ≤ formulaSize f := by
    have := leafSize_restrict_le PartialAssignment.empty F
    rw [PartialAssignment.free_empty, leafSizeIn_univ, hL] at this
    exact this
  have heq := le_antisymm hle (formulaSize_le hc)
  refine ⟨_, hc, heq, ?_⟩
  rcases restrict_eq_const_or_isSimplified PartialAssignment.empty F with h | h
  · exact Or.inl h
  · exact Or.inr (heq ▸ h.size_add_two_le)

end Boolean

end Cslib.Circuits
