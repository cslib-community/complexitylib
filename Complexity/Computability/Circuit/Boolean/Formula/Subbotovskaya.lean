/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula.Restriction
public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Foundations.Data.BitString.PartialAssignment.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Subbotovskaya's random restriction method

Fixing a variable `i` of a reduced De Morgan formula to a random constant removes the `ℓ_i` leaves
labelled by `i`, and for each such leaf that feeds a binary gate, the constant annihilates the gate
under one of the two values of `i`, eliminating the gate's other argument as well. Subbotovskaya
[Subbotovskaya1961] used this observation to show that a formula of least leaf size `L ≥ 2` shrinks
on average by at least `3 L / (2 s)` leaves when one of its `s` variables is fixed at random
(`Formula.IsLeafMinimal.leafSize_restrictAt_false_add_true_le`,
`Boolean.sum_formulaSize_restrict_update_le`), and therefore that restricting to `k` variables
shrinks the formula size by a factor of `(k / n) ^ (3 / 2)` [Jukna, Lemma 6.12][Jukna2012].

Stated without fractional powers by squaring both sides, every Boolean function on `n` bits and
every `1 ≤ k ≤ n` has a partial assignment with `k` free bits under which
`L(f↾ρ) ^ 2 * n ^ 3 ≤ L(f) ^ 2 * k ^ 3` (`Boolean.exists_withFree_formulaSize_sq_mul_pow_three_le`).
Taking `k = 1` gives Subbotovskaya's `n ^ (3 / 2)` lower bound for parity
(`Boolean.pow_three_le_formulaSize_parity_sq`), the first superlinear formula lower bound.
Averaging over all extensions with `k` free bits bounds the average restricted formula size, ready
to be combined with a union bound in Andreev's theorem
(`Boolean.sum_extensions_formulaSize_sub_sq_le`, `Boolean.exists_mem_formulaSize_sub_sq_le`).

## Main definitions

* `Cslib.Circuits.Formula.restrictAt`: restrict a De Morgan formula by fixing one input to a
  Boolean constant.
* `Cslib.Circuits.Formula.IsLeafMinimal`: formulas whose leaf size is the least among all formulas
  computing the same function.

## Main results

* `Cslib.Circuits.Formula.IsLeafMinimal.leafSize_restrictAt_false_add_true_le`: fixing input `i` to
  `false` and `true` in a leaf-minimal formula that is not a single `i`-leaf gives
  `L(F↾(i = 0)) + L(F↾(i = 1)) + 3 ℓ_i(F) ≤ 2 L(F)`.
* `Cslib.Circuits.Boolean.sum_formulaSize_restrict_update_le`: summing over `s` free inputs bounds
  restricted formula sizes by `(2 s - 3) L(f↾ρ)` when `L(f↾ρ) ≠ 1` (and `2 s - 2` when `L = 1`).
* `Cslib.Circuits.Boolean.exists_extensions_formulaSize_sq_mul_pow_three_le`,
  `Cslib.Circuits.Boolean.exists_withFree_formulaSize_sq_mul_pow_three_le`: Subbotovskaya's
  shrinkage lemma for `k` surviving free inputs.
* `Cslib.Circuits.Boolean.pow_three_le_formulaSize_parity_sq`,
  `Cslib.Circuits.Boolean.pow_three_le_leafSize_sq_of_computes_parity`: Subbotovskaya's
  `n ^ (3 / 2)` formula leaf-size lower bound for parity.
* `Cslib.Circuits.Boolean.sum_extensions_formulaSize_sub_sq_le`,
  `Cslib.Circuits.Boolean.exists_mem_formulaSize_sub_sq_le`: average shrinkage over all extensions
  leaving `k` inputs free, and existence of a small restriction inside any dense subset.

## References

* [B. A. Subbotovskaya, *Realizations of Linear Functions by Formulas Using `∨`, `&`, `-`*
  ][Subbotovskaya1961]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean BitString Finset Function

variable {n : ℕ}

namespace Formula

/-! ### Restricting a single input -/

/-- Restrict a De Morgan formula by fixing input `i` to `b` and leaving all other inputs free. -/
def restrictAt (i : Fin n) (b : Bool) (F : Formula signature n) : Formula signature n :=
  F.restrict (update PartialAssignment.empty i (some b))

@[simp] theorem eval_restrictAt (i : Fin n) (b : Bool) (F : Formula signature n)
    (x : BitString n) :
    (F.restrictAt i b).eval interpretation x = F.eval interpretation (update x i b) := by
  simp [restrictAt]

private theorem leafSize_restrictAt_add_leafSizeIn_le (F : Formula signature n) (i : Fin n)
    (b : Bool) :
    (F.restrictAt i b).leafSize + F.leafSizeIn {i} ≤ F.leafSize :=
  leafSize_restrict_update_le F i b

@[simp] theorem restrictAt_const (i : Fin n) (b c : Bool) :
    (const c : Formula signature n).restrictAt i b = const c :=
  rfl

@[simp] theorem restrictAt_not (i : Fin n) (b : Bool) (F : Formula signature n) :
    F.not.restrictAt i b = mkNot (F.restrictAt i b) :=
  rfl

@[simp] theorem restrictAt_and (i : Fin n) (b : Bool) (F G : Formula signature n) :
    (F.and G).restrictAt i b = mkAnd (F.restrictAt i b) (G.restrictAt i b) :=
  rfl

@[simp] theorem restrictAt_or (i : Fin n) (b : Bool) (F G : Formula signature n) :
    (F.or G).restrictAt i b = mkOr (F.restrictAt i b) (G.restrictAt i b) :=
  rfl

theorem restrictAt_input_self (i : Fin n) (b : Bool) :
    (input i : Formula signature n).restrictAt i b = const b := by
  simp [restrictAt]

private theorem restrictAt_input_of_ne {i j : Fin n} (h : j ≠ i) (b : Bool) :
    (input j : Formula signature n).restrictAt i b = input j := by
  simp [restrictAt, h]

/-! ### Leaf-minimal formulas -/

/-- A De Morgan formula is *leaf-minimal* when no formula with fewer leaves computes the same
Boolean function. -/
def IsLeafMinimal (F : Formula signature n) : Prop :=
  ∀ G : Formula signature n, G.Computes interpretation (F.eval interpretation) →
    F.leafSize ≤ G.leafSize

/-- A formula is leaf-minimal exactly when its leaf size equals the formula size of the function it
computes. -/
theorem isLeafMinimal_iff_leafSize_eq_formulaSize {F : Formula signature n} :
    F.IsLeafMinimal ↔ F.leafSize = formulaSize (F.eval interpretation) :=
  ⟨fun h => le_antisymm (le_formulaSize_iff.2 h) (formulaSize_le fun _ => rfl),
    fun h _ hG => h ▸ formulaSize_le hG⟩

/-- Every argument of a leaf-minimal gate is leaf-minimal. -/
private theorem IsLeafMinimal.arg {op : Op} {args : Fin (signature.Arity op) → Formula signature n}
    (hF : (gate op args).IsLeafMinimal) (j : Fin (signature.Arity op)) :
    (args j).IsLeafMinimal := by
  intro G hG
  have hcomp : (gate op (update args j G)).Computes interpretation
      ((gate op args).eval interpretation) := fun x => by
    simp only [eval_gate]
    congr 1
    funext k
    by_cases hk : k = j
    · subst hk
      simpa using hG x
    · simp [hk]
  have hle := hF (gate op (update args j G)) hcomp
  simp only [leafSize_gate] at hle
  have hsum1 := add_sum_erase univ (fun k => (args k).leafSize) (mem_univ j)
  have hsum2 := add_sum_erase univ (fun k => (update args j G k).leafSize) (mem_univ j)
  have heq : ∑ k ∈ univ.erase j, (update args j G k).leafSize =
      ∑ k ∈ univ.erase j, (args k).leafSize :=
    sum_congr rfl fun k hk => by simp [ne_of_mem_erase hk]
  rw [← hsum1, ← hsum2, update_self, heq] at hle
  omega

private theorem IsLeafMinimal.of_not {F : Formula signature n} (h : F.not.IsLeafMinimal) :
    F.IsLeafMinimal :=
  h.arg 0

private theorem IsLeafMinimal.left_of_and {F G : Formula signature n}
    (h : (F.and G).IsLeafMinimal) :
    F.IsLeafMinimal :=
  h.arg 0

private theorem IsLeafMinimal.right_of_and {F G : Formula signature n}
    (h : (F.and G).IsLeafMinimal) :
    G.IsLeafMinimal :=
  h.arg 1

private theorem IsLeafMinimal.left_of_or {F G : Formula signature n} (h : (F.or G).IsLeafMinimal) :
    F.IsLeafMinimal :=
  h.arg 0

private theorem IsLeafMinimal.right_of_or {F G : Formula signature n} (h : (F.or G).IsLeafMinimal) :
    G.IsLeafMinimal :=
  h.arg 1

/-! ### Single-step shrinkage -/

/-- A leaf-minimal formula with one leaf, at input `i`, restricts to `const a` at one value of `i`
and to `const (!a)` at the other. -/
private theorem exists_restrictAt_eq_const_of_leafSize_eq_one {G : Formula signature n}
    (hG : G.IsLeafMinimal) {i : Fin n} (hGL : G.leafSize = 1) (hGi : G.leafSizeIn {i} = 1)
    (a : Bool) :
    ∃ b₀ : Bool, G.restrictAt i b₀ = const a ∧ G.restrictAt i (!b₀) = const (!a) ∧
      ∀ x, G.eval interpretation x = if x i = b₀ then a else !a := by
  have h0 : (G.restrictAt i false).leafSize = 0 := by
    have := leafSize_restrictAt_add_leafSizeIn_le G i false; omega
  have h1 : (G.restrictAt i true).leafSize = 0 := by
    have := leafSize_restrictAt_add_leafSizeIn_le G i true; omega
  obtain ⟨c₀, hc₀⟩ := exists_restrict_eq_const _ h0
  obtain ⟨c₁, hc₁⟩ := exists_restrict_eq_const _ h1
  change G.restrictAt i false = const c₀ at hc₀
  change G.restrictAt i true = const c₁ at hc₁
  have heval (x : BitString n) : G.eval interpretation x = if x i then c₁ else c₀ := by
    have hx : G.eval interpretation (update x i (x i)) = G.eval interpretation x := by
      rw [update_eq_self]
    rw [← hx, ← eval_restrictAt]
    cases x i
    · rw [hc₀, eval_const]; rfl
    · rw [hc₁, eval_const]; rfl
  have hne : c₀ ≠ c₁ := by
    intro h
    subst h
    have hconst : (const c₀ : Formula signature n).Computes interpretation
        (G.eval interpretation) := fun x => by
      rw [eval_const, heval]
      cases x i <;> rfl
    have := hG (const c₀) hconst
    rw [leafSize_const] at this
    omega
  have hc₁' : c₁ = !c₀ := by cases c₀ <;> cases c₁ <;> simp_all
  subst hc₁'
  by_cases ha : c₀ = a
  · subst ha
    refine ⟨false, hc₀, hc₁, fun x => ?_⟩
    rw [heval]
    cases x i <;> rfl
  · have hc₀' : c₀ = !a := by cases c₀ <;> cases a <;> simp_all
    subst hc₀'
    refine ⟨true, by simpa using hc₁, by simpa using hc₀, fun x => ?_⟩
    rw [heval]
    cases x i <;> simp

/-- Shrinkage at a binary gate when one argument `G` has a single leaf at `i`: the restriction of
`G` that annihilates the gate eliminates the other argument `H`, while the restriction that is
neutral for the gate shows by leaf-minimality that `H` has no leaf at `i`. -/
private theorem leafSize_restrictAt_binary_of_unit (F G H : Formula signature n) {i : Fin n}
    (hF : F.IsLeafMinimal) (hG : G.IsLeafMinimal) (hGL : G.leafSize = 1)
    (hGi : G.leafSizeIn {i} = 1) (hFL : F.leafSize = G.leafSize + H.leafSize)
    (hFi : F.leafSizeIn {i} = G.leafSizeIn {i} + H.leafSizeIn {i})
    (hnu : ¬ (F.leafSize = 1 ∧ F.leafSizeIn {i} = 1)) (a : Bool)
    (h0 : ∀ b, G.restrictAt i b = const a → (F.restrictAt i b).leafSize = 0)
    (h1 : ∀ b, G.restrictAt i b = const (!a) →
      (F.restrictAt i b).leafSize ≤ (H.restrictAt i b).leafSize)
    (hrepl : ∀ b₀, (∀ x, G.eval interpretation x = if x i = b₀ then a else !a) →
      ∃ F' : Formula signature n, F'.Computes interpretation (F.eval interpretation) ∧
        F'.leafSize = G.leafSize + (H.restrictAt i (!b₀)).leafSize) :
    (F.restrictAt i false).leafSize + (F.restrictAt i true).leafSize + 3 * F.leafSizeIn {i} ≤
      2 * F.leafSize := by
  obtain ⟨b₀, hb₀, hb₁, hevalG⟩ := exists_restrictAt_eq_const_of_leafSize_eq_one hG hGL hGi a
  obtain ⟨F', hF'comp, hF'L⟩ := hrepl b₀ hevalG
  have hle : F.leafSize ≤ F'.leafSize := hF F' hF'comp
  have hH : (H.restrictAt i (!b₀)).leafSize + H.leafSizeIn {i} ≤ H.leafSize :=
    leafSize_restrictAt_add_leafSizeIn_le H i (!b₀)
  have hF₀ : (F.restrictAt i b₀).leafSize = 0 := h0 b₀ hb₀
  have hF₁ : (F.restrictAt i (!b₀)).leafSize ≤ (H.restrictAt i (!b₀)).leafSize := h1 (!b₀) hb₁
  have hsum : (F.restrictAt i false).leafSize + (F.restrictAt i true).leafSize =
      (F.restrictAt i b₀).leafSize + (F.restrictAt i (!b₀)).leafSize := by
    cases b₀ <;> simp [Nat.add_comm]
  omega

private theorem update_not_eq_self_of_ne {i : Fin n} {b₀ : Bool} {x : BitString n}
    (hx : x i ≠ b₀) : update x i (!b₀) = x := by
  have hxb : x i = !b₀ := by cases hxi : x i <;> cases b₀ <;> simp [hxi] at hx ⊢
  rw [← hxb, update_eq_self]

/-- **Subbotovskaya's single-variable shrinkage** on a leaf-minimal formula: for every input `i`,
unless `F` has a single leaf and that leaf is at `i`, the restrictions of `F` fixing `i` to `false`
and `true` satisfy `L(F↾(i = 0)) + L(F↾(i = 1)) + 3 ℓ_i(F) ≤ 2 L(F)`. -/
theorem IsLeafMinimal.leafSize_restrictAt_false_add_true_le {F : Formula signature n}
    (hF : F.IsLeafMinimal) (i : Fin n) (hnu : ¬ (F.leafSize = 1 ∧ F.leafSizeIn {i} = 1)) :
    (F.restrictAt i false).leafSize + (F.restrictAt i true).leafSize + 3 * F.leafSizeIn {i} ≤
      2 * F.leafSize := by
  induction F with
  | input j =>
    by_cases hj : j = i
    · subst hj
      exact absurd ⟨rfl, by simp⟩ hnu
    · simp [restrictAt_input_of_ne hj, hj]
  | gate op args ih =>
    cases op with
    | const c => simp [restrictAt, restrict]
    | not =>
      rw [gate_not_eq] at hF hnu ⊢
      have hnu' : ¬ ((args 0).leafSize = 1 ∧ (args 0).leafSizeIn {i} = 1) := by simpa using hnu
      have h0 := ih 0 hF.of_not hnu'
      rw [restrictAt_not, restrictAt_not, leafSize_mkNot, leafSize_mkNot, leafSize_not,
        leafSizeIn_not]
      exact h0
    | and =>
      rw [gate_and_eq] at hF hnu ⊢
      have hG : (args 0).IsLeafMinimal := hF.left_of_and
      have hH : (args 1).IsLeafMinimal := hF.right_of_and
      have hFL : ((args 0).and (args 1)).leafSize = (args 0).leafSize + (args 1).leafSize :=
        leafSize_and _ _
      have hFi : ((args 0).and (args 1)).leafSizeIn {i} =
          (args 0).leafSizeIn {i} + (args 1).leafSizeIn {i} :=
        leafSizeIn_and _ _ _
      by_cases hGu : (args 0).leafSize = 1 ∧ (args 0).leafSizeIn {i} = 1
      · refine leafSize_restrictAt_binary_of_unit ((args 0).and (args 1)) (args 0) (args 1)
          hF hG hGu.1 hGu.2 hFL hFi hnu false
          (fun b hb => by simp [restrictAt_and, hb])
          (fun b hb => by simp [restrictAt_and, hb])
          (fun b₀ hb => ⟨(args 0).and ((args 1).restrictAt i (!b₀)), fun x => ?_, leafSize_and _ _⟩)
        by_cases hx : x i = b₀ <;> simp [hb x, hx, update_not_eq_self_of_ne]
      · by_cases hHu : (args 1).leafSize = 1 ∧ (args 1).leafSizeIn {i} = 1
        · refine leafSize_restrictAt_binary_of_unit ((args 0).and (args 1)) (args 1) (args 0)
            hF hH hHu.1 hHu.2 (by omega) (by omega) hnu false
            (fun b hb => by simp [restrictAt_and, hb])
            (fun b hb => by simp [restrictAt_and, hb])
            (fun b₀ hb => ⟨((args 0).restrictAt i (!b₀)).and (args 1),
              fun x => ?_, by rw [leafSize_and]; omega⟩)
          by_cases hx : x i = b₀ <;> simp [hb x, hx, update_not_eq_self_of_ne]
        · have ihG := ih 0 hG hGu
          have ihH := ih 1 hH hHu
          have hm0 := leafSize_mkAnd_le ((args 0).restrictAt i false) ((args 1).restrictAt i false)
          have hm1 := leafSize_mkAnd_le ((args 0).restrictAt i true) ((args 1).restrictAt i true)
          simp only [restrictAt_and]
          omega
    | or =>
      rw [gate_or_eq] at hF hnu ⊢
      have hG : (args 0).IsLeafMinimal := hF.left_of_or
      have hH : (args 1).IsLeafMinimal := hF.right_of_or
      have hFL : ((args 0).or (args 1)).leafSize = (args 0).leafSize + (args 1).leafSize :=
        leafSize_or _ _
      have hFi : ((args 0).or (args 1)).leafSizeIn {i} =
          (args 0).leafSizeIn {i} + (args 1).leafSizeIn {i} :=
        leafSizeIn_or _ _ _
      by_cases hGu : (args 0).leafSize = 1 ∧ (args 0).leafSizeIn {i} = 1
      · refine leafSize_restrictAt_binary_of_unit ((args 0).or (args 1)) (args 0) (args 1)
          hF hG hGu.1 hGu.2 hFL hFi hnu true
          (fun b hb => by simp [restrictAt_or, hb])
          (fun b hb => by simp [restrictAt_or, hb])
          (fun b₀ hb => ⟨(args 0).or ((args 1).restrictAt i (!b₀)), fun x => ?_, leafSize_or _ _⟩)
        by_cases hx : x i = b₀ <;> simp [hb x, hx, update_not_eq_self_of_ne]
      · by_cases hHu : (args 1).leafSize = 1 ∧ (args 1).leafSizeIn {i} = 1
        · refine leafSize_restrictAt_binary_of_unit ((args 0).or (args 1)) (args 1) (args 0)
            hF hH hHu.1 hHu.2 (by omega) (by omega) hnu true
            (fun b hb => by simp [restrictAt_or, hb])
            (fun b hb => by simp [restrictAt_or, hb])
            (fun b₀ hb => ⟨((args 0).restrictAt i (!b₀)).or (args 1),
              fun x => ?_, by rw [leafSize_or]; omega⟩)
          by_cases hx : x i = b₀ <;> simp [hb x, hx, update_not_eq_self_of_ne]
        · have ihG := ih 0 hG hGu
          have ihH := ih 1 hH hHu
          have hm0 := leafSize_mkOr_le ((args 0).restrictAt i false) ((args 1).restrictAt i false)
          have hm1 := leafSize_mkOr_le ((args 0).restrictAt i true) ((args 1).restrictAt i true)
          simp only [restrictAt_or]
          omega

end Formula

namespace Boolean

open Formula

variable {f : BooleanFunction n}

/-- Summed over the free inputs of `ρ`, the formula sizes after fixing one free input of `ρ`
satisfy Subbotovskaya's single-step shrinkage inequality:
- when `L(f↾ρ) ≠ 1`, the sum plus `3 L(f↾ρ)` is at most `2 |ρ.free| L(f↾ρ)`;
- when `L(f↾ρ) = 1`, some free input has the single leaf and fixing it reduces the formula size to
  `0`, while the other `|ρ.free| - 1` free inputs contribute at most `2` each. -/
theorem sum_formulaSize_restrict_update_le (f : BooleanFunction n)
    (ρ : PartialAssignment (Fin n)) :
    ∑ i ∈ ρ.free,
        (formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
          formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true)))) +
        (if formulaSize (f ∘ ρ.fill) = 1 then 2 else 3 * formulaSize (f ∘ ρ.fill)) ≤
      2 * #ρ.free * formulaSize (f ∘ ρ.fill) := by
  set g := f ∘ ρ.fill
  obtain ⟨F, hF, hL⟩ := exists_computes_leafSize_eq g
  have hFg : F.eval interpretation = g := funext hF
  have hmin : F.IsLeafMinimal := isLeafMinimal_iff_leafSize_eq_formulaSize.2 (hFg ▸ hL)
  have hdep : DependsOn g ρ.free := PartialAssignment.dependsOn_comp_fill_free f ρ
  have hS : F.leafSizeIn ρ.free = F.leafSize := leafSizeIn_eq_leafSize_of_dependsOn hdep hF hL
  have hle_i (i : Fin n) (hi : i ∈ ρ.free) (b : Bool) :
      formulaSize (f ∘ PartialAssignment.fill (update ρ i (some b))) ≤
        (F.restrictAt i b).leafSize := by
    rw [← PartialAssignment.comp_fill_update_empty_of_mem_free hi]
    exact formulaSize_le fun x => by
      rw [eval_restrictAt, hF, comp_apply, PartialAssignment.fill_update_empty]
  by_cases hL1 : formulaSize g = 1
  · simp only [hL1, ↓reduceIte, mul_one]
    have hsum1 : ∑ i ∈ ρ.free, F.leafSizeIn {i} = 1 := by
      rw [sum_leafSizeIn_singleton, hS, hL, hL1]
    have hex : ∃ i₀ ∈ ρ.free, F.leafSizeIn {i₀} ≠ 0 := by
      by_contra! hall
      rw [sum_eq_zero hall] at hsum1
      exact absurd hsum1 (by decide)
    obtain ⟨i₀, hi₀, hne0⟩ := hex
    have hi₀_eq : F.leafSizeIn {i₀} = 1 := by
      have := single_le_sum (fun i _ => Nat.zero_le (F.leafSizeIn {i})) hi₀
      omega
    have h0_false : (F.restrictAt i₀ false).leafSize = 0 := by
      have := leafSize_restrictAt_add_leafSizeIn_le F i₀ false; omega
    have h0_true : (F.restrictAt i₀ true).leafSize = 0 := by
      have := leafSize_restrictAt_add_leafSizeIn_le F i₀ true; omega
    have hterm_le (i : Fin n) (hi : i ∈ ρ.free) :
        formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
          formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true))) ≤
          if i = i₀ then 0 else 2 := by
      split_ifs with h
      · subst h
        have := hle_i i hi false
        have := hle_i i hi true
        omega
      · have := (hle_i i hi false).trans
          ((Nat.le_add_right _ _).trans (leafSize_restrictAt_add_leafSizeIn_le F i false))
        have := (hle_i i hi true).trans
          ((Nat.le_add_right _ _).trans (leafSize_restrictAt_add_leafSizeIn_le F i true))
        omega
    calc ∑ i ∈ ρ.free, (formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
            formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true)))) + 2
        ≤ ∑ i ∈ ρ.free, (if i = i₀ then 0 else 2) + 2 :=
          Nat.add_le_add_right (sum_le_sum hterm_le) 2
      _ = 2 * #ρ.free := by
          have hsplit := add_sum_erase ρ.free (fun i => if i = i₀ then 0 else 2) hi₀
          simp only [↓reduceIte, zero_add] at hsplit
          have herase : ∑ i ∈ ρ.free.erase i₀, (if i = i₀ then 0 else 2) =
              2 * (#ρ.free - 1) := by
            have hcongr : ∑ i ∈ ρ.free.erase i₀, (if i = i₀ then 0 else 2) =
                ∑ _ ∈ ρ.free.erase i₀, 2 :=
              sum_congr rfl fun i hi => by simp [ne_of_mem_erase hi]
            rw [hcongr, sum_const, smul_eq_mul, card_erase_of_mem hi₀, mul_comm]
          have hcard : 1 ≤ #ρ.free := card_pos.2 ⟨i₀, hi₀⟩
          rw [← hsplit, herase]
          omega
  · simp only [hL1, ↓reduceIte]
    have hper (i : Fin n) (hi : i ∈ ρ.free) :
        formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
          formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true))) +
          3 * F.leafSizeIn {i} ≤ 2 * F.leafSize := by
      have hnu : ¬ (F.leafSize = 1 ∧ F.leafSizeIn {i} = 1) := fun ⟨h1, _⟩ => hL1 (hL ▸ h1)
      have := hmin.leafSize_restrictAt_false_add_true_le i hnu
      have := hle_i i hi false
      have := hle_i i hi true
      omega
    have hsum := sum_le_sum hper
    rw [sum_add_distrib, ← mul_sum, sum_leafSizeIn_singleton, hS, sum_const, smul_eq_mul, hL]
      at hsum
    linarith

/-- Uniform single-step shrinkage inequality valid for every formula size, including `1`:
the sum over all `2 |ρ.free|` single-variable extensions of `ρ` is at most
`(2 |ρ.free| - 3) L(f↾ρ) + 1`. -/
private theorem sum_formulaSize_restrict_update_le_add_one (f : BooleanFunction n)
    (ρ : PartialAssignment (Fin n)) :
    ∑ i ∈ ρ.free,
        (formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
          formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true)))) ≤
      (2 * #ρ.free - 3) * formulaSize (f ∘ ρ.fill) + 1 := by
  have h := sum_formulaSize_restrict_update_le f ρ
  rw [Nat.sub_mul]
  split_ifs at h with h1
  · rw [h1] at h ⊢
    omega
  · omega

/-! ### Deterministic shrinkage and Subbotovskaya's parity lower bound -/

/-- When `|ρ.free| ≥ 2`, fixing some free coordinate of `ρ` to a constant shrinks the formula size
so that `L' ^ 2 * s ^ 3 ≤ L ^ 2 * (s - 1) ^ 3` for `s = |ρ.free|`. -/
theorem exists_mem_free_formulaSize_sq_mul_pow_three_le (f : BooleanFunction n)
    {ρ : PartialAssignment (Fin n)} (hs : 2 ≤ #ρ.free) :
    ∃ i ∈ ρ.free, ∃ b : Bool,
      formulaSize (f ∘ PartialAssignment.fill (update ρ i (some b))) ^ 2 * (#ρ.free) ^ 3 ≤
        formulaSize (f ∘ ρ.fill) ^ 2 * (#ρ.free - 1) ^ 3 := by
  have hsum := sum_formulaSize_restrict_update_le f ρ
  generalize hs_eq : #ρ.free = s at hs hsum ⊢
  generalize hL_eq : formulaSize (f ∘ ρ.fill) = L at hsum ⊢
  by_cases hL1 : L = 1
  · simp only [hL1, ↓reduceIte, mul_one] at hsum
    have hex : ∃ i ∈ ρ.free,
        formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
          formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true))) < 2 := by
      by_contra! hall
      have := sum_le_sum hall
      rw [sum_const, hs_eq, smul_eq_mul] at this
      omega
    obtain ⟨i, hi, hlt⟩ := hex
    by_cases h0 : formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) = 0
    · exact ⟨i, hi, false, by rw [h0]; simp⟩
    · have h1 : formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true))) = 0 := by omega
      exact ⟨i, hi, true, by rw [h1]; simp⟩
  · simp only [hL1, ↓reduceIte] at hsum
    obtain ⟨d, rfl⟩ : ∃ d, s = d + 2 := ⟨s - 2, by omega⟩
    have hex : ∃ i ∈ ρ.free,
        (d + 2) * (formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
          formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true)))) ≤
          (2 * (d + 2) - 3) * L := by
      by_contra! hall
      have hsum' : ∑ i ∈ ρ.free, ((2 * d + 1) * L + 1) ≤
          ∑ i ∈ ρ.free, (d + 2) *
            (formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
              formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true)))) :=
        sum_le_sum fun i hi => hall i hi
      rw [sum_const, hs_eq, smul_eq_mul, ← mul_sum] at hsum'
      nlinarith
    obtain ⟨i, hi, hle⟩ := hex
    have hmin : ∃ b : Bool,
        2 * (d + 2) * formulaSize (f ∘ PartialAssignment.fill (update ρ i (some b))) ≤
          (2 * (d + 2) - 3) * L := by
      by_cases hab : formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) ≤
          formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true)))
      · exact ⟨false, by nlinarith⟩
      · exact ⟨true, by nlinarith⟩
    obtain ⟨b, hb⟩ := hmin
    refine ⟨i, hi, b, ?_⟩
    set L' := formulaSize (f ∘ PartialAssignment.fill (update ρ i (some b)))
    have hsq : (2 * (d + 2) * L') ^ 2 ≤ ((2 * (d + 2) - 3) * L) ^ 2 := Nat.pow_le_pow_left hb 2
    have hpoly : (d + 2) * (2 * (d + 2) - 3) ^ 2 ≤ 4 * (d + 2 - 1) ^ 3 := by
      change (d + 2) * (2 * d + 1) ^ 2 ≤ 4 * (d + 1) ^ 3
      nlinarith
    have hmul : 4 * (L' ^ 2 * (d + 2) ^ 3) ≤ 4 * (L ^ 2 * (d + 2 - 1) ^ 3) := by
      calc 4 * (L' ^ 2 * (d + 2) ^ 3)
          = (d + 2) * (2 * (d + 2) * L') ^ 2 := by ring
        _ ≤ (d + 2) * ((2 * (d + 2) - 3) * L) ^ 2 := Nat.mul_le_mul_left (d + 2) hsq
        _ = (d + 2) * (2 * (d + 2) - 3) ^ 2 * L ^ 2 := by ring
        _ ≤ 4 * (d + 2 - 1) ^ 3 * L ^ 2 := Nat.mul_le_mul_right (L ^ 2) hpoly
        _ = 4 * (L ^ 2 * (d + 2 - 1) ^ 3) := by ring
    omega

/-- **Subbotovskaya's shrinkage lemma** for extensions of a partial assignment `ρ₀`: for every
`1 ≤ k ≤ |ρ₀.free|`, some extension `ρ` of `ρ₀` with `k` free inputs satisfies
`L(f↾ρ) ^ 2 * |ρ₀.free| ^ 3 ≤ L(f↾ρ₀) ^ 2 * k ^ 3`. -/
theorem exists_extensions_formulaSize_sq_mul_pow_three_le (f : BooleanFunction n)
    (ρ₀ : PartialAssignment (Fin n)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ #ρ₀.free) :
    ∃ ρ ∈ ρ₀.extensions k,
      formulaSize (f ∘ ρ.fill) ^ 2 * (#ρ₀.free) ^ 3 ≤
        formulaSize (f ∘ ρ₀.fill) ^ 2 * k ^ 3 := by
  obtain ⟨d, hd⟩ : ∃ d, #ρ₀.free = k + d := ⟨#ρ₀.free - k, by omega⟩
  induction d generalizing ρ₀ with
  | zero =>
    rw [Nat.add_zero] at hd
    exact ⟨ρ₀, PartialAssignment.mem_extensions.2 ⟨.refl ρ₀, hd⟩, by rw [hd]⟩
  | succ d ih =>
    have hs : 2 ≤ #ρ₀.free := by omega
    obtain ⟨i, hi, b, hstep⟩ := exists_mem_free_formulaSize_sq_mul_pow_three_le f hs
    let ρ₁ : PartialAssignment (Fin n) := update ρ₀ i (some b)
    have hfree₁ : #ρ₁.free = k + d := by
      rw [PartialAssignment.free_update, card_erase_of_mem hi]
      omega
    have hk₁ : k ≤ #ρ₁.free := by omega
    obtain ⟨ρ, hρ, hih⟩ := ih ρ₁ hk₁ hfree₁
    obtain ⟨hext₁, hfree⟩ := PartialAssignment.mem_extensions.1 hρ
    have hext₀ : ρ.Extends ρ₀ :=
      hext₁.trans ((PartialAssignment.Extends.refl ρ₀).update_some hi b)
    refine ⟨ρ, PartialAssignment.mem_extensions.2 ⟨hext₀, hfree⟩, ?_⟩
    have hpos_card : 0 < #ρ₁.free := by omega
    have hpos : 0 < (#ρ₁.free) ^ 3 := by positivity
    have h1 : #ρ₀.free - 1 = #ρ₁.free := by omega
    rw [h1] at hstep
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc formulaSize (f ∘ ρ.fill) ^ 2 * (#ρ₀.free) ^ 3 * (#ρ₁.free) ^ 3
        = formulaSize (f ∘ ρ.fill) ^ 2 * (#ρ₁.free) ^ 3 * (#ρ₀.free) ^ 3 := by ring
      _ ≤ formulaSize (f ∘ ρ₁.fill) ^ 2 * k ^ 3 * (#ρ₀.free) ^ 3 :=
          Nat.mul_le_mul_right _ hih
      _ = formulaSize (f ∘ ρ₁.fill) ^ 2 * (#ρ₀.free) ^ 3 * k ^ 3 := by ring
      _ ≤ formulaSize (f ∘ ρ₀.fill) ^ 2 * (#ρ₁.free) ^ 3 * k ^ 3 :=
          Nat.mul_le_mul_right _ hstep
      _ = formulaSize (f ∘ ρ₀.fill) ^ 2 * k ^ 3 * (#ρ₁.free) ^ 3 := by ring

/-- **Subbotovskaya's shrinkage lemma**: for every Boolean function `f` on `n` bits and every
`1 ≤ k ≤ n`, some partial assignment `ρ` leaving `k` inputs free satisfies
`L(f↾ρ) ^ 2 * n ^ 3 ≤ L(f) ^ 2 * k ^ 3`. -/
theorem exists_withFree_formulaSize_sq_mul_pow_three_le (f : BooleanFunction n) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ n) :
    ∃ ρ ∈ PartialAssignment.withFree (Fin n) k,
      formulaSize (f ∘ ρ.fill) ^ 2 * n ^ 3 ≤ formulaSize f ^ 2 * k ^ 3 := by
  have hk' : k ≤ #(PartialAssignment.empty : PartialAssignment (Fin n)).free := by simpa using hk
  obtain ⟨ρ, hρ, hle⟩ := exists_extensions_formulaSize_sq_mul_pow_three_le
    f PartialAssignment.empty hk1 hk'
  rw [PartialAssignment.free_empty, card_univ, Fintype.card_fin] at hle
  exact ⟨ρ, hρ, hle⟩

/-- **Subbotovskaya's parity lower bound**: the formula size of `parity n` is at least
`n ^ (3 / 2)`, stated as `n ^ 3 ≤ L(parity n) ^ 2` [Subbotovskaya1961],
[Jukna, Section 6.3][Jukna2012]. -/
theorem pow_three_le_formulaSize_parity_sq (n : ℕ) :
    n ^ 3 ≤ formulaSize (parity n) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨ρ, hρ, hle⟩ := exists_withFree_formulaSize_sq_mul_pow_three_le
      (parity n) (k := 1) le_rfl hn
    have hfree : #ρ.free = 1 := PartialAssignment.mem_withFree.1 hρ
    obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < #ρ.free)
    have hpos : 1 ≤ formulaSize (parity n ∘ ρ.fill) := by
      by_contra! h0
      have hzero : formulaSize (parity n ∘ ρ.fill) = 0 := by omega
      obtain ⟨F, hF, hFL⟩ := exists_computes_leafSize_eq (parity n ∘ ρ.fill)
      rw [hzero] at hFL
      have hconst := eval_eq_of_leafSize_eq_zero hFL interpretation (fun _ => false)
        (update (fun _ => false) i true)
      rw [hF, hF, comp_apply, comp_apply,
        PartialAssignment.fill_update_of_eq_none (PartialAssignment.mem_free.1 hi)] at hconst
      have hflip := parity_update_not (ρ.fill fun _ => false) i
      have : update (ρ.fill fun _ => false) i true =
          update (ρ.fill fun _ => false) i (!(ρ.fill (fun _ => false) i)) := by
        rw [PartialAssignment.fill_of_eq_none (PartialAssignment.mem_free.1 hi)]
        rfl
      rw [this, hflip] at hconst
      have hne (b : Bool) : b ≠ !b := by cases b <;> decide
      exact hne _ hconst
    have hmul : 1 * n ^ 3 ≤ formulaSize (parity n ∘ ρ.fill) ^ 2 * n ^ 3 :=
      Nat.mul_le_mul_right _ (by nlinarith)
    linarith

/-- **Subbotovskaya's parity lower bound** for De Morgan formulas: every formula computing
`parity n` has leaf size `L` satisfying `n ^ 3 ≤ L ^ 2`. -/
theorem pow_three_le_leafSize_sq_of_computes_parity {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) :
    n ^ 3 ≤ F.leafSize ^ 2 :=
  (pow_three_le_formulaSize_parity_sq n).trans (Nat.pow_le_pow_left (formulaSize_le hF) 2)

/-! ### Average shrinkage over random restrictions -/

/-- **Subbotovskaya's average shrinkage** over all extensions of `ρ₀` with `k` free inputs:
for `1 ≤ k ≤ |ρ₀.free|`, the sum `S_k = ∑ ρ ∈ ρ₀.extensions k, L(f↾ρ)` and the count
`N_k = |ρ₀.extensions k|` satisfy
`(S_k - k * N_k) ^ 2 * |ρ₀.free| ^ 3 ≤ L(f↾ρ₀) ^ 2 * k ^ 3 * N_k ^ 2`. -/
theorem sum_extensions_formulaSize_sub_sq_le (f : BooleanFunction n)
    (ρ₀ : PartialAssignment (Fin n)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ #ρ₀.free) :
    (∑ ρ ∈ ρ₀.extensions k, formulaSize (f ∘ ρ.fill) - k * #(ρ₀.extensions k)) ^ 2 *
        (#ρ₀.free) ^ 3 ≤
      formulaSize (f ∘ ρ₀.fill) ^ 2 * k ^ 3 * #(ρ₀.extensions k) ^ 2 := by
  set s := #ρ₀.free
  set L₀ := formulaSize (f ∘ ρ₀.fill)
  obtain ⟨d, hd⟩ : ∃ d, k + d = s := ⟨s - k, by omega⟩
  induction d generalizing k with
  | zero =>
    have hks : k = s := by omega
    subst hks
    have hexts : ρ₀.extensions s = {ρ₀} := by
      ext ρ
      simp only [PartialAssignment.mem_extensions, mem_singleton]
      refine ⟨fun ⟨hext, hfree⟩ => ?_, ?_⟩
      · have hsub : ρ.free = ρ₀.free := eq_of_subset_of_card_le hext.free_subset (by rw [hfree])
        funext i
        by_cases hi : i ∈ ρ₀.free
        · have hi' : i ∈ ρ.free := hsub ▸ hi
          rw [PartialAssignment.mem_free.1 hi, PartialAssignment.mem_free.1 hi']
        · obtain ⟨c, hc⟩ :=
            Option.ne_none_iff_exists'.1 fun h => hi (PartialAssignment.mem_free.2 h)
          rw [hc, hext i c hc]
      · intro h
        rw [h]
        exact ⟨.refl ρ₀, rfl⟩
    rw [hexts, sum_singleton, card_singleton, mul_one, one_pow, mul_one]
    have : (L₀ - s) ^ 2 ≤ L₀ ^ 2 := Nat.pow_le_pow_left (Nat.sub_le L₀ s) 2
    exact Nat.mul_le_mul_right (s ^ 3) this
  | succ d ih =>
    set t := k + 1
    have ht1 : 2 ≤ t := by omega
    have hts : t ≤ s := by omega
    have hih := ih (k := t) (by omega) hts (by omega)
    set S_t := ∑ ρ ∈ ρ₀.extensions t, formulaSize (f ∘ ρ.fill)
    set N_t := #(ρ₀.extensions t)
    set S_k := ∑ ρ ∈ ρ₀.extensions k, formulaSize (f ∘ ρ.fill)
    set N_k := #(ρ₀.extensions k)
    have hstep_rec : (s - k) * S_k ≤ (2 * t - 3) * S_t + N_t := by
      have hdc := (PartialAssignment.sum_extensions_update ρ₀ (by omega : 1 ≤ t)
        (fun ρ => formulaSize (f ∘ ρ.fill))).symm
      have htk : t - 1 = k := by omega
      rw [htk] at hdc
      rw [hdc]
      calc ∑ ρ ∈ ρ₀.extensions t, ∑ i ∈ ρ.free,
            (formulaSize (f ∘ PartialAssignment.fill (update ρ i (some false))) +
              formulaSize (f ∘ PartialAssignment.fill (update ρ i (some true))))
          ≤ ∑ ρ ∈ ρ₀.extensions t,
            ((2 * #ρ.free - 3) * formulaSize (f ∘ ρ.fill) + 1) :=
            sum_le_sum fun ρ _ => sum_formulaSize_restrict_update_le_add_one f ρ
        _ = ∑ ρ ∈ ρ₀.extensions t, ((2 * t - 3) * formulaSize (f ∘ ρ.fill) + 1) :=
            sum_congr rfl fun ρ hρ => by rw [(PartialAssignment.mem_extensions.1 hρ).2]
        _ = (2 * t - 3) * S_t + N_t := by
            rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, mul_one]
    have hcard_rec : (s - k) * N_k = 2 * t * N_t := by
      simpa [t] using PartialAssignment.mul_card_extensions_sub_one ρ₀ (by omega : 1 ≤ t)
    have hsub_rec : (s - k) * (S_k - k * N_k) ≤ (2 * t - 3) * (S_t - t * N_t) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
      have h1 : (s - k) * (k * N_k) = k * ((s - k) * N_k) := by ring
      rw [h1, hcard_rec]
      have h2 : (2 * t - 3) * (t * N_t) + N_t ≤ k * (2 * t * N_t) := by
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        change (2 * m + 1) * ((m + 2) * N_t) + N_t ≤ (m + 1) * (2 * (m + 2) * N_t)
        nlinarith
      omega
    have hpoly : t * (2 * t - 3) ^ 2 ≤ 4 * k ^ 3 := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      change (m + 2) * (2 * (m + 2) - 3) ^ 2 ≤ 4 * (m + 1) ^ 3
      change (m + 2) * (2 * m + 1) ^ 2 ≤ 4 * (m + 1) ^ 3
      nlinarith
    have hsq : ((s - k) * (S_k - k * N_k)) ^ 2 ≤ ((2 * t - 3) * (S_t - t * N_t)) ^ 2 :=
      Nat.pow_le_pow_left hsub_rec 2
    have hsk : 0 < s - k := by omega
    have hpos : 0 < 4 * t ^ 3 * (s - k) ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (S_k - k * N_k) ^ 2 * s ^ 3 * (4 * t ^ 3 * (s - k) ^ 2)
        = 4 * t ^ 3 * s ^ 3 * ((s - k) * (S_k - k * N_k)) ^ 2 := by ring
      _ ≤ 4 * t ^ 3 * s ^ 3 * ((2 * t - 3) * (S_t - t * N_t)) ^ 2 :=
          Nat.mul_le_mul_left _ hsq
      _ = 4 * t ^ 3 * (2 * t - 3) ^ 2 * ((S_t - t * N_t) ^ 2 * s ^ 3) := by ring
      _ ≤ 4 * t ^ 3 * (2 * t - 3) ^ 2 * (L₀ ^ 2 * t ^ 3 * N_t ^ 2) :=
          Nat.mul_le_mul_left _ hih
      _ = t * (2 * t - 3) ^ 2 * (L₀ ^ 2 * t ^ 3 * (2 * t * N_t) ^ 2) := by ring
      _ ≤ 4 * k ^ 3 * (L₀ ^ 2 * t ^ 3 * (2 * t * N_t) ^ 2) :=
          Nat.mul_le_mul_right _ hpoly
      _ = 4 * k ^ 3 * (L₀ ^ 2 * t ^ 3 * ((s - k) * N_k) ^ 2) := by rw [← hcard_rec]
      _ = L₀ ^ 2 * k ^ 3 * N_k ^ 2 * (4 * t ^ 3 * (s - k) ^ 2) := by ring

/-- If a subset `A ⊆ ρ₀.extensions k` has at least half the extensions
(`|ρ₀.extensions k| ≤ 2 |A|`), then some `ρ ∈ A` has formula size bounded by Subbotovskaya's
shrinkage: `(L(f↾ρ) - 2 k) ^ 2 * |ρ₀.free| ^ 3 ≤ 4 * L(f↾ρ₀) ^ 2 * k ^ 3`. -/
theorem exists_mem_formulaSize_sub_sq_le (f : BooleanFunction n)
    (ρ₀ : PartialAssignment (Fin n)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ #ρ₀.free)
    {A : Finset (PartialAssignment (Fin n))} (hAsub : A ⊆ ρ₀.extensions k)
    (hAcard : #(ρ₀.extensions k) ≤ 2 * #A) :
    ∃ ρ ∈ A,
      (formulaSize (f ∘ ρ.fill) - 2 * k) ^ 2 * (#ρ₀.free) ^ 3 ≤
        4 * formulaSize (f ∘ ρ₀.fill) ^ 2 * k ^ 3 := by
  set N_k := #(ρ₀.extensions k)
  have hNk_pos : 0 < N_k := by
    change 0 < #(ρ₀.extensions k)
    rw [PartialAssignment.card_extensions]
    exact Nat.mul_pos (Nat.choose_pos hk) (by positivity)
  have hAne : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨ρ, hρA, hmin⟩ := exists_min_image A (fun ρ => formulaSize (f ∘ ρ.fill)) hAne
  refine ⟨ρ, hρA, ?_⟩
  set L' := formulaSize (f ∘ ρ.fill)
  set S_k := ∑ ρ' ∈ ρ₀.extensions k, formulaSize (f ∘ ρ'.fill)
  have hsumA : #A * L' ≤ S_k := by
    calc #A * L'
        = ∑ _ ∈ A, L' := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ ρ' ∈ A, formulaSize (f ∘ ρ'.fill) := sum_le_sum hmin
      _ ≤ S_k := sum_le_sum_of_subset hAsub
  have h2 : (L' - 2 * k) * N_k ≤ 2 * (S_k - k * N_k) := by
    have : L' * N_k ≤ 2 * S_k := by nlinarith
    rw [Nat.sub_mul, Nat.mul_sub_left_distrib, show 2 * (k * N_k) = 2 * k * N_k by ring]
    omega
  have hsq : ((L' - 2 * k) * N_k) ^ 2 ≤ (2 * (S_k - k * N_k)) ^ 2 :=
    Nat.pow_le_pow_left h2 2
  have havg := sum_extensions_formulaSize_sub_sq_le f ρ₀ hk1 hk
  have hpos : 0 < N_k ^ 2 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (L' - 2 * k) ^ 2 * (#ρ₀.free) ^ 3 * N_k ^ 2
      = ((L' - 2 * k) * N_k) ^ 2 * (#ρ₀.free) ^ 3 := by ring
    _ ≤ (2 * (S_k - k * N_k)) ^ 2 * (#ρ₀.free) ^ 3 := Nat.mul_le_mul_right _ hsq
    _ = 4 * ((S_k - k * N_k) ^ 2 * (#ρ₀.free) ^ 3) := by ring
    _ ≤ 4 * (formulaSize (f ∘ ρ₀.fill) ^ 2 * k ^ 3 * N_k ^ 2) := Nat.mul_le_mul_left 4 havg
    _ = 4 * formulaSize (f ∘ ρ₀.fill) ^ 2 * k ^ 3 * N_k ^ 2 := by ring

end Boolean

end Cslib.Circuits
