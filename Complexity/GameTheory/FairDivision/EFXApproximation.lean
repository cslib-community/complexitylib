/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.GameTheory.FairDivision.EFX
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Approximate EFX and Pareto efficiency

Theorem 2 of [MahabadiRamakrishnanTarnawski2026], introduction PDF p. 3 and §4,
PDF pp. 9–11: for every real `α > 2/3` some strictly positive additive four-agent,
nine-good instance has no complete allocation that is both `α`-EFX and Pareto optimal.
`ApproximateCounterexample.values K` is the exact table in §4, in order `x,y,a,b,c,d,e,p,q`.
For every integer `K ≥ 6` the exclusion holds when `α > 2/3 + 1/K`.

## Main definitions

* `ApproximateEFX`: the ordinary multiplicative relaxation, with a real factor and natural
  item values; all goods in the envied bundle are tested.
* `ApproximateCounterexample.values`: the paper's parameterized positive table.

## Main results

* `ApproximateCounterexample.not_approximateEFX_and_paretoOptimal`: the parameterized exclusion.
* `ApproximateCounterexample.exists_counterexample`: the arbitrary-real-factor endpoint.

The proof uses symbolic certificates, not a bound on `K`: write `K = 6 + z` and check
nonnegative coefficients of `(2K+3) r - 3K u`, where `u` is own utility and `r` is utility
after removal. Since `α > (2K+3)/(3K)`, this certifies an EFX violation. Otherwise a
listed allocation (the paper's trades and their symmetries), or swapping `x,y`, dominates:
its utility differences have nonnegative constant and linear coefficients, and a positive
constant coefficient for some agent. Ordinary kernel reduction checks all ownership functions;
the subsequent algebra proves validity for every `z ≥ 0`. No desired inequality is assumed.
-/

public section

namespace Cslib.FairDivision

open Finset

/-- Multiplicative approximate EFX with a real factor and nonnegative integral additive
values. For a good actually in the envied bundle, natural subtraction is exact removal.
This tests all goods, agreeing with the positive-good convention on positive instances. -/
@[expose] def ApproximateEFX {Agent Good : Type*} [Fintype Good] [DecidableEq Agent]
    (α : ℝ) (v : Agent → Good → ℕ) (a : Good → Agent) : Prop :=
  ∀ i j g, i ≠ j → a g = j →
    α * (bundleValue v a i j - v i g : ℕ) ≤ (bundleValue v a i i : ℝ)

/-- Weakening the approximation factor preserves approximate EFX. -/
theorem ApproximateEFX.mono {Agent Good : Type*} [Fintype Good] [DecidableEq Agent]
    {α β : ℝ} {v : Agent → Good → ℕ} {a : Good → Agent}
    (h : ApproximateEFX α v a) (hβα : β ≤ α) : ApproximateEFX β v a := by
  intro i j g hij hg
  exact (mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans (h i j g hij hg)

/-- At factor one the multiplicative condition is exactly EFX. -/
theorem approximateEFX_one_iff {Agent Good : Type*} [Fintype Good] [DecidableEq Agent]
    (v : Agent → Good → ℕ) (a : Good → Agent) : ApproximateEFX 1 v a ↔ EFX v a := by
  simp [ApproximateEFX, EFX]

namespace ApproximateCounterexample

/-- Theorem 2's table, with goods ordered `x,y,a,b,c,d,e,p,q`. -/
@[expose] def values (K : ℕ) : Fin 4 → Fin 9 → ℕ :=
  ![![3*K,2*K+2,K,K,1,1,K,2,1], ![2*K+2,3*K,1,K,K,1,K,1,2],
    ![3*K,2*K+2,1,1,K,K,K,2,1], ![2*K+2,3*K,K,1,1,K,K,1,2]]

/-- All item values are positive throughout the parameter range. -/
theorem values_pos {K : ℕ} (hK : 6 ≤ K) (i : Fin 4) (g : Fin 9) :
    0 < values K i g := by
  fin_cases i <;> fin_cases g <;> simp [values] <;> omega

private def slope : Fin 4 → Fin 9 → ℕ :=
  ![![3,2,1,1,0,0,1,0,0], ![2,3,0,1,1,0,1,0,0],
    ![3,2,0,0,1,1,1,0,0], ![2,3,1,0,0,1,1,0,0]]

private theorem values_affine {K : ℕ} (hK : 6 ≤ K) (i : Fin 4) (g : Fin 9) :
    values K i g = values 6 i g + (K-6) * slope i g := by
  fin_cases i <;> fin_cases g <;> simp [values, slope] <;> omega

private theorem bundle_affine {K : ℕ} (hK : 6 ≤ K) (a : Fin 9 → Fin 4)
    (i j : Fin 4) :
    bundleValue (values K) a i j =
      bundleValue (values 6) a i j + (K-6) * bundleValue slope a i j := by
  simp only [bundleValue, values_affine hK, Finset.mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro g _
  split_ifs <;> simp

private theorem item_le_bundle (v : Fin 4 → Fin 9 → ℕ) (a : Fin 9 → Fin 4)
    (i : Fin 4) (g : Fin 9) : v i g ≤ bundleValue v a i (a g) := by
  have h := Finset.single_le_sum (f := fun k => if a k = a g then v i k else 0)
    (fun k (_ : k ∈ (univ : Finset (Fin 9))) => Nat.zero_le _) (mem_univ g)
  simpa only [bundleValue, ite_true] using h

private theorem removed_affine {K : ℕ} (hK : 6 ≤ K) (a : Fin 9 → Fin 4)
    (i : Fin 4) (g : Fin 9) :
    bundleValue (values K) a i (a g) - values K i g =
      (bundleValue (values 6) a i (a g) - values 6 i g) +
      (K-6) * (bundleValue slope a i (a g) - slope i g) := by
  rw [bundle_affine hK, values_affine hK]
  have hb := item_le_bundle (values 6) a i g
  have hs := item_le_bundle slope a i g
  rw [Nat.mul_sub_left_distrib]
  have hm := Nat.mul_le_mul_left (K-6) hs
  omega

private abbrev Allocation := Fin 9 → Fin 4

private def allocation (n : ℕ) : Allocation :=
  fun g => ⟨n / 4^g.val % 4, Nat.mod_lt _ (by decide)⟩

private def utility (v : Fin 4 → Fin 9 → ℕ) (a : Allocation) (i j : Fin 4) : ℕ :=
  (if a 0 = j then v i 0 else 0) +
  (if a 1 = j then v i 1 else 0) +
  (if a 2 = j then v i 2 else 0) +
  (if a 3 = j then v i 3 else 0) +
  (if a 4 = j then v i 4 else 0) +
  (if a 5 = j then v i 5 else 0) +
  (if a 6 = j then v i 6 else 0) +
  (if a 7 = j then v i 7 else 0) +
  (if a 8 = j then v i 8 else 0)

private theorem utility_eq (v : Fin 4 → Fin 9 → ℕ) (a : Allocation) (i j : Fin 4) :
    utility v a i j = bundleValue v a i j := by
  simp [utility, bundleValue, Fin.sum_univ_succ, Nat.add_assoc]

private def violation (a : Allocation) : Prop :=
  ∃ i, ∃ g ∈ ([8, 7, 2, 3, 4, 5, 6, 0, 1] : List (Fin 9)),
    let j := a g
    let u := utility (values 6) a i i
    let t := utility slope a i i
    let r := utility (values 6) a i j - values 6 i g
    let s := utility slope a i j - slope i g
    i ≠ j ∧ 0 < r ∧ 18*u ≤ 15*r ∧ 3*u+18*t ≤ 2*r+15*s ∧ 3*t ≤ 2*s

private def improves (b a : Allocation) : Prop :=
  (∀ i, utility (values 6) a i i ≤ utility (values 6) b i i ∧
    utility slope a i i ≤ utility slope b i i) ∧
  ∃ i, utility (values 6) a i i < utility (values 6) b i i

private def witnesses : List Allocation :=
  [![0,2,3,1,1,3,1,2,3], ![0,2,3,1,1,3,3,2,1],
   ![3,1,0,0,2,2,0,2,3], ![3,1,0,0,2,2,2,0,3],
   ![2,0,3,1,1,3,1,0,3], ![2,0,3,1,1,3,3,0,1],
   ![1,3,0,0,2,2,0,2,1], ![1,3,0,0,2,2,2,0,1],
   ![0,1,3,1,2,3,2,2,3], ![0,3,3,1,1,2,2,2,1],
   ![0,1,3,0,2,2,3,2,3], ![2,1,0,0,2,3,3,0,3],
   ![2,1,3,0,1,3,0,0,3], ![2,3,0,1,1,3,0,0,1],
   ![0,3,0,1,2,2,1,2,1], ![2,3,0,0,1,2,1,0,1]]

private def swapLarge (a : Allocation) : Allocation :=
  fun g => if g = 0 then a 1 else if g = 1 then a 0 else a g

private def verified (n : ℕ) : Prop :=
  let a := allocation n
  violation a ∨ improves (swapLarge a) a ∨ ∃ b ∈ witnesses, improves b a

private instance (a : Allocation) : Decidable (violation a) := by
  unfold violation
  infer_instance

private instance (b a : Allocation) : Decidable (improves b a) := by
  unfold improves
  infer_instance

private instance (n : ℕ) : Decidable (verified n) := by
  unfold verified
  infer_instance

private theorem violation_not_approximateEFX {K : ℕ} (hK : 6 ≤ K)
    {α : ℝ} (hα : 2 / 3 + 1 / (K : ℝ) < α) (a : Allocation)
    (hv : violation a) : ¬ ApproximateEFX α (values K) a := by
  simp only [violation, utility_eq] at hv
  obtain ⟨i, g, _, hij, hr, h0, h1, h2⟩ := hv
  intro ha
  have hfair := ha i (a g) g hij rfl
  rw [removed_affine hK, bundle_affine hK] at hfair
  let u := bundleValue (values 6) a i i
  let t := bundleValue slope a i i
  let r := bundleValue (values 6) a i (a g) - values 6 i g
  let s := bundleValue slope a i (a g) - slope i g
  let z : ℝ := (K-6 : ℕ)
  have hz : 0 ≤ z := Nat.cast_nonneg _
  have hu : 0 ≤ (u : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have h0' : 18*(u : ℝ) ≤ 15*r := by exact_mod_cast h0
  have h1' : 3*(u : ℝ)+18*t ≤ 2*r+15*s := by exact_mod_cast h1
  have h2' : 3*(t : ℝ) ≤ 2*s := by exact_mod_cast h2
  have hK' : (K : ℝ) = 6+z := by
    dsimp [z]
    have : K = 6+(K-6) := by omega
    exact_mod_cast this
  have hpoly : (18+3*z)*((u : ℝ)+z*t) ≤ (15+2*z)*((r : ℝ)+z*s) := by
    nlinarith [mul_nonneg hz (sub_nonneg.mpr h1'),
      mul_nonneg (sq_nonneg z) (sub_nonneg.mpr h2')]
  have hkpos : 0 < (K : ℝ) := by rw [hK']; positivity
  have halpha : 2*(K : ℝ)+3 < α*(3*K) := by
    have hm := mul_lt_mul_of_pos_right hα hkpos
    field_simp at hm
    nlinarith
  have hrz : 0 < (r : ℝ)+z*s := by positivity
  have hstrict := mul_lt_mul_of_pos_right halpha hrz
  push_cast at hfair
  change α*((r : ℝ)+z*s) ≤ (u : ℝ)+z*t at hfair
  rw [hK'] at hstrict
  nlinarith [mul_nonneg (show 0 ≤ 18+3*z by positivity) (sub_nonneg.mpr hfair)]

private theorem improves_dominates {K : ℕ} (hK : 6 ≤ K) (b a : Allocation)
    (h : improves b a) : ParetoDominates (values K) b a := by
  simp only [improves, utility_eq] at h
  constructor
  · intro i
    rw [bundle_affine hK, bundle_affine hK]
    exact Nat.add_le_add (h.1 i).1 (Nat.mul_le_mul_left _ (h.1 i).2)
  · obtain ⟨i, hi⟩ := h.2
    refine ⟨i, ?_⟩
    rw [bundle_affine hK, bundle_affine hK]
    exact Nat.add_lt_add_of_lt_of_le hi (Nat.mul_le_mul_left _ (h.1 i).2)



private def checked (offset count : ℕ) : Bool :=
  (List.range count).all fun i => decide (verified (offset+i))

section Certificate

-- Each block traverses a list of 4096 ownership functions, hence this recursion stack bound.
-- `decide +kernel` uses ordinary kernel reduction, without native evaluation or extra axioms.
set_option maxRecDepth 32768

private theorem block0 : checked (0 * 4096) 4096 = true := by decide +kernel
private theorem block1 : checked (1 * 4096) 4096 = true := by decide +kernel
private theorem block2 : checked (2 * 4096) 4096 = true := by decide +kernel
private theorem block3 : checked (3 * 4096) 4096 = true := by decide +kernel
private theorem block4 : checked (4 * 4096) 4096 = true := by decide +kernel
private theorem block5 : checked (5 * 4096) 4096 = true := by decide +kernel
private theorem block6 : checked (6 * 4096) 4096 = true := by decide +kernel
private theorem block7 : checked (7 * 4096) 4096 = true := by decide +kernel
private theorem block8 : checked (8 * 4096) 4096 = true := by decide +kernel
private theorem block9 : checked (9 * 4096) 4096 = true := by decide +kernel
private theorem block10 : checked (10 * 4096) 4096 = true := by decide +kernel
private theorem block11 : checked (11 * 4096) 4096 = true := by decide +kernel
private theorem block12 : checked (12 * 4096) 4096 = true := by decide +kernel
private theorem block13 : checked (13 * 4096) 4096 = true := by decide +kernel
private theorem block14 : checked (14 * 4096) 4096 = true := by decide +kernel
private theorem block15 : checked (15 * 4096) 4096 = true := by decide +kernel
private theorem block16 : checked (16 * 4096) 4096 = true := by decide +kernel
private theorem block17 : checked (17 * 4096) 4096 = true := by decide +kernel
private theorem block18 : checked (18 * 4096) 4096 = true := by decide +kernel
private theorem block19 : checked (19 * 4096) 4096 = true := by decide +kernel
private theorem block20 : checked (20 * 4096) 4096 = true := by decide +kernel
private theorem block21 : checked (21 * 4096) 4096 = true := by decide +kernel
private theorem block22 : checked (22 * 4096) 4096 = true := by decide +kernel
private theorem block23 : checked (23 * 4096) 4096 = true := by decide +kernel
private theorem block24 : checked (24 * 4096) 4096 = true := by decide +kernel
private theorem block25 : checked (25 * 4096) 4096 = true := by decide +kernel
private theorem block26 : checked (26 * 4096) 4096 = true := by decide +kernel
private theorem block27 : checked (27 * 4096) 4096 = true := by decide +kernel
private theorem block28 : checked (28 * 4096) 4096 = true := by decide +kernel
private theorem block29 : checked (29 * 4096) 4096 = true := by decide +kernel
private theorem block30 : checked (30 * 4096) 4096 = true := by decide +kernel
private theorem block31 : checked (31 * 4096) 4096 = true := by decide +kernel
private theorem block32 : checked (32 * 4096) 4096 = true := by decide +kernel
private theorem block33 : checked (33 * 4096) 4096 = true := by decide +kernel
private theorem block34 : checked (34 * 4096) 4096 = true := by decide +kernel
private theorem block35 : checked (35 * 4096) 4096 = true := by decide +kernel
private theorem block36 : checked (36 * 4096) 4096 = true := by decide +kernel
private theorem block37 : checked (37 * 4096) 4096 = true := by decide +kernel
private theorem block38 : checked (38 * 4096) 4096 = true := by decide +kernel
private theorem block39 : checked (39 * 4096) 4096 = true := by decide +kernel
private theorem block40 : checked (40 * 4096) 4096 = true := by decide +kernel
private theorem block41 : checked (41 * 4096) 4096 = true := by decide +kernel
private theorem block42 : checked (42 * 4096) 4096 = true := by decide +kernel
private theorem block43 : checked (43 * 4096) 4096 = true := by decide +kernel
private theorem block44 : checked (44 * 4096) 4096 = true := by decide +kernel
private theorem block45 : checked (45 * 4096) 4096 = true := by decide +kernel
private theorem block46 : checked (46 * 4096) 4096 = true := by decide +kernel
private theorem block47 : checked (47 * 4096) 4096 = true := by decide +kernel
private theorem block48 : checked (48 * 4096) 4096 = true := by decide +kernel
private theorem block49 : checked (49 * 4096) 4096 = true := by decide +kernel
private theorem block50 : checked (50 * 4096) 4096 = true := by decide +kernel
private theorem block51 : checked (51 * 4096) 4096 = true := by decide +kernel
private theorem block52 : checked (52 * 4096) 4096 = true := by decide +kernel
private theorem block53 : checked (53 * 4096) 4096 = true := by decide +kernel
private theorem block54 : checked (54 * 4096) 4096 = true := by decide +kernel
private theorem block55 : checked (55 * 4096) 4096 = true := by decide +kernel
private theorem block56 : checked (56 * 4096) 4096 = true := by decide +kernel
private theorem block57 : checked (57 * 4096) 4096 = true := by decide +kernel
private theorem block58 : checked (58 * 4096) 4096 = true := by decide +kernel
private theorem block59 : checked (59 * 4096) 4096 = true := by decide +kernel
private theorem block60 : checked (60 * 4096) 4096 = true := by decide +kernel
private theorem block61 : checked (61 * 4096) 4096 = true := by decide +kernel
private theorem block62 : checked (62 * 4096) 4096 = true := by decide +kernel
private theorem block63 : checked (63 * 4096) 4096 = true := by decide +kernel

end Certificate

private theorem verified_all (n : Fin 262144) : verified n.val := by
  have h : ∀ b : Fin 64, checked (b.val * 4096) 4096 = true := by
    intro b
    fin_cases b
    · exact block0
    · exact block1
    · exact block2
    · exact block3
    · exact block4
    · exact block5
    · exact block6
    · exact block7
    · exact block8
    · exact block9
    · exact block10
    · exact block11
    · exact block12
    · exact block13
    · exact block14
    · exact block15
    · exact block16
    · exact block17
    · exact block18
    · exact block19
    · exact block20
    · exact block21
    · exact block22
    · exact block23
    · exact block24
    · exact block25
    · exact block26
    · exact block27
    · exact block28
    · exact block29
    · exact block30
    · exact block31
    · exact block32
    · exact block33
    · exact block34
    · exact block35
    · exact block36
    · exact block37
    · exact block38
    · exact block39
    · exact block40
    · exact block41
    · exact block42
    · exact block43
    · exact block44
    · exact block45
    · exact block46
    · exact block47
    · exact block48
    · exact block49
    · exact block50
    · exact block51
    · exact block52
    · exact block53
    · exact block54
    · exact block55
    · exact block56
    · exact block57
    · exact block58
    · exact block59
    · exact block60
    · exact block61
    · exact block62
    · exact block63
  have hc := h ⟨n.val / 4096, by omega⟩
  have hi : n.val % 4096 ∈ List.range 4096 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have hv := of_decide_eq_true (List.all_eq_true.mp hc (n.val % 4096) hi)
  change verified (n.val / 4096 * 4096 + n.val % 4096) at hv
  have heq : n.val / 4096 * 4096 + n.val % 4096 = n.val := by omega
  rwa [heq] at hv

/-- For every integer `K ≥ 6`, every `α`-EFX allocation of Theorem 2's table, with
`α > 2/3 + 1/K`, has an actual strict Pareto improvement. Source: §4, PDF pp. 9–11
of [MahabadiRamakrishnanTarnawski2026]. All goods are assigned exactly once. -/
theorem approximateEFX_has_pareto_improvement {K : ℕ} (hK : 6 ≤ K)
    {α : ℝ} (hα : 2 / 3 + 1 / (K : ℝ) < α) (a : Fin 9 → Fin 4)
    (ha : ApproximateEFX α (values K) a) : ∃ b, ParetoDominates (values K) b a := by
  have hid : allocation (finFunctionFinEquiv a).val = a :=
    finFunctionFinEquiv.symm_apply_apply a
  have hc := verified_all (finFunctionFinEquiv a)
  unfold verified at hc
  rw [hid] at hc
  rcases hc with hv | hb | ⟨b, _, hb⟩
  · exact False.elim (violation_not_approximateEFX hK hα a hv ha)
  · exact ⟨swapLarge a, improves_dominates hK _ _ hb⟩
  · exact ⟨b, improves_dominates hK _ _ hb⟩

/-- Theorem 2: the positive parameterized table admits no allocation that is both
`α`-EFX and Pareto optimal. This does not assert nonexistence of `α`-EFX alone. -/
theorem not_approximateEFX_and_paretoOptimal {K : ℕ} (hK : 6 ≤ K)
    {α : ℝ} (hα : 2 / 3 + 1 / (K : ℝ) < α) (a : Fin 9 → Fin 4) :
    ¬ (ApproximateEFX α (values K) a ∧ ParetoOptimal (values K) a) := by
  rintro ⟨ha, hp⟩
  exact hp (approximateEFX_has_pareto_improvement hK hα a ha)

/-- Archimedean choice supplies a valid integer parameter for every real factor above `2/3`.
There is no restriction to rational approximation factors or to a fixed finite set of parameters. -/
theorem exists_parameter {α : ℝ} (hα : 2 / 3 < α) :
    ∃ K : ℕ, 6 ≤ K ∧ 2 / 3 + 1 / (K : ℝ) < α := by
  have hgap : 0 < α - 2 / 3 := by linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (max 6 (1 / (α - 2 / 3)))
  have h6 : (6 : ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
  have hbound : 1 / (α - 2 / 3) < (K : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hK
  have hpos : 0 < (K : ℝ) := by linarith
  have hrec : 1 / (K : ℝ) < α - 2 / 3 := (one_div_lt hpos hgap).mpr hbound
  refine ⟨K, ?_, by linarith⟩
  exact_mod_cast le_of_lt h6

/-- The arbitrary-factor endpoint in the introduction (PDF p. 3): for each real
`α > 2/3` there are strictly positive additive valuations for four agents and nine goods
for which every complete allocation fails `α`-EFX or Pareto optimality. The construction is
the integer-valued family of Theorem 2, so it also supplies ordinary rational or real valuations
by the canonical embeddings; no normalization or computational resource convention is imposed. -/
theorem exists_counterexample {α : ℝ} (hα : 2 / 3 < α) :
    ∃ v : Fin 4 → Fin 9 → ℕ, (∀ i g, 0 < v i g) ∧
      ∀ a, ¬ (ApproximateEFX α v a ∧ ParetoOptimal v a) := by
  obtain ⟨K, hK, hαK⟩ := exists_parameter hα
  exact ⟨values K, values_pos hK, not_approximateEFX_and_paretoOptimal hK hαK⟩

end ApproximateCounterexample

end Cslib.FairDivision
