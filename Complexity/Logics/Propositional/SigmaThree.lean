/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.SubcubeFree
public import Complexity.Logics.Propositional.DNF
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Set.Card

/-!
# Depth-three formulas of bottom fan-in `k`

A `Σ₃^k` formula for `f` is an OR of formulas in conjunctive normal form of width at most `k`
computing `f` (`IsSigmaThree`), and `Σ₃^k(f)` is the least number of formulas in one
(`sigmaThreeSize`); dually `Π₃^k(f) = Σ₃^k(¬f)` (`IsPiThree`, `piThreeSize_eq_sigmaThreeSize_not`).
If the true inputs of `f` contain no subcube of dimension `D`, neither do the solutions of any
formula in an OR computing `f`, so the bound on such formulas gives
`|f⁻¹(1)| ≤ Σ₃^k(f) · 2 ^ ((1 - 1 / k + ε) N + C D)` (`card_filter_le_sigmaThreeSize_mul`). For a
family of functions with `2 ^ (n - o(n))` true inputs containing no subcube of dimension `o(n)` (a
*subcube disperser*), `Σ₃^k(f) ≥ 2 ^ ((1 / k - ε) n)` for all large `n`
(`eventually_two_rpow_le_sigmaThreeSize`). The exponent `1 / k` cannot be improved: parity has no
subcube of dimension one among its true inputs, and is an OR of `2 ^ (n / k - 1)` formulas of
width `k` when `k` divides `n` (`CNF.exists_any_eval_eq_parity`).

## Main definitions

* `Cslib.Logic.PL.IsSigmaThree`, `Cslib.Logic.PL.IsPiThree`: depth-three formulas of bottom
  fan-in `k`.
* `Cslib.Logic.PL.sigmaThreeSize`, `Cslib.Logic.PL.piThreeSize`: `Σ₃^k(f)` and `Π₃^k(f)`.
* `Cslib.Logic.PL.CNF.minterm`: the CNF formula of unit clauses accepting a single input.

## Main results

* `Cslib.Logic.PL.piThreeSize_eq_sigmaThreeSize_not`: De Morgan duality.
* `Cslib.Logic.PL.card_filter_le_sigmaThreeSize_mul`: the finite bound.
* `Cslib.Logic.PL.eventually_two_rpow_le_sigmaThreeSize`,
  `Cslib.Logic.PL.eventually_two_rpow_le_piThreeSize`: subcube dispersers need `2 ^ ((1/k - ε) n)`
  formulas.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability coding lemma*][PaturiPudlakZane1999]
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Filter Asymptotics BitString

variable {N : ℕ}

/-- `Fs` is a `Σ₃^k` formula for `f`: an OR of formulas in conjunctive normal form of width at
most `k` computing `f`. -/
def IsSigmaThree (k : ℕ) (f : BitString N → Bool) (Fs : List (CNF (Fin N))) : Prop :=
  (∀ F ∈ Fs, ∀ c ∈ F, c.length ≤ k) ∧ ∀ x, f x = Fs.any fun F => F.eval x

/-- `Gs` is a `Π₃^k` formula for `f`: an AND of formulas in disjunctive normal form of width at
most `k` computing `f`. -/
def IsPiThree (k : ℕ) (f : BitString N → Bool) (Gs : List (DNF (Fin N))) : Prop :=
  (∀ G ∈ Gs, ∀ t ∈ G, t.length ≤ k) ∧ ∀ x, f x = Gs.all fun G => G.eval x

/-- `Σ₃^k(f)`: the least number of formulas in a `Σ₃^k` formula for `f`; there is one for `k ≥ 1`
(`exists_isSigmaThree`). -/
noncomputable def sigmaThreeSize (k : ℕ) (f : BitString N → Bool) : ℕ :=
  sInf {t | ∃ Fs, IsSigmaThree k f Fs ∧ Fs.length = t}

/-- `Π₃^k(f)`: the least number of formulas in a `Π₃^k` formula for `f`. -/
noncomputable def piThreeSize (k : ℕ) (f : BitString N → Bool) : ℕ :=
  sInf {t | ∃ Gs, IsPiThree k f Gs ∧ Gs.length = t}

/-- The formula accepting exactly `x`: one unit clause per variable. -/
def CNF.minterm (x : BitString N) : CNF (Fin N) :=
  (List.finRange N).map fun i => [(i, x i)]

/-- `CNF.minterm x` evaluates to `true` on `y` iff `y = x`. -/
theorem CNF.eval_minterm_eq_true_iff (x y : BitString N) :
    (CNF.minterm x).eval y = true ↔ y = x := by
  rw [funext_iff]
  simp [CNF.minterm, CNF.eval_map_eq_true_iff]

/-- Every function has a `Σ₃^k` formula for `k ≥ 1`: the OR of the minterms of its true
inputs. -/
theorem exists_isSigmaThree {k : ℕ} (hk : 1 ≤ k) (f : BitString N → Bool) :
    ∃ Fs, IsSigmaThree k f Fs := by
  refine ⟨({x | f x = true} : Finset (BitString N)).toList.map CNF.minterm,
    fun F hF c hc => ?_, fun y => ?_⟩
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hF
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
    simpa using hk
  · rw [Bool.eq_iff_iff, List.any_eq_true]
    simp only [List.mem_map, mem_toList, mem_filter, mem_univ, true_and]
    constructor
    · intro hy
      exact ⟨CNF.minterm y, ⟨y, hy, rfl⟩, (CNF.eval_minterm_eq_true_iff y y).mpr rfl⟩
    · rintro ⟨F, ⟨x, hx, rfl⟩, hFy⟩
      rwa [(CNF.eval_minterm_eq_true_iff x y).mp hFy]

/-- For `k ≥ 1`, there exists a `Σ₃^k` formula for `f` attaining `sigmaThreeSize k f`. -/
theorem exists_isSigmaThree_length_eq_sigmaThreeSize {k : ℕ} (hk : 1 ≤ k)
    (f : BitString N → Bool) : ∃ Fs, IsSigmaThree k f Fs ∧ Fs.length = sigmaThreeSize k f := by
  obtain ⟨Fs, hFs⟩ := exists_isSigmaThree hk f
  exact Nat.sInf_mem (s := {t | ∃ Fs, IsSigmaThree k f Fs ∧ Fs.length = t})
    ⟨Fs.length, Fs, hFs, rfl⟩

/-- Every `Σ₃^k` formula for `f` has at least `sigmaThreeSize k f` CNF formulas. -/
theorem sigmaThreeSize_le_length {k : ℕ} {f : BitString N → Bool} {Fs : List (CNF (Fin N))}
    (h : IsSigmaThree k f Fs) : sigmaThreeSize k f ≤ Fs.length :=
  Nat.sInf_le ⟨Fs, h, rfl⟩

/-- **De Morgan duality**: an AND of formulas in disjunctive normal form computes `f` exactly when
the OR of their negations, of the same widths, computes `¬f`. -/
theorem isPiThree_iff_isSigmaThree_map_negate {k : ℕ} {f : BitString N → Bool}
    (Gs : List (DNF (Fin N))) :
    IsPiThree k f Gs ↔ IsSigmaThree k (fun x => !f x) (Gs.map DNF.negate) := by
  unfold IsPiThree IsSigmaThree
  refine and_congr ⟨fun h F hF c hc => ?_, fun h G hG t ht => ?_⟩ (forall_congr' fun x => ?_)
  · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    simpa [Term.negate] using h G hG t ht
  · simpa [Term.negate] using h _ (List.mem_map_of_mem hG) _ (List.mem_map_of_mem ht)
  · rw [List.any_map]
    simp only [Function.comp_def, DNF.eval_negate, List.any_eq_not_all_not, Bool.not_not]
    cases f x <;> cases Gs.all fun G => G.eval x <;> simp

private theorem DNF.negate_negate (G : CNF (Fin N)) : DNF.negate (CNF.negate G) = G := by
  simp only [DNF.negate, CNF.negate, List.map_map]
  conv_rhs => rw [← List.map_id G]
  congr 1
  funext c
  simp only [Function.comp_apply, Term.negate, Clause.negate, List.map_map, id]
  conv_rhs => rw [← List.map_id c]
  congr 1
  funext l
  simp

/-- `Π₃^k(f) = Σ₃^k(¬f)`. -/
theorem piThreeSize_eq_sigmaThreeSize_not (k : ℕ) (f : BitString N → Bool) :
    piThreeSize k f = sigmaThreeSize k (fun x => !f x) := by
  unfold piThreeSize sigmaThreeSize
  congr 1
  ext t
  constructor
  · rintro ⟨Gs, hGs, rfl⟩
    exact ⟨Gs.map DNF.negate, (isPiThree_iff_isSigmaThree_map_negate Gs).mp hGs,
      List.length_map _⟩
  · rintro ⟨Fs, hFs, rfl⟩
    refine ⟨Fs.map CNF.negate, (isPiThree_iff_isSigmaThree_map_negate _).mpr ?_, List.length_map _⟩
    rwa [List.map_map, show DNF.negate ∘ CNF.negate = id from funext DNF.negate_negate,
      List.map_id]

/-- **The finite bound**: for `k ≥ 1` and `ε > 0` there is `C ≥ 0` such that every OR of `t`
formulas of width at most `k` computing a function whose true inputs contain no subcube of
dimension `D` has `|f⁻¹(1)| ≤ t · 2 ^ ((1 - 1 / k + ε) N + C D)`. -/
private theorem IsSigmaThree.card_filter_le_length_mul (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (f : BitString N → Bool) (D : ℕ) (Fs : List (CNF (Fin N))),
      IsSigmaThree k f Fs → ¬ ContainsSubcube {x | f x = true} D →
      (#{x | f x = true} : ℝ) ≤ Fs.length * 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) := by
  obtain ⟨C, hC, hA⟩ := CNF.card_filter_eval_le_of_not_containsSubcube k hk hε
  refine ⟨C, hC, fun N f D Fs hFs hfree => ?_⟩
  set E := (1 - 1 / (k : ℝ) + ε) * N + C * D
  have hsub : ({x | f x = true} : Finset (BitString N)) ⊆
      Fs.toFinset.biUnion fun F => {x | F.eval x = true} := by
    intro x hx
    have hfx := (mem_filter.mp hx).2
    rw [hFs.2 x, List.any_eq_true] at hfx
    obtain ⟨F, hF, hFx⟩ := hfx
    exact mem_biUnion.mpr ⟨F, List.mem_toFinset.mpr hF, mem_filter.mpr ⟨mem_univ _, hFx⟩⟩
  have hpiece : ∀ F ∈ Fs.toFinset, (#{x | F.eval x = true} : ℝ) ≤ 2 ^ E := by
    intro F hF
    have hF' := List.mem_toFinset.mp hF
    refine hA N F D (hFs.1 F hF') fun h => hfree (h.mono fun x hx => ?_)
    change f x = true
    rw [hFs.2 x, List.any_eq_true]
    exact ⟨F, hF', hx⟩
  calc (#{x | f x = true} : ℝ)
      ≤ #(Fs.toFinset.biUnion fun F => ({x | F.eval x = true} : Finset (BitString N))) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ F ∈ Fs.toFinset, (#{x | F.eval x = true} : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _F ∈ Fs.toFinset, (2 : ℝ) ^ E := sum_le_sum hpiece
    _ = #Fs.toFinset * 2 ^ E := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Fs.length * 2 ^ E := by
        gcongr
        exact_mod_cast List.toFinset_card_le Fs

/-- **The finite bound for `Σ₃^k`**: for `k ≥ 1` and `ε > 0` there is `C ≥ 0` such that every `f`
whose true inputs contain no subcube of dimension `D` has
`|f⁻¹(1)| ≤ Σ₃^k(f) · 2 ^ ((1 - 1 / k + ε) N + C D)`. -/
theorem card_filter_le_sigmaThreeSize_mul (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (f : BitString N → Bool) (D : ℕ),
      ¬ ContainsSubcube {x | f x = true} D →
      (#{x | f x = true} : ℝ) ≤ sigmaThreeSize k f * 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) := by
  obtain ⟨C, hC, hbound⟩ := IsSigmaThree.card_filter_le_length_mul k hk hε
  refine ⟨C, hC, fun N f D hfree => ?_⟩
  obtain ⟨Fs, hFs, hlen⟩ := exists_isSigmaThree_length_eq_sigmaThreeSize hk f
  rw [← hlen]
  exact hbound N f D Fs hFs hfree

/-- **Subcube dispersers need many formulas**: if the true inputs of `f n` eventually contain no
subcube of dimension `D n = o(n)` and number `2 ^ (n - o(n))`, then for every `k ≥ 1` and `ε > 0`,
`Σ₃^k(f n) ≥ 2 ^ ((1 / k - ε) n)` for all large `n`. -/
theorem eventually_two_rpow_le_sigmaThreeSize {f : (n : ℕ) → BitString n → Bool} {D : ℕ → ℕ}
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hfree : ∀ᶠ n in atTop, ¬ ContainsSubcube {x | f n x = true} (D n))
    (hdense : (fun n : ℕ => (n : ℝ) * Real.log 2 - Real.log (#{x | f n x = true} : ℕ))
      =o[atTop] (fun n => (n : ℝ)))
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤ sigmaThreeSize k (f n) := by
  obtain ⟨C, hC, hA⟩ := card_filter_le_sigmaThreeSize_mul k hk (ε := ε / 3) (by positivity)
  set δ := min (ε / 3) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : ∀ᶠ n : ℕ in atTop, C * D n ≤ ε / 3 * n := by
    have hc : 0 < ε / (3 * (C + 1)) := by positivity
    filter_upwards [hD.bound hc] with n hn
    simp only [Real.norm_natCast] at hn
    calc C * D n ≤ C * (ε / (3 * (C + 1)) * n) := mul_le_mul_of_nonneg_left hn hC
      _ ≤ ε / 3 * n := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n)
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have h2 : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.log 2 - Real.log (#{x | f n x = true} : ℕ) ≤ δ * Real.log 2 * n := by
    filter_upwards [hdense.bound (mul_pos hδ0 hlog2)] with n hn
    simp only [Real.norm_natCast] at hn
    exact (le_abs_self _).trans hn
  filter_upwards [h1, h2, hfree, eventually_ge_atTop 1] with n h1 h2 hfree hn
  set s := #{x | f n x = true}
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- the true inputs are many
  have hlogs : (1 - δ) * n * Real.log 2 ≤ Real.log s := by nlinarith
  have hspos : (0 : ℝ) < s := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero] at hlogs
      have : δ ≤ 1 / 2 := min_le_right _ _
      have : 0 < (1 - δ) * n * Real.log 2 := mul_pos (mul_pos (by linarith) (by linarith)) hlog2
      linarith
    · exact_mod_cast hpos
  have hsbig : (2 : ℝ) ^ ((1 - δ) * n) ≤ s := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_log hspos]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbound := hA n (f n) (D n) hfree
  set E := (1 - 1 / (k : ℝ) + ε / 3) * n + C * D n
  have hlow : (2 : ℝ) ^ ((1 - δ) * n - E) ≤ sigmaThreeSize k (f n) := by
    rw [Real.rpow_sub (by norm_num), div_le_iff₀ (by positivity)]
    exact hsbig.trans hbound
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hlow
  have : δ ≤ ε / 3 := min_le_left _ _
  simp only [E]
  nlinarith

/-- **Dually for `Π₃^k`**: if the false inputs of `f n` eventually contain no subcube of dimension
`o(n)` and number `2 ^ (n - o(n))`, then `Π₃^k(f n) ≥ 2 ^ ((1 / k - ε) n)` for all large `n`. -/
theorem eventually_two_rpow_le_piThreeSize {f : (n : ℕ) → BitString n → Bool} {D : ℕ → ℕ}
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hfree : ∀ᶠ n in atTop, ¬ ContainsSubcube {x | f n x = false} (D n))
    (hdense : (fun n : ℕ => (n : ℝ) * Real.log 2 - Real.log (#{x | f n x = false} : ℕ))
      =o[atTop] (fun n => (n : ℝ)))
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤ piThreeSize k (f n) := by
  have hset (n : ℕ) : {x : BitString n | (!f n x) = true} = {x | f n x = false} := by
    ext x
    simp
  have hfin (n : ℕ) : (#{x : BitString n | (!f n x) = true} : ℕ) = #{x | f n x = false} := by
    simp
  have h := eventually_two_rpow_le_sigmaThreeSize (f := fun n x => !f n x) hD
    (by simpa only [hset] using hfree) (by simpa only [hfin] using hdense) hk hε
  simpa only [piThreeSize_eq_sigmaThreeSize_not] using h

end Cslib.Logic.PL
