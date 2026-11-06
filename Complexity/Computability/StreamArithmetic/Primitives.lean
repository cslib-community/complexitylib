/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import Complexity.Computability.StreamArithmetic.Interface
public import Complexity.Foundations.Analysis.SignedDigitStream.Reciprocal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified stream arithmetic primitives and composition combinators

This module constructs certified `UniformStreamRecipe` implementations for every primitive
operation in [OpenAI2026LogSpace, Sections 10.3--10.6, Lemmas 10.3--10.7]:

* **Variables, rational constants, negation, and structural guards**:
  `Cslib.StreamArithmetic.varRecipe`, `Cslib.StreamArithmetic.ratRecipe`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.neg`, and
  `Cslib.StreamArithmetic.UniformStreamRecipe.guardStruct`.
* **Elementary operations and shift-clip** (**Lemmas 10.3 & 10.7**):
  `Cslib.StreamArithmetic.pairAvgPrim`, `Cslib.StreamArithmetic.maxPrim`,
  `Cslib.StreamArithmetic.minPrim`, `Cslib.StreamArithmetic.shiftClipPrim`, and direct recipe
  combinators `Cslib.StreamArithmetic.UniformStreamRecipe.pairAvg`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.max`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.min`, and
  `Cslib.StreamArithmetic.UniformStreamRecipe.shiftClip` (with top-down comparator slope
  `coeffB = 6` when comparing prefixes without an uncharged loop counter).
* **Balanced binary-tree averages** (**Lemma 10.7**): `Cslib.StreamArithmetic.balancedAvgPrim` and
  `Cslib.StreamArithmetic.balancedAvgRecipe` averaging `2 ^ r` streams (`r ≤ κ * d`) with
  `coeffB = 0` and `O((κ + 1) * d)` retained bits.
* **Minimum-index dyadic band multiplication** (**Lemma 10.4**): `Cslib.StreamArithmetic.mulPrim`
  and `Cslib.StreamArithmetic.UniformStreamRecipe.mul`, paying for band width `2 ^ (k - 1)` and
  band/offset counters out of the clock drop `t - j`.
* **Early-word reciprocal on `[1 / 4, 1]` and unit prefix clamping** (**Lemma 10.5 & Section
  10.6**): `Cslib.StreamArithmetic.clipUnitPrefix`, `Cslib.StreamArithmetic.clippedUnitPrefixProg`,
  `Cslib.StreamArithmetic.recip64Prim`, and `Cslib.StreamArithmetic.UniformStreamRecipe.recip64`,
  forming the `(t / 2 + 8)`-place prefix (computing `1 / (64 * x)` for inputs `x ∈ [1 / 4, 1]`)
  only during early-word queries `j ≤ t / 2 + 7` and releasing it before any suffix query.
* **Indexed finite rank** (**Lemma 10.6**): `Cslib.StreamArithmetic.rankListRecipe` and
  `Cslib.StreamArithmetic.rankFinsetRecipe`, computing `Finset.kthLargest` over `≤ 2 ^ (κ * d)`
  streams with `O((κ + 1) * d)` index/counter overhead and comparator slope `coeffB = 6`.

## Main definitions

* `Cslib.StreamArithmetic.varRecipe`, `Cslib.StreamArithmetic.ratRecipe`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.neg`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.guardStruct`.
* `Cslib.StreamArithmetic.pairAvgPrim`, `Cslib.StreamArithmetic.maxPrim`,
  `Cslib.StreamArithmetic.minPrim`, `Cslib.StreamArithmetic.shiftClipPrim`,
  `Cslib.StreamArithmetic.balancedAvgPrim`, `Cslib.StreamArithmetic.balancedAvgRecipe`.
* `Cslib.StreamArithmetic.mulPrim`, `Cslib.StreamArithmetic.recip64Prim`,
  `Cslib.StreamArithmetic.clipUnitPrefix`, `Cslib.StreamArithmetic.clippedUnitPrefixProg`.
* `Cslib.StreamArithmetic.rankListRecipe`, `Cslib.StreamArithmetic.rankFinsetRecipe`.

## Main results

* `Cslib.StreamArithmetic.eval_pairAvgResProg`, `Cslib.StreamArithmetic.eval_maxResProg`,
  `Cslib.StreamArithmetic.eval_minResProg`, `Cslib.StreamArithmetic.eval_shiftClipResProg`.
* `Cslib.StreamArithmetic.balancedAvgDigitProg_emits`: exactness and signed-digit emission for
  depth-`r` balanced binary-tree averages.
* `Cslib.StreamArithmetic.eval_intPrefixProg`, `Cslib.StreamArithmetic.eval_clippedUnitPrefixProg`,
  `Cslib.StreamArithmetic.clipUnitPrefix_le_two_pow`,
  `Cslib.StreamArithmetic.abs_clipUnitPrefix_div_sub_streamVal_le`,
  `Cslib.StreamArithmetic.eval_recip64ResProg`.
* `Cslib.StreamArithmetic.eval_rankListResProg`: exact mod-16 residue evaluation for indexed
  `Finset.kthLargest` over duplicate-free lists.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 10.3--10.6, Lemmas 10.3--10.7 (23 September 2026, revision `7ef5c0cc`,
  not peer reviewed).
-/

public section

namespace Cslib.StreamArithmetic

open Cslib.SignedDigitStream Finset

universe u u' v w

section BasicPrimitives

/-- Exact negation of a signed-digit stream negates its real value. -/
theorem streamVal_neg_eq (x : ℕ → ℤ) : streamVal (fun j => -x j) = -streamVal x := by
  unfold streamVal
  simp only [Int.cast_neg, neg_div]
  exact tsum_neg

/-- Identity `UniformStreamRecipe` reading operand `op` directly. -/
@[expose] noncomputable def varRecipe {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (op : Op) : UniformStreamRecipe Op Struct where
  slack := d
  slack_pos := hd
  ValidEnv env _ := IsNormSignedStream (env op)
  targetVal val _ := val op
  digitProg t := .queryDigit op t 4 .ret
  coeffA := 4
  coeffB := 0
  coeffC := 0
  intrinsicCoeff := 4
  abs_targetVal_le_one h := h.2
  emits_signed h := h.1
  emits_exact _ := rfl
  allowance t _ _ ev hev := by
    simp only [QueryProg.activeQueries, List.mem_cons] at hev
    rcases hev with rfl | hev
    · refine ⟨by omega, ?_⟩
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact_mod_cast Nat.le_mul_of_pos_right 4 hd
    · nomatch hev
  intrinsic_bound t _ _ := by
    simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
    have h4 : 4 ≤ 4 * d := Nat.le_mul_of_pos_right 4 hd
    omega

/-- Constant rational `UniformStreamRecipe` emitting `ratStream q` for any `|q| ≤ 1` using
`(κ + 8) * (d + t)` scratch bits and zero oracle queries. -/
@[expose] noncomputable def ratRecipe {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (q : ℚ) (hq : |q| ≤ 1) (κ : ℕ := 0) :
    UniformStreamRecipe Op Struct where
  slack := d
  slack_pos := hd
  ValidEnv _ _ := True
  targetVal _ _ := (q : ℝ)
  digitProg t := .scratchStep ((κ + 8) * (d + t)) (.ret (ratStream q t))
  coeffA := 0
  coeffB := 0
  coeffC := 0
  intrinsicCoeff := κ + 8
  abs_targetVal_le_one _ := by exact_mod_cast hq
  emits_signed _ := ratStream_isSignedStream hq
  emits_exact _ := streamVal_ratStream hq
  allowance _ _ _ _ hev := nomatch hev
  intrinsic_bound _ _ _ := by simp [QueryProg.maxIntrinsicBits]

/-- Exact stream negation with zero additional query or storage overhead. -/
@[expose] noncomputable def UniformStreamRecipe.neg {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) : UniformStreamRecipe Op Struct where
  slack := R.slack
  slack_pos := R.slack_pos
  ValidEnv := R.ValidEnv
  targetVal val sEnv := -R.targetVal val sEnv
  digitProg t := (R.digitProg t).map (- ·)
  coeffA := R.coeffA
  coeffB := R.coeffB
  coeffC := R.coeffC
  intrinsicCoeff := R.intrinsicCoeff
  abs_targetVal_le_one h := by
    rw [abs_neg]
    exact R.abs_targetVal_le_one h
  emits_signed {env sEnv} h := by
    have heq : (fun t => ((R.digitProg t).map (- ·)).eval env sEnv) =
        fun t => -((R.digitProg t).eval env sEnv) := by
      ext t
      exact QueryProg.eval_map _ _ _ _
    rw [heq]
    exact (R.emits_signed h).neg
  emits_exact {env sEnv} h := by
    have heq : (fun t => ((R.digitProg t).map (- ·)).eval env sEnv) =
        fun t => -((R.digitProg t).eval env sEnv) := by
      ext t
      exact QueryProg.eval_map _ _ _ _
    rw [heq, streamVal_neg_eq, R.emits_exact h]
  allowance t env sEnv _ hev := by
    rw [QueryProg.activeQueries_map] at hev
    exact R.allowance t env sEnv hev
  intrinsic_bound t env sEnv := by
    rw [QueryProg.maxIntrinsicBits_map]
    exact R.intrinsic_bound t env sEnv

/-- Structural indicator guard emitting `R` when `sEnv sOp = true` and `0` when
`sEnv sOp = false`, requiring `R.ValidEnv` only on the active branch `sEnv sOp = true`
[OpenAI2026LogSpace, Section 10.5]. -/
@[expose] noncomputable def UniformStreamRecipe.guardStruct {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) (sOp : Struct) : UniformStreamRecipe Op Struct :=
  let zeroR := ratRecipe (Op := Op) (Struct := Struct) R.slack R.slack_pos 0 (by norm_num)
  let raw := UniformStreamRecipe.condStruct sOp R zeroR rfl
  (raw.weakenValid
    (fun env sEnv => sEnv sOp = true → R.ValidEnv env sEnv)
    (fun h => ⟨h, fun _ => trivial⟩)).congrTarget
    (fun val sEnv => if sEnv sOp then R.targetVal val sEnv else 0)
    (fun {env sEnv} _ => by
      change (if sEnv sOp then R.targetVal (fun op => streamVal (env op)) sEnv else ((0 : ℚ) : ℝ)) =
        if sEnv sOp then R.targetVal (fun op => streamVal (env op)) sEnv else 0
      rw [Rat.cast_zero])

/-- Remap operand indices inside a `QueryProg`. -/
@[expose] def QueryProg.reindexOp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {α : Type w} (f : Op₁ → Op₂) : QueryProg Op₁ Struct α → QueryProg Op₂ Struct α
  | .ret a => .ret a
  | .scratchStep s next => .scratchStep s (reindexOp f next)
  | .queryDigit op j l next => .queryDigit (f op) j l (fun d => reindexOp f (next d))
  | .queryStruct sOp l next => .queryStruct sOp l (fun b => reindexOp f (next b))

@[simp]
theorem QueryProg.eval_reindexOp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {α : Type w} (f : Op₁ → Op₂) (p : QueryProg Op₁ Struct α)
    (env : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.reindexOp f).eval env sEnv = p.eval (fun op => env (f op)) sEnv := by
  induction p with
  | ret _ => rfl
  | scratchStep _ _ ih => exact ih
  | queryDigit _ _ _ _ ih => exact ih _
  | queryStruct _ _ _ ih => exact ih _

theorem QueryProg.mem_activeQueries_reindexOp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {α : Type w} (f : Op₁ → Op₂) (p : QueryProg Op₁ Struct α)
    (env : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op₂ Struct}
    (hev : ev ∈ (p.reindexOp f).activeQueries env sEnv) :
    (∃ sOp l, QueryEvent.struct sOp l ∈ p.activeQueries (fun op => env (f op)) sEnv ∧
        ev = .struct sOp l) ∨
      ∃ op j l, QueryEvent.digit op j l ∈ p.activeQueries (fun op => env (f op)) sEnv ∧
        ev = .digit (f op) j l := by
  induction p with
  | ret _ => nomatch hev
  | scratchStep _ _ ih => exact ih hev
  | queryDigit op j l next ih =>
    simp only [reindexOp, activeQueries, List.mem_cons] at hev
    rcases hev with rfl | hev
    · right
      exact ⟨op, j, l, List.mem_cons_self, rfl⟩
    · rcases ih (env (f op) j) hev with ⟨sOp, ls, hs, rfl⟩ | ⟨op', j', l', hd, rfl⟩
      · left
        exact ⟨sOp, ls, List.mem_cons_of_mem _ hs, rfl⟩
      · right
        exact ⟨op', j', l', List.mem_cons_of_mem _ hd, rfl⟩
  | queryStruct sOp l next ih =>
    simp only [reindexOp, activeQueries, List.mem_cons] at hev
    rcases hev with rfl | hev
    · left
      exact ⟨sOp, l, List.mem_cons_self, rfl⟩
    · rcases ih (sEnv sOp) hev with ⟨sOp', ls, hs, rfl⟩ | ⟨op', j', l', hd, rfl⟩
      · left
        exact ⟨sOp', ls, List.mem_cons_of_mem _ hs, rfl⟩
      · right
        exact ⟨op', j', l', List.mem_cons_of_mem _ hd, rfl⟩

@[simp]
theorem QueryProg.maxIntrinsicBits_reindexOp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {α : Type w} (f : Op₁ → Op₂) (p : QueryProg Op₁ Struct α)
    (env : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.reindexOp f).maxIntrinsicBits env sEnv =
      p.maxIntrinsicBits (fun op => env (f op)) sEnv := by
  induction p with
  | ret _ => rfl
  | scratchStep _ _ ih => exact congrArg (max _) ih
  | queryDigit _ _ _ _ ih => exact congrArg (max _) (ih _)
  | queryStruct _ _ _ ih => exact congrArg (max _) (ih _)

end BasicPrimitives

section ElementaryRecipes

/-- Mod-16 residue program for `(streamVal x + streamVal y) / 2` using 9-place low windows
[OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def pairAvgResProg {Struct : Type v} (s : ℕ) : QueryProg (Fin 2) Struct ℤ :=
  (windowPrefixModProg 0 9 (s + 4)).bindOverhead 10 fun r₀ =>
    (windowPrefixModProg 1 9 (s + 4)).bindOverhead 20 fun r₁ =>
      .scratchStep 20 (.ret (((r₀ + r₁) % 512) / 32))

theorem eval_pairAvgResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (pairAvgResProg s).eval env sEnv = pairAvgApprox (env 0) (env 1) s % 16 := by
  simp only [pairAvgResProg, QueryProg.eval_bindOverhead, QueryProg.eval,
    eval_windowPrefixModProg]
  unfold pairAvgApprox
  have h9 : (2 : ℤ) ^ (9 : ℕ) = 512 := by decide
  rw [h9, ← Int.add_emod]
  simpa only [show (16 : ℤ) = (2 : ℤ) ^ (4 : ℕ) by decide,
    show (32 : ℤ) = (2 : ℤ) ^ (5 : ℕ) by decide,
    show (2 : ℤ) ^ (4 + 5 : ℕ) = (512 : ℤ) by decide] using
    (ediv_two_pow_emod_eq (intPrefix (env 0) (s + 4) + intPrefix (env 1) (s + 4)) 4 5).symm

theorem mem_activeQueries_pairAvgResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (pairAvgResProg s).activeQueries env sEnv) :
    ∃ op j L, j ≤ s + 4 ∧ L ≤ 38 ∧ ev = .digit op j L := by
  simp only [pairAvgResProg, QueryProg.activeQueries_bindOverhead, QueryProg.activeQueries,
    List.append_nil, List.mem_append, List.mem_map] at hev
  rcases hev with ⟨ev₀, hev₀, rfl⟩ | ⟨ev₁, hev₁, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg 0 9 (s + 4) env sEnv hev₀
    exact ⟨0, j, 28, hj, by decide, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg 1 9 (s + 4) env sEnv hev₁
    exact ⟨1, j, 38, hj, by decide, rfl⟩

theorem maxIntrinsicBits_pairAvgResProg_le {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (pairAvgResProg s).maxIntrinsicBits env sEnv ≤ s + 46 := by
  simp only [pairAvgResProg]
  refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
  · have h0 := maxIntrinsicBits_windowPrefixModProg_le (0 : Fin 2) 9 (s + 4) env sEnv
    omega
  · refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · have h1 := maxIntrinsicBits_windowPrefixModProg_le (1 : Fin 2) 9 (s + 4) env sEnv
      omega
    · simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
      omega

/-- **Lemma 10.3 (certified pairwise average primitive)** [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] noncomputable def pairAvgPrim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe (Fin 2) Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ i, IsNormSignedStream (env i))
    (fun val _ => (val 0 + val 1) / 2)
    (fun env _ => pairAvgApprox (env 0) (env 1))
    pairAvgResProg 38 0 4 46
    (fun {env _} hV => by
      have h0 := (hV 0).2
      have h1 := (hV 1).2
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri := abs_add_le (streamVal (env 0)) (streamVal (env 1))
      linarith)
    (fun hV => pairAvgApprox_isScaledApprox (hV 0).1 (hV 1).1)
    (fun _ s => eval_pairAvgResProg s _ _)
    (fun s env sEnv _ hev => by
      obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_pairAvgResProg s env sEnv hev
      refine ⟨by have h4 := Nat.le_mul_of_pos_right 4 hd; omega, ?_⟩
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact_mod_cast hL.trans (Nat.le_mul_of_pos_right 38 hd))
    (fun s env sEnv =>
      (maxIntrinsicBits_pairAvgResProg_le s env sEnv).trans
        (by
          have h46 := Nat.le_mul_of_pos_right 46 hd
          rw [Nat.mul_add]
          omega))

/-- Mod-16 residue program for `max (streamVal x) (streamVal y)`
[OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def maxResProg {Struct : Type v} (s : ℕ) : QueryProg (Fin 2) Struct ℤ :=
  (cmpPrefixProg 0 1 (s + 4)).bindOverhead 6 fun c =>
    let win : Fin 2 := if 0 ≤ c then 0 else 1
    (windowPrefixModProg win 8 (s + 4)).map (· / 16)

theorem eval_maxResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (maxResProg s).eval env sEnv = maxApprox (env 0) (env 1) s % 16 := by
  unfold maxResProg maxApprox
  rw [QueryProg.eval_bindOverhead]
  have hc := eval_cmpPrefixProg (0 : Fin 2) 1 (s + 4) env sEnv
  rw [hc]
  set c := cmpPrefix (env 0) (env 1) (s + 4)
  have h16 : (16 : ℤ) = (2 : ℤ) ^ (4 : ℕ) := by decide
  have h256 : (2 : ℤ) ^ (8 : ℕ) = (2 : ℤ) ^ (4 + 4 : ℕ) := rfl
  by_cases h0 : 0 ≤ c
  · simp only [h0, ↓reduceIte, QueryProg.eval_map, eval_windowPrefixModProg, h256]
    rw [h16, ediv_two_pow_emod_eq]
  · simp only [h0, ↓reduceIte, QueryProg.eval_map, eval_windowPrefixModProg, h256]
    rw [h16, ediv_two_pow_emod_eq]

/-- **Lemma 10.3 (certified binary maximum primitive)** [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] noncomputable def maxPrim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe (Fin 2) Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ i, IsNormSignedStream (env i))
    (fun val _ => max (val 0) (val 1))
    (fun env _ => maxApprox (env 0) (env 1))
    maxResProg 40 6 4 40
    (fun hV => by
      rw [abs_le]
      have h0 := abs_le.mp (hV 0).2
      have h1 := abs_le.mp (hV 1).2
      exact ⟨h0.1.trans (le_max_left _ _), max_le h0.2 h1.2⟩)
    (fun hV => maxApprox_isScaledApprox (hV 0).1 (hV 1).1)
    (fun _ s => eval_maxResProg s _ _)
    (fun s env sEnv _ hev => by
      have h40 := Nat.le_mul_of_pos_right 40 hd
      simp only [maxResProg, QueryProg.activeQueries_bindOverhead, List.mem_append,
        List.mem_map] at hev
      rcases hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
      · obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_cmpPrefixProg 0 1 (s + 4) env sEnv hev₀
        refine ⟨by have h4 := Nat.le_mul_of_pos_right 4 hd; omega, ?_⟩
        change ((6 + L : ℕ) : ℤ) ≤ ((40 * d : ℕ) : ℤ) + (6 : ℤ) * ((s : ℤ) - (j : ℤ))
        omega
      · rw [QueryProg.activeQueries_map] at hev₁
        obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg _ 8 (s + 4) env sEnv hev₁
        refine ⟨by have h4 := Nat.le_mul_of_pos_right 4 hd; omega, ?_⟩
        change ((2 * 8 : ℕ) : ℤ) ≤ ((40 * d : ℕ) : ℤ) + (6 : ℤ) * ((s : ℤ) - (j : ℤ))
        omega)
    (fun s env sEnv => by
      have h40 := Nat.le_mul_of_pos_right 40 hd
      simp only [maxResProg]
      refine ((QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)).trans
        (show 6 * s + 40 ≤ 40 * (d + s) by rw [Nat.mul_add]; omega)
      · have h0 := maxIntrinsicBits_cmpPrefixProg_le (0 : Fin 2) 1 (s + 4) env sEnv
        omega
      · rw [QueryProg.maxIntrinsicBits_map]
        have hw := maxIntrinsicBits_windowPrefixModProg_le
          (if 0 ≤ (cmpPrefixProg 0 1 (s + 4)).eval env sEnv then (0 : Fin 2) else 1)
          8 (s + 4) env sEnv
        omega)

/-- Mod-16 residue program for `min (streamVal x) (streamVal y)`
[OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def minResProg {Struct : Type v} (s : ℕ) : QueryProg (Fin 2) Struct ℤ :=
  (cmpPrefixProg 0 1 (s + 4)).bindOverhead 6 fun c =>
    let win : Fin 2 := if c ≤ 0 then 0 else 1
    (windowPrefixModProg win 8 (s + 4)).map (· / 16)

theorem eval_minResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (minResProg s).eval env sEnv = minApprox (env 0) (env 1) s % 16 := by
  unfold minResProg minApprox
  rw [QueryProg.eval_bindOverhead]
  have hc := eval_cmpPrefixProg (0 : Fin 2) 1 (s + 4) env sEnv
  rw [hc]
  set c := cmpPrefix (env 0) (env 1) (s + 4)
  have h16 : (16 : ℤ) = (2 : ℤ) ^ (4 : ℕ) := by decide
  have h256 : (2 : ℤ) ^ (8 : ℕ) = (2 : ℤ) ^ (4 + 4 : ℕ) := rfl
  by_cases h0 : c ≤ 0
  · simp only [h0, ↓reduceIte, QueryProg.eval_map, eval_windowPrefixModProg, h256]
    rw [h16, ediv_two_pow_emod_eq]
  · simp only [h0, ↓reduceIte, QueryProg.eval_map, eval_windowPrefixModProg, h256]
    rw [h16, ediv_two_pow_emod_eq]

/-- **Lemma 10.3 (certified binary minimum primitive)** [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] noncomputable def minPrim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe (Fin 2) Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ i, IsNormSignedStream (env i))
    (fun val _ => min (val 0) (val 1))
    (fun env _ => minApprox (env 0) (env 1))
    minResProg 40 6 4 40
    (fun hV => by
      rw [abs_le]
      have h0 := abs_le.mp (hV 0).2
      have h1 := abs_le.mp (hV 1).2
      exact ⟨le_min h0.1 h1.1, (min_le_left _ _).trans h0.2⟩)
    (fun hV => minApprox_isScaledApprox (hV 0).1 (hV 1).1)
    (fun _ s => eval_minResProg s _ _)
    (fun s env sEnv _ hev => by
      have h40 := Nat.le_mul_of_pos_right 40 hd
      simp only [minResProg, QueryProg.activeQueries_bindOverhead, List.mem_append,
        List.mem_map] at hev
      rcases hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
      · obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_cmpPrefixProg 0 1 (s + 4) env sEnv hev₀
        refine ⟨by have h4 := Nat.le_mul_of_pos_right 4 hd; omega, ?_⟩
        change ((6 + L : ℕ) : ℤ) ≤ ((40 * d : ℕ) : ℤ) + (6 : ℤ) * ((s : ℤ) - (j : ℤ))
        omega
      · rw [QueryProg.activeQueries_map] at hev₁
        obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg _ 8 (s + 4) env sEnv hev₁
        refine ⟨by have h4 := Nat.le_mul_of_pos_right 4 hd; omega, ?_⟩
        change ((2 * 8 : ℕ) : ℤ) ≤ ((40 * d : ℕ) : ℤ) + (6 : ℤ) * ((s : ℤ) - (j : ℤ))
        omega)
    (fun s env sEnv => by
      have h40 := Nat.le_mul_of_pos_right 40 hd
      simp only [minResProg]
      refine ((QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)).trans
        (show 6 * s + 40 ≤ 40 * (d + s) by rw [Nat.mul_add]; omega)
      · have h0 := maxIntrinsicBits_cmpPrefixProg_le (0 : Fin 2) 1 (s + 4) env sEnv
        omega
      · rw [QueryProg.maxIntrinsicBits_map]
        have hw := maxIntrinsicBits_windowPrefixModProg_le
          (if (cmpPrefixProg 0 1 (s + 4)).eval env sEnv ≤ 0 then (0 : Fin 2) else 1)
          8 (s + 4) env sEnv
        omega)

/-- Helper composing any normalized binary primitive on `Fin 2` with two child recipes `R₁, R₂`. -/
@[expose] noncomputable def composeBinPrim {Op : Type u} {Struct : Type v}
    (prim : UniformStreamRecipe (Fin 2) Struct)
    (hPrimValid : ∀ (env₁ : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool),
      (∀ i, IsNormSignedStream (env₁ i)) → prim.ValidEnv env₁ sEnv)
    (R₁ R₂ : UniformStreamRecipe Op Struct)
    (hSlackP : prim.slack = R₁.slack) (hSlack₂ : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  let child : Fin 2 → UniformStreamRecipe Op Struct := fun i => if i = 0 then R₁ else R₂
  let raw := prim.comp child
    (max R₁.coeffA R₂.coeffA)
    (max R₁.coeffB R₂.coeffB)
    (max R₁.coeffC R₂.coeffC)
    (max R₁.intrinsicCoeff R₂.intrinsicCoeff)
    (fun i => by
      dsimp only [child]
      split_ifs <;> omega)
    (fun i => by
      dsimp only [child]
      split_ifs
      · exact le_max_left _ _
      · exact le_max_right _ _)
    (fun i => by
      dsimp only [child]
      split_ifs
      · exact le_max_left _ _
      · exact le_max_right _ _)
    (fun i => by
      dsimp only [child]
      split_ifs
      · exact le_max_left _ _
      · exact le_max_right _ _)
    (fun i => by
      dsimp only [child]
      split_ifs
      · exact le_max_left _ _
      · exact le_max_right _ _)
  let cleaned := raw.weakenValid (fun env sEnv => R₁.ValidEnv env sEnv ∧ R₂.ValidEnv env sEnv)
    (fun ⟨h₁, h₂⟩ => by
      refine ⟨fun i => ?_, hPrimValid _ _ fun i => ?_⟩
      · dsimp only [child]
        split_ifs
        · exact h₁
        · exact h₂
      · dsimp only [child]
        split_ifs
        · refine ⟨R₁.emits_signed h₁, ?_⟩
          rw [R₁.emits_exact h₁]
          exact R₁.abs_targetVal_le_one h₁
        · refine ⟨R₂.emits_signed h₂, ?_⟩
          rw [R₂.emits_exact h₂]
          exact R₂.abs_targetVal_le_one h₂)
  { cleaned with
    slack := R₁.slack
    slack_pos := R₁.slack_pos
    allowance := fun t env sEnv _ hev => by
      have h := cleaned.allowance t env sEnv hev
      change AllowanceBound prim.slack _ _ _ t _ at h
      rwa [hSlackP] at h
    intrinsic_bound := fun t env sEnv => by
      have h := cleaned.intrinsic_bound t env sEnv
      change _ ≤ _ * (prim.slack + t) at h
      rwa [hSlackP] at h }

/-- Compose two `UniformStreamRecipe`s with exact pairwise average `(R₁ + R₂) / 2`. -/
@[expose] noncomputable def UniformStreamRecipe.pairAvg {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (hSlack : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  (composeBinPrim (pairAvgPrim R₁.slack R₁.slack_pos) (fun _ _ h => h) R₁ R₂ rfl hSlack).congrTarget
    (fun val sEnv => (R₁.targetVal val sEnv + R₂.targetVal val sEnv) / 2)
    (fun _ => rfl)

/-- Compose two `UniformStreamRecipe`s with exact binary maximum `max R₁ R₂`. -/
@[expose] noncomputable def UniformStreamRecipe.max {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (hSlack : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  (composeBinPrim (maxPrim R₁.slack R₁.slack_pos) (fun _ _ h => h) R₁ R₂ rfl hSlack).congrTarget
    (fun val sEnv => Max.max (R₁.targetVal val sEnv) (R₂.targetVal val sEnv))
    (fun _ => rfl)

/-- Compose two `UniformStreamRecipe`s with exact binary minimum `min R₁ R₂`. -/
@[expose] noncomputable def UniformStreamRecipe.min {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (hSlack : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  (composeBinPrim (minPrim R₁.slack R₁.slack_pos) (fun _ _ h => h) R₁ R₂ rfl hSlack).congrTarget
    (fun val sEnv => Min.min (R₁.targetVal val sEnv) (R₂.targetVal val sEnv))
    (fun _ => rfl)

end ElementaryRecipes

section ShiftClipAndBalancedAverage

/-- Public signed-digit stream whose `K`-place `intPrefix` equals `2 ^ m` whenever `m ≤ K + 3`
and `4 ≤ m`. -/
@[expose] def clipBoundStream (m K : ℕ) (j : ℕ) : ℤ :=
  if m ≤ K then
    if j = K - m then 1 else 0
  else if m = K + 1 then
    if j = 0 then 2 else 0
  else if m = K + 2 then
    if j = 0 then 4 else 0
  else
    if j = 0 then 6 else if j = 1 then 4 else 0

theorem clipBoundStream_isSignedStream (m K : ℕ) : IsSignedStream (clipBoundStream m K) := by
  intro j
  unfold clipBoundStream IsSignedDigit
  split_ifs <;> decide

theorem intPrefix_neg_eq (x : ℕ → ℤ) (K : ℕ) :
    intPrefix (fun j => -x j) K = -intPrefix x K := by
  unfold intPrefix
  simp only [neg_mul, sum_neg_distrib]

theorem intPrefix_clipBoundStream_eq {m K : ℕ} (hm4 : 4 ≤ m) (hmK : m ≤ K + 3) :
    intPrefix (clipBoundStream m K) K = (2 : ℤ) ^ m := by
  unfold intPrefix clipBoundStream
  by_cases hle : m ≤ K
  · simp only [hle, ↓reduceIte, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    have hlt : K - m < K + 1 := by omega
    have hsub : K - (K - m) = m := by omega
    simp [hlt, hsub]
  · simp only [hle, ↓reduceIte]
    by_cases h1 : m = K + 1
    · simp only [h1, ↓reduceIte, ite_mul, zero_mul, sum_ite_eq', mem_range, Nat.zero_lt_succ,
        Nat.sub_zero]
      ring
    · simp only [h1, ↓reduceIte]
      by_cases h2 : m = K + 2
      · simp only [h2, ↓reduceIte, ite_mul, zero_mul, sum_ite_eq', mem_range, Nat.zero_lt_succ,
          Nat.sub_zero]
        ring
      · have h3 : m = K + 3 := by omega
        have hK1 : 1 ≤ K := by omega
        rcases Nat.exists_eq_add_of_le' hK1 with ⟨K', rfl⟩
        simp only [h2, ↓reduceIte, sum_range_succ' _ (K' + 1)]
        rw [sum_range_succ']
        have hzero : ∑ k ∈ range K',
            (if k + 1 + 1 = 0 then (6 : ℤ) else if k + 1 + 1 = 1 then 4 else 0) *
              (2 : ℤ) ^ (K' + 1 - (k + 1 + 1)) = 0 :=
          sum_eq_zero fun k _ => by simp
        rw [hzero]
        simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, Nat.sub_zero, Nat.add_sub_cancel]
        rw [h3]
        ring

/-- Mod-16 saturated positive boundary residue `⌊2 ^ (s + 4) / 16⌋ % 16` for `shiftClipApprox`. -/
@[expose] def posClipRes (s : ℕ) : ℤ :=
  if s < 4 then (2 : ℤ) ^ s else 0

/-- Mod-16 saturated negative boundary residue `(-2 ^ s) % 16` for `shiftClipApprox`. -/
@[expose] def negClipRes (s : ℕ) : ℤ :=
  if s < 4 then (-(2 : ℤ) ^ s) % 16 else 0

theorem posClipRes_eq (s : ℕ) :
    posClipRes s = ((2 : ℤ) ^ (s + 4) / 16) % 16 := by
  unfold posClipRes
  rcases s with _ | _ | _ | _ | s
  · decide
  · decide
  · decide
  · decide
  · have hlt : ¬ s + 4 < 4 := by omega
    simp only [hlt, ↓reduceIte]
    have hp : (2 : ℤ) ^ (s + 4 + 4) = 16 * (16 * (2 : ℤ) ^ s) := by ring
    rw [hp, Int.mul_ediv_cancel_left _ (by decide), Int.mul_emod_right]

theorem negClipRes_eq (s : ℕ) :
    negClipRes s = ((-((2 : ℤ) ^ (s + 4))) / 16) % 16 := by
  unfold negClipRes
  rcases s with _ | _ | _ | _ | s
  · decide
  · decide
  · decide
  · decide
  · have hlt : ¬ s + 4 < 4 := by omega
    simp only [hlt, ↓reduceIte]
    have hp : -((2 : ℤ) ^ (s + 4 + 4)) = 16 * (-(16 * (2 : ℤ) ^ s)) := by ring
    have hn : -(16 * (2 : ℤ) ^ s) = 16 * (-(2 : ℤ) ^ s) := by ring
    rw [hp, Int.mul_ediv_cancel_left _ (by decide), hn, Int.mul_emod_right]

/-- Mod-16 residue program for `shiftClipApprox v (env ()) s` using at most two 27-state
constant-bound prefix comparisons and an 8-bit low-residue window [OpenAI2026LogSpace, Lemma 10.7].
-/
@[expose] def shiftClipResProg {Struct : Type v} (v : ℤ) (s : ℕ) : QueryProg Unit Struct ℤ :=
  if (s : ℤ) + v + 4 < 0 then
    .scratchStep 8 (.ret 0)
  else
    let K := ((s : ℤ) + v + 4).toNat
    if K + 4 ≤ s + 4 then
      (windowPrefixModProg () 8 K).map (· / 16)
    else
      (cmpWithConstProg () (clipBoundStream (s + 4) K) K).bindOverhead 6 fun cHi =>
        if 0 ≤ cHi then
          .scratchStep 8 (.ret (posClipRes s))
        else
          (cmpWithConstProg () (fun j => -clipBoundStream (s + 4) K j) K).bindOverhead 6 fun cLo =>
            if cLo ≤ 0 then
              .scratchStep 8 (.ret (negClipRes s))
            else
              (windowPrefixModProg () 8 K).map (· / 16)

theorem eval_shiftClipResProg {Struct : Type v} (v : ℤ) (s : ℕ)
    {env : Unit → ℕ → ℤ} (hx : IsSignedStream (env ())) (sEnv : Struct → Bool) :
    (shiftClipResProg v s).eval env sEnv = shiftClipApprox v (env ()) s % 16 := by
  unfold shiftClipResProg shiftClipApprox
  by_cases hneg : (s : ℤ) + v + 4 < 0
  · simp [hneg, QueryProg.eval]
  · simp only [hneg, ↓reduceIte]
    set K := ((s : ℤ) + v + 4).toNat
    set B : ℤ := (2 : ℤ) ^ (s + 4)
    have h16 : (16 : ℤ) = (2 : ℤ) ^ (4 : ℕ) := by decide
    have h256 : (2 : ℤ) ^ (8 : ℕ) = (2 : ℤ) ^ (4 + 4 : ℕ) := rfl
    by_cases hsmall : K + 4 ≤ s + 4
    · simp only [hsmall, ↓reduceIte, QueryProg.eval_map, eval_windowPrefixModProg, h256]
      have habs := abs_intPrefix_le hx K
      have hpow : 16 * (2 : ℤ) ^ K ≤ B := by
        dsimp [B]
        have h16p : (16 : ℤ) * (2 : ℤ) ^ K = (2 : ℤ) ^ (K + 4) := by ring
        rw [h16p]
        exact pow_le_pow_right₀ (by decide) hsmall
      have hK_pos : (0 : ℤ) < (2 : ℤ) ^ K := by positivity
      obtain ⟨hlo_abs, hhi_abs⟩ := abs_le.mp habs
      have hmin : min B (intPrefix (env ()) K) = intPrefix (env ()) K := min_eq_right (by omega)
      have hmax : max (-B) (intPrefix (env ()) K) = intPrefix (env ()) K := max_eq_right (by omega)
      rw [hmin, hmax, h16, ediv_two_pow_emod_eq]
    · simp only [hsmall, ↓reduceIte, QueryProg.eval_bindOverhead]
      have hmK : s + 4 ≤ K + 3 := by omega
      have hb_sign := clipBoundStream_isSignedStream (s + 4) K
      have hb_pref : intPrefix (clipBoundStream (s + 4) K) K = B :=
        intPrefix_clipBoundStream_eq (by omega) hmK
      rw [eval_cmpWithConstProg]
      by_cases hcHi : 0 ≤ cmpPrefix (env ()) (clipBoundStream (s + 4) K) K
      · simp only [hcHi, ↓reduceIte, QueryProg.eval, posClipRes_eq]
        have hge : B ≤ intPrefix (env ()) K := by
          rw [← hb_pref]
          exact (cmpPrefix_nonneg_iff hx hb_sign K).mp hcHi
        have hB0 : 0 ≤ B := by dsimp [B]; positivity
        rw [min_eq_left hge, max_eq_right (by omega)]
      · simp only [hcHi, ↓reduceIte, QueryProg.eval_bindOverhead, eval_cmpWithConstProg]
        have hltHi : intPrefix (env ()) K ≤ B := by
          have hnot := (cmpPrefix_nonneg_iff hx hb_sign K).not.mp hcHi
          rw [hb_pref] at hnot
          omega
        by_cases hcLo : cmpPrefix (env ()) (fun j => -clipBoundStream (s + 4) K j) K ≤ 0
        · simp only [hcLo, ↓reduceIte, QueryProg.eval, negClipRes_eq]
          have hleLo : intPrefix (env ()) K ≤ -B := by
            have h := (cmpPrefix_nonpos_iff hx hb_sign.neg K).mp hcLo
            rwa [intPrefix_neg_eq, hb_pref] at h
          rw [min_eq_right hltHi, max_eq_left hleLo]
        · simp only [hcLo, ↓reduceIte, QueryProg.eval_map, eval_windowPrefixModProg, h256]
          have hgtLo : -B ≤ intPrefix (env ()) K := by
            have hnot := (cmpPrefix_nonpos_iff hx hb_sign.neg K).not.mp hcLo
            rw [intPrefix_neg_eq, hb_pref] at hnot
            omega
          rw [min_eq_right hltHi, max_eq_right hgtLo, h16, ediv_two_pow_emod_eq]

private theorem shiftClipCutoff_le {d s κ : ℕ} {v : ℤ} (hd : 1 ≤ d)
    (hv : v ≤ ((κ * d : ℕ) : ℤ)) (hneg : ¬ ((s : ℤ) + v + 4 < 0)) :
    ((s : ℤ) + v + 4).toNat ≤ s + (κ + 4) * d := by
  set K := ((s : ℤ) + v + 4).toNat
  have hnonneg : 0 ≤ (s : ℤ) + v + 4 := not_lt.mp hneg
  have hKZ : (K : ℤ) = (s : ℤ) + v + 4 := Int.toNat_of_nonneg hnonneg
  have h4d : (4 : ℤ) ≤ ((4 * d : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_mul_of_pos_right 4 hd
  have hboundZ : (K : ℤ) ≤ ((s + (κ + 4) * d : ℕ) : ℤ) := by
    rw [Nat.add_mul]
    push_cast at hv h4d ⊢
    linarith
  exact_mod_cast hboundZ

/-- **Lemma 10.7 (certified shift-and-clip primitive)** [OpenAI2026LogSpace, Lemma 10.7]:
computes `max (-1) (min 1 (2 ^ v * streamVal x))` for any integer shift `v ≤ κ * d` with
top-down comparator slope `coeffB = 6` and `O((κ + 1) * d)` slack overhead. -/
@[expose] noncomputable def shiftClipPrim {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (v : ℤ) (κ : ℕ) (hv : v ≤ ((κ * d : ℕ) : ℤ)) :
    UniformStreamRecipe Unit Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => IsSignedStream (env ()))
    (fun val _ => shiftClipVal v (val ()))
    (fun env _ => shiftClipApprox v (env ()))
    (shiftClipResProg v) (6 * κ + 44) 6 (κ + 4) (6 * κ + 44)
    (fun _ => abs_shiftClipVal_le_one v _)
    (fun hV => shiftClipApprox_isScaledApprox v hV)
    (fun hV s => eval_shiftClipResProg v s hV _)
    (fun s env sEnv _ hev => by
      unfold shiftClipResProg at hev
      by_cases hneg : (s : ℤ) + v + 4 < 0
      · simp only [hneg, ↓reduceIte] at hev
        nomatch hev
      · simp only [hneg, ↓reduceIte] at hev
        set K := ((s : ℤ) + v + 4).toNat
        have hK_le : K ≤ s + (κ + 4) * d := shiftClipCutoff_le hd hv hneg
        have hc_split : (κ + 4) * d = κ * d + 4 * d := Nat.add_mul κ 4 d
        have ha_split : (6 * κ + 44) * d = 6 * (κ * d) + 44 * d := by ring
        have h44 : 44 ≤ 44 * d := Nat.le_mul_of_pos_right 44 hd
        have hL_bound : ∀ (j L : ℕ), j ≤ K → L ≤ 16 + 6 * (K - j) →
            AllowanceBound (Struct := Struct) d (6 * κ + 44) 6 (κ + 4) s (.digit () j L) :=
          fun j L hj hL => by
          refine ⟨hj.trans hK_le, ?_⟩
          change (L : ℤ) ≤ (((6 * κ + 44) * d : ℕ) : ℤ) + (6 : ℤ) * ((s : ℤ) - (j : ℤ))
          omega
        by_cases hsmall : K + 4 ≤ s + 4
        · simp only [hsmall, ↓reduceIte, QueryProg.activeQueries_map] at hev
          obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg () 8 K env sEnv hev
          exact hL_bound j 16 hj (by omega)
        · simp only [hsmall, ↓reduceIte, QueryProg.activeQueries_bindOverhead,
            List.mem_append, List.mem_map] at hev
          rcases hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
          · obtain ⟨j, L, hj, hL, rfl⟩ := mem_activeQueries_cmpWithConstProg () _ K env sEnv hev₀
            exact hL_bound j (6 + L) hj (by omega)
          · by_cases hcHi : 0 ≤ (cmpWithConstProg () (clipBoundStream (s + 4) K) K).eval env sEnv
            · simp only [hcHi, ↓reduceIte] at hev₁
              nomatch hev₁
            · simp only [hcHi, ↓reduceIte, QueryProg.activeQueries_bindOverhead,
                List.mem_append, List.mem_map] at hev₁
              rcases hev₁ with ⟨ev₀, hev₀, rfl⟩ | hev₂
              · obtain ⟨j, L, hj, hL, rfl⟩ :=
                  mem_activeQueries_cmpWithConstProg () _ K env sEnv hev₀
                exact hL_bound j (6 + L) hj (by omega)
              · by_cases hcLo :
                    (cmpWithConstProg () (fun j => -clipBoundStream (s + 4) K j) K).eval env sEnv ≤
                      0
                · simp only [hcLo, ↓reduceIte] at hev₂
                  nomatch hev₂
                · simp only [hcLo, ↓reduceIte, QueryProg.activeQueries_map] at hev₂
                  obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg () 8 K env sEnv hev₂
                  exact hL_bound j 16 hj (by omega))
    (fun s env sEnv => by
      have hd_pos : 1 ≤ d + s := by omega
      unfold shiftClipResProg
      by_cases hneg : (s : ℤ) + v + 4 < 0
      · simp only [hneg, ↓reduceIte, QueryProg.maxIntrinsicBits, Nat.max_zero]
        exact (by omega : 8 ≤ 6 * κ + 44).trans (Nat.le_mul_of_pos_right _ hd_pos)
      · simp only [hneg, ↓reduceIte]
        set K := ((s : ℤ) + v + 4).toNat
        have hK_le : K ≤ s + (κ + 4) * d := shiftClipCutoff_le hd hv hneg
        have hc_split : (κ + 4) * d = κ * d + 4 * d := Nat.add_mul κ 4 d
        have h44 : 44 ≤ 44 * d := Nat.le_mul_of_pos_right 44 hd
        have hInt_split : (6 * κ + 44) * (d + s) =
            6 * (κ * d) + 44 * d + 6 * (κ * s) + 44 * s := by ring
        have hK_int : 6 * K + 20 ≤ (6 * κ + 44) * (d + s) := by omega
        by_cases hsmall : K + 4 ≤ s + 4
        · simp only [hsmall, ↓reduceIte, QueryProg.maxIntrinsicBits_map]
          have hw := maxIntrinsicBits_windowPrefixModProg_le () 8 K env sEnv
          exact hw.trans (by omega)
        · simp only [hsmall, ↓reduceIte]
          refine ((QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans
            (max_le ?_ ?_)).trans hK_int
          · have hc := maxIntrinsicBits_cmpWithConstProg_le () (clipBoundStream (s + 4) K) K
              env sEnv
            omega
          · by_cases hcHi : 0 ≤ (cmpWithConstProg () (clipBoundStream (s + 4) K) K).eval env sEnv
            · simp only [hcHi, ↓reduceIte, QueryProg.maxIntrinsicBits, Nat.max_zero]
              omega
            · simp only [hcHi, ↓reduceIte]
              refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
              · have hc := maxIntrinsicBits_cmpWithConstProg_le ()
                  (fun j => -clipBoundStream (s + 4) K j) K env sEnv
                omega
              · by_cases hcLo :
                    (cmpWithConstProg () (fun j => -clipBoundStream (s + 4) K j) K).eval env sEnv ≤
                      0
                · simp only [hcLo, ↓reduceIte, QueryProg.maxIntrinsicBits, Nat.max_zero]
                  omega
                · simp only [hcLo, ↓reduceIte, QueryProg.maxIntrinsicBits_map]
                  have hw := maxIntrinsicBits_windowPrefixModProg_le () 8 K env sEnv
                  omega)

/-- Apply exact shift-and-clip `max (-1) (min 1 (2 ^ v * R))` (`v ≤ κ * d`) to a
`UniformStreamRecipe`. -/
@[expose] noncomputable def UniformStreamRecipe.shiftClip {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) (v : ℤ) (κ : ℕ)
    (hv : v ≤ ((κ * R.slack : ℕ) : ℤ)) : UniformStreamRecipe Op Struct :=
  let raw := (shiftClipPrim R.slack R.slack_pos v κ hv).comp (fun _ => R)
    R.coeffA R.coeffB R.coeffC R.intrinsicCoeff
    (fun _ => rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
  raw.weakenValid R.ValidEnv (fun h => ⟨fun _ => h, R.emits_signed h⟩)

/-- Binary-tree child index embedding `Fin 2 × Fin (2 ^ r) → Fin (2 ^ (r + 1))`. -/
@[expose] def splitFinPow {r : ℕ} (b : Fin 2) (idx : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨b.val * 2 ^ r + idx.val, by
    have hi := idx.isLt
    have hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
    rcases b with ⟨_ | _ | b, hb⟩
    · simp only [Nat.zero_mul, Nat.zero_add, hp]
      omega
    · simp only [hp]
      omega
    · omega⟩

private theorem sum_fin_two_pow_succ {r : ℕ} (g : Fin (2 ^ (r + 1)) → ℝ) :
    ∑ i : Fin (2 ^ (r + 1)), g i =
      (∑ idx : Fin (2 ^ r), g (splitFinPow 0 idx)) +
        (∑ idx : Fin (2 ^ r), g (splitFinPow 1 idx)) := by
  let extG : ℕ → ℝ := fun k => if hk : k < 2 ^ (r + 1) then g ⟨k, hk⟩ else 0
  have hlhs : ∑ i : Fin (2 ^ (r + 1)), g i = ∑ k ∈ range (2 ^ (r + 1)), extG k := by
    rw [← Fin.sum_univ_eq_sum_range extG (2 ^ (r + 1))]
    refine sum_congr rfl fun i _ => ?_
    simp [extG, i.isLt]
  have hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
  rw [hlhs, hp, sum_range_add]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range extG (2 ^ r)]
    refine sum_congr rfl fun idx _ => ?_
    have hlt : idx.val < 2 ^ (r + 1) := by have := idx.isLt; omega
    simp [extG, hlt, splitFinPow]
  · rw [← Fin.sum_univ_eq_sum_range (fun k => extG (2 ^ r + k)) (2 ^ r)]
    refine sum_congr rfl fun idx _ => ?_
    have hlt : 2 ^ r + idx.val < 2 ^ (r + 1) := by have := idx.isLt; omega
    simp [extG, hlt, splitFinPow]

/-- Direct balanced binary-tree average digit program over `2 ^ r` operand streams
[OpenAI2026LogSpace, Lemma 10.7]. -/
@[expose] def balancedAvgDigitProg {Struct : Type v} :
    (r : ℕ) → ℕ → QueryProg (Fin (2 ^ r)) Struct ℤ
  | 0, t => .queryDigit ⟨0, by decide⟩ t 4 .ret
  | r + 1, t =>
      (diffDigitProg pairAvgResProg t).substDigits 4 fun b u =>
        (balancedAvgDigitProg r u).reindexOp (splitFinPow b)

theorem balancedAvgDigitProg_emits {Struct : Type v} (r : ℕ)
    {env : Fin (2 ^ r) → ℕ → ℤ} (hEnv : ∀ i, IsNormSignedStream (env i))
    (sEnv : Struct → Bool) :
    IsSignedStream (fun t => (balancedAvgDigitProg r t).eval env sEnv) ∧
      streamVal (fun t => (balancedAvgDigitProg r t).eval env sEnv) =
        (∑ i : Fin (2 ^ r), streamVal (env i)) / (2 : ℝ) ^ r ∧
      |(∑ i : Fin (2 ^ r), streamVal (env i)) / (2 : ℝ) ^ r| ≤ 1 := by
  induction r with
  | zero =>
    have h0 := hEnv ⟨0, by decide⟩
    have hsum : (∑ i : Fin (2 ^ 0), streamVal (env i)) / (2 : ℝ) ^ 0 =
        streamVal (env ⟨0, by decide⟩) := by
      simp
    rw [hsum]
    exact ⟨h0.1, rfl, h0.2⟩
  | succ r ih =>
    obtain ⟨hs0_raw, hval0, hbnd0⟩ :=
      ih (env := fun idx => env (splitFinPow 0 idx)) (fun idx => hEnv _)
    obtain ⟨hs1_raw, hval1, hbnd1⟩ :=
      ih (env := fun idx => env (splitFinPow 1 idx)) (fun idx => hEnv _)
    set s₀ : ℕ → ℤ := fun u =>
      (balancedAvgDigitProg r u).eval (fun idx => env (splitFinPow 0 idx)) sEnv
    set s₁ : ℕ → ℤ := fun u =>
      (balancedAvgDigitProg r u).eval (fun idx => env (splitFinPow 1 idx)) sEnv
    set cEnv : Fin 2 → ℕ → ℤ := fun b u =>
      ((balancedAvgDigitProg r u).reindexOp (splitFinPow b)).eval env sEnv
    have hc0 : cEnv 0 = s₀ := by
      ext u
      exact QueryProg.eval_reindexOp _ _ _ _
    have hc1 : cEnv 1 = s₁ := by
      ext u
      exact QueryProg.eval_reindexOp _ _ _ _
    have htarget_eq : (∑ i : Fin (2 ^ (r + 1)), streamVal (env i)) / (2 : ℝ) ^ (r + 1) =
        (streamVal (cEnv 0) + streamVal (cEnv 1)) / 2 := by
      rw [hc0, hc1, hval0, hval1, sum_fin_two_pow_succ]
      rw [pow_succ]
      ring
    have hbound : |(streamVal (cEnv 0) + streamVal (cEnv 1)) / 2| ≤ 1 := by
      rw [hc0, hc1, hval0, hval1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri := abs_add_le
        ((∑ idx : Fin (2 ^ r), streamVal (env (splitFinPow 0 idx))) / (2 : ℝ) ^ r)
        ((∑ idx : Fin (2 ^ r), streamVal (env (splitFinPow 1 idx))) / (2 : ℝ) ^ r)
      linarith [hbnd0, hbnd1]
    have happrox : IsScaledApprox ((streamVal (cEnv 0) + streamVal (cEnv 1)) / 2)
        (pairAvgApprox (cEnv 0) (cEnv 1)) := by
      have hs0 : IsSignedStream (cEnv 0) := hc0 ▸ hs0_raw
      have hs1 : IsSignedStream (cEnv 1) := hc1 ▸ hs1_raw
      exact pairAvgApprox_isScaledApprox hs0 hs1
    have heval : (fun t => (balancedAvgDigitProg (r + 1) t).eval env sEnv) =
        diffDigit (pairAvgApprox (cEnv 0) (cEnv 1)) := by
      ext t
      simp only [balancedAvgDigitProg, QueryProg.eval_substDigits]
      exact eval_diffDigitProg pairAvgResProg (pairAvgApprox (cEnv 0) (cEnv 1)) hbound happrox
        (fun s => eval_pairAvgResProg s cEnv sEnv) t
    rw [heval, htarget_eq]
    exact ⟨diffDigit_isSignedStream hbound happrox, streamVal_diffDigit hbound happrox, hbound⟩

private theorem mem_activeQueries_diffDigit_pairAvg {Struct : Type v} (t : ℕ)
    (cEnv : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (diffDigitProg pairAvgResProg t).activeQueries cEnv sEnv) :
    ∃ b u w, u ≤ t + 4 ∧ w ≤ 46 ∧ ev = .digit b u w := by
  cases t with
  | zero =>
    simp only [diffDigitProg, QueryProg.activeQueries_map] at hev
    obtain ⟨b, u, w, hu, hw, rfl⟩ := mem_activeQueries_pairAvgResProg 0 cEnv sEnv hev
    exact ⟨b, u, w, hu, hw.trans (by decide), rfl⟩
  | succ t =>
    simp only [diffDigitProg, QueryProg.activeQueries_bindOverhead, QueryProg.activeQueries,
      List.append_nil, List.mem_append, List.mem_map] at hev
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | ⟨ev₁, hev₁, rfl⟩
    · obtain ⟨b, u, w, hu, hw, rfl⟩ := mem_activeQueries_pairAvgResProg (t + 1) cEnv sEnv hev₀
      exact ⟨b, u, 4 + w, hu, by omega, rfl⟩
    · obtain ⟨b, u, w, hu, hw, rfl⟩ := mem_activeQueries_pairAvgResProg t cEnv sEnv hev₁
      exact ⟨b, u, 8 + w, by omega, by omega, rfl⟩

theorem mem_activeQueries_balancedAvgDigitProg {Struct : Type v} (r t : ℕ)
    (env : Fin (2 ^ r) → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin (2 ^ r)) Struct}
    (hev : ev ∈ (balancedAvgDigitProg r t).activeQueries env sEnv) :
    ∃ op j L, j ≤ t + 4 * r ∧ L ≤ 4 + 50 * r ∧ ev = .digit op j L := by
  induction r generalizing t with
  | zero =>
    simp only [balancedAvgDigitProg, QueryProg.activeQueries, List.mem_cons] at hev
    rcases hev with rfl | hev
    · exact ⟨⟨0, by decide⟩, t, 4, by omega, by omega, rfl⟩
    · nomatch hev
  | succ r ih =>
    simp only [balancedAvgDigitProg] at hev
    rcases QueryProg.mem_activeQueries_substDigits 4 _ _ env sEnv hev with
      ⟨_, _, hs, _⟩ | ⟨b, u, w, evC, hd, hevC, rfl⟩
    · obtain ⟨_, _, _, _, _, hEq⟩ := mem_activeQueries_diffDigit_pairAvg t _ sEnv hs
      nomatch hEq
    · obtain ⟨_, _, _, hu, hw, hEq⟩ := mem_activeQueries_diffDigit_pairAvg t _ sEnv hd
      injection hEq with _ _ hw_eq
      subst hw_eq
      rcases QueryProg.mem_activeQueries_reindexOp (splitFinPow b) _ env sEnv hevC with
        ⟨_, _, hsC, _⟩ | ⟨idx, j, l, hdC, rfl⟩
      · obtain ⟨_, _, _, _, _, hEqC⟩ := ih u _ hsC
        nomatch hEqC
      · obtain ⟨_, j', l', hj, hl, hEqC⟩ := ih u _ hdC
        injection hEqC with _ hj_eq hl_eq
        subst hj_eq hl_eq
        exact ⟨splitFinPow b idx, j, w + 4 + l, by omega, by omega, rfl⟩

theorem maxIntrinsicBits_balancedAvgDigitProg_le {Struct : Type v} (r t : ℕ)
    (env : Fin (2 ^ r) → ℕ → ℤ) (sEnv : Struct → Bool) :
    (balancedAvgDigitProg r t).maxIntrinsicBits env sEnv ≤ t + 54 + 54 * r := by
  induction r generalizing t with
  | zero =>
    simp only [balancedAvgDigitProg, QueryProg.maxIntrinsicBits, Nat.max_zero]
    omega
  | succ r ih =>
    simp only [balancedAvgDigitProg]
    let cEnv : Fin 2 → ℕ → ℤ := fun op u =>
      ((balancedAvgDigitProg r u).reindexOp (splitFinPow op)).eval env sEnv
    apply QueryProg.maxIntrinsicBits_substDigits_le 4 _ _ env sEnv
    · cases t with
      | zero =>
        simp only [diffDigitProg, QueryProg.maxIntrinsicBits_map]
        exact (maxIntrinsicBits_pairAvgResProg_le 0 cEnv sEnv).trans (by omega)
      | succ t =>
        simp only [diffDigitProg]
        refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
        · have h1 := maxIntrinsicBits_pairAvgResProg_le (t + 1) cEnv sEnv
          dsimp only [cEnv] at h1
          omega
        · refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
          · have h0 := maxIntrinsicBits_pairAvgResProg_le t cEnv sEnv
            dsimp only [cEnv] at h0
            omega
          · simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
            omega
    · intro b u w hd
      obtain ⟨_, u', _, hu, hw, hEq⟩ := mem_activeQueries_diffDigit_pairAvg t _ sEnv hd
      injection hEq with _ hu_eq hw_eq
      subst hu_eq hw_eq
      rw [QueryProg.maxIntrinsicBits_reindexOp]
      have hch := ih u (fun idx => env (splitFinPow b idx))
      omega

/-- **Lemma 10.7 (certified balanced binary-tree average)** [OpenAI2026LogSpace, Lemma 10.7]:
averages `2 ^ r` normalized streams (`r ≤ κ * d`) in a single stage with `coeffB = 0`, clock
overshoot `4 * r ≤ (4 * κ) * d`, and `O((κ + 1) * d)` retained/intrinsic bits. -/
@[expose] noncomputable def balancedAvgPrim {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (r κ : ℕ) (hr : r ≤ κ * d) :
    UniformStreamRecipe (Fin (2 ^ r)) Struct where
  slack := d
  slack_pos := hd
  ValidEnv env _ := ∀ i, IsNormSignedStream (env i)
  targetVal val _ := (∑ i : Fin (2 ^ r), val i) / (2 : ℝ) ^ r
  digitProg := balancedAvgDigitProg r
  coeffA := 4 + 50 * κ
  coeffB := 0
  coeffC := 4 * κ
  intrinsicCoeff := 54 + 54 * κ
  abs_targetVal_le_one {env sEnv} hV := by
    obtain ⟨_, _, hbnd⟩ := balancedAvgDigitProg_emits r hV sEnv
    exact hbnd
  emits_signed {env sEnv} hV := (balancedAvgDigitProg_emits r hV sEnv).1
  emits_exact {env sEnv} hV := by
    obtain ⟨_, hexact, _⟩ := balancedAvgDigitProg_emits r hV sEnv
    exact hexact
  allowance t env sEnv _ hev := by
    obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_balancedAvgDigitProg r t env sEnv hev
    refine ⟨?_, ?_⟩
    · calc j ≤ t + 4 * r := hj
        _ ≤ t + 4 * (κ * d) := Nat.add_le_add_left (Nat.mul_le_mul_left 4 hr) t
        _ = t + (4 * κ) * d := by rw [Nat.mul_assoc]
    · have h4d : 4 ≤ 4 * d := Nat.le_mul_of_pos_right 4 hd
      have hLn : L ≤ (4 + 50 * κ) * d := by
        calc L ≤ 4 + 50 * r := hL
          _ ≤ 4 * d + 50 * (κ * d) := Nat.add_le_add h4d (Nat.mul_le_mul_left 50 hr)
          _ = (4 + 50 * κ) * d := by ring
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact_mod_cast hLn
  intrinsic_bound t env sEnv := by
    have h1 := maxIntrinsicBits_balancedAvgDigitProg_le r t env sEnv
    have h54 : 54 ≤ 54 * d := Nat.le_mul_of_pos_right 54 hd
    have h54r : 54 * r ≤ 54 * (κ * d) := Nat.mul_le_mul_left 54 hr
    have ht : t ≤ (54 + 54 * κ) * t := Nat.le_mul_of_pos_left t (by omega)
    have hexp : (54 + 54 * κ) * (d + t) = 54 * d + 54 * (κ * d) + (54 + 54 * κ) * t := by ring
    omega

/-- Compose `2 ^ r` (`r ≤ κ * d`) child `UniformStreamRecipe`s with `balancedAvgPrim` in a single
`O(1)`-depth stage. -/
@[expose] noncomputable def balancedAvgRecipe {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (r κ : ℕ) (hr : r ≤ κ * d)
    (children : Fin (2 ^ r) → UniformStreamRecipe Op Struct)
    (cA cB cC cInt : ℕ)
    (hSlack : ∀ i, (children i).slack = d)
    (hA : ∀ i, (children i).coeffA ≤ cA)
    (hB : ∀ i, (children i).coeffB ≤ cB)
    (hC : ∀ i, (children i).coeffC ≤ cC)
    (hInt : ∀ i, (children i).intrinsicCoeff ≤ cInt) :
    UniformStreamRecipe Op Struct :=
  let raw := (balancedAvgPrim d hd r κ hr).comp children cA cB cC cInt hSlack hA hB hC hInt
  raw.weakenValid (fun env sEnv => ∀ i, (children i).ValidEnv env sEnv)
    (fun hV => ⟨hV, fun i => ⟨(children i).emits_signed (hV i), by
      rw [(children i).emits_exact (hV i)]
      exact (children i).abs_targetVal_le_one (hV i)⟩⟩)

end ShiftClipAndBalancedAverage

section MultiplicationRecipe

/-- Decidable membership predicate for `(i, j) ∈ bandWindowPairs s 4 k`. -/
@[expose] def inBandWindow (s k i j : ℕ) : Prop :=
  bandStart k ≤ min i j ∧ min i j < bandEnd k ∧ i + j ≤ s + bandMargin k ∧ s < i + j + 4

instance instDecidableInBandWindow (s k i j : ℕ) : Decidable (inBandWindow s k i j) := by
  unfold inBandWindow
  infer_instance

private theorem mem_bandPairs_of_inBandWindow {s k i j : ℕ} (h : inBandWindow s k i j) :
    (i, j) ∈ bandPairs s k := by
  obtain ⟨hlo, hhi, hsum, _⟩ := h
  unfold bandPairs
  rw [mem_filter, mem_product, mem_range, mem_range]
  exact ⟨⟨by omega, by omega⟩, hlo, hhi, hsum⟩

private theorem bandStart_le_of_lt_maxBand {s k : ℕ} (hk : k < maxBand s) :
    bandStart k ≤ s + mulBaseMargin := by
  cases k with
  | zero => simp
  | succ m =>
    unfold maxBand at hk
    have hm : m ≤ Nat.log 2 (s + mulBaseMargin) := by omega
    unfold bandStart
    exact (Nat.pow_le_pow_right (by decide) hm).trans
      (Nat.pow_log_le_self 2 (by unfold mulBaseMargin; omega))

private theorem bandWindowSum_eq_double_sum (x y : ℕ → ℤ) (s k : ℕ) :
    bandWindowSum x y s 4 k =
      ∑ i ∈ range (s + bandMargin k + 1),
        ∑ j ∈ range (s + bandMargin k + 1),
          if inBandWindow s k i j then
            x i * y j * (2 : ℤ) ^ (s + bandMargin k - (i + j))
          else 0 := by
  unfold bandWindowSum bandWindowPairs bandPairs
  rw [Finset.filter_filter]
  have hpred : (range (s + bandMargin k + 1) ×ˢ range (s + bandMargin k + 1)).filter
      (fun p => (bandStart k ≤ min p.1 p.2 ∧ min p.1 p.2 < bandEnd k ∧
        p.1 + p.2 ≤ s + bandMargin k) ∧ s < p.1 + p.2 + 4) =
      (range (s + bandMargin k + 1) ×ˢ range (s + bandMargin k + 1)).filter
        (fun p => inBandWindow s k p.1 p.2) := by
    refine Finset.filter_congr fun p _ => ?_
    simp only [inBandWindow, and_assoc]
  rw [hpred, sum_filter, sum_product]

/-- Inner column loop accumulating band `k` terms modulo `2 ^ (4 + bandMargin k)`. -/
@[expose] def bandScanJ {Struct : Type v} (s k i idxJ : ℕ) :
    ℕ → ℤ → QueryProg (Fin 2) Struct ℤ
  | 0, acc => .scratchStep (4 + bandMargin k + s + 24) (.ret (acc % (2 : ℤ) ^ (4 + bandMargin k)))
  | remJ + 1, acc =>
      let M := (2 : ℤ) ^ (4 + bandMargin k)
      let W := 4 + bandMargin k + 2 * k + 12
      if inBandWindow s k i idxJ then
        .queryDigit 0 i W fun d₀ =>
          .queryDigit 1 idxJ (W + 4) fun d₁ =>
            let term := d₀ * d₁ * (2 : ℤ) ^ (s + bandMargin k - (i + idxJ))
            bandScanJ s k i (idxJ + 1) remJ ((acc + term) % M)
      else
        bandScanJ s k i (idxJ + 1) remJ acc

/-- Row loop over `i ∈ range (s + bandMargin k + 1)` for band `k`. -/
@[expose] def bandScanI {Struct : Type v} (s k idxI : ℕ) :
    ℕ → ℤ → QueryProg (Fin 2) Struct ℤ
  | 0, acc => .scratchStep (4 + bandMargin k + s + 24) (.ret (acc % (2 : ℤ) ^ (4 + bandMargin k)))
  | remI + 1, acc =>
      (bandScanJ s k idxI 0 (s + bandMargin k + 1) acc).bindOverhead 0 fun acc' =>
        bandScanI s k (idxI + 1) remI acc'

/-- Outer downward band fold from `maxBand s - 1` down to `0` (`step = 0 .. maxBand s`). -/
@[expose] def bandOuterAux {Struct : Type v} (s step : ℕ) :
    ℕ → ℤ → QueryProg (Fin 2) Struct ℤ
  | 0, prevFold => .scratchStep 24 (.ret (prevFold / (2 : ℤ) ^ mulBaseMargin))
  | rem + 1, prevFold =>
      let k := maxBand s - (step + 1)
      let shift := bandMargin (k + 1) - bandMargin k
      let M := (2 : ℤ) ^ (4 + bandMargin k)
      let initAcc := (prevFold / (2 : ℤ) ^ shift) % M
      (bandScanI s k 0 (s + bandMargin k + 1) initAcc).bindOverhead 0 fun nextFold =>
        bandOuterAux s (step + 1) rem nextFold

/-- Windowed mod-16 product residue program [OpenAI2026LogSpace, Lemma 10.4]. -/
@[expose] def mulResProg {Struct : Type v} (s : ℕ) : QueryProg (Fin 2) Struct ℤ :=
  bandOuterAux s 0 (maxBand s) 0

private def rowSumTerm (x y : ℕ → ℤ) (s k i j : ℕ) : ℤ :=
  if inBandWindow s k i j then x i * y j * (2 : ℤ) ^ (s + bandMargin k - (i + j)) else 0

private theorem eval_bandScanJ {Struct : Type v} (s k i idxJ remJ : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bandScanJ s k i idxJ remJ acc).eval env sEnv =
      (acc + ∑ j ∈ Ico idxJ (idxJ + remJ), rowSumTerm (env 0) (env 1) s k i j) %
        (2 : ℤ) ^ (4 + bandMargin k) := by
  set M := (2 : ℤ) ^ (4 + bandMargin k)
  induction remJ generalizing idxJ acc with
  | zero =>
    simp [bandScanJ, QueryProg.eval, M]
  | succ remJ ih =>
    have hsplit : Ico idxJ (idxJ + (remJ + 1)) =
        insert idxJ (Ico (idxJ + 1) (idxJ + 1 + remJ)) := by
      ext j
      simp only [mem_Ico, mem_insert]
      omega
    have hnot : idxJ ∉ Ico (idxJ + 1) (idxJ + 1 + remJ) := by simp
    unfold bandScanJ
    by_cases hwin : inBandWindow s k i idxJ
    · simp only [hwin, ↓reduceIte, QueryProg.eval]
      rw [ih, hsplit, sum_insert hnot]
      simp only [rowSumTerm, hwin, ↓reduceIte]
      rw [← add_assoc, Int.add_emod (((acc + _) % M)), Int.emod_emod, ← Int.add_emod]
    · simp only [hwin, ↓reduceIte]
      rw [ih, hsplit, sum_insert hnot]
      simp [rowSumTerm, hwin]

private theorem eval_bandScanI {Struct : Type v} (s k idxI remI : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bandScanI s k idxI remI acc).eval env sEnv =
      (acc + ∑ i ∈ Ico idxI (idxI + remI),
          ∑ j ∈ range (s + bandMargin k + 1), rowSumTerm (env 0) (env 1) s k i j) %
        (2 : ℤ) ^ (4 + bandMargin k) := by
  set M := (2 : ℤ) ^ (4 + bandMargin k)
  set N := s + bandMargin k + 1
  induction remI generalizing idxI acc with
  | zero =>
    simp [bandScanI, QueryProg.eval, M]
  | succ remI ih =>
    have hsplit : Ico idxI (idxI + (remI + 1)) =
        insert idxI (Ico (idxI + 1) (idxI + 1 + remI)) := by
      ext i
      simp only [mem_Ico, mem_insert]
      omega
    have hnot : idxI ∉ Ico (idxI + 1) (idxI + 1 + remI) := by simp
    simp only [bandScanI, QueryProg.eval_bindOverhead, eval_bandScanJ]
    rw [Nat.zero_add, ← Finset.range_eq_Ico, ih, hsplit, sum_insert hnot]
    rw [← add_assoc, Int.add_emod (((acc + _) % M)), Int.emod_emod, ← Int.add_emod]

theorem eval_mulResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (mulResProg s).eval env sEnv = mulApprox (env 0) (env 1) s % 16 := by
  have houter : ∀ step rem, step + rem = maxBand s →
      (bandOuterAux s step rem (bandFoldMod (env 0) (env 1) s 4 step)).eval env sEnv =
        mulResidue (env 0) (env 1) s 4 := by
    intro step rem
    induction rem generalizing step with
    | zero =>
      intro hsum
      have hstep : step = maxBand s := by omega
      subst hstep
      rfl
    | succ rem ih =>
      intro hsum
      simp only [bandOuterAux, QueryProg.eval_bindOverhead, eval_bandScanI]
      rw [Nat.zero_add, ← Finset.range_eq_Ico]
      set k := maxBand s - (step + 1)
      set shift := bandMargin (k + 1) - bandMargin k
      set M := (2 : ℤ) ^ (4 + bandMargin k)
      have hws : ∑ i ∈ range (s + bandMargin k + 1),
          ∑ j ∈ range (s + bandMargin k + 1), rowSumTerm (env 0) (env 1) s k i j =
          bandWindowSum (env 0) (env 1) s 4 k :=
        (bandWindowSum_eq_double_sum (env 0) (env 1) s k).symm
      rw [hws]
      have hnext : ((bandFoldMod (env 0) (env 1) s 4 step / (2 : ℤ) ^ shift) % M +
          bandWindowSum (env 0) (env 1) s 4 k) % M =
          bandFoldMod (env 0) (env 1) s 4 (step + 1) := by
        simp only [bandFoldMod]
        rw [add_comm, Int.add_emod (bandWindowSum _ _ _ _ _), Int.emod_emod, ← Int.add_emod]
      rw [hnext]
      exact ih (step + 1) (by omega)
  unfold mulResProg
  have h0 : (0 : ℤ) = bandFoldMod (env 0) (env 1) s 4 0 := rfl
  conv_lhs => rw [h0]
  rw [houter 0 (maxBand s) (Nat.zero_add _), mulResidue_eq_mulApprox_emod]
  rfl

private theorem mem_activeQueries_bandScanJ {Struct : Type v} (s k i idxJ remJ : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (bandScanJ s k i idxJ remJ acc).activeQueries env sEnv) :
    ∃ op idx L, (∃ j, inBandWindow s k i j ∧ (idx = i ∨ idx = j)) ∧
      L ≤ 4 + bandMargin k + 2 * k + 16 ∧ ev = .digit op idx L := by
  induction remJ generalizing idxJ acc with
  | zero => nomatch hev
  | succ remJ ih =>
    unfold bandScanJ at hev
    by_cases hwin : inBandWindow s k i idxJ
    · simp only [hwin, ↓reduceIte, QueryProg.activeQueries, List.mem_cons] at hev
      rcases hev with rfl | rfl | hev
      · exact ⟨0, i, _, ⟨idxJ, hwin, Or.inl rfl⟩, by omega, rfl⟩
      · exact ⟨1, idxJ, _, ⟨idxJ, hwin, Or.inr rfl⟩, le_rfl, rfl⟩
      · exact ih (idxJ + 1) _ hev
    · simp only [hwin, ↓reduceIte] at hev
      exact ih (idxJ + 1) _ hev

private theorem mem_activeQueries_bandScanI {Struct : Type v} (s k idxI remI : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (bandScanI s k idxI remI acc).activeQueries env sEnv) :
    ∃ op idx L, (∃ i j, inBandWindow s k i j ∧ (idx = i ∨ idx = j)) ∧
      L ≤ 4 + bandMargin k + 2 * k + 16 ∧ ev = .digit op idx L := by
  induction remI generalizing idxI acc with
  | zero => nomatch hev
  | succ remI ih =>
    simp only [bandScanI, QueryProg.activeQueries_bindOverhead, List.mem_append,
      List.mem_map] at hev
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
    · obtain ⟨op, idx, L, ⟨j, hwin, hidx⟩, hL, rfl⟩ :=
        mem_activeQueries_bandScanJ s k idxI 0 _ acc env sEnv hev₀
      exact ⟨op, idx, 0 + L, ⟨idxI, j, hwin, hidx⟩, by omega, rfl⟩
    · exact ih (idxI + 1) _ hev₁

private theorem allowance_bandScanI {Struct : Type v} {d : ℕ} (hd : 1 ≤ d)
    (s k idxI remI : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev₀ : QueryEvent (Fin 2) Struct}
    (hev₀ : ev₀ ∈ (bandScanI s k idxI remI acc).activeQueries env sEnv) :
    AllowanceBound d 58 1 16 s (ev₀.addBits 0) := by
  obtain ⟨op, idx, L, ⟨i, j, hwin, hidx⟩, hL, rfl⟩ :=
    mem_activeQueries_bandScanI s k idxI remI acc env sEnv hev₀
  have hp := mem_bandPairs_of_inBandWindow hwin
  have hidx_le_pair := index_le_clock_add_baseMargin hp
  have hidx_le : idx ≤ s + 16 := by
    unfold mulBaseMargin at hidx_le_pair
    rcases hidx with rfl | rfl <;> omega
  have hdrop : 4 * idx + 3 * bandStart k ≤ 4 * (s + 16) := by
    cases k with
    | zero =>
      simp only [bandStart_zero, mul_zero, add_zero]
      omega
    | succ m =>
      have h3 := three_mul_bandStart_le_four_mul_drop hp
      unfold mulBaseMargin at h3
      rcases hidx with rfl | rfl <;> omega
  have h2k := ten_add_two_mul_le_bandMargin k
  unfold bandMargin mulBaseMargin at hL h2k
  have hL_upper : L ≤ 42 + 2 * (bandStart k / 4) := by omega
  have hdiv4 : 8 * (bandStart k / 4) ≤ 3 * bandStart k := by omega
  refine ⟨?_, ?_⟩
  · have h16d : 16 ≤ 16 * d := Nat.le_mul_of_pos_right 16 hd
    omega
  · have h58d : (58 : ℤ) ≤ ((58 * d : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_mul_of_pos_right 58 hd
    have hLZ : ((0 + L : ℕ) : ℤ) ≤ 58 + ((s : ℤ) - (idx : ℤ)) := by omega
    push_cast at hLZ ⊢
    linarith

theorem allowance_mulResProg {Struct : Type v} {d : ℕ} (hd : 1 ≤ d) (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (mulResProg s).activeQueries env sEnv) :
    AllowanceBound d 58 1 16 s ev := by
  have houter : ∀ step rem prevFold,
      ev ∈ (bandOuterAux s step rem prevFold).activeQueries env sEnv →
      AllowanceBound d 58 1 16 s ev := by
    intro step rem
    induction rem generalizing step with
    | zero => intro _ h; nomatch h
    | succ rem ih =>
      intro prevFold h
      simp only [bandOuterAux, QueryProg.activeQueries_bindOverhead, List.mem_append,
        List.mem_map] at h
      rcases h with ⟨ev₀, hev₀, rfl⟩ | h₁
      · exact allowance_bandScanI hd s (maxBand s - (step + 1)) 0 _ _ env sEnv hev₀
      · exact ih (step + 1) _ h₁
  exact houter 0 (maxBand s) 0 hev

private theorem maxIntrinsicBits_bandScanJ_le {Struct : Type v} (s k i idxJ remJ : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bandScanJ s k i idxJ remJ acc).maxIntrinsicBits env sEnv ≤
      2 * bandMargin k + s + 28 := by
  have h2k := ten_add_two_mul_le_bandMargin k
  induction remJ generalizing idxJ acc with
  | zero =>
    simp only [bandScanJ, QueryProg.maxIntrinsicBits, Nat.max_zero]
    omega
  | succ remJ ih =>
    unfold bandScanJ
    split_ifs
    · simp only [QueryProg.maxIntrinsicBits]
      exact max_le (by omega) (max_le (by omega) (ih (idxJ + 1) _))
    · exact ih (idxJ + 1) _

private theorem maxIntrinsicBits_bandScanI_le {Struct : Type v} (s k idxI remI : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bandScanI s k idxI remI acc).maxIntrinsicBits env sEnv ≤
      2 * bandMargin k + s + 28 := by
  induction remI generalizing idxI acc with
  | zero =>
    simp only [bandScanI, QueryProg.maxIntrinsicBits, Nat.max_zero]
    omega
  | succ remI ih =>
    simp only [bandScanI]
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ (ih _ _))
    rw [Nat.zero_add]
    exact maxIntrinsicBits_bandScanJ_le s k idxI 0 _ acc env sEnv

theorem maxIntrinsicBits_mulResProg_le {Struct : Type v} {d : ℕ} (hd : 1 ≤ d) (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (mulResProg s).maxIntrinsicBits env sEnv ≤ 76 * (d + s) := by
  have hpos_mb : 0 < maxBand s := by unfold maxBand; omega
  have houter : ∀ step rem prevFold, step + rem = maxBand s →
      (bandOuterAux s step rem prevFold).maxIntrinsicBits env sEnv ≤ 76 * (d + s) := by
    intro step rem
    induction rem generalizing step with
    | zero =>
      intro _ _
      simp only [bandOuterAux, QueryProg.maxIntrinsicBits, Nat.max_zero]
      omega
    | succ rem ih =>
      intro prevFold hsum
      simp only [bandOuterAux]
      refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
      · rw [Nat.zero_add]
        set k := maxBand s - (step + 1)
        have hk_lt : k < maxBand s := by omega
        have hbs := bandStart_le_of_lt_maxBand hk_lt
        unfold mulBaseMargin at hbs
        have hbm : bandMargin k ≤ 16 + (s + 16) / 4 := by
          unfold bandMargin mulBaseMargin
          exact Nat.add_le_add_left (Nat.div_le_div_right hbs) 16
        have hscan := maxIntrinsicBits_bandScanI_le s k 0 (s + bandMargin k + 1)
          ((prevFold / (2 : ℤ) ^ (bandMargin (k + 1) - bandMargin k)) %
            (2 : ℤ) ^ (4 + bandMargin k)) env sEnv
        omega
      · exact ih (step + 1) _ (by omega)
  exact houter 0 (maxBand s) 0 (Nat.zero_add _)

/-- **Lemma 10.4 (certified minimum-index band multiplication primitive)**
[OpenAI2026LogSpace, Lemma 10.4]. -/
@[expose] noncomputable def mulPrim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe (Fin 2) Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ i, IsNormSignedStream (env i))
    (fun val _ => val 0 * val 1)
    (fun env _ => mulApprox (env 0) (env 1))
    mulResProg 58 1 16 76
    (fun hV => by
      rw [abs_mul]
      calc |streamVal _| * |streamVal _|
          ≤ 1 * 1 := mul_le_mul (hV 0).2 (hV 1).2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
    (fun hV => mulApprox_isScaledApprox (hV 0).1 (hV 1).1)
    (fun _ s => eval_mulResProg s _ _)
    (fun s env sEnv _ hev => allowance_mulResProg hd s env sEnv hev)
    (fun s env sEnv => maxIntrinsicBits_mulResProg_le hd s env sEnv)

/-- Compose two `UniformStreamRecipe`s with exact multiplication `R₁ * R₂`. -/
@[expose] noncomputable def UniformStreamRecipe.mul {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (hSlack : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  (composeBinPrim (mulPrim R₁.slack R₁.slack_pos) (fun _ _ h => h) R₁ R₂ rfl hSlack).congrTarget
    (fun val sEnv => R₁.targetVal val sEnv * R₂.targetVal val sEnv)
    (fun _ => rfl)

end MultiplicationRecipe

section ReciprocalRecipe

/-- Tail-recursive early-word integer prefix builder charging `cntBits + idx + 8` retained bits at
query `idx` (`cntBits` bits for the bounded place counter `idx ≤ K` plus `idx + 8` bits for the
growing prefix accumulator). -/
@[expose] def intPrefixAux {Op : Type u} {Struct : Type v} (op : Op) (cntBits idx : ℕ) :
    ℕ → ℤ → QueryProg Op Struct ℤ
  | 0, acc => .scratchStep (cntBits + idx + 8) (.ret acc)
  | rem + 1, acc =>
      .queryDigit op idx (cntBits + idx + 8) fun d =>
        intPrefixAux op cntBits (idx + 1) rem (2 * acc + d)

/-- Query program computing `intPrefix (env op) K` while retaining at most `2 * K + 8` bits
(including the place counter up to `K`). -/
@[expose] def intPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ) :
    QueryProg Op Struct ℤ :=
  intPrefixAux op K 0 (K + 1) 0

theorem eval_intPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (intPrefixProg op K).eval env sEnv = intPrefix (env op) K := by
  have hsnoc : ∀ cntBits idx rem acc,
      (intPrefixAux op cntBits idx (rem + 1) acc).eval env sEnv =
        2 * (intPrefixAux op cntBits idx rem acc).eval env sEnv + env op (idx + rem) := by
    intro cntBits idx rem
    induction rem generalizing idx with
    | zero => intro acc; simp [intPrefixAux, QueryProg.eval]
    | succ rem ih =>
      intro acc
      conv_lhs => rw [intPrefixAux, QueryProg.eval]
      rw [ih]
      have hidx : idx + 1 + rem = idx + (rem + 1) := by omega
      rw [hidx]
      rfl
  unfold intPrefixProg
  have hrec : ∀ n, (intPrefixAux op K 0 (n + 1) 0).eval env sEnv = intPrefix (env op) n := by
    intro n
    induction n with
    | zero => simp [intPrefixAux, QueryProg.eval, intPrefix_zero]
    | succ n ih => rw [hsnoc, Nat.zero_add, ih, intPrefix_succ]
  exact hrec K

theorem mem_activeQueries_intPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (intPrefixProg op K).activeQueries env sEnv) :
    ∃ j ≤ K, ev = .digit op j (K + j + 8) := by
  have haux : ∀ cntBits idx rem acc,
      ev ∈ (intPrefixAux op cntBits idx rem acc).activeQueries env sEnv →
      ∃ j < idx + rem, ev = .digit op j (cntBits + j + 8) := by
    intro cntBits idx rem
    induction rem generalizing idx with
    | zero => intro _ h; nomatch h
    | succ rem ih =>
      intro acc h
      simp only [intPrefixAux, QueryProg.activeQueries, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨idx, by omega, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ih (idx + 1) _ h
        exact ⟨j, by omega, rfl⟩
  obtain ⟨j, hj, rfl⟩ := haux K 0 (K + 1) 0 hev
  exact ⟨j, by omega, rfl⟩

theorem maxIntrinsicBits_intPrefixProg_le {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (intPrefixProg op K).maxIntrinsicBits env sEnv ≤ 2 * K + 9 := by
  have haux : ∀ cntBits idx rem acc,
      (intPrefixAux op cntBits idx rem acc).maxIntrinsicBits env sEnv ≤
        cntBits + idx + rem + 8 := by
    intro cntBits idx rem
    induction rem generalizing idx with
    | zero =>
      intro acc
      simp only [intPrefixAux, QueryProg.maxIntrinsicBits, Nat.max_zero]
      omega
    | succ rem ih =>
      intro acc
      simp only [intPrefixAux, QueryProg.maxIntrinsicBits]
      refine max_le (by omega) ((ih (idx + 1) _).trans (by omega))
  exact (haux K 0 (K + 1) 0).trans (by omega)

/-- Clamp a `K`-place signed-digit integer prefix into the canonical nonnegative range
`{0, ..., 2 ^ K}` [OpenAI2026LogSpace, Section 10.6]. -/
@[expose] def clipUnitPrefix (K : ℕ) (P : ℤ) : ℕ :=
  (min ((2 : ℤ) ^ K) (max 0 P)).toNat

/-- Query program computing the `{0, ..., 2 ^ K}`-clamped integer prefix of `env op` at place `K`
[OpenAI2026LogSpace, Section 10.6]. -/
@[expose] def clippedUnitPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ) :
    QueryProg Op Struct ℕ :=
  (intPrefixProg op K).map (clipUnitPrefix K)

theorem eval_clippedUnitPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (clippedUnitPrefixProg op K).eval env sEnv = clipUnitPrefix K (intPrefix (env op) K) := by
  rw [clippedUnitPrefixProg, QueryProg.eval_map, eval_intPrefixProg]

theorem clipUnitPrefix_le_two_pow (K : ℕ) (P : ℤ) : clipUnitPrefix K P ≤ 2 ^ K := by
  unfold clipUnitPrefix
  apply Int.toNat_le.mpr
  have hmin : min ((2 : ℤ) ^ K) (max 0 P) ≤ (2 : ℤ) ^ K := min_le_left _ _
  have hpow : (2 : ℤ) ^ K = ((2 ^ K : ℕ) : ℤ) := by push_cast; rfl
  omega

theorem abs_clipUnitPrefix_div_sub_streamVal_le {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (0 : ℝ) 1) (K : ℕ) :
    |(clipUnitPrefix K (intPrefix x K) : ℝ) / (2 : ℝ) ^ K - streamVal x| ≤ 6 / (2 : ℝ) ^ K := by
  set P := intPrefix x K
  set M : ℤ := min ((2 : ℤ) ^ K) (max 0 P)
  have hM0 : 0 ≤ M := le_min (by positivity) (le_max_left 0 P)
  have hcast : ((clipUnitPrefix K P : ℕ) : ℝ) = (M : ℝ) := by
    unfold clipUnitPrefix
    exact_mod_cast Int.toNat_of_nonneg hM0
  rw [hcast]
  have herr := abs_streamVal_sub_streamPrefix_le hx K
  rw [abs_sub_comm] at herr
  have h2K_pos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  refine le_trans ?_ herr
  rw [streamPrefix_eq_intPrefix_div]
  by_cases hP0 : P ≤ 0
  · have hM_eq : M = 0 := by
      dsimp only [M]
      rw [max_eq_left hP0, min_eq_right (by positivity)]
    have hp_nonpos : (P : ℝ) / (2 : ℝ) ^ K ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hP0) h2K_pos.le
    rw [hM_eq, Int.cast_zero, zero_div, abs_of_nonpos (by linarith [hx_mem.1]),
      abs_of_nonpos (by linarith [hx_mem.1])]
    linarith
  · have hP0' : 0 ≤ P := by omega
    by_cases hPK : (2 : ℤ) ^ K ≤ P
    · have hM_eq : M = (2 : ℤ) ^ K := by
        dsimp only [M]
        rw [max_eq_right hP0', min_eq_left hPK]
      have hp_ge1 : (1 : ℝ) ≤ (P : ℝ) / (2 : ℝ) ^ K := by
        rw [le_div_iff₀ h2K_pos, one_mul]
        exact_mod_cast hPK
      have hdiv1 : (((2 : ℤ) ^ K : ℤ) : ℝ) / (2 : ℝ) ^ K = 1 := by
        push_cast
        exact div_self h2K_pos.ne'
      rw [hM_eq, hdiv1, abs_of_nonneg (by linarith [hx_mem.2]),
        abs_of_nonneg (by linarith [hx_mem.2])]
      linarith
    · have hPK' : P ≤ (2 : ℤ) ^ K := by omega
      have hM_eq : M = P := by
        dsimp only [M]
        rw [max_eq_right hP0', min_eq_right hPK']
      rw [hM_eq]

/-- Fixed slack-1 inner recipe computing `(v₀ + v₁ * v₂) / 2` over virtual streams `Fin 3`. -/
@[expose] noncomputable def recipHalfVirtualRecipe {Struct : Type v} :
    UniformStreamRecipe (Fin 3) Struct :=
  let prodR := (varRecipe 1 le_rfl (1 : Fin 3)).mul (varRecipe 1 le_rfl (2 : Fin 3)) rfl
  (varRecipe 1 le_rfl (0 : Fin 3)).pairAvg prodR rfl

/-- Virtual 3-operand environment `[ratStream α, ratStream β, suffixStream x (recipCutoff s)]`. -/
@[expose] def recipVirtualEnv (x : ℕ → ℤ) (s : ℕ) (i : Fin 3) : ℕ → ℤ :=
  if i = 0 then ratStream (recipAlpha x s)
  else if i = 1 then ratStream (recipBeta x s)
  else suffixStream x (recipCutoff s)

private theorem eval_recipHalfVirtualRecipe {Struct : Type v} {x : ℕ → ℤ}
    (hx : IsSignedStream x) (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1)
    (s : ℕ) (sEnv : Struct → Bool) (u : ℕ) :
    (recipHalfVirtualRecipe.digitProg u).eval (recipVirtualEnv x s) sEnv =
      recipHalfStream x s u := by
  have hα := abs_recipAlpha_le_one hx hx_mem s
  have hβ := abs_recipBeta_le_one hx hx_mem s
  have hsuff := suffixStream_isSignedStream hx (recipCutoff s)
  have hprod : ∀ r,
      (((varRecipe 1 le_rfl (1 : Fin 3)).mul (varRecipe 1 le_rfl (2 : Fin 3)) rfl).digitProg r).eval
          (recipVirtualEnv x s) sEnv = recipProdStream x s r := by
    intro r
    change ((diffDigitProg mulResProg r).substDigits 4 _).eval (recipVirtualEnv x s) sEnv = _
    rw [QueryProg.eval_substDigits]
    set cEnvMul : Fin 2 → ℕ → ℤ := fun b =>
      if b = 0 then ratStream (recipBeta x s) else suffixStream x (recipCutoff s)
    have hchild : (fun (b : Fin 2) w =>
        ((if b = 0 then varRecipe 1 le_rfl (1 : Fin 3)
          else varRecipe 1 le_rfl (2 : Fin 3)).digitProg w).eval (recipVirtualEnv x s) sEnv) =
        cEnvMul := by
      ext b w
      rcases b with ⟨_ | _ | b, hb⟩
      · rfl
      · rfl
      · omega
    rw [hchild]
    have hbmul : |streamVal (cEnvMul 0) * streamVal (cEnvMul 1)| ≤ 1 := by
      have hc0 : cEnvMul 0 = ratStream (recipBeta x s) := rfl
      have hc1 : cEnvMul 1 = suffixStream x (recipCutoff s) := rfl
      rw [hc0, hc1, streamVal_ratStream hβ, streamVal_suffixStream hx, ← recipPrefixRat_cast,
        abs_mul]
      have hβR : |(recipBeta x s : ℝ)| ≤ 1 := by exact_mod_cast hβ
      have heR : |streamVal x - (recipPrefixRat x s : ℝ)| ≤ 1 :=
        (abs_tail_recipCutoff_le hx s).trans (by norm_num)
      calc |(recipBeta x s : ℝ)| * |streamVal x - (recipPrefixRat x s : ℝ)|
          ≤ 1 * 1 := mul_le_mul hβR heR (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hamul : IsScaledApprox (streamVal (cEnvMul 0) * streamVal (cEnvMul 1))
        (mulApprox (cEnvMul 0) (cEnvMul 1)) :=
      mulApprox_isScaledApprox (ratStream_isSignedStream hβ) hsuff
    exact eval_diffDigitProg mulResProg (mulApprox (cEnvMul 0) (cEnvMul 1)) hbmul hamul
      (fun t => eval_mulResProg t cEnvMul sEnv) r
  change ((diffDigitProg pairAvgResProg u).substDigits 4 _).eval (recipVirtualEnv x s) sEnv = _
  rw [QueryProg.eval_substDigits]
  set cEnvAvg : Fin 2 → ℕ → ℤ := fun b =>
    if b = 0 then ratStream (recipAlpha x s) else recipProdStream x s
  have hchildAvg : (fun (b : Fin 2) w =>
      ((if b = 0 then varRecipe 1 le_rfl (0 : Fin 3)
        else ((varRecipe 1 le_rfl (1 : Fin 3)).mul (varRecipe 1 le_rfl (2 : Fin 3)) rfl)).digitProg
          w).eval (recipVirtualEnv x s) sEnv) = cEnvAvg := by
    ext b w
    rcases b with ⟨_ | _ | b, hb⟩
    · rfl
    · change (((varRecipe 1 le_rfl (1 : Fin 3)).mul (varRecipe 1 le_rfl (2 : Fin 3)) rfl).digitProg
        w).eval (recipVirtualEnv x s) sEnv = recipProdStream x s w
      exact hprod w
    · omega
  rw [hchildAvg]
  have hbavg : |(streamVal (cEnvAvg 0) + streamVal (cEnvAvg 1)) / 2| ≤ 1 := by
    have ha0 : cEnvAvg 0 = ratStream (recipAlpha x s) := rfl
    have ha1 : cEnvAvg 1 = recipProdStream x s := rfl
    rw [ha0, ha1, streamVal_ratStream hα, streamVal_recipProdStream hx hx_mem s, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hαR : |(recipAlpha x s : ℝ)| ≤ 1 := by exact_mod_cast hα
    have hpR : |(recipBeta x s : ℝ) * (streamVal x - (recipPrefixRat x s : ℝ))| ≤ 1 := by
      have hβR : |(recipBeta x s : ℝ)| ≤ 1 := by exact_mod_cast hβ
      have heR : |streamVal x - (recipPrefixRat x s : ℝ)| ≤ 1 :=
        (abs_tail_recipCutoff_le hx s).trans (by norm_num)
      rw [abs_mul]
      calc |(recipBeta x s : ℝ)| * |streamVal x - (recipPrefixRat x s : ℝ)|
          ≤ 1 * 1 := mul_le_mul hβR heR (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have htri := abs_add_le (recipAlpha x s : ℝ)
      ((recipBeta x s : ℝ) * (streamVal x - (recipPrefixRat x s : ℝ)))
    linarith
  have haavg : IsScaledApprox ((streamVal (cEnvAvg 0) + streamVal (cEnvAvg 1)) / 2)
      (pairAvgApprox (cEnvAvg 0) (cEnvAvg 1)) :=
    pairAvgApprox_isScaledApprox (ratStream_isSignedStream hα)
      (recipProdStream_isSignedStream hx hx_mem s)
  exact eval_diffDigitProg pairAvgResProg (pairAvgApprox (cEnvAvg 0) (cEnvAvg 1)) hbavg haavg
    (fun t => eval_pairAvgResProg t cEnvAvg sEnv) u

private theorem recip64Approx_emod_sixteen {x : ℕ → ℤ}
    (hx : IsSignedStream x) (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (s : ℕ) :
    recip64Approx x s % 16 =
      (intPrefix (recipHalfStream x s) (s + 8) % (2 : ℤ) ^ (11 : ℕ)) / 128 := by
  set y := recipHalfStream x s
  have hy : IsSignedStream y := recipHalfStream_isSignedStream hx hx_mem s
  have hy_val : |streamVal y| ≤ 1 / 8 := by
    rw [streamVal_recipHalfStream hx hx_mem s, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmem := recipPrefixRat_mem_Icc hx hx_mem s
    have hα_le : |(recipAlpha x s : ℝ)| ≤ 1 / 12 := by
      unfold recipAlpha
      push_cast
      have hx0_pos : (0 : ℝ) < (recipPrefixRat x s : ℝ) := by linarith [hmem.1]
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [hmem.1])
    have hp_le : |(recipBeta x s : ℝ) * (streamVal x - (recipPrefixRat x s : ℝ))| ≤ 3 / 64 := by
      have hβR : |(recipBeta x s : ℝ)| ≤ 1 := by exact_mod_cast abs_recipBeta_le_one hx hx_mem s
      have heR := abs_tail_recipCutoff_le hx s
      rw [abs_mul]
      calc |(recipBeta x s : ℝ)| * |streamVal x - (recipPrefixRat x s : ℝ)|
          ≤ 1 * (3 / 64) := mul_le_mul hβR heR (abs_nonneg _) (by norm_num)
        _ = 3 / 64 := one_mul _
    have htri := abs_add_le (recipAlpha x s : ℝ)
      ((recipBeta x s : ℝ) * (streamVal x - (recipPrefixRat x s : ℝ)))
    linarith
  have hy_err := abs_streamVal_sub_streamPrefix_le (x := y) hy (s + 8)
  have hpow_ge : (256 : ℝ) ≤ (2 : ℝ) ^ (s + 8) := by
    calc (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (s + 8) := pow_le_pow_right₀ (by norm_num) (by omega)
  have herr_le : (6 : ℝ) / (2 : ℝ) ^ (s + 8) ≤ 6 / 256 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow_ge
  have hpref_le : |streamPrefix y (s + 8)| ≤ 1 / 2 := by
    have htri := abs_sub_le (streamPrefix y (s + 8)) (streamVal y) 0
    simp only [sub_zero] at htri
    rw [abs_sub_comm] at hy_err
    linarith
  have hint_le : |intPrefix y (s + 8)| ≤ (2 : ℤ) ^ (s + 7) := by
    rw [streamPrefix_eq_intPrefix_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + 8)),
      div_le_iff₀ (by positivity)] at hpref_le
    have hpow7 : (1 / 2 : ℝ) * (2 : ℝ) ^ (s + 8) = (((2 : ℤ) ^ (s + 7) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hpow7, ← Int.cast_abs] at hpref_le
    exact_mod_cast hpref_le
  obtain ⟨hlo, hhi⟩ := abs_le.mp hint_le
  unfold recip64Approx shiftClipApprox
  have hnot_neg : ¬ ((s + 3 : ℕ) : ℤ) + 1 + 4 < 0 := by omega
  simp only [hnot_neg, ↓reduceIte]
  have hK : (((s + 3 : ℕ) : ℤ) + 1 + 4).toNat = s + 8 := by omega
  have hB : (s + 3) + 4 = s + 7 := by omega
  rw [hK, hB, min_eq_right hhi, max_eq_right hlo, Int.ediv_ediv_of_nonneg (by decide)]
  have h128 : (16 : ℤ) * 8 = (2 : ℤ) ^ (7 : ℕ) := by decide
  have h16 : (16 : ℤ) = (2 : ℤ) ^ (4 : ℕ) := by decide
  have h11 : (2 : ℤ) ^ (11 : ℕ) = (2 : ℤ) ^ (4 + 7 : ℕ) := rfl
  have h7 : (2 : ℤ) ^ (7 : ℕ) = 128 := by decide
  rw [h128, h16, h11, ediv_two_pow_emod_eq, h7]

/-- Outer fixed-depth query program over the 3 virtual reciprocal streams. -/
@[expose] noncomputable def recipOuterProg {Struct : Type v} (s : ℕ) :
    QueryProg (Fin 3) Struct ℤ :=
  ((windowPrefixModProg () 11 (s + 8)).map (· / 128)).substDigits 4 fun _ u =>
    recipHalfVirtualRecipe.digitProg u

/-- Early-word / suffix child query programs realizing `recipVirtualEnv`:
forms `intPrefix (env ()) (recipCutoff s)` only on streams `0, 1` (`j ≤ recipCutoff s`) and
releases it before returning, while stream `2` (`suffixStream`) queries `env ()` directly only at
places `r > recipCutoff s` with zero retained prefix bits [OpenAI2026LogSpace, Lemma 10.5]. -/
@[expose] def recipChild {Struct : Type v} (s : ℕ) (op : Fin 3) (r : ℕ) :
    QueryProg Unit Struct ℤ :=
  if op = 0 then
    (intPrefixProg () (recipCutoff s)).bindOverhead 0 fun P =>
      let x0 : ℚ := (P : ℚ) / (2 : ℚ) ^ recipCutoff s
      .scratchStep (8 * (s + r + 8)) (.ret (ratStream (1 / (64 * x0)) r))
  else if op = 1 then
    (intPrefixProg () (recipCutoff s)).bindOverhead 0 fun P =>
      let x0 : ℚ := (P : ℚ) / (2 : ℚ) ^ recipCutoff s
      .scratchStep (8 * (s + r + 8)) (.ret (ratStream (-1 / (64 * x0 ^ 2)) r))
  else
    if r ≤ recipCutoff s then .ret 0 else .queryDigit () r 0 .ret

/-- Mod-16 residue program for `recip64Approx (env ()) s` [OpenAI2026LogSpace, Lemma 10.5]. -/
@[expose] noncomputable def recip64ResProg {Struct : Type v} (s : ℕ) :
    QueryProg Unit Struct ℤ :=
  (recipOuterProg s).substDigits 4 (recipChild s)

private theorem eval_recipChild_eq {Struct : Type v} (s : ℕ)
    (env : Unit → ℕ → ℤ) (sEnv : Struct → Bool) :
    (fun op r => (recipChild s op r).eval env sEnv) = recipVirtualEnv (env ()) s := by
  ext op r
  unfold recipChild recipVirtualEnv
  by_cases h0 : op = 0
  · simp [h0, QueryProg.eval_bindOverhead, QueryProg.eval, eval_intPrefixProg,
      recipAlpha, recipPrefixRat]
  · simp only [h0, ↓reduceIte]
    by_cases h1 : op = 1
    · simp [h1, QueryProg.eval_bindOverhead, QueryProg.eval, eval_intPrefixProg,
        recipBeta, recipPrefixRat]
    · simp only [h1, ↓reduceIte, suffixStream]
      split_ifs <;> rfl

theorem eval_recip64ResProg {Struct : Type v} (s : ℕ)
    {env : Unit → ℕ → ℤ} (hx : IsSignedStream (env ()))
    (hx_mem : streamVal (env ()) ∈ Set.Icc (1 / 4 : ℝ) 1) (sEnv : Struct → Bool) :
    (recip64ResProg s).eval env sEnv = recip64Approx (env ()) s % 16 := by
  unfold recip64ResProg recipOuterProg
  rw [QueryProg.eval_substDigits, eval_recipChild_eq, QueryProg.eval_substDigits,
    QueryProg.eval_map, eval_windowPrefixModProg]
  have hfun : (fun u =>
      (recipHalfVirtualRecipe.digitProg u).eval (recipVirtualEnv (env ()) s) sEnv) =
      recipHalfStream (env ()) s := by
    ext u
    exact eval_recipHalfVirtualRecipe hx hx_mem s sEnv u
  rw [hfun, recip64Approx_emod_sixteen hx hx_mem s]

theorem mem_activeQueries_recipOuterProg {Struct : Type v} (s : ℕ)
    (vEnv : Fin 3 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 3) Struct}
    (hev : ev ∈ (recipOuterProg s).activeQueries vEnv sEnv) :
    (∃ (sOp : Struct) (w : ℕ),
        w ≤ 26 + (recipHalfVirtualRecipe (Struct := Struct)).coeffA +
          8 * (recipHalfVirtualRecipe (Struct := Struct)).coeffB +
          (recipHalfVirtualRecipe (Struct := Struct)).coeffB * s ∧
        ev = .struct sOp w) ∨
      ∃ (op : Fin 3) (r w : ℕ),
        r ≤ s + (8 + (recipHalfVirtualRecipe (Struct := Struct)).coeffC) ∧
        (w : ℤ) ≤
          ((26 + (recipHalfVirtualRecipe (Struct := Struct)).coeffA +
              8 * (recipHalfVirtualRecipe (Struct := Struct)).coeffB : ℕ) : ℤ) +
            ((recipHalfVirtualRecipe (Struct := Struct)).coeffB : ℤ) * ((s : ℤ) - (r : ℤ)) ∧
        ev = .digit op r w := by
  set H := recipHalfVirtualRecipe (Struct := Struct)
  unfold recipOuterProg at hev
  rcases QueryProg.mem_activeQueries_substDigits 4 _ _ vEnv sEnv hev with
    ⟨_, _, hs, _⟩ | ⟨_, u, w₁, evH, hd, hevH, rfl⟩
  · rw [QueryProg.activeQueries_map] at hs
    obtain ⟨_, _, hEq⟩ := mem_activeQueries_windowPrefixModProg () 11 (s + 8) _ sEnv hs
    nomatch hEq
  · rw [QueryProg.activeQueries_map] at hd
    obtain ⟨u', hu, hEq⟩ := mem_activeQueries_windowPrefixModProg () 11 (s + 8) _ sEnv hd
    injection hEq with _ hu_eq hw_eq
    subst hu_eq hw_eq
    have hAllH := H.allowance u vEnv sEnv hevH
    have hslack1 : H.slack = 1 := rfl
    rw [hslack1] at hAllH
    cases evH with
    | struct sOp l =>
      left
      change (l : ℤ) ≤ ((H.coeffA * 1 : ℕ) : ℤ) + (H.coeffB : ℤ) * (u : ℤ) at hAllH
      refine ⟨sOp, (22 + 4) + l, ?_, rfl⟩
      have hleZ : (((22 + 4) + l : ℕ) : ℤ) ≤
          ((26 + H.coeffA + 8 * H.coeffB + H.coeffB * s : ℕ) : ℤ) := by
        have huZ : (u : ℤ) ≤ (s : ℤ) + 8 := by exact_mod_cast hu
        have hmul : (H.coeffB : ℤ) * (u : ℤ) ≤ (H.coeffB : ℤ) * ((s : ℤ) + 8) :=
          mul_le_mul_of_nonneg_left huZ (Nat.cast_nonneg _)
        push_cast at hAllH ⊢
        linarith
      exact_mod_cast hleZ
    | digit op r l =>
      right
      obtain ⟨hr, hl⟩ := hAllH
      refine ⟨op, r, (22 + 4) + l, by omega, ?_, rfl⟩
      have huZ : (u : ℤ) ≤ (s : ℤ) + 8 := by exact_mod_cast hu
      have hmul : (H.coeffB : ℤ) * ((u : ℤ) - (r : ℤ)) ≤
          (H.coeffB : ℤ) * ((s : ℤ) + 8 - (r : ℤ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      push_cast at hl ⊢
      linarith

/-- **Lemma 10.5 (certified early-word reciprocal primitive on `[1 / 4, 1]`)**
[OpenAI2026LogSpace, Lemma 10.5]. Here `[1 / 4, 1]` is the input domain
`streamVal (env ()) ∈ [1 / 4, 1]`, while the `1 / 64` factor normalizes the Taylor components and
output `1 / (64 * x)` into `[-1, 1]` before downstream `shiftClip` restores the target scale. -/
@[expose] noncomputable def recip64Prim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe Unit Struct :=
  let H := recipHalfVirtualRecipe (Struct := Struct)
  let A₀ := 26 + H.coeffA + 8 * H.coeffB
  let B₀ := H.coeffB
  let C₀ := 8 + H.coeffC
  let aRecip := max (A₀ + 26 + 15 * (B₀ + 1)) ((A₀ + 4) + (B₀ + 2) * C₀)
  let bRecip := 2 * B₀ + 2
  let K₂ := A₀ + B₀ + 8 * C₀ + 108
  let cInt := max (34 + 9 * H.intrinsicCoeff) K₂
  recipeOfMod16Prog d hd
    (fun env _ => IsNormSignedStream (env ()) ∧ streamVal (env ()) ∈ Set.Icc (1 / 4 : ℝ) 1)
    (fun val _ => 1 / (64 * val ()))
    (fun env _ => recip64Approx (env ()))
    recip64ResProg aRecip bRecip C₀ cInt
    (fun {env _} ⟨_, hlo, _⟩ => by
      have hge16 : (16 : ℝ) ≤ 64 * streamVal (env ()) := by linarith
      have hpos : (0 : ℝ) < 64 * streamVal (env ()) := by linarith
      rw [abs_of_pos (div_pos one_pos hpos)]
      exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) hge16).trans (by norm_num))
    (fun ⟨⟨hs, _⟩, hmem⟩ => recip64Approx_isScaledApprox hs hmem)
    (fun ⟨⟨hs, _⟩, hmem⟩ s => eval_recip64ResProg s hs hmem _)
    (fun s env sEnv ev hev => by
      unfold recip64ResProg at hev
      rcases QueryProg.mem_activeQueries_substDigits 4 _ _ env sEnv hev with
        ⟨sOp, w, hs, rfl⟩ | ⟨op, r, wOut, evC, hdOut, hevC, rfl⟩
      · rcases mem_activeQueries_recipOuterProg s _ sEnv hs with
          ⟨sOp', w', hw, hEq⟩ | ⟨_, _, _, _, _, hEq⟩
        · injection hEq with hs_eq hw_eq
          subst sOp' w'
          change (w : ℤ) ≤ ((aRecip * d : ℕ) : ℤ) + (bRecip : ℤ) * (s : ℤ)
          have ha_ge : A₀ ≤ aRecip := by dsimp [aRecip, A₀]; omega
          have had : A₀ ≤ aRecip * d := ha_ge.trans (Nat.le_mul_of_pos_right _ hd)
          have hb_ge : B₀ ≤ bRecip := by dsimp [bRecip, B₀]; omega
          have hleNat : w ≤ aRecip * d + bRecip * s := by
            have h1 : w ≤ A₀ + B₀ * s := hw
            have h2 : B₀ * s ≤ bRecip * s := Nat.mul_le_mul_right s hb_ge
            omega
          exact_mod_cast hleNat
        · nomatch hEq
      · rcases mem_activeQueries_recipOuterProg s _ sEnv hdOut with
          ⟨_, _, _, hEq⟩ | ⟨op', r', w', hr, hwOut, hEq⟩
        · nomatch hEq
        · injection hEq with hop hr_eq hw_eq
          subst op' r' w'
          unfold recipChild at hevC
          have hEarly : ∀ {evI : QueryEvent Unit Struct},
              evI ∈ (intPrefixProg () (recipCutoff s)).activeQueries env sEnv →
              AllowanceBound d aRecip bRecip C₀ s ((evI.addBits 0).addBits (wOut + 4)) := by
            intro evI hevI
            obtain ⟨j, hj, rfl⟩ := mem_activeQueries_intPrefixProg () (recipCutoff s) env sEnv hevI
            refine ⟨?_, ?_⟩
            · have hC₀_ge : 7 ≤ C₀ * d := by
                have h8 : 7 ≤ C₀ := by dsimp [C₀]; omega
                exact h8.trans (Nat.le_mul_of_pos_right _ hd)
              unfold recipCutoff at hj
              omega
            · have hpay := clock_succ_le_early_payment hj
              have hr0 : (0 : ℤ) ≤ (r : ℤ) := Nat.cast_nonneg r
              have hwOut_s : (wOut : ℤ) ≤ (A₀ : ℤ) + (B₀ : ℤ) * (s : ℤ) := by
                have hmul : (B₀ : ℤ) * ((s : ℤ) - (r : ℤ)) ≤ (B₀ : ℤ) * (s : ℤ) :=
                  mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
                dsimp only [A₀, B₀, H] at hwOut hmul ⊢
                push_cast at hwOut ⊢
                linarith
              have hj_le : recipCutoff s + j + 8 ≤ s + 22 := by unfold recipCutoff at hj ⊢; omega
              have hjZ : ((recipCutoff s + j + 8 : ℕ) : ℤ) ≤ (s : ℤ) + 22 := by
                exact_mod_cast hj_le
              have htot_s : ((wOut + 4 + (0 + (recipCutoff s + j + 8)) : ℕ) : ℤ) ≤
                  ((A₀ + 26 : ℕ) : ℤ) + ((B₀ + 1 : ℕ) : ℤ) * ((s + 1 : ℕ) : ℤ) := by
                push_cast
                linarith
              have hmul_pay : ((B₀ + 1 : ℕ) : ℤ) * ((s + 1 : ℕ) : ℤ) ≤
                  ((B₀ + 1 : ℕ) : ℤ) * (15 + 2 * ((s : ℤ) - (j : ℤ))) :=
                mul_le_mul_of_nonneg_left hpay (Nat.cast_nonneg _)
              have ha_le : A₀ + 26 + 15 * (B₀ + 1) ≤ aRecip * d :=
                (le_max_left _ _).trans (Nat.le_mul_of_pos_right _ hd)
              have haZ : (((A₀ + 26 + 15 * (B₀ + 1)) : ℕ) : ℤ) ≤ ((aRecip * d : ℕ) : ℤ) := by
                exact_mod_cast ha_le
              dsimp only [bRecip]
              push_cast at htot_s hmul_pay haZ ⊢
              linarith
          by_cases h0 : op = 0
          · simp only [h0, ↓reduceIte, QueryProg.activeQueries_bindOverhead,
              QueryProg.activeQueries, List.append_nil, List.mem_map] at hevC
            obtain ⟨evI, hevI, rfl⟩ := hevC
            exact hEarly hevI
          · simp only [h0, ↓reduceIte] at hevC
            by_cases h1 : op = 1
            · simp only [h1, ↓reduceIte, QueryProg.activeQueries_bindOverhead,
                QueryProg.activeQueries, List.append_nil, List.mem_map] at hevC
              obtain ⟨evI, hevI, rfl⟩ := hevC
              exact hEarly hevI
            · simp only [h1, ↓reduceIte] at hevC
              by_cases hrc : r ≤ recipCutoff s
              · simp only [hrc, ↓reduceIte] at hevC
                nomatch hevC
              · simp only [hrc, ↓reduceIte, QueryProg.activeQueries, List.mem_cons] at hevC
                rcases hevC with rfl | hevC
                · have hBase :
                      AllowanceBound (Struct := Struct) d (A₀ + 4) B₀ C₀ s
                        (.digit () r (wOut + 4 + 0)) := by
                    refine ⟨hr.trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right C₀ hd) s), ?_⟩
                    have hA4 : ((A₀ + 4 : ℕ) : ℤ) ≤ (((A₀ + 4) * d : ℕ) : ℤ) := by
                      exact_mod_cast Nat.le_mul_of_pos_right (A₀ + 4) hd
                    dsimp only [A₀, B₀, H] at hwOut hA4 ⊢
                    push_cast at hwOut hA4 ⊢
                    linarith
                  have hMono := hBase.mono_coeff (b := bRecip) (by dsimp [bRecip]; omega)
                  refine hMono.mono_ac (a := aRecip) (c := C₀) ?_ le_rfl
                  have hsub : bRecip - B₀ = B₀ + 2 := by dsimp [bRecip]; omega
                  rw [hsub]
                  exact le_max_right _ _
                · nomatch hevC)
    (fun s env sEnv => by
      have hd_pos : 1 ≤ d + s := by omega
      set vEnv : Fin 3 → ℕ → ℤ := fun op r => (recipChild s op r).eval env sEnv
      unfold recip64ResProg
      apply QueryProg.maxIntrinsicBits_substDigits_le 4 _ _ env sEnv
      · unfold recipOuterProg
        apply QueryProg.maxIntrinsicBits_substDigits_le 4 _ _ vEnv sEnv
        · rw [QueryProg.maxIntrinsicBits_map]
          refine (maxIntrinsicBits_windowPrefixModProg_le () 11 (s + 8) _ sEnv).trans ?_
          have h34 : 34 ≤ 34 * d := Nat.le_mul_of_pos_right 34 hd
          have h1 : (s + 8) + 2 * 11 + 4 ≤ (34 + 9 * H.intrinsicCoeff) * (d + s) := by
            have hexp : (34 + 9 * H.intrinsicCoeff) * (d + s) =
                34 * d + 34 * s + 9 * H.intrinsicCoeff * (d + s) := by ring
            omega
          exact h1.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
        · intro _ u w₁ hdOut
          rw [QueryProg.activeQueries_map] at hdOut
          obtain ⟨_, hu, hEq⟩ := mem_activeQueries_windowPrefixModProg () 11 (s + 8) _ sEnv hdOut
          injection hEq with _ hu_eq hw_eq
          subst hu_eq hw_eq
          have hIntH := H.intrinsic_bound u vEnv sEnv
          have hslack1 : H.slack = 1 := rfl
          rw [hslack1] at hIntH
          have hbound : 2 * 11 + 4 + H.intrinsicCoeff * (1 + u) ≤
              (34 + 9 * H.intrinsicCoeff) * (d + s) := by
            have hu9 : 1 + u ≤ 9 * (d + s) := by omega
            calc 2 * 11 + 4 + H.intrinsicCoeff * (1 + u)
                ≤ 34 * (d + s) + H.intrinsicCoeff * (9 * (d + s)) :=
                  Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ hu9)
              _ = (34 + 9 * H.intrinsicCoeff) * (d + s) := by ring
          exact (Nat.add_le_add_left hIntH 26).trans
            (hbound.trans (Nat.mul_le_mul_right _ (le_max_left _ _)))
      · intro op r wOut hdOut
        rcases mem_activeQueries_recipOuterProg s _ sEnv hdOut with
          ⟨_, _, _, hEq⟩ | ⟨op', r', w', hr, hwOut, hEq⟩
        · nomatch hEq
        · injection hEq with hop hr_eq hw_eq
          subst op' r' w'
          have hrC : r ≤ s + C₀ := by
            dsimp only [C₀, H] at hr ⊢
            exact hr
          have hwOut_nat : wOut ≤ A₀ + B₀ * s := by
            have hleZ : (wOut : ℤ) ≤ ((A₀ + B₀ * s : ℕ) : ℤ) := by
              have hmul : (B₀ : ℤ) * ((s : ℤ) - (r : ℤ)) ≤ (B₀ : ℤ) * (s : ℤ) :=
                mul_le_mul_of_nonneg_left (by omega) (Nat.cast_nonneg _)
              dsimp only [A₀, B₀, H] at hwOut hmul ⊢
              push_cast at hwOut ⊢
              linarith
            exact_mod_cast hleZ
          have hrc_eq : recipCutoff s = s / 2 + 7 := rfl
          have hch_int : (recipChild s op r).maxIntrinsicBits env sEnv ≤
              8 * (s + (s + C₀) + 8) + (s + 23) := by
            unfold recipChild
            split_ifs
            · refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
              · have hp := maxIntrinsicBits_intPrefixProg_le () (recipCutoff s) env sEnv
                omega
              · simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
                omega
            · refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
              · have hp := maxIntrinsicBits_intPrefixProg_le () (recipCutoff s) env sEnv
                omega
              · simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
                omega
            · simp [QueryProg.maxIntrinsicBits]
            · simp [QueryProg.maxIntrinsicBits]
          have hsum_le : wOut + 4 + (8 * (s + (s + C₀) + 8) + (s + 23)) ≤ K₂ * (d + s) := by
            have hlin : wOut + 4 + (8 * (s + (s + C₀) + 8) + (s + 23)) ≤
                (A₀ + 8 * C₀ + 91) + (B₀ + 17) * s := by
              rw [Nat.add_mul]
              omega
            have hd_term : A₀ + 8 * C₀ + 91 ≤ K₂ * d := by
              have hk : A₀ + 8 * C₀ + 91 ≤ K₂ := by dsimp [K₂]; omega
              exact hk.trans (Nat.le_mul_of_pos_right K₂ hd)
            have hs_term : (B₀ + 17) * s ≤ K₂ * s :=
              Nat.mul_le_mul_right s (by dsimp [K₂]; omega)
            calc wOut + 4 + (8 * (s + (s + C₀) + 8) + (s + 23))
                ≤ (A₀ + 8 * C₀ + 91) + (B₀ + 17) * s := hlin
              _ ≤ K₂ * d + K₂ * s := Nat.add_le_add hd_term hs_term
              _ = K₂ * (d + s) := (Nat.mul_add K₂ d s).symm
          exact (Nat.add_le_add_left hch_int (wOut + 4)).trans
            (hsum_le.trans (Nat.mul_le_mul_right _ (le_max_right _ _))))

/-- Compose a `UniformStreamRecipe` whose target value lies in `[1 / 4, 1]` with `recip64Prim` to
obtain `1 / (64 * R)`. -/
@[expose] noncomputable def UniformStreamRecipe.recip64 {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) : UniformStreamRecipe Op Struct :=
  let raw := (recip64Prim R.slack R.slack_pos).comp (fun _ => R)
    R.coeffA R.coeffB R.coeffC R.intrinsicCoeff
    (fun _ => rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
  raw.weakenValid
    (fun env sEnv =>
      R.ValidEnv env sEnv ∧
        R.targetVal (fun op => streamVal (env op)) sEnv ∈ Set.Icc (1 / 4 : ℝ) 1)
    (fun ⟨hR, hMem⟩ => by
      refine ⟨fun _ => hR, ⟨⟨R.emits_signed hR, ?_⟩, ?_⟩⟩
      · rw [R.emits_exact hR]
        exact R.abs_targetVal_le_one hR
      · rwa [R.emits_exact hR])

end ReciprocalRecipe

section RankRecipe

/-- Count how many elements `w` in `ws` satisfy `0 ≤ cmpPrefixProg w i K` using `O(idxBits)`
retained bits. -/
@[expose] def countAtLeastProg {Op : Type u} {Struct : Type v} (i : Op) (K idxBits : ℕ) :
    List Op → ℕ → QueryProg Op Struct ℕ
  | [], cnt => .scratchStep (2 * idxBits + 4) (.ret cnt)
  | w :: ws, cnt =>
      (cmpPrefixProg w i K).bindOverhead (2 * idxBits + 4) fun c =>
        countAtLeastProg i K idxBits ws (if 0 ≤ c then cnt + 1 else cnt)

/-- Streaming outer scan over candidate elements `rem`, tracking the index `best : Option Op` with
largest positive `intPrefix` among elements exceeded or matched by at least `k` members of `items`.
-/
@[expose] def rankFoldProg {Op : Type u} {Struct : Type v} (k : ℕ) (items : List Op)
    (K idxBits : ℕ) : List Op → Option Op → QueryProg Op Struct (Option Op)
  | [], best => .scratchStep (2 * idxBits + 4) (.ret best)
  | i :: rest, best =>
      (countAtLeastProg i K idxBits items 0).bindOverhead (2 * idxBits + 4) fun cnt =>
        if k ≤ cnt then
          (cmpWithConstProg i (fun _ => 0) K).bindOverhead (2 * idxBits + 4) fun cPos =>
            if 0 < cPos then
              match best with
              | none => rankFoldProg k items K idxBits rest (some i)
              | some b =>
                  (cmpPrefixProg i b K).bindOverhead (2 * idxBits + 4) fun cBest =>
                    rankFoldProg k items K idxBits rest (if 0 < cBest then some i else some b)
            else
              rankFoldProg k items K idxBits rest best
        else
          rankFoldProg k items K idxBits rest best

/-- Mod-16 residue program for `rankApprox k items.toFinset env s`, sizing its index/count
registers natively from `Nat.log 2 items.length + 2` [OpenAI2026LogSpace, Lemma 10.6]. -/
@[expose] def rankListResProg {Op : Type u} {Struct : Type v}
    (k : ℕ) (items : List Op) (s : ℕ) : QueryProg Op Struct ℤ :=
  let idxBits := Nat.log 2 items.length + 2
  (rankFoldProg k items (s + 4) idxBits items none).bindOverhead (idxBits + 4) fun best =>
    match best with
    | none => .scratchStep 8 (.ret 0)
    | some b => (windowPrefixModProg b 8 (s + 4)).map (· / 16)

private theorem eval_countAtLeastProg {Op : Type u} {Struct : Type v}
    (i : Op) (K idxBits : ℕ) (ws : List Op) (cnt : ℕ)
    {env : Op → ℕ → ℤ} (hi : IsSignedStream (env i))
    (hws : ∀ w ∈ ws, IsSignedStream (env w)) (sEnv : Struct → Bool) :
    (countAtLeastProg i K idxBits ws cnt).eval env sEnv =
      cnt + (ws.filter fun w => decide (intPrefix (env i) K ≤ intPrefix (env w) K)).length := by
  induction ws generalizing cnt with
  | nil => simp [countAtLeastProg, QueryProg.eval]
  | cons w ws ih =>
    have hw : IsSignedStream (env w) := hws w List.mem_cons_self
    have hws' : ∀ w' ∈ ws, IsSignedStream (env w') :=
      fun w' hm => hws w' (List.mem_cons_of_mem w hm)
    simp only [countAtLeastProg, QueryProg.eval_bindOverhead]
    rw [eval_cmpPrefixProg, ih _ hws']
    have hcmp := cmpPrefix_nonneg_iff hw hi K
    by_cases hle : intPrefix (env i) K ≤ intPrefix (env w) K
    · have hc : 0 ≤ cmpPrefix (env w) (env i) K := hcmp.mpr hle
      simp only [hc, ↓reduceIte, List.filter_cons, decide_eq_true hle, List.length_cons]
      omega
    · have hc : ¬ 0 ≤ cmpPrefix (env w) (env i) K := hcmp.not.mpr hle
      simp only [hc, ↓reduceIte, List.filter_cons, decide_eq_false hle, Bool.false_eq_true]

private def optIntPrefix {Op : Type u} (env : Op → ℕ → ℤ) (K : ℕ) : Option Op → ℤ
  | none => 0
  | some b => intPrefix (env b) K

private def foldQualMax {Op : Type u} (P : Op → Prop) [DecidablePred P] (h : Op → ℤ) :
    List Op → ℤ → ℤ
  | [], acc => acc
  | i :: rest, acc => foldQualMax P h rest (if P i then max acc (h i) else acc)

private theorem acc_le_foldQualMax {Op : Type u} (P : Op → Prop) [DecidablePred P] (h : Op → ℤ)
    (rem : List Op) (acc : ℤ) :
    acc ≤ foldQualMax P h rem acc := by
  induction rem generalizing acc with
  | nil => exact le_rfl
  | cons i rest ih =>
    simp only [foldQualMax]
    refine le_trans ?_ (ih _)
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl

private theorem mem_le_foldQualMax {Op : Type u} (P : Op → Prop) [DecidablePred P] (h : Op → ℤ)
    (rem : List Op) (acc : ℤ) {x : Op} (hx : x ∈ rem) (hPx : P x) :
    h x ≤ foldQualMax P h rem acc := by
  induction rem generalizing acc with
  | nil => nomatch hx
  | cons i rest ih =>
    simp only [foldQualMax]
    rcases List.mem_cons.mp hx with rfl | hx_rest
    · simp only [hPx, ↓reduceIte]
      exact (le_max_right acc (h x)).trans (acc_le_foldQualMax P h rest _)
    · exact ih _ hx_rest

private theorem foldQualMax_le {Op : Type u} (P : Op → Prop) [DecidablePred P] (h : Op → ℤ)
    (rem : List Op) (acc U : ℤ) (hacc : acc ≤ U) (hrem : ∀ x ∈ rem, P x → h x ≤ U) :
    foldQualMax P h rem acc ≤ U := by
  induction rem generalizing acc with
  | nil => exact hacc
  | cons i rest ih =>
    simp only [foldQualMax]
    refine ih _ ?_ (fun x hx hPx => hrem x (List.mem_cons_of_mem i hx) hPx)
    split_ifs with hPi
    · exact max_le hacc (hrem i List.mem_cons_self hPi)
    · exact hacc

private theorem eval_rankFoldProg_optIntPrefix {Op : Type u} [DecidableEq Op] {Struct : Type v}
    (k : ℕ) (items : List Op) (hNodup : items.Nodup) (K idxBits : ℕ)
    (rem : List Op) (hSub : ∀ x ∈ rem, x ∈ items)
    {env : Op → ℕ → ℤ} (hEnv : ∀ x ∈ items, IsSignedStream (env x)) (sEnv : Struct → Bool)
    (best : Option Op)
    (hBestMem : ∀ b, best = some b → b ∈ items)
    (hBestNonneg : 0 ≤ optIntPrefix env K best) :
    let h : Op → ℤ := fun x => intPrefix (env x) K
    let P : Op → Prop := fun x => k ≤ #{w ∈ items.toFinset | h x ≤ h w}
    (∀ b, (rankFoldProg k items K idxBits rem best).eval env sEnv = some b → b ∈ items) ∧
      optIntPrefix env K ((rankFoldProg k items K idxBits rem best).eval env sEnv) =
        foldQualMax P h rem (optIntPrefix env K best) := by
  intro h P
  induction rem generalizing best with
  | nil =>
    dsimp only [rankFoldProg, QueryProg.eval, foldQualMax]
    exact ⟨hBestMem, rfl⟩
  | cons i rest ih =>
    have hi_mem : i ∈ items := hSub i List.mem_cons_self
    have hrest_sub : ∀ x ∈ rest, x ∈ items := fun x hx => hSub x (List.mem_cons_of_mem i hx)
    have hi_sign : IsSignedStream (env i) := hEnv i hi_mem
    have hcnt_eq : (countAtLeastProg i K idxBits items 0).eval env sEnv =
        #{w ∈ items.toFinset | h i ≤ h w} := by
      rw [eval_countAtLeastProg i K idxBits items 0 hi_sign hEnv sEnv, Nat.zero_add]
      have hnod_f : (items.filter fun w => decide (h i ≤ h w)).Nodup := hNodup.filter _
      rw [← List.toFinset_card_of_nodup hnod_f]
      congr 1
      ext w
      simp [List.mem_toFinset, mem_filter]
    have hcPos_iff : 0 < (cmpWithConstProg i (fun _ => 0) K).eval env sEnv ↔ 0 < h i := by
      rw [eval_cmpWithConstProg, cmpPrefix_pos_iff hi_sign isSignedStream_zero K,
        streamPrefix_eq_intPrefix_div, streamPrefix_eq_intPrefix_div]
      have h0 : intPrefix (fun _ => 0) K = 0 := by
        unfold intPrefix
        simp
      rw [h0, Int.cast_zero, zero_div, div_pos_iff_of_pos_right (by positivity)]
      exact Int.cast_pos
    simp only [rankFoldProg, QueryProg.eval_bindOverhead, hcnt_eq, foldQualMax]
    by_cases hPi : P i
    · have hcnt_ge : k ≤ #{w ∈ items.toFinset | h i ≤ h w} := hPi
      simp only [hcnt_ge, hPi, ↓reduceIte, QueryProg.eval_bindOverhead]
      by_cases hpos : 0 < h i
      · have hcPos : 0 < (cmpWithConstProg i (fun _ => 0) K).eval env sEnv := hcPos_iff.mpr hpos
        simp only [hcPos, ↓reduceIte]
        cases best with
        | none =>
          have hmax0 : optIntPrefix env K (some i) = max (optIntPrefix env K none) (h i) := by
            simp only [optIntPrefix]
            exact (max_eq_right_of_lt hpos).symm
          have hres := ih (hSub := hrest_sub) (some i)
            (fun b hb => by injection hb with hb'; subst hb'; exact hi_mem)
            (by simp only [optIntPrefix]; exact hpos.le)
          rwa [hmax0] at hres
        | some b =>
          simp only [QueryProg.eval_bindOverhead]
          have hb_mem : b ∈ items := hBestMem b rfl
          have hb_sign : IsSignedStream (env b) := hEnv b hb_mem
          have hcBest_iff : 0 < (cmpPrefixProg i b K).eval env sEnv ↔ h b < h i := by
            rw [eval_cmpPrefixProg, cmpPrefix_pos_iff hi_sign hb_sign K,
              streamPrefix_eq_intPrefix_div, streamPrefix_eq_intPrefix_div,
              div_lt_div_iff_of_pos_right (by positivity)]
            exact Int.cast_lt
          set nextBest : Option Op :=
            if 0 < (cmpPrefixProg i b K).eval env sEnv then some i else some b
          have hnextMem : ∀ b', nextBest = some b' → b' ∈ items := by
            intro b' hb'
            dsimp [nextBest] at hb'
            split_ifs at hb' with hc
            · injection hb' with hb'; subst hb'; exact hi_mem
            · injection hb' with hb'; subst hb'; exact hb_mem
          have hnextVal : optIntPrefix env K nextBest =
              max (optIntPrefix env K (some b)) (h i) := by
            dsimp only [nextBest]
            by_cases hlt : h b < h i
            · have hc : 0 < (cmpPrefixProg i b K).eval env sEnv := hcBest_iff.mpr hlt
              simp only [hc, ↓reduceIte, optIntPrefix]
              exact (max_eq_right_of_lt hlt).symm
            · have hc : ¬ 0 < (cmpPrefixProg i b K).eval env sEnv := hcBest_iff.not.mpr hlt
              simp only [hc, ↓reduceIte, optIntPrefix]
              exact (max_eq_left (not_lt.mp hlt)).symm
          have hnextNonneg : 0 ≤ optIntPrefix env K nextBest := by
            rw [hnextVal]
            exact hBestNonneg.trans (le_max_left _ _)
          have hres := ih (hSub := hrest_sub) nextBest hnextMem hnextNonneg
          rwa [hnextVal] at hres
      · have hcPos : ¬ 0 < (cmpWithConstProg i (fun _ => 0) K).eval env sEnv :=
          hcPos_iff.not.mpr hpos
        simp only [hcPos, ↓reduceIte]
        have hmax_eq : max (optIntPrefix env K best) (h i) = optIntPrefix env K best :=
          max_eq_left ((not_lt.mp hpos).trans hBestNonneg)
        rw [hmax_eq]
        exact ih (hSub := hrest_sub) best hBestMem hBestNonneg
    · have hcnt_lt : ¬ k ≤ #{w ∈ items.toFinset | h i ≤ h w} := hPi
      simp only [hcnt_lt, hPi, ↓reduceIte]
      exact ih (hSub := hrest_sub) best hBestMem hBestNonneg

theorem eval_rankListResProg {Op : Type u} [DecidableEq Op] {Struct : Type v}
    (k : ℕ) (items : List Op) (hNodup : items.Nodup) (s : ℕ)
    {env : Op → ℕ → ℤ} (hEnv : ∀ x ∈ items, IsSignedStream (env x)) (sEnv : Struct → Bool) :
    (rankListResProg k items s).eval env sEnv =
      rankApprox k items.toFinset env s % 16 := by
  set idxBits := Nat.log 2 items.length + 2
  set K := s + 4
  set h : Op → ℤ := fun x => intPrefix (env x) K
  set P : Op → Prop := fun x => k ≤ #{w ∈ items.toFinset | h x ≤ h w}
  obtain ⟨_, hFoldVal⟩ := eval_rankFoldProg_optIntPrefix k items hNodup K idxBits items
    (fun _ hx => hx) hEnv sEnv none (fun _ hb => nomatch hb) le_rfl
  have hFold_eq_kth : foldQualMax P h items 0 = kthLargest k items.toFinset h := by
    unfold kthLargest
    apply le_antisymm
    · refine foldQualMax_le P h items 0 _ (le_max' _ _ (mem_insert_self _ _)) fun x hx hPx => ?_
      exact le_max' _ _ (mem_insert_of_mem
        (mem_image_of_mem h (mem_filter.mpr ⟨List.mem_toFinset.mpr hx, hPx⟩)))
    · refine max'_le _ _ _ fun r hr => ?_
      rcases mem_insert.mp hr with rfl | hr
      · exact acc_le_foldQualMax P h items 0
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
        obtain ⟨hxs, hPx⟩ := mem_filter.mp hx
        exact mem_le_foldQualMax P h items 0 (List.mem_toFinset.mp hxs) hPx
  unfold rankListResProg rankApprox
  dsimp only
  rw [QueryProg.eval_bindOverhead]
  set best := (rankFoldProg k items K idxBits items none).eval env sEnv
  have h16 : (16 : ℤ) = (2 : ℤ) ^ (4 : ℕ) := by decide
  have h256 : (2 : ℤ) ^ (8 : ℕ) = (2 : ℤ) ^ (4 + 4 : ℕ) := rfl
  cases hbest : best with
  | none =>
    simp only [QueryProg.eval]
    have hkth0 : kthLargest k items.toFinset h = 0 := by
      rw [← hFold_eq_kth]
      simpa only [best, hbest, optIntPrefix] using hFoldVal.symm
    change 0 = kthLargest k items.toFinset h / 16 % 16
    rw [hkth0]
    decide
  | some b =>
    simp only [QueryProg.eval_map, eval_windowPrefixModProg, h256]
    have hkth_b : kthLargest k items.toFinset h = intPrefix (env b) K := by
      rw [← hFold_eq_kth]
      simpa only [best, hbest, optIntPrefix] using hFoldVal.symm
    change (intPrefix (env b) K % (2 : ℤ) ^ (4 + 4 : ℕ)) / 16 =
      kthLargest k items.toFinset h / 16 % 16
    rw [hkth_b, h16, ediv_two_pow_emod_eq]

private theorem mem_activeQueries_countAtLeastProg {Op : Type u} {Struct : Type v}
    (i : Op) (K idxBits : ℕ) (ws : List Op) (cnt : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (countAtLeastProg i K idxBits ws cnt).activeQueries env sEnv) :
    ∃ op j L, j ≤ K ∧ L ≤ 2 * idxBits + 14 + 6 * (K - j) ∧ ev = .digit op j L := by
  induction ws generalizing cnt with
  | nil => nomatch hev
  | cons w ws ih =>
    simp only [countAtLeastProg, QueryProg.activeQueries_bindOverhead, List.mem_append,
      List.mem_map] at hev
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
    · obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_cmpPrefixProg w i K env sEnv hev₀
      exact ⟨op, j, (2 * idxBits + 4) + L, hj, by omega, rfl⟩
    · exact ih _ hev₁

private theorem maxIntrinsicBits_countAtLeastProg_le {Op : Type u} {Struct : Type v}
    (i : Op) (K idxBits : ℕ) (ws : List Op) (cnt : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (countAtLeastProg i K idxBits ws cnt).maxIntrinsicBits env sEnv ≤
      2 * idxBits + 6 * K + 14 := by
  induction ws generalizing cnt with
  | nil =>
    simp only [countAtLeastProg, QueryProg.maxIntrinsicBits, Nat.max_zero]
    omega
  | cons w ws ih =>
    simp only [countAtLeastProg]
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ (ih _))
    have hc := maxIntrinsicBits_cmpPrefixProg_le w i K env sEnv
    omega

theorem mem_activeQueries_rankFoldProg {Op : Type u} {Struct : Type v}
    (k : ℕ) (items : List Op) (K idxBits : ℕ) (rem : List Op) (best : Option Op)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (rankFoldProg k items K idxBits rem best).activeQueries env sEnv) :
    ∃ op j L, j ≤ K ∧ L ≤ 4 * idxBits + 18 + 6 * (K - j) ∧ ev = .digit op j L := by
  induction rem generalizing best with
  | nil => nomatch hev
  | cons i rest ih =>
    simp only [rankFoldProg, QueryProg.activeQueries_bindOverhead, List.mem_append,
      List.mem_map] at hev
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
    · obtain ⟨op, j, L, hj, hL, rfl⟩ :=
        mem_activeQueries_countAtLeastProg i K idxBits items 0 env sEnv hev₀
      exact ⟨op, j, (2 * idxBits + 4) + L, hj, by omega, rfl⟩
    · split_ifs at hev₁
      · simp only [QueryProg.activeQueries_bindOverhead, List.mem_append, List.mem_map] at hev₁
        rcases hev₁ with ⟨ev₀, hev₀, rfl⟩ | hev₂
        · obtain ⟨j, L, hj, hL, rfl⟩ :=
            mem_activeQueries_cmpWithConstProg i (fun _ => 0) K env sEnv hev₀
          exact ⟨i, j, (2 * idxBits + 4) + L, hj, by omega, rfl⟩
        · split_ifs at hev₂
          · cases best with
            | none => exact ih _ hev₂
            | some b =>
              simp only [QueryProg.activeQueries_bindOverhead, List.mem_append,
                List.mem_map] at hev₂
              rcases hev₂ with ⟨ev₀, hev₀, rfl⟩ | hev₃
              · obtain ⟨op, j, L, hj, hL, rfl⟩ :=
                  mem_activeQueries_cmpPrefixProg i b K env sEnv hev₀
                exact ⟨op, j, (2 * idxBits + 4) + L, hj, by omega, rfl⟩
              · exact ih _ hev₃
          · exact ih _ hev₂
      · exact ih _ hev₁

theorem maxIntrinsicBits_rankFoldProg_le {Op : Type u} {Struct : Type v}
    (k : ℕ) (items : List Op) (K idxBits : ℕ) (rem : List Op) (best : Option Op)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (rankFoldProg k items K idxBits rem best).maxIntrinsicBits env sEnv ≤
      4 * idxBits + 6 * K + 18 := by
  induction rem generalizing best with
  | nil =>
    simp only [rankFoldProg, QueryProg.maxIntrinsicBits, Nat.max_zero]
    omega
  | cons i rest ih =>
    simp only [rankFoldProg]
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · have hc := maxIntrinsicBits_countAtLeastProg_le i K idxBits items 0 env sEnv
      omega
    · split_ifs
      · refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
        · have hc := maxIntrinsicBits_cmpWithConstProg_le i (fun _ => 0) K env sEnv
          omega
        · split_ifs
          · cases best with
            | none => exact ih _
            | some b =>
              refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans
                (max_le ?_ (ih _))
              have hc := maxIntrinsicBits_cmpPrefixProg_le i b K env sEnv
              omega
          · exact ih _
      · exact ih _

private theorem log_two_le_of_le_two_pow {n m : ℕ} (h : n ≤ 2 ^ m) : Nat.log 2 n ≤ m := by
  by_contra hgt
  have hge : m + 1 ≤ Nat.log 2 n := by omega
  have hne : n ≠ 0 := by
    intro h0
    simp [h0] at hge
  have hp1 : 2 ^ (m + 1) ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by decide) hge
  have hp2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hne
  have hp3 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have hp0 : 0 < 2 ^ m := by positivity
  omega

/-- **Lemma 10.6 (certified indexed finite rank recipe over a duplicate-free list)**
[OpenAI2026LogSpace, Lemma 10.6]: computes `Finset.kthLargest k items.toFinset` over at most
`2 ^ (κ * d)` candidate streams with top-down comparator slope `coeffB = 6`, clock overshoot `4`,
and `O((κ + 1) * d)` slack/index overhead. -/
@[expose] noncomputable def rankListRecipe {Op : Type u} [DecidableEq Op] {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (items : List Op) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) :
    UniformStreamRecipe Op Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ x ∈ items.toFinset, IsNormSignedStream (env x))
    (fun val _ => kthLargest k items.toFinset val)
    (fun env _ => rankApprox k items.toFinset env)
    (rankListResProg k items) (5 * κ + 56) 6 4 (5 * κ + 56)
    (fun hV => by
      rw [abs_le]
      refine ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans kthLargest_nonneg, ?_⟩
      exact kthLargest_le zero_le_one fun x hx => (abs_le.mp (hV x hx).2).2)
    (fun hV => rankApprox_isScaledApprox k items.toFinset fun x hx => (hV x hx).1)
    (fun hV s => eval_rankListResProg k items hNodup s
      (fun x hx => (hV x (List.mem_toFinset.mpr hx)).1) _)
    (fun s env sEnv _ hev => by
      set idxBits := Nat.log 2 items.length + 2
      have hlog : Nat.log 2 items.length ≤ κ * d := log_two_le_of_le_two_pow hLen
      have hIdx : idxBits ≤ κ * d + 2 := Nat.add_le_add_right hlog 2
      have h56 : 56 ≤ 56 * d := Nat.le_mul_of_pos_right 56 hd
      have ha_split : (5 * κ + 56) * d = 5 * (κ * d) + 56 * d := by ring
      simp only [rankListResProg, QueryProg.activeQueries_bindOverhead, List.mem_append,
        List.mem_map] at hev
      rcases hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
      · obtain ⟨op, j, L, hj, hL, rfl⟩ :=
          mem_activeQueries_rankFoldProg k items (s + 4) idxBits items none env sEnv hev₀
        refine ⟨by have h4 := Nat.le_mul_of_pos_right 4 hd; omega, ?_⟩
        change (((idxBits + 4) + L : ℕ) : ℤ) ≤
          (((5 * κ + 56) * d : ℕ) : ℤ) + (6 : ℤ) * ((s : ℤ) - (j : ℤ))
        omega
      · cases hbest : (rankFoldProg k items (s + 4) idxBits items none).eval env sEnv with
        | none =>
          rw [hbest] at hev₁
          nomatch hev₁
        | some b =>
          rw [hbest, QueryProg.activeQueries_map] at hev₁
          obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg b 8 (s + 4) env sEnv hev₁
          refine ⟨by have h4 := Nat.le_mul_of_pos_right 4 hd; omega, ?_⟩
          change ((2 * 8 : ℕ) : ℤ) ≤
            (((5 * κ + 56) * d : ℕ) : ℤ) + (6 : ℤ) * ((s : ℤ) - (j : ℤ))
          omega)
    (fun s env sEnv => by
      simp only [rankListResProg]
      set idxBits := Nat.log 2 items.length + 2
      have hlog : Nat.log 2 items.length ≤ κ * d := log_two_le_of_le_two_pow hLen
      have hIdx : idxBits ≤ κ * d + 2 := Nat.add_le_add_right hlog 2
      have h56 : 56 ≤ 56 * d := Nat.le_mul_of_pos_right 56 hd
      have hInt_split : (5 * κ + 56) * (d + s) =
          5 * (κ * d) + 56 * d + 5 * (κ * s) + 56 * s := by ring
      refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
      · have hf := maxIntrinsicBits_rankFoldProg_le k items (s + 4) idxBits items none env sEnv
        omega
      · cases (rankFoldProg k items (s + 4) idxBits items none).eval env sEnv with
        | none =>
          simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
          omega
        | some b =>
          rw [QueryProg.maxIntrinsicBits_map]
          have hw := maxIntrinsicBits_windowPrefixModProg_le b 8 (s + 4) env sEnv
          omega)

/-- **Lemma 10.6 (`Finset` specification wrapper for `rankListRecipe`)**
[OpenAI2026LogSpace, Lemma 10.6]. Note that `Finset.toList` uses `Classical.choose` to pick an
arbitrary list ordering, so this wrapper is intended only for analytical `Finset` specifications;
machine-realizable log-space stages must pass a canonical duplicate-free list directly to
`rankListRecipe` (as in `rowCompressionNewDefaultRecipe` and `rowCompressionUpdateRecipe`). -/
@[expose] noncomputable def rankFinsetRecipe {Op : Type u} [DecidableEq Op] {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (s : Finset Op) (κ : ℕ) (hCard : s.card ≤ 2 ^ (κ * d)) :
    UniformStreamRecipe Op Struct :=
  have htoFinset : s.toList.toFinset = s := by
    ext x
    simp
  let raw := rankListRecipe (Struct := Struct) d hd k s.toList s.nodup_toList κ
    (by rwa [s.length_toList])
  (raw.weakenValid (fun env _ => ∀ x ∈ s, IsNormSignedStream (env x))
    (fun hV x hx => hV x (htoFinset ▸ hx))).congrTarget
    (fun val _ => kthLargest k s val)
    (fun _ => by
      change kthLargest k s.toList.toFinset _ = kthLargest k s _
      rw [htoFinset])

end RankRecipe

end Cslib.StreamArithmetic
