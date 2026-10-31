/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingSparsification
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# The counting-sparsification step with a captured runtime context

The counting-sparsification search (`Cslib.Complexity.CountingSparsify.step`) fixes its threshold
base `M` and its leaf counter `g` before the input. A single machine for Proposition 6.4
[OpenAI2026ETH] instead computes its parameters from the input: the threshold base from the
sparsification parameter, and the leaf counter's own parameters from the declared number of
variables (Section 6.4, printed pp. 43–44). This module carries a runtime context `c : C` beside
the search state: `Cslib.Complexity.CountingSparsify.stepWith θ K g` reads its thresholds `θ c` and
passes `c` to the leaf counter `g`, and never changes `c`.

The search state, its initialization `init` and its weighting and cap are those of the existing
search: the state records the number of variables occurring in the input, and the leaf counter's
contract is the occurring-support count `ψ.modelCount`. An externally declared number of variables
`N` lives in the context; accounting for the `N - φ.numVars` unused declared variables, and
normalizing any declared-`N` leaf count before it reaches the weighting, are left to the outer
wrapper.

For the thresholds `countingThreshold (MOf c)`, the context step is the existing step at base
`MOf c` with leaf counter `g (c, ·)`, at every iterate
(`Cslib.Complexity.CountingSparsify.iterate_stepWith_countingThreshold`), so the existing
correctness theorems apply pointwise. One step is computable within a polynomial in the encoded
context and state, plus the time and space of the leaf counter on a sparse head formula
(`Cslib.Complexity.CountingSparsify.exists_computableInO_stepWith`); the context is charged in
full, and the leaf counter's time and space are kept separate.

This module certifies one step only. The resource bound for a whole uniform search, the
outer wrapper for an externally declared count, and the assembly of Proposition 6.4 are separate.

The context step `Cslib.Complexity.CountingSparsify.stepWith` and its agreement lemmas live with
the search in `Complexity/Computability/Complexity/FineGrained/CountingSparsification.lean`; this
module certifies its resources.

## Main results

* `Cslib.Complexity.CountingSparsify.exists_computableInO_stepWith`: the time and space of one
  step.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 6.4,
  Proposition 6.4 (pp. 43–44) and Appendix A (pp. 44–47).
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM

namespace CountingSparsify

variable {C : Type}

section PolyTime

open ComputableInPolyTime

/-- Search states with a context, encoded as framed tuples: the context, the weighting count in
unary, the stack of formulas, and the accumulator in binary. -/
local notation "encX" encC =>
  encPair encC (encPair encUnary (encPair (encList encCNF) encNat))

variable {encC : C ↪ List Bool} {θ : C → ℕ → ℕ}

/-- Popping a sparse leaf and adding its weighted count is polynomial-time, keeping the context. -/
private theorem computableInPolyTime_leafUpdateWith :
    ComputableInPolyTime (fun p : (C × State) × ℕ => (p.1.1, leafUpdate p.1.2 p.2))
      (encPair (encX encC) encNat) (encX encC) := by
  have hvars := SAT.computableInPolyTime_distinctVars
  have heq : (fun p : (C × State) × ℕ => (p.1.1, leafUpdate p.1.2 p.2)) = fun p =>
      (p.1.1, (p.1.2.1, (p.1.2.2.1.tail,
        if !(decide (p.1.2.2.2 +
            2 ^ (p.1.2.1 - (p.1.2.2.1.headD []).distinctVars.length) * p.2 < 2 ^ p.1.2.1)) then
          2 ^ p.1.2.1
        else
          p.1.2.2.2 + 2 ^ (p.1.2.1 - (p.1.2.2.1.headD []).distinctVars.length) * p.2))) := by
    funext p
    simp only [leafUpdate, leafWeight, min_def, Bool.not_eq_true', decide_eq_false_iff_not,
      not_lt]
  rw [heq]
  unfold encCNF
  fun_prop

/-- Branching on the head formula is polynomial-time for runtime thresholds, keeping the context.
-/
private theorem computableInPolyTime_innerWith
    (hθ : ComputableInPolyTime (fun x : C × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encPair encC (encPair encUnary encUnary)) encBool) (K : ℕ) :
    ComputableInPolyTime (fun x : C × State =>
      (x.1, (x.2.1, (countingNext (θ x.1) K (x.2.2.1.headD []) false ::
        countingNext (θ x.1) K (x.2.2.1.headD []) true :: x.2.2.1.tail, x.2.2.2))))
      (encX encC) (encX encC) := by
  have h := computableInPolyTime_countingNextWith encNat hθ K
  have hH : ComputableInPolyTime (fun x : C × State => x.2.2.1.headD [])
      (encX encC) encCNF := by
    unfold encCNF
    fun_prop
  have hb (b : Bool) : ComputableInPolyTime
      (fun x : C × State => countingNext (θ x.1) K (x.2.2.1.headD []) b) (encX encC)
      (encList (encList (encPair encNat encBool))) := by
    simpa only [Function.comp_def] using
      h.comp ((fst encC _).prod (hH.prod (const b : ComputableInPolyTime _ _ encBool)))
  have h₀ := hb false
  have h₁ := hb true
  unfold encCNF
  fun_prop

/-- **The time and space of a context step**: a polynomial in the length of the encoded context
and state, plus the time (respectively space) of the leaf counter and a polynomial in the state and
counter output lengths when the head formula is sparse. -/
theorem exists_computableInO_stepWith
    (hθ : ComputableInPolyTime (fun x : C × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encPair encC (encPair encUnary encUnary)) encBool) (K : ℕ)
    {g : C × CNF ℕ → ℕ} {t s : C × CNF ℕ → ℕ}
    (hg : ComputableInO g (encPair encC encCNF) encNat t s) :
    ∃ d, ComputableInO (stepWith θ K g) (encX encC) (encX encC)
      (fun x => (((encX encC) x).length + 1) ^ d +
        if x.2.2.1.isEmpty = false ∧ isSparse (θ x.1) K (x.2.2.1.headD []) = true then
          t (x.1, x.2.2.1.headD []) +
            (((encX encC) x).length + (encNat (g (x.1, x.2.2.1.headD []))).length + 1) ^ d
        else 0)
      (fun x => (((encX encC) x).length + 1) ^ d +
        if x.2.2.1.isEmpty = false ∧ isSparse (θ x.1) K (x.2.2.1.headD []) = true then
          s (x.1, x.2.2.1.headD []) +
            (((encX encC) x).length + (encNat (g (x.1, x.2.2.1.headD []))).length + 1) ^ d
        else 0) := by
  have hH0 : ComputableInPolyTime (fun x : C × State => x.2.2.1.headD [])
      (encX encC) encCNF := by
    unfold encCNF
    fun_prop
  obtain ⟨dE, eE, hE⟩ := (show ComputableInPolyTime (fun x : C × State => x.2.2.1.isEmpty)
    (encX encC) encBool by unfold encCNF; fun_prop).exists_degree
  obtain ⟨dI, eI, hI⟩ := (id' (encIn := encX encC)).exists_degree
  have hS0 : ComputableInPolyTime
      (fun x : C × State => isSparse (θ x.1) K (x.2.2.1.headD [])) (encX encC) encBool := by
    simpa only [Function.comp_def] using
      (computableInPolyTime_isSparseWith encNat hθ K).comp ((fst encC _).prod hH0)
  obtain ⟨dS, eS, hS⟩ := hS0.exists_degree
  obtain ⟨dH, eH, hH⟩ := (show ComputableInPolyTime
      (fun x : C × State => (x.1, x.2.2.1.headD [])) (encX encC) (encPair encC encCNF) from
    (fst encC _).prod hH0).exists_degree
  obtain ⟨dN, eN, hN⟩ := (computableInPolyTime_innerWith hθ K).exists_degree
  obtain ⟨dU, eU, hU⟩ := (computableInPolyTime_leafUpdateWith (encC := encC)).exists_degree
  set D := dE + dI + dS + dH + dN + dU + 1
  have hE' := (hE.mono (d' := D) (e' := eE) (by omega) le_rfl).inO
  have hI' := (hI.mono (d' := D) (e' := eI) (by omega) le_rfl).inO
  have hS' := (hS.mono (d' := D) (e' := eS) (by omega) le_rfl).inO
  have hH' := (hH.mono (d' := D) (e' := eH) (by omega) le_rfl).inO
  have hN' := (hN.mono (d' := D) (e' := eN) (by omega) le_rfl).inO
  have hU' := (hU.mono (d' := D) (e' := eU) (by omega) le_rfl).inO
  have hleaf := hU'.comp (hI'.prod (hg.comp hH'))
  have h := hE'.ite hI' (hS'.ite hleaf hN')
  have heq : stepWith θ K g = fun x =>
      if x.2.2.1.isEmpty then x
      else if isSparse (θ x.1) K (x.2.2.1.headD []) then
        (x.1, leafUpdate x.2 (g (x.1, x.2.2.1.headD [])))
      else
        (x.1, (x.2.1, (countingNext (θ x.1) K (x.2.2.1.headD []) false ::
          countingNext (θ x.1) K (x.2.2.1.headD []) true :: x.2.2.1.tail, x.2.2.2))) := by
    funext x
    unfold stepWith
    split_ifs <;> rfl
  have hpair_le (x : C × State) (c : ℕ) :
      ((encPair (encX encC) encNat (x, c)).length + 1) ^ D ≤
        4 ^ D * (((encX encC) x).length + (encNat c).length + 1) ^ D := by
    rw [← mul_pow]
    refine Nat.pow_le_pow_left ?_ D
    simp only [length_encPair]
    omega
  rw [heq]
  refine ⟨D, h.mono (4 ^ D + 5) (fun x => ?_) (fun x => ?_)⟩ <;>
  · simp only [Function.comp_apply]
    have hp := hpair_le x (g (x.1, x.2.2.1.headD []))
    have h4D : 1 ≤ 4 ^ D := Nat.one_le_pow _ _ (by norm_num)
    generalize 4 ^ D = F at hp h4D ⊢
    generalize (((encX encC) x).length + 1) ^ D = P
    generalize t (x.1, x.2.2.1.headD []) = T
    generalize s (x.1, x.2.2.1.headD []) = S
    generalize (((encX encC) x).length + (encNat (g (x.1, x.2.2.1.headD []))).length + 1) ^ D = Q
      at hp ⊢
    generalize ((encPair (encX encC) encNat (x, g (x.1, x.2.2.1.headD []))).length + 1) ^ D = R
      at hp ⊢
    cases x.2.2.1.isEmpty <;>
      cases isSparse (θ x.1) K (x.2.2.1.headD []) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, and_true, and_false,
        Bool.true_eq_false] <;> nlinarith

end PolyTime

end CountingSparsify

end Cslib.Complexity
