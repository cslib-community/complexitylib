/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingSparsification
import CslibFrontier.Computability.Complexity.FineGrained.SearchStep
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

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
the search in `CslibFrontier/Computability/Complexity/FineGrained/CountingSparsification.lean`; this
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

variable {encC : C ↪ List Bool} {θ : C → ℕ → ℕ}

/-- Popping a sparse leaf and adding its weighted count is polynomial-time, keeping the context. -/
private theorem computableInPolyTime_leafUpdateWith :
    ComputableInPolyTime (fun p : (C × State) × ℕ => (p.1.1, leafUpdate p.1.2 p.2))
      (encPair (encPair encC encState) encNat) (encPair encC encState) := by
  have hctx : ComputableInPolyTime (fun p : (C × State) × ℕ => p.1.1)
      (encPair (encPair encC encState) encNat) encC := by
    fun_prop
  have hstate : ComputableInPolyTime (fun p : (C × State) × ℕ => (p.1.2, p.2))
      (encPair (encPair encC encState) encNat) (encPair encState encNat) := by
    fun_prop
  exact hctx.prod (computableInPolyTime_leafUpdate.comp hstate)

/-- Branching on the head formula is polynomial-time for runtime thresholds, keeping the context.
-/
private theorem computableInPolyTime_innerWith
    (hθ : ComputableInPolyTime (fun x : C × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encPair encC (encPair encUnary encUnary)) encBool) (K : ℕ) :
    ComputableInPolyTime (fun x : C × State =>
      (x.1, (x.2.1, (countingNext (θ x.1) K (x.2.2.1.headD []) false ::
        countingNext (θ x.1) K (x.2.2.1.headD []) true :: x.2.2.1.tail, x.2.2.2))))
      (encPair encC encState) (encPair encC encState) := by
  have h := computableInPolyTime_countingNextWith encNat hθ K
  have hH : ComputableInPolyTime (fun x : C × State => x.2.2.1.headD [])
      (encPair encC encState) encCNF := by
    unfold encCNF
    fun_prop
  have hb (b : Bool) : ComputableInPolyTime
      (fun x : C × State => countingNext (θ x.1) K (x.2.2.1.headD []) b) (encPair encC encState)
      (encList (encList (encPair encNat encBool))) := by
    simpa only [Function.comp_def] using
      h.comp ((fst encC _).prod (hH.prod (const b : ComputableInPolyTime _ _ encBool)))
  have h₀ := hb false
  have h₁ := hb true
  unfold encState encCNF
  fun_prop

/-- **The time and space of a context step**: a polynomial in the length of the encoded context
and state, plus the time (respectively space) of the leaf counter and a polynomial in the state and
counter output lengths when the head formula is sparse. The context and state are encoded as
`encPair encC encState`: the framed context followed by the search state. -/
theorem exists_computableInO_stepWith
    (hθ : ComputableInPolyTime (fun x : C × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encPair encC (encPair encUnary encUnary)) encBool) (K : ℕ)
    {g : C × CNF ℕ → ℕ} {t s : C × CNF ℕ → ℕ}
    (hg : ComputableInO g (encPair encC encCNF) encNat t s) :
    ∃ d, ComputableInO (stepWith θ K g) (encPair encC encState) (encPair encC encState)
      (fun x => ((encPair encC encState x).length + 1) ^ d +
        if x.2.2.1.isEmpty = false ∧ isSparse (θ x.1) K (x.2.2.1.headD []) = true then
          t (x.1, x.2.2.1.headD []) +
            ((encPair encC encState x).length + (encNat (g (x.1, x.2.2.1.headD []))).length + 1) ^ d
        else 0)
      (fun x => ((encPair encC encState x).length + 1) ^ d +
        if x.2.2.1.isEmpty = false ∧ isSparse (θ x.1) K (x.2.2.1.headD []) = true then
          s (x.1, x.2.2.1.headD []) +
            ((encPair encC encState x).length + (encNat (g (x.1, x.2.2.1.headD []))).length + 1) ^ d
        else 0) := by
  have hH : ComputableInPolyTime (fun x : C × State => (x.1, x.2.2.1.headD []))
      (encPair encC encState) (encPair encC encCNF) := by
    unfold encCNF
    fun_prop
  have hS : ComputableInPolyTime
      (fun x : C × State => isSparse (θ x.1) K (x.2.2.1.headD []))
      (encPair encC encState) encBool := by
    simpa only [Function.comp_def] using (computableInPolyTime_isSparseWith encNat hθ K).comp hH
  have h := exists_computableInO_searchStep
    (by unfold encState encCNF; fun_prop :
      ComputableInPolyTime (fun x : C × State => x.2.2.1.isEmpty) (encPair encC encState) encBool)
    hS hH (computableInPolyTime_innerWith hθ K) computableInPolyTime_leafUpdateWith hg
  -- the context step pulls its case split out of the context pair
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
  rw [heq]
  exact h

end PolyTime

end CountingSparsify

end Cslib.Complexity
