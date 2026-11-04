/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.Output
public import Complexity.Foundations.Probability.HierarchyRankEnvironment

/-!
# The actual single-environment request as an uncentered output

The existing `normalizedRequest` is evaluated on its original source, terminal and usage
coordinates with all copy suffixes. Only the second signal is usage-masked; the first rank
uses the entire terminal-retained set. The preparation mean averages the same full environment.
The numerator and gate are the actual request parameters, including routed-bin cutoffs.
This identity assumes neither an output-error bound nor independence of raw/preparation children.
-/

public section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
variable {P J : ℕ} [Fact P.Prime]

/-- The actual request's second channel is the uncentered, narrower usage-masked mean. -/
@[expose] noncomputable def requestSignals {V : Type*} {k : ℕ}
    (ζ : ℝ) (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (raw prep : Environment P J → Matrix V V ℝ) (σ : Environment P J) (x y : V) (ν : Fin 2) : ℝ :=
  if ν=0 then raw σ x y/r.terminal.rate else
    ζ*(if r.usage.retains (channels D) σ (ident y) then
      rowSliceMean (fun τ v => r.source.retains (channels D) τ (ident v))
        (fun τ v => r.usage.retains (channels D) τ (ident v)) prep x y else 0)

/-- The exact same arbitrary-child normalized request, with raw terminal rank. -/
theorem normalizedRequest_eq_output {V : Type*} [Fintype V] {k : ℕ}
    (cutoff gate : ℝ → ℝ) (K : ℕ) {ζ : ℝ} (hζ : 0 < ζ)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : Admissible r) (raw prep : Environment P J → Matrix V V ℝ)
    (σ : Environment P J) (x y : V) :
    normalizedRequest D ident r cutoff gate K raw prep σ x y =
      if r.usage.retains (channels D) σ (ident y) then
        Matrix.FourthRootHierarchyParams.NormalizedRow.output cutoff gate ζ
          (requestSignals ζ D ident r raw prep σ x y 0)
          (requestSignals ζ D ident r raw prep σ x y 1)
          (firstRank {z | r.terminal.retains (channels D) σ (ident z)} K 0
            (requestSignals ζ D ident r raw prep σ x)) else 0 := by
  classical
  rw [normalizedRequest_formula D ident r hr]
  by_cases hy : r.usage.retains (channels D) σ (ident y)
  · simp only [hy, ↓reduceIte, requestSignals, Fin.isValue, one_ne_zero,
      Matrix.FourthRootHierarchyParams.NormalizedRow.output,
        Matrix.FourthRootHierarchyParams.NormalizedRow.clip, mul_div_cancel_left₀ _ hζ.ne',
      firstRank, max_eq_right kthLargest_nonneg, rowGate]
  · simp only [hy, ↓reduceIte]


end Matrix.HierarchyParams.H4RankEnvironment
