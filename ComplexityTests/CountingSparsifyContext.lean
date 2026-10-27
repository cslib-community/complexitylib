/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.CountingSparsifyContext

/-!
# Tests for the counting-sparsification step with a captured runtime context
-/

namespace ComplexityTests.CountingSparsifyContext

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Cslib.Complexity
open Cslib.Complexity.CountingSparsify Turing.MultiTapeTM

/-- With the threshold base as the context, the context search is the existing search at that base,
so the existing correctness theorems apply to each input. -/
example (K k B M : ℕ) (g : ℕ × CNF ℕ → ℕ) (φ : CNF ℕ) :
    ((stepWith (fun c => countingThreshold c) K g)^[rounds B φ] (M, init k φ)).2.2.2 =
      search M K k B (fun ψ => g (M, ψ)) φ := by
  rw [iterate_stepWith_countingThreshold (Mof := fun c => c)]
  rfl

/-- The context is retained by the whole search. -/
example (θ : ℕ → ℕ → ℕ) (K : ℕ) (g : ℕ × CNF ℕ → ℕ) (i : ℕ) (x : ℕ × State) :
    ((stepWith θ K g)^[i] x).1 = x.1 :=
  iterate_stepWith_fst θ K g i x

/-- The context can hold an externally declared count `N` without changing the search: here the
context `(M, N)` supplies the base `M`, and `N` is only retained, for the outer wrapper. -/
example (K k B : ℕ) (g : (ℕ × ℕ) × CNF ℕ → ℕ) (M N : ℕ) (φ : CNF ℕ) :
    (stepWith (fun c => countingThreshold c.1) K g)^[rounds B φ] ((M, N), init k φ) =
      ((M, N), (step M K (fun ψ => g ((M, N), ψ)))^[rounds B φ] (init k φ)) :=
  iterate_stepWith_countingThreshold (fun c => c.1) K g (M, N) _ _

/-- On the empty formula the existing search counts one assignment, with any context. -/
example (N : ℕ) : ((stepWith (fun _ : ℕ => countingThreshold 2) 2 (fun x => x.2.modelCount))
    (N, init 2 [])).2.2.2 = 1 := by
  rw [stepWith_countingThreshold (Mof := fun _ => 2)]
  change (step 2 2 (fun ψ => ψ.modelCount) (init 2 [])).2.2 = 1
  decide

/-- One step for a runtime base `M` given in binary, with any leaf counter certificate. -/
example {g : ℕ × CNF ℕ → ℕ} {t s : ℕ × CNF ℕ → ℕ}
    (hg : ComputableInO g (encPair encNat encCNF) encNat t s) (K : ℕ) :
    ∃ d, ComputableInO (stepWith (fun c => countingThreshold c) K g)
      (encPair encNat (encPair encUnary (encPair (encList encCNF) encNat)))
      (encPair encNat (encPair encUnary (encPair (encList encCNF) encNat)))
      (fun x => ((encPair encNat (encPair encUnary (encPair (encList encCNF) encNat)) x).length +
          1) ^ d +
        if x.2.2.1.isEmpty = false ∧ isSparse (countingThreshold x.1) K (x.2.2.1.headD []) = true
        then t (x.1, x.2.2.1.headD []) +
          ((encPair encNat (encPair encUnary (encPair (encList encCNF) encNat)) x).length +
            (encNat (g (x.1, x.2.2.1.headD []))).length + 1) ^ d
        else 0)
      (fun x => ((encPair encNat (encPair encUnary (encPair (encList encCNF) encNat)) x).length +
          1) ^ d +
        if x.2.2.1.isEmpty = false ∧ isSparse (countingThreshold x.1) K (x.2.2.1.headD []) = true
        then s (x.1, x.2.2.1.headD []) +
          ((encPair encNat (encPair encUnary (encPair (encList encCNF) encNat)) x).length +
            (encNat (g (x.1, x.2.2.1.headD []))).length + 1) ^ d
        else 0) :=
  exists_computableInO_stepWith computableInPolyTime_countingThreshold_le_binary K hg

end ComplexityTests.CountingSparsifyContext
