/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceParityCounter

/-! # Original CNF counts and all-candidate native parity resources -/

public section

namespace ComplexityTests.TensorNetworkIncidenceParityCounter

open Cslib Cslib.BitString Cslib.GenericRAM Cslib.Complexity
open Cslib.Circuits.Frontier.IncidenceNetwork Cslib.Logic.PL Cslib.Logic.PL.CNF

/-- One used bit and two declared bits: the unused bit must double the count. -/
example (N₀ : ℕ) : countParity 1 0 N₀ (2, [[(0, true)]]) = 2 := by
  rw [countParity_eq_modelCountOn (by simp) (by decide) (Or.inl (by decide))]
  decide

example (N₀ : ℕ) : countParity 1 0 N₀ (0, []) = 1 := by
  rw [countParity_eq_modelCountOn (by simp) (by decide) (Or.inl (by decide))]
  decide

/-- Contradiction is counted through the actual original-count theorem. -/
example (N₀ : ℕ) : countParity 1 0 N₀ (2, [[]]) = 0 := by
  rw [countParity_eq_modelCountOn (by simp) (by decide) (Or.inl (by decide))]
  decide

/-- Symbolic sizes above the cutoff exercise the parity domain, not the bounded fallback.
The theorem applies to every tested row list, including candidates discarded by greedy search. -/
example (n : ℕ) (hn : parityCutoff 1 0 ≤ n) {rows : List (List Bool)}
    (hlen : rows.length ≤ 6 * n)
    (hwt : ∀ r ∈ rows, r.count true ≤ initialRowWeightBound (Nat.clog 2 n ^ 0) 1)
    (hv : (CNF.vars ([[(0, true)]] : CNF ℕ)).toFinset ⊆ Finset.range n) :
    SubexponentialSAT.IncidenceBranching.IsSparseSystem 1 (paritySparsity 0) n
      (compileParitySystemBounded 1 [[(0, true)]] rows) := by
  have hn1 : 1 ≤ n := by
    have : 0 < parityCutoff 1 0 := by
      unfold parityCutoff
      exact Nat.two_pow_pos _
    omega
  apply compiledSystem_isSparse hn (by simpa using hn1)
  exact SparseCNFLeafCounter.isCompiledSparseSystem_compileParitySystemBounded
    (by simp) hv hlen hwt

/-- Rejected variable indices do not enter the expensive native solver. -/
example : validSparseSystem 1 1 (2, [[[2]]]) = false ∧
    uniformSparseCount 1 1 0 (2, [[[2]]]) = 0 := by
  have h : validSparseSystem 1 1 (2, [[[2]]]) = false := by decide
  exact ⟨h, by simp [uniformSparseCount, h]⟩

/-- Global callback resources are derived for one actual machine, including nonsparse inputs. -/
example : ∃ N₀ : ℕ, ∃ (cs : NativeCertificate (uniformSparseCount 1 6 N₀)
    encArrayInput Turing.MultiTapeTM.encNat) (D : ℕ), ∀ p : ArrayInput,
    cs.time p ≤ D * ((encArrayInput p).length + 1) ^ D *
      2 ^ (D * Nat.logLogSqrtLogScale p.1) ∧
    cs.space p ≤ D * ((encArrayInput p).length + 1) ^ D :=
  exists_uniformSparseCount_certificate 1 6 (by decide)

/-- Actual greedy-search certificates have global workspace bounds, without a counter oracle. -/
example : ∃ N₀ : ℕ, ∃ cs : NativeCertificate (countParity 1 0 N₀)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary encCNF)
      Turing.MultiTapeTM.encNat,
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ ∀ x,
      cs.space x ≤
        poly (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary encCNF x).length := by
  obtain ⟨N₀, _, cs, poly, _, _, hp, _, _, h⟩ := exists_countParity_certificate 1 0 (by decide)
  exact ⟨N₀, cs, poly, hp, fun x => (h x).1⟩

end ComplexityTests.TensorNetworkIncidenceParityCounter
