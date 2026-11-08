/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralResources

/-! # Actual general-density counting: source resources, unused bits and rejected input -/

public section

namespace ComplexityTests.TensorNetworkIncidenceGeneralResources

open Cslib Cslib.BitString Cslib.GenericRAM Cslib.Complexity Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Circuits.Frontier.IncidenceNetwork Turing.MultiTapeTM

private def unit0 : CNF ℕ := [[(0, true)]]
/-- Quadratically many repeated unit clauses on a declared n-variable input. -/
def dense (n : ℕ) : CNF ℕ := List.replicate (n * n) [(0, true)]

private theorem dense_valid {n : ℕ} (hn : 1 ≤ n) : validDeclaredInput 2 n (dense n) = true := by
  apply validDeclaredInput_eq_true_iff.mpr
  constructor
  · intro c hc
    rw [(List.mem_replicate.mp hc).2]
    decide
  · intro v hv
    obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
    have heq : c = [(0, true)] := List.eq_of_mem_replicate hc
    rw [heq] at hb
    have hv0 : v = 0 := congrArg Prod.fst (List.mem_singleton.mp hb)
    exact Finset.mem_range.mpr (by omega)

private theorem dense_count {n : ℕ} (hn : 1 ≤ n) :
    (dense n).modelCountOn (Finset.range n) = 2 ^ (n - 1) := by
  have hn0 : n ≠ 0 := by omega
  have hmul : n * n ≠ 0 := Nat.mul_ne_zero hn0 hn0
  have heval : ∀ σ, (dense n).eval σ = unit0.eval σ := fun σ => by
    simp [dense, unit0, CNF.eval, hmul]
  have hsub : unit0.vars.toFinset ⊆ Finset.range n := by
    intro v hv
    have hv0 : v = 0 := by simpa [unit0, CNF.mem_vars] using hv
    exact Finset.mem_range.mpr (by omega)
  calc _ = unit0.modelCountOn (Finset.range n) := by simp only [CNF.modelCountOn, heval]
    _ = _ := by
      rw [CNF.modelCountOn_eq_mul_modelCount unit0 (Finset.range n) hsub, Finset.card_range,
        show unit0.numVars = 1 from by decide,
        show unit0.modelCount = 1 from by decide, Nat.mul_one]

/-- Unbounded clause-to-declared-variable density, repeated clauses and n-1 unused bits share
one actual machine and one source time/space bound. This is not an assumed leaf budget. -/
example : ∃ β N₀ Ncut : ℕ, ∃ cs : NativeCertificate (countGeneralParity 2 β N₀ Ncut)
    (encPair encUnary encCNF) encNat, ∃ C e A : ℕ, ∀ n, 20 ≤ n →
    countGeneralParity 2 β N₀ Ncut (n, dense n) = 2 ^ (n - 1) ∧
    (cs.time (n, dense n) : ℝ) ≤ (C : ℝ) * (n + n * n + 1 : ℕ) ^ e *
      (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n) ∧
    cs.space (n, dense n) ≤ C * (n + n * n + 1) ^ e := by
  obtain ⟨β, N₀, Ncut, cs, C, e, A, hcorrect, hresource⟩ :=
    exists_countGeneralParity_source_certificate 2 (by decide)
  refine ⟨β, N₀, Ncut, cs, C, e, A, fun n hn => ?_⟩
  have hv := dense_valid (by omega : 1 ≤ n)
  have hc := hcorrect (n, dense n)
  rw [ite_eq_left hv, dense_count (by omega : 1 ≤ n)] at hc
  exact ⟨hc, by simpa only [dense, List.length_replicate] using hresource n hn _ hv⟩

/-- The same certified implementation handles zero variables, contradiction, unused variables,
and invalid support. Invalid inputs do not invoke their occurring-support traversal clock. -/
example : ∃ β N₀ Ncut : ℕ,
    countGeneralParity 2 β N₀ Ncut (0, []) = 1 ∧
    countGeneralParity 2 β N₀ Ncut (0, [[]]) = 0 ∧
    countGeneralParity 2 β N₀ Ncut (2, unit0) = 2 ∧
    countGeneralParity 2 β N₀ Ncut (0, [[(65536, true)]]) = 0 := by
  obtain ⟨β, N₀, Ncut, _cs, _D, _hresource, hcorrect⟩ :=
    exists_countGeneralParity_sharp_certificate 2 (by decide)
  refine ⟨β, N₀, Ncut, ?_, ?_, ?_, ?_⟩
  all_goals rw [hcorrect]
  all_goals decide

/-- Unbounded invalid support at declared size zero is rejected with polynomial charged time.
The selected guard prevents charging its exponentially large occurring-support search clock. -/
example : ∃ β N₀ Ncut : ℕ, ∃ (cs : NativeCertificate (countGeneralParity 2 β N₀ Ncut)
    (encPair encUnary encCNF) encNat) (D : ℕ), ∀ m, 1 ≤ m →
    let φ : CNF ℕ := (List.range m).map fun v => [(v, true)]
    let L := (encPair encUnary encCNF (0, φ)).length
    countGeneralParity 2 β N₀ Ncut (0, φ) = 0 ∧
      cs.time (0, φ) ≤ D * (L + 1) ^ D ∧ cs.space (0, φ) ≤ D * (L + 1) ^ D := by
  obtain ⟨β, N₀, Ncut, cs, D, hresource, hcorrect⟩ :=
    exists_countGeneralParity_sharp_certificate 2 (by decide)
  refine ⟨β, N₀, Ncut, cs, D, fun m hm => ?_⟩
  let φ : CNF ℕ := (List.range m).map fun v => [(v, true)]
  have hmem : 0 ∈ φ.vars := CNF.mem_vars.mpr
    ⟨[(0, true)], List.mem_map.mpr ⟨0, List.mem_range.mpr hm, rfl⟩,
      true, List.mem_singleton_self _⟩
  have hv : validDeclaredInput 2 0 φ ≠ true := by
    intro h
    have := (validDeclaredInput_eq_true_iff.mp h).2 (List.mem_toFinset.mpr hmem)
    simp at this
  have hc := hcorrect (0, φ)
  simp only [hv, Bool.false_eq_true, ↓reduceIte] at hc
  exact ⟨hc, by simpa [Nat.logLogSqrtLogScale] using hresource (0, φ)⟩

end ComplexityTests.TensorNetworkIncidenceGeneralResources
