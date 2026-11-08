/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceParityResources
public import Complexity.Computability.Complexity.FineGrained.SharpCountingSchedule

/-!
# Disjoint general-density counting with actual native parity leaves

Compose the existing executable disjoint sparsification search at the source ceiling-square-root
schedule with the actual parity leaf counter. Normalize each declared leaf count to its occurring
support and restore unused original variables exactly once. Direct counting handles the fixed
exceptional-size prefix. The correctness theorem derives all leaf promises and accepts no
sparsifier/counter oracle.

This establishes unrestricted-density original-count correctness toward [ChenJiangZhu2027],
Lemma 3.2, using [OpenAI2026ETH], Appendix D.3, p. 57. The companion
`IncidenceGeneralResources` supplies the composed machine time/space certificate. Weighted
binary reconstruction and other source endpoints remain separate.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.GenericRAM Cslib.Complexity Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Logic.PL.ClauseSet.Sparsification CountingSparsify

/-- Actual source-schedule disjoint search, with bounded-size direct counting.
All parameters are fixed before the input; correctness below derives their sufficient choices. -/
@[expose] noncomputable def countGeneralParity (k β N₀ Ncut : ℕ) (x : ℕ × CNF ℕ) : ℕ :=
  if validDeclaredInput k x.1 x.2 then
    if x.1 < Ncut then ExhaustiveCountFallback.countCNFExhaustive x
    else searchDeclaredWith id
      (fun n => countingThresholdBase k (sharpSearchDivisor n)) sharpSearchDivisor k k
      (normalizeDeclaredLeaf id (countParity k β N₀)) x.1 x.2
  else 0

/-- Derive an actual unrestricted-density exact counter, with parameters fixed solely by width.
The native parity cutoff is arbitrary here: its correctness is already all-size. -/
theorem exists_countGeneralParity_eq_modelCountOn (k : ℕ) (hk : 2 ≤ k) :
    ∃ β Ncut : ℕ, ∀ N₀ n : ℕ, ∀ φ : CNF ℕ,
      (∀ clause ∈ φ, clause.length ≤ k) →
      φ.vars.toFinset ⊆ Finset.range n →
      countGeneralParity k β N₀ Ncut (n, φ) = φ.modelCountOn (Finset.range n) := by
  obtain ⟨β, N, hN⟩ := exists_sharp_leaf_density hk
  let Ncut := max N 1
  refine ⟨β, Ncut, fun N₀ n φ hw hv => ?_⟩
  have hvalid := validDeclaredInput_eq_true_iff.mpr ⟨hw, hv⟩
  simp only [countGeneralParity, hvalid, ↓reduceIte]
  split_ifs with hn
  · exact ExhaustiveCountFallback.countCNFExhaustive_eq_modelCountOn_range n φ
  · have hn1 : 1 ≤ n := (le_max_right _ _).trans (by omega : Ncut ≤ n)
    have hNn : N ≤ n := (le_max_left _ _).trans (by omega : Ncut ≤ n)
    have hk1 : 1 ≤ k := by omega
    refine searchDeclaredWith_eq_modelCountOn_of_normalized
      (NOf := id) (MOf := fun n => countingThresholdBase k (sharpSearchDivisor n))
      (BOf := sharpSearchDivisor) (K := k) (k := k) (p := n)
      (g := normalizeDeclaredLeaf id (countParity k β N₀))
      ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase k (sharpSearchDivisor n))) hk1
      (two_le_countingThresholdBase k (sharpSearchDivisor n)) (le_refl k)
      (sharp_countingTreeBound hk1 n) ?_ hw hv
    intro ψ _hNorm hwidth _hSparse hvars hlen
    simp only [id_eq] at hvars hlen ⊢
    apply normalizeDeclaredLeaf_eq_modelCount hvars
    apply countParity_eq_modelCountOn hwidth hvars
    apply Or.inl
    have hlen' : ψ.length ≤
        (occBound k (countingThresholdBase k (sharpSearchDivisor n)) + 1) * n :=
      hlen.trans (by nlinarith)
    exact hlen'.trans (Nat.mul_le_mul_right n (hN n hNn))

end Cslib.Circuits.Frontier.IncidenceNetwork
