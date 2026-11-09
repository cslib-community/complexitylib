/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryCorrectness
public import CslibFrontier.Foundations.BooleanAnalysis.MobiusColorProduct
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryCorrectness
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Data.List.GetD

/-!
# Actual test-group coefficients factor test by test

The row evaluator streams subsets of the whole selected group. Its coefficient nevertheless
factors over individual tests because their incidence coordinates are disjoint. Prove this
factorization and instantiate it for every actual constructed row, without supplied scope or
coefficient identities. This is the test-side product in [OpenAI2026ETH], Lemma D.2, PDF p.56.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.subsetMobius_rowPolynomial`: factor the group
  coefficient over the actual listed tests.
* `Cslib.Circuits.Frontier.IncidenceNetwork.val_rowVertex_prod`: the actual row entry is the
  product of individual test coefficients in the actual truncated modular ring.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF p.56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString Polynomial Finset GaloisRingArith

private theorem monomialsIn_filter (test : List (List ℕ)) (t : ℕ) (T : Finset (ℕ × ℕ)) :
    monomialsIn test t (T.filter (fun p => p.1 = t)).toList = monomialsIn test t T.toList := by
  simp [monomialsIn]

/-- The whole-group Möbius coefficient factors over its disjoint test-incidence coordinates. -/
theorem subsetMobius_rowPolynomial (ℓ : ℕ) (tests : List (List (List ℕ)))
    (S : Finset (ℕ × ℕ)) (hS : ∀ p ∈ S, p.1 < tests.length) :
    subsetMobius (rowPolynomial ℓ tests) S =
      ∏ t ∈ range tests.length,
        subsetMobius (fun T => parityFactor ℓ (monomialsIn (tests.getD t []) t T.toList : ℤ))
          (S.filter fun p => p.1 = t) := by
  have h := subsetMobius_color_product (range tests.length) Prod.fst
    (fun t T => parityFactor ℓ (monomialsIn (tests.getD t []) t T.toList : ℤ)) S
    (fun p hp => mem_range.mpr (hS p hp))
  convert h using 1
  congr 1
  funext T
  simp only [rowPolynomial, monomialsIn_filter]
  rw [← List.map_coe_finRange_eq_range, List.map_map, ← Fin.prod_univ_def]
  rw [Finset.prod_range]
  rfl

private theorem first_lt_of_mem_pairInc {J g h : ℕ} {sys : List (List (List ℕ))}
    {p : ℕ × ℕ} (hp : p ∈ pairInc J sys g h) :
    p.1 < (List.residueClass J sys.length g).length := by
  obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
  simpa using List.snd_lt_of_mem_zipIdx hq

/-- The actual row procedure yields the product of the individual test coefficients, or zero
on invalid ranks. All selected-coordinate scope conditions are derived from its blocks. -/
theorem val_rowVertex_prod (P ℓ J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (g : ℕ) (bs : List Bool) :
    let tests := (List.residueClass J sys.length g).map (sys.getD · [])
    let blocks := rowBlocks J sys d g
    let S := (selected blocks (blockIndices blocks bs)).toFinset
    val P (truncFl ℓ) (incEntry (rowVertex P ℓ J sys d g).2 bs) =
      if validIndices blocks (blockIndices blocks bs) then
        ∏ t ∈ range tests.length, truncRingHom P ℓ
          (subsetMobius (fun T => parityFactor ℓ (monomialsIn (tests.getD t []) t T.toList : ℤ))
            (S.filter fun p => p.1 = t))
      else 0 := by
  dsimp only
  rw [val_rowVertex]
  split_ifs
  · rw [subsetMobius_rowPolynomial, map_prod]
    intro p hp
    have hs := (selected_sublist (rowBlocks J sys d g)
      (blockIndices (rowBlocks J sys d g) bs)).subset (List.mem_toFinset.mp hp)
    obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hs
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hb
    simpa using first_lt_of_mem_pairInc hp
  · rfl

end Cslib.Circuits.Frontier.IncidenceNetwork
