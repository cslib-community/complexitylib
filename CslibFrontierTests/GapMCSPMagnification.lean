/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.Magnification.GapMCSP
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Tests for Gap-MCSP magnification near linear size

Checks the hypothesis shape of `Cslib.MCSP.not_NP_subset_PPoly_of_gapMCSP_hard` (OPS Theorem 1.4):
separators for its thresholds always exist, so the hypothesis is a size lower bound, and a hardness
assumption for every `β` in an interval `(0, β₀)` supplies its `∀ᶠ β in 𝓝[>] 0` quantifier.
-/

namespace Cslib.MCSP.Tests.GapMCSPMagnification

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.MCSP Turing.MultiTapeTM
open Filter Topology

-- For every `β` and `n`, the slice of `MCSP[⌊2^{βn}⌋₊]` separates OPS's Gap-MCSP instance. The
-- hypothesis of Theorem 1.4 therefore bounds the size of separators that exist.
example (β : ℝ) (n : ℕ) :
    (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.yesSet (fun m : ℕ => ⌊(2 : ℝ) ^ (β * m) / (10 * m)⌋₊) →
        (GapMCSP.yesSet (fun m : ℕ => ⌊(2 : ℝ) ^ (β * m)⌋₊)).slice (2 ^ n) T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.noSet (fun m : ℕ => ⌊(2 : ℝ) ^ (β * m)⌋₊) →
        (GapMCSP.yesSet (fun m : ℕ => ⌊(2 : ℝ) ^ (β * m)⌋₊)).slice (2 ^ n) T = false) :=
  slice_yesSet_separates (by
    rw [show (10 * (n : ℝ)) = ((10 * n : ℕ) : ℝ) by push_cast; ring, Nat.floor_div_natCast]
    exact Nat.div_le_self _ _)

-- A hardness assumption for every `β ∈ (0, β₀)` gives the hypothesis of Theorem 1.4, and with it
-- `P ≠ NP`.
example {ε β₀ : ℝ} (hε : 0 < ε) (hβ₀ : 0 < β₀)
    (h : ∀ β ∈ Set.Ioo 0 β₀, ∀ N₀ : ℕ, ∃ n ≥ N₀, ∀ F : BooleanFunction (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.yesSet (fun m : ℕ => ⌊(2 : ℝ) ^ (β * m) / (10 * m)⌋₊) → F T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.noSet (fun m : ℕ => ⌊(2 : ℝ) ^ (β * m)⌋₊) → F T = false) →
      ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) < complexity interpretation (single F)) :
    P encBits ≠ NP encBits :=
  P_ne_NP_of_gapMCSP_hard hε (mem_of_superset (Ioo_mem_nhdsGT hβ₀) h)

-- The same hypothesis refutes `NP ⊆ P/poly`.
example {ε : ℝ} (hε : 0 < ε)
    (h : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), ∀ N₀ : ℕ, ∃ n ≥ N₀, ∀ F : BooleanFunction (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.yesSet (fun m : ℕ => ⌊(2 : ℝ) ^ (β * m) / (10 * m)⌋₊) → F T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈
        GapMCSP.noSet (fun m : ℕ => ⌊(2 : ℝ) ^ (β * m)⌋₊) → F T = false) →
      ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) < complexity interpretation (single F)) :
    ¬ (NP encBits ⊆ PPolyOn encBits) :=
  not_NP_subset_PPoly_of_gapMCSP_hard hε h

end Cslib.MCSP.Tests.GapMCSPMagnification
