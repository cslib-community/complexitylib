/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Hierarchy
import CslibFrontier.Computability.MCSP.AntiChecker.Oracle.PolyTime

/-!
# Tests for the anti-checker oracle language

Contradictory samples make a yes-query at power `1` and threshold `0`, because no function agrees
with both, and no samples make a no-query, because a constant function fits them. Under
`NP ⊆ P/poly`, a `P/poly` language agreeing with the anti-checker oracle gives a threshold oracle
for the greedy. One query is checked against the length formula.
-/

namespace CslibFrontierTests.AntiCheckerOracle

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Cslib.MCSP.AntiChecker
  Cslib.Complexity Turing.MultiTapeTM

-- Contradictory samples at one input are a yes-query at power `1` and threshold `0`.
example (n s : ℕ) (x : BitString n) :
    encQuery (Query.ofSamples n s 1 0 [(x, false), (x, true)]) ∈ antiCheckerOracle := by
  by_contra h
  obtain ⟨g, -, hg⟩ := encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff.1 h
  have h0 := hg (x, false) (by simp)
  have h1 := hg (x, true) (by simp)
  simp_all

-- No samples are a no-query at power `1` and threshold `0` for circuits with one gate: a constant
-- function fits them.
example (n : ℕ) : encQuery (Query.ofSamples n 1 1 0 []) ∉ antiCheckerOracle :=
  encQuery_ofSamples_one_zero_notMem_antiCheckerOracle_iff.2
    ⟨fun _ => true, mem_computableFunctions_iff_complexity_le.2 (complexity_const true).le,
      by simp⟩

-- Under `NP ⊆ P/poly`, a `P/poly` language agreeing with the anti-checker oracle is a threshold
-- oracle for the greedy at every positive power.
open scoped Classical in
example (hNP : NP encBits ⊆ PPolyOn encBits) (n s ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ O ∈ PPoly, IsThresholdOracle (validCertificates n s) (certificateFunction n s) ℓ
      (fun P u => decide (encQuery (Query.ofSamples n s ℓ u P) ∈ O)) := by
  obtain ⟨O, hO, h⟩ := exists_mem_PPoly_agrees_antiCheckerOracle hNP
  exact ⟨O, hO, isThresholdOracle_of_eq_true_iff hℓ fun P u => by
    rw [decide_eq_true_iff]
    exact h _⟩

-- A query with one sample on three inputs has `2 (3 + 2 + 4 + 5) + 4 + (4 · 3 + 5)` bits.
example (P : List (BitString 3 × Bool)) (hP : P.length = 1) :
    (encQuery (Query.ofSamples 3 2 4 5 P)).length = 49 := by
  rw [length_encQuery_ofSamples, hP]

end CslibFrontierTests.AntiCheckerOracle
