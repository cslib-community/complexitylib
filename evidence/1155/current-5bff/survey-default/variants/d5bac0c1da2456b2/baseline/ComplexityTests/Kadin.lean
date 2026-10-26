/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BooleanHierarchy.Kadin
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Clients for Kadin's polynomial-hierarchy collapse theorem. -/

namespace ComplexityTests.Kadin

open Cslib.Complexity Turing.MultiTapeTM Polynomial

private abbrev sampleE : Set (List Bool × List Bool) :=
  {y | y.2.headD false = true}

private theorem sampleE_mem_NP : sampleE ∈ NP (encPair encBits encBits) :=
  ⟨0, fun x => x.1.2.headD false, by fun_prop, fun _ => by simp [sampleE]⟩

/-- The `kadinChain` built from a concrete `NP` language lies in `BH r` at every level `r`. -/
example (r : ℕ) :
    kadinChain encBits (1 : ℕ[X]) sampleE r ∈ BH (encPair encBits encBits) r :=
  kadinChain_mem_BH sampleE_mem_NP r

/-- The `allWordsIn` block predicate built from a concrete `NP` language lies in `NP`. -/
example (d : ℕ) :
    allWordsIn encBits (1 : ℕ[X]) sampleE d ∈ NP (encPair encBits encBits) :=
  allWordsIn_mem_NP sampleE_mem_NP d

/-- Concrete witness check: at level `2`, the two-bit word `[false, true]` belongs to
`kadinChain encBits 1 sampleE 2` because its second `1`-bit block `[true]` is in `sampleE` while its
first `1`-bit block `[false]` is not in `kadinChain encBits 1 sampleE 1`. -/
example : ([], [false, true]) ∈ kadinChain encBits (1 : ℕ[X]) sampleE 2 := by
  have hsplit : ([false, true] : List Bool) = [false] ++ [true] := rfl
  rw [hsplit]
  have h1 : ([false] : List Bool).length =
      (1 • (1 : ℕ[X])).eval (encBits ([] : List Bool)).length := by
    simp
  rw [mem_kadinChain_succ_append h1]
  refine ⟨rfl, ?_⟩
  have h0 : ([] : List Bool).length =
      (0 • (1 : ℕ[X])).eval (encBits ([] : List Bool)).length := by
    simp
  simpa [sampleE] using (mem_kadinChain_succ_append (E := sampleE) (y := [false]) h0).not.mpr
    (by simp [sampleE])

/-- Concrete witness check for `allWordsIn`: `[true, true]` has both `1`-bit blocks in `sampleE`. -/
example : ([], [true, true]) ∈ allWordsIn encBits (1 : ℕ[X]) sampleE 2 := by
  have hsplit : ([true, true] : List Bool) = [true] ++ [true] := rfl
  rw [hsplit]
  have h1 : ([true] : List Bool).length = (1 : ℕ[X]).eval (encBits ([] : List Bool)).length := by
    simp
  rw [mem_allWordsIn_succ_append h1]
  refine ⟨rfl, ?_⟩
  simpa using (mem_allWordsIn_succ_append (E := sampleE) (d := 0) (z := []) h1).mpr
    ⟨rfl, by simp [allWordsIn]⟩

/-- Every `BH` language over an arbitrary encoding polynomial-time many-one reduces to
`BH encBits`. -/
example (r : ℕ) :
    ∃ B ∈ BH encBits r,
      PolyTimeReducible (encPair encBits encBits) encBits
        (kadinChain encBits (1 : ℕ[X]) sampleE r) B :=
  exists_mem_BH_encBits_and_polyTimeReducible (kadinChain_mem_BH sampleE_mem_NP r)

/-- Kadin's level-3 collapse at a fixed instance encoding. -/
example {k : ℕ} (h : coBH (encPair encBits encBits) k ⊆ BH (encPair encBits encBits) k) :
    SigmaP 3 encBits = PiP 3 encBits :=
  SigmaP_three_eq_PiP_three_of_coBH_subset_BH h

/-- Kadin's full PH collapse from `coBH encBits k ⊆ BH encBits k`. -/
example {k : ℕ} (h : coBH encBits k ⊆ BH encBits k) :
    PH encBits = SigmaP 3 encBits :=
  PH_eq_SigmaP_three_of_coBH_subset_BH h

/-- Kadin's full PH collapse from `BH encBits (k + 1) = BH encBits k`. -/
example {k : ℕ} (h : BH encBits (k + 1) = BH encBits k) :
    PH encBits = SigmaP 3 encBits :=
  PH_eq_SigmaP_three_of_BH_succ_eq h

/-- Kadin's collapse from `DP encBits = coDP encBits`. -/
example (h : DP encBits = coDP encBits) :
    PH encBits = SigmaP 3 encBits :=
  PH_eq_SigmaP_three_of_DP_eq_coDP h

/-- Kadin's collapse from `SATUNSAT ∈ coDP`. -/
example (h : SATUNSAT ∈ coDP (encPair encCNF encCNF)) :
    PH encBits = SigmaP 3 encBits :=
  PH_eq_SigmaP_three_of_SATUNSAT_mem_coDP h

end ComplexityTests.Kadin
