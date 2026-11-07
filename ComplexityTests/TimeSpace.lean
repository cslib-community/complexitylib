/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.Hierarchy.Polynomial
public import Complexity.Computability.Complexity.Classes.TimeSpace.Basic
public import Complexity.Computability.Complexity.Classes.TimeSpace.Slowdown
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming

/-! Simultaneous time and space classes, two-quantifier alternating time and the slowdown lemma
on concrete instances. Parity is in linear time and constant space, hence in `Σ₂TIME(n)` and in
`Σ₂ᵖ`. The deterministic polynomial time hierarchy gives a problem outside `TISP(n, n)`. The
slowdown lemma is instantiated at the exponents of the Arora–Barak time–space lower bound and at a
quadratic deterministic hypothesis. -/

public section

namespace ComplexityTests.TimeSpace

open Cslib.Complexity
open _root_.Turing _root_.Turing.MultiTapeTM

/-- Parity of the number of true input bits. -/
def oddOnes (word : List Bool) : Bool := word.foldl (fun b x => b ^^ x) false

example : oddOnes [true, false, true, true] = true ∧ oddOnes [true, true] = false := by decide

/-- Parity is decided in linear time and constant work space simultaneously. -/
theorem oddOnes_mem_TISP : {w | oddOnes w = true} ∈ TISP encBits id fun _ => 0 :=
  setOf_mem_TISP_of_computableInO
    (ComputableTidilyInO.foldl_bits_finite encBool (fun b x => b ^^ x) false).computableInO
    (fun _ => le_rfl) fun _ => le_rfl

example : {w | oddOnes w = true} ∈ DTIME encBits id := TISP_subset_DTIME oddOnes_mem_TISP

example : {w | oddOnes w = true}ᶜ ∈ TISP encBits id fun _ => 0 := compl_mem_TISP oddOnes_mem_TISP

/-- Some problem decidable in time `O((n + 1) ^ 2)` is not in `TISP((n + 1), (n + 1))`. -/
example : ∃ A ∈ DTIME encBits (fun n => (n + 1) ^ 2),
    A ∉ TISP encBits (fun n => n + 1) fun n => n + 1 := by
  obtain ⟨-, hnot⟩ := DTIME_succ_pow_ssubset_DTIME_succ_pow (a := 1) (b := 2) le_rfl one_lt_two
  obtain ⟨A, hA, hA'⟩ := Set.not_subset.mp hnot
  exact ⟨A, hA, fun h => hA' (by simpa using TISP_subset_DTIME h)⟩

/-- Parity is in `Σ₂TIME(n)`, through nondeterministic linear time. -/
theorem oddOnes_mem_SigmaTwoTIME : {w | oddOnes w = true} ∈ SigmaTwoTIME encBits id :=
  NTIME_subset_SigmaTwoTIME (DTIME_subset_NTIME (TISP_subset_DTIME oddOnes_mem_TISP))

/-- The complement of parity is in `Σ₂TIME(n)`, through co-nondeterministic linear time. -/
example : {w | oddOnes w = true}ᶜ ∈ SigmaTwoTIME encBits id :=
  compl_mem_SigmaTwoTIME (DTIME_subset_NTIME (TISP_subset_DTIME oddOnes_mem_TISP))

/-- Parity is in `Σ₂ᵖ`, through the bridge to the polynomial hierarchy. -/
example : {w | oddOnes w = true} ∈ SigmaP 2 encBits :=
  mem_SigmaP_two_iff_exists_mem_SigmaTwoTIME.mpr
    ⟨1, SigmaTwoTIME_mono (fun n => by simp) oddOnes_mem_SigmaTwoTIME⟩

/-- The slowdown lemma at the exponents of the Arora–Barak lower bound: if nondeterministic
linear time is in `TISP((n + 1) ^ (6 / 5), s)`, written `t' m ^ 5 ≤ C * (m + 1) ^ 6`, then
`Σ₂TIME((n + 1) ^ 40) ⊆ NTIME((n + 1) ^ 48)`. -/
example {t' s : ℕ → ℕ} {C : ℕ} (hN : NTIME encBits id ⊆ TISP encBits t' s)
    (ht' : ∀ m, t' m ^ 5 ≤ C * (m + 1) ^ 6) :
    SigmaTwoTIME encBits (fun n => (n + 1) ^ 40) ⊆ NTIME encBits (fun n => (n + 1) ^ 48) :=
  SigmaTwoTIME_succ_pow_subset_NTIME_succ_pow (hN.trans TISP_subset_DTIME) ht' (by omega)
    (by omega) (by omega) (by omega)

/-- The slowdown lemma at a quadratic deterministic hypothesis: `NTIME(n) ⊆ DTIME((n + 1) ^ 2)`
gives `Σ₂TIME((n + 1) ^ 2) ⊆ NTIME((n + 1) ^ 4)`. -/
example (hN : NTIME encBits id ⊆ DTIME encBits fun m => (m + 1) ^ 2) :
    SigmaTwoTIME encBits (fun n => (n + 1) ^ 2) ⊆ NTIME encBits (fun n => (n + 1) ^ 4) :=
  SigmaTwoTIME_succ_pow_subset_NTIME_succ_pow (p := 2) (q := 1) (C := 1) hN
    (fun m => by simp) (by omega) le_rfl (by omega) (by omega)

end ComplexityTests.TimeSpace
