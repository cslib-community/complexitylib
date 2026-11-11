/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.Cycle
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Bounds.Basic

/-!
# Cycle-spectrum reduction and canonical hitting-time identities

Every fixed power of a map on a finite state type is determined by the eventual cycle length of
its argument: past the state-space cardinality, an exponent may be reduced modulo the cycle length
(`iterate_eq_card_add_mod`). The cycle length is recovered from the finite set of cycle lengths
(`cycleSpectrum`) by a divisibility test (`spectrum_test`, `cycleSpectrum_test`), and a permutation
is inverted by the power one below the cycle length (`perm_symm_eq_iterate`).

Given a linear order on the states, `canonicalTime f x` is the first time at which the trajectory
of `x` visits the least state of its eventual cycle (`canonicalCycle f x`). Off the cycles, one
step lowers `canonicalTime` by one (`canonicalTime_apply`). Past the transient depth, `f^[T] x` is
`f^[a] (canonicalCycle f x)` iff `a + canonicalTime f x ≡ T [MOD cycleLength f x]`
(`iterate_eq_canonical_iff`).

## Main definitions

* `Cslib.FunctionalGraph.cycleSpectrum`: the finite set of cycle lengths of `f`.

## Main results

* `Cslib.FunctionalGraph.iterate_add_cycleLength_mul`: adding whole cycles past the transient
  preserves the state.
* `Cslib.FunctionalGraph.iterate_eq_card_add_mod`: exponent reduction past `Fintype.card α`.
* `Cslib.FunctionalGraph.cycle_test_iff`, `Cslib.FunctionalGraph.spectrum_test`,
  `Cslib.FunctionalGraph.cycleSpectrum_test`: recovering `cycleLength f x` as the least candidate
  period dividing a return at `Fintype.card α`.
* `Cslib.FunctionalGraph.injective_cycle_test_iff`,
  `Cslib.FunctionalGraph.injective_spectrum_test`,
  `Cslib.FunctionalGraph.perm_symm_eq_iterate`: specializations to injective maps and permutations.
* `Cslib.FunctionalGraph.canonicalTime_apply`: one transient step decrements `canonicalTime`.
* `Cslib.FunctionalGraph.iterate_eq_canonical_iff`: characterization of states past the transient
  relative to `canonicalCycle`.

## References

* Adapted from lean/Proofs/{Spectrum,PhaseIdentities}.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

open Function

universe u

/-! ### Cycle-spectrum reduction -/

section Finite

variable {α : Type u} [Finite α] (f : α → α)

/-- Past the transient depth, adding whole multiples of the cycle length does not change the
state. -/
theorem iterate_add_cycleLength_mul (x : α) {a : ℕ} (ha : transientDepth f x ≤ a) (q : ℕ) :
    f^[a + cycleLength f x * q] x = f^[a] x := by
  have hp := (isPeriodicPt_cycleLength f x).mul_const q
  calc f^[a + cycleLength f x * q] x
      = f^[a - transientDepth f x]
          (f^[cycleLength f x * q] (f^[transientDepth f x] x)) := by
        rw [← iterate_add_apply, ← iterate_add_apply]
        congr 1
        omega
    _ = f^[a - transientDepth f x] (f^[transientDepth f x] x) := by rw [hp.eq]
    _ = f^[a] x := by
        rw [← iterate_add_apply]
        congr 1
        omega

end Finite

section Fintype

variable {α : Type u} [Fintype α] (f : α → α)

/-- **Spectrum reduction.** Every exponent `T` at least `Fintype.card α` can be replaced by
`Fintype.card α + (T - Fintype.card α) % cycleLength f x`. -/
theorem iterate_eq_card_add_mod (x : α) {T : ℕ} (hT : Fintype.card α ≤ T) :
    f^[T] x = f^[Fintype.card α + (T - Fintype.card α) % cycleLength f x] x := by
  have hd := (transientDepth_lt_card f x).le
  have h := iterate_add_cycleLength_mul f x
    (a := Fintype.card α + (T - Fintype.card α) % cycleLength f x) (by omega)
    ((T - Fintype.card α) / cycleLength f x)
  rw [← h]
  congr 1
  have := Nat.mod_add_div (T - Fintype.card α) (cycleLength f x)
  omega

/-- **The cycle-length divisibility test.** `f^[Fintype.card α + ℓ] x = f^[Fintype.card α] x`
holds iff `cycleLength f x ∣ ℓ`. -/
theorem cycle_test_iff (x : α) (ℓ : ℕ) :
    f^[Fintype.card α + ℓ] x = f^[Fintype.card α] x ↔ cycleLength f x ∣ ℓ := by
  rw [show Fintype.card α + ℓ = ℓ + Fintype.card α by omega, iterate_add_apply,
    ← minimalPeriod_iterate f x (transientDepth_lt_card f x).le,
    ← isPeriodicPt_iff_minimalPeriod_dvd]
  rfl

/-- The finite set of distinct cycle lengths of `f`. -/
noncomputable def cycleSpectrum : Finset ℕ :=
  Finset.univ.image (cycleLength f)

/-- Every cycle length belongs to the cycle spectrum. -/
theorem cycleLength_mem_cycleSpectrum (x : α) : cycleLength f x ∈ cycleSpectrum f :=
  Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- Every element of the cycle spectrum is positive. -/
theorem pos_of_mem_cycleSpectrum {ℓ : ℕ} (hℓ : ℓ ∈ cycleSpectrum f) : 0 < ℓ := by
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hℓ
  exact cycleLength_pos f y

/-- **The spectrum test.** Among any set `S` of positive candidates containing `cycleLength f x`,
the cycle length is the least element passing the return test at `Fintype.card α`. -/
theorem spectrum_test (S : Finset ℕ) (x : α) (hS : cycleLength f x ∈ S)
    (hpos : ∀ ℓ ∈ S, 0 < ℓ) :
    IsLeast {ℓ | ℓ ∈ S ∧ f^[Fintype.card α + ℓ] x = f^[Fintype.card α] x}
      (cycleLength f x) :=
  ⟨⟨hS, (cycle_test_iff f x _).mpr dvd_rfl⟩,
    fun ℓ ⟨hℓ, he⟩ => Nat.le_of_dvd (hpos ℓ hℓ) ((cycle_test_iff f x ℓ).mp he)⟩

/-- `cycleLength f x` is the least element of `cycleSpectrum f` passing the return test at
`Fintype.card α`. -/
theorem cycleSpectrum_test (x : α) :
    IsLeast {ℓ | ℓ ∈ cycleSpectrum f ∧ f^[Fintype.card α + ℓ] x = f^[Fintype.card α] x}
      (cycleLength f x) :=
  spectrum_test f _ x (cycleLength_mem_cycleSpectrum f x)
    (fun _ h => pos_of_mem_cycleSpectrum f h)

end Fintype

/-! ### Permutations and injective maps -/

section Perm

variable {α : Type u} [Finite α] (f : α → α)

/-- For an injective map, every state has transient depth zero. -/
theorem transientDepth_eq_zero_of_injective (hf : Injective f) (x : α) :
    transientDepth f x = 0 :=
  transientDepth_eq_zero_of_mem_periodicPts f (hf.mem_periodicPts x)

/-- For an injective map, the cycle length of `x` is the minimal period of `x`. -/
theorem cycleLength_eq_minimalPeriod_of_injective (hf : Injective f) (x : α) :
    cycleLength f x = minimalPeriod f x :=
  cycleLength_eq_minimalPeriod_of_mem_periodicPts f (hf.mem_periodicPts x)

/-- For an injective map, `f^[ℓ] x = x` holds iff `cycleLength f x ∣ ℓ`. -/
theorem injective_cycle_test_iff (hf : Injective f) (x : α) (ℓ : ℕ) :
    f^[ℓ] x = x ↔ cycleLength f x ∣ ℓ := by
  rw [cycleLength_eq_minimalPeriod_of_injective f hf, ← isPeriodicPt_iff_minimalPeriod_dvd]
  rfl

/-- The spectrum test for injective maps, without the shift by `Fintype.card α`. -/
theorem injective_spectrum_test (hf : Injective f) (S : Finset ℕ) (x : α)
    (hS : cycleLength f x ∈ S) (hpos : ∀ ℓ ∈ S, 0 < ℓ) :
    IsLeast {ℓ | ℓ ∈ S ∧ f^[ℓ] x = x} (cycleLength f x) :=
  ⟨⟨hS, (injective_cycle_test_iff f hf x _).mpr dvd_rfl⟩,
    fun ℓ ⟨hℓ, he⟩ =>
      Nat.le_of_dvd (hpos ℓ hℓ) ((injective_cycle_test_iff f hf x ℓ).mp he)⟩

/-- A permutation is inverted by the power one below the cycle length of its argument. -/
theorem perm_symm_eq_iterate (σ : Equiv.Perm α) (x : α) :
    σ.symm x = (⇑σ)^[cycleLength σ x - 1] x := by
  have hpos := cycleLength_pos σ x
  have h : (⇑σ)^[cycleLength σ x] x = x :=
    (injective_cycle_test_iff σ σ.injective x _).mpr dvd_rfl
  apply σ.injective
  rw [Equiv.apply_symm_apply, ← iterate_succ_apply' (⇑σ),
    Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne'), h]

end Perm

/-! ### Canonical hitting-time and phase identities -/

section PhaseIdentities

variable {α : Type u} [Finite α] [LinearOrder α] (f : α → α)

/-- **(P1)** One step from a transient state lowers `canonicalTime` by one. -/
theorem canonicalTime_apply (x : α) (hx : x ∉ periodicPts f) :
    canonicalTime f (f x) + 1 = canonicalTime f x := by
  have hc : canonicalCycle f (f x) = canonicalCycle f x := by
    simpa using canonicalCycle_iterate f x 1
  have hpos : 0 < canonicalTime f x := by
    rcases Nat.eq_zero_or_pos (canonicalTime f x) with h | h
    · have hs := canonicalTime_spec f x
      rw [h, iterate_zero_apply] at hs
      exact absurd (hs ▸ canonicalCycle_periodic f x) hx
    · exact h
  have hle1 : canonicalTime f x ≤ canonicalTime f (f x) + 1 := by
    have h : f^[canonicalTime f (f x) + 1] x = canonicalCycle f x := by
      rw [iterate_succ_apply, canonicalTime_spec, hc]
    exact Nat.find_min' (canonicalCycle_reachable f x) h
  have hle2 : canonicalTime f (f x) ≤ canonicalTime f x - 1 := by
    have h : f^[canonicalTime f x - 1] (f x) = canonicalCycle f (f x) := by
      rw [hc, ← iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
      exact canonicalTime_spec f x
    exact Nat.find_min' (canonicalCycle_reachable f (f x)) h
  omega

/-- **(P2)** Past the transient depth, `f^[T] x` is the state `a` steps after the least cyclic
state `canonicalCycle f x` iff `a + canonicalTime f x ≡ T [MOD cycleLength f x]`. -/
theorem iterate_eq_canonical_iff (x : α) {T : ℕ} (hT : transientDepth f x ≤ T) (a : ℕ) :
    f^[T] x = f^[a] (canonicalCycle f x) ↔
      a + canonicalTime f x ≡ T [MOD cycleLength f x] := by
  rw [← canonicalTime_spec f x, ← iterate_add_apply,
    iterate_eq_iterate_iff_modEq f x hT
      ((transientDepth_le_canonicalTime f x).trans (Nat.le_add_left _ _)),
    Nat.ModEq.comm]

end PhaseIdentities

end Cslib.FunctionalGraph
