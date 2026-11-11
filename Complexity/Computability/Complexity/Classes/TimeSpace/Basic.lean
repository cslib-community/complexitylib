/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time
public import Complexity.Computability.Complexity.Classes.Space.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Simultaneous time and space classes

`Cslib.Complexity.TISP enc t s` consists of the problems that one machine with a binary alphabet
and finitely many states decides within time `c₁ * t n + c₂` and, simultaneously, within space
`c₁ * s n + c₂`, for constants `c₁` and `c₂`, on instances whose encoding under `enc` has length
`n` [Arora and Barak, Section 5.4][AroraBarak09]. The model is the one of `DTIME` and `DSPACE`:
the input tape is read-only, the output tape write-only, and space counts visited work-tape
cells, so sublinear space bounds are meaningful.

Since a machine visits at most one new cell per step, time bounds space, and `TISP enc t t` is
`DTIME enc t` (`Cslib.Complexity.TISP_self_eq_DTIME`).

## Main definitions

* `Cslib.Complexity.TISP`: simultaneous deterministic time and space classes.

## Main results

* `Cslib.Complexity.mem_TISP_iff_computableInO`: membership through the charged bounds of
  `Turing.MultiTapeTM.ComputableInO`.
* `Cslib.Complexity.TISP_mono`, `Cslib.Complexity.TISP_mono_of_le_mul_add`: monotonicity.
* `Cslib.Complexity.TISP_subset_DTIME`, `Cslib.Complexity.TISP_subset_DSPACE`,
  `Cslib.Complexity.TISP_self_eq_DTIME`: the relation to time and space classes.
* `Cslib.Complexity.compl_mem_TISP`: closure under complement.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The problems decidable by one machine within time `O(t n)` and space `O(s n)` simultaneously,
that is within time `c₁ * t n + c₂` and space `c₁ * s n + c₂` for constants `c₁` and `c₂`, on
instances whose encoding under `enc` has length `n`, with a binary alphabet and finitely many
states. Space counts visited work-tape cells. -/
def TISP (enc : α ↪ List Bool) (t s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, DecidableInTimeAndSpace A enc (fun a => c₁ * t (enc a).length + c₂)
    fun a => c₁ * s (enc a).length + c₂}

/-- Membership in `TISP` is computability of the indicator within the charged bounds
`O(t n)` and `O(s n)`. -/
theorem mem_TISP_iff_computableInO {t s : ℕ → ℕ} : A ∈ TISP enc t s ↔
    ComputableInO (indicator A) enc encBool (fun a => t (enc a).length)
      fun a => s (enc a).length := by
  constructor
  · rintro ⟨c₁, c₂, hA⟩
    obtain ⟨g, hg, hgA⟩ := decidableInTimeAndSpace_iff.mp hA
    rw [indicator_eq_iff.mpr hgA]
    refine ⟨c₁ + c₂ + 1, hg.mono (fun a => ?_) fun a => ?_, fun a => ?_⟩
    · nlinarith
    · nlinarith
    · simp only [encBool_apply, List.length_singleton]
      nlinarith
  · rintro ⟨c, hc, -⟩
    refine ⟨c, c, decidableInTimeAndSpace_iff.mpr ⟨indicator A, ?_, indicator_eq_iff.mp rfl⟩⟩
    exact hc.mono (fun a => (Nat.mul_succ _ _).le) fun a => (Nat.mul_succ _ _).le

/-- A Boolean function computable within time `O(T a)` and space `O(S a)` decides its `true` set
within any bounds `t` and `s` of the length of the encoded instance above `T` and `S`. -/
theorem setOf_mem_TISP_of_computableInO {f : α → Bool} {T S : α → ℕ} {t s : ℕ → ℕ}
    (h : ComputableInO f enc encBool T S) (hT : ∀ a, T a ≤ t (enc a).length)
    (hS : ∀ a, S a ≤ s (enc a).length) : {a | f a = true} ∈ TISP enc t s := by
  rw [mem_TISP_iff_computableInO, indicator_eq_iff.mpr fun a => Iff.rfl]
  exact h.mono 1 (fun a => by simpa using (hT a).trans (Nat.le_succ _))
    fun a => by simpa using (hS a).trans (Nat.le_succ _)

/-- `TISP` depends on both bounds only up to a constant factor and an additive constant. -/
theorem TISP_mono_of_le_mul_add {t₁ t₂ s₁ s₂ : ℕ → ℕ} {C : ℕ}
    (ht : ∀ n, t₁ n ≤ C * t₂ n + C) (hs : ∀ n, s₁ n ≤ C * s₂ n + C) :
    TISP enc t₁ s₁ ⊆ TISP enc t₂ s₂ := by
  rintro A ⟨c₁, c₂, hA⟩
  refine ⟨c₁ * C, c₁ * C + c₂, ComputableInTimeAndSpace.mono hA (fun a => ?_) fun a => ?_⟩
  · have := Nat.mul_le_mul_left c₁ (ht (enc a).length)
    rw [Nat.mul_add, ← Nat.mul_assoc] at this
    omega
  · have := Nat.mul_le_mul_left c₁ (hs (enc a).length)
    rw [Nat.mul_add, ← Nat.mul_assoc] at this
    omega

/-- `TISP` is monotone in both bounds. -/
theorem TISP_mono {t₁ t₂ s₁ s₂ : ℕ → ℕ} (ht : ∀ n, t₁ n ≤ t₂ n) (hs : ∀ n, s₁ n ≤ s₂ n) :
    TISP enc t₁ s₁ ⊆ TISP enc t₂ s₂ :=
  TISP_mono_of_le_mul_add (C := 1) (fun n => by have := ht n; omega) fun n => by
    have := hs n; omega

/-- Forgetting the space bound. -/
theorem TISP_subset_DTIME {t s : ℕ → ℕ} : TISP enc t s ⊆ DTIME enc t :=
  fun _ ⟨c₁, c₂, hA⟩ => ⟨c₁, c₂, fun n => c₁ * s n + c₂, hA⟩

/-- Forgetting the time bound. -/
theorem TISP_subset_DSPACE {t s : ℕ → ℕ} : TISP enc t s ⊆ DSPACE enc s :=
  fun _ ⟨c₁, c₂, hA⟩ => ⟨c₁, c₂, fun n => c₁ * t n + c₂, hA⟩

/-- A machine running within time `O(t n)` also runs within space `O(t n)`. -/
theorem DTIME_subset_TISP {t : ℕ → ℕ} : DTIME enc t ⊆ TISP enc t t := by
  rintro A ⟨c₁, c₂, s, hA⟩
  obtain ⟨c, hc⟩ := ComputableInTimeAndSpace.exists_space_linear hA
  have hsplit (T : ℕ) : (c * c₁ + c₁) * T + (c * c₂ + c + c₂) =
      (c * (c₁ * T + c₂) + c) + (c₁ * T + c₂) := by ring
  refine ⟨c * c₁ + c₁, c * c₂ + c + c₂, hc.mono (fun a => ?_) fun a => ?_⟩
  · rw [hsplit]
    exact Nat.le_add_left _ _
  · rw [hsplit]
    exact Nat.le_add_right _ _

/-- With equal bounds, simultaneous time and space is deterministic time. -/
theorem TISP_self_eq_DTIME {t : ℕ → ℕ} : TISP enc t t = DTIME enc t :=
  Set.Subset.antisymm TISP_subset_DTIME DTIME_subset_TISP

/-- `TISP` is closed under complement: negate the output. -/
theorem compl_mem_TISP {t s : ℕ → ℕ} (h : A ∈ TISP enc t s) : Aᶜ ∈ TISP enc t s := by
  rw [mem_TISP_iff_computableInO] at h ⊢
  have hc : indicator Aᶜ = fun a => !indicator A a :=
    indicator_eq_iff.mpr fun a => by by_cases ha : a ∈ A <;> simp [indicator, ha]
  rw [hc]
  exact ComputableInO.not' h

end Cslib.Complexity
