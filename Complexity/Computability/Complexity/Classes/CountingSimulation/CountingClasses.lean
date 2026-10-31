/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CeqP.Time
public import Complexity.Computability.Complexity.Classes.CountingSimulation.Separation
public import Complexity.Computability.Complexity.Classes.ModP.Time
import Complexity.Computability.Complexity.Classes.FunctionTime.Decide
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision

/-!
# Counting classes from exact counting in time `2 ^ O(T / √log T)`

For time-constructible `T` with `max n 2 ≤ T n`, every count in `Cslib.Complexity.SharpTIME enc T`
is computed exactly, in binary, within time `2 ^ (C T n / √⌊log₂ (T n)⌋)`
(`Cslib.Complexity.CountingSimulation.SharpTIME_subset_iUnion_FTIME_two_pow_div_sqrt_log_two`).
Decision classes defined by a polynomial-time test of such counts follow from this. The test reads
outputs of at most that many digits, so it runs within time polynomial in
`2 ^ (C T n / √⌊log₂ (T n)⌋)` (`Cslib.Complexity.setOf_mem_DTIME_of_mem_FTIME`), which is
`2 ^ (C' T n / √⌊log₂ (T n)⌋)` for a larger constant `C'`. Hence every problem decided by a
polynomial-time test of two counts in `SharpTIME enc T` lies in
`⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`
(`Cslib.Complexity.CountingSimulation.setOf_mem_iUnion_DTIME_of_mem_SharpTIME`). On bit strings,
every class of such problems is strictly contained in `DTIME[2 ^ T]`
(`Cslib.Complexity.CountingSimulation.ssubset_DTIME_two_pow_of_forall_mem_SharpTIME`), by the
separation of `Complexity.Computability.Complexity.Classes.CountingSimulation.Separation`.

Parity, a nonzero residue modulo a fixed `k` and equality of two counts are such tests. This gives
the containments and strict containments of `Cslib.Complexity.ParityTIME`,
`Cslib.Complexity.ModTIME` (for every fixed `k`) and `Cslib.Complexity.CeqTIME`. The bounds are on
time only; no polynomial workspace bound is claimed for these classes.

`NTIME`, `BPTIME` and `PPTIME` reduce in this library to counts of padded fair-coin strings
(`Cslib.Complexity.exists_acceptCount_of_mem_NTIME`), not to terminal-path counts, so they are not
derived here. Their strict containments in `DTIME[2 ^ T]` are in `CountingSimulation.Separation`.

## Main results

* `Cslib.Complexity.CountingSimulation.setOf_mem_iUnion_DTIME_of_mem_SharpTIME`: a polynomial-time
  test of two terminal-path counts.
* `Cslib.Complexity.CountingSimulation.ssubset_DTIME_two_pow_of_forall_mem_SharpTIME`: the strict
  containment of every class of such tests in `DTIME[2 ^ T]`.
* `ParityTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `ModTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `CeqTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`: the containments.
* `ParityTIME_ssubset_DTIME_two_pow`, `ModTIME_ssubset_DTIME_two_pow`,
  `CeqTIME_ssubset_DTIME_two_pow`: the strict containments in `DTIME[2 ^ T]`.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}

/-- The scale `2 ^ (C T n / √⌊log₂ (T n)⌋)` is monotone in the constant. -/
private theorem two_pow_div_sqrt_log_two_mono {C C' : ℕ} (h : C ≤ C') (n : ℕ) :
    2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) ≤ 2 ^ (C' * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.mul_le_mul_right _ h))

/-- **A polynomial-time test of two terminal-path counts in time `2 ^ O(T / √log T)`.** For
time-constructible `T` with `max n 2 ≤ T n`, counts `f` and `g` in `SharpTIME enc T` and a
polynomial-time test `rule` of binary pairs, the instances where `rule (f a, g a)` holds form a
problem in `⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`. -/
theorem setOf_mem_iUnion_DTIME_of_mem_SharpTIME (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) {f g : α → ℕ} (hf : f ∈ SharpTIME enc T)
    (hg : g ∈ SharpTIME enc T) {rule : ℕ × ℕ → Bool}
    (hrule : ComputableInPolyTime rule (encPair encNat encNat) encBool) :
    {a | rule (f a, g a) = true} ∈
      ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) := by
  obtain ⟨C₁, hf'⟩ :=
    Set.mem_iUnion.mp (SharpTIME_subset_iUnion_FTIME_two_pow_div_sqrt_log_two hT hTn hf)
  obtain ⟨C₂, hg'⟩ :=
    Set.mem_iUnion.mp (SharpTIME_subset_iUnion_FTIME_two_pow_div_sqrt_log_two hT hTn hg)
  set C := max C₁ C₂
  obtain ⟨e, he⟩ := setOf_mem_DTIME_of_mem_FTIME
    (FTIME_mono (two_pow_div_sqrt_log_two_mono (le_max_left C₁ C₂)) hf')
    (FTIME_mono (two_pow_div_sqrt_log_two_mono (le_max_right C₁ C₂)) hg') hrule
  -- `(2 ^ x + 1) ^ e ≤ 2 ^ e * 2 ^ (e * x)`
  refine Set.mem_iUnion.mpr ⟨e * C, DTIME_mono_of_le_mul_add (C := 2 ^ e) (fun n => ?_) he⟩
  have h1 : 1 ≤ 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) := Nat.one_le_two_pow
  calc (2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) + 1) ^ e
      ≤ (2 * 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n)))) ^ e := Nat.pow_le_pow_left (by omega) e
    _ = 2 ^ e * 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n)) * e) := by rw [mul_pow, ← pow_mul]
    _ ≤ 2 ^ e * 2 ^ (e * C * T n / Nat.sqrt (Nat.log 2 (T n))) := by
        refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) ?_)
        rw [mul_comm _ e, mul_assoc]
        exact Nat.mul_div_le_mul_div_assoc _ _ _
    _ ≤ _ := Nat.le_add_right _ _

/-- **Strict containment in `DTIME[2 ^ T]` of every class decided by tests of counts.** For
time-constructible `T` with `max n 2 ≤ T n`, every class of problems on bit strings, each decided
by a polynomial-time test of two counts in `SharpTIME encBits T`, is strictly contained in
`DTIME[2 ^ T]`. -/
theorem ssubset_DTIME_two_pow_of_forall_mem_SharpTIME {𝒞 : Set (Set (List Bool))}
    (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n)
    (h : ∀ A ∈ 𝒞, ∃ f ∈ SharpTIME encBits T, ∃ g ∈ SharpTIME encBits T, ∃ rule : ℕ × ℕ → Bool,
      ComputableInPolyTime rule (encPair encNat encNat) encBool ∧
        ∀ x, x ∈ A ↔ rule (f x, g x) = true) :
    𝒞 ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_subset_iUnion hT (fun n => (le_max_left _ _).trans (hTn n))
    fun A hA => by
      obtain ⟨f, hf, g, hg, rule, hrule, hA⟩ := h A hA
      rw [show A = {x | rule (f x, g x) = true} from Set.ext hA]
      exact setOf_mem_iUnion_DTIME_of_mem_SharpTIME hT hTn hf hg hrule

/-! ### Parity, modular and exact counting -/

private theorem computableInPolyTime_mod_ne_zero (k : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 % k ≠ 0))
      (encPair encNat encNat) encBool :=
  ComputableInPolyTime.decide_not (p := fun p : ℕ × ℕ => p.1 % k = 0)
    (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.fst encNat encNat).prod (ComputableInPolyTime.const k)))
      (ComputableInPolyTime.const 0))

private theorem computableInPolyTime_eq :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 = p.2)) (encPair encNat encNat) encBool :=
  ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst encNat encNat)
    (ComputableInPolyTime.snd encNat encNat)

/-- `Mod_kTIME[T]` problems are decided by tests of counts in `SharpTIME enc T`. -/
private theorem ModTIME_forall_mem_SharpTIME {k : ℕ} {A : Set α} (hA : A ∈ ModTIME k enc T) :
    ∃ f ∈ SharpTIME enc T, ∃ g ∈ SharpTIME enc T, ∃ rule : ℕ × ℕ → Bool,
      ComputableInPolyTime rule (encPair encNat encNat) encBool ∧
        ∀ x, x ∈ A ↔ rule (f x, g x) = true := by
  obtain ⟨f, hf, hA⟩ := hA
  exact ⟨f, hf, f, hf, _, computableInPolyTime_mod_ne_zero k, fun x => by simp [hA x]⟩

/-- `C₌TIME[T]` problems are decided by tests of counts in `SharpTIME enc T`. -/
private theorem CeqTIME_forall_mem_SharpTIME {A : Set α} (hA : A ∈ CeqTIME enc T) :
    ∃ f ∈ SharpTIME enc T, ∃ g ∈ SharpTIME enc T, ∃ rule : ℕ × ℕ → Bool,
      ComputableInPolyTime rule (encPair encNat encNat) encBool ∧
        ∀ x, x ∈ A ↔ rule (f x, g x) = true := by
  obtain ⟨f, hf, g, hg, hA⟩ := hA
  exact ⟨f, hf, g, hg, _, computableInPolyTime_eq, fun x => by simp [hA x]⟩

/-- **`Mod_kTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for every fixed `k` and
time-constructible `T` with `max n 2 ≤ T n`. -/
theorem ModTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (k : ℕ) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    ModTIME k enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  fun A hA => by
    obtain ⟨f, hf, g, hg, rule, hrule, hA⟩ := ModTIME_forall_mem_SharpTIME hA
    rw [show A = {x | rule (f x, g x) = true} from Set.ext hA]
    exact setOf_mem_iUnion_DTIME_of_mem_SharpTIME hT hTn hf hg hrule

/-- **`⊕TIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for time-constructible `T` with
`max n 2 ≤ T n`. -/
theorem ParityTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    ParityTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) := by
  rw [← ModTIME_two]
  exact ModTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two 2 hT hTn

/-- **`C₌TIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for time-constructible `T` with
`max n 2 ≤ T n`. -/
theorem CeqTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    CeqTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  fun A hA => by
    obtain ⟨f, hf, g, hg, rule, hrule, hA⟩ := CeqTIME_forall_mem_SharpTIME hA
    rw [show A = {x | rule (f x, g x) = true} from Set.ext hA]
    exact setOf_mem_iUnion_DTIME_of_mem_SharpTIME hT hTn hf hg hrule

/-- **`Mod_kTIME[T] ⊊ DTIME[2 ^ T]`** for every fixed `k` and time-constructible `T` with
`max n 2 ≤ T n`. -/
theorem ModTIME_ssubset_DTIME_two_pow (k : ℕ) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) : ModTIME k encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME hT hTn fun _ => ModTIME_forall_mem_SharpTIME

/-- **`⊕TIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem ParityTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    ParityTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n := by
  rw [← ModTIME_two]
  exact ModTIME_ssubset_DTIME_two_pow 2 hT hTn

/-- **`C₌TIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem CeqTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    CeqTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME hT hTn fun _ => CeqTIME_forall_mem_SharpTIME

end Cslib.Complexity.CountingSimulation
