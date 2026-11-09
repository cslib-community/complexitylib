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
import Complexity.Computability.Complexity.Classes.Constructible.Log
import Complexity.Computability.Complexity.Classes.FunctionTime.Decide
import Complexity.Computability.Complexity.Classes.SharpP.PaddedCount
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Foundations.Data.Nat.SqrtLog.Factor

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

`NTIME`, `BPTIME` and `PPTIME` are such classes too. The library reduces them to padded fair-coin
counts (`Cslib.Complexity.exists_acceptCount_of_mem_NTIME`), and padded counts at a linear clock
are `SharpTIME enc T` functions (`Cslib.Complexity.exists_clock_acceptCount_mem_SharpTIME`).
So `NTIME[T]` is a positivity test of one count, and `PPTIME[T]` and `BPTIME[T]` compare a count
`f` with the count `g = 2 ^ τ` of all coin strings by `g < 2 * f`
(`Cslib.Complexity.exists_mem_SharpTIME_of_mem_NTIME`,
`Cslib.Complexity.exists_mem_SharpTIME_of_mem_PPTIME`). Their strict containments in
`DTIME[2 ^ T]` are instances of the same separation.

**Sharper separations.** The separation also holds for tests of counts at a larger time `t`, as long
as `t / √⌊log₂ t⌋ = o(T)`. In particular, for a factor `h ≥ 1` with `h = o(√⌊log₂ T⌋)` and
`T * h` time-constructible, `NTIME[T h]`, `BPTIME[T h]`, `PPTIME[T h]`, `⊕TIME[T h]`,
`Mod_kTIME[T h]` and `C₌TIME[T h]` are strictly contained in `DTIME[2 ^ T]`; hence
`DTIME[2 ^ T] ⊄ NTIME[T h]`. The hypothesis `h = o(√⌊log₂ T⌋)` reads
`∀ C, ∀ᶠ n in atTop, C * h n ≤ √⌊log₂ (T n)⌋`. It is needed for every `C` because the constant
in the exponent of the counting simulation depends on the simulated machine, while the classes
absorb constant factors in time. A factor `h n = g (T n)` with `g m = o(√⌊log₂ m⌋)` qualifies,
since `T` tends to infinity. The fourth root `h = ⌊√⌊√⌊log₂ T⌋⌋⌋` is a concrete instance whose
time-constructibility is proved (`Cslib.Complexity.TimeConstructible.mul_sqrt_sqrt_log_two`).
So `NTIME`, `BPTIME` and `PPTIME` at time `T * ⌊√⌊√⌊log₂ T⌋⌋⌋` are strictly contained in
`DTIME[2 ^ T]` under the hypotheses of #2054 alone.

## Main results

* `Cslib.Complexity.CountingSimulation.setOf_mem_iUnion_DTIME_of_mem_SharpTIME`: a polynomial-time
  test of two terminal-path counts.
* `Cslib.Complexity.CountingSimulation.ssubset_DTIME_two_pow_of_forall_mem_SharpTIME`: the strict
  containment in `DTIME[2 ^ T]` of every class of such tests at a time `t` with
  `t / √⌊log₂ t⌋ = o(T)`.
* `Cslib.Complexity.CountingSimulation.ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_self`,
  `Cslib.Complexity.CountingSimulation.ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_mul`: its
  specializations to tests at time `T` and at time `T * h` for a factor `h = o(√⌊log₂ T⌋)`.
* `ParityTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `ModTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `CeqTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`: the containments.
* `ParityTIME_ssubset_DTIME_two_pow`, `ModTIME_ssubset_DTIME_two_pow`,
  `CeqTIME_ssubset_DTIME_two_pow`: the strict containments in `DTIME[2 ^ T]`.
* `NTIME_ssubset_DTIME_two_pow`, `BPTIME_ssubset_DTIME_two_pow`, `PPTIME_ssubset_DTIME_two_pow`:
  the strict containments of nondeterministic, bounded-error and majority time.
* `NTIME_mul_ssubset_DTIME_two_pow`, `BPTIME_mul_ssubset_DTIME_two_pow`,
  `PPTIME_mul_ssubset_DTIME_two_pow`, `ParityTIME_mul_ssubset_DTIME_two_pow`,
  `ModTIME_mul_ssubset_DTIME_two_pow`, `CeqTIME_mul_ssubset_DTIME_two_pow`: the strict
  containments at time `T * h` for `h = o(√⌊log₂ T⌋)`.
* `NTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow`,
  `BPTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow`,
  `PPTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow`: the strict containments at time
  `T * ⌊√⌊√⌊log₂ T⌋⌋⌋`.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Filter Turing.MultiTapeTM

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
time-constructible `T` with `n ≤ T n` and time-constructible `t` with `max n 2 ≤ t n` and
`t / √⌊log₂ t⌋ = o(T)`, every class of problems on bit strings, each decided by a polynomial-time
test of two counts in `SharpTIME encBits t`, is strictly contained in `DTIME[2 ^ T]`. -/
theorem ssubset_DTIME_two_pow_of_forall_mem_SharpTIME {𝒞 : Set (Set (List Bool))} {t : ℕ → ℕ}
    (hT : TimeConstructible T) (hTn : ∀ n, n ≤ T n) (ht : TimeConstructible t)
    (htn : ∀ n, max n 2 ≤ t n)
    (hTt : ∀ C, ∀ᶠ n in atTop, C * t n ≤ T n * Nat.sqrt (Nat.log 2 (t n)))
    (h : ∀ A ∈ 𝒞, ∃ f ∈ SharpTIME encBits t, ∃ g ∈ SharpTIME encBits t, ∃ rule : ℕ × ℕ → Bool,
      ComputableInPolyTime rule (encPair encNat encNat) encBool ∧
        ∀ x, x ∈ A ↔ rule (f x, g x) = true) :
    𝒞 ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_subset_iUnion hT hTn hTt fun A hA => by
    obtain ⟨f, hf, g, hg, rule, hrule, hA⟩ := h A hA
    rw [show A = {x | rule (f x, g x) = true} from Set.ext hA]
    exact setOf_mem_iUnion_DTIME_of_mem_SharpTIME ht htn hf hg hrule

/-- **Strict containment in `DTIME[2 ^ T]` of every class decided by tests of counts at time
`T`**: `ssubset_DTIME_two_pow_of_forall_mem_SharpTIME` at `t = T`. For time-constructible `T` with
`max n 2 ≤ T n`, every class of problems on bit strings, each decided by a polynomial-time test of
two counts in `SharpTIME encBits T`, is strictly contained in `DTIME[2 ^ T]`. -/
theorem ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_self {𝒞 : Set (Set (List Bool))}
    (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n)
    (h : ∀ A ∈ 𝒞, ∃ f ∈ SharpTIME encBits T, ∃ g ∈ SharpTIME encBits T, ∃ rule : ℕ × ℕ → Bool,
      ComputableInPolyTime rule (encPair encNat encNat) encBool ∧
        ∀ x, x ∈ A ↔ rule (f x, g x) = true) :
    𝒞 ⊂ DTIME encBits fun n => 2 ^ T n :=
  have hTn' : ∀ n, n ≤ T n := fun n => (le_max_left _ _).trans (hTn n)
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME hT hTn' hT hTn
    (fun C => (tendsto_atTop_mono hTn' tendsto_id).eventually
      (Nat.eventually_mul_le_mul_sqrt_log_two C)) h

/-- **Strict containment in `DTIME[2 ^ T]` of every class decided by tests of counts at time
`T * h`**: `ssubset_DTIME_two_pow_of_forall_mem_SharpTIME` at `t = T * h`. For time-constructible
`T` with `max n 2 ≤ T n` and a factor `h ≥ 1` with `h = o(√⌊log₂ T⌋)` and `T * h`
time-constructible, every class of problems on bit strings, each decided by a polynomial-time test
of two counts in `SharpTIME encBits (T * h)`, is strictly contained in `DTIME[2 ^ T]`. -/
theorem ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_mul {𝒞 : Set (Set (List Bool))}
    {h : ℕ → ℕ} (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n)
    (hTh : TimeConstructible fun n => T n * h n) (hh₁ : ∀ n, 1 ≤ h n)
    (hh : ∀ C, ∀ᶠ n in atTop, C * h n ≤ Nat.sqrt (Nat.log 2 (T n)))
    (h𝒞 : ∀ A ∈ 𝒞, ∃ f ∈ SharpTIME encBits (fun n => T n * h n),
      ∃ g ∈ SharpTIME encBits (fun n => T n * h n), ∃ rule : ℕ × ℕ → Bool,
        ComputableInPolyTime rule (encPair encNat encNat) encBool ∧
          ∀ x, x ∈ A ↔ rule (f x, g x) = true) :
    𝒞 ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME hT (fun n => (le_max_left _ _).trans (hTn n)) hTh
    (fun n => (hTn n).trans (Nat.le_mul_of_pos_right _ (hh₁ n)))
    (fun C => (hh C).mono fun n hn => Nat.mul_mul_le_mul_sqrt_log_two_mul (hh₁ n) hn) h𝒞

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
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_self hT hTn fun _ => ModTIME_forall_mem_SharpTIME

/-- **`⊕TIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem ParityTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    ParityTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n := by
  rw [← ModTIME_two]
  exact ModTIME_ssubset_DTIME_two_pow 2 hT hTn

/-- **`C₌TIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem CeqTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    CeqTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_self hT hTn fun _ => CeqTIME_forall_mem_SharpTIME

/-! ### Nondeterministic, bounded-error and majority time -/

private theorem computableInPolyTime_pos :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (0 < p.1)) (encPair encNat encNat) encBool :=
  ComputableInPolyTime.binary_lt' (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.fst encNat encNat)

private theorem computableInPolyTime_lt_two_mul :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.2 < 2 * p.1)) (encPair encNat encNat)
      encBool :=
  ComputableInPolyTime.binary_lt' (ComputableInPolyTime.snd encNat encNat)
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.fst encNat encNat))

/-- `NTIME[T]` problems are decided by tests of counts in `SharpTIME enc T`. -/
private theorem NTIME_forall_mem_SharpTIME (hT : TimeConstructible T) {A : Set α}
    (hA : A ∈ NTIME enc T) :
    ∃ f ∈ SharpTIME enc T, ∃ g ∈ SharpTIME enc T, ∃ rule : ℕ × ℕ → Bool,
      ComputableInPolyTime rule (encPair encNat encNat) encBool ∧
        ∀ x, x ∈ A ↔ rule (f x, g x) = true := by
  obtain ⟨f, hf, hA⟩ := exists_mem_SharpTIME_of_mem_NTIME hT hA
  exact ⟨f, hf, f, hf, _, computableInPolyTime_pos, fun x => by simp [hA x]⟩

/-- `PPTIME[T]` problems are decided by tests of counts in `SharpTIME enc T`. -/
private theorem PPTIME_forall_mem_SharpTIME (hT : TimeConstructible T) {A : Set α}
    (hA : A ∈ PPTIME enc T) :
    ∃ f ∈ SharpTIME enc T, ∃ g ∈ SharpTIME enc T, ∃ rule : ℕ × ℕ → Bool,
      ComputableInPolyTime rule (encPair encNat encNat) encBool ∧
        ∀ x, x ∈ A ↔ rule (f x, g x) = true := by
  obtain ⟨f, hf, g, hg, hA⟩ := exists_mem_SharpTIME_of_mem_PPTIME hT hA
  exact ⟨f, hf, g, hg, _, computableInPolyTime_lt_two_mul, fun x => by simp [hA x]⟩

/-- **`NTIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem NTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    NTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_self hT hTn fun _ => NTIME_forall_mem_SharpTIME hT

/-- **`BPTIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem BPTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    BPTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_self hT hTn fun _ hA =>
    PPTIME_forall_mem_SharpTIME hT (BPTIME_subset_PPTIME hA)

/-- **`PPTIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem PPTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    PPTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_self hT hTn fun _ => PPTIME_forall_mem_SharpTIME hT

/-! ### Sharper separations at time `T * h` for `h = o(√log T)`

Each statement takes a factor `h ≥ 1` with `h = o(√⌊log₂ T⌋)`, that is
`∀ C, ∀ᶠ n in atTop, C * h n ≤ √⌊log₂ (T n)⌋`, such that `T * h` is time-constructible. -/

/-- **`Mod_kTIME[T h] ⊊ DTIME[2 ^ T]`** for every fixed `k`, time-constructible `T` with
`max n 2 ≤ T n` and a factor `h ≥ 1` with `h = o(√⌊log₂ T⌋)` and `T h` time-constructible. -/
theorem ModTIME_mul_ssubset_DTIME_two_pow (k : ℕ) {h : ℕ → ℕ} (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) (hTh : TimeConstructible fun n => T n * h n)
    (hh₁ : ∀ n, 1 ≤ h n) (hh : ∀ C, ∀ᶠ n in atTop, C * h n ≤ Nat.sqrt (Nat.log 2 (T n))) :
    ModTIME k encBits (fun n => T n * h n) ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_mul hT hTn hTh hh₁ hh fun _ =>
    ModTIME_forall_mem_SharpTIME

/-- **`⊕TIME[T h] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n` and a factor
`h ≥ 1` with `h = o(√⌊log₂ T⌋)` and `T h` time-constructible. -/
theorem ParityTIME_mul_ssubset_DTIME_two_pow {h : ℕ → ℕ} (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) (hTh : TimeConstructible fun n => T n * h n)
    (hh₁ : ∀ n, 1 ≤ h n) (hh : ∀ C, ∀ᶠ n in atTop, C * h n ≤ Nat.sqrt (Nat.log 2 (T n))) :
    ParityTIME encBits (fun n => T n * h n) ⊂ DTIME encBits fun n => 2 ^ T n := by
  rw [← ModTIME_two]
  exact ModTIME_mul_ssubset_DTIME_two_pow 2 hT hTn hTh hh₁ hh

/-- **`C₌TIME[T h] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n` and a factor
`h ≥ 1` with `h = o(√⌊log₂ T⌋)` and `T h` time-constructible. -/
theorem CeqTIME_mul_ssubset_DTIME_two_pow {h : ℕ → ℕ} (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) (hTh : TimeConstructible fun n => T n * h n)
    (hh₁ : ∀ n, 1 ≤ h n) (hh : ∀ C, ∀ᶠ n in atTop, C * h n ≤ Nat.sqrt (Nat.log 2 (T n))) :
    CeqTIME encBits (fun n => T n * h n) ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_mul hT hTn hTh hh₁ hh fun _ =>
    CeqTIME_forall_mem_SharpTIME

/-- **`NTIME[T h] ⊊ DTIME[2 ^ T]`**, hence `DTIME[2 ^ T] ⊄ NTIME[T h]`, for time-constructible
`T` with `max n 2 ≤ T n` and a factor `h ≥ 1` with `h = o(√⌊log₂ T⌋)` and `T h`
time-constructible. -/
theorem NTIME_mul_ssubset_DTIME_two_pow {h : ℕ → ℕ} (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) (hTh : TimeConstructible fun n => T n * h n)
    (hh₁ : ∀ n, 1 ≤ h n) (hh : ∀ C, ∀ᶠ n in atTop, C * h n ≤ Nat.sqrt (Nat.log 2 (T n))) :
    NTIME encBits (fun n => T n * h n) ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_mul hT hTn hTh hh₁ hh fun _ =>
    NTIME_forall_mem_SharpTIME hTh

/-- **`BPTIME[T h] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n` and a factor
`h ≥ 1` with `h = o(√⌊log₂ T⌋)` and `T h` time-constructible. -/
theorem BPTIME_mul_ssubset_DTIME_two_pow {h : ℕ → ℕ} (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) (hTh : TimeConstructible fun n => T n * h n)
    (hh₁ : ∀ n, 1 ≤ h n) (hh : ∀ C, ∀ᶠ n in atTop, C * h n ≤ Nat.sqrt (Nat.log 2 (T n))) :
    BPTIME encBits (fun n => T n * h n) ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_mul hT hTn hTh hh₁ hh fun _ hA =>
    PPTIME_forall_mem_SharpTIME hTh (BPTIME_subset_PPTIME hA)

/-- **`PPTIME[T h] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n` and a factor
`h ≥ 1` with `h = o(√⌊log₂ T⌋)` and `T h` time-constructible. -/
theorem PPTIME_mul_ssubset_DTIME_two_pow {h : ℕ → ℕ} (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) (hTh : TimeConstructible fun n => T n * h n)
    (hh₁ : ∀ n, 1 ≤ h n) (hh : ∀ C, ∀ᶠ n in atTop, C * h n ≤ Nat.sqrt (Nat.log 2 (T n))) :
    PPTIME encBits (fun n => T n * h n) ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_mul hT hTn hTh hh₁ hh fun _ =>
    PPTIME_forall_mem_SharpTIME hTh

/-! ### The fourth root of the logarithm -/

/-- The fourth root `h = ⌊√⌊√⌊log₂ T⌋⌋⌋` meets the hypotheses of the separations at time `T * h`:
`T * h` is time-constructible, `1 ≤ h` and `h = o(√⌊log₂ T⌋)`. -/
private theorem sqrt_sqrt_log_two_factor (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    (TimeConstructible fun n => T n * Nat.sqrt (Nat.sqrt (Nat.log 2 (T n)))) ∧
      (∀ n, 1 ≤ Nat.sqrt (Nat.sqrt (Nat.log 2 (T n)))) ∧
      ∀ C, ∀ᶠ n in atTop,
        C * Nat.sqrt (Nat.sqrt (Nat.log 2 (T n))) ≤ Nat.sqrt (Nat.log 2 (T n)) :=
  ⟨hT.mul_sqrt_sqrt_log_two fun n => (le_max_right _ _).trans (hTn n),
    fun n => Nat.one_le_sqrt_sqrt_log_two ((le_max_right _ _).trans (hTn n)),
    fun C => (tendsto_atTop_mono (fun n => (le_max_left _ _).trans (hTn n)) tendsto_id).eventually
      (Nat.eventually_mul_sqrt_sqrt_log_two_le C)⟩

/-- **`NTIME[T ⌊√⌊√⌊log₂ T⌋⌋⌋] ⊊ DTIME[2 ^ T]`**, hence
`DTIME[2 ^ T] ⊄ NTIME[T ⌊√⌊√⌊log₂ T⌋⌋⌋]`, for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem NTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    NTIME encBits (fun n => T n * Nat.sqrt (Nat.sqrt (Nat.log 2 (T n)))) ⊂
      DTIME encBits fun n => 2 ^ T n := by
  obtain ⟨hTh, hh₁, hh⟩ := sqrt_sqrt_log_two_factor hT hTn
  exact NTIME_mul_ssubset_DTIME_two_pow hT hTn hTh hh₁ hh

/-- **`BPTIME[T ⌊√⌊√⌊log₂ T⌋⌋⌋] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with
`max n 2 ≤ T n`. -/
theorem BPTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    BPTIME encBits (fun n => T n * Nat.sqrt (Nat.sqrt (Nat.log 2 (T n)))) ⊂
      DTIME encBits fun n => 2 ^ T n := by
  obtain ⟨hTh, hh₁, hh⟩ := sqrt_sqrt_log_two_factor hT hTn
  exact BPTIME_mul_ssubset_DTIME_two_pow hT hTn hTh hh₁ hh

/-- **`PPTIME[T ⌊√⌊√⌊log₂ T⌋⌋⌋] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with
`max n 2 ≤ T n`. -/
theorem PPTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    PPTIME encBits (fun n => T n * Nat.sqrt (Nat.sqrt (Nat.log 2 (T n)))) ⊂
      DTIME encBits fun n => 2 ^ T n := by
  obtain ⟨hTh, hh₁, hh⟩ := sqrt_sqrt_log_two_factor hT hTn
  exact PPTIME_mul_ssubset_DTIME_two_pow hT hTn hTh hh₁ hh

end Cslib.Complexity.CountingSimulation
