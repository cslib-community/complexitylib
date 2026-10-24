/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.NP.Nondeterministic
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.PPT.Clock
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Probability.PMF.Map
import Mathlib.Data.Set.Finite.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Time classes

The three parametric time classes, each relative to an encoding `enc : α ↪ List Bool` of
instances, with a bound `t : ℕ → ℕ` of the length `n` of the encoded instance, up to constants
`c₁ * t n + c₂`:

* `Cslib.Complexity.DTIME enc t`: decided by a deterministic machine with a binary alphabet and
  finitely many states within time `O(t n)`, with any space bound (upstream
  `Turing.MultiTapeTM.DecidableInTimeAndSpace`) [Arora and Barak, Definition 1.12][AroraBarak09].
  This is the definition of the classes proposed upstream in cslib pull request #767, stated for
  encoded instances.
* `Cslib.Complexity.NTIME enc t`: decided by a nondeterministic machine within time `O(t n)`
  (`Turing.MultiTapeNTM.DecidesInTime`): every computation path of that length has halted, and the
  instance is a member exactly when some computation path halts with output `[true]`
  [Arora and Barak, Definition 2.5][AroraBarak09].
* `Cslib.Complexity.BPTIME enc t`: decided with bounded error by a fair-coin machine within time
  `O(t n)` (`Turing.MultiTapePTM.DecidesWithBoundedErrorInTime`): every run on `T` coins has
  halted, for the clock `T = c₁ * t n + c₂`, and the run outputs the right answer, `[true]` for
  members and `[false]` for the others, with probability at least `2 / 3`
  [Arora and Barak, Definition 7.2][AroraBarak09].

Each polynomial class of the library is the union of the corresponding classes of time
`O(n ^ k)`, as in the textbook [Arora and Barak, Definition 1.13, Theorem 2.6,
Definition 7.2][AroraBarak09]:
`P` (`Cslib.Complexity.mem_P_iff_exists_mem_DTIME`), `NP`
(`Cslib.Complexity.mem_NP_iff_exists_mem_NTIME`, through the machine characterisation
`Cslib.Complexity.mem_NP_iff_decidableInPolyTime`) and `BPP`
(`Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME`). For `BPP`, defined by polynomial-time
verifiers reading random strings, this is the characterisation by probabilistic machines: a
verifier is run on sampled coins by a fair-coin machine compiled with a halting polynomial clock
(`Cslib.Probability.IsPPTOn.exists_halting_machine`), and a fair-coin machine halting within `T`
steps is a verifier replaying `T` coins
(`Turing.MultiTapePTM.computableTidilyInPolyTime_runClosedCoins`).

## Timed reductions

A problem `B` decidable within time `O(t' m)` on instances of length `m` pulls back along a
function `g` computable within time `O(T a)` to a problem decidable within time
`O(T a + t' |encB (g a)|)` (`Cslib.Complexity.preimage_mem_DTIME`): compute `g a`, then decide
whether it is in `B`. A decider of `B` within time `O(t' m)` is first brought to the tidy form,
within time and space `O(t' m)`
(`Cslib.Complexity.computableInO_indicator_of_mem_DTIME`), in which computations compose.

## Main definitions

* `Cslib.Complexity.DTIME`, `Cslib.Complexity.NTIME`, `Cslib.Complexity.BPTIME`.
* `Turing.MultiTapePTM.DecidesWithBoundedErrorInTime`: bounded error within a clock.

## Main results

* `Cslib.Complexity.DTIME_mono_of_le_mul_add`: `DTIME` absorbs constant factors.
* `Cslib.Complexity.computableInO_indicator_of_mem_DTIME`: a decider within the
  same time and space bounds up to constants.
* `Cslib.Complexity.preimage_mem_DTIME`: `DTIME` under timed reductions.
* `Cslib.Complexity.DTIME_mono_of_eventually_le`, `Cslib.Complexity.NTIME_mono_of_eventually_le`,
  `Cslib.Complexity.BPTIME_mono_of_eventually_le`: the classes only depend on the bound eventually.
* `Cslib.Complexity.DTIME_subset_NTIME`: a deterministic machine is a nondeterministic machine.
* `Cslib.Complexity.mem_P_iff_exists_mem_DTIME`, `Cslib.Complexity.mem_NP_iff_exists_mem_NTIME`,
  `Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME`: the polynomial classes are unions of time
  classes.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib

variable {k : ℕ} {State : Type} {α : Type*}

/-- `machine` decides `A` with bounded error within `t`, relative to the encoding `enc`: on every
encoded instance `enc a`, every run of `t a` steps with fair coins has halted, and the run outputs
`[true]` if `a ∈ A`, and `[false]` otherwise, with probability at least `2 / 3`. -/
def DecidesWithBoundedErrorInTime (machine : MultiTapePTM k Bool State) (enc : α ↪ List Bool)
    (A : Set α) (t : α → ℕ) : Prop :=
  ∀ a, (∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom (t a) (machine.initialConfig (enc a)))).support,
      final.tapes.state = none) ∧
    2 / 3 ≤ ProbComp.eval (machine.runClosed (t a) (enc a)) [MultiTapeTM.indicator A a]

/-- Time bounds can be increased: a halted run ignores further coins. -/
theorem DecidesWithBoundedErrorInTime.mono {machine : MultiTapePTM k Bool State}
    {enc : α ↪ List Bool} {A : Set α} {t t' : α → ℕ}
    (h : machine.DecidesWithBoundedErrorInTime enc A t) (ht : ∀ a, t a ≤ t' a) :
    machine.DecidesWithBoundedErrorInTime enc A t' := fun a => by
  obtain ⟨hhalt, hprob⟩ := h a
  refine ⟨?_, ?_⟩
  · rw [machine.eval_runClosedConfigFrom_eq_of_halted _ (ht a) hhalt]
    exact hhalt
  · rwa [machine.eval_runClosed_eq_of_halted _ (ht a) hhalt]

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Filter

variable {α : Type*}

/-- A bound on all but finitely many arguments is a bound up to an additive constant. -/
private theorem exists_add_of_eventually_le {t₁ t₂ : ℕ → ℕ} (h : ∀ᶠ n in atTop, t₁ n ≤ t₂ n) :
    ∃ C, ∀ n, t₁ n ≤ t₂ n + C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨∑ n ∈ Finset.range N, t₁ n, fun n => ?_⟩
  rcases le_or_gt N n with h | h
  · have := hN _ h
    omega
  · have := Finset.single_le_sum (f := t₁) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr h)
    omega

/-- Linear bounds `c₁ * t n + c₂` absorb a bound that holds eventually. -/
private theorem exists_linear_of_eventually_le {t₁ t₂ : ℕ → ℕ} (h : ∀ᶠ n in atTop, t₁ n ≤ t₂ n)
    (c₁ c₂ : ℕ) : ∃ c₂', ∀ n, c₁ * t₁ n + c₂ ≤ c₁ * t₂ n + c₂' := by
  obtain ⟨C, hC⟩ := exists_add_of_eventually_le h
  refine ⟨c₁ * C + c₂, fun n => ?_⟩
  have := Nat.mul_le_mul_left c₁ (hC n)
  rw [Nat.mul_add] at this
  omega

/-! ### Deterministic time -/

/-- The problems decidable within time `O(t n)`, that is `c₁ * t n + c₂` for constants `c₁` and
`c₂`, on instances whose encoding under `enc` has length `n`, by a machine with a binary alphabet
and finitely many states, with any space bound
[Arora and Barak, Definition 1.12][AroraBarak09]. -/
def DTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ s : ℕ → ℕ,
    DecidableInTimeAndSpace A enc (fun a => c₁ * t (enc a).length + c₂) fun a => s (enc a).length}

/-- `DTIME` is monotone in the time bound. -/
theorem DTIME_mono {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    DTIME enc t₁ ⊆ DTIME enc t₂ := by
  rintro A ⟨c₁, c₂, s, hA⟩
  exact ⟨c₁, c₂, s, ComputableInTimeAndSpace.mono hA
    (fun a => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _) fun _ => le_rfl⟩

/-- `DTIME` only depends on the time bound eventually: the finitely many other values are absorbed
by the additive constant. -/
theorem DTIME_mono_of_eventually_le {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ}
    (h : ∀ᶠ n in atTop, t₁ n ≤ t₂ n) : DTIME enc t₁ ⊆ DTIME enc t₂ := by
  rintro A ⟨c₁, c₂, s, hA⟩
  obtain ⟨c₂', hc⟩ := exists_linear_of_eventually_le h c₁ c₂
  exact ⟨c₁, c₂', s, ComputableInTimeAndSpace.mono hA (fun a => hc _) fun _ => le_rfl⟩

/-- Every function of the instances is bounded by a function of the length of the encoded
instance: there are finitely many instances of each length. -/
private theorem exists_le_length (enc : α ↪ List Bool) (S : α → ℕ) :
    ∃ s : ℕ → ℕ, ∀ a, S a ≤ s (enc a).length := by
  classical
  have hfin (n : ℕ) : {a | (enc a).length = n}.Finite :=
    (List.finite_length_eq Bool n).preimage_embedding enc
  exact ⟨fun n => (hfin n).toFinset.sup S, fun a =>
    Finset.le_sup (f := S) ((hfin _).mem_toFinset.mpr rfl)⟩

/-- A Boolean function, computable within a time bound of the length of the encoded instance,
decides a problem within that time. -/
theorem setOf_mem_DTIME_of_computableInO {enc : α ↪ List Bool} {f : α → Bool}
    {T S : α → ℕ} {t : ℕ → ℕ} (h : Turing.MultiTapeTM.ComputableInO f enc encBool T S)
    (hT : ∀ a, T a ≤ t (enc a).length) : {a | f a = true} ∈ DTIME enc t := by
  have h := h.tidy
  obtain ⟨c, hc, -⟩ := h
  obtain ⟨s, hs⟩ := exists_le_length enc S
  refine ⟨c, c, fun n => c * (s n + 1), decidableInTimeAndSpace_iff.mpr ⟨f, ?_, fun a => Iff.rfl⟩⟩
  refine hc.computableInTimeAndSpace.mono (fun a => ?_) fun a => ?_
  · have := Nat.mul_le_mul_left c (hT a)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · exact Nat.mul_le_mul_left c (Nat.add_le_add_right (hs a) 1)

section TimedReductions

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}

/-- `DTIME` absorbs constant factors. -/
theorem DTIME_mono_of_le_mul_add {t₁ t₂ : ℕ → ℕ} {C : ℕ} (h : ∀ n, t₁ n ≤ C * t₂ n + C) :
    DTIME enc t₁ ⊆ DTIME enc t₂ := by
  rintro A ⟨c₁, c₂, s, hA⟩
  refine ⟨c₁ * C, c₁ * C + c₂, s, ComputableInTimeAndSpace.mono hA (fun a => ?_) fun _ => le_rfl⟩
  have := Nat.mul_le_mul_left c₁ (h (enc a).length)
  rw [Nat.mul_add, ← Nat.mul_assoc] at this
  omega

/-- A problem in `DTIME enc t` is decided by a machine computing its indicator within time
and space `O(t n)`, on instances whose encoding has length `n`. -/
theorem computableInO_indicator_of_mem_DTIME {A : Set α} {t : ℕ → ℕ}
    (h : A ∈ DTIME enc t) :
    Turing.MultiTapeTM.ComputableInO (indicator A) enc encBool (fun a => t (enc a).length)
      fun a => t (enc a).length := by
  have this : ComputableTidilyInO (indicator A) enc encBool (fun a => t (enc a).length) fun a => t
      (enc a).length := by
    obtain ⟨c₁, c₂, s, hA⟩ := h
    obtain ⟨g, hg, hgA⟩ := decidableInTimeAndSpace_iff.mp hA
    obtain ⟨c, hg⟩ := hg.exists_space_linear
    obtain ⟨d, hg⟩ := hg.exists_computableTidilyInTimeAndSpace
    rw [indicator_eq_iff.mpr hgA]
    refine .of_bounds hg ((2 + 3 * c) * (c₁ + c₂) + 3 * c + d + d * (c * (c₁ + c₂) + c + 1) + 1)
      (fun a => ?_) (fun a => ?_) fun a => ?_
    · set T := t (enc a).length
      have hu : c₁ * T + c₂ ≤ (c₁ + c₂) * (T + 1) := by nlinarith
      calc 2 * (c₁ * T + c₂) + 3 * (c * (c₁ * T + c₂) + c) + d
          = (2 + 3 * c) * (c₁ * T + c₂) + (3 * c + d) := by ring
        _ ≤ (2 + 3 * c) * ((c₁ + c₂) * (T + 1)) + (3 * c + d) * (T + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hu) (Nat.le_mul_of_pos_right _ (by omega))
        _ = ((2 + 3 * c) * (c₁ + c₂) + 3 * c + d) * (T + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · set T := t (enc a).length
      have hu : c₁ * T + c₂ ≤ (c₁ + c₂) * (T + 1) := by nlinarith
      calc d * (c * (c₁ * T + c₂) + c + 1)
          ≤ d * (c * ((c₁ + c₂) * (T + 1)) + (c + 1) * (T + 1)) :=
            Nat.mul_le_mul_left _ (by
              have := Nat.mul_le_mul_left c hu
              have : c + 1 ≤ (c + 1) * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
              omega)
        _ = d * (c * (c₁ + c₂) + c + 1) * (T + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · simp only [encBool_apply, List.length_singleton]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  simpa only [Turing.MultiTapeTM.computableInO_iff_computableTidilyInO] using this

/-- **`DTIME` under timed reductions.** If `B` is decidable within time `O(t' m)` on instances whose
encoding has length `m`, and `g` is computable within time `O(T a)`, then `g ⁻¹' B` is decidable
within time `O(t n)` on instances whose encoding has length `n`, as soon as `T a + t' |encB (g a)|`
is within `O(t |enc a|)`: compute `g a`, then decide whether it is in `B`. -/
theorem preimage_mem_DTIME {B : Set β} {t' t : ℕ → ℕ} {g : α → β} {T S : α → ℕ} {C : ℕ}
    (hB : B ∈ DTIME encB t') (hg : Turing.MultiTapeTM.ComputableInO g enc encB T S)
    (ht : ∀ a, T a + t' (encB (g a)).length ≤ C * t (enc a).length + C) :
    g ⁻¹' B ∈ DTIME enc t := by
  have hg := hg.tidy
  have h := (computableInO_indicator_of_mem_DTIME hB).tidy.comp hg
  have hset : g ⁻¹' B = {a | (indicator B ∘ g) a = true} := by
    ext a
    simp [indicator]
  rw [hset]
  exact DTIME_mono_of_le_mul_add (C := C) (fun _ => le_rfl)
    (setOf_mem_DTIME_of_computableInO (t := fun n => C * t n + C) (.of_tidy h) ht)

end TimedReductions

/-! ### Nondeterministic time -/

/-- The problems decidable within time `O(t n)`, that is `c₁ * t n + c₂` for constants `c₁` and
`c₂`, on instances whose encoding under `enc` has length `n`, by a nondeterministic machine with a
binary alphabet and finitely many states: every computation path of that many steps has halted,
and `a ∈ A` exactly when some computation path halts with output `[true]`
[Arora and Barak, Definition 2.5][AroraBarak09]. -/
def NTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, MultiTapeNTM.DecidableInTime A enc fun a => c₁ * t (enc a).length + c₂}

/-- `NTIME` is monotone in the time bound. -/
theorem NTIME_mono {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    NTIME enc t₁ ⊆ NTIME enc t₂ := by
  rintro A ⟨c₁, c₂, k, State, hfinite, ntm, hA⟩
  exact ⟨c₁, c₂, k, State, hfinite, ntm,
    hA.mono fun a => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _⟩

/-- `NTIME` only depends on the time bound eventually. -/
theorem NTIME_mono_of_eventually_le {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ}
    (h : ∀ᶠ n in atTop, t₁ n ≤ t₂ n) : NTIME enc t₁ ⊆ NTIME enc t₂ := by
  rintro A ⟨c₁, c₂, k, State, hfinite, ntm, hA⟩
  obtain ⟨c₂', hc⟩ := exists_linear_of_eventually_le h c₁ c₂
  exact ⟨c₁, c₂', k, State, hfinite, ntm, hA.mono fun a => hc _⟩

/-- **A deterministic machine is a nondeterministic machine**, with one computation path, which
accepts exactly when the deterministic machine halts with output `[true]`. -/
theorem DTIME_subset_NTIME {enc : α ↪ List Bool} {t : ℕ → ℕ} : DTIME enc t ⊆ NTIME enc t := by
  rintro A ⟨c₁, c₂, s, hA⟩
  obtain ⟨f, ⟨k, State, hfinite, tm, htm⟩, hf⟩ := decidableInTimeAndSpace_iff.mp hA
  refine ⟨c₁, c₂, k, State, hfinite, tm.toMultiTapeNTM, fun a => ?_⟩
  obtain ⟨⟨u, hhalt, hout⟩, htime, -⟩ := htm a
  refine ⟨htime, ?_⟩
  rw [hf a, MultiTapeNTM.accepts_iff_exists_time_eq (runsInTime_of_halted hhalt)]
  constructor
  · intro hfa
    refine ⟨MultiTapeNTM.ComputationPath.ofDeterministic tm (enc a) u, rfl, ?_⟩
    rw [MultiTapeTM.computationPath_last_eq_runFrom]
    change (tm.runFrom _ u).output = _
    rw [hout, hfa]
    rfl
  · rintro ⟨q, hq, hout'⟩
    rw [MultiTapeTM.computationPath_last_eq_runFrom, hq, hout] at hout'
    exact List.head_eq_of_cons_eq hout'

/-! ### Bounded-error probabilistic time -/

/-- The problems decidable with bounded error within time `O(t n)`, that is `c₁ * t n + c₂` for
constants `c₁` and `c₂`, on instances whose encoding under `enc` has length `n`, by a fair-coin
machine with a binary alphabet and finitely many states: every run of that many steps has halted,
and outputs the right answer with probability at least `2 / 3`
[Arora and Barak, Definition 7.2][AroraBarak09]. -/
def BPTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State),
      machine.DecidesWithBoundedErrorInTime enc A fun a => c₁ * t (enc a).length + c₂}

/-- `BPTIME` is monotone in the time bound. -/
theorem BPTIME_mono {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    BPTIME enc t₁ ⊆ BPTIME enc t₂ := by
  rintro A ⟨c₁, c₂, k, State, hfinite, machine, hA⟩
  exact ⟨c₁, c₂, k, State, hfinite, machine,
    hA.mono fun a => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _⟩

/-- `BPTIME` only depends on the time bound eventually. -/
theorem BPTIME_mono_of_eventually_le {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ}
    (h : ∀ᶠ n in atTop, t₁ n ≤ t₂ n) : BPTIME enc t₁ ⊆ BPTIME enc t₂ := by
  rintro A ⟨c₁, c₂, k, State, hfinite, machine, hA⟩
  obtain ⟨c₂', hc⟩ := exists_linear_of_eventually_le h c₁ c₂
  exact ⟨c₁, c₂', k, State, hfinite, machine, hA.mono fun a => hc _⟩

/-! ### The polynomial classes -/

/-- A bound `O(n ^ k)` is polynomially bounded. -/
private theorem polyBounded_linear_pow (enc : α ↪ List Bool) (c₁ c₂ k : ℕ) :
    PolyBounded (fun a => (enc a).length) fun a => c₁ * (enc a).length ^ k + c₂ :=
  .of_forall_le (c₁ + c₂) k fun a => by
    have h₁ : (enc a).length ^ k ≤ ((enc a).length + 1) ^ k :=
      Nat.pow_le_pow_left (Nat.le_succ _) k
    have h₂ : 1 ≤ ((enc a).length + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith

/-- **`P` is the union of the classes `DTIME (n ^ k)`**, the definition of `P` in the classes
proposed upstream [Arora and Barak, Definition 1.13][AroraBarak09]. -/
theorem mem_P_iff_exists_mem_DTIME {α : Type*} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ P enc ↔ ∃ k, A ∈ DTIME enc (· ^ k) := by
  constructor
  · intro hA
    obtain ⟨t, s, ⟨d, hd⟩, -, h⟩ := mem_P_iff_exists_decidableInTimeAndSpace.mp hA
    refine ⟨d, DTIME_mono_of_eventually_le hd ⟨1, 0, s, ?_⟩⟩
    simpa only [one_mul, add_zero] using h
  · rintro ⟨k, c₁, c₂, s, h⟩
    exact mem_P_of_decidableInTimeAndSpace (t := fun n => c₁ * n ^ k + c₂)
      (.of_forall_le (c₁ + c₂) k fun n => by
        have h₁ : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) k
        have h₂ : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
        nlinarith) h

/-- **`NP` is the union of the classes `NTIME (n ^ k)`**, through the characterisation of `NP` by
nondeterministic machines [Arora and Barak, Theorem 2.6][AroraBarak09]. -/
theorem mem_NP_iff_exists_mem_NTIME {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ NP enc ↔ ∃ k, A ∈ NTIME enc (· ^ k) := by
  rw [mem_NP_iff_decidableInPolyTime]
  constructor
  · rintro ⟨t, ht, k, State, hfinite, ntm, hA⟩
    obtain ⟨c, d, hle⟩ := ht.exists_le
    exact ⟨d, c * 2 ^ d, c, k, State, hfinite, ntm,
      hA.mono fun a => (hle a).trans (Nat.mul_add_one_pow_le_two_pow c d _)⟩
  · rintro ⟨d, c₁, c₂, hA⟩
    exact ⟨_, polyBounded_linear_pow enc c₁ c₂ d, hA⟩

/-! ### Bounded-error polynomial time -/

open Cslib.Probability
open scoped ENNReal

/-- A probability of at least `2 / 3` is a fraction of at least two thirds. -/
private theorem two_thirds_le_div_iff {c n : ℕ} :
    (2 / 3 : ℝ≥0∞) ≤ c / 2 ^ n ↔ 2 * 2 ^ n ≤ 3 * c := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ two_ne_zero))
    (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), div_eq_mul_inv, mul_right_comm,
    ← div_eq_mul_inv, ENNReal.div_le_iff (by norm_num) (by norm_num)]
  constructor
  · intro h
    have : ((2 * 2 ^ n : ℕ) : ℝ≥0∞) ≤ ((3 * c : ℕ) : ℝ≥0∞) := by
      push_cast
      rw [mul_comm (3 : ℝ≥0∞)]
      exact h
    exact_mod_cast this
  · intro h
    have : ((2 * 2 ^ n : ℕ) : ℝ≥0∞) ≤ ((3 * c : ℕ) : ℝ≥0∞) := by exact_mod_cast h
    push_cast at this
    rw [mul_comm (c : ℝ≥0∞)]
    exact this

/-- An injective map keeps the probability of the image of a value. -/
private theorem map_apply_of_injective {β γ : Type} {p : PMF β} {f : β → γ}
    (hf : Function.Injective f) (b : β) : p.map f (f b) = p b := by
  rw [PMF.map_apply, tsum_eq_single b fun x hx => ite_eq_right fun h => hx (hf h).symm,
    ite_eq_left rfl]

/-- The right answer of a bounded-error verifier, on at least two thirds of the random strings. -/
private theorem DecidesWithBoundedError.two_mul_le {α : Type} {enc : α ↪ List Bool}
    {p : Polynomial ℕ} {V : α × List Bool → Bool} {A : Set α}
    (h : DecidesWithBoundedError enc p V A) (a : α) :
    2 * 2 ^ p.eval (enc a).length ≤ 3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) →
      Bool => V (a, List.ofFn r) = MultiTapeTM.indicator A a).card := by
  by_cases ha : a ∈ A
  · simpa [MultiTapeTM.indicator, ha] using (h a).1 ha
  · simpa [MultiTapeTM.indicator, ha] using (h a).2 ha

/-- **`BPP` is the union of the classes `BPTIME (n ^ k)`** [Arora and Barak, Definition 7.2,
Section 7.1][AroraBarak09]: a polynomial-time verifier run on uniformly sampled random strings is
a fair-coin machine halting within a polynomial clock, and a fair-coin machine halting within the
clock `T` is a verifier replaying random strings of length `T`. -/
theorem mem_BPP_iff_exists_mem_BPTIME {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ BPP enc ↔ ∃ k, A ∈ BPTIME enc (· ^ k) := by
  rw [mem_BPP]
  constructor
  · rintro ⟨p, V, hV, hA⟩
    -- sample a random string and run the verifier on it
    let program (a : α) : ProbComp Bool :=
      (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length)
    have hcount : ComputableTidilyInPolyTime (fun a => p.eval (enc a).length) enc encUnary :=
      (ComputableTidilyInPolyTime.unary_eval p).comp
        (ComputableTidilyInPolyTime.encoding_length enc)
    have hprogram : IsPPTOn enc encBool program := hcount.sampleList.map_with hV
    obtain ⟨k, State, hfinite, machine, c, d, heval, hhalt⟩ := hprogram.exists_halting_machine
    refine ⟨d, c * 2 ^ d, c, k, State, hfinite, machine,
      MultiTapePTM.DecidesWithBoundedErrorInTime.mono (t := fun a => c * ((enc a).length + 1) ^ d)
        (fun a => ⟨hhalt (enc a), ?_⟩) fun a => Nat.mul_add_one_pow_le_two_pow c d _⟩
    rw [← heval a, show [MultiTapeTM.indicator A a] = encBool (MultiTapeTM.indicator A a) from rfl,
      map_apply_of_injective encBool.injective]
    simp only [program, ProbComp.eval_map, BitString.eval_sampleList]
    rw [BitString.uniformList_map_apply]
    exact two_thirds_le_div_iff.mpr (hA.two_mul_le a)
  · rintro ⟨d, c₁, c₂, k, State, hfinite, machine, hA⟩
    -- replay the coins
    refine ⟨Polynomial.C c₁ * Polynomial.X ^ d + Polynomial.C c₂,
      fun x => decide (machine.runClosedCoins x.2 (enc x.1) = [true]),
      .of_tidy (ComputableTidilyInPolyTime.decide_eq'
        ((MultiTapePTM.computableTidilyInPolyTime_runClosedCoins machine).comp
          ((ComputableTidilyInPolyTime.snd enc encBits).prod
            ((ComputableTidilyInPolyTime.of_eq (encMid := encBits) fun _ => rfl).comp
              (ComputableTidilyInPolyTime.fst enc encBits))))
        (ComputableTidilyInPolyTime.const [true])), fun a => ?_⟩
    have heval : (Polynomial.C c₁ * Polynomial.X ^ d + Polynomial.C c₂).eval (enc a).length =
        c₁ * (enc a).length ^ d + c₂ := by
      simp
    have hprob := (hA a).2
    rw [MultiTapePTM.eval_runClosed_eq_map_coins, BitString.uniformList_map_apply,
      two_thirds_le_div_iff] at hprob
    rw [heval]
    constructor
    · intro ha
      simpa [MultiTapeTM.indicator, ha] using hprob
    · intro ha
      refine hprob.trans (Nat.mul_le_mul_left 3 (Finset.card_le_card fun r => ?_))
      simp only [MultiTapeTM.indicator, ha, Finset.mem_filter, Finset.mem_univ, true_and,
        decide_eq_false_iff_not]
      intro hr
      rw [hr]
      decide

end Cslib.Complexity
