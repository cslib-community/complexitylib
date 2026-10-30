/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.PPT.Clock
import Complexity.Computability.Probabilistic.Sampling

/-!
# Unbounded-error probabilistic time

`Cslib.Complexity.PPTIME enc t` consists of the problems decided by strict majority within time
`O(t n)`, that is `c₁ * t n + c₂` for constants `c₁` and `c₂`, by a fair-coin machine with a
binary alphabet and finitely many states (`Turing.MultiTapePTM.DecidesByMajorityInTime`): every
run on that many coins has halted, and `a ∈ A` exactly when the run outputs `[true]` with
probability more than `1 / 2` [Gill][Gill1977]. It is the unbounded-error counterpart of
`Cslib.Complexity.BPTIME`, with the same machines and clocks.

A fair-coin machine draws one coin per live step, so its acceptance probability within the clock
`t` is the number of accepting coin strings of length `t` divided by `2 ^ t`. Deciding by majority
is therefore the comparison `2 ^ t < 2 * count` of that count, an `Cslib.Complexity.acceptCount`
of the coin replay `Turing.MultiTapePTM.runClosedCoins`
(`Turing.MultiTapePTM.decidesByMajorityInTime_iff`).

`PP` (`Cslib.Complexity.PP`) is defined through polynomial-time verifiers reading random strings.
It is the union of the classes `PPTIME (n ^ k)` (`Cslib.Complexity.mem_PP_iff_exists_mem_PPTIME`),
by the argument for `BPP` and `BPTIME` (`Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME`): a
verifier run on sampled coins is a fair-coin machine with a halting polynomial clock, and a
fair-coin machine halting within `T` steps is a verifier replaying `T` coins. A bounded-error
decider decides by majority (`Cslib.Complexity.BPTIME_subset_PPTIME`).

## Main definitions

* `Turing.MultiTapePTM.DecidesByMajorityInTime`: strict majority within a clock.
* `Cslib.Complexity.PPTIME`: unbounded-error probabilistic time.

## Main results

* `Turing.MultiTapePTM.decidesByMajorityInTime_iff`: the majority condition as a count of
  accepting coin strings.
* `Cslib.Complexity.PPTIME_mono`: `PPTIME` is monotone in the time bound.
* `Cslib.Complexity.BPTIME_subset_PPTIME`: bounded error is a strict majority.
* `Cslib.Complexity.mem_PP_iff_exists_mem_PPTIME`: `PP` is the union of the classes
  `PPTIME (n ^ k)`.

## References

* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib
open scoped ENNReal

variable {k : ℕ} {State : Type} {α : Type*}

/-- `machine` decides `A` by strict majority within `t`, relative to the encoding `enc`: on every
encoded instance `enc a`, every run of `t a` steps with fair coins has halted, and `a ∈ A` exactly
when the run outputs `[true]` with probability more than `1 / 2` [Gill][Gill1977]. -/
def DecidesByMajorityInTime (machine : MultiTapePTM k Bool State) (enc : α ↪ List Bool)
    (A : Set α) (t : α → ℕ) : Prop :=
  ∀ a, (∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom (t a) (machine.initialConfig (enc a)))).support,
      final.tapes.state = none) ∧
    (a ∈ A ↔ 1 / 2 < ProbComp.eval (machine.runClosed (t a) (enc a)) [true])

/-- Time bounds can be increased: a halted run ignores further coins. -/
theorem DecidesByMajorityInTime.mono {machine : MultiTapePTM k Bool State}
    {enc : α ↪ List Bool} {A : Set α} {t t' : α → ℕ}
    (h : machine.DecidesByMajorityInTime enc A t) (ht : ∀ a, t a ≤ t' a) :
    machine.DecidesByMajorityInTime enc A t' := fun a => by
  obtain ⟨hhalt, hmem⟩ := h a
  refine ⟨?_, ?_⟩
  · rw [machine.eval_runClosedConfigFrom_eq_of_halted _ (ht a) hhalt]
    exact hhalt
  · rwa [machine.eval_runClosed_eq_of_halted _ (ht a) hhalt]

/-- A probability `c / 2 ^ n` exceeds one half exactly when `2 ^ n < 2 * c`. -/
private theorem half_lt_div_iff {c n : ℕ} :
    (1 / 2 : ℝ≥0∞) < c / 2 ^ n ↔ 2 ^ n < 2 * c := by
  have h2n : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2n' : (2 : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl h2n) (Or.inl h2n'), one_div, mul_comm,
    ← div_eq_mul_inv, ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
    show ((c : ℝ≥0∞) * 2) = ((2 * c : ℕ) : ℝ≥0∞) by push_cast; ring,
    show ((2 : ℝ≥0∞) ^ n) = ((2 ^ n : ℕ) : ℝ≥0∞) by push_cast; rfl]
  exact Nat.cast_lt

/-- **Deciding by majority is a count comparison.** A fair-coin machine decides `A` by strict
majority within `t` exactly when, on every instance, every run has halted by the clock and
`a ∈ A` exactly when more than half of the coin strings of length `t a` make the coin replay
`Turing.MultiTapePTM.runClosedCoins` output `[true]`. -/
theorem decidesByMajorityInTime_iff {machine : MultiTapePTM k Bool State}
    {enc : α ↪ List Bool} {A : Set α} {t : α → ℕ} :
    machine.DecidesByMajorityInTime enc A t ↔ ∀ a,
      (∀ final ∈ (ProbComp.eval
        (machine.runClosedConfigFrom (t a) (machine.initialConfig (enc a)))).support,
        final.tapes.state = none) ∧
      (a ∈ A ↔ 2 ^ t a < 2 * Complexity.acceptCount
        (fun x : List Bool × List Bool => decide (machine.runClosedCoins x.2 x.1 = [true]))
        (enc a) (t a)) := by
  refine forall_congr' fun a => and_congr_right' (iff_congr Iff.rfl ?_)
  rw [eval_runClosed_eq_map_coins, BitString.uniformList_map_apply, ← half_lt_div_iff]
  simp only [Complexity.acceptCount, decide_eq_true_eq]

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM
open Cslib.Probability
open scoped ENNReal

variable {α : Type*}

/-- The problems decidable by strict majority within time `O(t n)`, that is `c₁ * t n + c₂` for
constants `c₁` and `c₂`, on instances whose encoding under `enc` has length `n`, by a fair-coin
machine with a binary alphabet and finitely many states: every run of that many steps has halted,
and `a ∈ A` exactly when the run outputs `[true]` with probability more than `1 / 2`
[Gill][Gill1977]. -/
def PPTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State),
      machine.DecidesByMajorityInTime enc A fun a => c₁ * t (enc a).length + c₂}

/-- `PPTIME` is monotone in the time bound. -/
theorem PPTIME_mono {enc : α ↪ List Bool} {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    PPTIME enc t₁ ⊆ PPTIME enc t₂ := by
  rintro A ⟨c₁, c₂, k, State, hfinite, machine, hA⟩
  exact ⟨c₁, c₂, k, State, hfinite, machine,
    hA.mono fun a => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _⟩

/-- **Bounded error is a strict majority**: a machine outputting the right answer with probability
at least `2 / 3` outputs `[true]` with probability at least `2 / 3` on members, and at most `1 / 3`
on the others. -/
theorem BPTIME_subset_PPTIME {enc : α ↪ List Bool} {t : ℕ → ℕ} :
    BPTIME enc t ⊆ PPTIME enc t := by
  rintro A ⟨c₁, c₂, k, State, hfinite, machine, hA⟩
  refine ⟨c₁, c₂, k, State, hfinite, machine, fun a => ⟨(hA a).1, ?_⟩⟩
  have hprob := (hA a).2
  set p := ProbComp.eval (machine.runClosed (c₁ * t (enc a).length + c₂) (enc a))
  have hhalf : (1 / 2 : ℝ≥0∞) < 2 / 3 := by
    refine (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp ?_
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  by_cases ha : a ∈ A
  · simp only [MultiTapeTM.indicator, ha, ↓reduceIte] at hprob
    exact iff_of_true ha (hhalf.trans_le hprob)
  · simp only [MultiTapeTM.indicator, ha, ↓reduceIte] at hprob
    refine iff_of_false ha fun hlt => ?_
    -- the outputs `[true]` and `[false]` together have probability at most one
    have hsum : p [true] + p [false] ≤ 1 := by
      calc p [true] + p [false] = ∑ x ∈ {[true], [false]}, p x := by
            rw [Finset.sum_pair (by simp)]
        _ ≤ ∑' x, p x := sum_le_tsum _
        _ = 1 := p.tsum_coe
    have h1 : (1 / 2 : ℝ≥0∞) + 1 / 2 < p [true] + 1 / 2 :=
      ENNReal.add_lt_add_right (by norm_num) hlt
    rw [ENNReal.add_halves] at h1
    exact (h1.trans_le ((add_le_add le_rfl (hhalf.le.trans hprob)).trans hsum)).false

/-- **`PP` is the union of the classes `PPTIME (n ^ k)`** [Gill][Gill1977]: a polynomial-time
verifier run on uniformly sampled random strings is a fair-coin machine halting within a
polynomial clock, and a fair-coin machine halting within the clock `T` is a verifier replaying
random strings of length `T`. -/
theorem mem_PP_iff_exists_mem_PPTIME {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ PP enc ↔ ∃ k, A ∈ PPTIME enc (· ^ k) := by
  rw [mem_PP]
  constructor
  · rintro ⟨p, V, hV, hA⟩
    -- sample a random string and run the verifier on it
    let program (a : α) : ProbComp Bool :=
      (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length)
    have hcount : ComputableInPolyTime (fun a => p.eval (enc a).length) enc encUnary :=
      (ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length enc)
    have hprogram : IsPPTOn enc encBool program := hcount.sampleList.map_with hV
    obtain ⟨k, State, hfinite, machine, c, d, heval, hhalt⟩ := hprogram.exists_halting_machine
    refine ⟨d, c * 2 ^ d, c, k, State, hfinite, machine,
      MultiTapePTM.DecidesByMajorityInTime.mono (t := fun a => c * ((enc a).length + 1) ^ d)
        (fun a => ⟨hhalt (enc a), ?_⟩) fun a => Nat.mul_add_one_pow_le_two_pow c d _⟩
    -- the encoded output `[true]` has the probability of `true`
    have htrue :
        (ProbComp.eval (program a)).map encBool [true] = ProbComp.eval (program a) true := by
      simp [PMF.map_apply, encBool_apply]
    rw [← heval a, htrue]
    simp only [program, ProbComp.eval_map, BitString.eval_sampleList]
    rw [BitString.uniformList_map_apply, ← acceptCount, MultiTapePTM.half_lt_div_iff]
    exact hA a
  · rintro ⟨d, c₁, c₂, k, State, hfinite, machine, hA⟩
    -- replay the coins
    refine ⟨Polynomial.C c₁ * Polynomial.X ^ d + Polynomial.C c₂,
      fun x => decide (machine.runClosedCoins x.2 (enc x.1) = [true]),
      ComputableInPolyTime.decide_eq'
        ((MultiTapePTM.computableInPolyTime_runClosedCoins machine).comp
          ((ComputableInPolyTime.snd enc encBits).prod
            ((ComputableInPolyTime.of_eq (encOut := encBits) fun _ => rfl).comp
              (ComputableInPolyTime.fst enc encBits))))
        (ComputableInPolyTime.const [true]), fun a => ?_⟩
    have heval : (Polynomial.C c₁ * Polynomial.X ^ d + Polynomial.C c₂).eval (enc a).length =
        c₁ * (enc a).length ^ d + c₂ := by
      simp
    rw [heval, ((MultiTapePTM.decidesByMajorityInTime_iff.mp hA) a).2]
    rfl

end Cslib.Complexity
