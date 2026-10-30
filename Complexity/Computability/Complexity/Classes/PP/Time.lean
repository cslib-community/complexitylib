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
probability more than `1 / 2`. It is the unbounded-error counterpart of
`Cslib.Complexity.BPTIME`, with the same machines and clocks.

**Convention.** Unbounded-error probabilistic computation goes back to Gill [Gill1977]. The timed
predicate here is this library's convention, not a transcription of a source definition: acceptance
is strict and ties reject. A nonmember may output `[true]` with probability exactly `1 / 2`, and
its other outputs are unconstrained, so it need not output `[false]` with probability more than
`1 / 2`. This is the threshold of the library's verifier-based `PP`
(`Cslib.Complexity.DecidesByMajority`), and the two agree at polynomial time
(`Cslib.Complexity.mem_PP_iff_exists_mem_PPTIME`). That equivalence is a union over all polynomial
clocks; for a fixed time bound, no comparison with conventions that require a strict majority of
`[false]` on nonmembers is proved here.

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
when the run outputs `[true]` with probability more than `1 / 2`. Ties reject, and outputs other
than `[true]` are unconstrained; this is the library's convention, described in the module
docstring. -/
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

/-- More than half of the random words are accepted exactly when they are accepted with
probability more than one half. -/
private theorem half_lt_uniformList_map_iff {β : Type} (V : β × List Bool → Bool) (b : β)
    (n : ℕ) : 1 / 2 < ((BitString.uniformList n).map fun w => V (b, w)) true ↔
      2 ^ n < 2 * Complexity.acceptCount V b n := by
  have hne : ((BitString.uniformList n).map fun w => V (b, w)) true ≠ ⊤ := PMF.apply_ne_top _ _
  rw [← not_iff_not, not_lt, not_lt, Complexity.acceptCount_le_half_iff,
    ← ENNReal.toReal_le_toReal hne (by simp)]
  simp

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
  -- the probability of `[true]` is the accepted fraction of the coin strings
  have hprob : ProbComp.eval (machine.runClosed (t a) (enc a)) [true] =
      ((BitString.uniformList (t a)).map fun w =>
        decide (machine.runClosedCoins w (enc a) = [true])) true := by
    rw [eval_runClosed_eq_map_coins, BitString.uniformList_map_apply,
      BitString.uniformList_map_apply]
    simp only [decide_eq_true_eq]
  rw [hprob]
  exact half_lt_uniformList_map_iff
    (fun x : List Bool × List Bool => decide (machine.runClosedCoins x.2 x.1 = [true])) _ _

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM
open Cslib.Probability
open scoped ENNReal

variable {α : Type*}

/-- The problems decidable by strict majority within time `O(t n)`, that is `c₁ * t n + c₂` for
constants `c₁` and `c₂`, on instances whose encoding under `enc` has length `n`, by a fair-coin
machine with a binary alphabet and finitely many states: every run of that many steps has halted,
and `a ∈ A` exactly when the run outputs `[true]` with probability more than `1 / 2`. Ties reject
(`Turing.MultiTapePTM.DecidesByMajorityInTime`). -/
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

/-- **`PP` is the union of the classes `PPTIME (n ^ k)`**: a polynomial-time
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
    rw [MultiTapePTM.half_lt_uniformList_map_iff]
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
