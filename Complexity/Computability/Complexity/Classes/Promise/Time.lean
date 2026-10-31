/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.AcceptCount
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Complexity.Classes.Time.SampleVerify
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput

/-!
# Bounded-error probabilistic time for promise problems

`Cslib.Complexity.PromiseBPTIME enc t` consists of the promise problems solved with bounded error
within time `O(t n)`, that is `c₁ * t n + c₂` for constants `c₁` and `c₂`, on instances whose
encoding under `enc` has length `n`, by a fair-coin machine with a binary alphabet and finitely
many states (`Turing.MultiTapePTM.SolvesWithBoundedErrorInTime`). As for `BPTIME`, every run of
that many steps halts, on every instance. The output must be `[true]` with probability at least
`2 / 3` on the yes-instances and `[false]` with probability at least `2 / 3` on the no-instances;
nothing is required on instances outside the promise [Goldreich][Goldreich2006].
A decision problem is in the class exactly when it is in `BPTIME`
(`Cslib.Complexity.ofSet_mem_PromiseBPTIME_iff`).

The class is characterized by deterministic verifiers reading random strings, keeping the time
bound up to constant factors:

* **Sample and verify** (`Cslib.Complexity.mem_PromiseBPTIME_of_verifier`). If a verifier `V` is
  computable within time `T (a, w)` on encoded pairs, the length `ℓ a` of the random string is
  computable in unary within `Tℓ a`, and `(enc a).length + Tℓ a + T (a, w)` is within
  `O(t (enc a).length)`, then a promise problem is in `PromiseBPTIME enc t` when at least two
  thirds of the strings of length `ℓ a` are accepted on its yes-instances and rejected on its
  no-instances. The machine is `Cslib.Complexity.exists_machine_sampleVerify`.
* **Coin replay** (`Cslib.Complexity.exists_verifier_of_mem_PromiseBPTIME`). A promise problem in
  `PromiseBPTIME enc t` has a verifier computable in linear time on encoded pairs: replay the
  coins on the machine and test whether the output is `[true]`. Every random-string length of at
  least `c * t (enc a).length + c` works, since a halted run ignores further coins.

The polynomial characterization of `PromiseBPP`
(`Cslib.Complexity.mem_PromiseBPP_iff_exists_isPPTOn`) loses the polynomial degree; these
explicit-time forms are what a time hierarchy for promise problems needs. Such a hierarchy is
known without advice, by delayed diagonalization [He][He2025], while the hierarchy for `BPTIME`
itself is open.

## Main definitions

* `Turing.MultiTapePTM.SolvesWithBoundedErrorInTime`: bounded error on a promise problem within a
  clock.
* `Cslib.Complexity.PromiseBPTIME`: bounded-error probabilistic time for promise problems.

## Main results

* `Turing.MultiTapePTM.solvesWithBoundedErrorInTime_ofSet_iff`,
  `Cslib.Complexity.ofSet_mem_PromiseBPTIME_iff`: on decision problems, the notions are
  `Turing.MultiTapePTM.DecidesWithBoundedErrorInTime` and `Cslib.Complexity.BPTIME`.
* `Cslib.Complexity.promiseClass_BPTIME_subset_PromiseBPTIME`: the lift of `BPTIME` is contained.
* `Cslib.Complexity.PromiseBPTIME_mono`, `Cslib.Complexity.mem_PromiseBPTIME_of_subset`:
  monotonicity in the time bound and in the promise.
* `Cslib.Complexity.mem_PromiseBPTIME_of_verifier`: sample and verify within explicit time.
* `Cslib.Complexity.exists_verifier_of_mem_PromiseBPTIME`: a linear-time coin-replay verifier.

## References

* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. He, *A note on a hierarchy theorem for promise-BPTIME*][He2025]
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Complexity

variable {k : ℕ} {State : Type} {α : Type*}

/-- `machine` solves the promise problem `Q` with bounded error within `t`, relative to the
encoding `enc`: on every encoded instance `enc a`, every run of `t a` steps with fair coins has
halted; on a yes-instance the run outputs `[true]`, and on a no-instance `[false]`, with
probability at least `2 / 3`. -/
@[expose] def SolvesWithBoundedErrorInTime (machine : MultiTapePTM k Bool State)
    (enc : α ↪ List Bool) (Q : PromiseProblem α) (t : α → ℕ) : Prop :=
  ∀ a, (∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom (t a) (machine.initialConfig (enc a)))).support,
      final.tapes.state = none) ∧
    (a ∈ Q.yes → 2 / 3 ≤ ProbComp.eval (machine.runClosed (t a) (enc a)) [true]) ∧
    (a ∈ Q.no → 2 / 3 ≤ ProbComp.eval (machine.runClosed (t a) (enc a)) [false])

variable {machine : MultiTapePTM k Bool State} {enc : α ↪ List Bool} {Q : PromiseProblem α}

/-- Time bounds can be increased: a halted run ignores further coins. -/
theorem SolvesWithBoundedErrorInTime.mono {t t' : α → ℕ}
    (h : machine.SolvesWithBoundedErrorInTime enc Q t) (ht : ∀ a, t a ≤ t' a) :
    machine.SolvesWithBoundedErrorInTime enc Q t' := fun a => by
  obtain ⟨hhalt, hyes, hno⟩ := h a
  refine ⟨?_, ?_, ?_⟩
  · rw [machine.eval_runClosedConfigFrom_eq_of_halted _ (ht a) hhalt]
    exact hhalt
  · rwa [machine.eval_runClosed_eq_of_halted _ (ht a) hhalt]
  · rwa [machine.eval_runClosed_eq_of_halted _ (ht a) hhalt]

/-- A machine solving a promise problem solves every promise problem with fewer yes-instances and
fewer no-instances. -/
theorem SolvesWithBoundedErrorInTime.of_subset {Q' : PromiseProblem α} {t : α → ℕ}
    (h : machine.SolvesWithBoundedErrorInTime enc Q t) (hyes : Q'.yes ⊆ Q.yes)
    (hno : Q'.no ⊆ Q.no) : machine.SolvesWithBoundedErrorInTime enc Q' t := fun a =>
  ⟨(h a).1, fun ha => (h a).2.1 (hyes ha), fun ha => (h a).2.2 (hno ha)⟩

/-- On a decision problem, solving with bounded error is deciding with bounded error. -/
theorem solvesWithBoundedErrorInTime_ofSet_iff {A : Set α} {t : α → ℕ} :
    machine.SolvesWithBoundedErrorInTime enc (PromiseProblem.ofSet A) t ↔
      machine.DecidesWithBoundedErrorInTime enc A t := by
  refine forall_congr' fun a => and_congr_right fun _ => ?_
  by_cases ha : a ∈ A
  · have hno : a ∉ (PromiseProblem.ofSet A).no := fun h => h ha
    simp only [MultiTapeTM.indicator, ha, ite_true]
    exact ⟨fun h => h.1 ha, fun h => ⟨fun _ => h, fun h' => absurd h' hno⟩⟩
  · simp only [MultiTapeTM.indicator, ha, ite_false]
    exact ⟨fun h => h.2 ha, fun h => ⟨fun h' => absurd h' ha, fun _ => h⟩⟩

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM
open scoped ENNReal

section Definition

variable {α : Type*}

/-- The promise problems solved with bounded error within time `O(t n)`, that is `c₁ * t n + c₂`
for constants `c₁` and `c₂`, on instances whose encoding under `enc` has length `n`, by a fair-coin
machine with a binary alphabet and finitely many states: every run of that many steps has halted,
on every instance, and the output is `[true]` on the yes-instances and `[false]` on the
no-instances with probability at least `2 / 3` [Goldreich][Goldreich2006]. -/
@[expose] def PromiseBPTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (PromiseProblem α) :=
  {Q | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State),
      machine.SolvesWithBoundedErrorInTime enc Q fun a => c₁ * t (enc a).length + c₂}

variable {enc : α ↪ List Bool} {Q : PromiseProblem α}

/-- `PromiseBPTIME` is monotone in the time bound. -/
theorem PromiseBPTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    PromiseBPTIME enc t₁ ⊆ PromiseBPTIME enc t₂ := by
  rintro Q ⟨c₁, c₂, k, State, hfinite, machine, hQ⟩
  exact ⟨c₁, c₂, k, State, hfinite, machine,
    hQ.mono fun a => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _⟩

/-- A promise problem with fewer yes-instances and fewer no-instances than one in `PromiseBPTIME`
is in `PromiseBPTIME`. -/
theorem mem_PromiseBPTIME_of_subset {t : ℕ → ℕ} {Q' : PromiseProblem α}
    (hQ : Q ∈ PromiseBPTIME enc t) (hyes : Q'.yes ⊆ Q.yes) (hno : Q'.no ⊆ Q.no) :
    Q' ∈ PromiseBPTIME enc t := by
  obtain ⟨c₁, c₂, k, State, hfinite, machine, hQ⟩ := hQ
  exact ⟨c₁, c₂, k, State, hfinite, machine, hQ.of_subset hyes hno⟩

/-- **`PromiseBPTIME` agrees with `BPTIME` on decision problems.** -/
theorem ofSet_mem_PromiseBPTIME_iff {t : ℕ → ℕ} {A : Set α} :
    PromiseProblem.ofSet A ∈ PromiseBPTIME enc t ↔ A ∈ BPTIME enc t := by
  simp only [PromiseBPTIME, BPTIME, Set.mem_ofPred_eq,
    MultiTapePTM.solvesWithBoundedErrorInTime_ofSet_iff]

/-- **The lift of `BPTIME` is in `PromiseBPTIME`.** A bounded-error decider of a problem separating
the yes-instances from the no-instances solves the promise problem. -/
theorem promiseClass_BPTIME_subset_PromiseBPTIME {t : ℕ → ℕ} :
    promiseClass (BPTIME enc t) ⊆ PromiseBPTIME enc t := by
  rintro Q ⟨A, hA, hyes, hno⟩
  exact mem_PromiseBPTIME_of_subset (ofSet_mem_PromiseBPTIME_iff.mpr hA) hyes
    fun a ha haA => hno.notMem_of_mem_left haA ha

end Definition

/-! ### Sample and verify -/

section Verifier

variable {α : Type} {enc : α ↪ List Bool}

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

/-- The probability that the verdict on a uniformly random string of length `n` is `b` is the
fraction of the strings with that verdict. -/
private theorem uniformList_map_verdict_apply (V : α × List Bool → Bool) (a : α) (n : ℕ)
    (b : Bool) : ((BitString.uniformList n).map fun w => [V (a, w)]) [b] =
      (acceptCount (fun p => V p == b) a n : ℝ≥0∞) / 2 ^ n := by
  rw [BitString.uniformList_map_apply]
  simp only [acceptCount, List.cons.injEq, and_true, beq_iff_eq]

/-- **Sample and verify, within explicit time.** If a verifier `V` is computable within time
`T (a, w)` on encoded pairs, and the length `ℓ a` of the random string is computable in unary
within time `Tℓ a`, with `(enc a).length + Tℓ a + T (a, w) ≤ C * t (enc a).length + C` for every
string `w` of length `ℓ a`, then a promise problem is in `PromiseBPTIME enc t` when `V` accepts at
least two thirds of the strings of length `ℓ a` together with each yes-instance `a`, and rejects at
least two thirds of them together with each no-instance. -/
theorem mem_PromiseBPTIME_of_verifier {Q : PromiseProblem α} {V : α × List Bool → Bool}
    {ℓ : α → ℕ} {t : ℕ → ℕ} {Tℓ Sℓ : α → ℕ} {T S : α × List Bool → ℕ} {C : ℕ}
    (hℓ : ComputableInO ℓ enc encUnary Tℓ Sℓ)
    (hV : ComputableInO V (encPair enc encBits) encBool T S)
    (ht : ∀ a w, w.length = ℓ a → (enc a).length + Tℓ a + T (a, w) ≤ C * t (enc a).length + C)
    (hyes : ∀ a ∈ Q.yes, 2 * 2 ^ ℓ a ≤ 3 * acceptCount V a (ℓ a))
    (hno : ∀ a ∈ Q.no, 2 * 2 ^ ℓ a ≤ 3 * acceptCount (fun p => !V p) a (ℓ a)) :
    Q ∈ PromiseBPTIME enc t := by
  obtain ⟨c₁, c₂, k, State, hfinite, machine, hmachine⟩ := exists_machine_sampleVerify hℓ hV ht
  refine ⟨c₁, c₂, k, State, hfinite, machine, fun a => ⟨(hmachine a).1, fun ha => ?_, fun ha => ?_⟩⟩
  · rw [(hmachine a).2, uniformList_map_verdict_apply, two_thirds_le_div_iff]
    simpa only [beq_true] using hyes a ha
  · rw [(hmachine a).2, uniformList_map_verdict_apply, two_thirds_le_div_iff]
    simpa only [beq_false] using hno a ha

/-- **A linear-time verifier for promise-problem probabilistic time.** A promise problem in
`PromiseBPTIME enc t` has a verifier computable in linear time on encoded pairs. For a constant
`c`, every random-string length `L ≥ c * t (enc a).length + c` works: the verifier accepts at least
two thirds of the strings of length `L` together with each yes-instance, and rejects at least two
thirds of them together with each no-instance. The verifier replays the coins on the machine and
tests whether the output is `[true]`. -/
theorem exists_verifier_of_mem_PromiseBPTIME {Q : PromiseProblem α} {t : ℕ → ℕ}
    (hQ : Q ∈ PromiseBPTIME enc t) :
    ∃ (V : α × List Bool → Bool) (c : ℕ),
      ComputableInO V (encPair enc encBits) encBool (fun p => (encPair enc encBits p).length)
        (fun p => (encPair enc encBits p).length) ∧
      ∀ a L, c * t (enc a).length + c ≤ L →
        (a ∈ Q.yes → 2 * 2 ^ L ≤ 3 * acceptCount V a L) ∧
        (a ∈ Q.no → 2 * 2 ^ L ≤ 3 * acceptCount (fun p => !V p) a L) := by
  obtain ⟨c₁, c₂, k, State, hfinite, machine, hQ⟩ := hQ
  let V : α × List Bool → Bool := fun p => decide (machine.runClosedCoins p.2 (enc p.1) = [true])
  refine ⟨V, c₁ + c₂, ?_, fun a L hL => ?_⟩
  · -- replay the coins, then compare the output with `[true]`
    have hswap : ComputableInO (fun p : α × List Bool => (p.2, enc p.1)) (encPair enc encBits)
        (encPair encBits encBits)
        (fun p => (encPair enc encBits p).length +
          ((encPair enc encBits p).length + (enc p.1).length))
        (fun p => (encPair enc encBits p).length +
          ((encPair enc encBits p).length + (enc p.1).length)) :=
      (ComputableInO.snd enc encBits).prod
        ((ComputableInO.of_eq (f := fun x : α => enc x) (encIn := enc) (encMid := encBits)
          fun _ => rfl).comp (ComputableInO.fst enc encBits))
    have hrun := (ComputableInO.of_linear
      (MultiTapePTM.computableInLinearTimeAndSpace_runClosedCoins machine)).comp hswap
    obtain ⟨cr, hcr⟩ := hrun.length_le_time
    have heq := ComputableInO.eqWords.comp ((ComputableInO.const (encIn := encPair enc encBits)
      (encMid := encBits) [true]).prod hrun)
    have hfun : ((fun p : List Bool × List Bool => decide (p.1 = p.2)) ∘
        fun p : α × List Bool => ([true], ((fun q : List Bool × List Bool =>
          machine.runClosedCoins q.1 q.2) ∘ fun p : α × List Bool => (p.2, enc p.1)) p)) = V := by
      funext p
      simp [V, eq_comm]
    rw [hfun] at heq
    -- every part is linear in the encoded pair, including the replayed output
    have hbound (p : α × List Bool) :
        (encPair enc encBits p).length + ((encPair enc encBits p).length +
          ((encPair enc encBits p).length + (enc p.1).length) +
          (encPair encBits encBits (p.2, enc p.1)).length) +
        2 * ((machine.runClosedCoins p.2 (enc p.1)).length + 2) ≤
          (9 + 10 * cr) * ((encPair enc encBits p).length + 1) := by
      have hc := hcr p
      simp only [Function.comp_apply, encBits_apply] at hc
      have hle : (enc p.1).length ≤ (encPair enc encBits p).length := by
        simp only [encPair_apply, List.length_append, length_frame, encBits_apply]
        omega
      have hsw : (encPair encBits encBits (p.2, enc p.1)).length ≤
          2 * (encPair enc encBits p).length := by
        simp only [encPair_apply, List.length_append, length_frame, encBits_apply]
        omega
      generalize (encPair enc encBits p).length = N at *
      generalize (machine.runClosedCoins p.2 (enc p.1)).length = R at *
      generalize (encPair encBits encBits (p.2, enc p.1)).length = W at *
      have hR : R ≤ cr * (5 * N + 1) := hc.trans (Nat.mul_le_mul_left cr (by omega))
      nlinarith
    refine heq.mono (9 + 10 * cr) (fun p => ?_) fun p => ?_
    · have := hbound p
      simp only [Function.comp_apply, List.length_singleton] at this ⊢
      nlinarith
    · have := hbound p
      simp only [Function.comp_apply, List.length_singleton] at this ⊢
      omega
  · -- at `L` coins, the halted run is distributed as the replays
    obtain ⟨hhalt, hyes, hno⟩ := hQ a
    have hT : c₁ * t (enc a).length + c₂ ≤ L :=
      le_trans (by nlinarith) hL
    have heval : ProbComp.eval (machine.runClosed L (enc a)) =
        (BitString.uniformList L).map fun w => machine.runClosedCoins w (enc a) := by
      rw [MultiTapePTM.eval_runClosed_eq_map_coins]
    rw [← machine.eval_runClosed_eq_of_halted _ hT hhalt, heval,
      BitString.uniformList_map_apply, two_thirds_le_div_iff] at hyes hno
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · simpa only [acceptCount, V, decide_eq_true_eq] using hyes ha
    · refine (hno ha).trans (Nat.mul_le_mul_left 3 (Finset.card_le_card fun w hw => ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, V, Bool.not_eq_true',
        decide_eq_false_iff_not] at hw ⊢
      rw [hw]
      simp

end Verifier

end Cslib.Complexity
