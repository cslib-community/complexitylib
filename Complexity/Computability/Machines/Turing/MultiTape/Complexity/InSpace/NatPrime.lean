/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Native primality testing and bounded prime search

Trial division stores the candidate, one binary divisor counter and a Boolean accumulator.
The counted loop does not construct a list of divisors. Running time is unrestricted; all
counters, inputs and outputs are charged in the native work-space certificates.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

namespace PrimeSearch

/-- Candidate, divisor and whether all earlier tested divisors failed to divide it. -/
abbrev TrialState := ℕ × ℕ × Bool

/-- Binary candidate and divisor with the accumulated primality test bit. -/
abbrev encTrialState : TrialState ↪ List Bool := encPair encNat (encPair encNat encBool)

/-- One trial-division iteration. Divisors at or above the candidate have no effect. -/
@[expose] def trialStep (q : TrialState) : TrialState :=
  (q.1, q.2.1 + 1, q.2.2 && decide (q.2.1 < q.1 → q.1 % q.2.1 ≠ 0))

/-- The counted trial-division run. -/
@[expose] def trialRun (n k : ℕ) : TrialState := trialStep^[k] (n, 2, true)

@[simp] theorem trialRun_zero (n : ℕ) : trialRun n 0 = (n, 2, true) := rfl

theorem trialRun_succ (n k : ℕ) : trialRun n (k + 1) = trialStep (trialRun n k) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem trialRun_candidate (n k : ℕ) : (trialRun n k).1 = n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [trialRun_succ]; exact ih

@[simp] theorem trialRun_divisor (n k : ℕ) : (trialRun n k).2.1 = 2 + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [trialRun_succ]; change (trialRun n k).2.1 + 1 = 2 + (k + 1); omega

/-- Exactly the tested proper divisors contribute to the Boolean accumulator. -/
theorem trialRun_true_iff (n k : ℕ) :
    (trialRun n k).2.2 = true ↔ ∀ i < k, 2 + i < n → n % (2 + i) ≠ 0 := by
  induction k with
  | zero => simp [trialRun]
  | succ k ih =>
    rw [trialRun_succ]
    simp only [trialStep, trialRun_candidate, trialRun_divisor, Bool.and_eq_true,
      decide_eq_true_eq]
    rw [ih]
    constructor
    · rintro ⟨hold, hlast⟩ i hi hproper
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact hold i hlt hproper
      · exact hlast hproper
    · intro h
      exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

/-- Trial division, including the explicit lower bound on prime candidates. -/
@[expose] def isPrime (n : ℕ) : Bool := decide (2 ≤ n) && (trialRun n n).2.2

theorem isPrime_eq (n : ℕ) : isPrime n = decide n.Prime := by
  apply Bool.eq_iff_iff.mpr
  simp only [isPrime, Bool.and_eq_true, decide_eq_true_eq, trialRun_true_iff]
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun m hm hmn hdvd => ?_⟩
    have hproper : 2 + (m - 2) < n := by omega
    have hi : m - 2 < n := by omega
    have heq : 2 + (m - 2) = m := by omega
    exact h (m - 2) hi hproper (by simpa only [heq] using Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun i hi hip hmod => ?_⟩
    exact h (2 + i) (by omega) hip (Nat.dvd_of_mod_eq_zero hmod)

private theorem trialStep_inSpace :
    ComputableInSpace trialStep encTrialState encTrialState
      (fun q => (encTrialState q).length) := by
  have hn := fst encNat (encPair encNat encBool)
  have hrest := snd encNat (encPair encNat encBool)
  have hd := fst' hrest
  have hgood := snd' hrest
  have hlt := budget_natLt hd hn
  have hmod := budget_natMod hn hd
  have hnz := budget_finite (encC := encBool) not (budget_natIsZero hmod)
  have hpass := budget_ite hlt hnz (budget_const true (.refl _))
  have hacc := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hgood hpass)
  refine (budget_prod hn (budget_prod (budget_natSucc hd) hacc)).of_enc_eq ?_
  intro q
  by_cases h : q.2.1 < q.1 <;> simp [trialStep, h]

/-- Native trial division uses space linear in the candidate's binary encoding. -/
theorem isPrime_inSpace :
    ComputableInSpace isPrime encNat encBool (fun n => (encNat n).length) := by
  have hid : ComputableInSpace (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hinit := budget_prod hid
    (budget_prod (budget_const (encB := encNat) 2 (.refl _))
      (budget_const (encB := encBool) true (.refl _)))
  have hstates (n k : ℕ) (hk : k ≤ n) :
      (encTrialState (trialStep^[k] (n, 2, true))).length ≤ 16 * ((encNat n).length + 1) := by
    change (encTrialState (trialRun n k)).length ≤ _
    have hd := length_encNat_mono (show 2 + k ≤ n + 2 by omega)
    have hsum := length_encNat_add_le_add n 2
    have htwo : (encNat 2).length = 2 := rfl
    have hb : (encBool (trialRun n k).2.2).length = 1 := by simp
    simp only [encTrialState, length_encPair, trialRun_candidate, trialRun_divisor] at *
    omega
  have hrun := budget_iterate hid hinit trialStep_inSpace hstates
    (.of_le_linear 16 16 fun _ => le_rfl)
  have htrial := snd' (snd' hrun)
  have hlo : ComputableInSpace (fun n : ℕ => decide (2 ≤ n)) encNat encBool
      (fun n => (encNat n).length) :=
    (budget_finite (encC := encBool) not
      (budget_natLt hid (budget_const (encB := encNat) 2 (.refl _)))).of_enc_eq
      fun n => by
        by_cases hn : n < 2
        · have htwo : ¬2 ≤ n := by omega
          simp [hn, htwo]
        · have htwo : 2 ≤ n := by omega
          simp [hn, htwo]
  exact (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hlo htrial)).of_enc_eq fun _ => rfl

/-- Candidate and the first prime found, with zero standing for no answer yet. -/
abbrev SearchState := ℕ × ℕ

/-- Binary candidate cursor and retained first-prime answer. -/
abbrev encSearchState : SearchState ↪ List Bool := encPair encNat encNat

/-- Move to the next candidate, retaining the first prime once it has been found. -/
@[expose] def searchStep (q : SearchState) : SearchState :=
  (q.1 + 1, if q.2 = 0 then if isPrime q.1 then q.1 else 0 else q.2)

/-- Search a bounded number of candidates, without materializing their list. -/
@[expose] def boundedFirstPrime (lower bound : ℕ) : ℕ :=
  (searchStep^[bound + 1] (lower, 0)).2

private theorem searchStep_found (q p k : ℕ) (hp : p ≠ 0) :
    searchStep^[k] (q, p) = (q + k, p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [searchStep, hp, ↓reduceIte, Prod.mk.injEq, and_true]
    omega

private theorem searchStep_before (lower p : ℕ) (hlo : lower ≤ p)
    (hmin : ∀ q, lower ≤ q → q < p → ¬q.Prime) (j : ℕ) (hj : j ≤ p - lower) :
    searchStep^[j] (lower, 0) = (lower + j, 0) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hnot := hmin (lower + j) (by omega) (by omega)
    simp only [searchStep, isPrime_eq, hnot, decide_false, Bool.false_eq_true,
      ↓reduceIte, Prod.mk.injEq, and_true]
    omega

/-- A bounded search returns the least prime at or above its lower bound, provided the bound
covers that prime. The search uses `bound + 1` candidates starting at `lower`. -/
theorem boundedFirstPrime_eq (lower bound p : ℕ) (hlo : lower ≤ p) (hbound : p ≤ bound)
    (hp : p.Prime) (hmin : ∀ q, lower ≤ q → q < p → ¬q.Prime) :
    boundedFirstPrime lower bound = p := by
  have hbefore := searchStep_before lower p hlo hmin (p - lower) le_rfl
  have hat : searchStep^[p - lower + 1] (lower, 0) = (p + 1, p) := by
    rw [Function.iterate_succ_apply', hbefore]
    have heq : lower + (p - lower) = p := by omega
    simp only [heq, searchStep, isPrime_eq, hp, decide_true, ↓reduceIte]
  have hclock : bound + 1 = (bound - (p - lower)) + (p - lower + 1) := by omega
  unfold boundedFirstPrime
  rw [hclock, Function.iterate_add_apply, hat,
    searchStep_found (p + 1) p _ hp.ne_zero]

/-- The bounded implementation agrees with `Nat.find` rather than merely returning some prime. -/
theorem boundedFirstPrime_eq_find (lower bound : ℕ)
    (h : ∃ p, lower ≤ p ∧ p.Prime) (hbound : Nat.find h ≤ bound) :
    boundedFirstPrime lower bound = Nat.find h := by
  have hp := Nat.find_spec h
  apply boundedFirstPrime_eq lower bound (Nat.find h) hp.1 hbound hp.2
  intro q hlo hlt hprime
  have hmin := Nat.find_min' h ⟨hlo, hprime⟩
  omega

private theorem searchStep_inSpace :
    ComputableInSpace searchStep encSearchState encSearchState
      (fun q => (encSearchState q).length) := by
  have hq := fst encNat encNat
  have hfound := snd encNat encNat
  have hz := budget_natIsZero hfound
  have hp := budget_comp_linear isPrime_inSpace hq
  have hanswer := budget_ite hz
    (budget_ite hp hq (budget_const (encB := encNat) 0 (.refl _))) hfound
  refine (budget_prod (budget_natSucc hq) hanswer).of_enc_eq ?_
  intro q
  by_cases hz : q.2 = 0 <;> simp [searchStep, hz]

private theorem searchStep_bounds (lower j : ℕ) :
    (searchStep^[j] (lower, 0)).1 = lower + j ∧
      (searchStep^[j] (lower, 0)).2 ≤ lower + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hq, hf⟩ := ih
    constructor
    · change (searchStep^[j] (lower, 0)).1 + 1 = lower + (j + 1)
      omega
    · change (if (searchStep^[j] (lower, 0)).2 = 0 then
        if isPrime (searchStep^[j] (lower, 0)).1 then (searchStep^[j] (lower, 0)).1 else 0
        else (searchStep^[j] (lower, 0)).2) ≤ lower + (j + 1)
      split_ifs <;> omega

/-- Both search counters are binary and the primality test is uniform in the candidate. -/
theorem boundedFirstPrime_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => boundedFirstPrime q.1 q.2)
      (encPair encNat encNat) encNat (fun q => (encPair encNat encNat q).length) := by
  have hlo := fst encNat encNat
  have hb := snd encNat encNat
  have hn := budget_natSucc hb
  have hinit := budget_prod hlo (budget_const (encB := encNat) 0 (.refl _))
  have hstates (q : ℕ × ℕ) (k : ℕ) (hk : k ≤ q.2 + 1) :
      (encSearchState (searchStep^[k] (q.1, 0))).length ≤
        16 * ((encPair encNat encNat q).length + 1) := by
    obtain ⟨hcursor, hfound⟩ := searchStep_bounds q.1 k
    have hqbound := length_encNat_mono (show q.1 + k ≤ q.1 + q.2 + 1 by omega)
    have hfbound := length_encNat_mono hfound
    have hsum := length_encNat_add_le_add q.1 q.2
    have hsucc := length_encNat_add_le_add (q.1 + q.2) 1
    have hone : (encNat 1).length = 1 := rfl
    simp only [encSearchState, length_encPair, hcursor] at *
    omega
  have hrun := budget_iterate hn hinit searchStep_inSpace hstates
    (.of_le_linear 16 16 fun _ => le_rfl)
  exact (snd' hrun).of_enc_eq fun _ => rfl

end PrimeSearch

/-- Primality with a runtime binary candidate, certified by actual trial division. -/
theorem natPrime : ComputableInSpace (fun n : ℕ => decide n.Prime) encNat encBool
    (fun n => (encNat n).length) :=
  PrimeSearch.isPrime_inSpace.of_enc_eq fun n => by rw [PrimeSearch.isPrime_eq]

end Turing.MultiTapeTM.ComputableInSpace
