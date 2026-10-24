/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Assignment
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Exhaustive search for satisfiability

Exhaustive search decides `SAT` by trying the `2 ^ n` numbered assignments of the `n` distinct
variables of a formula (`Cslib.Logic.PL.CNF.satisfiable_iff_exists_bitsAssignment`). It iterates a
polynomial-time step `2 ^ n` times with a binary counter
(`Turing.MultiTapeTM.ComputableTidilyInO.iterate`), so it runs within time `2 ^ n` times a
polynomial in the length of the encoded formula
(`Cslib.Complexity.BruteForce.exists_computableInO_search`). Hence `SAT`, and every
`k`-SAT, is decidable within time `2 ^ n` times a polynomial
(`Cslib.Complexity.SAT_decidableInExpTime_one`, `Cslib.Complexity.KSAT_decidableInExpTime_one`).

## Main definitions

* `Cslib.Complexity.BruteForce.search`: exhaustive search.

## Main results

* `Cslib.Complexity.BruteForce.search_eq_true_iff`: exhaustive search decides `SAT`.
* `Cslib.Complexity.BruteForce.exists_computableInO_search`: its running time.
* `Cslib.Complexity.SAT_decidableInExpTime_one`, `Cslib.Complexity.KSAT_decidableInExpTime_one`:
  `SAT` and `k`-SAT are decidable within time `2 ^ n` times a polynomial.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Exponential bounds -/

/-- A bound by `2 ^ μ a + 1` rounds of a polynomial, plus a polynomial, is a bound by `2 ^ μ a`
times a polynomial. -/
theorem exists_le_mul_two_pow_of_polyBounded {α : Type*} {size μ T P Q : α → ℕ}
    (hP : PolyBounded size P) (hQ : PolyBounded size Q)
    (hT : ∀ a, T a ≤ (2 ^ μ a + 1) * P a + Q a) :
    ∃ c e, ∀ a, T a ≤ c * 2 ^ μ a * (size a + 1) ^ e := by
  obtain ⟨c₁, d₁, hP⟩ := hP.exists_le
  obtain ⟨c₂, d₂, hQ⟩ := hQ.exists_le
  refine ⟨2 * c₁ + c₂, d₁ + d₂, fun a => (hT a).trans ?_⟩
  have h₁ : (size a + 1) ^ d₁ ≤ (size a + 1) ^ (d₁ + d₂) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
  have h₂ : (size a + 1) ^ d₂ ≤ (size a + 1) ^ (d₁ + d₂) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
  have hN : 1 ≤ 2 ^ μ a := Nat.one_le_two_pow
  have hP' := (hP a).trans (Nat.mul_le_mul_left c₁ h₁)
  have hQ' := (hQ a).trans (Nat.mul_le_mul_left c₂ h₂)
  generalize (size a + 1) ^ (d₁ + d₂) = M at *
  generalize 2 ^ μ a = N at *
  have : (N + 1) * P a ≤ 2 * N * (c₁ * M) :=
    (Nat.mul_le_mul (show N + 1 ≤ 2 * N by omega) hP').trans (le_of_eq (by ring))
  have : Q a ≤ N * (c₂ * M) := hQ'.trans (Nat.le_mul_of_pos_left _ (by omega))
  nlinarith

namespace BruteForce

/-! ### The search -/

/-- The state of exhaustive search: the formula, its distinct variables, the number of the next
assignment to try, and whether a satisfying assignment was found. -/
abbrev State : Type := (CNF ℕ × List ℕ) × (ℕ × Bool)

/-- States encoded as framed tuples. -/
private abbrev encState : State ↪ List Bool :=
  encPair (encPair encCNF (encList encNat)) (encPair encNat encBool)

/-- Try the next numbered assignment. -/
def step (s : State) : State :=
  (s.1, (s.2.1 + 1, s.2.2 || s.1.1.eval (bitsAssignment s.1.2 s.2.1)))

/-- The initial state: no assignment tried yet. -/
def init (φ : CNF ℕ) : State := ((φ, φ.distinctVars), (0, false))

/-- **Exhaustive search**: try the `2 ^ n` assignments numbered by `i < 2 ^ n` on the `n` distinct
variables of the formula. -/
def search (φ : CNF ℕ) : Bool := (step^[2 ^ φ.distinctVars.length] (init φ)).2.2

private theorem iterate_step_init (φ : CNF ℕ) (k : ℕ) :
    step^[k] (init φ) = ((φ, φ.distinctVars),
      (k, (List.range k).any fun i => φ.eval (bitsAssignment φ.distinctVars i))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, step, List.range_succ, List.any_append]
    simp

/-- **Exhaustive search decides `SAT`.** -/
theorem search_eq_true_iff (φ : CNF ℕ) : search φ = true ↔ φ ∈ SAT := by
  rw [search, iterate_step_init, mem_SAT,
    CNF.satisfiable_iff_exists_bitsAssignment fun v hv => CNF.mem_distinctVars.mpr hv]
  simp

/-! ### Running time -/

open ComputableTidilyInPolyTime in
/-- A step of exhaustive search is polynomial-time. -/
private theorem computableTidilyInPolyTime_step
    : ComputableTidilyInPolyTime step encState encState := by
  have h : ComputableTidilyInPolyTime (fun s : State => s.1.1.eval (bitsAssignment s.1.2 s.2.1))
      encState encBool :=
    computableInPolyTime_eval_bitsAssignment.tidy.comp
      (show ComputableTidilyInPolyTime (fun s : State => (s.1, s.2.1)) encState
        (encPair (encPair encCNF (encList encNat)) encNat) by fun_prop)
  unfold step
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
open ComputableTidilyInPolyTime in
/-- The initial state is computed in polynomial time. -/
private theorem computableTidilyInPolyTime_init
    : ComputableTidilyInPolyTime init encCNF encState := by
  have hvars := SAT.computableInPolyTime_distinctVars.tidy
  unfold init
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
open ComputableTidilyInPolyTime in
/-- The number `2 ^ n` of rounds is computed in binary in polynomial time. -/
private theorem computableTidilyInPolyTime_count :
    ComputableTidilyInPolyTime (fun φ => 2 ^ φ.distinctVars.length) encCNF encNat := by
  fun_prop

/-- **The running time of exhaustive search**: within time `2 ^ n` times a polynomial in the
length of the encoded formula, on formulas with `n` variables. -/
theorem exists_computableInO_search : ∃ e, ComputableInO search encCNF encBool
    (fun φ => 2 ^ φ.numVars * ((encCNF φ).length + 1) ^ e)
    fun φ => 2 ^ φ.numVars * ((encCNF φ).length + 1) ^ e := by
  have this : ∃ e, ComputableTidilyInO search encCNF encBool
      (fun φ => 2 ^ φ.numVars * ((encCNF φ).length + 1) ^ e) fun φ => 2 ^ φ.numVars *
      ((encCNF φ).length + 1) ^ e := by
    obtain ⟨d, _, hstep⟩ := computableTidilyInPolyTime_step.exists_degree
    obtain ⟨d₀, _, hinit⟩ := computableTidilyInPolyTime_init.exists_degree
    obtain ⟨d₁, _, hcount⟩ := computableTidilyInPolyTime_count.exists_degree
    obtain ⟨d₂, _, hans⟩ :=
      (show ComputableTidilyInPolyTime (fun s : State => s.2.2) encState encBool
      by fun_prop).exists_degree
    obtain ⟨cv, dv, hvs⟩ :=
      SAT.computableInPolyTime_distinctVars.tidy.polyBounded_length.exists_le
    set size : CNF ℕ → ℕ := fun φ => (encCNF φ).length
    set B : CNF ℕ → ℕ := fun φ => (2 * cv + 13) * (size φ + 1) ^ (dv + 1)
    have hn (φ : CNF ℕ) : φ.distinctVars.length ≤ size φ := by
      rw [CNF.length_distinctVars]
      exact φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
    have hstate : ∀ φ, ∀ k ≤ 2 ^ φ.distinctVars.length,
        (encState (step^[k] (init φ))).length ≤ B φ := by
      intro φ k hk
      have hK := ComputableTidilyInO.length_encNat_mono hk
      rw [encNat_two_pow] at hK
      have hV := hvs φ
      have h₁ : size φ + 1 ≤ (size φ + 1) ^ (dv + 1) := by
        simpa using Nat.pow_le_pow_right (Nat.succ_pos (size φ)) (Nat.le_add_left 1 dv)
      have h₂ : (size φ + 1) ^ dv ≤ (size φ + 1) ^ (dv + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ dv)
      have h₃ := Nat.mul_le_mul_left cv h₂
      have h₄ := hn φ
      rw [iterate_step_init]
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hK
      simp only [encState, length_encPair, encBool_apply, List.length_singleton, B, size]
        at hV h₁ h₃ h₄ ⊢
      nlinarith
    have hiter := ComputableTidilyInO.iterate hcount.inO hinit.inO hstep.inO
      (R := fun φ => (B φ + 1) ^ d) (Q := fun φ => (B φ + 1) ^ d) (B := B)
      (fun φ k hk => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate φ k hk) 1) d)
      (fun φ k hk => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate φ k hk) 1) d) hstate
    have h := hans.inO.comp hiter
    have hB : PolyBounded size B := .of_forall_le (2 * cv + 13) (dv + 1) fun φ => le_rfl
    have hpow (j : ℕ) : PolyBounded size fun φ => (B φ + 1) ^ j :=
      ((PolyBounded.of_polynomiallyBounded id (bound := fun x => (x + 1) ^ j) (by fun_prop)).comp
        hB).mono fun φ => le_rfl
    have hL (j : ℕ) : PolyBounded size fun φ => (size φ + 1) ^ j :=
      .of_forall_le 1 j fun φ => by simp
    obtain ⟨c, e, hT⟩ := exists_le_mul_two_pow_of_polyBounded (size := size) (μ := CNF.numVars)
      ((hpow d).add (hB.add (.of_forall_le 4 2 fun φ => le_rfl)))
      ((hL d₁).add ((hL d₀).add (hpow d₂)))
      (T := fun φ => ((encCNF φ).length + 1) ^ d₁ + ((encCNF φ).length + 1) ^ d₀ +
        (2 ^ φ.distinctVars.length + 1) * ((B φ + 1) ^ d + B φ +
          ((encNat (2 ^ φ.distinctVars.length)).length + 1) ^ 2) +
        ((encState (step^[2 ^ φ.distinctVars.length] (init φ))).length + 1) ^ d₂)
      (fun φ => by
        have hK : ((encNat (2 ^ φ.distinctVars.length)).length + 1) ^ 2 ≤
            4 * (size φ + 1) ^ 2 := by
          rw [encNat_two_pow]
          simp only [List.length_append, List.length_replicate, List.length_singleton]
          calc (φ.distinctVars.length + 1 + 1) ^ 2 ≤ (2 * (size φ + 1)) ^ 2 :=
                Nat.pow_le_pow_left (by have := hn φ; omega) 2
            _ = 4 * (size φ + 1) ^ 2 := by ring
        have hS := Nat.pow_le_pow_left (Nat.add_le_add_right (hstate φ _ le_rfl) 1) d₂
        rw [CNF.length_distinctVars] at hK hS ⊢
        have := Nat.mul_le_mul_left (2 ^ φ.numVars + 1)
          (Nat.add_le_add_left hK ((B φ + 1) ^ d + B φ))
        simp only [size] at this hS ⊢
        nlinarith)
    refine ⟨e, (h.mono c (fun φ => ?_) fun φ => ?_).of_enc_eq fun φ => rfl⟩
    all_goals
      have h₁ := hT φ
      simp only [size] at h₁
      generalize 2 ^ φ.distinctVars.length = N at h₁ ⊢
      generalize (encNat N).length = K at h₁ ⊢
      obtain ⟨X, hX⟩ : ∃ X, (B φ + 1) ^ d + B φ = X := ⟨_, rfl⟩
      rw [hX] at h₁
      have h₂ : K ≤ (K + 1) ^ 2 := by nlinarith
      have h₃ : X + (K + 1) ^ 2 ≤ (N + 1) * (X + (K + 1) ^ 2) := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
  simpa only [computableInO_iff_computableTidilyInO] using this

end BruteForce

/-- **`SAT` by exhaustive search**: `SAT` is decidable within time `2 ^ n` times a polynomial in the
length of the encoded formula, on formulas with `n` variables. -/
theorem SAT_decidableInExpTime_one : DecidableInExpTime SAT encCNF CNF.numVars 1 := by
  obtain ⟨e, h⟩ := BruteForce.exists_computableInO_search
  refine DecidableInExpTime.of_computableInO h (fun φ => (BruteForce.search_eq_true_iff φ).symm) 1 e
    fun φ => ?_
  rw [one_mul, Real.rpow_natCast]
  push_cast
  rw [one_mul]

open ComputableTidilyInPolyTime in
/-- Checking that every clause has at most `k` literals is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_all_length_le (k : ℕ) :
    ComputableInPolyTime (fun φ : CNF ℕ => φ.all fun c => decide (c.length ≤ k)) encCNF
      encBool := by
  unfold encCNF
  fun_prop

/-- `k`-SAT is `SAT` restricted to the formulas whose clauses have at most `k` literals. -/
theorem KSAT_eq_inter (k : ℕ) {B : Set (CNF ℕ)} (hB : KSAT k ⊆ B) (hBSAT : B ⊆ SAT) :
    KSAT k = {φ | (φ.all fun c => decide (c.length ≤ k)) = true} ∩ B := by
  ext φ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, hB h⟩, fun h => ⟨h.1, hBSAT h.2⟩⟩

/-- **`k`-SAT by exhaustive search**: `k`-SAT is decidable within time `2 ^ n` times a polynomial
in the length of the encoded formula, on formulas with `n` variables. -/
theorem KSAT_decidableInExpTime_one (k : ℕ) : DecidableInExpTime (KSAT k) encCNF CNF.numVars 1 := by
  rw [KSAT_eq_inter k (KSAT_subset_SAT k) le_rfl]
  exact SAT_decidableInExpTime_one.inter (computableInPolyTime_all_length_le k) zero_le_one

end Cslib.Complexity
