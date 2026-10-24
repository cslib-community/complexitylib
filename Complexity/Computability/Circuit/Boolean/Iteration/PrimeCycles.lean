/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.CircuitCounting
public import Complexity.Computability.Circuit.Boolean.Iteration.ModulusCounter
public import Mathlib.Data.FinEnum
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Permutations with one prime cycle per hash class

This module formalizes the combinatorial and circuit-complexity structure of permutations on
`BitString (m + K)` that act as a disjoint union of prime-length cycles indexed by `m`-bit hash
classes. States of `BitString (m + K)` are pairs `(r, b)` of an `m`-bit class word `r` and a
`K`-bit position word `b`. Given a cycle length `ℓ r < 2 ^ K` for each class `r`, the step map
advances `b` by `1` modulo `ℓ r` when `b < ℓ r` and fixes every other state.

* `PrimeCycles.iterate_step` and `PrimeCycles.power_apply_mod`: the `T`-th power adds `T` modulo
  `ℓ r`, so it depends on `T` only through the remainder table `r ↦ T % ℓ r`.
* `PrimeCycles.iterate_eq_iterate_iff`: when the nontrivial lengths (`1 < ℓ r`) are pairwise
  coprime, two powers agree if and only if their exponents are congruent modulo `order ℓ`, the
  product of the nontrivial lengths. Hence `order ℓ` is both the permutation order
  (`PrimeCycles.iterate_eq_id_iff`) and the exact number of distinct powers
  (`PrimeCycles.card_range_iterate`).
* `PrimeCycles.classPrime`: the hash-class construction with candidates
  `2 ^ (m + g) + (r xor f z) * 2 ^ g + z` for `z < 2 ^ g` and `K = m + g + 1`. Different classes
  have disjoint candidate sets (`PrimeCycles.candidate_injective`), so the chosen prime lengths
  are distinct and pairwise coprime (`PrimeCycles.classPrime_coprime`).
* `PrimeCycles.near_landau_lower_bound`: for any mixing function `f` with values below `2 ^ m`,
  the resulting permutation is bijective, has order at least `2 ^ ((m + g) * c)` where `c` is the
  number of active classes, and has a power below its order requiring more than `q` gates whenever
  the ordered-syntax exponent for `q` gates is below `(m + g) * c`.
* `lcmBelow` and elementary upper bounds (`lcmBelow_add_dvd`, `four_pow_ge_two_mul_lcmBelow`,
  `lcmBelow_lt_four_pow`), together with the bundled `PrimeCycleData` interface
  (`PrimeCycleData.step_circuit`, `PrimeCycleData.power_circuit`,
  `PrimeCycleData.exists_hard_power`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.PrimeCycles.power`: `T`-step map advancing each class `r`
  modulo `ℓ r`.
* `Cslib.Circuits.Boolean.Iteration.PrimeCycles.step`: single-step permutation `power ℓ 1`.
* `Cslib.Circuits.Boolean.Iteration.PrimeCycles.order`: common-period product of the nontrivial
  cycle lengths (which equals the exact permutation order under `LengthsCoprime`).
* `Cslib.Circuits.Boolean.Iteration.PrimeCycles.classPrime`: least-index prime candidate in each
  hash class, or `1` if none exists.
* `Cslib.Circuits.Boolean.Iteration.lcmBelow`: least common multiple of `{1, …, n}`.
* `Cslib.Circuits.Boolean.Iteration.PrimeCycleData`: bundled cycle-length data with pairwise
  coprime nontrivial lengths.

## Main results

* `Cslib.Circuits.Boolean.Iteration.PrimeCycles.iterate_eq_iterate_iff`: two powers agree iff the
  exponents are congruent modulo `order ℓ`.
* `Cslib.Circuits.Boolean.Iteration.PrimeCycles.card_range_iterate`: the number of distinct powers
  equals `order ℓ`.
* `Cslib.Circuits.Boolean.Iteration.PrimeCycles.near_landau_lower_bound`: explicit lower bound for
  the hash-class prime-cycle permutation.
* `Cslib.Circuits.Boolean.Iteration.lcmBelow_lt_four_pow`: `lcm(1, …, n) < 4 ^ n` for `1 ≤ n`.
* `Cslib.Circuits.Boolean.Iteration.PrimeCycleData.step_circuit` and
  `Cslib.Circuits.Boolean.Iteration.PrimeCycleData.power_circuit`: circuit synthesis for the step
  and `T`-th power from class-length and remainder tables.

## References

* Adapted from lean/Proofs/PrimeCycles.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open scoped BigOperators

/-! ### Least common multiples up to `n` -/

/-- The least common multiple `lcm(1, …, n)`. -/
def lcmBelow (n : ℕ) : ℕ := Nat.lcmUpto n

theorem lcmBelow_pos (n : ℕ) : 0 < lcmBelow n := Nat.lcmUpto_pos n

theorem lcmBelow_eq_prod_prime_powers (n : ℕ) :
    lcmBelow n = ∏ p ∈ Nat.primesLE n, p ^ p.log n :=
  Nat.lcmUpto_eq_prod_pow_log n

/-- For `n ≤ m`, `lcmBelow (m + n)` divides `lcmBelow m * (m + n).choose m`. Every prime power
`p ^ L ≤ m + n` exceeding `m` satisfies `m < p ^ L ≤ m + n`, which forces a base-`p` carry at
digit `L` when adding `m` and `n`. -/
theorem lcmBelow_add_dvd {m n : ℕ} (h : n ≤ m) :
    lcmBelow (m + n) ∣ lcmBelow m * (m + n).choose m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · have hn : n = 0 := by omega
    subst hn
    decide
  · have hpos : 0 < (m + n).choose m := Nat.choose_pos (Nat.le_add_right m n)
    rw [lcmBelow, lcmBelow, ← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero _)
      (Nat.mul_ne_zero (Nat.lcmUpto_ne_zero _) hpos.ne')]
    intro p hp
    rw [Nat.factorization_lcmUpto (m + n) hp,
      Nat.factorization_mul (Nat.lcmUpto_ne_zero m) hpos.ne',
      Finsupp.coe_add, Pi.add_apply, Nat.factorization_lcmUpto m hp]
    set L := p.log (m + n)
    by_cases hL : L ≤ p.log m
    · omega
    · have hL : p.log m < L := by omega
      have hLpos : 1 ≤ L := by omega
      have hpow : p ^ L ≤ m + n := Nat.pow_log_le_self p (by omega)
      have hpow_pred : p ^ (L - 1) ≤ m := by
        have h1 : p ^ (L - 1) * p ≤ p * m := by
          calc
            p ^ (L - 1) * p = p ^ L := by rw [← pow_succ, Nat.sub_add_cancel hLpos]
            _ ≤ m + n := hpow
            _ ≤ 2 * m := by omega
            _ ≤ p * m := Nat.mul_le_mul_right m hp.two_le
        exact Nat.le_of_mul_le_mul_left (by linarith) hp.pos
      have hlog_ge : L - 1 ≤ p.log m := Nat.le_log_of_pow_le hp.one_lt hpow_pred
      have hLeq : L = p.log m + 1 := by omega
      have hm_lt : m < p ^ L := Nat.lt_pow_of_log_lt hp.one_lt hL
      have hn_lt : n < p ^ L := lt_of_le_of_lt h hm_lt
      have hchoose : 1 ≤ ((m + n).choose m).factorization p := by
        rw [Nat.add_comm m n,
          Nat.factorization_choose' hp (by rw [Nat.add_comm n m]; exact Nat.lt_succ_self L)]
        refine Finset.card_pos.mpr
          ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hLpos, Nat.lt_succ_self L⟩, ?_⟩⟩
        rw [Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hn_lt]
        exact hpow
      omega

private theorem lcmBelow_add_le {m n : ℕ} (h : n ≤ m) :
    lcmBelow (m + n) ≤ lcmBelow m * (m + n).choose m :=
  Nat.le_of_dvd (Nat.mul_pos (lcmBelow_pos m) (Nat.choose_pos (Nat.le_add_right m n)))
    (lcmBelow_add_dvd h)

/-- Elementary upper bound `2 * lcm(1, …, n) ≤ 4 ^ n` for all `n ≥ 1`. -/
theorem four_pow_ge_two_mul_lcmBelow (n : ℕ) (hn : 1 ≤ n) :
    2 * lcmBelow n ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    rcases le_or_gt n 2 with hn2 | hn2
    · interval_cases n <;> decide
    · rcases n.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hm : 1 ≤ m := by omega
        have hlt : m < m + m := by omega
        have hih := ihn m hlt hm
        have hdvd := lcmBelow_add_le (le_rfl : m ≤ m)
        have hbin : (m + m).choose m ≤ 4 ^ m := by
          calc
            (m + m).choose m ≤ ∑ i ∈ Finset.range (m + m + 1), (m + m).choose i :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                (Finset.mem_range.mpr (by omega))
            _ = 2 ^ (m + m) := Nat.sum_range_choose (m + m)
            _ = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
        calc
          2 * lcmBelow (m + m) ≤ 2 * (lcmBelow m * (m + m).choose m) :=
            Nat.mul_le_mul_left 2 hdvd
          _ = (2 * lcmBelow m) * (m + m).choose m := by ring
          _ ≤ 4 ^ m * 4 ^ m := Nat.mul_le_mul hih hbin
          _ = 4 ^ (m + m) := by rw [← pow_add]
      · have hm1 : 1 ≤ m + 1 := by omega
        have hlt : m + 1 < 2 * m + 1 := by omega
        have hih := ihn (m + 1) hlt hm1
        have hdvd : lcmBelow (2 * m + 1) ≤ lcmBelow (m + 1) * (2 * m + 1).choose m := by
          have h1 : lcmBelow ((m + 1) + m) ≤ lcmBelow (m + 1) * ((m + 1) + m).choose (m + 1) :=
            lcmBelow_add_le (Nat.le_succ m)
          have hchoose : ((m + 1) + m).choose (m + 1) = (2 * m + 1).choose m := by
            rw [Nat.choose_symm_add]
            congr 1
            omega
          have h2 : (m + 1) + m = 2 * m + 1 := by omega
          rwa [hchoose, h2] at h1
        have hbin : (2 * m + 1).choose m ≤ 4 ^ m := Nat.choose_middle_le_pow m
        calc
          2 * lcmBelow (2 * m + 1) ≤ 2 * (lcmBelow (m + 1) * (2 * m + 1).choose m) :=
            Nat.mul_le_mul_left 2 hdvd
          _ = (2 * lcmBelow (m + 1)) * (2 * m + 1).choose m := by ring
          _ ≤ 4 ^ (m + 1) * 4 ^ m := Nat.mul_le_mul hih hbin
          _ = 4 ^ (2 * m + 1) := by
            rw [← pow_add]
            congr 1
            omega

/-- For every `n ≥ 1`, `lcm(1, …, n) < 4 ^ n`. -/
theorem lcmBelow_lt_four_pow (n : ℕ) (hn : 1 ≤ n) :
    lcmBelow n < 4 ^ n := by
  have hpos := lcmBelow_pos n
  have hle := four_pow_ge_two_mul_lcmBelow n hn
  omega

/-! ### Disjoint prime-cycle permutations indexed by hash classes -/

namespace PrimeCycles

open ModulusCounter (advance advance_add advance_lt advance_zero)

variable {m K : ℕ}

/-- The `m`-bit class word in the first `m` coordinates. -/
def classWord (x : BitString (m + K)) : BitVec m := word fun i => x (Fin.castAdd K i)

/-- The `K`-bit position word in the last `K` coordinates. -/
def posWord (x : BitString (m + K)) : BitVec K := word fun i => x (Fin.natAdd m i)

/-- Pack an `m`-bit class word and a `K`-bit position word into `BitString (m + K)`. -/
def pack (r : BitVec m) (b : BitVec K) : BitString (m + K) :=
  Fin.append (fun i : Fin m => r.getLsbD i.val) (fun i : Fin K => b.getLsbD i.val)

@[simp] theorem classWord_pack (r : BitVec m) (b : BitVec K) : classWord (pack r b) = r := by
  simp only [classWord, pack, Fin.append_left, word_getLsbD]

@[simp] theorem posWord_pack (r : BitVec m) (b : BitVec K) : posWord (pack r b) = b := by
  simp only [posWord, pack, Fin.append_right, word_getLsbD]

@[simp] theorem pack_words (x : BitString (m + K)) : pack (classWord x) (posWord x) = x := by
  funext bit
  induction bit using Fin.addCases with
  | left i => simp only [pack, classWord, Fin.append_left, getLsbD_word]
  | right i => simp only [pack, posWord, Fin.append_right, getLsbD_word]

/-- The `T`-th power: advance the position by `T` modulo `ℓ r` on the cycle `b < ℓ r`, and fix
every other state (in particular every state with `ℓ r ≤ 1`). -/
def power (ℓ : BitVec m → ℕ) (T : ℕ) (x : BitString (m + K)) : BitString (m + K) :=
  pack (classWord x) (BitVec.ofNat K (advance (ℓ (classWord x)) (posWord x).toNat T))

/-- The single-step permutation `power ℓ 1`. -/
def step (ℓ : BitVec m → ℕ) : BitString (m + K) → BitString (m + K) := power ℓ 1

variable (ℓ : BitVec m → ℕ)

@[simp] theorem power_zero : power (K := K) ℓ 0 = id := by
  funext x
  simp [power]

private theorem power_add (hℓ : ∀ r, ℓ r < 2 ^ K) (S T : ℕ) (x : BitString (m + K)) :
    power ℓ T (power ℓ S x) = power ℓ (S + T) x := by
  simp only [power, classWord_pack, posWord_pack, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (advance_lt (hℓ _) (BitVec.isLt _)), advance_add]

/-- The `T`-th iterate of `step ℓ` is `power ℓ T`. -/
theorem iterate_step (hℓ : ∀ r, ℓ r < 2 ^ K) (T : ℕ) :
    (step (K := K) ℓ)^[T] = power ℓ T := by
  funext x
  induction T with
  | zero => simp
  | succ T ih => rw [Function.iterate_succ_apply', ih, step, power_add ℓ hℓ]

private theorem advance_mod (a b T : ℕ) : advance a b (T % a) = advance a b T := by
  unfold advance
  split_ifs with h
  · rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  · rfl

/-- `(step ℓ)^[T] (pack r b)` depends on `T` only through `T % ℓ r`. -/
theorem power_apply_mod (T : ℕ) (r : BitVec m) (b : BitVec K) :
    power ℓ T (pack r b) =
      pack r (BitVec.ofNat K
        (if 0 < ℓ r ∧ b.toNat < ℓ r then (b.toNat + T % ℓ r) % ℓ r else b.toNat)) := by
  simp only [power, classWord_pack, posWord_pack, ← advance_mod (ℓ r) _ T]
  rfl

/-- Every positive length divides the product of positive lengths, so that power is the identity. -/
private theorem power_prod_eq_id :
    power (K := K) ℓ (∏ r ∈ Finset.univ.filter (fun r => 0 < ℓ r), ℓ r) = id := by
  funext x
  simp only [power, id]
  unfold advance
  split_ifs with h
  · have hd : ℓ (classWord x) ∣ ∏ r ∈ Finset.univ.filter (fun r => 0 < ℓ r), ℓ r :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt h.2]
    simp
  · simp

theorem step_bijective (hℓ : ∀ r, ℓ r < 2 ^ K) : Function.Bijective (step (K := K) ℓ) := by
  set P := ∏ r ∈ Finset.univ.filter (fun r => 0 < ℓ r), ℓ r
  have hP : 0 < P := Finset.prod_pos fun r hr => (Finset.mem_filter.mp hr).2
  have hid := power_prod_eq_id (K := K) ℓ
  have h1 (x : BitString (m + K)) : power ℓ (P - 1) (step ℓ x) = x := by
    rw [step, power_add ℓ hℓ, Nat.add_sub_cancel' hP, hid]; rfl
  have h2 (x : BitString (m + K)) : step ℓ (power ℓ (P - 1) x) = x := by
    rw [step, power_add ℓ hℓ, Nat.sub_add_cancel hP, hid]; rfl
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

/-- Two powers agree iff the exponents agree modulo every nontrivial cycle length. -/
theorem power_eq_power_iff (hℓ : ∀ r, ℓ r < 2 ^ K) (S T : ℕ) :
    power (K := K) ℓ S = power ℓ T ↔ ∀ r, 1 < ℓ r → S ≡ T [MOD ℓ r] := by
  constructor
  · intro he r hr
    have hx := congrArg (fun F => (posWord (F (pack r (BitVec.ofNat K 0)))).toNat) he
    have hS := (Nat.mod_lt S (by omega : 0 < ℓ r)).trans (hℓ r)
    have hT := (Nat.mod_lt T (by omega : 0 < ℓ r)).trans (hℓ r)
    simpa [Nat.ModEq, power, advance, show 0 < ℓ r by omega, Nat.mod_eq_of_lt hS,
      Nat.mod_eq_of_lt hT] using hx
  · intro h
    funext x
    simp only [power]
    congr 2
    unfold advance
    split_ifs with ha
    · by_cases h1 : 1 < ℓ (classWord x)
      · exact (h _ h1).add_left _
      · have : ℓ (classWord x) = 1 := by omega
        rw [this, Nat.mod_one, Nat.mod_one]
    · rfl

/-- The nontrivial classes (`1 < ℓ r`). -/
def active : Finset (BitVec m) := Finset.univ.filter fun r => 1 < ℓ r

/-- The common-period product of the nontrivial cycle lengths (which equals the exact permutation
order under `LengthsCoprime`). -/
def order : ℕ := ∏ r ∈ active ℓ, ℓ r

theorem order_pos : 0 < order ℓ :=
  Finset.prod_pos fun r hr => by
    have := (Finset.mem_filter.mp hr).2
    omega

private theorem dvd_order {r : BitVec m} (hr : 1 < ℓ r) : ℓ r ∣ order ℓ :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)

/-- Pairwise coprimality of the nontrivial cycle lengths. -/
def LengthsCoprime : Prop := ((active ℓ : Finset (BitVec m)) : Set (BitVec m)).Pairwise
  fun r s => (ℓ r).Coprime (ℓ s)

variable {ℓ}

theorem modEq_order_iff (hc : LengthsCoprime ℓ) (S T : ℕ) :
    S ≡ T [MOD order ℓ] ↔ ∀ r, 1 < ℓ r → S ≡ T [MOD ℓ r] := by
  have hrel : ((active ℓ : Finset (BitVec m)) : Set (BitVec m)).Pairwise
      (Function.onFun IsRelPrime ℓ) :=
    fun r hr s hs hrs => Nat.coprime_iff_isRelPrime.mp (hc hr hs hrs)
  constructor
  · exact fun h r hr => Nat.ModEq.of_dvd (dvd_order ℓ hr) h
  · intro h
    rcases le_total S T with hST | hST
    · rw [Nat.modEq_iff_dvd' hST]
      exact Finset.prod_dvd_of_isRelPrime hrel fun r hr =>
        (Nat.modEq_iff_dvd' hST).mp (h r (Finset.mem_filter.mp hr).2)
    · refine Nat.ModEq.symm ?_
      rw [Nat.modEq_iff_dvd' hST]
      exact Finset.prod_dvd_of_isRelPrime hrel fun r hr =>
        (Nat.modEq_iff_dvd' hST).mp (h r (Finset.mem_filter.mp hr).2).symm

/-- With pairwise coprime nontrivial lengths, `(step ℓ)^[S] = (step ℓ)^[T]` iff
`S ≡ T [MOD order ℓ]`. -/
theorem iterate_eq_iterate_iff (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) (S T : ℕ) :
    (step (K := K) ℓ)^[S] = (step ℓ)^[T] ↔ S ≡ T [MOD order ℓ] := by
  rw [iterate_step ℓ hℓ, iterate_step ℓ hℓ, power_eq_power_iff ℓ hℓ, modEq_order_iff hc]

/-- `(step ℓ)^[T] = id` iff `order ℓ ∣ T`. -/
theorem iterate_eq_id_iff (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) (T : ℕ) :
    (step (K := K) ℓ)^[T] = id ↔ order ℓ ∣ T := by
  have h := iterate_eq_iterate_iff (K := K) hℓ hc T 0
  rw [Function.iterate_zero] at h
  rw [h, Nat.modEq_zero_iff_dvd]

/-- Distinct residues modulo `order ℓ` yield distinct powers. -/
theorem iterate_injective (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) :
    Function.Injective fun T : Fin (order ℓ) => (step (K := K) ℓ)^[T.val] := by
  intro S T h
  have hm := (iterate_eq_iterate_iff hℓ hc S.val T.val).mp h
  exact Fin.ext (by
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt S.isLt, Nat.mod_eq_of_lt T.isLt] at hm)

/-- The number of distinct powers of `step ℓ` is `order ℓ`. -/
theorem card_range_iterate (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) :
    Nat.card (Set.range fun T : ℕ => (step (K := K) ℓ)^[T]) = order ℓ := by
  have hrange : Set.range (fun T : ℕ => (step (K := K) ℓ)^[T]) =
      Set.range (fun T : Fin (order ℓ) => (step (K := K) ℓ)^[T.val]) := by
    ext G
    constructor
    · rintro ⟨T, rfl⟩
      refine ⟨⟨T % order ℓ, Nat.mod_lt _ (order_pos ℓ)⟩, ?_⟩
      exact (iterate_eq_iterate_iff hℓ hc _ _).mpr (Nat.mod_modEq _ _)
    · rintro ⟨T, rfl⟩
      exact ⟨T.val, rfl⟩
  rw [hrange, Nat.card_range_of_injective (iterate_injective hℓ hc)]
  simp

/-- The order is at least `L ^ c` when the `c` nontrivial lengths are each at least `L`. -/
private theorem pow_card_le_order {L : ℕ} (hL : ∀ r, 1 < ℓ r → L ≤ ℓ r) :
    L ^ (active ℓ).card ≤ order ℓ :=
  Finset.pow_card_le_prod _ _ _ fun r hr => hL r (Finset.mem_filter.mp hr).2

/-- If the ordered-syntax budget for `q` gates is below `order ℓ`, some power below `order ℓ`
requires more than `q` gates. -/
theorem exists_hard_power_of_budget_lt (hℓ : ∀ r, ℓ r < 2 ^ K) (hc : LengthsCoprime ℓ) (q : ℕ)
    (large : signature.orderedBudget (m + K) (m + K) q < order ℓ) :
    ∃ T < order ℓ, ∀ out : Circuit signature (m + K) (m + K),
      out.Computes interpretation (step (K := K) ℓ)^[T] → q < out.size := by
  classical
  let family := Finset.univ.image fun T : Fin (order ℓ) => (step (K := K) ℓ)^[T.val]
  have hcard : family.card = order ℓ := by
    rw [Finset.card_image_of_injective _ (iterate_injective hℓ hc)]
    simp
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := q)
    interpretation family (by rw [hcard]; exact large)
  obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨T.val, T.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by omega) hcomp

/-! ### Hash-class prime candidates -/

/-- The `z`-th candidate of class `r`: `2 ^ (m + g) + (r xor f z) * 2 ^ g + z`. -/
def candidate (g : ℕ) (f : ℕ → ℕ) (r : BitVec m) (z : ℕ) : ℕ :=
  2 ^ (m + g) + (r.toNat ^^^ f z) * 2 ^ g + z

/-- The class length: the prime candidate with least `z < 2 ^ g`, or `1` if there is none. -/
def classPrime (m g : ℕ) (f : ℕ → ℕ) (r : BitVec m) : ℕ :=
  if h : ∃ z, z < 2 ^ g ∧ (candidate g f r z).Prime then
    candidate g f r (Nat.find h) else 1

private theorem candidate_mod {g : ℕ} (f : ℕ → ℕ) (r : BitVec m) {z : ℕ} (hz : z < 2 ^ g) :
    candidate g f r z % 2 ^ g = z := by
  unfold candidate
  rw [pow_add, Nat.add_mod, Nat.add_mod (2 ^ m * 2 ^ g), Nat.mul_mod_left, Nat.mul_mod_left,
    Nat.mod_eq_of_lt hz]
  simp [Nat.mod_eq_of_lt hz]

private theorem candidate_bounds {g : ℕ} {f : ℕ → ℕ} (hf : ∀ z, f z < 2 ^ m) (r : BitVec m)
    {z : ℕ} (hz : z < 2 ^ g) :
    2 ^ (m + g) ≤ candidate g f r z ∧ candidate g f r z < 2 ^ (m + g + 1) := by
  have hx : r.toNat ^^^ f z < 2 ^ m := Nat.xor_lt_two_pow r.isLt (hf z)
  unfold candidate
  generalize r.toNat ^^^ f z = x at hx ⊢
  have : (x + 1) * 2 ^ g ≤ 2 ^ m * 2 ^ g := Nat.mul_le_mul_right _ hx
  rw [pow_succ, pow_add]
  constructor <;> nlinarith

/-- Different classes have disjoint candidate sets. -/
theorem candidate_injective {g : ℕ} (f : ℕ → ℕ) {r s : BitVec m} {y z : ℕ}
    (hy : y < 2 ^ g) (hz : z < 2 ^ g) (h : candidate g f r y = candidate g f s z) : r = s := by
  have hyz : y = z := by
    rw [← candidate_mod f r hy, ← candidate_mod f s hz, h]
  subst hyz
  unfold candidate at h
  have hm : (r.toNat ^^^ f y) * 2 ^ g = (s.toNat ^^^ f y) * 2 ^ g := by omega
  have hx := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos g) hm
  have := congrArg (· ^^^ f y) hx
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
  exact BitVec.eq_of_toNat_eq this

private theorem classPrime_spec {g : ℕ} (f : ℕ → ℕ) (r : BitVec m) :
    classPrime m g f r = 1 ∨
      ∃ z < 2 ^ g, classPrime m g f r = candidate g f r z ∧ (classPrime m g f r).Prime := by
  classical
  unfold classPrime
  split_ifs with h
  · right
    have hs := Nat.find_spec h
    exact ⟨_, hs.1, rfl, hs.2⟩
  · left; rfl

theorem classPrime_bounds {g : ℕ} {f : ℕ → ℕ} (hf : ∀ z, f z < 2 ^ m) (r : BitVec m) :
    classPrime m g f r < 2 ^ (m + g + 1) ∧
      (1 < classPrime m g f r → 2 ^ (m + g) ≤ classPrime m g f r ∧ (classPrime m g f r).Prime) := by
  rcases classPrime_spec (g := g) f r with h | ⟨z, hz, he, hp⟩
  · rw [h]
    exact ⟨Nat.one_lt_two_pow (by omega), by omega⟩
  · rw [he] at hp ⊢
    have hb := candidate_bounds hf r hz
    exact ⟨hb.2, fun _ => ⟨hb.1, hp⟩⟩

/-- Nontrivial class lengths are distinct primes, hence pairwise coprime. -/
theorem classPrime_coprime (g : ℕ) (f : ℕ → ℕ) :
    LengthsCoprime (classPrime m g f) := by
  intro r hr s hs hrs
  have hr' := (Finset.mem_filter.mp hr).2
  have hs' := (Finset.mem_filter.mp hs).2
  rcases classPrime_spec (g := g) f r with h | ⟨y, hy, hey, hpr⟩
  · omega
  rcases classPrime_spec (g := g) f s with h | ⟨z, hz, hez, hps⟩
  · omega
  rw [Nat.coprime_primes hpr hps]
  intro he
  rw [hey, hez] at he
  exact hrs (candidate_injective f hy hz he)

/-- Lower bound for the hash-class permutation: for any mixing function `f` with values below
`2 ^ m`, put `K = m + g + 1` and let `ℓ r` be the least-index prime candidate of class `r`. The
step is a bijection of `BitString (m + K)`, its order is at least `2 ^ ((m + g) * c)` where `c` is
the number of active classes, and if the ordered-syntax exponent for `q` gates is below
`(m + g) * c`, some power `F^[T]` with `T < order` requires more than `q` gates. -/
theorem near_landau_lower_bound (m g : ℕ) (f : ℕ → ℕ) (hf : ∀ z, f z < 2 ^ m) (q h : ℕ)
    (hw : m + (m + g + 1) + q + 1 ≤ 2 ^ h)
    (large : 3 * q + h * (2 * q + (m + (m + g + 1)) + 1) <
      (m + g) * (active (classPrime m g f)).card) :
    Function.Bijective (step (K := m + g + 1) (classPrime m g f)) ∧
      2 ^ ((m + g) * (active (classPrime m g f)).card) ≤ order (classPrime m g f) ∧
      ∃ T < order (classPrime m g f),
        ∀ out : Circuit signature (m + (m + g + 1)) (m + (m + g + 1)),
          out.Computes interpretation (step (K := m + g + 1) (classPrime m g f))^[T] →
            q < out.size := by
  have hℓ : ∀ r, classPrime m g f r < 2 ^ (m + g + 1) := fun r => (classPrime_bounds hf r).1
  have hord : 2 ^ ((m + g) * (active (classPrime m g f)).card) ≤ order (classPrime m g f) := by
    rw [pow_mul]
    exact pow_card_le_order fun r hr => ((classPrime_bounds hf r).2 hr).1
  refine ⟨step_bijective _ hℓ, hord, exists_hard_power_of_budget_lt hℓ (classPrime_coprime g f)
    q ?_⟩
  exact (boolean_orderedBudget_le_pow _ _ q h hw).trans_lt
    ((Nat.pow_lt_pow_right (by decide) large).trans_le hord)

end PrimeCycles

/-! ### Bundled prime-cycle permutation data and circuit synthesis -/

/-- Bundled cycle-length specification for `m`-bit hash classes and `K`-bit cycle positions, with
pairwise coprime nontrivial cycle lengths. -/
structure PrimeCycleData (m K : ℕ) where
  /-- Cycle length assigned to each `m`-bit class. -/
  length : BitVec m → ℕ
  /-- Every cycle length fits in `K` bits. -/
  length_lt : ∀ r, length r < 2 ^ K
  /-- Nontrivial cycle lengths (`1 < length r`) are pairwise coprime. -/
  lengths_coprime : PrimeCycles.LengthsCoprime length

namespace PrimeCycleData

variable {m K : ℕ} (D : PrimeCycleData m K)

/-- The effective cycle length of class `r`, equal to `D.length r` when `1 < D.length r` and `1`
otherwise. -/
def activeLength (r : BitVec m) : ℕ :=
  if 1 < D.length r then D.length r else 1

/-- Natural-number position update for class `r` in one step. -/
def stepNat (r : BitVec m) (b : ℕ) : ℕ :=
  ModulusCounter.advance (D.length r) b 1

/-- Single-step map on `BitString (m + K)`. -/
def step : BitString (m + K) → BitString (m + K) :=
  PrimeCycles.step D.length

theorem step_bijective : Function.Bijective D.step :=
  PrimeCycles.step_bijective D.length D.length_lt

/-- The permutation of `BitString (m + K)` induced by `D.step`. -/
noncomputable def perm : Equiv.Perm (BitString (m + K)) :=
  Equiv.ofBijective D.step D.step_bijective

/-- The order of `D.step`, equal to the product of the nontrivial cycle lengths. -/
def period : ℕ :=
  PrimeCycles.order D.length

theorem period_dvd_of_fixed (T : ℕ) :
    D.step^[T] = id ↔ D.period ∣ T :=
  PrimeCycles.iterate_eq_id_iff D.length_lt D.lengths_coprime T

theorem powers_injective :
    Function.Injective (fun T : Fin D.period => D.step^[T.val]) :=
  PrimeCycles.iterate_injective D.length_lt D.lengths_coprime

theorem exists_hard_power (q : ℕ)
    (large : signature.orderedBudget (m + K) (m + K) q < D.period) :
    ∃ T < D.period, ∀ out : Circuit signature (m + K) (m + K),
      out.Computes interpretation (D.step^[T]) → q < out.size :=
  PrimeCycles.exists_hard_power_of_budget_lt D.length_lt D.lengths_coprime q large

/-- The number of states moved by `D.step` is at most `2 ^ (m + K)`. -/
theorem step_diff_card_le :
    (Finset.univ.filter (fun x : BitString (m + K) => D.step x ≠ x)).card ≤ 2 ^ (m + K) := by
  calc
    (Finset.univ.filter (fun x : BitString (m + K) => D.step x ≠ x)).card ≤
        (Finset.univ : Finset (BitString (m + K))).card := Finset.card_filter_le _ _
    _ = 2 ^ (m + K) := by simp

/-- The `K`-bit cycle-length map on `BitString m` associated with `D`. -/
def lengthBits (r : BitString m) : BitString K :=
  fun i : Fin K => (BitVec.ofNat K (D.length (word r))).getLsbD i.val

@[simp] theorem word_lengthBits (r : BitString m) :
    word (D.lengthBits r) = BitVec.ofNat K (D.length (word r)) :=
  word_getLsbD _

/-- The `K`-bit remainder map `r ↦ T % D.length r` (or `0` when `D.length r = 0`) on
`BitString m`. -/
def remainderBits (T : ℕ) (r : BitString m) : BitString K :=
  fun i : Fin K =>
    (BitVec.ofNat K (if 0 < D.length (word r) then T % D.length (word r) else 0)).getLsbD i.val

@[simp] theorem word_remainderBits (T : ℕ) (r : BitString m) :
    word (D.remainderBits T r) =
      BitVec.ofNat K (if 0 < D.length (word r) then T % D.length (word r) else 0) :=
  word_getLsbD _

/-- Given a circuit `cLen` computing the `K`-bit class length `D.lengthBits`, the single-step
permutation `D.step` has a circuit of size at most `cLen.size + 50 * K + 20`. -/
theorem step_circuit (cLen : Circuit signature m K)
    (hLen : cLen.Computes interpretation D.lengthBits) :
    ∃ out : Circuit signature (m + K) (m + K),
      out.Computes interpretation D.step ∧ out.size ≤ cLen.size + 50 * K + 20 := by
  let init : BitString (m + K) → BitString m := fun x i => x (Fin.castAdd K i)
  let a := fun x : BitString (m + K) => word (cLen.eval interpretation (init x))
  let b := PrimeCycles.posWord (m := m) (K := K)
  let constants : Set (BooleanFunction (m + K)) := {fun _ => false, fun _ => true}
  let s0 := inputs (m + K) ∪ wires (fun x => cLen.eval interpretation (init x))
  let src := s0 ∪ constants
  have hc (v : Bool) : (fun _ : BitString (m + K) => v) ∈ src := by
    cases v <;> simp [src, constants]
  have ha (i : Fin K) : (fun x => (a x).getLsbD i.val) ∈ src := by
    left; right
    simpa only [a, getLsbD_word] using
      (show (fun x => cLen.eval interpretation (init x) i) ∈
        wires (fun x => cLen.eval interpretation (init x)) from ⟨i, rfl⟩)
  have hb (i : Fin K) : (fun x => (b x).getLsbD i.val) ∈ src := by
    left; left
    exact ⟨Fin.natAdd m i, by funext x; simp [b, PrimeCycles.posWord]⟩
  have hcirc := Synthesis.circuit (I := interpretation) (s := inputs (m + K)) cLen
    (fun i x => init x i) (fun i => ⟨Fin.castAdd K i, rfl⟩)
  have hconst : Synthesis interpretation s0 constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hstep := ModulusCounter.synthesis_stepValue src a b ha hb hc
  have htotal : Synthesis interpretation (inputs (m + K))
      (s0 ∪ (constants ∪ wordWires (fun x => ModulusCounter.stepValue (a x) (b x))))
      (cLen.size + 50 * K + 20) := by
    have h1 : Synthesis interpretation (inputs (m + K))
        (s0 ∪ (constants ∪ wordWires (fun x => ModulusCounter.stepValue (a x) (b x))))
        (0 + (cLen.size + (2 + (50 * K + 18)))) := by
      simpa only [s0, wires, Set.union_assoc] using
        (Synthesis.of_subset (I := interpretation)
          (s := inputs (m + K)) (t := inputs (m + K)) Set.Subset.rfl).union
          (hcirc.comp (hconst.comp hstep))
    exact h1.mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hwires : wires D.step ⊆
      s0 ∪ (constants ∪ wordWires (fun x => ModulusCounter.stepValue (a x) (b x))) := by
    rintro _ ⟨bit, rfl⟩
    induction bit using Fin.addCases with
    | left i =>
      left; left
      exact ⟨Fin.castAdd K i, by
        funext x
        simp only [step, PrimeCycles.step, PrimeCycles.power, PrimeCycles.pack, Fin.append_left,
          PrimeCycles.classWord, getLsbD_word]⟩
    | right i =>
      right; right
      refine ⟨i, ?_⟩
      funext x
      simp only [step, PrimeCycles.step, PrimeCycles.power, PrimeCycles.pack, Fin.append_right]
      have ha_eq : a x = BitVec.ofNat K (D.length (PrimeCycles.classWord x)) := by
        dsimp only [a]
        rw [hLen (init x), word_lengthBits]
        rfl
      have ha_toNat : (a x).toNat = D.length (PrimeCycles.classWord x) := by
        rw [ha_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (D.length_lt _)]
      rw [← ha_toNat, ← ModulusCounter.stepValue_spec]
  obtain ⟨out, hcomp, hsize⟩ := (htotal.mono Set.Subset.rfl hwires le_rfl).exists_circuit_outputs
  exact ⟨out, hcomp, hsize⟩

/-- Given circuits `cLen` for `D.lengthBits` and `cRem` for `D.remainderBits T`, the `T`-th power
`D.step^[T]` has a circuit of size at most `cLen.size + cRem.size + 100 * (K + 1)`. -/
theorem power_circuit (T : ℕ) (cLen cRem : Circuit signature m K)
    (hLen : cLen.Computes interpretation D.lengthBits)
    (hRem : cRem.Computes interpretation (D.remainderBits T)) :
    ∃ out : Circuit signature (m + K) (m + K),
      out.Computes interpretation (D.step^[T]) ∧
      out.size ≤ cLen.size + cRem.size + 100 * (K + 1) := by
  let init : BitString (m + K) → BitString m := fun x i => x (Fin.castAdd K i)
  let a := fun x : BitString (m + K) => word (cLen.eval interpretation (init x))
  let b := PrimeCycles.posWord (m := m) (K := K)
  let r := fun x : BitString (m + K) => word (cRem.eval interpretation (init x))
  let s := inputs (m + K) ∪
    (wires (fun x => cLen.eval interpretation (init x)) ∪
      wires (fun x => cRem.eval interpretation (init x)))
  have ha : wordWires a ⊆ s := by
    rintro _ ⟨i, rfl⟩
    right; left
    simpa only [a, getLsbD_word] using
      (show (fun x => cLen.eval interpretation (init x) i) ∈
        wires (fun x => cLen.eval interpretation (init x)) from ⟨i, rfl⟩)
  have hb : wordWires b ⊆ s := by
    rintro _ ⟨i, rfl⟩
    left
    exact ⟨Fin.natAdd m i, by funext x; simp [b, PrimeCycles.posWord]⟩
  have hr : wordWires r ⊆ s := by
    rintro _ ⟨i, rfl⟩
    right; right
    simpa only [r, getLsbD_word] using
      (show (fun x => cRem.eval interpretation (init x) i) ∈
        wires (fun x => cRem.eval interpretation (init x)) from ⟨i, rfl⟩)
  have hs := synthesis_addResidue s a b r ha hb hr
  have hcircLen := Synthesis.circuit (I := interpretation) (s := inputs (m + K)) cLen
    (fun i x => init x i) (fun i => ⟨Fin.castAdd K i, rfl⟩)
  have hcircRem := Synthesis.circuit (I := interpretation) (s := inputs (m + K)) cRem
    (fun i x => init x i) (fun i => ⟨Fin.castAdd K i, rfl⟩)
  have htotal : Synthesis interpretation (inputs (m + K))
      (s ∪ wordWires (fun x => addResidue (a x) (b x) (r x)))
      (cLen.size + cRem.size + 100 * (K + 1)) := by
    simpa only [s, wires, Set.union_assoc, Nat.zero_add] using
      (Synthesis.of_subset (I := interpretation)
        (s := inputs (m + K)) (t := inputs (m + K)) Set.Subset.rfl).union
        ((hcircLen.union hcircRem).comp hs)
  have hspec (x : BitString (m + K)) :
      addResidue (a x) (b x) (r x) =
        BitVec.ofNat K
          (ModulusCounter.advance (D.length (PrimeCycles.classWord x)) (b x).toNat T) := by
    have ha_eq : a x = BitVec.ofNat K (D.length (PrimeCycles.classWord x)) := by
      dsimp only [a]
      rw [hLen (init x), word_lengthBits]
      rfl
    have ha_toNat : (a x).toNat = D.length (PrimeCycles.classWord x) := by
      rw [ha_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (D.length_lt _)]
    have hr_eq : r x =
        BitVec.ofNat K
          (if 0 < D.length (PrimeCycles.classWord x) then
            T % D.length (PrimeCycles.classWord x) else 0) := by
      dsimp only [r]
      rw [hRem (init x), word_remainderBits]
      rfl
    rw [← ha_toNat]
    apply ModulusCounter.addResidue_spec
    intro hpos
    rw [ha_toNat] at hpos ⊢
    rw [hr_eq]
    simp only [hpos, ↓reduceIte, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.mod_lt T hpos).trans (D.length_lt _))
  have hwires : wires (D.step^[T]) ⊆
      s ∪ wordWires (fun x => addResidue (a x) (b x) (r x)) := by
    rw [step, PrimeCycles.iterate_step D.length D.length_lt]
    rintro _ ⟨bit, rfl⟩
    induction bit using Fin.addCases with
    | left i =>
      left; left
      exact ⟨Fin.castAdd K i, by
        funext x
        simp only [PrimeCycles.power, PrimeCycles.pack, Fin.append_left, PrimeCycles.classWord,
          getLsbD_word]⟩
    | right i =>
      right
      refine ⟨i, ?_⟩
      funext x
      simp only [hspec, PrimeCycles.power, PrimeCycles.pack, Fin.append_right, b]
  obtain ⟨out, ho, hsize⟩ := (htotal.mono Set.Subset.rfl hwires le_rfl).exists_circuit_outputs
  exact ⟨out, ho, hsize⟩

/-- Construct `PrimeCycleData` from the hash-class prime construction `PrimeCycles.classPrime`. -/
def ofHash (m g : ℕ) (f : ℕ → ℕ) (hf : ∀ z, f z < 2 ^ m) :
    PrimeCycleData m (m + g + 1) where
  length := PrimeCycles.classPrime m g f
  length_lt r := (PrimeCycles.classPrime_bounds hf r).1
  lengths_coprime := PrimeCycles.classPrime_coprime g f

end PrimeCycleData

end Cslib.Circuits.Boolean.Iteration
