/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.ModulusCounter.Basic
public import Complexity.Computability.Circuit.Boolean.Iteration.ModulusCounter.Remainders
import Mathlib.Tactic.Linarith

/-!
# The modular-counter permutation: exponential lower bounds and typical powers

`Complexity/Computability/Circuit/Boolean/Iteration/ModulusCounter/Basic.lean` defines the
single-step modular-counter permutation `counterStep k` on
`2 k` bits (`ModulusCounter.power 1`), constructs its linear-size De Morgan circuit of size at most
`50 * k + 20`, and proves that its powers below `ModulusCounter.period k = lcm(1, …, 2 ^ k - 1)` are
pairwise distinct.
`Complexity/Computability/Circuit/Boolean/Iteration/ModulusCounter/Remainders.lean` relates counter
powers to integer remainders and
short-exponent circuits.

By Chebyshev's lower bound on `lcmUpto (2 ^ k - 1)` and the ordered-syntax circuit count from
`CircuitCounting.lean`, this file proves that for every `k ≥ 64`:
* some exponent `T < ModulusCounter.period k` requires more than `lowerBudget k =
  2 ^ k / (1024 * (k + 1))` gates (`exists_hard_counter_power`, `counter_power_lower_bound`),
  matching the `2 ^ Θ(n)` fixed-power upper bound up to the constant factor in the exponent;
* at most a `2 ^ (-2 ^ (k - 1))` fraction of exponents below `ModulusCounter.period k` have
  circuits of size at most `lowerBudget k` (`almost_all_counter_powers_hard`,
  `counter_powers_average_complexity`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.easyCounterPowers`,
  `Cslib.Circuits.Boolean.Iteration.hardCounterPowers`: exponents below `period k` computable with
  at most `q` gates, and those requiring more than `q` gates.

## Main results

* `Cslib.Circuits.Boolean.Iteration.description_budget_lt_period`: the De Morgan description budget
  at `lowerBudget k` is strictly smaller than `ModulusCounter.period k` for `k ≥ 64`.
* `Cslib.Circuits.Boolean.Iteration.exists_hard_counter_power`,
  `Cslib.Circuits.Boolean.Iteration.counter_power_lower_bound`: for `k ≥ 64`, `counterStep k` has a
  power requiring more than `2 ^ k / (1024 * (k + 1))` gates.
* `Cslib.Circuits.Boolean.Iteration.almost_all_counter_powers_hard`,
  `Cslib.Circuits.Boolean.Iteration.counter_powers_average_complexity`: all but a
  `2 ^ (-2 ^ (k - 1))` fraction of powers below `period k` require more than `lowerBudget k` gates.
* `Cslib.Circuits.Boolean.Iteration.distinct_counter_powers_up_to`,
  `Cslib.Circuits.Boolean.Iteration.exists_hard_counter_power_up_to`: counting lower bound for
  prefixes `T < M ≤ period k`.

## References

* Adapted from lean/Proofs/{LowerBound,TypicalPowers}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean

variable {k : ℕ}

/-! ### Worst-case and typical-power lower bounds -/

/-- The De Morgan description budget for `lowerBudget k` gates is strictly smaller than
`ModulusCounter.period k` for `k ≥ 64`. -/
theorem description_budget_lt_period (k : ℕ) (hk : 64 ≤ k) :
    signature.orderedBudget (k + k) (k + k) (lowerBudget k) < ModulusCounter.period k := by
  let q := lowerBudget k
  let E := 3 * q + (k + 2) * (2 * q + (k + k) + 1)
  have hb : signature.orderedBudget (k + k) (k + k) q ≤ 2 ^ E :=
    boolean_orderedBudget_le_pow _ _ _ _ (lowerBudget_wire_bound k hk)
  have he : E + k < 2 ^ k - 1 := lowerBudget_description_exponent k hk
  have hp : 2 ^ (E + k) < 2 ^ (2 ^ k - 1) := Nat.pow_lt_pow_right (by decide) he
  have hl := Chebyshev.two_pow_le_mul_lcmUpto (2 ^ k - 1)
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [Nat.sub_add_cancel hN] at hl
  have hh := (Nat.mul_le_mul_right (2 ^ k) hb).trans_lt
    (by rw [← pow_add]; exact hp)
  have hh' := hh.trans_le hl
  change _ < 2 ^ k * ModulusCounter.period k at hh'
  nlinarith

/-- For every `k ≥ 64`, some exponent `T < ModulusCounter.period k` requires more than
`lowerBudget k` gates. -/
theorem exists_hard_counter_power (k : ℕ) (hk : 64 ≤ k) :
    ∃ T < ModulusCounter.period k,
      ∀ out : Circuit signature (k + k) (k + k),
        out.Computes interpretation (ModulusCounter.power (k := k) T) →
          lowerBudget k < out.size := by
  classical
  let family := Finset.univ.image (fun T : Fin (ModulusCounter.period k) =>
    ModulusCounter.power (k := k) T.val)
  have hcard : family.card = ModulusCounter.period k := counter_family_card k
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := lowerBudget k)
    interpretation family (by rw [hcard]; exact description_budget_lt_period k hk)
  obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨T.val, T.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by omega) hcomp

/-- **Matching exponential lower bound.** For every `k ≥ 64`, there is a bijective circuit `c` on
`2 k` bits of size at most `50 * (k + 1)` with a power `c^[T]` (`T < ModulusCounter.period k`)
requiring more than `2 ^ k / (1024 * (k + 1))` gates. -/
theorem counter_power_lower_bound (k : ℕ) (hk : 64 ≤ k) :
    ∃ c : Circuit signature (k + k) (k + k),
      c.size ≤ 50 * (k + 1) ∧ Function.Bijective (c.eval interpretation) ∧
      ∃ T < ModulusCounter.period k,
        ∀ out : Circuit signature (k + k) (k + k),
          out.Computes interpretation (c.eval interpretation)^[T] →
            2 ^ k / (1024 * (k + 1)) < out.size := by
  obtain ⟨c, hc, hs⟩ := ModulusCounter.exists_linear_circuit k
  obtain ⟨T, hT, hh⟩ := exists_hard_counter_power k hk
  have he : c.eval interpretation = ModulusCounter.power (k := k) 1 := funext hc
  refine ⟨c, by omega, he ▸ ModulusCounter.power_bijective, T, hT, ?_⟩
  intro out hout
  rw [he, ModulusCounter.iterate_power] at hout
  exact hh out hout

/-- Exponents below `ModulusCounter.period k` whose power has a circuit of size at most `q`. -/
noncomputable def easyCounterPowers (k q : ℕ) : Finset (Fin (ModulusCounter.period k)) :=
  Finset.univ.filter fun T => ModulusCounter.power (k := k) T.val ∈
    Circuit.functionsAtMost interpretation (k + k) (k + k) q

/-- Exponents below `ModulusCounter.period k` whose power requires more than `q` gates. -/
noncomputable def hardCounterPowers (k q : ℕ) : Finset (Fin (ModulusCounter.period k)) :=
  Finset.univ \ easyCounterPowers k q

theorem mem_easyCounterPowers (k q : ℕ) (T : Fin (ModulusCounter.period k)) :
    T ∈ easyCounterPowers k q ↔
      ∃ c : Circuit signature (k + k) (k + k),
        c.size ≤ q ∧ c.Computes interpretation (ModulusCounter.power T.val) := by
  classical
  simp only [easyCounterPowers, Finset.mem_filter, Finset.mem_univ, true_and,
    Circuit.mem_functionsAtMost_iff]

private theorem easyCounterPowers_card_le (k q : ℕ) :
    (easyCounterPowers k q).card ≤ signature.orderedBudget (k + k) (k + k) q := by
  classical
  have hsub : (easyCounterPowers k q).image (fun T => ModulusCounter.power (k := k) T.val) ⊆
      Circuit.functionsAtMost interpretation (k + k) (k + k) q := by
    intro target ht
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hT).2
  calc
    _ = ((easyCounterPowers k q).image (fun T => ModulusCounter.power (k := k) T.val)).card :=
      (Finset.card_image_of_injective _ ModulusCounter.powers_injective).symm
    _ ≤ _ := (Finset.card_le_card hsub).trans
      (Circuit.card_functionsAtMost_le interpretation)

theorem hardCounterPowers_card_ge (k q : ℕ) :
    ModulusCounter.period k - signature.orderedBudget (k + k) (k + k) q ≤
      (hardCounterPowers k q).card := by
  have hcard : (easyCounterPowers k q).card + (hardCounterPowers k q).card =
      ModulusCounter.period k := by
    classical
    have hsub : easyCounterPowers k q ⊆ Finset.univ := Finset.subset_univ _
    rw [hardCounterPowers, add_comm, Finset.card_sdiff_add_card_eq_card hsub,
      Finset.card_univ, Fintype.card_fin]
  have hle := easyCounterPowers_card_le k q
  omega

/-- The description budget at `lowerBudget k` leaves an additive margin of `2 ^ (k - 1)` in the
binary exponent. -/
private theorem lowerBudget_description_margin (k : ℕ) (hk : 64 ≤ k) :
    let q := lowerBudget k
    3 * q + (k + 2) * (2 * q + (k + k) + 1) + k + 2 ^ (k - 1) ≤ 2 ^ k - 1 := by
  dsimp only
  have hq : lowerBudget k * (1024 * (k + 1)) ≤ 2 ^ k := Nat.div_mul_le_self _ _
  have hs := square_le_exponential k hk
  have hpoly : (k + 2) * (k + k + 1) + k + 2 ≤ 4 * (k + 2) ^ 2 := by nlinarith
  have hcoef : (2 * (k + 2) + 3) * 128 ≤ 1024 * (k + 1) := by omega
  have hq' := Nat.mul_le_mul_right (lowerBudget k) hcoef
  have htotal : 128 * (3 * lowerBudget k +
      (k + 2) * (2 * lowerBudget k + (k + k) + 1) + k + 2) ≤ 5 * 2 ^ k := by
    nlinarith
  have hhalf : 2 ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- **Almost every counter power is hard.** At most a `2 ^ (-2 ^ (k - 1))` fraction of exponents
below `ModulusCounter.period k` have circuits of size at most `lowerBudget k`. -/
theorem almost_all_counter_powers_hard (k : ℕ) (hk : 64 ≤ k) :
    (easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1)) ≤
      ModulusCounter.period k := by
  let E := 3 * lowerBudget k + (k + 2) * (2 * lowerBudget k + (k + k) + 1)
  have heasy : (easyCounterPowers k (lowerBudget k)).card ≤ 2 ^ E :=
    (easyCounterPowers_card_le k _).trans
      (boolean_orderedBudget_le_pow _ _ _ _ (lowerBudget_wire_bound k hk))
  have he : E + 2 ^ (k - 1) + k ≤ 2 ^ k - 1 := by
    have := lowerBudget_description_margin k hk
    dsimp only at this
    dsimp [E]
    omega
  have hl := Chebyshev.two_pow_le_mul_lcmUpto (2 ^ k - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n := k))] at hl
  have hscaled : ((easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1))) * 2 ^ k ≤
      ModulusCounter.period k * 2 ^ k := by
    calc
      _ ≤ (2 ^ E * 2 ^ (2 ^ (k - 1))) * 2 ^ k := by gcongr
      _ = 2 ^ (E + 2 ^ (k - 1) + k) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (2 ^ k - 1) := Nat.pow_le_pow_right (by decide) he
      _ ≤ _ := by simpa only [ModulusCounter.period, Nat.mul_comm] using hl
  exact Nat.le_of_mul_le_mul_right hscaled (by positivity)

/-- For `k ≥ 64`, more than half of the exponents below `ModulusCounter.period k` lie in
`hardCounterPowers k (lowerBudget k)`. -/
theorem counter_powers_average_complexity (k : ℕ) (hk : 64 ≤ k) :
    ModulusCounter.period k < 2 * (hardCounterPowers k (lowerBudget k)).card := by
  have hcard : (easyCounterPowers k (lowerBudget k)).card +
      (hardCounterPowers k (lowerBudget k)).card = ModulusCounter.period k := by
    classical
    have hsub : easyCounterPowers k (lowerBudget k) ⊆ Finset.univ := Finset.subset_univ _
    rw [hardCounterPowers, add_comm, Finset.card_sdiff_add_card_eq_card hsub,
      Finset.card_univ, Fintype.card_fin]
  have halmost := almost_all_counter_powers_hard k hk
  have hpow : 2 < 2 ^ (2 ^ (k - 1)) := by
    have hk1 : 1 < 2 ^ (k - 1) := Nat.one_lt_two_pow (by omega)
    exact (show 2 = 2 ^ 1 by rfl) ▸ Nat.pow_lt_pow_right (by decide) hk1
  have hpos : 0 < ModulusCounter.period k := Nat.lcmUpto_pos _
  by_contra! hle
  have heasy_ge : ModulusCounter.period k ≤ 2 * (easyCounterPowers k (lowerBudget k)).card := by
    omega
  have h1 : 0 < (easyCounterPowers k (lowerBudget k)).card := by omega
  have h2 : 2 * (easyCounterPowers k (lowerBudget k)).card <
      (easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1)) := by
    calc
      2 * (easyCounterPowers k (lowerBudget k)).card =
          (easyCounterPowers k (lowerBudget k)).card * 2 := Nat.mul_comm _ _
      _ < (easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1)) :=
        Nat.mul_lt_mul_of_pos_left hpow h1
  omega

/-- All powers `ModulusCounter.power T` for `T < M` with `M ≤ ModulusCounter.period k` are
pairwise distinct. -/
theorem distinct_counter_powers_up_to {M : ℕ} (hM : M ≤ ModulusCounter.period k) :
    Function.Injective (fun T : Fin M => ModulusCounter.power (k := k) T.val) := by
  intro S T h
  have heq := ModulusCounter.powers_injective
    (a₁ := ⟨S.val, Nat.lt_of_lt_of_le S.isLt hM⟩)
    (a₂ := ⟨T.val, Nat.lt_of_lt_of_le T.isLt hM⟩) h
  exact Fin.ext (congrArg (fun a : Fin (ModulusCounter.period k) => a.val) heq)

/-- If `signature.orderedBudget (k + k) (k + k) q < M` and `M ≤ ModulusCounter.period k`, some
exponent `T < M` requires more than `q` gates. -/
theorem exists_hard_counter_power_up_to {M q : ℕ} (hM : M ≤ ModulusCounter.period k)
    (large : signature.orderedBudget (k + k) (k + k) q < M) :
    ∃ T < M, ∀ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (ModulusCounter.power (k := k) T) → q < out.size := by
  classical
  let family := Finset.univ.image (fun T : Fin M => ModulusCounter.power (k := k) T.val)
  have hcard : family.card = M := by
    rw [Finset.card_image_of_injective _ (distinct_counter_powers_up_to hM), Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := q)
    interpretation family (by rw [hcard]; exact large)
  obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨T.val, T.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by omega) hcomp

end Cslib.Circuits.Boolean.Iteration
