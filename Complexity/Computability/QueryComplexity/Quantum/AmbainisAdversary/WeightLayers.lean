/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Quantum.AmbainisAdversary
public import Complexity.Foundations.Data.BitString.Weight
import Complexity.Foundations.Data.BitString.WeightInterval
import Complexity.Foundations.Quantum.Measurement.Overlap

/-!
# Telling two weight layers apart by the adversary method

Let `a < b ≤ N`. Relate every input `x` of weight `a` to every `y ⊇ x` of weight `b`. Then:
* every `x` has `C(N - a, b - a)` partners, and every `y` has `C(b, a)`;
* among the partners of `x`, those that differ from it at a fixed `i` number at most
  `C(N - a - 1, b - a - 1)`;
* among the partners of `y`, those that differ from it at `i` number at most `C(b - 1, a)`.

Ambainis's bound (`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt`, [Ambainis2002],
Theorem 6) and the binomial identities
`C(N - a - 1, b - a - 1) (N - a) = C(N - a, b - a) (b - a)` and `C(b - 1, a) b = C(b, a) (b - a)`
give `(1 - δ) √((N - a) b) ≤ 2T (b - a)` when the final overlaps on related pairs are at most `δ`
(`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sub_of_le`). This is the relation that
[Ambainis2002], Theorem 5, uses for `a = N/2` and `b = (1 + ε)N/2`.

With bounded error `ε ≤ 1/2`, an algorithm that accepts weight `k` and rejects weight `k' ≠ k`,
and need not be correct on any other input, has:
* `(1 - 2√(ε(1-ε))) √((N - a) b) ≤ 2T |k - k'|` with `a = min k k'` and `b = max k k'`
  (`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_abs_sub_of_weight`). For `k' = k - 1` this is
  `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_weight`.
* `(1 - 2√(ε(1-ε))) (√(N |k - k'|) + √(m (N - m))) ≤ 4T |k - k'|` for every `m` between `k` and
  `k'` (`Cslib.Quantum.one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight`). This is
  [NayakWu1999], Corollary 1.2, `Ω(√(N/Δ) + √(m(N-m))/Δ)`, which the source proves by the
  polynomial method. It follows from `(N - a) b ≥ N (b - a)` and `(N - a) b ≥ m (N - m)`.
* `(1 - 2√(ε(1-ε))) N ≤ 4T |k - k'|` when `min k k' ≤ N/2 ≤ max k k'`
  (`Cslib.Quantum.one_sub_mul_card_le_four_mul_mul_abs_sub_of_weight`). This is the setting of
  [Ambainis2002], Theorem 5, and gives `Ω(1/ε')` for weights `N/2` against `(1 + ε')N/2`.

The constants are those of this proof. The sources state `Ω(·)` bounds.

## Main results

* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sub_of_le`: the δ-form for weights `a < b`.
* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_abs_sub_of_weight`: weight `k` against `k'`.
* `Cslib.Quantum.one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight`: the Nayak–Wu bound.
* `Cslib.Quantum.one_sub_mul_card_le_four_mul_mul_abs_sub_of_weight`: weights on both sides of
  `N/2`.

## References

* [A. Ambainis, *Quantum lower bounds by quantum arguments*][Ambainis2002]
* [A. Nayak, F. Wu, *The quantum query complexity of approximating the median and related
  statistics*][NayakWu1999]
-/

public section

namespace Cslib.Quantum

open Finset Function BitString

variable {N : ℕ} {W : Type*} [Fintype W]

variable (U : ℕ → State N W →ₗᵢ[ℂ] State N W)

/-- **Telling weight `a` from weight `b`**, the δ-form: let `a < b ≤ N`, and let a `T`-query
algorithm with a unit initial state end in states with overlap at most `δ` on every pair `x ≤ y`
with `|x| = a` and `|y| = b`. Then `(1 - δ) √((N - a) b) ≤ 2T (b - a)`. This is the containment
relation of [Ambainis2002], Theorem 5, for general `a < b`. The constant is that of this proof. -/
theorem one_sub_mul_sqrt_le_two_mul_mul_sub_of_le {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) {a b : ℕ} (hab : a < b) (hbN : b ≤ N) {δ : ℝ}
    (hδ : ∀ x y : BitString N, weight x = a → weight y = b → x ≤ y →
      ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ δ) :
    (1 - δ) * √((N - a) * b) ≤ 2 * T * (b - a) := by
  classical
  have card_ge (x : BitString N) : #{y : BitString N | x ≤ y ∧ weight y = b} =
      (N - weight x).choose (N - b) := by
    simpa using card_filter_ge_and_weight_eq x (by simpa using hbN)
  set R : Finset (BitString N × BitString N) :=
    (weightLayer N a ×ˢ weightLayer N b).filter fun p => p.1 ≤ p.2 with hRdef
  have hmemR {x y : BitString N} : (x, y) ∈ R ↔ weight x = a ∧ weight y = b ∧ x ≤ y := by
    simp [hRdef, and_assoc]
  have hR : R.Nonempty := by
    obtain ⟨y, hy⟩ := weightLayer_nonempty hbN
    have hy' : weight y = b := mem_weightLayer.1 hy
    have : 0 < #{x : BitString N | x ≤ y ∧ weight x = a} := by
      rw [card_filter_le_and_weight_eq, hy']
      exact Nat.choose_pos hab.le
    obtain ⟨x, hx⟩ := card_pos.1 this
    obtain ⟨hxy, hxa⟩ := (mem_filter.1 hx).2
    exact ⟨(x, y), hmemR.2 ⟨hxa, hy', hxy⟩⟩
  have hδR : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ := fun p hp => by
    obtain ⟨h1, h2, h3⟩ := hmemR.1 hp
    exact hδ p.1 p.2 h1 h2 h3
  have hm : ∀ p ∈ R, (N - a).choose (N - b) ≤ #{q ∈ R | q.1 = p.1} := by
    intro p hp
    obtain ⟨h1, -, -⟩ := hmemR.1 hp
    rw [← h1, ← card_ge p.1]
    refine card_le_card_of_injOn (fun y => (p.1, y)) (fun y hy => ?_) (fun y _ z _ h => ?_)
    · obtain ⟨hy1, hy2⟩ := (mem_filter.1 hy).2
      exact mem_filter.2 ⟨hmemR.2 ⟨h1, hy2, hy1⟩, rfl⟩
    · exact congrArg Prod.snd h
  have hm' : ∀ p ∈ R, b.choose a ≤ #{q ∈ R | q.2 = p.2} := by
    intro p hp
    obtain ⟨-, h2, -⟩ := hmemR.1 hp
    rw [← h2, ← card_filter_le_and_weight_eq p.2 a]
    refine card_le_card_of_injOn (fun x => (x, p.2)) (fun x hx => ?_) (fun x _ z _ h => ?_)
    · obtain ⟨hx1, hx2⟩ := (mem_filter.1 hx).2
      exact mem_filter.2 ⟨hmemR.2 ⟨hx2, h2, hx1⟩, rfl⟩
    · exact congrArg Prod.fst h
  have hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤
        (N - a - 1).choose (N - b) * (b - 1).choose a := by
    intro p hp i hi
    obtain ⟨h1, h2, h12⟩ := hmemR.1 hp
    obtain ⟨hp1, hp2⟩ := Bool.lt_iff.1 (lt_of_le_of_ne (h12 i) hi)
    refine Nat.mul_le_mul ?_ ?_
    · have hw : weight (update p.1 i true) = a + 1 := by rw [weight_update_true hp1, h1]
      rw [show N - a - 1 = N - weight (update p.1 i true) by omega, ← card_ge _]
      refine card_le_card_of_injOn Prod.snd (fun q hq => ?_) (fun q hq r hr h => ?_)
      · obtain ⟨hqR, hqi, hq1⟩ := mem_filter.1 hq
        obtain ⟨-, hq2, hq12⟩ := hmemR.1 hqR
        obtain ⟨-, hqi2⟩ := Bool.lt_iff.1 (lt_of_le_of_ne (hq12 i) hqi)
        refine mem_filter.2 ⟨mem_univ _, fun j => ?_, hq2⟩
        by_cases hj : j = i
        · subst hj
          simp [hqi2]
        · rw [update_of_ne hj, ← hq1]
          exact hq12 j
      · obtain ⟨-, -, hq1⟩ := mem_filter.1 hq
        obtain ⟨-, -, hr1⟩ := mem_filter.1 hr
        exact Prod.ext (hq1.trans hr1.symm) h
    · have hw : weight (update p.2 i false) = b - 1 := by
        have := weight_update_false hp2
        omega
      rw [show b - 1 = weight (update p.2 i false) from hw.symm,
        ← card_filter_le_and_weight_eq]
      refine card_le_card_of_injOn Prod.fst (fun q hq => ?_) (fun q hq r hr h => ?_)
      · obtain ⟨hqR, hqi, hq2⟩ := mem_filter.1 hq
        obtain ⟨hq1, -, hq12⟩ := hmemR.1 hqR
        obtain ⟨hqi1, -⟩ := Bool.lt_iff.1 (lt_of_le_of_ne (hq12 i) hqi)
        refine mem_filter.2 ⟨mem_univ _, fun j => ?_, hq1⟩
        by_cases hj : j = i
        · subst hj
          simp [hqi1]
        · rw [update_of_ne hj, ← hq2]
          exact hq12 j
      · obtain ⟨-, -, hq2⟩ := mem_filter.1 hq
        obtain ⟨-, -, hr2⟩ := mem_filter.1 hr
        exact Prod.ext h (hq2.trans hr2.symm)
  have hcore := one_sub_mul_sqrt_le_two_mul_mul_sqrt U hψ₀ T hR hδR hm hm' hL
  -- the binomial identities `l (N - a) = m (b - a)` and `l' b = m' (b - a)`
  have hx := Nat.choose_mul_succ_eq (N - a - 1) (N - b)
  rw [show N - a - 1 + 1 = N - a by omega, show N - a - (N - b) = b - a by omega] at hx
  have hy := Nat.choose_mul_succ_eq (b - 1) a
  rw [show b - 1 + 1 = b by omega] at hy
  have hl : 0 < (N - a - 1).choose (N - b) := Nat.choose_pos (by omega)
  have hl' : 0 < (b - 1).choose a := Nat.choose_pos (by omega)
  set m := (N - a).choose (N - b)
  set m' := b.choose a
  set l := (N - a - 1).choose (N - b)
  set l' := (b - 1).choose a
  have hkey : (N - a) * b * (l * l') = (b - a) * (b - a) * (m * m') := by
    calc (N - a) * b * (l * l') = (l * (N - a)) * (l' * b) := by ring
      _ = (m * (b - a)) * (m' * (b - a)) := by rw [hx, hy]
      _ = (b - a) * (b - a) * (m * m') := by ring
  have hkeyR : ((N : ℝ) - a) * b * ((l : ℝ) * l') = ((b : ℝ) - a) * (b - a) * (m * m') := by
    have := congrArg (Nat.cast : ℕ → ℝ) hkey
    push_cast [Nat.cast_sub hab.le, Nat.cast_sub (hab.trans_le hbN).le] at this
    exact this
  rw [Nat.cast_mul] at hcore
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hbNR : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hba : (0 : ℝ) ≤ b - a := by linarith
  rcases le_or_gt 1 δ with h1 | h1
  · have : (1 - δ) * √((N - a) * b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
    exact this.trans (mul_nonneg (by positivity) hba)
  have hLpos : (0 : ℝ) < √((l : ℝ) * l') :=
    Real.sqrt_pos.2 (mul_pos (by exact_mod_cast hl) (by exact_mod_cast hl'))
  have h0 : (0 : ℝ) ≤ (N - a) * b := mul_nonneg (by linarith) (Nat.cast_nonneg b)
  have hsq : √(((N : ℝ) - a) * b) * √((l : ℝ) * l') = √((m : ℝ) * m') * (b - a) := by
    rw [← Real.sqrt_mul h0, hkeyR, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hba,
      mul_comm]
  have key : (1 - δ) * √(((N : ℝ) - a) * b) * √((l : ℝ) * l') ≤
      2 * T * (b - a) * √((l : ℝ) * l') := by
    calc (1 - δ) * √(((N : ℝ) - a) * b) * √((l : ℝ) * l')
        = (1 - δ) * √((m : ℝ) * m') * (b - a) := by rw [mul_assoc, hsq, ← mul_assoc]
      _ ≤ 2 * T * √((l : ℝ) * l') * (b - a) := mul_le_mul_of_nonneg_right hcore hba
      _ = 2 * T * (b - a) * √((l : ℝ) * l') := by ring
  exact le_of_mul_le_mul_right key hLpos

/-- **Telling weight `k` from weight `k'`** [Ambainis2002], Theorem 5, for general weights: if a
`T`-query algorithm with a unit initial state accepts, by an outcome in `S`, every input of weight
`k` with probability at least `1 - ε` and every input of weight `k' ≠ k` with probability at most
`ε ≤ 1/2`, and need not be correct on any other input, then, with `a = min k k'` and
`b = max k k'`, `(1 - 2√(ε(1-ε))) √((N - a) b) ≤ 2T |k - k'|`. For `k' = k - 1` this is
`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_weight`. The constant is that of this proof. -/
theorem one_sub_mul_sqrt_le_two_mul_mul_abs_sub_of_weight {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {k k' : ℕ} (hkk' : k ≠ k')
    (hk : k ≤ N) (hk' : k' ≤ N) {ε : ℝ}
    (h₁ : ∀ x : BitString N, weight x = k → 1 - ε ≤ measureProb (run U ψ₀ x T) S)
    (h₂ : ∀ y : BitString N, weight y = k' → measureProb (run U ψ₀ y T) S ≤ ε)
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √((N - (min k k' : ℕ)) * (max k k' : ℕ)) ≤
      2 * T * |(k : ℝ) - k'| := by
  have hδ : ∀ x y : BitString N, weight x = k → weight y = k' →
      ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ y T)‖ ≤ 2 * √(ε * (1 - ε)) := fun x y hx hy =>
    norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀]) (by rw [norm_run, hψ₀])
      (h₁ x hx) (h₂ y hy) hε
  rcases Nat.lt_or_gt_of_ne hkk' with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h.le))]
    exact one_sub_mul_sqrt_le_two_mul_mul_sub_of_le U hψ₀ T h hk'
      fun x y hx hy _ => hδ x y hx hy
  · rw [min_eq_right h.le, max_eq_left h.le,
      abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h.le))]
    exact one_sub_mul_sqrt_le_two_mul_mul_sub_of_le U hψ₀ T h hk fun x y hx hy _ => by
      rw [norm_inner_symm]
      exact hδ y x hy hx

/-- **The Nayak–Wu bound** [NayakWu1999], Corollary 1.2, with the constants of this proof: if a
`T`-query algorithm with a unit initial state accepts, by an outcome in `S`, every input of weight
`k` with probability at least `1 - ε` and every input of weight `k' ≠ k` with probability at most
`ε ≤ 1/2`, then for every `m` between `k` and `k'`,
`(1 - 2√(ε(1-ε))) (√(N |k - k'|) + √(m (N - m))) ≤ 4T |k - k'|`. Dividing by `|k - k'|` gives the
source's `Ω(√(N/Δ) + √(m(N-m))/Δ)`, where the source takes `m ∈ {k, k'}` farther from `N/2`. The
source proves it by the polynomial method; this proof is by the adversary method. -/
theorem one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {k k' : ℕ} (hkk' : k ≠ k')
    (hk : k ≤ N) (hk' : k' ≤ N) {ε : ℝ}
    (h₁ : ∀ x : BitString N, weight x = k → 1 - ε ≤ measureProb (run U ψ₀ x T) S)
    (h₂ : ∀ y : BitString N, weight y = k' → measureProb (run U ψ₀ y T) S ≤ ε)
    (hε : 2 * ε ≤ 1) {m : ℕ} (hm : min k k' ≤ m) (hm' : m ≤ max k k') :
    (1 - 2 * √(ε * (1 - ε))) * (√(N * |(k : ℝ) - k'|) + √(m * (N - m))) ≤
      4 * T * |(k : ℝ) - k'| := by
  have hmain := one_sub_mul_sqrt_le_two_mul_mul_abs_sub_of_weight U hψ₀ T S hkk'
    hk hk' h₁ h₂ hε
  have hc := one_sub_two_mul_sqrt_nonneg ε
  set a := min k k' with ha
  set b := max k k' with hb
  have hab : a ≤ b := min_le_max
  have hbN : b ≤ N := max_le hk hk'
  have habs : |(k : ℝ) - k'| = b - a := by
    rcases le_total k k' with h | h
    · rw [ha, hb, min_eq_left h, max_eq_right h, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h))]
    · rw [ha, hb, min_eq_right h, max_eq_left h,
        abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h))]
  rw [habs] at hmain ⊢
  have haR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbR : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hmR : (a : ℝ) ≤ m := by exact_mod_cast hm
  have hmR' : (m : ℝ) ≤ b := by exact_mod_cast hm'
  have h₁' : √(N * ((b : ℝ) - a)) ≤ √((N - a) * b) :=
    Real.sqrt_le_sqrt (by nlinarith [Nat.cast_nonneg (α := ℝ) a])
  have h₂' : √((m : ℝ) * (N - m)) ≤ √((N - a) * b) :=
    Real.sqrt_le_sqrt (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
  calc (1 - 2 * √(ε * (1 - ε))) * (√(N * ((b : ℝ) - a)) + √(m * (N - m)))
      ≤ (1 - 2 * √(ε * (1 - ε))) * (2 * √((N - a) * b)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
    _ = 2 * ((1 - 2 * √(ε * (1 - ε))) * √((N - a) * b)) := by ring
    _ ≤ 2 * (2 * T * (b - a)) := by linarith
    _ = 4 * T * (b - a) := by ring

/-- **Weights on both sides of `N/2`**, the setting of [Ambainis2002], Theorem 5: if a `T`-query
algorithm with a unit initial state accepts, by an outcome in `S`, every input of weight `k` with
probability at least `1 - ε` and every input of weight `k' ≠ k` with probability at most
`ε ≤ 1/2`, and `min k k' ≤ N/2 ≤ max k k'`, then `(1 - 2√(ε(1-ε))) N ≤ 4T |k - k'|`. For
`k = N/2` and `k' = (1 + ε')N/2` this is `Ω(1/ε')`, the bound behind the `ε'`-approximate median
lower bound of [NayakWu1999]. -/
theorem one_sub_mul_card_le_four_mul_mul_abs_sub_of_weight {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {k k' : ℕ} (hkk' : k ≠ k')
    (hN : 2 * min k k' ≤ N) (hN' : N ≤ 2 * max k k') (hk : k ≤ N) (hk' : k' ≤ N) {ε : ℝ}
    (h₁ : ∀ x : BitString N, weight x = k → 1 - ε ≤ measureProb (run U ψ₀ x T) S)
    (h₂ : ∀ y : BitString N, weight y = k' → measureProb (run U ψ₀ y T) S ≤ ε)
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * N ≤ 4 * T * |(k : ℝ) - k'| := by
  have hmain := one_sub_mul_sqrt_le_two_mul_mul_abs_sub_of_weight U hψ₀ T S hkk'
    hk hk' h₁ h₂ hε
  have hc := one_sub_two_mul_sqrt_nonneg ε
  have haR : 2 * ((min k k' : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  have hbR : (N : ℝ) ≤ 2 * ((max k k' : ℕ) : ℝ) := by exact_mod_cast hN'
  have hsq : (N : ℝ) / 2 ≤ √((N - (min k k' : ℕ)) * (max k k' : ℕ)) :=
    Real.le_sqrt_of_sq_le (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  calc (1 - 2 * √(ε * (1 - ε))) * N
      = 2 * ((1 - 2 * √(ε * (1 - ε))) * (N / 2)) := by ring
    _ ≤ 2 * ((1 - 2 * √(ε * (1 - ε))) * √((N - (min k k' : ℕ)) * (max k k' : ℕ))) := by
        gcongr
    _ ≤ 2 * (2 * T * |(k : ℝ) - k'|) := by linarith
    _ = 4 * T * |(k : ℝ) - k'| := by ring

end Cslib.Quantum
