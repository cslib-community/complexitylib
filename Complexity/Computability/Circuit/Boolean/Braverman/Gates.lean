/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.BooleanAnalysis.Bernoulli
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Braverman's real gate approximators

Over `ℝ`, the conjunction of bits `b₁, …, b_K` is approximated by
`∏_c (1 - ∑_{j ∈ S c} (1 - bⱼ))` for a family `S` of sets of arguments (`andApprox`), and the
disjunction by its De Morgan dual `1 - ∏_c (1 - ∑_{j ∈ S c} bⱼ)` (`orApprox`). At bits, a factor
is `1` minus the number of zeros in its set, so the approximator is exact unless some argument is
`0` and no set contains exactly one zero (`AndMiss`, `andApprox_bitVal`). Negation is exactly
`1 - b`. Each approximator multiplies degrees by the number of sets (`gateApprox_mem_lowDegree`)
and its values stay bounded on bounded arguments (`abs_andApprox_le`, `abs_orApprox_le`,
`abs_gateApprox_le`).

Following [Braverman, Lemma 8][Braverman2010], take `s` sets at each of the rates
`2⁻¹, …, 2⁻ℓ`. When the arguments have `z ≥ 1` zeros and `2 ^ r ≤ z < 2 ^ (r + 1)`, a random set of
rate `p = 2 ^ -(r + 1)` contains exactly one zero with probability
`z p (1 - p) ^ (z - 1) ≥ 1 / (2e) > 9 / 50`. So the `s` sets of that rate all miss with probability
at most `(41 / 50) ^ s`, and averaging over the sets against any weights `ν` on the inputs fixes
sets whose misses have weight at most `(41 / 50) ^ s` times the total (`exists_sum_gateMiss_le`).
Braverman pads the fan-in to `k = 2 ^ ℓ` and also needs the rate `1 / (2k)` when all `k`
arguments are `0`; here the fan-in is assumed to be less than `2 ^ ℓ`, which avoids that case. We
choose the sets greedily, one at a time, each by an average over a single random set; the
constant `41 / 50` is Braverman's `0.82`.

The sup-norm bounds are our own; they replace [Braverman, Proposition 9][Braverman2010] in the
circuit-level approximation (`Braverman.exists_lowDegree_approx`).

## Main definitions

* `Cslib.Circuits.Boolean.Braverman.andApprox`, `Cslib.Circuits.Boolean.Braverman.orApprox`,
  `Cslib.Circuits.Boolean.Braverman.gateApprox`: the real approximators for a family of sets.
* `Cslib.Circuits.Boolean.Braverman.AndMiss`, `Cslib.Circuits.Boolean.Braverman.GateMiss`: the
  bits at which an approximator may err.

## Main results

* `Cslib.Circuits.Boolean.Braverman.gateApprox_bitVal`: exactness away from misses.
* `Cslib.Circuits.Boolean.Braverman.gateApprox_mem_lowDegree`: the degree bound.
* `Cslib.Circuits.Boolean.Braverman.abs_gateApprox_le`: the sup-norm bound.
* `Cslib.Circuits.Boolean.Braverman.exists_sum_gateMiss_le`: Braverman's choice of sets.

## References

* [M. Braverman, *Polylogarithmic independence fools AC⁰ circuits*][Braverman2010]
-/

public section

namespace Cslib.Circuits.Boolean.Braverman

open Finset BitString

section Approximators

variable {κ : Type*} [Fintype κ] {K : ℕ}

/-- Braverman's AND approximator for a family `S` of sets of arguments: the product over the sets
of `1 - ∑_{j ∈ S c} (1 - v j)` [Braverman, Lemma 8][Braverman2010]. -/
@[expose] noncomputable def andApprox (S : κ → Fin K → Bool) (v : Fin K → ℝ) : ℝ :=
  ∏ c, (1 - ∑ j with S c j = true, (1 - v j))

/-- The OR approximator, the De Morgan dual of `andApprox` (`orApprox_eq`). -/
@[expose] noncomputable def orApprox (S : κ → Fin K → Bool) (v : Fin K → ℝ) : ℝ :=
  1 - ∏ c, (1 - ∑ j with S c j = true, v j)

/-- The OR approximator is the De Morgan dual of the AND approximator. -/
theorem orApprox_eq (S : κ → Fin K → Bool) (v : Fin K → ℝ) :
    orApprox S v = 1 - andApprox S fun j => 1 - v j := by
  simp only [orApprox, andApprox, sub_sub_cancel]

/-- The AND approximator for `S` misses at the bits `b` when some bit is `false` but no set of `S`
contains exactly one `false` bit. -/
@[expose] def AndMiss (S : κ → Fin K → Bool) (b : Fin K → Bool) : Prop :=
  (∃ j, b j = false) ∧ ∀ c, #{j | S c j = true ∧ b j = false} ≠ 1

instance (S : κ → Fin K → Bool) (b : Fin K → Bool) : Decidable (AndMiss S b) :=
  inferInstanceAs
    (Decidable ((∃ j, b j = false) ∧ ∀ c, #{j | S c j = true ∧ b j = false} ≠ 1))

/-- At bits, a factor of the AND approximator is `1` minus the number of zeros in its set. -/
private theorem sum_one_sub_bitVal (T : Fin K → Bool) (b : Fin K → Bool) :
    ∑ j with T j = true, (1 - bitVal ℝ (b j)) = (#{j | T j = true ∧ b j = false} : ℝ) := by
  rw [sum_filter, ← sum_boole]
  refine sum_congr rfl fun j _ => ?_
  cases T j <;> cases b j <;> simp [bitVal]

/-- **Exactness of the AND approximator** at bits where it does not miss. -/
theorem andApprox_bitVal {S : κ → Fin K → Bool} {b : Fin K → Bool} (h : ¬AndMiss S b) :
    andApprox S (fun j => bitVal ℝ (b j)) = bitVal ℝ (decide (∀ j, b j = true)) := by
  by_cases hb : ∀ j, b j = true
  · rw [decide_eq_true hb, bitVal_true, andApprox]
    exact prod_eq_one fun c _ => by simp [hb]
  · obtain ⟨j, hj⟩ : ∃ j, b j = false := by simpa using hb
    have h' : ¬∀ c, #{j | S c j = true ∧ b j = false} ≠ 1 := fun hall => h ⟨⟨j, hj⟩, hall⟩
    obtain ⟨c, hc⟩ := not_forall.1 h'
    rw [not_not] at hc
    rw [decide_eq_false hb, bitVal_false, andApprox]
    exact prod_eq_zero (mem_univ c) (by rw [sum_one_sub_bitVal, hc]; norm_num)

/-- **Exactness of the OR approximator** at bits whose negations the AND approximator does not
miss. -/
theorem orApprox_bitVal {S : κ → Fin K → Bool} {b : Fin K → Bool}
    (h : ¬AndMiss S fun j => !b j) :
    orApprox S (fun j => bitVal ℝ (b j)) = bitVal ℝ (decide (∃ j, b j = true)) := by
  rw [orApprox_eq]
  simp only [← bitVal_not]
  rw [andApprox_bitVal h, ← bitVal_not]
  congr 1
  by_cases hb : ∃ j, b j = true <;> simp_all

/-- The AND approximator multiplies degrees by the number of sets. -/
theorem andApprox_mem_lowDegree {ι : Type*} {D : ℕ} (S : κ → Fin K → Bool)
    {v : Fin K → (ι → Bool) → ℝ} (hv : ∀ j, v j ∈ lowDegree ℝ ι D) :
    (fun x => andApprox S fun j => v j x) ∈ lowDegree ℝ ι (Fintype.card κ * D) := by
  have h : (fun x => andApprox S fun j => v j x) =
      ∏ c, (1 - ∑ j with S c j = true, (1 - v j)) := by
    funext x
    simp only [andApprox, Finset.prod_apply, Pi.sub_apply, Finset.sum_apply, Pi.one_apply]
  rw [h, ← card_univ]
  exact prod_mem_lowDegree _ fun c _ => one_sub_mem_lowDegree
    (sum_mem_lowDegree _ fun j _ => one_sub_mem_lowDegree (hv j))

/-- The OR approximator multiplies degrees by the number of sets. -/
theorem orApprox_mem_lowDegree {ι : Type*} {D : ℕ} (S : κ → Fin K → Bool)
    {v : Fin K → (ι → Bool) → ℝ} (hv : ∀ j, v j ∈ lowDegree ℝ ι D) :
    (fun x => orApprox S fun j => v j x) ∈ lowDegree ℝ ι (Fintype.card κ * D) := by
  have h := one_sub_mem_lowDegree (andApprox_mem_lowDegree S (v := fun j => 1 - v j)
    fun j => one_sub_mem_lowDegree (hv j))
  convert h using 1
  funext x
  simp only [orApprox_eq, Pi.sub_apply, Pi.one_apply]

/-- A factor `1 - ∑_{j ∈ T} w j` is at most `1 + K B` in absolute value when every `|w j| ≤ B`. -/
private theorem abs_one_sub_sum_le {T : Fin K → Bool} {w : Fin K → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ j, |w j| ≤ B) : |1 - ∑ j with T j = true, w j| ≤ 1 + K * B := by
  calc |1 - ∑ j with T j = true, w j| ≤ |1| + |∑ j with T j = true, w j| := abs_sub _ _
    _ ≤ 1 + ∑ j with T j = true, |w j| := by
        rw [abs_one]
        exact add_le_add_right (abs_sum_le_sum_abs _ _) 1
    _ ≤ 1 + ∑ j with T j = true, B := add_le_add_right (sum_le_sum fun j _ => hw j) 1
    _ ≤ 1 + K * B := by
        rw [sum_const, nsmul_eq_mul]
        have : (#{j | T j = true} : ℝ) ≤ K := by
          exact_mod_cast (card_filter_le _ _).trans (card_univ.trans (Fintype.card_fin K)).le
        nlinarith

/-- A product of factors `1 - ∑_{j ∈ T c} w j` is at most `(1 + K B) ^ |κ|` in absolute value. -/
private theorem abs_prod_le {T : κ → Fin K → Bool} {w : Fin K → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ j, |w j| ≤ B) :
    |∏ c, (1 - ∑ j with T c j = true, w j)| ≤ (1 + K * B) ^ Fintype.card κ := by
  rw [abs_prod, ← card_univ, ← prod_const]
  exact prod_le_prod₀ (fun _ _ => abs_nonneg _) fun c _ => abs_one_sub_sum_le hB hw

/-- **Sup-norm bound for the AND approximator.** -/
theorem abs_andApprox_le (S : κ → Fin K → Bool) {v : Fin K → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ j, |v j| ≤ B) : |andApprox S v| ≤ (1 + K * (1 + B)) ^ Fintype.card κ :=
  abs_prod_le (by positivity) fun j =>
    (abs_sub _ _).trans (by rw [abs_one]; exact add_le_add_right (hv j) 1)

/-- **Sup-norm bound for the OR approximator.** -/
theorem abs_orApprox_le (S : κ → Fin K → Bool) {v : Fin K → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ j, |v j| ≤ B) : |orApprox S v| ≤ 1 + (1 + K * B) ^ Fintype.card κ := by
  rw [orApprox]
  refine (abs_sub _ _).trans ?_
  rw [abs_one]
  exact add_le_add_right (abs_prod_le hB hv) 1

end Approximators

section Gates

variable {κ : Type*} [Fintype κ]

/-- The approximator of a gate of the unbounded fan-in basis for a family `S` of sets of its
arguments: `1 - v` for negation, `andApprox` and `orApprox` for conjunction and disjunction. -/
@[expose] noncomputable def gateApprox :
    (op : Unbounded.Op) → (κ → Fin op.arity → Bool) → (Fin op.arity → ℝ) → ℝ
  | .not, _, v => 1 - v 0
  | .and _, S, v => andApprox S v
  | .or _, S, v => orApprox S v

/-- The bits at which the approximator of a gate may err: never for negation, and `AndMiss` for
conjunction and, at the negated bits, for disjunction. -/
@[expose] def GateMiss :
    (op : Unbounded.Op) → (κ → Fin op.arity → Bool) → (Fin op.arity → Bool) → Prop
  | .not, _, _ => False
  | .and _, S, b => AndMiss S b
  | .or _, S, b => AndMiss S fun j => !b j

instance : ∀ (op : Unbounded.Op) (S : κ → Fin op.arity → Bool) (b : Fin op.arity → Bool),
    Decidable (GateMiss op S b)
  | .not, _, _ => instDecidableFalse
  | .and _, S, b => inferInstanceAs (Decidable (AndMiss S b))
  | .or _, S, b => inferInstanceAs (Decidable (AndMiss S fun j => !b j))

/-- **Exactness of the gate approximators** at bits where they do not miss. -/
theorem gateApprox_bitVal {op : Unbounded.Op} {S : κ → Fin op.arity → Bool}
    {b : Fin op.arity → Bool} (h : ¬GateMiss op S b) :
    gateApprox op S (fun j => bitVal ℝ (b j)) = bitVal ℝ (Unbounded.interpretation op b) := by
  match op, S, b, h with
  | .not, _, b, _ => exact (bitVal_not (b 0)).symm
  | .and _, _, _, h => exact andApprox_bitVal h
  | .or _, _, _, h => exact orApprox_bitVal h

/-- **Degrees of the gate approximators**: a gate with a nonempty family of sets multiplies
degrees by the number of sets. -/
theorem gateApprox_mem_lowDegree {ι : Type*} {D : ℕ} (hκ : 1 ≤ Fintype.card κ)
    (op : Unbounded.Op) (S : κ → Fin op.arity → Bool) {v : Fin op.arity → (ι → Bool) → ℝ}
    (hv : ∀ j, v j ∈ lowDegree ℝ ι D) :
    (fun x => gateApprox op S fun j => v j x) ∈ lowDegree ℝ ι (Fintype.card κ * D) :=
  match op, S, v, hv with
  | .not, _, _, hv => lowDegree_mono (Nat.le_mul_of_pos_left D hκ) (one_sub_mem_lowDegree (hv 0))
  | .and _, S, _, hv => andApprox_mem_lowDegree S hv
  | .or _, S, _, hv => orApprox_mem_lowDegree S hv

/-- **Sup-norm bound for the gate approximators** (our bound, replacing
[Braverman, Proposition 9][Braverman2010]): with a nonempty family of `t` sets, a gate of fan-in
less than `2 ^ ℓ` on arguments of absolute value at most `2 ^ E` has absolute value at most
`2 ^ (t (E + ℓ + 1))`. -/
theorem abs_gateApprox_le {ℓ E : ℕ} (hκ : 1 ≤ Fintype.card κ) (op : Unbounded.Op)
    (hop : op.arity < 2 ^ ℓ) (S : κ → Fin op.arity → Bool) {v : Fin op.arity → ℝ}
    (hv : ∀ j, |v j| ≤ 2 ^ E) :
    |gateApprox op S v| ≤ 2 ^ (Fintype.card κ * (E + ℓ + 1)) := by
  set t := Fintype.card κ
  have hE : (1 : ℝ) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hK : ((op.arity : ℕ) : ℝ) + 1 ≤ 2 ^ ℓ := by exact_mod_cast hop
  have h2ℓ : (0 : ℝ) ≤ 2 ^ ℓ := by positivity
  have hK0 : (0 : ℝ) ≤ op.arity := Nat.cast_nonneg _
  match op, S, v, hv, hop, hK, hK0 with
  | .not, _, v, hv, _, _, _ =>
    calc |gateApprox .not _ v| = |1 - v 0| := rfl
      _ ≤ 1 + 2 ^ E := (abs_sub _ _).trans (by rw [abs_one]; exact add_le_add_right (hv 0) 1)
      _ ≤ 2 ^ (E + 1) := by rw [pow_succ]; linarith
      _ ≤ 2 ^ (t * (E + ℓ + 1)) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  | .and K, S, v, hv, _, hK, hK0 =>
    calc |gateApprox (.and K) S v| = |andApprox S v| := rfl
      _ ≤ (1 + K * (1 + 2 ^ E)) ^ t := abs_andApprox_le S (by positivity) hv
      _ ≤ (2 ^ (E + ℓ + 1)) ^ t := by
          refine pow_le_pow_left₀ (by positivity) ?_ t
          rw [pow_succ, pow_add]
          nlinarith
      _ = 2 ^ (t * (E + ℓ + 1)) := by rw [← pow_mul, mul_comm]
  | .or K, S, v, hv, _, hK, hK0 =>
    calc |gateApprox (.or K) S v| = |orApprox S v| := rfl
      _ ≤ 1 + (1 + K * 2 ^ E) ^ t := abs_orApprox_le S (by positivity) hv
      _ ≤ 1 + (2 ^ (E + ℓ)) ^ t := by
          refine add_le_add_right (pow_le_pow_left₀ (by positivity) ?_ t) 1
          rw [pow_add]
          nlinarith
      _ ≤ 2 ^ ((E + ℓ) * t + 1) := by
          rw [← pow_mul, pow_succ]
          linarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := (E + ℓ) * t) (by norm_num)]
      _ ≤ 2 ^ (t * (E + ℓ + 1)) := pow_le_pow_right₀ (by norm_num) (by nlinarith)

end Gates

/-! ### Choosing the sets -/

section Choice

variable {K : ℕ}

/-- Some mask does no worse than the average. -/
private theorem exists_le_bernoulliAverage {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : (Fin K → Bool) → ℝ) : ∃ S, F S ≤ bernoulliAverage p F := by
  obtain ⟨S, -, hS⟩ := exists_min_image univ F univ_nonempty
  refine ⟨S, ?_⟩
  calc F S = bernoulliAverage p fun _ => F S := (bernoulliAverage_const p _).symm
    _ ≤ bernoulliAverage p F := bernoulliAverage_mono hp0 hp1 fun S' => hS S' (mem_univ _)

/-- **Greedy choice of `s` sets.** If, at every point of positive weight, a random mask of rate
`p` gives the nonnegative failure `f x` an average at most `q`, then `s` masks can be chosen so that
the weighted product of their failures is at most `q ^ s` times the total weight. -/
private theorem exists_sum_mul_prod_le {X : Type*} [Fintype X] {p q : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hq : 0 ≤ q) (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (f : X → (Fin K → Bool) → ℝ)
    (hf : ∀ x S, 0 ≤ f x S) (hfq : ∀ x, 0 < μ x → bernoulliAverage p (f x) ≤ q) (s : ℕ) :
    ∃ T : Fin s → Fin K → Bool, ∑ x, μ x * ∏ i, f x (T i) ≤ q ^ s * ∑ x, μ x := by
  induction s with
  | zero => exact ⟨Fin.elim0, by simp⟩
  | succ s ih =>
    obtain ⟨T, hT⟩ := ih
    have hw (x : X) : 0 ≤ μ x * ∏ i, f x (T i) :=
      mul_nonneg (hμ x) (prod_nonneg fun i _ => hf x (T i))
    obtain ⟨S, hS⟩ := exists_le_bernoulliAverage hp0 hp1
      fun S => ∑ x, (μ x * ∏ i, f x (T i)) * f x S
    refine ⟨Fin.cons (α := fun _ => Fin K → Bool) S T, ?_⟩
    have hcons (x : X) : ∏ i, f x (Fin.cons (α := fun _ => Fin K → Bool) S T i) =
        f x S * ∏ i, f x (T i) := by
      rw [Fin.prod_univ_succ]
      rfl
    have hterm (x : X) : (μ x * ∏ i, f x (T i)) * bernoulliAverage p (f x) ≤
        q * (μ x * ∏ i, f x (T i)) := by
      rcases (hμ x).lt_or_eq with hx | hx
      · rw [mul_comm q]
        exact mul_le_mul_of_nonneg_left (hfq x hx) (hw x)
      · rw [← hx]
        simp only [zero_mul, mul_zero, le_refl]
    calc ∑ x, μ x * ∏ i, f x (Fin.cons (α := fun _ => Fin K → Bool) S T i)
        = ∑ x, (μ x * ∏ i, f x (T i)) * f x S := by
          refine sum_congr rfl fun x _ => ?_
          rw [hcons]
          ring
      _ ≤ bernoulliAverage p fun S => ∑ x, (μ x * ∏ i, f x (T i)) * f x S := hS
      _ = ∑ x, (μ x * ∏ i, f x (T i)) * bernoulliAverage p (f x) := by
          rw [bernoulliAverage_sum]
          exact sum_congr rfl fun x _ => bernoulliAverage_const_mul p _ (f x)
      _ ≤ ∑ x, q * (μ x * ∏ i, f x (T i)) := sum_le_sum fun x _ => hterm x
      _ ≤ q ^ (s + 1) * ∑ x, μ x := by
          rw [← mul_sum, pow_succ, mul_comm (q ^ s) q, mul_assoc]
          exact mul_le_mul_of_nonneg_left hT hq

/-- A random set of rate `p` contains exactly one zero of `b` with probability at least
`z p (1 - p) ^ (z - 1)`, where `z` is the number of zeros. -/
private theorem le_bernoulliAverage_exactlyOne {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (b : Fin K → Bool) :
    #{j | b j = false} * (p * (1 - p) ^ (#{j | b j = false} - 1)) ≤
      bernoulliAverage p fun S =>
        if #{j | S j = true ∧ b j = false} = 1 then (1 : ℝ) else 0 := by
  -- the event that `S` meets the zeros exactly in `i`, as a product over the coordinates
  let g (i j : Fin K) (t : Bool) : ℝ :=
    if (j = i → t = true) ∧ (j ≠ i → b j = false → t = false) then 1 else 0
  have hfactor (i j : Fin K) : (1 - p) * g i j false + p * g i j true =
      if j = i then p else if b j = false then 1 - p else 1 := by
    by_cases hj : j = i <;> by_cases hb : b j = false <;> simp [g, hj, hb]
  have hprod (i : Fin K) (hi : b i = false) :
      bernoulliAverage p (fun S => ∏ j, g i j (S j)) =
        p * (1 - p) ^ (#{j | b j = false} - 1) := by
    rw [bernoulliAverage_prod]
    simp only [hfactor]
    rw [← mul_prod_erase univ _ (mem_univ i), ite_eq_left rfl]
    congr 1
    rw [prod_congr rfl fun j hj => ite_eq_right (ne_of_mem_erase hj), prod_ite, prod_const_one,
      mul_one, prod_const, filter_erase, card_erase_of_mem (by simpa using hi)]
  have hg (i : Fin K) (S : Fin K → Bool) : ∏ j, g i j (S j) =
      if S i = true ∧ ∀ j, j ≠ i → b j = false → S j = false then 1 else 0 := by
    rw [prod_boole]
    by_cases hq : S i = true ∧ ∀ j, j ≠ i → b j = false → S j = false
    · rw [ite_eq_left hq, ite_eq_left fun j _ => ⟨fun hji => hji ▸ hq.1, hq.2 j⟩]
    · rw [ite_eq_right hq, ite_eq_right fun h =>
        hq ⟨(h i (mem_univ _)).1 rfl, fun j hj => (h j (mem_univ _)).2 hj⟩]
  have hpoint (S : Fin K → Bool) : ∑ i with b i = false, ∏ j, g i j (S j) ≤
      if #{j | S j = true ∧ b j = false} = 1 then (1 : ℝ) else 0 := by
    simp only [hg]
    rw [sum_boole]
    split_ifs with h
    · exact_mod_cast card_le_one.2 fun a ha c hc => by
        simp only [mem_filter, mem_univ, true_and] at ha hc
        by_contra hac
        have := hc.2.2 a hac ha.1
        rw [ha.2.1] at this
        exact Bool.true_eq_false_eq_False this
    · have h0 : #{i ∈ ({i | b i = false} : Finset (Fin K)) |
          S i = true ∧ ∀ j, j ≠ i → b j = false → S j = false} = 0 := by
        refine card_eq_zero.2 (filter_eq_empty_iff.2 fun i hi hQ => h ?_)
        simp only [mem_filter, mem_univ, true_and] at hi
        refine card_eq_one.2 ⟨i, ext fun j => ?_⟩
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · rintro ⟨hS, hb⟩
          by_contra hji
          rw [hQ.2 j hji hb] at hS
          exact Bool.false_ne_true hS
        · rintro rfl
          exact ⟨hQ.1, hi⟩
      rw [h0, Nat.cast_zero]
  calc _ = ∑ i with b i = false, bernoulliAverage p (fun S => ∏ j, g i j (S j)) := by
        rw [sum_congr rfl fun i hi => hprod i (by simpa using hi), sum_const, nsmul_eq_mul]
    _ = bernoulliAverage p fun S => ∑ i with b i = false, ∏ j, g i j (S j) :=
        (bernoulliAverage_sum _ p _).symm
    _ ≤ _ := bernoulliAverage_mono hp0 hp1 hpoint

/-- The numerical heart of Braverman's bound: when `2 ^ r ≤ z < 2 ^ (r + 1)` and
`p = 2 ^ -(r + 1)`, `z p (1 - p) ^ (z - 1) ≥ 1 / (2e) > 9 / 50`. -/
private theorem nine_div_fifty_le {r z : ℕ} (h₁ : 2 ^ r ≤ z) (h₂ : z < 2 ^ (r + 1)) :
    (9 / 50 : ℝ) ≤ z * (1 / 2 ^ (r + 1) * (1 - 1 / 2 ^ (r + 1)) ^ (z - 1)) := by
  set N : ℝ := 2 ^ (r + 1) with hN
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_two_pow) h₁
  have hN2 : (2 : ℝ) ≤ N := by
    rw [hN, pow_succ]
    nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := r) (by norm_num)]
  have hzN : (z : ℝ) * 2 ≥ N := by
    rw [hN, pow_succ]
    exact_mod_cast Nat.mul_le_mul_right 2 h₁
  have hzN' : (z : ℝ) + 1 ≤ N := by
    rw [hN]
    exact_mod_cast Nat.succ_le_of_lt h₂
  set p : ℝ := 1 / N with hp
  set q : ℝ := 1 - p with hq
  have hpq : p + q = 1 := by ring
  have hp0 : 0 < p := by positivity
  have hq0 : 0 < q := by
    rw [hq, hp, sub_pos, div_lt_one (by linarith)]
    linarith
  -- `q ≥ exp (-(p / q))`, from `1 + p / q ≤ exp (p / q)`
  have hexp : Real.exp (-(p / q)) ≤ q := by
    have h := Real.add_one_le_exp (p / q)
    have h1 : p / q + 1 = 1 / q := by field_simp; linarith
    rw [h1] at h
    rw [Real.exp_neg]
    calc (Real.exp (p / q))⁻¹ ≤ (1 / q)⁻¹ := inv_anti₀ (by positivity) h
      _ = q := by simp
  have hpow : Real.exp (-1) ≤ q ^ (z - 1) := by
    calc Real.exp (-1) ≤ Real.exp (-(p / q)) ^ (z - 1) := by
          rw [← Real.exp_nat_mul]
          refine Real.exp_le_exp.2 ?_
          have hk : ((z - 1 : ℕ) : ℝ) = z - 1 := by rw [Nat.cast_sub hz1, Nat.cast_one]
          rw [hk]
          have hpq' : p / q = 1 / (N - 1) := by
            rw [hp, hq, hp]
            field_simp
          rw [hpq', mul_neg, mul_one_div, neg_le_neg_iff, div_le_one (by linarith)]
          linarith
      _ ≤ q ^ (z - 1) := pow_le_pow_left₀ (Real.exp_pos _).le hexp _
  have he : Real.exp 1 < 25 / 9 := Real.exp_one_lt_d9.trans (by norm_num)
  have he' : 9 / 25 < Real.exp (-1) := by
    rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    linarith
  have hzp : (1 : ℝ) / 2 ≤ z * p := by
    rw [hp, mul_one_div, le_div_iff₀ (by linarith)]
    linarith
  calc (9 / 50 : ℝ) ≤ 1 / 2 * Real.exp (-1) := by linarith
    _ ≤ z * p * q ^ (z - 1) :=
        mul_le_mul hzp hpow (Real.exp_pos _).le (by positivity)
    _ = z * (p * q ^ (z - 1)) := by ring

/-- One random set of rate `2 ^ -(r + 1)` fails to contain exactly one zero of `b` with
probability at most `41 / 50` when `b` has between `2 ^ r` and `2 ^ (r + 1)` zeros. -/
private theorem bernoulliAverage_fail_le {r : ℕ} {b : Fin K → Bool}
    (h₁ : 2 ^ r ≤ #{j | b j = false}) (h₂ : #{j | b j = false} < 2 ^ (r + 1)) :
    bernoulliAverage (1 / 2 ^ (r + 1)) (fun S =>
      if #{j | S j = true ∧ b j = false} = 1 then (0 : ℝ) else 1) ≤ 41 / 50 := by
  have h : (fun S : Fin K → Bool =>
      if #{j | S j = true ∧ b j = false} = 1 then (0 : ℝ) else 1) =
      fun S => 1 - if #{j | S j = true ∧ b j = false} = 1 then (1 : ℝ) else 0 := by
    funext S
    split_ifs <;> norm_num
  rw [h, bernoulliAverage_sub, bernoulliAverage_const]
  have hp1 : (1 : ℝ) / 2 ^ (r + 1) ≤ 1 :=
    div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
  linarith [le_bernoulliAverage_exactlyOne (by positivity) hp1 b, nine_div_fifty_le h₁ h₂]

variable {ℓ s : ℕ}

/-- **Braverman's choice of sets for an AND gate** [Braverman, Lemma 8][Braverman2010]: for every
nonnegative weights `ν` on a finite set of points, at which the `K < 2 ^ ℓ` arguments of the gate
take the values `u x`, there are `s` sets at each of the rates `2⁻¹, …, 2⁻ℓ` whose misses have
weight at most `(41 / 50) ^ s` times the total. -/
theorem exists_sum_andMiss_le {X : Type*} [Fintype X] (hK : K < 2 ^ ℓ) (ν : X → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (u : X → Fin K → Bool) :
    ∃ S : Fin (ℓ * s) → Fin K → Bool,
      ∑ x with AndMiss S (u x), ν x ≤ (41 / 50) ^ s * ∑ x, ν x := by
  -- the number of zeros, and the weights of the points whose zeros are at scale `r`
  let z (x : X) : ℕ := #{j | u x j = false}
  let μ (r : Fin ℓ) (x : X) : ℝ := if 0 < z x ∧ Nat.log 2 (z x) = r then ν x else 0
  let f (x : X) (S : Fin K → Bool) : ℝ :=
    if #{j | S j = true ∧ u x j = false} = 1 then 0 else 1
  have hμ (r : Fin ℓ) (x : X) : 0 ≤ μ r x := by
    simp only [μ]
    split_ifs
    exacts [hν x, le_rfl]
  have hf (x : X) (S : Fin K → Bool) : 0 ≤ f x S := by
    simp only [f]
    split_ifs <;> norm_num
  have hfq (r : Fin ℓ) (x : X) (hx : 0 < μ r x) :
      bernoulliAverage (1 / 2 ^ ((r : ℕ) + 1)) (f x) ≤ 41 / 50 := by
    have hc : 0 < z x ∧ Nat.log 2 (z x) = r := by
      by_contra hc
      simp [μ, hc] at hx
    refine bernoulliAverage_fail_le (r := r) ?_ ?_
    · rw [← hc.2]
      exact Nat.pow_log_le_self 2 hc.1.ne'
    · rw [← hc.2]
      exact Nat.lt_pow_succ_log_self (by norm_num) _
  choose T hT using fun r : Fin ℓ => exists_sum_mul_prod_le (K := K) (by positivity)
    (div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)) (by norm_num) (μ r) (hμ r) f
    hf (hfq r) s
  -- the sets, indexed by the pairs of a scale and one of its `s` sets
  let S (c : Fin (ℓ * s)) : Fin K → Bool := T (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2
  refine ⟨S, ?_⟩
  -- a missed point is counted, with its full weight, at the scale of its number of zeros
  have hpoint (x : X) : (if AndMiss S (u x) then ν x else 0) ≤
      ∑ r, μ r x * ∏ i, f x (T r i) := by
    split_ifs with hx
    · obtain ⟨⟨j, hj⟩, hall⟩ := hx
      have hz : 0 < z x := card_pos.2 ⟨j, by simpa using hj⟩
      have hzK : z x < 2 ^ ℓ :=
        ((card_filter_le _ _).trans (card_univ.trans (Fintype.card_fin K)).le).trans_lt hK
      let r₀ : Fin ℓ := ⟨Nat.log 2 (z x), Nat.log_lt_of_lt_pow hz.ne' hzK⟩
      refine le_trans (le_of_eq ?_) (single_le_sum (fun r _ => mul_nonneg (hμ r x)
        (prod_nonneg fun i _ => hf x (T r i))) (mem_univ r₀))
      rw [show μ r₀ x = ν x from ite_eq_left ⟨hz, rfl⟩,
        prod_eq_one fun i _ => ite_eq_right
          (by simpa only [S, Equiv.symm_apply_apply] using hall (finProdFinEquiv (r₀, i))),
        mul_one]
    · exact sum_nonneg fun r _ => mul_nonneg (hμ r x) (prod_nonneg fun i _ => hf x (T r i))
  -- the scales of a point are unique, so its weights over the scales sum to at most `ν x`
  have hsum (x : X) : ∑ r, μ r x ≤ ν x := by
    simp only [μ]
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    have hcard : #{r : Fin ℓ | 0 < z x ∧ Nat.log 2 (z x) = r} ≤ 1 :=
      card_le_one.2 fun a ha c hc => by
        simp only [mem_filter, mem_univ, true_and] at ha hc
        exact Fin.ext (ha.2.symm.trans hc.2)
    have : ((#{r : Fin ℓ | 0 < z x ∧ Nat.log 2 (z x) = r} : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    nlinarith [hν x]
  calc ∑ x with AndMiss S (u x), ν x
      = ∑ x, if AndMiss S (u x) then ν x else 0 := sum_filter _ _
    _ ≤ ∑ x, ∑ r, μ r x * ∏ i, f x (T r i) := sum_le_sum fun x _ => hpoint x
    _ = ∑ r, ∑ x, μ r x * ∏ i, f x (T r i) := sum_comm
    _ ≤ ∑ r, (41 / 50 : ℝ) ^ s * ∑ x, μ r x := sum_le_sum fun r _ => hT r
    _ = (41 / 50) ^ s * ∑ x, ∑ r, μ r x := by rw [← mul_sum, sum_comm]
    _ ≤ (41 / 50) ^ s * ∑ x, ν x :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => hsum x) (by positivity)

/-- **Braverman's choice of sets for a gate** [Braverman, Lemma 8][Braverman2010]: for every
nonnegative weights `ν` on a finite set of points, at which the arguments of a gate of fan-in less
than `2 ^ ℓ` take the values `u x`, there are `s` sets at each of the rates `2⁻¹, …, 2⁻ℓ` whose
misses have weight at most `(41 / 50) ^ s` times the total. -/
theorem exists_sum_gateMiss_le {X : Type*} [Fintype X] (ν : X → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (op : Unbounded.Op) (hop : op.arity < 2 ^ ℓ) (u : X → Fin op.arity → Bool) :
    ∃ S : Fin (ℓ * s) → Fin op.arity → Bool,
      ∑ x with GateMiss op S (u x), ν x ≤ (41 / 50) ^ s * ∑ x, ν x :=
  match op, hop, u with
  | .not, _, _ => ⟨fun _ _ => false,
      (sum_eq_zero fun _ hx => False.elim (mem_filter.1 hx).2).trans_le
        (mul_nonneg (by positivity) (sum_nonneg fun x _ => hν x))⟩
  | .and _, hop, u => exists_sum_andMiss_le hop ν hν u
  | .or _, hop, u => exists_sum_andMiss_le hop ν hν fun x j => !u x j

end Choice

end Cslib.Circuits.Boolean.Braverman
