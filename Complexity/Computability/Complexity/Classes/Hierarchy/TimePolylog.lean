/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Hierarchy.Time
import Complexity.Computability.Complexity.Classes.Hierarchy.LogClock
import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedComplexity
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# The time hierarchy with a polylogarithmic gap

With the universal machine running a fixed machine for `t` steps within time `O(t log t)`
(`Turing.MultiTapeTM.Universal.computableInO_universal_nlogn`), the clocked diagonal on short
descriptions `Cslib.Complexity.timeDiagonal J` of `Hierarchy.Time` is computable within time and
space `O(n + (log (n + 1) + 1) ^ k * (J n + 1) * (log (J n + 1) + 1))` on inputs of length `n`,
for a time-constructible clock `J` and an absolute constant `k`
(`Cslib.Complexity.exists_computableInO_timeDiagonal_polylog`). On a short description, of
`L ≤ log n` bits, the decoded description has encoded length polynomial in `L`, so the overhead of
the universal machine, polynomial in that length, is polylogarithmic in `n`; the symbols are bits.
Shortness and the final test are decided in linear time.

The diagonal argument of `Hierarchy.Time` then gives `DTIME f ⊂ DTIME g`
[Arora and Barak, Theorem 3.1][AroraBarak09], [Sipser, Theorem 9.10][Sipser2013]:

* when a time-constructible clock `J` eventually exceeds every `c * f n + c` and
  `n + (log (n + 1) + 1) ^ k * (J n + 1) * (log (J n + 1) + 1) ≤ g n` eventually
  (`Cslib.Complexity.exists_DTIME_ssubset_DTIME_of_clock_polylog`), or when the clock beats each
  `c * f n + c` only at arbitrarily large lengths and `f ≤ g` eventually
  (`Cslib.Complexity.exists_DTIME_ssubset_DTIME_of_frequently_clock_polylog`);
* when `f` is time-constructible, `n ≤ f n` and `(f n + 1) * (log (f n + 1) + 1) ^ k ≤ g n`
  eventually (`Cslib.Complexity.exists_DTIME_ssubset_DTIME_polylog`), with the clock
  `f n * (Nat.size (f n) + 1)` of `Hierarchy.LogClock`.

Each statement asserts an absolute exponent `k`, chosen before the bounds. The bounds are monotone
in `k`, so one exponent serves any finitely many of them. The gap is a polylogarithmic factor,
weaker than the textbook `f n * log (f n) = o(g n)`, which needs the diagonal to count the steps of
the universal machine itself rather than those of the simulated machine. Here the exponent `k`
comes from the polynomial overhead of the universal machine in the description and from the
degree of the description decoder; for time-constructible `f` it also absorbs the logarithmic
inflation of the clock `f n * (Nat.size (f n) + 1)` and the `J log J` term.

## Main results

* `Cslib.Complexity.exists_computableInO_timeDiagonal_polylog`: the clocked diagonal within time
  `O(n + polylog(n) * J log J)`.
* `Cslib.Complexity.exists_setOf_timeDiagonal_mem_DTIME_polylog`: its problem is in the
  corresponding class.
* `Cslib.Complexity.exists_DTIME_not_subset_DTIME_of_clock_polylog`,
  `Cslib.Complexity.exists_DTIME_ssubset_DTIME_of_frequently_clock_polylog`,
  `Cslib.Complexity.exists_DTIME_ssubset_DTIME_of_clock_polylog`: the time hierarchy for a clock.
* `Cslib.Complexity.exists_DTIME_ssubset_DTIME_polylog`: the time hierarchy for a
  time-constructible bound, with gap `f * polylog f`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

namespace Diagonal

/-- The test of the diagonal is within linear time and space. The comparison costs the length of
its first argument times the total length, so the constant `[eBit true]` is put first. (The
quadratic `Cslib.Complexity.Diagonal.computableInO_verdict` puts the result first.) -/
private theorem computableInO_verdict_linear :
    ComputableInO verdict eOut encBool (fun r => (eOut r).length) fun r => (eOut r).length := by
  have heq := (ComputableInO.eq (encList encUnary)).tidy.comp
    ((ComputableTidilyInO.const (encMid := encList encUnary) [eBit true]).prod
      (ComputableTidilyInO.fst (encList encUnary) encBool))
  have hfin := (ComputableTidilyInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun q : Bool × Bool => !(q.1 && q.2)).inO_one
  refine (((hfin.comp ((ComputableTidilyInO.snd (encList encUnary) encBool).prod heq)).mono 64
    (fun r => ?_) fun r => ?_).of_enc_eq fun r => ?_).computableInO
  rotate_left 2
  · simp only [verdict, Function.comp_apply, encBool_apply, List.cons.injEq, and_true]
    rw [decide_eq_decide.mpr eq_comm]
  all_goals
    have h₁ := length_le_encPair_left (encList encUnary) encBool r
    have h₂ : (encList encUnary [eBit true]).length = 3 := rfl
    simp only [Function.comp_apply, length_encPair, encBool_apply, List.length_singleton,
      h₂] at h₁ ⊢
    omega

/-- The numeric core of the resources of the clocked diagonal with the `O(t log t)` universal
machine, for the exponent `E` of its overhead: for an input of length `n` with a short framed
description of `L` bits, a decoding time `A` linear in `n`, a decoded description of encoded length
`D` polynomial in `L`, symbols of size `M ≤ 1` and an encoded universal input of length `I`,
everything is within `K * (n + (log (n + 1) + 1) ^ (e * E) * Y + 1)` for the clock term
`Y = (J + 1) * (log (J + 1) + 1)`. -/
private theorem polylogBounds_aux (E e ce cA : ℕ) (hE : 1 ≤ E) : ∃ K, ∀ {n L A D M J I : ℕ},
    2 ^ L ≤ n → A ≤ cA * (n + 1) → D ≤ ce * (L + 1) ^ e → M ≤ 1 →
    I ≤ 2 * D + 1 + (2 * (3 * n) + 1 + J) →
    n + A + (n + J) + (I + (D + M + 2) ^ E * ((J + 1) * (Nat.log 2 (J + 1) + 1))) ≤
      K * (n + (Nat.log 2 (n + 1) + 1) ^ (e * E) * ((J + 1) * (Nat.log 2 (J + 1) + 1)) + 1) := by
  refine ⟨cA + 2 * ce + (ce + 3) ^ E + 12, fun {n L A D M J I} hL hA hD hM hI => ?_⟩
  set ℓ := Nat.log 2 (n + 1) + 1 with hℓ
  set Y := (J + 1) * (Nat.log 2 (J + 1) + 1) with hY
  set V := ℓ ^ (e * E) * Y with hV
  have hℓ1 : 1 ≤ ℓ := Nat.le_add_left _ _
  have hLℓ : L + 1 ≤ ℓ := Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num)
    (hL.trans (Nat.le_succ n)))
  have hJY : J + 1 ≤ Y := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hYV : Y ≤ V := Nat.le_mul_of_pos_left _ (Nat.pow_pos hℓ1)
  have hpow : (L + 1) ^ e ≤ ℓ ^ e := Nat.pow_le_pow_left hLℓ e
  have hΛ : ℓ ^ e ≤ ℓ ^ (e * E) := Nat.pow_le_pow_right hℓ1 (Nat.le_mul_of_pos_right _ hE)
  have hΛV : ℓ ^ (e * E) ≤ V := Nat.le_mul_of_pos_right _ (by omega)
  have hDV : D ≤ ce * V := hD.trans (Nat.mul_le_mul_left _ ((hpow.trans hΛ).trans hΛV))
  have hB : (D + M + 2) ^ E * Y ≤ (ce + 3) ^ E * V := by
    have h₁ : D + M + 2 ≤ (ce + 3) * ℓ ^ e := by
      have := Nat.mul_le_mul_left ce hpow
      have : 1 ≤ ℓ ^ e := Nat.one_le_pow _ _ hℓ1
      have e₁ : (ce + 3) * ℓ ^ e = ce * ℓ ^ e + 3 * ℓ ^ e := by ring
      omega
    calc (D + M + 2) ^ E * Y ≤ ((ce + 3) * ℓ ^ e) ^ E * Y :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h₁ E)
      _ = (ce + 3) ^ E * V := by rw [hV, mul_pow, ← pow_mul]; ring
  have hcA : cA * (n + 1) ≤ cA * (n + V + 1) := Nat.mul_le_mul_left _ (by omega)
  have hce : ce * V ≤ ce * (n + V + 1) := Nat.mul_le_mul_left _ (by omega)
  have hC : (ce + 3) ^ E * V ≤ (ce + 3) ^ E * (n + V + 1) := Nat.mul_le_mul_left _ (by omega)
  have e₁ : (cA + 2 * ce + (ce + 3) ^ E + 12) * (n + V + 1) = cA * (n + V + 1) +
      2 * (ce * (n + V + 1)) + (ce + 3) ^ E * (n + V + 1) + 12 * (n + V + 1) := by ring
  rw [e₁]
  omega

end Diagonal

open Diagonal in
/-- **The clocked diagonal in time `O(n + polylog(n) · J log J)`.** There is an absolute constant
`k` such that, for every time-constructible clock `J`, the clocked diagonal on short descriptions
is computable within time and space `O(n + (log (n + 1) + 1) ^ k * (J n + 1) * (log (J n + 1) + 1))`
on inputs of length `n`. It charges the shortness test, decoding, the symbols, the clock, the
`O(t log t)` universal run and the test. -/
theorem exists_computableInO_timeDiagonal_polylog : ∃ k, ∀ {J : ℕ → ℕ}, TimeConstructible J →
    ComputableInO (timeDiagonal J) encBits encBool
      (fun x => x.length + (Nat.log 2 (x.length + 1) + 1) ^ k *
        ((J x.length + 1) * (Nat.log 2 (J x.length + 1) + 1)))
      fun x => x.length + (Nat.log 2 (x.length + 1) + 1) ^ k *
        ((J x.length + 1) * (Nat.log 2 (J x.length + 1) + 1)) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  obtain ⟨ce, hce⟩ := hdec.2
  obtain ⟨cA, hcA⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun u => (u + 1) ^ dd)
    (by fun_prop)
  obtain ⟨K, hK⟩ := polylogBounds_aux 6 ed ce cA (by norm_num)
  refine ⟨ed * 6, fun {J} hJ => ?_⟩
  have hu : ComputableTidilyInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
    ComputableTidilyInO.of_linear (.of_unframe fun _ => rfl)
  have hdesc := hdec.inO.tidy.comp hu
  have hsym := Universal.computableTidilyInDegree_map_eBit.inO_one
  have hclock := hJ.computableInO.tidy
  have hU := computableInO_universal_nlogn.tidy.comp (hdesc.prod (hsym.prod hclock))
  have h := computableInO_shortDesc.tidy.ite (computableInO_verdict_linear.tidy.comp hU)
    (ComputableTidilyInO.const (encMid := encBool) false)
  obtain ⟨cO, hcO⟩ := hU.length_le
  have hbound (x : List Bool) (hs : shortDesc x = true) :
      x.length + ((unframe x).length + 1) ^ dd + (x.length + J x.length) +
          ((eIn (decodeDesc (unframe x), x.map eBit, J x.length)).length +
            (descLen (decodeDesc (unframe x)) + listMax id (x.map eBit) + 2) ^ 6 *
              ((J x.length + 1) * (Nat.log 2 (J x.length + 1) + 1))) ≤
        K * (x.length + (Nat.log 2 (x.length + 1) + 1) ^ (ed * 6) *
          ((J x.length + 1) * (Nat.log 2 (J x.length + 1) + 1)) + 1) := by
    have hL : 2 ^ (unframe x).length ≤ x.length := of_decide_eq_true hs
    have hN : (encList encUnary (x.map eBit)).length ≤ 3 * x.length :=
      (length_encList_le encUnary _ (b := 1) fun s hs => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
        cases b
        · exact Nat.zero_le _
        · exact le_rfl).trans (by rw [List.length_map]; omega)
    have hJ := Universal.length_encNat_le (J x.length)
    refine hK hL ((hcA _).trans (Nat.mul_le_mul_left _ (hL.trans (Nat.le_succ _)))) (hce _)
      (listMax_le fun a ha => ?_) ?_
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
      cases b <;> decide
    · simp only [length_encPair, descLen]
      omega
  refine (h.mono ((K + 1) * (cO + 1) + 2) (fun x => ?_) fun x => ?_).computableInO
  all_goals
    have hO := hcO x
    dsimp only [Function.comp_apply, encBits_apply] at hO ⊢
    have hW : x.length ≤ x.length + (Nat.log 2 (x.length + 1) + 1) ^ (ed * 6) *
        ((J x.length + 1) * (Nat.log 2 (J x.length + 1) + 1)) := Nat.le_add_right _ _
    split_ifs with hs
    · have hT := hbound x hs
      set W := x.length + (Nat.log 2 (x.length + 1) + 1) ^ (ed * 6) *
        ((J x.length + 1) * (Nat.log 2 (J x.length + 1) + 1))
      have h₁ := Nat.mul_le_mul_left cO (Nat.add_le_add_right hT 1)
      have h₂ : cO ≤ cO * (W + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      have e₁ : ((K + 1) * (cO + 1) + 2) * (W + 1) =
          cO * (K * (W + 1)) + K * (W + 1) + cO * (W + 1) + 3 * (W + 1) := by ring
      have e₂ : cO * (K * (W + 1) + 1) = cO * (K * (W + 1)) + cO := by ring
      omega
    · set W := x.length + (Nat.log 2 (x.length + 1) + 1) ^ (ed * 6) *
        ((J x.length + 1) * (Nat.log 2 (J x.length + 1) + 1))
      have e₁ : ((K + 1) * (cO + 1) + 2) * (W + 1) =
          (K + 1) * (cO + 1) * (W + 1) + 2 * (W + 1) := by ring
      omega

/-- The problem of the clocked diagonal is decidable within time
`O(n + (log (n + 1) + 1) ^ k * (J n + 1) * (log (J n + 1) + 1))`, for an absolute constant `k`. -/
theorem exists_setOf_timeDiagonal_mem_DTIME_polylog : ∃ k, ∀ {J : ℕ → ℕ}, TimeConstructible J →
    {x | timeDiagonal J x = true} ∈ DTIME encBits fun n =>
      n + (Nat.log 2 (n + 1) + 1) ^ k * ((J n + 1) * (Nat.log 2 (J n + 1) + 1)) := by
  obtain ⟨k, hk⟩ := exists_computableInO_timeDiagonal_polylog
  exact ⟨k, fun hJ => setOf_mem_DTIME_of_computableInO (hk hJ) fun _ => le_rfl⟩

/-! ### The time hierarchy theorem -/

/-- **Time-class noninclusion from a clock, with a polylogarithmic gap.** Infinitely many favorable
lengths for each constant suffice to separate the upper class from `DTIME f`. -/
theorem exists_DTIME_not_subset_DTIME_of_clock_polylog : ∃ k, ∀ {f g J : ℕ → ℕ},
    TimeConstructible J → (∀ c, ∃ᶠ n in atTop, c * f n + c ≤ J n) →
    (∀ᶠ n in atTop,
      n + (Nat.log 2 (n + 1) + 1) ^ k * ((J n + 1) * (Nat.log 2 (J n + 1) + 1)) ≤ g n) →
    ¬DTIME encBits g ⊆ DTIME encBits f := by
  obtain ⟨k, hk⟩ := exists_setOf_timeDiagonal_mem_DTIME_polylog
  exact ⟨k, fun hJ hfJ hg h => setOf_timeDiagonal_notMem_DTIME_of_frequently_le hfJ
    (h (DTIME_mono_of_eventually_le hg (hk hJ)))⟩

/-- **A hierarchy for irregular bounds, with a polylogarithmic gap.** The clock must dominate the
lower bound only infinitely often for each constant; eventual `f ≤ g` supplies the inclusion. -/
theorem exists_DTIME_ssubset_DTIME_of_frequently_clock_polylog : ∃ k, ∀ {f g J : ℕ → ℕ},
    TimeConstructible J → (∀ c, ∃ᶠ n in atTop, c * f n + c ≤ J n) →
    (∀ᶠ n in atTop, f n ≤ g n) →
    (∀ᶠ n in atTop,
      n + (Nat.log 2 (n + 1) + 1) ^ k * ((J n + 1) * (Nat.log 2 (J n + 1) + 1)) ≤ g n) →
    DTIME encBits f ⊂ DTIME encBits g := by
  obtain ⟨k, hk⟩ := exists_DTIME_not_subset_DTIME_of_clock_polylog
  exact ⟨k, fun hJ hfJ hfg hg => ⟨DTIME_mono_of_eventually_le hfg, hk hJ hfJ hg⟩⟩

/-- **The time hierarchy theorem for a clock, with a polylogarithmic gap.** There is an absolute
constant `k` such that, if a time-constructible clock `J` eventually exceeds every `c * f n + c`,
then `DTIME f` is strictly contained in every `DTIME g` with
`n + (log (n + 1) + 1) ^ k * (J n + 1) * (log (J n + 1) + 1) ≤ g n` eventually
[Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem exists_DTIME_ssubset_DTIME_of_clock_polylog : ∃ k, ∀ {f g J : ℕ → ℕ},
    TimeConstructible J → (∀ c, ∀ᶠ n in atTop, c * f n + c ≤ J n) →
    (∀ᶠ n in atTop,
      n + (Nat.log 2 (n + 1) + 1) ^ k * ((J n + 1) * (Nat.log 2 (J n + 1) + 1)) ≤ g n) →
    DTIME encBits f ⊂ DTIME encBits g := by
  obtain ⟨k, hk⟩ := exists_DTIME_ssubset_DTIME_of_frequently_clock_polylog
  refine ⟨k, fun {f g J} hJ hfJ hg => hk hJ (fun c => (hfJ c).frequently) ?_ hg⟩
  filter_upwards [hfJ 1, hg] with n h₁ h₂
  have : J n + 1 ≤ (Nat.log 2 (n + 1) + 1) ^ k * ((J n + 1) * (Nat.log 2 (J n + 1) + 1)) :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _)))
  omega

/-- The bound of the clocked diagonal for the logarithmic clock `m * (Nat.size m + 1)` of an
at-least-linear `m = f n` is within `(m + 1) * (log (m + 1) + 1) ^ (k + 5)`. -/
private theorem logClockBound_le (k : ℕ) {n m : ℕ} (hnm : n ≤ m) (hm : 1 ≤ m) :
    n + (Nat.log 2 (n + 1) + 1) ^ k * ((m * (Nat.size m + 1) + 1) *
      (Nat.log 2 (m * (Nat.size m + 1) + 1) + 1)) ≤
      (m + 1) * (Nat.log 2 (m + 1) + 1) ^ (k + 5) := by
  set ℓ := Nat.log 2 (m + 1) + 1 with hℓ
  have hℓ2 : 2 ≤ ℓ := Nat.succ_le_succ (Nat.log_pos (by norm_num) (by omega))
  have hm2 : m + 1 < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by norm_num) _
  have hsize : Nat.size m ≤ ℓ := Nat.size_le.mpr (by omega)
  have hsm : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  have hJ₁ : m * (Nat.size m + 1) + 1 ≤ (m + 1) * (2 * ℓ) := by
    have := Nat.mul_le_mul_left m (Nat.add_le_add_right hsize 1)
    have e : (m + 1) * (2 * ℓ) = m * (ℓ + 1) + (m * (ℓ - 1) + 2 * ℓ) := by
      have : 2 * ℓ = (ℓ + 1) + (ℓ - 1) := by omega
      rw [this]
      ring
    omega
  have hJ₂ : m * (Nat.size m + 1) + 1 < 2 ^ (2 * ℓ) := by
    have h₁ : m * (Nat.size m + 1) + 1 ≤ (m + 1) * (m + 1) := by
      have := Nat.mul_le_mul_left m (Nat.add_le_add_right hsm 1)
      nlinarith
    have h₂ : (m + 1) * (m + 1) < 2 ^ ℓ * 2 ^ ℓ := Nat.mul_lt_mul'' hm2 hm2
    rw [two_mul, pow_add]
    omega
  have hlogJ : Nat.log 2 (m * (Nat.size m + 1) + 1) + 1 ≤ 2 * ℓ :=
    Nat.log_lt_of_lt_pow (by omega) hJ₂
  have hlogn : (Nat.log 2 (n + 1) + 1) ^ k ≤ ℓ ^ k :=
    Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.log_mono_right (by omega))) k
  have hP : m + 1 ≤ (m + 1) * ℓ ^ (k + 2) :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  have h8 : 8 * ((m + 1) * ℓ ^ (k + 2)) ≤ (m + 1) * ℓ ^ (k + 5) := by
    have : 2 ^ 3 ≤ ℓ ^ 3 := Nat.pow_le_pow_left hℓ2 3
    calc 8 * ((m + 1) * ℓ ^ (k + 2)) ≤ ℓ ^ 3 * ((m + 1) * ℓ ^ (k + 2)) :=
          Nat.mul_le_mul_right _ this
      _ = (m + 1) * ℓ ^ (k + 5) := by ring
  calc n + (Nat.log 2 (n + 1) + 1) ^ k * ((m * (Nat.size m + 1) + 1) *
        (Nat.log 2 (m * (Nat.size m + 1) + 1) + 1))
      ≤ m + ℓ ^ k * (((m + 1) * (2 * ℓ)) * (2 * ℓ)) :=
        Nat.add_le_add hnm (Nat.mul_le_mul hlogn (Nat.mul_le_mul hJ₁ hlogJ))
    _ = m + 4 * ((m + 1) * ℓ ^ (k + 2)) := by ring
    _ ≤ (m + 1) * ℓ ^ (k + 5) := by omega

/-- **The time hierarchy theorem, with a polylogarithmic gap.** There is an absolute constant `k`
such that, if `f` is time-constructible and `n ≤ f n`, then `DTIME f` is strictly contained in
every `DTIME g` with `(f n + 1) * (log (f n + 1) + 1) ^ k ≤ g n` eventually
[Arora and Barak, Theorem 3.1][AroraBarak09], [Sipser, Theorem 9.10][Sipser2013]. The gap is a
polylogarithmic factor, not the textbook `f n * log (f n) = o(g n)`. -/
theorem exists_DTIME_ssubset_DTIME_polylog : ∃ k, ∀ {f g : ℕ → ℕ}, TimeConstructible f →
    (∀ n, n ≤ f n) → (∀ᶠ n in atTop, (f n + 1) * (Nat.log 2 (f n + 1) + 1) ^ k ≤ g n) →
    DTIME encBits f ⊂ DTIME encBits g := by
  obtain ⟨k, hk⟩ := exists_DTIME_ssubset_DTIME_of_clock_polylog
  refine ⟨k + 5, fun {f g} hf hn hg =>
    hk hf.mul_size_succ (eventually_mul_add_le_mul_size_succ hn) ?_⟩
  filter_upwards [hg, eventually_ge_atTop 1] with n h h₁
  exact (logClockBound_le k (hn n) (h₁.trans (hn n))).trans h

end Cslib.Complexity
