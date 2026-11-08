/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Polarization.PolyTime
public import Complexity.Computability.Complexity.Problems.StatisticalDifference
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Polynomial-time polarization of Statistical Difference

The efficiency half of the Sahai–Vadhan Polarization Lemma [SahaiVadhan2003, §3]. Instances of
Statistical Difference are encoded by their common input and output counts in unary, followed by
the binary codes of the two circuits (`encSDInstance`). On this encoding, polarization is
polynomial-time whenever its parameters are computed in polynomial time in unary
(`SDInstance.computableInPolyTime_polarize`). The parameters of `SDInstance.exists_polarize` are
logarithmic in the number `k + 1` of outer coordinates, so polarization to error `2⁻⁽ᴷ⁽ˣ⁾⁺¹⁾` is
polynomial-time for every polynomial-time unary `K`
(`SDInstance.exists_polarize_computableInPolyTime`).

Two instances of `K` give the usual consequences, for constant thresholds `0 ≤ β < α² ≤ 1`:

* `K x` the length of the encoded instance: a polynomial-time map sends instances at distance at
  least `α` to distance at least `1 - 2⁻⁽ⁿ⁺¹⁾`, and instances at distance at most `β` to distance
  at most `2⁻⁽ⁿ⁺¹⁾`, where `n` is the input length
  (`SDInstance.exists_computableInPolyTime_polarize_length`).
* `K` constant: `SD^{α,β}` reduces in polynomial time to `SD^{α',β'}` for all constants
  `0 < β' < α' < 1` (`StatisticalDifference.polyTimeReducible`).

The circuits are De Morgan circuits with a common number of inputs and a common number of
outputs, as in `SDInstance`.

## Main definitions

* `Cslib.Complexity.encSDInstance`: the encoding of instances.

## Main results

* `Cslib.Complexity.SDInstance.computableInPolyTime_polarize`: polarization is polynomial-time.
* `Cslib.Complexity.SDInstance.exists_polarize_computableInPolyTime`: the Polarization Lemma with
  a polynomial-time map and error `2⁻⁽ᴷ⁽ˣ⁾⁺¹⁾`.
* `Cslib.Complexity.SDInstance.exists_computableInPolyTime_polarize_length`: error exponentially
  small in the instance length.
* `Cslib.Complexity.StatisticalDifference.polyTimeReducible`: `SD^{α,β}` reduces to `SD^{α',β'}`.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

@[expose] public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

/-- Instances of Statistical Difference encoded by the common input count and output count in
unary, followed by the binary codes of the two circuits (`Cslib.Circuits.Circuit.code`). -/
def encSDInstance : SDInstance ↪ List Bool :=
  ⟨fun x => encPair (encPair encUnary encUnary) (encPair encCode encCode)
      ((x.inputs, x.outputs), (x.left.code, x.right.code)), by
    rintro ⟨n, m, C₀, C₁⟩ ⟨n', m', C₀', C₁'⟩ h
    have h := (encPair (encPair encUnary encUnary) (encPair encCode encCode)).injective h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, h₀, h₁⟩ := h
    rw [Circuit.code_injective h₀, Circuit.code_injective h₁]⟩

theorem encSDInstance_apply (x : SDInstance) :
    encSDInstance x = encPair (encPair encUnary encUnary) (encPair encCode encCode)
      ((x.inputs, x.outputs), (x.left.code, x.right.code)) :=
  rfl

namespace SDInstance

/-- **Polarization is polynomial-time** on encoded instances, when its parameters are computed in
polynomial time in unary. -/
theorem computableInPolyTime_polarize {lam ell k : SDInstance → ℕ}
    (hlam : ComputableInPolyTime lam encSDInstance encUnary)
    (hell : ComputableInPolyTime ell encSDInstance encUnary)
    (hk : ComputableInPolyTime k encSDInstance encUnary) :
    ComputableInPolyTime (fun x => x.polarize (lam x) (ell x) (k x)) encSDInstance
      encSDInstance := by
  have hraw : ComputableInPolyTime
      (fun x : SDInstance => ((x.inputs, x.outputs), (x.left.code, x.right.code)))
      encSDInstance (encPair (encPair encUnary encUnary) (encPair encCode encCode)) :=
    .of_eq fun _ => rfl
  have hn := hraw.fst'.fst'
  have hm := hraw.fst'.snd'
  have hc₀ := hraw.snd'.fst'
  have hc₁ := hraw.snd'.snd'
  have hN : ComputableInPolyTime
      (fun x : SDInstance => k x + (k x + 1) * (ell x * (lam x + (lam x + 1) * x.inputs)))
      encSDInstance encUnary := by
    fun_prop
  have hM : ComputableInPolyTime
      (fun x : SDInstance => (k x + 1) * (ell x * ((lam x + 1) * x.outputs)))
      encSDInstance encUnary := by
    fun_prop
  have h := (hN.prod hM).prod
    ((computableInPolyTime_polarizeCode false hn hm hlam hell hk hc₀ hc₁).prod
      (computableInPolyTime_polarizeCode true hn hm hlam hell hk hc₀ hc₁))
  refine h.of_enc_eq fun x => ?_
  rw [encSDInstance_apply, polarizeCode_code, polarizeCode_code]
  rfl

/-- `⌊log₂ (n + 1)⌋ + 1` is the ceiling logarithm `⌈log₂ (n + 2)⌉`, the bit length of `n + 1`. -/
private theorem log_two_add_one_add_one (n : ℕ) :
    Nat.log 2 (n + 1) + 1 = Nat.clog 2 (n + 2) := by
  apply le_antisymm
  · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt one_lt_two]
    exact (Nat.pow_log_le_self 2 n.succ_ne_zero).trans_lt (Nat.lt_succ_self _)
  · exact Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two (n + 1))

/-- The polarization map of `SDInstance.exists_polarize`, with `K x + 1` outer coordinates, is
polynomial-time on encoded instances whenever `K` is polynomial-time with unary output. -/
theorem computableInPolyTime_polarize_log (m b : ℕ) {K : SDInstance → ℕ}
    (hK : ComputableInPolyTime K encSDInstance encUnary) :
    ComputableInPolyTime
      (fun x => x.polarize (m * (Nat.log 2 (K x + 1) + 1) - 1)
        (2 ^ (b * (Nat.log 2 (K x + 1) + 1))) (K x))
      encSDInstance encSDInstance := by
  have hK2 : ComputableInPolyTime (fun x => K x + 2) encSDInstance encUnary := by fun_prop
  have hclog : ComputableInPolyTime (fun x => Nat.clog 2 (K x + 2)) encSDInstance encUnary :=
    (unary_clog_const 2).comp hK2
  have hlam : ComputableInPolyTime (fun x => m * Nat.clog 2 (K x + 2) - 1) encSDInstance
      encUnary := by fun_prop
  have hell : ComputableInPolyTime (fun x => (2 ^ b) ^ Nat.clog 2 (K x + 2)) encSDInstance
      encUnary := unary_pow_clog_const hK2 (2 ^ b) 2
  simpa only [log_two_add_one_add_one, ← pow_mul] using
    computableInPolyTime_polarize hlam hell hK

/-- **The Polarization Lemma with a polynomial-time map** [SahaiVadhan2003, §3], for constant
thresholds `0 ≤ β < α² ≤ 1`. There are constants `m ≥ 1` and `b` such that, for every
polynomial-time unary parameter `K`, polarization with `λ = m (⌊log₂ (K x + 1)⌋ + 1)` inner
coordinates, `ℓ = 2 ^ (b (⌊log₂ (K x + 1)⌋ + 1))` copies and `K x + 1` outer coordinates is
polynomial-time on encoded instances, sends instances at distance at least `α` to distance at
least `1 - 2⁻⁽ᴷ⁽ˣ⁾⁺¹⁾`, and sends instances at distance at most `β` to distance at most
`2⁻⁽ᴷ⁽ˣ⁾⁺¹⁾`. -/
theorem exists_polarize_computableInPolyTime {α β : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ m b : ℕ, m ≠ 0 ∧ ∀ K : SDInstance → ℕ, ComputableInPolyTime K encSDInstance encUnary →
      ComputableInPolyTime
        (fun x => x.polarize (m * (Nat.log 2 (K x + 1) + 1) - 1)
          (2 ^ (b * (Nat.log 2 (K x + 1) + 1))) (K x))
        encSDInstance encSDInstance ∧
      ∀ x : SDInstance,
        (α ≤ x.distance → 1 - (1 / 2) ^ (K x + 1) ≤
          (x.polarize (m * (Nat.log 2 (K x + 1) + 1) - 1) (2 ^ (b * (Nat.log 2 (K x + 1) + 1)))
            (K x)).distance) ∧
        (x.distance ≤ β →
          (x.polarize (m * (Nat.log 2 (K x + 1) + 1) - 1) (2 ^ (b * (Nat.log 2 (K x + 1) + 1)))
            (K x)).distance ≤ (1 / 2) ^ (K x + 1)) := by
  obtain ⟨m, b, hm, -, -, h⟩ := exists_polarize hβ hβα hα hα1
  exact ⟨m, b, hm, fun K hK => ⟨computableInPolyTime_polarize_log m b hK, fun x => h x (K x)⟩⟩

/-- **Polarization to error exponentially small in the instance length** [SahaiVadhan2003, §3],
for constant thresholds `0 ≤ β < α² ≤ 1`: a polynomial-time map on encoded instances sends
instances at distance at least `α` to distance at least `1 - 2⁻⁽ⁿ⁺¹⁾`, and instances at distance at
most `β` to distance at most `2⁻⁽ⁿ⁺¹⁾`, where `n` is the length of the encoded input instance. -/
theorem exists_computableInPolyTime_polarize_length {α β : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ f : SDInstance → SDInstance, ComputableInPolyTime f encSDInstance encSDInstance ∧
      ∀ x : SDInstance,
        (α ≤ x.distance → 1 - (1 / 2) ^ ((encSDInstance x).length + 1) ≤ (f x).distance) ∧
        (x.distance ≤ β → (f x).distance ≤ (1 / 2) ^ ((encSDInstance x).length + 1)) := by
  obtain ⟨m, b, -, h⟩ := exists_polarize_computableInPolyTime hβ hβα hα hα1
  obtain ⟨hf, hdist⟩ := h _ (encoding_length encSDInstance)
  exact ⟨_, hf, hdist⟩

end SDInstance

/-- **Statistical Difference reduces to each of its gap versions** [SahaiVadhan2003, §3]: for
constant thresholds `0 ≤ β < α² ≤ 1` and `0 < β' < α' < 1`, `SD^{α,β}` reduces to `SD^{α',β'}` in
polynomial time, by polarization with a constant number of outer coordinates. -/
theorem StatisticalDifference.polyTimeReducible {α β α' β' : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hβ' : 0 < β') (hβα' : β' < α') (hα' : α' < 1) :
    PromiseProblem.PolyTimeReducible encSDInstance encSDInstance (StatisticalDifference α β)
      (StatisticalDifference α' β') := by
  obtain ⟨m, b, -, h⟩ := SDInstance.exists_polarize_computableInPolyTime hβ hβα hα hα1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (lt_min hβ' (sub_pos.2 hα'))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hk' : (1 / 2 : ℝ) ^ (k + 1) < min β' (1 - α') :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) k.le_succ).trans_lt hk
  obtain ⟨hf, hdist⟩ := h (fun _ => k) (const k)
  have hβα₀ : β < α := hβα.trans_le (pow_le_of_le_one hα hα1 two_ne_zero)
  refine ⟨_, hf, fun x hx => ?_, fun x hx => ?_⟩
  · have := (hdist x).1 hx
    rw [mem_yes_statisticalDifference]
    linarith [min_le_right β' (1 - α')]
  · rw [mem_no_statisticalDifference hβα₀] at hx
    have := (hdist x).2 hx
    rw [mem_no_statisticalDifference hβα']
    linarith [min_le_left β' (1 - α')]

end Cslib.Complexity
