/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Complexity.Problems.StatisticalDifference
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Circuit.Boolean.Polarization.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Polynomial-time polarization of Statistical Difference

The efficiency half of the Sahai–Vadhan Polarization Lemma [SahaiVadhan2003, Lemma 3.3].
Instances of Statistical Difference are encoded by their common input and output counts in unary,
followed by the binary codes of the two circuits (`encSDInstance`). On this encoding,
polarization is polynomial-time whenever the instance and its parameters are computed in
polynomial time, with the parameters in unary (`SDInstance.computableInPolyTime_polarize_comp`).
Of the parameters of `SDInstance.exists_polarize`, the number `λ` of inner coordinates is
logarithmic and the number `ℓ` of copies is polynomial in the number `k + 1` of outer coordinates
(`SDInstance.computableInPolyTime_polarize_log`). Polarization to error `2⁻⁽ᵏ⁺¹⁾` is therefore
polynomial-time with `k` a separate input in unary, as in the source
(`SDInstance.exists_computableInPolyTime_polarize_unary`), and with `k = K x` for every
polynomial-time unary function `K` of the instance
(`SDInstance.exists_computableInPolyTime_polarize`).

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

* `Cslib.Complexity.SDInstance.computableInPolyTime_polarize_comp`: polarization is
  polynomial-time; `Cslib.Complexity.SDInstance.computableInPolyTime_polarize` is the case of an
  input instance.
* `Cslib.Complexity.SDInstance.computableInPolyTime_polarize_log`: the polarization map of
  `SDInstance.exists_polarize` is polynomial-time.
* `Cslib.Complexity.SDInstance.exists_computableInPolyTime_polarize_unary`: the Polarization Lemma
  with a polynomial-time map and the error parameter in unary.
* `Cslib.Complexity.SDInstance.exists_computableInPolyTime_polarize`: the Polarization Lemma with
  a polynomial-time map and error `2⁻⁽ᴷ⁽ˣ⁾⁺¹⁾`.
* `Cslib.Complexity.SDInstance.exists_computableInPolyTime_polarize_length`: error exponentially
  small in the instance length.
* `Cslib.Complexity.StatisticalDifference.polyTimeReducible`: `SD^{α,β}` reduces to `SD^{α',β'}`.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

/-- Instances of Statistical Difference: the pair of counts, followed by the pair of circuit codes.
The pair of counts is the common input count in unary, framed, followed by the common output
count in unary; the pair of codes is the binary code (`Cslib.Circuits.Circuit.code`) of the left
circuit, framed, followed by the code of the right circuit. The pair of counts is itself framed,
since `encPair` frames its first component. -/
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
      ((x.inputs, x.outputs), (x.left.code, x.right.code)) := by
  rfl

namespace SDInstance

/-- **Polarization is polynomial-time**, for an instance and parameters computed in polynomial time
from any encoded input, with the parameters in unary. -/
theorem computableInPolyTime_polarize_comp {α : Type} {enc : α ↪ List Bool} {x : α → SDInstance}
    {lam ell k : α → ℕ} (hx : ComputableInPolyTime x enc encSDInstance)
    (hlam : ComputableInPolyTime lam enc encUnary) (hell : ComputableInPolyTime ell enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary) :
    ComputableInPolyTime (fun a => (x a).polarize (lam a) (ell a) (k a)) enc encSDInstance := by
  have hproj : ComputableInPolyTime
      (fun y : SDInstance => ((y.inputs, y.outputs), (y.left.code, y.right.code)))
      encSDInstance (encPair (encPair encUnary encUnary) (encPair encCode encCode)) :=
    .of_eq fun _ => rfl
  have hraw := hproj.comp' hx
  have hn : ComputableInPolyTime (fun a => (x a).inputs) enc encUnary := hraw.fst'.fst'
  have hm : ComputableInPolyTime (fun a => (x a).outputs) enc encUnary := hraw.fst'.snd'
  have hc₀ := hraw.snd'.fst'
  have hc₁ := hraw.snd'.snd'
  have hN : ComputableInPolyTime
      (fun a => k a + (k a + 1) * (ell a * (lam a + (lam a + 1) * (x a).inputs)))
      enc encUnary := by
    fun_prop
  have hM : ComputableInPolyTime
      (fun a => (k a + 1) * (ell a * ((lam a + 1) * (x a).outputs)))
      enc encUnary := by
    fun_prop
  have h := (hN.prod hM).prod
    ((computableInPolyTime_polarizeCode false hn hm hlam hell hk hc₀ hc₁).prod
      (computableInPolyTime_polarizeCode true hn hm hlam hell hk hc₀ hc₁))
  refine h.of_enc_eq fun a => ?_
  rw [encSDInstance_apply, polarizeCode_code, polarizeCode_code]
  rfl

/-- **Polarization is polynomial-time** on encoded instances, when its parameters are computed in
polynomial time in unary. -/
theorem computableInPolyTime_polarize {lam ell k : SDInstance → ℕ}
    (hlam : ComputableInPolyTime lam encSDInstance encUnary)
    (hell : ComputableInPolyTime ell encSDInstance encUnary)
    (hk : ComputableInPolyTime k encSDInstance encUnary) :
    ComputableInPolyTime (fun x => x.polarize (lam x) (ell x) (k x)) encSDInstance
      encSDInstance :=
  computableInPolyTime_polarize_comp id' hlam hell hk

/-- `⌊log₂ (n + 1)⌋ + 1` is the ceiling logarithm `⌈log₂ (n + 2)⌉`, the bit length of `n + 1`. -/
private theorem log_two_add_one_add_one (n : ℕ) :
    Nat.log 2 (n + 1) + 1 = Nat.clog 2 (n + 2) := by
  apply le_antisymm
  · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt one_lt_two]
    exact (Nat.pow_log_le_self 2 n.succ_ne_zero).trans_lt (Nat.lt_succ_self _)
  · exact Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two (n + 1))

/-- The polarization map of `SDInstance.exists_polarize`, with `K a + 1` outer coordinates, is
polynomial-time whenever the instance and `K` are computed in polynomial time from the encoded
input, with `K` in unary. -/
theorem computableInPolyTime_polarize_log {α : Type} {enc : α ↪ List Bool} (m b : ℕ)
    {x : α → SDInstance} {K : α → ℕ} (hx : ComputableInPolyTime x enc encSDInstance)
    (hK : ComputableInPolyTime K enc encUnary) :
    ComputableInPolyTime
      (fun a => (x a).polarize (m * (Nat.log 2 (K a + 1) + 1) - 1)
        (2 ^ (b * (Nat.log 2 (K a + 1) + 1))) (K a))
      enc encSDInstance := by
  have hK2 : ComputableInPolyTime (fun a => K a + 2) enc encUnary := by fun_prop
  have hclog : ComputableInPolyTime (fun a => Nat.clog 2 (K a + 2)) enc encUnary :=
    (unary_clog_const 2).comp hK2
  have hlam : ComputableInPolyTime (fun a => m * Nat.clog 2 (K a + 2) - 1) enc encUnary := by
    fun_prop
  have hell : ComputableInPolyTime (fun a => (2 ^ b) ^ Nat.clog 2 (K a + 2)) enc encUnary :=
    unary_pow_clog_const hK2 (2 ^ b) 2
  simpa only [log_two_add_one_add_one, ← pow_mul] using
    computableInPolyTime_polarize_comp hx hlam hell hK

/-- **The Polarization Lemma with a polynomial-time map** [SahaiVadhan2003, Lemma 3.3 and the
remark after its proof], for constant thresholds `0 ≤ β < α² ≤ 1`. There are constants `m ≥ 1`
and `b` such that, for every polynomial-time unary parameter `K`, polarization with
`λ = m (⌊log₂ (K x + 1)⌋ + 1)` inner coordinates, `ℓ = 2 ^ (b (⌊log₂ (K x + 1)⌋ + 1))` copies and
`K x + 1` outer coordinates is polynomial-time on encoded instances, sends instances at distance
at least `α` to distance at least `1 - 2⁻⁽ᴷ⁽ˣ⁾⁺¹⁾`, and sends instances at distance at most `β` to
distance at most `2⁻⁽ᴷ⁽ˣ⁾⁺¹⁾`.

Here the error parameter `K x` is a polynomial-time function of the instance alone. In the source
the error parameter is a separate input in unary; that form is
`SDInstance.exists_computableInPolyTime_polarize_unary`. -/
theorem exists_computableInPolyTime_polarize {α β : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2)
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
  exact ⟨m, b, hm, fun K hK =>
    ⟨computableInPolyTime_polarize_log m b id' hK, fun x => h x (K x)⟩⟩

/-- **The Polarization Lemma with the error parameter in unary** [SahaiVadhan2003, Lemma 3.3 and
the remark after its proof], for constant thresholds `0 ≤ β < α² ≤ 1`: a polynomial-time map on
pairs of an encoded instance and `k` in unary sends `(x, k)` with `x` at distance at least `α` to an
instance at distance at least `1 - 2⁻⁽ᵏ⁺¹⁾`, and `(x, k)` with `x` at distance at most `β` to an
instance at distance at most `2⁻⁽ᵏ⁺¹⁾`.

The source states Lemma 3.3 for the thresholds `2/3` and `1/3`, with strict inequalities and error
`2⁻ᵏ`, and extends it to thresholds `α² > β` in the remark after its proof. Here the thresholds are
non-strict and the error is `2⁻⁽ᵏ⁺¹⁾`. -/
theorem exists_computableInPolyTime_polarize_unary {α β : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ f : SDInstance × ℕ → SDInstance,
      ComputableInPolyTime f (encPair encSDInstance encUnary) encSDInstance ∧
      ∀ (x : SDInstance) (k : ℕ),
        (α ≤ x.distance → 1 - (1 / 2) ^ (k + 1) ≤ (f (x, k)).distance) ∧
        (x.distance ≤ β → (f (x, k)).distance ≤ (1 / 2) ^ (k + 1)) := by
  obtain ⟨m, b, -, -, -, h⟩ := exists_polarize hβ hβα hα hα1
  exact ⟨_, computableInPolyTime_polarize_log m b (fst _ _) (snd _ _), fun x k => h x k⟩

/-- **Polarization to error exponentially small in the instance length** [SahaiVadhan2003,
Lemma 3.3 and the remark after its proof], for constant thresholds `0 ≤ β < α² ≤ 1`: a
polynomial-time map on encoded instances sends instances at distance at least `α` to distance at
least `1 - 2⁻⁽ⁿ⁺¹⁾`, and instances at distance at most `β` to distance at most `2⁻⁽ⁿ⁺¹⁾`, where `n`
is the length of the encoded input instance. -/
theorem exists_computableInPolyTime_polarize_length {α β : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ f : SDInstance → SDInstance, ComputableInPolyTime f encSDInstance encSDInstance ∧
      ∀ x : SDInstance,
        (α ≤ x.distance → 1 - (1 / 2) ^ ((encSDInstance x).length + 1) ≤ (f x).distance) ∧
        (x.distance ≤ β → (f x).distance ≤ (1 / 2) ^ ((encSDInstance x).length + 1)) := by
  obtain ⟨m, b, -, h⟩ := exists_computableInPolyTime_polarize hβ hβα hα hα1
  obtain ⟨hf, hdist⟩ := h _ (encoding_length encSDInstance)
  exact ⟨_, hf, hdist⟩

end SDInstance

/-- **Statistical Difference reduces to each of its gap versions** [SahaiVadhan2003, Lemma 3.3 and
the remark after its proof]: for constant thresholds `0 ≤ β < α² ≤ 1` and `0 < β' < α' < 1`,
`SD^{α,β}` reduces to `SD^{α',β'}` in polynomial time, by polarization with a constant number of
outer coordinates. -/
theorem StatisticalDifference.polyTimeReducible {α β α' β' : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hβ' : 0 < β') (hβα' : β' < α') (hα' : α' < 1) :
    PromiseProblem.PolyTimeReducible encSDInstance encSDInstance (StatisticalDifference α β)
      (StatisticalDifference α' β') := by
  obtain ⟨m, b, -, h⟩ := SDInstance.exists_computableInPolyTime_polarize hβ hβα hα hα1
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
