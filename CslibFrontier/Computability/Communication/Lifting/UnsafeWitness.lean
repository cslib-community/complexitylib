/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.SafeParities
public import CslibFrontier.Computability.Communication.Lifting.DangerousProbability
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic.Linarith

/-!
# Unsafe values have conditional parity witnesses

Supported conditioning assignments are represented canonically by their values on the conditioned
coordinates and zero elsewhere. Thus counting witnesses need not pay for irrelevant coordinates.
The witness conversion below joins the pointwise safety criterion to the sampling-tail API.
-/

public section

namespace Cslib.Communication.Lifting

open Finset BitString Probability

variable {n m : ℕ}

namespace ParityTest

/-- Extend a partial conditioning assignment by zero outside its domain. -/
@[expose] def extendAssignment [NeZero m] (J : Finset (Fin n)) (a : J → Fin m) : Fin n → Fin m :=
  fun i => if hi : i ∈ J then a ⟨i, hi⟩ else 0

/-- Canonical witnesses carry no arbitrary data on unconditioned coordinates. -/
@[expose] def IsCanonical [NeZero m] {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    (w : ParityTest F Y) : Prop := ∀ i ∉ w.conditioned, w.assignment i = 0

/-- Canonically extending the restriction of an assignment does not change its conditioning
slice. -/
theorem agreeOn_extend_restrict [NeZero m] (Y : Finset (Fin n → Fin m))
    (J : Finset (Fin n)) (α : Fin n → Fin m) :
    agreeOn Y J (extendAssignment J (J.restrict α)) = agreeOn Y J α := by
  ext y
  simp only [agreeOn, mem_filter]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  simp [extendAssignment, hi]

/-- Construct a supported parity test from a partial conditioning assignment. -/
@[expose] def ofPartial [NeZero m] {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    (S J : Finset (Fin n)) (a : J → Fin m) (hS : S ⊆ F) (hJ : J ⊆ F)
    (hd : Disjoint J S) (ha : (agreeOn Y J (extendAssignment J a)).Nonempty) : ParityTest F Y where
  parity := S
  conditioned := J
  assignment := extendAssignment J a
  parity_subset := hS
  conditioned_subset := hJ
  disjoint := hd
  supported := ha

/-- Partial-assignment witnesses are canonical. -/
theorem ofPartial_isCanonical [NeZero m] {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    (S J : Finset (Fin n)) (a : J → Fin m) (hS : S ⊆ F) (hJ : J ⊆ F)
    (hd : Disjoint J S) (ha : (agreeOn Y J (extendAssignment J a)).Nonempty) :
    (ofPartial S J a hS hJ hd ha).IsCanonical := by
  intro i hi
  change i ∉ J at hi
  simp only [ofPartial, extendAssignment, hi, dite_false]

/-- Evaluate a conditional parity test directly on the original source. -/
theorem bias_eq_sum {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    (w : ParityTest F Y) (g : Fin m → Fin m → Bool) (x : Fin n → Fin m) :
    w.bias g x = |∑ y, ((PMF.uniformOfFinset (agreeOn Y w.conditioned w.assignment)
      w.supported) y).toReal * chi ℝ w.parity (fun i => g (x i) (y i))| := by
  unfold ParityTest.bias
  rw [PMF.sum_map_mul]
  congr 1
  apply sum_congr rfl
  intro y _
  congr 1
  rw [chi_eq_signVal_parityOn, parityOn_eq_sum]
  congr 1
  exact sum_coe_sort w.parity (fun i => g (x i) (y i))

/-- A parity of a gadget output law is exactly the corresponding conditional parity test. -/
theorem bias_eq_outputLaw {F I J : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    (w : ParityTest F Y) (g : Fin m → Fin m → Bool) (x : Fin n → Fin m)
    (S : Finset I) (α : Fin n → Fin m) (hA : (agreeOn Y J α).Nonempty)
    (hp : w.parity = S.map (Function.Embedding.subtype (· ∈ I)))
    (ha : agreeOn Y w.conditioned w.assignment = agreeOn Y J α) :
    w.bias g x = |BitString.bias (gadgetOutputLaw g (agreeOn Y J α) hA I x) S| := by
  rw [bias_eq_sum, bias_gadgetOutputLaw]
  have hlaw : PMF.uniformOfFinset (agreeOn Y w.conditioned w.assignment) w.supported =
      PMF.uniformOfFinset (agreeOn Y J α) hA := by congr 1
  rw [hlaw, hp]

end ParityTest

private theorem half_global_bias_bound_le {I : Finset (Fin n)} (hI : I.Nonempty) (s : ℕ) :
    (1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ s ≤
      (1 / 2 : ℝ) * (1 / (2 * I.card) : ℝ) ^ s := by
  have hi : (0 : ℝ) < I.card := by exact_mod_cast card_pos.mpr hI
  have hin : (I.card : ℝ) ≤ n := by
    exact_mod_cast (show I.card ≤ n by simpa only [Fintype.card_fin] using card_le_univ I)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le (by positivity) (by linarith)) s

/-- A conditional parity on an output subset has a canonical supported test with the same bias.
The larger output set `I` is absent from the test itself. -/
theorem exists_canonical_parityTest [NeZero m] {F I J : Finset (Fin n)}
    {Y : Finset (Fin n → Fin m)} (hI : I ⊆ F) (hJ : J ⊆ F \ I)
    (S : Finset I) (α : Fin n → Fin m) (hA : (agreeOn Y J α).Nonempty)
    (g : Fin m → Fin m → Bool) (x : Fin n → Fin m) :
    ∃ w : ParityTest F Y, w.IsCanonical ∧
      w.parity = S.map (Function.Embedding.subtype (· ∈ I)) ∧
      w.conditioned = J ∧ J.restrict w.assignment = J.restrict α ∧
      w.bias g x = |bias (gadgetOutputLaw g (agreeOn Y J α) hA I x) S| := by
  let P := S.map (Function.Embedding.subtype (· ∈ I))
  have hPI : P ⊆ I := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_map.mp hi
    exact j.property
  have hJF : J ⊆ F := fun j hj => (mem_sdiff.mp (hJ hj)).1
  have hd : Disjoint J P := by
    apply disjoint_left.mpr
    intro i hiJ hiP
    exact (mem_sdiff.mp (hJ hiJ)).2 (hPI hiP)
  have ha : (agreeOn Y J (ParityTest.extendAssignment J (J.restrict α))).Nonempty := by
    simpa only [ParityTest.agreeOn_extend_restrict] using hA
  let w := ParityTest.ofPartial P J (J.restrict α) (hPI.trans hI) hJF hd ha
  refine ⟨w, ParityTest.ofPartial_isCanonical _ _ _ _ _ _ _, rfl, rfl, ?_, ?_⟩
  · funext j
    simp [w, ParityTest.ofPartial, ParityTest.extendAssignment, j.property]
  · apply ParityTest.bias_eq_outputLaw w g x S α hA rfl
    exact ParityTest.agreeOn_extend_restrict Y J α

/-- Every unsafe value has a canonical conditional parity witness. The integer order assigned
to each conditioning slice must satisfy the explicit low-order-count budget. The witness is
unconditional, or has at least that many parity coordinates. Its bias exceeds the uniform
ambient threshold `1/2 * (2n)^(-|S|)`, independently of the larger output set used to find it.

This is a explicit witness reduction, not a bound on the number of eligible witnesses. -/
theorem exists_parityTest_of_not_isSafe [NeZero m]
    (g : Fin m → Fin m → Bool) (σ : ℝ) (F : Finset (Fin n))
    (Y : Finset (Fin n → Fin m)) (hY : Y.Nonempty) (hσ : 0 ≤ σ)
    (order : (I J : Finset (Fin n)) → (J → Fin m) → ℕ)
    (horder : ∀ I ⊆ F, ∀ J ⊆ F \ I, J.Nonempty → ∀ a : J → Fin m,
      ∀ _hA : (agreeOn Y J (ParityTest.extendAssignment J a)).Nonempty,
      1 ≤ order I J a ∧
        2 * (#{S : Finset I | S.card < order I J a} + 1 : ℝ) * σ ^ #J *
          #(agreeOn Y J (ParityTest.extendAssignment J a)) ≤ #Y)
    (x : Fin n → Fin m) (hunsafe : ¬ IsSafe g σ F Y x) :
    ∃ (I : Finset (Fin n)) (w : ParityTest F Y),
      I ⊆ F ∧ w.IsCanonical ∧ w.parity ⊆ I ∧ w.parity.Nonempty ∧
      (w.conditioned = ∅ ∨ (w.conditioned.Nonempty ∧ w.conditioned ⊆ F \ I ∧
        order I w.conditioned (w.conditioned.restrict w.assignment) ≤ w.parity.card)) ∧
      (1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.parity.card < w.bias g x := by
  classical
  by_contra! hnone
  apply hunsafe
  apply isSafe_of_parity_bias_le g σ F Y hY x hσ
  · intro I hI S hS
    have hA : (agreeOn Y ∅ (fun _ => (0 : Fin m))).Nonempty := by simpa [agreeOn] using hY
    obtain ⟨w, hcan, hp, hj, _, hb⟩ :=
      exists_canonical_parityTest hI (empty_subset _) S (fun _ => (0 : Fin m)) hA g x
    have hPI : w.parity ⊆ I := by
      rw [hp]
      intro i hi
      obtain ⟨j, _, rfl⟩ := mem_map.mp hi
      exact j.property
    have hPne : w.parity.Nonempty := by simpa only [hp, map_nonempty] using hS
    have hIp : I.Nonempty := hPne.mono hPI
    have hb' : w.bias g x = |bias (gadgetOutputLaw g Y hY I x) S| := by
      simpa [agreeOn] using hb
    have hc := hnone I w hI hcan hPI hPne (Or.inl hj)
    rw [hb', hp, card_map] at hc
    exact hc.trans (half_global_bias_bound_le hIp S.card)
  · intro I hI J hJ hJne α hA
    let a := J.restrict α
    have ha : (agreeOn Y J (ParityTest.extendAssignment J a)).Nonempty := by
      simpa only [a, ParityTest.agreeOn_extend_restrict] using hA
    obtain ⟨ht, hcap⟩ := horder I hI J hJ hJne a ha
    refine ⟨order I J a, ht, ?_, ?_⟩
    · intro S hS
      obtain ⟨w, hcan, hp, hj, hass, hb⟩ := exists_canonical_parityTest hI hJ S α hA g x
      have hPI : w.parity ⊆ I := by
        rw [hp]
        intro i hi
        obtain ⟨j, _, rfl⟩ := mem_map.mp hi
        exact j.property
      have hSnonempty : S.Nonempty := card_pos.mp (by omega)
      have hPne : w.parity.Nonempty := by simpa only [hp, map_nonempty] using hSnonempty
      have hIp : I.Nonempty := hPne.mono hPI
      have ho : order I w.conditioned (w.conditioned.restrict w.assignment) =
          order I J (J.restrict α) := by
        subst J
        rw [hass]
      have he : w.conditioned.Nonempty ∧ w.conditioned ⊆ F \ I ∧
          order I w.conditioned (w.conditioned.restrict w.assignment) ≤ w.parity.card := by
        simpa only [ho, hj, hp, card_map, a] using And.intro hJne (And.intro hJ hS)
      have hc := hnone I w hI hcan hPI hPne (Or.inr he)
      rw [hb, hp, card_map] at hc
      have hpow : (0 : ℝ) ≤ (1 / (2 * I.card) : ℝ) ^ S.card := by positivity
      exact (hc.trans (half_global_bias_bound_le hIp S.card)).trans (by nlinarith)
    · simpa only [a, ParityTest.agreeOn_extend_restrict] using hcap

end Cslib.Communication.Lifting
