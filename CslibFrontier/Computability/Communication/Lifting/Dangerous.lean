/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.Partition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Safe values and conditioning on gadget outputs

For an arbitrary Boolean gadget, `gadgetFiber` restricts Bob's finite input set to a specified
output on selected coordinates. `IsSafe` is the complement of the dangerous-value condition of
[Chattopadhyay, Filmus, Koroth, Meir and Pitassi, Definition 3.8]
[ChattopadhyayFilmusKorothMeirPitassi2021], for a nonempty set with its uniform distribution.
The multiplicative density parameter `σ` represents `2^((δY - ε)b)`. Nonemptiness and the
initial density of Bob's set are separate hypotheses, rather than part of this predicate.

The Bayes certificate retains the exact cardinality of a conditioned coordinate slice. Thus a
rare slice is not silently assigned the probability of a uniform slice. This is the finite-set,
multiplicative form of the step in the source's Claim 3.12. This module does not prove that
unsafe values are rare; that is the separate main dangerous-values lemma.

## Main definitions

* `Cslib.Communication.Lifting.gadgetFiber`: restriction to prescribed gadget outputs.
* `Cslib.Communication.Lifting.IsSafe`: no leaking and no loss of the target residual density.

## Main results

* `Cslib.Communication.Lifting.gadgetFiber_congr_left`: dependence only on queried coordinates.
* `Cslib.Communication.Lifting.IsSafe.congr_left`: safe values depend only on free coordinates.
* `Cslib.Communication.Lifting.exists_bayes_card_certificate`: failed density yields a strict
  conditional-output concentration certificate.
-/

public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ}

/-- Bob's inputs in `Y` giving output `β` on `I` when Alice's input is `x`. Only the values of
`x` and `β` on `I` are used. -/
@[expose] def gadgetFiber (g : Fin m → Fin m → Bool) (Y : Finset (Fin n → Fin m))
    (I : Finset (Fin n)) (x : Fin n → Fin m) (β : Fin n → Bool) :
    Finset (Fin n → Fin m) :=
  Y.filter fun y => ∀ i ∈ I, g (x i) (y i) = β i

/-- Membership in the gadget-output fiber. -/
@[simp] theorem mem_gadgetFiber {g : Fin m → Fin m → Bool} {Y : Finset (Fin n → Fin m)}
    {I : Finset (Fin n)} {x y : Fin n → Fin m} {β : Fin n → Bool} :
    y ∈ gadgetFiber g Y I x β ↔ y ∈ Y ∧ ∀ i ∈ I, g (x i) (y i) = β i :=
  mem_filter

/-- Conditioning on no gadget coordinates leaves the input set unchanged. -/
@[simp] theorem gadgetFiber_empty (g : Fin m → Fin m → Bool) (Y : Finset (Fin n → Fin m))
    (x : Fin n → Fin m) (β : Fin n → Bool) : gadgetFiber g Y ∅ x β = Y := by
  simp [gadgetFiber]

/-- Every gadget-output fiber is a subset of the original set. -/
theorem gadgetFiber_subset (g : Fin m → Fin m → Bool) (Y : Finset (Fin n → Fin m))
    (I : Finset (Fin n)) (x : Fin n → Fin m) (β : Fin n → Bool) :
    gadgetFiber g Y I x β ⊆ Y := filter_subset _ _

/-- Changing Alice's coordinates outside `I` does not change Bob's output fiber. -/
theorem gadgetFiber_congr_left (g : Fin m → Fin m → Bool) (Y : Finset (Fin n → Fin m))
    (I : Finset (Fin n)) {x x' : Fin n → Fin m} (hx : ∀ i ∈ I, x i = x' i)
    (β : Fin n → Bool) : gadgetFiber g Y I x β = gadgetFiber g Y I x' β := by
  ext y
  simp only [mem_gadgetFiber]
  apply and_congr_right
  intro _
  exact forall_congr' fun i => forall_congr' fun hi => by rw [hx i hi]

/-- Coordinate conditioning and gadget-output conditioning commute. No disjointness assumption
is required for this set identity. -/
theorem agreeOn_gadgetFiber (g : Fin m → Fin m → Bool) (Y : Finset (Fin n → Fin m))
    (I J : Finset (Fin n)) (x α : Fin n → Fin m) (β : Fin n → Bool) :
    agreeOn (gadgetFiber g Y I x β) J α = gadgetFiber g (agreeOn Y J α) I x β := by
  ext y
  simp only [agreeOn, mem_filter, mem_gadgetFiber]
  tauto

/-- An Alice value is safe for Bob's uniform finite source if every queried output fiber has
probability at least `2^(-|I|-1)` and retains density `σ` on the unqueried free coordinates.
For nonempty `Y`, this is exactly the complement of CFKMP Definition 3.8, with the original
density parameter converted to the multiplicative convention of `IsDense`. -/
structure IsSafe (g : Fin m → Fin m → Bool) (σ : ℝ) (F : Finset (Fin n))
    (Y : Finset (Fin n → Fin m)) (x : Fin n → Fin m) : Prop where
  /-- No queried output is too rare. -/
  nonleaking : ∀ I ⊆ F, ∀ β : Fin n → Bool,
    (#Y : ℝ) ≤ 2 ^ (#I + 1) * #(gadgetFiber g Y I x β)
  /-- Every queried output preserves the target density on remaining coordinates. -/
  dense : ∀ I ⊆ F, ∀ β : Fin n → Bool, IsDense σ (F \ I) (gadgetFiber g Y I x β)

/-- Safety only depends on the free coordinates of Alice's input. -/
theorem IsSafe.congr_left {g : Fin m → Fin m → Bool} {σ : ℝ} {F : Finset (Fin n)}
    {Y : Finset (Fin n → Fin m)} {x x' : Fin n → Fin m}
    (h : IsSafe g σ F Y x) (hx : ∀ i ∈ F, x i = x' i) : IsSafe g σ F Y x' := by
  have heq (I : Finset (Fin n)) (hI : I ⊆ F) (β : Fin n → Bool) :
      gadgetFiber g Y I x β = gadgetFiber g Y I x' β :=
    gadgetFiber_congr_left g Y I (fun i hi => hx i (hI hi)) β
  constructor
  · intro I hI β
    rw [← heq I hI β]
    exact h.nonleaking I hI β
  · intro I hI β
    rw [← heq I hI β]
    exact h.dense I hI β

/-- Safe conditioning of a nonempty source has a nonempty fiber for every output. -/
theorem IsSafe.fiber_nonempty {g : Fin m → Fin m → Bool} {σ : ℝ} {F : Finset (Fin n)}
    {Y : Finset (Fin n → Fin m)} {x : Fin n → Fin m}
    (h : IsSafe g σ F Y x) (hY : Y.Nonempty) {I : Finset (Fin n)} (hI : I ⊆ F)
    (β : Fin n → Bool) : (gadgetFiber g Y I x β).Nonempty := by
  have hc := h.nonleaking I hI β
  have hpos : (0 : ℝ) < #Y := by exact_mod_cast card_pos.mpr hY
  by_contra hn
  rw [not_nonempty_iff_eq_empty] at hn
  rw [hn, card_empty, Nat.cast_zero, mul_zero] at hc
  linarith

/-- **The cardinality Bayes certificate** (CFKMP Claim 3.12). If a nonleaking fiber fails
residual density, some disjoint coordinate slice has abnormally many inputs in that fiber.
The strict inequality keeps the actual slice size implicit; the next theorem makes it explicit. -/
theorem exists_bayes_card_certificate {g : Fin m → Fin m → Bool} {σ : ℝ}
    {F I : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    {x : Fin n → Fin m} {β : Fin n → Bool}
    (hleak : (#Y : ℝ) ≤ 2 ^ (#I + 1) * #(gadgetFiber g Y I x β))
    (hfail : ¬ IsDense σ (F \ I) (gadgetFiber g Y I x β)) :
    ∃ (J : Finset (Fin n)) (α : Fin n → Fin m),
      J ⊆ F \ I ∧ J.Nonempty ∧ Disjoint I J ∧
      (gadgetFiber g (agreeOn Y J α) I x β).Nonempty ∧
      (#Y : ℝ) < 2 ^ (#I + 1) * #(gadgetFiber g (agreeOn Y J α) I x β) * σ ^ #J := by
  unfold IsDense at hfail
  push Not at hfail
  obtain ⟨J, hJ, hJne, α, hα⟩ := hfail
  change (#(gadgetFiber g Y I x β) : ℝ) <
    #(agreeOn (gadgetFiber g Y I x β) J α) * σ ^ #J at hα
  rw [agreeOn_gadgetFiber] at hα
  have hdisj : Disjoint I J := by
    apply disjoint_left.mpr
    intro i hiI hiJ
    exact (mem_sdiff.mp (hJ hiJ)).2 hiI
  have hne : (gadgetFiber g (agreeOn Y J α) I x β).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    rw [hn, card_empty, Nat.cast_zero, zero_mul] at hα
    exact (not_lt_of_ge (Nat.cast_nonneg _)) hα
  refine ⟨J, α, hJ, hJne, hdisj, hne, ?_⟩
  have hmul := mul_lt_mul_of_pos_left hα (by positivity : (0 : ℝ) < 2 ^ (#I + 1))
  nlinarith

/-- The same Bayes certificate as a conditional frequency. Its threshold retains
`#Y / #(agreeOn Y J α)`, rather than replacing a possibly rare coordinate slice by a uniform one. -/
theorem exists_bayes_frequency_certificate {g : Fin m → Fin m → Bool} {σ : ℝ}
    {F I : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    {x : Fin n → Fin m} {β : Fin n → Bool} (hσ : 0 < σ)
    (hleak : (#Y : ℝ) ≤ 2 ^ (#I + 1) * #(gadgetFiber g Y I x β))
    (hfail : ¬ IsDense σ (F \ I) (gadgetFiber g Y I x β)) :
    ∃ (J : Finset (Fin n)) (α : Fin n → Fin m),
      J ⊆ F \ I ∧ J.Nonempty ∧ Disjoint I J ∧ (agreeOn Y J α).Nonempty ∧
      (#Y : ℝ) / #(agreeOn Y J α) / (2 ^ (#I + 1) * σ ^ #J) <
        #(gadgetFiber g (agreeOn Y J α) I x β) / (#(agreeOn Y J α) : ℝ) := by
  obtain ⟨J, α, hJ, hJne, hd, hne, hcard⟩ := exists_bayes_card_certificate hleak hfail
  have hAne : (agreeOn Y J α).Nonempty :=
    hne.mono (gadgetFiber_subset g _ I x β)
  have hA : (0 : ℝ) < #(agreeOn Y J α) := by exact_mod_cast card_pos.mpr hAne
  refine ⟨J, α, hJ, hJne, hd, hAne, ?_⟩
  have hc : (0 : ℝ) < 2 ^ (#I + 1) * σ ^ #J := by positivity
  have hdiv : (#Y : ℝ) / (2 ^ (#I + 1) * σ ^ #J) <
      #(gadgetFiber g (agreeOn Y J α) I x β) := by
    apply (div_lt_iff₀ hc).mpr
    nlinarith
  have hratio := (div_lt_div_iff_of_pos_right hA).mpr hdiv
  convert hratio using 1; ring

end Cslib.Communication.Lifting
