/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID.FirstAccepted
public import CslibFrontier.Probability.TupleSampler
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Direct-product decoding

Draft: definitions and counting identities for the direct-product decoder.
-/

public section

namespace Cslib.Circuits.Boolean.DirectProduct

open Finset Cslib.Probability

variable {U V : Type*} [Fintype U] [DecidableEq U] {k : ℕ}

/-- **Fibres of overwriting on `P`**: summing `H` over the tuples `r` overwritten by `b₀` on `P`
counts each tuple that agrees with `b₀` on `P` once for each of the `#U ^ #P` values `r` had
there. -/
theorem sum_piecewise_eq_card_pow_mul_sum {M : Type*} [AddCommMonoid M] (P : Finset (Fin k))
    (b₀ : Fin k → U) (H : (Fin k → U) → M) :
    ∑ r : Fin k → U, H (P.piecewise b₀ r) =
      Fintype.card U ^ #P • ∑ y ∈ {y : Fin k → U | ∀ i ∈ P, y i = b₀ i}, H y := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := {y : Fin k → U | ∀ i ∈ P, y i = b₀ i})
    (g := fun r => P.piecewise b₀ r) (fun r _ => by
      simp only [mem_filter, mem_univ, true_and]
      intro i hi
      exact P.piecewise_eq_of_mem _ _ hi), smul_sum]
  refine sum_congr rfl fun y hy => ?_
  have hy' : ∀ i ∈ P, y i = b₀ i := by simpa using hy
  rw [sum_congr rfl fun r hr => by rw [(mem_filter.1 hr).2], sum_const]
  congr 1
  have hfib : ({r ∈ (univ : Finset (Fin k → U)) | P.piecewise b₀ r = y}) =
      Fintype.piFinset fun i => if i ∈ P then univ else {y i} := by
    ext r
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl i
      split_ifs with hi
      · exact mem_univ _
      · simp [P.piecewise_eq_of_notMem _ _ hi]
    · intro h
      funext i
      by_cases hi : i ∈ P
      · rw [P.piecewise_eq_of_mem _ _ hi, hy' i hi]
      · have := h i
        simp only [hi, ↓reduceIte, mem_singleton] at this
        rw [P.piecewise_eq_of_notMem _ _ hi, this]
  rw [hfib, Fintype.card_piFinset]
  simp [apply_ite card, prod_ite_mem]

/-- A trial: a free position `j` and a filler tuple `r`. -/
abbrev Trial (U : Type*) (k : ℕ) := Fin k × (Fin k → U)

/-- The tuple queried by a trial: `b₀` on `P`, the input `x` at the free position `t.1`, and the
filler `t.2` elsewhere. -/
def trialTuple (P : Finset (Fin k)) (b₀ : Fin k → U) (x : U) (t : Trial U k) : Fin k → U :=
  Function.update (P.piecewise b₀ t.2) t.1 x

/-- **Counting trials**: the trials with free position outside `P` whose tuple satisfies `q`
(which may depend on the free position) number `#U ^ (#P + 1)` for each pair `(y, j)` with
`y = b₀` on `P`, `y j = x`, `j ∉ P` and `q j y`. -/
theorem card_filter_trialTuple (P : Finset (Fin k)) (b₀ : Fin k → U) (x : U)
    (q : Fin k → (Fin k → U) → Prop) [∀ j y, Decidable (q j y)] :
    #{t : Trial U k | t.1 ∉ P ∧ q t.1 (trialTuple P b₀ x t)} =
      Fintype.card U ^ (#P + 1) *
        #{p : Fin k × (Fin k → U) | p.1 ∉ P ∧ (∀ i ∈ P, p.2 i = b₀ i) ∧ p.2 p.1 = x ∧
          q p.1 p.2} := by
  classical
  simp only [card_filter, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ P
  · simp [hj]
  have hpw : ∀ r : Fin k → U, trialTuple P b₀ x (j, r) =
      (insert j P).piecewise (Function.update b₀ j x) r := by
    intro r
    funext i
    by_cases hij : i = j
    · subst hij
      simp [trialTuple]
    · by_cases hi : i ∈ P <;> simp [trialTuple, hij, hi]
  have h := sum_piecewise_eq_card_pow_mul_sum (insert j P) (Function.update b₀ j x)
    (fun y => if q j y then 1 else 0)
  simp only [hj, not_false_eq_true, true_and, hpw, h, card_insert_of_notMem hj, smul_eq_mul,
    sum_boole, Nat.cast_id]
  rw [← mul_sum, sum_boole, Nat.cast_id]
  congr 2
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp,
    Function.update_self]
  constructor
  · rintro ⟨⟨hx, hP⟩, hq⟩
    refine ⟨fun i hi => ?_, hx, hq⟩
    rw [hP i hi, Function.update_of_ne (fun h : i = j => hj (h ▸ hi))]
  · rintro ⟨hP, hx, hq⟩
    refine ⟨⟨hx, fun i hi => ?_⟩, hq⟩
    rw [hP i hi, Function.update_of_ne (fun h : i = j => hj (h ▸ hi))]

variable {V : Type*} [DecidableEq V]

/-- A trial is **accepted** at `x` when its free position lies outside `P` and `C'` gives its
tuple the same values on `P` as it gives `b₀`. -/
def accepts (C' : (Fin k → U) → Fin k → V) (P : Finset (Fin k)) (b₀ : Fin k → U) (x : U)
    (t : Trial U k) : Bool :=
  decide (t.1 ∉ P ∧ ∀ i ∈ P, C' (trialTuple P b₀ x t) i = C' b₀ i)

/-- **The direct-product decoder**: on input `x`, the value of `C'` at the free position of the
first accepted trial, or `dflt` if no trial is accepted. -/
def dpDecode (C' : (Fin k → U) → Fin k → V) (dflt : V) (P : Finset (Fin k)) (b₀ : Fin k → U)
    {m : ℕ} (v : Fin m → Trial U k) (x : U) : V :=
  ((firstAccepted (accepts C' P b₀ x) v).map fun t => C' (trialTuple P b₀ x t) t.1).getD dflt

/-- The pairs `(j, y)` that account for the trials accepted at `x`: `j ∉ P`, `y = b₀` on `P`,
`y j = x` and `C' y = C' b₀` on `P`. -/
def acceptedPairs (C' : (Fin k → U) → Fin k → V) (P : Finset (Fin k)) (b₀ : Fin k → U)
    (x : U) : Finset (Fin k × (Fin k → U)) :=
  {p | p.1 ∉ P ∧ (∀ i ∈ P, p.2 i = b₀ i) ∧ p.2 p.1 = x ∧ ∀ i ∈ P, C' p.2 i = C' b₀ i}

/-- The accepted pairs at which `C'` disagrees with `f`. -/
def badPairs (C' : (Fin k → U) → Fin k → V) (f : U → V) (P : Finset (Fin k))
    (b₀ : Fin k → U) (x : U) : Finset (Fin k × (Fin k → U)) :=
  {p | p.1 ∉ P ∧ (∀ i ∈ P, p.2 i = b₀ i) ∧ p.2 p.1 = x ∧
    ((∀ i ∈ P, C' p.2 i = C' b₀ i) ∧ C' p.2 p.1 ≠ f x)}

/-- The trials accepted at `x` number `#U ^ (#P + 1)` per accepted pair. -/
theorem card_filter_accepts (C' : (Fin k → U) → Fin k → V) (P : Finset (Fin k))
    (b₀ : Fin k → U) (x : U) :
    #{t : Trial U k | accepts C' P b₀ x t = true} =
      Fintype.card U ^ (#P + 1) * #(acceptedPairs C' P b₀ x) := by
  have := card_filter_trialTuple P b₀ x (fun _ y => ∀ i ∈ P, C' y i = C' b₀ i)
  simpa [accepts, acceptedPairs] using this

/-- **Error at one input**: weighted by the number `a` of accepted pairs at `x`, the trial vectors
on which the decoder errs at `x` are at most the bad pairs times `N ^ m`, plus `a` times the
vectors rejecting every trial. Here `N` is the number of trials. -/
theorem card_filter_dpDecode_ne_mul_le (C' : (Fin k → U) → Fin k → V) (f : U → V) (dflt : V)
    (P : Finset (Fin k)) (b₀ : Fin k → U) (m : ℕ) (x : U) :
    #{v : Fin m → Trial U k | dpDecode C' dflt P b₀ v x ≠ f x} * #(acceptedPairs C' P b₀ x) ≤
      #(badPairs C' f P b₀ x) * Fintype.card (Trial U k) ^ m +
        #(acceptedPairs C' P b₀ x) * (Fintype.card (Trial U k) -
          Fintype.card U ^ (#P + 1) * #(acceptedPairs C' P b₀ x)) ^ m := by
  classical
  have : Nonempty U := ⟨x⟩
  have hacc := card_filter_accepts C' P b₀ x
  set acc := accepts C' P b₀ x
  set bad : Trial U k → Bool := fun t => decide (C' (trialTuple P b₀ x t) t.1 ≠ f x)
  have haccbad : #{t : Trial U k | acc t ∧ bad t} =
      Fintype.card U ^ (#P + 1) * #(badPairs C' f P b₀ x) := by
    have := card_filter_trialTuple P b₀ x
      (fun j y => (∀ i ∈ P, C' y i = C' b₀ i) ∧ C' y j ≠ f x)
    simpa [acc, bad, accepts, badPairs, and_assoc] using this
  set a := #(acceptedPairs C' P b₀ x)
  set c := Fintype.card U ^ (#P + 1)
  have hfa := card_filter_firstAccepted_bad_mul_le acc bad m
  rw [hacc, haccbad] at hfa
  have hc : 0 < c := pow_pos Fintype.card_pos _
  have hfa' : #{v : Fin m → Trial U k | (firstAccepted acc v).any bad} * a ≤
      #(badPairs C' f P b₀ x) * Fintype.card (Trial U k) ^ m := by
    refine Nat.le_of_mul_le_mul_left ?_ hc
    calc c * (#{v : Fin m → Trial U k | (firstAccepted acc v).any bad} * a)
        = #{v : Fin m → Trial U k | (firstAccepted acc v).any bad} * (c * a) := by ring
      _ ≤ _ := hfa
      _ = _ := by ring
  have hnone : #{v : Fin m → Trial U k | ∀ i, acc (v i) = false} =
      (Fintype.card (Trial U k) - c * a) ^ m := by
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Trial U k)))
      (p := fun t => acc t = true)
    simp only [Bool.not_eq_true, card_univ] at hsplit
    rw [card_filter_forall_not_acc, ← hacc]
    congr 1
    omega
  have hsub : #{v : Fin m → Trial U k | dpDecode C' dflt P b₀ v x ≠ f x} ≤
      #{v : Fin m → Trial U k | (firstAccepted acc v).any bad} +
        #{v : Fin m → Trial U k | ∀ i, acc (v i) = false} := by
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro v hv
    simp only [mem_filter, mem_univ, true_and, mem_union] at hv ⊢
    cases h : firstAccepted acc v with
    | none => exact Or.inr ((firstAccepted_eq_none_iff acc v).1 h)
    | some t =>
      left
      simpa [dpDecode, acc, h, bad] using hv
  rw [← hnone]
  nlinarith [Nat.mul_le_mul_right a hsub]

/-- The tuples consistent with the seed: equal to `b₀` on `P`, with the same `C'` values there. -/
def consistent (C' : (Fin k → U) → Fin k → V) (P : Finset (Fin k)) (b₀ : Fin k → U) :
    Finset (Fin k → U) :=
  {y | (∀ i ∈ P, y i = b₀ i) ∧ ∀ i ∈ P, C' y i = C' b₀ i}

theorem acceptedPairs_eq_filter (C' : (Fin k → U) → Fin k → V) (P : Finset (Fin k))
    (b₀ : Fin k → U) (x : U) :
    acceptedPairs C' P b₀ x = (Pᶜ ×ˢ consistent C' P b₀).filter fun p => p.2 p.1 = x := by
  ext p
  simp only [acceptedPairs, consistent, mem_filter, mem_univ, true_and, mem_product, mem_compl]
  tauto

theorem badPairs_eq_filter (C' : (Fin k → U) → Fin k → V) (f : U → V) (P : Finset (Fin k))
    (b₀ : Fin k → U) (x : U) :
    badPairs C' f P b₀ x =
      ((Pᶜ ×ˢ consistent C' P b₀).filter fun p => C' p.2 p.1 ≠ f (p.2 p.1)).filter
        fun p => p.2 p.1 = x := by
  ext p
  simp only [badPairs, consistent, mem_filter, mem_univ, true_and, mem_product, mem_compl]
  constructor
  · rintro ⟨h1, h2, rfl, h3, h4⟩
    exact ⟨⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
  · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
    exact ⟨h1, h2, rfl, h3, h4⟩

/-- **Accepted pairs by input**: weighting the accepted pairs at `x` by `g x` and summing over
`x` is summing `g (y j)` over the free positions `j` of the consistent tuples `y`. -/
theorem sum_card_acceptedPairs_nsmul {M : Type*} [AddCommMonoid M]
    (C' : (Fin k → U) → Fin k → V) (P : Finset (Fin k)) (b₀ : Fin k → U) (g : U → M) :
    ∑ x, #(acceptedPairs C' P b₀ x) • g x = ∑ y ∈ consistent C' P b₀, ∑ j ∈ Pᶜ, g (y j) := by
  classical
  have h : ∀ x, #(acceptedPairs C' P b₀ x) • g x =
      ∑ p ∈ (Pᶜ ×ˢ consistent C' P b₀).filter (fun p => p.2 p.1 = x), g (p.2 p.1) := by
    intro x
    rw [acceptedPairs_eq_filter, ← sum_const]
    exact sum_congr rfl fun p hp => by rw [(mem_filter.1 hp).2]
  simp_rw [h]
  rw [sum_fiberwise_of_maps_to (fun _ _ => mem_univ _), sum_product, sum_comm]

/-- **Bad pairs by tuple**: the bad pairs, summed over inputs, are the free positions at which a
consistent tuple disagrees with `f`. -/
theorem sum_card_badPairs (C' : (Fin k → U) → Fin k → V) (f : U → V) (P : Finset (Fin k))
    (b₀ : Fin k → U) :
    ∑ x, #(badPairs C' f P b₀ x) =
      ∑ y ∈ consistent C' P b₀, #{j ∈ Pᶜ | C' y j ≠ f (y j)} := by
  classical
  simp_rw [badPairs_eq_filter]
  rw [← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _), card_filter, sum_product, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [card_filter]

/-- **Edges into a dense slice**: for a family `S` of tuples that agree on `P`, the free entries
carry weight at least `(#S - #U ^ w exp (-μ w / 8)) μ w / 2`, where `w = #Pᶜ`. This applies the
tuple-sampler weight bound to the coordinates outside `P`. -/
theorem sub_mul_le_two_mul_sum_sum_compl [Nonempty U] (F : U → ℝ) (hF : ∀ x, F x ∈ Set.Icc 0 1)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ * Fintype.card U ≤ ∑ x, F x) (P : Finset (Fin k))
    (b₀ : Fin k → U) (S : Finset (Fin k → U)) (hS : ∀ y ∈ S, ∀ i ∈ P, y i = b₀ i) :
    ((#S : ℝ) - Fintype.card U ^ #Pᶜ * Real.exp (-(μ * #Pᶜ / 8))) * (μ * #Pᶜ) ≤
      2 * ∑ y ∈ S, ∑ j ∈ Pᶜ, F (y j) := by
  classical
  let ρ : (Fin k → U) → ({i // i ∈ Pᶜ} → U) := fun y i => y i
  have hinj : Set.InjOn ρ S := by
    intro y hy z hz h
    funext i
    by_cases hi : i ∈ P
    · rw [hS y hy i hi, hS z hz i hi]
    · exact congrFun h ⟨i, mem_compl.2 hi⟩
  have h := sub_mul_le_two_mul_sum_sum (ι := {i // i ∈ Pᶜ}) F hF hμ0 hμ (S.image ρ)
  rw [card_image_of_injOn hinj, sum_image hinj, Fintype.card_coe] at h
  refine h.trans_eq ?_
  congr 1
  refine sum_congr rfl fun y _ => ?_
  exact sum_coe_sort Pᶜ fun j => F (y j)

/-- **Few inputs are rarely accepted**: if the consistent tuples have density at least `μ` among
the tuples agreeing with `b₀` on `P`, the inputs with fewer than `#S w / (4 #U)` accepted pairs,
where `S` is the consistent set and `w = #Pᶜ`, number at most `8 #U log (2 / μ) / w`. -/
theorem card_filter_acceptedPairs_lt_mul_le (C' : (Fin k → U) → Fin k → V) (P : Finset (Fin k))
    (b₀ : Fin k → U) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hS : μ * Fintype.card U ^ #Pᶜ ≤ #(consistent C' P b₀)) :
    (#{x | (#(acceptedPairs C' P b₀ x) : ℝ) <
        #(consistent C' P b₀) * #Pᶜ / (4 * Fintype.card U)} : ℝ) * #Pᶜ ≤
      8 * Fintype.card U * Real.log (2 / μ) := by
  classical
  set S := consistent C' P b₀
  set w : ℕ := #Pᶜ
  set n : ℕ := Fintype.card U
  set L := ({x | (#(acceptedPairs C' P b₀ x) : ℝ) < #S * w / (4 * n)} : Finset U)
  rcases L.eq_empty_or_nonempty with hL | hL
  · rw [hL, card_empty, Nat.cast_zero, zero_mul]
    have : 0 ≤ Real.log (2 / μ) := Real.log_nonneg (by rw [le_div_iff₀ hμ0]; linarith)
    positivity
  have : Nonempty U := let ⟨x, _⟩ := hL; ⟨x⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  set F : U → ℝ := fun x => if x ∈ L then 1 else 0
  have hF : ∀ x, F x ∈ Set.Icc 0 1 := fun x => by by_cases hx : x ∈ L <;> simp [F, hx]
  set μL : ℝ := #L / n
  have hμL : μL * n ≤ ∑ x, F x := by
    simp [F, μL, div_mul_cancel₀ _ hn.ne']
  have hrob := sub_mul_le_two_mul_sum_sum_compl F hF (by positivity) hμL P b₀ S
    (fun y hy => (mem_filter.1 hy).2.1)
  have hsum : ∑ y ∈ S, ∑ j ∈ Pᶜ, F (y j) = ∑ x, (#(acceptedPairs C' P b₀ x) : ℝ) * F x := by
    rw [← sum_card_acceptedPairs_nsmul]
    simp [nsmul_eq_mul]
  have hlow : ∑ x, (#(acceptedPairs C' P b₀ x) : ℝ) * F x ≤ #L * (#S * w / (4 * n)) := by
    rw [← sum_filter_add_sum_filter_not univ (· ∈ L)]
    have h0 : ∑ x ∈ univ.filter (· ∉ L), (#(acceptedPairs C' P b₀ x) : ℝ) * F x = 0 :=
      sum_eq_zero fun x hx => by simp [F, (mem_filter.1 hx).2]
    rw [h0, add_zero, filter_mem_eq_inter, univ_inter]
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun x hx => ?_
    have := (mem_filter.1 hx).2
    simp only [F, hx, ite_true, mul_one]
    exact this.le
  rw [hsum] at hrob
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hSpos : (0 : ℝ) < #S := lt_of_lt_of_le (by positivity) hS
  have hkey : (#S : ℝ) / 2 * (μL * w) ≤ n ^ w * Real.exp (-(μL * w / 8)) * (μL * w) := by
    have : 2 * (#L * (#S * w / (4 * n))) = #S / 2 * (μL * w) := by
      simp only [μL]; field_simp; ring
    nlinarith
  rcases (mul_nonneg (div_nonneg hn.le hn.le |>.trans_eq' rfl |> fun _ =>
    (by positivity : (0 : ℝ) ≤ μL)) hw).eq_or_lt with h0 | hpos
  · have : (#L : ℝ) * w = 0 := by
      have : μL * w = 0 := h0.symm
      simp only [μL] at this
      field_simp at this
      linarith
    rw [this]
    have : 0 ≤ Real.log (2 / μ) := Real.log_nonneg (by rw [le_div_iff₀ hμ0]; linarith)
    positivity
  have h1 : (#S : ℝ) / 2 ≤ n ^ w * Real.exp (-(μL * w / 8)) := le_of_mul_le_mul_right hkey hpos
  have h2 : μ / 2 ≤ Real.exp (-(μL * w / 8)) := by
    have hnw : (0 : ℝ) < n ^ w := by positivity
    rw [← mul_le_mul_iff_of_pos_left hnw]
    nlinarith
  have h3 : μL * w / 8 ≤ Real.log (2 / μ) := by
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_exp, Real.log_div hμ0.ne' (by norm_num)] at this
    rw [Real.log_div (by norm_num) hμ0.ne']
    linarith
  have : (#L : ℝ) * w = n * (μL * w) := by simp only [μL]; field_simp
  rw [this]
  nlinarith

/-- **Error at one input, real form**: if at least `θ > 0` pairs are accepted at `x`, the decoder
errs at `x` on at most `#bad N ^ m / θ + N ^ m exp (-m #U ^ (#P + 1) θ / N)` trial vectors, where
`N` is the number of trials. -/
theorem card_filter_dpDecode_ne_le (C' : (Fin k → U) → Fin k → V) (f : U → V) (dflt : V)
    (P : Finset (Fin k)) (b₀ : Fin k → U) (m : ℕ) (x : U) {θ : ℝ} (hθ : 0 < θ)
    (ha : θ ≤ #(acceptedPairs C' P b₀ x)) :
    (#{v : Fin m → Trial U k | dpDecode C' dflt P b₀ v x ≠ f x} : ℝ) ≤
      #(badPairs C' f P b₀ x) * Fintype.card (Trial U k) ^ m / θ +
        Fintype.card (Trial U k) ^ m *
          Real.exp (-(m * (Fintype.card U ^ (#P + 1) * θ / Fintype.card (Trial U k)))) := by
  classical
  have h := card_filter_dpDecode_ne_mul_le C' f dflt P b₀ m x
  set a := #(acceptedPairs C' P b₀ x)
  set B := #(badPairs C' f P b₀ x)
  set E := #{v : Fin m → Trial U k | dpDecode C' dflt P b₀ v x ≠ f x}
  set N := Fintype.card (Trial U k)
  set c := Fintype.card U ^ (#P + 1)
  have hca : c * a ≤ N := by rw [← card_filter_accepts]; exact card_le_univ _
  have ha0 : (0 : ℝ) < a := hθ.trans_le ha
  have hc0 : (0 : ℝ) < c := by
    have : Nonempty U := ⟨x⟩
    exact_mod_cast pow_pos Fintype.card_pos _
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < c * a := mul_pos hc0 ha0
    exact this.trans_le (by exact_mod_cast hca)
  have hR : (E : ℝ) * a ≤ B * N ^ m + a * ((N : ℝ) - c * a) ^ m := by
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast [hca] at this
    exact this
  have hpow : ((N : ℝ) - c * a) ^ m ≤ N ^ m * Real.exp (-(m * (c * θ / N))) := by
    have hbase : 0 ≤ 1 - c * a / (N : ℝ) := by
      rw [sub_nonneg, div_le_one hN0]
      exact_mod_cast hca
    have heq : (N : ℝ) - c * a = N * (1 - c * a / N) := by field_simp
    have hle : 1 - c * a / (N : ℝ) ≤ Real.exp (-(c * θ / N)) := by
      have h1 := Real.add_one_le_exp (-(c * a / (N : ℝ)))
      have h2 : -(c * a / (N : ℝ)) ≤ -(c * θ / N) := by
        rw [neg_le_neg_iff]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hc0.le) hN0.le
      linarith [Real.exp_le_exp.2 h2]
    rw [heq, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (1 - c * a / (N : ℝ)) ^ m ≤ Real.exp (-(c * θ / N)) ^ m :=
          pow_le_pow_left₀ hbase hle m
      _ = Real.exp (-(m * (c * θ / N))) := by rw [← Real.exp_nat_mul]; ring_nf
  have hE : (E : ℝ) ≤ B * N ^ m / a + N ^ m * Real.exp (-(m * (c * θ / N))) := by
    rw [div_add' _ _ _ ha0.ne', le_div_iff₀ ha0]
    nlinarith
  have hcast : (c : ℝ) = (Fintype.card U : ℝ) ^ (#P + 1) := by simp [c]
  rw [hcast] at hE
  have := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ B * N ^ m) hθ ha
  linarith

end Cslib.Circuits.Boolean.DirectProduct
