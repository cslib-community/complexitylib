/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Entropy
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.PMF.Map

/-!
# Mutual information and conditional mutual information

For a joint law of two finite random variables, the mutual information
`I(A; B) = H(A) + H(B) - H(A, B)` (`mutualInfo`) measures how much one reveals about the other, in
bits. For a joint law of three, listed with the conditioning variable first, the conditional
mutual information `I(A; B | C) = H(C, A) + H(C, B) - H(C, A, B) - H(C)` (`condMutualInfo`)
measures the same given `C` [Cover and Thomas, Sections 2.4 and 2.5][CoverThomas2006]. Both are
nonnegative: the first is subadditivity of entropy, the second says conditioning on more
cannot increase entropy.

Random variables are usually functions of an outcome drawn from `ν : PMF Ω`, and the lemmas take
the form `mutualInfo (ν.map fun ω => (A ω, B ω))`. In this form:

* Re-encoding a variable injectively on the support of `ν` changes nothing
  (`entropy_map_eq_of_comp`, `mutualInfo_map_congr`, `condMutualInfo_map_congr`).
* The chain rule splits `I((C, A); B) = I(C; B) + I(A; B | C)`
  (`mutualInfo_map_prodMk_eq_add`). Revealing an observation `B = k ∘ T` splits
  `I(A; T | C) = I(A; B | C) + E_b I(A; T | C, B = b)` (`condMutualInfo_map_eq_add_sum`,
  `mutualInfo_map_eq_add_sum`); conditioning on `B = b` is `conditionalSnd`.
* `I(A; T | C)` vanishes when `T` is determined by `C` (`condMutualInfo_map_eq_zero_of_determined`)
  and when the joint law of `(C, A, B)` factors as `f (c, a) * g (c, b)`
  (`condMutualInfo_eq_zero_of_apply_eq_mul`). Independent components carry no mutual information
  (`mutualInfo_bind_map_prodMk`).

## Main definitions

* `Cslib.Probability.PMF.mutualInfo`: mutual information of a joint law.
* `Cslib.Probability.PMF.condMutualInfo`: conditional mutual information, conditioning variable
  first.

## Main results

* `Cslib.Probability.PMF.mutualInfo_nonneg`, `Cslib.Probability.PMF.condMutualInfo_nonneg`,
  `Cslib.Probability.PMF.mutualInfo_le_entropy_map_snd`,
  `Cslib.Probability.PMF.condMutualInfo_le_conditionalEntropy_fst`,
  `Cslib.Probability.PMF.condMutualInfo_le_conditionalEntropy_snd`: basic bounds.
* `Cslib.Probability.PMF.mutualInfo_map_prodMk_eq_add`,
  `Cslib.Probability.PMF.condMutualInfo_map_eq_add_sum`,
  `Cslib.Probability.PMF.mutualInfo_map_eq_add_sum`: chain rules.
* `Cslib.Probability.PMF.condMutualInfo_map_le_mutualInfo`: `I(A; B | C) ≤ I((C, A); B)`.
* `Cslib.Probability.PMF.condMutualInfo_eq_zero_of_apply_eq_mul`,
  `Cslib.Probability.PMF.condMutualInfo_map_eq_zero_of_determined`,
  `Cslib.Probability.PMF.mutualInfo_bind_map_prodMk`: vanishing criteria;
  `Cslib.Probability.PMF.mutualInfo_eq_zero_iff`: `I(A; B) = 0` exactly for independent pairs.
* `Cslib.Probability.PMF.conditionalSnd_map_prodMk_apply`,
  `Cslib.Probability.PMF.eq_of_mem_support_conditionalSnd_map`: conditioning on an observation.

## Implementation notes

The entropy chain rule `entropy_map_prodMk_eq_add_sum` and the conditioning lemmas
`map_fst_map_prodMk`, `conditionalSnd_map_prodMk_apply` and
`eq_of_mem_support_conditionalSnd_map` do not mention mutual information. They live here because
the chain rules are their only clients so far; they could move to `Probability.Entropy` and
`Probability.Conditioning` when other modules need them.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Sections 2.4
  (mutual information) and 2.5 (chain rules, conditional mutual information).
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β γ δ τ τ' Ω : Type*}

/-- The **mutual information** `I(A; B) = H(A) + H(B) - H(A, B)` of a joint law, in bits. -/
noncomputable def mutualInfo [Finite α] [Finite β] (joint : PMF (α × β)) : ℝ :=
  entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint

/-- The **conditional mutual information** `I(A; B | C) = H(C, A) + H(C, B) - H(C, A, B) - H(C)`
of a joint law of `(C, A, B)`, in bits. -/
noncomputable def condMutualInfo [Finite γ] [Finite α] [Finite β] (joint : PMF (γ × α × β)) : ℝ :=
  entropy (joint.map (Prod.map id Prod.fst)) + entropy (joint.map (Prod.map id Prod.snd)) -
    entropy joint - entropy (joint.map Prod.fst)

theorem mutualInfo_nonneg [Finite α] [Finite β] (joint : PMF (α × β)) :
    0 ≤ mutualInfo joint := by
  have := entropy_le_entropy_map_fst_add_entropy_map_snd joint
  rw [mutualInfo]
  linarith

/-- `I(A; B) = H(B) - H(B | A)`: the mutual information is the entropy of `B` that `A` removes. -/
theorem mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy [Finite α] [Finite β]
    (joint : PMF (α × β)) :
    mutualInfo joint = entropy (joint.map Prod.snd) - conditionalEntropy joint := by
  rw [mutualInfo, conditionalEntropy]
  ring

theorem mutualInfo_le_entropy_map_snd [Finite α] [Finite β] (joint : PMF (α × β)) :
    mutualInfo joint ≤ entropy (joint.map Prod.snd) := by
  have := entropy_map_le joint Prod.fst
  rw [mutualInfo]
  linarith

/-- The mutual information vanishes exactly for independent pairs, whose joint law is the product
of its marginals. -/
theorem mutualInfo_eq_zero_iff [Finite α] [Finite β] (joint : PMF (α × β)) :
    mutualInfo joint = 0 ↔
      joint = (joint.map Prod.fst).bind fun a => (joint.map Prod.snd).map (a, ·) := by
  rw [← entropy_eq_entropy_map_fst_add_entropy_map_snd_iff, mutualInfo]
  constructor <;> intro h <;> linarith

/-- Entropy does not see an injective re-encoding `G = e ∘ F` that holds on the support. -/
theorem entropy_map_eq_of_comp [Finite α] [Finite β] (ν : PMF Ω) {F : Ω → α} {G : Ω → β}
    {e : α → β} (he : Function.Injective e) (h : ∀ ω ∈ ν.support, G ω = e (F ω)) :
    entropy (ν.map G) = entropy (ν.map F) := by
  rw [map_congr_on_support ν G (e ∘ F) h, ← PMF.map_comp]
  exact entropy_map_of_injective _ he

theorem mutualInfo_map [Finite α] [Finite β] (ν : PMF Ω) (A : Ω → α) (B : Ω → β) :
    mutualInfo (ν.map fun ω => (A ω, B ω)) =
      entropy (ν.map A) + entropy (ν.map B) - entropy (ν.map fun ω => (A ω, B ω)) := by
  simp only [mutualInfo, PMF.map_comp]
  rfl

theorem condMutualInfo_map [Finite γ] [Finite α] [Finite β] (ν : PMF Ω) (C : Ω → γ)
    (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      entropy (ν.map fun ω => (C ω, A ω)) + entropy (ν.map fun ω => (C ω, B ω)) -
        entropy (ν.map fun ω => (C ω, A ω, B ω)) - entropy (ν.map C) := by
  simp only [condMutualInfo, PMF.map_comp]
  rfl

/-- Conditional mutual information is nonnegative: conditioning on `A` as well as `C` cannot
increase the entropy of `B`. -/
theorem condMutualInfo_nonneg [Finite γ] [Finite α] [Finite β] (joint : PMF (γ × α × β)) :
    0 ≤ condMutualInfo joint := by
  have h := conditionalEntropy_map_fst_ge
    (joint.map (fun t => ((t.1, t.2.1), t.2.2))) Prod.fst
  have e1 : entropy (joint.map fun t => ((t.1, t.2.1), t.2.2)) = entropy joint :=
    entropy_map_of_injective joint (fun s t h => by
      obtain ⟨c, a, b⟩ := s
      obtain ⟨c', a', b'⟩ := t
      simp only [Prod.mk.injEq] at h
      simp [h])
  simp only [conditionalEntropy, PMF.map_comp, Function.comp_def, e1] at h
  change 0 ≤ entropy (joint.map fun x => (x.1, x.2.1)) + entropy (joint.map fun x => (x.1, x.2.2)) -
    entropy joint - entropy (joint.map fun x => x.1)
  linarith

/-- `I(A; B | C) ≤ H(A | C)`. -/
theorem condMutualInfo_le_conditionalEntropy_fst [Finite γ] [Finite α] [Finite β]
    (joint : PMF (γ × α × β)) :
    condMutualInfo joint ≤ conditionalEntropy (joint.map (Prod.map id Prod.fst)) := by
  have h := entropy_map_le joint (Prod.map id Prod.snd)
  rw [condMutualInfo, conditionalEntropy, PMF.map_comp]
  change _ ≤ _ - entropy (joint.map Prod.fst)
  linarith

/-- `I(A; B | C) ≤ H(B | C)`. -/
theorem condMutualInfo_le_conditionalEntropy_snd [Finite γ] [Finite α] [Finite β]
    (joint : PMF (γ × α × β)) :
    condMutualInfo joint ≤ conditionalEntropy (joint.map (Prod.map id Prod.snd)) := by
  have h := entropy_map_le joint (Prod.map id Prod.fst)
  rw [condMutualInfo, conditionalEntropy, PMF.map_comp]
  change _ ≤ _ - entropy (joint.map Prod.fst)
  linarith

/-- Revealing `B`, the joint entropy of `(B, F)` splits into that of `B` and the average entropy
of `F` given each value of `B`. -/
theorem entropy_map_prodMk_eq_add_sum [Fintype γ] [Finite α] (ν : PMF Ω) (B : Ω → γ)
    (F : Ω → α) :
    entropy (ν.map fun ω => (B ω, F ω)) = entropy (ν.map B) +
      ∑ c, ((ν.map B) c).toReal *
        entropy ((conditionalSnd (ν.map fun ω => (B ω, ω)) c).map F) := by
  have hrec := bind_conditionalSnd (ν.map fun ω => (B ω, ω))
  have hfst : (ν.map fun ω => (B ω, ω)).map Prod.fst = ν.map B := by
    rw [PMF.map_comp]
    rfl
  rw [hfst] at hrec
  have hlaw : (ν.map fun ω => (B ω, F ω)) = (ν.map B).bind
      (fun c => ((conditionalSnd (ν.map fun ω => (B ω, ω)) c).map F).map (c, ·)) := by
    calc (ν.map fun ω => (B ω, F ω)) = (ν.map fun ω => (B ω, ω)).map (Prod.map id F) := by
          rw [PMF.map_comp]
          rfl
      _ = ((ν.map B).bind fun c =>
            (conditionalSnd (ν.map fun ω => (B ω, ω)) c).map (c, ·)).map (Prod.map id F) := by
          rw [hrec]
      _ = _ := by
          simp only [PMF.map_bind, PMF.map_comp]
          rfl
  rw [hlaw]
  exact entropy_bind_pair _ _

private theorem toReal_map_apply_ne_zero (p : PMF α) (F : α → β) {a : α} (ha : p a ≠ 0) :
    ((p.map F) (F a)).toReal ≠ 0 :=
  ENNReal.toReal_ne_zero.mpr ⟨fun h0 => ha (le_antisymm (h0 ▸ le_map_apply p F a) bot_le),
    PMF.apply_ne_top _ _⟩

/-- `I(A; B | C) = 0` when the joint law of `(C, A, B)` factors as `f (c, a) * g (c, b)`: given
`C`, the variables `A` and `B` are independent. -/
theorem condMutualInfo_eq_zero_of_apply_eq_mul [Finite γ] [Finite α] [Finite β]
    (joint : PMF (γ × α × β)) (f : γ → α → ℝ≥0∞) (g : γ → β → ℝ≥0∞)
    (h : ∀ c a b, joint (c, a, b) = f c a * g c b) : condMutualInfo joint = 0 := by
  classical
  let := Fintype.ofFinite γ
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  have hCA (c : γ) (a : α) :
      joint.map (Prod.map id Prod.fst) (c, a) = f c a * ∑' b, g c b := by
    have : joint.map (Prod.map id Prod.fst) =
        (joint.map (Equiv.prodAssoc γ α β).symm).map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    rw [this, map_fst_apply, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun b => ?_
    rw [map_equiv_apply]
    simp [h]
  have hCB (c : γ) (b : β) :
      joint.map (Prod.map id Prod.snd) (c, b) = (∑' a, f c a) * g c b := by
    let e : γ × α × β ≃ (γ × β) × α :=
      ((Equiv.refl γ).prodCongr (Equiv.prodComm α β)).trans (Equiv.prodAssoc γ β α).symm
    have : joint.map (Prod.map id Prod.snd) = (joint.map e).map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    rw [this, map_fst_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [map_equiv_apply]
    simp [e, h]
  have hC (c : γ) : joint.map Prod.fst c = (∑' a, f c a) * ∑' b, g c b := by
    rw [map_fst_apply, tsum_fintype, Fintype.sum_prod_type, tsum_fintype, tsum_fintype,
      Finset.sum_mul_sum]
    simp [h]
  have hid (c : γ) (a : α) (b : β) :
      (joint (c, a, b)).toReal * (joint.map Prod.fst c).toReal =
        (joint.map (Prod.map id Prod.fst) (c, a)).toReal *
          (joint.map (Prod.map id Prod.snd) (c, b)).toReal := by
    rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, h, hC, hCA, hCB]
    congr 1
    ring
  rw [condMutualInfo, entropy_map_eq_sum, entropy_map_eq_sum, entropy_eq_sum_surprisal,
    entropy_map_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun t _ => ?_
  obtain ⟨c, a, b⟩ := t
  by_cases hm : joint (c, a, b) = 0
  · simp [hm]
  have hm' : (joint (c, a, b)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hm, PMF.apply_ne_top _ _⟩
  have h1 := toReal_map_apply_ne_zero joint (Prod.map id Prod.fst) hm
  have h2 := toReal_map_apply_ne_zero joint (Prod.map id Prod.snd) hm
  have h3 := toReal_map_apply_ne_zero joint Prod.fst hm
  simp only [Prod.map_apply, id] at h1 h2 h3 ⊢
  have hlog := congrArg (Real.logb 2) (hid c a b)
  rw [Real.logb_mul hm' h3, Real.logb_mul h1 h2] at hlog
  simp only [surprisal]
  linear_combination (joint (c, a, b)).toReal * hlog

/-- If `T` is determined by `C` on the support, it carries no information about `A` given `C`. -/
theorem condMutualInfo_map_eq_zero_of_determined [Finite γ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (T : Ω → β) (k : γ → β)
    (h : ∀ ω ∈ ν.support, T ω = k (C ω)) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, T ω)) = 0 := by
  rw [condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := C) (e := fun c => (c, k c))
      (fun _ _ he => congrArg Prod.fst he) (fun ω hω => by rw [h ω hω]),
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω)) (e := fun ca => (ca.1, ca.2, k ca.1))
      (fun s t hst => by
        simp only [Prod.mk.injEq] at hst
        exact Prod.ext hst.1 hst.2.1)
      (fun ω hω => by rw [h ω hω])]
  ring

/-- Injective re-encoding of the last variable on the support does not change conditional
mutual information. -/
theorem condMutualInfo_map_congr [Finite γ] [Finite α] [Finite τ] [Finite τ']
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) {T : Ω → τ} {T' : Ω → τ'} {e : τ → τ'}
    (he : Function.Injective e) (h : ∀ ω ∈ ν.support, T' ω = e (T ω)) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, T' ω)) =
      condMutualInfo (ν.map fun ω => (C ω, A ω, T ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, T ω)) (e := Prod.map id e)
      (Function.injective_id.prodMap he) (fun ω hω => by rw [h ω hω]; rfl),
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, T ω)) (e := Prod.map id (Prod.map id e))
      (Function.injective_id.prodMap (Function.injective_id.prodMap he))
      (fun ω hω => by rw [h ω hω]; rfl)]

/-- Injective re-encoding of the second variable on the support does not change mutual
information. -/
theorem mutualInfo_map_congr [Finite α] [Finite τ] [Finite τ']
    (ν : PMF Ω) (A : Ω → α) {T : Ω → τ} {T' : Ω → τ'} {e : τ → τ'}
    (he : Function.Injective e) (h : ∀ ω ∈ ν.support, T' ω = e (T ω)) :
    mutualInfo (ν.map fun ω => (A ω, T' ω)) = mutualInfo (ν.map fun ω => (A ω, T ω)) := by
  rw [mutualInfo_map, mutualInfo_map,
    entropy_map_eq_of_comp ν (F := T) he h,
    entropy_map_eq_of_comp ν (F := fun ω => (A ω, T ω)) (e := Prod.map id e)
      (Function.injective_id.prodMap he) (fun ω hω => by rw [h ω hω]; rfl)]

/-- Swapping the two parts of the first variable does not change mutual information. -/
theorem mutualInfo_map_swap_left [Finite α] [Finite β] [Finite γ] (ν : PMF Ω) (A : Ω → α)
    (B : Ω → β) (T : Ω → γ) :
    mutualInfo (ν.map fun ω => ((B ω, A ω), T ω)) =
      mutualInfo (ν.map fun ω => ((A ω, B ω), T ω)) := by
  rw [mutualInfo_map, mutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => (A ω, B ω)) (G := fun ω => (B ω, A ω))
      (e := Prod.swap) Prod.swap_injective (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => ((A ω, B ω), T ω))
      (G := fun ω => ((B ω, A ω), T ω)) (e := Prod.map Prod.swap id)
      (Prod.swap_injective.prodMap Function.injective_id) (fun _ _ => rfl)]

/-- **Chain rule**: `I((C, A); B) = I(C; B) + I(A; B | C)`. -/
theorem mutualInfo_map_prodMk_eq_add [Finite γ] [Finite α] [Finite β] (ν : PMF Ω)
    (C : Ω → γ) (A : Ω → α) (B : Ω → β) :
    mutualInfo (ν.map fun ω => ((C ω, A ω), B ω)) =
      mutualInfo (ν.map fun ω => (C ω, B ω)) +
        condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  rw [mutualInfo_map, mutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
      (e := fun t => ((t.1, t.2.1), t.2.2))
      (fun s t hst => by
        obtain ⟨c, a, b⟩ := s
        obtain ⟨c', a', b'⟩ := t
        simp only [Prod.mk.injEq] at hst
        simp [hst])
      (fun _ _ => rfl)]
  ring

/-- `I(A; B | C) ≤ I((C, A); B)`. -/
theorem condMutualInfo_map_le_mutualInfo [Finite γ] [Finite α] [Finite β] (ν : PMF Ω)
    (C : Ω → γ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) ≤
      mutualInfo (ν.map fun ω => ((C ω, A ω), B ω)) := by
  rw [mutualInfo_map_prodMk_eq_add]
  have := mutualInfo_nonneg (ν.map fun ω => (C ω, B ω))
  linarith

/-- **Chain rule** through an observation `B = k ∘ T`:
`I(A; T | C) = I(A; B | C) + E_b I(A; T | C, B = b)`. -/
theorem condMutualInfo_map_eq_add_sum [Fintype δ] [Finite γ] [Finite α] [Finite τ]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (T : Ω → τ) (B : Ω → δ) (k : τ → δ)
    (hB : ∀ ω, B ω = k (T ω)) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, T ω)) =
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) +
        ∑ b, ((ν.map B) b).toReal *
          condMutualInfo ((conditionalSnd (ν.map fun ω => (B ω, ω)) b).map
            fun ω => (C ω, A ω, T ω)) := by
  simp only [condMutualInfo_map, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have m1 := entropy_map_prodMk_eq_add_sum ν B (fun ω => (C ω, A ω))
  have m2 := entropy_map_prodMk_eq_add_sum ν B (fun ω => (C ω, T ω))
  have m3 := entropy_map_prodMk_eq_add_sum ν B (fun ω => (C ω, A ω, T ω))
  have m4 := entropy_map_prodMk_eq_add_sum ν B C
  have r1 := entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
    (G := fun ω => (B ω, C ω, A ω)) (e := fun t => (t.2.2, t.1, t.2.1))
    (fun s t hst => by
      obtain ⟨c, a, b⟩ := s
      obtain ⟨c', a', b'⟩ := t
      simp only [Prod.mk.injEq] at hst
      simp [hst]) (fun _ _ => rfl)
  have r2 := entropy_map_eq_of_comp ν (F := fun ω => (C ω, T ω))
    (G := fun ω => (B ω, C ω, T ω)) (e := fun t => (k t.2, t))
    (fun _ _ hst => congrArg Prod.snd hst) (fun ω _ => by rw [hB])
  have r3 := entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, T ω))
    (G := fun ω => (B ω, C ω, A ω, T ω)) (e := fun t => (k t.2.2, t))
    (fun _ _ hst => congrArg Prod.snd hst) (fun ω _ => by rw [hB])
  have r4 := entropy_map_eq_of_comp ν (F := fun ω => (C ω, B ω))
    (G := fun ω => (B ω, C ω)) (e := Prod.swap) Prod.swap_injective (fun _ _ => rfl)
  linarith

/-- **Chain rule** for `I(A; T)` through an observation `B = k ∘ T`:
`I(A; T) = I(A; B) + E_b I(A; T | B = b)`. -/
theorem mutualInfo_map_eq_add_sum [Fintype δ] [Finite α] [Finite τ]
    (ν : PMF Ω) (A : Ω → α) (T : Ω → τ) (B : Ω → δ) (k : τ → δ)
    (hB : ∀ ω, B ω = k (T ω)) :
    mutualInfo (ν.map fun ω => (A ω, T ω)) =
      mutualInfo (ν.map fun ω => (A ω, B ω)) +
        ∑ b, ((ν.map B) b).toReal *
          mutualInfo ((conditionalSnd (ν.map fun ω => (B ω, ω)) b).map
            fun ω => (A ω, T ω)) := by
  simp only [mutualInfo_map, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have m1 := entropy_map_prodMk_eq_add_sum ν B A
  have m2 := entropy_map_prodMk_eq_add_sum ν B T
  have m3 := entropy_map_prodMk_eq_add_sum ν B (fun ω => (A ω, T ω))
  have r2 := entropy_map_eq_of_comp ν (F := T)
    (G := fun ω => (B ω, T ω)) (e := fun t => (k t, t))
    (fun _ _ hst => congrArg Prod.snd hst) (fun ω _ => by rw [hB])
  have r3 := entropy_map_eq_of_comp ν (F := fun ω => (A ω, T ω))
    (G := fun ω => (B ω, A ω, T ω)) (e := fun t => (k t.2, t))
    (fun _ _ hst => congrArg Prod.snd hst) (fun ω _ => by rw [hB])
  have r4 := entropy_map_eq_of_comp ν (F := fun ω => (A ω, B ω))
    (G := fun ω => (B ω, A ω)) (e := Prod.swap) Prod.swap_injective (fun _ _ => rfl)
  linarith

/-- Independent components carry no mutual information. -/
theorem mutualInfo_bind_map_prodMk [Finite α] [Finite β] (p : PMF α) (q : PMF β) :
    mutualInfo (p.bind fun a => q.map (a, ·)) = 0 := by
  have hsnd : (p.bind fun a => q.map (a, ·)).map Prod.snd = q := by
    simp only [PMF.map_bind, PMF.map_comp]
    exact (congrArg p.bind (funext fun _ => PMF.map_id q)).trans (PMF.bind_const p q)
  rw [mutualInfo, map_fst_bind_pair, hsnd, entropy_prod]
  ring

/-! ### Conditioning on an observation -/

theorem map_fst_map_prodMk (ν : PMF Ω) (f : Ω → β) :
    (ν.map fun ω => (f ω, ω)).map Prod.fst = ν.map f := by
  rw [PMF.map_comp]
  rfl

/-- Conditioning on `f = c` keeps only outcomes with `f ω = c`. -/
theorem eq_of_mem_support_conditionalSnd_map (ν : PMF Ω) (f : Ω → β) {c : β}
    (hc : ν.map f c ≠ 0) {ω : Ω}
    (hω : ω ∈ (conditionalSnd (ν.map fun ω => (f ω, ω)) c).support) : f ω = c := by
  have hc' : c ∈ ((ν.map fun ω => (f ω, ω)).map Prod.fst).support := by
    rw [map_fst_map_prodMk]
    exact hc
  rw [mem_support_conditionalSnd_iff _ _ hc', PMF.mem_support_map_iff] at hω
  obtain ⟨ω', -, h⟩ := hω
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  exact h1

/-- Conditioning on `f = c` restricts to `f ω = c` and renormalizes. -/
theorem conditionalSnd_map_prodMk_apply [DecidableEq β] (ν : PMF Ω) (f : Ω → β) {c : β}
    (hc : ν.map f c ≠ 0) (ω : Ω) :
    conditionalSnd (ν.map fun ω => (f ω, ω)) c ω =
      (if f ω = c then ν ω else 0) / ν.map f c := by
  have hc' : c ∈ ((ν.map fun ω => (f ω, ω)).map Prod.fst).support := by
    rw [map_fst_map_prodMk]
    exact hc
  rw [conditionalSnd_apply _ _ hc', map_fst_map_prodMk, PMF.map_apply]
  congr 1
  rw [tsum_eq_single ω]
  · by_cases h : f ω = c
    · simp [h]
    · simp [h, Ne.symm h]
  · intro ω' hω'
    simp [Ne.symm hω']

end Cslib.Probability.PMF
