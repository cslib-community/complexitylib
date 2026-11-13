/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.MutualInformation
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformSubset

/-!
# Conditional mutual information chain rules, data processing, and fiber identities

General finite mutual-information and conditional mutual-information identities in bits
(`Real.logb 2`) complementing `Cslib.Probability.MutualInformation`:

* `Cslib.Probability.PMF.mutualInfo_map_swap`,
  `Cslib.Probability.PMF.mutualInfo_le_entropy_map_fst`:
  symmetry of mutual information and the first-marginal entropy upper bound.
* `Cslib.Probability.PMF.condMutualInfo_map_congr_cond`,
  `Cslib.Probability.PMF.condMutualInfo_map_pair_self`: invariance under injective re-encoding of
  the conditioning variable and appending the conditioning variable to both foreground variables.
* `Cslib.Probability.PMF.condMutualInfo_map_swap`,
  `Cslib.Probability.PMF.condMutualInfo_map_prodMk_left_eq_add`,
  `Cslib.Probability.PMF.condMutualInfo_map_prodMk_right_eq_add`: conditional symmetry and chain
  rules.
* `Cslib.Probability.PMF.condMutualInfo_map_le_of_comp_left`,
  `Cslib.Probability.PMF.condMutualInfo_map_le_of_comp`: conditional deterministic data processing.
* `Cslib.Probability.PMF.condMutualInfo_map_pair_fst_le_of_eq_zero`,
  `Cslib.Probability.PMF.condMutualInfo_map_pair_snd_le_of_eq_zero`: public-message conditioning
  monotonicity.
* `Cslib.Probability.PMF.mutualInfo_bind_pair_indep`: mutual-information invariance under
  independent private coins.
* `Cslib.Probability.PMF.mutualInfo_eq_entropy_map_snd_sub_logb_of_const_fiber`: mutual information
  of a joint law whose conditionals given the first coordinate are uniform over constant-size
  fibers.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {Ω α β γ δ : Type*}

private theorem mutualInfo_eq_entropy_add [Finite α] [Finite β] (p : PMF (α × β)) :
    mutualInfo p = entropy (p.map Prod.fst) + entropy (p.map Prod.snd) - entropy p := by
  have hid : p.map (fun ab : α × β => (ab.1, ab.2)) = p := PMF.map_id p
  simpa only [hid] using mutualInfo_map p Prod.fst Prod.snd

/-- Symmetry of mutual information: `I(B; A) = I(A; B)`. -/
theorem mutualInfo_map_swap [Finite α] [Finite β] (p : PMF (α × β)) :
    mutualInfo (p.map Prod.swap) = mutualInfo p := by
  rw [mutualInfo_eq_entropy_add, mutualInfo_eq_entropy_add,
    entropy_map_of_injective p Prod.swap_injective, PMF.map_comp, PMF.map_comp]
  have h1 : (Prod.fst ∘ (Prod.swap : α × β → β × α)) = Prod.snd := rfl
  have h2 : (Prod.snd ∘ (Prod.swap : α × β → β × α)) = Prod.fst := rfl
  rw [h1, h2]
  ring

/-- Mutual information is at most the entropy of the first marginal: `I(A; B) ≤ H(A)`. -/
theorem mutualInfo_le_entropy_map_fst [Finite α] [Finite β] (p : PMF (α × β)) :
    mutualInfo p ≤ entropy (p.map Prod.fst) := by
  rw [← mutualInfo_map_swap]
  have hsnd : (p.map Prod.swap).map Prod.snd = p.map Prod.fst := by
    rw [PMF.map_comp]
    rfl
  rw [← hsnd]
  exact mutualInfo_le_entropy_map_snd (p.map Prod.swap)

/-- Injective re-encoding of the conditioning variable on the support does not change conditional
mutual information: `I(A; B | e(C)) = I(A; B | C)`. -/
theorem condMutualInfo_map_congr_cond {γ' : Type*} [Finite γ] [Finite γ'] [Finite α] [Finite β]
    (ν : PMF Ω) {C : Ω → γ} {C' : Ω → γ'} (A : Ω → α) (B : Ω → β) {e : γ → γ'}
    (he : Function.Injective e) (h : ∀ ω ∈ ν.support, C' ω = e (C ω)) :
    condMutualInfo (ν.map fun ω => (C' ω, A ω, B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := C) (G := C') he h,
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω)) (G := fun ω => (C' ω, A ω))
      (e := Prod.map e id) (he.prodMap Function.injective_id)
      (fun ω hω => Prod.ext (h ω hω) rfl),
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, B ω)) (G := fun ω => (C' ω, B ω))
      (e := Prod.map e id) (he.prodMap Function.injective_id)
      (fun ω hω => Prod.ext (h ω hω) rfl),
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω)) (G := fun ω => (C' ω, A ω, B ω))
      (e := Prod.map e id) (he.prodMap Function.injective_id)
      (fun ω hω => Prod.ext (h ω hω) rfl)]

/-- Appending the conditioning variable `C` to both foreground variables does not change
conditional mutual information: `I((A, C); (B, C) | C) = I(A; B | C)`. -/
theorem condMutualInfo_map_pair_self [Finite γ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, (A ω, C ω), (B ω, C ω))) =
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω)) (G := fun ω => (C ω, A ω, C ω))
      (e := fun p => (p.1, p.2, p.1))
      (fun _ _ h => Prod.ext (congrArg (fun q : γ × α × γ => q.1) h)
        (congrArg (fun q : γ × α × γ => q.2.1) h))
      (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, B ω)) (G := fun ω => (C ω, B ω, C ω))
      (e := fun p => (p.1, p.2, p.1))
      (fun _ _ h => Prod.ext (congrArg (fun q : γ × β × γ => q.1) h)
        (congrArg (fun q : γ × β × γ => q.2.1) h))
      (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
      (G := fun ω => (C ω, (A ω, C ω), (B ω, C ω)))
      (e := fun p => (p.1, (p.2.1, p.1), (p.2.2, p.1)))
      (fun _ _ h => Prod.ext (congrArg (fun q : γ × (α × γ) × (β × γ) => q.1) h)
        (Prod.ext (congrArg (fun q : γ × (α × γ) × (β × γ) => q.2.1.1) h)
          (congrArg (fun q : γ × (α × γ) × (β × γ) => q.2.2.1) h)))
      (fun _ _ => rfl)]

/-- Symmetry of conditional mutual information in its two foreground variables:
`I(A; B | C) = I(B; A | C)`. -/
theorem condMutualInfo_map_swap [Finite γ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, B ω, A ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
      (G := fun ω => (C ω, B ω, A ω)) (e := Prod.map id Prod.swap)
      (Function.injective_id.prodMap Prod.swap_injective) (fun _ _ => rfl)]
  ring

/-- Chain rule for conditional mutual information in the first foreground variable:
`I((D, A); B | C) = I(D; B | C) + I(A; B | (C, D))`. -/
theorem condMutualInfo_map_prodMk_left_eq_add [Finite γ] [Finite δ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (D : Ω → δ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, (D ω, A ω), B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, D ω, B ω)) +
        condMutualInfo (ν.map fun ω => ((C ω, D ω), A ω, B ω)) := by
  let e1 : (γ × δ) × α ≃ γ × δ × α := Equiv.prodAssoc γ δ α
  let e2 : (γ × δ) × β ≃ γ × δ × β := Equiv.prodAssoc γ δ β
  let e3 : (γ × δ) × (α × β) ≃ γ × (δ × α) × β :=
    (Equiv.prodAssoc (γ × δ) α β).symm.trans
      (((Equiv.prodAssoc γ δ α).prodCongr (Equiv.refl β)).trans
        (Equiv.prodAssoc γ (δ × α) β))
  rw [condMutualInfo_map, condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), A ω))
      (G := fun ω => (C ω, D ω, A ω)) (e := e1) e1.injective (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), B ω))
      (G := fun ω => (C ω, D ω, B ω)) (e := e2) e2.injective (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), A ω, B ω))
      (G := fun ω => (C ω, (D ω, A ω), B ω)) (e := e3) e3.injective (fun _ _ => rfl)]
  ring

/-- Chain rule for conditional mutual information in the second foreground variable:
`I(A; (D, B) | C) = I(A; D | C) + I(A; B | (C, D))`. -/
theorem condMutualInfo_map_prodMk_right_eq_add [Finite γ] [Finite α] [Finite δ] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (D : Ω → δ) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, (D ω, B ω))) =
      condMutualInfo (ν.map fun ω => (C ω, A ω, D ω)) +
        condMutualInfo (ν.map fun ω => ((C ω, D ω), A ω, B ω)) := by
  rw [condMutualInfo_map_swap ν C A (fun ω => (D ω, B ω)),
    condMutualInfo_map_prodMk_left_eq_add ν C D B A,
    condMutualInfo_map_swap ν C D A,
    condMutualInfo_map_swap ν (fun ω => (C ω, D ω)) B A]

/-- Conditional mutual information decreases when replacing the first foreground variable by a
function determined on the support: `I(S; B | C) ≤ I(A; B | C)`. -/
theorem condMutualInfo_map_le_of_comp_left {α' : Type*}
    [Finite γ] [Finite α] [Finite α'] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (S : Ω → α') (B : Ω → β)
    (f : α → α') (hf : ∀ ω ∈ ν.support, S ω = f (A ω)) :
    condMutualInfo (ν.map fun ω => (C ω, S ω, B ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  have hinj : Function.Injective (fun a : α => (f a, a)) := fun _ _ h => congrArg Prod.snd h
  have h1 : condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, (S ω, A ω), B ω)) := by
    rw [condMutualInfo_map, condMutualInfo_map,
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω)) (G := fun ω => (C ω, (S ω, A ω)))
        (e := Prod.map id fun a => (f a, a)) (Function.injective_id.prodMap hinj)
        (fun ω hω => Prod.ext rfl (Prod.ext (hf ω hω) rfl)),
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
        (G := fun ω => (C ω, (S ω, A ω), B ω))
        (e := Prod.map id (Prod.map (fun a => (f a, a)) id))
        (Function.injective_id.prodMap (hinj.prodMap Function.injective_id))
        (fun ω hω => Prod.ext rfl (Prod.ext (Prod.ext (hf ω hω) rfl) rfl))]
  rw [h1, condMutualInfo_map_prodMk_left_eq_add]
  have := condMutualInfo_nonneg (ν.map fun ω => ((C ω, S ω), A ω, B ω))
  linarith

/-- Conditional data processing for deterministic maps on both foreground variables:
if `S` is determined by `A` and `R` is determined by `B` on the support of `ν`, then
`I(S; R | C) ≤ I(A; B | C)`. -/
theorem condMutualInfo_map_le_of_comp {α' β' : Type*}
    [Finite γ] [Finite α] [Finite α'] [Finite β] [Finite β']
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (S : Ω → α') (B : Ω → β) (R : Ω → β')
    (f : α → α') (hf : ∀ ω ∈ ν.support, S ω = f (A ω))
    (g : β → β') (hg : ∀ ω ∈ ν.support, R ω = g (B ω)) :
    condMutualInfo (ν.map fun ω => (C ω, S ω, R ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  calc condMutualInfo (ν.map fun ω => (C ω, S ω, R ω))
      ≤ condMutualInfo (ν.map fun ω => (C ω, A ω, R ω)) :=
        condMutualInfo_map_le_of_comp_left ν C A S R f hf
    _ = condMutualInfo (ν.map fun ω => (C ω, R ω, A ω)) :=
        condMutualInfo_map_swap ν C A R
    _ ≤ condMutualInfo (ν.map fun ω => (C ω, B ω, A ω)) :=
        condMutualInfo_map_le_of_comp_left ν C B R A g hg
    _ = condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) :=
        condMutualInfo_map_swap ν C B A

/-- Conditioning on a message `M` that carries no conditional mutual information with `B` given
`(C, A)` cannot increase `I(A; B | C)`. -/
theorem condMutualInfo_map_pair_fst_le_of_eq_zero [Finite γ] [Finite δ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (M : Ω → δ) (A : Ω → α) (B : Ω → β)
    (h : condMutualInfo (ν.map fun ω => ((C ω, A ω), M ω, B ω)) = 0) :
    condMutualInfo (ν.map fun ω => ((C ω, M ω), A ω, B ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  have h1 := condMutualInfo_map_prodMk_left_eq_add ν C M A B
  have h2 := condMutualInfo_map_prodMk_left_eq_add ν C A M B
  have hswap : condMutualInfo (ν.map fun ω => (C ω, (M ω, A ω), B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, (A ω, M ω), B ω)) := by
    rw [condMutualInfo_map, condMutualInfo_map,
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, (A ω, M ω)))
        (G := fun ω => (C ω, (M ω, A ω))) (e := Prod.map id Prod.swap)
        (Function.injective_id.prodMap Prod.swap_injective) (fun _ _ => rfl),
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, (A ω, M ω), B ω))
        (G := fun ω => (C ω, (M ω, A ω), B ω)) (e := Prod.map id (Prod.map Prod.swap id))
        (Function.injective_id.prodMap (Prod.swap_injective.prodMap Function.injective_id))
        (fun _ _ => rfl)]
  have hnonneg := condMutualInfo_nonneg (ν.map fun ω => (C ω, M ω, B ω))
  linarith

/-- Symmetric form: conditioning on a message `M` that carries no conditional mutual information
with `A` given `(C, B)` cannot increase `I(A; B | C)`. -/
theorem condMutualInfo_map_pair_snd_le_of_eq_zero [Finite γ] [Finite δ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (M : Ω → δ) (A : Ω → α) (B : Ω → β)
    (h : condMutualInfo (ν.map fun ω => ((C ω, B ω), M ω, A ω)) = 0) :
    condMutualInfo (ν.map fun ω => ((C ω, M ω), A ω, B ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  rw [condMutualInfo_map_swap ν (fun ω => (C ω, M ω)) A B,
    condMutualInfo_map_swap ν C A B]
  exact condMutualInfo_map_pair_fst_le_of_eq_zero ν C M B A h

/-- Independent private randomness does not change mutual information:
`I((A, R₀); (B, R₁)) = I(A; B)`. -/
theorem mutualInfo_bind_pair_indep [Finite α] [Finite β] [Finite γ] [Finite δ]
    (source : PMF (α × β)) (c₀ : PMF γ) (c₁ : PMF δ) :
    mutualInfo (source.bind fun ab => c₀.bind fun r₀ => c₁.map fun r₁ =>
      ((ab.1, r₀), (ab.2, r₁))) = mutualInfo source := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  let joint := source.bind fun ab => c₀.bind fun r₀ => c₁.map fun r₁ => ((ab.1, r₀), (ab.2, r₁))
  have hfst : joint.map Prod.fst =
      (source.map Prod.fst).bind fun a => c₀.map (a, ·) := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    calc source.bind (fun ab => c₀.bind fun r₀ => c₁.map (Function.const δ (ab.1, r₀)))
        = source.bind (fun ab => c₀.map (ab.1, ·)) := by
          congr 1 with ab : 1
          simp only [PMF.map_const]
          rfl
      _ = (source.map Prod.fst).bind fun a => c₀.map (a, ·) := by
          rw [PMF.bind_map]
          rfl
  have hsnd : joint.map Prod.snd =
      (source.map Prod.snd).bind fun b => c₁.map (b, ·) := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    calc source.bind (fun ab => c₀.bind (fun _ => c₁.map (ab.2, ·)))
        = source.bind (fun ab => c₁.map (ab.2, ·)) := by
          congr 1 with ab : 1
          exact PMF.bind_const c₀ _
      _ = (source.map Prod.snd).bind fun b => c₁.map (b, ·) := by
          rw [PMF.bind_map]
          rfl
  have hjoint : entropy joint = entropy source + entropy c₀ + entropy c₁ := by
    let e : (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) := Equiv.prodProdProdComm α β γ δ
    have heq : joint = (source.bind fun ab => (c₀.bind fun r₀ => c₁.map (r₀, ·)).map (ab, ·)).map
        e := by
      simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def, e]
      rfl
    rw [heq, entropy_map_of_injective _ e.injective, entropy_bind_pair]
    simp only [← Finset.sum_mul, sum_toReal, one_mul, entropy_prod]
    ring
  rw [mutualInfo_eq_entropy_add joint, mutualInfo_eq_entropy_add source, hfst, hsnd,
    entropy_prod, entropy_prod, hjoint]
  ring

/-- Mutual information of a joint law `p : PMF (α × β)` whose conditionals given each supported
first coordinate `a` are uniform over a `c`-element subset `unseen a : Finset β`:
`I(A; B) = H(B) - log₂ c`. -/
theorem mutualInfo_eq_entropy_map_snd_sub_logb_of_const_fiber [Finite α] [Finite β]
    (p : PMF (α × β)) (unseen : α → Finset β) (c : ℕ) (hc : 0 < c)
    (hcard : ∀ a ∈ (p.map Prod.fst).support, (unseen a).card = c)
    (hzero : ∀ a ∈ (p.map Prod.fst).support, ∀ b ∉ unseen a, p (a, b) = 0)
    (hconst : ∀ a ∈ (p.map Prod.fst).support,
      ∀ b₀ ∈ unseen a, ∀ b₁ ∈ unseen a, p (a, b₁) = p (a, b₀)) :
    mutualInfo p = entropy (p.map Prod.snd) - Real.logb 2 c := by
  classical
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  have hcond_supp : ∀ a ∈ (p.map Prod.fst).support,
      entropy (conditionalSnd p a) = Real.logb 2 c := by
    intro a ha
    have hca : (unseen a).card = c := hcard a ha
    have hne : (unseen a).Nonempty := Finset.card_pos.mp (hca ▸ hc)
    let val : ℝ≥0∞ := conditionalSnd p a hne.choose
    have hcond_eq : conditionalSnd p a = PMF.uniformOfFinset (unseen a) hne := by
      refine pmf_eq_uniformOfFinset_of_ite_const hne (c := val) fun b => ?_
      by_cases hb : b ∈ unseen a
      · simp only [hb, ↓reduceIte, val, conditionalSnd_apply p a ha]
        rw [hconst a ha hne.choose hne.choose_spec b hb]
      · simp only [hb, ↓reduceIte, conditionalSnd_apply p a ha, hzero a ha b hb, ENNReal.zero_div]
    rw [hcond_eq, entropy_uniformOfFinset (unseen a) hne, hca]
  have hcond : conditionalEntropy p = Real.logb 2 c := by
    rw [conditionalEntropy_eq_sum]
    have hterm : ∀ a : α, ((p.map Prod.fst) a).toReal * entropy (conditionalSnd p a) =
        ((p.map Prod.fst) a).toReal * Real.logb 2 c := by
      intro a
      by_cases ha : a ∈ (p.map Prod.fst).support
      · rw [hcond_supp a ha]
      · have h0 : (p.map Prod.fst) a = 0 := by
          by_contra hne0
          exact ha hne0
        rw [h0, ENNReal.toReal_zero, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_mul, sum_toReal, one_mul]
  rw [mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy, hcond]

end Cslib.Probability.PMF
