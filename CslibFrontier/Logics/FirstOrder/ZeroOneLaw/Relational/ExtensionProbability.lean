/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.BernoulliStructure
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational.ExtensionAxiom
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import CslibFrontier.Foundations.Analysis.SpecificLimits.DescFactorial
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Product.Event
import CslibFrontier.Probability.Product.Reindex
import CslibFrontier.Probability.Product.Split
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Extension axioms hold almost surely

Let `L` be a relational language with finitely many relation symbols, and let each relation symbol
`R` have a probability `0 < p R < 1`. Every extension axiom holds in the random `L`-structure
`Cslib.Logic.FO.bernoulliStructure p n` on `Fin n` with probability tending to `1`. For the uniform
random structure, where every `p R` is `1/2`, this is Fagin's lemma [Fagin1976]
[Libkin2004, Chapter 12]; the argument is the same for every `p`.

Fix a tuple `x` of `k` distinct elements and a pattern `s` on the atomic facts that mention the new
element. For each of the `n - k` other elements `z`, those facts with `z` in place of the new
element are distinct atomic facts on `Fin n`, disjoint for distinct `z`. So `z` witnesses `s` with
probability `w = ∏ₐ Pr[atomic fact a has value s a]`, independently of the other elements, and `w`
is positive. A union bound over the `n (n - 1) ⋯ (n - k + 1)` tuples gives
`Pr[the extension axiom for s fails] ≤ n (n - 1) ⋯ (n - k + 1) · (1 - w) ^ (n - k)`,
which tends to `0`.

The independence is `Cslib.Probability.PMF.pi_map_comp_injective`: restricting independent coins
along an injection gives independent coins. In the uniform case `w = 2⁻ᵃ`, where `a` is the number
of atomic facts mentioning the new element.

## Main results

* `Cslib.Logic.FO.Relational.structProb_bernoulliStructure_forall_not_isExtensionWitness`: the exact
  probability `(1 - w) ^ (n - k)` that a fixed tuple has no witness.
* `Cslib.Logic.FO.Relational.structProb_bernoulliStructure_not_hasExtension_le`: the union bound
  above.
* `Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_extensionAxiom`: each extension
  axiom holds with probability tending to `1`.
* `Cslib.Logic.FO.Relational.structProb_forall_not_isExtensionWitness`,
  `Cslib.Logic.FO.Relational.structProb_not_hasExtension_le`,
  `Cslib.Logic.FO.Relational.tendsto_sentenceProb_extensionAxiom`: the uniform case.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure Filter Cslib.Probability
open scoped unitInterval

namespace Cslib.Logic.FO.Relational

universe u v

variable {L : Language.{u, v}}

/-- The atomic fact on `Fin n` obtained from a new atomic fact by reading `0` as `z` and `i + 1`
as `x i`. -/
private def atomEmbed {n k : ℕ} (x : Fin k → Fin n)
    (q : {z : Fin n // z ∉ Set.range x} × NewAtom L k) : Atom L n :=
  ⟨q.2.1.1, (Fin.cons q.1.1 x : Fin (k + 1) → Fin n) ∘ q.2.1.2⟩

private theorem atomEmbed_injective {n k : ℕ} {x : Fin k → Fin n} (hx : Function.Injective x) :
    Function.Injective (atomEmbed (L := L) x) := by
  rintro ⟨⟨z, hz⟩, ⟨⟨R, t⟩, ht⟩⟩ ⟨⟨z', hz'⟩, ⟨⟨R', t'⟩, ht'⟩⟩ h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  have h := eq_of_heq h
  obtain ⟨j, hj⟩ := ht
  change t j = 0 at hj
  obtain rfl : z = z' := by
    have := congrFun h j
    simp only [Function.comp_apply] at this
    rw [hj, Fin.cons_zero] at this
    rcases Fin.eq_zero_or_eq_succ (t' j) with h0 | ⟨i, hi⟩
    · rwa [h0, Fin.cons_zero] at this
    · rw [hi, Fin.cons_succ] at this
      exact absurd ⟨i, this.symm⟩ hz
  obtain rfl : t = t' := funext fun j => (Fin.cons_injective_iff.2 ⟨hz, hx⟩) (congrFun h j)
  rfl

variable [L.IsRelational]

private theorem isExtensionWitness_atomStructure_iff {n k : ℕ} (y : Atom L n → Bool)
    (x : Fin k → Fin n) (s : NewAtom L k → Bool) (z : Fin n) :
    @IsExtensionWitness L (Fin n) (atomStructure y) k x s z ↔
      ∃ hz : z ∉ Set.range x, ∀ a, y (atomEmbed x (⟨z, hz⟩, a)) = s a := by
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun ⟨i, hi⟩ => hne i hi.symm, fun a => Bool.eq_iff_iff.2 (h a)⟩
  · rintro ⟨hz, h⟩
    exact ⟨fun i hi => hz ⟨i, hi.symm⟩, fun a => Bool.eq_iff_iff.1 (h a)⟩

variable [Finite (Σ l, L.Relations l)]

/-- For a fixed tuple `x` of `k` distinct elements, the probability that no element witnesses the
extension of `x` by `s` is `(1 - w) ^ (n - k)`, where `w` is the probability that the atomic facts
mentioning a fresh element take the values `s`. -/
theorem structProb_bernoulliStructure_forall_not_isExtensionWitness
    (p : (Σ l, L.Relations l) → I) {n k : ℕ} (x : Fin k → Fin n) (hx : Function.Injective x)
    (s : NewAtom L k → Bool) :
    structProb (bernoulliStructure p n) (fun S => ∀ z, ¬@IsExtensionWitness L (Fin n) S k x s z) =
      (1 - ∏ᶠ a : NewAtom L k, (PMF.coin (p a.1.1) (s a)).toReal) ^ (n - k) := by
  classical
  have := Fintype.ofFinite (Σ l, L.Relations l)
  have := Fintype.ofFinite (NewAtom L k)
  let O := {z : Fin n // z ∉ Set.range x}
  let e := atomEmbed (L := L) x
  -- The atomic facts at the fresh elements, as a family indexed by `O`.
  let g : (Atom L n → Bool) → O → NewAtom L k → Bool := fun y => Function.curry fun q => y (e q)
  have hev : atomStructure ⁻¹' {S : L.Structure (Fin n) |
      ∀ z, ¬@IsExtensionWitness L (Fin n) S k x s z} =
      g ⁻¹' {u | ∀ z, u z ∈ ({s}ᶜ : Set (NewAtom L k → Bool))} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, isExtensionWitness_atomStructure_iff,
      not_exists, Set.mem_compl_iff, Set.mem_singleton_iff, g, e]
    exact ⟨fun h z hz => h z z.2 fun a => congrFun hz a, fun h z hz ha => h ⟨z, hz⟩ (funext ha)⟩
  -- These families are independent, one for each fresh element.
  have hg : (PMF.pi fun a : Atom L n => PMF.coin (p a.1)).map g =
      PMF.pi fun _ : O => PMF.pi fun a : NewAtom L k => PMF.coin (p a.1.1) := by
    have h1 := PMF.pi_map_comp_injective (fun a : Atom L n => PMF.coin (p a.1))
      (atomEmbed_injective (L := L) hx)
    have h2 := PMF.pi_map_curry (fun q : O × NewAtom L k => PMF.coin (p (e q).1))
    rw [← h1, PMF.map_comp] at h2
    exact h2
  have hO : Fintype.card O = n - k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Set.card_range_of_injective hx,
      Fintype.card_fin]
  have hfactor : ((PMF.pi fun a : NewAtom L k => PMF.coin (p a.1.1)).toOuterMeasure
      ({s}ᶜ : Set (NewAtom L k → Bool))).toReal =
      1 - ∏ᶠ a : NewAtom L k, (PMF.coin (p a.1.1) (s a)).toReal := by
    rw [eq_sub_of_add_eq' (PMF.toOuterMeasure_toReal_add_compl _ {s}),
      PMF.toOuterMeasure_apply_singleton, PMF.pi_apply, ENNReal.toReal_prod,
      finprod_eq_prod_of_fintype]
  rw [structProb_def, bernoulliStructure_eq_map, PMF.toOuterMeasure_map_apply, hev,
    ← PMF.toOuterMeasure_map_apply, hg, PMF.toOuterMeasure_pi_forall, ENNReal.toReal_prod]
  simp only [hfactor, Finset.prod_const, Finset.card_univ, hO]

/-- **Extension axioms fail rarely.** The probability that `bernoulliStructure p n` violates the
extension axiom for `s` is at most `n (n - 1) ⋯ (n - k + 1) · (1 - w) ^ (n - k)`, where `w` is the
probability that the atomic facts mentioning a fresh element take the values `s`. -/
theorem structProb_bernoulliStructure_not_hasExtension_le (p : (Σ l, L.Relations l) → I)
    (n k : ℕ) (s : NewAtom L k → Bool) :
    structProb (bernoulliStructure p n) (fun S => ¬@HasExtension L (Fin n) S k s) ≤
      n.descFactorial k *
        (1 - ∏ᶠ a : NewAtom L k, (PMF.coin (p a.1.1) (s a)).toReal) ^ (n - k) := by
  classical
  calc _ ≤ structProb (bernoulliStructure p n) (fun S =>
          ∃ x ∈ (Finset.univ : Finset (Fin k ↪ Fin n)),
            ∀ z, ¬@IsExtensionWitness L (Fin n) S k x s z) := by
        refine structProb_mono fun S hS => ?_
        simp only [HasExtension, not_forall, not_exists] at hS
        obtain ⟨x, hx, h⟩ := hS
        exact ⟨⟨x, hx⟩, Finset.mem_univ _, h⟩
    _ ≤ ∑ x : Fin k ↪ Fin n, structProb (bernoulliStructure p n)
          (fun S => ∀ z, ¬@IsExtensionWitness L (Fin n) S k x s z) :=
        structProb_exists_le _ _ _
    _ = _ := by
        simp only [fun x : Fin k ↪ Fin n =>
          structProb_bernoulliStructure_forall_not_isExtensionWitness (L := L) p x x.injective s,
          Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
          nsmul_eq_mul]

/-- **Extension axioms hold almost surely** when every relation symbol has a probability strictly
between `0` and `1`. -/
theorem tendsto_sentenceProb_bernoulliStructure_extensionAxiom {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) (k : ℕ) (s : NewAtom L k → Bool) :
    Tendsto (fun n => sentenceProb (bernoulliStructure p n) (extensionAxiom k s)) atTop
      (nhds 1) := by
  have := Fintype.ofFinite (NewAtom L k)
  have hw (a : NewAtom L k) :
      0 < (PMF.coin (p a.1.1) (s a)).toReal ∧ (PMF.coin (p a.1.1) (s a)).toReal ≤ 1 := by
    rw [PMF.coin_apply_toReal]
    split_ifs
    · exact ⟨(hp _).1, (hp _).2.le⟩
    · exact ⟨sub_pos.2 (hp _).2, by linarith [(hp a.1.1).1]⟩
  have hc : 0 < ∏ᶠ a : NewAtom L k, (PMF.coin (p a.1.1) (s a)).toReal := by
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_pos fun a _ => (hw a).1
  have hc1 : ∏ᶠ a : NewAtom L k, (PMF.coin (p a.1.1) (s a)).toReal ≤ 1 := by
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_le_one₀ (fun a _ => (hw a).1.le) fun a _ => (hw a).2
  have h0 : Tendsto
      (fun n => structProb (bernoulliStructure p n) (fun S => ¬@HasExtension L (Fin n) S k s))
      atTop (nhds 0) :=
    squeeze_zero (fun n => structProb_nonneg _ _)
      (fun n => structProb_bernoulliStructure_not_hasExtension_le p n k s)
      (tendsto_descFactorial_mul_pow_sub k (by linarith) (by linarith))
  have := h0.const_sub 1
  simp only [sub_zero, structProb_not, sub_sub_cancel] at this
  refine this.congr fun n => ?_
  rw [sentenceProb_def]
  congr 1 with S : 1
  exact propext (@realize_extensionAxiom L (Fin n) S _ k s).symm

/-- Every sentence of the extension theory holds almost surely in `bernoulliStructure p n` when
`0 < p R < 1` for every relation symbol `R`. -/
theorem tendsto_sentenceProb_bernoulliStructure_of_mem_extensionTheory
    {p : (Σ l, L.Relations l) → I} (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) {φ : L.Sentence}
    (hφ : φ ∈ extensionTheory L) :
    Tendsto (fun n => sentenceProb (bernoulliStructure p n) φ) atTop (nhds 1) := by
  obtain ⟨k, s, rfl⟩ := mem_extensionTheory.1 hφ
  exact tendsto_sentenceProb_bernoulliStructure_extensionAxiom hp k s

/-! ### The uniform random structure -/

omit [L.IsRelational] in
/-- With fair coins, the atomic facts mentioning a fresh element take prescribed values with
probability `2⁻ᵃ`. -/
private theorem finprod_coin_half (k : ℕ) (s : NewAtom L k → Bool) :
    ∏ᶠ a : NewAtom L k, (PMF.coin ⟨1 / 2, by norm_num, by norm_num⟩ (s a)).toReal =
      ((2 : ℝ) ^ Nat.card (NewAtom L k))⁻¹ := by
  have := Fintype.ofFinite (NewAtom L k)
  have h (a : NewAtom L k) :
      (PMF.coin ⟨1 / 2, by norm_num, by norm_num⟩ (s a)).toReal = 2⁻¹ := by
    rw [PMF.coin_apply_toReal]
    split_ifs <;> norm_num
  rw [finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun a _ => h a, Finset.prod_const,
    Finset.card_univ, Nat.card_eq_fintype_card, inv_pow]

/-- For a fixed tuple `x` of `k` distinct elements, the probability that no element witnesses the
extension of `x` by `s` in the uniform random structure is `(1 - 2⁻ᵃ) ^ (n - k)`, where `a` is the
number of atomic facts mentioning the new element. -/
theorem structProb_forall_not_isExtensionWitness {n k : ℕ} (x : Fin k → Fin n)
    (hx : Function.Injective x) (s : NewAtom L k → Bool) :
    structProb (uniformStructure n) (fun S => ∀ z, ¬@IsExtensionWitness L (Fin n) S k x s z) =
      (1 - ((2 : ℝ) ^ Nat.card (NewAtom L k))⁻¹) ^ (n - k) := by
  rw [← bernoulliStructure_const_half,
    structProb_bernoulliStructure_forall_not_isExtensionWitness _ x hx, finprod_coin_half]

/-- **Extension axioms fail rarely.** The probability that the uniform random structure on
`Fin n` violates the extension axiom for `s` is at most
`n (n - 1) ⋯ (n - k + 1) · (1 - 2⁻ᵃ) ^ (n - k)`, where `a` is the number of atomic facts mentioning
the new element [Fagin1976]. -/
theorem structProb_not_hasExtension_le (n k : ℕ) (s : NewAtom L k → Bool) :
    structProb (uniformStructure n) (fun S => ¬@HasExtension L (Fin n) S k s) ≤
      n.descFactorial k * (1 - ((2 : ℝ) ^ Nat.card (NewAtom L k))⁻¹) ^ (n - k) := by
  rw [← bernoulliStructure_const_half, ← finprod_coin_half k s]
  exact structProb_bernoulliStructure_not_hasExtension_le _ n k s

/-- **Extension axioms hold almost surely** [Fagin1976]. -/
theorem tendsto_sentenceProb_extensionAxiom (k : ℕ) (s : NewAtom L k → Bool) :
    Tendsto (fun n => sentenceProb (uniformStructure n) (extensionAxiom k s)) atTop (nhds 1) := by
  simp only [← bernoulliStructure_const_half]
  exact tendsto_sentenceProb_bernoulliStructure_extensionAxiom
    (fun _ => ⟨by norm_num, by norm_num⟩) k s

/-- Every sentence of the extension theory holds almost surely. -/
theorem tendsto_sentenceProb_of_mem_extensionTheory {φ : L.Sentence}
    (hφ : φ ∈ extensionTheory L) :
    Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) := by
  obtain ⟨k, p, rfl⟩ := mem_extensionTheory.1 hφ
  exact tendsto_sentenceProb_extensionAxiom k p

end Cslib.Logic.FO.Relational
