/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational.ExtensionAxiom
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.UniformStructure
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import CslibFrontier.Foundations.Analysis.SpecificLimits.DescFactorial
import CslibFrontier.Foundations.Data.Fintype.RestrictInjective
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Extension axioms hold almost surely

Let `L` be a relational language with finitely many relation symbols. Every extension axiom holds
in the uniform random `L`-structure on `Fin n` with probability tending to `1` [Fagin1976]
[Libkin2004, Chapter 12]. Fix a tuple `x` of `k` distinct elements and a pattern `p` on the `a`
atomic facts that mention the new element. For each of the `n - k` other elements `z`, those facts
with `z` in place of the new element are `a` distinct atomic facts on `Fin n`, disjoint for
distinct `z`. So each `z` fails to witness `p` with probability `1 - 2⁻ᵃ`, independently of the
others. A union bound over the `n (n - 1) ⋯ (n - k + 1)` tuples gives
`Pr[the extension axiom for p fails] ≤ n (n - 1) ⋯ (n - k + 1) · (1 - 2⁻ᵃ) ^ (n - k)`,
which tends to `0`.

The independence is `Nat.card_subtype_comp_injective_div`: the restriction of a uniformly random
truth table along an injection is uniformly random.

## Main results

* `Cslib.Logic.FO.Relational.structProb_forall_not_isExtensionWitness`: the exact probability
  `(1 - 2⁻ᵃ) ^ (n - k)` that a fixed tuple has no witness.
* `Cslib.Logic.FO.Relational.structProb_not_hasExtension_le`: the union bound above.
* `Cslib.Logic.FO.Relational.tendsto_sentenceProb_extensionAxiom`: each extension axiom holds with
  probability tending to `1`.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure Filter

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
    (x : Fin k → Fin n) (p : NewAtom L k → Bool) (z : Fin n) :
    @IsExtensionWitness L (Fin n) (atomStructure y) k x p z ↔
      ∃ hz : z ∉ Set.range x, ∀ a, y (atomEmbed x (⟨z, hz⟩, a)) = p a := by
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun ⟨i, hi⟩ => hne i hi.symm, fun a => Bool.eq_iff_iff.2 (h a)⟩
  · rintro ⟨hz, h⟩
    exact ⟨fun i hi => hz ⟨i, hi.symm⟩, fun a => Bool.eq_iff_iff.1 (h a)⟩

variable [Finite (Σ l, L.Relations l)]

/-- For a fixed tuple `x` of `k` distinct elements, the probability that no element witnesses the
extension of `x` by `p` is `(1 - 2⁻ᵃ) ^ (n - k)`, where `a` is the number of atomic facts
mentioning the new element. -/
theorem structProb_forall_not_isExtensionWitness {n k : ℕ} (x : Fin k → Fin n)
    (hx : Function.Injective x) (p : NewAtom L k → Bool) :
    structProb (uniformStructure n) (fun S => ∀ z, ¬@IsExtensionWitness L (Fin n) S k x p z) =
      (1 - ((2 : ℝ) ^ Nat.card (NewAtom L k))⁻¹) ^ (n - k) := by
  classical
  rw [structProb_uniformStructure]
  let O := {z : Fin n // z ∉ Set.range x}
  let Q : (O × NewAtom L k → Bool) → Prop := fun h => ∀ z : O, (fun a => h (z, a)) ≠ p
  have hev : ∀ y : Atom L n → Bool,
      (∀ z, ¬@IsExtensionWitness L (Fin n) (atomStructure y) k x p z) ↔
        Q (y ∘ atomEmbed x) := by
    intro y
    simp only [isExtensionWitness_atomStructure_iff, not_exists]
    exact ⟨fun h z hz => h z z.2 fun a => congrFun hz a, fun h z hz ha => h ⟨z, hz⟩ (funext ha)⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hev),
    Nat.card_subtype_comp_injective_div _ (atomEmbed_injective hx) Q]
  have e : {h : O × NewAtom L k → Bool // Q h} ≃ (O → {b : NewAtom L k → Bool // b ≠ p}) :=
    ((Equiv.curry O (NewAtom L k) Bool).subtypeEquiv (q := fun f => ∀ z, f z ≠ p)
      fun h => Iff.rfl).trans (Equiv.subtypePiEquivPi (p := fun _ b => b ≠ p))
  have := Fintype.ofFinite (NewAtom L k)
  have hb : Nat.card {b : NewAtom L k → Bool // b ≠ p} = 2 ^ Nat.card (NewAtom L k) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Fintype.card_fun, Fintype.card_bool, Nat.card_eq_fintype_card]
  have hO : Nat.card O = n - k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Set.card_range_of_injective hx, Fintype.card_fin]
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, hb, hO, Nat.card_prod, hO,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  push_cast [Nat.cast_sub Nat.one_le_two_pow]
  rw [mul_comm (n - k), pow_mul, ← div_pow]
  congr 1
  have : (2 : ℝ) ^ Nat.card (NewAtom L k) ≠ 0 := by positivity
  field_simp

/-- **Extension axioms fail rarely.** The probability that the uniform random structure on
`Fin n` violates the extension axiom for `p` is at most
`n (n - 1) ⋯ (n - k + 1) · (1 - 2⁻ᵃ) ^ (n - k)`, where `a` is the number of atomic facts mentioning
the new element [Fagin1976]. -/
theorem structProb_not_hasExtension_le (n k : ℕ) (p : NewAtom L k → Bool) :
    structProb (uniformStructure n) (fun S => ¬@HasExtension L (Fin n) S k p) ≤
      n.descFactorial k * (1 - ((2 : ℝ) ^ Nat.card (NewAtom L k))⁻¹) ^ (n - k) := by
  classical
  calc _ ≤ structProb (uniformStructure n) (fun S => ∃ x ∈ (Finset.univ : Finset (Fin k ↪ Fin n)),
          ∀ z, ¬@IsExtensionWitness L (Fin n) S k x p z) := by
        refine structProb_mono fun S hS => ?_
        simp only [HasExtension, not_forall, not_exists] at hS
        obtain ⟨x, hx, h⟩ := hS
        exact ⟨⟨x, hx⟩, Finset.mem_univ _, h⟩
    _ ≤ ∑ x : Fin k ↪ Fin n, structProb (uniformStructure n)
          (fun S => ∀ z, ¬@IsExtensionWitness L (Fin n) S k x p z) :=
        structProb_exists_le _ _ _
    _ = _ := by
        simp only [fun x : Fin k ↪ Fin n =>
          structProb_forall_not_isExtensionWitness (L := L) x x.injective p,
          Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
          nsmul_eq_mul]

/-- **Extension axioms hold almost surely** [Fagin1976]. -/
theorem tendsto_sentenceProb_extensionAxiom (k : ℕ) (p : NewAtom L k → Bool) :
    Tendsto (fun n => sentenceProb (uniformStructure n) (extensionAxiom k p)) atTop (nhds 1) := by
  have hq0 : (0 : ℝ) ≤ 1 - ((2 : ℝ) ^ Nat.card (NewAtom L k))⁻¹ :=
    sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))
  have hq1 : 1 - ((2 : ℝ) ^ Nat.card (NewAtom L k))⁻¹ < 1 :=
    sub_lt_self _ (inv_pos.2 (by positivity))
  have h0 : Tendsto
      (fun n => structProb (uniformStructure n) (fun S => ¬@HasExtension L (Fin n) S k p))
      atTop (nhds 0) :=
    squeeze_zero (fun n => structProb_nonneg _ _)
      (fun n => structProb_not_hasExtension_le n k p) (tendsto_descFactorial_mul_pow_sub k hq0 hq1)
  have := h0.const_sub 1
  simp only [sub_zero, structProb_not, sub_sub_cancel] at this
  refine this.congr fun n => ?_
  rw [sentenceProb_def]
  congr 1 with S : 1
  exact propext (@realize_extensionAxiom L (Fin n) S _ k p).symm

/-- Every sentence of the extension theory holds almost surely. -/
theorem tendsto_sentenceProb_of_mem_extensionTheory {φ : L.Sentence}
    (hφ : φ ∈ extensionTheory L) :
    Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) := by
  obtain ⟨k, p, rfl⟩ := mem_extensionTheory.1 hφ
  exact tendsto_sentenceProb_extensionAxiom k p

end Cslib.Logic.FO.Relational
