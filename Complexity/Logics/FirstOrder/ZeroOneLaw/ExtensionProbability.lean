/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.ZeroOneLaw.ExtensionAxiom
public import Complexity.Logics.FirstOrder.ZeroOneLaw.RandomGraph
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Complexity.Foundations.Combinatorics.SimpleGraph.SymmDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Extension axioms hold almost surely

Every extension axiom holds in `G(n, 1/2)` with probability tending to `1`
[Fagin1976] [Libkin2004, Section 12.2]. For a fixed tuple `x` of `k` distinct vertices and a fixed
pattern `s`, each of the `n - k` other vertices fails to witness `s` with probability
`1 - 2⁻ᵏ`, independently of the others. A union bound over the `n (n - 1) ⋯ (n - k + 1)`
tuples gives
`Pr[G(n, 1/2) ⊭ EA(k, s)] ≤ n (n - 1) ⋯ (n - k + 1) · (1 - 2⁻ᵏ) ^ (n - k)`,
which tends to `0`.

The independence is proved by counting: toggling the edges between `x` and the vertices outside
it is a bijection between `SimpleGraph V` and the product of the adjacency patterns of the
outside vertices towards `x` with the graphs having no such edges.

## Main results

* `Cslib.Logic.FO.graph.randomGraphProb_not_extensionAxiom_le`: the explicit bound above.
* `Cslib.Logic.FO.graph.tendsto_randomGraphProb_extensionAxiom`: each extension axiom holds with
  probability tending to `1`.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 12.2.
-/

public section

open Function

namespace Cslib.Logic.FO.graph

universe u

variable {V : Type u}

/-- `z` witnesses the extension of `x` by the pattern `s` in the graph `G`. -/
private def IsWitness (G : SimpleGraph V) {k : ℕ} (x : Fin k → V) (s : Fin k → Bool) (z : V) :
    Prop :=
  (∀ i, z ≠ x i) ∧ ∀ i, (G.Adj z (x i) ↔ s i = true)

/-- The vertices outside the tuple `x`. -/
private abbrev Outside {k : ℕ} (x : Fin k ↪ V) := {z : V // z ∉ Set.range x}

/-- The graph whose edges join each outside vertex `z` to those `x i` with `t z i = true`. -/
private def toggle {k : ℕ} (x : Fin k ↪ V) (t : Outside x → Fin k → Bool) : SimpleGraph V :=
  SimpleGraph.fromRel fun a b => ∃ z : Outside x, ∃ i, t z i = true ∧ a = z ∧ b = x i

private theorem toggle_adj {k : ℕ} (x : Fin k ↪ V) (t : Outside x → Fin k → Bool)
    (z : Outside x) (i : Fin k) : (toggle x t).Adj z (x i) ↔ t z i = true := by
  rw [toggle, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨z', i', h, hz, hx⟩ | ⟨z', i', h, hx, hz⟩⟩
    · obtain rfl : z = z' := Subtype.ext hz
      obtain rfl : i = i' := x.injective hx
      exact h
    · exact absurd ⟨i', hz.symm⟩ z.2
  · intro h
    exact ⟨fun he => z.2 ⟨i, he.symm⟩, Or.inl ⟨z, i, h, rfl, rfl⟩⟩

open Classical in
/-- The adjacency pattern of the outside vertices towards `x`. -/
private noncomputable def pattern {k : ℕ} (x : Fin k ↪ V) (G : SimpleGraph V) :
    Outside x → Fin k → Bool :=
  fun z i => decide (G.Adj z (x i))

private theorem pattern_symmDiff_toggle {k : ℕ} (x : Fin k ↪ V) (G : SimpleGraph V)
    (t : Outside x → Fin k → Bool) :
    pattern x (symmDiff G (toggle x t)) = fun z i => xor (pattern x G z i) (t z i) := by
  funext z i
  have h1 := SimpleGraph.symmDiff_adj G (toggle x t) z (x i)
  rw [toggle_adj] at h1
  simp only [pattern]
  cases ht : t z i <;> by_cases h : G.Adj z (x i) <;> simp_all

/-- Toggling the edges between `x` and the outside vertices splits a graph into its pattern
towards `x` and a graph with no edges between `x` and the outside vertices. -/
private noncomputable def decomp {k : ℕ} (x : Fin k ↪ V) :
    SimpleGraph V ≃
      (Outside x → Fin k → Bool) × {H : SimpleGraph V // pattern x H = fun _ _ => false} where
  toFun G := (pattern x G, ⟨symmDiff G (toggle x (pattern x G)), by
    rw [pattern_symmDiff_toggle]; funext z i; exact Bool.xor_self _⟩)
  invFun q := symmDiff q.2.1 (toggle x q.1)
  left_inv G := symmDiff_symmDiff_cancel_right _ _
  right_inv := by
    rintro ⟨p, H, hH⟩
    have hp : pattern x (symmDiff H (toggle x p)) = p := by
      rw [pattern_symmDiff_toggle, hH]; funext z i; exact Bool.false_xor _
    ext1
    · exact hp
    · apply Subtype.ext
      change symmDiff (symmDiff H (toggle x p)) (toggle x (pattern x (symmDiff H (toggle x p))))
        = H
      rw [hp, symmDiff_symmDiff_cancel_right]

private theorem isWitness_iff {k : ℕ} (x : Fin k ↪ V) (G : SimpleGraph V) (s : Fin k → Bool)
    (z : V) : IsWitness G x s z ↔ ∃ h : z ∉ Set.range x, pattern x G ⟨z, h⟩ = s := by
  constructor
  · rintro ⟨hne, hadj⟩
    refine ⟨fun ⟨i, hi⟩ => hne i hi.symm, funext fun i => ?_⟩
    simp only [pattern]
    by_cases h : G.Adj z (x i)
    · simp [h, (hadj i).1 h]
    · cases hs : s i
      · simp [h]
      · exact absurd ((hadj i).2 hs) h
  · rintro ⟨hz, hp⟩
    refine ⟨fun i he => hz ⟨i, he.symm⟩, fun i => ?_⟩
    have := congrFun hp i
    simp only [pattern] at this
    rw [← this]
    simp

/-- Every tuple of `k` distinct vertices has a witness of the extension by `s`. -/
private def HasExtensionG (G : SimpleGraph V) (k : ℕ) (s : Fin k → Bool) : Prop :=
  ∀ x : Fin k → V, Injective x → ∃ z, IsWitness G x s z

variable [Fintype V]

private theorem card_outside [DecidableEq V] {k : ℕ} (x : Fin k ↪ V) :
    Fintype.card (Outside x) = Fintype.card V - k := by
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin]

/-- For a fixed injective tuple `x`, the graphs in which no vertex witnesses `s` are a
`(1 - 2⁻ᵏ) ^ (|V| - k)` fraction of all graphs. -/
private theorem card_noWitness {k : ℕ} (x : Fin k ↪ V) (s : Fin k → Bool) :
    Nat.card {G : SimpleGraph V // ∀ z, ¬IsWitness G x s z} * 2 ^ (k * (Fintype.card V - k)) =
      (2 ^ k - 1) ^ (Fintype.card V - k) * Nat.card (SimpleGraph V) := by
  classical
  let H : Type u := {H : SimpleGraph V // pattern x H = fun _ _ => false}
  let P : Type u := Outside x → Fin k → Bool
  have e0 : {G : SimpleGraph V // ∀ z, ¬IsWitness G x s z} ≃ {q : P × H // ∀ z, q.1 z ≠ s} :=
    (decomp x).subtypeEquiv fun G => by
      simp only [isWitness_iff, not_exists]
      exact ⟨fun h z => h z z.2, fun h z hz => h ⟨z, hz⟩⟩
  have e1 : {G : SimpleGraph V // ∀ z, ¬IsWitness G x s z} ≃ {p : P // ∀ z, p z ≠ s} × H :=
    e0.trans (Equiv.prodSubtypeFstEquivSubtypeProd (α := P) (β := H)
      (p := fun p => ∀ z, p z ≠ s))
  have e2 : {p : Outside x → Fin k → Bool // ∀ z, p z ≠ s} ≃
      (Outside x → {b : Fin k → Bool // b ≠ s}) :=
    Equiv.subtypePiEquivPi (β := fun _ => Fin k → Bool) (p := fun _ b => b ≠ s)
  have hb : Fintype.card {b : Fin k → Bool // b ≠ s} = 2 ^ k - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_unique]
  rw [Nat.card_congr e1, Nat.card_congr (decomp x), Nat.card_prod, Nat.card_prod,
    Nat.card_congr e2, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := Outside x → _),
    Fintype.card_fun, Fintype.card_fun, hb, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, card_outside, ← pow_mul]
  ring

/-- Union bound over the injective tuples. -/
private theorem card_not_hasExtension_mul (k : ℕ) (s : Fin k → Bool) :
    Nat.card {G : SimpleGraph V // ¬HasExtensionG G k s} * 2 ^ (k * (Fintype.card V - k)) ≤
      (Fintype.card V).descFactorial k * ((2 ^ k - 1) ^ (Fintype.card V - k) *
        Nat.card (SimpleGraph V)) := by
  classical
  have hsub : (Finset.univ.filter fun G : SimpleGraph V => ¬HasExtensionG G k s) ⊆
      Finset.univ.biUnion fun x : Fin k ↪ V =>
        Finset.univ.filter fun G : SimpleGraph V => ∀ z, ¬IsWitness G x s z := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasExtensionG, not_forall,
      not_exists] at hG
    obtain ⟨x, hx, h⟩ := hG
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨⟨x, hx⟩, h⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ x : Fin k ↪ V,
      (Finset.univ.filter fun G : SimpleGraph V => ∀ z, ¬IsWitness G x s z).card *
        2 ^ (k * (Fintype.card V - k)) =
      (2 ^ k - 1) ^ (Fintype.card V - k) * Nat.card (SimpleGraph V) := by
    intro x
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_noWitness x s
  calc Nat.card {G : SimpleGraph V // ¬HasExtensionG G k s} * 2 ^ (k * (Fintype.card V - k))
      = (Finset.univ.filter fun G : SimpleGraph V => ¬HasExtensionG G k s).card *
          2 ^ (k * (Fintype.card V - k)) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ (∑ x : Fin k ↪ V,
          (Finset.univ.filter fun G : SimpleGraph V => ∀ z, ¬IsWitness G x s z).card) *
          2 ^ (k * (Fintype.card V - k)) := Nat.mul_le_mul_right _ h1
    _ = ∑ _x : Fin k ↪ V, (2 ^ k - 1) ^ (Fintype.card V - k) * Nat.card (SimpleGraph V) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => h2 x
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
          smul_eq_mul]

private theorem ratio_le (k : ℕ) (s : Fin k → Bool) :
    (Nat.card {G : SimpleGraph V // ¬HasExtensionG G k s} : ℝ) / Nat.card (SimpleGraph V) ≤
      (Fintype.card V).descFactorial k * (1 - (2 ^ k : ℝ)⁻¹) ^ (Fintype.card V - k) := by
  have h := card_not_hasExtension_mul (V := V) k s
  have hN : (0 : ℝ) < Nat.card (SimpleGraph V) := by exact_mod_cast Nat.card_pos
  have h2 : (0 : ℝ) < 2 ^ (k * (Fintype.card V - k)) := by positivity
  rw [div_le_iff₀ hN]
  have hcast : ((Nat.card {G : SimpleGraph V // ¬HasExtensionG G k s} *
      2 ^ (k * (Fintype.card V - k)) : ℕ) : ℝ) ≤
      (((Fintype.card V).descFactorial k * ((2 ^ k - 1) ^ (Fintype.card V - k) *
        Nat.card (SimpleGraph V)) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub Nat.one_le_two_pow] at hcast
  have hq : (1 - (2 ^ k : ℝ)⁻¹) ^ (Fintype.card V - k) * 2 ^ (k * (Fintype.card V - k)) =
      (2 ^ k - 1) ^ (Fintype.card V - k) := by
    rw [pow_mul, ← mul_pow]
    congr 1
    have : (2 ^ k : ℝ) ≠ 0 := by positivity
    field_simp
  refine le_of_mul_le_mul_right ?_ h2
  calc _ ≤ _ := hcast
    _ = _ := by rw [← hq]; ring

/-- **Extension axioms fail rarely.** The probability that `G(n, 1/2)` violates the extension
axiom for a pattern `s : Fin k → Bool` is at most
`n (n - 1) ⋯ (n - k + 1) · (1 - 2⁻ᵏ) ^ (n - k)` [Libkin2004, Section 12.2]. -/
theorem randomGraphProb_not_extensionAxiom_le (n k : ℕ) (s : Fin k → Bool) :
    randomGraphProb n (fun G => ¬Satisfies G (extensionAxiom k s)) ≤
      n.descFactorial k * (1 - (2 ^ k : ℝ)⁻¹) ^ (n - k) := by
  rw [randomGraphProb_eq]
  have h := ratio_le (V := Fin n) k s
  rw [Fintype.card_fin] at h
  calc _ = (Nat.card {G : SimpleGraph (Fin n) // ¬HasExtensionG G k s} : ℝ) /
        Nat.card (SimpleGraph (Fin n)) := by
        congr 2
        exact Nat.card_congr (Equiv.subtypeEquivRight fun G => by
          rw [satisfies_extensionAxiom_iff]
          rfl)
    _ ≤ _ := h

private theorem tendsto_descFactorial_mul_pow (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => (n.descFactorial k : ℝ) * (1 - (2 ^ k : ℝ)⁻¹) ^ (n - k))
      Filter.atTop (nhds 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.descFactorial_zero, Nat.cast_one, pow_zero, inv_one, sub_self, one_mul,
      Nat.sub_zero]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one le_rfl zero_lt_one
  set q : ℝ := 1 - (2 ^ k : ℝ)⁻¹ with hq
  have hq0 : 0 < q := by
    rw [hq, sub_pos]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (one_lt_two : (1 : ℝ) < 2) hk.ne')
  have hq1 : q < 1 := by
    rw [hq, sub_lt_self_iff, inv_pos]
    positivity
  -- `n ^ k q ^ n → 0`, and the descending factorial is at most `n ^ k`.
  have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k
    (abs_lt.2 ⟨by linarith, hq1⟩)).const_mul (q ^ k)⁻¹
  rw [mul_zero] at hlim
  refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0.le _)) ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  calc (n.descFactorial k : ℝ) * q ^ (n - k) ≤ (n : ℝ) ^ k * q ^ (n - k) := by
        gcongr
        exact_mod_cast Nat.descFactorial_le_pow n k
    _ = (q ^ k)⁻¹ * ((n : ℝ) ^ k * q ^ n) := by
        rw [← pow_sub_mul_pow q hn]
        field_simp

/-- **Extension axioms hold almost surely.** For every pattern `s`, the probability that
`G(n, 1/2)` satisfies the extension axiom for `s` tends to `1` [Fagin1976]
[Libkin2004, Section 12.2]. -/
theorem tendsto_randomGraphProb_extensionAxiom (k : ℕ) (s : Fin k → Bool) :
    Filter.Tendsto (fun n => randomGraphProb n (fun G => Satisfies G (extensionAxiom k s)))
      Filter.atTop (nhds 1) := by
  have h0 : Filter.Tendsto
      (fun n => randomGraphProb n (fun G => ¬Satisfies G (extensionAxiom k s)))
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => randomGraphProb_nonneg _ _)
      (fun n => randomGraphProb_not_extensionAxiom_le n k s) (tendsto_descFactorial_mul_pow k)
  have := h0.const_sub 1
  simp only [sub_zero, randomGraphProb_not, sub_sub_cancel] at this
  exact this

end Cslib.Logic.FO.graph
