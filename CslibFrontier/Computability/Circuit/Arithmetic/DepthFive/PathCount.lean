/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Path
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.WordSum

/-!
# Counting four paths of a given type

The second trace moment of the `IMM_{n,n}` operator is a sum over four paths `P, Q, R, S` whose
edges are paired in every layer: in a layer of type `𝒩` the edges of `P, Q` agree and those of
`R, S` agree, and in a layer of type `𝒟` those of `P, R` agree and those of `Q, S` agree
[OpenAI, §4][OpenAI2026DepthFive]. These conditions constrain the four labels at each vertex
separately, so the four paths of a type word `τ` form a Cartesian product over the vertices.
An internal vertex has `n ^ 2` labellings if its two layers have the same type and `n` otherwise,
and asking in addition that `P` and `R` agree on a layer of type `𝒩` costs a factor `n` at each
end vertex of that layer whose other layer has type `𝒩`.

## Main definitions

* `Cslib.Circuits.DepthFive.Quad`: four paths.
* `Quad.HasType`: the four paths are paired according to a type word.

## Main results

* `sum_quad_le`: the weighted number of four paths of a type word.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 (unrefereed preprint)
-/

@[expose] public section

open Finset

namespace Cslib.Circuits.DepthFive

variable {n : ℕ} [NeZero n]

/-- Four paths `((P, Q), (R, S))`. -/
abbrev Quad (n : ℕ) [NeZero n] := (Path n × Path n) × (Path n × Path n)

/-- The four paths have type `τ`: in a layer of type `𝒩` (`false`) the edges of `P, Q` agree and
those of `R, S` agree; in a layer of type `𝒟` (`true`) those of `P, R` agree and those of `Q, S`
agree. -/
def Quad.HasType (W : Quad n) (τ : Fin n → Bool) : Prop :=
  ∀ t, if τ t then W.1.1.edge t = W.2.1.edge t ∧ W.1.2.edge t = W.2.2.edge t
    else W.1.1.edge t = W.1.2.edge t ∧ W.2.1.edge t = W.2.2.edge t

instance (W : Quad n) (τ : Fin n → Bool) : Decidable (W.HasType τ) := by
  unfold Quad.HasType
  infer_instance

/-- The four labels at a vertex. -/
private abbrev Label (n : ℕ) := (Fin n × Fin n) × (Fin n × Fin n)

/-- The labels of four paths at the vertex `j`. -/
private def Quad.label (W : Quad n) (j : Fin (n + 1)) : Label n :=
  ((W.1.1.1 j, W.1.2.1 j), (W.2.1.1 j, W.2.2.1 j))

private theorem Quad.label_injective : Function.Injective (Quad.label (n := n)) := by
  intro W W' h
  have h' := fun j => congrFun h j
  simp only [Quad.label, Prod.mk.injEq] at h'
  exact Prod.ext
    (Prod.ext (Subtype.ext (funext fun j => (h' j).1.1)) (Subtype.ext (funext fun j => (h' j).1.2)))
    (Prod.ext (Subtype.ext (funext fun j => (h' j).2.1)) (Subtype.ext (funext fun j => (h' j).2.2)))

private theorem edge_eq_iff (P Q : Path n) (t : Fin n) :
    P.edge t = Q.edge t ↔ P.1 t.castSucc = Q.1 t.castSucc ∧ P.1 t.succ = Q.1 t.succ := by
  simp [Path.edge]

/-- The condition of layer `t` on the labels at one of its end vertices: the pairing of the type
of the layer, and equality of the first and third labels if `t` is in `S`. -/
private def LayerOK (τ : Fin n → Bool) (S : Finset (Fin n)) (t : Fin n) (x : Label n) : Prop :=
  (if τ t then x.1.1 = x.2.1 ∧ x.1.2 = x.2.2 else x.1.1 = x.1.2 ∧ x.2.1 = x.2.2) ∧
    (t ∈ S → x.1.1 = x.2.1)

open scoped Classical in
/-- The labels allowed at the vertex `j`. -/
private noncomputable def vset (τ : Fin n → Bool) (S : Finset (Fin n)) (j : Fin (n + 1)) :
    Finset (Label n) :=
  univ.filter fun x => ((j = 0 ∨ j = Fin.last n) → x = ((0, 0), (0, 0))) ∧
    ∀ t : Fin n, (t.castSucc = j ∨ t.succ = j) → LayerOK τ S t x

private theorem Quad.label_mem {W : Quad n} {τ : Fin n → Bool} {S : Finset (Fin n)}
    (h : W.HasType τ) (hS : ∀ t ∈ S, W.1.1.edge t = W.2.1.edge t) (j : Fin (n + 1)) :
    W.label j ∈ vset τ S j := by
  classical
  simp only [vset, mem_filter, mem_univ, true_and]
  refine ⟨?_, fun t ht => ⟨?_, fun htS => ?_⟩⟩
  · rintro (rfl | rfl)
    · simp [Quad.label, W.1.1.2.1, W.1.2.2.1, W.2.1.2.1, W.2.2.2.1]
    · simp [Quad.label, W.1.1.2.2, W.1.2.2.2, W.2.1.2.2, W.2.2.2.2]
  · have := h t
    simp only [edge_eq_iff] at this
    rcases ht with rfl | rfl <;> split_ifs at this ⊢ <;>
      first | exact ⟨this.1.1, this.2.1⟩ | exact ⟨this.1.2, this.2.2⟩
  · have := (edge_eq_iff _ _ _).1 (hS t htS)
    rcases ht with rfl | rfl
    · exact this.1
    · exact this.2

omit [NeZero n] in
/-- Labels determined by one of them are at most `n`. -/
private theorem card_le_of_eq {s : Finset (Label n)}
    (h : ∀ x ∈ s, x.1.1 = x.1.2 ∧ x.1.1 = x.2.1 ∧ x.1.1 = x.2.2) : s.card ≤ n := by
  refine (card_le_card_of_injOn (fun x => x.1.1) (fun _ _ => mem_univ _) ?_).trans
    (by simp)
  intro x hx y hy hxy
  have hx := h x hx
  have hy := h y hy
  dsimp only at hxy
  refine Prod.ext (Prod.ext hxy ?_) (Prod.ext ?_ ?_)
  · rw [← hx.1, ← hy.1, hxy]
  · rw [← hx.2.1, ← hy.2.1, hxy]
  · rw [← hx.2.2, ← hy.2.2, hxy]

omit [NeZero n] in
/-- Labels determined by the first and the last of them are at most `n ^ 2`. -/
private theorem card_le_of_pair {s : Finset (Label n)}
    (h' : (∀ x ∈ s, x.1.1 = x.2.1 ∧ x.1.2 = x.2.2) ∨ ∀ x ∈ s, x.1.1 = x.1.2 ∧ x.2.1 = x.2.2) :
    s.card ≤ n ^ 2 := by
  refine (card_le_card_of_injOn (fun x => (x.1.1, x.2.2)) (fun _ _ => mem_univ _) ?_).trans
    (by simp [sq])
  intro x hx y hy hxy
  simp only [Prod.mk.injEq] at hxy
  rcases h' with h' | h'
  · have hx := h' x hx
    have hy := h' y hy
    refine Prod.ext (Prod.ext hxy.1 ?_) (Prod.ext ?_ hxy.2)
    · rw [hx.2, hy.2, hxy.2]
    · rw [← hx.1, ← hy.1, hxy.1]
  · have hx := h' x hx
    have hy := h' y hy
    refine Prod.ext (Prod.ext hxy.1 ?_) (Prod.ext ?_ hxy.2)
    · rw [← hx.1, ← hy.1, hxy.1]
    · rw [hx.2, hy.2, hxy.2]

open scoped Classical in
/-- The number of labels allowed at the first vertex of layer `j`. -/
private theorem card_vset_castSucc (τ : Fin n → Bool) (S : Finset (Fin n)) (j : Fin n) :
    ((vset τ S j.castSucc).card : ℝ) ≤ (if j = 0 then 1 else (n : ℝ) ^ 2) *
      (if ∃ i : Fin n, (i : ℕ) + 1 = j ∧ τ i ≠ τ j then (n : ℝ)⁻¹ else 1) *
      (if ∃ i : Fin n, (i : ℕ) + 1 = j ∧ τ i = false ∧ τ j = false ∧ (i ∈ S ∨ j ∈ S)
        then (n : ℝ)⁻¹ else 1) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  by_cases hj : j = 0
  · subst hj
    have h0 (q : Fin n → Prop) : ¬ ∃ i : Fin n, (i : ℕ) + 1 = (0 : Fin n) ∧ q i := by
      rintro ⟨i, hi, -⟩
      simp at hi
    rw [ite_eq_left rfl, ite_eq_right (h0 _), ite_eq_right (h0 _), mul_one, mul_one]
    have : vset τ S (Fin.castSucc 0) ⊆ {((0, 0), (0, 0))} := by
      intro x hx
      simp only [vset, mem_filter, mem_univ, true_and] at hx
      exact mem_singleton.2 (hx.1 (Or.inl (by simp)))
    exact_mod_cast (card_le_card this).trans (by simp)
  · have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext (by simpa using h))
    let i : Fin n := ⟨j - 1, by omega⟩
    have hi : (i : ℕ) + 1 = j := by simp only [i]; omega
    have hmem : ∀ x ∈ vset τ S j.castSucc, LayerOK τ S i x ∧ LayerOK τ S j x := by
      intro x hx
      simp only [vset, mem_filter, mem_univ, true_and] at hx
      exact ⟨hx.2 i (Or.inr (Fin.ext (by simp [hi]))), hx.2 j (Or.inl rfl)⟩
    have huniq : ∀ i' : Fin n, (i' : ℕ) + 1 = j → i' = i := fun i' h => Fin.ext (by omega)
    simp only [hj, ↓reduceIte]
    by_cases hsw : ∃ i : Fin n, (i : ℕ) + 1 = j ∧ τ i ≠ τ j
    · have hg : ¬ ∃ i : Fin n, (i : ℕ) + 1 = j ∧ τ i = false ∧ τ j = false ∧
          (i ∈ S ∨ j ∈ S) := by
        rintro ⟨i₁, h₁, h₂, h₃, -⟩
        obtain ⟨i₂, h₄, h₅⟩ := hsw
        rw [huniq i₂ h₄, ← huniq i₁ h₁, h₂, h₃] at h₅
        exact h₅ rfl
      obtain ⟨i', hi', hτ⟩ := hsw
      rw [huniq i' hi'] at hτ
      have : (vset τ S j.castSucc).card ≤ n := card_le_of_eq fun x hx => by
        obtain ⟨⟨h₁, -⟩, ⟨h₂, -⟩⟩ := hmem x hx
        cases hi : τ i <;> cases hj : τ j <;> simp_all
      simp only [show (∃ i : Fin n, (i : ℕ) + 1 = j ∧ τ i ≠ τ j) from ⟨i, hi, hτ⟩, hg,
        ↓reduceIte, mul_one]
      calc ((vset τ S j.castSucc).card : ℝ) ≤ n := by exact_mod_cast this
        _ = (n : ℝ) ^ 2 * (n : ℝ)⁻¹ := by field_simp
    · by_cases hg : ∃ i : Fin n, (i : ℕ) + 1 = j ∧ τ i = false ∧ τ j = false ∧ (i ∈ S ∨ j ∈ S)
      · have : (vset τ S j.castSucc).card ≤ n := card_le_of_eq fun x hx => by
          obtain ⟨⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩⟩ := hmem x hx
          obtain ⟨i', hi', hτi, hτj, hS⟩ := hg
          rw [huniq i' hi'] at hτi hS
          simp only [hτi, hτj, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
          have h₃ : x.1.1 = x.2.1 := hS.elim h₁' h₂'
          exact ⟨h₁.1, h₃, h₃.trans h₁.2⟩
        simp only [hsw, hg, ↓reduceIte, mul_one]
        calc ((vset τ S j.castSucc).card : ℝ) ≤ n := by exact_mod_cast this
          _ = (n : ℝ) ^ 2 * (n : ℝ)⁻¹ := by field_simp
      · have hτ : τ i = τ j := by
          by_contra h
          exact hsw ⟨i, hi, h⟩
        have : (vset τ S j.castSucc).card ≤ n ^ 2 := by
          refine card_le_of_pair ?_
          · cases hτj : τ j
            · refine Or.inr fun x hx => ?_
              have h₂ := (hmem x hx).2.1
              rwa [hτj] at h₂
            · refine Or.inl fun x hx => ?_
              have h₂ := (hmem x hx).2.1
              rwa [hτj] at h₂
        simp only [hsw, hg, ↓reduceIte, mul_one]
        exact_mod_cast this

/-- The neighbours of type `𝒩` of the layers in `S` are counted by the vertices between two
layers of type `𝒩`, one of them in `S`: no vertex is counted twice, because no two layers of `S`
are adjacent. -/
private theorem sum_nbrN_le (p : Params)
    (hadj : ∀ t t' : Fin p.n, (t : ℕ) + 1 = t' → p.isV t → p.isV t' → False)
    (τ : Fin p.n → Bool) {S : Finset (Fin p.n)} (hS : ∀ t ∈ S, p.isV t ∧ τ t = false) :
    ∑ t ∈ S, p.nbrN τ t ≤ (univ.filter fun j : Fin p.n =>
      ∃ i : Fin p.n, (i : ℕ) + 1 = j ∧ τ i = false ∧ τ j = false ∧ (i ∈ S ∨ j ∈ S)).card := by
  simp only [Params.nbrN]
  rw [← card_sigma]
  refine card_le_card_of_injOn (fun z => if (z.2 : ℕ) + 1 = z.1 then z.1 else z.2) ?_ ?_
  · rintro ⟨t, i⟩ h
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_univ, true_and] at h
    obtain ⟨ht, hti, hτ⟩ := h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    split_ifs with h'
    · exact ⟨i, h', hτ, (hS t ht).2, Or.inr ht⟩
    · exact ⟨t, hti.resolve_left h', (hS t ht).2, hτ, Or.inl ht⟩
  · rintro ⟨t, i⟩ h ⟨t', i'⟩ h' heq
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_univ, true_and] at h h'
    obtain ⟨ht, hti, -⟩ := h
    obtain ⟨ht', hti', -⟩ := h'
    dsimp only at heq
    have key : (t : ℕ) = t' ∧ (i : ℕ) = i' := by
      split_ifs at heq with h₁ h₂ h₂
      · have := congrArg Fin.val heq
        omega
      · have := congrArg Fin.val heq
        exact (hadj t' t (by omega) (hS t' ht').1 (hS t ht).1).elim
      · have := congrArg Fin.val heq
        exact (hadj t t' (by omega) (hS t ht).1 (hS t' ht').1).elim
      · have := congrArg Fin.val heq
        omega
    obtain rfl : t = t' := Fin.ext key.1
    obtain rfl : i = i' := Fin.ext key.2
    rfl

/-- The number of four paths of type `τ` in which `P` and `R` agree on the layers in `S`. -/
private theorem card_quad_le (p : Params) [NeZero p.n]
    (hadj : ∀ t t' : Fin p.n, (t : ℕ) + 1 = t' → p.isV t → p.isV t' → False)
    (τ : Fin p.n → Bool) {S : Finset (Fin p.n)} (hS : ∀ t ∈ S, p.isV t ∧ τ t = false) :
    ((univ.filter fun W : Quad p.n =>
        W.HasType τ ∧ ∀ t ∈ S, W.1.1.edge t = W.2.1.edge t).card : ℝ) ≤
      (p.n : ℝ) ^ (2 * (p.n - 1)) * ((p.n : ℝ)⁻¹) ^ p.switches τ *
        ∏ t ∈ S, ((p.n : ℝ)⁻¹) ^ p.nbrN τ t := by
  classical
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast NeZero.one_le
  have hinv : (p.n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hinv0 : (0 : ℝ) ≤ (p.n : ℝ)⁻¹ := by positivity
  have hcard : (univ.filter fun W : Quad p.n =>
      W.HasType τ ∧ ∀ t ∈ S, W.1.1.edge t = W.2.1.edge t).card ≤
        ∏ j, (vset τ S j).card := by
    rw [← Fintype.card_piFinset]
    refine card_le_card_of_injOn Quad.label (fun W hW => ?_) Quad.label_injective.injOn
    have hW := (mem_filter.1 hW).2
    exact Fintype.mem_piFinset.2 (Quad.label_mem hW.1 hW.2)
  have hlast : (vset τ S (Fin.last p.n)).card ≤ 1 := by
    have : vset τ S (Fin.last p.n) ⊆ {((0, 0), (0, 0))} := by
      intro x hx
      simp only [vset, mem_filter, mem_univ, true_and] at hx
      exact mem_singleton.2 (hx.1 (Or.inr trivial))
    exact (card_le_card this).trans (by simp)
  have hzero : (univ.filter fun j : Fin p.n => ¬ j = 0).card = p.n - 1 := by
    rw [filter_ne' univ (0 : Fin p.n), card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin]
  calc ((univ.filter fun W : Quad p.n =>
        W.HasType τ ∧ ∀ t ∈ S, W.1.1.edge t = W.2.1.edge t).card : ℝ)
      ≤ ∏ j : Fin p.n, ((vset τ S j.castSucc).card : ℝ) := by
        refine (Nat.cast_le.2 hcard).trans ?_
        rw [Fin.prod_univ_castSucc, Nat.cast_mul, Nat.cast_prod]
        exact mul_le_of_le_one_right (by positivity) (by exact_mod_cast hlast)
    _ ≤ ∏ j : Fin p.n, ((if j = 0 then 1 else (p.n : ℝ) ^ 2) *
          (if ∃ i : Fin p.n, (i : ℕ) + 1 = j ∧ τ i ≠ τ j then (p.n : ℝ)⁻¹ else 1) *
          (if ∃ i : Fin p.n, (i : ℕ) + 1 = j ∧ τ i = false ∧ τ j = false ∧ (i ∈ S ∨ j ∈ S)
            then (p.n : ℝ)⁻¹ else 1)) :=
        prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun j _ => card_vset_castSucc τ S j
    _ = (p.n : ℝ) ^ (2 * (p.n - 1)) * ((p.n : ℝ)⁻¹) ^ p.switches τ *
          ((p.n : ℝ)⁻¹) ^ (univ.filter fun j : Fin p.n => ∃ i : Fin p.n,
            (i : ℕ) + 1 = j ∧ τ i = false ∧ τ j = false ∧ (i ∈ S ∨ j ∈ S)).card := by
        simp only [prod_mul_distrib, prod_ite, prod_const_one, prod_const, one_mul, mul_one,
          hzero, ← pow_mul, Params.switches]
    _ ≤ _ := by
        rw [prod_pow_eq_pow_sum]
        gcongr ?_ * ?_
        exact pow_le_pow_of_le_one hinv0 hinv (sum_nbrN_le p hadj τ hS)

/-- The weighted number of four paths of type `τ`, where a differentiated layer of type `𝒩` on
which `P` and `R` agree has the weight `1 + x` [OpenAI, §4][OpenAI2026DepthFive]. -/
theorem sum_quad_le (p : Params) [NeZero p.n]
    (hadj : ∀ t t' : Fin p.n, (t : ℕ) + 1 = t' → p.isV t → p.isV t' → False)
    (τ : Fin p.n → Bool) {x : ℝ} (hx : 0 ≤ x) :
    ∑ W : Quad p.n, (if W.HasType τ then
        ∏ t with p.isV t ∧ τ t = false, (1 + x * if W.1.1.edge t = W.2.1.edge t then 1 else 0)
      else 0) ≤
      (p.n : ℝ) ^ (2 * (p.n - 1)) * ((p.n : ℝ)⁻¹) ^ p.switches τ *
        ∏ t with p.isV t ∧ τ t = false, (1 + x * ((p.n : ℝ)⁻¹) ^ p.nbrN τ t) := by
  have hterm (W : Quad p.n) : (if W.HasType τ then
        ∏ t with p.isV t ∧ τ t = false, (1 + x * if W.1.1.edge t = W.2.1.edge t then 1 else 0)
      else 0) = ∑ S ∈ (univ.filter fun t => p.isV t ∧ τ t = false).powerset,
        x ^ S.card * if W.HasType τ ∧ ∀ t ∈ S, W.1.1.edge t = W.2.1.edge t then 1 else 0 := by
    by_cases hW : W.HasType τ
    · simp only [hW, ↓reduceIte, true_and]
      rw [prod_one_add]
      refine sum_congr rfl fun S _ => ?_
      rw [prod_mul_distrib, prod_const, prod_ite_zero, prod_const_one]
      congr
    · simp [hW]
  simp_rw [hterm]
  rw [sum_comm, prod_one_add, mul_sum]
  refine sum_le_sum fun S hS => ?_
  rw [← mul_sum, sum_boole, prod_mul_distrib, prod_const, mul_left_comm]
  gcongr
  exact card_quad_le p hadj τ fun t ht => (mem_filter.1 (mem_powerset.1 hS ht)).2

end Cslib.Circuits.DepthFive
