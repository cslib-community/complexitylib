/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Correlation
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

/-!
# Exponential extension-complexity lower bound for stable set polytopes

The **stable set polytope** `stabPolytope K G` (`STAB(G)`) of a finite simple graph `G` on `V` is
the convex hull of the characteristic vectors of all independent sets of `G`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.3].

Following [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 8 and Theorem 10], for each `n` we
construct the `2 n²`-vertex gadget graph `corrGadgetGraph n` (`H_n`), whose maximum-cardinality
stable sets (`|S| = n + n (n - 1) / 2`) pick one vertex from each vertex-pair clique and one from
each edge-quadruple clique, and project linearly onto `corrPolytope K (Fin n)`. Padding with
isolated vertices to any `m ≥ 2` using `p = ⌊√(m / 2)⌋` produces a graph `stabHardGraph m` on
`Fin m` with `extensionComplexity (stabPolytope K (stabHardGraph m)) ≥ (3 / 2) ^ ⌊√(m / 2)⌋`.

## Main definitions

* `stabVertex`, `stabPolytope`: the stable set polytope `STAB(G)` of a finite simple graph `G`.
* `CorrPairIdx`, `CorrGadgetV`, `corrGadgetGraph`: the `2 n²`-vertex gadget graph `H_n`.
* `stabHardGraph`: the `m`-vertex graph on `Fin m` embedding `corrGadgetGraph ⌊√(m / 2)⌋`.

## Main results

* `extensionComplexity_corrPolytope_le_corrGadgetGraph`:
  `xc (corrPolytope K (Fin n)) ≤ xc (stabPolytope K (corrGadgetGraph n))`.
* `three_pow_le_two_pow_mul_extensionComplexity_stabPolytope`:
  for `m ≥ 2` and `p = Nat.sqrt (m / 2)`,
  `3 ^ p ≤ 2 ^ p * extensionComplexity (stabPolytope K (stabHardGraph m))`.
* `HasExtendedFormulation.three_div_two_pow_le_of_stabPolytope`: for `m ≥ 2` and
  `HasExtendedFormulation (stabPolytope K (stabHardGraph m)) r`, `(3 / 2 : F) ^ ⌊√(m / 2)⌋ ≤ r`.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.3 (Lemmas 8–9 and Theorem 10).
* [KaibelWeltge2015], Section 2 (Theorem 1).
-/

public section

section Defs

variable (K : Type*) [Semiring K] [PartialOrder K]

/-- Characteristic vector of a subset `S : Finset V` in `V → K`. -/
@[expose] def stabVertex {V : Type*} [DecidableEq V] (S : Finset V) : V → K :=
  fun v => if v ∈ S then 1 else 0

/-- The **stable set polytope** `STAB(G)` of a simple graph `G` on `V`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.3]. -/
@[expose] def stabPolytope {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (V → K) :=
  convexHull K (Set.range fun S : {S : Finset V // G.IsIndepSet (S : Set V)} =>
    stabVertex K S.1)

end Defs

section Gadget

/-- Ordered pairs `(fst, snd)` in `Fin n` with `fst < snd`. -/
structure CorrPairIdx (n : ℕ) where
  /-- Smaller vertex index in `Fin n`. -/
  fst : Fin n
  /-- Larger vertex index in `Fin n`. -/
  snd : Fin n
  /-- Ordering witness `fst < snd`. -/
  lt : fst < snd
  deriving DecidableEq

private def corrPairIdxEquivSubtype (n : ℕ) :
    CorrPairIdx n ≃ {p : Fin n × Fin n // p.1 < p.2} where
  toFun e := ⟨(e.fst, e.snd), e.lt⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[no_expose] instance (n : ℕ) : Fintype (CorrPairIdx n) :=
  Fintype.ofEquiv _ (corrPairIdxEquivSubtype n).symm

/-- Vertices of the FMPTW stable-set gadget graph `H_n`
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 8]: two vertices per node of `K_n` and four per
edge of `K_n`. -/
inductive CorrGadgetV (n : ℕ) : Type
  | vertex (i : Fin n) (val : Bool)
  | edge (e : CorrPairIdx n) (val₁ val₂ : Bool)
  deriving DecidableEq

private def corrGadgetVEquivSum (n : ℕ) :
    CorrGadgetV n ≃ (Fin n × Bool) ⊕ (CorrPairIdx n × Bool × Bool) where
  toFun
    | .vertex i b => Sum.inl (i, b)
    | .edge e b₁ b₂ => Sum.inr (e, b₁, b₂)
  invFun
    | Sum.inl (i, b) => .vertex i b
    | Sum.inr (e, b₁, b₂) => .edge e b₁ b₂
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, b⟩ | ⟨e, b₁, b₂⟩ <;> rfl

@[no_expose] instance (n : ℕ) : Fintype (CorrGadgetV n) :=
  Fintype.ofEquiv _ (corrGadgetVEquivSum n).symm

private def corrPairSuccEquiv (n : ℕ) : CorrPairIdx (n + 1) ≃ CorrPairIdx n ⊕ Fin n where
  toFun e :=
    if h : e.snd = Fin.last n then
      Sum.inr ⟨e.fst.1, by have := e.lt; rw [h] at this; exact this⟩
    else
      Sum.inl ⟨e.fst.castPred (Fin.ne_last_of_lt (lt_of_lt_of_le e.lt (Fin.le_last _))),
        e.snd.castPred h, by
          simpa only [Fin.lt_def, Fin.coe_castPred] using e.lt⟩
  invFun
    | Sum.inl e => ⟨e.fst.castSucc, e.snd.castSucc, by
        simpa only [Fin.lt_def, Fin.val_castSucc] using e.lt⟩
    | Sum.inr i => ⟨i.castSucc, Fin.last n, Fin.castSucc_lt_last i⟩
  left_inv e := by
    dsimp only
    split_ifs with h
    · obtain ⟨f, s, lt⟩ := e
      dsimp only at h
      subst h
      simp only [Fin.castSucc_mk, Fin.eta]
    · cases e with
      | mk f s lt =>
          simp only [Fin.castSucc_castPred]
  right_inv x := by
    rcases x with e | i
    · dsimp only
      have hs : e.snd.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last e.snd).ne
      simp only [hs, ↓reduceDIte, Fin.castPred_castSucc]
    · simp only [↓reduceDIte, Fin.val_castSucc, Fin.eta]

/-- Exact vertex count `|V(H_n)| = 2 n²` [FioriniMassarPokuttaTiwaryDeWolf2015, §3.3]. -/
theorem card_corrGadgetV (n : ℕ) : Fintype.card (CorrGadgetV n) = 2 * n ^ 2 := by
  have hpair : ∀ k, 2 * k + 4 * Fintype.card (CorrPairIdx k) = 2 * k ^ 2 := by
    intro k
    induction k with
    | zero =>
        have h0 : Fintype.card (CorrPairIdx 0) = 0 :=
          Fintype.card_eq_zero_iff.2 ⟨fun e => Fin.elim0 e.fst⟩
        simp only [h0, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]
    | succ k ih =>
        have hcard : Fintype.card (CorrPairIdx (k + 1)) = Fintype.card (CorrPairIdx k) + k := by
          rw [Fintype.card_congr (corrPairSuccEquiv k), Fintype.card_sum, Fintype.card_fin]
        rw [hcard]
        nlinarith
  rw [Fintype.card_congr (corrGadgetVEquivSum n), Fintype.card_sum, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  linarith [hpair n]

private def corrGadgetAdjRel {n : ℕ} : CorrGadgetV n → CorrGadgetV n → Prop
  | .vertex i b₁, .vertex j b₂ => i = j ∧ b₁ ≠ b₂
  | .edge e₁ c₁ d₁, .edge e₂ c₂ d₂ => e₁ = e₂ ∧ (c₁ ≠ c₂ ∨ d₁ ≠ d₂)
  | .vertex i b, .edge e c₁ c₂ => (i = e.fst ∧ b ≠ c₁) ∨ (i = e.snd ∧ b ≠ c₂)
  | .edge e c₁ c₂, .vertex i b => (i = e.fst ∧ b ≠ c₁) ∨ (i = e.snd ∧ b ≠ c₂)

/-- The FMPTW stable-set gadget graph `H_n` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 8]. -/
def corrGadgetGraph (n : ℕ) : SimpleGraph (CorrGadgetV n) where
  Adj := corrGadgetAdjRel
  symm := ⟨fun u v h => by cases u <;> cases v <;> simp only [corrGadgetAdjRel] at h ⊢ <;> tauto⟩
  loopless := ⟨fun u h => by cases u <;> simp only [corrGadgetAdjRel] at h <;> tauto⟩

private def gadgetBlock {n : ℕ} : CorrGadgetV n → Fin n ⊕ CorrPairIdx n
  | .vertex i _ => Sum.inl i
  | .edge e _ _ => Sum.inr e

private theorem adj_of_gadgetBlock_eq {n : ℕ} {u v : CorrGadgetV n} (hne : u ≠ v)
    (heq : gadgetBlock u = gadgetBlock v) : (corrGadgetGraph n).Adj u v := by
  cases u <;> cases v <;> simp only [gadgetBlock, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at heq
  · subst heq
    refine ⟨rfl, fun h => hne (by rw [h])⟩
  · subst heq
    refine ⟨rfl, ?_⟩
    by_contra! h
    exact hne (by rw [h.1, h.2])

private theorem card_le_of_isIndepSet_corrGadgetGraph {n : ℕ} {S : Finset (CorrGadgetV n)}
    (hS : (corrGadgetGraph n).IsIndepSet (S : Set (CorrGadgetV n))) :
    S.card ≤ n + Fintype.card (CorrPairIdx n) := by
  have hinj : Set.InjOn gadgetBlock (S : Set (CorrGadgetV n)) := fun u hu v hv heq => by
    by_contra hne
    exact hS hu hv hne (adj_of_gadgetBlock_eq hne heq)
  calc
    S.card = (S.image gadgetBlock).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin n ⊕ CorrPairIdx n) := Finset.card_le_univ _
    _ = n + Fintype.card (CorrPairIdx n) := by rw [Fintype.card_sum, Fintype.card_fin]

private def liftCorrIndep {n : ℕ} (b : Finset (Fin n)) : Finset (CorrGadgetV n) :=
  (Finset.univ.image fun i => CorrGadgetV.vertex i (decide (i ∈ b))) ∪
    Finset.univ.image fun e : CorrPairIdx n =>
      CorrGadgetV.edge e (decide (e.fst ∈ b)) (decide (e.snd ∈ b))

private theorem isIndepSet_liftCorrIndep {n : ℕ} (b : Finset (Fin n)) :
    (corrGadgetGraph n).IsIndepSet (liftCorrIndep b : Set (CorrGadgetV n)) := by
  intro u hu v hv hne hadj
  simp only [Finset.mem_coe, liftCorrIndep, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hu hv
  rcases hu with ⟨i, rfl⟩ | ⟨e₁, rfl⟩ <;> rcases hv with ⟨j, rfl⟩ | ⟨e₂, rfl⟩
  · simp only [corrGadgetGraph, corrGadgetAdjRel] at hadj
    obtain ⟨h1, h2⟩ := hadj
    subst h1
    exact h2 rfl
  · simp only [corrGadgetGraph, corrGadgetAdjRel] at hadj
    rcases hadj with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;> exact hb rfl
  · simp only [corrGadgetGraph, corrGadgetAdjRel] at hadj
    rcases hadj with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;> exact hb rfl
  · simp only [corrGadgetGraph, corrGadgetAdjRel] at hadj
    obtain ⟨h1, h2⟩ := hadj
    subst h1
    rcases h2 with h | h <;> exact h rfl

private theorem card_liftCorrIndep {n : ℕ} (b : Finset (Fin n)) :
    (liftCorrIndep b).card = n + Fintype.card (CorrPairIdx n) := by
  have hdisj : Disjoint
      (Finset.univ.image fun i => CorrGadgetV.vertex i (decide (i ∈ b)))
      (Finset.univ.image fun e : CorrPairIdx n =>
        CorrGadgetV.edge e (decide (e.fst ∈ b)) (decide (e.snd ∈ b))) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_image] at hx hy
    obtain ⟨i, _, rfl⟩ := hx
    obtain ⟨e, _, he⟩ := hy
    cases he
  have h1 : (Finset.univ.image fun i => CorrGadgetV.vertex i (decide (i ∈ b))).card = n := by
    rw [Finset.card_image_of_injective _ fun i j h => by cases h; rfl, Finset.card_fin]
  have h2 : (Finset.univ.image fun e : CorrPairIdx n =>
      CorrGadgetV.edge e (decide (e.fst ∈ b)) (decide (e.snd ∈ b))).card =
      Fintype.card (CorrPairIdx n) := by
    rw [Finset.card_image_of_injective _ fun e₁ e₂ h => by cases h; rfl, Finset.card_univ]
  rw [liftCorrIndep, Finset.card_union_of_disjoint hdisj, h1, h2]

private def stabToCorrLinear (K : Type*) [Semiring K] (n : ℕ) :
    (CorrGadgetV n → K) →ₗ[K] ((Fin n × Fin n) → K) where
  toFun x p :=
    if h : p.1 = p.2 then x (.vertex p.1 true)
    else if hlt : p.1 < p.2 then x (.edge ⟨p.1, p.2, hlt⟩ true true)
    else x (.edge ⟨p.2, p.1, (lt_or_gt_of_ne h).resolve_left hlt⟩ true true)
  map_add' x y := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply]
    split_ifs <;> rfl
  map_smul' c x := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> rfl

private theorem stabToCorrLinear_lift {K : Type*} [Semiring K]
    {n : ℕ} (b : Finset (Fin n)) :
    stabToCorrLinear K n (stabVertex K (liftCorrIndep b)) = corrVertex K b := by
  ext ⟨i, j⟩
  simp only [stabToCorrLinear, LinearMap.coe_mk, AddHom.coe_mk, stabVertex, liftCorrIndep,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, corrVertex]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceDIte, and_self, reduceCtorEq, exists_false, or_false,
      CorrGadgetV.vertex.injEq, decide_eq_true_eq, exists_eq_left]
  · simp only [hij, ↓reduceDIte]
    have hiff (u v : Fin n) (hlt' : u < v) :
        (∃ e : CorrPairIdx n, CorrGadgetV.edge e (decide (e.fst ∈ b)) (decide (e.snd ∈ b)) =
          CorrGadgetV.edge ⟨u, v, hlt'⟩ true true) ↔ u ∈ b ∧ v ∈ b := by
      constructor
      · rintro ⟨e, he⟩
        simp only [CorrGadgetV.edge.injEq] at he
        rcases he with ⟨rfl, h1, h2⟩
        exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
      · rintro ⟨hu, hv⟩
        exact ⟨⟨u, v, hlt'⟩, by simp only [hu, hv, decide_true]⟩
    by_cases hlt : i < j
    · simp only [hlt, ↓reduceDIte, reduceCtorEq, exists_false, false_or, hiff i j hlt]
    · simp only [hlt, ↓reduceDIte, reduceCtorEq, exists_false, false_or,
        hiff j i ((lt_or_gt_of_ne hij).resolve_left hlt), and_comm]

private theorem stabToCorrLinear_tight {K : Type*} [Semiring K]
    {n : ℕ} {S : Finset (CorrGadgetV n)}
    (hS : (corrGadgetGraph n).IsIndepSet (S : Set (CorrGadgetV n)))
    (hcard : S.card = n + Fintype.card (CorrPairIdx n)) :
    ∃ b : Finset (Fin n), stabToCorrLinear K n (stabVertex K S) = corrVertex K b := by
  have hinj : Set.InjOn gadgetBlock (S : Set (CorrGadgetV n)) := fun u hu v hv heq => by
    by_contra hne
    exact hS hu hv hne (adj_of_gadgetBlock_eq hne heq)
  have him : S.image gadgetBlock = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_sum, Fintype.card_fin]
  let b : Finset (Fin n) := Finset.univ.filter fun i => CorrGadgetV.vertex i true ∈ S
  refine ⟨b, ?_⟩
  have hv_mem : ∀ i : Fin n, ∃ val : Bool, CorrGadgetV.vertex i val ∈ S := fun i => by
    have hi : Sum.inl i ∈ S.image gadgetBlock := him ▸ Finset.mem_univ _
    rw [Finset.mem_image] at hi
    obtain ⟨u, hu, hu_eq⟩ := hi
    cases u with
    | vertex i' val =>
        simp only [gadgetBlock, Sum.inl.injEq] at hu_eq
        subst hu_eq
        exact ⟨val, hu⟩
    | edge e c₁ c₂ => cases hu_eq
  have hv_true : ∀ i : Fin n, CorrGadgetV.vertex i (decide (i ∈ b)) ∈ S := fun i => by
    by_cases hi : i ∈ b
    · simp only [hi, decide_true]
      exact (Finset.mem_filter.1 hi).2
    · simp only [hi, decide_false]
      obtain ⟨val, hval⟩ := hv_mem i
      cases val
      · exact hval
      · exfalso
        exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, hval⟩)
  have he_mem : ∀ e : CorrPairIdx n,
      CorrGadgetV.edge e true true ∈ S ↔ e.fst ∈ b ∧ e.snd ∈ b := fun e => by
    have he : Sum.inr e ∈ S.image gadgetBlock := him ▸ Finset.mem_univ _
    rw [Finset.mem_image] at he
    obtain ⟨u, hu, hu_eq⟩ := he
    cases u with
    | vertex i val => cases hu_eq
    | edge e' c₁ c₂ =>
        simp only [gadgetBlock, Sum.inr.injEq] at hu_eq
        subst hu_eq
        have hc₁ : c₁ = decide (e'.fst ∈ b) := by
          by_contra hne
          exact hS (hv_true e'.fst) hu (by intro h; cases h)
            (Or.inl ⟨rfl, fun h => hne h.symm⟩)
        have hc₂ : c₂ = decide (e'.snd ∈ b) := by
          by_contra hne
          exact hS (hv_true e'.snd) hu (by intro h; cases h)
            (Or.inr ⟨rfl, fun h => hne h.symm⟩)
        constructor
        · intro htrue
          have huq := hinj hu htrue rfl
          cases huq
          exact ⟨of_decide_eq_true hc₁.symm, of_decide_eq_true hc₂.symm⟩
        · rintro ⟨h1, h2⟩
          have hc₁' : c₁ = true := hc₁.trans (decide_eq_true h1)
          have hc₂' : c₂ = true := hc₂.trans (decide_eq_true h2)
          rwa [hc₁', hc₂'] at hu
  ext ⟨i, j⟩
  simp only [stabToCorrLinear, LinearMap.coe_mk, AddHom.coe_mk, stabVertex, corrVertex]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceDIte, and_self, b, Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [hij, ↓reduceDIte]
    by_cases hlt : i < j
    · simp only [hlt, ↓reduceDIte, he_mem ⟨i, j, hlt⟩]
    · simp only [hlt, ↓reduceDIte, he_mem ⟨j, i, (lt_or_gt_of_ne hij).resolve_left hlt⟩,
        and_comm]

/-- `CORR(n)` is the linear projection of a face of `STAB(corrGadgetGraph n)`
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemmas 8–9]. -/
theorem extensionComplexity_corrPolytope_le_corrGadgetGraph
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (n : ℕ) :
    extensionComplexity (corrPolytope K (Fin n)) ≤
      extensionComplexity (stabPolytope K (corrGadgetGraph n)) := by
  let δ : K := (n + Fintype.card (CorrPairIdx n) : ℕ)
  let c : CorrGadgetV n → K := fun _ => 1
  have hdot : ∀ S : Finset (CorrGadgetV n), c ⬝ᵥ stabVertex K S = (S.card : K) := fun S => by
    simp only [dotProduct, c, stabVertex, one_mul, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
  have hvalid : ∀ S : {S : Finset (CorrGadgetV n) // (corrGadgetGraph n).IsIndepSet (S : Set _)},
      c ⬝ᵥ stabVertex K S.1 ≤ δ := fun S => by
    rw [hdot]
    dsimp only [δ]
    exact_mod_cast card_le_of_isIndepSet_corrGadgetGraph S.2
  have htight_iff :
      ∀ S : {S : Finset (CorrGadgetV n) // (corrGadgetGraph n).IsIndepSet (S : Set _)},
      c ⬝ᵥ stabVertex K S.1 = δ ↔ S.1.card = n + Fintype.card (CorrPairIdx n) := fun S => by
    rw [hdot]
    exact Nat.cast_inj
  let face := stabPolytope K (corrGadgetGraph n) ∩ {x | c ⬝ᵥ x = δ}
  have him : stabToCorrLinear K n '' face = corrPolytope K (Fin n) := by
    have hface : face =
        convexHull K ((fun S : {S : Finset (CorrGadgetV n) //
            (corrGadgetGraph n).IsIndepSet (S : Set _)} => stabVertex K S.1) ''
          {S | c ⬝ᵥ stabVertex K S.1 = δ}) := by
      simpa only [face, stabPolytope] using convexHull_inter_dotProduct_eq hvalid
    rw [hface, LinearMap.image_convexHull, corrPolytope]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨S, hS, hSc, rfl⟩, rfl⟩
      rw [htight_iff ⟨S, hS⟩] at hSc
      obtain ⟨b, hb⟩ := stabToCorrLinear_tight (K := K) hS hSc
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩
      refine ⟨stabVertex K (liftCorrIndep b),
        ⟨liftCorrIndep b, isIndepSet_liftCorrIndep b, ?_, rfl⟩,
        stabToCorrLinear_lift b⟩
      rw [htight_iff ⟨liftCorrIndep b, isIndepSet_liftCorrIndep b⟩]
      exact card_liftCorrIndep b
  calc
    extensionComplexity (corrPolytope K (Fin n))
        = extensionComplexity (stabToCorrLinear K n '' face) := by rw [him]
    _ ≤ extensionComplexity face := extensionComplexity_image_linearMap_le face _
    _ ≤ extensionComplexity (stabPolytope K (corrGadgetGraph n)) :=
      extensionComplexity_inter_dotProduct_eq_le _ c δ

end Gadget

section LowerBound

private noncomputable def stabHardEmb (m : ℕ) :
    CorrGadgetV (Nat.sqrt (m / 2)) ↪ Fin m := by
  let p := Nat.sqrt (m / 2)
  have hle : Fintype.card (CorrGadgetV p) ≤ m := by
    rw [card_corrGadgetV]
    have hsq : p ^ 2 ≤ m / 2 := Nat.sqrt_le' (m / 2)
    omega
  exact (Fintype.equivFin (CorrGadgetV p)).toEmbedding.trans (Fin.castLEEmb hle)

/-- An explicit `m`-vertex graph (`m ≥ 2`) obtained by embedding `corrGadgetGraph ⌊√(m / 2)⌋`
together with isolated vertices [FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 10]. -/
noncomputable def stabHardGraph (m : ℕ) : SimpleGraph (Fin m) :=
  if hm : 2 ≤ m then
    { Adj := fun u v => ∃ a b, stabHardEmb m a = u ∧ stabHardEmb m b = v ∧
        (corrGadgetGraph (Nat.sqrt (m / 2))).Adj a b
      symm := ⟨fun _ _ ⟨a, b, ha, hb, hab⟩ => ⟨b, a, hb, ha, hab.symm⟩⟩
      loopless := ⟨fun _ ⟨a, b, ha, hb, hab⟩ => by
        have hba : a = b := (stabHardEmb m).injective (ha.trans hb.symm)
        subst hba
        exact (corrGadgetGraph (Nat.sqrt (m / 2))).ne_of_adj hab rfl⟩ }
  else ⊥

private theorem extensionComplexity_corrGadgetGraph_le_stabHardGraph
    {K : Type*} [Field K] [LinearOrder K] (m : ℕ) (hm : 2 ≤ m) :
    extensionComplexity (stabPolytope K (corrGadgetGraph (Nat.sqrt (m / 2)))) ≤
      extensionComplexity (stabPolytope K (stabHardGraph m)) := by
  classical
  let p := Nat.sqrt (m / 2)
  let emb := stabHardEmb m
  let proj : (Fin m → K) →ₗ[K] (CorrGadgetV p → K) := LinearMap.funLeft K K emb
  have him : proj '' stabPolytope K (stabHardGraph m) =
      stabPolytope K (corrGadgetGraph p) := by
    rw [stabPolytope, LinearMap.image_convexHull, stabPolytope]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
      let S' : Finset (CorrGadgetV p) := Finset.univ.filter fun a => emb a ∈ S
      have hS' : (corrGadgetGraph p).IsIndepSet (S' : Set (CorrGadgetV p)) := by
        intro a ha b hb hab hadj
        simp only [Finset.mem_coe, S', Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        refine hS ha hb (fun heq => hab (emb.injective heq)) ?_
        simp only [stabHardGraph, hm, ↓reduceDIte]
        exact ⟨a, b, rfl, rfl, hadj⟩
      refine ⟨S', hS', ?_⟩
      ext a
      simp only [proj, LinearMap.funLeft_apply, stabVertex, S', Finset.mem_filter,
        Finset.mem_univ, true_and]
    · rintro ⟨T, hT, rfl⟩
      have hT' : (stabHardGraph m).IsIndepSet (T.map emb : Set (Fin m)) := by
        intro u hu v hv huv hadj
        simp only [stabHardGraph, hm, ↓reduceDIte] at hadj
        obtain ⟨a, b, rfl, rfl, hab⟩ := hadj
        simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hu hv
        obtain ⟨a', ha', hae⟩ := hu
        obtain ⟨b', hb', hbe⟩ := hv
        have haa' : a' = a := emb.injective hae
        have hbb' : b' = b := emb.injective hbe
        subst haa' hbb'
        exact hT ha' hb' (fun heq => huv (congrArg emb heq)) hab
      refine ⟨stabVertex K (T.map emb), ⟨T.map emb, hT', rfl⟩, ?_⟩
      ext a
      simp only [proj, LinearMap.funLeft_apply, stabVertex, Finset.mem_map,
        EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  rw [← him]
  exact extensionComplexity_image_linearMap_le _ proj

/-- Exponential lower bound for the stable set polytope on `m ≥ 2` vertices: for
`p = Nat.sqrt (m / 2)`, `3 ^ p ≤ 2 ^ p * xc (stabPolytope K (stabHardGraph m))` in `ℕ∞`
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 10]; [KaibelWeltge2015, Theorem 1]. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_stabPolytope
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (m : ℕ) (hm : 2 ≤ m) :
    ((3 ^ Nat.sqrt (m / 2) : ℕ) : ℕ∞) ≤
      (2 ^ Nat.sqrt (m / 2) : ℕ∞) * extensionComplexity (stabPolytope K (stabHardGraph m)) := by
  have hp : 0 < Nat.sqrt (m / 2) := Nat.sqrt_pos.2 (by omega)
  have : Nonempty (Fin (Nat.sqrt (m / 2))) := ⟨⟨0, hp⟩⟩
  have h1 := three_pow_le_two_pow_mul_extensionComplexity_corrPolytope (K := K)
    (α := Fin (Nat.sqrt (m / 2)))
  rw [Fintype.card_fin] at h1
  have h2 := (extensionComplexity_corrPolytope_le_corrGadgetGraph (K := K)
    (Nat.sqrt (m / 2))).trans (extensionComplexity_corrGadgetGraph_le_stabHardGraph (K := K) m hm)
  exact h1.trans (mul_le_mul_right h2 _)

/-- Field-valued `2^{Ω(√m)}` lower bound: any extended formulation of
`stabPolytope K (stabHardGraph m)` (`m ≥ 2`) with `r` inequalities satisfies
`(3 / 2 : F) ^ Nat.sqrt (m / 2) ≤ r`. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_stabPolytope
    {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {m r : ℕ} (hm : 2 ≤ m) (hr : HasExtendedFormulation (stabPolytope K (stabHardGraph m)) r) :
    (3 / 2 : F) ^ Nat.sqrt (m / 2) ≤ r :=
  hr.three_div_two_pow_le_of_mul_le (three_pow_le_two_pow_mul_extensionComplexity_stabPolytope m hm)

end LowerBound
