/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ExactOne
public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Complexity.Problems.Graph.PerfectMatchingPolyTime
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Logics.Propositional.CNF.GraphCountingEncodings
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Computability.Circuit.Boolean.Encoding
import CslibFrontier.Computability.Complexity.Problems.Graph.VertexColors
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.Range
import CslibFrontier.Logics.Propositional.CSP.Vars
import CslibFrontier.Tactic.EncLen

/-!
# Polynomial-time counting CNF reductions for graph problems

Executable polynomial-time CNF encodings for three classical graph counting problems on
`Cslib.Complexity.Graph`, preserving exact solution counts with explicit assignment bijections:

1. **Independent sets** (`Graph.toIndepSetCNF`): `n = |V|` variables, clause width `2`,
   preserving `Nat.card {S // G.induced.IsIndepSet S}`.
2. **Proper `q`-colourings** (`Graph.toColoringCNF q`): `n = q * |V|` variables, clause width
   `≤ max q 2`, preserving `Nat.card (G.induced.Coloring (Fin q))`.
3. **Perfect matchings** (`Graph.toPerfectMatchingCNF`): `n ≤ 1 + 4 |V| + 7 |E| = O(|V| + |E|)`
   variables, exact clause width `3`, compiled via sequential linear-size exact-one De Morgan
   circuits (`Cslib.Circuits.Boolean.seqExactlyOneAll`) and `tseitinSatCNF`, preserving
   `Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching}` ([Tseitin 1983][Tseitin1983],
   [Cygan et al.][CyganEtAl2015]).

## Main definitions

* `Cslib.Complexity.Graph.toIndepSetCNF`, `Cslib.Complexity.Graph.indepSetCNFEquiv`.
* `Cslib.Complexity.Graph.coloringVar`, `Cslib.Complexity.Graph.toColoringCNF`,
  `Cslib.Complexity.Graph.coloringCNFEquiv`.
* `Cslib.Complexity.Graph.perfectMatchingWires`, `Cslib.Complexity.Graph.perfectMatchingCircuit`,
  `Cslib.Complexity.Graph.toPerfectMatchingCNF`, `Cslib.Complexity.Graph.perfectMatchingCNFEquiv`.

## Main results

* `Cslib.Complexity.Graph.modelCount_toIndepSetCNF`,
  `Cslib.Complexity.Graph.computableInPolyTime_toIndepSetCNF`: exact count, width `2`,
  `numVars = |V|`, and polynomial-time compilation for independent sets.
* `Cslib.Complexity.Graph.modelCount_toColoringCNF`,
  `Cslib.Complexity.Graph.computableInPolyTime_toColoringCNF`: exact count, width `≤ max q 2`,
  `numVars = q * |V|`, and polynomial-time compilation for `q`-colourings.
* `Cslib.Complexity.Graph.modelCountOn_toPerfectMatchingCNF`,
  `Cslib.Complexity.Graph.numVars_toPerfectMatchingCNF_le`,
  `Cslib.Complexity.Graph.computableInPolyTime_toPerfectMatchingCNF`: exact count, width `3`,
  linear `O(|V| + |E|)` variables and clauses, and polynomial-time compilation for perfect
  matchings.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  and S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime Circuits Boolean

/-! ### 1. Independent sets (`n = |V|`, width `2`) -/

/-- Executable width-`2` CNF encoding of the independent sets of `G.induced` on `|V|` variables. -/
@[expose] def toIndepSetCNF (G : Graph) : CNF ℕ :=
  CNF.indepSetCNF G.1 G.2

/-- Every clause of `G.toIndepSetCNF` has exact length `2`. -/
theorem length_clause_toIndepSetCNF {G : Graph} {c : Clause ℕ} (hc : c ∈ G.toIndepSetCNF) :
    c.length = 2 :=
  CNF.length_clause_indepSetCNF hc

/-- `G.toIndepSetCNF` has exactly `G.1.toFinset.card` occurring variables. -/
@[simp]
theorem numVars_toIndepSetCNF (G : Graph) : G.toIndepSetCNF.numVars = G.1.toFinset.card :=
  CNF.numVars_indepSetCNF G.1 G.2

/-- Occurring variables of `G.toIndepSetCNF` are bounded by `(encGraph G).length`. -/
theorem numVars_toIndepSetCNF_le_enc (G : Graph) :
    G.toIndepSetCNF.numVars ≤ (encGraph G).length := by
  rw [numVars_toIndepSetCNF]
  exact G.1.toFinset_card_le.trans G.length_vertices_le_encGraph

/-- Explicit bijection between satisfying assignments of `G.toIndepSetCNF` on `G.1.toFinset`
and independent sets of `G.induced`. -/
def indepSetCNFEquiv (G : Graph) :
    {σ : G.1.toFinset → Bool //
      G.toIndepSetCNF.eval (fun v => if hv : v ∈ G.1.toFinset then σ ⟨v, hv⟩ else false) =
        true} ≃
      {S : Finset {v : ℕ // v ∈ G.1} // G.induced.IsIndepSet (S : Set {v : ℕ // v ∈ G.1})} :=
  CNF.indepSetCNFEquiv (G := G.induced) fun _ _ => Graph.induced_adj.trans Graph.toSimpleGraph_adj

/-- **Exact model count of `G.toIndepSetCNF`**: number of independent sets of `G.induced`. -/
theorem modelCount_toIndepSetCNF (G : Graph) :
    G.toIndepSetCNF.modelCount =
      Nat.card {S : Finset {v : ℕ // v ∈ G.1} //
        G.induced.IsIndepSet (S : Set {v : ℕ // v ∈ G.1})} :=
  CNF.modelCount_indepSetCNF (G := G.induced) fun _ _ =>
    Graph.induced_adj.trans Graph.toSimpleGraph_adj

private theorem computableInPolyTime_edgePairs :
    ComputableInPolyTime (fun G : Graph => CNF.edgePairs G.1 G.2)
      encGraph (encList (encPair encNat encNat)) := by
  have h : ComputableInPolyTime
      (fun G : Graph => G.2.filter fun e =>
        decide (e.1 ∈ G.1) && decide (e.2 ∈ G.1) && decide (e.1 ≠ e.2))
      encGraph (encList (encPair encNat encNat)) := by
    unfold encGraph
    fun_prop
  refine h.of_enc_eq fun G => congrArg (encList (encPair encNat encNat)) ?_
  simp only [CNF.edgePairs, Bool.decide_and, Bool.and_assoc]

/-- Constructing `G.toIndepSetCNF` from `encGraph` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toIndepSetCNF :
    ComputableInPolyTime toIndepSetCNF encGraph encCNF := by
  have hed := computableInPolyTime_edgePairs
  unfold toIndepSetCNF CNF.indepSetCNF
  fun_prop

/-! ### 2. Proper `q`-colourings (`n = q * |V|`, width `≤ max q 2`) -/

/-- Natural variable index encoding `(v, c)` as `q * G.distinctVertices.idxOf v + c`. -/
@[expose] def coloringVar (q : ℕ) (G : Graph) (p : ℕ × ℕ) : ℕ :=
  q * G.distinctVertices.idxOf p.1 + p.2

/-- Executable CNF encoding of proper `q`-colourings of `G.induced` over dense natural variables
`0, …, q * |V| - 1`, with clause width at most `max q 2`. -/
@[expose] def toColoringCNF (q : ℕ) (G : Graph) : CNF ℕ :=
  (CNF.coloringCNF q G.1 G.2).relabel (coloringVar q G)

/-- Every clause of `G.toColoringCNF q` has width at most `max q 2`. -/
theorem length_clause_toColoringCNF_le {q : ℕ} {G : Graph} {c : Clause ℕ}
    (hc : c ∈ G.toColoringCNF q) : c.length ≤ max q 2 := by
  simp only [toColoringCNF, CNF.relabel, Clause.relabel, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  rw [List.length_map]
  exact CNF.length_clause_coloringCNF_le hc₀

private theorem coloringVar_injOn (q : ℕ) (G : Graph) :
    Set.InjOn (coloringVar q G) {p | p ∈ (CNF.coloringCNF q G.1 G.2).vars} := by
  intro ⟨v₁, c₁⟩ h₁ ⟨v₂, c₂⟩ h₂ heq
  obtain ⟨hv₁, hc₁⟩ := CNF.mem_vars_coloringCNF.mp h₁
  obtain ⟨hv₂, hc₂⟩ := CNF.mem_vars_coloringCNF.mp h₂
  dsimp only [coloringVar] at heq
  have hq : 0 < q := Nat.zero_lt_of_lt hc₁
  have hdv₁ : (q * G.distinctVertices.idxOf v₁ + c₁) / q = G.distinctVertices.idxOf v₁ := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hc₁, Nat.zero_add]
  have hdv₂ : (q * G.distinctVertices.idxOf v₂ + c₂) / q = G.distinctVertices.idxOf v₂ := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hc₂, Nat.zero_add]
  have hdiv : G.distinctVertices.idxOf v₁ = G.distinctVertices.idxOf v₂ :=
    hdv₁.symm.trans ((congrArg (· / q) heq).trans hdv₂)
  have hmod : c₁ = c₂ := by
    have hm1 : (q * G.distinctVertices.idxOf v₁ + c₁) % q = c₁ := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc₁]
    have hm2 : (q * G.distinctVertices.idxOf v₂ + c₂) % q = c₂ := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc₂]
    exact hm1.symm.trans ((congrArg (· % q) heq).trans hm2)
  have hvEq : v₁ = v₂ :=
    (List.idxOf_inj (Graph.mem_distinctVertices.mpr hv₁)).mp hdiv
  exact Prod.ext hvEq hmod

/-- The occurring variables of `G.toColoringCNF q` are precisely `Finset.range (q * |V|)`. -/
theorem vars_toColoringCNF (q : ℕ) (G : Graph) :
    (G.toColoringCNF q).vars.toFinset = Finset.range (q * G.distinctVertices.length) := by
  ext k
  rw [toColoringCNF, List.mem_toFinset, CNF.vars_relabel, List.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨⟨v, c⟩, hv, rfl⟩
    obtain ⟨hvG, hc⟩ := CNF.mem_vars_coloringCNF.mp hv
    have hidx : G.distinctVertices.idxOf v < G.distinctVertices.length :=
      List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr hvG)
    have h1 : q * G.distinctVertices.idxOf v + c < q * (G.distinctVertices.idxOf v + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact h1.trans_le (Nat.mul_le_mul_left q (Nat.succ_le_of_lt hidx))
  · intro hk
    have hq : 0 < q := by
      by_contra hq0
      have hq' : q = 0 := by omega
      subst hq'
      simp at hk
    have hdiv : k / q < G.distinctVertices.length := (Nat.div_lt_iff_lt_mul hq).mpr
      (by simpa only [Nat.mul_comm] using hk)
    let v := G.distinctVertices[k / q]
    have hv : v ∈ G.1 := Graph.mem_distinctVertices.mp (List.getElem_mem hdiv)
    refine ⟨(v, k % q), CNF.mem_vars_coloringCNF.mpr ⟨hv, Nat.mod_lt k hq⟩, ?_⟩
    rw [coloringVar, (Graph.nodup_distinctVertices G).idxOf_getElem (k / q) hdiv]
    have := Nat.div_add_mod k q
    omega

/-- `G.toColoringCNF q` uses exactly `q * G.1.toFinset.card` variables. -/
@[simp]
theorem numVars_toColoringCNF (q : ℕ) (G : Graph) :
    (G.toColoringCNF q).numVars = q * G.1.toFinset.card := by
  rw [CNF.numVars, vars_toColoringCNF, Finset.card_range, Graph.length_distinctVertices]

theorem validDeclaredInput_toColoringCNF (q : ℕ) (G : Graph) :
    CNF.validDeclaredInput (max q 2) (q * G.distinctVertices.length) (G.toColoringCNF q) =
      true := by
  rw [CNF.validDeclaredInput_eq_true_iff, vars_toColoringCNF]
  exact ⟨fun _ hc => length_clause_toColoringCNF_le hc, Finset.Subset.rfl⟩

/-- Variable-domain bijection `G.1.toFinset ×ˢ Finset.range q ≃ Finset.range (q * |V|)`. -/
private def coloringDomainEquiv (q : ℕ) (G : Graph) :
    ↥(G.1.toFinset ×ˢ Finset.range q) ≃ ↥(Finset.range (q * G.distinctVertices.length)) where
  toFun p := ⟨coloringVar q G p.1, by
    have hp := Finset.mem_product.mp p.2
    have hvG : p.1.1 ∈ G.1 := List.mem_toFinset.mp hp.1
    have hc : p.1.2 < q := Finset.mem_range.mp hp.2
    have hidx : G.distinctVertices.idxOf p.1.1 < G.distinctVertices.length :=
      List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr hvG)
    have h1 : q * G.distinctVertices.idxOf p.1.1 + p.1.2 <
        q * (G.distinctVertices.idxOf p.1.1 + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact Finset.mem_range.mpr (h1.trans_le (Nat.mul_le_mul_left q (Nat.succ_le_of_lt hidx)))⟩
  invFun k := ⟨(G.distinctVertices[k.1 / q]'(by
      have hq : 0 < q := by
        by_contra h0
        have : q = 0 := by omega
        have hk := Finset.mem_range.mp k.2
        subst this
        simp at hk
      exact (Nat.div_lt_iff_lt_mul hq).mpr
        (by simpa only [Nat.mul_comm] using Finset.mem_range.mp k.2)), k.1 % q), by
    have hk := Finset.mem_range.mp k.2
    have hq : 0 < q := by
      by_contra h0
      have : q = 0 := by omega
      subst this
      simp at hk
    have hdiv : k.1 / q < G.distinctVertices.length :=
      (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [Nat.mul_comm] using hk)
    exact Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr (Graph.mem_distinctVertices.mp (List.getElem_mem hdiv)),
        Finset.mem_range.mpr (Nat.mod_lt k.1 hq)⟩⟩
  left_inv p := by
    have hp := Finset.mem_product.mp p.2
    have hvG : p.1.1 ∈ G.1 := List.mem_toFinset.mp hp.1
    have hc : p.1.2 < q := Finset.mem_range.mp hp.2
    have hq : 0 < q := Nat.zero_lt_of_lt hc
    have hdiv : (q * G.distinctVertices.idxOf p.1.1 + p.1.2) / q =
        G.distinctVertices.idxOf p.1.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hc, Nat.zero_add]
    have hmod : (q * G.distinctVertices.idxOf p.1.1 + p.1.2) % q = p.1.2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    refine Subtype.ext (Prod.ext ?_ hmod)
    simp only [coloringVar, hdiv]
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr hvG))
  right_inv k := by
    have hk := Finset.mem_range.mp k.2
    have hq : 0 < q := by
      by_contra h0
      have : q = 0 := by omega
      subst this
      simp at hk
    have hdiv : k.1 / q < G.distinctVertices.length :=
      (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [Nat.mul_comm] using hk)
    refine Subtype.ext ?_
    dsimp only [coloringVar]
    rw [(Graph.nodup_distinctVertices G).idxOf_getElem (k.1 / q) hdiv]
    have := Nat.div_add_mod k.1 q
    omega

/-- Explicit bijection between satisfying assignments of `G.toColoringCNF q` on
`Finset.range (q * |V|)` and proper `q`-colourings of `G.induced`. -/
noncomputable def coloringCNFEquiv (q : ℕ) (G : Graph) :
    {σ : Finset.range (q * G.distinctVertices.length) → Bool //
      (G.toColoringCNF q).eval
        (fun k => if hk : k ∈ Finset.range (q * G.distinctVertices.length) then σ ⟨k, hk⟩
          else false) = true} ≃
      G.induced.Coloring (Fin q) := by
  let eAssign :
      {σ : Finset.range (q * G.distinctVertices.length) → Bool //
        (G.toColoringCNF q).eval
          (fun k => if hk : k ∈ Finset.range (q * G.distinctVertices.length) then σ ⟨k, hk⟩
            else false) = true} ≃
      {σ : G.1.toFinset ×ˢ Finset.range q → Bool //
        (CNF.coloringCNF q G.1 G.2).eval
          (fun p => if hp : p ∈ G.1.toFinset ×ˢ Finset.range q then σ ⟨p, hp⟩ else false) =
            true} :=
    { toFun := fun σ => ⟨fun p => σ.1 (coloringDomainEquiv q G p), by
        have h := σ.2
        dsimp only [toColoringCNF] at h
        rw [CNF.eval_relabel] at h
        refine (CNF.eval_congr fun p hp => ?_).trans h
        have hp' : p ∈ G.1.toFinset ×ˢ Finset.range q := by
          obtain ⟨hv, hc⟩ := CNF.mem_vars_coloringCNF.mp hp
          exact Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, Finset.mem_range.mpr hc⟩
        have hmem : coloringVar q G p ∈ Finset.range (q * G.distinctVertices.length) :=
          (coloringDomainEquiv q G ⟨p, hp'⟩).2
        simp only [Function.comp_def, hp', ↓reduceDIte, hmem]
        rfl⟩
      invFun := fun σ => ⟨fun k => σ.1 ((coloringDomainEquiv q G).symm k), by
        dsimp only [toColoringCNF]
        rw [CNF.eval_relabel]
        refine (CNF.eval_congr fun p hp => ?_).trans σ.2
        have hp' : p ∈ G.1.toFinset ×ˢ Finset.range q := by
          obtain ⟨hv, hc⟩ := CNF.mem_vars_coloringCNF.mp hp
          exact Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, Finset.mem_range.mpr hc⟩
        have hmem : coloringVar q G p ∈ Finset.range (q * G.distinctVertices.length) :=
          (coloringDomainEquiv q G ⟨p, hp'⟩).2
        simp only [Function.comp_def, hmem, ↓reduceDIte, hp']
        exact congrArg σ.1 ((coloringDomainEquiv q G).symm_apply_apply ⟨p, hp'⟩)⟩
      left_inv := fun σ => Subtype.ext (funext fun k =>
        congrArg σ.1 ((coloringDomainEquiv q G).apply_symm_apply k))
      right_inv := fun σ => Subtype.ext (funext fun p =>
        congrArg σ.1 ((coloringDomainEquiv q G).symm_apply_apply p)) }
  exact eAssign.trans (CNF.coloringCNFEquiv (G := G.induced) fun _ _ =>
    Graph.induced_adj.trans Graph.toSimpleGraph_adj)

/-- **Exact model count of `G.toColoringCNF q`**: number of proper `q`-colourings of `G.induced`. -/
theorem modelCount_toColoringCNF (q : ℕ) (G : Graph) :
    (G.toColoringCNF q).modelCount = Nat.card (G.induced.Coloring (Fin q)) := by
  rw [toColoringCNF, CNF.modelCount_relabel_of_injOn _ (coloringVar_injOn q G)]
  exact CNF.modelCount_coloringCNF (G := G.induced) fun _ _ =>
    Graph.induced_adj.trans Graph.toSimpleGraph_adj

theorem modelCountOn_toColoringCNF (q : ℕ) (G : Graph) :
    (G.toColoringCNF q).modelCountOn (Finset.range (q * G.distinctVertices.length)) =
      Nat.card (G.induced.Coloring (Fin q)) := by
  rw [← vars_toColoringCNF, CNF.modelCountOn_vars, modelCount_toColoringCNF]

private theorem tidy_coloringVar (q c : ℕ) :
    ComputableTidilyInPolyTime (fun p : Graph × ℕ => coloringVar q p.1 (p.2, c))
      (encPair encGraph encNat) encNat := by
  unfold coloringVar
  have hidx : ComputableTidilyInPolyTime
      (fun p : Graph × ℕ => p.1.distinctVertices.idxOf p.2)
      (encPair encGraph encNat) encUnary :=
    ComputableTidilyInPolyTime.idxOfWithInput
      (Graph.computableInPolyTime_distinctVertices.comp
        (ComputableInPolyTime.fst encGraph encNat)).tidy
      (ComputableTidilyInPolyTime.snd encGraph encNat)
  have hmul : ComputableTidilyInPolyTime
      (fun p : Graph × ℕ => q * p.1.distinctVertices.idxOf p.2 + c)
      (encPair encGraph encNat) encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const q).prod hidx)).prod
        (ComputableTidilyInPolyTime.const c))
  exact ComputableTidilyInPolyTime.unary_to_binary.comp hmul

private theorem tidy_coloringVertexClauses (q : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : Graph × ℕ =>
        ([(List.range q).map fun c => (coloringVar q p.1 (p.2, c), true)] : CNF ℕ) ++
          (List.range q).flatMap fun c₁ =>
            ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂)).map fun c₂ =>
              [(coloringVar q p.1 (p.2, c₁), false), (coloringVar q p.1 (p.2, c₂), false)])
      (encPair encGraph encNat) encCNF := by
  have hal : ComputableTidilyInPolyTime
      (fun p : Graph × ℕ => (List.range q).map fun c => (coloringVar q p.1 (p.2, c), true))
      (encPair encGraph encNat) (encClause encNat) :=
    ComputableTidilyInPolyTime.mapConst (List.range q) fun c _ =>
      (tidy_coloringVar q c).prod (ComputableTidilyInPolyTime.const true)
  have hamo : ComputableTidilyInPolyTime
      (fun p : Graph × ℕ =>
        (List.range q).flatMap fun c₁ =>
          ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂)).map fun c₂ =>
            [(coloringVar q p.1 (p.2, c₁), false), (coloringVar q p.1 (p.2, c₂), false)])
      (encPair encGraph encNat) encCNF :=
    ComputableTidilyInPolyTime.flatMapConst (List.range q) fun c₁ _ =>
      ComputableTidilyInPolyTime.mapConst ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂))
        fun c₂ _ =>
          ((tidy_coloringVar q c₁).prod (ComputableTidilyInPolyTime.const false)).cons'
            (((tidy_coloringVar q c₂).prod (ComputableTidilyInPolyTime.const false)).cons'
              (ComputableTidilyInPolyTime.const ([] : Clause ℕ)))
  exact (ComputableTidilyInPolyTime.listAppend (encClause encNat)).comp
    ((hal.cons' (ComputableTidilyInPolyTime.const ([] : CNF ℕ))).prod hamo)

private theorem tidy_coloringEdgeVar1 (q c : ℕ) :
    ComputableTidilyInPolyTime (fun p : Graph × ℕ × ℕ => coloringVar q p.1 (p.2.1, c))
      (encPair encGraph (encPair encNat encNat)) encNat :=
  (tidy_coloringVar q c).comp
    ((ComputableTidilyInPolyTime.fst encGraph (encPair encNat encNat)).prod
      (ComputableTidilyInPolyTime.snd encGraph (encPair encNat encNat)).fst')

private theorem tidy_coloringEdgeVar2 (q c : ℕ) :
    ComputableTidilyInPolyTime (fun p : Graph × ℕ × ℕ => coloringVar q p.1 (p.2.2, c))
      (encPair encGraph (encPair encNat encNat)) encNat :=
  (tidy_coloringVar q c).comp
    ((ComputableTidilyInPolyTime.fst encGraph (encPair encNat encNat)).prod
      (ComputableTidilyInPolyTime.snd encGraph (encPair encNat encNat)).snd')

private theorem tidy_coloringEdgeClauses (q : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : Graph × ℕ × ℕ =>
        (List.range q).map fun c =>
          [(coloringVar q p.1 (p.2.1, c), false), (coloringVar q p.1 (p.2.2, c), false)])
      (encPair encGraph (encPair encNat encNat)) encCNF :=
  ComputableTidilyInPolyTime.mapConst (List.range q) fun c _ =>
    ((tidy_coloringEdgeVar1 q c).prod (ComputableTidilyInPolyTime.const false)).cons'
      (((tidy_coloringEdgeVar2 q c).prod (ComputableTidilyInPolyTime.const false)).cons'
        (ComputableTidilyInPolyTime.const ([] : Clause ℕ)))

/-- Constructing `G.toColoringCNF q` from `encGraph` is polynomial-time for every fixed `q`. -/
@[fun_prop]
theorem computableInPolyTime_toColoringCNF (q : ℕ) :
    ComputableInPolyTime (toColoringCNF q) encGraph encCNF := by
  have hpart1 : ComputableTidilyInPolyTime
      (fun G : Graph => G.1.flatMap fun v =>
        [List.map (fun c => (coloringVar q G (v, c), true)) (List.range q)] ++
          (List.range q).flatMap fun c₁ =>
            ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂)).map fun c₂ =>
              [(coloringVar q G (v, c₁), false), (coloringVar q G (v, c₂), false)])
      encGraph encCNF :=
    ComputableTidilyInPolyTime.flatMapWithInput
      (Graph.computableInPolyTime_fst ComputableInPolyTime.id').tidy (tidy_coloringVertexClauses q)
  have hpart2 : ComputableTidilyInPolyTime
      (fun G : Graph => (CNF.edgePairs G.1 G.2).flatMap fun e =>
        (List.range q).map fun c =>
          [(coloringVar q G (e.1, c), false), (coloringVar q G (e.2, c), false)])
      encGraph encCNF :=
    ComputableTidilyInPolyTime.flatMapWithInput
      computableInPolyTime_edgePairs.tidy (tidy_coloringEdgeClauses q)
  have hcomb : ComputableInPolyTime
      (fun G : Graph =>
        (G.1.flatMap fun v =>
          [List.map (fun c => (coloringVar q G (v, c), true)) (List.range q)] ++
            (List.range q).flatMap fun c₁ =>
              ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂)).map fun c₂ =>
                [(coloringVar q G (v, c₁), false), (coloringVar q G (v, c₂), false)]) ++
        ((CNF.edgePairs G.1 G.2).flatMap fun e =>
          (List.range q).map fun c =>
            [(coloringVar q G (e.1, c), false), (coloringVar q G (e.2, c), false)]))
      encGraph encCNF :=
    (ComputableTidilyInPolyTime.listAppend (encClause encNat)).computableInPolyTime.comp
      (hpart1.prod hpart2).computableInPolyTime
  refine hcomb.of_enc_eq fun G => congrArg encCNF ?_
  simp only [toColoringCNF, CNF.coloringCNF, CNF.relabel, Clause.relabel, CNF.exactlyOne,
    CNF.atLeastOne, CNF.atMostOne, List.map_append, List.map_flatMap, List.map_cons,
    List.map_nil, List.map_map, Function.comp_def, List.flatMap_map,
    List.cons_append, List.nil_append]
  congr 1
  refine List.flatMap_congr fun v _ => ?_
  congr 1
  refine List.flatMap_congr fun c₁ _ => ?_
  rw [List.filter_map, List.map_map]
  congr 1
  refine List.filter_congr fun c₂ _ => ?_
  simp [eq_comm]

/-! ### 3. Perfect matchings (`n = O(|V| + |E|)`, width `3`) -/

/-- Exact-one wire lists for `G.edgeList`: for each distinct vertex `v ∈ G.distinctVertices`,
the positions `i < G.edgeList.length` of edges incident to `v`. -/
@[expose] def perfectMatchingWires (G : Graph) : List (List ℕ) :=
  G.distinctVertices.map fun v =>
    (List.range G.edgeList.length).filter fun i =>
      Graph.incident (G.edgeList.getD i (0, 0)) v

/-- Linear-size sequential exact-one De Morgan gate list and output wire for `G`. -/
@[expose] def perfectMatchingCircuit (G : Graph) : List (Op × List ℕ) × ℕ :=
  seqExactlyOneAll G.edgeList.length G.perfectMatchingWires

/-- **Width-`3` CNF encoding of perfect matchings** via sequential exact-one De Morgan circuits
and Tseitin compilation: exact clause width `3` and `O(|V| + |E|)` variables and clauses. -/
@[expose] def toPerfectMatchingCNF (G : Graph) : CNF ℕ :=
  tseitinSatCNF [] G.edgeList.length G.perfectMatchingCircuit.1 G.perfectMatchingCircuit.2

/-- Every clause of `G.toPerfectMatchingCNF` has exact width `3`. -/
theorem length_clause_toPerfectMatchingCNF {G : Graph} {c : Clause ℕ}
    (hc : c ∈ G.toPerfectMatchingCNF) : c.length = 3 :=
  length_of_mem_tseitinSatCNF hc

/-- `G.edgeList` has at most `G.2.length` entries. -/
theorem length_edgeList_le (G : Graph) : G.edgeList.length ≤ G.2.length :=
  (List.eraseDupsBy_sublist _).length_le.trans List.filter_sublist.length_le

private theorem mem_perfectMatchingWires_lt (G : Graph) :
    ∀ ws ∈ G.perfectMatchingWires, ∀ w ∈ ws, w < G.edgeList.length := by
  intro ws hws w hw
  simp only [perfectMatchingWires, List.mem_map] at hws
  obtain ⟨v, _, rfl⟩ := hws
  exact List.mem_range.mp (List.mem_filter.mp hw).1

/-- Total length of all vertex-incidence lists is at most `2 * G.edgeList.length`, since each
edge contributes to at most two vertex constraints. -/
theorem sum_length_perfectMatchingWires_le (G : Graph) :
    (G.perfectMatchingWires.map List.length).sum ≤ 2 * G.edgeList.length := by
  classical
  have hvars : G.perfectMatchingWires.flatten = G.perfectMatchingInstance.vars := by
    simp only [perfectMatchingWires, perfectMatchingInstance, CSP.vars, List.flatMap_map,
      List.flatten_eq_flatMap, id_eq]
  have hsub : G.perfectMatchingInstance.vars.toFinset ⊆ Finset.range G.edgeList.length := by
    intro i hi
    exact Finset.mem_range.mpr (mem_vars_perfectMatchingInstance.mp (List.mem_toFinset.mp hi))
  rw [← List.length_flatten, hvars]
  exact (CSP.length_vars_le_mul_numVars (Graph.count_vars_perfectMatchingInstance G)).trans
    ((Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans_eq
      (by rw [Finset.card_range]))

/-- Number of gates in `G.perfectMatchingCircuit` is `O(|V| + |E|)`. -/
theorem length_perfectMatchingCircuit_le (G : Graph) :
    G.perfectMatchingCircuit.1.length ≤
      1 + 4 * G.1.toFinset.card + 6 * G.edgeList.length := by
  rw [perfectMatchingCircuit, length_seqExactlyOneAll]
  have hwlen : G.perfectMatchingWires.length = G.1.toFinset.card := by
    rw [perfectMatchingWires, List.length_map, Graph.length_distinctVertices]
  have hsum := sum_length_perfectMatchingWires_le G
  omega

/-- Number of clauses of `G.toPerfectMatchingCNF` is linear: `≤ 4 + 12 |V| + 18 |E|`. -/
theorem length_toPerfectMatchingCNF_le (G : Graph) :
    G.toPerfectMatchingCNF.length ≤
      4 + 12 * G.1.toFinset.card + 18 * G.edgeList.length := by
  rw [toPerfectMatchingCNF, length_tseitinSatCNF, List.length_nil]
  have h := length_perfectMatchingCircuit_le G
  omega

theorem vars_toPerfectMatchingCNF_subset (G : Graph) :
    G.toPerfectMatchingCNF.vars.toFinset ⊆
      Finset.range (G.edgeList.length + G.perfectMatchingCircuit.1.length) := by
  have hcode := isCodeFrom_seqExactlyOneAll G.edgeList.length (mem_perfectMatchingWires_lt G)
  have ho := snd_lt_seqExactlyOneAll G.edgeList.length (mem_perfectMatchingWires_lt G)
  have hpos : 0 < G.edgeList.length + G.perfectMatchingCircuit.1.length := by
    simp [perfectMatchingCircuit, length_seqExactlyOneAll]
  exact vars_tseitinSatCNF_subset hcode ho hpos

/-- Variable count of `G.toPerfectMatchingCNF` is linear: `≤ 1 + 4 |V| + 7 |E|`. -/
theorem numVars_toPerfectMatchingCNF_le (G : Graph) :
    G.toPerfectMatchingCNF.numVars ≤
      1 + 4 * G.1.toFinset.card + 7 * G.edgeList.length := by
  have h1 : G.toPerfectMatchingCNF.numVars ≤
      G.edgeList.length + G.perfectMatchingCircuit.1.length :=
    (Finset.card_le_card (vars_toPerfectMatchingCNF_subset G)).trans_eq (Finset.card_range _)
  have h2 := length_perfectMatchingCircuit_le G
  omega

/-- Variable count of `G.toPerfectMatchingCNF` in terms of `(encGraph G).length`. -/
theorem numVars_toPerfectMatchingCNF_le_enc (G : Graph) :
    G.toPerfectMatchingCNF.numVars ≤ 7 * (encGraph G).length + 1 := by
  have h1 := numVars_toPerfectMatchingCNF_le G
  have h2 := G.1.toFinset_card_le
  have h3 := length_edgeList_le G
  have h4 := Graph.length_vertices_add_length_edges_le_encGraph G
  omega

/-- Explicit bijection between declared-range models of `G.toPerfectMatchingCNF` and perfect
matchings of `G.induced`. -/
noncomputable def perfectMatchingCNFEquiv (G : Graph) :
    {σ : Finset.range (G.edgeList.length + G.perfectMatchingCircuit.1.length) → Bool //
      G.toPerfectMatchingCNF.eval
        (fun w =>
          if hw : w ∈ Finset.range (G.edgeList.length + G.perfectMatchingCircuit.1.length) then
            σ ⟨w, hw⟩
          else false) = true} ≃
      {M : G.induced.Subgraph // M.IsPerfectMatching} := by
  have hcode := isCodeFrom_seqExactlyOneAll G.edgeList.length (mem_perfectMatchingWires_lt G)
  have ho := snd_lt_seqExactlyOneAll G.edgeList.length (mem_perfectMatchingWires_lt G)
  let e1 := (tseitinSatAssignmentEquiv hcode ho).symm
  let e2 : {x : Fin G.edgeList.length → Bool //
        evalOutput (List.ofFn x) G.perfectMatchingCircuit.1 G.perfectMatchingCircuit.2 = true} ≃
      {S : Finset ℕ // (∀ i ∈ S, i < G.edgeList.length) ∧
        ∀ v ∈ G.1, ∃! i, i < G.edgeList.length ∧
          Graph.incident (G.edgeList.getD i (0, 0)) v = true ∧ i ∈ S} :=
    { toFun := fun x =>
        ⟨(Finset.univ.filter fun i : Fin G.edgeList.length => x.1 i = true).map
            ⟨Fin.val, Fin.val_injective⟩, by
          have hx := x.2
          dsimp only [perfectMatchingCircuit] at hx
          have hev := evalOutput_seqExactlyOneAll (x := List.ofFn x.1)
            (wss := G.perfectMatchingWires)
            (by simpa only [List.length_ofFn] using mem_perfectMatchingWires_lt G)
          simp only [List.length_ofFn] at hev
          rw [hev, List.all_eq_true] at hx
          refine ⟨fun i hi => ?_, fun v hv => ?_⟩
          · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
            exact j.isLt
          · have hv' : v ∈ G.distinctVertices := Graph.mem_distinctVertices.mpr hv
            let ws := (List.range G.edgeList.length).filter fun i =>
              Graph.incident (G.edgeList.getD i (0, 0)) v
            have hws : ws ∈ G.perfectMatchingWires := List.mem_map.mpr ⟨v, hv', rfl⟩
            have hcnt := of_decide_eq_true (hx ws hws)
            rw [List.countP_eq_length_filter, List.filter_filter,
              List.length_filter_range_eq_one_iff] at hcnt
            obtain ⟨i, ⟨hi, hp⟩, huniq⟩ := hcnt
            rw [Bool.and_eq_true, List.getD_ofFn_of_lt x.1 hi false] at hp
            refine ⟨i, ⟨hi, hp.2, Finset.mem_map.mpr
              ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1⟩, rfl⟩⟩, ?_⟩
            intro j ⟨hj, hjinc, hjs⟩
            obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hjs
            have hjxt := (Finset.mem_filter.mp hj').2
            refine huniq j'.1 ⟨j'.isLt, ?_⟩
            rw [Bool.and_eq_true, List.getD_ofFn_of_lt x.1 j'.isLt false]
            exact ⟨hjxt, hjinc⟩⟩
      invFun := fun S => ⟨fun i => decide (i.1 ∈ S.1), by
        dsimp only [perfectMatchingCircuit]
        have hev := evalOutput_seqExactlyOneAll
          (x := List.ofFn fun i : Fin G.edgeList.length => decide (i.1 ∈ S.1))
          (wss := G.perfectMatchingWires)
          (by simpa only [List.length_ofFn] using mem_perfectMatchingWires_lt G)
        simp only [List.length_ofFn] at hev
        rw [hev, List.all_eq_true]
        intro ws hws
        simp only [perfectMatchingWires, List.mem_map, Graph.mem_distinctVertices] at hws
        obtain ⟨v, hv, rfl⟩ := hws
        rw [decide_eq_true_eq, List.countP_eq_length_filter, List.filter_filter,
          List.length_filter_range_eq_one_iff]
        obtain ⟨i, ⟨hi, hinc, hiS⟩, huniq⟩ := S.2.2 v hv
        refine ⟨i, ⟨hi, ?_⟩, fun j ⟨hj, hjp⟩ => huniq j ⟨hj, ?_⟩⟩
        · rw [Bool.and_eq_true, List.getD_ofFn_of_lt _ hi false, decide_eq_true_eq]
          exact ⟨hiS, hinc⟩
        · rw [Bool.and_eq_true, List.getD_ofFn_of_lt _ hj false, decide_eq_true_eq] at hjp
          exact ⟨hjp.2, hjp.1⟩⟩
      left_inv := fun x => by
        obtain ⟨x, hx⟩ := x
        refine Subtype.ext (funext fun i => ?_)
        cases hxi : x i <;> simp [hxi]
      right_inv := fun S => by
        obtain ⟨S, hS1, hS2⟩ := S
        refine Subtype.ext (Finset.ext fun i => ?_)
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact decide_eq_true_eq.mp hj
        · intro hi
          exact ⟨⟨i, hS1 i hi⟩, decide_eq_true hi, rfl⟩ }
  exact e1.trans (e2.trans (Graph.perfectMatchingPositionsEquiv G).symm)

/-- **Exact model count of `G.toPerfectMatchingCNF` on `Finset.range (|E| + gates)`**:
equals the number of perfect matchings of `G.induced`. -/
theorem modelCountOn_toPerfectMatchingCNF (G : Graph) :
    G.toPerfectMatchingCNF.modelCountOn
        (Finset.range (G.edgeList.length + G.perfectMatchingCircuit.1.length)) =
      Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching} := by
  classical
  rw [CNF.modelCountOn, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr ((Equiv.subtypeEquivRight
    (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])).trans
    (perfectMatchingCNFEquiv G))

/-- **Exact model count of `G.toPerfectMatchingCNF`** (`modelCount`), preserving the number of
perfect matchings up to unused free wires (and exact equality when every wire occurs). -/
theorem modelCount_toPerfectMatchingCNF_mul (G : Graph) :
    2 ^ ((G.edgeList.length + G.perfectMatchingCircuit.1.length) -
        G.toPerfectMatchingCNF.numVars) *
      G.toPerfectMatchingCNF.modelCount =
      Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching} := by
  rw [← Finset.card_range (G.edgeList.length + G.perfectMatchingCircuit.1.length),
    ← CNF.modelCountOn_eq_mul_modelCount G.toPerfectMatchingCNF
      (Finset.range (G.edgeList.length + G.perfectMatchingCircuit.1.length))
      (vars_toPerfectMatchingCNF_subset G)]
  exact modelCountOn_toPerfectMatchingCNF G

theorem validDeclaredInput_toPerfectMatchingCNF (G : Graph) :
    CNF.validDeclaredInput 3
        (G.edgeList.length + G.perfectMatchingCircuit.1.length) G.toPerfectMatchingCNF =
      true := by
  rw [CNF.validDeclaredInput_eq_true_iff]
  exact ⟨fun _ hc => (length_clause_toPerfectMatchingCNF hc).le,
    vars_toPerfectMatchingCNF_subset G⟩

/-! ### Polynomial-time certificate for `Graph.toPerfectMatchingCNF` -/

private theorem seqExactlyOneStep_eq_zipIdx (nextWire seen1 seen2 : ℕ) (ws : List ℕ) :
    (seqExactlyOneStep nextWire seen1 seen2 ws).1 =
      ws.zipIdx.flatMap fun p =>
        let nw := nextWire + 3 * p.2
        let s1 := if p.2 = 0 then seen1 else nw - 1
        let s2 := if p.2 = 0 then seen2 else nw - 2
        [(.and, [s1, p.1]), (.or, [s2, nw]), (.or, [s1, p.1])] := by
  induction ws generalizing nextWire seen1 seen2 with
  | nil => rfl
  | cons w ws ih =>
    rw [seqExactlyOneStep, ih (nextWire + 3) (nextWire + 2) (nextWire + 1),
      List.zipIdx_cons', List.flatMap_cons, List.flatMap_map]
    dsimp only [Nat.mul_zero, Nat.add_zero, ↓reduceIte]
    congr 1
    refine List.flatMap_congr fun ⟨u, j⟩ _ => ?_
    dsimp only [Prod.map, id_eq]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rcases j with _ | k
    · simp only [↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]
      have h1 : nextWire + 3 - 1 = nextWire + 2 := by omega
      have h2 : nextWire + 3 - 2 = nextWire + 1 := by omega
      rw [h1, h2]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      have h0 : nextWire + 3 * (k + 1 + 1) = nextWire + 3 + 3 * (k + 1) := by omega
      rw [h0]

private theorem snd_seqExactlyOneStep (nextWire seen1 seen2 : ℕ) (ws : List ℕ) :
    (seqExactlyOneStep nextWire seen1 seen2 ws).2 =
      if ws.length = 0 then (seen1, seen2)
      else (nextWire + 3 * ws.length - 1, nextWire + 3 * ws.length - 2) := by
  induction ws generalizing nextWire seen1 seen2 with
  | nil => rfl
  | cons w ws ih =>
    rw [seqExactlyOneStep, ih]
    rcases ws with _ | ⟨w', ws'⟩
    · simp
    · simp only [List.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      congr 1 <;> omega

private theorem sum_clauseGateCost_take (wss : List (List ℕ)) (i : ℕ) :
    ((wss.take i).map fun u => 3 * u.length + 4).sum =
      3 * (wss.take i).flatten.length + 4 * (wss.take i).length := by
  induction wss.take i with
  | nil => simp
  | cons u us ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append,
      List.length_cons, ih]
    omega

private theorem seqExactlyOneFold_eq_zipIdx (n base acc : ℕ) (wss : List (List ℕ)) :
    (seqExactlyOneFold n base acc wss).1 =
      wss.zipIdx.flatMap (fun p =>
        let off := ((wss.take p.2).map fun u => 3 * u.length + 4).sum
        let curBase := base + off
        let curAcc := if p.2 = 0 then acc else n + curBase - 1
        let cl := seqExactlyOneClause n curBase p.1
        cl.1 ++ [(.and, [curAcc, cl.2])]) ∧
      (seqExactlyOneFold n base acc wss).2 =
        if wss.length = 0 then acc
        else n + base + (wss.map fun u => 3 * u.length + 4).sum - 1 := by
  induction wss generalizing base acc with
  | nil => simp [seqExactlyOneFold]
  | cons ws wss ih =>
    let cl := seqExactlyOneClause n base ws
    let nextAcc := n + base + cl.1.length
    have hlen : cl.1.length = 3 * ws.length + 3 := length_seqExactlyOneClause n base ws
    have hnext : base + cl.1.length + 1 = base + (3 * ws.length + 4) := by omega
    have hacc : nextAcc = n + (base + (3 * ws.length + 4)) - 1 := by omega
    obtain ⟨ih1, ih2⟩ := ih (base + cl.1.length + 1) nextAcc
    rw [seqExactlyOneFold]
    refine ⟨?_, ?_⟩
    · rw [ih1, List.zipIdx_cons', List.flatMap_cons, List.flatMap_map]
      dsimp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, ↓reduceIte, cl]
      congr 1
      refine List.flatMap_congr fun ⟨u, j⟩ _ => ?_
      dsimp only [Prod.map, id_eq]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      have hadd1 : base + (3 * ws.length + 4 +
          ((wss.take j).map fun u => 3 * u.length + 4).sum) =
          base + cl.1.length + 1 + ((wss.take j).map fun u => 3 * u.length + 4).sum := by
        omega
      rw [hadd1]
      rcases j with _ | k
      · simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, ↓reduceIte]
        have ha : nextAcc = n + (base + cl.1.length + 1) - 1 := by omega
        rw [ha]
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        rfl
    · rw [ih2]
      rcases wss with _ | ⟨ws', wss'⟩
      · simp [nextAcc, hlen]
      · simp only [List.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          List.map_cons, List.sum_cons]
        omega

private theorem gateClauses_eq_ite (w : ℕ) (gate : Op × List ℕ) :
    gateClauses w gate =
      let a := gate.2.getD 0 0
      let b := gate.2.getD 1 0
      if gate.1 = .const false then
        [[(w, false), (w, false), (w, false)],
         [(w, false), (w, false), (w, false)],
         [(w, false), (w, false), (w, false)]]
      else if gate.1 = .const true then
        [[(w, true), (w, true), (w, true)],
         [(w, true), (w, true), (w, true)],
         [(w, true), (w, true), (w, true)]]
      else if gate.1 = .not then
        [[(w, true), (a, true), (a, true)],
         [(w, false), (a, false), (a, false)],
         [(w, true), (a, true), (a, true)]]
      else if gate.1 = .and then
        [[(w, false), (a, true), (a, true)],
         [(w, false), (b, true), (b, true)],
         [(w, true), (a, false), (b, false)]]
      else
        [[(w, true), (a, false), (a, false)],
         [(w, true), (b, false), (b, false)],
         [(w, false), (a, true), (b, true)]] := by
  obtain ⟨op, args⟩ := gate
  cases op with
  | const v => cases v <;> rfl
  | not => rfl
  | and => rfl
  | or => rfl

private theorem list_zipIdx_eq_map_finRange {α : Type*} (l : List α) :
    l.zipIdx = (List.finRange l.length).map fun i : Fin l.length => (l[i], i.1) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.length_zipIdx] at h1
  simp [List.getElem_zipIdx]

private theorem tseitinCNF_eq_zipIdx (n : ℕ) (gates : List (Op × List ℕ)) :
    tseitinCNF n gates = gates.zipIdx.flatMap fun p => gateClauses (n + p.2) p.1 := by
  rw [tseitinCNF, list_zipIdx_eq_map_finRange, List.flatMap_map]

private theorem tidy_perfectMatchingWires :
    ComputableTidilyInPolyTime perfectMatchingWires encGraph (encList (encList encUnary)) := by
  have h : ComputableInPolyTime perfectMatchingWires encGraph (encList (encList encUnary)) := by
    have hE := computableInPolyTime_edgeList
    unfold perfectMatchingWires Graph.incident
    fun_prop
  exact h.tidy

private def seqStepClosed (nw s1 s2 : ℕ) (ws : List ℕ) : List (Op × List ℕ) :=
  ws.zipIdx.flatMap fun p =>
    let nw' := nw + 3 * p.2
    let a1 := if p.2 = 0 then s1 else nw' - 1
    let a2 := if p.2 = 0 then s2 else nw' - 2
    [(.and, [a1, p.1]), (.or, [a2, nw']), (.or, [a1, p.1])]

private theorem tidy_seqStepClosed :
    ComputableTidilyInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × List ℕ => seqStepClosed q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encList encUnary))
      (encList encGate) := by
  let E0 := encPair (encPair (encPair encUnary encUnary) encUnary) (encList encUnary)
  let E := encPair E0 (encPair encUnary encUnary)
  have hzip : ComputableTidilyInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × List ℕ => q.2.zipIdx)
      E0 (encList (encPair encUnary encUnary)) :=
    (ComputableTidilyInPolyTime.zipIdx encUnary).comp
      (ComputableTidilyInPolyTime.snd (encPair (encPair encUnary encUnary) encUnary)
        (encList encUnary))
  have hq0 := ComputableTidilyInPolyTime.fst E0 (encPair encUnary encUnary)
  have hqNw : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => q.1.1.1.1) E encUnary :=
    hq0.fst'.fst'.fst'
  have hqS1 : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => q.1.1.1.2) E encUnary :=
    hq0.fst'.fst'.snd'
  have hqS2 : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => q.1.1.2) E encUnary :=
    hq0.fst'.snd'
  have hqWire : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => q.2.1) E encUnary :=
    (ComputableTidilyInPolyTime.snd E0 (encPair encUnary encUnary)).fst'
  have hqIdx : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => q.2.2) E encUnary :=
    (ComputableTidilyInPolyTime.snd E0 (encPair encUnary encUnary)).snd'
  have hnwU : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => q.1.1.1.1 + 3 * q.2.2) E encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp
      (hqNw.prod (ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const 3).prod hqIdx)))
  have hnw : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => q.1.1.1.1 + 3 * q.2.2) E encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp hnwU
  have hzero : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => decide (q.2.2 = 0)) E encBool :=
    (ComputableInPolyTime.decide_eq' hqIdx.computableInPolyTime
      (ComputableTidilyInPolyTime.const
        (encIn := E) (encMid := encUnary) 0).computableInPolyTime).tidy
  have ha1 : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) =>
        if q.2.2 = 0 then q.1.1.1.2 else q.1.1.1.1 + 3 * q.2.2 - 1) E encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.ite_decide hzero hqS1
        (ComputableTidilyInPolyTime.unary_sub.comp
          (hnwU.prod (ComputableTidilyInPolyTime.const 1))))
  have ha2 : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) =>
        if q.2.2 = 0 then q.1.1.2 else q.1.1.1.1 + 3 * q.2.2 - 2) E encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.ite_decide hzero hqS2
        (ComputableTidilyInPolyTime.unary_sub.comp
          (hnwU.prod (ComputableTidilyInPolyTime.const 2))))
  have hw : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => q.2.1) E encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp hqWire
  have hgate (op : Op) {a b : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) → ℕ}
      (ha : ComputableTidilyInPolyTime a E encNat)
      (hb : ComputableTidilyInPolyTime b E encNat) :
      ComputableTidilyInPolyTime (fun q => (op, [a q, b q])) E encGate :=
    (ComputableTidilyInPolyTime.const op).prod
      (ha.cons' (hb.cons' (ComputableTidilyInPolyTime.const ([] : List ℕ))))
  have hitem : ComputableTidilyInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) =>
        let nw' := q.1.1.1.1 + 3 * q.2.2
        let a1 := if q.2.2 = 0 then q.1.1.1.2 else nw' - 1
        let a2 := if q.2.2 = 0 then q.1.1.2 else nw' - 2
        ([(.and, [a1, q.2.1]), (.or, [a2, nw']), (.or, [a1, q.2.1])] : List (Op × List ℕ)))
      E (encList encGate) :=
    (hgate .and ha1 hw).cons'
      ((hgate .or ha2 hnw).cons'
        ((hgate .or ha1 hw).cons'
          (ComputableTidilyInPolyTime.const ([] : List (Op × List ℕ)))))
  exact ComputableTidilyInPolyTime.flatMapWithInput hzip hitem

private theorem tidy_seqExactlyOneClause :
    ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ => (seqExactlyOneClause q.1.1 q.1.2 q.2).1)
      (encPair (encPair encUnary encUnary) (encList encUnary)) (encList encGate) := by
  let E2 := encPair (encPair encUnary encUnary) (encList encUnary)
  have hq2 := ComputableTidilyInPolyTime.fst (encPair encUnary encUnary) (encList encUnary)
  have hq2N : ComputableTidilyInPolyTime (fun q : (ℕ × ℕ) × List ℕ => q.1.1) E2 encUnary :=
    hq2.fst'
  have hq2B : ComputableTidilyInPolyTime (fun q : (ℕ × ℕ) × List ℕ => q.1.2) E2 encUnary :=
    hq2.snd'
  have hq2W : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ => q.2) E2 (encList encUnary) :=
    ComputableTidilyInPolyTime.snd (encPair encUnary encUnary) (encList encUnary)
  have hq2WLen : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ => q.2.length) E2 encUnary :=
    (ComputableTidilyInPolyTime.length_list encUnary).comp hq2W
  have hq2NB : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ => q.1.1 + q.1.2) E2 encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp (hq2N.prod hq2B)
  have hq2NB1 : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ => q.1.1 + q.1.2 + 1) E2 encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp (hq2NB.prod (ComputableTidilyInPolyTime.const 1))
  have hq2NW : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ => q.1.1 + q.1.2 + 1 + 3 * q.2.length) E2 encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp
      (hq2NB1.prod (ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const 3).prod hq2WLen)))
  have hq2W0 : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ => decide (q.2.length = 0)) E2 encBool :=
    (ComputableInPolyTime.decide_eq' hq2WLen.computableInPolyTime
      (ComputableTidilyInPolyTime.const
        (encIn := E2) (encMid := encUnary) 0).computableInPolyTime).tidy
  have hs : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ =>
        seqStepClosed (q.1.1 + q.1.2 + 1) (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2)
      E2 (encList encGate) :=
    tidy_seqStepClosed.comp (((hq2NB1.prod hq2NB).prod hq2NB).prod hq2W)
  have hseen (off : ℕ) : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ =>
        if q.2.length = 0 then q.1.1 + q.1.2
        else q.1.1 + q.1.2 + 1 + 3 * q.2.length - off) E2 encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.ite_decide hq2W0 hq2NB
        (ComputableTidilyInPolyTime.unary_sub.comp
          (hq2NW.prod (ComputableTidilyInPolyTime.const off))))
  have hnot : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ =>
        (.not, [(seqExactlyOneStep (q.1.1 + q.1.2 + 1)
          (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2).2.2]))
      E2 encGate := by
    have harg : ComputableTidilyInPolyTime
        (fun q : (ℕ × ℕ) × List ℕ =>
          (seqExactlyOneStep (q.1.1 + q.1.2 + 1)
            (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2).2.2) E2 encNat :=
      (hseen 2).of_enc_eq fun q => by
        rw [snd_seqExactlyOneStep]
        split_ifs <;> rfl
    exact (ComputableTidilyInPolyTime.const Op.not).prod
      (harg.cons' (ComputableTidilyInPolyTime.const ([] : List ℕ)))
  have hand : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ =>
        (.and, [(seqExactlyOneStep (q.1.1 + q.1.2 + 1)
          (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2).2.1,
          q.1.1 + q.1.2 + 1 + 3 * q.2.length]))
      E2 encGate := by
    have hs1 : ComputableTidilyInPolyTime
        (fun q : (ℕ × ℕ) × List ℕ =>
          (seqExactlyOneStep (q.1.1 + q.1.2 + 1)
            (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2).2.1) E2 encNat :=
      (hseen 1).of_enc_eq fun q => by
        rw [snd_seqExactlyOneStep]
        split_ifs <;> rfl
    have hnw : ComputableTidilyInPolyTime
        (fun q : (ℕ × ℕ) × List ℕ => q.1.1 + q.1.2 + 1 + 3 * q.2.length) E2 encNat :=
      ComputableTidilyInPolyTime.unary_to_binary.comp hq2NW
    exact (ComputableTidilyInPolyTime.const Op.and).prod
      (hs1.cons' (hnw.cons' (ComputableTidilyInPolyTime.const ([] : List ℕ))))
  have hc : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ =>
        [(.const false, [])] ++
          seqStepClosed (q.1.1 + q.1.2 + 1) (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2 ++
          [(.not, [(seqExactlyOneStep (q.1.1 + q.1.2 + 1)
            (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2).2.2]),
           (.and, [(seqExactlyOneStep (q.1.1 + q.1.2 + 1)
            (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2).2.1,
            q.1.1 + q.1.2 + 1 + 3 * q.2.length])])
      E2 (encList encGate) := by
    have ha := (ComputableTidilyInPolyTime.listAppend encGate).comp
      ((ComputableTidilyInPolyTime.const ([(.const false, [])] : List (Op × List ℕ))).prod hs)
    have htail : ComputableTidilyInPolyTime
        (fun q : (ℕ × ℕ) × List ℕ =>
          [(.not, [(seqExactlyOneStep (q.1.1 + q.1.2 + 1)
            (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2).2.2]),
           (.and, [(seqExactlyOneStep (q.1.1 + q.1.2 + 1)
            (q.1.1 + q.1.2) (q.1.1 + q.1.2) q.2).2.1,
            q.1.1 + q.1.2 + 1 + 3 * q.2.length])])
        E2 (encList encGate) :=
      hnot.cons' (hand.cons' (ComputableTidilyInPolyTime.const ([] : List (Op × List ℕ))))
    exact (ComputableTidilyInPolyTime.listAppend encGate).comp (ha.prod htail)
  refine hc.of_enc_eq fun q => congrArg (encList encGate) ?_
  rw [seqExactlyOneClause]
  dsimp only
  rw [length_seqExactlyOneStep, seqExactlyOneStep_eq_zipIdx, seqStepClosed]

private theorem tidy_perfectMatchingBlock :
    ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) =>
        let take := q.1.perfectMatchingWires.take q.2.2
        let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
        let curAcc := if q.2.2 = 0 then q.1.edgeList.length else q.1.edgeList.length + curBase - 1
        let cl := seqExactlyOneClause q.1.edgeList.length curBase q.2.1
        cl.1 ++ [(.and, [curAcc, cl.2])])
      (encPair encGraph (encPair (encList encUnary) encUnary)) (encList encGate) := by
  let P := encPair encGraph (encPair (encList encUnary) encUnary)
  have hN : ComputableTidilyInPolyTime (fun G : Graph => G.edgeList.length) encGraph encUnary :=
    (ComputableTidilyInPolyTime.length_list (encPair encNat encNat)).comp
      computableInPolyTime_edgeList.tidy
  have hG := ComputableTidilyInPolyTime.fst encGraph (encPair (encList encUnary) encUnary)
  have hP2 := ComputableTidilyInPolyTime.snd encGraph (encPair (encList encUnary) encUnary)
  have hNq : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) => q.1.edgeList.length) P encUnary :=
    hN.comp hG
  have hIdxq : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) => q.2.2) P encUnary :=
    hP2.snd'
  have hWsq : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) => q.2.1) P (encList encUnary) :=
    hP2.fst'
  have htake : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) => q.1.perfectMatchingWires.take q.2.2)
      P (encList (encList encUnary)) :=
    ComputableTidilyInPolyTime.listTakeWithInput (tidy_perfectMatchingWires.comp hG) hIdxq
  have htakeFl : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) => (q.1.perfectMatchingWires.take q.2.2).flatten)
      P (encList encUnary) :=
    (ComputableTidilyInPolyTime.flatten encUnary).comp htake
  have hbase : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) =>
        1 + (3 * (q.1.perfectMatchingWires.take q.2.2).flatten.length +
          4 * (q.1.perfectMatchingWires.take q.2.2).length)) P encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.const 1).prod
        (ComputableTidilyInPolyTime.unary_add.comp
          ((ComputableTidilyInPolyTime.unary_mul.comp
            ((ComputableTidilyInPolyTime.const 3).prod
              ((ComputableTidilyInPolyTime.length_list encUnary).comp htakeFl))).prod
            (ComputableTidilyInPolyTime.unary_mul.comp
              ((ComputableTidilyInPolyTime.const 4).prod
                ((ComputableTidilyInPolyTime.length_list (encList encUnary)).comp htake))))))
  have hclq : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) =>
        let take := q.1.perfectMatchingWires.take q.2.2
        let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
        (seqExactlyOneClause q.1.edgeList.length curBase q.2.1).1) P (encList encGate) :=
    tidy_seqExactlyOneClause.comp ((hNq.prod hbase).prod hWsq)
  have hidx0 : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) => decide (q.2.2 = 0)) P encBool :=
    (ComputableInPolyTime.decide_eq' hIdxq.computableInPolyTime
      (ComputableTidilyInPolyTime.const
        (encIn := P) (encMid := encUnary) 0).computableInPolyTime).tidy
  have hacc : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) =>
        let take := q.1.perfectMatchingWires.take q.2.2
        let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
        if q.2.2 = 0 then q.1.edgeList.length else q.1.edgeList.length + curBase - 1)
      P encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.ite_decide hidx0 hNq
        (ComputableTidilyInPolyTime.unary_sub.comp
          ((ComputableTidilyInPolyTime.unary_add.comp (hNq.prod hbase)).prod
            (ComputableTidilyInPolyTime.const 1))))
  have hcl2 : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) =>
        let take := q.1.perfectMatchingWires.take q.2.2
        let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
        (seqExactlyOneClause q.1.edgeList.length curBase q.2.1).2) P encNat := by
    have hu : ComputableTidilyInPolyTime
        (fun q : Graph × (List ℕ × ℕ) =>
          let take := q.1.perfectMatchingWires.take q.2.2
          let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
          q.1.edgeList.length + curBase + 3 * q.2.1.length + 2) P encUnary :=
      ComputableTidilyInPolyTime.unary_add.comp
        ((ComputableTidilyInPolyTime.unary_add.comp
          ((ComputableTidilyInPolyTime.unary_add.comp (hNq.prod hbase)).prod
            (ComputableTidilyInPolyTime.unary_mul.comp
              ((ComputableTidilyInPolyTime.const 3).prod
                ((ComputableTidilyInPolyTime.length_list encUnary).comp hWsq))))).prod
          (ComputableTidilyInPolyTime.const 2))
    exact (ComputableTidilyInPolyTime.unary_to_binary.comp hu).of_enc_eq fun q => by
      rw [snd_seqExactlyOneClause]
      rfl
  have handGate : ComputableTidilyInPolyTime
      (fun q : Graph × (List ℕ × ℕ) =>
        let take := q.1.perfectMatchingWires.take q.2.2
        let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
        let curAcc := if q.2.2 = 0 then q.1.edgeList.length else q.1.edgeList.length + curBase - 1
        let cl := seqExactlyOneClause q.1.edgeList.length curBase q.2.1
        [(.and, [curAcc, cl.2])]) P (encList encGate) :=
    ((ComputableTidilyInPolyTime.const Op.and).prod
      (hacc.cons' (hcl2.cons' (ComputableTidilyInPolyTime.const ([] : List ℕ))))).cons'
      (ComputableTidilyInPolyTime.const ([] : List (Op × List ℕ)))
  exact (ComputableTidilyInPolyTime.listAppend encGate).comp (hclq.prod handGate)

private theorem tidy_perfectMatchingCircuit :
    ComputableTidilyInPolyTime (fun G : Graph => G.perfectMatchingCircuit)
      encGraph (encPair (encList encGate) encUnary) := by
  have hN : ComputableTidilyInPolyTime (fun G : Graph => G.edgeList.length) encGraph encUnary :=
    (ComputableTidilyInPolyTime.length_list (encPair encNat encNat)).comp
      computableInPolyTime_edgeList.tidy
  have hzip : ComputableTidilyInPolyTime
      (fun G : Graph => G.perfectMatchingWires.zipIdx)
      encGraph (encList (encPair (encList encUnary) encUnary)) :=
    (ComputableTidilyInPolyTime.zipIdx (encList encUnary)).comp tidy_perfectMatchingWires
  have hgates : ComputableTidilyInPolyTime
      (fun G : Graph => G.perfectMatchingCircuit.1) encGraph (encList encGate) := by
    have hfold : ComputableTidilyInPolyTime
        (fun G : Graph => (Op.const true, ([] : List ℕ)) ::
          (G.perfectMatchingWires.zipIdx.flatMap fun p =>
            let take := G.perfectMatchingWires.take p.2
            let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
            let curAcc := if p.2 = 0 then G.edgeList.length else G.edgeList.length + curBase - 1
            let cl := seqExactlyOneClause G.edgeList.length curBase p.1
            cl.1 ++ [(.and, [curAcc, cl.2])]))
        encGraph (encList encGate) :=
      (ComputableTidilyInPolyTime.const (Op.const true, ([] : List ℕ))).cons'
        (ComputableTidilyInPolyTime.flatMapWithInput hzip tidy_perfectMatchingBlock)
    refine hfold.of_enc_eq fun G => congrArg (encList encGate) ?_
    rw [perfectMatchingCircuit, seqExactlyOneAll]
    dsimp only
    congr 1
    rw [(seqExactlyOneFold_eq_zipIdx G.edgeList.length 1 G.edgeList.length
      G.perfectMatchingWires).1]
    refine List.flatMap_congr fun p _ => ?_
    rw [sum_clauseGateCost_take]
  have hout : ComputableTidilyInPolyTime
      (fun G : Graph => G.perfectMatchingCircuit.2) encGraph encUnary := by
    have hfl : ComputableTidilyInPolyTime
        (fun G : Graph => G.perfectMatchingWires.flatten) encGraph (encList encUnary) :=
      (ComputableTidilyInPolyTime.flatten encUnary).comp tidy_perfectMatchingWires
    have hwlen : ComputableTidilyInPolyTime
        (fun G : Graph => G.perfectMatchingWires.length) encGraph encUnary :=
      (ComputableTidilyInPolyTime.length_list (encList encUnary)).comp tidy_perfectMatchingWires
    have hsumU : ComputableTidilyInPolyTime
        (fun G : Graph =>
          3 * G.perfectMatchingWires.flatten.length + 4 * G.perfectMatchingWires.length)
        encGraph encUnary :=
      ComputableTidilyInPolyTime.unary_add.comp
        ((ComputableTidilyInPolyTime.unary_mul.comp
          ((ComputableTidilyInPolyTime.const 3).prod
            ((ComputableTidilyInPolyTime.length_list encUnary).comp hfl))).prod
          (ComputableTidilyInPolyTime.unary_mul.comp
            ((ComputableTidilyInPolyTime.const 4).prod hwlen)))
    have hw0 : ComputableTidilyInPolyTime
        (fun G : Graph => decide (G.perfectMatchingWires.length = 0)) encGraph encBool :=
      (ComputableInPolyTime.decide_eq' hwlen.computableInPolyTime
        (ComputableTidilyInPolyTime.const (encIn := encGraph)
          (encMid := encUnary) 0).computableInPolyTime).tidy
    have hu : ComputableTidilyInPolyTime
        (fun G : Graph =>
          if G.perfectMatchingWires.length = 0 then G.edgeList.length
          else G.edgeList.length + 1 +
            (3 * G.perfectMatchingWires.flatten.length + 4 * G.perfectMatchingWires.length) - 1)
        encGraph encUnary :=
      ComputableTidilyInPolyTime.ite_decide hw0 hN
        (ComputableTidilyInPolyTime.unary_sub.comp
          ((ComputableTidilyInPolyTime.unary_add.comp
            ((ComputableTidilyInPolyTime.unary_add.comp
              (hN.prod (ComputableTidilyInPolyTime.const 1))).prod hsumU)).prod
            (ComputableTidilyInPolyTime.const 1)))
    refine hu.of_enc_eq fun G => ?_
    rw [perfectMatchingCircuit, seqExactlyOneAll,
      (seqExactlyOneFold_eq_zipIdx G.edgeList.length 1 G.edgeList.length
        G.perfectMatchingWires).2]
    have hsum : (G.perfectMatchingWires.map fun u => 3 * u.length + 4).sum =
        3 * G.perfectMatchingWires.flatten.length + 4 * G.perfectMatchingWires.length := by
      have ht := sum_clauseGateCost_take G.perfectMatchingWires G.perfectMatchingWires.length
      rwa [List.take_length] at ht
    rw [hsum]
  exact hgates.prod hout

private theorem tidy_gateClauses :
    ComputableTidilyInPolyTime (fun p : ℕ × (Op × List ℕ) => gateClauses p.1 p.2)
      (encPair encUnary encGate) (encList (encClause encNat)) := by
  have hOpTag (op : Op) : ComputableInPolyTime
      (fun p : ℕ × (Op × List ℕ) => decide (p.2.1 = op))
      (encPair encUnary encGate) encBool :=
    (ComputableInPolyTime.of_finite (encIn := encOp) (encOut := encBool)
      fun x => decide (x = op)).comp
      (ComputableInPolyTime.snd encUnary encGate).fst'
  have hw : ComputableInPolyTime (fun p : ℕ × (Op × List ℕ) => p.1)
      (encPair encUnary encGate) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.fst encUnary encGate)
  have hargs : ComputableInPolyTime (fun p : ℕ × (Op × List ℕ) => p.2.2)
      (encPair encUnary encGate) (encList encNat) :=
    (ComputableInPolyTime.snd encUnary encGate).snd'
  have ha : ComputableInPolyTime (fun p : ℕ × (Op × List ℕ) => p.2.2.getD 0 0)
      (encPair encUnary encGate) encNat :=
    ComputableInPolyTime.listGetD_binary (encA := encNat) (encL := encList encNat) 0 hargs
      (ComputableInPolyTime.const 0)
  have hb : ComputableInPolyTime (fun p : ℕ × (Op × List ℕ) => p.2.2.getD 1 0)
      (encPair encUnary encGate) encNat :=
    ComputableInPolyTime.listGetD_binary (encA := encNat) (encL := encList encNat) 0 hargs
      (ComputableInPolyTime.const 1)
  have hcl3 (x y z : ℕ × (Op × List ℕ) → ℕ) (sx sy sz : Bool)
      (hx : ComputableInPolyTime x (encPair encUnary encGate) encNat)
      (hy : ComputableInPolyTime y (encPair encUnary encGate) encNat)
      (hz : ComputableInPolyTime z (encPair encUnary encGate) encNat) :
      ComputableInPolyTime
        (fun p => ([(x p, sx), (y p, sy), (z p, sz)] : Clause ℕ))
        (encPair encUnary encGate) (encClause encNat) :=
    (hx.prod (ComputableInPolyTime.const sx)).cons'
      ((hy.prod (ComputableInPolyTime.const sy)).cons'
        ((hz.prod (ComputableInPolyTime.const sz)).cons'
          (ComputableInPolyTime.const ([] : Clause ℕ))))
  have hcnf3 (c1 c2 c3 : ℕ × (Op × List ℕ) → Clause ℕ)
      (hc1 : ComputableInPolyTime c1 (encPair encUnary encGate) (encClause encNat))
      (hc2 : ComputableInPolyTime c2 (encPair encUnary encGate) (encClause encNat))
      (hc3 : ComputableInPolyTime c3 (encPair encUnary encGate) (encClause encNat)) :
      ComputableInPolyTime (fun p => ([c1 p, c2 p, c3 p] : CNF ℕ))
        (encPair encUnary encGate) (encList (encClause encNat)) :=
    hc1.cons' (hc2.cons' (hc3.cons' (ComputableInPolyTime.const ([] : CNF ℕ))))
  have hcf := hcnf3 _ _ _ (hcl3 _ _ _ false false false hw hw hw)
    (hcl3 _ _ _ false false false hw hw hw) (hcl3 _ _ _ false false false hw hw hw)
  have hct := hcnf3 _ _ _ (hcl3 _ _ _ true true true hw hw hw)
    (hcl3 _ _ _ true true true hw hw hw) (hcl3 _ _ _ true true true hw hw hw)
  have hcnot := hcnf3 _ _ _ (hcl3 _ _ _ true true true hw ha ha)
    (hcl3 _ _ _ false false false hw ha ha) (hcl3 _ _ _ true true true hw ha ha)
  have hcand := hcnf3 _ _ _ (hcl3 _ _ _ false true true hw ha ha)
    (hcl3 _ _ _ false true true hw hb hb) (hcl3 _ _ _ true false false hw ha hb)
  have hcor := hcnf3 _ _ _ (hcl3 _ _ _ true false false hw ha ha)
    (hcl3 _ _ _ true false false hw hb hb) (hcl3 _ _ _ false true true hw ha hb)
  have hcomp := ComputableInPolyTime.ite (hOpTag (.const false)) hcf
    (ComputableInPolyTime.ite (hOpTag (.const true)) hct
      (ComputableInPolyTime.ite (hOpTag .not) hcnot
        (ComputableInPolyTime.ite (hOpTag .and) hcand hcor)))
  exact (hcomp.of_enc_eq fun p => by
    rw [gateClauses_eq_ite]
    simp only [decide_eq_true_eq]).tidy

/-- Constructing `G.toPerfectMatchingCNF` from `encGraph` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toPerfectMatchingCNF :
    ComputableInPolyTime toPerfectMatchingCNF encGraph encCNF := by
  have hN : ComputableTidilyInPolyTime (fun G : Graph => G.edgeList.length) encGraph encUnary :=
    (ComputableTidilyInPolyTime.length_list (encPair encNat encNat)).comp
      computableInPolyTime_edgeList.tidy
  have hzipG : ComputableTidilyInPolyTime
      (fun G : Graph => G.perfectMatchingCircuit.1.zipIdx)
      encGraph (encList (encPair encGate encUnary)) :=
    (ComputableTidilyInPolyTime.zipIdx encGate).comp tidy_perfectMatchingCircuit.fst'
  have hP2 := ComputableTidilyInPolyTime.snd encGraph (encPair encGate encUnary)
  have hbody : ComputableTidilyInPolyTime
      (fun q : Graph × ((Op × List ℕ) × ℕ) => gateClauses (q.1.edgeList.length + q.2.2) q.2.1)
      (encPair encGraph (encPair encGate encUnary)) (encList (encClause encNat)) :=
    tidy_gateClauses.comp
      ((ComputableTidilyInPolyTime.unary_add.comp
        ((hN.comp (ComputableTidilyInPolyTime.fst encGraph (encPair encGate encUnary))).prod
          hP2.snd')).prod hP2.fst')
  have hts : ComputableTidilyInPolyTime
      (fun G : Graph => tseitinCNF G.edgeList.length G.perfectMatchingCircuit.1)
      encGraph encCNF :=
    (ComputableTidilyInPolyTime.flatMapWithInput
      (f := fun (G : Graph) (p : (Op × List ℕ) × ℕ) => gateClauses (G.edgeList.length + p.2) p.1)
      hzipG hbody).of_enc_eq fun G =>
        congrArg (encList (encClause encNat))
          (tseitinCNF_eq_zipIdx G.edgeList.length G.perfectMatchingCircuit.1)
  have hoBin : ComputableTidilyInPolyTime
      (fun G : Graph => G.perfectMatchingCircuit.2) encGraph encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp tidy_perfectMatchingCircuit.snd'
  have hoLit : ComputableTidilyInPolyTime
      (fun G : Graph => (G.perfectMatchingCircuit.2, true))
      encGraph (encPair encNat encBool) :=
    hoBin.prod (ComputableTidilyInPolyTime.const true)
  have hunit : ComputableTidilyInPolyTime
      (fun G : Graph => unitClause (G.perfectMatchingCircuit.2, true))
      encGraph (encClause encNat) := by
    unfold unitClause
    exact hoLit.cons' (hoLit.cons' (hoLit.cons'
      (ComputableTidilyInPolyTime.const ([] : Clause ℕ))))
  exact (hunit.cons' hts).computableInPolyTime.of_enc_eq fun G =>
    congrArg encCNF (by simp [toPerfectMatchingCNF, tseitinSatCNF])

end Cslib.Complexity.Graph
