/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.DomainInterpretation
public import CslibFrontier.Logics.FirstOrder.Ordered.TransitiveClosure
public import Mathlib.ModelTheory.Graph
import CslibFrontier.Foundations.Relation.Transport

/-!
# Canonical ordered directed reachability

Over Mathlib's language of graphs `FirstOrder.Language.graph`, a structure on `Fin n` interprets
`Language.adj` as an arbitrary binary relation: directed edges and self-loops are permitted,
matching Immerman's binary edge relation `E(x, y)`. On canonically ordered structures (`Fin n` with
`2 ≤ n`), `Cslib.Logic.FO.Ordered.Reach` (`REACH` of [Immerman1999, Section 3.3 and Theorem 3.16])
asks whether the greatest vertex `n - 1` (`max`) is reachable from `0` by a directed path of zero
or more edges.

This module defines `Reach`, its canonical vocabulary `graphVocabulary`, its positive FO(TC)
definability (`posTCDefinable_Reach`), pullback of `PosTCDefinable` along ordered first-order
reductions to `Reach` (`PosTCDefinable.of_reduces_Reach`), a reusable full-tuple sandwich
interpretation (`boundedReachInterpretation`) turning reachability between `d`-tuples satisfying
source, step and target formulas into `Reach` on `Fin (n ^ (d + 2))`, and endpoint normalization
between `Reach` and arbitrary marked `s`–`t` reachability `STReach` (including `s = t`). Native
`NL` membership, the `STCON` bridge, and unconditional ordered first-order `NL`-completeness are in
`CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reachability`.

## Main definitions

* `Cslib.Logic.FO.Ordered.Structure.maxElem`: the greatest element `M.size - 1` of a canonically
  ordered structure.
* `Cslib.Logic.FO.Ordered.graphVocabulary`: canonical vocabulary for `FirstOrder.Language.graph`.
* `Cslib.Logic.FO.Ordered.graphAdj`, `Cslib.Logic.FO.Ordered.Reach`: directed edge relation and
  canonical `0`-to-`max` reachability query on ordered graphs.
* `Cslib.Logic.FO.Ordered.reachSentence`: positive FO(TC) sentence defining `Reach`.
* `Cslib.Logic.FO.Ordered.boundedReachInterpretation`: full-tuple interpretation reducing
  reachability between `d`-tuples from a source formula to a target formula into `Reach`.
* `Cslib.Logic.FO.Ordered.STMarkerRelation`, `Cslib.Logic.FO.Ordered.stMarkerLanguage`,
  `Cslib.Logic.FO.Ordered.stGraphLanguage`, `Cslib.Logic.FO.Ordered.stGraphVocabulary`: directed
  graphs expanded by unary source and target markers, with their canonical vocabulary.
* `Cslib.Logic.FO.Ordered.STReach`, `Cslib.Logic.FO.Ordered.mkMarkedGraph`: ordered `s`–`t`
  reachability query with marked endpoints and helper constructor for vertex pairs `(s, t)`.
* `Cslib.Logic.FO.Ordered.stReachToReachInterpretation`,
  `Cslib.Logic.FO.Ordered.reachToSTReachInterpretation`: full-tuple interpretations normalizing
  between `STReach` and `Reach`.

## Main results

* `Cslib.Logic.FO.Ordered.posTCDefinable_Reach`, `Cslib.Logic.FO.Ordered.tcDefinable_Reach`:
  `Reach` is definable in positive FO(TC).
* `Cslib.Logic.FO.Ordered.PosTCDefinable.of_reduces_Reach`,
  `Cslib.Logic.FO.Ordered.TCDefinable.of_reduces_Reach`: ordered reductions to `Reach` pull back
  positive FO(TC) definability.
* `Cslib.Logic.FO.Ordered.mem_Reach_boundedReachInterpretation`: exact reachability characterization
  for `boundedReachInterpretation`.
* `Cslib.Logic.FO.Ordered.stReach_reduces_Reach`, `Cslib.Logic.FO.Ordered.reach_reduces_STReach`:
  bidirectional ordered first-order reductions between `STReach` and `Reach`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 3.3, Theorem 3.16 and
  Exercise 3.20 (pp. 64–66).
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language

/-- Every canonically ordered structure has positive universe size (`2 ≤ M.size`), so `0 : M` is
available via `OfNat`. -/
instance Structure.instNeZeroSize {L : Language} (M : Structure L) : NeZero M.size :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt M.size_ge_two)⟩

/-- The greatest element `M.size - 1` (`max`) of a canonically ordered structure `M`. -/
abbrev Structure.maxElem {L : Language} (M : Structure L) : M :=
  ⟨M.size - 1, NumericFunction.index_lt M.size_ge_two .max⟩

private theorem realize_zero_eq {L : Language} {M : Structure L} {α : Type} (v : α → Fin M.size) :
    (zero L).realize v = (0 : Fin M.size) := rfl

private theorem realize_max_eq {L : Language} {M : Structure L} {α : Type} (v : α → Fin M.size) :
    (max L).realize v = M.maxElem := rfl

/-- The canonical vocabulary enumerating the binary edge symbol `Language.adj`. -/
@[expose] def graphVocabulary : Vocabulary Language.graph where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, Language.adj⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun ⟨_, .adj⟩ => rfl }

/-- The directed edge relation of an ordered graph structure. `Language.graph.Structure (Fin n)`
interprets `Language.adj` as an arbitrary binary relation, so directed arcs and self-loops
are permitted, matching Immerman's `E(x, y)`. -/
@[expose] def graphAdj (M : Structure Language.graph) (x y : M) : Prop :=
  Language.Structure.RelMap Language.adj ![x, y]

/-- **Canonical ordered reachability** (`REACH` of [Immerman1999, Section 3.3 and Theorem 3.16]):
an ordered directed graph structure on `Fin n` (`2 ≤ n`), possibly with self-loops, belongs to
`Reach` when its greatest vertex `n - 1` (`max`) is reachable from `0` by a directed path of zero
or more edges. -/
@[expose] def Reach : Query Language.graph :=
  {M | Relation.ReflTransGen (graphAdj M) 0 M.maxElem}

theorem mem_Reach {M : Structure Language.graph} :
    M ∈ Reach ↔ Relation.ReflTransGen (graphAdj M) 0 M.maxElem :=
  Iff.rfl

/-! ### Positive FO(TC) definability and pullback -/

/-- The positive width-1 FO(TC) sentence expressing reachability from `zero` to `max` along
`Language.adj`. -/
@[expose] def reachSentence : Operator.Formula (language Language.graph) TC.shape [] Empty :=
  TC.tc
    (.ofFO (Relations.formula₂
      ((LHom.sumInl : Language.graph →ᴸ language Language.graph).onRelation Language.adj)
      (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))))
    (TC.pair ![zero Language.graph] ![max Language.graph])

theorem positive_reachSentence : TC.Positive reachSentence true :=
  ⟨rfl, trivial⟩

theorem realize_reachSentence (M : Structure Language.graph) :
    M ∈ Reach ↔
      reachSentence.Realize (M := M) TC.interpretation Operator.RelEnv.empty Empty.elim := by
  have hedge : ∀ us vs : Fin 1 → Fin M.size,
      (Operator.Formula.ofFO (shape := TC.shape) (Γ := [])
        (Relations.formula₂
          ((LHom.sumInl : Language.graph →ᴸ language Language.graph).onRelation Language.adj)
          (Term.var (Sum.inr (0 : Fin (2 * 1))))
          (Term.var (Sum.inr (1 : Fin (2 * 1)))))).Realize
        TC.interpretation Operator.RelEnv.empty (Sum.elim Empty.elim (TC.pair us vs)) ↔
      graphAdj M (us 0) (vs 0) := by
    intro us vs
    simp only [Operator.Formula.realize_ofFO, Formula.realize_rel₂]
    rfl
  rw [reachSentence, TC.realize_tc_pair, mem_Reach]
  simp only [Matrix.cons_val_fin_one]
  constructor
  · intro h
    exact Relation.ReflTransGen.lift (fun x : Fin M.size => fun _ : Fin 1 => x)
      (fun a b hab => (hedge _ _).mpr hab) _ _ h
  · intro h
    exact Relation.ReflTransGen.lift (fun us : Fin 1 → Fin M.size => us 0)
      (fun us vs huv => (hedge us vs).mp huv) _ _ h

/-- **`Reach` is definable in positive FO(TC).** -/
theorem posTCDefinable_Reach : PosTCDefinable Reach :=
  ⟨reachSentence, positive_reachSentence, realize_reachSentence⟩

/-- **`Reach` is definable in FO(TC).** -/
theorem tcDefinable_Reach : TCDefinable Reach :=
  posTCDefinable_Reach.tcDefinable

private theorem reflTransGen_subtype_iff {α : Type*} {P : α → Prop} {R : α → α → Prop}
    (x y : {a : α // P a}) :
    Relation.ReflTransGen (fun u w => (P u ∧ P w) ∧ R u w) x.val y.val ↔
      Relation.ReflTransGen (fun u w : {a : α // P a} => R u.val w.val) x y := by
  have hrange (z : α)
      (hz : Relation.ReflTransGen (fun u w => (P u ∧ P w) ∧ R u w) x.val z) :
      ∃ w : {a : α // P a}, w.val = z := by
    cases hz with
    | refl => exact ⟨x, rfl⟩
    | tail _ hstep =>
      rcases hstep with ⟨⟨_, hzP⟩, _⟩
      exact ⟨⟨z, hzP⟩, rfl⟩
  have hrel : (fun u w : {a : α // P a} => (P u.val ∧ P w.val) ∧ R u.val w.val) =
      fun u w => R u.val w.val :=
    funext₂ fun u w => propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨u.property, w.property⟩, h⟩⟩
  rw [← hrel]
  exact (Relation.reflTransGen_onFun_iff Subtype.val_injective hrange).symm

/-- Pull `Reach` back along a certified ordered domain interpretation into one positive FO(TC)
sentence over the source language. -/
private noncomputable def pullbackReachSentence {L : Language} {k : ℕ}
    {I : DomainInterpretation L Language.graph k} (C : I.Certificate) :
    Operator.Formula (language L) TC.shape [] Empty :=
  Operator.Formula.exs (2 * k)
    (.conj (.ofFO ((I.domain.relabel fun j => .inr (TC.left _root_.id j)) ⊓
        ((C.const .zero).relabel fun j => .inr (TC.left _root_.id j))))
      (.conj (.ofFO ((I.domain.relabel fun j => .inr (TC.right _root_.id j)) ⊓
          ((C.const .max).relabel fun j => .inr (TC.right _root_.id j))))
        (TC.tc (k := k)
          (.ofFO (((I.domain.relabel fun j => .inr (TC.left _root_.id j)) ⊓
              (I.domain.relabel fun j => .inr (TC.right _root_.id j))) ⊓
            (I.rel Language.adj).relabel fun p =>
              if p.1 = 0 then .inr (TC.left _root_.id p.2)
              else .inr (TC.right _root_.id p.2)))
          (fun i => .var (.inr i)))))

/-- **Ordered first-order reductions to `Reach` pull back positive FO(TC) definability.** -/
theorem PosTCDefinable.of_reduces_Reach {L : Language} {K : Query L} (h : Reduces K Reach) :
    PosTCDefinable K := by
  obtain ⟨_, ⟨k, I, hI, ⟨C⟩, rfl⟩, hK⟩ := h
  refine ⟨pullbackReachSentence C, ?_, fun M => (hK M).trans ?_⟩
  · rw [pullbackReachSentence, TC.positive_exs]
    exact ⟨trivial, trivial, rfl, trivial⟩
  · let zeroIdx : I.map hI M := 0
    let maxIdx : I.map hI M := (I.map hI M).maxElem
    let e : {x : Fin k → Fin M.size // I.domain.Realize x} ≃ I.map hI M :=
      { toFun := fun x => I.rank M x.val x.property
        invFun := fun i => ⟨I.unrank M i, I.realize_domain_unrank i⟩
        left_inv := fun x => Subtype.ext (I.unrank_rank x.property)
        right_inv := I.rank_unrank }
    have hconst (c : NumericFunction 0) (idx : I.map hI M)
        (hidx : idx.val = c.index (I.card M)) (u : Fin k → Fin M.size) :
        I.domain.Realize u ∧ (C.const c).Realize u ↔ u = I.unrank M idx := by
      constructor
      · rintro ⟨hu, hc⟩
        rw [← I.unrank_rank hu] at hc ⊢
        exact congrArg (I.unrank M) (Fin.ext (((C.realize_const M c _).mp hc).trans hidx.symm))
      · rintro rfl
        exact ⟨I.realize_domain_unrank idx, (C.realize_const M c idx).mpr hidx⟩
    have hzero := hconst .zero zeroIdx rfl
    have hmax := hconst .max maxIdx rfl
    have hpair_left (xs ys : Fin k → Fin M.size) (j : Fin k) :
        TC.pair xs ys (TC.left _root_.id j) = xs j := congrFun (TC.left_pair xs ys) j
    have hpair_right (xs ys : Fin k → Fin M.size) (j : Fin k) :
        TC.pair xs ys (TC.right _root_.id j) = ys j := congrFun (TC.right_pair xs ys) j
    have hedge (u w : {x : Fin k → Fin M.size // I.domain.Realize x}) :
        (I.rel Language.adj).Realize
            (fun p : Fin 2 × Fin k => if p.1 = 0 then u.val p.2 else w.val p.2) ↔
          graphAdj (I.map hI M) (e u) (e w) := by
      change _ ↔ (I.rel Language.adj).Realize
        (fun p => I.unrank M (![e u, e w] p.1) p.2)
      refine iff_of_eq (congrArg (I.rel Language.adj).Realize (funext fun p => ?_))
      rcases p with ⟨b, j⟩
      cases b using Fin.cases with
      | zero => exact (congrFun (I.unrank_rank u.property) j).symm
      | succ b' =>
        have hb' : b' = 0 := Subsingleton.elim _ _
        subst hb'
        exact (congrFun (I.unrank_rank w.property) j).symm
    let z₀ : {x : Fin k → Fin M.size // I.domain.Realize x} :=
      ⟨I.unrank M zeroIdx, I.realize_domain_unrank zeroIdx⟩
    let m₀ : {x : Fin k → Fin M.size // I.domain.Realize x} :=
      ⟨I.unrank M maxIdx, I.realize_domain_unrank maxIdx⟩
    have hez : e z₀ = zeroIdx := I.rank_unrank zeroIdx
    have hem : e m₀ = maxIdx := I.rank_unrank maxIdx
    have hpath : Relation.ReflTransGen
        (fun u w : Fin k → Fin M.size =>
          (I.domain.Realize u ∧ I.domain.Realize w) ∧
            (I.rel Language.adj).Realize
              (fun p : Fin 2 × Fin k => if p.1 = 0 then u p.2 else w p.2))
        z₀.val m₀.val ↔ I.map hI M ∈ Reach := by
      rw [reflTransGen_subtype_iff z₀ m₀]
      change _ ↔ Relation.ReflTransGen (graphAdj (I.map hI M)) zeroIdx maxIdx
      rw [← hez, ← hem]
      exact Relation.reflTransGen_equiv_iff e hedge z₀ m₀
    have hargs_l (xs : Fin (2 * k) → Fin M.size) :
        (fun i => Term.realize (Sum.elim Empty.elim xs)
          (TC.left (fun i : Fin (2 * k) => (Term.var (.inr i) : (language L).Term _)) i)) =
          TC.left xs := rfl
    have hargs_r (xs : Fin (2 * k) → Fin M.size) :
        (fun i => Term.realize (Sum.elim Empty.elim xs)
          (TC.right (fun i : Fin (2 * k) => (Term.var (.inr i) : (language L).Term _)) i)) =
          TC.right xs := rfl
    have hleft_id (xs : Fin (2 * k) → Fin M.size) :
        (fun x => xs (TC.left _root_.id x)) = TC.left xs := rfl
    have hright_id (xs : Fin (2 * k) → Fin M.size) :
        (fun x => xs (TC.right _root_.id x)) = TC.right xs := rfl
    rw [← hpath]
    simp only [pullbackReachSentence, Operator.Formula.realize_exs, Operator.Formula.realize_conj,
      Operator.Formula.realize_ofFO, TC.realize_tc, Formula.realize_inf, Formula.realize_relabel,
      Function.comp_def, apply_ite, Sum.elim_inr, hpair_left, hpair_right, hargs_l, hargs_r,
      hleft_id, hright_id, hzero, hmax]
    constructor
    · intro hr
      exact ⟨TC.pair z₀.val m₀.val, TC.left_pair _ _, TC.right_pair _ _, by
        simpa only [TC.left_pair, TC.right_pair] using hr⟩
    · rintro ⟨xs, hz, ht, hr⟩
      rwa [hz, ht] at hr

/-- **Ordered first-order reductions to `Reach` pull back FO(TC) definability.** -/
theorem TCDefinable.of_reduces_Reach {L : Language} {K : Query L} (h : Reduces K Reach) :
    TCDefinable K :=
  (PosTCDefinable.of_reduces_Reach h).tcDefinable

/-! ### Full-tuple sandwich interpretation into `Reach` -/

section BoundedReach

private def tagZeroIdx (d : ℕ) : Fin (d + 2) := ⟨0, by omega⟩
private def tagOneIdx (d : ℕ) : Fin (d + 2) := ⟨1, by omega⟩
private def payloadIdx {d : ℕ} (i : Fin d) : Fin (d + 2) := ⟨i.val + 2, by omega⟩

private def midTuple {n d : ℕ} [NeZero n] (maxElem : Fin n) (x : Fin d → Fin n)
    (j : Fin (d + 2)) : Fin n :=
  if h0 : j.val = 0 then 0
  else if h1 : j.val = 1 then maxElem
  else x ⟨j.val - 2, by have := j.isLt; omega⟩

private theorem midTuple_tagZero {n d : ℕ} [NeZero n] (maxElem : Fin n) (x : Fin d → Fin n) :
    midTuple maxElem x (tagZeroIdx d) = 0 := rfl

private theorem midTuple_tagOne {n d : ℕ} [NeZero n] (maxElem : Fin n) (x : Fin d → Fin n) :
    midTuple maxElem x (tagOneIdx d) = maxElem := rfl

private theorem midTuple_payload {n d : ℕ} [NeZero n] (maxElem : Fin n) (x : Fin d → Fin n)
    (i : Fin d) :
    midTuple maxElem x (payloadIdx i) = x i := by
  simp only [midTuple, payloadIdx]
  have h0 : i.val + 2 ≠ 0 := by omega
  have h1 : i.val + 2 ≠ 1 := by omega
  simp only [h0, h1, ↓reduceDIte, Nat.add_sub_cancel]

/-- **Full-tuple sandwich interpretation into `Reach`**: on `Fin (n ^ (d + 2))`, the minimum tuple
`(0, 0, …, 0)` steps to `(0, max, x)` when `src` holds of `x`, interior tuples `(0, max, x)` step
to `(0, max, y)` when `step` holds of `(x, y)`, and `(0, max, y)` steps to `(max, max, …, max)`
when `tgt` holds of `y`. Because `0 ≠ max` on `Fin n` (`2 ≤ n`), the tags `(0, 0)`, `(0, max)` and
`(max, max)` never collide, even when `n = 2`, `d = 0`, or a start tuple already satisfies `tgt`. -/
noncomputable def boundedReachInterpretation {L : Language} {d : ℕ}
    (src : (language L).Formula (Fin d))
    (step : (language L).Formula (Fin d ⊕ Fin d))
    (tgt : (language L).Formula (Fin d)) :
    FullTupleInterpretation L Language.graph (d + 2) where
  rel
    | .adj =>
      let allZero (b : Fin 2) : (language L).Formula (Fin 2 × Fin (d + 2)) :=
        Formula.iInf fun j => Term.equal (.var (b, j)) (zero L)
      let allMax (b : Fin 2) : (language L).Formula (Fin 2 × Fin (d + 2)) :=
        Formula.iInf fun j => Term.equal (.var (b, j)) (max L)
      let isMid (b : Fin 2) : (language L).Formula (Fin 2 × Fin (d + 2)) :=
        Term.equal (.var (b, tagZeroIdx d)) (zero L) ⊓
          Term.equal (.var (b, tagOneIdx d)) (max L)
      ((allZero 0 ⊓ isMid 1) ⊓ src.relabel (fun i => (1, payloadIdx i))) ⊔
        ((isMid 0 ⊓ isMid 1) ⊓
          step.relabel (Sum.elim (fun i => (0, payloadIdx i)) (fun i => (1, payloadIdx i)))) ⊔
        ((isMid 0 ⊓ allMax 1) ⊓ tgt.relabel (fun i => (0, payloadIdx i)))

/-- **Exact reachability semantics of `boundedReachInterpretation`**: the image graph belongs to
`Reach` if and only if some tuple satisfying `src` reaches a tuple satisfying `tgt` in zero or more
`step`-transitions. -/
theorem mem_Reach_boundedReachInterpretation {L : Language} {d : ℕ}
    (src : (language L).Formula (Fin d))
    (step : (language L).Formula (Fin d ⊕ Fin d))
    (tgt : (language L).Formula (Fin d))
    {hI : (boundedReachInterpretation src step tgt).toDomainInterpretation.Admissible}
    (M : Structure L) :
    (boundedReachInterpretation src step tgt).toDomainInterpretation.map hI M ∈ Reach ↔
      ∃ x y : Fin d → Fin M.size, src.Realize x ∧
        Relation.ReflTransGen (fun a b => step.Realize (Sum.elim a b)) x y ∧ tgt.Realize y := by
  let I := boundedReachInterpretation src step tgt
  let maxElem : Fin M.size := M.maxElem
  have h0_ne_max : (0 : Fin M.size) ≠ maxElem := by
    intro h
    have hv := congrArg Fin.val h
    have hge := M.size_ge_two
    simp only [Fin.val_zero, maxElem] at hv
    omega
  let Z : Fin (d + 2) → Fin M.size := constantTuple (n := M.size) (k := d + 1) .zero
  let T : Fin (d + 2) → Fin M.size := constantTuple (n := M.size) (k := d + 1) .max
  let hc : (I.toDomainInterpretation.map hI M).size = M.size ^ (d + 2) :=
    I.card_toDomainInterpretation M
  let e : (Fin (d + 2) → Fin M.size) ≃ Fin (I.toDomainInterpretation.map hI M).size :=
    lexEquiv.trans (finCongr hc.symm)
  have heZ : e Z = 0 := by
    apply Fin.ext
    change lexRank Z = 0
    exact Ordered.lexRank_constantTuple .zero
  have heT : e T = (I.toDomainInterpretation.map hI M).maxElem := by
    apply Fin.ext
    change lexRank T = (I.toDomainInterpretation.map hI M).size - 1
    rw [hc]
    exact Ordered.lexRank_constantTuple .max
  let IsMid (u : Fin (d + 2) → Fin M.size) : Prop :=
    u (tagZeroIdx d) = 0 ∧ u (tagOneIdx d) = maxElem
  let Edge (u w : Fin (d + 2) → Fin M.size) : Prop :=
    ((u = Z ∧ IsMid w) ∧ src.Realize (fun i => w (payloadIdx i))) ∨
      ((IsMid u ∧ IsMid w) ∧
        step.Realize (Sum.elim (fun i => u (payloadIdx i)) (fun i => w (payloadIdx i)))) ∨
      ((IsMid u ∧ w = T) ∧ tgt.Realize (fun i => u (payloadIdx i)))
  have hedge (u w : Fin (d + 2) → Fin M.size) :
      Edge u w ↔ graphAdj (I.toDomainInterpretation.map hI M) (e u) (e w) := by
    rw [graphAdj, I.relMap_map_toDomainInterpretation (Nat.zero_lt_succ (d + 1))]
    change Edge u w ↔ (I.rel Language.adj).Realize
      (fun p => lexEquiv.symm ((Fin.cast hc ∘ ![e u, e w]) p.1) p.2)
    have hsymm : (fun p : Fin 2 × Fin (d + 2) =>
          lexEquiv.symm ((Fin.cast hc ∘ ![e u, e w]) p.1) p.2) =
        fun p => ![u, w] p.1 p.2 := by
      funext ⟨b, j⟩
      cases b using Fin.cases with
      | zero => exact congrFun (lexEquiv.symm_apply_apply u) j
      | succ b' =>
        have hb' : b' = 0 := Subsingleton.elim _ _
        subst hb'
        exact congrFun (lexEquiv.symm_apply_apply w) j
    rw [hsymm]
    have hzero_eq (a : Fin (d + 2) → Fin M.size) : (∀ j, a j = 0) ↔ a = Z :=
      ⟨fun h => funext h, fun h j => h ▸ rfl⟩
    have hmax_eq (a : Fin (d + 2) → Fin M.size) : (∀ j, a j = maxElem) ↔ a = T :=
      ⟨fun h => funext h, fun h j => h ▸ rfl⟩
    have hsum : ((fun p : Fin 2 × Fin (d + 2) => ![u, w] p.1 p.2) ∘
          Sum.elim (fun i => ((0 : Fin 2), payloadIdx i))
            (fun i => ((1 : Fin 2), payloadIdx i))) =
        Sum.elim (fun i => u (payloadIdx i)) (fun i => w (payloadIdx i)) := by
      funext x
      cases x <;> rfl
    simp only [I, boundedReachInterpretation, Formula.realize_sup, Formula.realize_inf,
      Formula.realize_iInf, Formula.realize_relabel, Formula.realize_equal,
      Term.realize_var, realize_zero_eq, realize_max_eq, maxElem, hsum, Function.comp_def,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      hzero_eq, hmax_eq, Edge, IsMid, or_assoc]
  change Relation.ReflTransGen (graphAdj (I.toDomainInterpretation.map hI M)) 0
      (I.toDomainInterpretation.map hI M).maxElem ↔ _
  rw [← heZ, ← heT, ← Relation.reflTransGen_equiv_iff e hedge Z T]
  have hZ_not_mid : ¬ IsMid Z := fun h => h0_ne_max h.2
  have hT_not_mid : ¬ IsMid T := fun h => h0_ne_max h.1.symm
  have hZ_ne_T : Z ≠ T := fun h => h0_ne_max (congrFun h (tagZeroIdx d))
  constructor
  · intro hpath
    let Inv (w : Fin (d + 2) → Fin M.size) : Prop :=
      w = Z ∨
        (IsMid w ∧ ∃ x : Fin d → Fin M.size, src.Realize x ∧
          Relation.ReflTransGen (fun a b => step.Realize (Sum.elim a b))
            x (fun i => w (payloadIdx i))) ∨
        (w = T ∧ ∃ x y : Fin d → Fin M.size, src.Realize x ∧
          Relation.ReflTransGen (fun a b => step.Realize (Sum.elim a b)) x y ∧ tgt.Realize y)
    have hinv : ∀ {w}, Relation.ReflTransGen Edge Z w → Inv w := by
      intro w hw
      induction hw with
      | refl => exact Or.inl rfl
      | @tail u w _ huw ih =>
        rcases ih with rfl | ⟨hu_mid, x, hx, hxu⟩ | ⟨rfl, -⟩
        · rcases huw with ⟨⟨_, hw_mid⟩, hsrc⟩ | ⟨⟨hZ, _⟩, _⟩ | ⟨⟨hZ, _⟩, _⟩
          · exact Or.inr (Or.inl ⟨hw_mid, _, hsrc, .refl⟩)
          · exact False.elim (hZ_not_mid hZ)
          · exact False.elim (hZ_not_mid hZ)
        · rcases huw with ⟨⟨rfl, _⟩, _⟩ | ⟨⟨_, hw_mid⟩, hstep⟩ | ⟨⟨_, rfl⟩, htgt⟩
          · exact False.elim (hZ_not_mid hu_mid)
          · exact Or.inr (Or.inl ⟨hw_mid, x, hx, hxu.tail hstep⟩)
          · exact Or.inr (Or.inr ⟨rfl, x, _, hx, hxu, htgt⟩)
        · rcases huw with ⟨⟨hTZ, _⟩, _⟩ | ⟨⟨hT, _⟩, _⟩ | ⟨⟨hT, _⟩, _⟩
          · exact False.elim (hZ_ne_T hTZ.symm)
          · exact False.elim (hT_not_mid hT)
          · exact False.elim (hT_not_mid hT)
    rcases hinv hpath with hTZ | ⟨hT, -⟩ | ⟨_, hgoal⟩
    · exact False.elim (hZ_ne_T hTZ.symm)
    · exact False.elim (hT_not_mid hT)
    · exact hgoal
  · rintro ⟨x, y, hx, hxy, hy⟩
    have hmid (a : Fin d → Fin M.size) : IsMid (midTuple maxElem a) :=
      ⟨midTuple_tagZero maxElem a, midTuple_tagOne maxElem a⟩
    have h1 : Edge Z (midTuple maxElem x) := by
      refine Or.inl ⟨⟨rfl, hmid x⟩, ?_⟩
      simpa only [midTuple_payload] using hx
    have h2 : Relation.ReflTransGen Edge (midTuple maxElem x) (midTuple maxElem y) :=
      Relation.ReflTransGen.lift (midTuple maxElem)
        (fun a b hab => Or.inr (Or.inl ⟨⟨hmid a, hmid b⟩, by
          simpa only [midTuple_payload] using hab⟩)) x y hxy
    have h3 : Edge (midTuple maxElem y) T := by
      refine Or.inr (Or.inr ⟨⟨hmid y, rfl⟩, ?_⟩)
      simpa only [midTuple_payload] using hy
    exact (Relation.ReflTransGen.head h1 h2).tail h3

end BoundedReach

/-! ### Endpoint normalization (`STReach` ↔ `Reach`, including `s = t`) -/

/-- Unary endpoint relation symbols for directed `s`–`t` reachability. -/
inductive STMarkerRelation : ℕ → Type
  /-- Source vertex marker. -/
  | source : STMarkerRelation 1
  /-- Target vertex marker. -/
  | target : STMarkerRelation 1
  deriving DecidableEq

/-- The relational language of unary source and target markers. -/
abbrev stMarkerLanguage : Language where
  Functions _ := Empty
  Relations := STMarkerRelation

instance : stMarkerLanguage.IsRelational := fun _ => inferInstance

/-- Directed graphs expanded by unary source and target markers. -/
abbrev stGraphLanguage : Language := Language.graph.sum stMarkerLanguage

instance : stGraphLanguage.IsRelational := fun _ => inferInstance

/-- Canonical vocabulary for `stGraphLanguage`: index `0` is `adj` (arity `2`), index `1` is
`source` (arity `1`), and index `2` is `target` (arity `1`). -/
@[expose] def stGraphVocabulary : Vocabulary stGraphLanguage where
  count := 3
  symbol :=
    { toFun
        | ⟨0, _⟩ => ⟨2, .inl .adj⟩
        | ⟨1, _⟩ => ⟨1, .inr .source⟩
        | ⟨2, _⟩ => ⟨1, .inr .target⟩
      invFun
        | ⟨_, .inl .adj⟩ => ⟨0, by decide⟩
        | ⟨_, .inr .source⟩ => ⟨1, by decide⟩
        | ⟨_, .inr .target⟩ => ⟨2, by decide⟩
      left_inv := by
        rintro ⟨i, hi⟩
        match i, hi with
        | 0, _ | 1, _ | 2, _ => rfl
      right_inv := by
        rintro ⟨_, r⟩
        rcases r with (_ | _) | (_ | _) <;> rfl }

/-- **Ordered marked `s`–`t` reachability**: some vertex marked `source` reaches some vertex marked
`target` by zero or more directed `adj`-edges (including the zero-step path when `s = t`). -/
@[expose] def STReach : Query stGraphLanguage :=
  {M | ∃ s t : M,
    Language.Structure.RelMap (L := stGraphLanguage) (.inr .source) ![s] ∧
    Language.Structure.RelMap (L := stGraphLanguage) (.inr .target) ![t] ∧
    Relation.ReflTransGen
      (fun x y : M => Language.Structure.RelMap (L := stGraphLanguage) (.inl .adj) ![x, y]) s t}

theorem mem_STReach {M : Structure stGraphLanguage} :
    M ∈ STReach ↔ ∃ s t : M,
      Language.Structure.RelMap (L := stGraphLanguage) (.inr .source) ![s] ∧
      Language.Structure.RelMap (L := stGraphLanguage) (.inr .target) ![t] ∧
      Relation.ReflTransGen
        (fun x y : M => Language.Structure.RelMap (L := stGraphLanguage) (.inl .adj) ![x, y]) s t :=
  Iff.rfl

/-- Expand a graph structure on `Fin n` (`2 ≤ n`) by marking a chosen vertex pair `(s, t)` as
singleton `source` and `target` predicates. -/
@[expose] def mkMarkedGraph {n : ℕ} (hn : 2 ≤ n) (G : Language.graph.Structure (Fin n))
    (s t : Fin n) : Structure stGraphLanguage where
  size := n
  size_ge_two := hn
  input :=
    letI := G
    letI : stMarkerLanguage.Structure (Fin n) :=
      { funMap := fun f => isEmptyElim f
        RelMap
          | .source, x => x 0 = s
          | .target, x => x 0 = t }
    inferInstance

@[simp]
theorem mem_STReach_mkMarkedGraph {n : ℕ} (hn : 2 ≤ n) (G : Language.graph.Structure (Fin n))
    (s t : Fin n) :
    mkMarkedGraph hn G s t ∈ STReach ↔
      Relation.ReflTransGen (fun x y : Fin n => G.RelMap Language.adj ![x, y]) s t := by
  simp only [mem_STReach, mkMarkedGraph]
  constructor
  · rintro ⟨s', t', rfl, rfl, hpath⟩
    exact hpath
  · intro hpath
    exact ⟨s, t, rfl, rfl, hpath⟩

/-- Full-tuple interpretation of dimension `3` normalizing `STReach` (arbitrary marked endpoints,
including `s = t`) into canonical `0`-to-`max` `Reach`. -/
noncomputable def stReachToReachInterpretation :
    FullTupleInterpretation stGraphLanguage Language.graph 3 :=
  boundedReachInterpretation (d := 1)
    (Relations.formula₁
      ((LHom.sumInl : stGraphLanguage →ᴸ language stGraphLanguage).onRelation (.inr .source))
      (.var 0))
    (Relations.formula₂
      ((LHom.sumInl : stGraphLanguage →ᴸ language stGraphLanguage).onRelation (.inl .adj))
      (.var (.inl 0)) (.var (.inr 0)))
    (Relations.formula₁
      ((LHom.sumInl : stGraphLanguage →ᴸ language stGraphLanguage).onRelation (.inr .target))
      (.var 0))

theorem mem_Reach_stReachToReachInterpretation
    {hI : stReachToReachInterpretation.toDomainInterpretation.Admissible}
    (M : Structure stGraphLanguage) :
    stReachToReachInterpretation.toDomainInterpretation.map hI M ∈ Reach ↔ M ∈ STReach := by
  refine (mem_Reach_boundedReachInterpretation _ _ _ M).trans ?_
  rw [mem_STReach]
  have hmark (r : STMarkerRelation 1) (x : Fin 1 → Fin M.size) :
      (Relations.formula₁
        ((LHom.sumInl : stGraphLanguage →ᴸ language stGraphLanguage).onRelation (.inr r))
        (.var (0 : Fin 1))).Realize x ↔
      Language.Structure.RelMap (L := stGraphLanguage) (.inr r) ![x 0] := by
    simp only [Formula.realize_rel₁, Term.realize_var]
    rfl
  have hstep (a b : Fin 1 → Fin M.size) :
      (Relations.formula₂
        ((LHom.sumInl : stGraphLanguage →ᴸ language stGraphLanguage).onRelation (.inl .adj))
        (.var (.inl (0 : Fin 1))) (.var (.inr (0 : Fin 1)))).Realize (Sum.elim a b) ↔
      Language.Structure.RelMap (L := stGraphLanguage) (.inl .adj) ![a 0, b 0] := by
    simp only [Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    rfl
  let uEquiv : (Fin 1 → Fin M.size) ≃ Fin M.size :=
    { toFun := fun x => x 0
      invFun := fun s _ => s
      left_inv := fun x => funext fun i => congrArg x (Subsingleton.elim 0 i)
      right_inv := fun _ => rfl }
  constructor
  · rintro ⟨x, y, hx, hxy, hy⟩
    refine ⟨x 0, y 0, (hmark .source x).mp hx, (hmark .target y).mp hy, ?_⟩
    exact (Relation.reflTransGen_equiv_iff uEquiv hstep x y).mp hxy
  · rintro ⟨s, t, hs, ht, hst⟩
    refine ⟨uEquiv.symm s, uEquiv.symm t, (hmark .source _).mpr hs, ?_, (hmark .target _).mpr ht⟩
    exact (Relation.reflTransGen_equiv_iff uEquiv hstep (uEquiv.symm s) (uEquiv.symm t)).mpr hst

/-- **Endpoint normalization**: `STReach` first-order reduces to canonical `0`-to-`max` `Reach`
(including when `s = t`). -/
theorem stReach_reduces_Reach : Reduces STReach Reach :=
  stReachToReachInterpretation.reduces (by decide) fun M =>
    (mem_Reach_stReachToReachInterpretation M).symm

/-- Dimension-1 full-tuple interpretation marking `0` as `source` and `max` as `target`. -/
def reachToSTReachInterpretation : FullTupleInterpretation Language.graph stGraphLanguage 1 where
  rel
    | .inl .adj =>
      Relations.formula₂
        ((LHom.sumInl : Language.graph →ᴸ language Language.graph).onRelation .adj)
        (.var (0, 0)) (.var (1, 0))
    | .inr .source => Term.equal (.var (0, 0)) (zero Language.graph)
    | .inr .target => Term.equal (.var (0, 0)) (max Language.graph)

theorem mem_STReach_reachToSTReachInterpretation
    {hI : reachToSTReachInterpretation.toDomainInterpretation.Admissible}
    (M : Structure Language.graph) :
    reachToSTReachInterpretation.toDomainInterpretation.map hI M ∈ STReach ↔ M ∈ Reach := by
  let I := reachToSTReachInterpretation
  let hc : (I.toDomainInterpretation.map hI M).size = M.size ^ 1 := I.card_toDomainInterpretation M
  have hc1 : (I.toDomainInterpretation.map hI M).size = M.size := hc.trans (pow_one M.size)
  let e : Fin M.size ≃ Fin (I.toDomainInterpretation.map hI M).size := finCongr hc1.symm
  have hrel {r : ℕ} (R : stGraphLanguage.Relations r) (x : Fin r → Fin M.size) :
      Language.Structure.RelMap (L := stGraphLanguage) R (e ∘ x) ↔
        (I.rel R).Realize (fun p => x p.1) := by
    rw [I.relMap_map_toDomainInterpretation (by decide)]
    change (I.rel R).Realize
        (fun p => lexEquiv.symm (Fin.cast hc (e (x p.1))) p.2) ↔
      (I.rel R).Realize (fun p => x p.1)
    refine iff_of_eq (congrArg (I.rel R).Realize (funext fun p => ?_))
    rcases p with ⟨a, j⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    change lexEquiv.symm (Fin.cast hc (e (x a))) 0 = x a
    have hlex : lexEquiv (fun _ : Fin 1 => x a) = Fin.cast hc (e (x a)) := by
      apply Fin.ext
      change lexRank (fun _ : Fin 1 => x a) = (x a).val
      rw [lexRank_apply, Fin.sum_univ_one]
      simp
    rw [← hlex, Equiv.symm_apply_apply]
  have hrel1 (R : stGraphLanguage.Relations 1) (s : Fin M.size) :
      Language.Structure.RelMap (L := stGraphLanguage) R ![e s] ↔
        (I.rel R).Realize (fun p => (![s] : Fin 1 → Fin M.size) p.1) := by
    have h := hrel R ![s]
    have hfn : e ∘ ![s] = ![e s] := funext fun i => by
      have hi : i = 0 := Subsingleton.elim _ _; subst hi; rfl
    rwa [hfn] at h
  have hsrc (s : Fin M.size) :
      Language.Structure.RelMap (L := stGraphLanguage) (.inr .source) ![e s] ↔ s = 0 :=
    (hrel1 (.inr .source) s).trans (by
      simp only [I, reachToSTReachInterpretation, Formula.realize_equal, Term.realize_var,
        realize_zero_eq, Matrix.cons_val_zero])
  have htgt (t : Fin M.size) :
      Language.Structure.RelMap (L := stGraphLanguage) (.inr .target) ![e t] ↔
        t = M.maxElem :=
    (hrel1 (.inr .target) t).trans (by
      simp only [I, reachToSTReachInterpretation, Formula.realize_equal, Term.realize_var,
        realize_max_eq, Matrix.cons_val_zero])
  have hadj (x y : Fin M.size) :
      graphAdj M x y ↔
        Language.Structure.RelMap (L := stGraphLanguage) (.inl .adj) ![e x, e y] := by
    have h := hrel (.inl .adj) ![x, y]
    have hfn : e ∘ ![x, y] = ![e x, e y] := funext fun i => by
      cases i using Fin.cases with
      | zero => rfl
      | succ i' => have hi : i' = 0 := Subsingleton.elim _ _; subst hi; rfl
    rw [hfn] at h
    refine Iff.symm (h.trans ?_)
    simp only [I, reachToSTReachInterpretation, Formula.realize_rel₂, Term.realize_var,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rfl
  rw [mem_STReach, mem_Reach]
  constructor
  · rintro ⟨s', t', hs', ht', hpath⟩
    obtain ⟨s, rfl⟩ := e.surjective s'
    obtain ⟨t, rfl⟩ := e.surjective t'
    rw [(hsrc s).mp hs'] at hpath
    rw [(htgt t).mp ht'] at hpath
    exact (Relation.reflTransGen_equiv_iff e hadj _ _).mpr hpath
  · intro hpath
    exact ⟨e 0, e M.maxElem,
      (hsrc 0).mpr rfl, (htgt _).mpr rfl, (Relation.reflTransGen_equiv_iff e hadj _ _).mp hpath⟩

/-- `Reach` first-order reduces to `STReach`. -/
theorem reach_reduces_STReach : Reduces Reach STReach :=
  reachToSTReachInterpretation.reduces (by decide) fun M =>
    (mem_STReach_reachToSTReachInterpretation M).symm

end Cslib.Logic.FO.Ordered
