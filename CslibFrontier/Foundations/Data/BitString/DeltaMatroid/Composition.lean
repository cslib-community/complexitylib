/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Operations
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Composition of Boolean delta-matroids

Composition identifies shared coordinates and existentially removes them. This formalizes
Proposition 6 and its evenness corollary of [KazdaKolmogorovRolinek2018], arXiv v6,
printed pp. 4–5. In addition to the source's exchange hypotheses we require a nonempty output:
nonempty inputs alone need not have compatible shared coordinates. Empty external coordinate
types are allowed. The proof uses one-sided exchange twice to eliminate one equal pair,
then eliminates finitely many pairs; it assumes no simultaneous exchange principle.

## Main definitions

* `comp`: relational composition along finitely many shared Boolean coordinates.
* `tracePair`, `trace`: eliminate one equal pair, or a finite family of equal pairs.
* `oneHotRelation`: exactly-one on an arbitrary coordinate type.
* `star`, `starAt`: the all-zero or single-internal/connector-pair gadget and its twists.

## Main results

* `IsDeltaMatroid.comp`, `IsEvenDeltaMatroid.comp`: closure with compatible output.
* `isEvenDeltaMatroid_oneHotRelation`: exactly-one has odd common parity.
* `isEvenDeltaMatroid_starAt`: the reference-based contraction gadget is even.
-/

public section

namespace Cslib.BitString

open Finset

universe u

variable {ι κ τ : Type u} [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

/-- The direct product of Boolean relations on disjoint coordinate types. -/
@[expose] def sumProd (R : Set (ι → Bool)) (S : Set (κ → Bool)) : Set ((ι ⊕ κ) → Bool) :=
  {x | (fun i => x (.inl i)) ∈ R ∧ (fun k => x (.inr k)) ∈ S}

/-- Direct products preserve one-sided exchange. -/
theorem IsDeltaMatroid.sumProd {R : Set (ι → Bool)} {S : Set (κ → Bool)}
    (hR : IsDeltaMatroid R) (hS : IsDeltaMatroid S) : IsDeltaMatroid (sumProd R S) where
  nonempty := by
    obtain ⟨x, hx⟩ := hR.nonempty
    obtain ⟨y, hy⟩ := hS.nonempty
    exact ⟨Sum.elim x y, hx, hy⟩
  exchange := by
    rintro x y ⟨hxR, hxS⟩ ⟨hyR, hyS⟩ (i | k) hi
    · obtain ⟨j, hj, hf⟩ := hR.exchange hxR hyR hi
      refine ⟨.inl j, hj, ?_, ?_⟩
      · convert hf using 1
        ext a
        simp [flipOn]
      · convert hxS using 1
        ext a
        simp [flipOn]
    · obtain ⟨j, hj, hf⟩ := hS.exchange hxS hyS hi
      refine ⟨.inr j, hj, ?_, ?_⟩
      · convert hxR using 1
        ext a
        simp [flipOn]
      · convert hf using 1
        ext a
        simp [flipOn]

/-- Parity splits over disjoint coordinate types. -/
theorem parityOn_univ_sum {α β : Type*} [Fintype α] [Fintype β] (x : (α ⊕ β) → Bool) :
    parityOn univ x = (parityOn univ (fun i => x (.inl i)) ^^
      parityOn univ (fun k => x (.inr k))) := by
  simp only [parityOn_eq_sum, Fintype.sum_sum_type, Bool.add_eq_xor]

/-- Direct products preserve common parity, including odd parity inputs. -/
theorem IsEvenDeltaMatroid.sumProd [Fintype ι] [Fintype κ]
    {R : Set (ι → Bool)} {S : Set (κ → Bool)}
    (hR : IsEvenDeltaMatroid R) (hS : IsEvenDeltaMatroid S) :
    IsEvenDeltaMatroid (sumProd R S) where
  isDeltaMatroid := hR.isDeltaMatroid.sumProd hS.isDeltaMatroid
  parity_eq := by
    rintro x y ⟨hxR, hxS⟩ ⟨hyR, hyS⟩
    rw [parityOn_univ_sum, parityOn_univ_sum, hR.parity_eq hxR hyR, hS.parity_eq hxS hyS]

/-- Identify two coordinates, indexed by `Bool`, and remove both. -/
@[expose] def tracePair (R : Set ((ι ⊕ Bool) → Bool)) : Set (ι → Bool) :=
  {x | ∃ b : Bool, Sum.elim x (fun _ => b) ∈ R}

private theorem flipOn_inl_pair (x : ι → Bool) (b : Bool) (i j : ι) :
    flipOn {Sum.inl i, Sum.inl j} (Sum.elim x (fun _ : Bool => b)) =
      Sum.elim (flipOn {i, j} x) (fun _ => b) := by
  ext (a | a) <;> simp [flipOn]

/-- Eliminating one equal pair preserves exchange, provided the result is nonempty.
When exchange enters the hidden pair, a second exchange exits it. Both steps move toward
the same feasible target, so the second cannot undo the first external coordinate. -/
theorem IsDeltaMatroid.tracePair {R : Set ((ι ⊕ Bool) → Bool)}
    (hR : IsDeltaMatroid R) (hne : (tracePair R).Nonempty) :
    IsDeltaMatroid (tracePair R) where
  nonempty := hne
  exchange := by
    rintro x y ⟨b, hx⟩ ⟨c, hy⟩ i hi
    obtain ⟨j, hj, hf⟩ := hR.exchange hx hy (i := .inl i) hi
    rcases j with j | a
    · exact ⟨j, hj, b, by rwa [flipOn_inl_pair] at hf⟩
    · have hbc : b ≠ c := hj
      have hnext : flipOn {Sum.inl i, Sum.inr a} (Sum.elim x (fun _ : Bool => b))
          (.inr (!a)) ≠ Sum.elim y (fun _ : Bool => c) (.inr (!a)) := by
        simpa [flipOn] using hbc
      obtain ⟨k, hk, hff⟩ := hR.exchange hf hy hnext
      rcases k with k | d
      · have hki : k ≠ i := by
          intro he
          subst k
          simp only [flipOn, mem_insert, mem_singleton, true_or,
            ite_true, Sum.elim_inl] at hk
          cases hx : x i <;> cases hy : y i <;> simp_all
        have hk' : x k ≠ y k := by simpa [flipOn, hki] using hk
        refine ⟨k, hk', c, ?_⟩
        convert hff using 1
        ext (t | t)
        · by_cases hti : t = i <;> by_cases htk : t = k <;> simp_all [flipOn]
        · cases a <;> cases t <;> cases b <;> cases c <;> simp_all [flipOn]
      · have hda : d ≠ a := by
          intro he
          subst d
          simp only [flipOn, mem_insert, mem_singleton, or_true,
            ite_true, Sum.elim_inr] at hk
          cases b <;> cases c <;> simp_all
        refine ⟨i, hi, c, ?_⟩
        convert hff using 1
        ext (t | t)
        · by_cases hti : t = i <;> simp_all [flipOn]
        · cases a <;> cases d <;> cases t <;> cases b <;> cases c <;>
            simp_all [flipOn]

omit [DecidableEq ι] in
private theorem parityOn_pair_extension [Fintype ι] (x : ι → Bool) (b : Bool) :
    parityOn univ (Sum.elim x (fun _ : Bool => b)) = parityOn univ x := by
  rw [parityOn_univ_sum]
  have hb : parityOn (univ : Finset Bool) (fun _ => b) = false := by
    cases b <;> decide
  simp only [Sum.elim_inl, Sum.elim_inr, hb, Bool.xor_false]

/-- An eliminated equal pair contributes zero parity. -/
theorem IsEvenDeltaMatroid.tracePair [Fintype ι] {R : Set ((ι ⊕ Bool) → Bool)}
    (hR : IsEvenDeltaMatroid R) (hne : (tracePair R).Nonempty) :
    IsEvenDeltaMatroid (tracePair R) where
  isDeltaMatroid := hR.isDeltaMatroid.tracePair hne
  parity_eq := by
    rintro x y ⟨b, hx⟩ ⟨c, hy⟩
    simpa only [parityOn_pair_extension] using hR.parity_eq hx hy

/-- Identify and eliminate a finite family of disjoint equal pairs. -/
@[expose] def trace (R : Set ((ι ⊕ (κ × Bool)) → Bool)) : Set (ι → Bool) :=
  {x | ∃ z : κ → Bool, Sum.elim x (fun p => z p.1) ∈ R}

private def optionPairEquiv : (ι ⊕ (Option κ × Bool)) ≃ ((ι ⊕ (κ × Bool)) ⊕ Bool) where
  toFun
    | .inl i => .inl (.inl i)
    | .inr (none, b) => .inr b
    | .inr (some k, b) => .inl (.inr (k, b))
  invFun
    | .inl (.inl i) => .inl i
    | .inl (.inr (k, b)) => .inr (some k, b)
    | .inr b => .inr (none, b)
  left_inv := by rintro (i | ⟨_ | k, b⟩) <;> rfl
  right_inv := by rintro ((i | ⟨k, b⟩) | b) <;> rfl

omit [DecidableEq ι] [DecidableEq κ] in
private theorem trace_option (R : Set ((ι ⊕ (Option κ × Bool)) → Bool)) :
    trace (tracePair {x | (fun i => x (optionPairEquiv i)) ∈ R}) = trace R := by
  ext x
  constructor
  · rintro ⟨z, b, hz⟩
    refine ⟨fun k => Option.elim k b z, ?_⟩
    change _ ∈ R at hz ⊢
    convert hz using 1
    ext (i | ⟨_ | k, a⟩) <;> rfl
  · rintro ⟨z, hz⟩
    refine ⟨fun k => z (some k), z none, ?_⟩
    change _ ∈ R at hz ⊢
    convert hz using 1
    ext (i | ⟨_ | k, a⟩) <;> rfl

/-- Finite equal-pair elimination preserves exchange. The output must have a witness. -/
theorem IsDeltaMatroid.trace [Finite κ] {R : Set ((ι ⊕ (κ × Bool)) → Bool)}
    (hR : IsDeltaMatroid R) (hne : (trace R).Nonempty) : IsDeltaMatroid (trace R) := by
  classical
  have h : ∀ (α : Type u) [Finite α] [DecidableEq α], ∀ (β : Type u) [DecidableEq β]
      (T : Set ((β ⊕ (α × Bool)) → Bool)), IsDeltaMatroid T →
      (BitString.trace T).Nonempty → IsDeltaMatroid (BitString.trace T) := by
    intro α _
    refine Finite.induction_empty_option
      (P := fun α => ∀ [DecidableEq α], ∀ (β : Type u) [DecidableEq β]
        (T : Set ((β ⊕ (α × Bool)) → Bool)), IsDeltaMatroid T →
        (BitString.trace T).Nonempty → IsDeltaMatroid (BitString.trace T)) ?_ ?_ ?_ α
    · intro α δ e ih _ β _ T hT hn
      let E := Equiv.sumCongr (Equiv.refl β) (Equiv.prodCongr e.symm (Equiv.refl Bool))
      let U : Set ((β ⊕ (α × Bool)) → Bool) := {x | (fun i => x (E i)) ∈ T}
      have he : BitString.trace U = BitString.trace T := by
        ext x
        constructor
        · rintro ⟨z, hz⟩
          refine ⟨fun a => z (e.symm a), ?_⟩
          change _ ∈ T at hz ⊢
          convert hz using 1
          ext (i | ⟨k, b⟩) <;> rfl
        · rintro ⟨z, hz⟩
          refine ⟨fun a => z (e a), ?_⟩
          change _ ∈ T
          convert hz using 1
          ext (i | ⟨k, b⟩) <;> simp [E]
      rw [← he]
      exact ih β U (hT.reindex E) (he.symm ▸ hn)
    · intro _ β _ T hT hn
      let E : (β ⊕ (PEmpty × Bool)) ≃ β :=
        { toFun := Sum.elim id (fun p => p.1.elim)
          invFun := Sum.inl
          left_inv := by
            rintro (i | ⟨k, b⟩)
            · rfl
            · exact k.elim
          right_inv := fun _ => rfl }
      have he : BitString.trace T = {x | (fun i => x (E i)) ∈ T} := by
        ext x
        constructor
        · rintro ⟨z, hz⟩
          change _ ∈ T
          convert hz using 1
          ext (i | ⟨k, b⟩)
          · rfl
          · exact k.elim
        · intro hx
          refine ⟨PEmpty.elim, ?_⟩
          change _ ∈ T at hx ⊢
          convert hx using 1
          ext (i | ⟨k, b⟩)
          · rfl
          · exact k.elim
      rw [he]
      exact hT.reindex E
    · intro α _ ih _ β _ T hT hn
      let U : Set (((β ⊕ (α × Bool)) ⊕ Bool) → Bool) :=
        {x | (fun i => x (optionPairEquiv i)) ∈ T}
      have he : BitString.trace (BitString.tracePair U) = BitString.trace T := trace_option T
      have hn' : (BitString.trace (BitString.tracePair U)).Nonempty := he.symm ▸ hn
      have hpair : (BitString.tracePair U).Nonempty := by
        obtain ⟨x, z, hz⟩ := hn'
        exact ⟨_, hz⟩
      rw [← he]
      exact ih β (BitString.tracePair U)
        ((hT.reindex optionPairEquiv).tracePair hpair) hn'
  exact h κ ι R hR hne

omit [DecidableEq ι] [DecidableEq κ] in
private theorem parityOn_trace_extension [Fintype ι] [Fintype κ]
    (x : ι → Bool) (z : κ → Bool) :
    parityOn univ (Sum.elim x (fun p : κ × Bool => z p.1)) = parityOn univ x := by
  rw [parityOn_univ_sum]
  have hz : parityOn univ (fun p : κ × Bool => z p.1) = false := by
    simp only [parityOn_eq_sum, Fintype.sum_prod_type]
    have he (k : κ) : ∑ _ : Bool, z k = (0 : Bool) := by
      rw [Fintype.sum_bool]; cases z k <;> rfl
    simp_rw [he]
    exact Finset.sum_const_zero
  simp only [Sum.elim_inl, Sum.elim_inr, hz, Bool.xor_false]

/-- Eliminating equal pairs preserves common parity. -/
theorem IsEvenDeltaMatroid.trace [Fintype ι] [Fintype κ]
    {R : Set ((ι ⊕ (κ × Bool)) → Bool)} (hR : IsEvenDeltaMatroid R)
    (hne : (trace R).Nonempty) : IsEvenDeltaMatroid (trace R) where
  isDeltaMatroid := hR.isDeltaMatroid.trace hne
  parity_eq := by
    rintro x y ⟨z, hx⟩ ⟨w, hy⟩
    simpa only [parityOn_trace_extension] using hR.parity_eq hx hy

/-- Composition by existential equality of the shared coordinates `κ`.
The external coordinates retain the `ι`, then `τ`, order. -/
@[expose] def comp (R : Set ((ι ⊕ κ) → Bool)) (S : Set ((κ ⊕ τ) → Bool)) :
    Set ((ι ⊕ τ) → Bool) :=
  {x | ∃ z : κ → Bool, Sum.elim (fun i => x (.inl i)) z ∈ R ∧
    Sum.elim z (fun k => x (.inr k)) ∈ S}

private def compEquiv : ((ι ⊕ κ) ⊕ (κ ⊕ τ)) ≃ ((ι ⊕ τ) ⊕ (κ × Bool)) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr k) => .inr (k, false)
    | .inr (.inl k) => .inr (k, true)
    | .inr (.inr l) => .inl (.inr l)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr l) => .inr (.inr l)
    | .inr (k, false) => .inl (.inr k)
    | .inr (k, true) => .inr (.inl k)
  left_inv := by rintro ((i | k) | (k | l)) <;> rfl
  right_inv := by rintro ((i | l) | ⟨k, _ | _⟩) <;> rfl

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] in
private theorem comp_eq_trace (R : Set ((ι ⊕ κ) → Bool)) (S : Set ((κ ⊕ τ) → Bool)) :
    comp R S = trace {x | (fun i => x (compEquiv i)) ∈ sumProd R S} := by
  ext x
  apply exists_congr
  intro z
  change (_ ∈ R ∧ _ ∈ S) ↔ (_ ∈ R ∧ _ ∈ S)
  have hR : (fun i => Sum.elim x (fun p => z p.1) (compEquiv (.inl i))) =
      Sum.elim (fun i => x (.inl i)) z := by
    ext (i | k) <;> rfl
  have hS : (fun i => Sum.elim x (fun p => z p.1) (compEquiv (.inr i))) =
      Sum.elim z (fun i => x (.inr i)) := by
    ext (k | i) <;> rfl
  rw [hR, hS]

/-- Proposition 6 of [KazdaKolmogorovRolinek2018], with compatibility explicit.
Neither input nonemptiness nor nonempty external coordinates imply compatibility. -/
theorem IsDeltaMatroid.comp [Finite κ]
    {R : Set ((ι ⊕ κ) → Bool)} {S : Set ((κ ⊕ τ) → Bool)}
    (hR : IsDeltaMatroid R) (hS : IsDeltaMatroid S) (hne : (comp R S).Nonempty) :
    IsDeltaMatroid (comp R S) := by
  rw [comp_eq_trace] at hne ⊢
  exact ((hR.sumProd hS).reindex compEquiv).trace hne

/-- The parity corollary after Proposition 6, with nonempty output explicit. -/
theorem IsEvenDeltaMatroid.comp [Fintype ι] [Fintype κ] [Fintype τ]
    {R : Set ((ι ⊕ κ) → Bool)} {S : Set ((κ ⊕ τ) → Bool)}
    (hR : IsEvenDeltaMatroid R) (hS : IsEvenDeltaMatroid S)
    (hne : (comp R S).Nonempty) : IsEvenDeltaMatroid (comp R S) := by
  rw [comp_eq_trace] at hne ⊢
  exact ((hR.sumProd hS).reindex compEquiv).trace hne

/-- The relation with exactly one true coordinate. The coordinate type must be inhabited
for this relation to be a delta-matroid. -/
@[expose] def oneHotRelation (ι : Type*) [DecidableEq ι] : Set (ι → Bool) :=
  Set.range (fun i j : ι => decide (j = i))

/-- Exactly-one is an even delta-matroid of odd common parity.
This is Example 17 of [KazdaKolmogorovRolinek2018], printed p. 7, with a nonempty coordinate
type explicit: the arity-zero relation has no tuples and is excluded by Definition 5. -/
theorem isEvenDeltaMatroid_oneHotRelation [Fintype ι] [Nonempty ι] :
    IsEvenDeltaMatroid (oneHotRelation ι) where
  isDeltaMatroid := {
    nonempty := Set.range_nonempty _
    exchange := by
      rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩ i hi
      have hab : a ≠ b := by intro h; subst b; exact hi rfl
      have hiab : i = a ∨ i = b := by
        by_contra hn
        push Not at hn
        simp [hn.1, hn.2] at hi
      have hf : flipOn {a, b} (fun j => decide (j = a)) =
          (fun j => decide (j = b)) := by
        ext j
        by_cases hja : j = a <;> by_cases hjb : j = b <;> simp_all [flipOn]
      rcases hiab with hi | hi
      · subst i
        exact ⟨b, by simp [hab.symm], b, hf.symm⟩
      · subst i
        exact ⟨a, by simp [hab], b, by simpa only [pair_comm] using hf.symm⟩ }
  parity_eq := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    have hp (a : ι) : parityOn univ (fun j => decide (j = a)) = true := by
      have he : {j ∈ (univ : Finset ι) | j = a} = {a} := by ext j; simp
      simp only [parityOn, decide_eq_true_eq, he, card_singleton]
    rw [hp, hp]

/-- The even star gadget in Section 5.3 of [KazdaKolmogorovRolinek2018], printed p. 12.
It accepts all-zero, and each tuple with one internal bit and the final connector true.
It is exactly-one twisted at the connector, rather than exactly-one on all ports. -/
@[expose] def star (κ : Type*) [DecidableEq κ] : Set ((κ ⊕ Unit) → Bool) :=
  flipOn {Sum.inr ()} ⁻¹' oneHotRelation (κ ⊕ Unit)

/-- The star relation is an even delta-matroid, including with no internal coordinates. -/
theorem isEvenDeltaMatroid_star [Fintype κ] : IsEvenDeltaMatroid (star κ) :=
  isEvenDeltaMatroid_oneHotRelation.twist {Sum.inr ()}

/-- The star's two cases: all internal bits zero, or exactly one true internal bit.
The connector is false in the first case and true in the second. -/
theorem mem_star_iff {x : (κ ⊕ Unit) → Bool} : x ∈ star κ ↔
    ((∀ k, x (.inl k) = false) ∧ x (.inr ()) = false) ∨
      ∃ k, (∀ j, x (.inl j) = decide (j = k)) ∧ x (.inr ()) = true := by
  constructor
  · rintro ⟨k | u, hk⟩
    · right
      refine ⟨k, ?_, ?_⟩
      · intro j
        have h := congrFun hk (.inl j)
        simpa [flipOn] using h.symm
      · have h := congrFun hk (.inr ())
        simpa [flipOn] using h.symm
    · left
      constructor
      · intro j
        have h := congrFun hk (.inl j)
        simpa [flipOn] using h.symm
      · have h := congrFun hk (.inr ())
        simpa [flipOn] using h.symm
  · rintro (⟨hx, hc⟩ | ⟨k, hx, hc⟩)
    · refine ⟨.inr (), ?_⟩
      ext (j | u) <;> simp [flipOn, hx, hc]
    · refine ⟨.inl k, ?_⟩
      ext (j | u) <;> simp [flipOn, hx, hc]

/-- The star gadget based at an arbitrary internal reference tuple; its connector reference
is false. Only the internal coordinates are twisted. -/
@[expose] def starAt [Fintype κ] (reference : κ → Bool) : Set ((κ ⊕ Unit) → Bool) :=
  flipOn (univ.filter (fun i => Sum.elim reference (fun _ : Unit => false) i = true)) ⁻¹' star κ

/-- The reference-based star remains even. -/
theorem isEvenDeltaMatroid_starAt [Fintype κ] (reference : κ → Bool) :
    IsEvenDeltaMatroid (starAt reference) :=
  isEvenDeltaMatroid_star.twist _

/-- Membership in the reference-based star records zero or one internal deviations. -/
theorem mem_starAt_iff [Fintype κ] (reference : κ → Bool) {x : (κ ⊕ Unit) → Bool} :
    x ∈ starAt reference ↔
      ((∀ k, (x (.inl k) != reference k) = false) ∧ x (.inr ()) = false) ∨
        ∃ k, (∀ j, (x (.inl j) != reference j) = decide (j = k)) ∧
          x (.inr ()) = true := by
  change flipOn _ x ∈ star κ ↔ _
  rw [mem_star_iff]
  have hi (k : κ) :
      flipOn (univ.filter
        (fun i => Sum.elim reference (fun _ : Unit => false) i = true)) x (.inl k) =
        (x (.inl k) != reference k) := by
    cases hr : reference k <;> cases hx : x (.inl k) <;> simp [flipOn, hr, hx]
  have hc : flipOn (univ.filter
      (fun i => Sum.elim reference (fun _ : Unit => false) i = true)) x
      (.inr ()) = x (.inr ()) := by simp [flipOn]
  simp only [hi, hc]

end Cslib.BitString
