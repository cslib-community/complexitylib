/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Edge.DAGSurgery

/-!
# Attaching an external port to a timestamped incidence DAG

The last part of Lemma 44 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
printed pp. 21–22, attaches an outside variable to a selected copied blossom constraint.
The finite support permits either orientation: an external source receives a rank below the
old graph, and an external sink receives a rank above its maximum. No timestamp renumbering
or minimum-timestamp predecessor is needed.
The cut/completion lemmas below are an original unified argument for the source's
attachment cases; they retain all six `IsFDAG` invariants.
-/

public section

namespace Cslib.Logic.PL.CSP.DAG

open Finset

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]
  {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool} {T : DAG F}

omit [DecidableEq V] in
/-- A paired subgraph contains every ambient arc at each of its copied nodes. -/
theorem PairedCopies.full_copy {S : DAG F} (hT : T.PairedCopies) (hS : S.PairedCopies)
    (hst : S.Subgraph T) {e : Arc F} (he : e ∈ T.arcs) (hc : e.copy ∈ S.copies) :
    e ∈ S.arcs := by
  obtain ⟨a, ha, b, hb, _, hac, hbc, hab, hpairS⟩ := hS e.copy hc
  obtain ⟨c, hcm, d, hdm, _, hcc, hdc, _, hpairT⟩ := hT e.copy (hst.2.1 hc)
  have hea := hpairT a (hst.2.2 ha) hac
  have heb := hpairT b (hst.2.2 hb) hbc
  rcases hpairT e he rfl with rfl | rfl
  · rcases hea with rfl | hea
    · exact ha
    · rcases heb with rfl | heb
      · exact hb
      · exact (hab (hea.trans heb.symm)).elim
  · rcases hea with hea | rfl
    · rcases heb with heb | rfl
      · exact (hab (hea.trans heb.symm)).elim
      · exact hb
    · exact ha

/-- Keep whole selected copies and one boundary arc at a further copy. Isolated old variables
remain in the support, so externality can still be checked against the original blossom. -/
@[expose] def cutAt (T : DAG F) (cs : Finset (Copy F)) (a : Arc F) : DAG F where
  vars := T.vars
  copies := insert a.copy (T.copies ∩ cs)
  arcs := T.arcs.filter fun e => e.copy ∈ cs ∨ e = a

omit [DecidableEq V] in
/-- Cutting at an actual arc is a supported subgraph operation. -/
theorem Supported.cutAt (h : T.Supported) (cs : Finset (Copy F)) (a : Arc F) :
    (T.cutAt cs a).Supported := by
  intro e he
  obtain ⟨he, hc | hea⟩ := mem_filter.mp he
  · exact ⟨(h e he).1, mem_insert_of_mem (mem_inter.mpr ⟨(h e he).2, hc⟩)⟩
  · exact ⟨(h e he).1, hea ▸ mem_insert_self _ _⟩

omit [DecidableEq V] in
/-- Cutting deletes actual arcs and copies only. -/
theorem cutAt_subgraph (T : DAG F) (cs : Finset (Copy F)) {a : Arc F}
    (ha : a ∈ T.arcs) (hs : T.Supported) : (T.cutAt cs a).Subgraph T := by
  refine ⟨Subset.rfl, ?_, fun _ he => (mem_filter.mp he).1⟩
  intro c hc
  rcases mem_insert.mp hc with rfl | hc
  · exact (hs a ha).2
  · exact (mem_inter.mp hc).1

omit [DecidableEq V] in
/-- Every copy of the cut has its old pair, except the selected boundary copy, which has
exactly its selected arc. This is the structural certificate used before attaching a port. -/
theorem PairedCopies.cutAt {cs : Finset (Copy F)} {a : Arc F}
    (hp : T.PairedCopies) (hc : a.copy ∉ cs) :
    (∀ e ∈ (T.cutAt cs a).arcs, e.copy = a.copy → e = a) ∧
      ∀ c ∈ (T.cutAt cs a).copies, c ≠ a.copy →
        ∃ b ∈ (T.cutAt cs a).arcs, ∃ d ∈ (T.cutAt cs a).arcs,
          b.incoming = true ∧ b.copy = c ∧ d.copy = c ∧ b ≠ d ∧
            ∀ e ∈ (T.cutAt cs a).arcs, e.copy = c → e = b ∨ e = d := by
  constructor
  · intro e he hec
    rcases (mem_filter.mp he).2 with hecs | hea
    · exact (hc (hec ▸ hecs)).elim
    · exact hea
  · intro c hcm hca
    have hcs := (mem_inter.mp ((mem_insert.mp hcm).resolve_left hca)).2
    have hct := (mem_inter.mp ((mem_insert.mp hcm).resolve_left hca)).1
    obtain ⟨b, hb, d, hd, hbi, hbc, hdc, hbd, hall⟩ := hp c hct
    exact ⟨b, mem_filter.mpr ⟨hb, Or.inl (hbc ▸ hcs)⟩,
      d, mem_filter.mpr ⟨hd, Or.inl (hdc ▸ hcs)⟩, hbi, hbc, hdc, hbd,
      fun e he hec => hall e (mem_filter.mp he).1 hec⟩

omit [DecidableEq V] in
/-- Cutting at the end of a paired subgraph retains its precise original arcs and the one
boundary arc. This identifies the eventual flip with an actual arm of the cycle. -/
theorem cutAt_arcs {S : DAG F} (hT : T.PairedCopies) (hS : S.PairedCopies)
    (hst : S.Subgraph T) (hs : S.Supported) {a : Arc F} (ha : a ∈ T.arcs) :
    (T.cutAt S.copies a).arcs = insert a S.arcs := by
  ext e
  constructor
  · intro he
    obtain ⟨het, hc | rfl⟩ := mem_filter.mp he
    · exact mem_insert_of_mem (hT.full_copy hS hst het hc)
    · exact mem_insert_self _ _
  · intro he
    rcases mem_insert.mp he with rfl | he
    · exact mem_filter.mpr ⟨ha, Or.inr rfl⟩
    · exact mem_filter.mpr ⟨hst.2.2 he, Or.inl (hs e he).2⟩

/-- Attach one actual original port at an already supported copied constraint. -/
@[expose] def attachPort (T : DAG F) (a : Arc F) : DAG F where
  vars := insert a.occurrence.var T.vars
  copies := T.copies
  arcs := insert a T.arcs

/-- Attaching an outside source or sink preserves all six f-DAG conditions when the local
pair is feasible and the before/after forbidden moves hold. Blossom lifting derives these
forbidden moves by selecting the first accessible input or the last accessible output. -/
theorem IsFDAG.attachPort (h : T.IsFDAG sem f) (a : Arc F)
    (hx : a.occurrence.var ∉ T.vars) (hc : a.copy ∈ T.copies)
    (hp : ∀ b ∈ T.arcs, a.copy = b.copy → ValidLabeling sem (pairFlip f a.occurrence b.occurrence))
    (hbefore : ∀ b ∈ T.arcs, b.incoming = true → b.occurrence.1 = a.occurrence.1 →
      b.time < a.time → ¬ ValidLabeling sem (pairFlip f b.occurrence a.occurrence))
    (hafter : a.incoming = true → ∀ b ∈ T.arcs,
      a.occurrence.1 = b.occurrence.1 → a.time < b.time →
        ¬ ValidLabeling sem (pairFlip f a.occurrence b.occurrence)) :
    (T.attachPort a).IsFDAG sem f := by
  have hvar : ∀ b ∈ T.arcs, b.occurrence.var ≠ a.occurrence.var := by
    intro b hb he
    exact hx (he ▸ (h.supported b hb).1)
  refine ⟨h.valid, ?_, ?_, ?_, ⟨h.ordered.1, ?_⟩, ?_, ?_⟩
  · intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact ⟨mem_insert_self _ _, hc⟩
    · exact ⟨mem_insert_of_mem (h.supported b hb).1, (h.supported b hb).2⟩
  · intro b hb c hc he
    rcases mem_insert.mp hb with hba | hb0 <;> rcases mem_insert.mp hc with hca | hc0
    · exact hba.trans hca.symm
    · subst b
      exact ((hvar c hc0) (congrArg Occurrence.var he).symm).elim
    · subst c
      exact ((hvar b hb0) (congrArg Occurrence.var he)).elim
    · exact h.unique b hb0 c hc0 he
  · intro b hb c hc hbi hci he
    rcases mem_insert.mp hb with hba | hb0 <;> rcases mem_insert.mp hc with hca | hc0
    · exact hba.trans hca.symm
    · subst b
      exact ((hvar c hc0) he.symm).elim
    · subst c
      exact ((hvar b hb0) he).elim
    · exact h.indegree b hb0 c hc0 hbi hci he
  · obtain ⟨oldRank, hr⟩ := h.ordered.2
    let top := T.nodes.sup oldRank
    let rank (n : Node F) :=
      if n = .inl a.occurrence.var then (if a.incoming then 0 else top + 2) else oldRank n + 1
    have hbound : oldRank (.inr a.copy) ≤ top :=
      le_sup (mem_disjSum.mpr (Or.inr ⟨a.copy, hc, rfl⟩))
    have hends : ∀ b ∈ T.arcs,
        b.source ≠ .inl a.occurrence.var ∧ b.target ≠ .inl a.occurrence.var := by
      intro b hb
      cases he : b.incoming <;> simp [Arc.source, Arc.target, he, hvar b hb]
    refine ⟨rank, ?_⟩
    intro x y hxy
    rcases hxy with ⟨b, hb, rfl, rfl⟩ | ⟨c, hc, d, hd, hcd, rfl, rfl⟩
    · rcases mem_insert.mp hb with hba | hb0
      · subst b
        cases he : a.incoming with
        | false => simp [rank, Arc.source, Arc.target, he]; omega
        | true => simp [rank, Arc.source, Arc.target, he]
      · have hh := hr _ _ (Or.inl ⟨b, hb0, rfl, rfl⟩)
        simpa only [rank, ite_eq_right (hends b hb0).1, ite_eq_right (hends b hb0).2] using
          Nat.add_lt_add_right hh 1
    · have hh := hr _ _ (Or.inr ⟨c, hc, d, hd, hcd, rfl, rfl⟩)
      simpa only [rank, Sum.inr_ne_inl, ↓reduceIte] using Nat.add_lt_add_right hh 1
  · intro b hb c hc hbi he
    rcases mem_insert.mp hb with hba | hb0 <;> rcases mem_insert.mp hc with hca | hc0
    · subst b
      subst c
      simpa only [pairFlip_self] using h.valid
    · subst b
      exact hp c hc0 he
    · subst c
      rw [pairFlip_comm]
      exact hp b hb0 he.symm
    · exact h.feasible b hb0 c hc0 hbi he
  · intro b hb c hc hbi he ht
    rcases mem_insert.mp hb with hba | hb0 <;> rcases mem_insert.mp hc with hca | hc0
    · subst b
      subst c
      omega
    · subst b
      exact hafter hbi c hc0 he ht
    · subst c
      exact hbefore b hb0 hbi he ht
    · exact h.noShortcut b hb0 c hc0 hbi he ht

/-- Complete a cut blossom arm by one external port. The missing copy receives precisely
the boundary port and its external mate; all other retained copies keep their original pair.
The before/after conditions are local finite tests, discharged by the first-input/last-output
selection in blossom lifting. -/
theorem IsFDAG.valid_complete_cut (h : T.IsFDAG sem f) (hp : T.PairedCopies)
    (hM : EdgeInstance.EvenConstraints sem F) (cs : Finset (Copy F)) {a : Arc F}
    (ha : a ∈ T.arcs) (hc : a.copy ∉ cs) (x : Occurrence F)
    (hx : x.var ∉ T.vars) (hxa : x.1 = a.occurrence.1)
    (hv : ValidLabeling sem (pairFlip f x a.occurrence))
    (hbefore : ∀ e ∈ T.arcs, e.incoming = true → e.occurrence.1 = x.1 →
      e.time < a.time → ¬ ValidLabeling sem (pairFlip f e.occurrence x))
    (hafter : a.incoming = false → ∀ e ∈ T.arcs,
      x.1 = e.occurrence.1 → a.time < e.time →
        ¬ ValidLabeling sem (pairFlip f x e.occurrence)) :
    ValidLabeling sem (((T.cutAt cs a).attachPort
      ⟨x, a.time, !a.incoming⟩).flip f) := by
  let b : Arc F := ⟨x, a.time, !a.incoming⟩
  let S := T.cutAt cs a
  have hbc : b.copy = a.copy := Prod.ext hxa rfl
  have hS := h.subgraph (cutAt_subgraph T cs ha h.supported) (h.supported.cutAt cs a)
  have hparts := hp.cutAt hc
  have has : a ∈ S.arcs := mem_filter.mpr ⟨ha, Or.inr rfl⟩
  have hbs : b.copy ∈ S.copies := hbc ▸ mem_insert_self _ _
  have hab : a ≠ b := by
    intro he
    exact hx ((congrArg (fun e : Arc F => e.occurrence.var) he) ▸ (h.supported a ha).1)
  have hnew : (S.attachPort b).IsFDAG sem f := hS.attachPort b hx hbs (by
    intro e he hec
    have hea := hparts.1 e he (hec.symm.trans hbc)
    subst e
    exact hv) (fun e he hei hex het =>
      hbefore e (mem_filter.mp he).1 hei hex het) (by
        intro hbi e he hex het
        have hai : a.incoming = false := by simpa [b] using hbi
        exact hafter hai e (mem_filter.mp he).1 hex het)
  apply hnew.valid_flip_of_pairedCopies hM
  intro c hcm
  by_cases hec : c = a.copy
  · subst c
    have hpair : ∀ e ∈ (S.attachPort b).arcs, e.copy = a.copy → e = a ∨ e = b := by
      intro e he hec
      rcases mem_insert.mp he with rfl | he
      · exact Or.inr rfl
      · exact Or.inl (hparts.1 e he hec)
    cases hai : a.incoming with
    | false =>
      exact ⟨b, mem_insert_self _ _, a, mem_insert_of_mem has, by simp [b, hai],
        hbc, rfl, hab.symm, fun e he hec => (hpair e he hec).symm⟩
    | true =>
      exact ⟨a, mem_insert_of_mem has, b, mem_insert_self _ _, hai,
        rfl, hbc, hab, hpair⟩
  · obtain ⟨d, hd, e, he, hdi, hdc, hec0, hde, hall⟩ := hparts.2 c hcm hec
    refine ⟨d, mem_insert_of_mem hd, e, mem_insert_of_mem he, hdi, hdc, hec0, hde, ?_⟩
    intro q hq hqc
    rcases mem_insert.mp hq with rfl | hq
    · exact (hec (hqc.symm.trans hbc)).elim
    · exact hall q hq hqc

end Cslib.Logic.PL.CSP.DAG
