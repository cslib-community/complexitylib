/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Restore
import Mathlib.Data.List.GetD

/-!
# An actual connector entry yields an original local exchange

The first-connector step in Lemma 44 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
printed p. 21, reads a stored row of the simultaneous whole-constraint contraction. Its single
internal deviation identifies an actual original port, even at repeated constraints.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table DAG Finset

variable {F : CSP Table ℕ}

private theorem oldPort_ne_connector (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence F) (ho : o.var ∉ vs) (i : Fin F.length) (hi : i ∈ touched F vs) :
    oldPort f vs o ho ≠ connectorPort f vs i hi := by
  intro he
  have hv := congrArg Occurrence.var he
  rw [oldPort_var, connectorPort_var] at hv
  exact connector_not_mem i (hv ▸ o.var_mem)

/-- A feasible first connector move identifies a feasible original two-port move. The current
original labels may have arbitrary changed outside values; their internal bits are the reference. -/
theorem exchange_of_connector (hF : EdgeInstance F) {f current : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hcurrent : ValidLabeling sem current) (vs : List ℕ)
    (hinside : ∀ o : Occurrence F, o.var ∈ vs → current o = f o)
    (o : Occurrence F) (ho : o.var ∉ vs) (ht : o.1 ∈ touched F vs) (central : List Bool)
    (hnew : ValidLabeling sem (pairFlip (transport f vs current (fun _ => false) central)
      (oldPort f vs o ho) (connectorPort f vs o.1 ht))) :
    ∃ e : Occurrence F, e.1 = o.1 ∧ e.var ∈ vs ∧
      ValidLabeling sem (pairFlip current o e) := by
  cases o with | mk i oj =>
  let o : Occurrence F := ⟨i, oj⟩
  let ps := positions vs F[i.val].2
  let os := outsidePositions F[i.val].2.length ps
  let a := oldPort f vs o ho
  let c := connectorPort f vs i ht
  let before := transport f vs current (fun _ => false) central
  let after := pairFlip before a c
  let row := localTuple after c.1
  have hac : a ≠ c := oldPort_ne_connector f vs o ho i ht
  have hct : after c = true := by
    change pairFlip before a c c = true
    rw [pairFlip_eq _ hac]
    simp [BitString.flipOn_apply, c, before, transport_connectorPort]
  have hguard := canContract_constraint hf vs i
  have hrow : (F[i.val].1.contract (localTuple f i) ps).sem row = true := by
    have hv := hnew c.1
    change (contract f vs)[i.val].1.sem row = true at hv
    rw [get_contract_old] at hv
    have hp : (positions vs F[i.val].2).isEmpty = false := by
      simpa only [List.isEmpty_eq_false_iff] using (mem_touched vs i).mp ht
    simpa only [constraint, hp, Bool.false_eq_true, ↓reduceIte] using hv
  obtain ⟨old, _, hm, hd, he⟩ := contractWitness_spec hguard hrow
  have hsem : F[i.val].1.sem old = true :=
    sem_eq_true.mpr ⟨(canContract_eq_true.mp hguard).1, hm⟩
  have hrefLen : (localTuple f i).length = F[i.val].2.length := by simp [localTuple]
  rw [hrefLen] at he
  have holdlen : old.length = F[i.val].2.length := by
    have hh := canContract_eq_true.mp hguard
    have hflen := (wellFormed_eq_true.mp hh.1) (localTuple f i) hh.2.1
    exact ((wellFormed_eq_true.mp hh.1) old hm).trans (hflen.symm.trans hrefLen)
  have hdev : deviations (localTuple f i) old ps = 1 := by
    have hh := congrArg (fun r => r.getD os.length false) he
    change (project old os ++ [decide (deviations (localTuple f i) old ps = 1)]).getD
      os.length false = row.getD os.length false at hh
    rw [List.getD_append_right _ _ _ _ (by simp [project])] at hh
    simp only [project, List.length_map, Nat.sub_self, List.getD_cons_zero] at hh
    have hread : row.getD os.length false = after c := by
      change (localTuple after c.1).getD c.2.val false = after c
      simp [localTuple, c.2.isLt]
    rw [hread, hct] at hh
    exact of_decide_eq_true hh
  obtain ⟨j, hj, hjdiff, hothers⟩ := deviations_eq_one hdev
  have hjb : j < F[i.val].2.length := List.mem_range.mp (List.mem_filter.mp hj).1
  let e : Occurrence F := ⟨i, ⟨j, hjb⟩⟩
  have hev : e.var ∈ vs := (mem_positions vs i ⟨j, hjb⟩).mp hj
  have hoe : o ≠ e := fun he => ho (congrArg Occurrence.var he ▸ hev)
  refine ⟨e, rfl, hev, ?_⟩
  -- The following pointwise row comparison identifies the stored witness with the actual
  -- original two-port exchange; it retains every outside coordinate of the changed current row.
  apply (validLabeling_pairFlip_iff hcurrent i oj ⟨j, hjb⟩ (by
    intro hh
    exact hoe (congrArg (Sigma.mk i) hh))).mpr
  have heq : List.ofFn (BitString.flipOn {oj, (⟨j, hjb⟩ : Fin F[i.val].2.length)}
      (fun k => current ⟨i, k⟩)) = old := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using holdlen.symm
    · intro k hk hko
      have hkb : k < F[i.val].2.length := by simpa only [List.length_ofFn] using hk
      let q : Occurrence F := ⟨i, ⟨k, hkb⟩⟩
      have hqref : (localTuple f i).getD k false = f q := by simp [localTuple, q, hkb]
      by_cases hkp : k ∈ ps
      · have hqv := (mem_positions vs i ⟨k, hkb⟩).mp hkp
        have hqcur := hinside q hqv
        have hko0 : k ≠ oj.val := by
          intro hh
          have hqo : q = o := congrArg (Sigma.mk i) (Fin.ext hh)
          exact ho (congrArg Occurrence.var hqo ▸ hqv)
        have hfinO : (⟨k, hkb⟩ : Fin F[i.val].2.length) ≠ oj := fun hh =>
          hko0 (congrArg Fin.val hh)
        by_cases hkj : k = j
        · have hdiff : old.getD k false ≠ f q := by
            have hh := hjdiff
            rw [← hkj, hqref] at hh
            exact hh
          have hmem : (⟨k, hkb⟩ : Fin F[i.val].2.length) ∈
              ({oj, ⟨j, hjb⟩} : Finset (Fin F[i.val].2.length)) :=
            mem_insert.mpr (Or.inr (mem_singleton.mpr (Fin.ext hkj)))
          simp only [List.getElem_ofFn, BitString.flipOn_apply, hmem, ↓reduceIte]
          change (!current q) = old[k]
          rw [← List.getD_eq_getElem old false hko, hqcur]
          cases hfq : f q <;> cases hoq : old.getD k false <;> simp_all
        · have heold := hothers k hkp hkj
          rw [hqref] at heold
          have hmem : (⟨k, hkb⟩ : Fin F[i.val].2.length) ∉
              ({oj, ⟨j, hjb⟩} : Finset (Fin F[i.val].2.length)) := by
            simp only [mem_insert, mem_singleton, not_or]
            exact ⟨hfinO, fun hh => hkj (congrArg Fin.val hh)⟩
          simp only [List.getElem_ofFn, BitString.flipOn_apply, hmem, ↓reduceIte]
          exact hqcur.trans ((List.getD_eq_getElem old false hko).symm.trans heold).symm
      · have hqout : q.var ∉ vs := by
          exact (mem_positions vs i ⟨k, hkb⟩).not.mp hkp
        have hkos : k ∈ os := (mem_outsidePositions vs F[i.val].2 k).mpr
          ⟨hkb, by simpa only [List.getD_eq_getElem _ _ hkb, Occurrence.var] using hqout⟩
        have hidx := List.idxOf_lt_length_iff.mpr hkos
        have hh := congrArg (fun r => r.getD (os.idxOf k) false) he
        change (project old os ++ [decide (deviations (localTuple f i) old ps = 1)]).getD
          (os.idxOf k) false = row.getD (os.idxOf k) false at hh
        rw [List.getD_append _ _ _ _ (by simpa [project] using hidx),
          project_getD_idxOf _ _ hkos] at hh
        have hread : row.getD (os.idxOf k) false = after (oldPort f vs q hqout) := by
          change (localTuple after (oldPort f vs q hqout).1).getD
            (oldPort f vs q hqout).2.val false = _
          simp [localTuple, (oldPort f vs q hqout).2.isLt]
        rw [hread] at hh
        have hqc := oldPort_ne_connector f vs q hqout i ht
        change oldPort f vs q hqout ≠ c at hqc
        have hqa : oldPort f vs q hqout = a ↔ k = oj.val := by
          constructor
          · intro hh
            have hqo := oldPort_injective hF f vs hqout ho hh
            exact congrArg (fun o : Occurrence F => o.2.val) hqo
          · intro hh
            have hqo : q = o := congrArg (Sigma.mk i) (Fin.ext hh)
            exact congrArg (fun p : {a : Occurrence F // a.var ∉ vs} =>
              oldPort f vs p.val p.property) (Subtype.ext hqo :
                (⟨q, hqout⟩ : {a : Occurrence F // a.var ∉ vs}) = ⟨o, ho⟩)
        have hkj : k ≠ j := fun heq => hkp (heq ▸ hj)
        change old.getD k false = pairFlip before a c (oldPort f vs q hqout) at hh
        rw [pairFlip_eq _ hac] at hh
        simp only [BitString.flipOn_apply, mem_insert, mem_singleton, hqa, hqc, or_false,
          before, transport_oldPort] at hh
        have hmem : (⟨k, hkb⟩ : Fin F[i.val].2.length) ∈
            ({oj, ⟨j, hjb⟩} : Finset (Fin F[i.val].2.length)) ↔ k = oj.val := by
          simp [Fin.ext_iff, hkj]
        simp only [List.getElem_ofFn, BitString.flipOn_apply, hmem]
        exact hh.symm.trans (List.getD_eq_getElem old false hko)
  exact (congrArg F[i.val].1.sem heq).trans hsem

end Cslib.Logic.PL.CSP.Blossom
