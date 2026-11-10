/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk
import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Operations

/-!
# Constructing an augmenting walk from an improving labeling

The two phases of Lemma 31 in [KazdaKolmogorovRolinek2018], arXiv v6, Section 6.1,
printed p. 15, use deterministic scans of the actual positional incidence records. The first
phase repairs defects of the comparison labeling outside the original defect set; the second
phase follows remaining disagreements. Each exchange removes exactly two disagreements.
The clock counts exchanges, not native-machine steps; native encoding and runtime certification
belong to the solver integration. An improving valid comparison labeling is an input, not an
assumed solver result. The construction works for any specified excluded start, strengthening
the source's hypothesis that this variable is inconsistent; it may be the terminal variable.

## Main definitions

* `incidenceList`: deterministic typed positional incidence scan.
* `EdgeInstance.repair`, `EdgeInstance.buildWalk`: the two clocked exchange phases.
* `EdgeInstance.augmentingWalk`: their total, choice-free composition.

## Main results

* `EdgeInstance.repair_spec`, `EdgeInstance.buildWalk_spec`: phase invariants and exact progress.
* `EdgeInstance.augmentingWalk_spec`: Lemma 31 with a bound on the combined exchange count.
* `EdgeInstance.isOptimalLabeling_iff_no_augmentingWalk`: the augmenting-walk characterization.
-/

public section

namespace Cslib.Logic.PL.CSP

open BitString Finset
open scoped symmDiff

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

/-- Positional incidences in constraint order and then argument order. This is a typed view of
`CSP.occurrences`, without choosing representatives or identifying repeated constraints. -/
@[expose] def incidenceList (F : CSP Rel V) : List (Occurrence F) :=
  (List.ofFn fun i : Fin F.length =>
    List.ofFn fun j : Fin F[i].2.length => (⟨i, j⟩ : Occurrence F)).flatten

omit [DecidableEq V] in
/-- Every incidence appears in the deterministic scan. -/
theorem mem_incidenceList (o : Occurrence F) : o ∈ incidenceList F := by
  rcases o with ⟨i, j⟩
  exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩,
    List.mem_ofFn.mpr ⟨j, rfl⟩⟩

instance (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool) :
    Decidable (ValidLabeling sem f) :=
  inferInstanceAs (Decidable (∀ i : Fin F.length,
    sem F[i].1 (localTuple f i) = true))

namespace EdgeInstance

/-- First satisfying incidence pair in positional order. This scan examines pairs, not trails. -/
@[expose] def findPair (F : CSP Rel V) (P : Occurrence F × Occurrence F → Prop)
    [DecidablePred P] : Option (Occurrence F × Occurrence F) :=
  ((incidenceList F).product (incidenceList F)).find? fun a => decide (P a)

omit [DecidableEq V] in
/-- A returned scan pair satisfies the predicate. -/
theorem findPair_spec {P : Occurrence F × Occurrence F → Prop} [DecidablePred P]
    {a : Occurrence F × Occurrence F} (ha : findPair F P = some a) : P a := by
  have ht := List.find?_some (p := fun a => decide (P a)) ha
  exact of_decide_eq_true ht

omit [DecidableEq V] in
/-- A failed scan rules out every pair, since all incidences are enumerated. -/
theorem findPair_none {P : Occurrence F × Occurrence F → Prop} [DecidablePred P]
    (hn : findPair F P = none) (o p : Occurrence F) : ¬ P (o, p) := by
  have hm : (o, p) ∈ (incidenceList F).product (incidenceList F) :=
    List.mem_product.mpr ⟨mem_incidenceList o, mem_incidenceList p⟩
  have he := List.find?_eq_none.mp hn (o, p) hm
  simpa only [decide_eq_true_eq] using he

/-- A first-phase exchange repairs an f-consistent variable at which g has a new defect. -/
@[expose] def RepairMove (sem : Rel → List Bool → Bool)
    (f g : OccurrenceLabeling F Bool) (a : Occurrence F × Occurrence F) : Prop :=
  let (o, p) := a
  o.1 = p.1 ∧ o ≠ p ∧ g o ≠ f o ∧ g p ≠ f p ∧
    ¬ Inconsistent f o.var ∧ Inconsistent g o.var ∧
    ValidLabeling sem (flipOn {o, p} g)

instance (sem : Rel → List Bool → Bool) (f g : OccurrenceLabeling F Bool)
    (a : Occurrence F × Occurrence F) : Decidable (RepairMove sem f g a) :=
  inferInstanceAs (Decidable (a.1.1 = a.2.1 ∧ a.1 ≠ a.2 ∧ g a.1 ≠ f a.1 ∧ g a.2 ≠ f a.2 ∧
    ¬ Inconsistent f a.1.var ∧ Inconsistent g a.1.var ∧
    ValidLabeling sem (flipOn {a.1, a.2} g)))

/-- Clocked first phase. The second output counts exchanges. No choice or partner operation
occurs in this routine; an exhausted clock returns its current labeling. -/
@[expose] def repair (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool) :
    ℕ → OccurrenceLabeling F Bool → OccurrenceLabeling F Bool × ℕ
  | 0, g => (g, 0)
  | n + 1, g =>
    match findPair F (RepairMove sem f g) with
    | none => (g, 0)
    | some (o, p) =>
      let (g', k) := repair sem f n (flipOn {o, p} g)
      (g', k + 1)

omit [DecidableEq V] in
/-- A new defect provides a first-phase exchange using the local even delta-matroid axiom. -/
theorem exists_repairMove {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    {v : V} (hvf : ¬ Inconsistent f v) (hvg : Inconsistent g v) :
    ∃ a, RepairMove sem f g a := by
  obtain ⟨o, p, hov, hpv, hgp⟩ := hvg
  have hgf : g o ≠ f o ∨ g p ≠ f p := by
    by_contra hn
    push Not at hn
    have hfop : f o = f p := by
      by_contra hh
      exact hvf ⟨o, p, hov, hpv, hh⟩
    exact hgp (hn.1.trans (hfop.trans hn.2.symm))
  obtain ⟨a, hav, ha⟩ : ∃ a : Occurrence F, a.var = v ∧ g a ≠ f a := by
    rcases hgf with ho | hp
    · exact ⟨o, hov, ho⟩
    · exact ⟨p, hpv, hp⟩
  obtain ⟨b, hc, hne, hb, hv⟩ := exists_valid_exchange hM hg hf a ha
  refine ⟨(a, b), hc, hne, ha, hb, ?_, ?_, hv⟩
  · simpa only [hav] using hvf
  · rw [hav]
    exact ⟨o, p, hov, hpv, hgp⟩

/-- The clocked repair preserves validity and never increases defects. It removes two
occurrence disagreements per exchange, and a clock at least the initial Hamming distance
suffices to leave no new defects. -/
theorem repair_spec (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g) (fuel : ℕ) :
    let (g', k) := repair sem f fuel g
    ValidLabeling sem g' ∧ (defects g').card ≤ (defects g).card ∧
      hammingDist f g' + 2 * k = hammingDist f g ∧ k ≤ fuel ∧
      (hammingDist f g ≤ fuel → defects g' ⊆ defects f) := by
  induction fuel generalizing g with
  | zero =>
    refine ⟨hg, le_rfl, by simp, le_rfl, ?_⟩
    intro hd
    have he : f = g := hammingDist_eq_zero.mp (by omega)
    subst g
    exact Subset.rfl
  | succ n ih =>
    cases hs : findPair F (RepairMove sem f g) with
    | none =>
      simp only [repair, hs]
      refine ⟨hg, le_rfl, by simp, Nat.zero_le _, ?_⟩
      intro _ v hvg
      by_contra hvf
      obtain ⟨a, ha⟩ := exists_repairMove hM hf hg
        (mt mem_defects.mpr hvf) (mem_defects.mp hvg)
      exact findPair_none hs a.1 a.2 ha
    | some a =>
      rcases a with ⟨o, p⟩
      obtain ⟨hc, hne, ho, hp, hcf, hcg, hv⟩ := findPair_spec hs
      have hrec := ih hv
      have hd := hammingDist_flipOn_pair_add_two hne ho hp
      have hcard := h.card_defects_flipOn_pair_le g hne hcg
      simp only [repair, hs]
      dsimp only at hrec ⊢
      refine ⟨hrec.1, hrec.2.1.trans hcard, ?_, by omega, ?_⟩
      · rw [hammingDist_comm g f, hammingDist_comm (flipOn {o, p} g) f] at hd
        omega
      · intro hb
        apply hrec.2.2.2.2
        rw [hammingDist_comm g f, hammingDist_comm (flipOn {o, p} g) f] at hd
        omega

/-- Two fewer defects and containment provide a starting defect different from any specified
variable. Only the start is excluded; the walk may end at that variable. -/
theorem exists_start_ne (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    (hlt : (defects g).card < (defects f).card) (x : V) :
    ∃ r, r ≠ x ∧ Inconsistent f r ∧ ¬ Inconsistent g r := by
  have hp := h.card_defects_mod_two_eq hM hf hg
  have htwo : (defects g).card + 2 ≤ (defects f).card := by omega
  by_contra hn
  have hcover : defects f ⊆ insert x (defects g) := by
    intro v hv
    by_cases he : v = x
    · exact mem_insert.mpr (Or.inl he)
    · have hm : Inconsistent g v := by
        by_contra hh
        exact hn ⟨v, he, mem_defects.mp hv, hh⟩
      exact mem_insert_of_mem (mem_defects.mpr hm)
  have hb := card_le_card hcover
  have hi := card_insert_le x (defects g)
  omega

/-- A second-phase move follows an incidence disagreement at the current endpoint. -/
@[expose] def WalkMove (sem : Rel → List Bool → Bool)
    (g current : OccurrenceLabeling F Bool) (v : V)
    (a : Occurrence F × Occurrence F) : Prop :=
  let (o, p) := a
  o.var = v ∧ o.1 = p.1 ∧ o ≠ p ∧ current o ≠ g o ∧ current p ≠ g p ∧
    ValidLabeling sem (flipOn {o, p} current)

instance (sem : Rel → List Bool → Bool) (g current : OccurrenceLabeling F Bool)
    (v : V) (a : Occurrence F × Occurrence F) : Decidable (WalkMove sem g current v a) :=
  inferInstanceAs (Decidable (a.1.var = v ∧ a.1.1 = a.2.1 ∧ a.1 ≠ a.2 ∧
    current a.1 ≠ g a.1 ∧ current a.2 ≠ g a.2 ∧
    ValidLabeling sem (flipOn {a.1, a.2} current)))

/-- Clocked second phase. It extends the current trail by one local exchange and stops on the
first original defect reached. The scan and recursion contain no noncomputable choice. -/
@[expose] def buildWalk (sem : Rel → List Bool → Bool)
    (f g : OccurrenceLabeling F Bool) : ℕ → Walk F → Option (Walk F)
  | 0, _ => none
  | n + 1, w =>
    match findPair F (WalkMove sem g (w.flip f) w.finish) with
    | none => none
    | some (o, p) =>
      let w' := w.snoc o p
      if Inconsistent f p.var then some w' else buildWalk sem f g n w'

omit [DecidableEq V] in
private theorem exists_disagreement {f g : OccurrenceLabeling F Bool} {v : V}
    (hf : Inconsistent f v) (hg : ¬ Inconsistent g v) :
    ∃ o : Occurrence F, o.var = v ∧ f o ≠ g o := by
  obtain ⟨o, p, hov, hpv, hop⟩ := hf
  by_cases ho : f o = g o
  · refine ⟨p, hpv, ?_⟩
    intro hp
    exact hg ⟨o, p, hov, hpv, by rwa [← ho, ← hp]⟩
  · exact ⟨o, hov, ho⟩

omit [DecidableEq V] in
/-- A defective current endpoint, consistent in the target, always admits an exchange. -/
theorem exists_walkMove {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {g current : OccurrenceLabeling F Bool}
    (hg : ValidLabeling sem g) (hc : ValidLabeling sem current) {v : V}
    (hcv : Inconsistent current v) (hgv : ¬ Inconsistent g v) :
    ∃ a, WalkMove sem g current v a := by
  obtain ⟨o, hov, ho⟩ := exists_disagreement hcv hgv
  obtain ⟨p, hcon, hne, hp, hv⟩ := exists_valid_exchange hM hc hg o ho
  exact ⟨(o, p), hov, hcon, hne, ho, hp, hv⟩

omit [DecidableEq V] in
private theorem other_endpoint_eq (h : EdgeInstance F)
    {f g : OccurrenceLabeling F Bool} {o a : Occurrence F}
    (hf : Inconsistent f o.var) (hg : ¬ Inconsistent g o.var) (ho : f o ≠ g o)
    (ha : a.var = o.var) (hne : a ≠ o) : f a = g a := by
  have hi := (h.inconsistent_iff f o).mp hf
  have hj := not_not.mp (mt (h.inconsistent_iff g o).mpr hg)
  rcases h.eq_or_eq_partner ha with he | he
  · exact (hne he).elim
  · subst a
    cases hf0 : f o <;> cases hf1 : f (h.partner o) <;>
      cases hg0 : g o <;> cases hg1 : g (h.partner o) <;> simp_all

/-- The second-phase invariant. Already-used incidences agree with the target, so scans of
remaining disagreements cannot reuse them. Once the first step is taken, every incidence of
the starting variable agrees with the target, preventing a return to that start. -/
structure WalkState (sem : Rel → List Bool → Bool)
    (f g : OccurrenceLabeling F Bool) (w : Walk F) : Prop where
  prefix_valid : w.IsFPrefix sem f
  endpoint_defect : Inconsistent (w.flip f) w.finish
  target_endpoint : ¬ Inconsistent g w.finish
  internal_endpoint : w.steps = [] ∨ ¬ Inconsistent f w.finish
  start_defect : Inconsistent f w.start
  target_start : ¬ Inconsistent g w.start
  used_agrees : ∀ a ∈ w.edges, w.flip f a = g a
  start_cleared : w.steps ≠ [] → ∀ a, a.var = w.start → w.flip f a = g a

private theorem WalkState.extend (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} {f g : OccurrenceLabeling F Bool} {w : Walk F}
    (hw : WalkState sem f g w) (hsub : defects g ⊆ defects f)
    {o p : Occurrence F} (hm : WalkMove sem g (w.flip f) w.finish (o, p)) :
    (w.snoc o p).IsFPrefix sem f ∧ p.var ≠ w.start ∧
      (¬ Inconsistent f p.var → WalkState sem f g (w.snoc o p)) := by
  obtain ⟨hov, hc, hne, ho, hp, hv⟩ := hm
  have hno : o ∉ w.edges := fun he => ho (hw.used_agrees o he)
  have hnp : p ∉ w.edges := fun he => hp (hw.used_agrees p he)
  have hvar := h.var_ne_of_constraint_eq hc hne
  have hps : p.var ≠ w.start := by
    by_cases he : w.steps = []
    · have hfin : w.finish = w.start := by simp [Walk.finish, he, Walk.finishFrom]
      exact fun hh => hvar (hov.trans (hfin.trans hh.symm))
    · exact fun hh => hp (hw.start_cleared he p hh)
  have hvp := hw.prefix_valid.snoc hov hc hne hno hnp hw.internal_endpoint hv
  have hflip := Walk.flip_snoc w f o p hw.prefix_valid.1 hno hnp hne
  have hused : ∀ a ∈ (w.snoc o p).edges, (w.snoc o p).flip f a = g a := by
    intro a ha
    have he : (w.snoc o p).edges = w.edges ++ [o, p] := by
      exact Walk.edgesOf_append _ _
    rw [he, List.mem_append] at ha
    rw [hflip]
    rcases ha with ha | ha
    · have hao : a ≠ o := fun he => hno (he ▸ ha)
      have hap : a ≠ p := fun he => hnp (he ▸ ha)
      simpa only [flipOn_apply, mem_insert, mem_singleton, hao, hap, or_self,
        ite_eq_right, not_false_eq_true] using hw.used_agrees a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha | ha
      · subst a
        cases hx : w.flip f o <;> cases hy : g o <;> simp_all [flipOn_apply]
      · subst a
        cases hx : w.flip f p <;> cases hy : g p <;> simp_all [flipOn_apply]
  refine ⟨hvp, hps, ?_⟩
  intro hpf
  refine ⟨hvp, ?_, ?_, Or.inr (by simpa only [Walk.finish_snoc] using hpf),
    hw.start_defect, hw.target_start, hused, ?_⟩
  · rw [Walk.finish_snoc, ← mem_defects, hvp.1.defects_flip h, Walk.finish_snoc]
    change p.var ∈ defects f ∆ {w.start} ∆ {p.var}
    simp [mem_symmDiff, mem_defects, hps, hpf]
  · rw [Walk.finish_snoc]
    exact fun he => hpf (mem_defects.mp (hsub (mem_defects.mpr he)))
  · intro _ a ha
    rw [hflip]
    have hap : a ≠ p := fun he => hps ((congrArg Occurrence.var he).symm.trans ha)
    by_cases he : w.steps = []
    · have hfin : w.finish = w.start := by simp [Walk.finish, he, Walk.finishFrom]
      have hao : a.var = o.var := ha.trans (hov.trans hfin).symm
      by_cases heo : a = o
      · subst a
        cases hx : w.flip f o <;> cases hy : g o <;> simp_all [flipOn_apply]
      · have hother := other_endpoint_eq h
          (by simpa only [hov] using hw.endpoint_defect)
          (by simpa only [hov] using hw.target_endpoint) ho hao heo
        simpa [flipOn_apply, heo, hap] using hother
    · have hao : a ≠ o := by
        intro hao
        have hstart : o.var = w.start := (congrArg Occurrence.var hao).symm.trans ha
        exact ho (hw.start_cleared he o hstart)
      simpa [flipOn_apply, hao, hap] using hw.start_cleared he a ha

/-- The second phase returns an augmenting prefix-valid incidence trail. Its clock counts
exchanges, and each appended step removes exactly two remaining occurrence disagreements. -/
theorem buildWalk_spec (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hg : ValidLabeling sem g) (hsub : defects g ⊆ defects f)
    (fuel : ℕ) {w : Walk F} (hw : WalkState sem f g w)
    (hclock : hammingDist (w.flip f) g ≤ fuel) :
    ∃ w' k, buildWalk sem f g fuel w = some w' ∧ w'.IsAugmenting sem f ∧
      w'.start = w.start ∧ w'.steps.length = w.steps.length + k ∧
      hammingDist (w'.flip f) g + 2 * k = hammingDist (w.flip f) g ∧ k ≤ fuel := by
  induction fuel generalizing w with
  | zero =>
    have he : w.flip f = g := hammingDist_eq_zero.mp (by omega)
    have hi := hw.endpoint_defect
    rw [he] at hi
    exact (hw.target_endpoint hi).elim
  | succ n ih =>
    cases hs : findPair F (WalkMove sem g (w.flip f) w.finish) with
    | none =>
      obtain ⟨a, ha⟩ := exists_walkMove hM hg hw.prefix_valid.valid_flip
        hw.endpoint_defect hw.target_endpoint
      exact (findPair_none hs a.1 a.2 ha).elim
    | some a =>
      rcases a with ⟨o, p⟩
      have hm := findPair_spec hs
      obtain ⟨hov, hc, hne, ho, hp, hv⟩ := hm
      have hno : o ∉ w.edges := fun he => ho (hw.used_agrees o he)
      have hnp : p ∉ w.edges := fun he => hp (hw.used_agrees p he)
      have hflip := Walk.flip_snoc w f o p hw.prefix_valid.1 hno hnp hne
      have hd := hammingDist_flipOn_pair_add_two hne ho hp
      rw [← hflip] at hd
      obtain ⟨hprefix, hps, hstate⟩ := hw.extend h hsub
        (show WalkMove sem g (w.flip f) w.finish (o, p) from
          ⟨hov, hc, hne, ho, hp, hv⟩)
      by_cases hpf : Inconsistent f p.var
      · refine ⟨w.snoc o p, 1, ?_, ?_, rfl, ?_, ?_, by omega⟩
        · simp only [buildWalk, hs, ite_eq_left hpf]
        · refine ⟨⟨hprefix, ?_⟩, hw.start_defect, ?_⟩
          · change w.start ≠ (w.snoc o p).finish
            rw [Walk.finish_snoc]
            exact hps.symm
          · simpa only [Walk.finish_snoc] using hpf
        · simp [Walk.snoc]
        · omega
      · obtain ⟨w', k, hr, ha, hstart, hlen, hdist, hk⟩ :=
          ih (hstate hpf) (by omega)
        refine ⟨w', k + 1, ?_, ha, hstart, ?_, ?_, by omega⟩
        · simpa only [buildWalk, hs, ite_eq_right hpf] using hr
        · simp only [Walk.snoc, List.length_append, List.length_singleton] at hlen
          omega
        · omega

/-- Start the second phase at a chosen original defect absent from the comparison labeling. -/
theorem buildWalk_from_start (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g) (hsub : defects g ⊆ defects f)
    (r : V) (hrf : Inconsistent f r) (hrg : ¬ Inconsistent g r) :
    ∃ w k, buildWalk sem f g (hammingDist f g) ⟨r, []⟩ = some w ∧
      w.IsAugmenting sem f ∧ w.start = r ∧ w.steps.length = k ∧
      hammingDist (w.flip f) g + 2 * k = hammingDist f g ∧ k ≤ hammingDist f g := by
  have he : (⟨r, []⟩ : Walk F).flip f = f := by
    simp [Walk.flip, Walk.edges, Walk.edgesOf]
  have hw : WalkState sem f g ⟨r, []⟩ := {
    prefix_valid := ⟨⟨trivial, List.nodup_nil⟩, trivial, hf⟩
    endpoint_defect := by simpa only [he, Walk.finish, Walk.finishFrom] using hrf
    target_endpoint := hrg
    internal_endpoint := Or.inl rfl
    start_defect := hrf
    target_start := hrg
    used_agrees := by simp [Walk.edges, Walk.edgesOf]
    start_cleared := by simp }
  have hb := h.buildWalk_spec hM hg hsub (hammingDist f g) hw (by rw [he])
  simpa only [he, List.length_nil, Nat.zero_add] using hb

/-- Full Lemma 31 existence conclusion, obtained by the actual two phases. The specified
variable is excluded only as the start. No solver or augmenting-walk assumption is used. -/
theorem exists_augmentingWalk_start_ne (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} (hM : EvenConstraints sem F)
    {f g : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    (hlt : (defects g).card < (defects f).card) (x : V) :
    ∃ w : Walk F, w.IsAugmenting sem f ∧ w.start ≠ x ∧
      2 * w.steps.length ≤ hammingDist f g := by
  let fixed := repair sem f (hammingDist f g) g
  have hfix := h.repair_spec hM hf hg (hammingDist f g)
  change ValidLabeling sem fixed.1 ∧ (defects fixed.1).card ≤ (defects g).card ∧
    hammingDist f fixed.1 + 2 * fixed.2 = hammingDist f g ∧
    fixed.2 ≤ hammingDist f g ∧
    (hammingDist f g ≤ hammingDist f g → defects fixed.1 ⊆ defects f) at hfix
  have hsub := hfix.2.2.2.2 le_rfl
  obtain ⟨r, hrx, hrf, hrg⟩ := h.exists_start_ne hM hf hfix.1
    (hfix.2.1.trans_lt hlt) x
  obtain ⟨w, k, _, hw, hstart, hlen, hdist, _⟩ :=
    h.buildWalk_from_start hM hf hfix.1 hsub r hrf hrg
  refine ⟨w, hw, hstart ▸ hrx, ?_⟩
  omega

/-- First original defect absent from the comparison labeling, excluding the specified start.
Incidences are scanned in positional order; no arbitrary occurrence is chosen. -/
@[expose] def findStart (F : CSP Rel V) (f g : OccurrenceLabeling F Bool) (x : V) :
    Option (Occurrence F) :=
  (incidenceList F).find? fun o =>
    decide (o.var ≠ x ∧ Inconsistent f o.var ∧ ¬ Inconsistent g o.var)

/-- The full two-phase construction of Lemma 31. The clocks are occurrence Hamming distances;
failed or insufficient inputs return `none`. Correctness under the mathematical hypotheses
is `augmentingWalk_spec`. The routine does not solve for the improving comparison labeling. -/
@[expose] def augmentingWalk (sem : Rel → List Bool → Bool)
    (f g : OccurrenceLabeling F Bool) (x : V) : Option (Walk F) :=
  let fixed := (repair sem f (hammingDist f g) g).1
  match findStart F f fixed x with
  | none => none
  | some o => buildWalk sem f fixed (hammingDist f fixed) ⟨o.var, []⟩

/-- Lemma 31 with a concrete total routine: given an improving valid comparison labeling,
`augmentingWalk` returns an augmenting f-walk starting away from the specified variable.
Both phases together perform at most half the original occurrence disagreements in exchanges.
This bounds local exchanges; no native-machine runtime bound is asserted. -/
theorem augmentingWalk_spec (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    (hlt : (defects g).card < (defects f).card) (x : V) :
    ∃ w : Walk F, augmentingWalk sem f g x = some w ∧ w.IsAugmenting sem f ∧
      w.start ≠ x ∧
      2 * ((repair sem f (hammingDist f g) g).2 + w.steps.length) ≤ hammingDist f g := by
  let fixed := repair sem f (hammingDist f g) g
  have hfix := h.repair_spec hM hf hg (hammingDist f g)
  change ValidLabeling sem fixed.1 ∧ (defects fixed.1).card ≤ (defects g).card ∧
    hammingDist f fixed.1 + 2 * fixed.2 = hammingDist f g ∧
    fixed.2 ≤ hammingDist f g ∧
    (hammingDist f g ≤ hammingDist f g → defects fixed.1 ⊆ defects f) at hfix
  have hsub := hfix.2.2.2.2 le_rfl
  cases hs : findStart F f fixed.1 x with
  | none =>
    obtain ⟨r, hrx, hrf, hrg⟩ := h.exists_start_ne hM hf hfix.1
      (hfix.2.1.trans_lt hlt) x
    obtain ⟨o, p, hor, hpr, hop⟩ := hrf
    have hn := List.find?_eq_none.mp hs o (mem_incidenceList o)
    exact (hn (by simpa only [hor, decide_eq_true_eq] using
      (show r ≠ x ∧ Inconsistent f r ∧ ¬ Inconsistent fixed.1 r from
        ⟨hrx, ⟨o, p, hor, hpr, hop⟩, hrg⟩))).elim
  | some o =>
    have ho : o.var ≠ x ∧ Inconsistent f o.var ∧ ¬ Inconsistent fixed.1 o.var := by
      have ht := List.find?_some (p := fun o : Occurrence F =>
        decide (o.var ≠ x ∧ Inconsistent f o.var ∧ ¬ Inconsistent fixed.1 o.var)) hs
      exact of_decide_eq_true ht
    obtain ⟨w, k, hw, ha, hstart, hlen, hdist, _⟩ :=
      h.buildWalk_from_start hM hf hfix.1 hsub o.var ho.2.1 ho.2.2
    refine ⟨w, ?_, ha, hstart ▸ ho.1, ?_⟩
    · have hs' : findStart F f (repair sem f (hammingDist f g) g).1 x = some o := hs
      simpa only [augmentingWalk, hs'] using hw
    · change 2 * (fixed.2 + w.steps.length) ≤ hammingDist f g
      omega

/-- Nonoptimality is equivalent to existence of an augmenting walk, without assuming a solver. -/
theorem exists_improvement_iff_exists_augmentingWalk (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} (hM : EvenConstraints sem F)
    {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f) :
    (∃ g : OccurrenceLabeling F Bool,
      ValidLabeling sem g ∧ (defects g).card < (defects f).card) ↔
      ∃ w : Walk F, w.IsAugmenting sem f := by
  constructor
  · rintro ⟨g, hg, hlt⟩
    obtain ⟨x, _⟩ := card_pos.mp (show 0 < (defects f).card by omega)
    obtain ⟨w, hw, _, _⟩ := h.exists_augmentingWalk_start_ne hM hf hg hlt x
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    refine ⟨w.flip f, hw.1.1.valid_flip, ?_⟩
    have hd := hw.card_defects_flip_add_two h
    omega

/-- An optimal valid labeling has no augmenting walk, and conversely. -/
theorem isOptimalLabeling_iff_no_augmentingWalk (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} (hM : EvenConstraints sem F)
    {f : OccurrenceLabeling F Bool} :
    IsOptimalLabeling sem f ↔ ValidLabeling sem f ∧ ¬ ∃ w : Walk F, w.IsAugmenting sem f := by
  constructor
  · rintro ⟨hf, hopt⟩
    refine ⟨hf, ?_⟩
    intro hw
    obtain ⟨g, hg, hlt⟩ := (h.exists_improvement_iff_exists_augmentingWalk hM hf).mpr hw
    exact (Nat.not_lt_of_ge (hopt g hg)) hlt
  · rintro ⟨hf, hn⟩
    refine ⟨hf, fun g hg => ?_⟩
    by_contra hlt
    exact hn ((h.exists_improvement_iff_exists_augmentingWalk hM hf).mp
      ⟨g, hg, Nat.lt_of_not_ge hlt⟩)

end EdgeInstance

end Cslib.Logic.PL.CSP
