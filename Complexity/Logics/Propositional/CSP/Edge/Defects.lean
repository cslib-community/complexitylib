/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Occurrence
public import Complexity.Foundations.Data.BitString.DeltaMatroid.Basic
public import Complexity.Foundations.Data.BitString.Hamming
import Complexity.Foundations.Data.BitString.DeltaMatroid.Operations
import Mathlib.Data.Fintype.Sigma
import Complexity.Foundations.Data.Finset.SymmDiff

/-!
# Defects of Boolean occurrence labelings

Defects are distinct occurring variables, rather than incidences. All indices retain constraint
positions, including repeated identical constraints. These definitions specialize Definition 20
of [KazdaKolmogorovRolinek2018], arXiv v6, printed p. 8. Nullary constraints remain subject to
`ValidLabeling`; variables absent from the CSP never contribute defects.

## Main definitions

* `Inconsistent`, `defects`: distinct defective variables of an occurrence labeling.
* `IsOptimalLabeling`: minimum defect count among valid labelings.
* `EdgeInstance.EvenConstraints`: an even delta-matroid on each constraint's argument positions.

## Main results

* `satisfiable_iff_exists_zero_defects`: exact agreement with the existing CSP semantics.
* `EdgeInstance.exists_valid_exchange`: a local exchange lifted to the occurrence labeling.
* `EdgeInstance.card_defects_mod_two_eq`: Observation 30, allowing odd local parity.
-/

public section

namespace Cslib.Logic.PL.CSP

open Finset BitString
open scoped symmDiff

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

/-- A variable has two occurrences carrying unequal Boolean labels. -/
@[expose] def Inconsistent (f : OccurrenceLabeling F Bool) (v : V) : Prop :=
  ∃ o p : Occurrence F, o.var = v ∧ p.var = v ∧ f o ≠ f p

instance (f : OccurrenceLabeling F Bool) (v : V) : Decidable (Inconsistent f v) :=
  inferInstanceAs (Decidable (∃ o p : Occurrence F,
    o.var = v ∧ p.var = v ∧ f o ≠ f p))

/-- The finite set of inconsistent variables, with each variable counted once. -/
@[expose] def defects (f : OccurrenceLabeling F Bool) : Finset V :=
  (univ.image (Occurrence.var (F := F))).filter (Inconsistent f)

/-- Defect membership has no additional occurrence hypothesis. -/
@[simp] theorem mem_defects {f : OccurrenceLabeling F Bool} {v : V} :
    v ∈ defects f ↔ Inconsistent f v := by
  simp only [defects, mem_filter, mem_image, mem_univ, true_and]
  exact and_iff_right_of_imp fun ⟨o, _, ho, _, _⟩ => ⟨o, ho⟩

/-- Zero defects is exactly consistency, for arbitrary CSP instances. -/
theorem defects_eq_empty_iff (f : OccurrenceLabeling F Bool) :
    defects f = ∅ ↔ ConsistentLabeling f := by
  simp only [eq_empty_iff_forall_notMem, mem_defects, Inconsistent, ConsistentLabeling]
  constructor
  · intro h o p hp
    by_contra hn
    exact h o.var ⟨o, p, rfl, hp.symm, hn⟩
  · intro h v ⟨o, p, ho, hp, hn⟩
    exact hn (h o p (ho.trans hp.symm))

/-- Valid occurrence labels with no defects are exactly models of the original CSP. -/
theorem satisfiable_iff_exists_zero_defects (sem : Rel → List Bool → Bool) :
    F.Satisfiable sem ↔ ∃ f : OccurrenceLabeling F Bool,
      ValidLabeling sem f ∧ (defects f).card = 0 := by
  simp only [card_eq_zero, defects_eq_empty_iff]
  exact satisfiable_iff_exists_labeling sem false

/-- A valid labeling is optimal when no valid labeling has fewer inconsistent variables.
This is Definition 20 of [KazdaKolmogorovRolinek2018], arXiv v6, printed p. 8. -/
@[expose] def IsOptimalLabeling (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) : Prop :=
  ValidLabeling sem f ∧ ∀ g : OccurrenceLabeling F Bool,
    ValidLabeling sem g → (defects f).card ≤ (defects g).card

namespace EdgeInstance


omit [DecidableEq V] in
/-- At an edge occurrence, inconsistency compares exactly its two endpoint labels. -/
theorem inconsistent_iff (h : EdgeInstance F) (f : OccurrenceLabeling F Bool) (o : Occurrence F) :
    Inconsistent f o.var ↔ f o ≠ f (h.partner o) := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩ hf
    rcases h.eq_or_eq_partner ha with rfl | rfl <;>
      rcases h.eq_or_eq_partner hb with rfl | rfl <;> exact hab (by simp_all)
  · intro hf
    exact ⟨o, h.partner o, rfl, (h.partner_variable o).symm, hf⟩

omit [DecidableEq V] in
/-- Distinct argument positions of one constraint name distinct variables. -/
theorem var_ne_of_constraint_eq (h : EdgeInstance F) {o p : Occurrence F}
    (hc : o.1 = p.1) (hne : o ≠ p) :
    o.var ≠ p.var := fun hv => hne (h.eq_of_constraint_eq hv hc)

omit [DecidableEq V] in
/-- A flip toggles a defect precisely when it flips exactly one endpoint. -/
theorem inconsistent_flipOn_iff (h : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (s : Finset (Occurrence F))
    (o : Occurrence F) :
    Inconsistent (flipOn s f) o.var ↔
      if (o ∈ s ↔ h.partner o ∈ s) then Inconsistent f o.var
      else ¬ Inconsistent f o.var := by
  simp only [h.inconsistent_iff, flipOn_apply]
  by_cases ho : o ∈ s <;> by_cases hp : h.partner o ∈ s <;>
    cases hf : f o <;> cases hg : f (h.partner o) <;> simp_all

/-- Flipping one occurrence toggles just its variable's defect status. -/
theorem defects_flipOn_singleton (h : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (o : Occurrence F) :
    defects (flipOn {o} f) = defects f ∆ {o.var} := by
  ext v
  by_cases hv : v = o.var
  · subst v
    rw [mem_defects, h.inconsistent_flipOn_iff]
    have hp : h.partner o ≠ o := (h.partner_ne o).symm
    simp [hp, mem_defects, mem_symmDiff]
  · by_cases hi : ∃ p : Occurrence F, p.var = v
    · obtain ⟨p, rfl⟩ := hi
      have hpo : p ≠ o := fun he => hv (congrArg Occurrence.var he)
      have hqo : h.partner p ≠ o := fun he =>
        hv ((h.partner_variable p).trans (congrArg Occurrence.var he))
      rw [mem_defects, h.inconsistent_flipOn_iff]
      simp [hpo, hqo, hv, mem_defects, mem_symmDiff]
    · have hn (l : OccurrenceLabeling F Bool) : ¬ Inconsistent l v :=
        fun ⟨p, _, hp, _, _⟩ => hi ⟨p, hp⟩
      simp [mem_defects, hn, hv, mem_symmDiff]

/-- A same-constraint two-coordinate flip toggles two different variable defects. -/
theorem defects_flipOn_pair (h : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    {o p : Occurrence F}
    (hc : o.1 = p.1) (hne : o ≠ p) :
    defects (flipOn {o, p} f) = defects f ∆ {o.var, p.var} := by
  rw [flipOn_insert (by simpa using hne), h.defects_flipOn_singleton,
    h.defects_flipOn_singleton, symmDiff_assoc]
  congr 1
  ext v
  simp only [mem_symmDiff, mem_singleton, mem_insert]
  have hv := h.var_ne_of_constraint_eq hc hne
  aesop

private theorem card_toggle_mod_two (s : Finset V) (v : V) :
    (s ∆ {v}).card % 2 = (s.card + 1) % 2 := by
  by_cases hv : v ∈ s
  · have he := card_erase_add_one hv
    rw [symmDiff_singleton_eq, ite_eq_left hv]
    omega
  · rw [symmDiff_singleton_eq, ite_eq_right hv, card_insert_of_notMem hv]

/-- Two-coordinate exchanges preserve the number of defects modulo two. -/
theorem card_defects_flipOn_pair_mod_two (h : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    {o p : Occurrence F} (hne : o ≠ p) :
    (defects (flipOn {o, p} f)).card % 2 = (defects f).card % 2 := by
  rw [flipOn_insert (by simpa using hne), h.defects_flipOn_singleton,
    h.defects_flipOn_singleton]
  have ha := card_toggle_mod_two (defects f) p.var
  have hb := card_toggle_mod_two (defects f ∆ {p.var}) o.var
  omega

/-- Repairing a defect by a two-coordinate move cannot increase the defect count. -/
theorem card_defects_flipOn_pair_le (h : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    {o p : Occurrence F} (hne : o ≠ p)
    (ho : Inconsistent f o.var) :
    (defects (flipOn {o, p} f)).card ≤ (defects f).card := by
  have he := card_erase_add_one (mem_defects.mpr ho)
  have hb := card_symmDiff_singleton_le ((defects f).erase o.var) p.var
  have heq : (defects f ∆ {p.var}) ∆ {o.var} =
      (defects f ∆ {o.var}) ∆ {p.var} := by
    ext v
    simp only [mem_symmDiff, mem_singleton]
    tauto
  rw [flipOn_insert (by simpa using hne), h.defects_flipOn_singleton,
    h.defects_flipOn_singleton, heq, symmDiff_singleton_eq (defects f) o.var,
    ite_eq_left (mem_defects.mpr ho)]
  omega

/-- Each constraint relation, on its actual ordered argument positions, is an even delta-matroid.
Common parity may be odd and may differ between constraints. -/
@[expose] def EvenConstraints (sem : Rel → List Bool → Bool) (F : CSP Rel V) : Prop :=
  ∀ i : Fin F.length,
    IsEvenDeltaMatroid {t : Fin F[i].2.length → Bool | sem F[i].1 (List.ofFn t) = true}

omit [DecidableEq V] in
/-- A two-coordinate move in one constraint preserves validity exactly when its new tuple does. -/
theorem validLabeling_flipOn_pair {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (i : Fin F.length) (a b : Fin F[i].2.length)
    (hab : sem F[i].1 (List.ofFn (flipOn {a, b} (fun j => f ⟨i, j⟩))) = true) :
    ValidLabeling sem (flipOn {⟨i, a⟩, ⟨i, b⟩} f) := by
  intro k
  by_cases hk : k = i
  · subst k
    have he : localTuple (flipOn {⟨i, a⟩, ⟨i, b⟩} f) i =
        List.ofFn (flipOn {a, b} (fun j => f ⟨i, j⟩)) := by
      apply congrArg List.ofFn
      funext j
      simp [flipOn_apply]
    rw [he]
    exact hab
  · have he : localTuple (flipOn {⟨i, a⟩, ⟨i, b⟩} f) k = localTuple f k := by
      apply congrArg List.ofFn
      funext j
      have ha : (⟨k, j⟩ : Occurrence F) ≠ ⟨i, a⟩ :=
        fun he => hk (congrArg Sigma.fst he)
      have hb : (⟨k, j⟩ : Occurrence F) ≠ ⟨i, b⟩ :=
        fun he => hk (congrArg Sigma.fst he)
      simp [flipOn_apply, ha, hb]
    rw [he]
    exact hf k

omit [DecidableEq V] in
/-- Symmetric exchange at the actual constraint position gives a valid global two-bit move. -/
theorem exists_valid_exchange {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    (o : Occurrence F) (ho : f o ≠ g o) :
    ∃ p : Occurrence F, o.1 = p.1 ∧ o ≠ p ∧ f p ≠ g p ∧
      ValidLabeling sem (flipOn {o, p} f) := by
  obtain ⟨j, hj, hd, hv⟩ := (hM o.1).exchange (hf o.1) (hg o.1) ho
  refine ⟨⟨o.1, j⟩, rfl, ?_, hd, ?_⟩
  · intro he
    exact hj (by cases o; cases he; rfl)
  · exact validLabeling_flipOn_pair hf o.1 o.2 j hv

/-- Observation 30 of [KazdaKolmogorovRolinek2018], printed p. 14: valid labelings have
congruent defect counts modulo two. Local common parities need not be zero. -/
theorem card_defects_mod_two_eq (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EvenConstraints sem F) {f g : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g) :
    (defects f).card % 2 = (defects g).card % 2 := by
  generalize hn : hammingDist f g = n
  induction n using Nat.strong_induction_on generalizing f with
  | ind n ih =>
    by_cases he : f = g
    · subst g
      rfl
    · obtain ⟨o, ho⟩ := Function.ne_iff.mp he
      obtain ⟨p, hc, hne, hp, hv⟩ := exists_valid_exchange hM hf hg o ho
      have hd := hammingDist_flipOn_pair_add_two hne ho hp
      have ht : hammingDist (flipOn {o, p} f) g < n := by omega
      exact (h.card_defects_flipOn_pair_mod_two f hne).symm.trans
        (ih _ ht hv rfl)

end EdgeInstance

end Cslib.Logic.PL.CSP
