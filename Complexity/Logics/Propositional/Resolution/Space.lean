/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Proof
public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Clause space of resolution refutations

A resolution refutation in the *configuration-style* presentation of Esteban and Torán keeps a set
of clauses in memory and changes it one step at a time [Esteban and Torán][EstebanToran2001]
[Filmus, Lauria, Mikša, Nordström and Vinyals, Section 2][FilmusLauriaMiksaNordstromVinyals2014]:

* *axiom download*: a clause of the formula is added;
* *inference*: the resolvent of two clauses in memory, on a variable occurring positively in the
  first and negatively in the second, is added;
* *erasure*: a clause is removed.

These are the moves (`Cslib.Logic.PL.ConfigMove`) of a labelled transition system on sets of
clauses (`Cslib.Logic.PL.CNF.configLTS`). A refutation starts from the empty configuration and ends
with one containing the empty clause. Its *clause space* is the largest number of clauses it holds
at once, and `φ` is refutable in clause space `s` (`Cslib.Logic.PL.CNF.RefutableInSpace`) if it has
a refutation in which every configuration has at most `s` clauses. The derivation steps are those of
`Cslib.Logic.PL.CNF.IsProof`; in particular there is no weakening rule. Configurations are sets of
clauses, so the space of a configuration counts distinct clauses. Clauses are lists, so two
orderings of the same literals count as two clauses; this does not change the least space of a
refutation compared with the convention of clauses as sets, since mapping each clause to its set of
literals never increases space, and a refutation on sets lifts by fixing one list for each set.

Clause space is the resolution analogue of the number of pebbles in the black pebble game
(`Cslib.Pebbling.blackPebbleGame`): a download places a pebble on a source of the graph of a proof,
an inference places one on a vertex whose two predecessors carry pebbles, and an erasure removes a
pebble. Both are labelled transition systems on finite sets with a cardinality budget.

Every configuration reachable from the empty one consists of derivable clauses, so refutations in
bounded space are sound (`Cslib.Logic.PL.CNF.RefutableInSpace.not_satisfiable`). Conversely a
refutation with `s` lines can be replayed, downloading or deriving its lines in order and never
erasing anything, in space `s` (`Cslib.Logic.PL.CNF.RefutableInSize.refutableInSpace`); so the
unsatisfiable formulas are exactly those refutable in some clause space
(`Cslib.Logic.PL.CNF.exists_refutableInSpace_iff_not_satisfiable`). Unless the formula contains the
empty clause, a refutation needs space at least `3`: the empty clause is derived from two clauses
held at the same time (`Cslib.Logic.PL.CNF.RefutableInSpace.three_le`).

The Atserias–Dalmau inequality, bounding width by clause space, is in
`Complexity.Logics.Propositional.Resolution.SpaceWidth`.

## Main definitions

* `Cslib.Logic.PL.ConfigMove`, `Cslib.Logic.PL.CNF.ConfigStep`: the moves of configuration-style
  resolution refutations, and their effect on a configuration.
* `Cslib.Logic.PL.CNF.configLTS`: configuration-style resolution with configurations of at most `s`
  clauses, as a cslib `LTS`.
* `Cslib.Logic.PL.CNF.RefutableInSpace`: refutability in clause space `s`.

## Main results

* `Cslib.Logic.PL.CNF.RefutableInSpace.not_satisfiable`: soundness.
* `Cslib.Logic.PL.CNF.RefutableInSize.refutableInSpace`: clause space is at most size.
* `Cslib.Logic.PL.CNF.exists_refutableInSpace_iff_not_satisfiable`: completeness.
* `Cslib.Logic.PL.CNF.RefutableInSpace.three_le`: refutations of formulas without the empty clause
  need space at least `3`.

## References

* [J. L. Esteban, J. Torán, *Space bounds for resolution*][EstebanToran2001]
* [Y. Filmus, M. Lauria, M. Mikša, J. Nordström, M. Vinyals, *From small space to small width in
  resolution*][FilmusLauriaMiksaNordstromVinyals2014]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-- A move of a configuration-style resolution refutation: download a clause, infer the resolvent of
two clauses on a variable, or erase a clause. -/
inductive ConfigMove (V : Type*) where
  /-- Axiom download. -/
  | download (c : Clause V)
  /-- Inference of `c₁.resolvent c₂ v`. -/
  | infer (c₁ c₂ : Clause V) (v : V)
  /-- Erasure. -/
  | erase (c : Clause V)

namespace CNF

/-- The effect of a move on a configuration of a **configuration-style resolution refutation** from
`φ` [Esteban and Torán][EstebanToran2001]: download a clause of `φ`, add the resolvent of two
clauses of the configuration on a variable occurring positively in the first and negatively in the
second, or erase a clause. -/
inductive ConfigStep (φ : CNF V) : Finset (Clause V) → ConfigMove V → Finset (Clause V) → Prop
  /-- Axiom download: add a clause of `φ`. -/
  | download {M : Finset (Clause V)} {c : Clause V} (hc : c ∈ φ) :
      ConfigStep φ M (.download c) (insert c M)
  /-- Inference: add the resolvent of two clauses of the configuration. -/
  | infer {M : Finset (Clause V)} {c₁ c₂ : Clause V} (v : V) (h₁ : c₁ ∈ M) (h₂ : c₂ ∈ M)
      (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) :
      ConfigStep φ M (.infer c₁ c₂ v) (insert (c₁.resolvent c₂ v) M)
  /-- Erasure: remove a clause. -/
  | erase {M : Finset (Clause V)} (c : Clause V) : ConfigStep φ M (.erase c) (M.erase c)

/-- Configuration-style resolution from `φ` with configurations of at most `s` clauses, as a
labelled transition system. -/
def configLTS (φ : CNF V) (s : ℕ) : LTS (Finset (Clause V)) (ConfigMove V) where
  Tr M m M' := φ.ConfigStep M m M' ∧ M'.card ≤ s

/-- `φ` is **refutable in clause space `s`** [Esteban and Torán][EstebanToran2001]: some sequence of
moves leads from the empty configuration to one containing the empty clause, through configurations
of at most `s` clauses each. -/
def RefutableInSpace (φ : CNF V) (s : ℕ) : Prop :=
  ∃ (ms : List (ConfigMove V)) (M : Finset (Clause V)), (φ.configLTS s).MTr ∅ ms M ∧ [] ∈ M

variable {φ : CNF V} {s t : ℕ}

/-- A transition of `configLTS φ s` is a step whose result has at most `s` clauses. -/
theorem configLTS_tr {M M' : Finset (Clause V)} {m : ConfigMove V} :
    (φ.configLTS s).Tr M m M' ↔ φ.ConfigStep M m M' ∧ M'.card ≤ s := Iff.rfl

/-- A run within space `s` is a run within any larger space. -/
theorem configLTS_mTr_mono (hst : s ≤ t) {M M' : Finset (Clause V)} {ms : List (ConfigMove V)}
    (h : (φ.configLTS s).MTr M ms M') : (φ.configLTS t).MTr M ms M' := by
  induction h with
  | refl => exact .refl
  | stepL h _ ih => exact .stepL ⟨h.1, h.2.trans hst⟩ ih

/-- A configuration reachable from one of derivable clauses consists of derivable clauses. -/
theorem derives_of_configLTS_mTr {M M' : Finset (Clause V)} {ms : List (ConfigMove V)}
    (h : (φ.configLTS s).MTr M ms M') (hM : ∀ c ∈ M, φ.Derives c) : ∀ c ∈ M', φ.Derives c := by
  induction h with
  | refl => exact hM
  | stepL hstep _ ih =>
    refine ih fun c hc => ?_
    cases hstep.1 with
    | download hc' =>
      rcases Finset.mem_insert.1 hc with rfl | hc
      exacts [.mem hc', hM c hc]
    | infer v h₁ h₂ hv₁ hv₂ =>
      rcases Finset.mem_insert.1 hc with rfl | hc
      exacts [.resolvent v (hM _ h₁) (hM _ h₂) hv₁ hv₂, hM c hc]
    | erase _ => exact hM c (Finset.mem_of_mem_erase hc)

/-- A run that introduces the empty clause into a configuration without it holds `3` clauses at
some point. -/
private theorem three_le_of_configLTS_mTr (hφ : [] ∉ φ) {M M' : Finset (Clause V)}
    {ms : List (ConfigMove V)} (h : (φ.configLTS s).MTr M ms M') (hM : [] ∉ M) (hM' : [] ∈ M') :
    3 ≤ s := by
  induction h with
  | refl => exact absurd hM' hM
  | @stepL M m M₁ ms M₂ hstep _ ih =>
    obtain ⟨hstep, hcard⟩ := hstep
    by_cases h₁ : [] ∈ M₁
    · cases hstep with
      | download hc =>
        rcases Finset.mem_insert.1 h₁ with h | h
        exacts [absurd (h ▸ hc) hφ, absurd h hM]
      | @infer c₁ c₂ v h₁' h₂ hv₁ hv₂ =>
        rcases Finset.mem_insert.1 h₁ with h | h
        · -- the parents are different nonempty clauses, and the empty clause is a third one
          refine le_trans ?_ hcard
          have hne : c₁ ≠ c₂ := by
            rintro rfl
            have : (v, false) ∈ c₁.resolvent c₁ v := Clause.mem_resolvent.2 (Or.inl ⟨hv₂, by simp⟩)
            rw [← h] at this
            simp at this
          refine Finset.two_lt_card.2 ⟨c₁, Finset.mem_insert_of_mem h₁', c₂,
            Finset.mem_insert_of_mem h₂, [], Finset.mem_insert.2 (Or.inl h), hne, ?_, ?_⟩
          · rintro rfl
            simp at hv₁
          · rintro rfl
            simp at hv₂
        · exact absurd h hM
      | erase c => exact absurd (Finset.mem_of_mem_erase h₁) hM
    · exact ih h₁ hM'

namespace RefutableInSpace

/-- **Soundness**: a formula refutable in some clause space is unsatisfiable. -/
theorem not_satisfiable (h : φ.RefutableInSpace s) : ¬ φ.Satisfiable := by
  obtain ⟨ms, M, hM, hnil⟩ := h
  exact (derives_of_configLTS_mTr hM (by simp) [] hnil).not_satisfiable

/-- `RefutableInSpace` is monotone in the space bound. -/
theorem mono (h : φ.RefutableInSpace s) (hst : s ≤ t) : φ.RefutableInSpace t :=
  let ⟨ms, M, hM, hnil⟩ := h
  ⟨ms, M, configLTS_mTr_mono hst hM, hnil⟩

/-- Refutations of a formula without the empty clause need **space at least `3`**: the empty clause
is the resolvent of two different clauses, `[x]` and `[¬x]`, held together with it. -/
theorem three_le (hφ : [] ∉ φ) (h : φ.RefutableInSpace s) : 3 ≤ s :=
  let ⟨_, _, hM, hnil⟩ := h
  three_le_of_configLTS_mTr hφ hM (by simp) hnil

end RefutableInSpace

/-- Replaying the lines of a proof, from its first to its last, reaches the configuration of its
lines through configurations of at most as many clauses as it has lines. -/
private theorem exists_configLTS_mTr_toFinset {ls : List (Clause V)} (h : φ.IsProof ls) :
    ∃ ms, (φ.configLTS ls.length).MTr ∅ ms ls.toFinset := by
  induction h with
  | nil => exact ⟨[], .refl⟩
  | @mem _ c _ hc ih =>
    obtain ⟨ms, hms⟩ := ih
    refine ⟨ms ++ [.download c], (configLTS_mTr_mono (Nat.le_succ _) hms).stepR _ ⟨?_, ?_⟩⟩
    · rw [List.toFinset_cons]
      exact .download hc
    · exact List.toFinset_card_le _
  | @resolvent _ c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨ms, hms⟩ := ih
    refine ⟨ms ++ [.infer c₁ c₂ v], (configLTS_mTr_mono (Nat.le_succ _) hms).stepR _ ⟨?_, ?_⟩⟩
    · rw [List.toFinset_cons]
      exact .infer v (List.mem_toFinset.2 h₁) (List.mem_toFinset.2 h₂) hv₁ hv₂
    · exact List.toFinset_card_le _

/-- **Clause space is at most size**: a refutation with `s` lines gives a refutation in clause space
`s`, which downloads or derives the lines in order and never erases. -/
theorem RefutableInSize.refutableInSpace (h : φ.RefutableInSize s) : φ.RefutableInSpace s :=
  let ⟨_, hp, hnil, hlen⟩ := h
  let ⟨ms, hms⟩ := exists_configLTS_mTr_toFinset hp
  ⟨ms, _, configLTS_mTr_mono hlen hms, List.mem_toFinset.2 hnil⟩

/-- **Resolution refutes exactly the unsatisfiable formulas**, in some clause space. -/
theorem exists_refutableInSpace_iff_not_satisfiable :
    (∃ s, φ.RefutableInSpace s) ↔ ¬ φ.Satisfiable := by
  refine ⟨fun ⟨_, h⟩ => h.not_satisfiable, fun h => ?_⟩
  obtain ⟨s, hs⟩ := exists_refutableInSize_iff_not_satisfiable.2 h
  exact ⟨s, hs.refutableInSpace⟩

end CNF

end Cslib.Logic.PL
