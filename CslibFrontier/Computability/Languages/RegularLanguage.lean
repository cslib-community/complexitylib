/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Languages/RegularLanguage.lean`)

public import CslibFrontier.Computability.Automata.NA.Map
public import Cslib.Computability.Languages.RegularLanguage

/-!
# Further closure properties of regular languages

Regular languages are closed under images along letter maps (`Language.map`), the projection
step of the translation of monadic second-order logic into automata
[Thomas, Section 3][Thomas1997]. The alphabet may be infinite. Three families of languages defined
by the positions of letters are regular for every pair of letter predicates `p`, `q`: the words
all of whose letters satisfy `p`, the words with some letter satisfying `p`, and the words with a
letter satisfying `p` strictly before a letter satisfying `q`. They are the atomic languages of
the same translation; the first two are also stated over positions `w[i]`.

Languages given by conditions on words, `{w | P w}`, are closed under the connectives through
the existing CSLib closures, with no set-builder restatement: `hP.inf hQ` proves regularity of
`{w | P w ∧ Q w}`, and likewise `IsRegular.add` for `∨`, `IsRegular.compl` for `¬`, and
`IsRegular.top`/`IsRegular.zero` for `True`/`False`. Finite conjunctions over an index type are
`IsRegular.setOf_forall`.

## Main results

* `Cslib.Language.IsRegular.map`: the image of a regular language along a letter map is regular.
* `Cslib.Language.IsRegular.setOf_forall_mem`, `Cslib.Language.IsRegular.setOf_exists_mem`,
  `Cslib.Language.IsRegular.setOf_exists_lt`, `Cslib.Language.IsRegular.setOf_forall_getElem`,
  `Cslib.Language.IsRegular.setOf_exists_getElem`: regularity of the positional languages.
* `Cslib.Language.IsRegular.setOf_forall`: regularity of a finite conjunction of regular
  conditions.

## References

* [W. Thomas, *Languages, automata, and logic*][Thomas1997]
-/

public section

namespace Cslib.Language

open Automata Acceptor

variable {Symbol Symbol' : Type*}

/-- The image of a regular language along a letter map is regular. -/
theorem IsRegular.map (f : Symbol → Symbol') {l : Language Symbol} (h : l.IsRegular) :
    (Language.map f l).IsRegular := by
  rw [IsRegular.iff_nfa] at h ⊢
  obtain ⟨State, h_fin, nfa, rfl⟩ := h
  exact ⟨State, h_fin, nfa.map f, nfa.map_language_eq f⟩

/-- The words all of whose letters satisfy `p` form a regular language. -/
theorem IsRegular.setOf_forall_mem (p : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∀ a ∈ w, p a} := by
  classical
  let M : DFA Symbol Bool := ⟨fun s a => s && decide (p a), true, {true}⟩
  have key : ∀ (w : List Symbol) (s : Bool),
      M.evalFrom s w = (s && decide (∀ a ∈ w, p a)) := by
    intro w
    induction w with
    | nil => intro s; simp [DFA.evalFrom_nil]
    | cons a w ih =>
      intro s
      rw [DFA.evalFrom_cons, ih]
      simp only [M, List.mem_cons, forall_eq_or_imp, Bool.and_assoc, Bool.decide_and]
  refine ⟨Bool, inferInstance, M, ?_⟩
  ext w
  rw [DFA.mem_accepts, DFA.eval, key]
  simp only [M, Bool.true_and, Set.mem_singleton_iff, decide_eq_true_eq]
  rfl

/-- The words with some letter satisfying `p` form a regular language. -/
theorem IsRegular.setOf_exists_mem (p : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∃ a ∈ w, p a} := by
  have e : ({w : List Symbol | ∃ a ∈ w, p a} : Language Symbol) =
      ({w : List Symbol | ∀ a ∈ w, ¬ p a} : Language Symbol)ᶜ := by
    ext w; simp
  rw [e]
  exact (IsRegular.setOf_forall_mem _).compl

private theorem exists_lt_iff_mem_mul (p q : Symbol → Prop) (w : List Symbol) :
    (∃ i j : Fin w.length, i < j ∧ p w[i] ∧ q w[j]) ↔
      ∃ a ∈ ({w : List Symbol | ∃ a ∈ w, p a} : Language Symbol),
        ∃ b ∈ ({w : List Symbol | ∃ a ∈ w, q a} : Language Symbol), a ++ b = w := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨w.take j, ⟨w[i], ?_, hi⟩, w.drop j, ⟨w[j], ?_, hj⟩, List.take_append_drop _ _⟩
    · rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take]; omega, by simp⟩
    · rw [List.mem_iff_getElem]
      exact ⟨0, by rw [List.length_drop]; omega, by simp⟩
  · rintro ⟨a, ⟨x, hxa, hx⟩, b, ⟨y, hyb, hy⟩, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hxa
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hyb
    refine ⟨⟨i, by simp; omega⟩, ⟨a.length + j, by simp; omega⟩, ?_, ?_, ?_⟩
    · rw [Fin.mk_lt_mk]; omega
    · simpa [List.getElem_append_left hi] using hx
    · simpa [List.getElem_append_right] using hy

/-- The words with a letter satisfying `p` strictly before a letter satisfying `q` form a regular
language. -/
theorem IsRegular.setOf_exists_lt (p q : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∃ i j : Fin w.length, i < j ∧ p w[i] ∧ q w[j]} := by
  have h := IsRegular.mul (IsRegular.setOf_exists_mem p) (IsRegular.setOf_exists_mem q)
  refine (congrArg Language.IsRegular (Set.ext fun w => ?_)).mp h
  exact Language.mem_mul.trans (exists_lt_iff_mem_mul p q w).symm

/-- The words all of whose positions carry a letter satisfying `p` form a regular language. -/
theorem IsRegular.setOf_forall_getElem (p : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∀ i : Fin w.length, p w[i]} :=
  (congrArg Language.IsRegular (Set.ext fun _ => List.forall_mem_iff_get)).mp
    (IsRegular.setOf_forall_mem p)

/-- The words with some position carrying a letter satisfying `p` form a regular language. -/
theorem IsRegular.setOf_exists_getElem (p : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∃ i : Fin w.length, p w[i]} :=
  (congrArg Language.IsRegular (Set.ext fun _ => List.exists_mem_iff_get)).mp
    (IsRegular.setOf_exists_mem p)

/-- A finite conjunction of regular conditions on words is regular. -/
theorem IsRegular.setOf_forall {ι : Type*} [Finite ι] {P : ι → List Symbol → Prop}
    (h : ∀ i, Language.IsRegular {w | P i w}) : Language.IsRegular {w | ∀ i, P i w} := by
  refine (congrArg Language.IsRegular (Set.ext fun w => ?_)).mp
    (IsRegular.iInf (s := Set.univ) fun i _ => h i)
  exact Set.mem_iInter₂.trans (by simp)

end Cslib.Language
