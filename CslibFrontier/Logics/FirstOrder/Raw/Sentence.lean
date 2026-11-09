/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.Primrec

/-!
# Free variables, sentences and existential closure of raw formulas

The free variables of a raw formula (`Cslib.Logic.FO.RawFormula.freeVars`), sentences (formulas
without free variables, `Cslib.Logic.FO.RawFormula.IsSentence`), and sentences over a vocabulary
`σ` of pairs (relation symbol, arity) (`Cslib.Logic.FO.RawFormula.IsSentenceOver`). The block
`exRange B L φ = ∃ x_B ⋯ ∃ x_{B+L-1}, φ` existentially quantifies a range of variables; quantifying
all variables below `varBound φ` gives the existential closure `exClosure φ`, a sentence with the
same atoms that is finitely satisfiable iff `φ` is. All of these are primitive recursive.

## Main definitions

* `Cslib.Logic.FO.RawFormula.freeVars`, `Cslib.Logic.FO.RawFormula.IsSentence`,
  `Cslib.Logic.FO.RawFormula.IsSentenceOver`: free variables and sentences.
* `Cslib.Logic.FO.RawFormula.exRange`, `Cslib.Logic.FO.RawFormula.exClosure`: existential
  quantification of a range of variables, and existential closure.

## Main results

* `Cslib.Logic.FO.RawFormula.realize_exRange`: semantics of `exRange`.
* `Cslib.Logic.FO.RawFormula.isSentence_exClosure`,
  `Cslib.Logic.FO.RawFormula.finSat_exClosure`: the existential closure is a finitely satisfiable
  sentence iff the formula is finitely satisfiable.
-/

-- Exposed so that clients can unfold the derived formulas and decide sentencehood of concrete
-- formulas (`IsSentence` is decided by computing `freeVars`).
@[expose] public section

namespace Cslib.Logic.FO

namespace RawFormula

/-! ### Free variables and sentences -/

/-- The free variables of a formula, with repetitions. -/
def freeVars : RawFormula → List ℕ
  | falsum => []
  | equal x y => [x, y]
  | rel _ args => args
  | imp φ ψ => freeVars φ ++ freeVars ψ
  | all x φ => (freeVars φ).filter (· ≠ x)

/-- A **sentence** is a formula without free variables. -/
def IsSentence (φ : RawFormula) : Prop := φ.freeVars = []

instance : DecidablePred IsSentence := fun φ => inferInstanceAs (Decidable (φ.freeVars = []))

/-- `φ` is a sentence over the vocabulary `σ`: a set of pairs (relation symbol, arity) containing
every atom of `φ`. -/
def IsSentenceOver (σ : Set (ℕ × ℕ)) (φ : RawFormula) : Prop :=
  IsSentence φ ∧ ∀ a ∈ φ.atoms, a ∈ σ

theorem mem_freeVars_all {x y : ℕ} {φ : RawFormula} :
    y ∈ (all x φ).freeVars ↔ y ∈ φ.freeVars ∧ y ≠ x := by
  simp [freeVars]

theorem lt_varBound_of_mem_freeVars :
    ∀ {φ : RawFormula} {y : ℕ}, y ∈ φ.freeVars → y < φ.varBound
  | equal x z, y, h => by
    simp only [freeVars, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [varBound]
    omega
  | rel _ args, y, h => lt_varBound_of_mem h
  | imp φ ψ, y, h => by
    simp only [freeVars, List.mem_append] at h
    simp only [varBound]
    rcases h with h | h
    · exact lt_max_of_lt_left (lt_varBound_of_mem_freeVars h)
    · exact lt_max_of_lt_right (lt_varBound_of_mem_freeVars h)
  | all x φ, y, h => by
    simp only [varBound]
    exact lt_max_of_lt_right (lt_varBound_of_mem_freeVars (mem_freeVars_all.1 h).1)

@[simp] theorem freeVars_neg (φ : RawFormula) : (neg φ).freeVars = φ.freeVars := by
  simp [neg, freeVars]

@[simp] theorem atoms_neg (φ : RawFormula) : (neg φ).atoms = φ.atoms := by
  simp [neg, atoms]

theorem isSentence_neg {φ : RawFormula} : IsSentence (neg φ) ↔ IsSentence φ := by
  rw [IsSentence, IsSentence, freeVars_neg]

theorem isSentenceOver_neg {σ : Set (ℕ × ℕ)} {φ : RawFormula} :
    IsSentenceOver σ (neg φ) ↔ IsSentenceOver σ φ := by
  rw [IsSentenceOver, IsSentenceOver, isSentence_neg, atoms_neg]

theorem freeVars_rename (σ : List ℕ) : ∀ φ : RawFormula, (rename σ φ).freeVars = φ.freeVars
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ => by simp only [rename, freeVars, freeVars_rename σ φ, freeVars_rename σ ψ]
  | all _ φ => by simp only [rename, freeVars, freeVars_rename σ φ]

theorem atoms_rename (σ : List ℕ) :
    ∀ φ : RawFormula, (rename σ φ).atoms = φ.atoms.map fun a => (σ.getD a.1 a.1, a.2)
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ => by simp [rename, atoms, atoms_rename σ φ, atoms_rename σ ψ]
  | all _ φ => by simp [rename, atoms, atoms_rename σ φ]

theorem atoms_bigConj {l : List RawFormula} {a : ℕ × ℕ} (h : a ∈ (bigConj l).atoms) :
    ∃ φ ∈ l, a ∈ φ.atoms := by
  induction l with
  | nil => simp [bigConj, verum, neg, atoms] at h
  | cons ψ l ih =>
    simp only [bigConj, conj, neg, atoms, List.append_nil, List.mem_append] at h
    rcases h with h | h
    · exact ⟨ψ, by simp, h⟩
    · obtain ⟨φ, hφ, h⟩ := ih h
      exact ⟨φ, by simp [hφ], h⟩

/-! ### Existential quantification of a range of variables -/

/-- `exRange B L φ = ∃ x_B ⋯ ∃ x_{B+L-1}, φ`. -/
def exRange (B L : ℕ) (φ : RawFormula) : RawFormula := (List.range' B L).foldr ex φ

theorem exRange_succ (B L : ℕ) (φ : RawFormula) :
    exRange B (L + 1) φ = ex B (exRange (B + 1) L φ) :=
  rfl

theorem realize_exRange {M : Type*} {I : ℕ → List M → Prop} :
    ∀ (B L : ℕ) (φ : RawFormula) (v : ℕ → M), (exRange B L φ).Realize I v ↔
      ∃ w : ℕ → M, (∀ y, ¬(B ≤ y ∧ y < B + L) → w y = v y) ∧ φ.Realize I w
  | B, 0, φ, v => by
    constructor
    · exact fun h => ⟨v, fun _ _ => rfl, h⟩
    · rintro ⟨w, hw, h⟩
      have : w = v := funext fun y => hw y (by omega)
      subst this
      exact h
  | B, L + 1, φ, v => by
    rw [exRange_succ, realize_ex]
    simp only [realize_exRange (B + 1) L]
    constructor
    · rintro ⟨m, w, hw, h⟩
      refine ⟨w, fun y hy => ?_, h⟩
      rw [hw y (by omega), Function.update_of_ne (by omega)]
    · rintro ⟨w, hw, h⟩
      refine ⟨w B, w, fun y hy => ?_, h⟩
      by_cases hyB : y = B
      · subst hyB; simp
      · rw [Function.update_of_ne hyB, hw y (by omega)]

theorem atoms_exRange (B L : ℕ) (φ : RawFormula) : (exRange B L φ).atoms = φ.atoms := by
  induction L generalizing B with
  | zero => rfl
  | succ L ih => simp [exRange_succ, ex, neg, atoms, ih]

theorem mem_freeVars_exRange {y : ℕ} {φ : RawFormula} :
    ∀ {B L : ℕ}, y ∈ (exRange B L φ).freeVars → ¬(B ≤ y ∧ y < B + L) ∧ y ∈ φ.freeVars
  | B, 0, h => ⟨by omega, h⟩
  | B, L + 1, h => by
    rw [exRange_succ, ex, freeVars_neg, mem_freeVars_all, freeVars_neg] at h
    obtain ⟨h1, h2⟩ := mem_freeVars_exRange h.1
    exact ⟨by omega, h2⟩

theorem finSat_exRange (B L : ℕ) (φ : RawFormula) : FinSat (exRange B L φ) ↔ FinSat φ := by
  constructor
  · rintro ⟨M, hf, hn, I, v, h⟩
    obtain ⟨w, -, hw⟩ := (realize_exRange B L φ v).1 h
    exact ⟨M, hf, hn, I, w, hw⟩
  · rintro ⟨M, hf, hn, I, v, h⟩
    exact ⟨M, hf, hn, I, v, (realize_exRange B L φ v).2 ⟨v, fun _ _ => rfl, h⟩⟩

/-- The **existential closure** of `φ`: all variables below `varBound φ` quantified
existentially. -/
def exClosure (φ : RawFormula) : RawFormula := exRange 0 φ.varBound φ

theorem isSentence_exClosure (φ : RawFormula) : IsSentence (exClosure φ) := by
  rw [IsSentence, List.eq_nil_iff_forall_not_mem]
  intro y hy
  obtain ⟨h1, h2⟩ := mem_freeVars_exRange hy
  have := lt_varBound_of_mem_freeVars h2
  omega

theorem atoms_exClosure (φ : RawFormula) : (exClosure φ).atoms = φ.atoms :=
  atoms_exRange _ _ φ

theorem finSat_exClosure (φ : RawFormula) : FinSat (exClosure φ) ↔ FinSat φ :=
  finSat_exRange _ _ φ

section Primrec

open Primrec

variable {α : Type*} [Primcodable α]

theorem primrec_exRange {f g : α → ℕ} {h : α → RawFormula} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => exRange (f a) (g a) (h a) := by
  have hr : Primrec fun a => List.range' (f a) (g a) :=
    (list_map (list_range.comp hg) (nat_add.comp (hf.comp fst) snd).to₂).of_eq fun a => by
      rw [List.range'_eq_map_range]
  exact list_foldr hr hh (primrec_ex (fst.comp snd) (snd.comp snd)).to₂

theorem primrec_exClosure : Primrec exClosure :=
  primrec_exRange (const 0) primrec_varBound Primrec.id

end Primrec

end RawFormula

end Cslib.Logic.FO
