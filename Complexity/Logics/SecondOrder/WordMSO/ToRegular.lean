/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Languages.RegularLanguage
public import Complexity.Logics.SecondOrder.WordMSO.Basic

/-!
# MSO-definable languages are regular

The direction "MSO-definable ⇒ regular" of the Büchi–Elgot–Trakhtenbrot theorem
[Büchi][Buchi1960], [Elgot][Elgot1961], [Libkin, Theorem 7.21][Libkin2004],
[Thomas, Section 3][Thomas1997].

Following Thomas, a formula `φ : Formula α m n` with free variables is read over the extended
alphabet `ExtLetter α m n`, whose letters carry, besides a letter of `α`, one bit per free
first-order variable and one per free set variable. An extended word encodes the word of its
`α`-components together with an assignment: set variable `X` is assigned the positions whose
`X`-bit is set, and first-order variable `x` the unique position whose `x`-bit is set. The
language `Formula.extLanguage φ` consists of the extended words in which every first-order
variable is marked exactly once and whose encoded word and assignment satisfy `φ`. It is regular
by induction on `φ`: atoms are positional conditions, implication is handled by complement and
union, and both quantifiers by the image along the letter map forgetting the bit of the bound
variable (`Cslib.Language.IsRegular.map`). For a sentence, there are no bits, and the language of
the sentence is the image of its extended language along the projection to `α`.

The alphabet `α` is arbitrary here; finiteness is only needed for the converse.

## Main definitions

* `Cslib.Logic.WordMSO.ExtLetter`: letters of the extended alphabet.
* `Cslib.Logic.WordMSO.Formula.extLanguage`: the language of a formula over the extended alphabet.

## Main results

* `Cslib.Logic.WordMSO.Formula.isRegular_extLanguage`: the extended language of every formula is
  regular.
* `Cslib.Logic.WordMSO.Sentence.isRegular_language`,
  `Cslib.Logic.WordMSO.Definable.isRegular`: MSO-definable languages are regular.

## References

* [J. R. Büchi, *Weak second-order arithmetic and finite automata*][Buchi1960]
* [C. C. Elgot, *Decision problems of finite automata design and related arithmetics*][Elgot1961]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
* [W. Thomas, *Languages, automata, and logic*][Thomas1997]
-/

public section

universe u

namespace Cslib.Logic.WordMSO

variable {α : Type u}

/-- A letter of the extended alphabet for formulas with `m` free first-order and `n` free set
variables: a letter of `α` together with one bit per free variable, recording whether the
current position is the value of the first-order variable, respectively belongs to the value of
the set variable. -/
structure ExtLetter (α : Type u) (m n : ℕ) where
  /-- The underlying letter. -/
  letter : α
  /-- The bits of the first-order variables. -/
  vars : Fin m → Bool
  /-- The bits of the set variables. -/
  sets : Fin n → Bool

namespace ExtLetter

variable {m n : ℕ}

/-- Forget the bit of the last first-order variable. -/
def dropVar (e : ExtLetter α (m + 1) n) : ExtLetter α m n := ⟨e.letter, Fin.init e.vars, e.sets⟩

/-- Forget the bit of the last set variable. -/
def dropSet (e : ExtLetter α m (n + 1)) : ExtLetter α m n := ⟨e.letter, e.vars, Fin.init e.sets⟩

end ExtLetter

namespace Formula

open ExtLetter

variable {m n : ℕ}

/-- The language of `φ` over the extended alphabet: the extended words in which every first-order
variable `x` is marked at exactly one position `v x`, and whose letters satisfy `φ` under the
assignment `v` and the assignment of the set of marked positions to each set variable. -/
def extLanguage (φ : Formula α m n) : Language (ExtLetter α m n) :=
  {u | ∃ v : Fin m → Fin u.length, (∀ i x, u[i].vars x = true ↔ v x = i) ∧
    φ.Realize (fun i => u[i].letter) v (fun X => {i | u[i].sets X = true})}

theorem mem_extLanguage {φ : Formula α m n} {u : List (ExtLetter α m n)} :
    u ∈ φ.extLanguage ↔ ∃ v : Fin m → Fin u.length, (∀ i x, u[i].vars x = true ↔ v x = i) ∧
      φ.Realize (fun i => u[i].letter) v (fun X => {i | u[i].sets X = true}) :=
  Iff.rfl

/-! ### Regularity toolkit for languages given by predicates on letter functions -/

section Toolkit

variable {β γ : Type*}

private theorem isRegular_of_iff {P Q : List β → Prop} (h : Language.IsRegular {u | P u})
    (hPQ : ∀ u, P u ↔ Q u) : Language.IsRegular {u | Q u} := by
  have e : {u | P u} = {u | Q u} := Set.ext hPQ
  rw [← e]
  exact h

private theorem isRegular_true : Language.IsRegular {_u : List β | True} :=
  isRegular_of_iff Cslib.Language.IsRegular.top fun _ => Iff.rfl

private theorem isRegular_false : Language.IsRegular {_u : List β | False} :=
  isRegular_of_iff Cslib.Language.IsRegular.zero fun _ => Iff.rfl

private theorem isRegular_and {P Q : List β → Prop} (hP : Language.IsRegular {u | P u})
    (hQ : Language.IsRegular {u | Q u}) : Language.IsRegular {u | P u ∧ Q u} :=
  isRegular_of_iff (Cslib.Language.IsRegular.inf hP hQ) fun _ => Language.mem_inf

private theorem isRegular_or {P Q : List β → Prop} (hP : Language.IsRegular {u | P u})
    (hQ : Language.IsRegular {u | Q u}) : Language.IsRegular {u | P u ∨ Q u} :=
  isRegular_of_iff (Cslib.Language.IsRegular.add hP hQ) fun u => Language.mem_add _ _ u

private theorem isRegular_not {P : List β → Prop} (hP : Language.IsRegular {u | P u}) :
    Language.IsRegular {u | ¬ P u} :=
  isRegular_of_iff (Cslib.Language.IsRegular.compl hP) fun _ => Iff.rfl

private theorem isRegular_forall_fin {k : ℕ} {P : Fin k → List β → Prop}
    (hP : ∀ x, Language.IsRegular {u | P x u}) : Language.IsRegular {u | ∀ x, P x u} := by
  induction k with
  | zero => exact isRegular_of_iff isRegular_true fun _ => ⟨fun _ x => x.elim0, fun _ => trivial⟩
  | succ k ih =>
    exact isRegular_of_iff (isRegular_and (hP 0) (ih fun x => hP x.succ))
      fun u => (Fin.forall_fin_succ (P := fun x => P x u)).symm

private theorem isRegular_forall_getElem (p : β → Prop) :
    Language.IsRegular {u : List β | ∀ i : Fin u.length, p u[i]} :=
  isRegular_of_iff (Cslib.Language.IsRegular.setOf_forall_mem p) fun u =>
    ⟨fun h i => h _ (List.getElem_mem _), fun h a ha => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
      exact h ⟨i, hi⟩⟩

private theorem isRegular_exists_getElem (p : β → Prop) :
    Language.IsRegular {u : List β | ∃ i : Fin u.length, p u[i]} :=
  isRegular_of_iff (Cslib.Language.IsRegular.setOf_exists_mem p) fun u =>
    ⟨fun ⟨a, ha, hpa⟩ => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
      exact ⟨⟨i, hi⟩, hpa⟩, fun ⟨i, hi⟩ => ⟨_, List.getElem_mem _, hi⟩⟩

/-- Transport a predicate on letter functions along an equality of lengths. -/
private theorem transport {P : (ℓ : ℕ) → (Fin ℓ → β) → Prop} {ℓ ℓ' : ℕ} (h : ℓ = ℓ')
    {g : Fin ℓ → β} {g' : Fin ℓ' → β} (hg : ∀ i, g' (Fin.cast h i) = g i) :
    P ℓ' g' ↔ P ℓ g := by
  subst h
  have : g' = g := funext hg
  rw [this]

/-- The image along a letter map `f` of a regular language given by a predicate `P` on letter
functions is the regular language given by `Q`, provided `Q` holds of a letter function exactly
when it is `f` applied to a letter function satisfying `P`. -/
private theorem isRegular_map {P : (ℓ : ℕ) → (Fin ℓ → β) → Prop}
    {Q : (ℓ : ℕ) → (Fin ℓ → γ) → Prop} (f : β → γ)
    (hP : Language.IsRegular {u : List β | P u.length (fun i => u[i])})
    (hPQ : ∀ ℓ (g' : Fin ℓ → γ), Q ℓ g' ↔ ∃ g : Fin ℓ → β, f ∘ g = g' ∧ P ℓ g) :
    Language.IsRegular {u' : List γ | Q u'.length (fun i => u'[i])} := by
  refine isRegular_of_iff (Cslib.Language.IsRegular.map f hP) fun u' => ?_
  change u' ∈ List.map f '' {u : List β | P u.length (fun i => u[i])} ↔ _
  rw [hPQ]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hlen : u.length = (u.map f).length := (List.length_map _).symm
    refine ⟨fun i => u[Fin.cast hlen.symm i], funext fun i => (List.getElem_map ..).symm, ?_⟩
    exact (transport (P := P) hlen (g := fun i => u[i])
      (g' := fun i => u[Fin.cast hlen.symm i]) fun _ => rfl).2 hu
  · rintro ⟨g, hfg, hg⟩
    refine ⟨List.ofFn g, ?_, ?_⟩
    · exact (transport (P := P) (List.length_ofFn (f := g)).symm fun i => List.getElem_ofFn ..).2 hg
    · rw [List.map_ofFn, hfg]
      exact List.ofFn_getElem

end Toolkit

/-! ### Satisfaction over extended words -/

/-- An assignment `v` of positions to the first-order variables is the one marked by the letter
function `g`. -/
private def Marks {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (v : Fin m → Fin ℓ) : Prop :=
  ∀ i x, (g i).vars x = true ↔ v x = i

/-- Satisfaction of `φ` by the word and assignment encoded by the letter function `g`. -/
private def Sat (φ : Formula α m n) (ℓ : ℕ) (g : Fin ℓ → ExtLetter α m n) : Prop :=
  ∃ v, Marks g v ∧ φ.Realize (fun i => (g i).letter) v (fun X => {i | (g i).sets X = true})

/-- Every first-order variable is marked exactly once. -/
private def Valid {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) : Prop := ∃ v, Marks g v

private theorem Marks.unique {ℓ : ℕ} {g : Fin ℓ → ExtLetter α m n} {v v' : Fin m → Fin ℓ}
    (hv : Marks g v) (hv' : Marks g v') : v = v' :=
  funext fun x => ((hv' (v x) x).1 ((hv (v x) x).2 rfl)).symm

private theorem valid_iff {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) :
    Valid g ↔ ∀ x, (∃ i, (g i).vars x = true) ∧
      ¬ ∃ i j : Fin ℓ, i < j ∧ (g i).vars x = true ∧ (g j).vars x = true := by
  constructor
  · rintro ⟨v, hv⟩ x
    refine ⟨⟨v x, (hv _ x).2 rfl⟩, ?_⟩
    rintro ⟨i, j, hij, hi, hj⟩
    rw [hv] at hi hj
    exact hij.ne (hi.symm.trans hj)
  · intro h
    choose v hv using fun x => (h x).1
    refine ⟨v, fun i x => ⟨fun hi => ?_, fun hi => hi ▸ hv x⟩⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (h x).2 ⟨v x, i, hlt, hv x, hi⟩
    · exact (h x).2 ⟨i, v x, hlt, hi, hv x⟩

private theorem isRegular_valid :
    Language.IsRegular {u : List (ExtLetter α m n) | Valid (fun i : Fin u.length => u[i])} := by
  refine isRegular_of_iff (isRegular_forall_fin fun x => isRegular_and
    (isRegular_exists_getElem fun e : ExtLetter α m n => e.vars x = true)
    (isRegular_not (Cslib.Language.IsRegular.setOf_exists_lt (fun e : ExtLetter α m n =>
      e.vars x = true) fun e => e.vars x = true))) fun u => (valid_iff _).symm

/-- For a formula whose satisfaction at the marked assignment is a condition `Q` on the marked
positions, satisfaction amounts to validity together with `Q` at all candidate positions. -/
private theorem sat_iff_of_marks {φ : Formula α m n} {ℓ : ℕ} {g : Fin ℓ → ExtLetter α m n}
    {Q : Prop} (hQ : ∀ v, Marks g v → (φ.Realize (fun i => (g i).letter) v
      (fun X => {i | (g i).sets X = true}) ↔ Q)) :
    Sat φ ℓ g ↔ Valid g ∧ Q :=
  ⟨fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, (hQ v hv).1 h⟩, fun ⟨⟨v, hv⟩, h⟩ => ⟨v, hv, (hQ v hv).2 h⟩⟩

private theorem sat_letter {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (a : α) (x : Fin m) :
    Sat (letter a x) ℓ g ↔ Valid g ∧ ∀ i, (g i).vars x = true → (g i).letter = a :=
  sat_iff_of_marks fun v hv =>
    ⟨fun h i hi => (hv i x).1 hi ▸ h, fun h => h (v x) ((hv _ x).2 rfl)⟩

private theorem sat_lt {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (x y : Fin m) :
    Sat (lt x y) ℓ g ↔
      Valid g ∧ ∃ i j : Fin ℓ, i < j ∧ (g i).vars x = true ∧ (g j).vars y = true :=
  sat_iff_of_marks fun v hv =>
    ⟨fun h => ⟨v x, v y, h, (hv _ x).2 rfl, (hv _ y).2 rfl⟩, fun ⟨i, j, hij, hi, hj⟩ => by
      change v x < v y
      rw [(hv i x).1 hi, (hv j y).1 hj]
      exact hij⟩

private theorem sat_mem {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (x : Fin m) (X : Fin n) :
    Sat (mem x X) ℓ g ↔ Valid g ∧ ∀ i, (g i).vars x = true → (g i).sets X = true :=
  sat_iff_of_marks fun v hv =>
    ⟨fun h i hi => (hv i x).1 hi ▸ h, fun h => h (v x) ((hv _ x).2 rfl)⟩

private theorem sat_falsum {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) :
    Sat (falsum : Formula α m n) ℓ g ↔ False :=
  ⟨fun ⟨_, _, h⟩ => h, False.elim⟩

private theorem sat_imp {ℓ : ℕ} (g : Fin ℓ → ExtLetter α m n) (φ ψ : Formula α m n) :
    Sat (imp φ ψ) ℓ g ↔ Valid g ∧ (¬ Sat φ ℓ g ∨ Sat ψ ℓ g) := by
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨⟨v, hv⟩, ?_⟩
    by_cases hφ : Sat φ ℓ g
    · obtain ⟨v', hv', hφ'⟩ := hφ
      rw [hv.unique hv'] at h
      exact Or.inr ⟨v', hv', h hφ'⟩
    · exact Or.inl hφ
  · rintro ⟨⟨v, hv⟩, h⟩
    refine ⟨v, hv, fun hφ => ?_⟩
    rcases h with h | ⟨v', hv', hψ⟩
    · exact absurd ⟨v, hv, hφ⟩ h
    · rwa [hv.unique hv']

private theorem sat_ex {ℓ : ℕ} (g' : Fin ℓ → ExtLetter α m n) (φ : Formula α (m + 1) n) :
    Sat (ex φ) ℓ g' ↔ ∃ g : Fin ℓ → ExtLetter α (m + 1) n, dropVar ∘ g = g' ∧ Sat φ ℓ g := by
  classical
  constructor
  · rintro ⟨v, hv, j, hφ⟩
    refine ⟨fun i => ⟨(g' i).letter, Fin.snoc (g' i).vars (decide (i = j)), (g' i).sets⟩,
      funext fun i => ?_, Fin.snoc v j, fun i x => ?_, hφ⟩
    · simp only [Function.comp_apply, dropVar, Fin.init_snoc]
    · refine Fin.lastCases ?_ (fun x => ?_) x
      · simp only [Fin.snoc_last, decide_eq_true_eq]
        exact eq_comm
      · simp only [Fin.snoc_castSucc]
        exact hv i x
  · rintro ⟨g, rfl, v, hv, hφ⟩
    refine ⟨Fin.init v, fun i x => hv i x.castSucc, v (Fin.last m), ?_⟩
    rw [Fin.snoc_init_self]
    exact hφ

private theorem sat_exSet {ℓ : ℕ} (g' : Fin ℓ → ExtLetter α m n) (φ : Formula α m (n + 1)) :
    Sat (exSet φ) ℓ g' ↔ ∃ g : Fin ℓ → ExtLetter α m (n + 1), dropSet ∘ g = g' ∧ Sat φ ℓ g := by
  classical
  constructor
  · rintro ⟨v, hv, S, hφ⟩
    refine ⟨fun i => ⟨(g' i).letter, (g' i).vars, Fin.snoc (g' i).sets (decide (i ∈ S))⟩,
      funext fun i => ?_, v, hv, ?_⟩
    · simp only [Function.comp_apply, dropSet, Fin.init_snoc]
    · have key : (fun X : Fin (n + 1) => {i : Fin ℓ |
          (Fin.snoc (g' i).sets (decide (i ∈ S)) : Fin (n + 1) → Bool) X = true}) =
          Fin.snoc (fun X => {i | (g' i).sets X = true}) S := by
        funext X
        refine Fin.lastCases ?_ (fun X => ?_) X
        · ext i
          simp only [Fin.snoc_last, Set.mem_ofPred_eq, decide_eq_true_eq]
        · simp only [Fin.snoc_castSucc]
      change φ.Realize _ v (fun X : Fin (n + 1) => {i : Fin ℓ |
          (Fin.snoc (g' i).sets (decide (i ∈ S)) : Fin (n + 1) → Bool) X = true})
      rw [key]
      exact hφ
  · rintro ⟨g, rfl, v, hv, hφ⟩
    refine ⟨v, hv, {i | (g i).sets (Fin.last n) = true}, ?_⟩
    have key : (Fin.snoc (fun X : Fin n => {i : Fin ℓ | (dropSet (g i)).sets X = true})
        {i | (g i).sets (Fin.last n) = true} : Fin (n + 1) → Set (Fin ℓ)) =
        fun X => {i | (g i).sets X = true} := by
      funext X
      refine Fin.lastCases ?_ (fun X => ?_) X
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc, dropSet, Fin.init]
    change φ.Realize _ v (Fin.snoc (fun X : Fin n => {i : Fin ℓ | (dropSet (g i)).sets X = true})
        {i | (g i).sets (Fin.last n) = true})
    rw [key]
    exact hφ

private theorem isRegular_sat : ∀ {m n : ℕ} (φ : Formula α m n),
    Language.IsRegular {u : List (ExtLetter α m n) | Sat φ u.length (fun i => u[i])}
  | _, _, letter a x => isRegular_of_iff (isRegular_and isRegular_valid
      (isRegular_forall_getElem fun e => e.vars x = true → e.letter = a))
      fun _ => (sat_letter _ a x).symm
  | _, _, lt x y => isRegular_of_iff (isRegular_and isRegular_valid
      (Cslib.Language.IsRegular.setOf_exists_lt (fun e => e.vars x = true) fun e =>
        e.vars y = true))
      fun _ => (sat_lt _ x y).symm
  | _, _, mem x X => isRegular_of_iff (isRegular_and isRegular_valid
      (isRegular_forall_getElem fun e => e.vars x = true → e.sets X = true))
      fun _ => (sat_mem _ x X).symm
  | _, _, falsum => isRegular_of_iff isRegular_false fun _ => (sat_falsum _).symm
  | _, _, imp φ ψ => isRegular_of_iff (isRegular_and isRegular_valid
      (isRegular_or (isRegular_not (isRegular_sat φ)) (isRegular_sat ψ)))
      fun _ => (sat_imp _ φ ψ).symm
  | _, _, ex φ => isRegular_map dropVar (isRegular_sat φ) fun _ g' => sat_ex g' φ
  | _, _, exSet φ => isRegular_map dropSet (isRegular_sat φ) fun _ g' => sat_exSet g' φ

/-- **MSO ⇒ regular, with free variables.** The language over the extended alphabet of any MSO
formula is regular [Thomas, Section 3][Thomas1997]. -/
theorem isRegular_extLanguage (φ : Formula α m n) : φ.extLanguage.IsRegular :=
  isRegular_sat φ

end Formula

/-- **MSO ⇒ regular.** The language of an MSO sentence is regular, over any alphabet
[Büchi][Buchi1960], [Libkin, Theorem 7.21][Libkin2004]. -/
theorem Sentence.isRegular_language (φ : Sentence α) : φ.language.IsRegular := by
  refine Formula.isRegular_map (P := fun ℓ g => Formula.Sat φ ℓ g)
    (Q := fun ℓ w => φ.Realize w Fin.elim0 Fin.elim0) ExtLetter.letter
    (Formula.isRegular_sat φ) fun ℓ w => ?_
  constructor
  · intro h
    refine ⟨fun i => ⟨w i, Fin.elim0, Fin.elim0⟩, rfl, Fin.elim0, fun _ x => x.elim0, ?_⟩
    have e : (fun X : Fin 0 => {i : Fin ℓ | (Fin.elim0 X : Bool) = true}) = Fin.elim0 :=
      funext fun X => X.elim0
    change φ.Realize w Fin.elim0 (fun X : Fin 0 => {i : Fin ℓ | (Fin.elim0 X : Bool) = true})
    rw [e]
    exact h
  · rintro ⟨g, rfl, v, _, h⟩
    have ev : v = Fin.elim0 := funext fun x => x.elim0
    have eV : (fun X : Fin 0 => {i : Fin ℓ | (g i).sets X = true}) = Fin.elim0 :=
      funext fun X => X.elim0
    rw [ev, eV] at h
    exact h

/-- **MSO-definable languages are regular**, over any alphabet. -/
theorem Definable.isRegular {L : Language α} (h : Definable L) : L.IsRegular := by
  obtain ⟨φ, rfl⟩ := h
  exact φ.isRegular_language

/-- First-order definable languages are regular. -/
theorem FODefinable.isRegular {L : Language α} (h : FODefinable L) : L.IsRegular :=
  h.definable.isRegular

end Cslib.Logic.WordMSO
