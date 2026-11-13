/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.Occurrence
public import CslibFrontier.Foundations.Data.Matrix.Permanent.Split

/-!
# Counting cycle covers of the tracks

After all clause gadgets are eliminated, the matrix of a formula is reduced to its tracks: the
rows are the auxiliary vertices and the exits of a set `P` of occurrences, the columns the
auxiliary vertices and the entries of `P`, and the entries count track edges. A bijection along
track edges chooses one of the two tracks at every auxiliary vertex, that is, an assignment, and
is then forced along the chosen tracks. It exists exactly when `P` is the set of occurrences whose
literal is true under that assignment. `permOn_trackMatrix` counts these bijections: they are as
many as the assignments of the listed variables whose true occurrences are exactly `P`.
-/

@[expose] public section

open Finset Matrix

namespace Cslib.Complexity.PermanentThreeSAT

open Cslib.Logic.PL

variable {φ : CNF ℕ}

/-- The track edges of `φ` as a matrix. -/
def trackMatrix (φ : CNF ℕ) : Matrix (Fin (size φ)) (Fin (size φ)) ℤ :=
  fun k l => trackEntry φ k l

/-- The row vertices left with the occurrences `P`: auxiliary vertices and exits of `P`. -/
def InRows (φ : CNF ℕ) (P : Finset ℕ) (k : ℕ) : Prop :=
  k < numAux φ ∨ ∃ o ∈ P, k = exitIdx φ o

/-- The column vertices left with the occurrences `P`: auxiliary vertices and entries of `P`. -/
def InCols (φ : CNF ℕ) (P : Finset ℕ) (k : ℕ) : Prop :=
  k < numAux φ ∨ ∃ o ∈ P, k = entryIdx φ o

instance (P : Finset ℕ) : DecidablePred (InRows φ P) := fun _ => by
  unfold InRows; infer_instance

instance (P : Finset ℕ) : DecidablePred (InCols φ P) := fun _ => by
  unfold InCols; infer_instance

/-- The value of a variable under an assignment of the listed variables, `false` if unlisted. -/
def assignVal (φ : CNF ℕ) (a : Fin (numAux φ) → Bool) (x : ℕ) : Bool :=
  if h : (varList φ).idxOf x < numAux φ then a ⟨_, h⟩ else false

/-- The occurrences of `P` are exactly the occurrences whose literal is true under `a`. -/
def TrueExactly (φ : CNF ℕ) (P : Finset ℕ) (a : Fin (numAux φ) → Bool) : Prop :=
  ∀ o < numOcc φ, o ∈ P ↔ Literal.eval (assignVal φ a) (litAt φ o) = true

instance (P : Finset ℕ) : DecidablePred (TrueExactly φ P) := fun _ => by
  unfold TrueExactly; infer_instance

/-- The head of the track edge used at `k` under the assignment `a`. -/
def succOf (φ : CNF ℕ) (a : Fin (numAux φ) → Bool) (k : ℕ) : ℕ :=
  if h : k < numAux φ then auxSucc φ k (a ⟨k, h⟩) else exitSucc φ (exitOcc φ k)

theorem assignVal_getD (a : Fin (numAux φ) → Bool) {i : ℕ} (hi : i < numAux φ) :
    assignVal φ a ((varList φ).getD i 0) = a ⟨i, hi⟩ := by
  unfold assignVal
  rw [dite_eq_left (by rw [idxOf_getD_varList hi]; exact hi)]
  congr 1
  exact Fin.ext (idxOf_getD_varList hi)

/-- A true occurrence is the literal of its variable's index with the assigned value. -/
theorem litAt_eq_of_true (hφ : WellFormed φ) (a : Fin (numAux φ) → Bool) {o : ℕ}
    (ho : o < numOcc φ) (ht : Literal.eval (assignVal φ a) (litAt φ o) = true) :
    ∃ (i : ℕ) (hi : i < numAux φ), litAt φ o = ((varList φ).getD i 0, a ⟨i, hi⟩) := by
  have hm := fst_litAt_mem_varList hφ ho
  have hi : (varList φ).idxOf (litAt φ o).1 < numAux φ := List.idxOf_lt_length_iff.2 hm
  refine ⟨_, hi, Prod.ext (getD_varList_idxOf hm).symm ?_⟩
  rw [Literal.eval_eq_true_iff, assignVal, dite_eq_left hi] at ht
  exact ht.symm

theorem eval_of_litAt_eq (a : Fin (numAux φ) → Bool) {o i : ℕ} (hi : i < numAux φ)
    (h : litAt φ o = ((varList φ).getD i 0, a ⟨i, hi⟩)) :
    Literal.eval (assignVal φ a) (litAt φ o) = true := by
  rw [h, Literal.eval_eq_true_iff, assignVal_getD]

theorem succOf_aux (a : Fin (numAux φ) → Bool) {k : ℕ} (hk : k < numAux φ) :
    succOf φ a k = auxSucc φ k (a ⟨k, hk⟩) := by
  rw [succOf, dite_eq_left hk]

theorem succOf_exit (a : Fin (numAux φ) → Bool) (o : ℕ) :
    succOf φ a (exitIdx φ o) = exitSucc φ o := by
  rw [succOf, dite_eq_right (by have := numAux_le_exitIdx φ o; omega), exitOcc_exitIdx]

/-! ### Track entries -/

theorem trackEntry_aux {k : ℕ} (hk : k < numAux φ) (l : ℕ) :
    trackEntry φ k l =
      (if auxSucc φ k true = l then 1 else 0) + (if auxSucc φ k false = l then 1 else 0) := by
  rw [trackEntry, ite_eq_left hk]

theorem trackEntry_exit (o l : ℕ) :
    trackEntry φ (exitIdx φ o) l = if exitSucc φ o = l then 1 else 0 := by
  have h1 : ¬ exitIdx φ o < numAux φ := by have := numAux_le_exitIdx φ o; omega
  have h2 : 3 ≤ (exitIdx φ o - numAux φ) % 8 ∧ (exitIdx φ o - numAux φ) % 8 < 6 := by
    unfold exitIdx; omega
  rw [trackEntry, ite_eq_right h1, ite_eq_left h2, exitOcc_exitIdx]

theorem trackEntry_zero_or_one (hφ : WellFormed φ) (k l : ℕ) :
    trackEntry φ k l = 0 ∨ trackEntry φ k l = 1 := by
  by_cases h1 : k < numAux φ
  · rw [trackEntry_aux h1]
    have hne := auxSucc_true_ne_false hφ h1
    by_cases h2 : auxSucc φ k true = l <;> by_cases h3 : auxSucc φ k false = l
    · exact absurd (h2.trans h3.symm) hne
    all_goals simp [h2, h3]
  · unfold trackEntry
    rw [ite_eq_right h1]
    split_ifs <;> simp

/-- The aux row has a `1` exactly at the heads of its two tracks. -/
theorem trackEntry_aux_eq_one (hφ : WellFormed φ) {k : ℕ} (hk : k < numAux φ) (l : ℕ) :
    trackEntry φ k l = 1 ↔ l = auxSucc φ k true ∨ l = auxSucc φ k false := by
  rw [trackEntry_aux hk]
  have hne := auxSucc_true_ne_false hφ hk
  by_cases h2 : auxSucc φ k true = l <;> by_cases h3 : auxSucc φ k false = l
  · exact absurd (h2.trans h3.symm) hne
  · subst h2; simp [h3, Ne.symm h3]
  · subst h3; simp [h2, Ne.symm h2]
  · simp [h2, h3, Ne.symm h2, Ne.symm h3]

theorem trackEntry_exit_eq_one (o l : ℕ) :
    trackEntry φ (exitIdx φ o) l = 1 ↔ l = exitSucc φ o := by
  rw [trackEntry_exit]
  by_cases h : exitSucc φ o = l
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ### Injectivity, mapping and recovery -/

section Lemmas

variable (hφ : WellFormed φ) {P : Finset ℕ} (hP : P ⊆ range (numOcc φ))
  (a : Fin (numAux φ) → Bool)
include hφ hP

/-- The used edges lead into the columns when `P` is exactly the true occurrences. -/
theorem inCols_succOf (hgood : TrueExactly φ P a) {k : ℕ} (hk : InRows φ P k) :
    InCols φ P (succOf φ a k) := by
  rcases hk with hk | ⟨o, hoP, rfl⟩
  · rw [succOf_aux a hk]
    rcases h : firstOcc φ ((varList φ).getD k 0, a ⟨k, hk⟩) with _ | o
    · rw [auxSucc_eq_none h]; exact Or.inl hk
    · rw [auxSucc_eq_some h]
      obtain ⟨ho, hl, -⟩ := firstOcc_eq_some.1 h
      exact Or.inr ⟨o, (hgood o ho).2 (eval_of_litAt_eq a hk hl), rfl⟩
  · have ho : o < numOcc φ := mem_range.1 (hP hoP)
    rw [succOf_exit]
    rcases h : nextOcc φ o with _ | o'
    · rw [exitSucc_eq_none h]
      exact Or.inl (List.idxOf_lt_length_iff.2 (fst_litAt_mem_varList hφ ho))
    · rw [exitSucc_eq_some h]
      obtain ⟨ho', -, hl, -⟩ := nextOcc_eq_some.1 h
      refine Or.inr ⟨o', (hgood o' ho').2 ?_, rfl⟩
      rw [hl]
      exact (hgood o ho).1 hoP

omit hP in
private theorem aux_ne_exit (hgood : TrueExactly φ P a) {k o : ℕ} (hk : k < numAux φ)
    (ho : o < numOcc φ) (hoP : o ∈ P) : auxSucc φ k (a ⟨k, hk⟩) ≠ exitSucc φ o := by
  intro h
  rcases h1 : firstOcc φ ((varList φ).getD k 0, a ⟨k, hk⟩) with _ | o₁ <;>
    rcases h2 : nextOcc φ o with _ | o₂
  · rw [auxSucc_eq_none h1, exitSucc_eq_none h2] at h
    obtain ⟨i, hi, hl⟩ := litAt_eq_of_true hφ a ho ((hgood o ho).1 hoP)
    have hm := fst_litAt_mem_varList hφ ho
    have hik : i = k := by
      rw [hl] at h
      rw [h, idxOf_getD_varList hi]
    subst hik
    exact firstOcc_eq_none.1 h1 o ho hl
  · rw [auxSucc_eq_none h1, exitSucc_eq_some h2] at h
    have := numAux_le_entryIdx φ o₂
    omega
  · rw [auxSucc_eq_some h1, exitSucc_eq_none h2] at h
    have := numAux_le_entryIdx φ o₁
    have := List.idxOf_lt_length_iff.2 (fst_litAt_mem_varList hφ ho)
    unfold numAux at *
    omega
  · rw [auxSucc_eq_some h1, exitSucc_eq_some h2] at h
    have h12 := entryIdx_injective φ h
    subst h12
    obtain ⟨-, hl₁, hmin⟩ := firstOcc_eq_some.1 h1
    obtain ⟨-, hlt, hl₂, -⟩ := nextOcc_eq_some.1 h2
    exact hmin o hlt (hl₂.symm.trans hl₁)

/-- The used edges are injective on the rows when `P` is exactly the true occurrences. -/
theorem succOf_injOn (hgood : TrueExactly φ P a) {k₁ k₂ : ℕ} (h₁ : InRows φ P k₁)
    (h₂ : InRows φ P k₂) (h : succOf φ a k₁ = succOf φ a k₂) : k₁ = k₂ := by
  rcases h₁ with hk₁ | ⟨o₁, ho₁P, rfl⟩ <;> rcases h₂ with hk₂ | ⟨o₂, ho₂P, rfl⟩
  · rw [succOf_aux a hk₁, succOf_aux a hk₂] at h
    rcases e₁ : firstOcc φ ((varList φ).getD k₁ 0, a ⟨k₁, hk₁⟩) with _ | p₁ <;>
      rcases e₂ : firstOcc φ ((varList φ).getD k₂ 0, a ⟨k₂, hk₂⟩) with _ | p₂
    · rwa [auxSucc_eq_none e₁, auxSucc_eq_none e₂] at h
    · rw [auxSucc_eq_none e₁, auxSucc_eq_some e₂] at h
      have := numAux_le_entryIdx φ p₂; omega
    · rw [auxSucc_eq_some e₁, auxSucc_eq_none e₂] at h
      have := numAux_le_entryIdx φ p₁; omega
    · rw [auxSucc_eq_some e₁, auxSucc_eq_some e₂] at h
      have hp := entryIdx_injective φ h
      subst hp
      have hl := (firstOcc_eq_some.1 e₁).2.1.symm.trans (firstOcc_eq_some.1 e₂).2.1
      have hx := congrArg Prod.fst hl
      simp only at hx
      rw [← idxOf_getD_varList hk₁, hx, idxOf_getD_varList hk₂]
  · rw [succOf_aux a hk₁, succOf_exit] at h
    exact absurd h (aux_ne_exit hφ a hgood hk₁ (mem_range.1 (hP ho₂P)) ho₂P)
  · rw [succOf_aux a hk₂, succOf_exit] at h
    exact absurd h.symm (aux_ne_exit hφ a hgood hk₂ (mem_range.1 (hP ho₁P)) ho₁P)
  · rw [succOf_exit, succOf_exit] at h
    have ho₁ := mem_range.1 (hP ho₁P)
    have ho₂ := mem_range.1 (hP ho₂P)
    suffices o₁ = o₂ by rw [this]
    rcases e₁ : nextOcc φ o₁ with _ | p₁ <;> rcases e₂ : nextOcc φ o₂ with _ | p₂
    · rw [exitSucc_eq_none e₁, exitSucc_eq_none e₂] at h
      obtain ⟨i₁, hi₁, hl₁⟩ := litAt_eq_of_true hφ a ho₁ ((hgood o₁ ho₁).1 ho₁P)
      obtain ⟨i₂, hi₂, hl₂⟩ := litAt_eq_of_true hφ a ho₂ ((hgood o₂ ho₂).1 ho₂P)
      have hi : i₁ = i₂ := by
        rw [hl₁, hl₂] at h
        simpa only [idxOf_getD_varList hi₁, idxOf_getD_varList hi₂] using h
      subst hi
      have hl : litAt φ o₁ = litAt φ o₂ := hl₁.trans hl₂.symm
      rcases lt_trichotomy o₁ o₂ with hlt | heq | hgt
      · exact absurd hl.symm (nextOcc_eq_none.1 e₁ o₂ ho₂ hlt)
      · exact heq
      · exact absurd hl (nextOcc_eq_none.1 e₂ o₁ ho₁ hgt)
    · rw [exitSucc_eq_none e₁, exitSucc_eq_some e₂] at h
      have := numAux_le_entryIdx φ p₂
      have := List.idxOf_lt_length_iff.2 (fst_litAt_mem_varList hφ ho₁)
      unfold numAux at *; omega
    · rw [exitSucc_eq_some e₁, exitSucc_eq_none e₂] at h
      have := numAux_le_entryIdx φ p₁
      have := List.idxOf_lt_length_iff.2 (fst_litAt_mem_varList hφ ho₂)
      unfold numAux at *; omega
    · rw [exitSucc_eq_some e₁, exitSucc_eq_some e₂] at h
      have hp := entryIdx_injective φ h
      subst hp
      obtain ⟨-, hlt₁, hl₁, hmin₁⟩ := nextOcc_eq_some.1 e₁
      obtain ⟨-, hlt₂, hl₂, hmin₂⟩ := nextOcc_eq_some.1 e₂
      rcases lt_trichotomy o₁ o₂ with hlt | heq | hgt
      · exact absurd (hl₂.symm.trans hl₁) (hmin₁ o₂ hlt₂ hlt)
      · exact heq
      · exact absurd (hl₁.symm.trans hl₂) (hmin₂ o₁ hlt₁ hgt)

/-- If the used edges map the rows into and onto the columns, `P` is exactly the set of true
occurrences. -/
theorem trueExactly_of_succOf (hmap : ∀ k, InRows φ P k → InCols φ P (succOf φ a k))
    (hsurj : ∀ l, InCols φ P l → ∃ k, InRows φ P k ∧ succOf φ a k = l) :
    TrueExactly φ P a := by
  have memP : ∀ o, InCols φ P (entryIdx φ o) → o ∈ P := fun o h => by
    rcases h with h | ⟨o', ho', he⟩
    · have := numAux_le_entryIdx φ o; omega
    · rwa [entryIdx_injective φ he]
  intro o ho
  constructor
  · intro hoP
    induction o using Nat.strong_induction_on with
    | _ o ih =>
      obtain ⟨k, hk, hks⟩ := hsurj _ (Or.inr ⟨o, hoP, rfl⟩)
      rcases hk with hk | ⟨o', ho'P, rfl⟩
      · rw [succOf_aux a hk] at hks
        rcases e : firstOcc φ ((varList φ).getD k 0, a ⟨k, hk⟩) with _ | o₁
        · rw [auxSucc_eq_none e] at hks
          have := numAux_le_entryIdx φ o; omega
        · rw [auxSucc_eq_some e] at hks
          have := entryIdx_injective φ hks
          subst this
          exact eval_of_litAt_eq a hk (firstOcc_eq_some.1 e).2.1
      · rw [succOf_exit] at hks
        rcases e : nextOcc φ o' with _ | o₁
        · rw [exitSucc_eq_none e] at hks
          have := numAux_le_entryIdx φ o
          have := List.idxOf_lt_length_iff.2
            (fst_litAt_mem_varList hφ (mem_range.1 (hP ho'P)))
          unfold numAux at *; omega
        · rw [exitSucc_eq_some e] at hks
          have := entryIdx_injective φ hks
          subst this
          obtain ⟨-, hlt, hl, -⟩ := nextOcc_eq_some.1 e
          rw [hl]
          exact ih o' hlt (mem_range.1 (hP ho'P)) ho'P
  · intro ht
    induction o using Nat.strong_induction_on with
    | _ o ih =>
      by_cases hpred : ∃ o' < o, litAt φ o' = litAt φ o
      · obtain ⟨o', hlt, hl, hn⟩ := exists_nextOcc_eq ho hpred
        have ho'P : o' ∈ P := ih o' hlt (by omega) (by rw [hl]; exact ht)
        have := hmap _ (Or.inr ⟨o', ho'P, rfl⟩)
        rw [succOf_exit, exitSucc_eq_some hn] at this
        exact memP o this
      · obtain ⟨i, hi, hl⟩ := litAt_eq_of_true hφ a ho ht
        have hf : firstOcc φ ((varList φ).getD i 0, a ⟨i, hi⟩) = some o :=
          firstOcc_eq_some.2 ⟨ho, hl, fun o' ho' h => hpred ⟨o', ho', h.trans hl.symm⟩⟩
        have := hmap i (Or.inl hi)
        rw [succOf_aux a hi, auxSucc_eq_some hf] at this
        exact memP o this

end Lemmas

/-! ### The count -/

/-- The row vertices for the occurrences `P`, as a set of vertices. -/
def rowSet (φ : CNF ℕ) (P : Finset ℕ) : Finset (Fin (size φ)) :=
  univ.filter fun u => InRows φ P u

/-- The column vertices for the occurrences `P`, as a set of vertices. -/
def colSet (φ : CNF ℕ) (P : Finset ℕ) : Finset (Fin (size φ)) :=
  univ.filter fun u => InCols φ P u

theorem numAux_le_size (φ : CNF ℕ) : numAux φ ≤ size φ := by unfold size; omega

theorem succOf_lt_size (hφ : WellFormed φ) {P : Finset ℕ} (hP : P ⊆ range (numOcc φ))
    {k : ℕ} (hk : InRows φ P k) (a : Fin (numAux φ) → Bool) :
    succOf φ a k < size φ := by
  rcases hk with hk | ⟨o, hoP, rfl⟩
  · rw [succOf_aux a hk]; exact auxSucc_lt_size hk _
  · rw [succOf_exit]; exact exitSucc_lt_size hφ (mem_range.1 (hP hoP))

/-- There are as many row vertices as column vertices. -/
theorem card_rowSet {P : Finset ℕ} (hP : P ⊆ range (numOcc φ)) :
    (rowSet φ P).card = (colSet φ P).card := by
  refine card_bij' (fun u hu => ⟨if u.val < numAux φ then u else u - 3, ?_⟩)
    (fun u hu => ⟨if u.val < numAux φ then u else u + 3, ?_⟩) ?_ ?_ ?_ ?_
  · split_ifs <;> omega
  · simp only [colSet, mem_filter, mem_univ, true_and] at hu
    split_ifs with h
    · exact u.2
    · rcases hu with hu | ⟨o, hoP, he⟩
      · exact absurd hu h
      · have := exitIdx_lt_size (φ := φ) (mem_range.1 (hP hoP))
        unfold exitIdx at this; unfold entryIdx at he; omega
  · intro u hu
    simp only [rowSet, colSet, mem_filter, mem_univ, true_and] at hu ⊢
    rcases hu with hu | ⟨o, hoP, he⟩
    · simp only [hu, ite_true]; exact Or.inl hu
    · have := numAux_le_exitIdx φ o
      have hn : ¬ u.val < numAux φ := by omega
      simp only [hn, ite_false]
      refine Or.inr ⟨o, hoP, ?_⟩
      rw [he]; unfold exitIdx entryIdx; omega
  · intro u hu
    simp only [rowSet, colSet, mem_filter, mem_univ, true_and] at hu ⊢
    rcases hu with hu | ⟨o, hoP, he⟩
    · simp only [hu, ite_true]; exact Or.inl hu
    · have := numAux_le_entryIdx φ o
      have hn : ¬ u.val < numAux φ := by omega
      simp only [hn, ite_false]
      refine Or.inr ⟨o, hoP, ?_⟩
      rw [he]; unfold exitIdx entryIdx; omega
  · intro u hu
    ext
    simp only [rowSet, mem_filter, mem_univ, true_and] at hu
    by_cases h : u.val < numAux φ
    · simp [h]
    · have h3 : ¬ u.val - 3 < numAux φ := by
        rcases hu with hu | ⟨o, -, he⟩
        · exact absurd hu h
        · rw [he]; unfold exitIdx; omega
      simp only [h, h3, ite_false]
      rcases hu with hu | ⟨o, -, he⟩
      · exact absurd hu h
      · rw [he]; unfold exitIdx; omega
  · intro u hu
    ext
    simp only [colSet, mem_filter, mem_univ, true_and] at hu
    by_cases h : u.val < numAux φ
    · simp [h]
    · have h3 : ¬ u.val + 3 < numAux φ := by omega
      simp only [h, h3, ite_false]
      omega

/-- The bijection of an assignment: follow the chosen tracks on the rows. -/
def bijOfAssign {P : Finset ℕ} (hlt : ∀ k, InRows φ P k → ∀ a, succOf φ a k < size φ)
    (a : Fin (numAux φ) → Bool) (u : Fin (size φ)) : Fin (size φ) :=
  if h : InRows φ P u then ⟨succOf φ a u, hlt u h a⟩ else u

/-- The assignment read off a bijection at the auxiliary vertices. -/
def assignOfBij (f : Fin (size φ) → Fin (size φ)) (i : Fin (numAux φ)) : Bool :=
  decide ((f ⟨i, lt_of_lt_of_le i.2 (numAux_le_size φ)⟩).val = auxSucc φ i true)

/-- **The count of track bijections**: the permanent sum of the track matrix between the rows and
the columns of `P` is the number of assignments whose true occurrences are exactly `P`. -/
theorem permOn_trackMatrix (hφ : WellFormed φ) {P : Finset ℕ}
    (hP : P ⊆ range (numOcc φ)) :
    permOn (trackMatrix φ) (rowSet φ P) (colSet φ P) =
      ((univ : Finset (Fin (numAux φ) → Bool)).filter (TrueExactly φ P)).card := by
  have hlt : ∀ k, InRows φ P k → ∀ a, succOf φ a k < size φ :=
    fun k hk a => succOf_lt_size hφ hP hk a
  rw [permOn_eq_card (M := trackMatrix φ) fun i j => trackEntry_zero_or_one hφ _ _]
  norm_cast
  have hval : ∀ (f : Fin (size φ) → Fin (size φ)),
      f ∈ (bijOn (rowSet φ P) (colSet φ P)).filter
        (fun f => ∀ i ∈ rowSet φ P, trackMatrix φ i (f i) = 1) →
      bijOfAssign hlt (assignOfBij f) = f := by
    intro f hf
    simp only [mem_filter, mem_bijOn] at hf
    obtain ⟨⟨-, -, -, hout⟩, hedge⟩ := hf
    funext u
    unfold bijOfAssign
    split_ifs with hu
    · have hur : u ∈ rowSet φ P := by simp [rowSet, hu]
      have he := hedge u hur
      unfold trackMatrix at he
      ext
      change succOf φ (assignOfBij f) u = (f u).val
      rcases hu with hk | ⟨o, hoP, hko⟩
      · rw [succOf_aux _ hk]
        rcases (trackEntry_aux_eq_one hφ hk _).1 he with h | h
        · have : assignOfBij f ⟨u, hk⟩ = true := by
            simp only [assignOfBij, decide_eq_true_eq]; exact h
          rw [this, h]
        · have : assignOfBij f ⟨u, hk⟩ = false := by
            simp only [assignOfBij, decide_eq_false_iff_not]
            rw [show (⟨u.val, _⟩ : Fin (size φ)) = u from rfl, h]
            exact (auxSucc_true_ne_false hφ hk).symm
          rw [this, h]
      · rw [hko, succOf_exit]
        rw [hko] at he
        exact ((trackEntry_exit_eq_one o _).1 he).symm
    · exact (hout u (by simpa [rowSet] using hu)).symm
  symm
  refine card_bij' (fun a _ => bijOfAssign hlt a) (fun f _ => assignOfBij f) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    simp only [mem_filter, mem_bijOn]
    have hF : ∀ (u : Fin (size φ)) (hu : InRows φ P u),
        (bijOfAssign hlt a u).val = succOf φ a u := by
      intro u hu
      simp [bijOfAssign, hu]
    have hmap : ∀ u ∈ rowSet φ P, bijOfAssign hlt a u ∈ colSet φ P := fun u hu => by
      simp only [rowSet, colSet, mem_filter, mem_univ, true_and] at hu ⊢
      rw [hF u hu]
      exact inCols_succOf hφ hP a ha hu
    have hinj : ∀ u ∈ rowSet φ P, ∀ v ∈ rowSet φ P,
        bijOfAssign hlt a u = bijOfAssign hlt a v → u = v := fun u hu v hv h => by
      simp only [rowSet, mem_filter, mem_univ, true_and] at hu hv
      have := congrArg Fin.val h
      rw [hF u hu, hF v hv] at this
      exact Fin.ext (succOf_injOn hφ hP a ha hu hv this)
    refine ⟨⟨hmap, hinj, ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
    · intro t ht
      have hsurj := Finset.surj_on_of_inj_on_of_card_le
        (s := rowSet φ P) (t := colSet φ P) (fun u _ => bijOfAssign hlt a u)
        hmap (fun u v hu hv h => hinj u hu v hv h) (card_rowSet hP).ge
      obtain ⟨u, hu, rfl⟩ := hsurj t ht
      exact ⟨u, hu, rfl⟩
    · have hu' : ¬ InRows φ P u := by simpa [rowSet] using hu
      simp [bijOfAssign, hu']
    · simp only [rowSet, mem_filter, mem_univ, true_and] at hu
      unfold trackMatrix
      rw [hF u hu]
      rcases hu with hk | ⟨o, hoP, hko⟩
      · rw [succOf_aux a hk, trackEntry_aux_eq_one hφ hk]
        cases a ⟨u, hk⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
      · rw [hko, succOf_exit, trackEntry_exit_eq_one]
  · intro f hf
    simp only [mem_filter, mem_univ, true_and]
    have hfa := hval f hf
    simp only [mem_filter, mem_bijOn] at hf
    obtain ⟨⟨hmaps, -, hsurj, -⟩, -⟩ := hf
    set a := assignOfBij f
    have hF : ∀ (u : Fin (size φ)) (hu : InRows φ P u), (f u).val = succOf φ a u := by
      intro u hu
      rw [← hfa]
      simp [bijOfAssign, hu]
    refine trueExactly_of_succOf hφ hP a (fun k hk => ?_) (fun l hl => ?_)
    · have hkN : k < size φ := by
        rcases hk with hk | ⟨o, hoP, rfl⟩
        · exact lt_of_lt_of_le hk (numAux_le_size φ)
        · exact exitIdx_lt_size (mem_range.1 (hP hoP))
      have := hmaps ⟨k, hkN⟩ (by simp [rowSet, hk])
      simp only [colSet, mem_filter, mem_univ, true_and] at this
      rwa [hF ⟨k, hkN⟩ hk] at this
    · have hlN : l < size φ := by
        rcases hl with hl | ⟨o, hoP, rfl⟩
        · exact lt_of_lt_of_le hl (numAux_le_size φ)
        · exact entryIdx_lt_size (mem_range.1 (hP hoP))
      obtain ⟨u, hu, hul⟩ := hsurj ⟨l, hlN⟩ (by simp [colSet, hl])
      simp only [rowSet, mem_filter, mem_univ, true_and] at hu
      refine ⟨u, hu, ?_⟩
      rw [← hF u hu, hul]
  · intro a _
    funext i
    have hi : InRows φ P i := Or.inl i.2
    simp only [assignOfBij, bijOfAssign, hi, dite_true]
    rw [succOf_aux a i.2]
    have hne := auxSucc_true_ne_false hφ i.2
    cases h : a i
    · simp only [decide_eq_false_iff_not]
      exact hne.symm
    · simp
  · intro f hf
    exact hval f hf


end Cslib.Complexity.PermanentThreeSAT
