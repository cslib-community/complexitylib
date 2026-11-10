/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Pebbling.Descending
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Tactic.EncLen

/-!
# Pebble configuration words in the space of their storage

Native space certificates for the operations on configuration words and value tables that the
pebbling evaluator of `Cslib.Pebbling.Descending` performs: the first difference of two words,
readiness of an index, a move of the pebble game on words, and reading, clearing and listing the
stored values. Each certificate takes space linear in its encoded arguments plus the space of the
certificates it is given for the child map and the pebble bound, which may depend on a parameter.

Each operation comes in two forms. A `budget_` form computes the operation on arguments computed
within a common budget, and stays within it; these compose. An `_inSpace` form states the space on
the encoded arguments. Through `ComputableInSpace.exists_inO`, `wordStep_inSpace` gives an edge
test for Savitch's algorithm, `Cslib.Reachability.computableInO_savitch`.

Inserting an entry into a table and comparing its length with a bound are compositions of
existing certificates: `budget_cons (budget_prod hi hx) ht` and
`budget_natLt (budget_length ht) hs`.

## Main definitions

* `Cslib.Pebbling.Descending.encTable`: the encoding of a table of binary indices with their words.

## Main results

* `Cslib.Pebbling.Descending.diffIndex_inSpace`, `Cslib.Pebbling.Descending.budget_diffIndex`:
  the first difference of two words.
* `Cslib.Pebbling.Descending.budget_getD_diffIndex`: the letter at the first difference.
* `Cslib.Pebbling.Descending.ready_inSpace`, `Cslib.Pebbling.Descending.budget_ready`: readiness
  of an index for a child map depending on a parameter.
* `Cslib.Pebbling.Descending.wordStep_inSpace`, `Cslib.Pebbling.Descending.budget_wordStep`: a
  move of the pebble game on words, with readiness by a child map and a pebble bound depending on
  a parameter.
* `Cslib.Pebbling.Descending.lookup_inSpace`, `Cslib.Pebbling.Descending.budget_lookup`: the
  stored value at an index.
* `Cslib.Pebbling.Descending.erase_inSpace`, `Cslib.Pebbling.Descending.budget_erase`: clearing
  an index.
* `Cslib.Pebbling.Descending.childValues_inSpace`, `Cslib.Pebbling.Descending.budget_childValues`:
  the stored values of the children of an index.
-/

public section

namespace Cslib.Pebbling.Descending

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-! ### The first difference -/

private theorem find?_range_succ (n : ℕ) (p : ℕ → Bool) :
    (List.range (n + 1)).find? p =
      if p 0 then some 0 else ((List.range n).find? (p ∘ Nat.succ)).map Nat.succ := by
  rw [List.range_succ_eq_map, List.find?_cons, List.find?_map]
  cases p 0 <;> rfl

private theorem diffIndex_nil (v : List Bool) : diffIndex [] v = 0 := rfl

/-- Peeling a common first letter shifts the first difference by one. -/
private theorem diffIndex_cons (a : Bool) (u v : List Bool) :
    diffIndex (a :: u) v =
      if a = v.headD false then diffIndex u v.tail + 1 else 0 := by
  unfold diffIndex
  rw [List.length_cons, find?_range_succ]
  have hsucc : ((fun i => (a :: u).getD i false != v.getD i false) ∘ Nat.succ) =
      fun i => u.getD i false != v.tail.getD i false := by
    funext i
    cases v <;> simp
  have h0 : ((a :: u).getD 0 false != v.getD 0 false) = !decide (a = v.headD false) := by
    cases v <;> cases a <;> simp
  rw [hsucc, h0]
  by_cases ha : a = v.headD false
  · simp only [ha, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases (List.range u.length).find? fun i => u.getD i false != v.tail.getD i false <;> rfl
  · simp only [ha, decide_false, Bool.not_false, ↓reduceIte, Option.getD_some]

/-- One letter of the scan for the first difference: the rest of the second word, the position
reached, and whether a difference was found. -/
private def diffStep (s : List Bool × ℕ × Bool) (a : Bool) : List Bool × ℕ × Bool :=
  if s.2.2 then s
  else if a == s.1.headD false then (s.1.tail, s.2.1 + 1, false)
  else (s.1, s.2.1, true)

private theorem foldl_diffStep_done (u v : List Bool) (k : ℕ) :
    u.foldl diffStep (v, k, true) = (v, k, true) := by
  induction u with
  | nil => rfl
  | cons a u ih => exact ih

private theorem foldl_diffStep (u v : List Bool) (k : ℕ) :
    (u.foldl diffStep (v, k, false)).2.1 = k + diffIndex u v := by
  induction u generalizing v k with
  | nil => rfl
  | cons a u ih =>
    rw [List.foldl_cons, diffIndex_cons]
    by_cases ha : a = v.headD false
    · have hs : diffStep (v, k, false) a = (v.tail, k + 1, false) := by
        simp only [diffStep, Bool.false_eq_true, ↓reduceIte, ha, beq_self_eq_true]
      rw [hs, ih]
      simp only [ha, ↓reduceIte]
      omega
    · have hb : (a == v.headD false) = false := by simpa using ha
      have hs : diffStep (v, k, false) a = (v, k, true) := by
        simp only [diffStep, Bool.false_eq_true, ↓reduceIte, hb]
      rw [hs, foldl_diffStep_done]
      simp only [ha, ↓reduceIte, Nat.add_zero]

private theorem foldl_diffStep_le (u v : List Bool) (k : ℕ) (b : Bool) :
    (u.foldl diffStep (v, k, b)).1.length ≤ v.length ∧
      (u.foldl diffStep (v, k, b)).2.1 ≤ k + u.length := by
  induction u generalizing v k b with
  | nil => simp
  | cons a u ih =>
    rw [List.foldl_cons]
    have hs : (diffStep (v, k, b) a).1.length ≤ v.length ∧
        (diffStep (v, k, b) a).2.1 ≤ k + 1 := by
      unfold diffStep
      split_ifs <;> simp
    generalize diffStep (v, k, b) a = s at hs ⊢
    obtain ⟨v', k', b'⟩ := s
    obtain ⟨h₁, h₂⟩ := ih v' k' b'
    simp only [List.length_cons] at hs ⊢
    exact ⟨h₁.trans hs.1, by omega⟩

/-- **The first difference of two words**, in space linear in the words. -/
theorem diffIndex_inSpace :
    ComputableInSpace (fun p : List Bool × List Bool => diffIndex p.1 p.2)
      (encPair encBits encBits) encNat fun p => (encPair encBits encBits p).length := by
  let encS := encPair encBits (encPair encNat encBool)
  have hid : ComputableInSpace (fun q : (List Bool × ℕ × Bool) × Bool => q) (encPair encS encBool)
      (encPair encS encBool) fun q => (encPair encS encBool q).length :=
    (budget_prod (fst _ _) (snd _ _)).of_enc_eq fun _ => rfl
  have hs := fst' hid
  have ha := snd' hid
  have hw := fst' hs
  have hk := fst' (snd' hs)
  have hdone := snd' (snd' hs)
  have hhead : ComputableInSpace (fun w : List Bool => w.headD false) encBits encBool
      fun w => (encBits w).length := of_inO (.of_linear (ListEncoding.headD false))
  have htail : ComputableInSpace List.tail encBits encBits fun w => (encBits w).length :=
    of_inO (.of_linear (ListEncoding.tail encBool))
  have hbeq : ComputableInSpace (fun q : (List Bool × ℕ × Bool) × Bool => q.2 == q.1.1.headD false)
      (encPair encS encBool) encBool fun q => (encPair encS encBool q).length :=
    budget_finite (fun c : Bool × Bool => c.1 == c.2) (budget_prod ha (budget_comp_linear hhead hw))
  have hstep : ComputableInSpace (fun q : (List Bool × ℕ × Bool) × Bool => diffStep q.1 q.2)
      (encPair encS encBool) encS fun q => (encPair encS encBool q).length :=
    (budget_ite hdone hs (budget_ite hbeq
      (budget_prod (budget_comp_linear htail hw)
        (budget_prod (budget_natSucc hk) (budget_const false (.refl _))))
      (budget_prod hw (budget_prod hk (budget_const true (.refl _)))))).of_enc_eq fun _ => rfl
  have hstate (p : List Bool × List Bool) (i : ℕ) :
      (encS ((p.1.take i).foldl diffStep (p.2, 0, false))).length ≤
        4 * (p.1.length + p.2.length) + 8 := by
    obtain ⟨h₁, h₂⟩ := foldl_diffStep_le (p.1.take i) p.2 0 false
    have h₃ := length_encNat_le_self ((p.1.take i).foldl diffStep (p.2, 0, false)).2.1
    have h₄ : (p.1.take i).length ≤ p.1.length := by simp
    simp only [encS, length_encPair, encBits_apply]
    have : (encBool ((p.1.take i).foldl diffStep (p.2, 0, false)).2.2).length ≤ 1 := by
      cases ((p.1.take i).foldl diffStep (p.2, 0, false)).2.2 <;> decide
    omega
  have hfold := foldl (encA := encBool) (encL := encBits) (encB := encS) (fst encBits encBits)
    (budget_prod (snd encBits encBits) (budget_const (0, false) (.refl _))) hstep
    (Q := fun p => 8 * (p.1.length + p.2.length) + 20)
    (B := fun p => 4 * (p.1.length + p.2.length) + 8)
    (fun p i hi => by
      have := hstate p i
      simp only [length_encPair] at this ⊢
      have : (encBool (p.1[i])).length ≤ 1 := by cases p.1[i] <;> decide
      omega)
    (fun p i _ => hstate p i)
  refine (fst' (snd' hfold)).weaken (.of_le_linear 32 32 fun p => ?_) |>.of_enc_eq fun p => ?_
  · simp only [length_encPair, encBits_apply]
    omega
  · rw [foldl_diffStep, zero_add]

variable {α π : Type} {encIn : α ↪ List Bool} {encP : π ↪ List Bool} {Bs : α → ℕ} {d : ℕ}

/-- The first difference of two words computed within a budget, within the budget. -/
theorem budget_diffIndex {u v : α → List Bool} (hu : ComputableInSpace u encIn encBits Bs)
    (hv : ComputableInSpace v encIn encBits Bs) :
    ComputableInSpace (fun x => diffIndex (u x) (v x)) encIn encNat Bs :=
  budget_comp_linear diffIndex_inSpace (budget_prod hu hv)

/-- The letter of the first word at the first difference, within the budget. -/
theorem budget_getD_diffIndex {u v : α → List Bool} (hu : ComputableInSpace u encIn encBits Bs)
    (hv : ComputableInSpace v encIn encBits Bs) :
    ComputableInSpace (fun x => (u x).getD (diffIndex (u x) (v x)) false) encIn encBool Bs :=
  budget_comp_linear (bitsGetD false) (budget_prod hu (budget_diffIndex hu hv))

/-! ### Readiness -/

private theorem budget_zero_or_all {i : α → ℕ} {f : α → Fin d → Bool}
    (hi : ComputableInSpace i encIn encNat Bs)
    (hf : ∀ a, ComputableInSpace (fun x => f x a) encIn encBool Bs) (l : List (Fin d)) :
    ComputableInSpace (fun x => decide (i x = 0) || l.all (f x)) encIn encBool Bs := by
  induction l with
  | nil => simpa using budget_finite (encC := encBool) (fun _ : Bool => true) (budget_natIsZero hi)
  | cons a l ih =>
    refine (budget_finite (encC := encBool) (fun c : Bool × Bool × Bool => c.1 || (c.2.1 && c.2.2))
      (budget_prod (budget_natIsZero hi) (budget_prod (hf a) ih))).of_enc_eq fun x => ?_
    by_cases h : i x = 0 <;> simp [h]

/-- **Readiness of an index**, for a child map depending on a parameter, within a budget that
computes each child. -/
theorem budget_ready {child : π → ℕ → Fin d → ℕ} {par : α → π} {w : α → List Bool} {i : α → ℕ}
    (hw : ComputableInSpace w encIn encBits Bs) (hi : ComputableInSpace i encIn encNat Bs)
    (hchild : ∀ a, ComputableInSpace (fun x => child (par x) (i x) a) encIn encNat Bs) :
    ComputableInSpace (fun x => ready (child (par x)) (w x) (i x)) encIn encBool Bs := by
  refine (budget_zero_or_all hi (fun a => budget_comp_linear (bitsGetD false)
    (budget_prod hw (hchild a))) (List.finRange d)).of_enc_eq (encC := encBool) fun x => ?_
  by_cases h : i x = 0 <;> simp [ready, h]

/-- **Readiness in the space of its arguments and of the children**: the space is linear in the
encoded parameter, word and index, plus the space `Sc` of computing a child. -/
theorem ready_inSpace {child : π → ℕ → Fin d → ℕ} {Sc : π × ℕ → ℕ}
    (hchild : ∀ a, ComputableInSpace (fun (p, i) => child p i a) (encPair encP encNat) encNat Sc) :
    ComputableInSpace (fun (p, w, i) => ready (child p) w i)
      (encPair encP (encPair encBits encNat)) encBool
      fun (p, w, i) => (encPair encP (encPair encBits encNat) (p, w, i)).length + Sc (p, i) := by
  let E := encPair encP (encPair encBits encNat)
  have hid : ComputableInSpace (fun q : π × List Bool × ℕ => q) E E
      fun (p, w, i) => (E (p, w, i)).length + Sc (p, i) :=
    ((budget_prod (fst _ _) (snd _ _)).of_enc_eq fun _ => rfl).mono_le
      fun _ => Nat.le_add_right _ _
  have hpi : ComputableInSpace (fun q : π × List Bool × ℕ => (q.1, q.2.2)) E (encPair encP encNat)
      fun (p, w, i) => (E (p, w, i)).length + Sc (p, i) := budget_prod (fst' hid) (snd' (snd' hid))
  exact budget_ready (fst' (snd' hid)) (snd' (snd' hid)) fun a =>
    budget_comp (hchild a) hpi (.of_le fun _ => Nat.le_add_left _ _)

/-! ### Counting pebbles -/

private def countStep (n : ℕ) (b : Bool) : ℕ := if b then n + 1 else n

private theorem foldl_countStep (u : List Bool) (n : ℕ) :
    u.foldl countStep n = n + u.count true := by
  induction u generalizing n with
  | nil => rfl
  | cons b u ih =>
    rw [List.foldl_cons, ih, List.count_cons]
    cases b
    · simp [countStep]
    · simp [countStep]
      omega

private theorem countTrue_inSpace :
    ComputableInSpace (fun u : List Bool => u.count true) encBits encNat
      fun u => (encBits u).length := by
  have hid : ComputableInSpace (fun q : ℕ × Bool => q) (encPair encNat encBool)
      (encPair encNat encBool) fun q => (encPair encNat encBool q).length :=
    (budget_prod (fst _ _) (snd _ _)).of_enc_eq fun _ => rfl
  have hstep : ComputableInSpace (fun q : ℕ × Bool => countStep q.1 q.2) (encPair encNat encBool)
      encNat fun q => (encPair encNat encBool q).length :=
    (budget_ite (snd' hid) (budget_natSucc (fst' hid)) (fst' hid)).of_enc_eq fun _ => rfl
  have hstate (u : List Bool) (i : ℕ) :
      (encNat ((u.take i).foldl countStep 0)).length ≤ u.length := by
    rw [foldl_countStep, zero_add]
    have h₁ := length_encNat_le_self ((u.take i).count true)
    have h₂ := List.count_le_length (a := true) (l := u.take i)
    have h₃ : (u.take i).length ≤ u.length := by simp
    omega
  have hfold := foldl (encA := encBool) (encL := encBits) (encB := encNat)
    (of_inO (ComputableInO.of_eq (f := fun u : List Bool => u) (encIn := encBits)
      (encMid := encBits) fun _ => rfl))
    (const (encB := encNat) 0) hstep
    (Q := fun u => 2 * u.length + 3) (B := fun u => u.length)
    (fun u i hi => by
      have := hstate u i
      simp only [length_encPair]
      have : (encBool (u[i])).length ≤ 1 := by cases u[i] <;> decide
      omega)
    (fun u i _ => hstate u i)
  refine hfold.weaken (.of_le_linear 8 8 fun u => ?_) |>.of_enc_eq fun u => ?_
  · simp only [encBits_apply]
    omega
  · rw [foldl_countStep, zero_add]

/-! ### Moves -/

/-- Flipping bit `i` of `u` gives `v` exactly when `i` is the first difference of the two words,
`v` reaches past it and they agree after it. -/
private theorem set_eq_iff_drop_eq {u v : List Bool} {i : ℕ} (hi : i < u.length)
    (hlt : ∀ j < i, u.getD j false = v.getD j false) (hne : u.getD i false ≠ v.getD i false) :
    v = u.set i (!u.getD i false) ↔ u.drop (i + 1) = v.drop (i + 1) ∧ i < v.length := by
  constructor
  · intro h
    subst h
    exact ⟨(List.drop_set_of_lt (Nat.lt_succ_self i)).symm, by simpa using hi⟩
  · rintro ⟨hdrop, hiv⟩
    refine List.ext_getElem? fun n => ?_
    rcases lt_trichotomy n i with hn | rfl | hn
    · rw [List.getElem?_set_ne (by omega)]
      have := hlt n hn
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simpa using this.symm
    · rw [List.getElem?_set_self hi, List.getElem?_eq_getElem hiv]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiv] at hne
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      simp only [Option.getD_some] at hne ⊢
      cases h₁ : u[n] <;> cases h₂ : v[n] <;> simp_all
    · rw [List.getElem?_set_ne (by omega)]
      have := congrArg (·[n - (i + 1)]?) hdrop
      simp only [List.getElem?_drop] at this
      rw [show i + 1 + (n - (i + 1)) = n by omega] at this
      exact this.symm

/-- Below the first difference the words agree; at it, within the first word, they differ. -/
private theorem diffIndex_spec {u v : List Bool} (h : diffIndex u v < u.length) :
    (∀ j < diffIndex u v, u.getD j false = v.getD j false) ∧
      u.getD (diffIndex u v) false ≠ v.getD (diffIndex u v) false := by
  unfold diffIndex at h ⊢
  cases hf : (List.range u.length).find? fun i => u.getD i false != v.getD i false with
  | none => rw [hf] at h; exact absurd h (lt_irrefl _)
  | some j =>
    rw [Option.getD_some]
    obtain ⟨h₁, -, h₂⟩ := List.find?_range_eq_some.1 hf
    exact ⟨fun k hk => by simpa using h₂ k hk, by simpa using h₁⟩

/-- **A move tests only the first difference**: after it the words agree, and the second word
has at most `s` bits set. -/
private theorem wordStep_eq_diffIndex (rd : List Bool → ℕ → Bool) (s : ℕ) (u v : List Bool) :
    wordStep rd s u v =
      (decide (diffIndex u v < u.length) && (u.getD (diffIndex u v) false || rd u (diffIndex u v))
        && decide (diffIndex u v < v.length)
        && decide (u.drop (diffIndex u v + 1) = v.drop (diffIndex u v + 1))
        && decide (v.count true ≤ s)) := by
  rw [Bool.eq_iff_iff]
  simp only [wordStep, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, ⟨hrd, hv⟩, hs⟩
    have hd : diffIndex u v = j := by
      rw [hv]
      exact diffIndex_set hj (by cases u.getD j false <;> simp)
    subst hd
    obtain ⟨hlt, hne⟩ := diffIndex_spec hj
    exact ⟨⟨⟨⟨hj, hrd⟩, ((set_eq_iff_drop_eq hj hlt hne).1 hv).2⟩,
      ((set_eq_iff_drop_eq hj hlt hne).1 hv).1⟩, hs⟩
  · rintro ⟨⟨⟨⟨hi, hrd⟩, hiv⟩, hdrop⟩, hs⟩
    obtain ⟨hlt, hne⟩ := diffIndex_spec hi
    exact ⟨diffIndex u v, hi, ⟨hrd, (set_eq_iff_drop_eq hi hlt hne).2 ⟨hdrop, hiv⟩⟩, hs⟩

private theorem not_isEmpty_drop (l : List Bool) (i : ℕ) :
    (!(l.drop i).isEmpty) = decide (i < l.length) := by
  rw [Bool.eq_iff_iff]
  simp [List.drop_eq_nil_iff]

/-- **A move of the pebble game on words**, for a child map and a pebble bound depending on a
parameter, within a budget that computes the children at the first difference. -/
theorem budget_wordStep {child : π → ℕ → Fin d → ℕ} {s : π → ℕ} {par : α → π}
    {u v : α → List Bool} (hu : ComputableInSpace u encIn encBits Bs)
    (hv : ComputableInSpace v encIn encBits Bs)
    (hchild : ∀ a, ComputableInSpace (fun x => child (par x) (diffIndex (u x) (v x)) a) encIn
      encNat Bs)
    (hs : ComputableInSpace (fun x => s (par x)) encIn encNat Bs) :
    ComputableInSpace (fun x => wordStep (ready (child (par x))) (s (par x)) (u x) (v x)) encIn
      encBool Bs := by
  have hi := budget_diffIndex hu hv
  have hempty : ComputableInSpace (fun w : List Bool => w.isEmpty) encBits encBool
      fun w => (encBits w).length := of_inO (.of_linear (ListEncoding.isEmpty encBool))
  have hinU := budget_comp_linear hempty (budget_comp_linear bitsDrop (budget_prod hu hi))
  have hinV := budget_comp_linear hempty (budget_comp_linear bitsDrop (budget_prod hv hi))
  have hmove := budget_finite (encC := encBool) (fun c : Bool × Bool => c.1 || c.2)
    (budget_prod (budget_getD_diffIndex hu hv) (budget_ready hu hi hchild))
  have hi₁ := budget_natSucc hi
  have heq : ComputableInSpace (fun x => decide ((u x).drop (diffIndex (u x) (v x) + 1) =
      (v x).drop (diffIndex (u x) (v x) + 1))) encIn encBool Bs :=
    budget_comp_lin (of_inO ComputableInO.eqWords) (.of_le_linear 1 1 fun _ => by
      simp only [length_encPair, encBits_apply]; omega)
      (budget_prod (budget_comp_linear bitsDrop (budget_prod hu hi₁))
        (budget_comp_linear bitsDrop (budget_prod hv hi₁)))
  have hcount := budget_natLt (budget_comp_linear countTrue_inSpace hv) (budget_natSucc hs)
  refine (budget_finite (encC := encBool)
    (fun c : Bool × Bool × Bool × Bool × Bool =>
      !c.1 && c.2.1 && !c.2.2.1 && c.2.2.2.1 && c.2.2.2.2)
    (budget_prod hinU (budget_prod hmove (budget_prod hinV (budget_prod heq hcount))))).of_enc_eq
    fun x => ?_
  simp only [wordStep_eq_diffIndex, not_isEmpty_drop, Nat.lt_succ_iff]

/-- **A move of the pebble game on words, as an edge test in space**: the space is linear in the
encoded parameter and words, plus the space `Sc` of computing a child of the first difference and
the space `Ss` of computing the pebble bound. -/
theorem wordStep_inSpace {child : π → ℕ → Fin d → ℕ} {s : π → ℕ} {Sc : π × ℕ → ℕ} {Ss : π → ℕ}
    (hchild : ∀ a, ComputableInSpace (fun (p, i) => child p i a) (encPair encP encNat) encNat Sc)
    (hs : ComputableInSpace s encP encNat Ss) :
    ComputableInSpace (fun (p, u, v) => wordStep (ready (child p)) (s p) u v)
      (encPair encP (encPair encBits encBits)) encBool
      fun (p, u, v) => (encPair encP (encPair encBits encBits) (p, u, v)).length +
        Sc (p, diffIndex u v) + Ss p := by
  let E := encPair encP (encPair encBits encBits)
  have hid : ComputableInSpace (fun q : π × List Bool × List Bool => q) E E
      fun (p, u, v) => (E (p, u, v)).length + Sc (p, diffIndex u v) + Ss p :=
    ((budget_prod (fst _ _) (snd _ _)).of_enc_eq fun _ => rfl).mono_le
      fun _ => Nat.le_add_right_of_le (Nat.le_add_right _ _)
  have hp := fst' hid
  have hu := fst' (snd' hid)
  have hv := snd' (snd' hid)
  have hpi := budget_prod hp (budget_diffIndex hu hv)
  exact budget_wordStep (child := child) (s := s) (par := Prod.fst) hu hv
    (fun a => budget_comp (hchild a) hpi
      (.of_le fun _ => Nat.le_add_right_of_le (Nat.le_add_left _ _)))
    (budget_comp hs hp (.of_le fun _ => Nat.le_add_left _ _))

/-! ### Tables of stored values -/

/-- The encoding of a table of stored values: a list of binary indices with their words. -/
abbrev encTable : List (ℕ × List Bool) ↪ List Bool := encList (encPair encNat encBits)

private theorem lookup_eq_find? (t : List (ℕ × List Bool)) (i : ℕ) :
    (t.lookup i).getD [] = ((t.find? fun q => decide (i = q.1)).getD (0, [])).2 := by
  induction t with
  | nil => rfl
  | cons q t ih =>
    obtain ⟨j, x⟩ := q
    by_cases h : i = j
    · subst h
      simp [List.lookup]
    · have hb : (i == j) = false := by simpa using h
      simp [List.lookup, hb, h, ih]

/-- A scan of a table with a test on its entries and an index takes space linear in both. -/
private theorem scan_le (q : List (ℕ × List Bool) × ℕ) :
    (encPair encTable encNat q).length + (encPair encTable encNat q).length +
        (encPair encTable encNat q).length + (encNat q.2).length + (encTable q.1).length +
        listMax (fun a => (encPair encNat (encPair encNat encBits) (q.2, a)).length) q.1 ≤
      8 * (encPair encTable encNat q).length + 8 := by
  have h : listMax (fun a => (encPair encNat (encPair encNat encBits) (q.2, a)).length) q.1 ≤
      2 * (encNat q.2).length + 1 + (encTable q.1).length :=
    listMax_le fun a ha => by
      have h₁ : (encPair encNat encBits a).length ≤ (encTable q.1).length :=
        length_le_encList_of_mem _ ha
      have h₂ : (encPair encNat (encPair encNat encBits) (q.2, a)).length =
          2 * (encNat q.2).length + 1 + (encPair encNat encBits a).length := length_encPair _
      change (encPair encNat (encPair encNat encBits) (q.2, a)).length ≤ _
      omega
  have h₂ : (encPair encTable encNat q).length = 2 * (encTable q.1).length + 1 +
      (encNat q.2).length := length_encPair _
  omega

/-- The test of an entry against an index, as `List.lookup` compares. -/
private theorem keyEq_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ × List Bool => decide (q.1 = q.2.1))
      (encPair encNat (encPair encNat encBits)) encBool
      fun q => (encPair encNat (encPair encNat encBits) q).length :=
  budget_natEq (fst _ _) (fst' (snd _ _))

/-- The test of an entry against an index, as `List.filter` in `Descending.tableStep` compares. -/
private theorem keyNe_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ × List Bool => q.2.1 != q.1)
      (encPair encNat (encPair encNat encBits)) encBool
      fun q => (encPair encNat (encPair encNat encBits) q).length :=
  budget_finite (encC := encBool) (fun b : Bool => !b) (budget_natEq (fst' (snd _ _)) (fst _ _))

/-- **The stored value at an index**, or the empty word, in space linear in the table and the
index. -/
theorem lookup_inSpace :
    ComputableInSpace (fun (t, i) => (t.lookup i).getD []) (encPair encTable encNat) encBits
      fun q => (encPair encTable encNat q).length := by
  obtain ⟨_, ht⟩ := keyEq_inSpace.exists_inO
  obtain ⟨_, hi⟩ := (snd encTable encNat).exists_inO
  obtain ⟨_, hl⟩ := (fst encTable encNat).exists_inO
  have hfind := of_inO (ComputableInO.findWith ht hi hl)
  refine (snd' (budget_optionGetD (0, []) hfind)).weaken (.of_le_linear 8 8 scan_le)
    |>.of_enc_eq fun q => ?_
  exact congrArg encBits (lookup_eq_find? q.1 q.2)

/-- **Clearing an index**: the entries of the table at other indices, in space linear in the
table and the index. -/
theorem erase_inSpace :
    ComputableInSpace (fun (t, i) => t.filter fun q => q.1 != i) (encPair encTable encNat) encTable
      fun q => (encPair encTable encNat q).length := by
  obtain ⟨_, ht⟩ := keyNe_inSpace.exists_inO
  obtain ⟨_, hi⟩ := (snd encTable encNat).exists_inO
  obtain ⟨_, hl⟩ := (fst encTable encNat).exists_inO
  refine (of_inO (ComputableInO.filterWith ht hi hl)).weaken (.of_le_linear 8 8 scan_le)
    |>.of_enc_eq fun q => ?_
  rfl

/-- The stored value at an index computed within a budget, within the budget. -/
theorem budget_lookup {t : α → List (ℕ × List Bool)} {i : α → ℕ}
    (ht : ComputableInSpace t encIn encTable Bs) (hi : ComputableInSpace i encIn encNat Bs) :
    ComputableInSpace (fun x => ((t x).lookup (i x)).getD []) encIn encBits Bs :=
  budget_comp_linear lookup_inSpace (budget_prod ht hi)

/-- Clearing an index computed within a budget, within the budget. -/
theorem budget_erase {t : α → List (ℕ × List Bool)} {i : α → ℕ}
    (ht : ComputableInSpace t encIn encTable Bs) (hi : ComputableInSpace i encIn encNat Bs) :
    ComputableInSpace (fun x => (t x).filter fun q => q.1 != i x) encIn encTable Bs :=
  budget_comp_linear erase_inSpace (budget_prod ht hi)

private theorem budget_map_lookup {t : α → List (ℕ × List Bool)} {k : α → Fin d → ℕ}
    (ht : ComputableInSpace t encIn encTable Bs)
    (hk : ∀ a, ComputableInSpace (fun x => k x a) encIn encNat Bs) (l : List (Fin d)) :
    ComputableInSpace (fun x => l.map fun a => ((t x).lookup (k x a)).getD []) encIn
      (encList encBits) Bs := by
  induction l with
  | nil => exact budget_finite (fun _ : Bool => []) (budget_isEmpty ht)
  | cons a l ih => exact budget_cons (budget_lookup ht (hk a)) ih

/-- **The stored values of the children of an index**, within a budget that computes the
children. -/
theorem budget_childValues {child : π → ℕ → Fin d → ℕ} {par : α → π}
    {t : α → List (ℕ × List Bool)} {i : α → ℕ} (ht : ComputableInSpace t encIn encTable Bs)
    (hchild : ∀ a, ComputableInSpace (fun x => child (par x) (i x) a) encIn encNat Bs) :
    ComputableInSpace
      (fun x => (List.finRange d).map fun a => ((t x).lookup (child (par x) (i x) a)).getD [])
      encIn (encList encBits) Bs :=
  budget_map_lookup ht hchild _

/-- **The stored values of the children of an index, in space**: linear in the encoded parameter,
table and index, plus the space `Sc` of computing a child. -/
theorem childValues_inSpace {child : π → ℕ → Fin d → ℕ} {Sc : π × ℕ → ℕ}
    (hchild : ∀ a, ComputableInSpace (fun (p, i) => child p i a) (encPair encP encNat) encNat Sc) :
    ComputableInSpace
      (fun (p, t, i) => (List.finRange d).map fun a => (t.lookup (child p i a)).getD [])
      (encPair encP (encPair encTable encNat)) (encList encBits)
      fun (p, t, i) => (encPair encP (encPair encTable encNat) (p, t, i)).length + Sc (p, i) := by
  let E := encPair encP (encPair encTable encNat)
  have hid : ComputableInSpace (fun q : π × List (ℕ × List Bool) × ℕ => q) E E
      fun (p, t, i) => (E (p, t, i)).length + Sc (p, i) :=
    ((budget_prod (fst _ _) (snd _ _)).of_enc_eq fun _ => rfl).mono_le
      fun _ => Nat.le_add_right _ _
  have hpi : ComputableInSpace (fun q : π × List (ℕ × List Bool) × ℕ => (q.1, q.2.2)) E
      (encPair encP encNat) fun (p, t, i) => (E (p, t, i)).length + Sc (p, i) :=
    budget_prod (fst' hid) (snd' (snd' hid))
  exact budget_childValues (fst' (snd' hid)) fun a =>
    budget_comp (hchild a) hpi (.of_le fun _ => Nat.le_add_left _ _)

end Cslib.Pebbling.Descending
