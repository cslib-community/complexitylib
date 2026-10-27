/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger, Anton Kovsharov
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
import Mathlib.Tactic.Linarith

/-! # Size bounds for readable list encodings

The pure interface and instances are moved unchanged from the quantitative fold provider.
The framed-list upper bound retains its original statement and proof from the list provider.
-/

namespace Turing.MultiTapeTM

/-- A list encoding whose encoded lists are at least as long as their elements, their suffixes and
their lengths. -/
public class SizedListEncoding {α : Type*} (encA : α ↪ List Bool) (encL : List α ↪ List Bool) :
    Prop where
  length_le (l : List α) : l.length ≤ (encL l).length
  length_elem_le (l : List α) : ∀ a ∈ l, (encA a).length ≤ (encL l).length
  length_drop_le (l : List α) (i : ℕ) : (encL (l.drop i)).length ≤ (encL l).length

public instance {α : Type*} (enc : α ↪ List Bool) : SizedListEncoding enc (encList enc) where
  length_le l := by induction l <;> grind [encList_cons, length_frame]
  length_elem_le l a ha := by induction l <;> grind [encList_cons, length_frame]
  length_drop_le l i := ((List.drop_sublist i l).flatMap (frame ∘ enc)).length_le

public instance : SizedListEncoding encBool encBits where
  length_le l := by simp
  length_elem_le l a ha := by
    simp only [encBool_apply, List.length_singleton, encBits_apply]
    exact List.length_pos_of_mem ha
  length_drop_le l i := by simp

variable {α : Type}

/-- A list of elements of bounded size has bounded size. -/
public lemma length_encList_le (enc : α ↪ List Bool) (l : List α) {b : ℕ}
    (h : ∀ a ∈ l, (enc a).length ≤ b) : (encList enc l).length ≤ l.length * (2 * b + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h₁ := h a (List.mem_cons_self ..)
    have h₂ := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    simp only [encList_cons, List.length_append, length_frame, List.length_cons]
    nlinarith

/-- Sublists do not increase framed list encoding length. -/
public lemma length_encList_sublist {α : Type*} (enc : α ↪ List Bool) {l₁ l₂ : List α}
    (h : List.Sublist l₁ l₂) : (encList enc l₁).length ≤ (encList enc l₂).length :=
  (h.flatMap (frame ∘ enc)).length_le

/-- Elementwise encoding-length bounds lift across `List.map` on framed list encodings. -/
public lemma length_encList_map_le {α β : Type*} (ea : α ↪ List Bool) (eb : β ↪ List Bool)
    {f : α → β} {l : List α} (hf : ∀ x ∈ l, (eb (f x)).length ≤ (ea x).length) :
    (encList eb (l.map f)).length ≤ (encList ea l).length := by
  induction l with
  | nil => exact le_rfl
  | cons a ls ih =>
    have ha := hf a List.mem_cons_self
    have hls := ih fun x hx => hf x (List.mem_cons_of_mem a hx)
    simp only [List.map_cons, encList_cons, List.length_append, length_frame]; omega

end Turing.MultiTapeTM
