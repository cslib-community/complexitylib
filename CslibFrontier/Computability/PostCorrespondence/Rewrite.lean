/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PostCorrespondence.Basic
public import Mathlib.Logic.Relation

/-!
# String rewriting and the modified correspondence problem

A set `R` of dominoes is read as a semi-Thue system: one step replaces an occurrence of the top
word of a domino of `R` by its bottom word. With the copy dominoes `a / a`, an MPCP instance with
start domino `ε / w` simulates rewriting from `w` to the empty word: a match is a sequence of
rewriting steps, each written below the word it rewrites. This is the mechanism of Sipser's
computation-history dominoes [Sipser2013, proof of Theorem 5.15], with the rule set of the
simulated machine as `R`.

Completeness needs nothing beyond the copy dominoes. Soundness needs an end marker `e` that
separates successive words: every reachable word other than `ε` ends with its only `e`, and `e`
occurs in the top of a domino only as its last letter. Then each block of the match up to an
occurrence of `e` rewrites the current word to the next one.

## Main definitions

* `Cslib.PostCorrespondence.Rewrites`: one rewriting step.
* `Cslib.PostCorrespondence.copy`: the copy domino of a letter.

## Main results

* `Cslib.PostCorrespondence.mSolvable_of_reflTransGen`: completeness, from a rewriting of `w` to
  `ε` to a match.
* `Cslib.PostCorrespondence.reflTransGen_of_mSolvable`: soundness, from a match to a rewriting.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.PostCorrespondence

open Relation

variable {α : Type*}

/-- One rewriting step with a set `R` of dominoes, read as a semi-Thue system: an occurrence of the
top word of a domino of `R` is replaced by its bottom word. -/
@[expose] def Rewrites (R : Domino α → Prop) (u v : List α) : Prop :=
  ∃ p d s, R d ∧ u = p ++ d.top ++ s ∧ v = p ++ d.bottom ++ s

theorem Rewrites.append_left {R : Domino α → Prop} {u v : List α} (h : Rewrites R u v)
    (w : List α) : Rewrites R (w ++ u) (w ++ v) := by
  obtain ⟨p, d, s, hd, rfl, rfl⟩ := h
  exact ⟨w ++ p, d, s, hd, by simp only [List.append_assoc],
    by simp only [List.append_assoc]⟩

theorem Rewrites.append_right {R : Domino α → Prop} {u v : List α} (h : Rewrites R u v)
    (w : List α) : Rewrites R (u ++ w) (v ++ w) := by
  obtain ⟨p, d, s, hd, rfl, rfl⟩ := h
  exact ⟨p, d, s ++ w, hd, by simp only [List.append_assoc],
    by simp only [List.append_assoc]⟩

theorem reflTransGen_rewrites_append_left {R : Domino α → Prop} {u v : List α}
    (h : ReflTransGen (Rewrites R) u v) (w : List α) :
    ReflTransGen (Rewrites R) (w ++ u) (w ++ v) :=
  ReflTransGen.lift (w ++ ·) (fun _ _ (h : Rewrites R _ _) => h.append_left w) _ _ h

theorem reflTransGen_rewrites_append_right {R : Domino α → Prop} {u v : List α}
    (h : ReflTransGen (Rewrites R) u v) (w : List α) :
    ReflTransGen (Rewrites R) (u ++ w) (v ++ w) :=
  ReflTransGen.lift (· ++ w) (fun _ _ (h : Rewrites R _ _) => h.append_right w) _ _ h

/-- A sequence of dominoes, each of which is in `R` or has equal top and bottom, rewrites its top
concatenation to its bottom concatenation. -/
theorem reflTransGen_tops_bottoms {R : Domino α → Prop} :
    ∀ {σ : List (Domino α)}, (∀ d ∈ σ, R d ∨ d.top = d.bottom) →
      ReflTransGen (Rewrites R) (tops σ) (bottoms σ)
  | [], _ => ReflTransGen.refl
  | d :: σ, h => by
    rw [tops_cons, bottoms_cons]
    have ih := reflTransGen_tops_bottoms fun e he => h e (List.mem_cons_of_mem d he)
    refine ReflTransGen.trans ?_ (reflTransGen_rewrites_append_left ih d.bottom)
    rcases h d List.mem_cons_self with hd | hd
    · exact ReflTransGen.single ⟨[], d, tops σ, hd, rfl, rfl⟩
    · rw [hd]

/-- The copy domino of a letter. -/
@[expose] def copy (a : α) : Domino α := ⟨[a], [a]⟩

@[simp] theorem copy_top (a : α) : (copy a).top = [a] := rfl
@[simp] theorem copy_bottom (a : α) : (copy a).bottom = [a] := rfl

theorem tops_map_copy (w : List α) : tops (w.map copy) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.map_cons, tops_cons, ih]; rfl

theorem bottoms_map_copy (w : List α) : bottoms (w.map copy) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.map_cons, bottoms_cons, ih]; rfl

/-- Every rewriting step is realized by a sequence of copy dominoes and one domino of `R`. -/
theorem Rewrites.exists_dominoes {R : Domino α → Prop} {u v : List α} (h : Rewrites R u v) :
    ∃ σ : List (Domino α), (∀ d ∈ σ, R d ∨ ∃ a, d = copy a) ∧ tops σ = u ∧ bottoms σ = v := by
  obtain ⟨p, d, s, hd, rfl, rfl⟩ := h
  refine ⟨p.map copy ++ d :: s.map copy, fun e he => ?_, ?_, ?_⟩
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp he
      exact Or.inr ⟨a, rfl⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl hd
      · obtain ⟨a, -, rfl⟩ := List.mem_map.mp he
        exact Or.inr ⟨a, rfl⟩
  · rw [tops_append, tops_cons, tops_map_copy, tops_map_copy, List.append_assoc]
  · rw [bottoms_append, bottoms_cons, bottoms_map_copy, bottoms_map_copy, List.append_assoc]

/-- Completeness of the semi-Thue encoding: if `w` rewrites to the empty word, the MPCP instance
with start domino `ε / w` is solvable, using the dominoes of `R` and the copy dominoes. -/
theorem mSolvable_of_reflTransGen {R : Domino α → Prop} {D : List (Domino α)}
    (hR : ∀ d, R d → d ∈ D) (hcopy : ∀ a, copy a ∈ D) {w : List α}
    (h : ReflTransGen (Rewrites R) w []) : (MInstance.mk ⟨[], w⟩ D).Solvable := by
  suffices ∀ u, ReflTransGen (Rewrites R) u [] →
      ∃ σ : List (Domino α), (∀ d ∈ σ, d ∈ D) ∧ tops σ = u ++ bottoms σ by
    obtain ⟨σ, hσ, heq⟩ := this w h
    exact ⟨σ, hσ, by rw [List.nil_append, heq]⟩
  intro u hu
  induction hu using ReflTransGen.head_induction_on with
  | refl => exact ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | head hstep _ ih =>
    obtain ⟨σ, hσ, heq⟩ := ih
    obtain ⟨τ, hτ, htop, hbot⟩ := hstep.exists_dominoes
    refine ⟨τ ++ σ, fun d hd => ?_, ?_⟩
    · rcases List.mem_append.mp hd with hd | hd
      · rcases hτ d hd with hd | ⟨a, rfl⟩
        · exact hR d hd
        · exact hcopy a
      · exact hσ d hd
    · rw [tops_append, bottoms_append, htop, heq, hbot]

/-- Soundness of the semi-Thue encoding. Suppose a letter `e` occurs in the top word of a domino
only as its last letter, and every word reachable from `w` is empty or ends with its only `e`.
Then a match of the MPCP instance with start domino `ε / w` yields a rewriting of `w` to the
empty word. -/
theorem reflTransGen_of_mSolvable {R : Domino α → Prop} {D : List (Domino α)}
    (hD : ∀ d ∈ D, R d ∨ d.top = d.bottom) {e : α}
    (he : ∀ d ∈ D, e ∈ d.top → ∃ t, d.top = t ++ [e] ∧ e ∉ t) {w : List α}
    (hw : ∀ u, ReflTransGen (Rewrites R) w u → u = [] ∨ ∃ u', u = u' ++ [e] ∧ e ∉ u')
    (h : (MInstance.mk ⟨[], w⟩ D).Solvable) : ReflTransGen (Rewrites R) w [] := by
  obtain ⟨σ, hσ, heq⟩ := h
  rw [List.nil_append] at heq
  suffices ∀ n (σ : List (Domino α)) u, σ.length = n → (∀ d ∈ σ, d ∈ D) →
      ReflTransGen (Rewrites R) w u → tops σ = u ++ bottoms σ → ReflTransGen (Rewrites R) u [] by
    exact this _ σ w rfl hσ ReflTransGen.refl heq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro σ u hn hσ hu heq
  rcases hw u hu with rfl | ⟨u', rfl, hu'⟩
  · exact ReflTransGen.refl
  have hmem : ∃ d ∈ σ, e ∈ d.top := by
    have : e ∈ tops σ := by rw [heq]; simp
    obtain ⟨d, hd, hed⟩ := List.mem_flatMap.mp this
    exact ⟨d, hd, hed⟩
  obtain ⟨σ₁, d, σ₂, rfl, hed, hσ₁⟩ := exists_eq_append_cons_of_exists_mem hmem
  have hdD : d ∈ D := hσ d (by simp)
  obtain ⟨t, ht, het⟩ := he d hdD hed
  have hnot : e ∉ tops σ₁ ++ t := by
    intro hmem'
    rcases List.mem_append.mp hmem' with hmem' | hmem'
    · obtain ⟨d', hd', hed'⟩ := List.mem_flatMap.mp hmem'
      exact hσ₁ d' hd' hed'
    · exact het hmem'
  have hsplit : (tops σ₁ ++ t) ++ e :: tops σ₂ = u' ++ e :: bottoms (σ₁ ++ d :: σ₂) := by
    have h' := heq
    rw [tops_append, tops_cons, ht] at h'
    simpa only [List.append_assoc, List.singleton_append] using h'
  obtain ⟨h₁, h₂⟩ := (append_cons_inj_of_notMem_prefix hnot hu').mp hsplit
  have hτ : ∀ d' ∈ σ₁ ++ [d], R d' ∨ d'.top = d'.bottom := fun d' hd' =>
    hD d' (hσ d' (by
      rcases List.mem_append.mp hd' with hd' | hd'
      · exact List.mem_append_left _ hd'
      · rw [List.mem_singleton.mp hd']; simp))
  have hstep : ReflTransGen (Rewrites R) (u' ++ [e]) (bottoms (σ₁ ++ [d])) := by
    have := reflTransGen_tops_bottoms hτ
    rwa [tops_append, tops_cons, tops_nil, List.append_nil, ht, ← List.append_assoc, h₁] at this
  refine hstep.trans (ih σ₂.length ?_ σ₂ _ rfl (fun d' hd' => hσ d' (by simp [hd']))
    (hu.trans hstep) ?_)
  · rw [← hn, List.length_append, List.length_cons]
    omega
  · rw [h₂, bottoms_append, bottoms_append, bottoms_cons, bottoms_cons, bottoms_nil,
      List.append_nil, List.append_assoc]

end Cslib.PostCorrespondence
