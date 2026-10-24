/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Basic

/-!
# Recursive van Emde Boas memory representation

A tree occupies a contiguous five-word header followed by its summary and clusters.
An empty record's minimum and maximum cells may contain arbitrary stale words; its presence
flag and static split/child-span fields remain specified. Memory outside the recursive
footprint is unconstrained by this representation.

This is a memory predicate and its frame/update calculus. It does not by itself provide an
initializer, native execution, or an implemented time/space bound. The minimum-excluded
algorithm follows [Demaine2015VanEmdeBoas], whose notes credit Michael Bender; this particular
contiguous record layout is an engineering choice.

## Main definitions

* `splitSize`, `childSpan`, `Header`: the static split/child-span header fields and the five-word
  record predicate allowing stale empty extrema.
* `Rep`: recursive interpretation of actual memory as a functional tree.
* `writeBounds`: the concrete presence/extrema writes.

## Main results

* `rep_frame`: changing memory outside a represented interval preserves it.
* `rep_writeBounds`, `rep_replace_cluster`, `rep_replace_summary`: local representation updates.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.Algorithms.Lean.VanEmdeBoas

/-- Stored split size: zero marks a leaf. -/
def splitSize : ℕ → ℕ
  | 0 => 0
  | d + 1 => universeSize d

/-- Stored size of each recursively allocated child record. -/
def childSpan : ℕ → ℕ
  | 0 => 0
  | d + 1 => span d

/-- A record header; absent extrema are deliberately unconstrained. -/
def Header (d : ℕ) (b : Option (ℕ × ℕ)) (p : ℕ) (mem : ℕ → ℕ) : Prop :=
  mem p = (if b.isSome then 1 else 0) ∧
    (match b with
    | none => True
    | some (m, M) => mem (p + 1) = m ∧ mem (p + 2) = M) ∧
    mem (p + 3) = splitSize d ∧ mem (p + 4) = childSpan d

/-- Recursive, interval-local representation of a functional tree in actual memory. -/
def Rep : {d : ℕ} → Tree d → ℕ → (ℕ → ℕ) → Prop
  | 0, .leaf b, p, mem => Header 0 b p mem
  | d + 1, .node b s c, p, mem => Header (d + 1) b p mem ∧
      Rep s (p + summaryOffset) mem ∧ ∀ i, Rep (c i) (p + clusterOffset d i.val) mem

/-- A represented tree exposes the header of its root, regardless of surrounding memory. -/
theorem Rep.header {d p : ℕ} {t : Tree d} {mem : ℕ → ℕ} (hr : Rep t p mem) :
    Header d t.bounds p mem := by
  cases t with
  | leaf => exact hr
  | node => exact hr.1

/-- The recursive record is large enough to store every universe index as a word offset. -/
theorem universeSize_le_span (d : ℕ) : universeSize d ≤ span d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [universeSize_succ, span_succ]
    have h₁ := Nat.mul_le_mul_left (universeSize d) ih
    have h₂ : universeSize d * span d ≤ (universeSize d + 1) * span d :=
      Nat.mul_le_mul_right (span d) (by omega)
    omega

/-- Every smaller record size is bounded by its parent record size. -/
theorem span_le_succ (d : ℕ) : span d ≤ span (d + 1) := by
  have h := summary_end_le_span d
  dsimp only [summaryOffset] at h
  omega

/-- Every split size is bounded by its record span. -/
theorem splitSize_le_span (d : ℕ) : splitSize d ≤ span d := by
  cases d with
  | zero => decide
  | succ d =>
    dsimp only [splitSize]
    exact Nat.le_trans (universeSize_le_span d) (span_le_succ d)

/-- Every child span is bounded by its parent record span. -/
theorem childSpan_le_span (d : ℕ) : childSpan d ≤ span d := by
  cases d with
  | zero => decide
  | succ d => exact span_le_succ d

/-- A valid occupied header stores a maximum below its subtree universe. -/
theorem maximum_lt_universe {d p m M : ℕ} {t : Tree d} {mem : ℕ → ℕ}
    (ht : t.Valid) (hr : Rep t p mem) (hb : t.bounds = some (m, M)) :
    mem (p + 2) = M ∧ M < universeSize d := by
  have he := ht.extrema
  simp only [Tree.Extrema, hb] at he
  have hh := hr.header
  simp only [Header, hb] at hh
  exact ⟨hh.2.1.2, he.2.1⟩

/-- The cached-maximum guard makes every computed cluster index valid, even for a query
initially outside the universe. No hypothesis constrains memory outside the represented tree. -/
theorem member_descent_safe {d p m M x : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d} {mem : ℕ → ℕ}
    (ht : (Tree.node (some (m, M)) s c).Valid)
    (hr : Rep (Tree.node (some (m, M)) s c) p mem)
    (hx : x < mem (p + 2)) :
    x / universeSize d < universeSize d ∧
      x % universeSize d < universeSize d ∧
      p + clusterOffset d (x / universeSize d) + span d ≤ p + span (d + 1) := by
  obtain ⟨hm, hM⟩ := maximum_lt_universe ht hr rfl
  rw [hm] at hx
  have hxu : x < universeSize d * universeSize d := Nat.lt_trans hx hM
  have hi : x / universeSize d < universeSize d :=
    (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr hxu
  refine ⟨hi, Nat.mod_lt _ (universeSize_pos d), ?_⟩
  simpa only [Nat.add_assoc] using Nat.add_le_add_left (cluster_end_le_span d hi) p

/-- Every header word of a cluster reached through the maximum guard lies in its parent
interval. This statement applies before reading that cluster, not only after it is represented. -/
theorem member_descendant_read_safe {d p m M x a : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d} {mem : ℕ → ℕ}
    (ht : (Tree.node (some (m, M)) s c).Valid)
    (hr : Rep (Tree.node (some (m, M)) s c) p mem)
    (hx : x < mem (p + 2)) (ha : a < 5) :
    p ≤ p + clusterOffset d (x / universeSize d) + a ∧
      p + clusterOffset d (x / universeSize d) + a < p + span (d + 1) := by
  have h := member_descent_safe ht hr hx
  have hw := cluster_word_lt_span d h.1 (header_word_lt_span d ha)
  omega

/-- A header depends only on its five words. -/
theorem header_congr {d p : ℕ} {b : Option (ℕ × ℕ)} {m m' : ℕ → ℕ}
    (h : ∀ a < 5, m (p + a) = m' (p + a)) :
    Header d b p m ↔ Header d b p m' := by
  have h0 : m p = m' p := by simpa only [Nat.add_zero] using h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  cases b with
  | none => simp only [Header, h0, h3, h4]
  | some b => cases b; simp only [Header, h0, h1, h2, h3, h4]

/-- Representation depends only on the allocated recursive interval. -/
theorem rep_congr {d p : ℕ} {t : Tree d} {m m' : ℕ → ℕ}
    (h : ∀ a < span d, m (p + a) = m' (p + a)) :
    Rep t p m ↔ Rep t p m' := by
  induction d generalizing p with
  | zero =>
    cases t with
    | leaf b => exact header_congr h
  | succ d ih =>
    cases t with
    | node b s c =>
      have hh := header_congr (b := b) (d := d + 1)
        (fun a ha => h a (header_word_lt_span _ ha))
      have hs : Rep s (p + summaryOffset) m ↔ Rep s (p + summaryOffset) m' := by
        apply ih
        intro a ha
        simpa only [Nat.add_assoc] using h (summaryOffset + a) (summary_word_lt_span d ha)
      have hc : ∀ i, Rep (c i) (p + clusterOffset d i.val) m ↔
          Rep (c i) (p + clusterOffset d i.val) m' := by
        intro i
        apply ih
        intro a ha
        simpa only [Nat.add_assoc] using
          h (clusterOffset d i.val + a) (cluster_word_lt_span d i.isLt ha)
      simp only [Rep, hh, hs, hc]

/-- Arbitrary changes outside a tree interval preserve its representation. -/
theorem rep_frame {d p : ℕ} {t : Tree d} {m m' : ℕ → ℕ} (hr : Rep t p m)
    (h : ∀ a, p ≤ a → a < p + span d → m' a = m a) : Rep t p m' := by
  apply (rep_congr (t := t) (m := m) (m' := m') ?_).mp hr
  intro a ha
  exact (h (p + a) (by omega) (by omega)).symm

/-- Write presence and, only for a nonempty record, the two extrema. -/
def writeBounds (mem : ℕ → ℕ) (p : ℕ) : Option (ℕ × ℕ) → (ℕ → ℕ)
  | none => Function.update mem p 0
  | some (m, M) => Function.update
      (Function.update (Function.update mem p 1) (p + 1) m) (p + 2) M

/-- Updating extrema leaves every cell outside the three-word bounds area unchanged. -/
theorem writeBounds_away {mem : ℕ → ℕ} {p a : ℕ} (b : Option (ℕ × ℕ))
    (ha : a < p ∨ p + 3 ≤ a) : writeBounds mem p b a = mem a := by
  have h0 : a ≠ p := by omega
  have h1 : a ≠ p + 1 := by omega
  have h2 : a ≠ p + 2 := by omega
  cases b <;> simp [writeBounds, Function.update_of_ne, h0, h1, h2]

/-- Concrete extrema writes preserve static header fields. -/
theorem header_writeBounds {d p : ℕ} {old : Option (ℕ × ℕ)} {mem : ℕ → ℕ}
    (hr : Header d old p mem) (b : Option (ℕ × ℕ)) :
    Header d b p (writeBounds mem p b) := by
  cases b with
  | none => simp [Header, writeBounds, hr.2.2]
  | some b =>
    obtain ⟨lo, hi⟩ := b
    simp [Header, writeBounds, hr.2.2]

/-- Concrete extrema writes change precisely the represented root bounds. -/
theorem rep_writeBounds {d p : ℕ} {t : Tree d} {mem : ℕ → ℕ}
    (hr : Rep t p mem) (b : Option (ℕ × ℕ)) :
    Rep (t.withBounds b) p (writeBounds mem p b) := by
  cases t with
  | leaf old => exact header_writeBounds hr b
  | node old s c =>
    refine ⟨header_writeBounds hr.1 b, ?_, ?_⟩
    · apply rep_frame hr.2.1
      intro a ha _
      exact writeBounds_away b (Or.inr (by dsimp only [summaryOffset] at ha; omega))
    · intro i
      apply rep_frame (hr.2.2 i)
      intro a ha _
      exact writeBounds_away b (Or.inr (by dsimp only [clusterOffset] at ha; omega))

/-- Replacing one cluster interval preserves its parent, summary and sibling clusters. -/
theorem rep_replace_cluster {d p : ℕ} {b : Option (ℕ × ℕ)} {s : Tree d}
    {c : Fin (universeSize d) → Tree d} {mem mem' : ℕ → ℕ}
    (hr : Rep (.node b s c) p mem) (i : Fin (universeSize d)) {t : Tree d}
    (ht : Rep t (p + clusterOffset d i.val) mem')
    (hf : ∀ a, a < p + clusterOffset d i.val ∨
      p + clusterOffset d i.val + span d ≤ a → mem' a = mem a) :
    Rep (.node b s (Function.update c i t)) p mem' := by
  refine ⟨(header_congr ?_).mp hr.1, ?_, ?_⟩
  · intro a ha
    have hstart : 5 ≤ clusterOffset d i.val := by dsimp only [clusterOffset]; omega
    exact (hf (p + a) (Or.inl (by omega))).symm
  · apply rep_frame hr.2.1
    intro a _ ha
    have hend := summary_end_le_clusterOffset d i.val
    exact hf a (Or.inl (by omega))
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using ht
    · rw [Function.update_of_ne hji]
      apply rep_frame (hr.2.2 j)
      intro a hlo hhi
      have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases hlt : j.val < i.val
      · have hend := cluster_end_le_clusterOffset d hlt
        exact hf a (Or.inl (by omega))
      · have hlt' : i.val < j.val := by omega
        have hend := cluster_end_le_clusterOffset d hlt'
        exact hf a (Or.inr (by omega))

/-- Replacing the summary interval preserves the parent header and every cluster. -/
theorem rep_replace_summary {d p : ℕ} {b : Option (ℕ × ℕ)} {s s' : Tree d}
    {c : Fin (universeSize d) → Tree d} {mem mem' : ℕ → ℕ}
    (hr : Rep (.node b s c) p mem) (hs : Rep s' (p + summaryOffset) mem')
    (hf : ∀ a, a < p + summaryOffset ∨ p + summaryOffset + span d ≤ a →
      mem' a = mem a) : Rep (.node b s' c) p mem' := by
  refine ⟨(header_congr ?_).mp hr.1, hs, ?_⟩
  · intro a ha
    exact (hf (p + a) (Or.inl (by dsimp only [summaryOffset]; omega))).symm
  · intro i
    apply rep_frame (hr.2.2 i)
    intro a hlo _
    have hend := summary_end_le_clusterOffset d i.val
    exact hf a (Or.inr (by omega))

end Cslib.Algorithms.WordRAM.VanEmdeBoas

