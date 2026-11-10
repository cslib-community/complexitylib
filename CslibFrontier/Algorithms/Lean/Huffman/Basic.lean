/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.List.Count
public import Mathlib.InformationTheory.Coding.PrefixFree

/-!
# Binary Code Trees and Prefix-Free Bit-Stream Coding

This module defines full binary code trees (`CodeTree α`), their weighted external path length
(`CodeTree.weightedPathLength`), their prefix-free binary codebook (`CodeTree.codewords`), and
total bit-stream encoding and decoding (`CodeTree.encode`, `CodeTree.decode`), connecting the tree
model to Mathlib's `InformationTheory.IsPrefixFree` and `InformationTheory.IsUniquelyDecodable`
([Huffman1952]; [CLRS2009], Section 16.3; [CoverThomas2006], Chapter 5).

## Main definitions

* `Cslib.Algorithms.Lean.Huffman.CodeTree`: full binary tree with symbol-labeled leaves.
* `CodeTree.leaves`, `CodeTree.leafDepths`, `CodeTree.maxDepth`: leaf sequence, `(symbol, depth)`
  pairs, and maximum leaf depth.
* `CodeTree.weight`, `CodeTree.weightedPathLength`: total leaf weight and weighted external path
  length (defined recursively via subtree weight sums).
* `CodeTree.codewords`, `CodeTree.codewordSet`: canonical `false`/`true` prefix-free codebook.
* `CodeTree.encodeSym`, `CodeTree.encode`, `CodeTree.decodeOne`, `CodeTree.decode`: bit-stream
  encoder and tree-walk decoder.

## Main results

* `CodeTree.weightedPathLength_eq_sum_leafDepths`,
  `CodeTree.weightedPathLength_eq_sum_codewords`: external-path-length identity ([CLRS2009],
  Equation (16.4) and Exercise 16.3-4) equating the recursive internal-weight sum with
  `∑ (a, d), d • w a`.
* `CodeTree.weightedPathLength_join`: compositional path-length identity for grafting a forest of
  code trees onto a skeleton `CodeTree (CodeTree α)`.
* `CodeTree.isPrefixFree_codewordSet`, `CodeTree.isUniquelyDecodable_codewordSet`: every
  `CodeTree` codebook is `InformationTheory.IsPrefixFree`, and every non-leaf `CodeTree` codebook
  is `InformationTheory.IsUniquelyDecodable`.
* `CodeTree.decode_encode`, `CodeTree.length_encode_eq_weightedPathLength_count`: lossless
  bit-stream round-trip and exact equality between compressed bit length and weighted external path
  length under empirical symbol counts.

## References

* [Huffman1952] David A. Huffman, *A Method for the Construction of Minimum-Redundancy Codes*, 1952.
* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms* (3rd ed.), Section 16.3, Equation (16.4) and Exercise 16.3-4, 2009.
* [CoverThomas2006] Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory* (2nd ed.),
  Chapter 5, 2006.
-/

public section

namespace Cslib.Algorithms.Lean.Huffman

/-- A full binary code tree with symbols of type `α` at the leaves. -/
inductive CodeTree (α : Type*) : Type _
  | leaf (sym : α) : CodeTree α
  | branch (left right : CodeTree α) : CodeTree α
  deriving DecidableEq, Repr

namespace CodeTree

section Structure

variable {α β : Type*}

/-- Whether a `CodeTree` consists of a single leaf. -/
@[expose] def isLeaf : CodeTree α → Bool
  | .leaf _ => true
  | .branch _ _ => false

/-- Left-to-right list of leaf symbols in `T`. -/
@[expose] def leaves : CodeTree α → List α
  | .leaf a => [a]
  | .branch l r => l.leaves ++ r.leaves

/-- Pairs `(a, d)` of each leaf symbol `a` together with its root-to-leaf depth `d`. -/
@[expose] def leafDepths : CodeTree α → List (α × ℕ)
  | .leaf a => [(a, 0)]
  | .branch l r =>
    (l.leafDepths.map fun p => (p.1, p.2 + 1)) ++
      (r.leafDepths.map fun p => (p.1, p.2 + 1))

/-- Maximum root-to-leaf depth of `T`. -/
@[expose] def maxDepth : CodeTree α → ℕ
  | .leaf _ => 0
  | .branch l r => max l.maxDepth r.maxDepth + 1

/-- Functorial map on leaf labels. -/
@[expose] def map (f : α → β) : CodeTree α → CodeTree β
  | .leaf a => .leaf (f a)
  | .branch l r => .branch (l.map f) (r.map f)

/-- Graft a `CodeTree` of subtrees into a single `CodeTree`. -/
@[expose] def join : CodeTree (CodeTree α) → CodeTree α
  | .leaf t => t
  | .branch l r => .branch l.join r.join

@[simp] theorem leaves_leaf (a : α) : (leaf a).leaves = [a] := rfl

@[simp] theorem leaves_branch (l r : CodeTree α) :
    (branch l r).leaves = l.leaves ++ r.leaves := rfl

theorem one_le_length_leaves (T : CodeTree α) : 1 ≤ T.leaves.length := by
  induction T with
  | leaf _ => simp
  | branch l r ihl ihr => simp; omega

theorem leaves_ne_nil (T : CodeTree α) : T.leaves ≠ [] := by
  have := T.one_le_length_leaves
  intro h; simp_all

theorem two_le_length_leaves_of_branch (l r : CodeTree α) :
    2 ≤ (branch l r).leaves.length := by
  have := l.one_le_length_leaves
  have := r.one_le_length_leaves
  simp; omega

theorem eq_leaf_of_leaves_perm_singleton {T : CodeTree α} {a : α}
    (h : T.leaves.Perm [a]) : T = leaf a := by
  cases T with
  | leaf b => exact congrArg leaf (List.singleton_inj.mp h.eq_singleton)
  | branch l r =>
    have := h.length_eq
    have := two_le_length_leaves_of_branch l r
    simp only [List.length_singleton] at *; omega

@[simp] theorem leaves_map (f : α → β) (T : CodeTree α) :
    (T.map f).leaves = T.leaves.map f := by
  induction T with
  | leaf a => rfl
  | branch l r ihl ihr => simp [map, ihl, ihr]

@[simp] theorem join_map_leaf (T : CodeTree α) : (T.map leaf).join = T := by
  induction T with
  | leaf _ => rfl
  | branch l r ihl ihr => simp [map, join, ihl, ihr]

theorem leaves_join (S : CodeTree (CodeTree α)) :
    S.join.leaves = (S.leaves.map leaves).flatten := by
  induction S with
  | leaf t => simp [join]
  | branch l r ihl ihr => simp [join, ihl, ihr, List.flatten_append]

@[simp] theorem map_fst_leafDepths (T : CodeTree α) :
    T.leafDepths.map Prod.fst = T.leaves := by
  induction T with
  | leaf a => rfl
  | branch l r ihl ihr =>
    simp [leafDepths, List.map_append, List.map_map, Function.comp_def, ihl, ihr]

theorem snd_le_maxDepth_of_mem_leafDepths {T : CodeTree α} {p : α × ℕ}
    (hp : p ∈ T.leafDepths) : p.2 ≤ T.maxDepth := by
  induction T generalizing p with
  | leaf a => simp_all [leafDepths, maxDepth]
  | branch l r ihl ihr =>
    simp only [leafDepths, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;> simp only [maxDepth]
    · exact Nat.succ_le_succ ((ihl hq).trans (le_max_left _ _))
    · exact Nat.succ_le_succ ((ihr hq).trans (le_max_right _ _))

end Structure

/-! ## Subtree weight and weighted external path length -/

section Weights

variable {α β : Type*}

/-- Total weight of all leaves in `T` with respect to symbol weight `w`. -/
@[expose] def weight [Add β] (w : α → β) : CodeTree α → β
  | .leaf a => w a
  | .branch l r => l.weight w + r.weight w

/-- Weighted external path length of `T`, defined recursively via internal child-weight sums
([CLRS2009], Exercise 16.3-4): `0` at a leaf, and
`l.weightedPathLength w + r.weightedPathLength w + (l.weight w + r.weight w)` at an internal
branch. -/
@[expose] def weightedPathLength [Add β] [Zero β] (w : α → β) : CodeTree α → β
  | .leaf _ => 0
  | .branch l r =>
    l.weightedPathLength w + r.weightedPathLength w + (l.weight w + r.weight w)

@[simp] theorem weight_leaf [Add β] (w : α → β) (a : α) :
    (leaf a).weight w = w a := rfl

@[simp] theorem weight_branch [Add β] (w : α → β) (l r : CodeTree α) :
    (branch l r).weight w = l.weight w + r.weight w := rfl

@[simp] theorem weightedPathLength_leaf [Add β] [Zero β] (w : α → β) (a : α) :
    (leaf a).weightedPathLength w = 0 := rfl

@[simp] theorem weightedPathLength_branch [Add β] [Zero β] (w : α → β) (l r : CodeTree α) :
    (branch l r).weightedPathLength w =
      l.weightedPathLength w + r.weightedPathLength w + (l.weight w + r.weight w) := rfl

theorem weight_eq_sum_leaves [AddCommMonoid β] (w : α → β) (T : CodeTree α) :
    T.weight w = (T.leaves.map w).sum := by
  induction T with
  | leaf a => simp
  | branch l r ihl ihr => simp [ihl, ihr, List.map_append, List.sum_append]

theorem weight_eq_of_leaves_perm [AddCommMonoid β] (w : α → β) {T₁ T₂ : CodeTree α}
    (h : T₁.leaves.Perm T₂.leaves) : T₁.weight w = T₂.weight w := by
  rw [weight_eq_sum_leaves, weight_eq_sum_leaves]
  exact (h.map w).sum_eq

theorem weight_nonneg [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {T : CodeTree α} (hw : ∀ a ∈ T.leaves, 0 ≤ w a) :
    0 ≤ T.weight w := by
  induction T with
  | leaf a => exact hw a List.mem_cons_self
  | branch l r ihl ihr =>
    exact add_nonneg (ihl fun a ha => hw a (List.mem_append_left _ ha))
      (ihr fun a ha => hw a (List.mem_append_right _ ha))

/-- **External-Path-Length Identity** ([CLRS2009], Equation (16.4) and Exercise 16.3-4): the
recursive internal-weight sum `weightedPathLength w` equals `∑ (a, d) ∈ T.leafDepths, d • w a`. -/
theorem weightedPathLength_eq_sum_leafDepths [AddCommMonoid β] (w : α → β) (T : CodeTree α) :
    T.weightedPathLength w = (T.leafDepths.map fun p => p.2 • w p.1).sum := by
  induction T with
  | leaf a => simp [leafDepths]
  | branch l r ihl ihr =>
    have hshift (U : CodeTree α) :
        ((U.leafDepths.map fun p => (p.1, p.2 + 1)).map fun p => p.2 • w p.1).sum =
          (U.leafDepths.map fun p => p.2 • w p.1).sum + U.weight w := by
      have hwt : (U.leafDepths.map fun p => w p.1).sum = U.weight w := by
        rw [weight_eq_sum_leaves, ← map_fst_leafDepths U, List.map_map]; rfl
      rw [← hwt, List.map_map]
      simp only [Function.comp_def, succ_nsmul]
      exact List.sum_map_add
    simp only [weightedPathLength_branch, leafDepths, List.map_append, List.sum_append,
      hshift, ihl, ihr]
    ac_rfl

theorem weight_join [Add β] (w : α → β) (S : CodeTree (CodeTree α)) :
    S.join.weight w = S.weight (fun t => t.weight w) := by
  induction S with
  | leaf _ => rfl
  | branch l r ihl ihr => simp [join, ihl, ihr]

/-- Grafting subtrees onto a skeleton `S : CodeTree (CodeTree α)` decomposes weighted external path
length into the skeleton's weighted path length (under subtree weights) plus the sum of the
subtrees' own weighted path lengths. -/
theorem weightedPathLength_join [AddCommMonoid β] (w : α → β) (S : CodeTree (CodeTree α)) :
    S.join.weightedPathLength w =
      S.weightedPathLength (fun t => t.weight w) +
        (S.leaves.map fun t => t.weightedPathLength w).sum := by
  induction S with
  | leaf t => simp [join]
  | branch l r ihl ihr =>
    simp only [join, weightedPathLength_branch, leaves_branch, List.map_append, List.sum_append,
      weight_join, ihl, ihr]
    ac_rfl

end Weights

/-! ## Prefix-free codebook and bit-stream encoding/decoding -/

section Coding

variable {α : Type*}

/-- Canonical binary codebook assigning `false` to left branches and `true` to right branches. -/
@[expose] def codewords : CodeTree α → List (α × List Bool)
  | .leaf a => [(a, [])]
  | .branch l r =>
    (l.codewords.map fun p => (p.1, false :: p.2)) ++
      (r.codewords.map fun p => (p.1, true :: p.2))

/-- Set of binary codewords produced by `T`. -/
def codewordSet (T : CodeTree α) : Set (List Bool) :=
  {c | ∃ a, (a, c) ∈ T.codewords}

@[simp] theorem map_fst_codewords (T : CodeTree α) :
    T.codewords.map Prod.fst = T.leaves := by
  induction T with
  | leaf _ => rfl
  | branch l r ihl ihr =>
    simp [codewords, List.map_append, List.map_map, Function.comp_def, ihl, ihr]

@[simp] theorem map_length_codewords (T : CodeTree α) :
    (T.codewords.map fun p => (p.1, p.2.length)) = T.leafDepths := by
  induction T with
  | leaf _ => rfl
  | branch l r ihl ihr =>
    rw [codewords, leafDepths, ← ihl, ← ihr]
    simp [List.map_append, List.map_map, Function.comp_def]

theorem weightedPathLength_eq_sum_codewords {β : Type*} [AddCommMonoid β]
    (w : α → β) (T : CodeTree α) :
    T.weightedPathLength w = (T.codewords.map fun p => p.2.length • w p.1).sum := by
  rw [weightedPathLength_eq_sum_leafDepths, ← map_length_codewords, List.map_map]
  rfl

theorem pairwise_rel_of_ne {γ : Type*} {R : γ → γ → Prop}
    (hsym : ∀ {u v}, R u v → R v u) {L : List γ} (hpw : L.Pairwise R)
    {x y : γ} (hx : x ∈ L) (hy : y ∈ L) (hne : x ≠ y) : R x y := by
  induction hpw with
  | nil => cases hx
  | @cons a as ha _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact absurd rfl hne
    · exact ha y hy'
    · exact hsym (ha x hx')
    · exact ih hx' hy'

/-- Distinct leaf entries in `T.codewords` have prefix-incomparable codewords. -/
theorem pairwise_incomparable_codewords (T : CodeTree α) :
    (T.codewords.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) := by
  induction T with
  | leaf _ => simp [codewords]
  | branch l r ihl ihr =>
    have hmap (b : Bool) (L : List (α × List Bool)) :
        (L.map fun p => (p.1, b :: p.2)).map Prod.snd = (L.map Prod.snd).map (b :: ·) := by
      simp [List.map_map, Function.comp_def]
    have hcons (b : Bool) {L : List (List Bool)}
        (h : L.Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁)) :
        (L.map (b :: ·)).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) :=
      List.pairwise_map.mpr <| h.imp fun h' =>
        ⟨fun hp => h'.1 (List.cons_prefix_cons.mp hp).2,
         fun hp => h'.2 (List.cons_prefix_cons.mp hp).2⟩
    rw [codewords, List.map_append, hmap, hmap, List.pairwise_append]
    refine ⟨hcons false ihl, hcons true ihr, ?_⟩
    rintro _ hx _ hy
    rcases List.mem_map.mp hx with ⟨_, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨_, _, rfl⟩
    simp

theorem nodup_map_snd_codewords (T : CodeTree α) :
    (T.codewords.map Prod.snd).Nodup :=
  List.Pairwise.imp
    (fun {c₁ c₂} h (hEq : c₁ = c₂) => h.1 (hEq ▸ List.prefix_refl c₁))
    T.pairwise_incomparable_codewords

/-- Every `CodeTree` codebook satisfies Mathlib's `InformationTheory.IsPrefixFree`. -/
theorem isPrefixFree_codewordSet (T : CodeTree α) :
    InformationTheory.IsPrefixFree T.codewordSet := by
  rintro x ⟨a, ha⟩ y ⟨b, hb⟩ hpref
  by_contra hne
  exact (pairwise_rel_of_ne (fun h => ⟨h.2, h.1⟩) T.pairwise_incomparable_codewords
    (List.mem_map.mpr ⟨_, ha, rfl⟩) (List.mem_map.mpr ⟨_, hb, rfl⟩) hne).1 hpref

theorem nil_notMem_codewordSet_branch (l r : CodeTree α) :
    [] ∉ (branch l r).codewordSet := by
  rintro ⟨a, ha⟩
  simp only [codewords, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨p, _, hp⟩ | ⟨p, _, hp⟩ <;> simp at hp

/-- Every non-leaf `CodeTree` codebook satisfies Mathlib's
`InformationTheory.IsUniquelyDecodable`. -/
theorem isUniquelyDecodable_codewordSet (l r : CodeTree α) :
    InformationTheory.IsUniquelyDecodable (branch l r).codewordSet :=
  (branch l r).isPrefixFree_codewordSet.isUniquelyDecodable (nil_notMem_codewordSet_branch l r)

/-- Lookup the binary codeword of symbol `a` in `T` (first match in left-to-right order). -/
@[expose] def encodeSym [DecidableEq α] : CodeTree α → α → Option (List Bool)
  | .leaf b, a => if a = b then some [] else none
  | .branch l r, a =>
    match l.encodeSym a with
    | some c => some (false :: c)
    | none => (r.encodeSym a).map (true :: ·)

/-- Encode a message `msg : List α` by concatenating symbol codewords. -/
@[expose] def encode [DecidableEq α] (T : CodeTree α) : List α → Option (List Bool)
  | [] => some []
  | a :: msg => do
    let c ← T.encodeSym a
    let rest ← T.encode msg
    pure (c ++ rest)

/-- Decode a single symbol by walking from `cur` to a leaf, returning the remaining bit stream. -/
@[expose] def decodeOne : CodeTree α → List Bool → Option (α × List Bool)
  | .leaf a, bits => some (a, bits)
  | .branch l _, false :: bits => decodeOne l bits
  | .branch _ r, true :: bits => decodeOne r bits
  | .branch _ _, [] => none

theorem decodeOne_branch_length_lt {l r : CodeTree α} {bits rem : List Bool} {a : α}
    (h : decodeOne (branch l r) bits = some (a, rem)) :
    rem.length < bits.length := by
  have hle : ∀ (T : CodeTree α) (bs rm : List Bool) (x : α),
      decodeOne T bs = some (x, rm) → rm.length ≤ bs.length := by
    intro T
    induction T with
    | leaf b => simp [decodeOne]
    | branch l' r' ihl ihr =>
      rintro (_ | ⟨false | true, bs⟩) rm x hd <;> simp only [decodeOne] at hd
      · cases hd
      · exact Nat.le_succ_of_le (ihl bs rm x hd)
      · exact Nat.le_succ_of_le (ihr bs rm x hd)
  rcases bits with _ | ⟨false | true, bs⟩ <;> simp only [decodeOne] at h
  · cases h
  · exact Nat.lt_succ_of_le (hle l bs rem a h)
  · exact Nat.lt_succ_of_le (hle r bs rem a h)

/-- Decode a bit stream into a list of symbols using a non-leaf code tree `T`. -/
@[expose] def decode : CodeTree α → List Bool → Option (List α)
  | .leaf _, _ => none
  | .branch _l _r, [] => some []
  | .branch l r, b :: bs =>
    match h : decodeOne (.branch l r) (b :: bs) with
    | none => none
    | some (a, rem) =>
      have : rem.length < (b :: bs).length := decodeOne_branch_length_lt h
      (decode (.branch l r) rem).map (a :: ·)
termination_by _ bits => bits.length

theorem encodeSym_eq_none_of_notMem [DecidableEq α] {T : CodeTree α} {a : α}
    (ha : a ∉ T.leaves) : T.encodeSym a = none := by
  induction T with
  | leaf b => simp_all [encodeSym]
  | branch l r ihl ihr =>
    simp only [leaves_branch, List.mem_append, not_or] at ha
    simp [encodeSym, ihl ha.1, ihr ha.2]

theorem mem_codewords_of_encodeSym [DecidableEq α] {T : CodeTree α} {a : α} {c : List Bool}
    (h : T.encodeSym a = some c) : (a, c) ∈ T.codewords := by
  induction T generalizing c with
  | leaf b =>
    simp only [encodeSym] at h; split_ifs at h with hab
    simp only [Option.some.injEq] at h; subst hab h; simp [codewords]
  | branch l r ihl ihr =>
    simp only [encodeSym] at h
    cases hl : l.encodeSym a with
    | some cl =>
      simp only [hl, Option.some.injEq] at h; subst h
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_, ihl hl, rfl⟩)
    | none =>
      simp only [hl, Option.map_eq_some_iff] at h
      rcases h with ⟨cr, hr, rfl⟩
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ihr hr, rfl⟩)

theorem exists_encodeSym_of_mem_leaves [DecidableEq α] {T : CodeTree α} {a : α}
    (ha : a ∈ T.leaves) : ∃ c, T.encodeSym a = some c := by
  induction T with
  | leaf b => simp_all [encodeSym]
  | branch l r ihl ihr =>
    by_cases hal : a ∈ l.leaves
    · rcases ihl hal with ⟨cl, hcl⟩; exact ⟨false :: cl, by simp [encodeSym, hcl]⟩
    · rcases ihr (by simp_all) with ⟨cr, hcr⟩
      exact ⟨true :: cr, by simp [encodeSym, encodeSym_eq_none_of_notMem hal, hcr]⟩

theorem encodeSym_eq_some_iff_mem_codewords [DecidableEq α] {T : CodeTree α}
    (hnodup : T.leaves.Nodup) {a : α} {c : List Bool} :
    T.encodeSym a = some c ↔ (a, c) ∈ T.codewords := by
  refine ⟨mem_codewords_of_encodeSym, fun hmem => ?_⟩
  have ha : a ∈ T.leaves := map_fst_codewords T ▸ List.mem_map.mpr ⟨_, hmem, rfl⟩
  rcases exists_encodeSym_of_mem_leaves ha with ⟨c', hc'⟩
  have hpw : T.codewords.Pairwise (fun p q => p.1 ≠ q.1) :=
    List.pairwise_map.mp (map_fst_codewords T ▸ hnodup)
  by_cases hEq : c' = c
  · rwa [← hEq]
  · exact False.elim (pairwise_rel_of_ne (fun h => h.symm) hpw
      (mem_codewords_of_encodeSym hc') hmem (fun h => hEq (Prod.mk.inj h).2) rfl)

theorem decodeOne_append_of_mem_codewords {T : CodeTree α} {a : α} {c : List Bool}
    (hmem : (a, c) ∈ T.codewords) (rest : List Bool) :
    decodeOne T (c ++ rest) = some (a, rest) := by
  induction T generalizing c with
  | leaf b => simp_all [codewords]; rfl
  | branch l r ihl ihr =>
    simp only [codewords, List.mem_append, List.mem_map, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨a', cl⟩, hl, rfl, rfl⟩ | ⟨⟨a', cr⟩, hr, rfl, rfl⟩
    · exact ihl hl
    · exact ihr hr

theorem exists_encode_of_subset_leaves [DecidableEq α] {T : CodeTree α} {msg : List α}
    (hmsg : ∀ a ∈ msg, a ∈ T.leaves) :
    ∃ bits, T.encode msg = some bits := by
  induction msg with
  | nil => exact ⟨[], rfl⟩
  | cons a msg ih =>
    rcases exists_encodeSym_of_mem_leaves (hmsg a List.mem_cons_self) with ⟨c, hc⟩
    rcases ih (fun b hb => hmsg b (List.mem_cons_of_mem a hb)) with ⟨rest, hrest⟩
    exact ⟨c ++ rest, by simp [encode, hc, hrest]⟩

/-- **Lossless Bit-Stream Round-Trip**: for any non-leaf `CodeTree` (`branch l r`) and any message
whose encoded bit stream is `bits`, `decode` recovers `msg` exactly. -/
theorem decode_encode [DecidableEq α] (l r : CodeTree α) {msg : List α} {bits : List Bool}
    (henc : (branch l r).encode msg = some bits) :
    (branch l r).decode bits = some msg := by
  induction msg generalizing bits with
  | nil => simp_all [encode, decode]
  | cons a msg ih =>
    simp only [encode, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at henc
    rcases henc with ⟨c, hc, rest, hrest, rfl⟩
    have hmem := mem_codewords_of_encodeSym hc
    rcases c with _ | ⟨b, bs⟩
    · exact absurd ⟨a, hmem⟩ (nil_notMem_codewordSet_branch l r)
    · have hd1 : decodeOne (branch l r) (b :: (bs ++ rest)) = some (a, rest) :=
        decodeOne_append_of_mem_codewords hmem rest
      rw [List.cons_append, decode]
      split
      · next hnone => rw [hd1] at hnone; cases hnone
      · next a' rem hsome =>
        simp only [hd1, Option.some.injEq, Prod.mk.injEq] at hsome
        rcases hsome with ⟨rfl, rfl⟩
        simp [ih hrest]

private theorem sum_codewords_count_cons [DecidableEq α] {L : List (α × List Bool)}
    (hnodup : (L.map Prod.fst).Nodup) {a : α} {c : List Bool}
    (hmem : (a, c) ∈ L) (msg : List α) :
    (L.map fun p => p.2.length • (a :: msg).count p.1).sum =
      c.length + (L.map fun p => p.2.length • msg.count p.1).sum := by
  induction L with
  | nil => cases hmem
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, List.nodup_cons] at hnodup ⊢
    rcases List.mem_cons.mp hmem with rfl | hps
    · have htail : (ps.map fun q => q.2.length • (a :: msg).count q.1) =
          ps.map fun q => q.2.length • msg.count q.1 :=
        List.map_congr_left fun q hq => by
          have hne : q.1 ≠ a := fun h => hnodup.1 (h ▸ List.mem_map.mpr ⟨q, hq, rfl⟩)
          rw [List.count_cons_of_ne hne.symm]
      simp only [List.count_cons_self, htail]
      rw [show c.length • (msg.count a + 1) = c.length • msg.count a + c.length from
        Nat.mul_succ c.length (msg.count a)]
      omega
    · have hpa : a ≠ p.1 := fun h => hnodup.1 (h.symm ▸ List.mem_map.mpr ⟨_, hps, rfl⟩)
      simp only [List.count_cons_of_ne hpa, ih hnodup.2 hps]; omega

/-- When `T.leaves.Nodup`, the bit length of `T.encode msg` equals the weighted external path length
of `T` under the empirical symbol frequency function `fun a => msg.count a`. -/
theorem length_encode_eq_weightedPathLength_count [DecidableEq α] {T : CodeTree α}
    (hnodup : T.leaves.Nodup) {msg : List α} {bits : List Bool}
    (henc : T.encode msg = some bits) :
    bits.length = T.weightedPathLength (fun a => msg.count a) := by
  induction msg generalizing bits with
  | nil =>
    simp only [encode, Option.some.injEq] at henc; subst henc
    simp [weightedPathLength_eq_sum_codewords]
  | cons a msg ih =>
    simp only [encode, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at henc
    rcases henc with ⟨c, hc, rest, hrest, rfl⟩
    have hnodup_cw : (T.codewords.map Prod.fst).Nodup := by rwa [map_fst_codewords]
    rw [List.length_append, ih hrest, weightedPathLength_eq_sum_codewords,
      weightedPathLength_eq_sum_codewords,
      sum_codewords_count_cons hnodup_cw (mem_codewords_of_encodeSym hc) msg]

end Coding

end CodeTree

end Cslib.Algorithms.Lean.Huffman
