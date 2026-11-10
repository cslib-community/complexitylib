/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Huffman.Kraft

/-!
# Optimality of Huffman Coding

This module formalizes the relational specification of Huffman tree construction (`IsHuffmanBuild`)
and proves its optimality over:

1. **All full binary `CodeTree α`s** (`IsHuffmanBuild.weightedPathLength_le`, formalizing
   [Huffman1952] and [CLRS2009], Lemmas 16.2–16.3 and Theorem 16.4), over any ordered additive
   commutative monoid `β` (`ℕ`, `ℤ`, `ℚ`, `ℝ`, ...) without requiring `DecidableEq α`,
   `LinearOrder β`, or nonnegativity of symbol weights.
2. **All finite injective `InformationTheory.IsPrefixFree` binary codes**
   (`IsHuffmanBuild.weightedPathLength_le_of_isPrefixFree`) under nonnegative weights, via unary
   trie compaction (`exists_codeTree_of_isPrefixFree`).
3. **All finite injective `InformationTheory.IsUniquelyDecodable` binary codes**
   (`IsHuffmanBuild.weightedPathLength_le_of_isUniquelyDecodable`) under nonnegative weights, via
   Mathlib's Kraft–McMillan inequality and our constructive binary Kraft converse
   (`exists_codeTree_of_isUniquelyDecodable`, [McMillan1956]; [CoverThomas2006], Theorem 5.8.1,
   specialized to binary alphabet `Bool`, $D = 2$, and generalized from real probability weights to
   any ordered additive commutative monoid `β`).

## Proof architecture

Rather than indexing into trees via `[DecidableEq α]` (which creates nine-way aliasing casework and
breaks on duplicate symbols during intermediate merges), we represent a competitor over an
intermediate forest `F : List (CodeTree α)` as a *skeleton* `S : CodeTree (CodeTree α)` with
`S.leaves.Perm F`. Rotating deeper subtrees leftward (`rotateDeepestLeft`) places a maximum-depth
sibling cherry at the first two leaf slots without changing `weightedPathLength`, relabeling moves a
minimum-weight pair `(t₁, t₂)` into that cherry without increasing cost (Lemma 16.2), and
contracting the cherry via `LeftCherryAtDepth` leaves `CodeTree.join` unchanged
(`LeftCherryAtDepth.join_contract_eq`) while also satisfying the additive shift identity of
Lemma 16.3.

## Main definitions

* `Cslib.Algorithms.Lean.Huffman.IsMinPair`: two trees in a forest have minimum weight among all
  remaining trees.
* `Cslib.Algorithms.Lean.Huffman.IsHuffmanBuild`: relational trace of greedy Huffman forest merges.
* `Cslib.Algorithms.Lean.Huffman.LeftCherryAtDepth`: witness that a `CodeTree` has a sibling cherry
  at the bottom of its leftmost spine at a specified depth, paired with its contraction context.

## Main results

* `Cslib.Algorithms.Lean.Huffman.exists_cherry_weightedPathLength_le`: greedy-choice exchange lemma
  ([CLRS2009], Lemma 16.2).
* `Cslib.Algorithms.Lean.Huffman.LeftCherryAtDepth.weightedPathLength_eq_contract_add`: cherry
  contraction path-length identity ([CLRS2009], Lemma 16.3).
* `Cslib.Algorithms.Lean.Huffman.IsHuffmanBuild.weightedPathLength_le`: optimality among all full
  binary `CodeTree`s ([CLRS2009], Theorem 16.4).
* `Cslib.Algorithms.Lean.Huffman.IsHuffmanBuild.weightedPathLength_le_of_isPrefixFree`: optimality
  among all injective `InformationTheory.IsPrefixFree` binary codes.
* `Cslib.Algorithms.Lean.Huffman.IsHuffmanBuild.weightedPathLength_le_of_isUniquelyDecodable`:
  optimality among all injective `InformationTheory.IsUniquelyDecodable` binary codes.

## References

* [Huffman1952] David A. Huffman, *A Method for the Construction of Minimum-Redundancy Codes*, 1952.
* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms* (3rd ed.), Section 16.3, Lemmas 16.2–16.3 and Theorem 16.4, 2009.
* [CoverThomas2006] Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory* (2nd ed.),
  Section 5.8, Theorem 5.8.1, 2006.
-/

public section

namespace Cslib.Algorithms.Lean.Huffman

/-! ## Relational specification of Huffman tree construction -/

/-- `(t₁, t₂)` is a minimum-weight pair extracted from forest `F` leaving `F_rest`. -/
structure IsMinPair {α β : Type*} [Add β] [LE β] (w : α → β)
    (F : List (CodeTree α)) (t₁ t₂ : CodeTree α) (F_rest : List (CodeTree α)) : Prop where
  /-- Extracting `t₁` and `t₂` from `F` leaves `F_rest` up to permutation. -/
  perm : F.Perm (t₁ :: t₂ :: F_rest)
  /-- Both `t₁` and `t₂` have weight at most every remaining tree in `F_rest`. -/
  weight_le : ∀ t ∈ F_rest, t₁.weight w ≤ t.weight w ∧ t₂.weight w ≤ t.weight w

/-- `IsHuffmanBuild w F T` holds when `T` is obtained from the non-empty forest `F` by repeatedly
merging a minimum-weight pair of trees ([Huffman1952]; [CLRS2009], Section 16.3). -/
inductive IsHuffmanBuild {α β : Type*} [Add β] [LE β] (w : α → β) :
    List (CodeTree α) → CodeTree α → Prop
  | single (t : CodeTree α) : IsHuffmanBuild w [t] t
  | step {F F_rest : List (CodeTree α)} {t₁ t₂ T : CodeTree α} :
      IsMinPair w F t₁ t₂ F_rest →
      IsHuffmanBuild w (.branch t₁ t₂ :: F_rest) T →
      IsHuffmanBuild w F T

theorem IsHuffmanBuild.leaves_perm_flatten {α β : Type*} [Add β] [LE β] {w : α → β}
    {F : List (CodeTree α)} {T : CodeTree α} (h : IsHuffmanBuild w F T) :
    T.leaves.Perm (F.map CodeTree.leaves).flatten := by
  induction h with
  | single t => simp
  | @step F F_rest t₁ t₂ T hmin _ ih =>
    have hflat : ((CodeTree.branch t₁ t₂ :: F_rest).map CodeTree.leaves).flatten =
        ((t₁ :: t₂ :: F_rest).map CodeTree.leaves).flatten := by
      simp [List.append_assoc]
    rw [hflat] at ih
    exact ih.trans (hmin.perm.symm.map CodeTree.leaves).flatten

theorem IsHuffmanBuild.leaves_perm {α β : Type*} [Add β] [LE β] {w : α → β}
    {syms : List α} {T : CodeTree α} (h : IsHuffmanBuild w (syms.map .leaf) T) :
    T.leaves.Perm syms := by
  have hflat : ∀ L : List α, ((L.map CodeTree.leaf).map CodeTree.leaves).flatten = L := fun L => by
    induction L with
    | nil => rfl
    | cons a as ih =>
      simp only [List.map_cons, List.flatten_cons, CodeTree.leaves_leaf, List.singleton_append, ih]
  exact hflat syms ▸ h.leaves_perm_flatten

/-! ## Monoid rearrangement and depth-weighted list swaps -/

/-- Subtraction-free rearrangement inequality: if `d₁ ≤ d₂` and `w₁ ≤ w₂`, assigning the larger
depth `d₂` to the smaller weight `w₁` does not exceed assigning `d₂` to `w₂`. -/
theorem rearrangement_nsmul_le {β : Type*} [AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β] {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) {w₁ w₂ : β} (hw : w₁ ≤ w₂) :
    d₂ • w₁ + d₁ • w₂ ≤ d₁ • w₁ + d₂ • w₂ := by
  rw [← Nat.add_sub_of_le hd, add_nsmul, add_nsmul]
  have hle := add_le_add (le_refl (d₁ • w₁ + d₁ • w₂)) (nsmul_le_nsmul_right hw (d₂ - d₁))
  rwa [show (d₁ • w₁ + d₁ • w₂) + (d₂ - d₁) • w₁ = d₁ • w₁ + (d₂ - d₁) • w₁ + d₁ • w₂ by ac_rfl,
    show (d₁ • w₁ + d₁ • w₂) + (d₂ - d₁) • w₂ = d₁ • w₁ + (d₁ • w₂ + (d₂ - d₁) • w₂) by ac_rfl]
    at hle

private def zipCost {γ β : Type*} [AddCommMonoid β] (W : γ → β)
    (xs : List γ) (ds : List ℕ) : β :=
  ((xs.zip ds).map fun p => p.2 • W p.1).sum

private theorem zipCost_cons {γ β : Type*} [AddCommMonoid β] (W : γ → β)
    (x : γ) (xs : List γ) (d : ℕ) (ds : List ℕ) :
    zipCost W (x :: xs) (d :: ds) = d • W x + zipCost W xs ds := by
  simp [zipCost]

private theorem zipCost_append {γ β : Type*} [AddCommMonoid β] (W : γ → β)
    {xs₁ xs₂ : List γ} {ds₁ ds₂ : List ℕ} (hlen : xs₁.length = ds₁.length) :
    zipCost W (xs₁ ++ xs₂) (ds₁ ++ ds₂) = zipCost W xs₁ ds₁ + zipCost W xs₂ ds₂ := by
  induction xs₁ generalizing ds₁ with
  | nil =>
    cases ds₁ with
    | nil => simp [zipCost]
    | cons _ _ => simp at hlen
  | cons x xs₁ ih =>
    cases ds₁ with
    | nil => simp at hlen
    | cons d ds₁ =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.cons_append, zipCost_cons, ih hlen]
      ac_rfl

private theorem zipCost_swap_first_two {γ β : Type*} [AddCommMonoid β] (W : γ → β)
    (x y : γ) (xs : List γ) (D : ℕ) (ds : List ℕ) :
    zipCost W (x :: y :: xs) (D :: D :: ds) = zipCost W (y :: x :: xs) (D :: D :: ds) := by
  simp only [zipCost_cons]
  ac_rfl

private theorem split_at_length {α₁ α₂ : Type*} (p : List α₁) (z : α₁) (q : List α₁)
    {es : List α₂} (hlen : (p ++ z :: q).length = es.length) :
    ∃ d_p d_z d_q, es = d_p ++ d_z :: d_q ∧ p.length = d_p.length ∧ q.length = d_q.length := by
  induction p generalizing es with
  | nil =>
    cases es with
    | nil => simp at hlen
    | cons d_z d_q =>
      simp only [List.nil_append, List.length_cons, Nat.succ.injEq] at hlen
      exact ⟨[], d_z, d_q, rfl, rfl, hlen⟩
  | cons a p ih =>
    cases es with
    | nil => simp at hlen
    | cons e es =>
      simp only [List.cons_append, List.length_cons, Nat.succ.injEq] at hlen
      rcases ih hlen with ⟨d_p, d_z, d_q, rfl, hp, hq⟩
      exact ⟨e :: d_p, d_z, d_q, rfl, congrArg Nat.succ hp, hq⟩

private theorem zipCost_swap_head_tail {γ β : Type*} [AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β] (W : γ → β) {u z : γ} {p q : List γ} {D : ℕ} {es : List ℕ}
    (hlen : (p ++ z :: q).length = es.length)
    (hD : ∀ d ∈ es, d ≤ D) (hw : W z ≤ W u) :
    zipCost W (z :: (p ++ u :: q)) (D :: es) ≤
      zipCost W (u :: (p ++ z :: q)) (D :: es) := by
  rcases split_at_length p z q hlen with ⟨d_p, d_z, d_q, rfl, hp, _⟩
  simp only [zipCost_cons, zipCost_append W hp]
  have hle := add_le_add (rearrangement_nsmul_le (hD d_z (by simp)) hw)
    (le_refl (zipCost W p d_p + zipCost W q d_q))
  rwa [show D • W z + d_z • W u + (zipCost W p d_p + zipCost W q d_q) =
      D • W z + (zipCost W p d_p + (d_z • W u + zipCost W q d_q)) by ac_rfl,
    show d_z • W z + D • W u + (zipCost W p d_p + zipCost W q d_q) =
      D • W u + (zipCost W p d_p + (d_z • W z + zipCost W q d_q)) by ac_rfl] at hle

private theorem zipCost_swap_second_tail {γ β : Type*} [AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β] (W : γ → β) (x : γ) {v z : γ} {p q : List γ} {D : ℕ} {es : List ℕ}
    (hlen : (p ++ z :: q).length = es.length)
    (hD : ∀ d ∈ es, d ≤ D) (hw : W z ≤ W v) :
    zipCost W (x :: z :: (p ++ v :: q)) (D :: D :: es) ≤
      zipCost W (x :: v :: (p ++ z :: q)) (D :: D :: es) :=
  add_le_add le_rfl (zipCost_swap_head_tail W hlen hD hw)

/-- Step B: when `x` already occupies slot 0 (`depth D`), move `y` into slot 1 (`depth D`). -/
private theorem exists_perm_tail_stepB {γ β : Type*} [AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β] (W : γ → β) (x y : γ) {F_rest : List γ}
    {v : γ} {tail : List γ} {D : ℕ} {es : List ℕ}
    (hperm : (y :: F_rest).Perm (v :: tail))
    (hmin_y : ∀ z ∈ F_rest, W y ≤ W z)
    (hlen : tail.length = es.length)
    (hD : ∀ d ∈ es, d ≤ D) :
    ∃ tail' : List γ, tail'.Perm F_rest ∧
      zipCost W (x :: y :: tail') (D :: D :: es) ≤
        zipCost W (x :: v :: tail) (D :: D :: es) := by
  rcases List.mem_cons.mp (hperm.subset List.mem_cons_self) with rfl | hy_tail
  · exact ⟨tail, (List.Perm.cons_inv hperm).symm, le_rfl⟩
  · rcases List.append_of_mem hy_tail with ⟨p, q, rfl⟩
    have hF_perm : F_rest.Perm (v :: p ++ q) := List.Perm.cons_inv <|
      hperm.trans (by simpa using List.perm_middle (l₁ := v :: p) (a := y) (l₂ := q))
    exact ⟨p ++ v :: q, List.perm_middle.trans hF_perm.symm,
      zipCost_swap_second_tail W x hlen hD (hmin_y v (hF_perm.symm.subset List.mem_cons_self))⟩

/-- Moving a minimum-weight pair `(x, y)` into the first two leaf slots `(D, D)` of a depth profile
`D :: D :: es` (`∀ d ∈ es, d ≤ D`) never increases `zipCost`. -/
private theorem exists_perm_tail_zipCost_le {γ β : Type*} [AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β] (W : γ → β) {x y : γ} {F_rest : List γ}
    {u v : γ} {tail : List γ} {D : ℕ} {es : List ℕ}
    (hperm : (x :: y :: F_rest).Perm (u :: v :: tail))
    (hmin : ∀ z ∈ F_rest, W x ≤ W z ∧ W y ≤ W z)
    (hlen : tail.length = es.length)
    (hD : ∀ d ∈ es, d ≤ D) :
    ∃ tail' : List γ, tail'.Perm F_rest ∧
      zipCost W (x :: y :: tail') (D :: D :: es) ≤
        zipCost W (u :: v :: tail) (D :: D :: es) := by
  have hmin_y : ∀ z ∈ F_rest, W y ≤ W z := fun z hz => (hmin z hz).2
  rcases List.mem_cons.mp (hperm.subset List.mem_cons_self) with rfl | hx_vtail
  · exact exists_perm_tail_stepB W x y (List.Perm.cons_inv hperm) hmin_y hlen hD
  · rcases List.mem_cons.mp hx_vtail with rfl | hx_tail
    · rcases exists_perm_tail_stepB W x y
          (List.Perm.cons_inv (hperm.trans (List.Perm.swap x u tail))) hmin_y hlen hD with
        ⟨tail', htp, hle⟩
      exact ⟨tail', htp, hle.trans_eq (zipCost_swap_first_two W x u tail D es)⟩
    · rcases List.append_of_mem hx_tail with ⟨a, b, rfl⟩
      have hyF : (y :: F_rest).Perm (u :: v :: a ++ b) := List.Perm.cons_inv <|
        hperm.trans (by simpa using List.perm_middle (l₁ := u :: v :: a) (a := x) (l₂ := b))
      rcases List.mem_cons.mp (by simpa using hyF.subset List.mem_cons_self :
          y ∈ u :: (v :: a ++ b)) with rfl | hy_rest
      · have hF_perm : F_rest.Perm (v :: a ++ b) := List.Perm.cons_inv hyF
        refine ⟨a ++ v :: b, List.perm_middle.trans hF_perm.symm, ?_⟩
        rw [zipCost_swap_first_two]
        exact zipCost_swap_second_tail W y hlen hD
          (hmin v (hF_perm.symm.subset List.mem_cons_self)).1
      · rcases List.append_of_mem hy_rest with ⟨p, q, hpq⟩
        have hF_perm : F_rest.Perm (u :: p ++ q) := List.Perm.cons_inv <|
          (show (y :: F_rest).Perm (u :: (p ++ y :: q)) by simpa [hpq] using hyF).trans
            (by simpa using List.perm_middle (l₁ := u :: p) (a := y) (l₂ := q))
        have hle_head := zipCost_swap_head_tail W (p := v :: a) (q := b)
          (by simpa [List.cons_append] using hlen) (List.forall_mem_cons.mpr ⟨le_rfl, hD⟩)
          (hmin u (hF_perm.symm.subset List.mem_cons_self)).1
        have hyF_new : (y :: F_rest).Perm (v :: (a ++ u :: b)) := hyF.trans
          (((List.perm_middle (l₁ := a) (a := u) (l₂ := b)).cons v).trans
            (List.Perm.swap u v (a ++ b))).symm
        rcases exists_perm_tail_stepB W x y hyF_new hmin_y (by simpa using hlen) hD with
          ⟨tail', htp, hle_B⟩
        exact ⟨tail', htp, le_trans hle_B (by simpa [List.cons_append] using hle_head)⟩

/-! ## Maximum-depth leftward rotation, relabeling, and cherry contraction -/

/-- Rotate deeper subtrees to the left so that the leftmost spine ends in a sibling cherry at depth
`T.maxDepth`. -/
def rotateDeepestLeft {δ : Type*} : CodeTree δ → CodeTree δ
  | .leaf a => .leaf a
  | .branch l r =>
    if r.maxDepth ≤ l.maxDepth then
      .branch (rotateDeepestLeft l) r
    else
      .branch (rotateDeepestLeft r) l

@[simp] theorem maxDepth_rotateDeepestLeft {δ : Type*} (T : CodeTree δ) :
    (rotateDeepestLeft T).maxDepth = T.maxDepth := by
  induction T with
  | leaf _ => rfl
  | branch l r ihl ihr =>
    simp only [rotateDeepestLeft]
    split_ifs <;> simp [CodeTree.maxDepth, ihl, ihr, Nat.max_comm]

theorem leaves_rotateDeepestLeft_perm {δ : Type*} (T : CodeTree δ) :
    (rotateDeepestLeft T).leaves.Perm T.leaves := by
  induction T with
  | leaf _ => exact List.Perm.refl _
  | branch l r ihl ihr =>
    simp only [rotateDeepestLeft]
    split_ifs
    · exact ihl.append (List.Perm.refl _)
    · exact (ihr.append (List.Perm.refl _)).trans List.perm_append_comm

theorem weightedPathLength_rotateDeepestLeft {δ β : Type*} [AddCommMonoid β]
    (W : δ → β) (T : CodeTree δ) :
    (rotateDeepestLeft T).weightedPathLength W = T.weightedPathLength W := by
  induction T with
  | leaf _ => rfl
  | branch l r ihl ihr =>
    have hwl := CodeTree.weight_eq_of_leaves_perm W (leaves_rotateDeepestLeft_perm l)
    have hwr := CodeTree.weight_eq_of_leaves_perm W (leaves_rotateDeepestLeft_perm r)
    simp only [rotateDeepestLeft]
    split_ifs
    · simp only [CodeTree.weightedPathLength_branch, ihl, hwl]
    · simp only [CodeTree.weightedPathLength_branch, ihr, hwr]
      ac_rfl

/-- `LeftCherryAtDepth T D u v C` witnesses that `T` has the sibling cherry
`.branch (.leaf u) (.leaf v)` at depth `D` along its leftmost spine, with contraction context `C`
replacing that cherry by `.leaf z`. -/
inductive LeftCherryAtDepth {δ : Type*} :
    CodeTree δ → ℕ → δ → δ → (δ → CodeTree δ) → Prop
  | base (u v : δ) :
      LeftCherryAtDepth (.branch (.leaf u) (.leaf v)) 1 u v (fun z => .leaf z)
  | left {l r : CodeTree δ} {d : ℕ} {u v : δ} {C : δ → CodeTree δ} :
      LeftCherryAtDepth l d u v C →
      LeftCherryAtDepth (.branch l r) (d + 1) u v (fun z => .branch (C z) r)

private theorem map_snd_map_succ {δ : Type*} (L : List (δ × ℕ)) :
    (L.map fun p => (p.1, p.2 + 1)).map Prod.snd = (L.map Prod.snd).map (· + 1) := by
  simp [List.map_map, Function.comp_def]

theorem exists_leftCherryAtDepth_rotateDeepestLeft {δ : Type*} (l r : CodeTree δ) :
    ∃ u v C, LeftCherryAtDepth (rotateDeepestLeft (CodeTree.branch l r))
      (CodeTree.branch l r).maxDepth u v C := by
  suffices h : ∀ T : CodeTree δ, 1 ≤ T.maxDepth →
      ∃ u v C, LeftCherryAtDepth (rotateDeepestLeft T) T.maxDepth u v C from
    h (.branch l r) (by simp [CodeTree.maxDepth])
  intro T h1
  have hstep : ∀ {a b : CodeTree δ}, b.maxDepth ≤ a.maxDepth →
      (1 ≤ a.maxDepth → ∃ u v C, LeftCherryAtDepth (rotateDeepestLeft a) a.maxDepth u v C) →
      ∃ u v C, LeftCherryAtDepth (.branch (rotateDeepestLeft a) b)
        (CodeTree.branch a b).maxDepth u v C := by
    intro a b hab iha
    cases a with
    | leaf u =>
      cases b with
      | leaf v =>
        exact ⟨u, v, .leaf, by
          simpa [rotateDeepestLeft, CodeTree.maxDepth] using LeftCherryAtDepth.base u v⟩
      | branch _ _ => simp [CodeTree.maxDepth] at hab
    | branch a₁ a₂ =>
      rcases iha (by simp [CodeTree.maxDepth]) with ⟨u, v, C, hC⟩
      have hd : (CodeTree.branch a₁ a₂).maxDepth + 1 =
          (CodeTree.branch (.branch a₁ a₂) b).maxDepth := by
        simp only [CodeTree.maxDepth] at hab ⊢
        omega
      exact ⟨u, v, fun z => .branch (C z) b, hd ▸ LeftCherryAtDepth.left hC⟩
  induction T with
  | leaf _ => simp [CodeTree.maxDepth] at h1
  | branch l r ihl ihr =>
    simp only [rotateDeepestLeft]
    split_ifs with hcmp
    · exact hstep hcmp ihl
    · have hcomm : (CodeTree.branch l r).maxDepth = (CodeTree.branch r l).maxDepth := by
        simp [CodeTree.maxDepth, Nat.max_comm]
      exact hcomm ▸ hstep (by omega) ihr

theorem LeftCherryAtDepth.leaves_and_depths {δ : Type*} {T : CodeTree δ} {D : ℕ} {u v : δ}
    {C : δ → CodeTree δ} (h : LeftCherryAtDepth T D u v C) :
    ∃ tail ds,
      T.leaves = u :: v :: tail ∧
      (∀ z, (C z).leaves = z :: tail) ∧
      T.leafDepths.map Prod.snd = D :: D :: ds ∧
      tail.length = ds.length := by
  induction h with
  | base u v =>
    exact ⟨[], [], rfl, fun _ => rfl, rfl, rfl⟩
  | @left l r d u v C _ ih =>
    rcases ih with ⟨tail_l, ds_l, hl_leaves, hC_leaves, hl_depths, hlen_l⟩
    refine ⟨tail_l ++ r.leaves,
      ds_l.map (· + 1) ++ (r.leafDepths.map Prod.snd).map (· + 1), ?_, fun z => ?_, ?_, ?_⟩
    · simp [hl_leaves]
    · simp [hC_leaves z]
    · simp only [CodeTree.leafDepths, List.map_append, map_snd_map_succ, hl_depths, List.map_cons,
        List.cons_append]
    · have hr_len : r.leaves.length = (r.leafDepths.map Prod.snd).length := by
        rw [List.length_map, ← CodeTree.map_fst_leafDepths r, List.length_map]
      simp [hlen_l, hr_len]

/-- Relabel the leaves of `T` left-to-right from `as`, returning the relabeled tree and unconsumed
suffix of `as`. -/
private def relabel {δ γ : Type*} (fb : γ) : CodeTree δ → List γ → CodeTree γ × List γ
  | .leaf _, [] => (.leaf fb, [])
  | .leaf _, a :: as => (.leaf a, as)
  | .branch l r, as =>
    let res₁ := relabel fb l as
    let res₂ := relabel fb r res₁.2
    (.branch res₁.1 res₂.1, res₂.2)

private theorem relabel_append_spec {δ γ : Type*} (fb : γ) (T : CodeTree δ)
    {xs ys : List γ} (hlen : xs.length = T.leaves.length) :
    relabel fb T (xs ++ ys) = ((relabel fb T xs).1, ys) ∧
      (relabel fb T xs).1.leaves = xs ∧
      (relabel fb T xs).1.leafDepths = xs.zip (T.leafDepths.map Prod.snd) := by
  induction T generalizing xs ys with
  | leaf _ =>
    rcases xs with _ | ⟨x, _ | ⟨_, _⟩⟩
    · simp at hlen
    · simp [relabel, CodeTree.leafDepths]
    · simp at hlen
  | branch l r ihl ihr =>
    simp only [CodeTree.leaves_branch, List.length_append] at hlen
    let xs₁ := xs.take l.leaves.length
    let xs₂ := xs.drop l.leaves.length
    have hxs_split : xs = xs₁ ++ xs₂ := (List.take_append_drop l.leaves.length xs).symm
    have hlen₁ : xs₁.length = l.leaves.length := by simp only [xs₁, List.length_take]; omega
    have hlen₂ : xs₂.length = r.leaves.length := by simp only [xs₂, List.length_drop]; omega
    rcases ihl (ys := xs₂ ++ ys) hlen₁ with ⟨hl_app_ys, hl_leaves, hl_depths⟩
    rcases ihl (ys := xs₂) hlen₁ with ⟨hl_app, _, _⟩
    rcases ihr (ys := ys) hlen₂ with ⟨hr_app_ys, hr_leaves, hr_depths⟩
    have hbr_xs : (relabel fb (.branch l r) xs).1 =
        .branch (relabel fb l xs₁).1 (relabel fb r xs₂).1 := by
      rw [hxs_split]; simp only [relabel, hl_app]
    refine ⟨?_, ?_, ?_⟩
    · rw [hbr_xs, hxs_split, List.append_assoc]; simp only [relabel, hl_app_ys, hr_app_ys]
    · rw [hbr_xs, CodeTree.leaves_branch, hl_leaves, hr_leaves, ← hxs_split]
    · have hzip_succ : ∀ (us : List γ) (ds : List ℕ),
          (us.zip ds).map (fun p => (p.1, p.2 + 1)) = us.zip (ds.map (· + 1)) := by
        intro us; induction us with
        | nil => simp
        | cons u us ihu => intro ds; cases ds <;> simp [ihu]
      have hdl_len : xs₁.length = ((l.leafDepths.map Prod.snd).map (· + 1)).length := by
        rw [List.length_map, List.length_map, hlen₁, ← CodeTree.map_fst_leafDepths l,
          List.length_map]
      rw [hbr_xs, CodeTree.leafDepths, hl_depths, hr_depths, hxs_split]
      simp only [CodeTree.leafDepths, List.map_append, map_snd_map_succ, hzip_succ,
        List.zip_append hdl_len]

private theorem LeftCherryAtDepth.relabel_spec {δ γ : Type*} {T : CodeTree δ} {D : ℕ} {u v : δ}
    {C : δ → CodeTree δ} (h : LeftCherryAtDepth T D u v C)
    (x y : γ) {rest : List γ} (hlen : (x :: y :: rest).length = T.leaves.length) :
    ∃ C' : γ → CodeTree γ,
      LeftCherryAtDepth (relabel x T (x :: y :: rest)).1 D x y C' ∧
      ∀ z, (C' z).leaves = z :: rest := by
  induction h generalizing rest with
  | base u v =>
    cases rest with
    | nil => exact ⟨.leaf, by simpa [relabel] using LeftCherryAtDepth.base x y, fun _ => rfl⟩
    | cons _ _ => simp at hlen
  | @left l r d u v C hl ih =>
    rcases hl.leaves_and_depths with ⟨tail_l, _, hl_leaves, _, _, _⟩
    simp only [CodeTree.leaves_branch, hl_leaves, List.cons_append, List.length_cons,
      List.length_append, Nat.succ.injEq] at hlen
    let rest₁ := rest.take tail_l.length
    let rest₂ := rest.drop tail_l.length
    have hrest_split : rest = rest₁ ++ rest₂ := (List.take_append_drop tail_l.length rest).symm
    have hlen₁ : (x :: y :: rest₁).length = l.leaves.length := by
      rw [hl_leaves]; simp only [rest₁, List.length_cons, List.length_take]; omega
    have hlen₂ : rest₂.length = r.leaves.length := by
      simp only [rest₂, List.length_drop]; omega
    rcases relabel_append_spec x l (xs := x :: y :: rest₁) (ys := rest₂) hlen₁ with ⟨hl_app, _, _⟩
    rcases relabel_append_spec x r (xs := rest₂) (ys := []) hlen₂ with ⟨_, hr_leaves, _⟩
    rcases ih hlen₁ with ⟨C'_l, hC'_l, hC'_leaves⟩
    have hbr : (relabel x (.branch l r) (x :: y :: rest)).1 =
        .branch (relabel x l (x :: y :: rest₁)).1 (relabel x r rest₂).1 := by
      rw [show x :: y :: rest = (x :: y :: rest₁) ++ rest₂ by simp [hrest_split]]
      simp only [relabel, hl_app]
    refine ⟨fun z => .branch (C'_l z) (relabel x r rest₂).1,
      hbr ▸ LeftCherryAtDepth.left hC'_l, fun z => by simp [hC'_leaves z, hr_leaves, ← hrest_split]⟩

/-- **Greedy-Choice Exchange Lemma** ([CLRS2009], Lemma 16.2): in any full binary tree `S` whose
leaves contain a minimum-weight pair `(x, y)` (`∀ z ∈ F_rest, W x ≤ W z ∧ W y ≤ W z`), rotating and
swapping `(x, y)` into a maximum-depth sibling cherry produces a tree `S'` with the same leaf
multiset and `S'.weightedPathLength W ≤ S.weightedPathLength W`. -/
theorem exists_cherry_weightedPathLength_le {γ β : Type*}
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    (W : γ → β) {x y : γ} {F_rest : List γ} (S : CodeTree γ)
    (hperm : S.leaves.Perm (x :: y :: F_rest))
    (hmin : ∀ z ∈ F_rest, W x ≤ W z ∧ W y ≤ W z) :
    ∃ (S' : CodeTree γ) (C' : γ → CodeTree γ) (tail' : List γ),
      LeftCherryAtDepth S' S.maxDepth x y C' ∧
      S'.leaves = x :: y :: tail' ∧
      tail'.Perm F_rest ∧
      (∀ z, (C' z).leaves = z :: tail') ∧
      S'.weightedPathLength W ≤ S.weightedPathLength W := by
  cases S with
  | leaf a => have := hperm.length_eq; simp at this
  | branch l r =>
    let S₁ := rotateDeepestLeft (CodeTree.branch l r)
    rcases exists_leftCherryAtDepth_rotateDeepestLeft l r with ⟨u, v, C, hC⟩
    rcases hC.leaves_and_depths with ⟨tail, ds, hS₁_leaves, _, hS₁_depths, htail_len⟩
    have hperm₁ : (x :: y :: F_rest).Perm (u :: v :: tail) :=
      hS₁_leaves ▸ hperm.symm.trans (leaves_rotateDeepestLeft_perm (CodeTree.branch l r)).symm
    have hD_ds : ∀ d ∈ ds, d ≤ (CodeTree.branch l r).maxDepth := by
      intro d hd
      rcases List.mem_map.mp (show d ∈ S₁.leafDepths.map Prod.snd by grind) with ⟨p, hp, rfl⟩
      exact (CodeTree.snd_le_maxDepth_of_mem_leafDepths hp).trans_eq (maxDepth_rotateDeepestLeft _)
    rcases exists_perm_tail_zipCost_le W hperm₁ hmin htail_len hD_ds with ⟨tail', htail'_perm, hle⟩
    have hlen_relabel : (x :: y :: tail').length = S₁.leaves.length := by
      have := hperm₁.length_eq; have := htail'_perm.length_eq
      rw [hS₁_leaves]; simp only [List.length_cons] at *; omega
    rcases relabel_append_spec x S₁ (xs := x :: y :: tail') (ys := []) hlen_relabel with
      ⟨_, hS'_leaves, hS'_depths⟩
    rcases hC.relabel_spec x y hlen_relabel with ⟨C', hC', hC'_leaves⟩
    let S' := (relabel x S₁ (x :: y :: tail')).1
    have hS'_wpl : S'.weightedPathLength W =
        zipCost W (x :: y :: tail') ((CodeTree.branch l r).maxDepth ::
          (CodeTree.branch l r).maxDepth :: ds) := by
      rw [CodeTree.weightedPathLength_eq_sum_leafDepths, hS'_depths, hS₁_depths]; rfl
    have hS₁_wpl : S₁.weightedPathLength W =
        zipCost W (u :: v :: tail) ((CodeTree.branch l r).maxDepth ::
          (CodeTree.branch l r).maxDepth :: ds) := by
      have hzip_self : ∀ L : List (γ × ℕ), L = (L.map Prod.fst).zip (L.map Prod.snd) := by
        intro L; induction L with | nil => rfl | cons p ps ih => exact congrArg (p :: ·) ih
      rw [CodeTree.weightedPathLength_eq_sum_leafDepths, hzip_self S₁.leafDepths,
        CodeTree.map_fst_leafDepths, hS₁_leaves, hS₁_depths]
      rfl
    refine ⟨S', C', tail', hC', hS'_leaves, htail'_perm, hC'_leaves, ?_⟩
    rw [hS'_wpl, ← weightedPathLength_rotateDeepestLeft W (.branch l r), hS₁_wpl]
    exact hle

theorem LeftCherryAtDepth.weight_contract_eq {γ β : Type*} [AddCommMonoid β]
    {S : CodeTree γ} {D : ℕ} {x y : γ} {C : γ → CodeTree γ}
    (h : LeftCherryAtDepth S D x y C) (W : γ → β) {z : γ} (hz : W z = W x + W y) :
    (C z).weight W = S.weight W := by
  induction h with
  | base _ _ => exact hz
  | left _ ihl => simp [CodeTree.weight_branch, ihl hz]

/-- **Cherry-Contraction Path-Length Identity** ([CLRS2009], Lemma 16.3): contracting a sibling
cherry `(x, y)` into a single leaf `z` of weight `W z = W x + W y` shifts `weightedPathLength` by
`W x + W y`. -/
theorem LeftCherryAtDepth.weightedPathLength_eq_contract_add {γ β : Type*} [AddCommMonoid β]
    {S : CodeTree γ} {D : ℕ} {x y : γ} {C : γ → CodeTree γ}
    (h : LeftCherryAtDepth S D x y C) (W : γ → β) {z : γ} (hz : W z = W x + W y) :
    S.weightedPathLength W = (C z).weightedPathLength W + (W x + W y) := by
  induction h with
  | base _ _ => simp
  | left hl ihl =>
    simp only [CodeTree.weightedPathLength_branch, ihl hz, hl.weight_contract_eq W hz]
    ac_rfl

/-- Contracting a sibling cherry `(t₁, t₂)` in a skeleton `CodeTree (CodeTree α)` into
`.leaf (.branch t₁ t₂)` leaves `CodeTree.join` *identical*. -/
theorem LeftCherryAtDepth.join_contract_eq {α : Type*} {S : CodeTree (CodeTree α)} {D : ℕ}
    {t₁ t₂ : CodeTree α} {C : CodeTree α → CodeTree (CodeTree α)}
    (h : LeftCherryAtDepth S D t₁ t₂ C) :
    (C (.branch t₁ t₂)).join = S.join := by
  induction h with
  | base _ _ => rfl
  | left _ ih => simp [CodeTree.join, ih]

/-! ## Main optimality theorems ([CLRS2009], Theorem 16.4; [CoverThomas2006], Theorem 5.8.1) -/

/-- **Skeleton Optimality of `IsHuffmanBuild`**: for any forest `F` and any skeleton
`S : CodeTree (CodeTree α)` with `S.leaves.Perm F`, a Huffman merge tree `T` built from `F` achieves
`T.weightedPathLength w ≤ S.join.weightedPathLength w`. -/
theorem IsHuffmanBuild.weightedPathLength_le_join {α β : Type*}
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {F : List (CodeTree α)} {T : CodeTree α}
    (hbuild : IsHuffmanBuild w F T)
    (S : CodeTree (CodeTree α)) (hS : S.leaves.Perm F) :
    T.weightedPathLength w ≤ S.join.weightedPathLength w := by
  induction hbuild generalizing S with
  | single t =>
    have hEq := CodeTree.eq_leaf_of_leaves_perm_singleton hS
    subst hEq
    exact le_rfl
  | @step F F_rest t₁ t₂ T hmin _ ih =>
    let W : CodeTree α → β := fun t => t.weight w
    rcases exists_cherry_weightedPathLength_le W S (hS.trans hmin.perm) hmin.weight_le with
      ⟨S', C', tail', hC', hS'_leaves, htail'_perm, hC'_leaves, hwpl_le⟩
    have hS'_perm_S : S'.leaves.Perm S.leaves := by
      rw [hS'_leaves]
      exact (htail'_perm.cons t₂ |>.cons t₁).trans (hS.trans hmin.perm).symm
    have hjoin_le : S'.join.weightedPathLength w ≤ S.join.weightedPathLength w := by
      rw [CodeTree.weightedPathLength_join, CodeTree.weightedPathLength_join,
        (hS'_perm_S.map fun t => t.weightedPathLength w).sum_eq]
      exact add_le_add hwpl_le le_rfl
    let S_c := C' (.branch t₁ t₂)
    have hSc_perm : S_c.leaves.Perm (.branch t₁ t₂ :: F_rest) := by
      rw [hC'_leaves]
      exact htail'_perm.cons (.branch t₁ t₂)
    have hih := ih S_c hSc_perm
    rw [hC'.join_contract_eq] at hih
    exact le_trans hih hjoin_le

/-- **Optimality of Huffman Coding over Full Binary Code Trees** ([Huffman1952]; [CLRS2009],
Theorem 16.4): every tree `T` produced by `IsHuffmanBuild w (syms.map .leaf) T` minimizes
`weightedPathLength w` over all full binary trees `T'` whose leaf multiset is a permutation of
`syms`. -/
theorem IsHuffmanBuild.weightedPathLength_le {α β : Type*}
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {syms : List α} {T : CodeTree α}
    (hbuild : IsHuffmanBuild w (syms.map .leaf) T)
    (T' : CodeTree α) (hT' : T'.leaves.Perm syms) :
    T.weightedPathLength w ≤ T'.weightedPathLength w := by
  have hS : (T'.map CodeTree.leaf).leaves.Perm (syms.map CodeTree.leaf) := by
    grind [CodeTree.leaves_map]
  have hle := hbuild.weightedPathLength_le_join (T'.map CodeTree.leaf) hS
  rwa [CodeTree.join_map_leaf] at hle

/-- **Optimality of Huffman Coding over Prefix-Free Binary Codes** ([Huffman1952];
[CoverThomas2006], Section 5.8): under nonnegative symbol weights, a Huffman tree `T` achieves
weighted path length at most the weighted codeword length of *any* injective
`InformationTheory.IsPrefixFree` binary code on `syms`. -/
theorem IsHuffmanBuild.weightedPathLength_le_of_isPrefixFree {α β : Type*}
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {syms : List α} (hne : syms ≠ []) (hnodup : syms.Nodup)
    {w : α → β} (hw : ∀ a ∈ syms, 0 ≤ w a)
    {T : CodeTree α} (hbuild : IsHuffmanBuild w (syms.map .leaf) T)
    {code : α → List Bool}
    (hinj : Set.InjOn code {a | a ∈ syms})
    (hpf : InformationTheory.IsPrefixFree (code '' {a | a ∈ syms})) :
    T.weightedPathLength w ≤ (syms.map fun a => (code a).length • w a).sum := by
  rcases exists_codeTree_of_isPrefixFree hne hnodup hinj hpf hw with ⟨T', hperm, hwpl⟩
  exact le_trans (hbuild.weightedPathLength_le T' hperm) hwpl

/-- **Optimality of Huffman Coding over All Uniquely Decodable Binary Codes** ([McMillan1956];
[CoverThomas2006], Theorem 5.8.1 specialized to binary alphabet `Bool`, $D = 2$, and generalized to
arbitrary ordered additive commutative monoid weights `β`): under nonnegative symbol weights, a
Huffman tree `T` achieves weighted path length at most the weighted codeword length of *any*
injective `InformationTheory.IsUniquelyDecodable` binary code on `syms`. -/
theorem IsHuffmanBuild.weightedPathLength_le_of_isUniquelyDecodable {α β : Type*}
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {syms : List α} (hne : syms ≠ []) (hnodup : syms.Nodup)
    {w : α → β} (hw : ∀ a ∈ syms, 0 ≤ w a)
    {T : CodeTree α} (hbuild : IsHuffmanBuild w (syms.map .leaf) T)
    {code : α → List Bool}
    (hinj : Set.InjOn code {a | a ∈ syms})
    (hud : InformationTheory.IsUniquelyDecodable (code '' {a | a ∈ syms})) :
    T.weightedPathLength w ≤ (syms.map fun a => (code a).length • w a).sum := by
  rcases exists_codeTree_of_isUniquelyDecodable hne hnodup hinj hud hw with ⟨T', hperm, hwpl⟩
  exact le_trans (hbuild.weightedPathLength_le T' hperm) hwpl

end Cslib.Algorithms.Lean.Huffman
