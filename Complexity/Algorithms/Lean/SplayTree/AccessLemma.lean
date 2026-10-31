/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.SplayTree.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Sleator–Tarjan's Access Lemma, Static Optimality, and Update Bounds

This module formalizes the potential-method amortized analysis of self-adjusting splay trees due to
Sleator and Tarjan ([SleatorTarjan1985b], Sections 2–3, pp. 656–665).

Given any positive weight assignment `w : α → ℝ` (`∀ x, 0 < w x` — a purely analytical parameter
not stored in the tree), each subtree `t` has size `subtreeWeight w t`, binary-logarithm rank
`nodeRank w t = Real.logb 2 (subtreeWeight w t)` ([SleatorTarjan1985b], Section 2, p. 658,
Footnote 1), and tree potential `potential w t` summing `nodeRank w` over all internal subtrees of
`t`. Following [SleatorTarjan1985b], Section 2, p. 658, `splayTime res = max res.rotations 1`
charges one unit when no rotations occur and the exact rotation count otherwise.

## Main definitions

* `subtreeWeight`, `nodeRank`, `potential`: parameterized subtree weight, base-2 logarithmic node
  rank, and rank-sum potential ([SleatorTarjan1985b], Section 2, p. 658).
* `splayTime`, `splaySeq`, `splaySeqTime`, `splaySeqRotations`: single-splay and multi-access
  sequence cost measures.
* `unitWeight`, `unitPotential`: unit-weight specialization (`w = fun _ => 1`) used for the
  Balance Theorem and dynamic dictionary updates ([SleatorTarjan1985b], Section 2, Theorem 1,
  p. 659; Section 3, Lemma 2 and Theorem 6, pp. 663–665).

## Main results

* `splayUp_amortized_le`, `splay_splayTime_amortized_le`, `exists_mem_splay_splayTime_amortized_le`,
  `splay_splayTime_amortized_le_of_mem`: Sleator and Tarjan's **Access Lemma**
  ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658).
* `potential_sub_potential_le_sum_logb`: fixed-weight net potential drop bound
  `Φ(t₁) - Φ(t₂) ≤ ∑_{y ∈ t₁} log₂(W / w(y))` ([SleatorTarjan1985b], Section 2, p. 659).
* `splaySeqTime_le_balance`: **Balance Theorem** ([SleatorTarjan1985b], Section 2, Theorem 1,
  p. 659), bounding any sequence of `m` accesses (present or absent) on an `n`-element splay tree
  by `(3m + n) log₂ n + m`.
* `splaySeqTime_le_static_optimality`: **Static Optimality Theorem** ([SleatorTarjan1985b],
  Section 2, Theorem 2, p. 659), bounding `m` accesses to present items (each accessed at least
  once) by `m + 4 ∑_{y ∈ t} q(y) log₂(m / q(y))`.
* `contains_unitPotential_amortized_le`, `split_unitPotential_amortized_le`,
  `join_unitPotential_amortized_le`, `insert_unitPotential_amortized_le`,
  `erase_unitPotential_amortized_le`: unit-weight (`w = 1`) specialization of Sleator and Tarjan's
  **Update Lemma** ([SleatorTarjan1985b], Section 3, Lemma 2, pp. 663–664, where `log₂ 1 = 0`
  eliminates Lemma 2's external-item potential term), extended to total set-idempotent `insert`
  and `erase`.
* `minimum_unitPotential_amortized_le`, `successor_unitPotential_amortized_le`: companion
  unit-weight rotation bounds derived from the Access Lemma ([SleatorTarjan1985b], Section 2,
  Lemma 1, p. 658) for `Cslib.OrderedSet.spec` (`minimum` and `successor` are not part of
  Lemma 2).

## References

* [SleatorTarjan1985b] Daniel Dominic Sleator and Robert Endre Tarjan,
  *Self-Adjusting Binary Search Trees*, Journal of the ACM 32(3), Sections 2–3, pp. 656–665, 1985.
-/

public section

namespace Cslib.Algorithms.Lean.SplayTree

open Cslib.Algorithms.Lean.SearchTree (elements Ordered mem_elements_node card_elements)

/-! ### Subtree Weights, Node Ranks, and Rank-Sum Potential -/

section Weights

variable {α : Type*}

/-- Sum of item weights `w` over all internal nodes of a `BinaryTree α`
(`s(x)` in [SleatorTarjan1985b], Section 2, p. 658). -/
@[expose] noncomputable def subtreeWeight (w : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node a l r => w a + subtreeWeight w l + subtreeWeight w r

@[simp] theorem subtreeWeight_nil (w : α → ℝ) : subtreeWeight w (.nil : BinaryTree α) = 0 := rfl

@[simp] theorem subtreeWeight_node (w : α → ℝ) (a : α) (l r : BinaryTree α) :
    subtreeWeight w (.node a l r) = w a + subtreeWeight w l + subtreeWeight w r := rfl

theorem subtreeWeight_nonneg {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (t : BinaryTree α) :
    0 ≤ subtreeWeight w t := by
  induction t with
  | nil => exact le_rfl
  | node a l r ihl ihr =>
    have ha := hw a
    simp only [subtreeWeight_node]
    linarith

theorem subtreeWeight_pos {w : α → ℝ} (hw : ∀ x, 0 < w x) {t : BinaryTree α} (ht : t ≠ .nil) :
    0 < subtreeWeight w t := by
  cases t with
  | nil => exact (ht rfl).elim
  | node a l r =>
    have ha := hw a
    have hl := subtreeWeight_nonneg (fun x => (hw x).le) l
    have hr := subtreeWeight_nonneg (fun x => (hw x).le) r
    simp only [subtreeWeight_node]
    linarith

theorem subtreeWeight_plug_congr (w : α → ℝ) {t₁ t₂ : BinaryTree α} (ctx : List (Frame α))
    (h : subtreeWeight w t₁ = subtreeWeight w t₂) :
    subtreeWeight w (plug t₁ ctx) = subtreeWeight w (plug t₂ ctx) := by
  induction ctx generalizing t₁ t₂ with
  | nil => exact h
  | cons f ctx ih =>
    cases f with
    | left p r =>
      apply ih
      simp only [subtreeWeight_node, h]
    | right l p =>
      apply ih
      simp only [subtreeWeight_node, h]

theorem le_subtreeWeight_plug {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (t : BinaryTree α)
    (ctx : List (Frame α)) :
    subtreeWeight w t ≤ subtreeWeight w (plug t ctx) := by
  induction ctx generalizing t with
  | nil => exact le_rfl
  | cons f ctx ih =>
    cases f with
    | left p r =>
      have hp := hw p
      have hr := subtreeWeight_nonneg hw r
      have hstep : subtreeWeight w t ≤ subtreeWeight w (.node p t r) := by
        simp only [subtreeWeight_node]; linarith
      exact hstep.trans (ih (.node p t r))
    | right l p =>
      have hp := hw p
      have hl := subtreeWeight_nonneg hw l
      have hstep : subtreeWeight w t ≤ subtreeWeight w (.node p l t) := by
        simp only [subtreeWeight_node]; linarith
      exact hstep.trans (ih (.node p l t))

theorem subtreeWeight_splayUp (w : α → ℝ) (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    subtreeWeight w (splayUp x l r ctx).tree = subtreeWeight w (plug (.node x l r) ctx) := by
  induction l, r, ctx using splayUp.induct x with
  | case1 => rfl
  | case2 l r p c =>
    simp only [splayUp, plug_left, plug_nil, subtreeWeight_node]
    ring
  | case3 l r c p =>
    simp only [splayUp, plug_right, plug_nil, subtreeWeight_node]
    ring
  | case4 l r p c g d ctx ih =>
    simp only [splayUp, plug_left]
    rw [ih]
    apply subtreeWeight_plug_congr
    simp only [subtreeWeight_node]
    ring
  | case5 l r c p d g ctx ih =>
    simp only [splayUp, plug_right]
    rw [ih]
    apply subtreeWeight_plug_congr
    simp only [subtreeWeight_node]
    ring
  | case6 l r a p g d ctx ih =>
    simp only [splayUp, plug_right, plug_left]
    rw [ih]
    apply subtreeWeight_plug_congr
    simp only [subtreeWeight_node]
    ring
  | case7 l r p c d g ctx ih =>
    simp only [splayUp, plug_left, plug_right]
    rw [ih]
    apply subtreeWeight_plug_congr
    simp only [subtreeWeight_node]
    ring

@[simp] theorem subtreeWeight_splayMin (w : α → ℝ) (t : BinaryTree α) :
    subtreeWeight w (splayMin t).tree = subtreeWeight w t := by
  simp only [splayMin]
  cases hf : focusMin t [] with
  | none => simp [(focusMin_eq_none_iff t []).mp hf]
  | some f =>
    have htree := (focusMin_spec hf).1
    rw [subtreeWeight_splayUp]
    simpa only [Focus.toTree, Focus.sub, plug_nil] using congrArg (subtreeWeight w) htree

@[simp] theorem subtreeWeight_splayMax (w : α → ℝ) (t : BinaryTree α) :
    subtreeWeight w (splayMax t).tree = subtreeWeight w t := by
  simp only [splayMax]
  cases hf : focusMax t [] with
  | none => simp [(focusMax_eq_none_iff t []).mp hf]
  | some f =>
    have htree := (focusMax_spec hf).1
    rw [subtreeWeight_splayUp]
    simpa only [Focus.toTree, Focus.sub, plug_nil] using congrArg (subtreeWeight w) htree

/-- Base-2 logarithmic rank `r(x) = log₂ s(x)` of a subtree ([SleatorTarjan1985b], Section 2,
p. 658, Footnote 1). -/
@[expose] noncomputable def nodeRank (w : α → ℝ) (t : BinaryTree α) : ℝ :=
  Real.logb 2 (subtreeWeight w t)

@[simp] theorem nodeRank_nil (w : α → ℝ) : nodeRank w (.nil : BinaryTree α) = 0 := by
  simp [nodeRank]

theorem nodeRank_congr {w : α → ℝ} {t₁ t₂ : BinaryTree α}
    (h : subtreeWeight w t₁ = subtreeWeight w t₂) :
    nodeRank w t₁ = nodeRank w t₂ := by
  simp only [nodeRank, h]

theorem nodeRank_mono {w : α → ℝ} {t₁ t₂ : BinaryTree α}
    (hpos : 0 < subtreeWeight w t₁) (hle : subtreeWeight w t₁ ≤ subtreeWeight w t₂) :
    nodeRank w t₁ ≤ nodeRank w t₂ :=
  Real.logb_le_logb_of_le (by norm_num) hpos hle

/-- Sleator–Tarjan potential `Φ(t) = ∑_x r(x)` summing `nodeRank w` over all internal subtrees of
`t` ([SleatorTarjan1985b], Section 2, p. 658). -/
@[expose] noncomputable def potential (w : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node a l r => nodeRank w (.node a l r) + potential w l + potential w r

@[simp] theorem potential_nil (w : α → ℝ) : potential w (.nil : BinaryTree α) = 0 := rfl

@[simp] theorem potential_node (w : α → ℝ) (a : α) (l r : BinaryTree α) :
    potential w (.node a l r) = nodeRank w (.node a l r) + potential w l + potential w r := rfl

/-- Local restructurings that preserve `subtreeWeight` leave the ranks of all proper ancestors in
`ctx` unchanged, so the global potential difference equals the local potential difference. -/
theorem potential_plug_sub_eq (w : α → ℝ) {t₁ t₂ : BinaryTree α} (ctx : List (Frame α))
    (hsw : subtreeWeight w t₁ = subtreeWeight w t₂) :
    potential w (plug t₁ ctx) - potential w (plug t₂ ctx) =
      potential w t₁ - potential w t₂ := by
  induction ctx generalizing t₁ t₂ with
  | nil => rfl
  | cons f ctx ih =>
    cases f with
    | left p r =>
      have hsw' : subtreeWeight w (.node p t₁ r) = subtreeWeight w (.node p t₂ r) := by
        simp only [subtreeWeight_node, hsw]
      simp only [plug_left]
      rw [ih hsw']
      have hrk : nodeRank w (.node p t₁ r) = nodeRank w (.node p t₂ r) := nodeRank_congr hsw'
      simp only [potential_node, hrk]
      ring
    | right l p =>
      have hsw' : subtreeWeight w (.node p l t₁) = subtreeWeight w (.node p l t₂) := by
        simp only [subtreeWeight_node, hsw]
      simp only [plug_right]
      rw [ih hsw']
      have hrk : nodeRank w (.node p l t₁) = nodeRank w (.node p l t₂) := nodeRank_congr hsw'
      simp only [potential_node, hrk]
      ring

/-- Sleator–Tarjan running-time measure for a single splay ([SleatorTarjan1985b], Section 2,
p. 658): the number of rotations performed, or `1` when zero rotations are performed. -/
@[expose] def splayTime (res : SplayResult α) : ℕ :=
  max res.rotations 1

theorem rotations_le_splayTime (res : SplayResult α) : res.rotations ≤ splayTime res :=
  le_max_left _ _

theorem one_le_splayTime (res : SplayResult α) : 1 ≤ splayTime res :=
  le_max_right _ _

/-! ### Elementary AM-GM Binary-Logarithm Inequality and Bottom-Up Access Lemma -/

/-- Elementary AM-GM inequality in base-2 logarithms: for `0 < a`, `0 < b`, and `a + b ≤ s`,
`2 + log₂ a + log₂ b ≤ 2 log₂ s` ([SleatorTarjan1985b], Section 2, proof of Lemma 1, p. 658). -/
private theorem two_add_logb_two_add_le {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ s) :
    2 + Real.logb 2 a + Real.logb 2 b ≤ 2 * Real.logb 2 s := by
  have h1 : 0 ≤ (s - (a + b)) * (s + a + b) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have hsq : 4 * (a * b) ≤ s ^ 2 := by nlinarith
  have hlog : Real.logb 2 (4 * (a * b)) ≤ Real.logb 2 (s ^ 2) :=
    Real.logb_le_logb_of_le (by norm_num) (mul_pos (by norm_num) (mul_pos ha hb)) hsq
  have h4 : Real.logb 2 4 = 2 := by
    have hpow : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [hpow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_mul (by norm_num) (mul_ne_zero ha.ne' hb.ne'),
    Real.logb_mul ha.ne' hb.ne', h4, Real.logb_pow] at hlog
  norm_num at hlog
  linarith

/-- **Bottom-Up Access Lemma** ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658):
for any positive weights `w`, bottom-up splaying of `(x, l, r)` through `ctx` has amortized
rotation cost at most `3 (r(root) - r(u))` when `ctx = []` and at most `3 (r(root) - r(u)) + 1`
when `ctx ≠ []`. -/
theorem splayUp_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    ((splayUp x l r ctx).rotations : ℝ) +
        potential w (splayUp x l r ctx).tree - potential w (plug (.node x l r) ctx) ≤
      3 * (nodeRank w (plug (.node x l r) ctx) - nodeRank w (.node x l r)) +
        if ctx.isEmpty then 0 else 1 := by
  have hw0 : ∀ y, 0 ≤ w y := fun y => (hw y).le
  induction l, r, ctx using splayUp.induct x with
  | case1 l r =>
    simp [splayUp]
  | case2 l r p c =>
    -- Terminal zig (left child of root)
    simp only [splayUp, plug_left, plug_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_one]
    set u₀ : BinaryTree α := .node x l r
    set t₀ : BinaryTree α := .node p u₀ c
    set p₁ : BinaryTree α := .node p r c
    set t₁ : BinaryTree α := .node x l p₁
    have hsw_eq : subtreeWeight w t₁ = subtreeWeight w t₀ := by
      simp only [t₁, p₁, t₀, u₀, subtreeWeight_node]; ring
    have hr_eq : nodeRank w t₁ = nodeRank w t₀ := nodeRank_congr hsw_eq
    have hp₁_le : nodeRank w p₁ ≤ nodeRank w t₀ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [p₁]))
      have hx := hw x
      have hl := subtreeWeight_nonneg hw0 l
      simp only [p₁, t₀, u₀, subtreeWeight_node]; linarith
    have hu₀_le : nodeRank w u₀ ≤ nodeRank w t₀ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [u₀]))
      have hp := hw p
      have hc := subtreeWeight_nonneg hw0 c
      simp only [u₀, t₀, subtreeWeight_node]; linarith
    simp only [t₁, p₁, t₀, u₀, potential_node] at hr_eq hp₁_le hu₀_le ⊢
    linarith
  | case3 l r c p =>
    -- Terminal zig (right child of root)
    simp only [splayUp, plug_right, plug_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_one]
    set u₀ : BinaryTree α := .node x l r
    set t₀ : BinaryTree α := .node p c u₀
    set p₁ : BinaryTree α := .node p c l
    set t₁ : BinaryTree α := .node x p₁ r
    have hsw_eq : subtreeWeight w t₁ = subtreeWeight w t₀ := by
      simp only [t₁, p₁, t₀, u₀, subtreeWeight_node]; ring
    have hr_eq : nodeRank w t₁ = nodeRank w t₀ := nodeRank_congr hsw_eq
    have hp₁_le : nodeRank w p₁ ≤ nodeRank w t₀ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [p₁]))
      have hx := hw x
      have hr := subtreeWeight_nonneg hw0 r
      simp only [p₁, t₀, u₀, subtreeWeight_node]; linarith
    have hu₀_le : nodeRank w u₀ ≤ nodeRank w t₀ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [u₀]))
      have hp := hw p
      have hc := subtreeWeight_nonneg hw0 c
      simp only [u₀, t₀, subtreeWeight_node]; linarith
    simp only [t₁, p₁, t₀, u₀, potential_node] at hr_eq hp₁_le hu₀_le ⊢
    linarith
  | case4 l r p c g d ctx ih =>
    -- Zig-zig (left-left)
    simp only [splayUp, plug_left, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Nat.cast_add,
      Nat.cast_ofNat]
    set u₀ : BinaryTree α := .node x l r
    set p₀ : BinaryTree α := .node p u₀ c
    set g₀ : BinaryTree α := .node g p₀ d
    set g₁ : BinaryTree α := .node g c d
    set p₁ : BinaryTree α := .node p r g₁
    set u₁ : BinaryTree α := .node x l p₁
    have hsw_local : subtreeWeight w u₁ = subtreeWeight w g₀ := by
      simp only [u₁, p₁, g₁, g₀, p₀, u₀, subtreeWeight_node]; ring
    have hsw_root : subtreeWeight w (plug u₁ ctx) = subtreeWeight w (plug g₀ ctx) :=
      subtreeWeight_plug_congr w ctx hsw_local
    have hr_root : nodeRank w (plug u₁ ctx) = nodeRank w (plug g₀ ctx) := nodeRank_congr hsw_root
    have hr_local : nodeRank w u₁ = nodeRank w g₀ := nodeRank_congr hsw_local
    have hpot_plug : potential w (plug u₁ ctx) - potential w (plug g₀ ctx) =
        potential w u₁ - potential w g₀ := potential_plug_sub_eq w ctx hsw_local
    have hlog : 2 + nodeRank w u₀ + nodeRank w g₁ ≤ 2 * nodeRank w u₁ := by
      apply two_add_logb_two_add_le
        (subtreeWeight_pos hw (by simp [u₀]))
        (subtreeWeight_pos hw (by simp [g₁]))
      have hp := hw p
      simp only [u₀, g₁, u₁, p₁, subtreeWeight_node]; linarith
    have hp₁_le : nodeRank w p₁ ≤ nodeRank w u₁ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [p₁]))
      have hx := hw x
      have hl := subtreeWeight_nonneg hw0 l
      simp only [p₁, u₁, subtreeWeight_node]; linarith
    have hu₀_le_p₀ : nodeRank w u₀ ≤ nodeRank w p₀ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [u₀]))
      have hp := hw p
      have hc := subtreeWeight_nonneg hw0 c
      simp only [u₀, p₀, subtreeWeight_node]; linarith
    have hstep : 2 + potential w u₁ - potential w g₀ ≤ 3 * (nodeRank w u₁ - nodeRank w u₀) := by
      simp only [u₁, p₁, g₁, g₀, p₀, u₀, potential_node] at hr_local hlog hp₁_le hu₀_le_p₀ ⊢
      linarith
    have hite : (if ctx.isEmpty then (0 : ℝ) else 1) ≤ 1 := by split <;> norm_num
    linarith [ih]
  | case5 l r c p d g ctx ih =>
    -- Zig-zig (right-right)
    simp only [splayUp, plug_right, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Nat.cast_add,
      Nat.cast_ofNat]
    set u₀ : BinaryTree α := .node x l r
    set p₀ : BinaryTree α := .node p c u₀
    set g₀ : BinaryTree α := .node g d p₀
    set g₁ : BinaryTree α := .node g d c
    set p₁ : BinaryTree α := .node p g₁ l
    set u₁ : BinaryTree α := .node x p₁ r
    have hsw_local : subtreeWeight w u₁ = subtreeWeight w g₀ := by
      simp only [u₁, p₁, g₁, g₀, p₀, u₀, subtreeWeight_node]; ring
    have hsw_root : subtreeWeight w (plug u₁ ctx) = subtreeWeight w (plug g₀ ctx) :=
      subtreeWeight_plug_congr w ctx hsw_local
    have hr_root : nodeRank w (plug u₁ ctx) = nodeRank w (plug g₀ ctx) := nodeRank_congr hsw_root
    have hr_local : nodeRank w u₁ = nodeRank w g₀ := nodeRank_congr hsw_local
    have hpot_plug : potential w (plug u₁ ctx) - potential w (plug g₀ ctx) =
        potential w u₁ - potential w g₀ := potential_plug_sub_eq w ctx hsw_local
    have hlog : 2 + nodeRank w u₀ + nodeRank w g₁ ≤ 2 * nodeRank w u₁ := by
      apply two_add_logb_two_add_le
        (subtreeWeight_pos hw (by simp [u₀]))
        (subtreeWeight_pos hw (by simp [g₁]))
      have hp := hw p
      simp only [u₀, g₁, u₁, p₁, subtreeWeight_node]; linarith
    have hp₁_le : nodeRank w p₁ ≤ nodeRank w u₁ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [p₁]))
      have hx := hw x
      have hr := subtreeWeight_nonneg hw0 r
      simp only [p₁, u₁, subtreeWeight_node]; linarith
    have hu₀_le_p₀ : nodeRank w u₀ ≤ nodeRank w p₀ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [u₀]))
      have hp := hw p
      have hc := subtreeWeight_nonneg hw0 c
      simp only [u₀, p₀, subtreeWeight_node]; linarith
    have hstep : 2 + potential w u₁ - potential w g₀ ≤ 3 * (nodeRank w u₁ - nodeRank w u₀) := by
      simp only [u₁, p₁, g₁, g₀, p₀, u₀, potential_node] at hr_local hlog hp₁_le hu₀_le_p₀ ⊢
      linarith
    have hite : (if ctx.isEmpty then (0 : ℝ) else 1) ≤ 1 := by split <;> norm_num
    linarith [ih]
  | case6 l r a p g d ctx ih =>
    -- Zig-zag (left-right)
    simp only [splayUp, plug_right, plug_left, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_add, Nat.cast_ofNat]
    set u₀ : BinaryTree α := .node x l r
    set p₀ : BinaryTree α := .node p a u₀
    set g₀ : BinaryTree α := .node g p₀ d
    set l₁ : BinaryTree α := .node p a l
    set r₁ : BinaryTree α := .node g r d
    set u₁ : BinaryTree α := .node x l₁ r₁
    have hsw_local : subtreeWeight w u₁ = subtreeWeight w g₀ := by
      simp only [u₁, l₁, r₁, g₀, p₀, u₀, subtreeWeight_node]; ring
    have hsw_root : subtreeWeight w (plug u₁ ctx) = subtreeWeight w (plug g₀ ctx) :=
      subtreeWeight_plug_congr w ctx hsw_local
    have hr_root : nodeRank w (plug u₁ ctx) = nodeRank w (plug g₀ ctx) := nodeRank_congr hsw_root
    have hr_local : nodeRank w u₁ = nodeRank w g₀ := nodeRank_congr hsw_local
    have hpot_plug : potential w (plug u₁ ctx) - potential w (plug g₀ ctx) =
        potential w u₁ - potential w g₀ := potential_plug_sub_eq w ctx hsw_local
    have hlog : 2 + nodeRank w l₁ + nodeRank w r₁ ≤ 2 * nodeRank w u₁ := by
      apply two_add_logb_two_add_le
        (subtreeWeight_pos hw (by simp [l₁]))
        (subtreeWeight_pos hw (by simp [r₁]))
      have hx := hw x
      simp only [l₁, r₁, u₁, subtreeWeight_node]; linarith
    have hu₀_le_p₀ : nodeRank w u₀ ≤ nodeRank w p₀ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [u₀]))
      have hp := hw p
      have ha := subtreeWeight_nonneg hw0 a
      simp only [u₀, p₀, subtreeWeight_node]; linarith
    have hu₀_le_u₁ : nodeRank w u₀ ≤ nodeRank w u₁ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [u₀]))
      have hp := hw p
      have hg := hw g
      have ha := subtreeWeight_nonneg hw0 a
      have hd := subtreeWeight_nonneg hw0 d
      simp only [u₀, u₁, l₁, r₁, subtreeWeight_node]; linarith
    have hstep : 2 + potential w u₁ - potential w g₀ ≤ 3 * (nodeRank w u₁ - nodeRank w u₀) := by
      simp only [u₁, l₁, r₁, g₀, p₀, u₀, potential_node] at hr_local hlog hu₀_le_p₀ hu₀_le_u₁ ⊢
      linarith
    have hite : (if ctx.isEmpty then (0 : ℝ) else 1) ≤ 1 := by split <;> norm_num
    linarith [ih]
  | case7 l r p c d g ctx ih =>
    -- Zig-zag (right-left)
    simp only [splayUp, plug_left, plug_right, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_add, Nat.cast_ofNat]
    set u₀ : BinaryTree α := .node x l r
    set p₀ : BinaryTree α := .node p u₀ c
    set g₀ : BinaryTree α := .node g d p₀
    set l₁ : BinaryTree α := .node g d l
    set r₁ : BinaryTree α := .node p r c
    set u₁ : BinaryTree α := .node x l₁ r₁
    have hsw_local : subtreeWeight w u₁ = subtreeWeight w g₀ := by
      simp only [u₁, l₁, r₁, g₀, p₀, u₀, subtreeWeight_node]; ring
    have hsw_root : subtreeWeight w (plug u₁ ctx) = subtreeWeight w (plug g₀ ctx) :=
      subtreeWeight_plug_congr w ctx hsw_local
    have hr_root : nodeRank w (plug u₁ ctx) = nodeRank w (plug g₀ ctx) := nodeRank_congr hsw_root
    have hr_local : nodeRank w u₁ = nodeRank w g₀ := nodeRank_congr hsw_local
    have hpot_plug : potential w (plug u₁ ctx) - potential w (plug g₀ ctx) =
        potential w u₁ - potential w g₀ := potential_plug_sub_eq w ctx hsw_local
    have hlog : 2 + nodeRank w l₁ + nodeRank w r₁ ≤ 2 * nodeRank w u₁ := by
      apply two_add_logb_two_add_le
        (subtreeWeight_pos hw (by simp [l₁]))
        (subtreeWeight_pos hw (by simp [r₁]))
      have hx := hw x
      simp only [l₁, r₁, u₁, subtreeWeight_node]; linarith
    have hu₀_le_p₀ : nodeRank w u₀ ≤ nodeRank w p₀ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [u₀]))
      have hp := hw p
      have hc := subtreeWeight_nonneg hw0 c
      simp only [u₀, p₀, subtreeWeight_node]; linarith
    have hu₀_le_u₁ : nodeRank w u₀ ≤ nodeRank w u₁ := by
      apply nodeRank_mono (subtreeWeight_pos hw (by simp [u₀]))
      have hp := hw p
      have hg := hw g
      have hc := subtreeWeight_nonneg hw0 c
      have hd := subtreeWeight_nonneg hw0 d
      simp only [u₀, u₁, l₁, r₁, subtreeWeight_node]; linarith
    have hstep : 2 + potential w u₁ - potential w g₀ ≤ 3 * (nodeRank w u₁ - nodeRank w u₀) := by
      simp only [u₁, l₁, r₁, g₀, p₀, u₀, potential_node] at hr_local hlog hu₀_le_p₀ hu₀_le_u₁ ⊢
      linarith
    have hite : (if ctx.isEmpty then (0 : ℝ) else 1) ≤ 1 := by split <;> norm_num
    linarith [ih]

/-- Sleator–Tarjan `splayTime` Access Lemma on `splayUp` ([SleatorTarjan1985b], Section 2, Lemma 1,
p. 658). -/
theorem splayUp_splayTime_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    (splayTime (splayUp x l r ctx) : ℝ) +
        potential w (splayUp x l r ctx).tree - potential w (plug (.node x l r) ctx) ≤
      3 * (nodeRank w (plug (.node x l r) ctx) - nodeRank w (.node x l r)) + 1 := by
  have h := splayUp_amortized_le hw x l r ctx
  cases ctx with
  | nil =>
    simp [splayUp, splayTime]
  | cons f ctx' =>
    have hlen : 1 ≤ (splayUp x l r (f :: ctx')).rotations := by
      simp [rotations_splayUp]
    have htime : splayTime (splayUp x l r (f :: ctx')) =
        (splayUp x l r (f :: ctx')).rotations := max_eq_left hlen
    rw [htime]
    simpa using h

/-- Unit weight `w(x) = 1` ([SleatorTarjan1985b], Section 2, Theorem 1, p. 659; Section 3,
Theorem 6, p. 665). -/
@[expose] noncomputable def unitWeight : α → ℝ := fun _ => 1

/-- Rank-sum potential under unit weights (`unitWeight`). -/
@[expose] noncomputable def unitPotential (t : BinaryTree α) : ℝ :=
  potential unitWeight t

@[simp] theorem unitPotential_nil : unitPotential (.nil : BinaryTree α) = 0 := rfl

theorem subtreeWeight_unitWeight_nonneg (t : BinaryTree α) :
    0 ≤ subtreeWeight (unitWeight (α := α)) t :=
  subtreeWeight_nonneg (fun _ => zero_le_one) t

theorem subtreeWeight_unitWeight_pos {t : BinaryTree α} (ht : t ≠ .nil) :
    0 < subtreeWeight (unitWeight (α := α)) t :=
  subtreeWeight_pos (fun _ => zero_lt_one) ht

theorem subtreeWeight_unitWeight_eq_numNodes (t : BinaryTree α) :
    subtreeWeight (unitWeight (α := α)) t = t.numNodes := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
    simp only [subtreeWeight_node, unitWeight, ihl, ihr, BinaryTree.numNodes, Nat.cast_add,
      Nat.cast_one]
    ring

theorem unitPotential_nonneg (t : BinaryTree α) : 0 ≤ unitPotential t := by
  induction t with
  | nil => exact le_rfl
  | node a l r ihl ihr =>
    have hsw : 1 ≤ subtreeWeight (unitWeight (α := α)) (.node a l r) := by
      have hl := subtreeWeight_unitWeight_nonneg l
      have hr := subtreeWeight_unitWeight_nonneg r
      simp only [subtreeWeight_node, unitWeight]; linarith
    have hrk : 0 ≤ nodeRank (unitWeight (α := α)) (.node a l r) :=
      Real.logb_nonneg (by norm_num) hsw
    simp only [unitPotential, potential_node] at ihl ihr ⊢
    linarith

end Weights

/-! ### Access Lemma on Search Trees, Balance Theorem, and Static Optimality -/

section OrderedAccess

variable {α : Type*} [LinearOrder α]

@[simp] theorem subtreeWeight_splay (w : α → ℝ) (x : α) (t : BinaryTree α) :
    subtreeWeight w (splay x t).tree = subtreeWeight w t := by
  simp only [splay]
  cases hf : focusSearch x t [] with
  | none => simp [(focusSearch_eq_none_iff x t []).mp hf]
  | some f =>
    have htree := (focusSearch_toTree_and_length hf).1
    rw [subtreeWeight_splayUp]
    simpa only [Focus.toTree, Focus.sub, plug_nil] using congrArg (subtreeWeight w) htree

/-- On an `Ordered` search tree, `subtreeWeight w t` equals the Finset sum of `w` over
`elements t`. -/
theorem subtreeWeight_eq_sum_elements (w : α → ℝ) {t : BinaryTree α} (ht : Ordered t) :
    subtreeWeight w t = ∑ x ∈ elements t, w x := by
  induction t with
  | nil => simp [elements]
  | node a l r ihl ihr =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    have hdis : Disjoint (elements l) (elements r) := by
      refine Finset.disjoint_left.mpr fun y hyl hyr => ?_
      exact lt_asymm (hla y hyl) (har y hyr)
    have ha : a ∉ elements l ∪ elements r := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · exact lt_irrefl a (hla a hmem)
      · exact lt_irrefl a (har a hmem)
    simp only [subtreeWeight_node, elements, Finset.sum_insert ha,
      Finset.sum_union hdis, ihl hl, ihr hr]
    ring

theorem le_subtreeWeight_of_mem {w : α → ℝ} (hw : ∀ y, 0 ≤ w y) {t : BinaryTree α}
    (ht : Ordered t) {x : α} (hx : x ∈ elements t) :
    w x ≤ subtreeWeight w t := by
  rw [subtreeWeight_eq_sum_elements w ht]
  exact Finset.single_le_sum (fun y _ => hw y) hx

/-- **Access Lemma (focused-subtree form)** ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658):
if `focusSearch x t [] = some f`, splaying `t` at `x` has amortized `splayTime` at most
`3 (r(t) - r(f.sub)) + 1`. -/
theorem splay_splayTime_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y) {x : α} {t : BinaryTree α}
    {f : Focus α} (hf : focusSearch x t [] = some f) :
    (splayTime (splay x t) : ℝ) + potential w (splay x t).tree - potential w t ≤
      3 * (nodeRank w t - nodeRank w f.sub) + 1 := by
  have htree : plug (.node f.key f.leftSub f.rightSub) f.ctx = t := by
    simpa only [Focus.toTree, Focus.sub, plug_nil] using (focusSearch_toTree_and_length hf).1
  simp only [splay, hf, Focus.sub]
  simpa only [htree] using splayUp_splayTime_amortized_le hw f.key f.leftSub f.rightSub f.ctx

/-- **Access Lemma (general key-weight form)** ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658;
Section 3, p. 664): on any non-empty `Ordered` tree `t` and any query `x` (present or absent),
there exists a splayed key `u ∈ elements t` (equal to `x` if `x ∈ elements t`) such that the
amortized `splayTime` of `splay x t` is at most `3 log₂(W / w(u)) + 1`. -/
theorem exists_mem_splay_splayTime_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) (hne : t ≠ .nil) (x : α) :
    ∃ u ∈ elements t, (x ∈ elements t → u = x) ∧
      (splayTime (splay x t) : ℝ) + potential w (splay x t).tree - potential w t ≤
        3 * Real.logb 2 (subtreeWeight w t / w u) + 1 := by
  cases hf : focusSearch x t [] with
  | none => exact (hne ((focusSearch_eq_none_iff x t []).mp hf)).elim
  | some f =>
    obtain ⟨hmem, hxeq, _⟩ := focusSearch_ordered_spec ht hf
    refine ⟨f.key, hmem, hxeq, ?_⟩
    have hacc := splay_splayTime_amortized_le hw hf
    have hw_le : w f.key ≤ subtreeWeight w f.sub := by
      have hl := subtreeWeight_nonneg (fun y => (hw y).le) f.leftSub
      have hr := subtreeWeight_nonneg (fun y => (hw y).le) f.rightSub
      simp only [Focus.sub, subtreeWeight_node]; linarith
    have hrk_le : Real.logb 2 (w f.key) ≤ nodeRank w f.sub :=
      Real.logb_le_logb_of_le (by norm_num) (hw f.key) hw_le
    have hwt_pos : 0 < subtreeWeight w t := subtreeWeight_pos hw hne
    have hdiv : Real.logb 2 (subtreeWeight w t / w f.key) =
        nodeRank w t - Real.logb 2 (w f.key) :=
      Real.logb_div hwt_pos.ne' (hw f.key).ne'
    linarith

/-- **Access Lemma for present keys** ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658):
when `x ∈ elements t` in an `Ordered` tree `t`, splaying `t` at `x` has amortized `splayTime`
at most `3 log₂(W / w(x)) + 1`. -/
theorem splay_splayTime_amortized_le_of_mem {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) {x : α} (hx : x ∈ elements t) :
    (splayTime (splay x t) : ℝ) + potential w (splay x t).tree - potential w t ≤
      3 * Real.logb 2 (subtreeWeight w t / w x) + 1 := by
  have hne : t ≠ .nil := by
    intro h; subst h; simp [elements] at hx
  obtain ⟨u, _, hux, hbound⟩ := exists_mem_splay_splayTime_amortized_le hw ht hne x
  rwa [hux hx] at hbound

/-- Rotation-count corollary of `splay_splayTime_amortized_le_of_mem`. -/
theorem splay_rotations_amortized_le_of_mem {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) {x : α} (hx : x ∈ elements t) :
    ((splay x t).rotations : ℝ) + potential w (splay x t).tree - potential w t ≤
      3 * Real.logb 2 (subtreeWeight w t / w x) + 1 := by
  have hle : ((splay x t).rotations : ℝ) ≤ (splayTime (splay x t) : ℝ) := by
    exact_mod_cast rotations_le_splayTime (splay x t)
  linarith [splay_splayTime_amortized_le_of_mem hw ht hx]

/-- Amortized rotation bound for `splayMin` on a non-empty tree. -/
theorem splayMin_rotations_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (hne : t ≠ .nil) :
    ∃ m ∈ elements t,
      ((splayMin t).rotations : ℝ) + potential w (splayMin t).tree - potential w t ≤
        3 * Real.logb 2 (subtreeWeight w t / w m) + 1 := by
  cases hf : focusMin t [] with
  | none => exact (hne ((focusMin_eq_none_iff t []).mp hf)).elim
  | some f =>
    have htree : plug (.node f.key f.leftSub f.rightSub) f.ctx = t := by
      simpa only [Focus.toTree, Focus.sub, plug_nil] using (focusMin_spec hf).1
    have hmem : f.key ∈ elements t := by
      have he := elements_splayUp f.key f.leftSub f.rightSub f.ctx
      rw [htree] at he
      obtain ⟨l', r', hnode⟩ := exists_node_splayUp f.key f.leftSub f.rightSub f.ctx
      rw [hnode] at he
      exact he ▸ by simp
    refine ⟨f.key, hmem, ?_⟩
    have hup := splayUp_splayTime_amortized_le hw f.key f.leftSub f.rightSub f.ctx
    rw [htree] at hup
    have hrot_le : ((splayUp f.key f.leftSub f.rightSub f.ctx).rotations : ℝ) ≤
        (splayTime (splayUp f.key f.leftSub f.rightSub f.ctx) : ℝ) := by
      exact_mod_cast rotations_le_splayTime _
    have hw_le : w f.key ≤ subtreeWeight w (.node f.key f.leftSub f.rightSub) := by
      have hl := subtreeWeight_nonneg (fun y => (hw y).le) f.leftSub
      have hr := subtreeWeight_nonneg (fun y => (hw y).le) f.rightSub
      simp only [subtreeWeight_node]; linarith
    have hrk_le : Real.logb 2 (w f.key) ≤ nodeRank w (.node f.key f.leftSub f.rightSub) :=
      Real.logb_le_logb_of_le (by norm_num) (hw f.key) hw_le
    have hdiv : Real.logb 2 (subtreeWeight w t / w f.key) =
        nodeRank w t - Real.logb 2 (w f.key) :=
      Real.logb_div (subtreeWeight_pos hw hne).ne' (hw f.key).ne'
    simp only [splayMin, hf]
    linarith

/-- Amortized rotation bound for `splayMax` on a non-empty tree. -/
theorem splayMax_rotations_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (hne : t ≠ .nil) :
    ∃ m ∈ elements t,
      ((splayMax t).rotations : ℝ) + potential w (splayMax t).tree - potential w t ≤
        3 * Real.logb 2 (subtreeWeight w t / w m) + 1 := by
  cases hf : focusMax t [] with
  | none => exact (hne ((focusMax_eq_none_iff t []).mp hf)).elim
  | some f =>
    have htree : plug (.node f.key f.leftSub f.rightSub) f.ctx = t := by
      simpa only [Focus.toTree, Focus.sub, plug_nil] using (focusMax_spec hf).1
    have hmem : f.key ∈ elements t := by
      have he := elements_splayUp f.key f.leftSub f.rightSub f.ctx
      rw [htree] at he
      obtain ⟨l', r', hnode⟩ := exists_node_splayUp f.key f.leftSub f.rightSub f.ctx
      rw [hnode] at he
      exact he ▸ by simp
    refine ⟨f.key, hmem, ?_⟩
    have hup := splayUp_splayTime_amortized_le hw f.key f.leftSub f.rightSub f.ctx
    rw [htree] at hup
    have hrot_le : ((splayUp f.key f.leftSub f.rightSub f.ctx).rotations : ℝ) ≤
        (splayTime (splayUp f.key f.leftSub f.rightSub f.ctx) : ℝ) := by
      exact_mod_cast rotations_le_splayTime _
    have hw_le : w f.key ≤ subtreeWeight w (.node f.key f.leftSub f.rightSub) := by
      have hl := subtreeWeight_nonneg (fun y => (hw y).le) f.leftSub
      have hr := subtreeWeight_nonneg (fun y => (hw y).le) f.rightSub
      simp only [subtreeWeight_node]; linarith
    have hrk_le : Real.logb 2 (w f.key) ≤ nodeRank w (.node f.key f.leftSub f.rightSub) :=
      Real.logb_le_logb_of_le (by norm_num) (hw f.key) hw_le
    have hdiv : Real.logb 2 (subtreeWeight w t / w f.key) =
        nodeRank w t - Real.logb 2 (w f.key) :=
      Real.logb_div (subtreeWeight_pos hw hne).ne' (hw f.key).ne'
    simp only [splayMax, hf]
    linarith

/-! ### Fixed-Weight Potential Drop, Balance Theorem, and Static Optimality -/

private theorem sum_logb_weight_le_potential {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) :
    ∑ y ∈ elements t, Real.logb 2 (w y) ≤ potential w t := by
  induction t with
  | nil => simp [elements]
  | node a l r ihl ihr =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    have hdis : Disjoint (elements l) (elements r) := by
      refine Finset.disjoint_left.mpr fun y hyl hyr => ?_
      exact lt_asymm (hla y hyl) (har y hyr)
    have ha : a ∉ elements l ∪ elements r := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · exact lt_irrefl a (hla a hmem)
      · exact lt_irrefl a (har a hmem)
    have ha_le : Real.logb 2 (w a) ≤ nodeRank w (.node a l r) := by
      apply Real.logb_le_logb_of_le (by norm_num) (hw a)
      have hwl := subtreeWeight_nonneg (fun y => (hw y).le) l
      have hwr := subtreeWeight_nonneg (fun y => (hw y).le) r
      simp only [subtreeWeight_node]; linarith
    simp only [elements, Finset.sum_insert ha, Finset.sum_union hdis, potential_node]
    linarith [ihl hl, ihr hr]

private theorem potential_le_sum_logb_of_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) {W : ℝ} (hW : subtreeWeight w t ≤ W) :
    potential w t ≤ ∑ _y ∈ elements t, Real.logb 2 W := by
  induction t with
  | nil => simp [elements]
  | node a l r ihl ihr =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    have hdis : Disjoint (elements l) (elements r) := by
      refine Finset.disjoint_left.mpr fun y hyl hyr => ?_
      exact lt_asymm (hla y hyl) (har y hyr)
    have ha : a ∉ elements l ∪ elements r := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · exact lt_irrefl a (hla a hmem)
      · exact lt_irrefl a (har a hmem)
    have hwl : subtreeWeight w l ≤ W := by
      have hwa := hw a
      have hwr := subtreeWeight_nonneg (fun y => (hw y).le) r
      simp only [subtreeWeight_node] at hW; linarith
    have hwr : subtreeWeight w r ≤ W := by
      have hwa := hw a
      have hwl' := subtreeWeight_nonneg (fun y => (hw y).le) l
      simp only [subtreeWeight_node] at hW; linarith
    have hrk : nodeRank w (.node a l r) ≤ Real.logb 2 W :=
      Real.logb_le_logb_of_le (by norm_num) (subtreeWeight_pos hw (by simp)) hW
    simp only [elements, Finset.sum_insert ha, Finset.sum_union hdis, potential_node]
    linarith [ihl hl hwl, ihr hr hwr]

/-- **Fixed-Weight Potential Drop Bound** ([SleatorTarjan1985b], Section 2, p. 659):
between any two `Ordered` trees `t₁` and `t₂` representing the same set of keys, if
`0 < W` and `subtreeWeight w t₁ ≤ W`, the net potential decrease satisfies
`potential w t₁ - potential w t₂ ≤ ∑ y ∈ elements t₁, log₂(W / w(y))`. -/
theorem potential_sub_potential_le_sum_logb {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t₁ t₂ : BinaryTree α} (ht₁ : Ordered t₁) (ht₂ : Ordered t₂)
    (helem : elements t₁ = elements t₂) {W : ℝ} (hWpos : 0 < W) (hW : subtreeWeight w t₁ ≤ W) :
    potential w t₁ - potential w t₂ ≤ ∑ y ∈ elements t₁, Real.logb 2 (W / w y) := by
  have h1 := potential_le_sum_logb_of_le hw ht₁ hW
  have h2 := sum_logb_weight_le_potential hw ht₂
  rw [← helem] at h2
  have hdiff : (∑ _y ∈ elements t₁, Real.logb 2 W) - (∑ y ∈ elements t₁, Real.logb 2 (w y)) =
      ∑ y ∈ elements t₁, Real.logb 2 (W / w y) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact (Real.logb_div hWpos.ne' (hw y).ne').symm
  linarith

/-- Execute a sequence of `splay` operations `xs` starting from `t`, returning the final tree
and the list of per-operation `SplayResult`s. -/
@[expose] def splaySeq : List α → BinaryTree α → BinaryTree α × List (SplayResult α)
  | [], t => (t, [])
  | x :: xs, t =>
      let res := splay x t
      let rest := splaySeq xs res.tree
      (rest.1, res :: rest.2)

/-- Total Sleator–Tarjan splay time (`∑ max rotations 1`) across an access sequence `xs`. -/
@[expose] def splaySeqTime (xs : List α) (t : BinaryTree α) : ℕ :=
  ((splaySeq xs t).2.map splayTime).sum

/-- Total edge rotations across an access sequence `xs`. -/
@[expose] def splaySeqRotations (xs : List α) (t : BinaryTree α) : ℕ :=
  ((splaySeq xs t).2.map SplayResult.rotations).sum

@[simp] theorem splaySeq_nil (t : BinaryTree α) : splaySeq [] t = (t, []) := rfl

@[simp] theorem splaySeqTime_nil (t : BinaryTree α) : splaySeqTime [] t = 0 := rfl

@[simp] theorem splaySeqTime_cons (x : α) (xs : List α) (t : BinaryTree α) :
    splaySeqTime (x :: xs) t = splayTime (splay x t) + splaySeqTime xs (splay x t).tree := rfl

theorem splaySeqRotations_le_splaySeqTime (xs : List α) (t : BinaryTree α) :
    splaySeqRotations xs t ≤ splaySeqTime xs t := by
  induction xs generalizing t with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [splaySeqRotations, splaySeqTime, splaySeq, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (rotations_le_splayTime _) (ih _)

theorem splaySeq_ordered_and_elements (xs : List α) {t : BinaryTree α} (ht : Ordered t) :
    Ordered (splaySeq xs t).1 ∧ elements (splaySeq xs t).1 = elements t := by
  induction xs generalizing t with
  | nil => exact ⟨ht, rfl⟩
  | cons x xs ih =>
    simp only [splaySeq]
    obtain ⟨ho, he⟩ := ih (ordered_splay ht x)
    exact ⟨ho, he.trans (elements_splay x t)⟩

@[simp] theorem subtreeWeight_splaySeq (w : α → ℝ) (xs : List α) (t : BinaryTree α) :
    subtreeWeight w (splaySeq xs t).1 = subtreeWeight w t := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [splaySeq]
    exact (ih (splay x t).tree).trans (subtreeWeight_splay w x t)

theorem subtreeWeight_unitWeight_eq_card {t : BinaryTree α} (ht : Ordered t) :
    subtreeWeight (unitWeight (α := α)) t = (elements t).card := by
  rw [subtreeWeight_unitWeight_eq_numNodes, card_elements ht]

private theorem splaySeqTime_unit_telescoping (xs : List α) {t : BinaryTree α}
    (ht : Ordered t) (hne : t ≠ .nil) :
    (splaySeqTime xs t : ℝ) + unitPotential (splaySeq xs t).1 - unitPotential t ≤
      xs.length * (3 * Real.logb 2 (elements t).card + 1) := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
    have hne' : (splay x t).tree ≠ .nil := by
      intro h; exact hne ((tree_splay_eq_nil_iff x t).mp h)
    have ho' : Ordered (splay x t).tree := ordered_splay ht x
    have he' : elements (splay x t).tree = elements t := elements_splay x t
    obtain ⟨u, _, _, hstep⟩ := exists_mem_splay_splayTime_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) ht hne x
    rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hstep
    have hrest := ih ho' hne'
    rw [he'] at hrest
    simp only [splaySeqTime_cons, splaySeq, List.length_cons, Nat.cast_add, Nat.cast_one]
    change (splayTime (splay x t) : ℝ) + (splaySeqTime xs (splay x t).tree : ℝ) +
        unitPotential (splaySeq xs (splay x t).tree).1 - unitPotential t ≤ _
    change (splayTime (splay x t) : ℝ) + unitPotential (splay x t).tree - unitPotential t ≤ _
      at hstep
    linarith

/-- **Balance Theorem** ([SleatorTarjan1985b], Section 2, Theorem 1, p. 659):
for any non-empty `Ordered` tree `t` of `n = (elements t).card` elements and any sequence `xs`
of `m = xs.length` accesses (whether successful or unsuccessful), the total splay time satisfies
`splaySeqTime xs t ≤ (3m + n) log₂ n + m`. -/
theorem splaySeqTime_le_balance (xs : List α) {t : BinaryTree α} (ht : Ordered t)
    (hne : t ≠ .nil) :
    (splaySeqTime xs t : ℝ) ≤
      (3 * (xs.length : ℝ) + (elements t).card) * Real.logb 2 (elements t).card + xs.length := by
  have htel := splaySeqTime_unit_telescoping xs ht hne
  obtain ⟨ho_end, he_end⟩ := splaySeq_ordered_and_elements xs ht
  have hn_pos : (0 : ℝ) < (elements t).card := by
    rw [← subtreeWeight_unitWeight_eq_card ht]
    exact subtreeWeight_pos (fun _ => zero_lt_one) hne
  have hdrop := potential_sub_potential_le_sum_logb (w := unitWeight) (fun _ => zero_lt_one)
    ht ho_end he_end.symm hn_pos (subtreeWeight_unitWeight_eq_card ht).le
  simp only [unitWeight, div_one, Finset.sum_const, nsmul_eq_mul] at hdrop
  change unitPotential t - unitPotential (splaySeq xs t).1 ≤ _ at hdrop
  linarith

private theorem splaySeqTime_present_telescoping {w : α → ℝ} (hw : ∀ y, 0 < w y)
    (xs : List α) {t : BinaryTree α} (ht : Ordered t) (hxs : ∀ x ∈ xs, x ∈ elements t) :
    (splaySeqTime xs t : ℝ) + potential w (splaySeq xs t).1 - potential w t ≤
      (xs.map fun x => 3 * Real.logb 2 (subtreeWeight w t / w x) + 1).sum := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
    have hx_mem : x ∈ elements t := hxs x List.mem_cons_self
    have hstep := splay_splayTime_amortized_le_of_mem hw ht hx_mem
    have ho' : Ordered (splay x t).tree := ordered_splay ht x
    have he' : elements (splay x t).tree = elements t := elements_splay x t
    have hxs' : ∀ y ∈ xs, y ∈ elements (splay x t).tree := by
      intro y hy
      rw [he']
      exact hxs y (List.mem_cons_of_mem x hy)
    have hrest := ih ho' hxs'
    rw [subtreeWeight_splay w x t] at hrest
    simp only [splaySeqTime_cons, splaySeq, List.map_cons, List.sum_cons, Nat.cast_add]
    linarith

private theorem list_sum_map_eq_sum_count {s : Finset α} (xs : List α)
    (hxs : ∀ x ∈ xs, x ∈ s) (f : α → ℝ) :
    (xs.map f).sum = ∑ y ∈ s, (xs.count y : ℝ) * f y := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx_mem : x ∈ s := hxs x List.mem_cons_self
    have hxs' : ∀ z ∈ xs, z ∈ s := fun z hz => hxs z (List.mem_cons_of_mem x hz)
    simp only [List.map_cons, List.sum_cons, ih hxs']
    have hsplit : ∀ y ∈ s, ((x :: xs).count y : ℝ) * f y =
        (xs.count y : ℝ) * f y + if y = x then f y else 0 := by
      intro y _
      rw [List.count_cons]
      by_cases hyx : y = x
      · subst hyx
        simp only [beq_self_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        ring
      · have hxy : (x == y) = false := beq_false_of_ne (Ne.symm hyx)
        simp [hyx, hxy]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' s x f]
    simp only [hx_mem, ↓reduceIte]
    ring

/-- **Static Optimality Theorem** ([SleatorTarjan1985b], Section 2, Theorem 2, p. 659):
for any `Ordered` splay tree `t` and any access sequence `xs` of present keys (`∀ x ∈ xs, x ∈ t`)
in which every key in `t` is accessed at least once (`∀ y ∈ elements t, 1 ≤ xs.count y`),
the total splay time is bounded by the empirical Shannon access-frequency sum:
`splaySeqTime xs t ≤ m + 4 ∑ y ∈ elements t, q(y) log₂(m / q(y))`, where `m = xs.length` and
`q(y) = xs.count y`. -/
theorem splaySeqTime_le_static_optimality (xs : List α) {t : BinaryTree α} (ht : Ordered t)
    (hxs : ∀ x ∈ xs, x ∈ elements t) (hq : ∀ y ∈ elements t, 1 ≤ xs.count y) :
    (splaySeqTime xs t : ℝ) ≤ (xs.length : ℝ) +
      4 * ∑ y ∈ elements t, (xs.count y : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count y) := by
  cases t with
  | nil =>
    cases xs with
    | nil => simp
    | cons x xs' =>
      have hx := hxs x List.mem_cons_self
      simp [elements] at hx
  | node a l r =>
    set s := elements (.node a l r)
    let w : α → ℝ := fun y => if y ∈ s then (xs.count y : ℝ) else 1
    have hw : ∀ y, 0 < w y := by
      intro y
      simp only [w]
      split_ifs with hy
      · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hq y hy)
      · exact zero_lt_one
    have hcount_sum : (xs.length : ℝ) = ∑ y ∈ s, (xs.count y : ℝ) := by
      have h1 := list_sum_map_eq_sum_count xs hxs (fun _ => (1 : ℝ))
      have hmap : (xs.map fun _ => (1 : ℝ)).sum = xs.length := by simp
      simpa [hmap] using h1
    have hW_eq : subtreeWeight w (.node a l r) = (xs.length : ℝ) := by
      rw [subtreeWeight_eq_sum_elements w ht, hcount_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      simp [w, hy]
    have hm_pos : (0 : ℝ) < xs.length := by
      rw [← hW_eq]
      exact subtreeWeight_pos hw (by simp)
    have htel := splaySeqTime_present_telescoping hw xs ht hxs
    obtain ⟨ho_end, he_end⟩ := splaySeq_ordered_and_elements xs ht
    have hdrop := potential_sub_potential_le_sum_logb hw ht ho_end he_end.symm hm_pos hW_eq.le
    have hmap_sum := list_sum_map_eq_sum_count xs hxs
      (fun x => 3 * Real.logb 2 (subtreeWeight w (.node a l r) / w x) + 1)
    rw [hmap_sum] at htel
    have hrew_tel :
        ∑ y ∈ s, (xs.count y : ℝ) * (3 * Real.logb 2 (subtreeWeight w (.node a l r) / w y) + 1) =
          (xs.length : ℝ) +
            3 * ∑ y ∈ s, (xs.count y : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count y) := by
      have hterm : ∀ y ∈ s,
          (xs.count y : ℝ) * (3 * Real.logb 2 (subtreeWeight w (.node a l r) / w y) + 1) =
            (xs.count y : ℝ) +
              3 * ((xs.count y : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count y)) := by
        intro y hy
        simp only [hW_eq, w, hy, ↓reduceIte]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← hcount_sum]
    have hdrop_le :
        ∑ y ∈ s, Real.logb 2 ((xs.length : ℝ) / w y) ≤
          ∑ y ∈ s, (xs.count y : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count y) := by
      refine Finset.sum_le_sum fun y hy => ?_
      simp only [w, hy, ↓reduceIte]
      have hcy_ge : (1 : ℝ) ≤ xs.count y := by exact_mod_cast hq y hy
      have hcy_le : (xs.count y : ℝ) ≤ xs.length := by
        rw [hcount_sum]
        exact Finset.single_le_sum (f := fun z => (xs.count z : ℝ))
          (fun z _ => Nat.cast_nonneg _) hy
      have hcy_pos : (0 : ℝ) < xs.count y := by linarith
      have hdiv_ge : 1 ≤ (xs.length : ℝ) / xs.count y := (one_le_div hcy_pos).mpr hcy_le
      have hlog_nonneg : 0 ≤ Real.logb 2 ((xs.length : ℝ) / xs.count y) :=
        Real.logb_nonneg (by norm_num) hdiv_ge
      nlinarith
    linarith

/-! ### Unit-Weight Update Lemma Specialization and `OrderedSet` Companion Bounds

Sleator and Tarjan's Update Lemma ([SleatorTarjan1985b], Section 3, Lemma 2, pp. 663–664) states
general positive-weight bounds for `access`, `join`, `split`, `insert` (assuming `x ∉ t`), and
`delete` (assuming `x ∈ t`) under a multi-tree potential incorporating `∑_{i ∉ trees} log₂ w(i)`.
At unit weights (`unitWeight`, where `log₂ 1 = 0`), that external-item potential term vanishes.
Below we prove this unit-weight specialization for `contains`, `split`, `join`, and total
set-idempotent `insert` and `erase`, together with companion unit-weight bounds for `minimum` and
`successor` derived directly from the Access Lemma (`Lemma 1`, p. 658). -/

theorem unitPotential_le_card_mul_logb {t : BinaryTree α} (ht : Ordered t) :
    unitPotential t ≤ (elements t).card * Real.logb 2 ((elements t).card + 1) := by
  have hW : subtreeWeight (unitWeight (α := α)) t ≤ (elements t).card + 1 := by
    rw [subtreeWeight_unitWeight_eq_card ht]; linarith
  have h := potential_le_sum_logb_of_le (w := unitWeight) (fun _ => zero_lt_one) ht hW
  simpa only [unitPotential, Finset.sum_const, nsmul_eq_mul] using h

private theorem logb_two_card_add_one_nonneg (n : ℕ) : 0 ≤ Real.logb 2 ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact Real.logb_nonneg (by norm_num) (by linarith)

/-- Unit-weight (`w = 1`) specialization of the `access` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664, for `contains`. -/
theorem contains_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((contains x t).rotations : ℝ) + unitPotential (contains x t).tree - unitPotential t ≤
      3 * Real.logb 2 ((elements t).card + 1) + 1 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil =>
    simp only [contains, splay_nil, unitPotential_nil, Nat.cast_zero]
    linarith
  | node a l r =>
    have hne : BinaryTree.node a l r ≠ .nil := by simp
    obtain ⟨u, _, _, hacc⟩ := exists_mem_splay_splayTime_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) ht hne x
    rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hacc
    have hn_pos : (0 : ℝ) < (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht]
      exact subtreeWeight_unitWeight_pos hne
    have hlog_le : Real.logb 2 (elements (.node a l r)).card ≤
        Real.logb 2 ((elements (.node a l r)).card + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hn_pos (by linarith)
    have hrot_le : ((splay x (.node a l r)).rotations : ℝ) ≤
        (splayTime (splay x (.node a l r)) : ℝ) := by
      exact_mod_cast rotations_le_splayTime _
    simp only [contains]
    cases hs : (splay x (.node a l r)).tree with
    | nil =>
      have := (tree_splay_eq_nil_iff x (.node a l r)).mp hs
      simp at this
    | node r' l' R' =>
      dsimp only
      change ((splay x (.node a l r)).rotations : ℝ) +
          unitPotential (.node r' l' R') - unitPotential (.node a l r) ≤ _
      rw [hs] at hacc
      change (splayTime (splay x (.node a l r)) : ℝ) +
          unitPotential (.node r' l' R') - unitPotential (.node a l r) ≤ _ at hacc
      linarith

/-- Companion unit-weight amortized rotation bound for `minimum`, derived from the Access Lemma
([SleatorTarjan1985b], Section 2, Lemma 1, p. 658) via `splayMin_rotations_amortized_le` (`minimum`
is not part of Section 3, Lemma 2). -/
theorem minimum_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) :
    ((minimum t).rotations : ℝ) + unitPotential (minimum t).tree - unitPotential t ≤
      3 * Real.logb 2 ((elements t).card + 1) + 1 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil =>
    simp only [minimum, splayMin_nil, unitPotential_nil, Nat.cast_zero]
    linarith
  | node a l r =>
    have hne : BinaryTree.node a l r ≠ .nil := by simp
    obtain ⟨m, _, hacc⟩ := splayMin_rotations_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) hne
    rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hacc
    have hn_pos : (0 : ℝ) < (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht]
      exact subtreeWeight_unitWeight_pos hne
    have hlog_le : Real.logb 2 (elements (.node a l r)).card ≤
        Real.logb 2 ((elements (.node a l r)).card + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hn_pos (by linarith)
    simp only [minimum]
    cases hs : (splayMin (.node a l r)).tree with
    | nil =>
      have := (tree_splayMin_eq_nil_iff (.node a l r)).mp hs
      simp at this
    | node m' l' R' =>
      dsimp only
      change ((splayMin (.node a l r)).rotations : ℝ) +
          unitPotential (.node m' l' R') - unitPotential (.node a l r) ≤ _
      rw [hs] at hacc
      change ((splayMin (.node a l r)).rotations : ℝ) +
          unitPotential (.node m' l' R') - unitPotential (.node a l r) ≤ _ at hacc
      linarith

/-- Unit-weight (`w = 1`) specialization of the `split` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664. -/
theorem split_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((split x t).rotations : ℝ) +
        unitPotential (split x t).left + unitPotential (split x t).right - unitPotential t ≤
      3 * Real.logb 2 ((elements t).card + 1) + 1 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil =>
    simp only [split, splay_nil, unitPotential_nil, Nat.cast_zero]
    linarith
  | node a l r =>
    have hne : BinaryTree.node a l r ≠ .nil := by simp
    obtain ⟨u, _, _, hacc⟩ := exists_mem_splay_splayTime_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) ht hne x
    rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hacc
    have hn_pos : (0 : ℝ) < (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht]
      exact subtreeWeight_unitWeight_pos hne
    have hlog_le : Real.logb 2 (elements (.node a l r)).card ≤
        Real.logb 2 ((elements (.node a l r)).card + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hn_pos (by linarith)
    have hrot_le : ((splay x (.node a l r)).rotations : ℝ) ≤
        (splayTime (splay x (.node a l r)) : ℝ) := by
      exact_mod_cast rotations_le_splayTime _
    simp only [split]
    cases hs : (splay x (.node a l r)).tree with
    | nil =>
      have := (tree_splay_eq_nil_iff x (.node a l r)).mp hs
      simp at this
    | node r' l' R' =>
      dsimp only
      rw [hs] at hacc
      change (splayTime (splay x (.node a l r)) : ℝ) +
          unitPotential (.node r' l' R') - unitPotential (.node a l r) ≤ _ at hacc
      split <;> dsimp only
      · have hrk : nodeRank (unitWeight (α := α)) (.node r' .nil R') ≤
            nodeRank (unitWeight (α := α)) (.node r' l' R') := by
          apply nodeRank_mono (subtreeWeight_unitWeight_pos (by simp))
          have hwl := subtreeWeight_unitWeight_nonneg l'
          simp only [subtreeWeight_node, subtreeWeight_nil]; linarith
        simp only [unitPotential, potential_node, potential_nil] at hacc ⊢
        linarith
      · have hrk : nodeRank (unitWeight (α := α)) (.node r' l' .nil) ≤
            nodeRank (unitWeight (α := α)) (.node r' l' R') := by
          apply nodeRank_mono (subtreeWeight_unitWeight_pos (by simp))
          have hwR := subtreeWeight_unitWeight_nonneg R'
          simp only [subtreeWeight_node, subtreeWeight_nil]; linarith
        simp only [unitPotential, potential_node, potential_nil] at hacc ⊢
        linarith

/-- Unit-weight (`w = 1`) specialization of the `join` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664. -/
theorem join_unitPotential_amortized_le {t₁ t₂ : BinaryTree α}
    (ht₁ : Ordered t₁) (ht₂ : Ordered t₂) :
    ((join t₁ t₂).rotations : ℝ) +
        unitPotential (join t₁ t₂).tree - (unitPotential t₁ + unitPotential t₂) ≤
      3 * Real.logb 2 ((elements t₁).card + (elements t₂).card + 1) + 1 := by
  have hn₁_nn : (0 : ℝ) ≤ (elements t₁).card := Nat.cast_nonneg _
  have hn₂_nn : (0 : ℝ) ≤ (elements t₂).card := Nat.cast_nonneg _
  have hL : 0 ≤ Real.logb 2 (((elements t₁).card : ℝ) + (elements t₂).card + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  cases t₁ with
  | nil =>
    simp only [join, unitPotential_nil, Nat.cast_zero]
    linarith
  | node a l r =>
    have hne : BinaryTree.node a l r ≠ .nil := by simp
    obtain ⟨m, lm, hm⟩ := exists_node_nil_right_splayMax (t := .node a l r) hne
    obtain ⟨u, _, hacc⟩ := splayMax_rotations_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) hne
    rw [subtreeWeight_unitWeight_eq_card ht₁, unitWeight, div_one, hm] at hacc
    have hn₁_pos : (0 : ℝ) < (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht₁]
      exact subtreeWeight_unitWeight_pos hne
    have hlog₁ : Real.logb 2 (elements (.node a l r)).card ≤
        Real.logb 2 (((elements (.node a l r)).card : ℝ) + (elements t₂).card + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hn₁_pos (by linarith)
    have hsw_m : subtreeWeight (unitWeight (α := α)) (.node m lm .nil) =
        (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht₁,
        ← subtreeWeight_splayMax unitWeight (.node a l r), hm]
    have hrk_m : nodeRank (unitWeight (α := α)) (.node m lm .nil) =
        Real.logb 2 (elements (.node a l r)).card := by
      rw [nodeRank, hsw_m]
    have hrk_join : nodeRank (unitWeight (α := α)) (.node m lm t₂) ≤
        Real.logb 2 (((elements (.node a l r)).card : ℝ) + (elements t₂).card + 1) := by
      apply Real.logb_le_logb_of_le (by norm_num)
        (subtreeWeight_unitWeight_pos (by simp))
      have hsw₂ := subtreeWeight_unitWeight_eq_card ht₂
      simp only [subtreeWeight_node, subtreeWeight_nil] at hsw_m ⊢
      linarith
    simp only [join, hm, unitPotential, potential_node, potential_nil, hrk_m] at hacc ⊢
    linarith

/-- Unit-weight (`w = 1`) specialization of the `insert` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664, extended from `x ∉ elements t` to total set-idempotent `insert`. -/
theorem insert_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((insert x t).rotations : ℝ) + unitPotential (insert x t).tree - unitPotential t ≤
      4 * Real.logb 2 ((elements t).card + 1) + 1 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil =>
    have hrk0 : nodeRank (unitWeight (α := α)) (.node x .nil .nil) = 0 := by
      simp [nodeRank, unitWeight]
    simp only [insert, unitPotential, potential_node, potential_nil, hrk0, Nat.cast_zero]
    linarith
  | node a l r =>
    have hne : BinaryTree.node a l r ≠ .nil := by simp
    obtain ⟨u, _, _, hacc⟩ := exists_mem_splay_splayTime_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) ht hne x
    rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hacc
    have hn_pos : (0 : ℝ) < (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht]
      exact subtreeWeight_unitWeight_pos hne
    have hlog_le : Real.logb 2 (elements (.node a l r)).card ≤
        Real.logb 2 ((elements (.node a l r)).card + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hn_pos (by linarith)
    have hrot_le : ((splay x (.node a l r)).rotations : ℝ) ≤
        (splayTime (splay x (.node a l r)) : ℝ) := by
      exact_mod_cast rotations_le_splayTime _
    simp only [insert]
    cases hs : (splay x (.node a l r)).tree with
    | nil =>
      have := (tree_splay_eq_nil_iff x (.node a l r)).mp hs
      simp at this
    | node r' l' R' =>
      dsimp only
      have hsw : subtreeWeight (unitWeight (α := α)) (.node r' l' R') =
          (elements (.node a l r)).card := by
        rw [← subtreeWeight_unitWeight_eq_card ht,
          ← subtreeWeight_splay unitWeight x (.node a l r), hs]
      rw [hs] at hacc
      split
      · dsimp only
        have hrk_sub : nodeRank (unitWeight (α := α)) (.node r' .nil R') ≤
            nodeRank (unitWeight (α := α)) (.node r' l' R') := by
          apply nodeRank_mono (subtreeWeight_unitWeight_pos (by simp))
          have hwl := subtreeWeight_unitWeight_nonneg l'
          simp only [subtreeWeight_node, subtreeWeight_nil]; linarith
        have hrk_new : nodeRank (unitWeight (α := α)) (.node x l' (.node r' .nil R')) =
            Real.logb 2 ((elements (.node a l r)).card + 1) := by
          simp only [nodeRank, subtreeWeight_node, subtreeWeight_nil, unitWeight] at hsw ⊢
          congr 1; linarith
        simp only [unitPotential, potential_node, potential_nil, hrk_new] at hacc ⊢
        linarith
      · split <;> dsimp only
        · have hrk_sub : nodeRank (unitWeight (α := α)) (.node r' l' .nil) ≤
              nodeRank (unitWeight (α := α)) (.node r' l' R') := by
            apply nodeRank_mono (subtreeWeight_unitWeight_pos (by simp))
            have hwR := subtreeWeight_unitWeight_nonneg R'
            simp only [subtreeWeight_node, subtreeWeight_nil]; linarith
          have hrk_new : nodeRank (unitWeight (α := α)) (.node x (.node r' l' .nil) R') =
              Real.logb 2 ((elements (.node a l r)).card + 1) := by
            simp only [nodeRank, subtreeWeight_node, subtreeWeight_nil, unitWeight] at hsw ⊢
            congr 1; linarith
          simp only [unitPotential, potential_node, potential_nil, hrk_new] at hacc ⊢
          linarith
        · simp only [unitPotential] at hacc ⊢
          linarith

/-- Unit-weight (`w = 1`) specialization of the `delete` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664, extended from `x ∈ elements t` to total set-idempotent `erase`. -/
theorem erase_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((erase x t).rotations : ℝ) + unitPotential (erase x t).tree - unitPotential t ≤
      6 * Real.logb 2 ((elements t).card + 1) + 2 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil =>
    simp only [erase, unitPotential_nil, Nat.cast_zero]
    linarith
  | node a l r =>
    have hne : BinaryTree.node a l r ≠ .nil := by simp
    obtain ⟨u, _, _, hacc⟩ := exists_mem_splay_splayTime_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) ht hne x
    rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hacc
    have hn_pos : (0 : ℝ) < (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht]
      exact subtreeWeight_unitWeight_pos hne
    have hlog_le : Real.logb 2 (elements (.node a l r)).card ≤
        Real.logb 2 ((elements (.node a l r)).card + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hn_pos (by linarith)
    have hrot_le : ((splay x (.node a l r)).rotations : ℝ) ≤
        (splayTime (splay x (.node a l r)) : ℝ) := by
      exact_mod_cast rotations_le_splayTime _
    simp only [erase]
    cases hs : (splay x (.node a l r)).tree with
    | nil =>
      have := (tree_splay_eq_nil_iff x (.node a l r)).mp hs
      simp at this
    | node r' l' R' =>
      dsimp only
      have hsw : subtreeWeight (unitWeight (α := α)) (.node r' l' R') =
          (elements (.node a l r)).card := by
        rw [← subtreeWeight_unitWeight_eq_card ht,
          ← subtreeWeight_splay unitWeight x (.node a l r), hs]
      rw [hs] at hacc
      split <;> dsimp only
      · cases hl_eq : l' with
        | nil =>
          have hrk_nonneg : 0 ≤ nodeRank (unitWeight (α := α)) (.node r' .nil R') := by
            apply Real.logb_nonneg (by norm_num)
            have hwR := subtreeWeight_unitWeight_nonneg R'
            simp only [subtreeWeight_node, subtreeWeight_nil, unitWeight]; linarith
          rw [hl_eq] at hacc
          simp only [join, unitPotential, potential_node, potential_nil, Nat.add_zero] at hacc ⊢
          linarith
        | node b ll lr =>
          have hne_l : BinaryTree.node b ll lr ≠ .nil := by simp
          obtain ⟨m, lm, hm⟩ := exists_node_nil_right_splayMax (t := .node b ll lr) hne_l
          obtain ⟨v, _, hacc_l⟩ := splayMax_rotations_amortized_le
            (w := unitWeight) (fun _ => zero_lt_one) hne_l
          have hsw_l_pos : 0 < subtreeWeight (unitWeight (α := α)) (.node b ll lr) :=
            subtreeWeight_unitWeight_pos hne_l
          have hsw_l_le : subtreeWeight (unitWeight (α := α)) (.node b ll lr) ≤
              (elements (.node a l r)).card + 1 := by
            rw [hl_eq] at hsw
            have hwR := subtreeWeight_unitWeight_nonneg R'
            simp only [subtreeWeight_node, unitWeight] at hsw ⊢
            linarith
          have hlog_l : Real.logb 2 (subtreeWeight (unitWeight (α := α)) (.node b ll lr)) ≤
              Real.logb 2 ((elements (.node a l r)).card + 1) :=
            Real.logb_le_logb_of_le (by norm_num) hsw_l_pos hsw_l_le
          rw [unitWeight, div_one, hm] at hacc_l
          have hsw_m : subtreeWeight (unitWeight (α := α)) (.node m lm .nil) =
              subtreeWeight (unitWeight (α := α)) (.node b ll lr) := by
            rw [← subtreeWeight_splayMax unitWeight (.node b ll lr), hm]
          have hrk_m_nonneg : 0 ≤ nodeRank (unitWeight (α := α)) (.node m lm .nil) := by
            apply Real.logb_nonneg (by norm_num)
            have hlm := subtreeWeight_unitWeight_nonneg lm
            simp only [subtreeWeight_node, subtreeWeight_nil, unitWeight]; linarith
          have hrk_join_le : nodeRank (unitWeight (α := α)) (.node m lm R') ≤
              nodeRank (unitWeight (α := α)) (.node r' (.node b ll lr) R') := by
            apply nodeRank_mono (subtreeWeight_unitWeight_pos (by simp))
            simp only [subtreeWeight_node, subtreeWeight_nil, unitWeight] at hsw_m ⊢
            linarith
          rw [hl_eq] at hacc
          simp only [join, hm, unitPotential, potential_node, potential_nil, Nat.cast_add]
            at hacc hacc_l ⊢
          linarith
      · simp only [unitPotential] at hacc ⊢
        linarith

/-- Companion unit-weight amortized rotation bound for `successor` (splaying `x`, followed by
`splayMin` on the right subtree when `root ≤ x`), derived from the Access Lemma
([SleatorTarjan1985b], Section 2, Lemma 1, p. 658; `successor` is not part of Section 3,
Lemma 2). -/
theorem successor_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((successor x t).rotations : ℝ) + unitPotential (successor x t).tree - unitPotential t ≤
      7 * Real.logb 2 ((elements t).card + 1) + 3 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil =>
    simp only [successor, splay_nil, unitPotential_nil, Nat.cast_zero]
    linarith
  | node a l r =>
    have hne : BinaryTree.node a l r ≠ .nil := by simp
    obtain ⟨u, _, _, hacc⟩ := exists_mem_splay_splayTime_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) ht hne x
    rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hacc
    have hn_pos : (0 : ℝ) < (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht]
      exact subtreeWeight_unitWeight_pos hne
    have hlog_le : Real.logb 2 (elements (.node a l r)).card ≤
        Real.logb 2 ((elements (.node a l r)).card + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hn_pos (by linarith)
    have hrot_le : ((splay x (.node a l r)).rotations : ℝ) ≤
        (splayTime (splay x (.node a l r)) : ℝ) := by
      exact_mod_cast rotations_le_splayTime _
    simp only [successor]
    cases hs : (splay x (.node a l r)).tree with
    | nil =>
      have := (tree_splay_eq_nil_iff x (.node a l r)).mp hs
      simp at this
    | node r' l' R' =>
      dsimp only
      have hsw : subtreeWeight (unitWeight (α := α)) (.node r' l' R') =
          (elements (.node a l r)).card := by
        rw [← subtreeWeight_unitWeight_eq_card ht,
          ← subtreeWeight_splay unitWeight x (.node a l r), hs]
      rw [hs] at hacc
      split
      · dsimp only
        simp only [unitPotential] at hacc ⊢
        linarith
      · cases hR_eq : R' with
        | nil =>
          dsimp only
          rw [hR_eq] at hacc
          simp only [unitPotential] at hacc ⊢
          linarith
        | node b rl rr =>
          dsimp only
          have hne_R : BinaryTree.node b rl rr ≠ .nil := by simp
          obtain ⟨m, rm, hm⟩ := exists_node_nil_left_splayMin (t := .node b rl rr) hne_R
          obtain ⟨v, _, hacc_R⟩ := splayMin_rotations_amortized_le
            (w := unitWeight) (fun _ => zero_lt_one) hne_R
          have hsw_R_pos : 0 < subtreeWeight (unitWeight (α := α)) (.node b rl rr) :=
            subtreeWeight_unitWeight_pos hne_R
          have hsw_R_le : subtreeWeight (unitWeight (α := α)) (.node b rl rr) ≤
              (elements (.node a l r)).card + 1 := by
            rw [hR_eq] at hsw
            have hwl := subtreeWeight_unitWeight_nonneg l'
            simp only [subtreeWeight_node, unitWeight] at hsw ⊢
            linarith
          have hlog_R : Real.logb 2 (subtreeWeight (unitWeight (α := α)) (.node b rl rr)) ≤
              Real.logb 2 ((elements (.node a l r)).card + 1) :=
            Real.logb_le_logb_of_le (by norm_num) hsw_R_pos hsw_R_le
          rw [unitWeight, div_one, hm] at hacc_R
          have hsw_m : subtreeWeight (unitWeight (α := α)) (.node m .nil rm) =
              subtreeWeight (unitWeight (α := α)) (.node b rl rr) := by
            rw [← subtreeWeight_splayMin unitWeight (.node b rl rr), hm]
          have hrk_m_nonneg : 0 ≤ nodeRank (unitWeight (α := α)) (.node m .nil rm) := by
            apply Real.logb_nonneg (by norm_num)
            have hrm := subtreeWeight_unitWeight_nonneg rm
            simp only [subtreeWeight_node, subtreeWeight_nil, unitWeight]; linarith
          have hrk_root_eq :
              nodeRank (unitWeight (α := α)) (.node m (.node r' l' .nil) rm) =
                nodeRank (unitWeight (α := α)) (.node r' l' (.node b rl rr)) := by
            apply nodeRank_congr
            simp only [subtreeWeight_node, subtreeWeight_nil, unitWeight] at hsw_m ⊢
            linarith
          have hrk_left_le :
              nodeRank (unitWeight (α := α)) (.node r' l' .nil) ≤
                Real.logb 2 ((elements (.node a l r)).card + 1) := by
            apply Real.logb_le_logb_of_le (by norm_num)
              (subtreeWeight_unitWeight_pos (by simp))
            rw [hR_eq] at hsw
            have hrl := subtreeWeight_unitWeight_nonneg rl
            have hrr := subtreeWeight_unitWeight_nonneg rr
            simp only [subtreeWeight_node, subtreeWeight_nil, unitWeight] at hsw ⊢
            linarith
          rw [hR_eq] at hacc
          simp only [hm, unitPotential, potential_node, potential_nil, hrk_root_eq, Nat.cast_add,
            Nat.cast_one] at hacc hacc_R ⊢
          linarith

end OrderedAccess

end Cslib.Algorithms.Lean.SplayTree
