/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPSZ.Defs
public import Complexity.Foundations.Data.BitString.Flip
import Mathlib.Algebra.Order.Ring.GeomSum

/-!
# Critical clause trees and the forcing lemma for PPSZ

Let `σ` satisfy a CNF formula `φ`. It is *`h`-isolated* (`IsIsolated`) if flipping any nonempty
set of at most `h` variables falsifies `φ` [Paturi, Pudlák, Saks, Zane, p. 343]
[PaturiPudlakSaksZane2005]; a unique satisfying assignment is `h`-isolated for every `h`
(`isIsolated_of_unique`).

The *critical clause tree* of a variable `x` has root labelled `x`. A node is identified with its
root path `p`, the list of the variable labels from the node up to the root. A node of depth less
than `h` has at most `h` labels on its root path, so flipping them falsifies `φ`; the node is
labelled by a clause `C p` of `φ` violated by that flip, and its children are labelled by the
variables of `C p` not on `p` (`children`) [Scheder, §3.1][Scheder2021]
[Paturi, Pudlák, Saks, Zane, §3.2][PaturiPudlakSaksZane2005]. Here the tree is given by the
labelling `C`, a function on all lists, and `IsCriticalTree φ σ h C` says that it labels every
root path of at most `h` variables by such a clause. Labellings exist for `h`-isolated `σ`
(`exists_isCriticalTree`), labels on a path are distinct (`nodup_append_of_descends`), and every
node of depth less than `h` has at most `k - 1` children when the clauses of `φ` have at most `k`
literals (`card_children_le`).

The tree of `x` only visits root paths that contain `x`. `IsCriticalTreeAt φ σ x h C` asks for
the clause labels on those paths only; it follows from `IsCriticalTree φ σ h C`
(`IsCriticalTree.isCriticalTreeAt`), and the degree bound and the forcing lemma need no more. For
general satisfiable formulas, PPSZ needs trees for frozen variables of restricted formulas, which
are rooted trees but not isolated ones.

`Cut C A d p` says that every downward path of `d` steps from the node `p` has a node other than
`p` labelled in `A` (`cut_iff_forall_descends`). It is decidable, monotone in `A` (`Cut.mono`),
and satisfies `Cut C A (d + 1) p ↔ ∀ y ∈ children C p, y ∈ A ∨ Cut C A d (y :: p)` (`cut_succ`).

**Forcing lemma.** If every path from the root of the tree of `x` to depth `h` meets `A`, then
`x = σ x` is implied, under `σ` restricted to `A`, by the clause labels of the tree, which are
at most `∑ i < h, (k - 1) ^ i` (`wImplied_of_cut`, and `IsCriticalTreeAt.wImplied_of_cut` for
rooted trees). In PPSZ, with `A` the variables placed before
`x`, this says that `x` is forced [Scheder, Lemma 3.2][Scheder2021].

## Main definitions

* `Cslib.Complexity.PPSZ.IsIsolated`: flipping at most `h` variables falsifies the formula.
* `Cslib.Complexity.PPSZ.IsCriticalTree`: a clause labelling of the critical clause tree.
* `Cslib.Complexity.PPSZ.IsCriticalTreeAt`: a clause labelling of the critical clause tree
  rooted at a given variable.
* `Cslib.Complexity.PPSZ.children`: the children of a node.
* `Cslib.Complexity.PPSZ.Descends`: the downward paths from a node.
* `Cslib.Complexity.PPSZ.Cut`: every downward path from a node meets a set of variables.
* `Cslib.Complexity.PPSZ.labels`: the clause labels of the nodes of bounded depth.

## Main results

* `Cslib.Complexity.PPSZ.exists_isCriticalTree`: critical clause trees of isolated assignments.
* `Cslib.Complexity.PPSZ.card_children_le`: the tree has degree at most `k - 1`.
* `Cslib.Complexity.PPSZ.cut_succ`: the recursion of `Cut`.
* `Cslib.Complexity.PPSZ.cut_insert_of_mem`: `Cut` below `p` does not depend on the labels on
  `p`.
* `Cslib.Complexity.PPSZ.cut_iff_forall_descends`: `Cut` in terms of paths.
* `Cslib.Complexity.PPSZ.IsCriticalTreeAt.wImplied_of_cut`: the forcing lemma for a rooted tree
  and `w ≥ ∑ i < h, (k - 1) ^ i`.
* `Cslib.Complexity.PPSZ.wImplied_of_cut`: the forcing lemma for `w ≥ ∑ i < h, (k - 1) ^ i`.
* `Cslib.Complexity.PPSZ.wImplied_of_forall_descends`: the forcing lemma for
  `w ≥ (k - 1) ^ (h + 1)` [Scheder, Lemma 3.2][Scheder2021].

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [D. Scheder, *PPSZ is better than you think*][Scheder2021]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL Cslib.BitString Finset

variable {n : ℕ}

/-! ### Isolation and critical clause trees -/

/-- `σ` is **`h`-isolated** in `φ`: flipping any nonempty set of at most `h` variables falsifies
`φ`. For a satisfying `σ`, no other satisfying assignment is within Hamming distance `h`
[Paturi, Pudlák, Saks, Zane, p. 343][PaturiPudlakSaksZane2005]. -/
def IsIsolated (φ : CNF (Fin n)) (σ : Fin n → Bool) (h : ℕ) : Prop :=
  ∀ D : Finset (Fin n), D.Nonempty → D.card ≤ h → φ.eval (flipOn D σ) ≠ true

/-- A unique satisfying assignment is `h`-isolated for every `h`. -/
theorem isIsolated_of_unique {φ : CNF (Fin n)} {σ : Fin n → Bool}
    (huniq : ∀ τ, φ.eval τ = true → τ = σ) (h : ℕ) : IsIsolated φ σ h := by
  intro D ⟨y, hy⟩ _ hD
  have := congrFun (huniq _ hD) y
  rw [flipOn_apply_of_mem hy] at this
  cases hσ : σ y <;> simp [hσ] at this

/-- The clause labelling `C` defines a **critical clause tree of height `h`** for `σ`: every root
path `p` of at most `h` variables (a node of depth less than `h`, listed from the node up to the
root) is labelled by a clause of `φ` that flipping the variables of `p` violates
[Scheder, §3.1][Scheder2021]. -/
def IsCriticalTree (φ : CNF (Fin n)) (σ : Fin n → Bool) (h : ℕ)
    (C : List (Fin n) → Clause (Fin n)) : Prop :=
  ∀ p : List (Fin n), p ≠ [] → p.length ≤ h →
    C p ∈ φ ∧ (C p).eval (flipOn p.toFinset σ) = false

/-- **Critical clause trees exist** for isolated assignments. -/
theorem exists_isCriticalTree {φ : CNF (Fin n)} {σ : Fin n → Bool} {h : ℕ}
    (hiso : IsIsolated φ σ h) : ∃ C, IsCriticalTree φ σ h C := by
  classical
  have key : ∀ p : List (Fin n), p ≠ [] → p.length ≤ h →
      ∃ c ∈ φ, c.eval (flipOn p.toFinset σ) = false := by
    intro p hp hlen
    have hne : p.toFinset.Nonempty := List.toFinset_nonempty_iff p |>.mpr hp
    have hD := hiso _ hne ((List.toFinset_card_le p).trans hlen)
    by_contra hall
    push Not at hall
    exact hD ((CNF.eval_eq_true_iff _ φ).mpr fun c hc => by simpa using hall c hc)
  have key' : ∀ p : List (Fin n), ∃ c : Clause (Fin n), p ≠ [] → p.length ≤ h →
      c ∈ φ ∧ c.eval (flipOn p.toFinset σ) = false := by
    intro p
    by_cases hp : p ≠ [] ∧ p.length ≤ h
    · obtain ⟨c, hc, hce⟩ := key p hp.1 hp.2
      exact ⟨c, fun _ _ => ⟨hc, hce⟩⟩
    · exact ⟨[], fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hp⟩
  choose C hC using key'
  exact ⟨C, hC⟩

/-- The clause labelling `C` defines a **critical clause tree of height `h` rooted at `x`** for
`σ`: every root path `p` of at most `h` variables that contains `x` is labelled by a clause of `φ`
that flipping the variables of `p` violates. The root paths of the nodes of the tree of `x` end
in `x`, so this is the part of `IsCriticalTree` that the tree of `x` uses
(`IsCriticalTree.isCriticalTreeAt`). Unlike `IsCriticalTree`, it can hold when `σ` is not
isolated, for instance for a frozen variable of a restricted formula (original). -/
def IsCriticalTreeAt (φ : CNF (Fin n)) (σ : Fin n → Bool) (x : Fin n) (h : ℕ)
    (C : List (Fin n) → Clause (Fin n)) : Prop :=
  ∀ p : List (Fin n), x ∈ p → p.length ≤ h →
    C p ∈ φ ∧ (C p).eval (flipOn p.toFinset σ) = false

/-- A critical clause tree is a critical clause tree rooted at every variable. -/
theorem IsCriticalTree.isCriticalTreeAt {φ : CNF (Fin n)} {σ : Fin n → Bool} {h : ℕ}
    {C : List (Fin n) → Clause (Fin n)} (hC : IsCriticalTree φ σ h C) (x : Fin n) :
    IsCriticalTreeAt φ σ x h C :=
  fun p hxp hph => hC p (List.ne_nil_of_mem hxp) hph

/-- The **children** of the node with root path `p`: the variables of its clause label that are
not on `p` [Paturi, Pudlák, Saks, Zane, §3.2][PaturiPudlakSaksZane2005]. -/
def children (C : List (Fin n) → Clause (Fin n)) (p : List (Fin n)) : Finset (Fin n) :=
  PPZ.vars (C p) \ p.toFinset

/-- Membership in `children`. -/
theorem mem_children {C : List (Fin n) → Clause (Fin n)} {p : List (Fin n)} {y : Fin n} :
    y ∈ children C p ↔ y ∈ PPZ.vars (C p) ∧ y ∉ p := by
  simp [children]

/-- A child is not on the root path of its parent. -/
theorem notMem_of_mem_children {C : List (Fin n) → Clause (Fin n)} {p : List (Fin n)}
    {y : Fin n} (hy : y ∈ children C p) : y ∉ p :=
  (mem_children.mp hy).2

/-- The critical clause tree has **degree at most `k - 1`** for clauses of at most `k` literals:
some variable of a node's clause label is on its root path [Scheder, §3.1][Scheder2021]. -/
theorem card_children_le {k h : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool} {x : Fin n}
    {C : List (Fin n) → Clause (Fin n)} (hσ : φ.eval σ = true) (hC : IsCriticalTreeAt φ σ x h C)
    (hlen : ∀ c ∈ φ, c.length ≤ k) {p : List (Fin n)} (hxp : x ∈ p) (hph : p.length ≤ h) :
    (children C p).card ≤ k - 1 := by
  obtain ⟨hmem, hflip⟩ := hC p hxp hph
  obtain ⟨l, hl, hls⟩ :=
    (Clause.eval_eq_true_iff σ _).mp ((CNF.eval_eq_true_iff σ φ).mp hσ _ hmem)
  have hlp : l.1 ∈ p := by
    by_contra hlp
    have : (C p).eval (flipOn p.toFinset σ) = true :=
      (Clause.eval_eq_true_iff _ _).mpr
        ⟨l, hl, by rwa [flipOn_apply_of_notMem (by simpa using hlp)]⟩
    simp [hflip] at this
  have hlv : l.1 ∈ PPZ.vars (C p) := List.mem_toFinset.mpr (List.mem_map_of_mem hl)
  have hsub : children C p ⊆ (PPZ.vars (C p)).erase l.1 := fun y hy =>
    mem_erase.mpr ⟨fun e => notMem_of_mem_children hy (e ▸ hlp), (mem_children.mp hy).1⟩
  calc (children C p).card ≤ ((PPZ.vars (C p)).erase l.1).card := card_le_card hsub
    _ = (PPZ.vars (C p)).card - 1 := card_erase_of_mem hlv
    _ ≤ k - 1 := Nat.sub_le_sub_right ((PPZ.card_vars_le _).trans (hlen _ hmem)) 1

/-! ### Paths and cuts -/

/-- `Descends C d p s`: the list `s`, deepest first, labels a downward path of `d` steps from the
node `p`, so that `s ++ p` is the root path of its end node. -/
def Descends (C : List (Fin n) → Clause (Fin n)) : ℕ → List (Fin n) → List (Fin n) → Prop
  | 0, _, s => s = []
  | d + 1, p, s => ∃ y ∈ children C p, ∃ t, s = t ++ [y] ∧ Descends C d (y :: p) t

/-- **Labels on a path are distinct** [Scheder, Observation 3.1][Scheder2021]. -/
theorem nodup_append_of_descends {C : List (Fin n) → Clause (Fin n)} :
    ∀ {d : ℕ} {p s : List (Fin n)}, p.Nodup → Descends C d p s → (s ++ p).Nodup
  | 0, p, s, hp, hs => by
    rw [show s = [] from hs]
    exact hp
  | d + 1, p, s, hp, hs => by
    obtain ⟨y, hy, t, rfl, ht⟩ := hs
    have := nodup_append_of_descends (List.nodup_cons.mpr ⟨notMem_of_mem_children hy, hp⟩) ht
    simpa using this

/-- `Cut C A d p`: every downward path of `d` steps from the node `p` has a node other than `p`
labelled by a variable of `A`. For the root `[x]` of the tree of `x` with `x ∉ A`, this says that
every path from the root to depth `d` meets `A`; the set of nodes labelled in `A` then contains a
cut in the sense of [Paturi, Pudlák, Saks, Zane, p. 347][PaturiPudlakSaksZane2005]. -/
def Cut (C : List (Fin n) → Clause (Fin n)) (A : Finset (Fin n)) : ℕ → List (Fin n) → Prop
  | 0, _ => False
  | d + 1, p => ∀ y ∈ children C p, y ∈ A ∨ Cut C A d (y :: p)

/-- No node has a cut of depth `0`. -/
@[simp] theorem cut_zero (C : List (Fin n) → Clause (Fin n)) (A : Finset (Fin n))
    (p : List (Fin n)) : ¬Cut C A 0 p :=
  id

/-- **The recursion of `Cut`**: every child is in `A` or has a cut one level shallower. -/
theorem cut_succ (C : List (Fin n) → Clause (Fin n)) (A : Finset (Fin n)) (d : ℕ)
    (p : List (Fin n)) :
    Cut C A (d + 1) p ↔ ∀ y ∈ children C p, y ∈ A ∨ Cut C A d (y :: p) :=
  Iff.rfl

/-- `Cut` is decidable, by its recursion. -/
instance Cut.decidable (C : List (Fin n) → Clause (Fin n)) (A : Finset (Fin n)) :
    ∀ d p, Decidable (Cut C A d p)
  | 0, p => isFalse (cut_zero C A p)
  | d + 1, p =>
    have := fun y => Cut.decidable C A d (y :: p)
    decidable_of_iff _ (cut_succ C A d p).symm

/-- `Cut` is **monotone** in the set of variables. -/
theorem Cut.mono {C : List (Fin n) → Clause (Fin n)} {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    ∀ {d : ℕ} {p : List (Fin n)}, Cut C A d p → Cut C B d p
  | 0, _, h => h
  | _ + 1, _, h => fun y hy => (h y hy).imp (fun hA => hAB hA) (Cut.mono hAB)

/-- **A cut does not depend on the labels of the root path**: the nodes below `p` are labelled by
variables not on `p`, so adding a variable of `p` to the set does not change `Cut`. -/
theorem cut_insert_of_mem {C : List (Fin n) → Clause (Fin n)} {A : Finset (Fin n)} {y : Fin n} :
    ∀ {d : ℕ} {p : List (Fin n)}, y ∈ p → (Cut C (insert y A) d p ↔ Cut C A d p)
  | 0, _, _ => Iff.rfl
  | d + 1, p, hy => by
    rw [cut_succ, cut_succ]
    refine forall₂_congr fun z hz => or_congr ?_ (cut_insert_of_mem (List.mem_cons_of_mem z hy))
    rw [mem_insert, or_iff_right fun (e : z = y) => notMem_of_mem_children hz (e ▸ hy)]

/-- **`Cut` in terms of paths**: every downward path of `d` steps from `p` meets `A` outside
`p`. -/
theorem cut_iff_forall_descends {C : List (Fin n) → Clause (Fin n)} {A : Finset (Fin n)} :
    ∀ {d : ℕ} {p : List (Fin n)},
      Cut C A d p ↔ ∀ s, Descends C d p s → ∃ y ∈ s, y ∈ A
  | 0, p => by
    simp only [cut_zero, false_iff, Descends, not_forall]
    exact ⟨[], rfl, by simp⟩
  | d + 1, p => by
    rw [cut_succ]
    constructor
    · rintro h s ⟨y, hy, t, rfl, ht⟩
      rcases h y hy with hyA | hcut
      · exact ⟨y, by simp, hyA⟩
      · obtain ⟨z, hz, hzA⟩ := cut_iff_forall_descends.mp hcut t ht
        exact ⟨z, List.mem_append_left _ hz, hzA⟩
    · intro h y hy
      by_cases hyA : y ∈ A
      · exact Or.inl hyA
      · refine Or.inr (cut_iff_forall_descends.mpr fun t ht => ?_)
        obtain ⟨z, hz, hzA⟩ := h (t ++ [y]) ⟨y, hy, t, rfl, ht⟩
        rcases List.mem_append.mp hz with hz | hz
        · exact ⟨z, hz, hzA⟩
        · exact absurd (List.mem_singleton.mp hz ▸ hzA) hyA

/-! ### The forcing lemma -/

/-- The clause labels of the nodes of depth less than `d` below the node `p`, including `p`. -/
def labels (C : List (Fin n) → Clause (Fin n)) : ℕ → List (Fin n) → Finset (Clause (Fin n))
  | 0, _ => ∅
  | d + 1, p => insert (C p) ((children C p).biUnion fun y => labels C d (y :: p))

/-- Membership in the clause labels of a tree of depth `d + 1`. -/
theorem mem_labels_succ {C : List (Fin n) → Clause (Fin n)} {d : ℕ} {p : List (Fin n)}
    {c : Clause (Fin n)} :
    c ∈ labels C (d + 1) p ↔ c = C p ∨ ∃ y ∈ children C p, c ∈ labels C d (y :: p) := by
  simp [labels]

/-- The clause labels of a critical clause tree are clauses of the formula. -/
theorem mem_of_mem_labels {φ : CNF (Fin n)} {σ : Fin n → Bool} {x : Fin n} {h : ℕ}
    {C : List (Fin n) → Clause (Fin n)} (hC : IsCriticalTreeAt φ σ x h C) :
    ∀ {d : ℕ} {p : List (Fin n)}, x ∈ p → p.length + d ≤ h + 1 →
      ∀ c ∈ labels C d p, c ∈ φ
  | 0, _, _, _, c, hc => by simp [labels] at hc
  | d + 1, p, hxp, hph, c, hc => by
    rcases mem_labels_succ.mp hc with rfl | ⟨y, _, hy⟩
    · exact (hC p hxp (by omega)).1
    · exact mem_of_mem_labels hC (List.mem_cons_of_mem y hxp) (by rw [List.length_cons]; omega)
        c hy

/-- **The number of clause labels** of nodes of depth less than `d` is at most
`∑ i < d, (k - 1) ^ i`. -/
theorem card_labels_le {k h : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool} {x : Fin n}
    {C : List (Fin n) → Clause (Fin n)} (hσ : φ.eval σ = true) (hC : IsCriticalTreeAt φ σ x h C)
    (hlen : ∀ c ∈ φ, c.length ≤ k) :
    ∀ {d : ℕ} {p : List (Fin n)}, x ∈ p → p.length + d ≤ h + 1 →
      (labels C d p).card ≤ ∑ i ∈ range d, (k - 1) ^ i
  | 0, _, _, _ => by simp [labels]
  | d + 1, p, hxp, hph => by
    have hch := card_children_le hσ hC hlen hxp (by omega)
    calc (labels C (d + 1) p).card
        ≤ ((children C p).biUnion fun y => labels C d (y :: p)).card + 1 := card_insert_le _ _
      _ ≤ (∑ y ∈ children C p, (labels C d (y :: p)).card) + 1 :=
        Nat.add_le_add_right card_biUnion_le 1
      _ ≤ (∑ _y ∈ children C p, ∑ i ∈ range d, (k - 1) ^ i) + 1 :=
        Nat.add_le_add_right (sum_le_sum fun y _ =>
          card_labels_le hσ hC hlen (List.mem_cons_of_mem y hxp)
            (by rw [List.length_cons]; omega)) 1
      _ ≤ (k - 1) * (∑ i ∈ range d, (k - 1) ^ i) + 1 := by
        rw [sum_const, smul_eq_mul]
        exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hch) 1
      _ = ∑ i ∈ range (d + 1), (k - 1) ^ i := geom_sum_succ.symm

/-- The core of the forcing lemma: an assignment `γ` that agrees with `σ` on `A` and differs from
`σ` on the root path `p` violates a clause label below `p` if `p` has a cut in `A`. Follow the
children on which `γ` differs from `σ`; where this stops, `γ` agrees with the flip of `σ` on the
whole clause label. -/
theorem exists_mem_labels_eval_eq_false {φ : CNF (Fin n)} {σ γ : Fin n → Bool} {x : Fin n}
    {h : ℕ} {C : List (Fin n) → Clause (Fin n)} (hC : IsCriticalTreeAt φ σ x h C)
    {A : Finset (Fin n)} (hA : ∀ y ∈ A, γ y = σ y) :
    ∀ {d : ℕ} {p : List (Fin n)}, x ∈ p → p.length + d ≤ h + 1 → (∀ y ∈ p, γ y ≠ σ y) →
      Cut C A d p → ∃ c ∈ labels C d p, c.eval γ = false
  | 0, _, _, _, _, hcut => absurd hcut (cut_zero C A _)
  | d + 1, p, hxp, hph, hγ, hcut => by
    by_cases hall : ∀ y ∈ children C p, γ y = σ y
    · refine ⟨C p, mem_labels_succ.mpr (Or.inl rfl), ?_⟩
      have hflip := (hC p hxp (by omega)).2
      have hagree : ∀ l ∈ C p, γ l.1 = flipOn p.toFinset σ l.1 := by
        intro l hl
        by_cases hlp : l.1 ∈ p
        · rw [flipOn_apply_of_mem (List.mem_toFinset.mpr hlp)]
          have h1 := hγ l.1 hlp
          generalize γ l.1 = a at h1 ⊢
          generalize σ l.1 = b at h1 ⊢
          cases a <;> cases b <;> simp_all
        · rw [flipOn_apply_of_notMem (by simpa using hlp)]
          exact hall l.1 (mem_children.mpr ⟨List.mem_toFinset.mpr (List.mem_map_of_mem hl), hlp⟩)
      by_contra hne
      obtain ⟨l, hl, hls⟩ := (Clause.eval_eq_true_iff γ _).mp (by simpa using hne)
      have : (C p).eval (flipOn p.toFinset σ) = true :=
        (Clause.eval_eq_true_iff _ _).mpr ⟨l, hl, (hagree l hl).symm.trans hls⟩
      simp [hflip] at this
    · push Not at hall
      obtain ⟨y, hy, hyγ⟩ := hall
      have hyA : y ∉ A := fun hyA => hyγ (hA y hyA)
      have hcut' := ((cut_succ C A d p).mp hcut y hy).resolve_left hyA
      obtain ⟨c, hc, hcγ⟩ := exists_mem_labels_eval_eq_false hC hA (List.mem_cons_of_mem y hxp)
        (by rw [List.length_cons]; omega) (by simpa using ⟨hyγ, hγ⟩) hcut'
      exact ⟨c, mem_labels_succ.mpr (Or.inr ⟨y, hy, hc⟩), hcγ⟩

/-- **The forcing lemma for a rooted tree** (original: a strengthening of
[Scheder, Lemma 3.2][Scheder2021], whose proof uses only the number of clause-labelled nodes).
Let `σ` satisfy `φ`, whose clauses have at most `k` literals, and let `C` label a critical clause
tree of height `h` rooted at `x`. If every path from the root `x` to depth `h` meets `A` outside
the root, then `x = σ x` is `w`-implied under `σ` restricted to `A` whenever
`w ≥ ∑ i < h, (k - 1) ^ i`, a bound on the number of nodes of depth less than `h`. -/
theorem IsCriticalTreeAt.wImplied_of_cut {k h w : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool}
    {x : Fin n} {C : List (Fin n) → Clause (Fin n)} (hC : IsCriticalTreeAt φ σ x h C)
    (hσ : φ.eval σ = true) (hlen : ∀ c ∈ φ, c.length ≤ k) (hw : ∑ i ∈ range h, (k - 1) ^ i ≤ w)
    {A : Finset (Fin n)} (hcut : Cut C A h [x]) :
    WImplied φ w (PPZ.restrict σ A) x (σ x) := by
  have hx : x ∈ [x] := List.mem_singleton_self x
  have hxh : [x].length + h ≤ h + 1 := by simp [Nat.add_comm]
  refine ⟨(labels C h [x]).toList, fun c hc => mem_of_mem_labels hC hx hxh c (by simpa using hc),
    by simpa using (card_labels_le hσ hC hlen hx hxh).trans hw, ?_⟩
  intro γ hγ hψ
  have hA : ∀ y ∈ A, γ y = σ y := fun y hy => hγ y (σ y) (by simp [PPZ.restrict, hy])
  by_contra hne
  obtain ⟨c, hc, hcγ⟩ :=
    exists_mem_labels_eval_eq_false hC hA hx hxh (by simpa using hne) hcut
  have := (CNF.eval_eq_true_iff γ _).mp hψ c (by simpa using hc)
  simp [hcγ] at this

/-- **The forcing lemma** (original: a strengthening of [Scheder, Lemma 3.2][Scheder2021], whose
proof uses only the number of clause-labelled nodes). Let `σ` satisfy `φ`, whose clauses have at
most `k` literals, and let `C` label a critical clause tree of height `h`. If every path from the
root `x` to depth `h` meets `A` outside the root, then `x = σ x` is `w`-implied under `σ`
restricted to `A` whenever `w ≥ ∑ i < h, (k - 1) ^ i`, a bound on the number of nodes of depth
less than `h`. -/
theorem wImplied_of_cut {k h w : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool}
    {C : List (Fin n) → Clause (Fin n)} (hσ : φ.eval σ = true) (hC : IsCriticalTree φ σ h C)
    (hlen : ∀ c ∈ φ, c.length ≤ k) (hw : ∑ i ∈ range h, (k - 1) ^ i ≤ w)
    {A : Finset (Fin n)} {x : Fin n} (hcut : Cut C A h [x]) :
    WImplied φ w (PPZ.restrict σ A) x (σ x) :=
  (hC.isCriticalTreeAt x).wImplied_of_cut hσ hlen hw hcut

/-- **The forcing lemma** [Scheder, Lemma 3.2][Scheder2021]. Let `σ` satisfy the `k`-CNF formula
`φ` with `k ≥ 3`, let `C` label a critical clause tree of height `h`, and let
`w ≥ (k - 1) ^ (h + 1)`. If every path from the root `x` to a node at depth `h` contains a node
labelled in `A`, then `x = σ x` is `w`-implied under `σ` restricted to `A`. [Scheder][Scheder2021]
builds the tree for a unique satisfying assignment; here it only needs to exist, which
`h`-isolation guarantees (`exists_isCriticalTree`). For bounded resolution in place of
`w`-implication, the corresponding statements are
[Paturi, Pudlák, Saks, Zane, Definition 1 and Lemma 4][PaturiPudlakSaksZane2005]. -/
theorem wImplied_of_forall_descends {k h w : ℕ} (hk : 3 ≤ k) {φ : CNF (Fin n)}
    {σ : Fin n → Bool} {C : List (Fin n) → Clause (Fin n)} (hσ : φ.eval σ = true)
    (hC : IsCriticalTree φ σ h C) (hlen : ∀ c ∈ φ, c.length ≤ k) (hw : (k - 1) ^ (h + 1) ≤ w)
    {A : Finset (Fin n)} {x : Fin n}
    (hpath : ∀ s, Descends C h [x] s → ∃ y ∈ s ++ [x], y ∈ A) :
    WImplied φ w (PPZ.restrict σ A) x (σ x) := by
  by_cases hxA : x ∈ A
  · refine ⟨[], by simp, by simp, fun γ hγ _ => hγ x (σ x) (by simp [PPZ.restrict, hxA])⟩
  · refine wImplied_of_cut hσ hC hlen ?_ (cut_iff_forall_descends.mpr fun s hs => ?_)
    · calc ∑ i ∈ range h, (k - 1) ^ i ≤ (k - 1) ^ h :=
            (Nat.geomSum_lt (by omega) fun i hi => mem_range.mp hi).le
        _ ≤ (k - 1) ^ (h + 1) := Nat.pow_le_pow_right (by omega) h.le_succ
        _ ≤ w := hw
    · obtain ⟨y, hy, hyA⟩ := hpath s hs
      rcases List.mem_append.mp hy with hy | hy
      · exact ⟨y, hy, hyA⟩
      · exact absurd (List.mem_singleton.mp hy ▸ hyA) hxA

end Cslib.Complexity.PPSZ
