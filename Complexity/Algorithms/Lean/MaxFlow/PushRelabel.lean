/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.MaxFlow.Preflow
public import Complexity.Algorithms.Lean.MaxFlow.EdmondsKarp
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The Generic Push–Relabel Algorithm

The generic push–relabel maximum-flow algorithm of Goldberg and Tarjan ([GoldbergTarjan1988];
[CLRS2009], Section 26.4), with its operation bounds, its correctness at termination, and an
executable scheduler.

## Model and source mapping

* **Runs (`PushRelabel.State.IsRun`):** a state is a preflow with heights; a run is a list of
  operations (`Op.push u v`, `Op.relabel u`), each admissible (`Preflow.CanPush`,
  `Preflow.CanRelabel`) in the state it is applied to. Any order of admissible operations is a run,
  as in the generic algorithm of [CLRS2009], Section 26.4.
* **Counts:** `numRelabels`, `numSatPushes` (pushes moving the whole residual capacity) and
  `numNonsatPushes` count the operations of a run along the states it visits.
* **Executable (`pushRelabelWith`, `pushRelabel`):** repeatedly picks the first active vertex in a
  vertex list and pushes along its first admissible arc, else relabels it; `pushRelabel` on
  `Fin n` tabulates the state as a matrix and a vector after every step, so the kernel can evaluate
  it (`decide`).
* **Edge measure:** the bounds are stated with `N.symArcs` (ordered pairs `u ≠ v` with
  `cap u v + cap v u > 0`, the arcs that can ever be residual) and, in [CLRS2009]'s form, with
  `N.posArcs` (non-loop arcs of positive capacity, the edge set `E`).

## Main definitions

* `PushRelabel.State`, `PushRelabel.Op`, `PushRelabel.init`, `State.apply`, `State.Admissible`,
  `State.run`, `State.IsRun`, `State.IsSatPush`.
* `State.numRelabels`, `State.numSatPushes`, `State.numNonsatPushes`, `PushRelabel.maxOps`.
* `State.selectOp`, `State.loop`, `pushRelabelWith`, `pushRelabel`.

## Main results

* `PushRelabel.numRelabels_le`: at most `(|V| - 2)(2|V| - 1)` relabels; `numRelabels_lt`:
  fewer than `2|V|²` ([CLRS2009], Corollary 26.21).
* `PushRelabel.numSatPushes_le`: at most `|V| |N.symArcs|` saturating pushes;
  `numSatPushes_le_posArcs`: at most `2|V| |E|` ([CLRS2009], Lemma 26.22, which states `<`; the
  non-strict form also covers `E = ∅`).
* `PushRelabel.numNonsatPushes_le`: at most `(|V| - 2)(2|V| - 1) + (2|V| - 1)|V| |N.symArcs|`
  nonsaturating pushes; `numNonsatPushes_lt_posArcs`: fewer than `4|V|²(|V| + |E|)`
  ([CLRS2009], Lemma 26.23).
* `PushRelabel.length_le`: every run from the initial state has at most `maxOps N` operations, and
  `maxOps_le`: `maxOps N ≤ 4|V|²(1 + |E|)`, so the generic algorithm terminates after
  `O(|V|² (|E| + 1))` operations ([CLRS2009], Theorem 26.24, operation count).
* `PushRelabel.isMaxFlow_isMinCut_of_isRun`: a run under any selection rule that reaches a state
  admitting no operation ends with a maximum flow and a minimum gap cut of equal value
  ([CLRS2009], Lemma 26.14 and Theorem 26.18).
* `pushRelabelWith_correct`, `pushRelabel_correct`: the executable returns a maximum flow and a
  minimum cut of equal value after a run of at most `maxOps N` operations ([CLRS2009], Theorems
  26.18 and 26.24).

## Limitations

The bounds count operations; no cost is charged for selecting an operation, so this is not a
`TimeM` running-time bound. Only the generic algorithm is treated: the FIFO and relabel-to-front
(`O(|V|³)`) and highest-label (`O(|V|² √|E|)`) selection rules, gap and global relabelling
heuristics, and dynamic trees ([GoldbergTarjan1988]) are not formalized.

## References

* [A. V. Goldberg and R. E. Tarjan,
  *A New Approach to the Maximum-Flow Problem*][GoldbergTarjan1988]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

namespace Network

namespace PushRelabel

open Preflow

variable {V : Type*} [Fintype V] {N : Network V}

variable (N) in
/-- A state of the generic push–relabel algorithm: a preflow and vertex heights. -/
structure State where
  /-- The current preflow. -/
  flow : N.Preflow
  /-- The current heights (distance labels). -/
  height : V → ℕ

/-- A basic operation of the generic algorithm. -/
inductive Op (V : Type*) where
  /-- Push from the first vertex to the second. -/
  | push (u v : V)
  /-- Relabel a vertex. -/
  | relabel (u : V)
  deriving DecidableEq

/-- `o` is a push. -/
@[expose] def Op.IsPush {V : Type*} : Op V → Prop
  | .push _ _ => True
  | .relabel _ => False

/-- `o` is a relabel. -/
@[expose] def Op.IsRelabel {V : Type*} : Op V → Prop
  | .push _ _ => False
  | .relabel _ => True

instance {V : Type*} : DecidablePred (Op.IsPush (V := V))
  | .push _ _ => isTrue trivial
  | .relabel _ => isFalse id

instance {V : Type*} : DecidablePred (Op.IsRelabel (V := V))
  | .push _ _ => isFalse id
  | .relabel _ => isTrue trivial

variable [DecidableEq V]

variable (N) in
/-- The initial state: the initial preflow and heights ([CLRS2009], Section 26.4). -/
@[expose] def init : State N := ⟨Preflow.initial N, Preflow.initialHeight N⟩

namespace State

/-- The effect of an operation (meaningful when it is admissible). -/
@[expose] def apply (σ : State N) : Op V → State N
  | .push u v => ⟨σ.flow.push u v, σ.height⟩
  | .relabel u => ⟨σ.flow, σ.flow.relabel σ.height u⟩

/-- The precondition of an operation. -/
@[expose] def Admissible (σ : State N) : Op V → Prop
  | .push u v => σ.flow.CanPush σ.height u v
  | .relabel u => σ.flow.CanRelabel σ.height u

instance (σ : State N) : DecidablePred σ.Admissible
  | .push u v => inferInstanceAs (Decidable (σ.flow.CanPush σ.height u v))
  | .relabel u => inferInstanceAs (Decidable (σ.flow.CanRelabel σ.height u))

/-- The state reached by applying a list of operations in order. -/
@[expose] def run (σ : State N) : List (Op V) → State N
  | [] => σ
  | o :: os => (σ.apply o).run os

/-- `os` is a run of the generic algorithm from `σ`: each operation is admissible when applied. -/
@[expose] def IsRun (σ : State N) : List (Op V) → Prop
  | [] => True
  | o :: os => σ.Admissible o ∧ (σ.apply o).IsRun os

instance instDecidableIsRun : (σ : State N) → (os : List (Op V)) → Decidable (σ.IsRun os)
  | _, [] => isTrue trivial
  | σ, o :: os =>
    have := instDecidableIsRun (σ.apply o) os
    inferInstanceAs (Decidable (σ.Admissible o ∧ (σ.apply o).IsRun os))

/-- A saturating push: it moves the whole residual capacity of its arc. -/
@[expose] def IsSatPush (σ : State N) : Op V → Prop
  | .push u v => σ.flow.pushAmount u v = σ.flow.resCap u v
  | .relabel _ => False

instance (σ : State N) : DecidablePred σ.IsSatPush
  | .push u v => inferInstanceAs (Decidable (σ.flow.pushAmount u v = σ.flow.resCap u v))
  | .relabel _ => isFalse id

/-- The number of operations of `os` satisfying `p` in the state they are applied to. -/
@[expose] def countOps (p : State N → Op V → Prop) [∀ σ o, Decidable (p σ o)] (σ : State N) :
    List (Op V) → ℕ
  | [] => 0
  | o :: os => (if p σ o then 1 else 0) + (σ.apply o).countOps p os

/-- The number of relabels in a run. -/
@[expose] def numRelabels (σ : State N) (os : List (Op V)) : ℕ :=
  σ.countOps (fun _ o => o.IsRelabel) os

/-- The number of saturating pushes in a run. -/
@[expose] def numSatPushes (σ : State N) (os : List (Op V)) : ℕ :=
  σ.countOps IsSatPush os

/-- The number of nonsaturating pushes in a run. -/
@[expose] def numNonsatPushes (σ : State N) (os : List (Op V)) : ℕ :=
  σ.countOps (fun σ o => o.IsPush ∧ ¬ σ.IsSatPush o) os

/-- The number of saturating pushes from `a` to `b` in a run. -/
@[expose] def numSatPushesAt (a b : V) (σ : State N) (os : List (Op V)) : ℕ :=
  σ.countOps (fun σ o => o = .push a b ∧ σ.IsSatPush o) os

@[simp] theorem apply_push_flow (σ : State N) (u v : V) :
    (σ.apply (.push u v)).flow = σ.flow.push u v := rfl

@[simp] theorem apply_push_height (σ : State N) (u v : V) :
    (σ.apply (.push u v)).height = σ.height := rfl

@[simp] theorem apply_relabel_flow (σ : State N) (u : V) :
    (σ.apply (.relabel u)).flow = σ.flow := rfl

@[simp] theorem apply_relabel_height (σ : State N) (u : V) :
    (σ.apply (.relabel u)).height = σ.flow.relabel σ.height u := rfl

@[simp] theorem run_nil (σ : State N) : σ.run [] = σ := rfl

@[simp] theorem run_cons (σ : State N) (o : Op V) (os : List (Op V)) :
    σ.run (o :: os) = (σ.apply o).run os := rfl

@[simp] theorem isRun_nil (σ : State N) : σ.IsRun [] := trivial

theorem isRun_cons {σ : State N} {o : Op V} {os : List (Op V)} :
    σ.IsRun (o :: os) ↔ σ.Admissible o ∧ (σ.apply o).IsRun os := Iff.rfl

theorem numRelabels_cons (σ : State N) (o : Op V) (os : List (Op V)) :
    σ.numRelabels (o :: os) = (if o.IsRelabel then 1 else 0) + (σ.apply o).numRelabels os := rfl

theorem numSatPushes_cons (σ : State N) (o : Op V) (os : List (Op V)) :
    σ.numSatPushes (o :: os) = (if σ.IsSatPush o then 1 else 0) + (σ.apply o).numSatPushes os :=
  rfl

theorem numNonsatPushes_cons (σ : State N) (o : Op V) (os : List (Op V)) :
    σ.numNonsatPushes (o :: os) =
      (if o.IsPush ∧ ¬ σ.IsSatPush o then 1 else 0) + (σ.apply o).numNonsatPushes os := rfl

theorem numSatPushesAt_cons (a b : V) (σ : State N) (o : Op V) (os : List (Op V)) :
    σ.numSatPushesAt a b (o :: os) =
      (if o = .push a b ∧ σ.IsSatPush o then 1 else 0) + (σ.apply o).numSatPushesAt a b os := rfl

/-- Every operation of a run is a relabel, a saturating push or a nonsaturating push. -/
theorem length_eq (σ : State N) (os : List (Op V)) :
    os.length = σ.numRelabels os + σ.numSatPushes os + σ.numNonsatPushes os := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih =>
    rw [numRelabels_cons, numSatPushes_cons, numNonsatPushes_cons, List.length_cons,
      ih (σ.apply o)]
    cases o with
    | relabel u =>
      have h1 : (Op.relabel u : Op V).IsRelabel := trivial
      have h2 : ¬ σ.IsSatPush (.relabel u) := id
      have h3 : ¬ ((Op.relabel u : Op V).IsPush ∧ ¬ σ.IsSatPush (.relabel u)) := fun h => h.1
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3]
      omega
    | push u v =>
      have h1 : ¬ (Op.push u v : Op V).IsRelabel := id
      rw [ite_eq_right h1]
      by_cases hs : σ.IsSatPush (.push u v)
      · have h3 : ¬ ((Op.push u v : Op V).IsPush ∧ ¬ σ.IsSatPush (.push u v)) := fun h => h.2 hs
        rw [ite_eq_left hs, ite_eq_right h3]
        omega
      · have h3 : (Op.push u v : Op V).IsPush ∧ ¬ σ.IsSatPush (.push u v) := ⟨trivial, hs⟩
        rw [ite_eq_right hs, ite_eq_left h3]
        omega

/-! ### Invariants -/

/-- The invariant of the generic algorithm: a valid labeling with heights at most `2|V| - 1`. -/
structure Inv (σ : State N) : Prop where
  /-- The heights form a valid labeling. -/
  valid : σ.flow.IsValidLabeling σ.height
  /-- Every height is at most `2|V| - 1` ([CLRS2009], Lemma 26.20). -/
  height_le : ∀ v, σ.height v ≤ 2 * Fintype.card V - 1

theorem Inv.apply {σ : State N} (hσ : σ.Inv) {o : Op V} (ho : σ.Admissible o) :
    (σ.apply o).Inv := by
  cases o with
  | push u v => exact ⟨hσ.valid.push ho, hσ.height_le⟩
  | relabel u =>
    have hv := hσ.valid.relabel ho
    refine ⟨hv, fun x => ?_⟩
    by_cases hx : x = u
    · subst hx
      exact hv.le_of_excess_pos ho.active.2.2
    · change σ.flow.relabel σ.height u x ≤ _
      rw [relabel_of_ne _ _ hx]
      exact hσ.height_le x

theorem Inv.run {σ : State N} (hσ : σ.Inv) {os : List (Op V)} (hos : σ.IsRun os) :
    (σ.run os).Inv := by
  induction os generalizing σ with
  | nil => exact hσ
  | cons o os ih => exact ih (hσ.apply hos.1) hos.2

omit [DecidableEq V] in
/-- A state satisfying the invariant and admitting no operation has no active vertex
([CLRS2009], Lemma 26.14). -/
theorem Inv.not_isActive {σ : State N} (hσ : σ.Inv) (hstop : ∀ o, ¬ σ.Admissible o) (v : V) :
    ¬ σ.flow.IsActive v := fun hv => by
  rcases hσ.valid.exists_canPush_or_canRelabel hv with ⟨w, hw⟩ | hr
  · exact hstop (.push v w) hw
  · exact hstop (.relabel v) hr

theorem le_height_apply {σ : State N} {o : Op V} (ho : σ.Admissible o) (x : V) :
    σ.height x ≤ (σ.apply o).height x := by
  cases o with
  | push u v => exact le_rfl
  | relabel u => exact CanRelabel.le_relabel ho x

/-! ### Relabels -/

theorem numRelabels_add_sum_le {σ : State N} {os : List (Op V)} (hos : σ.IsRun os) :
    σ.numRelabels os + ∑ v, σ.height v ≤ ∑ v, (σ.run os).height v := by
  induction os generalizing σ with
  | nil => simp [numRelabels, countOps]
  | cons o os ih =>
    have h1 := ih hos.2
    have hstep : (∑ v, σ.height v) + (if o.IsRelabel then 1 else 0) ≤
        ∑ v, (σ.apply o).height v := by
      cases o with
      | push u v => simp [apply, Op.IsRelabel]
      | relabel u =>
        have hlt : ∑ v, σ.height v < ∑ v, (σ.apply (.relabel u)).height v :=
          Finset.sum_lt_sum (fun x _ => le_height_apply hos.1 x)
            ⟨u, Finset.mem_univ _, by
              change σ.height u < σ.flow.relabel σ.height u u
              rw [relabel_self]
              exact CanRelabel.lt_relabelHeight hos.1⟩
        rw [ite_eq_left (show (Op.relabel u : Op V).IsRelabel from trivial)]
        omega
    rw [numRelabels_cons, run_cons]
    omega

omit [DecidableEq V] in
theorem sum_height_le {σ : State N} (hσ : σ.Inv) :
    ∑ v, σ.height v ≤ Fintype.card V + (Fintype.card V - 2) * (2 * Fintype.card V - 1) := by
  classical
  have hst := hσ.valid.source_ne_sink
  have hs : N.s ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  have ht : N.t ∈ (Finset.univ.erase N.s : Finset V) :=
    Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hs, ← Finset.add_sum_erase _ _ ht, hσ.valid.source,
    hσ.valid.sink]
  have hcard : ((Finset.univ.erase N.s).erase N.t).card = Fintype.card V - 2 := by grind
  have := Finset.sum_le_card_nsmul ((Finset.univ.erase N.s).erase N.t) (fun v => σ.height v)
    (2 * Fintype.card V - 1) (fun v _ => hσ.height_le v)
  rw [hcard, Nat.nsmul_eq_mul] at this
  omega

/-! ### Saturating pushes -/

/-- The bookkeeping behind the saturating-push bound: after `c` saturating pushes from `a` to `b`,
heights have grown by about `2c` ([CLRS2009], proof of Lemma 26.22). -/
def PairInv (a b : V) (σ : State N) (c : ℕ) : Prop :=
  (σ.flow.resCap a b = 0 → 2 * c ≤ σ.height a + 1) ∧
    (0 < σ.flow.resCap a b → 2 * c ≤ σ.height b)

theorem PairInv.apply {a b : V} {σ : State N} {c : ℕ} (hc : σ.PairInv a b c) {o : Op V}
    (ho : σ.Admissible o) :
    (σ.apply o).PairInv a b (c + if o = .push a b ∧ σ.IsSatPush o then 1 else 0) := by
  cases o with
  | relabel u =>
    have hfalse : ¬ (Op.relabel u = .push a b ∧ σ.IsSatPush (.relabel u)) := fun h => by
      cases h.1
    rw [ite_eq_right hfalse, Nat.add_zero]
    have hle := le_height_apply ho
    refine ⟨fun h0 => ?_, fun hpos => ?_⟩
    · have := hc.1 h0
      have := hle a
      omega
    · have := hc.2 hpos
      have := hle b
      omega
  | push u v =>
    have hp : σ.flow.CanPush σ.height u v := ho
    have huv := hp.ne
    have hδ := σ.flow.pushAmount_le_resCap u v
    have hδpos := hp.pushAmount_pos
    simp only [PairInv, apply_push_flow, apply_push_height]
    by_cases hab : u = a ∧ v = b
    · obtain ⟨rfl, rfl⟩ := hab
      have hr := σ.flow.resCap_push_self huv
      have hc2 := hc.2 hp.resCap_pos
      have heq := hp.height_eq
      by_cases hsat : σ.IsSatPush (.push u v)
      · have hsat' : σ.flow.pushAmount u v = σ.flow.resCap u v := hsat
        rw [ite_eq_left ⟨rfl, hsat⟩]
        refine ⟨fun _ => ?_, fun hpos => ?_⟩
        · omega
        · omega
      · have hsat' : σ.flow.pushAmount u v ≠ σ.flow.resCap u v := hsat
        rw [ite_eq_right fun h => hsat h.2, Nat.add_zero]
        refine ⟨fun h0 => ?_, fun _ => hc2⟩
        omega
    · have hne : ¬ (Op.push u v = .push a b ∧ σ.IsSatPush (.push u v)) := fun h => by
        cases h.1
        exact hab ⟨rfl, rfl⟩
      rw [ite_eq_right hne, Nat.add_zero]
      by_cases hba : u = b ∧ v = a
      · obtain ⟨rfl, rfl⟩ := hba
        have hr := σ.flow.resCap_push_swap huv
        have heq := hp.height_eq
        refine ⟨fun h0 => by omega, fun _ => ?_⟩
        by_cases h0 : σ.flow.resCap v u = 0
        · have := hc.1 h0
          omega
        · have := hc.2 (Nat.pos_of_ne_zero h0)
          omega
      · have hr := σ.flow.resCap_push_of_ne (u := u) (v := v) (x := a) (y := b)
          (fun h => hab ⟨h.1.symm, h.2.symm⟩) (fun h => hba ⟨h.2.symm, h.1.symm⟩)
        rw [hr]
        exact hc

theorem PairInv.run {a b : V} {σ : State N} {c : ℕ} (hc : σ.PairInv a b c) {os : List (Op V)}
    (hos : σ.IsRun os) : (σ.run os).PairInv a b (c + σ.numSatPushesAt a b os) := by
  induction os generalizing σ c with
  | nil => simpa [numSatPushesAt, countOps] using hc
  | cons o os ih =>
    have := ih (hc.apply hos.1) hos.2
    rw [numSatPushesAt_cons, run_cons, ← Nat.add_assoc]
    exact this

/-- At most `|V|` saturating pushes from `a` to `b` ([CLRS2009], proof of Lemma 26.22). -/
theorem numSatPushesAt_le {σ : State N} (hσ : σ.Inv) {os : List (Op V)} (hos : σ.IsRun os)
    (a b : V) : σ.numSatPushesAt a b os ≤ Fintype.card V := by
  have h0 : σ.PairInv a b 0 := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  have hrun := h0.run hos
  rw [Nat.zero_add] at hrun
  have hinv := hσ.run hos
  have ha := hinv.height_le a
  have hb := hinv.height_le b
  by_cases h : (σ.run os).flow.resCap a b = 0
  · have := hrun.1 h
    omega
  · have := hrun.2 (Nat.pos_of_ne_zero h)
    omega

theorem numSatPushes_eq_sum (σ : State N) (os : List (Op V)) :
    σ.numSatPushes os = ∑ e : V × V, σ.numSatPushesAt e.1 e.2 os := by
  induction os generalizing σ with
  | nil => simp [numSatPushes, numSatPushesAt, countOps]
  | cons o os ih =>
    rw [numSatPushes_cons, ih]
    simp only [numSatPushesAt_cons]
    rw [Finset.sum_add_distrib]
    congr 1
    cases o with
    | relabel u =>
      have : ¬ σ.IsSatPush (.relabel u) := fun h => h
      simp [this]
    | push u v =>
      rw [Finset.sum_eq_single (u, v)]
      · simp
      · intro e _ he
        refine ite_eq_right fun ⟨h, _⟩ => ?_
        obtain ⟨h1, h2⟩ := Op.push.inj h
        exact he (Prod.ext h1.symm h2.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h

theorem numSatPushesAt_eq_zero {a b : V} (hab : (a, b) ∉ N.symArcs) (σ : State N)
    {os : List (Op V)} (hos : σ.IsRun os) : σ.numSatPushesAt a b os = 0 := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih =>
    rw [numSatPushesAt_cons, ih _ hos.2, Nat.add_zero, ite_eq_right]
    rintro ⟨rfl, _⟩
    have hp : σ.flow.CanPush σ.height a b := hos.1
    apply hab
    have hle := σ.flow.resCap_le_cap_add_cap a b
    have := hp.resCap_pos
    simp only [symArcs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp.ne, by omega⟩

theorem numSatPushes_le_of_inv {σ : State N} (hσ : σ.Inv) {os : List (Op V)} (hos : σ.IsRun os) :
    σ.numSatPushes os ≤ Fintype.card V * N.symArcs.card := by
  rw [numSatPushes_eq_sum, ← Finset.sum_subset (Finset.subset_univ N.symArcs)
    (fun e _ he => numSatPushesAt_eq_zero he σ hos)]
  have := Finset.sum_le_card_nsmul N.symArcs (fun e : V × V => σ.numSatPushesAt e.1 e.2 os)
    (Fintype.card V) (fun e _ => numSatPushesAt_le hσ hos e.1 e.2)
  rw [Nat.nsmul_eq_mul] at this
  rw [Nat.mul_comm]
  exact this

/-! ### Nonsaturating pushes -/

/-- The potential `Φ = ∑_{v active} h(v)` of [CLRS2009], proof of Lemma 26.23. -/
def potential (σ : State N) : ℕ :=
  ∑ v, if σ.flow.IsActive v then σ.height v else 0

private theorem sum_split_two {u v : V} (huv : u ≠ v) (g : V → ℕ) :
    ∑ x, g x = g u + g v + ∑ x ∈ (Finset.univ.erase u).erase v, g x := by
  have hu : u ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  have hv : v ∈ (Finset.univ.erase u : Finset V) :=
    Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hu, ← Finset.add_sum_erase _ _ hv, Nat.add_assoc]

/-- One admissible operation raises the potential by at most the height increase, plus `2|V| - 1`
for a saturating push, and lowers it by at least one for a nonsaturating push ([CLRS2009], proof of
Lemma 26.23). -/
theorem potential_apply_le {σ : State N} (hσ : σ.Inv) {o : Op V} (ho : σ.Admissible o) :
    (σ.apply o).potential + ∑ v, σ.height v + (if o.IsPush ∧ ¬ σ.IsSatPush o then 1 else 0) ≤
      σ.potential + ∑ v, (σ.apply o).height v +
        (2 * Fintype.card V - 1) * (if σ.IsSatPush o then 1 else 0) := by
  cases o with
  | relabel u =>
    have hns : ¬ ((Op.relabel u : Op V).IsPush ∧ ¬ σ.IsSatPush (.relabel u)) := fun h => h.1
    have hs : ¬ σ.IsSatPush (.relabel u) := id
    rw [ite_eq_right hns, ite_eq_right hs, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
    have hpt : ∀ x, (if (σ.apply (.relabel u)).flow.IsActive x then
        (σ.apply (.relabel u)).height x else 0) + σ.height x ≤
        (if σ.flow.IsActive x then σ.height x else 0) + (σ.apply (.relabel u)).height x := by
      intro x
      have := le_height_apply ho x
      rw [apply_relabel_flow]
      split_ifs <;> omega
    have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpt x
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
    exact this
  | push u v =>
    have hp : σ.flow.CanPush σ.height u v := ho
    have huv := hp.ne
    have hδ := σ.flow.pushAmount_le_resCap u v
    have hδpos := hp.pushAmount_pos
    have hdec := sum_split_two huv
    have hpu : (Op.push u v : Op V).IsPush := trivial
    change (∑ x, if (σ.flow.push u v).IsActive x then σ.height x else 0) + ∑ v, σ.height v +
        (if (Op.push u v : Op V).IsPush ∧ ¬ σ.IsSatPush (.push u v) then 1 else 0) ≤
      (∑ x, if σ.flow.IsActive x then σ.height x else 0) + ∑ v, σ.height v +
        (2 * Fintype.card V - 1) * (if σ.IsSatPush (.push u v) then 1 else 0)
    rw [hdec (fun x => if (σ.flow.push u v).IsActive x then σ.height x else 0),
      hdec (fun x => if σ.flow.IsActive x then σ.height x else 0)]
    have hrest : ∑ x ∈ (Finset.univ.erase u).erase v,
        (if (σ.flow.push u v).IsActive x then σ.height x else 0) =
        ∑ x ∈ (Finset.univ.erase u).erase v, (if σ.flow.IsActive x then σ.height x else 0) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxv := Finset.ne_of_mem_erase hx
      have hxu := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
      simp only [isActive_push_of_ne σ.flow hxu hxv]
    have hu_act : σ.flow.IsActive u := hp.active
    have hex := σ.flow.excess_push_self huv
    have hTu : (if (σ.flow.push u v).IsActive u then σ.height u else 0) ≤ σ.height u := by
      split_ifs <;> omega
    have hTv : (if (σ.flow.push u v).IsActive v then σ.height v else 0) ≤ σ.height v := by
      split_ifs <;> omega
    rw [ite_eq_left hu_act]
    by_cases hsat : σ.IsSatPush (.push u v)
    · have hns : ¬ ((Op.push u v : Op V).IsPush ∧ ¬ σ.IsSatPush (.push u v)) := fun h => h.2 hsat
      rw [ite_eq_right hns, ite_eq_left hsat, Nat.mul_one, Nat.add_zero]
      have hv_le := hσ.height_le v
      have : 0 ≤ (if σ.flow.IsActive v then σ.height v else 0) := Nat.zero_le _
      omega
    · have hns : (Op.push u v : Op V).IsPush ∧ ¬ σ.IsSatPush (.push u v) := ⟨hpu, hsat⟩
      rw [ite_eq_left hns, ite_eq_right hsat, Nat.mul_zero, Nat.add_zero]
      have hsat' : σ.flow.pushAmount u v ≠ σ.flow.resCap u v := hsat
      -- a nonsaturating push moves the whole excess of `u`
      have hamt : (σ.flow.pushAmount u v : ℤ) = σ.flow.excess u := by grind [pushAmount]
      have hTu0 : ¬ (σ.flow.push u v).IsActive u := fun h => by
        have := h.2.2
        omega
      rw [ite_eq_right hTu0]
      have heq := hp.height_eq
      have : 0 ≤ (if σ.flow.IsActive v then σ.height v else 0) := Nat.zero_le _
      omega

theorem numNonsatPushes_add_le {σ : State N} (hσ : σ.Inv) {os : List (Op V)} (hos : σ.IsRun os) :
    σ.numNonsatPushes os + (σ.run os).potential + ∑ v, σ.height v ≤
      σ.potential + ∑ v, (σ.run os).height v +
        (2 * Fintype.card V - 1) * σ.numSatPushes os := by
  induction os generalizing σ with
  | nil => simp [numNonsatPushes, countOps]
  | cons o os ih =>
    have h1 := ih (hσ.apply hos.1) hos.2
    have h2 := potential_apply_le hσ hos.1
    rw [numNonsatPushes_cons, numSatPushes_cons, run_cons, Nat.mul_add]
    omega

end State

/-! ### Bounds from the initial state -/

open State

theorem inv_init (hst : N.s ≠ N.t) : (init N).Inv := by
  refine ⟨isValidLabeling_initial hst, fun v => ?_⟩
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  change Preflow.initialHeight N v ≤ _
  unfold Preflow.initialHeight
  split_ifs <;> omega

theorem sum_height_init : ∑ v, (init N).height v = Fintype.card V := by
  change ∑ v, Preflow.initialHeight N v = _
  unfold Preflow.initialHeight
  rw [Finset.sum_ite_eq' Finset.univ N.s, ite_eq_left (Finset.mem_univ _)]

theorem potential_init : (init N).potential = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  change (if (Preflow.initial N).IsActive x then Preflow.initialHeight N x else 0) = 0
  split_ifs with hx
  · simp [Preflow.initialHeight, hx.1]
  · rfl

/-- **Relabel bound** ([CLRS2009], Corollary 26.21): a run from the initial state performs at most
`(|V| - 2)(2|V| - 1)` relabels. -/
theorem numRelabels_le (hst : N.s ≠ N.t) {os : List (Op V)} (hos : (init N).IsRun os) :
    (init N).numRelabels os ≤ (Fintype.card V - 2) * (2 * Fintype.card V - 1) := by
  have h1 := numRelabels_add_sum_le hos
  have h2 := sum_height_le ((inv_init hst).run hos)
  rw [sum_height_init] at h1
  omega

/-- **Relabel bound**, [CLRS2009]'s form (Corollary 26.21): fewer than `2|V|²` relabels. -/
theorem numRelabels_lt (hst : N.s ≠ N.t) {os : List (Op V)} (hos : (init N).IsRun os) :
    (init N).numRelabels os < 2 * Fintype.card V ^ 2 := by
  have h := numRelabels_le hst hos
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  have hle : (Fintype.card V - 2) * (2 * Fintype.card V - 1) ≤
      (Fintype.card V - 1) * (2 * Fintype.card V) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlt : (Fintype.card V - 1) * (2 * Fintype.card V) <
      Fintype.card V * (2 * Fintype.card V) :=
    Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have heq : Fintype.card V * (2 * Fintype.card V) = 2 * Fintype.card V ^ 2 := by ring
  omega

/-- **Saturating-push bound** ([CLRS2009], Lemma 26.22): a run from the initial state performs at
most `|V|` saturating pushes per pair of `N.symArcs`. -/
theorem numSatPushes_le (hst : N.s ≠ N.t) {os : List (Op V)} (hos : (init N).IsRun os) :
    (init N).numSatPushes os ≤ Fintype.card V * N.symArcs.card :=
  numSatPushes_le_of_inv (inv_init hst) hos

/-- **Saturating-push bound**, [CLRS2009]'s form (Lemma 26.22): at most `2|V| |E|` saturating
pushes, where `E = N.posArcs`. The source states `<`; the non-strict form also covers `E = ∅`. -/
theorem numSatPushes_le_posArcs (hst : N.s ≠ N.t) {os : List (Op V)} (hos : (init N).IsRun os) :
    (init N).numSatPushes os ≤ 2 * Fintype.card V * N.posArcs.card := by
  have h := numSatPushes_le hst hos
  have h2 := Nat.mul_le_mul_left (Fintype.card V) N.card_symArcs_le_two_mul_posArcs
  rw [Nat.mul_left_comm, ← Nat.mul_assoc] at h2
  omega

/-- **Nonsaturating-push bound** ([CLRS2009], Lemma 26.23): a run from the initial state performs at
most `(|V| - 2)(2|V| - 1) + (2|V| - 1) |V| |N.symArcs|` nonsaturating pushes. -/
theorem numNonsatPushes_le (hst : N.s ≠ N.t) {os : List (Op V)} (hos : (init N).IsRun os) :
    (init N).numNonsatPushes os ≤ (Fintype.card V - 2) * (2 * Fintype.card V - 1) +
      (2 * Fintype.card V - 1) * (Fintype.card V * N.symArcs.card) := by
  have h0 := inv_init (N := N) hst
  have h1 := numNonsatPushes_add_le h0 hos
  have h2 := sum_height_le (h0.run hos)
  have h3 := Nat.mul_le_mul_left (2 * Fintype.card V - 1) (numSatPushes_le hst hos)
  rw [potential_init, sum_height_init] at h1
  omega

/-- **Nonsaturating-push bound**, [CLRS2009]'s form (Lemma 26.23): fewer than `4|V|²(|V| + |E|)`
nonsaturating pushes, where `E = N.posArcs`. -/
theorem numNonsatPushes_lt_posArcs (hst : N.s ≠ N.t) {os : List (Op V)}
    (hos : (init N).IsRun os) :
    (init N).numNonsatPushes os < 4 * Fintype.card V ^ 2 * (Fintype.card V + N.posArcs.card) := by
  have h := numNonsatPushes_le hst hos
  have hS := N.card_symArcs_le_two_mul_posArcs
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, N.posArcs.card = P := ⟨_, rfl⟩
  rw [hn] at h hpos ⊢
  rw [hP] at hS ⊢
  have h1 : (n - 2) * (2 * n - 1) ≤ n * (2 * n) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 * n - 1) * (n * N.symArcs.card) ≤ (2 * n) * (n * (2 * P)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hS)
  have h3 : n * (2 * n) < 4 * n ^ 2 * n := by
    have h4 : n * (2 * n) = 2 * n ^ 2 := by ring
    have h5 : 4 * n ^ 2 ≤ 4 * n ^ 2 * n := Nat.le_mul_of_pos_right _ hpos
    have h6 : 0 < n ^ 2 := Nat.pow_pos hpos
    omega
  have h6 : 2 * n * (n * (2 * P)) = 4 * n ^ 2 * P := by ring
  have h7 : 4 * n ^ 2 * (n + P) = 4 * n ^ 2 * n + 4 * n ^ 2 * P := by ring
  omega

/-- The total operation bound `2 (|V| - 2)(2|V| - 1) + 2|V| · |V| |N.symArcs|`; at most
`4|V|²(1 + |E|)` by `maxOps_le`. -/
@[expose] def maxOps (N : Network V) : ℕ :=
  2 * ((Fintype.card V - 2) * (2 * Fintype.card V - 1)) +
    2 * Fintype.card V * (Fintype.card V * N.symArcs.card)

/-- `maxOps N ≤ 4|V|²(1 + |E|)` with `E = N.posArcs`, so `maxOps N = O(|V|² (|E| + 1))`. -/
theorem maxOps_le (N : Network V) :
    maxOps N ≤ 4 * Fintype.card V ^ 2 * (1 + N.posArcs.card) := by
  have hS := N.card_symArcs_le_two_mul_posArcs
  unfold maxOps
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, N.posArcs.card = P := ⟨_, rfl⟩
  rw [hn, hP]
  rw [hP] at hS
  have h1 : (n - 2) * (2 * n - 1) ≤ n * (2 * n) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 2 * n * (n * N.symArcs.card) ≤ 2 * n * (n * (2 * P)) := by gcongr
  have h3 : n * (2 * n) = 2 * n ^ 2 := by ring
  have h4 : 2 * n * (n * (2 * P)) = 4 * n ^ 2 * P := by ring
  have h5 : 4 * n ^ 2 * (1 + P) = 4 * n ^ 2 + 4 * n ^ 2 * P := by ring
  omega

/-- **Operation bound** ([CLRS2009], Theorem 26.24, operation count): every run of the generic
algorithm from the initial state has at most `maxOps N ≤ 4|V|²(1 + |E|)` operations
(`maxOps_le`). -/
theorem length_le (hst : N.s ≠ N.t) {os : List (Op V)} (hos : (init N).IsRun os) :
    os.length ≤ maxOps N := by
  rw [length_eq (init N) os]
  have h1 := numRelabels_le hst hos
  have h2 := numSatPushes_le hst hos
  have h3 := numNonsatPushes_le hst hos
  unfold maxOps
  have h4 : (2 * Fintype.card V - 1) * (Fintype.card V * N.symArcs.card) + Fintype.card V *
      N.symArcs.card ≤ 2 * Fintype.card V * (Fintype.card V * N.symArcs.card) := by
    have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
    rw [← Nat.succ_mul]
    refine Nat.mul_le_mul_right _ ?_
    omega
  omega

/-- **Correctness of every run** ([CLRS2009], Lemma 26.14 and Theorem 26.18): if a run of the
generic algorithm from the initial state, under any selection rule, reaches a state admitting no
operation, then its preflow is a maximum flow and the gap cut of its heights is a minimum cut of
the same value. By `length_le`, every run reaches such a state within `maxOps N` operations. -/
theorem isMaxFlow_isMinCut_of_isRun (hst : N.s ≠ N.t) {os : List (Op V)}
    (hos : (init N).IsRun os) (hstop : ∀ o, ¬ ((init N).run os).Admissible o) :
    ∃ hz : ∀ v, v ≠ N.s → v ≠ N.t → ((init N).run os).flow.excess v = 0,
      (((init N).run os).flow.toFlow hz).IsMaxFlow ∧
        N.IsMinCut (gapCut ((init N).run os).height) ∧
        (((init N).run os).flow.toFlow hz).value =
          (N.cutCapacity (gapCut ((init N).run os).height) : ℤ) := by
  have hinv := (inv_init hst).run hos
  have hz := excess_eq_zero_of_forall_not_isActive _ (hinv.not_isActive hstop)
  exact ⟨hz, hinv.valid.isMaxFlow_toFlow hz, hinv.valid.isMinCut_gapCut hz⟩

/-! ### An executable scheduler -/

namespace State

/-- The operation chosen by scanning `vs`: the first active vertex `u` of `vs` pushes to the first
`v` of `vs` with `(u, v)` admissible, or is relabelled if there is none; `none` if no vertex of `vs`
is active. -/
@[expose] def selectOp (vs : List V) (σ : State N) : Option (Op V) :=
  match vs.find? fun u => decide (σ.flow.IsActive u) with
  | none => none
  | some u =>
    match vs.find? fun v => decide (0 < σ.flow.resCap u v ∧ σ.height u = σ.height v + 1) with
    | some v => some (.push u v)
    | none => some (.relabel u)

theorem not_isActive_of_selectOp_eq_none {vs : List V} {σ : State N} (h : σ.selectOp vs = none)
    {u : V} (hu : u ∈ vs) : ¬ σ.flow.IsActive u := by
  unfold selectOp at h
  split at h
  · rename_i hf
    intro hact
    exact List.find?_eq_none.mp hf u hu (decide_eq_true hact)
  · split at h <;> cases h

theorem admissible_of_selectOp_eq_some {vs : List V} (hvs : ∀ v, v ∈ vs) {σ : State N}
    (hσ : σ.flow.IsValidLabeling σ.height) {o : Op V} (h : σ.selectOp vs = some o) :
    σ.Admissible o := by
  unfold selectOp at h
  split at h
  · cases h
  · rename_i u hu
    have hact : σ.flow.IsActive u :=
      of_decide_eq_true (List.find?_some (p := fun u => decide (σ.flow.IsActive u)) hu)
    split at h
    · rename_i v hv
      cases h
      have hp := of_decide_eq_true (List.find?_some
        (p := fun v => decide (0 < σ.flow.resCap u v ∧ σ.height u = σ.height v + 1)) hv)
      exact ⟨hact, hp.1, hp.2⟩
    · rename_i hv
      cases h
      refine ⟨hact, fun v hpos => ?_⟩
      have h1 := hσ.le_add_one u v hpos
      have h2 := List.find?_eq_none.mp hv v (hvs v)
      have h3 : ¬ (0 < σ.flow.resCap u v ∧ σ.height u = σ.height v + 1) := fun h =>
        h2 (decide_eq_true h)
      omega

/-- Apply operations chosen by `selectOp vs` until none applies or `fuel` runs out, normalizing the
state with `norm` after every step; returns the operations performed and the final state.
Executable instances use `norm` to tabulate the state (see `PushRelabel.tabulate`); correctness
assumes that `norm` is the identity. -/
@[expose] def loop (vs : List V) (norm : State N → State N) :
    ℕ → State N → List (Op V) × State N
  | 0, σ => ([], σ)
  | fuel + 1, σ =>
    match σ.selectOp vs with
    | none => ([], σ)
    | some o =>
      let r := loop vs norm fuel (norm (σ.apply o))
      (o :: r.1, r.2)

theorem loop_spec {vs : List V} (hvs : ∀ v, v ∈ vs) {norm : State N → State N}
    (hnorm : ∀ σ, norm σ = σ) :
    ∀ (fuel : ℕ) (σ : State N), σ.Inv →
      (loop vs norm fuel σ).2 = σ.run (loop vs norm fuel σ).1 ∧ σ.IsRun (loop vs norm fuel σ).1 ∧
        ((loop vs norm fuel σ).1.length < fuel → ∀ v, ¬ (loop vs norm fuel σ).2.flow.IsActive v)
  | 0, σ, _ => ⟨rfl, trivial, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | fuel + 1, σ, hσ => by
    cases ho : σ.selectOp vs with
    | none =>
      simp only [loop, ho]
      exact ⟨rfl, trivial, fun _ v => not_isActive_of_selectOp_eq_none ho (hvs v)⟩
    | some o =>
      have hadm := admissible_of_selectOp_eq_some hvs hσ.valid ho
      obtain ⟨h0, h1, h2⟩ := loop_spec hvs hnorm fuel (σ.apply o) (hσ.apply hadm)
      simp only [loop, ho, hnorm, List.length_cons, run_cons]
      exact ⟨h0, ⟨hadm, h1⟩, fun hlen => h2 (by omega)⟩

end State

/-! ### Tabulated states on `Fin n` -/

/-- Tabulate a preflow on `Fin n` as an `n × n` matrix. -/
@[expose] def tabulateFlow {n : ℕ} {N : Network (Fin n)} (f : N.Preflow) : N.Preflow :=
  let mat : Vector (Vector ℕ n) n := Vector.ofFn fun u => Vector.ofFn fun v => f u v
  have hmat : ∀ u v, fget mat u v = f u v := fun u v => by simp [mat, fget, vget]
  { toFun := fget mat
    le_cap := fun u v => hmat u v ▸ f.le_cap u v
    out_le_in := fun v hv => by simpa only [hmat] using f.out_le_in v hv }

theorem tabulateFlow_eq {n : ℕ} {N : Network (Fin n)} (f : N.Preflow) : tabulateFlow f = f := by
  ext u v
  simp [tabulateFlow, fget, vget]

/-- Tabulate a state on `Fin n`: the preflow as a matrix and the heights as a vector. -/
@[expose] def tabulate {n : ℕ} {N : Network (Fin n)} (σ : State N) : State N :=
  let hs : Vector ℕ n := Vector.ofFn σ.height
  ⟨tabulateFlow σ.flow, vget hs⟩

theorem tabulate_eq {n : ℕ} {N : Network (Fin n)} (σ : State N) : tabulate σ = σ := by
  obtain ⟨f, h⟩ := σ
  simp only [tabulate, tabulateFlow_eq, State.mk.injEq, true_and]
  funext v
  simp [vget]

end PushRelabel

end Network

/-! ### The executable algorithm -/

section Executable

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

open Network Network.Preflow Network.PushRelabel

/-- The output of `pushRelabelWith`. -/
structure PushRelabelOutput (N : Network V) where
  /-- The operations performed, in order. -/
  ops : List (Op V)
  /-- The final flow. -/
  flow : N.Flow
  /-- The gap cut of the final labeling. -/
  cut : Finset V

/-- The output read off a final state: its preflow as a flow when every excess off `N.s`, `N.t`
vanishes (the zero flow otherwise), and its gap cut. -/
@[expose] def PushRelabelOutput.ofState (ops : List (Op V)) (σ : State N) :
    PushRelabelOutput N where
  ops := ops
  flow := if hz : ∀ v, v ≠ N.s → v ≠ N.t → σ.flow.excess v = 0 then σ.flow.toFlow hz
    else Flow.zero N
  cut := gapCut σ.height

/-- The generic push–relabel algorithm with the scheduler `State.selectOp vs`, normalizing states
with `norm`, for at most `maxOps N + 1` steps from the initial state. -/
@[expose] def pushRelabelWith (N : Network V) (vs : List V) (norm : State N → State N) :
    PushRelabelOutput N :=
  if N.s = N.t then ⟨[], Flow.zero N, ∅⟩ else
    let r := (PushRelabel.init N).loop vs norm (maxOps N + 1)
    PushRelabelOutput.ofState r.1 r.2

/-- **Correctness of the executable generic algorithm** ([CLRS2009], Theorems 26.18 and 26.24): if
`vs` lists every vertex, `norm` is the identity and `N.s ≠ N.t`, then `pushRelabelWith N vs norm`
performs a run of at most `maxOps N` operations of the generic algorithm from the initial state and
returns a maximum flow and a minimum cut of equal value. -/
theorem pushRelabelWith_correct {vs : List V} (hvs : ∀ v, v ∈ vs) {norm : State N → State N}
    (hnorm : ∀ σ, norm σ = σ) (hst : N.s ≠ N.t) :
    (pushRelabelWith N vs norm).flow.IsMaxFlow ∧ N.IsMinCut (pushRelabelWith N vs norm).cut ∧
      (pushRelabelWith N vs norm).flow.value =
        (N.cutCapacity (pushRelabelWith N vs norm).cut : ℤ) ∧
      (PushRelabel.init N).IsRun (pushRelabelWith N vs norm).ops ∧
      (pushRelabelWith N vs norm).ops.length ≤ maxOps N := by
  obtain ⟨hfin, hrun, hterm⟩ :=
    State.loop_spec hvs hnorm (maxOps N + 1) (PushRelabel.init N) (inv_init hst)
  have hlen := length_le hst hrun
  have hinv := (inv_init hst).run hrun
  rw [← hfin] at hinv
  have hz := excess_eq_zero_of_forall_not_isActive _ (hterm (by omega))
  have hmax := hinv.valid.isMaxFlow_toFlow hz
  obtain ⟨hmin, hval⟩ := hinv.valid.isMinCut_gapCut hz
  unfold pushRelabelWith
  rw [ite_eq_right hst]
  simp only [PushRelabelOutput.ofState]
  rw [dite_eq_left hz]
  exact ⟨hmax, hmin, hval, hrun, hlen⟩

/-- The generic push–relabel algorithm on `Fin n`: scan the vertices in increasing order, tabulating
the state after every operation. -/
@[expose] def pushRelabel {n : ℕ} (N : Network (Fin n)) : PushRelabelOutput N :=
  pushRelabelWith N (List.finRange n) tabulate

/-- **Correctness of `pushRelabel`** ([CLRS2009], Theorems 26.18 and 26.24). -/
theorem pushRelabel_correct {n : ℕ} {N : Network (Fin n)} (hst : N.s ≠ N.t) :
    (pushRelabel N).flow.IsMaxFlow ∧ N.IsMinCut (pushRelabel N).cut ∧
      (pushRelabel N).flow.value = (N.cutCapacity (pushRelabel N).cut : ℤ) ∧
      (PushRelabel.init N).IsRun (pushRelabel N).ops ∧ (pushRelabel N).ops.length ≤ maxOps N :=
  pushRelabelWith_correct List.mem_finRange tabulate_eq hst

end Executable

end Cslib.Algorithms.Lean.MaxFlow
