/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.MaxFlow.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Preflows, Valid Labelings, Push and Relabel

The basic objects of the Goldberg–Tarjan push–relabel method ([GoldbergTarjan1988]; [CLRS2009],
Section 26.4) on the integral networks of `Complexity.Algorithms.Lean.MaxFlow.Basic`.

## Model and source mapping

* **Preflow (`Network.Preflow`):** integral arc flows bounded by the capacities, with inflow at
  least outflow at every vertex other than `N.s` ([CLRS2009], Section 26.4). Unlike [CLRS2009], the
  network may have antiparallel arcs and arcs entering `N.s` or leaving `N.t`; the condition at
  `N.t` is enforced.
* **Excess and residual capacity:** `excess f v` is inflow minus outflow (in `ℤ`); `resCap f u v`
  is `(cap u v - f u v) + f v u`, as for `Network.Flow.resCap`.
* **Valid labeling (`Preflow.IsValidLabeling`):** `h N.s = |V|`, `h N.t = 0` and
  `h u ≤ h v + 1` on every residual arc ([CLRS2009], Section 26.4).
* **Push (`Preflow.push`):** moves `min (excess u, resCap u v)` units from `u` to `v`, first
  cancelling flow on `(v, u)` and then increasing flow on `(u, v)`.
* **Relabel (`Preflow.relabel`):** sets `h u := 1 + min {h v | resCap u v > 0}`. The preconditions
  of push and relabel are `Preflow.CanPush` and `Preflow.CanRelabel`.

## Main definitions

* `Network.Preflow`, `Preflow.excess`, `Preflow.resCap`, `Preflow.IsActive`,
  `Preflow.ResReachable`, `Preflow.toFlow`.
* `Preflow.IsValidLabeling`, `Preflow.push`, `Preflow.relabel`, `Preflow.CanPush`,
  `Preflow.CanRelabel`, `Preflow.initial`, `Preflow.initialHeight`.
* `Preflow.gapLevel`, `Preflow.gapCut`: the least empty level of a labeling and the vertices above
  it.

## Main results

* `Preflow.IsValidLabeling.not_resReachable`: no residual `s`–`t` path ([CLRS2009], Lemma 26.17).
* `Preflow.resReachable_source_of_excess_pos`: positive excess implies a residual path to `N.s`
  ([CLRS2009], Lemma 26.19); `Preflow.IsValidLabeling.le_of_excess_pos`: such vertices have height
  at most `2|V| - 1` ([CLRS2009], Lemma 26.20).
* `Preflow.IsValidLabeling.push`, `Preflow.IsValidLabeling.relabel`: push and relabel preserve valid
  labelings ([CLRS2009], Lemma 26.16); `Preflow.CanRelabel.lt_relabelHeight`: relabel raises the
  height ([CLRS2009], Lemma 26.15); `Preflow.IsValidLabeling.exists_canPush_or_canRelabel`: an
  active vertex admits one of them ([CLRS2009], Lemma 26.14).
* `Preflow.IsValidLabeling.isMaxFlow_toFlow`: a preflow with a valid labeling and no active vertex
  is a maximum flow ([CLRS2009], Theorem 26.18); `Preflow.IsValidLabeling.isMinCut_gapCut`: its gap
  cut is then a minimum cut of the same value.

## References

* [A. V. Goldberg and R. E. Tarjan,
  *A New Approach to the Maximum-Flow Problem*][GoldbergTarjan1988]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

namespace Network

variable {V : Type*} [Fintype V]

variable (N : Network V)

/-- An integral preflow on `N`: arc flows bounded by the capacities, with inflow at least outflow at
every vertex other than `N.s` ([CLRS2009], Section 26.4). -/
@[ext]
structure Preflow where
  /-- Integral flow on each directed arc `(u, v)`. -/
  toFun : V → V → ℕ
  /-- Capacity bound on every directed arc. -/
  le_cap : ∀ u v, toFun u v ≤ N.cap u v
  /-- Outflow is at most inflow at every vertex other than the source. -/
  out_le_in : ∀ v, v ≠ N.s → ∑ w, toFun v w ≤ ∑ u, toFun u v

instance : CoeFun N.Preflow (fun _ => V → V → ℕ) := ⟨Preflow.toFun⟩

namespace Preflow

variable {N}

/-- The excess `e(v)` of `v`: inflow minus outflow. -/
@[expose] def excess (f : N.Preflow) (v : V) : ℤ :=
  (∑ u, (f u v : ℤ)) - ∑ w, (f v w : ℤ)

theorem excess_nonneg (f : N.Preflow) {v : V} (hv : v ≠ N.s) : 0 ≤ f.excess v := by
  have h := f.out_le_in v hv
  unfold excess
  have h' : ((∑ w, f v w : ℕ) : ℤ) ≤ ((∑ u, f u v : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at h'
  omega

/-- Residual capacity `c_f(u, v)`: unused capacity on `(u, v)` plus cancellable flow on `(v, u)`. -/
@[expose] def resCap (f : N.Preflow) (u v : V) : ℕ :=
  (N.cap u v - f u v) + f v u

theorem resCap_coe (f : N.Preflow) (u v : V) :
    (f.resCap u v : ℤ) = (N.cap u v : ℤ) - ((f u v : ℤ) - (f v u : ℤ)) := by
  unfold resCap
  have h := f.le_cap u v
  omega

theorem resCap_le_cap_add_cap (f : N.Preflow) (u v : V) :
    f.resCap u v ≤ N.cap u v + N.cap v u := by
  unfold resCap
  have h := f.le_cap v u
  omega

/-- A vertex other than `N.s` and `N.t` is active when it has positive excess. -/
@[expose] def IsActive (f : N.Preflow) (v : V) : Prop :=
  v ≠ N.s ∧ v ≠ N.t ∧ 0 < f.excess v

instance [DecidableEq V] (f : N.Preflow) (v : V) : Decidable (f.IsActive v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Residual reachability: `v` is reachable from `u` along arcs of positive residual capacity. -/
@[expose] def ResReachable (f : N.Preflow) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => 0 < f.resCap x y) u v

/-- A preflow with zero excess at every vertex other than `N.s` and `N.t` is a flow. -/
@[expose] def toFlow (f : N.Preflow) (h : ∀ v, v ≠ N.s → v ≠ N.t → f.excess v = 0) : N.Flow where
  toFun := f.toFun
  le_cap := f.le_cap
  conserve v hs ht := by
    have h0 := h v hs ht
    unfold excess at h0
    have h' : ((∑ u, f u v : ℕ) : ℤ) = ((∑ w, f v w : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast h'

@[simp]
theorem toFlow_apply (f : N.Preflow) (h : ∀ v, v ≠ N.s → v ≠ N.t → f.excess v = 0) (u v : V) :
    f.toFlow h u v = f u v := rfl

theorem resCap_toFlow (f : N.Preflow) (h : ∀ v, v ≠ N.s → v ≠ N.t → f.excess v = 0) (u v : V) :
    (f.toFlow h).resCap u v = f.resCap u v := rfl

theorem resReachable_toFlow (f : N.Preflow) (h : ∀ v, v ≠ N.s → v ≠ N.t → f.excess v = 0)
    (u v : V) : (f.toFlow h).ResReachable u v ↔ f.ResReachable u v := Iff.rfl

/-! ### Valid labelings -/

/-- A valid labeling (height function) for `f` ([CLRS2009], Section 26.4). -/
structure IsValidLabeling (f : N.Preflow) (h : V → ℕ) : Prop where
  /-- The source has height `|V|`. -/
  source : h N.s = Fintype.card V
  /-- The sink has height `0`. -/
  sink : h N.t = 0
  /-- Residual arcs descend by at most one level. -/
  le_add_one : ∀ u v, 0 < f.resCap u v → h u ≤ h v + 1

theorem isValidLabeling_iff {f : N.Preflow} {h : V → ℕ} :
    f.IsValidLabeling h ↔
      h N.s = Fintype.card V ∧ h N.t = 0 ∧ ∀ u v, 0 < f.resCap u v → h u ≤ h v + 1 :=
  ⟨fun hh => ⟨hh.source, hh.sink, hh.le_add_one⟩, fun hh => ⟨hh.1, hh.2.1, hh.2.2⟩⟩

instance (f : N.Preflow) (h : V → ℕ) : Decidable (f.IsValidLabeling h) :=
  decidable_of_iff _ isValidLabeling_iff.symm

/-- Along a walk whose steps lower `h` by at most one, every height between the endpoints is taken
by some vertex, so the walk descends by fewer than `|V|` levels. -/
private theorem le_add_card_of_reflTransGen {r : V → V → Prop} {h : V → ℕ}
    (hr : ∀ u v, r u v → h u ≤ h v + 1) {u w : V} (huw : Relation.ReflTransGen r u w) :
    h u + 1 ≤ h w + Fintype.card V := by
  classical
  have key : ∀ x, Relation.ReflTransGen r x w → Finset.Icc (h w) (h x) ⊆ Finset.univ.image h := by
    intro x hx
    induction hx using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro k hk
      rw [Finset.mem_Icc] at hk
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, by omega⟩
    | @head x y hxy _ ih =>
      intro k hk
      rw [Finset.mem_Icc] at hk
      by_cases hky : k ≤ h y
      · exact ih (Finset.mem_Icc.mpr ⟨hk.1, hky⟩)
      · have := hr x y hxy
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by omega⟩
  have hcard := Finset.card_le_card (key u huw)
  rw [Nat.card_Icc] at hcard
  have := (Finset.card_image_le (s := Finset.univ) (f := h))
  rw [Finset.card_univ] at this
  omega

theorem IsValidLabeling.le_add_card {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h)
    {u w : V} (huw : f.ResReachable u w) : h u + 1 ≤ h w + Fintype.card V :=
  le_add_card_of_reflTransGen hh.le_add_one huw

/-- **No residual `s`–`t` path** ([CLRS2009], Lemma 26.17). -/
theorem IsValidLabeling.not_resReachable {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h) :
    ¬ f.ResReachable N.s N.t := by
  intro hst
  have := hh.le_add_card hst
  rw [hh.source, hh.sink] at this
  omega

theorem IsValidLabeling.source_ne_sink {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h) :
    N.s ≠ N.t := by
  intro hst
  exact hh.not_resReachable (hst ▸ .refl)

/-! ### Excess and residual reachability -/

private theorem sum_netIn_eq [DecidableEq V] (g : V → V → ℕ) (U : Finset V) :
    (∑ v ∈ U, ((∑ u, (g u v : ℤ)) - ∑ w, (g v w : ℤ))) =
      (∑ v ∈ U, ∑ u ∈ Finset.univ \ U, (g u v : ℤ)) -
        ∑ v ∈ U, ∑ w ∈ Finset.univ \ U, (g v w : ℤ) := by
  have hsplit : ∀ k : V → ℤ, ∑ x, k x = (∑ x ∈ U, k x) + ∑ x ∈ Finset.univ \ U, k x := by
    intro k
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ U)]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ v ∈ U, ∑ u, (g u v : ℤ) =
      (∑ v ∈ U, ∑ u ∈ U, (g u v : ℤ)) + ∑ v ∈ U, ∑ u ∈ Finset.univ \ U, (g u v : ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hsplit _
  have h2 : ∑ v ∈ U, ∑ w, (g v w : ℤ) =
      (∑ v ∈ U, ∑ w ∈ U, (g v w : ℤ)) + ∑ v ∈ U, ∑ w ∈ Finset.univ \ U, (g v w : ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hsplit _
  have h3 : (∑ v ∈ U, ∑ u ∈ U, (g u v : ℤ)) = ∑ v ∈ U, ∑ w ∈ U, (g v w : ℤ) := Finset.sum_comm
  omega

/-- **Overflowing vertices reach the source** ([CLRS2009], Lemma 26.19): in a preflow, every vertex
with positive excess has a residual path to `N.s`. -/
theorem resReachable_source_of_excess_pos (f : N.Preflow) {x : V} (hx : 0 < f.excess x) :
    f.ResReachable x N.s := by
  classical
  by_contra hns
  set U := Finset.univ.filter fun v => f.ResReachable x v with hU
  have hxU : x ∈ U := by
    rw [hU, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, .refl⟩
  have hsU : N.s ∉ U := by simpa [hU] using hns
  have hzero : ∀ v ∈ U, ∀ w ∈ Finset.univ \ U, f.resCap v w = 0 := by
    intro v hv w hw
    by_contra hpos
    have hv' : f.ResReachable x v := by simpa [hU] using hv
    have hw' : ¬ f.ResReachable x w := by simpa [hU] using hw
    exact hw' (hv'.tail (Nat.pos_of_ne_zero hpos))
  have hsum : (∑ v ∈ U, f.excess v) ≤ 0 := by
    unfold excess
    rw [sum_netIn_eq f.toFun U]
    have hin : (∑ v ∈ U, ∑ u ∈ Finset.univ \ U, (f u v : ℤ)) = 0 := by
      refine Finset.sum_eq_zero fun v hv => Finset.sum_eq_zero fun u hu => ?_
      have := hzero v hv u hu
      unfold resCap at this
      have : f u v = 0 := by omega
      rw [this, Nat.cast_zero]
    have hout : 0 ≤ ∑ v ∈ U, ∑ w ∈ Finset.univ \ U, (f v w : ℤ) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
    change (∑ v ∈ U, ∑ u ∈ Finset.univ \ U, (f u v : ℤ)) -
        ∑ v ∈ U, ∑ w ∈ Finset.univ \ U, (f v w : ℤ) ≤ 0
    omega
  have hnonneg : ∀ v ∈ U, 0 ≤ f.excess v := fun v hv =>
    f.excess_nonneg fun h => hsU (h ▸ hv)
  have hle := Finset.single_le_sum hnonneg hxU
  omega

/-- **Height bound** ([CLRS2009], Lemma 26.20): under a valid labeling, a vertex with positive
excess has height at most `2|V| - 1`. -/
theorem IsValidLabeling.le_of_excess_pos {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h)
    {x : V} (hx : 0 < f.excess x) : h x ≤ 2 * Fintype.card V - 1 := by
  have := hh.le_add_card (f.resReachable_source_of_excess_pos hx)
  rw [hh.source] at this
  omega

/-! ### Push and relabel -/

/-- The amount `min (e(u), c_f(u, v))` moved by a push from `u` to `v` ([CLRS2009], Section 26.4,
procedure `PUSH`). -/
@[expose] def pushAmount (f : N.Preflow) (u v : V) : ℕ :=
  min (f.excess u).toNat (f.resCap u v)

theorem pushAmount_le_resCap (f : N.Preflow) (u v : V) : f.pushAmount u v ≤ f.resCap u v :=
  min_le_right _ _

/-- Residual out-neighbours of `u`. -/
@[expose] def resNbrs (f : N.Preflow) (u : V) : Finset V :=
  Finset.univ.filter fun v => 0 < f.resCap u v

theorem mem_resNbrs (f : N.Preflow) (u v : V) :
    v ∈ f.resNbrs u ↔ 0 < f.resCap u v := by
  simp [resNbrs]

/-- The height `1 + min {h v | c_f(u, v) > 0}` assigned by a relabel of `u` ([CLRS2009], Section
26.4, procedure `RELABEL`); `h u` when `u` has no residual out-arc. -/
@[expose] def relabelHeight (f : N.Preflow) (h : V → ℕ) (u : V) : ℕ :=
  if hne : (f.resNbrs u).Nonempty then (f.resNbrs u).inf' hne h + 1 else h u

/-- Precondition of a push from `u` to `v` ([CLRS2009], Section 26.4): `u` is active and `(u, v)` is
a residual arc going down one level. -/
structure CanPush (f : N.Preflow) (h : V → ℕ) (u v : V) : Prop where
  /-- `u` is active. -/
  active : f.IsActive u
  /-- `(u, v)` is a residual arc. -/
  resCap_pos : 0 < f.resCap u v
  /-- `(u, v)` goes down one level. -/
  height_eq : h u = h v + 1

/-- Precondition of a relabel of `u` ([CLRS2009], Section 26.4): `u` is active and no residual arc
leaving `u` goes downhill. -/
structure CanRelabel (f : N.Preflow) (h : V → ℕ) (u : V) : Prop where
  /-- `u` is active. -/
  active : f.IsActive u
  /-- No residual arc leaving `u` goes downhill. -/
  le_height : ∀ v, 0 < f.resCap u v → h u ≤ h v

theorem canPush_iff {f : N.Preflow} {h : V → ℕ} {u v : V} :
    f.CanPush h u v ↔ f.IsActive u ∧ 0 < f.resCap u v ∧ h u = h v + 1 :=
  ⟨fun hp => ⟨hp.active, hp.resCap_pos, hp.height_eq⟩, fun hp => ⟨hp.1, hp.2.1, hp.2.2⟩⟩

theorem canRelabel_iff {f : N.Preflow} {h : V → ℕ} {u : V} :
    f.CanRelabel h u ↔ f.IsActive u ∧ ∀ v, 0 < f.resCap u v → h u ≤ h v :=
  ⟨fun hr => ⟨hr.active, hr.le_height⟩, fun hr => ⟨hr.1, hr.2⟩⟩

instance [DecidableEq V] (f : N.Preflow) (h : V → ℕ) (u v : V) : Decidable (f.CanPush h u v) :=
  decidable_of_iff _ canPush_iff.symm

instance [DecidableEq V] (f : N.Preflow) (h : V → ℕ) (u : V) : Decidable (f.CanRelabel h u) :=
  decidable_of_iff _ canRelabel_iff.symm

theorem CanPush.ne {f : N.Preflow} {h : V → ℕ} {u v : V} (hp : f.CanPush h u v) : u ≠ v := by
  rintro rfl
  have := hp.height_eq
  omega

theorem CanPush.pushAmount_pos {f : N.Preflow} {h : V → ℕ} {u v : V} (hp : f.CanPush h u v) :
    0 < f.pushAmount u v := by
  have h1 := hp.active.2.2
  have h2 := hp.resCap_pos
  unfold pushAmount
  omega

/-- Every active vertex admits a push or a relabel ([CLRS2009], Lemma 26.14). -/
theorem IsValidLabeling.exists_canPush_or_canRelabel {f : N.Preflow} {h : V → ℕ} {u : V}
    (hh : f.IsValidLabeling h) (hu : f.IsActive u) : (∃ v, f.CanPush h u v) ∨ f.CanRelabel h u := by
  by_cases hex : ∃ v, 0 < f.resCap u v ∧ h u = h v + 1
  · obtain ⟨v, hpos, heq⟩ := hex
    exact .inl ⟨v, hu, hpos, heq⟩
  · refine .inr ⟨hu, fun v hpos => ?_⟩
    have h1 := hh.le_add_one u v hpos
    have h2 : ¬ (0 < f.resCap u v ∧ h u = h v + 1) := fun h' => hex ⟨v, h'⟩
    omega

/-! ### Termination and the gap cut -/

/-- With no active vertex, every vertex other than `N.s` and `N.t` has zero excess. -/
theorem excess_eq_zero_of_forall_not_isActive (f : N.Preflow) (hno : ∀ v, ¬ f.IsActive v) :
    ∀ v, v ≠ N.s → v ≠ N.t → f.excess v = 0 := by
  intro v hs ht
  have h1 := f.excess_nonneg hs
  by_contra h
  exact hno v ⟨hs, ht, by omega⟩

/-- **Optimality at termination** ([CLRS2009], Theorem 26.18): a preflow with a valid labeling and
no active vertex is a maximum flow. -/
theorem IsValidLabeling.isMaxFlow_toFlow {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h)
    (hz : ∀ v, v ≠ N.s → v ≠ N.t → f.excess v = 0) : (f.toFlow hz).IsMaxFlow := by
  rw [Flow.isMaxFlow_iff_not_exists_augmentingPath _ hh.source_ne_sink,
    Flow.exists_augmentingPath_iff_resReachable]
  exact hh.not_resReachable

/-- The least level `0 < k < |V|` occupied by no vertex (`0` if there is none). -/
@[expose] def gapLevel (h : V → ℕ) : ℕ :=
  ((List.range (Fintype.card V)).find? fun k => decide (0 < k ∧ ∀ v, h v ≠ k)).getD 0

/-- By pigeonhole, a valid labeling leaves some level strictly between `0` and `|V|` empty. -/
theorem IsValidLabeling.exists_gap {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h) :
    ∃ k, 0 < k ∧ k < Fintype.card V ∧ ∀ v, h v ≠ k := by
  classical
  by_contra hcon
  have hocc : ∀ k, 0 < k → k < Fintype.card V → ∃ v, h v = k := fun k h0 h1 => by
    by_contra hne
    exact hcon ⟨k, h0, h1, fun v hv => hne ⟨v, hv⟩⟩
  have hsub : Finset.range (Fintype.card V + 1) ⊆ Finset.univ.image h := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_image]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨N.t, Finset.mem_univ _, hh.sink⟩
    · by_cases hkn : k = Fintype.card V
      · exact ⟨N.s, Finset.mem_univ _, hkn ▸ hh.source⟩
      · obtain ⟨v, hv⟩ := hocc k hk0 (by omega)
        exact ⟨v, Finset.mem_univ _, hv⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_range] at h1
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset V)) (f := h)
  rw [Finset.card_univ] at h2
  omega

theorem IsValidLabeling.gapLevel_spec {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h) :
    0 < gapLevel h ∧ gapLevel h < Fintype.card V ∧ ∀ v, h v ≠ gapLevel h := by
  obtain ⟨k, hk0, hkn, hk⟩ := hh.exists_gap
  unfold gapLevel
  cases hfind : (List.range (Fintype.card V)).find? (fun k => decide (0 < k ∧ ∀ v, h v ≠ k)) with
  | none =>
    rw [List.find?_eq_none] at hfind
    exact absurd (decide_eq_true ⟨hk0, hk⟩) (hfind k (List.mem_range.mpr hkn))
  | some j =>
    have hp' : decide (0 < j ∧ ∀ v, h v ≠ j) = true :=
      List.find?_some (p := fun k => decide (0 < k ∧ ∀ v, h v ≠ k)) hfind
    have hp := of_decide_eq_true hp'
    have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
    exact ⟨hp.1, hmem, hp.2⟩

/-- The gap cut of a labeling: the vertices strictly above `gapLevel h`. -/
@[expose] def gapCut (h : V → ℕ) : Finset V :=
  Finset.univ.filter fun v => gapLevel h < h v

theorem mem_gapCut {h : V → ℕ} {v : V} : v ∈ gapCut h ↔ gapLevel h < h v := by
  simp [gapCut]

theorem IsValidLabeling.isCut_gapCut {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h) :
    N.IsCut (gapCut h) := by
  obtain ⟨_, hlt, _⟩ := hh.gapLevel_spec
  refine ⟨mem_gapCut.mpr (by rw [hh.source]; exact hlt), fun ht => ?_⟩
  have := mem_gapCut.mp ht
  rw [hh.sink] at this
  omega

theorem IsValidLabeling.resCap_eq_zero_of_mem_gapCut {f : N.Preflow} {h : V → ℕ}
    (hh : f.IsValidLabeling h) {u w : V} (hu : u ∈ gapCut h) (hw : w ∉ gapCut h) :
    f.resCap u w = 0 := by
  obtain ⟨_, _, hg⟩ := hh.gapLevel_spec
  have hu' := mem_gapCut.mp hu
  have hw' : ¬ gapLevel h < h w := fun h' => hw (mem_gapCut.mpr h')
  have := hg w
  by_contra hpos
  have := hh.le_add_one u w (Nat.pos_of_ne_zero hpos)
  omega

section DecidableEq

variable [DecidableEq V]

/-- **Gap cut at termination**: for a preflow with a valid labeling and no active vertex, the
vertices above the least empty level form a minimum cut whose capacity is the flow value. -/
theorem IsValidLabeling.isMinCut_gapCut {f : N.Preflow} {h : V → ℕ} (hh : f.IsValidLabeling h)
    (hz : ∀ v, v ≠ N.s → v ≠ N.t → f.excess v = 0) :
    N.IsMinCut (gapCut h) ∧ (f.toFlow hz).value = (N.cutCapacity (gapCut h) : ℤ) := by
  have hcut := hh.isCut_gapCut
  have hval := (f.toFlow hz).value_eq_cutCapacity_of_resCap_eq_zero hcut fun u hu w hw =>
    hh.resCap_eq_zero_of_mem_gapCut hu (Finset.mem_sdiff.mp hw).2
  exact ⟨(f.toFlow hz).isMinCut_of_value_eq_cutCapacity hcut hval, hval⟩

/-! ### The push operation -/

/-- Arc flows after pushing `δ` units from `u` to `v`: first cancel up to `δ` units of the reverse
flow `f v u`, then add the remainder to `f u v`. -/
@[expose] def pushFun (f : V → V → ℕ) (u v : V) (δ : ℕ) (x y : V) : ℕ :=
  if x = u ∧ y = v then f x y + (δ - min δ (f y x))
  else if x = v ∧ y = u then f x y - min δ (f x y)
  else f x y

omit [Fintype V] in
theorem pushFun_sub_pushFun (f : V → V → ℕ) (u v : V) (δ : ℕ) (x y : V) :
    (pushFun f u v δ x y : ℤ) - (pushFun f u v δ y x : ℤ) =
      (f x y : ℤ) - (f y x : ℤ) + (if x = u ∧ y = v then (δ : ℤ) else 0) -
        (if x = v ∧ y = u then (δ : ℤ) else 0) := by
  have hA' : (y = v ∧ x = u) ↔ (x = u ∧ y = v) := and_comm
  have hB' : (y = u ∧ x = v) ↔ (x = v ∧ y = u) := and_comm
  unfold pushFun
  simp only [hA', hB']
  by_cases hA : x = u ∧ y = v
  · by_cases hB : x = v ∧ y = u
    · have hxy : x = y := hA.1.trans hB.2.symm
      subst hxy
      simp only [ite_eq_left hA, ite_eq_left hB]
      omega
    · simp only [ite_eq_left hA, ite_eq_right hB]
      omega
  · by_cases hB : x = v ∧ y = u
    · simp only [ite_eq_right hA, ite_eq_left hB]
      omega
    · simp only [ite_eq_right hA, ite_eq_right hB]
      omega

theorem sum_pushFun_sub (f : V → V → ℕ) (u v : V) (δ : ℕ) (x : V) :
    (∑ y, (pushFun f u v δ y x : ℤ)) - ∑ y, (pushFun f u v δ x y : ℤ) =
      (∑ y, (f y x : ℤ)) - (∑ y, (f x y : ℤ)) - (if x = u then (δ : ℤ) else 0) +
        (if x = v then (δ : ℤ) else 0) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hpt : ∀ y, (pushFun f u v δ y x : ℤ) - (pushFun f u v δ x y : ℤ) =
      ((f y x : ℤ) - (f x y : ℤ)) + ((if y = u ∧ x = v then (δ : ℤ) else 0) -
        (if y = v ∧ x = u then (δ : ℤ) else 0)) := by
    intro y
    rw [pushFun_sub_pushFun f u v δ y x]
    omega
  simp only [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ y, (if y = u ∧ x = v then (δ : ℤ) else 0) = if x = v then (δ : ℤ) else 0 := by
    by_cases hx : x = v <;> simp [hx]
  have h2 : ∑ y, (if y = v ∧ x = u then (δ : ℤ) else 0) = if x = u then (δ : ℤ) else 0 := by
    by_cases hx : x = u <;> simp [hx]
  rw [Finset.sum_sub_distrib, h1, h2]
  omega

/-- Push `f.pushAmount u v` units from `u` to `v`, cancelling reverse flow first ([CLRS2009],
Section 26.4, procedure `PUSH`). -/
@[expose] def push (f : N.Preflow) (u v : V) : N.Preflow where
  toFun := pushFun f u v (f.pushAmount u v)
  le_cap x y := by
    have hδ := f.pushAmount_le_resCap u v
    unfold pushFun
    split_ifs with h1 h2
    · obtain ⟨rfl, rfl⟩ := h1
      unfold resCap at hδ
      have := f.le_cap x y
      omega
    · exact (Nat.sub_le _ _).trans (f.le_cap x y)
    · exact f.le_cap x y
  out_le_in x hx := by
    have key := sum_pushFun_sub f.toFun u v (f.pushAmount u v) x
    have hex := f.excess_nonneg hx
    have hδ : x = u → (f.pushAmount u v : ℤ) ≤ f.excess x := by grind [pushAmount]
    unfold excess at hex hδ
    have h0 : (0 : ℤ) ≤ (∑ y, (pushFun f u v (f.pushAmount u v) y x : ℤ)) -
        ∑ y, (pushFun f u v (f.pushAmount u v) x y : ℤ) := by
      rw [key]
      by_cases hxu : x = u
      · have := hδ hxu
        split_ifs <;> omega
      · split_ifs <;> omega
    have : ((∑ y, pushFun f u v (f.pushAmount u v) x y : ℕ) : ℤ) ≤
        ((∑ y, pushFun f u v (f.pushAmount u v) y x : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast this

theorem push_apply (f : N.Preflow) (u v x y : V) :
    f.push u v x y = pushFun f u v (f.pushAmount u v) x y := rfl

theorem excess_push (f : N.Preflow) (u v x : V) :
    (f.push u v).excess x = f.excess x - (if x = u then (f.pushAmount u v : ℤ) else 0) +
      (if x = v then (f.pushAmount u v : ℤ) else 0) :=
  sum_pushFun_sub f.toFun u v (f.pushAmount u v) x

theorem resCap_push_coe (f : N.Preflow) (u v x y : V) :
    ((f.push u v).resCap x y : ℤ) =
      f.resCap x y - (if x = u ∧ y = v then (f.pushAmount u v : ℤ) else 0) +
        (if x = v ∧ y = u then (f.pushAmount u v : ℤ) else 0) := by
  rw [resCap_coe, resCap_coe]
  have := pushFun_sub_pushFun f.toFun u v (f.pushAmount u v) x y
  change (N.cap x y : ℤ) - ((pushFun f u v (f.pushAmount u v) x y : ℤ) -
    (pushFun f u v (f.pushAmount u v) y x : ℤ)) = _
  rw [this]
  omega

theorem resCap_push_self (f : N.Preflow) {u v : V} (huv : u ≠ v) :
    (f.push u v).resCap u v = f.resCap u v - f.pushAmount u v := by
  have h := f.resCap_push_coe u v u v
  have hA : u = u ∧ v = v := ⟨rfl, rfl⟩
  have hB : ¬ (u = v ∧ v = u) := fun h => huv h.1
  rw [ite_eq_left hA, ite_eq_right hB] at h
  have := f.pushAmount_le_resCap u v
  omega

theorem resCap_push_swap (f : N.Preflow) {u v : V} (huv : u ≠ v) :
    (f.push u v).resCap v u = f.resCap v u + f.pushAmount u v := by
  have h := f.resCap_push_coe u v v u
  have hA : ¬ (v = u ∧ u = v) := fun h => huv h.2
  have hB : v = v ∧ u = u := ⟨rfl, rfl⟩
  rw [ite_eq_right hA, ite_eq_left hB] at h
  omega

theorem resCap_push_of_ne (f : N.Preflow) {u v x y : V} (h1 : ¬ (x = u ∧ y = v))
    (h2 : ¬ (x = v ∧ y = u)) : (f.push u v).resCap x y = f.resCap x y := by
  have h := f.resCap_push_coe u v x y
  rw [ite_eq_right h1, ite_eq_right h2] at h
  omega

theorem excess_push_self (f : N.Preflow) {u v : V} (huv : u ≠ v) :
    (f.push u v).excess u = f.excess u - f.pushAmount u v := by
  rw [excess_push, ite_eq_left rfl, ite_eq_right huv]
  omega

theorem excess_push_target (f : N.Preflow) {u v : V} (huv : u ≠ v) :
    (f.push u v).excess v = f.excess v + f.pushAmount u v := by
  rw [excess_push, ite_eq_right (Ne.symm huv), ite_eq_left rfl]
  omega

theorem excess_push_of_ne (f : N.Preflow) {u v x : V} (hu : x ≠ u) (hv : x ≠ v) :
    (f.push u v).excess x = f.excess x := by
  rw [excess_push, ite_eq_right hu, ite_eq_right hv]
  omega

theorem isActive_push_of_ne (f : N.Preflow) {u v x : V} (hu : x ≠ u) (hv : x ≠ v) :
    (f.push u v).IsActive x ↔ f.IsActive x := by
  unfold IsActive
  rw [excess_push_of_ne f hu hv]

/-- Pushes preserve valid labelings ([CLRS2009], Lemma 26.16). -/
theorem IsValidLabeling.push {f : N.Preflow} {h : V → ℕ} {u v : V} (hh : f.IsValidLabeling h)
    (hp : f.CanPush h u v) : (f.push u v).IsValidLabeling h where
  source := hh.source
  sink := hh.sink
  le_add_one x y hxy := by
    by_cases hb : x = v ∧ y = u
    · obtain ⟨rfl, rfl⟩ := hb
      have := hp.height_eq
      omega
    · by_cases ha : x = u ∧ y = v
      · obtain ⟨rfl, rfl⟩ := ha
        have := hp.height_eq
        omega
      · rw [f.resCap_push_of_ne ha hb] at hxy
        exact hh.le_add_one x y hxy

/-! ### The relabel operation -/

/-- Relabel `u`: replace its height by `f.relabelHeight h u` ([CLRS2009], Section 26.4, procedure
`RELABEL`). -/
@[expose] def relabel (f : N.Preflow) (h : V → ℕ) (u : V) : V → ℕ :=
  Function.update h u (f.relabelHeight h u)

omit [DecidableEq V] in
theorem resNbrs_nonempty (f : N.Preflow) {u : V} (hu : 0 < f.excess u) :
    (f.resNbrs u).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hz : ∀ w, f w u = 0 := by
    intro w
    have hw : w ∉ f.resNbrs u := by grind
    rw [mem_resNbrs, not_lt] at hw
    unfold resCap at hw
    omega
  unfold excess at hu
  have h0 : ∑ w, (f w u : ℤ) = 0 := Finset.sum_eq_zero fun w _ => by simp [hz w]
  have : 0 ≤ ∑ w, (f u w : ℤ) := Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  omega

theorem relabel_self (f : N.Preflow) (h : V → ℕ) (u : V) :
    f.relabel h u u = f.relabelHeight h u :=
  Function.update_self _ _ _

theorem relabel_of_ne (f : N.Preflow) (h : V → ℕ) {u x : V} (hx : x ≠ u) :
    f.relabel h u x = h x :=
  Function.update_of_ne hx _ _

omit [DecidableEq V] in
theorem relabelHeight_le {f : N.Preflow} {h : V → ℕ} {u v : V} (hpos : 0 < f.resCap u v) :
    f.relabelHeight h u ≤ h v + 1 := by
  have hv : v ∈ f.resNbrs u := (mem_resNbrs f u v).mpr hpos
  have hne : (f.resNbrs u).Nonempty := ⟨v, hv⟩
  unfold relabelHeight
  simp only [hne, ↓reduceDIte]
  have := Finset.inf'_le h hv
  omega

omit [DecidableEq V] in
/-- A relabel strictly raises the height of the relabelled vertex ([CLRS2009], Lemma 26.15). -/
theorem CanRelabel.lt_relabelHeight {f : N.Preflow} {h : V → ℕ} {u : V} (hr : f.CanRelabel h u) :
    h u < f.relabelHeight h u := by
  have hne := f.resNbrs_nonempty hr.active.2.2
  unfold relabelHeight
  simp only [hne, ↓reduceDIte]
  obtain ⟨w, hw, heq⟩ := Finset.exists_mem_eq_inf' hne h
  rw [heq]
  have := hr.le_height w ((mem_resNbrs f u w).mp hw)
  omega

theorem CanRelabel.le_relabel {f : N.Preflow} {h : V → ℕ} {u : V} (hr : f.CanRelabel h u) (x : V) :
    h x ≤ f.relabel h u x := by
  by_cases hx : x = u
  · subst hx
    rw [relabel_self]
    exact hr.lt_relabelHeight.le
  · rw [relabel_of_ne f h hx]

/-- Relabels preserve valid labelings ([CLRS2009], Lemma 26.16). -/
theorem IsValidLabeling.relabel {f : N.Preflow} {h : V → ℕ} {u : V} (hh : f.IsValidLabeling h)
    (hr : f.CanRelabel h u) : f.IsValidLabeling (f.relabel h u) where
  source := by rw [relabel_of_ne f h (Ne.symm hr.active.1)]; exact hh.source
  sink := by rw [relabel_of_ne f h (Ne.symm hr.active.2.1)]; exact hh.sink
  le_add_one x y hxy := by
    by_cases hx : x = u
    · subst hx
      by_cases hy : y = x
      · subst hy
        omega
      · rw [relabel_self, relabel_of_ne f h hy]
        exact relabelHeight_le hxy
    · rw [relabel_of_ne f h hx]
      have h1 := hh.le_add_one x y hxy
      have h2 := hr.le_relabel y
      omega

/-! ### Initialization -/

variable (N) in
/-- The initial preflow: saturate every arc leaving the source ([CLRS2009], Section 26.4, procedure
`INITIALIZE-PREFLOW`). -/
@[expose] def initial : N.Preflow where
  toFun u v := if u = N.s then N.cap u v else 0
  le_cap u v := by
    split_ifs
    exacts [le_rfl, Nat.zero_le _]
  out_le_in v hv := by simp [hv]

variable (N) in
/-- The initial heights: `|V|` at the source and `0` elsewhere ([CLRS2009], Section 26.4). -/
@[expose] def initialHeight : V → ℕ :=
  fun v => if v = N.s then Fintype.card V else 0

theorem isValidLabeling_initial (hst : N.s ≠ N.t) :
    (initial N).IsValidLabeling (initialHeight N) where
  source := by simp [initialHeight]
  sink := by simp [initialHeight, hst.symm]
  le_add_one u v huv := by
    unfold initialHeight
    by_cases hu : u = N.s
    · subst hu
      by_cases hv : v = N.s
      · subst hv
        omega
      · exfalso
        simp [resCap, initial, hv] at huv
    · simp [hu]

end DecidableEq

end Preflow

end Network

end Cslib.Algorithms.Lean.MaxFlow
