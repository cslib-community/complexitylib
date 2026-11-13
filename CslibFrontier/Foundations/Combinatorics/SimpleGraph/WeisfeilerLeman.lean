/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/WeisfeilerLeman.lean`, after
-- counting classes by `Nat.card (Set.range _)` instead of `Cslib.SetPartition.blocks`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.ColorRefinement
public import Mathlib.Data.Fin.Tuple.Basic
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

/-!
# The `k`-dimensional Weisfeiler–Leman algorithm

The (folklore) *`k`-dimensional Weisfeiler–Leman algorithm* (`k`-WL) colors `k`-tuples
`u : Fin k → V` of a finite simple graph `G` round by round ([CaiFurerImmerman1992], Section 5):

* In **round `0`**, `u` receives its ordered atomic isomorphism type (`SimpleGraph.tupleAtom`): the
  equality relation `u i = u j` and the adjacency relation `G.Adj (u i) (u j)` on `Fin k`.
* In **round `n + 1`**, `u` is recolored (`SimpleGraph.wlRefine`) by its round-`n` color together
  with the multiset over all `v : V` of the step profile (`SimpleGraph.wlStepProfile`): the atomic
  isomorphism type of the `(k + 1)`-tuple `Fin.snoc u v` paired with the `k`-tuple of round-`n`
  colors `fun i => χ (Function.update u i v)` obtained by substituting `v` at each coordinate.

Recording the atomic isomorphism type of `Fin.snoc u v` in the step profile matches `W^r` in
[CaiFurerImmerman1992], Section 5. For `k ≥ 2`, every coordinate of `u` already survives in some
`Function.update u i v`, whereas for `k = 1`, `Function.update u 0 v` overwrites the sole coordinate
`u 0`; including `G.tupleAtom (Fin.snoc u v)` keeps `v = u 0` and `G.Adj (u 0) v` so that `k = 1`
agrees with vertex color refinement (`SimpleGraph.refinementColoring`) and the correspondence with
the `(k + 1)`-pebble bijective game holds uniformly for every `k : ℕ`.

The colors of round `n` live in `SimpleGraph.WLColor k n : Type`, independent of the vertex type and
its universe, so tuple colors and histograms (`SimpleGraph.wlHistogram`) of different graphs are
directly comparable without decidable-equality or decidable-adjacency hypotheses.

Partitioning `Fin k → V` by `Setoid.ker (G.wlColoring n)` refines the partition each round until it
stabilizes within `|V| ^ k - k₀` rounds (`SimpleGraph.ker_wlColoring_eq`), where `k₀` is the number
of atomic `k`-tuple classes. Applying the same counting argument to the combined coloring
`Sum.elim (G.wlColoring n) (H.wlColoring n)` on `(Fin k → V) ⊕ (Fin k → W)` shows that `k`-WL
distinguishes two tuples or two graphs in some round if and only if it distinguishes them in round
`|V| ^ k + |W| ^ k` (`SimpleGraph.forall_wlColoring_eq_iff`,
`SimpleGraph.forall_wlHistogram_eq_iff`).

## Main definitions

* `SimpleGraph.TupleAtom`, `SimpleGraph.tupleAtom`: the ordered atomic isomorphism type of a tuple.
* `SimpleGraph.WLColor`: the type of `k`-WL colors of round `n`.
* `SimpleGraph.wlStepProfile`: the step profile of `(u, v)` under a `k`-tuple coloring.
* `SimpleGraph.wlRefine`: one round of `k`-WL refinement.
* `SimpleGraph.wlColoring`: the `k`-WL coloring after `n` rounds.
* `SimpleGraph.stableWLColoring`: the `k`-WL coloring after `|V| ^ k` rounds.
* `SimpleGraph.wlHistogram`: the multiset of `k`-WL tuple colors of round `n`.

## Main results

* `SimpleGraph.tupleAtom_eq_iff`: equal atomic types mean preservation of equality and adjacency.
* `SimpleGraph.wlRefine_eq_of_imp`, `SimpleGraph.ker_wlRefine_mono`: monotonicity of a `k`-WL step.
* `SimpleGraph.blocks_ker_wlColoring_lt_succ`: the number of `k`-tuple color classes increases
  strictly until stabilization.
* `SimpleGraph.ker_wlColoring_eq`, `SimpleGraph.ker_stableWLColoring`: single-graph stabilization
  within `|V| ^ k - k₀` (and `|V| ^ k`) rounds.
* `SimpleGraph.Iso.wlColoring_comp`, `SimpleGraph.Iso.wlHistogram_eq`,
  `SimpleGraph.isEmpty_iso_of_wlHistogram_ne`: isomorphism invariance and soundness of the `k`-WL
  isomorphism test.
* `SimpleGraph.wlColoring_eq_of_le`, `SimpleGraph.wlHistogram_eq_of_le`: agreement in round `m`
  implies agreement in every earlier round `n ≤ m`.
* `SimpleGraph.forall_wlColoring_eq_iff`, `SimpleGraph.forall_wlHistogram_eq_iff`: tuple colors or
  histograms agree in every round iff they agree in round `|V| ^ k + |W| ^ k`.

## References

* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 5.
-/

public section

open Finset

namespace SimpleGraph

variable {V W β γ : Type*}

/-! ### Atomic isomorphism types of tuples -/

/-- The ordered atomic isomorphism type of an `m`-tuple in a simple graph: the equality relation and
the adjacency relation among its coordinates. -/
abbrev TupleAtom (m : ℕ) : Type :=
  (Fin m → Fin m → Prop) × (Fin m → Fin m → Prop)

/-- The ordered atomic isomorphism type of `t : Fin m → V` in `G`. -/
def tupleAtom (G : SimpleGraph V) {m : ℕ} (t : Fin m → V) : TupleAtom m :=
  ((fun i j => t i = t j), (fun i j => G.Adj (t i) (t j)))

@[simp] theorem tupleAtom_fst (G : SimpleGraph V) {m : ℕ} (t : Fin m → V) (i j : Fin m) :
    (G.tupleAtom t).1 i j ↔ t i = t j :=
  Iff.rfl

@[simp] theorem tupleAtom_snd (G : SimpleGraph V) {m : ℕ} (t : Fin m → V) (i j : Fin m) :
    (G.tupleAtom t).2 i j ↔ G.Adj (t i) (t j) :=
  Iff.rfl

/-- Two tuples have the same atomic isomorphism type exactly when equality and adjacency agree on
all coordinate pairs. -/
theorem tupleAtom_eq_iff {G : SimpleGraph V} {H : SimpleGraph W} {m : ℕ}
    {t₁ : Fin m → V} {t₂ : Fin m → W} :
    G.tupleAtom t₁ = H.tupleAtom t₂ ↔
      ∀ i j, (t₁ i = t₁ j ↔ t₂ i = t₂ j) ∧ (G.Adj (t₁ i) (t₁ j) ↔ H.Adj (t₂ i) (t₂ j)) := by
  rw [tupleAtom, tupleAtom, Prod.mk.injEq]
  simp only [funext_iff, eq_iff_iff]
  exact ⟨fun ⟨heq, hadj⟩ i j => ⟨heq i j, hadj i j⟩,
    fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩⟩

/-- Reindexing coordinates preserves equality of atomic isomorphism types. -/
theorem tupleAtom_comp_eq {G : SimpleGraph V} {H : SimpleGraph W} {m r : ℕ}
    {t₁ : Fin m → V} {t₂ : Fin m → W} (h : G.tupleAtom t₁ = H.tupleAtom t₂) (g : Fin r → Fin m) :
    G.tupleAtom (t₁ ∘ g) = H.tupleAtom (t₂ ∘ g) := by
  rw [tupleAtom_eq_iff] at h ⊢
  exact fun i j => h (g i) (g j)

/-- Graph isomorphisms preserve the atomic isomorphism type of every tuple. -/
theorem Iso.tupleAtom_comp {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) {m : ℕ}
    (t : Fin m → V) : H.tupleAtom (e ∘ t) = G.tupleAtom t := by
  rw [tupleAtom_eq_iff]
  exact fun i j => ⟨e.injective.eq_iff, e.map_adj_iff⟩

/-! ### Colors, step profiles and `k`-WL refinement -/

/-- The colors of round `n` of `k`-dimensional Weisfeiler–Leman: round `0` records the atomic
isomorphism type of a `k`-tuple, and round `n + 1` pairs the round-`n` color with a multiset of step
profiles. -/
@[expose] def WLColor (k : ℕ) : ℕ → Type
  | 0 => TupleAtom k
  | n + 1 => WLColor k n × Multiset (TupleAtom (k + 1) × (Fin k → WLColor k n))

/-- The step profile of extending `u : Fin k → V` by `v : V` under a tuple coloring `χ`: the atomic
isomorphism type of `Fin.snoc u v` together with the colors of the `k` tuples obtained by replacing
each coordinate of `u` with `v`. -/
def wlStepProfile (G : SimpleGraph V) {k : ℕ} (χ : (Fin k → V) → β) (u : Fin k → V) (v : V) :
    TupleAtom (k + 1) × (Fin k → β) :=
  (G.tupleAtom (Fin.snoc u v), fun i => χ (Function.update u i v))

/-- One round of `k`-dimensional Weisfeiler–Leman refinement on `u : Fin k → V`. -/
def wlRefine [Fintype V] (G : SimpleGraph V) {k : ℕ} (χ : (Fin k → V) → β) (u : Fin k → V) :
    β × Multiset (TupleAtom (k + 1) × (Fin k → β)) :=
  (χ u, (univ : Finset V).val.map (G.wlStepProfile χ u))

/-- The `k`-dimensional Weisfeiler–Leman coloring of `G` after `n` rounds. -/
def wlColoring [Fintype V] (G : SimpleGraph V) {k : ℕ} : (n : ℕ) → (Fin k → V) → WLColor k n
  | 0 => G.tupleAtom
  | n + 1 => G.wlRefine (G.wlColoring n)

/-- The `k`-WL coloring after `|V| ^ k` rounds, whose partition is stable by
`SimpleGraph.ker_stableWLColoring`. -/
def stableWLColoring [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (Fin k → V) → WLColor k (Fintype.card V ^ k) :=
  G.wlColoring (Fintype.card V ^ k)

/-- The `k`-WL color histogram of round `n`: the multiset of colors of all `k`-tuples in `G`. -/
def wlHistogram [Fintype V] (G : SimpleGraph V) (k n : ℕ) : Multiset (WLColor k n) :=
  (univ : Finset (Fin k → V)).val.map (G.wlColoring n)

section Basic

variable {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}

theorem wlStepProfile_apply (χ : (Fin k → V) → β) (u : Fin k → V) (v : V) :
    G.wlStepProfile χ u v = (G.tupleAtom (Fin.snoc u v), fun i => χ (Function.update u i v)) := by
  rw [wlStepProfile]

theorem wlStepProfile_eq_iff {χ : (Fin k → V) → β} {ψ : (Fin k → W) → β}
    {u : Fin k → V} {w : Fin k → W} {v : V} {z : W} :
    G.wlStepProfile χ u v = H.wlStepProfile ψ w z ↔
      G.tupleAtom (Fin.snoc u v) = H.tupleAtom (Fin.snoc w z) ∧
        ∀ i, χ (Function.update u i v) = ψ (Function.update w i z) := by
  rw [wlStepProfile, wlStepProfile, Prod.mk.injEq, funext_iff]

variable [Fintype V]

theorem wlRefine_apply (χ : (Fin k → V) → β) (u : Fin k → V) :
    G.wlRefine χ u = (χ u, (univ : Finset V).val.map (G.wlStepProfile χ u)) := by
  rw [wlRefine]

theorem wlColoring_zero : G.wlColoring (k := k) 0 = G.tupleAtom := by
  rw [wlColoring]

theorem wlColoring_succ (n : ℕ) :
    G.wlColoring (k := k) (n + 1) = G.wlRefine (G.wlColoring n) := by
  rw [wlColoring]

theorem stableWLColoring_eq :
    G.stableWLColoring k = G.wlColoring (Fintype.card V ^ k) := by
  rw [stableWLColoring]

theorem wlHistogram_eq (k n : ℕ) :
    G.wlHistogram k n = (univ : Finset (Fin k → V)).val.map (G.wlColoring n) := by
  rw [wlHistogram]

theorem card_wlRefine_snd (χ : (Fin k → V) → β) (u : Fin k → V) :
    Multiset.card (G.wlRefine χ u).2 = Fintype.card V := by
  rw [wlRefine, Multiset.card_map, Finset.card_val, Finset.card_univ]

theorem card_wlHistogram (k n : ℕ) :
    Multiset.card (G.wlHistogram k n) = Fintype.card V ^ k := by
  rw [wlHistogram, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]

theorem mem_wlHistogram {n : ℕ} {c : WLColor k n} :
    c ∈ G.wlHistogram k n ↔ ∃ u : Fin k → V, G.wlColoring n u = c := by
  simp only [wlHistogram, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]

theorem wlRefine_eq_wlRefine_iff [Fintype W] {χ : (Fin k → V) → β} {ψ : (Fin k → W) → β}
    {u : Fin k → V} {w : Fin k → W} :
    G.wlRefine χ u = H.wlRefine ψ w ↔
      χ u = ψ w ∧
        (univ : Finset V).val.map (G.wlStepProfile χ u) =
          (univ : Finset W).val.map (H.wlStepProfile ψ w) :=
  Prod.ext_iff

theorem wlColoring_zero_eq_iff [Fintype W] {u : Fin k → V} {w : Fin k → W} :
    G.wlColoring 0 u = H.wlColoring 0 w ↔
      ∀ i j, (u i = u j ↔ w i = w j) ∧ (G.Adj (u i) (u j) ↔ H.Adj (w i) (w j)) := by
  change G.tupleAtom u = H.tupleAtom w ↔ _
  exact tupleAtom_eq_iff

theorem wlColoring_succ_eq_iff [Fintype W] {n : ℕ} {u : Fin k → V} {w : Fin k → W} :
    G.wlColoring (n + 1) u = H.wlColoring (n + 1) w ↔
      G.wlColoring n u = H.wlColoring n w ∧
        (univ : Finset V).val.map (G.wlStepProfile (G.wlColoring n) u) =
          (univ : Finset W).val.map (H.wlStepProfile (H.wlColoring n) w) := by
  change G.wlRefine (G.wlColoring n) u = H.wlRefine (H.wlColoring n) w ↔ _
  exact wlRefine_eq_wlRefine_iff

/-- If `χ₁ u = ψ₁ w` implies `χ₂ u = ψ₂ w` for all `k`-tuples, then the same implication holds
after one round of `k`-WL refinement. -/
theorem wlRefine_eq_of_imp [Fintype W] {χ₁ : (Fin k → V) → β} {ψ₁ : (Fin k → W) → β}
    {χ₂ : (Fin k → V) → γ} {ψ₂ : (Fin k → W) → γ}
    (himp : ∀ (u' : Fin k → V) (w' : Fin k → W), χ₁ u' = ψ₁ w' → χ₂ u' = ψ₂ w')
    {u : Fin k → V} {w : Fin k → W} (h : G.wlRefine χ₁ u = H.wlRefine ψ₁ w) :
    G.wlRefine χ₂ u = H.wlRefine ψ₂ w := by
  obtain ⟨huw, hmset⟩ := wlRefine_eq_wlRefine_iff.1 h
  refine wlRefine_eq_wlRefine_iff.2 ⟨himp u w huw, ?_⟩
  obtain ⟨f, hf⟩ := Equiv.exists_apply_eq_iff_map_univ_eq.2 hmset
  refine Equiv.exists_apply_eq_iff_map_univ_eq.1 ⟨f, fun v => ?_⟩
  obtain ⟨hatom, hupd⟩ := wlStepProfile_eq_iff.1 (hf v).symm
  exact (wlStepProfile_eq_iff.2 ⟨hatom, fun i => himp _ _ (hupd i)⟩).symm

/-- A round of `k`-WL refinement refines the tuple partition. -/
theorem ker_wlRefine_le (χ : (Fin k → V) → β) :
    Setoid.ker (G.wlRefine χ) ≤ Setoid.ker χ :=
  fun _ _ h => (wlRefine_eq_wlRefine_iff.1 h).1

/-- A round of `k`-WL refinement is monotone in the tuple partition. -/
theorem ker_wlRefine_mono {χ : (Fin k → V) → β} {ψ : (Fin k → V) → γ}
    (h : Setoid.ker χ ≤ Setoid.ker ψ) :
    Setoid.ker (G.wlRefine χ) ≤ Setoid.ker (G.wlRefine ψ) :=
  fun _ _ hu => wlRefine_eq_of_imp (fun _ _ h' => h h') hu

end Basic

/-! ### Refinement and stabilization -/

section Stabilization

open Cslib.SetPartition

/-- Generic finite-partition stabilization: an antitone sequence of setoid kernels on a finite type
`X` whose equality at `n` propagates to `n + 1` stabilizes by round `|X| - blocks (ker (Φ 0))`. -/
private theorem ker_eq_of_antitone_step {X : Type*} [Fintype X] {C : ℕ → Type*}
    (Φ : (n : ℕ) → X → C n)
    (hle : ∀ n, Setoid.ker (Φ (n + 1)) ≤ Setoid.ker (Φ n))
    (hstep : ∀ n, Setoid.ker (Φ (n + 1)) = Setoid.ker (Φ n) →
      Setoid.ker (Φ (n + 2)) = Setoid.ker (Φ (n + 1)))
    {m : ℕ} (hm : Fintype.card X - blocks (Setoid.ker (Φ 0)) ≤ m) :
    Setoid.ker (Φ m) = Setoid.ker (Φ (Fintype.card X - blocks (Setoid.ker (Φ 0)))) := by
  have hprop : ∀ {n r}, Setoid.ker (Φ (n + 1)) = Setoid.ker (Φ n) → n ≤ r →
      Setoid.ker (Φ r) = Setoid.ker (Φ n) := by
    intro n r hn hnr
    have hsucc : ∀ t, n ≤ t → Setoid.ker (Φ (t + 1)) = Setoid.ker (Φ t) := by
      intro t hnt
      induction t, hnt using Nat.le_induction with
      | base => exact hn
      | succ t hnt ih => exact hstep t ih
    induction r, hnr using Nat.le_induction with
    | base => rfl
    | succ t hnt ih => rw [hsucc t hnt, ih]
  set N := Fintype.card X - blocks (Setoid.ker (Φ 0))
  suffices ∃ i ≤ N, Setoid.ker (Φ (i + 1)) = Setoid.ker (Φ i) by
    obtain ⟨i, hi, h⟩ := this
    rw [hprop h (hi.trans hm), hprop h hi]
  by_contra hne
  push Not at hne
  have key : ∀ i ≤ N + 1, blocks (Setoid.ker (Φ 0)) + i ≤ blocks (Setoid.ker (Φ i)) := by
    intro i hi
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
      have hlt : blocks (Setoid.ker (Φ i)) < blocks (Setoid.ker (Φ (i + 1))) :=
        blocks_lt_of_lt (lt_of_le_of_ne (hle i) (hne i (by omega)))
      have := ih (by omega)
      omega
  have h1 := key (N + 1) le_rfl
  have h2 := blocks_le_card (Setoid.ker (Φ (N + 1)))
  have h3 := blocks_le_card (Setoid.ker (Φ 0))
  rw [Nat.card_eq_fintype_card] at h2 h3
  omega

variable [Fintype V] {G : SimpleGraph V} {k : ℕ}

/-- Each round of `k`-WL refines the tuple partition of the previous round. -/
theorem ker_wlColoring_succ_le (n : ℕ) :
    Setoid.ker (G.wlColoring (k := k) (n + 1)) ≤ Setoid.ker (G.wlColoring (k := k) n) :=
  ker_wlRefine_le _

theorem antitone_ker_wlColoring :
    Antitone fun n => Setoid.ker (G.wlColoring (k := k) n) :=
  antitone_nat_of_succ_le ker_wlColoring_succ_le

/-- Every round of `k`-WL refines the atomic tuple partition of round `0`. -/
theorem ker_wlColoring_le_zero (n : ℕ) :
    Setoid.ker (G.wlColoring (k := k) n) ≤ Setoid.ker (G.wlColoring (k := k) 0) :=
  antitone_ker_wlColoring (Nat.zero_le n)

/-- Once a round of `k`-WL does not change the tuple partition, no later round does. -/
theorem ker_wlColoring_eq_of_succ_eq {n : ℕ}
    (h : Setoid.ker (G.wlColoring (k := k) (n + 1)) = Setoid.ker (G.wlColoring (k := k) n))
    {m : ℕ} (hm : n ≤ m) :
    Setoid.ker (G.wlColoring (k := k) m) = Setoid.ker (G.wlColoring (k := k) n) := by
  have hsucc : ∀ t, n ≤ t → Setoid.ker (G.wlColoring (k := k) (t + 1)) =
      Setoid.ker (G.wlColoring (k := k) t) := by
    intro t hnt
    induction t, hnt using Nat.le_induction with
    | base => exact h
    | succ t _ ih =>
      exact le_antisymm (ker_wlColoring_succ_le _) (ker_wlRefine_mono (G := G) ih.ge)
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ t hnt ih => rw [hsucc t hnt, ih]

/-- The number of `k`-WL color classes does not decrease from one round to the next. -/
theorem blocks_ker_wlColoring_le_succ (n : ℕ) :
    blocks (Setoid.ker (G.wlColoring (k := k) n)) ≤
      blocks (Setoid.ker (G.wlColoring (k := k) (n + 1))) :=
  blocks_le_of_le (ker_wlColoring_succ_le n)

/-- The number of `k`-WL color classes increases strictly as long as the partition changes. -/
theorem blocks_ker_wlColoring_lt_succ {n : ℕ}
    (h : Setoid.ker (G.wlColoring (k := k) (n + 1)) ≠ Setoid.ker (G.wlColoring (k := k) n)) :
    blocks (Setoid.ker (G.wlColoring (k := k) n)) <
      blocks (Setoid.ker (G.wlColoring (k := k) (n + 1))) :=
  blocks_lt_of_lt (lt_of_le_of_ne (ker_wlColoring_succ_le n) h)

/-- **Stabilization of `k`-WL**: if round `0` has `k₀` atomic tuple classes, then the tuple
partition does not change after round `|V| ^ k - k₀`. -/
theorem ker_wlColoring_eq {m : ℕ}
    (hm : Fintype.card V ^ k - blocks (Setoid.ker (G.wlColoring (k := k) 0)) ≤ m) :
    Setoid.ker (G.wlColoring (k := k) m) =
      Setoid.ker (G.wlColoring (k := k)
        (Fintype.card V ^ k - blocks (Setoid.ker (G.wlColoring (k := k) 0)))) := by
  have hcard : Fintype.card (Fin k → V) = Fintype.card V ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [← hcard] at hm ⊢
  exact ker_eq_of_antitone_step (G.wlColoring (k := k)) ker_wlColoring_succ_le
    (fun n hn => le_antisymm (ker_wlColoring_succ_le _) (ker_wlRefine_mono hn.ge)) hm

/-- From round `|V| ^ k` on, the tuple partition is that of `stableWLColoring`. -/
theorem ker_stableWLColoring {m : ℕ} (hm : Fintype.card V ^ k ≤ m) :
    Setoid.ker (G.wlColoring (k := k) m) = Setoid.ker (G.stableWLColoring k) := by
  rw [stableWLColoring, ker_wlColoring_eq ((Nat.sub_le _ _).trans hm),
    ker_wlColoring_eq ((Nat.sub_le _ _).trans le_rfl)]

end Stabilization

/-! ### Isomorphism invariance and soundness -/

section Iso

variable [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}

/-- A graph isomorphism preserves the `k`-WL color of every tuple in every round. -/
theorem Iso.wlColoring_comp (e : G ≃g H) (n : ℕ) (u : Fin k → V) :
    H.wlColoring n (e ∘ u) = G.wlColoring n u := by
  induction n generalizing u with
  | zero =>
    rw [wlColoring_zero, wlColoring_zero]
    exact e.tupleAtom_comp u
  | succ n ih =>
    refine wlColoring_succ_eq_iff.2 ⟨ih u, ?_⟩
    rw [← Finset.map_univ_equiv e.toEquiv, Finset.map_val, Multiset.map_map]
    congr 1
    funext v
    change H.wlStepProfile (H.wlColoring n) (e ∘ u) (e v) =
      G.wlStepProfile (G.wlColoring n) u v
    refine wlStepProfile_eq_iff.2 ⟨?_, fun i => ?_⟩
    · rw [← Fin.comp_snoc]
      exact e.tupleAtom_comp (Fin.snoc u v)
    · rw [← Function.comp_update]
      exact ih (Function.update u i v)

/-- Isomorphic finite graphs have the same `k`-WL histogram in every round. -/
theorem Iso.wlHistogram_eq (e : G ≃g H) (k n : ℕ) :
    H.wlHistogram k n = G.wlHistogram k n := by
  let eTuple : (Fin k → V) ≃ (Fin k → W) := Equiv.arrowCongr (Equiv.refl (Fin k)) e.toEquiv
  rw [wlHistogram, wlHistogram, ← Finset.map_univ_equiv eTuple, Finset.map_val, Multiset.map_map]
  congr 1
  exact funext fun u => e.wlColoring_comp n u

/-- **Soundness of the `k`-WL isomorphism test**: if the `k`-WL histograms differ in some round,
then the graphs are not isomorphic. -/
theorem isEmpty_iso_of_wlHistogram_ne {n : ℕ} (h : G.wlHistogram k n ≠ H.wlHistogram k n) :
    IsEmpty (G ≃g H) :=
  ⟨fun e => h (e.wlHistogram_eq k n).symm⟩

end Iso

/-! ### Earlier rounds and completeness of round `|V| ^ k + |W| ^ k` -/

section Truncate

/-- Forget the last `r` rounds of a `k`-WL color of round `n + r`. -/
def WLColor.truncate {k : ℕ} (n : ℕ) : (r : ℕ) → WLColor k (n + r) → WLColor k n
  | 0, c => c
  | r + 1, c => truncate n r c.1

variable [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}

/-- The `k`-WL color of round `n + r` determines the color of round `n`. -/
theorem truncate_wlColoring (n r : ℕ) (u : Fin k → V) :
    (G.wlColoring (n + r) u).truncate n r = G.wlColoring n u := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih

/-- `k`-WL colors that agree in some round agree in every earlier round. -/
theorem wlColoring_eq_of_le {m n : ℕ} (hnm : n ≤ m) {u : Fin k → V} {w : Fin k → W}
    (h : G.wlColoring m u = H.wlColoring m w) :
    G.wlColoring n u = H.wlColoring n w := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [← truncate_wlColoring n r u, ← truncate_wlColoring n r w, h]

/-- The `k`-WL histogram of round `n + r` determines the histogram of round `n`. -/
theorem wlHistogram_map_truncate (k n r : ℕ) :
    (G.wlHistogram k (n + r)).map (WLColor.truncate n r) = G.wlHistogram k n := by
  rw [wlHistogram, wlHistogram, Multiset.map_map]
  congr 1
  exact funext (truncate_wlColoring n r)

/-- `k`-WL histograms that agree in some round agree in every earlier round. -/
theorem wlHistogram_eq_of_le {m n : ℕ} (hnm : n ≤ m)
    (h : G.wlHistogram k m = H.wlHistogram k m) :
    G.wlHistogram k n = H.wlHistogram k n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [← wlHistogram_map_truncate k n r, ← wlHistogram_map_truncate k n r, h]

end Truncate

section Completeness

open Cslib.SetPartition

variable [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}

private theorem ker_sum_wlColoring_le {m : ℕ}
    (hm : Fintype.card V ^ k + Fintype.card W ^ k ≤ m) :
    Setoid.ker (Sum.elim (G.wlColoring (k := k) (Fintype.card V ^ k + Fintype.card W ^ k))
        (H.wlColoring (k := k) (Fintype.card V ^ k + Fintype.card W ^ k))) ≤
      Setoid.ker (Sum.elim (G.wlColoring (k := k) m) (H.wlColoring (k := k) m)) := by
  let Φ : (n : ℕ) → (Fin k → V) ⊕ (Fin k → W) → WLColor k n :=
    fun n => Sum.elim (G.wlColoring n) (H.wlColoring n)
  have hle : ∀ n, Setoid.ker (Φ (n + 1)) ≤ Setoid.ker (Φ n) := by
    rintro n (u₁ | w₁) (u₂ | w₂) h <;> exact wlColoring_eq_of_le (Nat.le_succ n) h
  have hstep : ∀ n, Setoid.ker (Φ (n + 1)) = Setoid.ker (Φ n) →
      Setoid.ker (Φ (n + 2)) = Setoid.ker (Φ (n + 1)) := by
    intro n hn
    refine le_antisymm (hle (n + 1)) ?_
    rintro (u₁ | w₁) (u₂ | w₂) h1
    · exact wlRefine_eq_of_imp (fun u u' hu => hn.ge (x := .inl u) (y := .inl u') hu) h1
    · exact wlRefine_eq_of_imp (fun u w hu => hn.ge (x := .inl u) (y := .inr w) hu) h1
    · exact wlRefine_eq_of_imp (fun w u hw => hn.ge (x := .inr w) (y := .inl u) hw) h1
    · exact wlRefine_eq_of_imp (fun w w' hw => hn.ge (x := .inr w) (y := .inr w') hw) h1
  have hcard : Fintype.card ((Fin k → V) ⊕ (Fin k → W)) =
      Fintype.card V ^ k + Fintype.card W ^ k := by
    rw [Fintype.card_sum, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
  have hN := ker_eq_of_antitone_step Φ hle hstep (m := Fintype.card V ^ k + Fintype.card W ^ k)
    (by rw [hcard]; exact Nat.sub_le _ _)
  have hm' := ker_eq_of_antitone_step Φ hle hstep (m := m)
    (by rw [hcard]; exact (Nat.sub_le _ _).trans hm)
  exact (hN.trans hm'.symm).le

/-- `k`-WL distinguishes two `k`-tuples of `G` and `H` in some round if and only if it
distinguishes them in round `|V| ^ k + |W| ^ k`. -/
theorem forall_wlColoring_eq_iff {u : Fin k → V} {w : Fin k → W} :
    (∀ n, G.wlColoring n u = H.wlColoring n w) ↔
      G.wlColoring (Fintype.card V ^ k + Fintype.card W ^ k) u =
        H.wlColoring (Fintype.card V ^ k + Fintype.card W ^ k) w := by
  refine ⟨fun h => h _, fun h m => ?_⟩
  rcases le_total m (Fintype.card V ^ k + Fintype.card W ^ k) with hm | hm
  · exact wlColoring_eq_of_le hm h
  · exact ker_sum_wlColoring_le hm (x := .inl u) (y := .inr w) h

/-- `k`-WL distinguishes two graphs `G` and `H` in some round if and only if it distinguishes them
in round `|V| ^ k + |W| ^ k`. -/
theorem forall_wlHistogram_eq_iff :
    (∀ n, G.wlHistogram k n = H.wlHistogram k n) ↔
      G.wlHistogram k (Fintype.card V ^ k + Fintype.card W ^ k) =
        H.wlHistogram k (Fintype.card V ^ k + Fintype.card W ^ k) := by
  refine ⟨fun h => h _, fun h m => ?_⟩
  rcases le_total m (Fintype.card V ^ k + Fintype.card W ^ k) with hm | hm
  · exact wlHistogram_eq_of_le hm h
  let Φ : (n : ℕ) → (Fin k → V) ⊕ (Fin k → W) → WLColor k n :=
    fun n => Sum.elim (G.wlColoring n) (H.wlColoring n)
  have hG : ∀ n, G.wlHistogram k n =
      ((univ : Finset (Fin k → V)).val.map Sum.inl).map (Φ n) := fun n => by
    rw [wlHistogram, Multiset.map_map]
    rfl
  have hH : ∀ n, H.wlHistogram k n =
      ((univ : Finset (Fin k → W)).val.map Sum.inr).map (Φ n) := fun n => by
    rw [wlHistogram, Multiset.map_map]
    rfl
  rw [hG, hH] at h ⊢
  exact Multiset.map_eq_map_of_ker_le (ker_sum_wlColoring_le hm) h

end Completeness

end SimpleGraph
