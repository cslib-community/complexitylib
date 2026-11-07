/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.EdmondsKarp
public import Complexity.Computability.Circuit.BipartiteMatching
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators

/-!
# Maximum Bipartite Matching and König's Theorem via Network Flows

Formalizes the reduction of **maximum bipartite matching** and **minimum bipartite vertex cover**
to integral `s`-`t` network flow ([FordFulkerson1962], Chapter II, Sections 4–5, Theorem 4.1;
[CLRS2009], Section 26.3, Lemma 26.9, Theorem 26.10 & Corollary 26.11, pp. 732–735), derives
**König's Theorem** ([Koenig1931], pp. 116–119), bridges to
`Cslib.Circuits.BipartiteMatching.HasPerfectMatching`, and provides an executable polynomial-time
solver in `TimeM ℕ` via `edmondsKarpDenseM`.

## Model and source mapping

* **Bipartite graph (`G : L × R → Bool`):** edge indicator on finite left/right vertex types `L` and
  `R`, matching the convention of `Cslib.Circuits.BipartiteMatching` on `V × V → Bool`.
* **Unit-capacity flow network (`bipartiteNetwork G`):** adds `BipartiteVertex.source` and
  `BipartiteVertex.sink` with unit-capacity arcs `.source → .left u`, `.left u → .right v` whenever
  `G (u, v) = true`, and `.right v → .sink` ([CLRS2009], Section 26.3, pp. 732–733).
* **Flows ↔ matchings (`matchingToFlow`, `flowToMatching`):** every matching `M` yields an integral
  flow of value `M.card`, and every feasible integral flow `f` on `bipartiteNetwork G` induces a
  matching of cardinality `f.value.toNat` (`(M.card : ℤ) = f.value`; [CLRS2009], Lemma 26.9,
  pp. 733–734).
* **Cuts ↔ vertex covers & König's Theorem (`vertexCoverToCut`, `cutToVertexCover`,
  `exists_maxMatching_eq_minVertexCover`):** every vertex cover `C` yields an `s`-`t` cut of
  capacity `C.size`, and every `s`-`t` cut `S` yields a cover of size at most `cutCapacity S`.
  Combining with `Network.exists_maxFlow_eq_minCut` proves that maximum matching size equals minimum
  vertex cover size ([Koenig1931], pp. 116–119; [FordFulkerson1962], Chapter II, Section 4,
  Theorem 4.1).
* **Executable `TimeM` solver (`bipartiteMatchingM`, `decidePerfectMatchingM`):** transports
  `bipartiteNetwork G` onto `Fin (2 + (m + r))`, runs `edmondsKarpDenseM`, and materializes the
  resulting matching and König cover in `O((m + r)^5)` charged `TimeM` ticks.

## Cost model and limitations

* **Tick accounting and unit-cost primitives:** `bipartiteMatchingM` charges all ticks of
  `edmondsKarpDenseM` on `bipartiteFinNetwork G` plus explicit post-processing scans
  (`m * (r + 1)` ticks in `extractMatchingM` to inspect all `(u, v) ∈ Fin m × Fin r`, and at most
  `m * (r + 1) + r` ticks in `extractCoverM` to build `cover.left` and `cover.right`), and
  `decidePerfectMatchingM` charges `1` additional tick for the final cardinality comparison. As in
  `EdmondsKarp`, `Vector` indexing/update (`FlowMatrix`), `Finset` insertion/membership/cardinality
  operations, `ℕ` arithmetic, and edge-indicator queries `G (u, v)` inside each charged step are
  treated as unit-cost primitives (not persistent copy-on-write or bit-level Turing costs).
* **Algorithmic scope:** `bipartiteMatchingM` uses the dense Edmonds–Karp wrapper in `O((m + r)^5)`
  ticks rather than specialized unit-capacity blocking-flow phases (Hopcroft–Karp `O(|E| √|V|)`).

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.IsMatching`, `IsMaxMatching`: bipartite matchings and maximum
  matchings.
* `Cslib.Algorithms.Lean.MaxFlow.VertexCover`, `IsVertexCover`, `IsMinVertexCover`: bipartite
  vertex covers and minimum vertex covers.
* `Cslib.Algorithms.Lean.MaxFlow.BipartiteVertex`, `bipartiteNetwork`, `matchingToFlow`,
  `flowToMatching`, `vertexCoverToCut`, `cutToVertexCover`: unit-capacity flow reduction.
* `Cslib.Algorithms.Lean.MaxFlow.BipartiteOutput`, `bipartiteMatchingM`, `decidePerfectMatchingM`:
  executable `TimeM ℕ` solver for maximum bipartite matching, minimum vertex cover, and perfect
  matching decision.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.card_le_size_of_matching_vertexCover`: weak duality (`M.card ≤
  C.size`).
* `Cslib.Algorithms.Lean.MaxFlow.exists_maxMatching_eq_minVertexCover`: **König's Theorem**.
* `Cslib.Algorithms.Lean.MaxFlow.hasPerfectMatching_iff_exists_matching_card` and
  `hasPerfectMatching_iff_exists_flow_value_card`: characterizations of
  `Cslib.Circuits.BipartiteMatching.HasPerfectMatching`.
* `Cslib.Algorithms.Lean.MaxFlow.bipartiteMatchingM_correct`, `bipartiteMatchingM_time_le`,
  `decidePerfectMatchingM_eq_true_iff`, `decidePerfectMatchingM_time_le`: correctness and polynomial
  `TimeM` complexity bounds.

## References

* [D. König, *Gráfok és mátrixok*][Koenig1931]
* [L. R. Ford, Jr. and D. R. Fulkerson, *Flows in Networks*][FordFulkerson1962]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.Algorithms.Lean

/-! ### Bipartite matchings and vertex covers -/

section Definitions

variable {L R : Type*}

/-- `M` is a matching in the bipartite graph `G : L × R → Bool` if every pair in `M` is an edge of
`G` and no two edges in `M` share a left endpoint or a right endpoint. -/
@[expose] def IsMatching (G : L × R → Bool) (M : Finset (L × R)) : Prop :=
  (∀ e ∈ M, G e = true) ∧
    (∀ u v₁ v₂, (u, v₁) ∈ M → (u, v₂) ∈ M → v₁ = v₂) ∧
    (∀ u₁ u₂ v, (u₁, v) ∈ M → (u₂, v) ∈ M → u₁ = u₂)

instance instDecidableIsMatching [DecidableEq L] [DecidableEq R] (G : L × R → Bool)
    (M : Finset (L × R)) : Decidable (IsMatching G M) := by
  refine decidable_of_iff
    ((∀ e ∈ M, G e = true) ∧
      (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.1 = e₂.1 → e₁.2 = e₂.2) ∧
      (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.2 = e₂.2 → e₁.1 = e₂.1)) ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun u v₁ v₂ m₁ m₂ => h2 (u, v₁) m₁ (u, v₂) m₂ rfl,
      fun u₁ u₂ v m₁ m₂ => h3 (u₁, v) m₁ (u₂, v) m₂ rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rintro ⟨u₁, v₁⟩ m₁ ⟨u₂, v₂⟩ m₂ (hu : u₁ = u₂)
      subst hu
      exact h2 u₁ v₁ v₂ m₁ m₂
    · rintro ⟨u₁, v₁⟩ m₁ ⟨u₂, v₂⟩ m₂ (hv : v₁ = v₂)
      subst hv
      exact h3 u₁ u₂ v₁ m₁ m₂

/-- `M` is a maximum-cardinality matching in `G`. -/
@[expose] def IsMaxMatching (G : L × R → Bool) (M : Finset (L × R)) : Prop :=
  IsMatching G M ∧ ∀ M' : Finset (L × R), IsMatching G M' → M'.card ≤ M.card

/-- A bipartite vertex cover on `(L, R)`, consisting of chosen `left` and `right` vertex subsets. -/
structure VertexCover (L R : Type*) where
  /-- Chosen left vertices. -/
  left : Finset L
  /-- Chosen right vertices. -/
  right : Finset R

instance instDecidableEqVertexCover [DecidableEq L] [DecidableEq R] :
    DecidableEq (VertexCover L R) :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    (by cases a; cases b; simp)

/-- Total cardinality `|C.left| + |C.right|` of a bipartite vertex cover `C`. -/
@[expose] def VertexCover.size (C : VertexCover L R) : ℕ :=
  C.left.card + C.right.card

/-- `C` is a vertex cover of `G` if every edge `(u, v)` with `G (u, v) = true` has `u ∈ C.left` or
`v ∈ C.right`. -/
@[expose] def IsVertexCover (G : L × R → Bool) (C : VertexCover L R) : Prop :=
  ∀ u v, G (u, v) = true → u ∈ C.left ∨ v ∈ C.right

instance instDecidableIsVertexCover [Fintype L] [Fintype R] [DecidableEq L]
    [DecidableEq R] (G : L × R → Bool) (C : VertexCover L R) :
    Decidable (IsVertexCover G C) := by
  unfold IsVertexCover
  infer_instance

/-- `C` is a minimum-cardinality vertex cover of `G`. -/
@[expose] def IsMinVertexCover (G : L × R → Bool) (C : VertexCover L R) : Prop :=
  IsVertexCover G C ∧ ∀ C' : VertexCover L R, IsVertexCover G C' → C.size ≤ C'.size

end Definitions

/-! ### Unit-capacity flow network for a bipartite graph -/

section FlowReduction

variable {L R : Type*}

/-- Vertices of the unit-capacity `s`-`t` flow network for a bipartite graph on `(L, R)`:
designated `source` and `sink` together with `left u` (`u : L`) and `right v` (`v : R`). -/
inductive BipartiteVertex (L R : Type*)
  | source
  | sink
  | left (u : L)
  | right (v : R)

/-- Canonical equivalence between `BipartiteVertex L R` and `Bool ⊕ (L ⊕ R)`. -/
@[expose] def bipartiteVertexEquiv (L R : Type*) : BipartiteVertex L R ≃ Bool ⊕ (L ⊕ R) where
  toFun
    | .source => .inl false
    | .sink => .inl true
    | .left u => .inr (.inl u)
    | .right v => .inr (.inr v)
  invFun
    | .inl false => .source
    | .inl true => .sink
    | .inr (.inl u) => .left u
    | .inr (.inr v) => .right v
  left_inv x := by cases x <;> rfl
  right_inv y := by rcases y with (_ | _) | (_ | _) <;> rfl

instance instDecidableEqBipartiteVertex [DecidableEq L] [DecidableEq R] :
    DecidableEq (BipartiteVertex L R) :=
  (bipartiteVertexEquiv L R).decidableEq

instance instFintypeBipartiteVertex [Fintype L] [Fintype R] :
    Fintype (BipartiteVertex L R) :=
  Fintype.ofEquiv (Bool ⊕ (L ⊕ R)) (bipartiteVertexEquiv L R).symm

theorem sum_bipartiteVertex {M : Type*} [AddCommMonoid M] [Fintype L] [Fintype R]
    (g : BipartiteVertex L R → M) :
    (∑ x : BipartiteVertex L R, g x) =
      g .source + g .sink + (∑ u : L, g (.left u)) + (∑ v : R, g (.right v)) := by
  rw [← (bipartiteVertexEquiv L R).symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool,
    Fintype.sum_sum_type]
  simp only [bipartiteVertexEquiv, Equiv.coe_fn_symm_mk]
  rw [add_comm (g .sink) (g .source), ← add_assoc]

/-- Unit-capacity `s`-`t` network associated with `G : L × R → Bool` ([CLRS2009], Section 26.3,
pp. 732–733): unit arcs `.source → .left u`, `.left u → .right v` when `G (u, v) = true`, and
`.right v → .sink`. -/
@[expose] def bipartiteNetwork (G : L × R → Bool) : Network (BipartiteVertex L R) where
  cap x y :=
    match x, y with
    | .source, .left _ => 1
    | .left u, .right v => if G (u, v) then 1 else 0
    | .right _, .sink => 1
    | _, _ => 0
  s := .source
  t := .sink

theorem bipartiteNetwork_s_ne_t (G : L × R → Bool) :
    (bipartiteNetwork G).s ≠ (bipartiteNetwork G).t := by
  simp [bipartiteNetwork]

section FlowProperties

variable [Fintype L] [Fintype R] {G : L × R → Bool}

private theorem flow_in_source_eq_zero (f : (bipartiteNetwork G).Flow) (x : BipartiteVertex L R) :
    f x .source = 0 := by
  have h := f.le_cap x .source
  cases x <;> simp only [bipartiteNetwork] at h <;> omega

private theorem flow_source_out_eq_sum_left (f : (bipartiteNetwork G).Flow) :
    (∑ y : BipartiteVertex L R, f .source y) = ∑ u : L, f .source (.left u) := by
  rw [sum_bipartiteVertex]
  have hs : f .source .source = 0 := Nat.eq_zero_of_le_zero (f.le_cap .source .source)
  have ht : f .source .sink = 0 := Nat.eq_zero_of_le_zero (f.le_cap .source .sink)
  have hr : (∑ v : R, f .source (.right v)) = 0 :=
    Finset.sum_eq_zero fun v _ => Nat.eq_zero_of_le_zero (f.le_cap .source (.right v))
  omega

theorem bipartiteFlow_value_eq_sum_left (f : (bipartiteNetwork G).Flow) :
    f.value = ∑ u : L, (f .source (.left u) : ℤ) := by
  unfold Network.Flow.value Network.Flow.netOut
  change (∑ y : BipartiteVertex L R, (f .source y : ℤ)) -
      (∑ x : BipartiteVertex L R, (f x .source : ℤ)) = _
  have hin : (∑ x : BipartiteVertex L R, (f x .source : ℤ)) = 0 :=
    Finset.sum_eq_zero fun x _ => by simp [flow_in_source_eq_zero f x]
  have hout : (∑ y : BipartiteVertex L R, (f .source y : ℤ)) =
      ∑ u : L, (f .source (.left u) : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, flow_source_out_eq_sum_left f]
  omega

theorem bipartiteFlow_left_conserve (f : (bipartiteNetwork G).Flow) (u : L) :
    (∑ v : R, f (.left u) (.right v)) = f .source (.left u) := by
  have hcons := f.conserve (.left u) (by simp [bipartiteNetwork]) (by simp [bipartiteNetwork])
  rw [sum_bipartiteVertex, sum_bipartiteVertex] at hcons
  have h_out_s : f (.left u) .source = 0 := Nat.eq_zero_of_le_zero (f.le_cap (.left u) .source)
  have h_out_t : f (.left u) .sink = 0 := Nat.eq_zero_of_le_zero (f.le_cap (.left u) .sink)
  have h_out_l : (∑ u' : L, f (.left u) (.left u')) = 0 :=
    Finset.sum_eq_zero fun u' _ => Nat.eq_zero_of_le_zero (f.le_cap (.left u) (.left u'))
  have h_in_t : f .sink (.left u) = 0 := Nat.eq_zero_of_le_zero (f.le_cap .sink (.left u))
  have h_in_l : (∑ u' : L, f (.left u') (.left u)) = 0 :=
    Finset.sum_eq_zero fun u' _ => Nat.eq_zero_of_le_zero (f.le_cap (.left u') (.left u))
  have h_in_r : (∑ v : R, f (.right v) (.left u)) = 0 :=
    Finset.sum_eq_zero fun v _ => Nat.eq_zero_of_le_zero (f.le_cap (.right v) (.left u))
  omega

theorem bipartiteFlow_right_conserve (f : (bipartiteNetwork G).Flow) (v : R) :
    (∑ u : L, f (.left u) (.right v)) = f (.right v) .sink := by
  have hcons := f.conserve (.right v) (by simp [bipartiteNetwork]) (by simp [bipartiteNetwork])
  rw [sum_bipartiteVertex, sum_bipartiteVertex] at hcons
  have h_out_s : f (.right v) .source = 0 := Nat.eq_zero_of_le_zero (f.le_cap (.right v) .source)
  have h_out_l : (∑ u : L, f (.right v) (.left u)) = 0 :=
    Finset.sum_eq_zero fun u _ => Nat.eq_zero_of_le_zero (f.le_cap (.right v) (.left u))
  have h_out_r : (∑ v' : R, f (.right v) (.right v')) = 0 :=
    Finset.sum_eq_zero fun v' _ => Nat.eq_zero_of_le_zero (f.le_cap (.right v) (.right v'))
  have h_in_s : f .source (.right v) = 0 := Nat.eq_zero_of_le_zero (f.le_cap .source (.right v))
  have h_in_t : f .sink (.right v) = 0 := Nat.eq_zero_of_le_zero (f.le_cap .sink (.right v))
  have h_in_r : (∑ v' : R, f (.right v') (.right v)) = 0 :=
    Finset.sum_eq_zero fun v' _ => Nat.eq_zero_of_le_zero (f.le_cap (.right v') (.right v))
  omega

/-- Extract a bipartite matching from any feasible integral flow `f` on `bipartiteNetwork G` by
selecting pairs `(u, v)` carrying positive flow ([CLRS2009], Lemma 26.9, p. 733). -/
@[expose] def flowToMatching (f : (bipartiteNetwork G).Flow) : Finset (L × R) :=
  Finset.univ.filter fun e => 0 < f (.left e.1) (.right e.2)

theorem isMatching_flowToMatching (f : (bipartiteNetwork G).Flow) :
    IsMatching G (flowToMatching f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨u, v⟩ he
    simp only [flowToMatching, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have hcap := f.le_cap (.left u) (.right v)
    simp only [bipartiteNetwork] at hcap
    cases hG : G (u, v)
    · rw [hG] at hcap
      simp only [Bool.false_eq_true, ↓reduceIte] at hcap
      omega
    · rfl
  · intro u v₁ v₂ hv₁ hv₂
    simp only [flowToMatching, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    by_contra hne
    have hpair : ∑ v ∈ ({v₁, v₂} : Finset R), f (.left u) (.right v) =
        f (.left u) (.right v₁) + f (.left u) (.right v₂) := Finset.sum_pair hne
    have hsub : ∑ v ∈ ({v₁, v₂} : Finset R), f (.left u) (.right v) ≤
        ∑ v : R, f (.left u) (.right v) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hcons := bipartiteFlow_left_conserve f u
    have hcap : f .source (.left u) ≤ 1 := f.le_cap .source (.left u)
    omega
  · intro u₁ u₂ v hu₁ hu₂
    simp only [flowToMatching, Finset.mem_filter, Finset.mem_univ, true_and] at hu₁ hu₂
    by_contra hne
    have hpair : ∑ u ∈ ({u₁, u₂} : Finset L), f (.left u) (.right v) =
        f (.left u₁) (.right v) + f (.left u₂) (.right v) := Finset.sum_pair hne
    have hsub : ∑ u ∈ ({u₁, u₂} : Finset L), f (.left u) (.right v) ≤
        ∑ u : L, f (.left u) (.right v) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hcons := bipartiteFlow_right_conserve f v
    have hcap : f (.right v) .sink ≤ 1 := f.le_cap (.right v) .sink
    omega

theorem card_flowToMatching_coe (f : (bipartiteNetwork G).Flow) :
    ((flowToMatching f).card : ℤ) = f.value := by
  have h01 : ∀ u : L, ∀ v : R,
      (if 0 < f (.left u) (.right v) then 1 else 0) = f (.left u) (.right v) := by
    intro u v
    have hle : f (.left u) (.right v) ≤ 1 := by
      have hcap := f.le_cap (.left u) (.right v)
      simp only [bipartiteNetwork] at hcap
      split_ifs at hcap <;> omega
    split_ifs <;> omega
  have hcard : (flowToMatching f).card = ∑ u : L, f .source (.left u) := by
    calc
      (flowToMatching f).card = ∑ _e ∈ flowToMatching f, 1 := by simp
      _ = ∑ e : L × R, if 0 < f (.left e.1) (.right e.2) then 1 else 0 :=
        Finset.sum_filter _ _
      _ = ∑ u : L, ∑ v : R, if 0 < f (.left u) (.right v) then 1 else 0 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ u : L, ∑ v : R, f (.left u) (.right v) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => h01 u v
      _ = ∑ u : L, f .source (.left u) :=
        Finset.sum_congr rfl fun u _ => bipartiteFlow_left_conserve f u
  rw [hcard, bipartiteFlow_value_eq_sum_left, Nat.cast_sum]

/-- Construct a feasible unit integral flow on `bipartiteNetwork G` of value `M.card` from any
bipartite matching `M` ([CLRS2009], Lemma 26.9, p. 733). -/
@[expose] def matchingToFlow [DecidableEq L] [DecidableEq R] {M : Finset (L × R)}
    (hM : IsMatching G M) : (bipartiteNetwork G).Flow where
  toFun x y :=
    match x, y with
    | .source, .left u => if ∃ v : R, (u, v) ∈ M then 1 else 0
    | .left u, .right v => if (u, v) ∈ M then 1 else 0
    | .right v, .sink => if ∃ u : L, (u, v) ∈ M then 1 else 0
    | _, _ => 0
  le_cap x y := by
    obtain ⟨hM_edge, _, _⟩ := hM
    cases x <;> cases y <;> simp only [bipartiteNetwork]
    all_goals try exact Nat.zero_le _
    · split_ifs <;> omega
    · rename_i u v
      by_cases hmem : (u, v) ∈ M
      · simp [hmem, hM_edge (u, v) hmem]
      · simp [hmem]
    · split_ifs <;> omega
  conserve x hxs hxt := by
    obtain ⟨_, hM_left, hM_right⟩ := hM
    cases x with
    | source => exact absurd rfl hxs
    | sink => exact absurd rfl hxt
    | left u =>
      rw [sum_bipartiteVertex, sum_bipartiteVertex]
      simp only [Nat.zero_add, Finset.sum_const_zero, Nat.add_zero]
      by_cases hex : ∃ v : R, (u, v) ∈ M
      · simp only [hex, ↓reduceIte]
        obtain ⟨v₀, hv₀⟩ := hex
        symm
        rw [Finset.sum_eq_single v₀
          (fun v _ hne => by
            have hnot : (u, v) ∉ M := fun hv => hne (hM_left u v v₀ hv hv₀)
            simp only [hnot, ↓reduceIte])
          (fun h => absurd (Finset.mem_univ v₀) h)]
        simp only [hv₀, ↓reduceIte]
      · simp only [hex, ↓reduceIte]
        symm
        exact Finset.sum_eq_zero fun v _ => by
          have hnot : (u, v) ∉ M := fun hv => hex ⟨v, hv⟩
          simp only [hnot, ↓reduceIte]
    | right v =>
      rw [sum_bipartiteVertex, sum_bipartiteVertex]
      simp only [Nat.zero_add, Finset.sum_const_zero, Nat.add_zero]
      by_cases hex : ∃ u : L, (u, v) ∈ M
      · simp only [hex, ↓reduceIte]
        obtain ⟨u₀, hu₀⟩ := hex
        rw [Finset.sum_eq_single u₀
          (fun u _ hne => by
            have hnot : (u, v) ∉ M := fun hu => hne (hM_right u u₀ v hu hu₀)
            simp only [hnot, ↓reduceIte])
          (fun h => absurd (Finset.mem_univ u₀) h)]
        simp only [hu₀, ↓reduceIte]
      · simp only [hex, ↓reduceIte]
        exact Finset.sum_eq_zero fun u _ => by
          have hnot : (u, v) ∉ M := fun hu => hex ⟨u, hu⟩
          simp only [hnot, ↓reduceIte]

@[simp]
theorem value_matchingToFlow [DecidableEq L] [DecidableEq R] {M : Finset (L × R)}
    (hM : IsMatching G M) : (matchingToFlow hM).value = (M.card : ℤ) := by
  rw [bipartiteFlow_value_eq_sum_left, ← Nat.cast_sum]
  congr 1
  have hlhs :
      (∑ u : L, (matchingToFlow hM) .source (.left u)) =
        ∑ u : L, ∑ v : R, (matchingToFlow hM) (.left u) (.right v) :=
    Finset.sum_congr rfl fun u _ => (bipartiteFlow_left_conserve (matchingToFlow hM) u).symm
  rw [hlhs]
  calc
    (∑ u : L, ∑ v : R, (if (u, v) ∈ M then 1 else 0))
      = ∑ e : L × R, if e ∈ M then 1 else 0 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ _e ∈ Finset.univ.filter (fun e : L × R => e ∈ M), 1 :=
        (Finset.sum_filter _ _).symm
    _ = M.card := by
        have hflt : Finset.univ.filter (fun e : L × R => e ∈ M) = M := by ext e; simp
        rw [hflt]
        simp

end FlowProperties

/-! ### Cuts, vertex covers, and König's Theorem -/

section Koenig

variable [Fintype L] [Fintype R] {G : L × R → Bool}

private theorem bipartiteNetwork_cutCapacity_eq [DecidableEq L] [DecidableEq R]
    {S : Finset (BipartiteVertex L R)} (hS : (bipartiteNetwork G).IsCut S) :
    (bipartiteNetwork G).cutCapacity S =
      (∑ u : L, if .left u ∉ S then 1 else 0) +
        (∑ u : L, ∑ v : R,
          if .left u ∈ S ∧ .right v ∉ S ∧ G (u, v) = true then 1 else 0) +
        (∑ v : R, if .right v ∈ S then 1 else 0) := by
  have hs_in : BipartiteVertex.source ∈ S := hS.1
  have ht_out : BipartiteVertex.sink ∉ S := hS.2
  have hexpand :
      (bipartiteNetwork G).cutCapacity S =
        ∑ x : BipartiteVertex L R, ∑ y : BipartiteVertex L R,
          if x ∈ S ∧ y ∉ S then (bipartiteNetwork G).cap x y else 0 := by
    unfold Network.cutCapacity
    have hmem : S = Finset.univ.filter (fun x : BipartiteVertex L R => x ∈ S) := by ext x; simp
    have hsdiff : Finset.univ \ S = Finset.univ.filter (fun y : BipartiteVertex L R => y ∉ S) := by
      ext y; simp
    rw [hsdiff]
    conv_lhs => rw [hmem]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ S
    · simp [hx, Finset.sum_filter]
    · simp [hx]
  rw [hexpand, sum_bipartiteVertex]
  have h_src :
      (∑ y : BipartiteVertex L R,
          if BipartiteVertex.source ∈ S ∧ y ∉ S then (bipartiteNetwork G).cap .source y else 0) =
        ∑ u : L, if .left u ∉ S then 1 else 0 := by
    rw [sum_bipartiteVertex]
    simp [bipartiteNetwork, hs_in]
  have h_snk :
      (∑ y : BipartiteVertex L R,
          if BipartiteVertex.sink ∈ S ∧ y ∉ S then
            (bipartiteNetwork G).cap .sink y
          else 0) = 0 := by
    simp [ht_out]
  have h_left :
      (∑ u : L, ∑ y : BipartiteVertex L R,
          if BipartiteVertex.left u ∈ S ∧ y ∉ S then
            (bipartiteNetwork G).cap (.left u) y
          else 0) =
        ∑ u : L, ∑ v : R,
          if .left u ∈ S ∧ .right v ∉ S ∧ G (u, v) = true then 1 else 0 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [sum_bipartiteVertex]
    simp only [bipartiteNetwork, ite_self, Nat.zero_add, Finset.sum_const_zero]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h1 : BipartiteVertex.left u ∈ S <;>
      by_cases h2 : BipartiteVertex.right v ∉ S <;>
      cases G (u, v) <;> simp [h1, h2]
  have h_right :
      (∑ v : R, ∑ y : BipartiteVertex L R,
          if BipartiteVertex.right v ∈ S ∧ y ∉ S then
            (bipartiteNetwork G).cap (.right v) y
          else 0) =
        ∑ v : R, if .right v ∈ S then 1 else 0 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [sum_bipartiteVertex]
    simp [bipartiteNetwork, ht_out]
  rw [h_src, h_snk, h_left, h_right]
  omega

/-- Boolean membership predicate for `vertexCoverToCut C`. -/
private def vertexCoverCutPred [DecidableEq L] [DecidableEq R]
    (C : VertexCover L R) : BipartiteVertex L R → Bool
  | .source => true
  | .sink => false
  | .left u => decide (u ∉ C.left)
  | .right v => decide (v ∈ C.right)

/-- Turn a bipartite vertex cover `C` into an `s`-`t` cut of `bipartiteNetwork G` of capacity
`C.size` ([FordFulkerson1962], Chapter II, Section 4, Theorem 4.1). -/
def vertexCoverToCut [DecidableEq L] [DecidableEq R]
    (C : VertexCover L R) : Finset (BipartiteVertex L R) :=
  Finset.univ.filter fun x => vertexCoverCutPred C x = true

theorem isCut_vertexCoverToCut [DecidableEq L] [DecidableEq R]
    (C : VertexCover L R) : (bipartiteNetwork G).IsCut (vertexCoverToCut C) := by
  simp [Network.IsCut, bipartiteNetwork, vertexCoverToCut, vertexCoverCutPred]

theorem cutCapacity_vertexCoverToCut [DecidableEq L] [DecidableEq R]
    {C : VertexCover L R} (hC : IsVertexCover G C) :
    (bipartiteNetwork G).cutCapacity (vertexCoverToCut C) = C.size := by
  rw [bipartiteNetwork_cutCapacity_eq (isCut_vertexCoverToCut C)]
  have hL :
      (∑ u : L, if BipartiteVertex.left u ∉ vertexCoverToCut C then 1 else 0) = C.left.card := by
    have : (fun u : L => if BipartiteVertex.left u ∉ vertexCoverToCut C then 1 else 0) =
        fun u : L => if u ∈ C.left then 1 else 0 := by
      funext u
      simp [vertexCoverToCut, vertexCoverCutPred]
    rw [this, ← Finset.sum_filter]
    have hflt : Finset.univ.filter (fun u : L => u ∈ C.left) = C.left := by ext u; simp
    rw [hflt]
    simp
  have hM :
      (∑ u : L, ∑ v : R,
          if BipartiteVertex.left u ∈ vertexCoverToCut C ∧
              BipartiteVertex.right v ∉ vertexCoverToCut C ∧ G (u, v) = true then
            1
          else 0) = 0 := by
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
    by_cases hG : G (u, v) = true
    · rcases hC u v hG with hu | hv
      · simp [vertexCoverToCut, vertexCoverCutPred, hu, hG]
      · simp [vertexCoverToCut, vertexCoverCutPred, hv, hG]
    · simp [hG]
  have hR :
      (∑ v : R, if BipartiteVertex.right v ∈ vertexCoverToCut C then 1 else 0) = C.right.card := by
    have : (fun v : R => if BipartiteVertex.right v ∈ vertexCoverToCut C then 1 else 0) =
        fun v : R => if v ∈ C.right then 1 else 0 := by
      funext v
      simp [vertexCoverToCut, vertexCoverCutPred]
    rw [this, ← Finset.sum_filter]
    have hflt : Finset.univ.filter (fun v : R => v ∈ C.right) = C.right := by ext v; simp
    rw [hflt]
    simp
  rw [hL, hM, hR]
  unfold VertexCover.size
  omega

/-- Extract a bipartite vertex cover of size at most `cutCapacity S` from any `s`-`t` cut `S` of
`bipartiteNetwork G`. -/
@[expose] def cutToVertexCover [DecidableEq L] [DecidableEq R]
    (G : L × R → Bool) (S : Finset (BipartiteVertex L R)) : VertexCover L R where
  left := Finset.univ.filter fun u => .left u ∉ S ∨ ∃ v : R, G (u, v) = true ∧ .right v ∉ S
  right := Finset.univ.filter fun v => .right v ∈ S

theorem isVertexCover_cutToVertexCover [DecidableEq L] [DecidableEq R]
    (G : L × R → Bool) (S : Finset (BipartiteVertex L R)) :
    IsVertexCover G (cutToVertexCover G S) := by
  intro u v hG
  by_cases hv : BipartiteVertex.right v ∈ S
  · exact .inr (by simp [cutToVertexCover, hv])
  · left
    simp only [cutToVertexCover, Finset.mem_filter, Finset.mem_univ, true_and]
    exact .inr ⟨v, hG, hv⟩

theorem size_cutToVertexCover_le [DecidableEq L] [DecidableEq R]
    {S : Finset (BipartiteVertex L R)} (hS : (bipartiteNetwork G).IsCut S) :
    (cutToVertexCover G S).size ≤ (bipartiteNetwork G).cutCapacity S := by
  rw [bipartiteNetwork_cutCapacity_eq hS]
  unfold VertexCover.size cutToVertexCover
  have hL_card :
      (Finset.univ.filter
          (fun u : L => .left u ∉ S ∨ ∃ v : R, G (u, v) = true ∧ .right v ∉ S)).card =
        ∑ u : L,
          if .left u ∉ S ∨ ∃ v : R, G (u, v) = true ∧ .right v ∉ S then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  have hR_card :
      (Finset.univ.filter (fun v : R => .right v ∈ S)).card =
        ∑ v : R, if .right v ∈ S then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [hL_card, hR_card, ← Finset.sum_add_distrib]
  have hle_left :
      (∑ u : L, if .left u ∉ S ∨ ∃ v : R, G (u, v) = true ∧ .right v ∉ S then 1 else 0) ≤
        ∑ u : L,
          ((if .left u ∉ S then 1 else 0) +
            ∑ v : R, if .left u ∈ S ∧ .right v ∉ S ∧ G (u, v) = true then 1 else 0) := by
    refine Finset.sum_le_sum fun u _ => ?_
    by_cases hu : BipartiteVertex.left u ∉ S
    · simp [hu]
    · have hu_in : BipartiteVertex.left u ∈ S := Classical.not_not.mp hu
      by_cases hex : ∃ v : R, G (u, v) = true ∧ BipartiteVertex.right v ∉ S
      · simp only [hu, false_or, hex, ↓reduceIte, zero_add]
        obtain ⟨v₀, hG₀, hv₀⟩ := hex
        let term : R → ℕ := fun v =>
          if BipartiteVertex.left u ∈ S ∧ BipartiteVertex.right v ∉ S ∧ G (u, v) = true then 1
          else 0
        have hterm₀ : term v₀ = 1 := by simp [term, hu_in, hv₀, hG₀]
        have hsingle : term v₀ ≤ ∑ v : R, term v :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v₀)
        simpa [term, hterm₀] using hsingle
      · simp [hu, hex]
  omega

end Koenig

section KoenigFinite

variable [Finite L] [Finite R] {G : L × R → Bool}

/-- **Weak duality for bipartite matchings and vertex covers:** every matching `M` in `G` has
cardinality at most the size of every vertex cover `C` of `G`. -/
theorem card_le_size_of_matching_vertexCover {M : Finset (L × R)} (hM : IsMatching G M)
    {C : VertexCover L R} (hC : IsVertexCover G C) :
    M.card ≤ C.size := by
  classical
  cases nonempty_fintype L
  cases nonempty_fintype R
  have hflow := (matchingToFlow hM).value_le_cutCapacity (isCut_vertexCoverToCut (G := G) C)
  rw [value_matchingToFlow hM, cutCapacity_vertexCoverToCut hC] at hflow
  omega

/-- **König's Theorem** ([Koenig1931], pp. 116–119; [FordFulkerson1962], Chapter II, Section 4,
Theorem 4.1): every finite bipartite graph `G : L × R → Bool` admits a maximum matching `M` and a
minimum vertex cover `C` of equal size (`M.card = C.size`). -/
theorem exists_maxMatching_eq_minVertexCover (G : L × R → Bool) :
    ∃ (M : Finset (L × R)) (C : VertexCover L R),
      IsMaxMatching G M ∧ IsMinVertexCover G C ∧ M.card = C.size := by
  classical
  cases nonempty_fintype L
  cases nonempty_fintype R
  obtain ⟨f, S, _, hS_min, hval⟩ :=
    (bipartiteNetwork G).exists_maxFlow_eq_minCut (bipartiteNetwork_s_ne_t G)
  let M := flowToMatching f
  let C := cutToVertexCover G S
  have hM : IsMatching G M := isMatching_flowToMatching f
  have hC : IsVertexCover G C := isVertexCover_cutToVertexCover G S
  have hM_eq_cap : M.card = (bipartiteNetwork G).cutCapacity S := by
    have hcoe := card_flowToMatching_coe f
    change (M.card : ℤ) = f.value at hcoe
    omega
  have hC_le_cap : C.size ≤ (bipartiteNetwork G).cutCapacity S :=
    size_cutToVertexCover_le hS_min.1
  have hM_le_C : M.card ≤ C.size := card_le_size_of_matching_vertexCover hM hC
  have heq : M.card = C.size := by omega
  refine ⟨M, C, ⟨hM, fun M' hM' => ?_⟩, ⟨hC, fun C' hC' => ?_⟩, heq⟩
  · have := card_le_size_of_matching_vertexCover hM' hC
    omega
  · have := card_le_size_of_matching_vertexCover hM hC'
    omega

end KoenigFinite

end FlowReduction

/-! ### Bridge to `Cslib.Circuits.BipartiteMatching.HasPerfectMatching` -/

section PerfectMatchingBridge

variable {V : Type*} [Fintype V]

/-- `HasPerfectMatching G` holds if and only if `G` admits a matching of cardinality
`Fintype.card V`. -/
theorem hasPerfectMatching_iff_exists_matching_card (G : V × V → Bool) :
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching G ↔
      ∃ M : Finset (V × V), IsMatching G M ∧ M.card = Fintype.card V := by
  classical
  constructor
  · rintro ⟨σ, hσ⟩
    let M : Finset (V × V) := Finset.univ.image fun u => (u, σ u)
    have hinj : Function.Injective (fun u : V => (u, σ u)) := fun a b h => (Prod.mk.inj h).1
    refine ⟨M, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro e he
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
      exact hσ u
    · intro u v₁ v₂ h₁ h₂
      obtain ⟨a₁, _, ha₁⟩ := Finset.mem_image.mp h₁
      obtain ⟨a₂, _, ha₂⟩ := Finset.mem_image.mp h₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha₂
      rfl
    · intro u₁ u₂ v h₁ h₂
      obtain ⟨a₁, _, ha₁⟩ := Finset.mem_image.mp h₁
      obtain ⟨a₂, _, ha₂⟩ := Finset.mem_image.mp h₂
      obtain ⟨rfl, hv₁⟩ := Prod.mk.inj ha₁
      obtain ⟨rfl, hv₂⟩ := Prod.mk.inj ha₂
      exact σ.injective (hv₁.trans hv₂.symm)
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  · rintro ⟨M, ⟨hM_edge, hM_left, hM_right⟩, hcard⟩
    have hinj_fst : Set.InjOn Prod.fst (M : Set (V × V)) := by
      intro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hu : u₁ = u₂)
      subst hu
      exact Prod.ext rfl (hM_left u₁ v₁ v₂ h₁ h₂)
    have himg_card : (M.image Prod.fst).card = Fintype.card V := by
      rw [Finset.card_image_of_injOn hinj_fst, hcard]
    have himg_univ : M.image Prod.fst = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [himg_card])
    have hex : ∀ u : V, ∃ v : V, (u, v) ∈ M := by
      intro u
      have hu : u ∈ M.image Prod.fst := by rw [himg_univ]; exact Finset.mem_univ u
      obtain ⟨⟨u', v⟩, hmem, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨v, hmem⟩
    let g : V → V := fun u => Classical.choose (hex u)
    have hg_mem : ∀ u : V, (u, g u) ∈ M := fun u => Classical.choose_spec (hex u)
    have hg_inj : Function.Injective g := fun u₁ u₂ heq =>
      hM_right u₁ u₂ (g u₁) (hg_mem u₁) (heq ▸ hg_mem u₂)
    exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj),
      fun u => hM_edge (u, g u) (hg_mem u)⟩

/-- Flow characterization of `HasPerfectMatching G`: `G : V × V → Bool` has a perfect matching if
and only if `bipartiteNetwork G` admits an integral flow of value `Fintype.card V`. -/
theorem hasPerfectMatching_iff_exists_flow_value_card (G : V × V → Bool) :
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching G ↔
      ∃ f : (bipartiteNetwork G).Flow, f.value = (Fintype.card V : ℤ) := by
  classical
  rw [hasPerfectMatching_iff_exists_matching_card]
  constructor
  · rintro ⟨M, hM, hcard⟩
    exact ⟨matchingToFlow hM, by rw [value_matchingToFlow hM, hcard]⟩
  · rintro ⟨f, hval⟩
    refine ⟨flowToMatching f, isMatching_flowToMatching f, ?_⟩
    have hcoe := card_flowToMatching_coe f
    omega

end PerfectMatchingBridge

/-! ### Executable polynomial-time bipartite matching and König cover solver in `TimeM ℕ` -/

section ExecutableBipartite

/-- Equivalence between `Bool` and `Fin 2` (`false ↦ 0`, `true ↦ 1`). -/
@[expose] def boolEquivFin2 : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i.1 == 1
  left_inv b := by cases b <;> rfl
  right_inv i := by rcases i with ⟨_ | _ | _, hi⟩ <;> [rfl; rfl; omega]

/-- Computable vertex equivalence `BipartiteVertex (Fin m) (Fin r) ≃ Fin (2 + (m + r))`. -/
@[expose] def bipartiteFinEquiv (m r : ℕ) :
    BipartiteVertex (Fin m) (Fin r) ≃ Fin (2 + (m + r)) :=
  (bipartiteVertexEquiv (Fin m) (Fin r)).trans
    ((Equiv.sumCongr boolEquivFin2 finSumFinEquiv).trans finSumFinEquiv)

/-- Reindexed `Fin (2 + (m + r))` flow network for `G : Fin m × Fin r → Bool`. -/
@[expose] def bipartiteFinNetwork {m r : ℕ}
    (G : Fin m × Fin r → Bool) : Network (Fin (2 + (m + r))) :=
  (bipartiteNetwork G).reindex (bipartiteFinEquiv m r)

/-- Output of `bipartiteMatchingM` on `G : Fin m × Fin r → Bool`. -/
structure BipartiteOutput (m r : ℕ) where
  /-- Maximum-cardinality matching in `G`. -/
  matching : Finset (Fin m × Fin r)
  /-- Minimum-cardinality König vertex cover of `G`. -/
  cover : VertexCover (Fin m) (Fin r)
  /-- Number of shortest-path augmentations performed by Edmonds–Karp. -/
  augmentations : ℕ

/-- Scan right vertices `vs` for positive flow from `.left u`, charging `1` tick per pair. -/
@[expose] def extractMatchingRowM {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) (u : Fin m) :
    List (Fin r) → Finset (Fin m × Fin r) → TimeM ℕ (Finset (Fin m × Fin r))
  | [], acc => pure acc
  | v :: vs, acc => do
    ✓
    let acc' := if 0 < f (.left u) (.right v) then insert (u, v) acc else acc
    extractMatchingRowM f u vs acc'

private theorem mem_extractMatchingRowM_ret {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) (u : Fin m) (vs : List (Fin r))
    (acc : Finset (Fin m × Fin r)) (e : Fin m × Fin r) :
    e ∈ (extractMatchingRowM f u vs acc).ret ↔
      e ∈ acc ∨ (e.1 = u ∧ e.2 ∈ vs ∧ 0 < f (.left u) (.right e.2)) := by
  induction vs generalizing acc with
  | nil => simp [extractMatchingRowM]
  | cons v vs' ih =>
    simp only [extractMatchingRowM, TimeM.ret_bind, ih, List.mem_cons]
    rcases e with ⟨u', v'⟩
    by_cases hpos : 0 < f (.left u) (.right v)
    · simp only [hpos, ↓reduceIte, Finset.mem_insert, Prod.mk.injEq]
      constructor
      · rintro ((⟨rfl, rfl⟩ | hacc) | ⟨rfl, hvs, hp⟩)
        · exact .inr ⟨rfl, .inl rfl, hpos⟩
        · exact .inl hacc
        · exact .inr ⟨rfl, .inr hvs, hp⟩
      · rintro (hacc | ⟨rfl, rfl | hvs, hp⟩)
        · exact .inl (.inr hacc)
        · exact .inl (.inl ⟨rfl, rfl⟩)
        · exact .inr ⟨rfl, hvs, hp⟩
    · simp only [hpos, ↓reduceIte]
      constructor
      · rintro (hacc | ⟨rfl, hvs, hp⟩)
        · exact .inl hacc
        · exact .inr ⟨rfl, .inr hvs, hp⟩
      · rintro (hacc | ⟨rfl, rfl | hvs, hp⟩)
        · exact .inl hacc
        · exact absurd hp hpos
        · exact .inr ⟨rfl, hvs, hp⟩

private theorem extractMatchingRowM_time {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) (u : Fin m) (vs : List (Fin r))
    (acc : Finset (Fin m × Fin r)) :
    (extractMatchingRowM f u vs acc).time = vs.length := by
  induction vs generalizing acc with
  | nil => rfl
  | cons _ vs' ih =>
    simp only [extractMatchingRowM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    omega

/-- Scan left vertices `us` and all right vertices `Fin r` to extract `flowToMatching f`. -/
@[expose] def extractMatchingLoopM {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) :
    List (Fin m) → Finset (Fin m × Fin r) → TimeM ℕ (Finset (Fin m × Fin r))
  | [], acc => pure acc
  | u :: us, acc => do
    ✓
    let acc' ← extractMatchingRowM f u (List.finRange r) acc
    extractMatchingLoopM f us acc'

private theorem mem_extractMatchingLoopM_ret {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) (us : List (Fin m))
    (acc : Finset (Fin m × Fin r)) (e : Fin m × Fin r) :
    e ∈ (extractMatchingLoopM f us acc).ret ↔
      e ∈ acc ∨ (e.1 ∈ us ∧ 0 < f (.left e.1) (.right e.2)) := by
  induction us generalizing acc with
  | nil => simp [extractMatchingLoopM]
  | cons u us' ih =>
    simp only [extractMatchingLoopM, TimeM.ret_bind, ih, mem_extractMatchingRowM_ret,
      List.mem_finRange, true_and, List.mem_cons]
    constructor
    · rintro ((hacc | ⟨he1, hp⟩) | ⟨hus, hp⟩)
      · exact .inl hacc
      · exact .inr ⟨.inl he1, he1 ▸ hp⟩
      · exact .inr ⟨.inr hus, hp⟩
    · rintro (hacc | ⟨he1 | hus, hp⟩)
      · exact .inl (.inl hacc)
      · exact .inl (.inr ⟨he1, he1 ▸ hp⟩)
      · exact .inr ⟨hus, hp⟩

private theorem extractMatchingLoopM_time {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) (us : List (Fin m)) (acc : Finset (Fin m × Fin r)) :
    (extractMatchingLoopM f us acc).time = us.length * (r + 1) := by
  induction us generalizing acc with
  | nil => simp [extractMatchingLoopM]
  | cons u us' ih =>
    simp only [extractMatchingLoopM, TimeM.time_bind, TimeM.time_tick, extractMatchingRowM_time,
      List.length_finRange, ih, List.length_cons]
    rw [Nat.add_one_mul]
    omega

/-- Extract `flowToMatching f` in `m * (r + 1)` charged `TimeM` ticks. -/
@[expose] def extractMatchingM {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) : TimeM ℕ (Finset (Fin m × Fin r)) :=
  extractMatchingLoopM f (List.finRange m) ∅

@[simp]
theorem extractMatchingM_ret {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) :
    (extractMatchingM f).ret = flowToMatching f := by
  ext e
  simp [extractMatchingM, mem_extractMatchingLoopM_ret, List.mem_finRange, flowToMatching]

@[simp]
theorem extractMatchingM_time {m r : ℕ} {G : Fin m × Fin r → Bool}
    (f : (bipartiteNetwork G).Flow) :
    (extractMatchingM f).time = m * (r + 1) := by
  simp [extractMatchingM, extractMatchingLoopM_time]

/-- Check whether `u` has an edge `G (u, v) = true` to a right vertex `v` whose reindexed vertex
lies outside `cut`, charging `1` tick per inspected right vertex. -/
@[expose] def hasUncoveredRightM {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) (u : Fin m) : List (Fin r) → TimeM ℕ Bool
  | [] => pure false
  | v :: vs => do
    ✓
    if G (u, v) && decide (bipartiteFinEquiv m r (.right v) ∉ cut) then
      pure true
    else
      hasUncoveredRightM G cut u vs

private theorem hasUncoveredRightM_ret {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) (u : Fin m) (vs : List (Fin r)) :
    (hasUncoveredRightM G cut u vs).ret = true ↔
      ∃ v ∈ vs, G (u, v) = true ∧ bipartiteFinEquiv m r (.right v) ∉ cut := by
  induction vs with
  | nil => simp [hasUncoveredRightM]
  | cons v vs' ih =>
    simp only [hasUncoveredRightM, TimeM.ret_bind, List.mem_cons]
    by_cases h : (G (u, v) && decide (bipartiteFinEquiv m r (.right v) ∉ cut)) = true
    · simp only [h, ↓reduceIte, TimeM.ret_pure, true_iff]
      obtain ⟨hG, hnot⟩ := Bool.and_eq_true_iff.mp h
      exact ⟨v, .inl rfl, hG, of_decide_eq_true hnot⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ih]
      constructor
      · rintro ⟨w, hw, hGw, hnw⟩
        exact ⟨w, .inr hw, hGw, hnw⟩
      · rintro ⟨w, rfl | hw, hGw, hnw⟩
        · exfalso
          apply h
          exact Bool.and_eq_true_iff.mpr ⟨hGw, decide_eq_true hnw⟩
        · exact ⟨w, hw, hGw, hnw⟩

private theorem hasUncoveredRightM_time_le {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) (u : Fin m) (vs : List (Fin r)) :
    (hasUncoveredRightM G cut u vs).time ≤ vs.length := by
  induction vs with
  | nil => simp [hasUncoveredRightM]
  | cons _ vs' ih =>
    simp only [hasUncoveredRightM, TimeM.time_bind, TimeM.time_tick, List.length_cons]
    split_ifs
    · simp only [TimeM.time_pure]
      omega
    · omega

/-- Scan left vertices `us` to build `(cutToVertexCover G S).left` in `TimeM ℕ`. -/
@[expose] def extractCoverLeftLoopM {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) :
    List (Fin m) → Finset (Fin m) → TimeM ℕ (Finset (Fin m))
  | [], acc => pure acc
  | u :: us, acc => do
    ✓
    if decide (bipartiteFinEquiv m r (.left u) ∉ cut) then
      extractCoverLeftLoopM G cut us (insert u acc)
    else
      let hit ← hasUncoveredRightM G cut u (List.finRange r)
      let acc' := if hit then insert u acc else acc
      extractCoverLeftLoopM G cut us acc'

private theorem mem_extractCoverLeftLoopM_ret {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) (us : List (Fin m)) (acc : Finset (Fin m)) (x : Fin m) :
    x ∈ (extractCoverLeftLoopM G cut us acc).ret ↔
      x ∈ acc ∨
        (x ∈ us ∧
          (bipartiteFinEquiv m r (.left x) ∉ cut ∨
            ∃ v : Fin r, G (x, v) = true ∧ bipartiteFinEquiv m r (.right v) ∉ cut)) := by
  induction us generalizing acc with
  | nil => simp [extractCoverLeftLoopM]
  | cons u us' ih =>
    simp only [extractCoverLeftLoopM, TimeM.ret_bind, List.mem_cons]
    by_cases hu : bipartiteFinEquiv m r (.left u) ∉ cut
    · simp only [decide_eq_true hu, ↓reduceIte, ih, Finset.mem_insert]
      constructor
      · rintro ((rfl | hacc) | ⟨hus, hp⟩)
        · exact .inr ⟨.inl rfl, .inl hu⟩
        · exact .inl hacc
        · exact .inr ⟨.inr hus, hp⟩
      · rintro (hacc | ⟨rfl | hus, hp⟩)
        · exact .inl (.inr hacc)
        · exact .inl (.inl rfl)
        · exact .inr ⟨hus, hp⟩
    · simp only [decide_eq_false hu, Bool.false_eq_true, ↓reduceIte, TimeM.ret_bind, ih]
      by_cases hhit : (hasUncoveredRightM G cut u (List.finRange r)).ret = true
      · simp only [hhit, ↓reduceIte, Finset.mem_insert]
        have hex : ∃ v : Fin r, G (u, v) = true ∧ bipartiteFinEquiv m r (.right v) ∉ cut := by
          simpa [List.mem_finRange] using
            (hasUncoveredRightM_ret G cut u (List.finRange r)).mp hhit
        constructor
        · rintro ((rfl | hacc) | ⟨hus, hp⟩)
          · exact .inr ⟨.inl rfl, .inr hex⟩
          · exact .inl hacc
          · exact .inr ⟨.inr hus, hp⟩
        · rintro (hacc | ⟨rfl | hus, hp⟩)
          · exact .inl (.inr hacc)
          · exact .inl (.inl rfl)
          · exact .inr ⟨hus, hp⟩
      · simp only [hhit, Bool.false_eq_true, ↓reduceIte]
        have hno : ¬ ∃ v : Fin r, G (u, v) = true ∧ bipartiteFinEquiv m r (.right v) ∉ cut := by
          intro hex
          apply hhit
          exact (hasUncoveredRightM_ret G cut u (List.finRange r)).mpr
            (let ⟨v, hG, hnv⟩ := hex; ⟨v, List.mem_finRange v, hG, hnv⟩)
        constructor
        · rintro (hacc | ⟨hus, hp⟩)
          · exact .inl hacc
          · exact .inr ⟨.inr hus, hp⟩
        · rintro (hacc | ⟨rfl | hus, hp⟩)
          · exact .inl hacc
          · exact absurd hp (not_or.mpr ⟨hu, hno⟩)
          · exact .inr ⟨hus, hp⟩

private theorem extractCoverLeftLoopM_time_le {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) (us : List (Fin m)) (acc : Finset (Fin m)) :
    (extractCoverLeftLoopM G cut us acc).time ≤ us.length * (r + 1) := by
  induction us generalizing acc with
  | nil => simp [extractCoverLeftLoopM]
  | cons u us' ih =>
    simp only [extractCoverLeftLoopM, TimeM.time_bind, TimeM.time_tick, List.length_cons]
    rw [Nat.add_one_mul]
    split_ifs
    · have hrec := ih (insert u acc)
      omega
    · simp only [TimeM.time_bind]
      have h1 := hasUncoveredRightM_time_le G cut u (List.finRange r)
      simp only [List.length_finRange] at h1
      have hrec :=
        ih (if (hasUncoveredRightM G cut u (List.finRange r)).ret then insert u acc else acc)
      omega

/-- Extract `cutToVertexCover G (Network.cutOfReindex (bipartiteFinEquiv m r) cut)` in at most
`m * (r + 1) + r` charged `TimeM` ticks. -/
@[expose] def extractCoverM {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) : TimeM ℕ (VertexCover (Fin m) (Fin r)) := do
  let left ← extractCoverLeftLoopM G cut (List.finRange m) ∅
  let right ← extractFinsetM fun v : Fin r => decide (bipartiteFinEquiv m r (.right v) ∈ cut)
  pure ⟨left, right⟩

@[simp]
theorem extractCoverM_ret {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) :
    (extractCoverM G cut).ret =
      cutToVertexCover G (Network.cutOfReindex (bipartiteFinEquiv m r) cut) := by
  simp only [extractCoverM, TimeM.ret_bind, extractFinsetM_ret, TimeM.ret_pure]
  unfold cutToVertexCover
  congr 1
  · ext u
    simp [mem_extractCoverLeftLoopM_ret, List.mem_finRange, Network.cutOfReindex]
  · ext v
    simp [Network.cutOfReindex]

theorem extractCoverM_time_le {m r : ℕ} (G : Fin m × Fin r → Bool)
    (cut : Finset (Fin (2 + (m + r)))) :
    (extractCoverM G cut).time ≤ m * (r + 1) + r := by
  simp only [extractCoverM, TimeM.time_bind, extractFinsetM_time, TimeM.time_pure, Nat.add_zero]
  have hL := extractCoverLeftLoopM_time_le G cut (List.finRange m) ∅
  simp only [List.length_finRange] at hL
  omega

/-- Compute a maximum bipartite matching and minimum König vertex cover of
`G : Fin m × Fin r → Bool` in `TimeM ℕ` via `edmondsKarpDenseM`. -/
@[expose] def bipartiteMatchingM {m r : ℕ}
    (G : Fin m × Fin r → Bool) : TimeM ℕ (BipartiteOutput m r) := do
  let out ← edmondsKarpDenseM (bipartiteFinNetwork G)
  let f := out.flow.ofReindex (bipartiteFinEquiv m r)
  let matching ← extractMatchingM f
  let cover ← extractCoverM G out.cut
  pure
    { matching := matching
      cover := cover
      augmentations := out.augmentations }

/-- **Correctness of `bipartiteMatchingM`:** returns a maximum matching `res.matching` and minimum
vertex cover `res.cover` satisfying König strong duality `res.matching.card = res.cover.size`. -/
theorem bipartiteMatchingM_correct {m r : ℕ} (G : Fin m × Fin r → Bool) :
    let res := (bipartiteMatchingM G).ret
    IsMaxMatching G res.matching ∧
      IsMinVertexCover G res.cover ∧
      res.matching.card = res.cover.size := by
  have hst : (bipartiteFinNetwork G).s ≠ (bipartiteFinNetwork G).t := by
    intro h
    exact bipartiteNetwork_s_ne_t G ((bipartiteFinEquiv m r).injective h)
  let out := (edmondsKarpDenseM (bipartiteFinNetwork G)).ret
  obtain ⟨_, hmin_cut, hval, _, _, _⟩ :
      out.flow.IsMaxFlow ∧
        (bipartiteFinNetwork G).IsMinCut out.cut ∧
        out.flow.value = ((bipartiteFinNetwork G).cutCapacity out.cut : ℤ) ∧
        out.cut = out.flow.reachableCut ∧
        out.augmentations ≤ (bipartiteFinNetwork G).symArcs.card * ((2 + (m + r)) / 2) ∧
        out.augmentations ≤ (2 + (m + r)) * (bipartiteFinNetwork G).posArcs.card :=
    edmondsKarpDenseM_correct hst
  let f := out.flow.ofReindex (bipartiteFinEquiv m r)
  let S := Network.cutOfReindex (bipartiteFinEquiv m r) out.cut
  simp only [bipartiteMatchingM, TimeM.ret_bind, extractMatchingM_ret, extractCoverM_ret,
    TimeM.ret_pure]
  change IsMaxMatching G (flowToMatching f) ∧
    IsMinVertexCover G (cutToVertexCover G S) ∧
    (flowToMatching f).card = (cutToVertexCover G S).size
  have hM : IsMatching G (flowToMatching f) := isMatching_flowToMatching f
  have hC : IsVertexCover G (cutToVertexCover G S) := isVertexCover_cutToVertexCover G S
  have hS_cut : (bipartiteNetwork G).IsCut S :=
    Network.isCut_cutOfReindex (bipartiteFinEquiv m r) hmin_cut.1
  have hcap_eq : (bipartiteNetwork G).cutCapacity S = (bipartiteFinNetwork G).cutCapacity out.cut :=
    Network.cutCapacity_cutOfReindex (bipartiteFinEquiv m r) (bipartiteNetwork G) out.cut
  have hf_val : f.value = out.flow.value :=
    Network.Flow.value_ofReindex (bipartiteFinEquiv m r) out.flow
  have hM_card : (flowToMatching f).card = (bipartiteNetwork G).cutCapacity S := by
    have hcoe := card_flowToMatching_coe f
    omega
  have hC_le : (cutToVertexCover G S).size ≤ (bipartiteNetwork G).cutCapacity S :=
    size_cutToVertexCover_le hS_cut
  have hM_le_C : (flowToMatching f).card ≤ (cutToVertexCover G S).size :=
    card_le_size_of_matching_vertexCover hM hC
  have heq : (flowToMatching f).card = (cutToVertexCover G S).size := by omega
  refine ⟨⟨hM, fun M' hM' => ?_⟩, ⟨hC, fun C' hC' => ?_⟩, heq⟩
  · have := card_le_size_of_matching_vertexCover hM' hC
    omega
  · have := card_le_size_of_matching_vertexCover hM hC'
    omega

/-- Polynomial `O((m + r)^5)` `TimeM` step bound for `bipartiteMatchingM`, charging both
`edmondsKarpDenseM` and explicit matching/cover extraction (under unit-cost `Vector`, `Finset`, `ℕ`,
and `G` primitives; see module docstring `## Cost model and limitations`). -/
theorem bipartiteMatchingM_time_le {m r : ℕ} (G : Fin m × Fin r → Bool) :
    let N_v := 2 + (m + r)
    (bipartiteMatchingM G).time ≤ (N_v * N_v * (N_v / 2) + 4) * (N_v * N_v + 5 * N_v) := by
  intro N_v
  simp only [bipartiteMatchingM, TimeM.time_bind, extractMatchingM_time, TimeM.time_pure,
    Nat.add_zero]
  have hek : (edmondsKarpDenseM (bipartiteFinNetwork G)).time ≤
      (N_v * N_v * (N_v / 2) + 2) * (N_v * N_v + 5 * N_v) :=
    edmondsKarpDenseM_time_le (bipartiteFinNetwork G)
  have hcov := extractCoverM_time_le G (edmondsKarpDenseM (bipartiteFinNetwork G)).ret.cut
  have hprod : m * (r + 1) ≤ N_v * N_v :=
    Nat.mul_le_mul (by omega) (by omega)
  have hpost : m * (r + 1) + (extractCoverM G
      (edmondsKarpDenseM (bipartiteFinNetwork G)).ret.cut).time ≤
      2 * (N_v * N_v + 5 * N_v) := by
    have hr : r ≤ N_v := by omega
    omega
  have hsplit : (N_v * N_v * (N_v / 2) + 4) * (N_v * N_v + 5 * N_v) =
      (N_v * N_v * (N_v / 2) + 2) * (N_v * N_v + 5 * N_v) + 2 * (N_v * N_v + 5 * N_v) := by
    rw [show N_v * N_v * (N_v / 2) + 4 = (N_v * N_v * (N_v / 2) + 2) + 2 by omega, Nat.add_mul]
  omega

/-- Decide whether `G : Fin n × Fin n → Bool` has a perfect matching in polynomial `TimeM` steps
(in contrast to the `n!`-permutation enumeration of `Equiv.Perm (Fin n)`). -/
@[expose] def decidePerfectMatchingM {n : ℕ} (G : Fin n × Fin n → Bool) : TimeM ℕ Bool := do
  let res ← bipartiteMatchingM G
  ✓
  pure (decide (res.matching.card = n))

/-- `decidePerfectMatchingM G` returns `true` if and only if
`Cslib.Circuits.BipartiteMatching.HasPerfectMatching G` holds. -/
theorem decidePerfectMatchingM_eq_true_iff {n : ℕ} (G : Fin n × Fin n → Bool) :
    (decidePerfectMatchingM G).ret = true ↔
      Cslib.Circuits.BipartiteMatching.HasPerfectMatching G := by
  simp only [decidePerfectMatchingM, TimeM.ret_bind, TimeM.ret_pure, decide_eq_true_iff]
  rw [hasPerfectMatching_iff_exists_matching_card, Fintype.card_fin]
  obtain ⟨hM_max, _, _⟩ := bipartiteMatchingM_correct G
  constructor
  · intro hcard
    exact ⟨(bipartiteMatchingM G).ret.matching, hM_max.1, hcard⟩
  · rintro ⟨M, hM, hcard⟩
    have hle₁ : n ≤ (bipartiteMatchingM G).ret.matching.card :=
      Nat.le_trans (Nat.le_of_eq hcard.symm) (hM_max.2 M hM)
    have htriv_cov : IsVertexCover G ⟨Finset.univ, ∅⟩ := fun u _ _ => .inl (Finset.mem_univ u)
    have hle₂ : (bipartiteMatchingM G).ret.matching.card ≤ n := by
      have h := card_le_size_of_matching_vertexCover hM_max.1 htriv_cov
      simpa [VertexCover.size] using h
    omega

/-- Polynomial `O(n^5)` `TimeM` step bound for `decidePerfectMatchingM` (under unit-cost `Vector`,
`Finset`, `ℕ`, and `G` primitives; see module docstring `## Cost model and limitations`). -/
theorem decidePerfectMatchingM_time_le {n : ℕ} (G : Fin n × Fin n → Bool) :
    let N_v := 2 + (n + n)
    (decidePerfectMatchingM G).time ≤
      (N_v * N_v * (N_v / 2) + 4) * (N_v * N_v + 5 * N_v) + 1 := by
  dsimp only
  simp only [decidePerfectMatchingM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
    Nat.add_zero]
  have h := bipartiteMatchingM_time_le G
  dsimp only at h
  omega

end ExecutableBipartite

end Cslib.Algorithms.Lean.MaxFlow
