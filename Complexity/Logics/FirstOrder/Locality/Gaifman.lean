/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.ModelTheory.Graph
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Gaifman graphs and isomorphisms of neighborhoods

The **Gaifman graph** of a structure `M` (`gaifmanGraph L M`) joins two distinct elements when they
occur together in some tuple of some relation. Its distance (`SimpleGraph.edist`, valued in `ℕ∞`)
is the distance used by locality arguments in finite model theory. The **ball** of radius `r`
around a tuple `a` (`ball L a r`) is the set of elements at distance at most `r` from some entry of
`a`.

`IsNbhdIso L r a b h` says that `h : M → N` is an isomorphism between the radius-`r` neighborhoods
of `a` in `M` and of `b` in `N`, that is, between the substructures induced on the two balls with
the tuples as distinguished constants. `NbhdIso L r a b` says that such an `h` exists. These are
the objects `N_r(a) ≅ N_r(b)` of [Libkin, §4.1][Libkin2004]. The neighborhood isomorphism is
encoded by a function on all of `M` that is a bijection between the balls (`Set.BijOn`), so that
it composes, inverts and restricts without subtype bookkeeping.

The combinatorial facts of [Libkin, Lemma 4.8][Libkin2004] are proved here:

* `IsNbhdIso.mono`: a neighborhood isomorphism of radius `r` is one of every radius `d ≤ r`;
* `IsNbhdIso.restrict`: a neighborhood isomorphism of radius `r` restricts to the radius-`d`
  neighborhood of any tuple inside the radius-`l` ball, when `l + d ≤ r`;
* `IsNbhdIso.snoc`: a radius-`r` neighborhood isomorphism of the tuples and one of a single point
  lying at distance more than `2r + 1` from the tuple (on both sides) combine into one of the
  tuples with that point added;

together with `IsNbhdIso.symm`, `IsNbhdIso.trans` and `IsNbhdIso.refl`.

Function symbols play no role: the Gaifman graph and the neighborhood isomorphisms only see the
relations and equality.

## Main definitions

* `Cslib.Logic.FO.Locality.gaifmanGraph`: the Gaifman graph of a structure.
* `Cslib.Logic.FO.Locality.ball`: the ball of radius `r` around a tuple.
* `Cslib.Logic.FO.Locality.IsNbhdIso`, `Cslib.Logic.FO.Locality.NbhdIso`: isomorphisms of
  neighborhoods.

## Main results

* `Cslib.Logic.FO.Locality.gaifmanGraph_structure`: the Gaifman graph of a simple graph, viewed as
  a structure of Mathlib's language of graphs, is the graph itself.
* `Cslib.Logic.FO.Locality.IsNbhdIso.mono`, `Cslib.Logic.FO.Locality.IsNbhdIso.restrict`,
  `Cslib.Logic.FO.Locality.IsNbhdIso.snoc`: [Libkin, Lemma 4.8][Libkin2004].

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], §4.1 (Gaifman graphs, balls and
  neighborhoods, Definitions 4.1 and 4.2) and §4.2 (Lemma 4.8, whose proof the book leaves as an
  exercise).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Locality

universe u v w w' w''

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {P : Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P]

/-! ### The Gaifman graph -/

variable (L M) in
/-- The Gaifman graph of an `L`-structure: distinct elements are adjacent when they occur together
in a tuple of some relation ([Libkin, Definition 4.1][Libkin2004]). -/
def gaifmanGraph : SimpleGraph M where
  Adj x y := x ≠ y ∧ ∃ (l : ℕ) (R : L.Relations l) (t : Fin l → M),
    RelMap R t ∧ (∃ i, t i = x) ∧ ∃ j, t j = y
  symm := ⟨fun _ _ ⟨hne, l, R, t, hR, hi, hj⟩ => ⟨hne.symm, l, R, t, hR, hj, hi⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem gaifmanGraph_adj {x y : M} :
    (gaifmanGraph L M).Adj x y ↔ x ≠ y ∧ ∃ (l : ℕ) (R : L.Relations l) (t : Fin l → M),
      RelMap R t ∧ (∃ i, t i = x) ∧ ∃ j, t j = y := Iff.rfl

/-- Two entries of a tuple in a relation are equal or adjacent in the Gaifman graph. -/
theorem edist_le_one_of_relMap {l : ℕ} {R : L.Relations l} {t : Fin l → M} (hR : RelMap R t)
    (i j : Fin l) : (gaifmanGraph L M).edist (t i) (t j) ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  by_cases h : t i = t j
  · exact .inr h
  · exact .inl ⟨h, l, R, t, hR, ⟨i, rfl⟩, j, rfl⟩

/-- The Gaifman graph of a simple graph, viewed as a structure of Mathlib's language of graphs,
is the graph itself. -/
theorem gaifmanGraph_structure {V : Type*} (G : SimpleGraph V) :
    @gaifmanGraph Language.graph V G.structure = G := by
  let := G.structure
  ext x y
  rw [gaifmanGraph_adj]
  constructor
  · rintro ⟨hne, l, R, t, hR, ⟨i, rfl⟩, j, rfl⟩
    cases R
    have h01 : ∀ p : Fin 2, p = 0 ∨ p = 1 := fun p => by fin_cases p <;> simp
    change G.Adj (t 0) (t 1) at hR
    rcases h01 i with rfl | rfl <;> rcases h01 j with rfl | rfl
    · exact absurd rfl hne
    · exact hR
    · exact hR.symm
    · exact absurd rfl hne
  · intro h
    exact ⟨h.ne, 2, .adj, ![x, y], h, ⟨0, rfl⟩, 1, rfl⟩

/-! ### Distances -/

section Distance

variable {V : Type*} {G : SimpleGraph V}

private theorem edist_le_one_of_adj {x y : V} (h : G.Adj x y) : G.edist x y ≤ 1 :=
  SimpleGraph.edist_le_one_iff_adj_or_eq.2 (.inl h)

/-- The first step of a path of length at most `s + 1`. -/
private theorem exists_adj_of_edist_le_succ {x y : V} {s : ℕ} (h : G.edist x y ≤ (s + 1 : ℕ)) :
    x = y ∨ ∃ z, G.Adj x z ∧ G.edist z y ≤ s := by
  have hne : G.edist x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  cases p with
  | nil => exact .inl rfl
  | @cons _ z _ hxz q =>
    refine .inr ⟨z, hxz, ?_⟩
    rw [← hp, SimpleGraph.Walk.length_cons, Nat.cast_le] at h
    exact (SimpleGraph.edist_le q).trans (by exact_mod_cast (by omega : q.length ≤ s))

/-- Points within distance `r` of two points at distance more than `2r + 1` are neither equal nor
adjacent. -/
private theorem one_lt_edist_of_far {a c y z : V} {r : ℕ}
    (hac : ((2 * r + 1 : ℕ) : ℕ∞) < G.edist a c) (hy : G.edist a y ≤ r)
    (hz : G.edist c z ≤ r) : 1 < G.edist y z := by
  by_contra hyz
  rw [not_lt] at hyz
  rw [SimpleGraph.edist_comm] at hz
  have : G.edist a c ≤ ((2 * r + 1 : ℕ) : ℕ∞) :=
    calc G.edist a c ≤ G.edist a z + G.edist z c := SimpleGraph.edist_triangle
      _ ≤ (G.edist a y + G.edist y z) + G.edist z c :=
        add_le_add SimpleGraph.edist_triangle le_rfl
      _ ≤ (r + 1) + r := add_le_add (add_le_add hy hyz) hz
      _ = ((2 * r + 1 : ℕ) : ℕ∞) := by push_cast; ring
  exact absurd hac (not_lt.2 this)

end Distance

/-! ### Balls -/

variable (L) in
/-- The ball of radius `r` around a tuple `a`: the elements at distance at most `r` from some entry
of `a` in the Gaifman graph ([Libkin, Definition 4.2][Libkin2004]). -/
def ball {k : ℕ} (a : Fin k → M) (r : ℕ) : Set M :=
  {x | ∃ i, (gaifmanGraph L M).edist (a i) x ≤ r}

theorem mem_ball {k : ℕ} {a : Fin k → M} {r : ℕ} {x : M} :
    x ∈ ball L a r ↔ ∃ i, (gaifmanGraph L M).edist (a i) x ≤ r := Iff.rfl

theorem ball_mono {k : ℕ} {a : Fin k → M} {r s : ℕ} (h : r ≤ s) : ball L a r ⊆ ball L a s :=
  fun _ ⟨i, hi⟩ => ⟨i, hi.trans (by exact_mod_cast h)⟩

theorem mem_ball_self {k : ℕ} (a : Fin k → M) (r : ℕ) (i : Fin k) : a i ∈ ball L a r :=
  ⟨i, by simp⟩

theorem mem_ball_of_edist_le {k : ℕ} {a : Fin k → M} {l s : ℕ} {x y : M} (hx : x ∈ ball L a l)
    (hy : (gaifmanGraph L M).edist x y ≤ s) : y ∈ ball L a (l + s) := by
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, SimpleGraph.edist_triangle.trans (by push_cast; exact add_le_add hi hy)⟩

/-- The radius-`d` ball around a tuple inside the radius-`l` ball around `a` lies in the
radius-`(l + d)` ball around `a`. -/
theorem ball_subset_ball {k m : ℕ} {a : Fin k → M} {x : Fin m → M} {l d : ℕ}
    (hx : ∀ i, x i ∈ ball L a l) : ball L x d ⊆ ball L a (l + d) :=
  fun _ ⟨i, hi⟩ => mem_ball_of_edist_le (hx i) hi

theorem mem_ball_const {r : ℕ} {c x : M} :
    x ∈ ball L (fun _ : Fin 1 => c) r ↔ (gaifmanGraph L M).edist c x ≤ r :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

theorem mem_ball_snoc {k r : ℕ} {a : Fin k → M} {c x : M} :
    x ∈ ball L (Fin.snoc a c : Fin (k + 1) → M) r ↔
      x ∈ ball L a r ∨ x ∈ ball L (fun _ : Fin 1 => c) r := by
  rw [mem_ball_const]
  simp only [mem_ball, Fin.exists_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]

theorem ball_snoc {k r : ℕ} (a : Fin k → M) (c : M) :
    ball L (Fin.snoc a c : Fin (k + 1) → M) r = ball L a r ∪ ball L (fun _ : Fin 1 => c) r :=
  Set.ext fun _ => mem_ball_snoc

/-! ### Isomorphisms of neighborhoods -/

variable (L) in
/-- `h` is an isomorphism between the radius-`r` neighborhoods of `a` in `M` and of `b` in `N`
(Libkin's `N_r(a) ≅ N_r(b)`): a bijection between the balls that sends `a` to `b` and preserves
and reflects every relation on tuples from the ball. -/
structure IsNbhdIso {k : ℕ} (r : ℕ) (a : Fin k → M) (b : Fin k → N) (h : M → N) : Prop where
  /-- `h` is a bijection between the balls. -/
  bijOn : Set.BijOn h (ball L a r) (ball L b r)
  /-- `h` sends the tuple `a` to the tuple `b`. -/
  map_tuple : ∀ i, h (a i) = b i
  /-- `h` preserves and reflects the relations on the ball. -/
  relMap_iff : ∀ {l : ℕ} (R : L.Relations l) (t : Fin l → M), (∀ i, t i ∈ ball L a r) →
    (RelMap R (h ∘ t) ↔ RelMap R t)

variable (L) in
/-- The radius-`r` neighborhoods of `a` in `M` and of `b` in `N` are isomorphic.

The isomorphism is encoded by a function `M → N`. So for the empty tuple (`k = 0`, where both
balls are empty) `NbhdIso L r a b` holds exactly when there is some function `M → N` and the
nullary relations agree. In particular, if `M` is empty, `N` is not, and the nullary relations
agree, then `NbhdIso L r a b` holds but `NbhdIso L r b a` does not. The main results avoid this
asymmetry: they use tuples of positive length, a single structure, or a bijection `M ≃ N`. -/
def NbhdIso {k : ℕ} (r : ℕ) (a : Fin k → M) (b : Fin k → N) : Prop :=
  ∃ h : M → N, IsNbhdIso L r a b h

theorem nbhdIso_iff {k r : ℕ} {a : Fin k → M} {b : Fin k → N} :
    NbhdIso L r a b ↔ ∃ h : M → N, IsNbhdIso L r a b h := Iff.rfl

namespace IsNbhdIso

variable {k : ℕ} {r : ℕ} {a : Fin k → M} {b : Fin k → N} {h : M → N}

theorem nbhdIso (H : IsNbhdIso L r a b h) : NbhdIso L r a b := ⟨h, H⟩

/-- Gaifman adjacency from a point of the radius-`l` ball is preserved, when `l + 1 ≤ r`. -/
theorem adj {x z : M} (H : IsNbhdIso L r a b h) {l : ℕ} (hlr : l + 1 ≤ r)
    (hx : x ∈ ball L a l) (hxz : (gaifmanGraph L M).Adj x z) :
    (gaifmanGraph L N).Adj (h x) (h z) := by
  obtain ⟨hne, m, R, t, hR, ⟨i, rfl⟩, j, rfl⟩ := hxz
  have ht : ∀ p, t p ∈ ball L a r := fun p =>
    ball_mono hlr (mem_ball_of_edist_le hx (edist_le_one_of_relMap hR i p))
  exact ⟨fun heq => hne (H.bijOn.injOn (ht i) (ht j) heq), m, R, h ∘ t,
    (H.relMap_iff R t ht).2 hR, ⟨i, rfl⟩, j, rfl⟩

/-- Distances from points of the radius-`l` ball are not increased up to `r - l`. -/
theorem edist_le (H : IsNbhdIso L r a b h) :
    ∀ {s l : ℕ} {x y : M}, l + s ≤ r → x ∈ ball L a l → (gaifmanGraph L M).edist x y ≤ s →
      (gaifmanGraph L N).edist (h x) (h y) ≤ s
  | 0, _, x, y, _, _, hxy => by
    have : x = y := SimpleGraph.edist_eq_zero_iff.1 (nonpos_iff_eq_zero.1 (by exact_mod_cast hxy))
    subst this
    simp
  | s + 1, l, x, y, hls, hx, hxy => by
    rcases exists_adj_of_edist_le_succ hxy with rfl | ⟨z, hxz, hzy⟩
    · simp
    · have hz : z ∈ ball L a (l + 1) :=
        mem_ball_of_edist_le hx (by exact_mod_cast edist_le_one_of_adj hxz)
      have h1 := H.adj (by omega) hx hxz
      have h2 := H.edist_le (s := s) (l := l + 1) (by omega) hz hzy
      calc (gaifmanGraph L N).edist (h x) (h y)
          ≤ (gaifmanGraph L N).edist (h x) (h z) + (gaifmanGraph L N).edist (h z) (h y) :=
            SimpleGraph.edist_triangle
        _ ≤ 1 + s := add_le_add (edist_le_one_of_adj h1) h2
        _ = ((s + 1 : ℕ) : ℕ∞) := by push_cast; ring

theorem mapsTo_ball (H : IsNbhdIso L r a b h) {l : ℕ} (hl : l ≤ r) :
    Set.MapsTo h (ball L a l) (ball L b l) := fun _ ⟨i, hi⟩ =>
  ⟨i, H.map_tuple i ▸ H.edist_le (l := 0) (by omega) (mem_ball_self a 0 i) hi⟩

/-- The inverse of a neighborhood isomorphism. `M` must be nonempty to define it. -/
theorem symm [Nonempty M] (H : IsNbhdIso L r a b h) :
    IsNbhdIso L r b a (Function.invFunOn h (ball L a r)) := by
  have hinv := H.bijOn.invOn_invFunOn
  refine ⟨H.bijOn.symm hinv.symm, fun i => ?_, fun R t ht => ?_⟩
  · rw [← H.map_tuple i]
    exact hinv.1 (mem_ball_self a r i)
  · have hmaps := (H.bijOn.symm hinv.symm).mapsTo
    rw [← H.relMap_iff R (Function.invFunOn h (ball L a r) ∘ t) (fun i => hmaps (ht i))]
    have : h ∘ (Function.invFunOn h (ball L a r) ∘ t) = t := funext fun i => hinv.2 (ht i)
    rw [this]

theorem refl (r : ℕ) (a : Fin k → M) : IsNbhdIso L r a a id :=
  ⟨Set.bijOn_id _, fun _ => rfl, fun _ _ _ => Iff.rfl⟩

theorem trans {c : Fin k → P} {h' : N → P} (H : IsNbhdIso L r a b h)
    (H' : IsNbhdIso L r b c h') : IsNbhdIso L r a c (h' ∘ h) := by
  refine ⟨H'.bijOn.comp H.bijOn, fun i => by simp [H.map_tuple, H'.map_tuple], fun R t ht => ?_⟩
  rw [Function.comp_assoc, H'.relMap_iff R (h ∘ t) (fun i => H.bijOn.mapsTo (ht i)),
    H.relMap_iff R t ht]

/-- Restriction to the neighborhood of a tuple near `a` ([Libkin, Lemma 4.8][Libkin2004], second
item): if `x` lies in the radius-`l` ball around `a` and `l + d ≤ r`, then `h` is an isomorphism
of the radius-`d` neighborhoods of `x` and of `h ∘ x`. With `x = a` and `l = 0` this is the first
item, restriction to a smaller radius. -/
theorem restrict {m : ℕ} {x : Fin m → M} {l d : ℕ} (H : IsNbhdIso L r a b h)
    (hx : ∀ i, x i ∈ ball L a l) (hld : l + d ≤ r) : IsNbhdIso L d x (h ∘ x) h := by
  have hsub : ball L x d ⊆ ball L a r := (ball_subset_ball hx).trans (ball_mono hld)
  refine ⟨⟨?_, H.bijOn.injOn.mono hsub, ?_⟩, fun _ => rfl, fun R t ht => H.relMap_iff R t
    (fun i => hsub (ht i))⟩
  · rintro y ⟨i, hi⟩
    exact ⟨i, H.edist_le (by omega) (hx i) hi⟩
  · rintro y' ⟨i, hi⟩
    have : Nonempty M := ⟨x i⟩
    have hxi : h (x i) ∈ ball L b l := H.mapsTo_ball (by omega) (hx i)
    refine ⟨Function.invFunOn h (ball L a r) y', ⟨i, ?_⟩,
      H.bijOn.invOn_invFunOn.2 (ball_mono hld (mem_ball_of_edist_le hxi hi))⟩
    have := H.symm.edist_le (by omega) hxi hi
    rwa [H.bijOn.invOn_invFunOn.1 (ball_mono (by omega) (hx i))] at this

/-- Restriction to a smaller radius ([Libkin, Lemma 4.8][Libkin2004], first item). -/
theorem mono {d : ℕ} (H : IsNbhdIso L r a b h) (hd : d ≤ r) : IsNbhdIso L d a b h := by
  have := H.restrict (x := a) (l := 0) (d := d) (fun i => mem_ball_self a 0 i) (by omega)
  rwa [show h ∘ a = b from funext H.map_tuple] at this

open Classical in
/-- Neighborhoods of far-apart tuples combine ([Libkin, Lemma 4.8][Libkin2004], third item, for a
single added point): if the radius-`r` neighborhoods of `a` and `b`, and of `c` and `c'`, are
isomorphic, and `c` and `c'` are at distance more than `2r + 1` from `a` and `b`, then the
radius-`r` neighborhoods of `a` with `c` added and of `b` with `c'` added are isomorphic. -/
theorem snoc {h₁ h₂ : M → N} {c : M} {c' : N} (H₁ : IsNbhdIso L r a b h₁)
    (H₂ : IsNbhdIso L r (fun _ : Fin 1 => c) (fun _ : Fin 1 => c') h₂)
    (hc : ∀ i, ((2 * r + 1 : ℕ) : ℕ∞) < (gaifmanGraph L M).edist (a i) c)
    (hc' : ∀ i, ((2 * r + 1 : ℕ) : ℕ∞) < (gaifmanGraph L N).edist (b i) c') :
    NbhdIso L r (Fin.snoc a c : Fin (k + 1) → M) (Fin.snoc b c' : Fin (k + 1) → N) := by
  set S := ball L a r
  set S' := ball L (fun _ : Fin 1 => c) r
  set T := ball L b r
  set T' := ball L (fun _ : Fin 1 => c') r
  have farM : ∀ y ∈ S, ∀ z ∈ S', 1 < (gaifmanGraph L M).edist y z := by
    rintro y ⟨i, hy⟩ z hz
    exact one_lt_edist_of_far (hc i) hy (mem_ball_const.1 hz)
  have farN : ∀ y ∈ T, ∀ z ∈ T', 1 < (gaifmanGraph L N).edist y z := by
    rintro y ⟨i, hy⟩ z hz
    exact one_lt_edist_of_far (hc' i) hy (mem_ball_const.1 hz)
  have neM : ∀ y ∈ S, ∀ z ∈ S', y ≠ z := fun y hy z hz hyz => by
    have := farM y hy z hz
    rw [hyz, SimpleGraph.edist_self] at this
    exact absurd this (by simp)
  have neN : ∀ y ∈ T, ∀ z ∈ T', y ≠ z := fun y hy z hz hyz => by
    have := farN y hy z hz
    rw [hyz, SimpleGraph.edist_self] at this
    exact absurd this (by simp)
  let H : M → N := fun x => if x ∈ S then h₁ x else h₂ x
  have HS : Set.EqOn H h₁ S := fun x hx => by simp [H, hx]
  have HS' : Set.EqOn H h₂ S' := fun x hx => by
    simp [H, show x ∉ S from fun h => neM x h x hx rfl]
  have hb1 : Set.BijOn H S T := H₁.bijOn.congr HS.symm
  have hb2 : Set.BijOn H S' T' := H₂.bijOn.congr HS'.symm
  refine ⟨H, ⟨?_, fun i => ?_, fun R t ht => ?_⟩⟩
  · rw [ball_snoc, ball_snoc]
    refine hb1.union hb2 ?_
    rw [Set.injOn_union (Set.disjoint_left.2 fun x hx hx' => neM x hx x hx' rfl)]
    exact ⟨hb1.injOn, hb2.injOn, fun x hx y hy hxy =>
      neN _ (hb1.mapsTo hx) _ (hb2.mapsTo hy) hxy⟩
  · induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      rw [HS' (mem_ball_self _ r 0)]
      exact H₂.map_tuple 0
    | cast i =>
      simp only [Fin.snoc_castSucc]
      rw [HS (mem_ball_self _ r i)]
      exact H₁.map_tuple i
  · have ht' : ∀ i, t i ∈ S ∨ t i ∈ S' := fun i => mem_ball_snoc.1 (ht i)
    by_cases hS : ∀ i, t i ∈ S
    · have : H ∘ t = h₁ ∘ t := funext fun i => HS (hS i)
      rw [this]
      exact H₁.relMap_iff R t hS
    by_cases hS' : ∀ i, t i ∈ S'
    · have : H ∘ t = h₂ ∘ t := funext fun i => HS' (hS' i)
      rw [this]
      exact H₂.relMap_iff R t hS'
    simp only [not_forall] at hS hS'
    obtain ⟨i, hi⟩ := hS
    obtain ⟨j, hj⟩ := hS'
    have hi' : t i ∈ S' := (ht' i).resolve_left hi
    have hj' : t j ∈ S := (ht' j).resolve_right hj
    have hHi : H (t i) ∈ T' := by rw [HS' hi']; exact H₂.bijOn.mapsTo hi'
    have hHj : H (t j) ∈ T := by rw [HS hj']; exact H₁.bijOn.mapsTo hj'
    constructor
    · intro hR
      exact absurd (edist_le_one_of_relMap hR j i) (not_le.2 (farN _ hHj _ hHi))
    · intro hR
      exact absurd (edist_le_one_of_relMap hR j i) (not_le.2 (farM _ hj' _ hi'))

end IsNbhdIso

namespace NbhdIso

variable {k r : ℕ}

theorem refl (r : ℕ) (a : Fin k → M) : NbhdIso L r a a := ⟨id, IsNbhdIso.refl r a⟩

theorem symm [Nonempty M] {a : Fin k → M} {b : Fin k → N} (H : NbhdIso L r a b) :
    NbhdIso L r b a :=
  let ⟨_, H⟩ := H; ⟨_, H.symm⟩

theorem trans {a : Fin k → M} {b : Fin k → N} {c : Fin k → P} (H : NbhdIso L r a b)
    (H' : NbhdIso L r b c) : NbhdIso L r a c :=
  let ⟨_, H⟩ := H; let ⟨_, H'⟩ := H'; ⟨_, H.trans H'⟩

theorem mono {d : ℕ} {a : Fin k → M} {b : Fin k → N} (H : NbhdIso L r a b) (hd : d ≤ r) :
    NbhdIso L d a b :=
  let ⟨_, H⟩ := H; ⟨_, H.mono hd⟩

end NbhdIso

end Cslib.Logic.FO.Locality
