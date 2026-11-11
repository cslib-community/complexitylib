/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.VertexSeparator
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.OddCycleTransversal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Odd cycle transversal by iterative compression

`Cslib.Algorithms.Lean.IterativeCompression.octM G k` decides whether a simple graph `G` on
`Fin n` has an odd cycle transversal (`SimpleGraph.IsOddCycleTransversal`) of at most `k` vertices.
When one exists it returns one, together with a Boolean colouring that is proper on the edges
outside it. This is the iterative compression algorithm of Reed, Smith and Vetta
[ReedSmithVetta2004], with the three-way guess of [Hueffner2009, Section 3] and
[CyganEtAl2015, Section 4.4].

## Algorithm

*Iteration* (`Cslib.Algorithms.Lean.IterativeCompression.loopM`). The vertices are added one at a
time. The state after `i` vertices is an odd cycle transversal `S`, `|S| ≤ k`, of the subgraph
`prefixGraph G i` spanned by the first `i` vertices, with a colouring proper off `S`. Adding
vertex `i` to `S` gives an odd cycle transversal `W` of `prefixGraph G (i + 1)`. If `|W| ≤ k`, it
is the new state. Otherwise `|W| = k + 1` and the compression step either shrinks `W` to at most
`k` vertices or proves that `prefixGraph G (i + 1)` has no odd cycle transversal of at most `k`
vertices. Then neither has `G`, and the algorithm stops.

*Compression* (`Cslib.Algorithms.Lean.IterativeCompression.compressM`). Given `W` and a colouring
`c₀` proper off `W`, enumerate the `3 ^ |W|` guesses `g : Fin n → Option Bool` that are `none`
off `W` (`Cslib.Algorithms.Lean.IterativeCompression.guesses`). A vertex `w ∈ W` with
`g w = none` is deleted, and `g w = some b` colours it `b`. For a guess that is proper on the kept
part of `W`, compute a minimum separator `X` of the keep terminals from the flip terminals in
`G - W` (`Cslib.Algorithms.Lean.MaxFlow.minSeparatorM`). Accept if the deleted part of `W` and `X`
together have at most `k` vertices. Correctness is the compression lemma
`SimpleGraph.exists_isOddCycleTransversal_card_le_iff` and its two directions.

## Cost model

`TimeM ℕ`, with the unit-cost conventions of `Cslib.Algorithms.Lean.MaxFlow.edmondsKarpDenseM`:
`Vector` access and update, `ℕ` arithmetic and adjacency tests cost `O(1)`. The annotations are
trusted:

* a leaf (`Cslib.Algorithms.Lean.IterativeCompression.leafM`) is charged `|W|²` for the
  properness test of the guess, `5 (n + 1) (|W| + 1)` for the terminal tables, the deleted set and
  the new colouring, and the cost of `minSeparatorM`;
* the enumeration of guesses is charged `3 ^ (|W| + 1)`, which bounds the number of nodes of the
  ternary guess tree, each produced by one `Vector` update;
* a step of the iteration is charged `k + 2` for inserting the new vertex, and the initial
  colouring `n`.

The resulting bound (`Cslib.Algorithms.Lean.IterativeCompression.time_octM_le`) is
`O(3 ^ k · n ^ 6)`: `n` steps, `3 ^ (k + 1)` guesses per step and `O(n ^ 5)` per minimum
separator. Reed, Smith and Vetta state `O(4 ^ k · k m n)` for their algorithm. The `3 ^ k`
count, one of three roles for each vertex of `W`, is the analysis of [Hueffner2009, Theorem 1],
which gives `O(3 ^ k · k m n)`; see also [CyganEtAl2015, Section 4.4]. The polynomial factor here
comes from the dense Edmonds–Karp solver. The sharper bounds stop each flow computation after
`k + 1` augmenting paths on adjacency lists; they are not formalized here.

The enumeration charge follows the library's `Vector` convention: an update costs one tick even
when the vector is shared between branches of the guess tree, where a persistent implementation
would copy it.

## Main definitions

* `Cslib.Algorithms.Lean.IterativeCompression.prefixGraph`: the subgraph on the first `m` vertices.
* `Cslib.Algorithms.Lean.IterativeCompression.IsProperOff`: a colouring vector is proper on the
  edges outside a list of vertices.
* `Cslib.Algorithms.Lean.IterativeCompression.findSomeM`: the first successful branch of a list.
* `Cslib.Algorithms.Lean.IterativeCompression.guesses`: the `3 ^ |W|` guesses on `W`.
* `Cslib.Algorithms.Lean.IterativeCompression.leafM`: one guess, solved by a minimum separator.
* `Cslib.Algorithms.Lean.IterativeCompression.compressM`: the compression step.
* `Cslib.Algorithms.Lean.IterativeCompression.stepM`,
  `Cslib.Algorithms.Lean.IterativeCompression.loopM`: one step of the iteration, and the iteration.
* `Cslib.Algorithms.Lean.IterativeCompression.octM`: odd cycle transversal of size at most `k`.
* `Cslib.Algorithms.Lean.IterativeCompression.leafCost`,
  `Cslib.Algorithms.Lean.IterativeCompression.stepCost`: the charged cost of a leaf and of a step.

## Main results

* `Cslib.Algorithms.Lean.IterativeCompression.length_guesses`,
  `Cslib.Algorithms.Lean.IterativeCompression.mem_guesses`: the guesses are exactly the
  `Option Bool` labellings that are `none` off `W`, and there are `3 ^ |W|` of them.
* `Cslib.Algorithms.Lean.IterativeCompression.compressM_sound`,
  `Cslib.Algorithms.Lean.IterativeCompression.compressM_complete`: the compression step.
* `Cslib.Algorithms.Lean.IterativeCompression.octM_sound`,
  `Cslib.Algorithms.Lean.IterativeCompression.octM_isOddCycleTransversal`,
  `Cslib.Algorithms.Lean.IterativeCompression.octM_eq_none`,
  `Cslib.Algorithms.Lean.IterativeCompression.octM_isSome_iff`: correctness.
* `Cslib.Algorithms.Lean.IterativeCompression.time_leafM_le`,
  `Cslib.Algorithms.Lean.IterativeCompression.time_compressM_le`,
  `Cslib.Algorithms.Lean.IterativeCompression.time_octM_le_stepCost`: the running time, step by
  step.
* `Cslib.Algorithms.Lean.IterativeCompression.time_octM_le`: the `O(3 ^ k · n ^ 6)` running time.

## References

* [B. Reed, K. Smith, A. Vetta, *Finding odd cycle transversals*][ReedSmithVetta2004]
* [F. Hüffner, *Algorithm engineering for optimal graph bipartization*][Hueffner2009]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.Lean.IterativeCompression

open SimpleGraph SimpleGraph.OddCycleTransversal Cslib.Algorithms.Lean.MaxFlow

variable {n : ℕ}

/-! ### Prefix subgraphs -/

/-- The subgraph of `G` spanned by the vertices `0, …, m - 1`. The other vertices are isolated. -/
@[expose] def prefixGraph (G : SimpleGraph (Fin n)) (m : ℕ) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u.1 < m ∧ v.1 < m
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

@[simp]
theorem prefixGraph_adj {G : SimpleGraph (Fin n)} {m : ℕ} {u v : Fin n} :
    (prefixGraph G m).Adj u v ↔ G.Adj u v ∧ u.1 < m ∧ v.1 < m :=
  Iff.rfl

instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ) :
    DecidableRel (prefixGraph G m).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u.1 < m ∧ v.1 < m))

theorem prefixGraph_le (G : SimpleGraph (Fin n)) (m : ℕ) : prefixGraph G m ≤ G :=
  fun _ _ h => h.1

theorem prefixGraph_mono (G : SimpleGraph (Fin n)) {m m' : ℕ} (h : m ≤ m') :
    prefixGraph G m ≤ prefixGraph G m' :=
  fun _ _ huv => ⟨huv.1, Nat.lt_of_lt_of_le huv.2.1 h, Nat.lt_of_lt_of_le huv.2.2 h⟩

theorem prefixGraph_of_le (G : SimpleGraph (Fin n)) {m : ℕ} (h : n ≤ m) : prefixGraph G m = G := by
  ext u v
  simp only [prefixGraph_adj, and_iff_left_iff_imp]
  exact fun _ => ⟨by omega, by omega⟩

/-! ### Search in the time monad -/

/-- The first `some` among `f a` for `a ∈ l`, running `f` on the elements in order. -/
@[expose] def findSomeM {α β : Type*} (f : α → TimeM ℕ (Option β)) : List α → TimeM ℕ (Option β)
  | [] => pure none
  | a :: l => do
    let r ← f a
    match r with
    | some b => pure (some b)
    | none => findSomeM f l

@[simp]
theorem ret_findSomeM {α β : Type*} (f : α → TimeM ℕ (Option β)) (l : List α) :
    (findSomeM f l).ret = l.findSome? fun a => (f a).ret := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [findSomeM, TimeM.ret_bind, List.findSome?_cons]
    cases (f a).ret with
    | some b => rfl
    | none => exact ih

theorem time_findSomeM_le {α β : Type*} (f : α → TimeM ℕ (Option β)) (l : List α) {C : ℕ}
    (hf : ∀ a ∈ l, (f a).time ≤ C) : (findSomeM f l).time ≤ l.length * C := by
  induction l with
  | nil => simp only [findSomeM, TimeM.time_pure, List.length_nil, Nat.zero_mul, le_refl]
  | cons a l ih =>
    rw [findSomeM, TimeM.time_bind, List.length_cons, Nat.succ_mul]
    have ha := hf a List.mem_cons_self
    have hl := ih fun b hb => hf b (List.mem_cons_of_mem a hb)
    cases (f a).ret with
    | some b => simp only [TimeM.time_pure]; omega
    | none => simp only; omega

/-! ### Guesses -/

/-- The `3 ^ |ws|` guesses on `ws`: the vectors `g` with `g v = none` off `ws` and `g w ∈
{none, some false, some true}` on `ws`. -/
def guesses : List (Fin n) → List (Vector (Option Bool) n)
  | [] => [Vector.replicate n none]
  | w :: ws => (guesses ws).flatMap fun g =>
      [vset g w none, vset g w (some false), vset g w (some true)]

theorem length_guesses (ws : List (Fin n)) : (guesses ws).length = 3 ^ ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [guesses, List.length_flatMap]
    simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate, ih,
      smul_eq_mul, pow_succ]

theorem mem_guesses {ws : List (Fin n)} {g : Vector (Option Bool) n}
    (hg : ∀ v, v ∉ ws → vget g v = none) : g ∈ guesses ws := by
  induction ws generalizing g with
  | nil =>
    have : g = Vector.replicate n none := by
      refine Vector.ext fun i hi => ?_
      rw [Vector.getElem_replicate]
      exact hg ⟨i, hi⟩ List.not_mem_nil
    exact this ▸ List.mem_singleton_self _
  | cons w ws ih =>
    have hg' : vset g w none ∈ guesses ws := ih fun v hv => by
      by_cases hvw : w = v
      · rw [hvw, vget_vset_self]
      · rw [vget_vset_ne _ _ hvw]
        exact hg v fun h => (List.mem_cons.mp h).elim (fun h' => hvw h'.symm) hv
    have hset : vset (vset g w none) w (vget g w) = g := by
      refine Vector.ext fun i hi => ?_
      simp only [vset, vget, Vector.getElem_set]
      split_ifs with h
      · subst h; rfl
      · rfl
    have hmem : ∀ x : Option Bool, vset (vset g w none) w x ∈
        [vset (vset g w none) w none, vset (vset g w none) w (some false),
          vset (vset g w none) w (some true)] := by
      rintro (_ | _ | _) <;> simp
    rw [guesses, List.mem_flatMap]
    refine ⟨_, hg', ?_⟩
    have := hmem (vget g w)
    rwa [hset] at this

/-! ### Terminal tables -/

/-- The membership table of `W`. -/
def memTable (W : List (Fin n)) : Vector Bool n :=
  Vector.ofFn fun v => decide (v ∈ W)

/-- The keep terminals of a guess `g` relative to the colouring `c₀`: the vertices `v ∉ W` with a
neighbour `w ∈ W` such that `g w = some b` and `b ≠ c₀ v`. -/
def keepTable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : List (Fin n))
    (g : Vector (Option Bool) n) (c₀ : Vector Bool n) : Vector Bool n :=
  Vector.ofFn fun v => decide (v ∉ W ∧
    ∃ w ∈ W, (vget g w).isSome ∧ G.Adj w v ∧ (vget g w).getD false ≠ vget c₀ v)

/-- The flip terminals of a guess `g` relative to the colouring `c₀`: the vertices `v ∉ W` with a
neighbour `w ∈ W` such that `g w = some b` and `b = c₀ v`. -/
def flipTable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : List (Fin n))
    (g : Vector (Option Bool) n) (c₀ : Vector Bool n) : Vector Bool n :=
  Vector.ofFn fun v => decide (v ∉ W ∧
    ∃ w ∈ W, (vget g w).isSome ∧ G.Adj w v ∧ (vget g w).getD false = vget c₀ v)

/-- The colouring produced by a guess `g` and a side labelling: `g` on `W`; off `W`, keep the
colour `c₀ v` where `side v = true` and flip it where `side v = false`. -/
def newColour (W : List (Fin n)) (g : Vector (Option Bool) n) (c₀ side : Vector Bool n) :
    Vector Bool n :=
  Vector.ofFn fun v => if v ∈ W then (vget g v).getD false else (vget c₀ v == vget side v)

private theorem vget_ofFn {α : Type*} (f : Fin n → α) (v : Fin n) : vget (Vector.ofFn f) v = f v :=
  Vector.getElem_ofFn _

@[simp]
theorem vget_memTable (W : List (Fin n)) (v : Fin n) : vget (memTable W) v = decide (v ∈ W) :=
  vget_ofFn _ v

/-- The guess `g` deletes `D` and colours `W \ D` by `σ`. -/
private def Encodes (W : List (Fin n)) (g : Vector (Option Bool) n) (D : Set (Fin n))
    (σ : Fin n → Bool) : Prop :=
  ∀ w ∈ W, (w ∈ D ↔ vget g w = none) ∧ (w ∉ D → vget g w = some (σ w))

private theorem terminal_iff {W : List (Fin n)} {g : Vector (Option Bool) n} {D : Set (Fin n)}
    {σ : Fin n → Bool} (h : Encodes W g D σ) (p : Bool → Prop) {w : Fin n} (hw : w ∈ W) :
    ((vget g w).isSome ∧ p ((vget g w).getD false)) ↔ (w ∉ D ∧ p (σ w)) := by
  by_cases hD : w ∈ D
  · have hg := (h w hw).1.mp hD
    simp only [hg, Option.isSome_none, Bool.false_eq_true, false_and, hD, not_true_eq_false]
  · have hg := (h w hw).2 hD
    simp only [hg, Option.isSome_some, Option.getD_some, true_and, hD, not_false_eq_true]

private theorem keepTable_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {W : List (Fin n)}
    {g : Vector (Option Bool) n} {D : Set (Fin n)} {σ : Fin n → Bool} (h : Encodes W g D σ)
    (c₀ : Vector Bool n) (v : Fin n) :
    vget (keepTable G W g c₀) v = true ↔
      v ∈ keepTerminals G {w | w ∈ W} D σ fun u => vget c₀ u := by
  rw [keepTable, vget_ofFn, decide_eq_true_iff, mem_keepTerminals]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨w, hw, hs, hadj, hne⟩
    obtain ⟨hD, hσ⟩ := (terminal_iff h (fun b => b ≠ vget c₀ v) hw).mp ⟨hs, hne⟩
    exact ⟨w, hw, hD, hadj, hσ⟩
  · rintro ⟨w, hw, hD, hadj, hσ⟩
    obtain ⟨hs, hne⟩ := (terminal_iff h (fun b => b ≠ vget c₀ v) hw).mpr ⟨hD, hσ⟩
    exact ⟨w, hw, hs, hadj, hne⟩

private theorem flipTable_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {W : List (Fin n)}
    {g : Vector (Option Bool) n} {D : Set (Fin n)} {σ : Fin n → Bool} (h : Encodes W g D σ)
    (c₀ : Vector Bool n) (v : Fin n) :
    vget (flipTable G W g c₀) v = true ↔
      v ∈ flipTerminals G {w | w ∈ W} D σ fun u => vget c₀ u := by
  rw [flipTable, vget_ofFn, decide_eq_true_iff, mem_flipTerminals]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨w, hw, hs, hadj, heq⟩
    obtain ⟨hD, hσ⟩ := (terminal_iff h (fun b => b = vget c₀ v) hw).mp ⟨hs, heq⟩
    exact ⟨w, hw, hD, hadj, hσ⟩
  · rintro ⟨w, hw, hD, hadj, hσ⟩
    obtain ⟨hs, heq⟩ := (terminal_iff h (fun b => b = vget c₀ v) hw).mpr ⟨hD, hσ⟩
    exact ⟨w, hw, hs, hadj, heq⟩

/-! ### The compression step -/

/-- A colouring `c` is proper on the edges of `G` with both endpoints outside `S`. -/
abbrev IsProperOff (G : SimpleGraph (Fin n)) (c : Vector Bool n) (S : List (Fin n)) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∉ S → v ∉ S → vget c u ≠ vget c v

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- One leaf of the compression step: the guess `g` on `W`. If `g` is proper on the kept part of
`W`, compute a minimum separator of its keep terminals from its flip terminals in `G - W`, and
accept if the deleted part of `W` and the separator have at most `k` vertices together. -/
@[expose] def leafM (k : ℕ) (W : List (Fin n)) (c₀ : Vector Bool n) (g : Vector (Option Bool) n) :
    TimeM ℕ (Option (List (Fin n) × Vector Bool n)) := do
  TimeM.tick (W.length * W.length)
  if ∀ u ∈ W, ∀ v ∈ W, G.Adj u v → ∀ a b, vget g u = some a → vget g v = some b → a ≠ b then
    TimeM.tick (5 * (n + 1) * (W.length + 1))
    let out ← minSeparatorM G (memTable W) (keepTable G W g c₀) (flipTable G W g c₀)
    let D := W.filter fun w => (vget g w).isNone
    pure (if D.length + out.sep.length ≤ k then some (D ++ out.sep, newColour W g c₀ out.side)
      else none)
  else
    pure none

/-- The charged running time of a leaf on `n` vertices with `|W| = L`. -/
@[expose] def leafCost (n L : ℕ) : ℕ :=
  L * L + 5 * (n + 1) * (L + 1) + minSeparatorCost n

theorem time_leafM_le (k : ℕ) (W : List (Fin n)) (c₀ : Vector Bool n)
    (g : Vector (Option Bool) n) : (leafM G k W c₀ g).time ≤ leafCost n W.length := by
  unfold leafM leafCost
  split_ifs
  · have h := time_minSeparatorM_le (G := G) (Z := memTable W) (A := keepTable G W g c₀)
      (B := flipTable G W g c₀)
    simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    omega
  · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    omega

/-- **Compression step.** Given an odd cycle transversal `W` of `G` with a colouring `c₀` proper
off `W`, look for an odd cycle transversal of at most `k` vertices: run `leafM` on the
`3 ^ |W|` guesses on `W`. -/
@[expose] def compressM (k : ℕ) (W : List (Fin n)) (c₀ : Vector Bool n) :
    TimeM ℕ (Option (List (Fin n) × Vector Bool n)) := do
  TimeM.tick (3 ^ (W.length + 1))
  findSomeM (leafM G k W c₀) (guesses W)

variable {G}

/-- Soundness of a leaf. -/
private theorem leafM_sound {k : ℕ} {W : List (Fin n)} {c₀ : Vector Bool n}
    {g : Vector (Option Bool) n} (hc₀ : IsProperOff G c₀ W) (hW : W.Nodup)
    {S : List (Fin n)} {c : Vector Bool n} (h : (leafM G k W c₀ g).ret = some (S, c)) :
    S.Nodup ∧ S.length ≤ k ∧ IsProperOff G c S := by
  simp only [leafM, TimeM.ret_bind] at h
  split_ifs at h with hprop
  · simp only [TimeM.ret_bind, TimeM.ret_pure] at h
    set out := (minSeparatorM G (memTable W) (keepTable G W g c₀) (flipTable G W g c₀)).ret
      with hout
    set D := W.filter fun w => (vget g w).isNone with hD
    split_ifs at h with hk
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hmemD : ∀ {w}, w ∈ D ↔ w ∈ W ∧ vget g w = none := fun {w} => by
      simp only [hD, List.mem_filter, Option.isNone_iff_eq_none]
    have hsepW : ∀ {v}, v ∈ out.sep → v ∉ W := fun {v} hv => by
      have := minSeparatorM_vget_eq_false_of_mem_sep hv
      rwa [vget_memTable, decide_eq_false_iff_not] at this
    refine ⟨List.nodup_append.mpr ⟨hW.filter _, minSeparatorM_nodup_sep _ _ _ _,
      fun a ha b hb hab => hsepW (hab ▸ hb) (hmemD.mp ha).1⟩,
      (List.length_append).trans_le hk, ?_⟩
    have henc : Encodes W g {w | w ∈ W ∧ vget g w = none} fun w => (vget g w).getD false :=
      fun w hw => ⟨by simp only [Set.mem_ofPred_eq, hw, true_and], fun hD' => by
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp fun h' => hD' ⟨hw, h'⟩
        change vget g w = some ((vget g w).getD false)
        rw [hb, Option.getD_some]⟩
    have hprop' : ∀ ⦃u v⦄, G.Adj u v → u ∈ {w | w ∈ W} → v ∈ {w | w ∈ W} →
        u ∉ {w | w ∈ W ∧ vget g w = none} → v ∉ {w | w ∈ W ∧ vget g w = none} →
        (vget g u).getD false ≠ (vget g v).getD false := fun u v huv hu hv hu' hv' => by
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp fun h' => hu' ⟨hu, h'⟩
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp fun h' => hv' ⟨hv, h'⟩
      rw [ha, hb, Option.getD_some, Option.getD_some]
      exact hprop u hu v hv huv a b ha hb
    have hZ : ∀ {v}, v ∉ ({w | w ∈ W} : Set (Fin n)) → vget (memTable W) v = false :=
      fun {v} hv => by
        have hv' : v ∉ W := hv
        simpa only [vget_memTable, decide_eq_false_iff_not] using hv'
    have key := proper_of_side (X := {v | v ∈ out.sep}) (side := fun v => vget out.side v)
      (c := fun v => vget (newColour W g c₀ out.side) v) (fun u v huv hu hv => hc₀ huv hu hv)
      hprop' (fun u v huv hu hv hus hvs => minSeparatorM_side_eq_of_adj huv (hZ hu) (hZ hv) hus hvs)
      (fun v hv hvs => minSeparatorM_side_eq_true ((keepTable_iff G henc c₀ v).mpr hv)
        (hZ (mem_keepTerminals.mp hv).1) hvs)
      (fun v hv _ => minSeparatorM_side_eq_false ((flipTable_iff G henc c₀ v).mpr hv))
      (fun v hv => by
        simp only [newColour, vget_ofFn, show v ∈ W from hv, ↓reduceIte])
      (fun v hv => by
        have hv' : v ∉ W := hv
        simp only [newColour, vget_ofFn, hv', ↓reduceIte])
    intro u v huv hu hv
    refine key huv ?_ ?_
    · rintro (hu' | hu')
      · exact hu (List.mem_append_left _ (hmemD.mpr hu'))
      · exact hu (List.mem_append_right _ hu')
    · rintro (hv' | hv')
      · exact hv (List.mem_append_left _ (hmemD.mpr hv'))
      · exact hv (List.mem_append_right _ hv')
  · simp only [TimeM.ret_pure, reduceCtorEq] at h

/-- **Compression step, soundness.** An output of `compressM` is an odd cycle transversal of at
most `k` vertices, without repetitions, with a colouring proper off it. -/
theorem compressM_sound {k : ℕ} {W : List (Fin n)} {c₀ : Vector Bool n}
    (hc₀ : IsProperOff G c₀ W) (hW : W.Nodup) {S : List (Fin n)} {c : Vector Bool n}
    (h : (compressM G k W c₀).ret = some (S, c)) :
    S.Nodup ∧ S.length ≤ k ∧ IsProperOff G c S := by
  simp only [compressM, TimeM.ret_bind, ret_findSomeM] at h
  obtain ⟨g, -, hg⟩ := List.exists_of_findSome?_eq_some h
  exact leafM_sound hc₀ hW hg

/-- **Compression step, completeness.** If `compressM` finds nothing, then every odd cycle
transversal of `G` has more than `k` vertices. -/
theorem compressM_complete {k : ℕ} {W : List (Fin n)} {c₀ : Vector Bool n}
    (hc₀ : IsProperOff G c₀ W) (hW : W.Nodup) (h : (compressM G k W c₀).ret = none)
    (T : Finset (Fin n)) (hT : G.IsOddCycleTransversal T) : k < T.card := by
  classical
  by_contra hk
  push Not at hk
  simp only [compressM, TimeM.ret_bind, ret_findSomeM, List.findSome?_eq_none_iff] at h
  obtain ⟨cT, hcT⟩ := isOddCycleTransversal_iff_exists_bool.mp hT
  set g : Vector (Option Bool) n := Vector.ofFn fun v => if v ∈ W ∧ v ∉ T then some (cT v) else none
    with hg
  have hgv : ∀ v, vget g v = if v ∈ W ∧ v ∉ T then some (cT v) else none := fun v => vget_ofFn _ v
  have henc : Encodes W g ((T : Set (Fin n)) ∩ {w | w ∈ W}) cT := fun w hw => by
    rw [hgv]
    by_cases hwT : w ∈ T
    · have hw' : w ∈ (T : Set (Fin n)) ∩ {w | w ∈ W} := ⟨hwT, hw⟩
      simp [hw', hwT]
    · have hw' : w ∉ (T : Set (Fin n)) ∩ {w | w ∈ W} := fun h => hwT h.1
      simp [hw', hwT, hw]
  have hleaf := h g (mem_guesses fun v hv => by rw [hgv]; simp only [hv, false_and, ↓reduceIte])
  have hprop : ∀ u ∈ W, ∀ v ∈ W, G.Adj u v → ∀ a b, vget g u = some a → vget g v = some b →
      a ≠ b := by
    intro u hu v hv huv a b ha hb
    rw [hgv] at ha hb
    split_ifs at ha hb with hu' hv'
    obtain rfl := Option.some.inj ha
    obtain rfl := Option.some.inj hb
    exact hcT huv hu'.2 hv'.2
  simp only [leafM, TimeM.ret_bind] at hleaf
  split_ifs at hleaf
  simp only [TimeM.ret_bind, TimeM.ret_pure] at hleaf
  split_ifs at hleaf with hlen
  apply hlen
  -- The deleted part of `W` is `T ∩ W`.
  have hD : (W.filter fun w => (vget g w).isNone).length ≤ (T ∩ W.toFinset).card := by
    rw [← List.toFinset_card_of_nodup (hW.filter _)]
    refine Finset.card_le_card fun w hw => ?_
    simp only [List.mem_toFinset, List.mem_filter, hgv, Option.isNone_iff_eq_none] at hw
    obtain ⟨hwW, hw⟩ := hw
    split_ifs at hw with h'
    exact Finset.mem_inter.mpr ⟨by tauto, List.mem_toFinset.mpr hwW⟩
  -- The rest of `T` separates the terminals.
  have hsep := isSeparator_of_proper (S := (T : Set (Fin n))) (W := {w | w ∈ W})
    (c₀ := fun v => vget c₀ v) (σ := cT) (fun u v huv hu hv => hc₀ huv hu hv) hcT
    fun _ _ _ => rfl
  have hkeep : {v | vget (keepTable G W g c₀) v = true} =
      keepTerminals G {w | w ∈ W} ((T : Set (Fin n)) ∩ {w | w ∈ W}) cT fun u => vget c₀ u :=
    Set.ext fun v => keepTable_iff G henc c₀ v
  have hflip : {v | vget (flipTable G W g c₀) v = true} =
      flipTerminals G {w | w ∈ W} ((T : Set (Fin n)) ∩ {w | w ∈ W}) cT fun u => vget c₀ u :=
    Set.ext fun v => flipTable_iff G henc c₀ v
  have hZ : {v | vget (memTable W) v = true} ∪ ↑(T \ W.toFinset) = {w | w ∈ W} ∪ (T : Set _) := by
    ext v
    simp only [vget_memTable, decide_eq_true_iff, Set.mem_union, Set.mem_ofPred_eq,
      Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, List.coe_toFinset]
    tauto
  rw [← hkeep, ← hflip, ← hZ] at hsep
  have hX := minSeparatorM_length_sep_le hsep
  have hcard := Finset.card_inter_add_card_sdiff T W.toFinset
  omega

theorem time_compressM_le (k : ℕ) (W : List (Fin n)) (c₀ : Vector Bool n) :
    (compressM G k W c₀).time ≤ 3 ^ (W.length + 1) + 3 ^ W.length * leafCost n W.length := by
  simp only [compressM, TimeM.time_bind, TimeM.time_tick]
  have h := time_findSomeM_le (leafM G k W c₀) (guesses W)
    fun g _ => time_leafM_le G k W c₀ g
  rw [length_guesses] at h
  omega

/-! ### The iteration -/

variable (G)

/-- One step of the iteration: add vertex `i` to the odd cycle transversal `S` of
`prefixGraph G i`, and compress if the result has `k + 1` vertices. -/
@[expose] def stepM (k : ℕ) (i : Fin n) :
    Option (List (Fin n) × Vector Bool n) → TimeM ℕ (Option (List (Fin n) × Vector Bool n))
  | none => pure none
  | some (S, c) => do
    TimeM.tick (k + 2)
    let W := if i ∈ S then S else i :: S
    if W.length ≤ k then pure (some (W, c))
    else compressM (prefixGraph G (i.1 + 1)) k W c

/-- The first `i` steps of the iteration, starting from `∅` and the all-`false` colouring. -/
@[expose] def loopM (k : ℕ) : (i : ℕ) → i ≤ n → TimeM ℕ (Option (List (Fin n) × Vector Bool n))
  | 0, _ => do
    TimeM.tick n
    pure (some ([], Vector.replicate n false))
  | i + 1, h => do
    let r ← loopM k i (by omega)
    stepM G k ⟨i, h⟩ r

/-- **Odd cycle transversal by iterative compression** [ReedSmithVetta2004] [Hueffner2009]: an odd
cycle transversal of `G` with at most `k` vertices and a colouring proper off it, or `none` if
there is no such transversal. -/
@[expose] def octM (k : ℕ) : TimeM ℕ (Option (List (Fin n) × Vector Bool n)) :=
  loopM G k n le_rfl

variable {G}

/-- The loop invariant after `i` steps. -/
private def Inv (G : SimpleGraph (Fin n)) (k i : ℕ) : Option (List (Fin n) × Vector Bool n) → Prop
  | none => ∀ T : Finset (Fin n), (prefixGraph G i).IsOddCycleTransversal T → k < T.card
  | some (S, c) => S.Nodup ∧ S.length ≤ k ∧ IsProperOff (prefixGraph G i) c S

private theorem inv_stepM {k : ℕ} {i : Fin n} {r : Option (List (Fin n) × Vector Bool n)}
    (h : Inv G k i.1 r) : Inv G k (i.1 + 1) (stepM G k i r).ret := by
  rcases r with _ | ⟨S, c⟩
  · exact fun T hT => h T (hT.anti (prefixGraph_mono G (Nat.le_succ _)))
  obtain ⟨hS, hSk, hc⟩ := h
  set W := if i ∈ S then S else i :: S with hWdef
  have hWS : ∀ v, v ∈ W ↔ v = i ∨ v ∈ S := fun v => by
    by_cases hi : i ∈ S
    · simp only [hWdef, hi, ↓reduceIte, iff_or_self]
      exact fun h => h ▸ hi
    · simp only [hWdef, hi, ↓reduceIte, List.mem_cons]
  have hW : W.Nodup := by
    by_cases hi : i ∈ S
    · simpa only [hWdef, hi, ↓reduceIte] using hS
    · simpa only [hWdef, hi, ↓reduceIte] using List.nodup_cons.mpr ⟨hi, hS⟩
  have hcW : IsProperOff (prefixGraph G (i.1 + 1)) c W := by
    intro u v huv hu hv
    rw [hWS, not_or] at hu hv
    refine hc ⟨huv.1, ?_, ?_⟩ hu.2 hv.2
    · have := huv.2.1
      have := Fin.val_ne_of_ne hu.1
      omega
    · have := huv.2.2
      have := Fin.val_ne_of_ne hv.1
      omega
  simp only [stepM, TimeM.ret_bind]
  rw [← hWdef]
  split_ifs with hk
  · exact ⟨hW, hk, hcW⟩
  · rcases hr : (compressM (prefixGraph G (i.1 + 1)) k W c).ret with _ | ⟨S', c'⟩
    · exact compressM_complete hcW hW hr
    · exact compressM_sound hcW hW hr

private theorem inv_loopM (k : ℕ) : ∀ (i : ℕ) (hi : i ≤ n), Inv G k i (loopM G k i hi).ret
  | 0, _ => ⟨List.nodup_nil, Nat.zero_le _, fun _ _ huv => absurd huv.2.1 (Nat.not_lt_zero _)⟩
  | i + 1, hi => by
    simp only [loopM, TimeM.ret_bind]
    exact inv_stepM (i := ⟨i, by omega⟩) (inv_loopM k i (by omega))

/-- **Soundness.** An output `(S, c)` of `octM` has no repetitions, at most `k` vertices, and `c`
is proper on the edges of `G` outside `S`. -/
theorem octM_sound {k : ℕ} {S : List (Fin n)} {c : Vector Bool n}
    (h : (octM G k).ret = some (S, c)) : S.Nodup ∧ S.length ≤ k ∧ IsProperOff G c S := by
  have hinv := inv_loopM (G := G) k n le_rfl
  rw [← octM, h] at hinv
  obtain ⟨hS, hk, hc⟩ := hinv
  rw [prefixGraph_of_le G le_rfl] at hc
  exact ⟨hS, hk, hc⟩

/-- **Soundness.** An output of `octM` is an odd cycle transversal of at most `k` vertices. -/
theorem octM_isOddCycleTransversal {k : ℕ} {S : List (Fin n)} {c : Vector Bool n}
    (h : (octM G k).ret = some (S, c)) :
    G.IsOddCycleTransversal {v | v ∈ S} ∧ S.length ≤ k := by
  obtain ⟨-, hk, hc⟩ := octM_sound h
  exact ⟨isOddCycleTransversal_iff_exists_bool.mpr ⟨fun v => vget c v, hc⟩, hk⟩

/-- **Completeness.** If `octM` returns `none`, every odd cycle transversal of `G` has more than
`k` vertices. -/
theorem octM_eq_none {k : ℕ} (h : (octM G k).ret = none) (T : Finset (Fin n))
    (hT : G.IsOddCycleTransversal T) : k < T.card := by
  have hinv := inv_loopM (G := G) k n le_rfl
  rw [← octM, h] at hinv
  exact hinv T ((prefixGraph_of_le G le_rfl).symm ▸ hT)

/-- **Correctness.** `octM G k` succeeds exactly when `G` has an odd cycle transversal of at most
`k` vertices. -/
theorem octM_isSome_iff {k : ℕ} :
    (octM G k).ret.isSome ↔ ∃ T : Finset (Fin n), G.IsOddCycleTransversal T ∧ T.card ≤ k := by
  classical
  constructor
  · intro h
    obtain ⟨⟨S, c⟩, hSc⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hS, hk⟩ := octM_isOddCycleTransversal hSc
    refine ⟨S.toFinset, ?_, (List.toFinset_card_le S).trans hk⟩
    simpa only [List.coe_toFinset] using hS
  · rintro ⟨T, hT, hk⟩
    rcases hr : (octM G k).ret with _ | _
    · exact absurd (octM_eq_none hr T hT) (Nat.not_lt.mpr hk)
    · rfl

/-! ### Running time -/

private theorem leafCost_mono (n : ℕ) {L L' : ℕ} (h : L ≤ L') : leafCost n L ≤ leafCost n L' := by
  unfold leafCost
  gcongr

/-- The charged cost of one step of the iteration. -/
@[expose] def stepCost (n k : ℕ) : ℕ :=
  k + 2 + 3 ^ (k + 2) + 3 ^ (k + 1) * leafCost n n

private theorem time_stepM_le {k : ℕ} {i : Fin n} {r : Option (List (Fin n) × Vector Bool n)}
    (h : Inv G k i.1 r) : (stepM G k i r).time ≤ stepCost n k := by
  rcases r with _ | ⟨S, c⟩
  · exact Nat.zero_le _
  obtain ⟨hS, hSk, -⟩ := h
  set W := if i ∈ S then S else i :: S with hWdef
  have hWlen : W.length ≤ S.length + 1 := by
    by_cases hi : i ∈ S
    · simp only [hWdef, hi, ↓reduceIte]; omega
    · simp only [hWdef, hi, ↓reduceIte, List.length_cons, le_refl]
  have hW : W.Nodup := by
    by_cases hi : i ∈ S
    · simpa only [hWdef, hi, ↓reduceIte] using hS
    · simpa only [hWdef, hi, ↓reduceIte] using List.nodup_cons.mpr ⟨hi, hS⟩
  have hWn : W.length ≤ n := by simpa only [Fintype.card_fin] using hW.length_le_card
  simp only [stepM, TimeM.time_bind, TimeM.time_tick]
  rw [← hWdef]
  unfold stepCost
  split_ifs with hk
  · simp only [TimeM.time_pure]
    have h0 : 0 ≤ 3 ^ (k + 2) := Nat.zero_le _
    omega
  · have hc := time_compressM_le (G := prefixGraph G (i.1 + 1)) k W c
    have h1 : 3 ^ (W.length + 1) ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ W.length * leafCost n W.length ≤ 3 ^ (k + 1) * leafCost n n :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (leafCost_mono n hWn)
    omega

private theorem time_loopM_le (k : ℕ) :
    ∀ (i : ℕ) (hi : i ≤ n), (loopM G k i hi).time ≤ n + i * stepCost n k
  | 0, _ => by simp only [loopM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]; omega
  | i + 1, hi => by
    simp only [loopM, TimeM.time_bind]
    have h1 := time_loopM_le k i (by omega)
    have h2 := time_stepM_le (G := G) (i := ⟨i, by omega⟩) (inv_loopM k i (by omega))
    rw [Nat.succ_mul]
    omega

/-- **Running time.** `octM` takes at most `n + n · stepCost n k` ticks. -/
theorem time_octM_le_stepCost (k : ℕ) : (octM G k).time ≤ n + n * stepCost n k :=
  time_loopM_le k n le_rfl

private theorem leafCost_le (n : ℕ) : leafCost n n ≤ 100 * (n + 1) ^ 5 := by
  unfold leafCost minSeparatorCost
  have hm : (n + n + 2) / 2 = n + 1 := by omega
  have e : n + n + 2 = 2 * (n + 1) := by omega
  rw [hm, e]
  have h1 : 1 ≤ n + 1 := Nat.succ_pos n
  have h2 : n + 1 ≤ (n + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
  have h4 : (n + 1) ^ 4 ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
  have h6 : 0 ≤ (n + 1) ^ 5 := Nat.zero_le _
  linarith

/-- **Running time, closed form.** `octM G k` takes `O(3 ^ k · n ^ 6)` steps: at most
`312 · 3 ^ k · (n + 1) ^ 6`. -/
theorem time_octM_le (k : ℕ) : (octM G k).time ≤ 312 * 3 ^ k * (n + 1) ^ 6 := by
  refine (time_octM_le_stepCost k).trans ?_
  unfold stepCost
  have hL := leafCost_le n
  have hx1 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
  have hk : k + 2 ≤ 2 * 3 ^ k := by
    have := Nat.lt_pow_self (n := k) (a := 3) (by norm_num)
    omega
  have hN : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
  have h9 : 3 ^ (k + 2) = 9 * 3 ^ k := by ring
  have h3 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
  rw [h9, h3]
  have a : n ≤ n * 3 ^ k := Nat.le_mul_of_pos_right n hx1
  have b : n * (k + 2) ≤ n * (2 * 3 ^ k) := Nat.mul_le_mul_left n hk
  have c : n * (3 * 3 ^ k * leafCost n n) ≤ n * (3 * 3 ^ k * (100 * (n + 1) ^ 5)) :=
    Nat.mul_le_mul_left n (Nat.mul_le_mul_left _ hL)
  have d : n * 3 ^ k ≤ 3 ^ k * (n + 1) ^ 6 := by
    rw [Nat.mul_comm (3 ^ k)]
    exact Nat.mul_le_mul_right _ ((Nat.le_succ n).trans hN)
  have e : n * 3 ^ k * (n + 1) ^ 5 ≤ 3 ^ k * (n + 1) ^ 6 := by
    calc n * 3 ^ k * (n + 1) ^ 5 ≤ (n + 1) * 3 ^ k * (n + 1) ^ 5 := by gcongr; omega
      _ = 3 ^ k * (n + 1) ^ 6 := by ring
  linarith

end Cslib.Algorithms.Lean.IterativeCompression
