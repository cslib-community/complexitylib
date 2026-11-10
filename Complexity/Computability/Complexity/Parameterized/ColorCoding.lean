/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized
public import Complexity.Computability.Complexity.Problems.Graph.VertexColors
public import Complexity.Computability.Complexity.Problems.LongPath
import Complexity.Computability.Complexity.FineGrained.Padding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Foundations.Data.Nat.Bitwise.Carry
import Mathlib.Data.List.GetD

/-!
# Color coding: colorful paths

A path is *colorful* under a coloring of the vertices when its vertices have pairwise distinct
colors. Alon, Yuster and Zwick decide whether a graph with `k` colors has a colorful path on `k`
vertices by dynamic programming over the sets of colors [AlonYusterZwick1995, Lemma 3.1]
[CyganEtAl2015, Lemma 5.5]: for each set `S` of colors, list the vertices `v` at which some
colorful path with color set exactly `S` ends. Such a path is the single vertex `v` when
`S = {χ v}`, and otherwise extends a colorful path with color set `S \ {χ v}` ending at a neighbor
of `v`. Color coding then finds a path on `k` vertices with probability at least `e ^ (-k)` by
running this procedure on a uniformly random coloring.

`Cslib.Complexity.ColorfulPath` is the problem: instances are a graph, a list of colors parallel to
its vertex list (`Cslib.Complexity.colorOf`) and a target `k`, and the question is whether there is
a path on `k` vertices with pairwise distinct colors less than `k`. The color sets are bit masks
`m < 2 ^ k`, and the table (`Cslib.Complexity.ColorCoding.table`) has one entry per mask in
increasing order, so that the entry at `m - 2 ^ χ v` precedes that at `m`.

*Resources.* The table on `N` masks is polynomial-time with `N` in unary
(`Cslib.Complexity.ColorCoding.computableInPolyTime_table`), so the decider runs in polynomial time
on the instance padded by `2 ^ min(n, k)`, with `n` the number of distinct vertices. Padding
(`Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime_pad`) gives a multi-tape machine
within time `2 ^ (δ k)` times a polynomial in the encoded length, for some constant `δ`
(`Cslib.Complexity.ColorfulPath_decidableInExpTime`), so `ColorfulPath` is fixed-parameter
tractable in `k` (`Cslib.Complexity.ColorfulPath_mem_FPT`). The constant `δ` is not explicit: the
`2 ^ k` operations of the RAM analysis are not claimed for multi-tape machines.

## Main definitions

* `Cslib.Complexity.ColorfulPath`: colorful paths on `k` vertices with colors less than `k`, the
  colors given by a list (`Cslib.Complexity.colorOf`).
* `Cslib.Complexity.ColorCoding.Reaches`: the colorful paths with a given color set and last
  vertex.
* `Cslib.Complexity.ColorCoding.table`: the dynamic programming table over color sets.
* `Cslib.Complexity.colorfulPathBool`: the decider.

## Main results

* `Cslib.Complexity.ColorCoding.reaches_iff`: the recurrence of the dynamic programming.
* `Cslib.Complexity.ColorCoding.mem_table_getD`: correctness of the table: the entry at a color
  set lists exactly the endpoints of colorful paths with that color set.
* `Cslib.Complexity.ColorCoding.exists_reaches_iff`: colorful paths with color set
  `{0, …, k - 1}` are the colorful paths on `k` vertices with colors less than `k`.
* `Cslib.Complexity.colorfulPathBool_eq_true_iff`: correctness of the decider.
* `Cslib.Complexity.ColorCoding.computableInPolyTime_table`: the table on `N` color sets is
  polynomial-time for `N` in unary.
* `Cslib.Complexity.ColorfulPath_decidableInExpTime`, `Cslib.Complexity.ColorfulPath_mem_FPT`:
  colorful k-Path in time `2 ^ O(k)` times a polynomial, and in `FPT`.

## References

* [N. Alon, R. Yuster, U. Zwick, *Color-coding*][AlonYusterZwick1995]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Colorful k-Path** [CyganEtAl2015, Section 5.2]: the triples `((G, cs), k)` such that `G` has a
path on `k` vertices whose colors are pairwise distinct and less than `k`; colors are given by a
list parallel to the vertex list (`Cslib.Complexity.colorOf`). -/
@[expose]
def ColorfulPath : Set ((Graph × List ℕ) × ℕ) :=
  {x | ∃ p : List ℕ, x.1.1.IsVertexPath p ∧ p.length = x.2 ∧
    (p.map (colorOf x.1.1 x.1.2)).Nodup ∧ ∀ v ∈ p, colorOf x.1.1 x.1.2 v < x.2}

theorem mem_ColorfulPath_iff {G : Graph} {cs : List ℕ} {k : ℕ} :
    ((G, cs), k) ∈ ColorfulPath ↔ ∃ p : List ℕ, G.IsVertexPath p ∧ p.length = k ∧
      (p.map (colorOf G cs)).Nodup ∧ ∀ v ∈ p, colorOf G cs v < k :=
  Iff.rfl

namespace ColorCoding

variable (G : Graph) (χ : ℕ → ℕ)

/-- The color set `m`, read as a bit mask, is the set of colors of a colorful path of `G`
ending at `v`. -/
def Reaches (m v : ℕ) : Prop :=
  ∃ p : List ℕ, G.IsVertexPath (p ++ [v]) ∧ ((p ++ [v]).map χ).Nodup ∧
    ∀ c, m.testBit c = true ↔ c ∈ (p ++ [v]).map χ

/-- The entry of the dynamic programming table at the color set `m`, given the entries at
smaller color sets: the vertices `v` with `χ v ∈ m` such that `m = {χ v}`, or some neighbor of
`v` is in the entry at `m \ {χ v}`. -/
@[expose]
def entry (T : List (List ℕ)) (m : ℕ) : List ℕ :=
  G.distinctVertices.filter fun v => m.testBit (χ v) &&
    (m == 2 ^ χ v || (T.getD (m - 2 ^ χ v) []).any fun u => G.adjBool u v)

/-- The dynamic programming table on the color sets `0, …, N - 1`. -/
@[expose]
def table (N : ℕ) : List (List ℕ) :=
  (List.range N).foldl (fun T m => T ++ [entry G χ T m]) []

variable {G χ}

/-- **The recurrence of the dynamic programming** [CyganEtAl2015, Lemma 5.5]: a colorful path with
color set `m` ends at `v` exactly when `χ v ∈ m`, and either `m = {χ v}` or a colorful path with
color set `m \ {χ v}` ends at a neighbor of `v`. -/
theorem reaches_iff {m v : ℕ} :
    Reaches G χ m v ↔ v ∈ G.1 ∧ m.testBit (χ v) = true ∧
      (m = 2 ^ χ v ∨ ∃ u, Reaches G χ (m - 2 ^ χ v) u ∧ G.toSimpleGraph.Adj u v) := by
  constructor
  · rintro ⟨p, hp, hnd, hm⟩
    refine ⟨hp.2.1 v (by simp), (hm _).2 (by simp), ?_⟩
    rcases List.eq_nil_or_concat' p with rfl | ⟨L, u, rfl⟩
    · left
      exact Nat.eq_two_pow_of_testBit fun c => by simpa using hm c
    · right
      have hch := hp.2.2
      rw [List.isChain_append] at hch
      have hnd' := hnd
      rw [List.map_append, List.nodup_append] at hnd'
      have hva : χ v ∉ (L ++ [u]).map χ := fun h => hnd'.2.2 _ h _ (by simp) rfl
      refine ⟨u, ⟨L, ⟨(List.nodup_append.1 hp.1).1,
        fun x hx => hp.2.1 x (List.mem_append_left _ hx), hch.1⟩, hnd'.1, fun c => ?_⟩,
        hch.2.2 u (by simp) v (by simp)⟩
      rw [Nat.testBit_sub_two_pow ((hm _).2 (by simp)), Bool.and_eq_true, hm,
        decide_eq_true_iff]
      constructor
      · rintro ⟨hc, hne⟩
        simpa [hne] using hc
      · intro hc
        refine ⟨by simp_all, fun h => hva (h ▸ hc)⟩
  · rintro ⟨hv, hbit, rfl | ⟨u, ⟨p, hp, hnd, hm⟩, hadj⟩⟩
    · refine ⟨[], ⟨by simp, by simpa using hv, by simp⟩, by simp, fun c => ?_⟩
      rw [Nat.testBit_two_pow]
      simp [eq_comm]
    · have hva : χ v ∉ (p ++ [u]).map χ := fun h => by
        have := (hm (χ v)).2 h
        rw [Nat.testBit_sub_two_pow hbit] at this
        simp at this
      have hvp : v ∉ p ++ [u] := fun h => hva (List.mem_map_of_mem h)
      refine ⟨p ++ [u], ⟨?_, fun x hx => ?_, ?_⟩, ?_, fun c => ?_⟩
      · exact List.nodup_append.2 ⟨hp.1, by simp, fun a ha b hb => by
          simp only [List.mem_singleton] at hb
          exact hb ▸ fun h => hvp (h ▸ ha)⟩
      · rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hp.2.1 x hx
        · exact hv
      · rw [List.isChain_append]
        refine ⟨hp.2.2, by simp, fun x hx y hy => ?_⟩
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
        subst hx hy
        exact hadj
      · rw [List.map_append, List.nodup_append]
        exact ⟨hnd, by simp, fun a ha b hb => by
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          exact hb ▸ fun h => hva (h ▸ ha)⟩
      · have := hm c
        rw [Nat.testBit_sub_two_pow hbit, Bool.and_eq_true, decide_eq_true_iff] at this
        rw [List.map_append, List.mem_append, ← this, List.map_singleton, List.mem_singleton]
        by_cases hc : c = χ v
        · subst hc
          simp [hbit]
        · simp [hc]

theorem table_succ (N : ℕ) :
    table G χ (N + 1) = table G χ N ++ [entry G χ (table G χ N) N] := by
  simp only [table, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem length_table (N : ℕ) : (table G χ N).length = N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [table_succ, List.length_append, ih, List.length_singleton]

/-- **Correctness of the colorful-path table** [AlonYusterZwick1995, Lemma 3.1]
[CyganEtAl2015, Lemma 5.5]: below `N`, the entry at the color set `m` lists the vertices at
which some colorful path with color set `m` ends. -/
theorem mem_table_getD {N m v : ℕ} (hm : m < N) :
    v ∈ (table G χ N).getD m [] ↔ Reaches G χ m v := by
  induction N generalizing m v with
  | zero => omega
  | succ N ih =>
    rw [table_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · rw [List.getD_append _ _ _ _ (by rw [length_table]; exact hm)]
      exact ih hm
    · rw [List.getD_append_right _ _ _ _ (by rw [length_table]), length_table, Nat.sub_self,
        List.getD_cons_zero, entry, List.mem_filter, Graph.mem_distinctVertices,
        Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, reaches_iff]
      refine and_congr_right fun _ => and_congr_right fun hbit => or_congr_right ?_
      have hlt : m - 2 ^ χ v < m := Nat.sub_lt_self (Nat.two_pow_pos _)
        (Nat.ge_two_pow_of_testBit hbit)
      constructor
      · rintro ⟨u, hu, hadj⟩
        exact ⟨u, (ih hlt).1 hu, (Graph.adjBool_eq_true_iff G u v).1 hadj⟩
      · rintro ⟨u, hu, hadj⟩
        exact ⟨u, (ih hlt).2 hu, (Graph.adjBool_eq_true_iff G u v).2 hadj⟩

/-- The colorful paths on `k` vertices with colors less than `k` are the colorful paths ending
anywhere with color set `{0, …, k - 1}`. -/
theorem exists_reaches_iff {k : ℕ} (hk : 0 < k) :
    (∃ v, Reaches G χ (2 ^ k - 1) v) ↔ ∃ p : List ℕ, G.IsVertexPath p ∧ p.length = k ∧
      (p.map χ).Nodup ∧ ∀ v ∈ p, χ v < k := by
  constructor
  · rintro ⟨v, p, hp, hnd, hm⟩
    have hmem : ∀ c, c ∈ (p ++ [v]).map χ ↔ c < k := fun c => by
      rw [← hm, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    refine ⟨p ++ [v], hp, ?_, hnd, fun x hx => (hmem _).1 (List.mem_map_of_mem hx)⟩
    have hfs : ((p ++ [v]).map χ).toFinset = Finset.range k := by
      ext c
      rw [List.mem_toFinset, hmem, Finset.mem_range]
    rw [← List.length_map (f := χ), ← List.toFinset_card_of_nodup hnd, hfs, Finset.card_range]
  · rintro ⟨p, hp, hlen, hnd, hlt⟩
    rcases List.eq_nil_or_concat' p with rfl | ⟨L, v, rfl⟩
    · rw [List.length_nil] at hlen
      omega
    have hfs : ((L ++ [v]).map χ).toFinset = Finset.range k :=
      Finset.eq_of_subset_of_card_le
        (fun c hc => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
          exact Finset.mem_range.2 (hlt x hx))
        (by rw [Finset.card_range, List.toFinset_card_of_nodup hnd, List.length_map, hlen])
    refine ⟨v, L, hp, hnd, fun c => ?_⟩
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_iff, ← Finset.mem_range, ← hfs,
      List.mem_toFinset]

/-! ### Polynomial time on padded inputs -/

variable (G χ) in
/-- `Cslib.Complexity.ColorCoding.entry` with colors capped at `m`: the same entry
(`Cslib.Complexity.ColorCoding.entry_eq_entryCapped`), whose powers of two have length at most
`m + 1`. -/
private def entryCapped (T : List (List ℕ)) (m : ℕ) : List ℕ :=
  G.distinctVertices.filter fun v => m.testBit (min m (χ v)) &&
    (m == 2 ^ min m (χ v) || (T.getD (m - 2 ^ min m (χ v)) []).any fun u => G.adjBool u v)

private theorem entry_eq_entryCapped (T : List (List ℕ)) (m : ℕ) :
    entry G χ T m = entryCapped G χ T m := by
  refine List.filter_congr fun v _ => ?_
  rcases le_or_gt m (χ v) with h | h
  · rw [min_eq_left h, Nat.testBit_lt_two_pow (Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by norm_num) h)), Nat.testBit_lt_two_pow Nat.lt_two_pow_self,
      Bool.false_and, Bool.false_and]
  · rw [min_eq_right h.le]

private theorem table_eq_foldl (N : ℕ) :
    table G χ N = (List.range N).foldl (fun T m => T ++ [entryCapped G χ T m]) [] := by
  simp only [table, entry_eq_entryCapped]

end ColorCoding

/-- The input of a step of the table computation: the instance, the number of color sets in
unary, the table so far and the color set in unary. -/
private abbrev StepInput : Type := (((Graph × List ℕ) × ℕ) × List (List ℕ)) × ℕ

private abbrev encStepInput : StepInput ↪ List Bool :=
  encPair (encPair (encPair (encPair encGraph (encList encNat)) encUnary)
    (encList (encList encNat))) encUnary

open ComputableInPolyTime in
private theorem computableInPolyTime_entryCapped :
    ComputableInPolyTime
      (fun q : StepInput =>
        ColorCoding.entryCapped q.1.1.1.1 (colorOf q.1.1.1.1 q.1.1.1.2) q.1.2 q.2)
      encStepInput (encList encNat) := by
  have hG : ComputableInPolyTime (fun q : StepInput × ℕ => q.1.1.1.1.1)
      (encPair encStepInput encNat) encGraph := by fun_prop
  have hcs : ComputableInPolyTime (fun q : StepInput × ℕ => q.1.1.1.1.2)
      (encPair encStepInput encNat) (encList encNat) := by fun_prop
  have hv : ComputableInPolyTime (fun q : StepInput × ℕ => q.2)
      (encPair encStepInput encNat) encNat := by fun_prop
  have hmU : ComputableInPolyTime (fun q : StepInput × ℕ => q.1.2)
      (encPair encStepInput encNat) encUnary := by fun_prop
  have hmB : ComputableInPolyTime (fun q : StepInput × ℕ => q.1.2)
      (encPair encStepInput encNat) encNat := unary_to_binary.comp hmU
  have hT : ComputableInPolyTime (fun q : StepInput × ℕ => q.1.1.2)
      (encPair encStepInput encNat) (encList (encList encNat)) := by fun_prop
  have hidx : ComputableInPolyTime (fun q : StepInput × ℕ => q.1.1.1.1.1.1.idxOf q.2)
      (encPair encStepInput encNat) encUnary := by
    have hV : ComputableInPolyTime (fun q : StepInput × ℕ => q.1.1.1.1.1.1)
        (encPair encStepInput encNat) (encList encNat) := by
      unfold encGraph at hG
      exact (fst _ _).comp hG
    exact idxOfWithInput hV hv
  have hcol : ComputableInPolyTime
      (fun q : StepInput × ℕ => colorOf q.1.1.1.1.1 q.1.1.1.1.2 q.2)
      (encPair encStepInput encNat) encNat := by
    unfold colorOf
    exact (listGetD 0).comp (hcs.prod hidx)
  have hcap : ComputableInPolyTime
      (fun q : StepInput × ℕ => min q.1.2 (colorOf q.1.1.1.1.1 q.1.1.1.1.2 q.2))
      (encPair encStepInput encNat) encUnary := binary_min_unary' hmU hcol
  have hpow : ComputableInPolyTime
      (fun q : StepInput × ℕ => 2 ^ min q.1.2 (colorOf q.1.1.1.1.1 q.1.1.1.1.2 q.2))
      (encPair encStepInput encNat) encNat := binary_two_pow.comp hcap
  have hbit := binary_testBit hmB hcap
  have heq := beq hmB hpow
  have hsub := binary_sub' hmB hpow
  have hrow := listGetD_binary (encA := encList encNat) [] hT hsub
  have hany : ComputableInPolyTime
      (fun q : StepInput × ℕ =>
        (q.1.1.2.getD (q.1.2 - 2 ^ min q.1.2 (colorOf q.1.1.1.1.1 q.1.1.1.1.2 q.2)) []).any
          fun u => q.1.1.1.1.1.adjBool u q.2)
      (encPair encStepInput encNat) encBool := by
    refine anyWithInput hrow ?_
    have hG' : ComputableInPolyTime (fun p : (StepInput × ℕ) × ℕ => p.1.1.1.1.1.1)
        (encPair (encPair encStepInput encNat) encNat) encGraph := hG.comp (fst _ _)
    exact Graph.computableInPolyTime_adjBool_comp hG' (snd _ _) (hv.comp (fst _ _))
  have htest := bool_and' hbit (bool_or.comp (heq.prod hany))
  have hV : ComputableInPolyTime (fun q : StepInput => q.1.1.1.1.distinctVertices)
      encStepInput (encList encNat) := by fun_prop
  unfold ColorCoding.entryCapped
  exact filterWithInput hV htest

open ComputableInPolyTime in
/-- The table on `N` color sets, for `N` in unary, is polynomial-time. -/
theorem ColorCoding.computableInPolyTime_table :
    ComputableInPolyTime (fun x : (Graph × List ℕ) × ℕ => table x.1.1 (colorOf x.1.1 x.1.2) x.2)
      (encPair (encPair encGraph (encList encNat)) encUnary) (encList (encList encNat)) := by
  simp only [table_eq_foldl]
  have hstep : ComputableInPolyTime
      (fun q : StepInput =>
        q.1.2 ++ [entryCapped q.1.1.1.1 (colorOf q.1.1.1.1 q.1.1.1.2) q.1.2 q.2])
      encStepInput (encList (encList encNat)) :=
    listAppend' (snd' (fst _ _)) (cons' computableInPolyTime_entryCapped (const []))
  refine foldlWithInput_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (const []) ⟨range.comp (snd _ _), hstep, inferInstance, inferInstance⟩
    (growth := fun x => 2 * (encList encNat x.1.1.distinctVertices).length + 1)
    ⟨((PolyBounded.const 2).mul (Graph.computableInPolyTime_distinctVertices.comp
      ((fst _ _).comp (fst _ _))).polyBounded_length).add (.const 1), fun x T m _ => ?_⟩
  simp only [encList_append, List.length_append, encList_cons, encList_nil, List.append_nil,
    length_frame]
  have : (encList encNat (entryCapped x.1.1 (colorOf x.1.1 x.1.2) T m)).length ≤
      (encList encNat x.1.1.distinctVertices).length :=
    length_encList_sublist encNat List.filter_sublist
  omega

/-- The padded test of the dynamic programming: whether the table on `N` color sets has a
nonempty entry at the color set `N - 1`. -/
@[expose]
def ColorCoding.lastEntryNonempty (x : (Graph × List ℕ) × ℕ) : Bool :=
  !((table x.1.1 (colorOf x.1.1 x.1.2) x.2).getD (x.2 - 1) []).isEmpty

/-- **The color-coding decider for colorful k-paths** [CyganEtAl2015, Lemma 5.5]: accept when
`k = 0`; otherwise check that `k` is at most the number `n` of distinct vertices, and that the table
on the color sets `0, …, 2 ^ k - 1` has a nonempty entry at `{0, …, k - 1}`. -/
@[expose]
def colorfulPathBool (x : (Graph × List ℕ) × ℕ) : Bool :=
  x.2 == 0 || (decide (x.2 ≤ x.1.1.distinctVertices.length) &&
    ColorCoding.lastEntryNonempty (x.1, 2 ^ min x.1.1.distinctVertices.length x.2))

theorem colorfulPathBool_eq_true_iff (x : (Graph × List ℕ) × ℕ) :
    colorfulPathBool x = true ↔ x ∈ ColorfulPath := by
  obtain ⟨⟨G, cs⟩, k⟩ := x
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact iff_of_true (by simp [colorfulPathBool]) ⟨[], by simp [Graph.IsVertexPath]⟩
  have hk0 : (k == 0) = false := by simpa using hk.ne'
  have hlt : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt (Nat.two_pow_pos k) Nat.one_pos
  rw [colorfulPathBool, hk0, Bool.false_or, Bool.and_eq_true, decide_eq_true_iff,
    ColorCoding.lastEntryNonempty, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨hkn, hne⟩
    rw [Nat.min_eq_right hkn] at hne
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
    exact (ColorCoding.exists_reaches_iff hk).1 ⟨v, (ColorCoding.mem_table_getD hlt).1 hv⟩
  · intro hx
    obtain ⟨p, hp, hlen, -⟩ := id hx
    have hkn : k ≤ G.distinctVertices.length := hlen.symm.trans_le hp.length_le
    refine ⟨hkn, ?_⟩
    rw [Nat.min_eq_right hkn]
    obtain ⟨v, hv⟩ := (ColorCoding.exists_reaches_iff hk).2 hx
    exact List.ne_nil_of_mem ((ColorCoding.mem_table_getD hlt).2 hv)

open ComputableInPolyTime in
private theorem computableInPolyTime_colorfulPathPad :
    ComputableInPolyTime
      (fun y : ((Graph × List ℕ) × ℕ) × ℕ => y.1.2 == 0 ||
        (decide (y.1.2 ≤ y.1.1.1.distinctVertices.length) &&
          ColorCoding.lastEntryNonempty (y.1.1, y.2)))
      (encPair (encPair (encPair encGraph (encList encNat)) encNat) encUnary) encBool := by
  have hx : ComputableInPolyTime (fun y : ((Graph × List ℕ) × ℕ) × ℕ => y.1.1)
      (encPair (encPair (encPair encGraph (encList encNat)) encNat) encUnary)
      (encPair encGraph (encList encNat)) := fst' (fst _ _)
  have hk : ComputableInPolyTime (fun y : ((Graph × List ℕ) × ℕ) × ℕ => y.1.2)
      (encPair (encPair (encPair encGraph (encList encNat)) encNat) encUnary) encNat :=
    snd' (fst _ _)
  have hN : ComputableInPolyTime (fun y : ((Graph × List ℕ) × ℕ) × ℕ => y.2)
      (encPair (encPair (encPair encGraph (encList encNat)) encNat) encUnary) encUnary := snd _ _
  have hn := (length_list_binary encNat).comp
    (Graph.computableInPolyTime_distinctVertices.comp (fst' hx))
  have htab := ColorCoding.computableInPolyTime_table.comp (hx.prod hN)
  have hget := (listGetD (encA := encList encNat) []).comp (htab.prod (unary_sub' hN (const 1)))
  exact bool_or.comp ((beq hk (const 0)).prod
    (bool_and' (binary_le' hk hn) (bool_not.comp ((listIsEmpty (encA := encNat)).comp hget))))

open ComputableInPolyTime in
private theorem computableInPolyTime_colorfulPathExponent :
    ComputableInPolyTime (fun x : (Graph × List ℕ) × ℕ => min x.1.1.distinctVertices.length x.2)
      (encPair (encPair encGraph (encList encNat)) encNat) encUnary :=
  binary_min_unary' ((length_list encNat).comp
    (Graph.computableInPolyTime_distinctVertices.comp (fst' (fst _ _)))) (snd _ _)

/-- **Colorful k-Path in time `2 ^ O(k)` times a polynomial** [AlonYusterZwick1995, Lemma 3.1]
[CyganEtAl2015, Lemma 5.5], on multi-tape machines: the dynamic programming over color sets
(`Cslib.Complexity.colorfulPathBool`) runs on the input padded to length `2 ^ min(n, k)`. The
constant `δ` is not explicit; the bound `2 ^ k` of the RAM analysis is not claimed. -/
theorem ColorfulPath_decidableInExpTime :
    ∃ δ : ℝ, DecidableInExpTime ColorfulPath (encPair (encPair encGraph (encList encNat)) encNat)
      Prod.snd δ :=
  DecidableInExpTime.of_computableInPolyTime_pad computableInPolyTime_colorfulPathPad
    computableInPolyTime_colorfulPathExponent (fun _ => min_le_right _ _)
    fun x => (colorfulPathBool_eq_true_iff x).symm

/-- **Colorful k-Path is fixed-parameter tractable** in `k`. -/
theorem ColorfulPath_mem_FPT :
    ColorfulPath ∈ FPT (encPair (encPair encGraph (encList encNat)) encNat) Prod.snd :=
  let ⟨_, h⟩ := ColorfulPath_decidableInExpTime
  h.mem_FPT

end Cslib.Complexity
