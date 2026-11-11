/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Locality.Hanf
public import CslibFrontier.Logics.FirstOrder.Locality.Reachability
import CslibFrontier.Tactic.FirstOrder.Simp
import Mathlib.Basic.Finite.Sum
import Mathlib.Tactic.FinCases

/-!
# Exact Hanf and Gaifman locality ranks of first-order logic

`CslibFrontier.Logics.FirstOrder.Locality.Hanf` proves Hanf and Gaifman locality with the radii
`(3 ^ n - 1) / 2` and `(3 ^ (n + 1) - 1) / 2` of [Libkin, Theorem 4.12 and
Corollary 4.13][Libkin2004]. This module improves both bounds to their exact values on finite
structures, solving [Libkin, Exercises 4.10 and 4.11 (pp. 63–64)][Libkin2004]:

* **Sharp Gaifman locality (`2 ^ n - 1`).** In a finite structure `M`, tuples `a₁, a₂` with
  isomorphic radius-`(2 ^ n - 1)` neighborhoods are `n`-round Ehrenfeucht–Fraïssé-equivalent
  (`NbhdIso.duplicatorWins_of_two_pow`; `NbhdIso.duplicatorWins_of_equiv_two_pow` is the
  two-structure form) and, when `L.IsRelational`, satisfy the same formulas of quantifier rank at
  most `n` (`NbhdIso.realize_iff_of_two_pow`, `NbhdIso.formula_realize_iff_of_two_pow`).
* **Sharp Hanf locality (`2 ^ (n - 1) - 1`).** Over finite nonempty structures, Hanf-equivalence at
  radius `2 ^ (n - 1) - 1` implies `n`-round Ehrenfeucht–Fraïssé-equivalence
  (`HanfEquiv.duplicatorWins_of_two_pow`), and therefore agreement on relational formulas and
  sentences of quantifier rank at most `n` (`HanfEquiv.realize_iff_of_two_pow`,
  `HanfEquiv.formula_realize_iff_of_two_pow`, `realize_sentence_iff_of_nbhdIso_two_pow`). Notice
  that in `ℕ`, `2 ^ (0 - 1) - 1 = 0` and `2 ^ (1 - 1) - 1 = 0`, so radius `0` suffices for both
  `n = 0` and `n = 1`.
* **Matching lower bounds over `FirstOrder.Language.graph`.**
  - For every `n ≥ 1` and `r < 2 ^ n - 1`, two vertices of a finite `Language.graph`-structure
    have isomorphic radius-`r` neighborhoods yet disagree on the quantifier-rank-`n` formula
    `loopReach n` (`exists_nbhdIso_realize_loopReach`), so any Gaifman locality radius `ρ n` valid
    on finite `Language.graph`-structures satisfies `2 ^ n - 1 ≤ ρ n` for all `n`
    (`two_pow_sub_one_le_of_gaifman_radius`).
  - For every `n ≥ 2` and `d < 2 ^ (n - 1) - 1`, two finite nonempty `Language.graph`-structures
    are Hanf-equivalent at radius `d` yet disagree on a `Language.graph.Sentence` of quantifier
    rank `n` (`exists_hanfEquiv_sentence_not_realize_iff`), and likewise for `1`-tuples and
    `Language.graph.Formula (Fin 1)` (`exists_hanfEquiv_formula_not_realize_iff`). Consequently any
    Hanf locality radius `ρ n` valid on finite nonempty `Language.graph`-structures satisfies
    `2 ^ (n - 1) - 1 ≤ ρ n` for all `n` (`two_pow_pred_sub_one_le_of_hanf_sentence_radius`,
    `two_pow_pred_sub_one_le_of_hanf_radius`).

**Proof ideas.** The upper bounds maintain a shrinking clustered neighborhood-isomorphism invariant
`ClusterWitness`: with `m` rounds remaining, the pebbled indices are partitioned into clusters that
are pairwise more than `2 ^ m` apart on both sides and carry radius-`(2 ^ m - 1)` neighborhood
isomorphisms. When Spoiler plays within `T = 2 ^ m'` of a cluster at `m = m' + 1`, that cluster is
unique because distinct clusters are more than `2 T` apart, and restricting its radius-`(2 T - 1)`
isomorphism extends the cluster at radius `T - 1` while keeping distance more than `T` from all
other clusters. When Spoiler plays outside every radius-`T` cluster ball, those balls are pairwise
disjoint and `exists_compl_equiv_nbhdIso` matches the move outside the balls on the other side with
the same radius-`(T - 1)` singleton neighborhood type, forming a new cluster.

For the lower bounds, `relStructure` interprets `Language.graph` as directed graphs with self-loops,
whose Gaifman graph ignores edge orientation and self-loops (`gaifmanGraph_relStructure`). Adding a
self-loop at the far end of one component of `P_{2^n} ⊕ P_{2^n}` gives the `2 ^ n - 1` Gaifman
bound via `loopReach n`. Placing two self-loops on one directed path of `P_{2^n - 1} ⊕ P_{2^n - 1}`
versus one self-loop on each component gives the `2 ^ (n - 1) - 1` Hanf bound: swapping components
on the `d`-ball around the right endpoint matches all `d`-neighborhoods whenever `2 d < 2 ^ n - 2`,
while a rank-`n` sentence detects two distinct self-loops at directed distance at most `2 ^ n - 2`
by meeting at their midpoint.

## Main definitions

* `Cslib.Logic.FO.Locality.loopReach`: the rank-`n` formula stating that a self-loop lies within
  distance `2 ^ n - 1` along `distLE`.

## Main results

* `Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins_of_equiv_two_pow`,
  `Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins_of_two_pow`,
  `Cslib.Logic.FO.Locality.NbhdIso.realize_iff_of_two_pow`,
  `Cslib.Logic.FO.Locality.NbhdIso.formula_realize_iff_of_two_pow`: sharp Gaifman locality at
  radius `2 ^ n - 1` ([Libkin, Exercises 4.10 and 4.11][Libkin2004]).
* `Cslib.Logic.FO.Locality.HanfEquiv.duplicatorWins_of_two_pow`,
  `Cslib.Logic.FO.Locality.HanfEquiv.realize_iff_of_two_pow`,
  `Cslib.Logic.FO.Locality.HanfEquiv.formula_realize_iff_of_two_pow`,
  `Cslib.Logic.FO.Locality.realize_sentence_iff_of_nbhdIso_two_pow`: sharp Hanf locality at radius
  `2 ^ (n - 1) - 1` ([Libkin, Exercises 4.10 and 4.11][Libkin2004]).
* `Cslib.Logic.FO.Locality.quantifierRank_loopReach`,
  `Cslib.Logic.FO.Locality.exists_nbhdIso_realize_loopReach`,
  `Cslib.Logic.FO.Locality.two_pow_sub_one_le_of_gaifman_radius`: optimality of the `2 ^ n - 1`
  Gaifman radius ([Libkin, Exercise 4.11][Libkin2004]).
* `Cslib.Logic.FO.Locality.exists_hanfEquiv_sentence_not_realize_iff`,
  `Cslib.Logic.FO.Locality.exists_hanfEquiv_formula_not_realize_iff`,
  `Cslib.Logic.FO.Locality.two_pow_pred_sub_one_le_of_hanf_sentence_radius`,
  `Cslib.Logic.FO.Locality.two_pow_pred_sub_one_le_of_hanf_radius`: optimality of the
  `2 ^ (n - 1) - 1` Hanf radius ([Libkin, Exercise 4.11][Libkin2004]).

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Exercises 4.10 and 4.11 (pp. 63–64).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Locality

universe u v w w'

section UpperBounds

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-! ### Shrinking clustered neighborhood-isomorphism invariant -/

/-- One cluster `p` in a clustered game position: an enumeration `idx` of the indices assigned to
`p` together with a radius-`r` neighborhood isomorphism on the corresponding subtuples. -/
private structure ClusterEntry (L : Language.{u, v}) [L.Structure M] [L.Structure N]
    (r k : ℕ) (a : Fin k → M) (b : Fin k → N) (c : ℕ) (cl : Fin k → Fin c) (p : Fin c) where
  sz : ℕ
  idx : Fin sz → Fin k
  cl_idx : ∀ u, cl (idx u) = p
  mem_idx : ∀ i, cl i = p → ∃ u, idx u = i
  isoFun : M → N
  isNbhdIso : IsNbhdIso L r (a ∘ idx) (b ∘ idx) isoFun

/-- A clustered position with `m` rounds remaining: the `k` pebble indices are partitioned into `c`
clusters, each carrying a radius-`(2 ^ m - 1)` neighborhood isomorphism, while indices in distinct
clusters lie at Gaifman distance strictly greater than `2 ^ m` in both `M` and `N`. -/
private structure ClusterWitness (L : Language.{u, v}) [L.Structure M] [L.Structure N]
    (m : ℕ) {k : ℕ} (a : Fin k → M) (b : Fin k → N) where
  c : ℕ
  cl : Fin k → Fin c
  entry : ∀ p : Fin c, ClusterEntry L (2 ^ m - 1) k a b c cl p
  nullary : ∀ R : L.Relations 0,
    RelMap R (Fin.elim0 : Fin 0 → M) ↔ RelMap R (Fin.elim0 : Fin 0 → N)
  sepM : ∀ i j : Fin k, cl i ≠ cl j →
    ((2 ^ m : ℕ) : ℕ∞) < (gaifmanGraph L M).edist (a i) (a j)
  sepN : ∀ i j : Fin k, cl i ≠ cl j →
    ((2 ^ m : ℕ) : ℕ∞) < (gaifmanGraph L N).edist (b i) (b j)

private theorem two_pow_add_pred_eq (m : ℕ) : 2 ^ m + (2 ^ m - 1) = 2 ^ (m + 1) - 1 := by
  have := @Nat.one_le_two_pow m
  rw [pow_succ]
  omega

private theorem one_le_cast_two_pow (m : ℕ) : (1 : ℕ∞) ≤ ((2 ^ m : ℕ) : ℕ∞) := by
  exact_mod_cast @Nat.one_le_two_pow m

/-- Every clustered position is a partial isomorphism: pebbles in the same cluster agree via that
cluster's neighborhood isomorphism, while pebbles in distinct clusters have Gaifman distance
greater than `1` and therefore cannot be equal or share a relation tuple. -/
private theorem ClusterWitness.partialIso {m k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (W : ClusterWitness L m a b) : PartialIso L a b := by
  refine ⟨fun i j => ?_, fun {l} R f => ?_⟩
  · by_cases hij : W.cl i = W.cl j
    · set p := W.cl i
      obtain ⟨u, hu⟩ := (W.entry p).mem_idx i rfl
      obtain ⟨v, hv⟩ := (W.entry p).mem_idx j hij.symm
      have heq := (W.entry p).isNbhdIso.partialIso.eq_iff u v
      simp only [Function.comp_apply, hu, hv] at heq
      exact heq
    · have ha : a i ≠ a j := fun h => by
        have hsep := W.sepM i j hij
        rw [h, SimpleGraph.edist_self] at hsep
        exact absurd ( (one_le_cast_two_pow m).trans_lt hsep ) (by simp)
      have hb : b i ≠ b j := fun h => by
        have hsep := W.sepN i j hij
        rw [h, SimpleGraph.edist_self] at hsep
        exact absurd ( (one_le_cast_two_pow m).trans_lt hsep ) (by simp)
      exact iff_of_false ha hb
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · rw [Subsingleton.elim (a ∘ f) Fin.elim0, Subsingleton.elim (b ∘ f) Fin.elim0]
      exact W.nullary R
    · let i₀ : Fin l := ⟨0, hl⟩
      set p := W.cl (f i₀)
      by_cases hall : ∀ q : Fin l, W.cl (f q) = p
      · choose g hg using fun q => (W.entry p).mem_idx (f q) (hall q)
        have ha : a ∘ f = (a ∘ (W.entry p).idx) ∘ g := funext fun q => congrArg a (hg q).symm
        have hb : b ∘ f = (b ∘ (W.entry p).idx) ∘ g := funext fun q => congrArg b (hg q).symm
        rw [ha, hb]
        exact (W.entry p).isNbhdIso.partialIso.relMap_iff R g
      · simp only [not_forall] at hall
        obtain ⟨q, hq⟩ := hall
        have farM : 1 < (gaifmanGraph L M).edist (a (f q)) (a (f i₀)) :=
          (one_le_cast_two_pow m).trans_lt (W.sepM (f q) (f i₀) hq)
        have farN : 1 < (gaifmanGraph L N).edist (b (f q)) (b (f i₀)) :=
          (one_le_cast_two_pow m).trans_lt (W.sepN (f q) (f i₀) hq)
        exact iff_of_false
          (fun hR => absurd (edist_le_one_of_relMap hR q i₀) (not_le.2 farM))
          (fun hR => absurd (edist_le_one_of_relMap hR q i₀) (not_le.2 farN))

/-- Symmetry of clustered positions when `M` is nonempty. -/
private noncomputable def ClusterWitness.symm [Nonempty M] {m k : ℕ} {a : Fin k → M}
    {b : Fin k → N} (W : ClusterWitness L m a b) : ClusterWitness L m b a where
  c := W.c
  cl := W.cl
  entry p :=
    { sz := (W.entry p).sz
      idx := (W.entry p).idx
      cl_idx := (W.entry p).cl_idx
      mem_idx := (W.entry p).mem_idx
      isoFun := Function.invFunOn (W.entry p).isoFun (ball L (a ∘ (W.entry p).idx) (2 ^ m - 1))
      isNbhdIso := (W.entry p).isNbhdIso.symm }
  nullary R := (W.nullary R).symm
  sepM := W.sepN
  sepN := W.sepM

private theorem edist_gt_of_sep {V : Type*} {G : SimpleGraph V} {T : ℕ} {u v x : V}
    (huv : ((2 * T : ℕ) : ℕ∞) < G.edist u v) (hux : G.edist u x ≤ T) :
    ((T : ℕ) : ℕ∞) < G.edist x v := by
  by_contra hle
  rw [not_lt] at hle
  have htri : G.edist u v ≤ ((2 * T : ℕ) : ℕ∞) :=
    calc G.edist u v ≤ G.edist u x + G.edist x v := SimpleGraph.edist_triangle
      _ ≤ (T : ℕ∞) + T := add_le_add hux hle
      _ = ((2 * T : ℕ) : ℕ∞) := by rw [← Nat.cast_add, two_mul]
  exact absurd huv (not_lt.2 htri)

/-- One forth step of the clustered invariant: from stage `m + 1` and Spoiler move `x : M`,
Duplicator finds `y : N` preserving `ClusterWitness` at stage `m`. -/
private theorem ClusterWitness.forth [Finite M] {m k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (W : ClusterWitness L (m + 1) a b) (e : M ≃ N)
    (he : ∀ z, NbhdIso L (2 ^ m - 1) (fun _ : Fin 1 => z) (fun _ : Fin 1 => e z)) (x : M) :
    ∃ y : N, Nonempty (ClusterWitness L m (Fin.snoc a x : Fin (k + 1) → M)
      (Fin.snoc b y : Fin (k + 1) → N)) := by
  have hr_eq := two_pow_add_pred_eq m
  have hpow : ((2 ^ (m + 1) : ℕ) : ℕ∞) = ((2 * 2 ^ m : ℕ) : ℕ∞) := by rw [pow_succ, mul_comm]
  by_cases hnear : ∃ p : Fin W.c, x ∈ ball L (a ∘ (W.entry p).idx) (2 ^ m)
  · -- Case A: `x` lies within `2 ^ m` of some cluster `p₀`; extend `p₀`.
    obtain ⟨p₀, hx⟩ := hnear
    set E₀ := W.entry p₀
    set y := E₀.isoFun x
    have hy : y ∈ ball L (b ∘ E₀.idx) (2 ^ m) :=
      E₀.isNbhdIso.mapsTo_ball (by omega) hx
    refine ⟨y, ⟨{
      c := W.c
      cl := Fin.snoc W.cl p₀
      entry := fun p =>
        if hp : p = p₀ then
          { sz := E₀.sz + 1
            idx := Fin.snoc (Fin.castSucc ∘ E₀.idx) (Fin.last k)
            cl_idx := fun u => by
              induction u using Fin.lastCases with
              | last => simp [hp]
              | cast u => simp [E₀.cl_idx u, hp]
            mem_idx := fun i hi => by
              induction i using Fin.lastCases with
              | last => exact ⟨Fin.last E₀.sz, by simp⟩
              | cast j =>
                simp only [Fin.snoc_castSucc] at hi
                obtain ⟨u, hu⟩ := E₀.mem_idx j ( hi.trans hp )
                exact ⟨u.castSucc, by simp [hu]⟩
            isoFun := E₀.isoFun
            isNbhdIso := by
              have hsub : ∀ u : Fin (E₀.sz + 1),
                  (Fin.snoc (a ∘ E₀.idx) x : Fin (E₀.sz + 1) → M) u ∈
                    ball L (a ∘ E₀.idx) (2 ^ m) := by
                intro u
                induction u using Fin.lastCases with
                | last => simpa using hx
                | cast u =>
                  simpa using ball_mono (by omega) (mem_ball_self (a ∘ E₀.idx) 0 u)
              have hres := E₀.isNbhdIso.restrict (x := Fin.snoc (a ∘ E₀.idx) x)
                (l := 2 ^ m) (d := 2 ^ m - 1) hsub hr_eq.le
              have ha_eq : (Fin.snoc a x : Fin (k + 1) → M) ∘
                  Fin.snoc (Fin.castSucc ∘ E₀.idx) (Fin.last k) =
                  Fin.snoc (a ∘ E₀.idx) x := by
                ext u
                induction u using Fin.lastCases <;> simp
              have hb_eq : (Fin.snoc b y : Fin (k + 1) → N) ∘
                  Fin.snoc (Fin.castSucc ∘ E₀.idx) (Fin.last k) =
                  E₀.isoFun ∘ Fin.snoc (a ∘ E₀.idx) x := by
                ext u
                induction u using Fin.lastCases with
                | last => simp [y]
                | cast u =>
                  simp only [Function.comp_apply, Fin.snoc_castSucc]
                  exact (E₀.isNbhdIso.map_tuple u).symm
              rwa [ha_eq, hb_eq] }
        else
          { sz := (W.entry p).sz
            idx := Fin.castSucc ∘ (W.entry p).idx
            cl_idx := fun u => by simp [(W.entry p).cl_idx u]
            mem_idx := fun i hi => by
              induction i using Fin.lastCases with
              | last =>
                simp only [Fin.snoc_last] at hi
                exact absurd hi.symm hp
              | cast j =>
                simp only [Fin.snoc_castSucc] at hi
                obtain ⟨u, hu⟩ := (W.entry p).mem_idx j hi
                exact ⟨u, by simp [hu]⟩
            isoFun := (W.entry p).isoFun
            isNbhdIso := by
              have ha_eq : (Fin.snoc a x : Fin (k + 1) → M) ∘
                  (Fin.castSucc ∘ (W.entry p).idx) = a ∘ (W.entry p).idx := by
                ext u; simp
              have hb_eq : (Fin.snoc b y : Fin (k + 1) → N) ∘
                  (Fin.castSucc ∘ (W.entry p).idx) = b ∘ (W.entry p).idx := by
                ext u; simp
              rw [ha_eq, hb_eq]
              exact (W.entry p).isNbhdIso.mono (by omega) }
      nullary := W.nullary
      sepM := fun i j hij => by
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij ⊢
            obtain ⟨u, hu⟩ := mem_ball.1 hx
            have hsep := W.sepM (E₀.idx u) j (by rwa [E₀.cl_idx u])
            rw [hpow] at hsep
            exact edist_gt_of_sep hsep hu
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij ⊢
            obtain ⟨u, hu⟩ := mem_ball.1 hx
            have hsep := W.sepM (E₀.idx u) i (by rw [E₀.cl_idx u]; exact hij.symm)
            rw [hpow] at hsep
            rw [SimpleGraph.edist_comm]
            exact edist_gt_of_sep hsep hu
          | cast j =>
            simp only [Fin.snoc_castSucc] at hij ⊢
            have hle : ((2 ^ m : ℕ) : ℕ∞) ≤ ((2 ^ (m + 1) : ℕ) : ℕ∞) := by
              exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.le_succ m)
            exact hle.trans_lt (W.sepM i j hij)
      sepN := fun i j hij => by
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij ⊢
            obtain ⟨u, hu⟩ := mem_ball.1 hy
            have hsep := W.sepN (E₀.idx u) j (by rwa [E₀.cl_idx u])
            rw [hpow] at hsep
            exact edist_gt_of_sep hsep hu
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij ⊢
            obtain ⟨u, hu⟩ := mem_ball.1 hy
            have hsep := W.sepN (E₀.idx u) i (by rw [E₀.cl_idx u]; exact hij.symm)
            rw [hpow] at hsep
            rw [SimpleGraph.edist_comm]
            exact edist_gt_of_sep hsep hu
          | cast j =>
            simp only [Fin.snoc_castSucc] at hij ⊢
            have hle : ((2 ^ m : ℕ) : ℕ∞) ≤ ((2 ^ (m + 1) : ℕ) : ℕ∞) := by
              exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.le_succ m)
            exact hle.trans_lt (W.sepN i j hij) }⟩⟩
  · -- Case B: `x` lies outside every cluster's `2 ^ m`-ball; form a new singleton cluster.
    let BM : Fin W.c → Set M := fun p => ball L (a ∘ (W.entry p).idx) (2 ^ m)
    let BN : Fin W.c → Set N := fun p => ball L (b ∘ (W.entry p).idx) (2 ^ m)
    have disjM : ∀ {p q : Fin W.c}, p ≠ q → ∀ {z : M}, z ∈ BM p → z ∉ BM q := by
      intro p q hpq z hzp hzq
      obtain ⟨u, hu⟩ := mem_ball.1 hzp
      obtain ⟨v, hv⟩ := mem_ball.1 hzq
      have hsep := W.sepM ((W.entry p).idx u) ((W.entry q).idx v)
        (by rw [(W.entry p).cl_idx u, (W.entry q).cl_idx v]; exact hpq)
      rw [hpow] at hsep
      rw [SimpleGraph.edist_comm] at hv
      exact absurd hv (not_le.2 (edist_gt_of_sep hsep hu))
    have disjN : ∀ {p q : Fin W.c}, p ≠ q → ∀ {w : N}, w ∈ BN p → w ∉ BN q := by
      intro p q hpq w hwp hwq
      obtain ⟨u, hu⟩ := mem_ball.1 hwp
      obtain ⟨v, hv⟩ := mem_ball.1 hwq
      have hsep := W.sepN ((W.entry p).idx u) ((W.entry q).idx v)
        (by rw [(W.entry p).cl_idx u, (W.entry q).cl_idx v]; exact hpq)
      rw [hpow] at hsep
      rw [SimpleGraph.edist_comm] at hv
      exact absurd hv (not_le.2 (edist_gt_of_sep hsep hu))
    set SM : Set M := ⋃ p, BM p
    set SN : Set N := ⋃ p, BN p
    classical
    let H : M → N := fun z => if hz : ∃ p, z ∈ BM p then (W.entry hz.choose).isoFun z else e z
    have hEq : ∀ (p : Fin W.c) {z : M}, z ∈ BM p → H z = (W.entry p).isoFun z := by
      intro p z hzp
      have hz : ∃ q, z ∈ BM q := ⟨p, hzp⟩
      have hp : hz.choose = p := by
        by_contra hne
        exact disjM hne hz.choose_spec hzp
      simp only [H, hz, dite_true]
      rw [hp]
    have hBij : Set.BijOn H SM SN := by
      refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ h12 => ?_, fun w hw => ?_⟩
      · obtain ⟨p, hzp⟩ := Set.mem_iUnion.1 hz
        refine Set.mem_iUnion.2 ⟨p, ?_⟩
        rw [hEq p hzp]
        exact (W.entry p).isNbhdIso.mapsTo_ball (by omega) hzp
      · obtain ⟨p₁, hz₁p⟩ := Set.mem_iUnion.1 hz₁
        obtain ⟨p₂, hz₂p⟩ := Set.mem_iUnion.1 hz₂
        rw [hEq p₁ hz₁p, hEq p₂ hz₂p] at h12
        have hw₁ : (W.entry p₁).isoFun z₁ ∈ BN p₁ :=
          (W.entry p₁).isNbhdIso.mapsTo_ball (by omega) hz₁p
        have hw₂ : (W.entry p₁).isoFun z₁ ∈ BN p₂ := by
          rw [h12]
          exact (W.entry p₂).isNbhdIso.mapsTo_ball (by omega) hz₂p
        have hp : p₁ = p₂ := by
          by_contra hne
          exact disjN hne hw₁ hw₂
        subst hp
        exact ((W.entry p₁).isNbhdIso.mono (by omega : 2 ^ m ≤ 2 ^ (m + 1) - 1)).bijOn.injOn
          hz₁p hz₂p h12
      · obtain ⟨p, hwp⟩ := Set.mem_iUnion.1 hw
        obtain ⟨z, hzp, rfl⟩ :=
          ((W.entry p).isNbhdIso.mono (by omega : 2 ^ m ≤ 2 ^ (m + 1) - 1)).bijOn.surjOn hwp
        exact ⟨z, Set.mem_iUnion.2 ⟨p, hzp⟩, hEq p hzp⟩
    have hPt : ∀ z ∈ SM, NbhdIso L (2 ^ m - 1) (fun _ : Fin 1 => z) (fun _ : Fin 1 => H z) := by
      intro z hz
      obtain ⟨p, hzp⟩ := Set.mem_iUnion.1 hz
      rw [hEq p hzp]
      exact ((W.entry p).isNbhdIso.restrict (x := fun _ : Fin 1 => z) (l := 2 ^ m)
        (d := 2 ^ m - 1) (fun _ => hzp) hr_eq.le).nbhdIso
    obtain ⟨g, hg⟩ := exists_compl_equiv_nbhdIso e he hBij hPt
    have hxSM : x ∈ SMᶜ := fun hx' => hnear (Set.mem_iUnion.1 hx')
    set y : N := (g ⟨x, hxSM⟩).val
    have hySN : y ∉ SN := (g ⟨x, hxSM⟩).property
    obtain ⟨h_xy, H_xy⟩ := nbhdIso_iff.1 (hg ⟨x, hxSM⟩)
    refine ⟨y, ⟨{
      c := W.c + 1
      cl := Fin.snoc (Fin.castSucc ∘ W.cl) (Fin.last W.c)
      entry := fun p =>
        Fin.lastCases
          { sz := 1
            idx := fun _ => Fin.last k
            cl_idx := fun _ => by simp
            mem_idx := fun i hi => by
              induction i using Fin.lastCases with
              | last => exact ⟨0, rfl⟩
              | cast j =>
                simp only [Fin.snoc_castSucc, Function.comp_apply] at hi
                exact absurd hi (Fin.castSucc_ne_last _)
            isoFun := h_xy
            isNbhdIso := by
              have ha_eq : (Fin.snoc a x : Fin (k + 1) → M) ∘ (fun _ : Fin 1 => Fin.last k) =
                  fun _ : Fin 1 => x := by ext; simp
              have hb_eq : (Fin.snoc b y : Fin (k + 1) → N) ∘ (fun _ : Fin 1 => Fin.last k) =
                  fun _ : Fin 1 => y := by ext; simp
              rwa [ha_eq, hb_eq] }
          (fun p' =>
            { sz := (W.entry p').sz
              idx := Fin.castSucc ∘ (W.entry p').idx
              cl_idx := fun u => by simp [(W.entry p').cl_idx u]
              mem_idx := fun i hi => by
                induction i using Fin.lastCases with
                | last =>
                  simp only [Fin.snoc_last] at hi
                  exact absurd hi.symm (Fin.castSucc_ne_last _)
                | cast j =>
                  simp only [Fin.snoc_castSucc, Function.comp_apply,
                    Fin.castSucc_inj] at hi
                  obtain ⟨u, hu⟩ := (W.entry p').mem_idx j hi
                  exact ⟨u, by simp [hu]⟩
              isoFun := (W.entry p').isoFun
              isNbhdIso := by
                have ha_eq : (Fin.snoc a x : Fin (k + 1) → M) ∘
                    (Fin.castSucc ∘ (W.entry p').idx) = a ∘ (W.entry p').idx := by ext; simp
                have hb_eq : (Fin.snoc b y : Fin (k + 1) → N) ∘
                    (Fin.castSucc ∘ (W.entry p').idx) = b ∘ (W.entry p').idx := by ext; simp
                rw [ha_eq, hb_eq]
                exact (W.entry p').isNbhdIso.mono (by omega) })
          p
      nullary := W.nullary
      sepM := fun i j hij => by
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc]
            obtain ⟨u, hu⟩ := (W.entry (W.cl j)).mem_idx j rfl
            rw [SimpleGraph.edist_comm]
            exact lt_of_not_ge fun hle => hxSM (Set.mem_iUnion.2
              ⟨W.cl j, mem_ball.2 ⟨u, by simpa [Function.comp_apply, hu] using hle⟩⟩)
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            obtain ⟨u, hu⟩ := (W.entry (W.cl i)).mem_idx i rfl
            exact lt_of_not_ge fun hle => hxSM (Set.mem_iUnion.2
              ⟨W.cl i, mem_ball.2 ⟨u, by simpa [Function.comp_apply, hu] using hle⟩⟩)
          | cast j =>
            simp only [Fin.snoc_castSucc, Function.comp_apply, ne_eq, Fin.castSucc_inj] at hij ⊢
            have hle : ((2 ^ m : ℕ) : ℕ∞) ≤ ((2 ^ (m + 1) : ℕ) : ℕ∞) := by
              exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.le_succ m)
            exact hle.trans_lt (W.sepM i j hij)
      sepN := fun i j hij => by
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc]
            obtain ⟨u, hu⟩ := (W.entry (W.cl j)).mem_idx j rfl
            rw [SimpleGraph.edist_comm]
            exact lt_of_not_ge fun hle => hySN (Set.mem_iUnion.2
              ⟨W.cl j, mem_ball.2 ⟨u, by simpa [Function.comp_apply, hu] using hle⟩⟩)
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            obtain ⟨u, hu⟩ := (W.entry (W.cl i)).mem_idx i rfl
            exact lt_of_not_ge fun hle => hySN (Set.mem_iUnion.2
              ⟨W.cl i, mem_ball.2 ⟨u, by simpa [Function.comp_apply, hu] using hle⟩⟩)
          | cast j =>
            simp only [Fin.snoc_castSucc, Function.comp_apply, ne_eq, Fin.castSucc_inj] at hij ⊢
            have hle : ((2 ^ m : ℕ) : ℕ∞) ≤ ((2 ^ (m + 1) : ℕ) : ℕ∞) := by
              exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.le_succ m)
            exact hle.trans_lt (W.sepN i j hij) }⟩⟩

private theorem ClusterWitness.duplicatorWins [Finite M] :
    ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N} (e : M ≃ N),
      (∀ m < n, ∀ z, NbhdIso L (2 ^ m - 1) (fun _ : Fin 1 => z) (fun _ : Fin 1 => e z)) →
      ClusterWitness L n a b → DuplicatorWins L n a b
  | 0, _, _, _, _, _, W => duplicatorWins_zero.2 W.partialIso
  | n + 1, _, _, _, e, he, W => by
    refine duplicatorWins_succ.2 ⟨W.partialIso, fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, ⟨W'⟩⟩ := W.forth e (he n (Nat.lt_succ_self n)) x
      exact ⟨y, W'.duplicatorWins e (fun m hm => he m (Nat.lt_succ_of_lt hm))⟩
    · have hM : Nonempty M := ⟨e.symm y⟩
      have hN : Nonempty N := ⟨y⟩
      have : Finite N := Finite.of_equiv M e
      have he' : ∀ z, NbhdIso L (2 ^ n - 1) (fun _ : Fin 1 => z) (fun _ : Fin 1 => e.symm z) :=
        fun z => by simpa using (he n (Nat.lt_succ_self n) (e.symm z)).symm
      obtain ⟨x, ⟨W'⟩⟩ := W.symm.forth e.symm he' y
      exact ⟨x, W'.symm.duplicatorWins e (fun m hm => he m (Nat.lt_succ_of_lt hm))⟩

/-! ### Sharp Gaifman locality (`2 ^ n - 1`) -/

/-- **Sharp Gaifman locality, two-structure form**
([Libkin, Exercises 4.10 and 4.11][Libkin2004]): if a bijection `e : M ≃ N` from a finite
structure matches points with isomorphic radius-`(2 ^ (n - 1) - 1)` neighborhoods, then tuples
with isomorphic radius-`(2 ^ n - 1)` neighborhoods are `n`-round
Ehrenfeucht–Fraïssé-equivalent. -/
theorem NbhdIso.duplicatorWins_of_equiv_two_pow [Finite M] {n k : ℕ} {a : Fin k → M}
    {b : Fin k → N} (e : M ≃ N)
    (he : ∀ c, NbhdIso L (2 ^ (n - 1) - 1) (fun _ : Fin 1 => c) (fun _ : Fin 1 => e c))
    (hab : NbhdIso L (2 ^ n - 1) a b) : DuplicatorWins L n a b := by
  obtain ⟨h, Hh⟩ := nbhdIso_iff.1 hab
  let W : ClusterWitness L n a b :=
    { c := 1
      cl := fun _ => 0
      entry := fun p =>
        { sz := k
          idx := id
          cl_idx := fun _ => Subsingleton.elim 0 p
          mem_idx := fun i _ => ⟨i, rfl⟩
          isoFun := h
          isNbhdIso := Hh }
      nullary := fun R => by
        simpa only [Subsingleton.elim (a ∘ Fin.elim0) Fin.elim0,
          Subsingleton.elim (b ∘ Fin.elim0) Fin.elim0] using Hh.partialIso.relMap_iff R Fin.elim0
      sepM := fun _ _ hne => absurd (Subsingleton.elim _ _) hne
      sepN := fun _ _ hne => absurd (Subsingleton.elim _ _) hne }
  refine W.duplicatorWins e fun m hm z => (he z).mono ?_
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega)) 1

/-- **Sharp Gaifman locality** ([Libkin, Exercises 4.10 and 4.11][Libkin2004]): in a finite
structure, tuples with isomorphic radius-`(2 ^ n - 1)` neighborhoods are `n`-round
Ehrenfeucht–Fraïssé-equivalent. -/
theorem NbhdIso.duplicatorWins_of_two_pow [Finite M] {n k : ℕ} {a₁ a₂ : Fin k → M}
    (hab : NbhdIso L (2 ^ n - 1) a₁ a₂) : DuplicatorWins L n a₁ a₂ :=
  hab.duplicatorWins_of_equiv_two_pow (Equiv.refl M) fun _ => NbhdIso.refl _ _

/-- **Sharp Gaifman locality for bounded formulas**
([Libkin, Exercises 4.10 and 4.11][Libkin2004]): in a finite structure over a relational language,
tuples with isomorphic radius-`(2 ^ n - 1)` neighborhoods satisfy the same formulas of quantifier
rank at most `n`. -/
theorem NbhdIso.realize_iff_of_two_pow [L.IsRelational] [Finite M] {n k : ℕ} {a₁ a₂ : Fin k → M}
    (h : NbhdIso L (2 ^ n - 1) a₁ a₂) {φ : L.BoundedFormula Empty k}
    (hφ : quantifierRank φ ≤ n) : φ.Realize default a₁ ↔ φ.Realize default a₂ :=
  h.duplicatorWins_of_two_pow.realize_iff hφ

/-- **Sharp Gaifman locality for formulas with free variables**
([Libkin, Exercises 4.10 and 4.11][Libkin2004]): the form of `NbhdIso.realize_iff_of_two_pow` for
`φ : L.Formula (Fin k)`. -/
theorem NbhdIso.formula_realize_iff_of_two_pow [L.IsRelational] [Finite M] {n k : ℕ}
    {a₁ a₂ : Fin k → M} (h : NbhdIso L (2 ^ n - 1) a₁ a₂) {φ : L.Formula (Fin k)}
    (hφ : quantifierRank φ ≤ n) : φ.Realize a₁ ↔ φ.Realize a₂ :=
  h.duplicatorWins_of_two_pow.formula_realize_iff hφ

/-! ### Sharp Hanf locality (`2 ^ (n - 1) - 1`) -/

/-- **Sharp Hanf locality** ([Libkin, Exercises 4.10 and 4.11][Libkin2004]): over a finite
nonempty structure, tuples that are Hanf-equivalent at radius `2 ^ (n - 1) - 1` are `n`-round
Ehrenfeucht–Fraïssé-equivalent. The language is arbitrary. -/
theorem HanfEquiv.duplicatorWins_of_two_pow [Finite M] [Nonempty M] :
    ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N},
      HanfEquiv L (2 ^ (n - 1) - 1) a b → DuplicatorWins L n a b
  | 0, _, _, _, H => duplicatorWins_zero.2 H.nbhdIso.partialIso
  | m + 1, k, a, b, H => by
    have hP := H.nbhdIso.partialIso
    simp only [Nat.add_sub_cancel] at H
    obtain ⟨f, hf⟩ := hanfEquiv_iff.1 H
    have he : ∀ c', NbhdIso L (2 ^ (m - 1) - 1) (fun _ : Fin 1 => c')
        (fun _ : Fin 1 => f c') := fun c' => by
      obtain ⟨h, Hh⟩ := nbhdIso_iff.1 (hf c')
      have hres := Hh.restrict (x := fun _ : Fin 1 => c') (l := 0) (d := 2 ^ (m - 1) - 1)
        (fun _ => mem_ball_snoc.2 (.inr (mem_ball_self _ 0 0)))
        (by
          have : 2 ^ (m - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (Nat.sub_le m 1)
          omega)
      have hc' : h c' = f c' := by simpa using Hh.map_tuple (Fin.last k)
      exact (by simpa [Function.comp_def, hc'] using hres : IsNbhdIso L _ _ _ h).nbhdIso
    refine duplicatorWins_succ.2 ⟨hP, fun c => ⟨f c, ?_⟩, fun d => ⟨f.symm d, ?_⟩⟩
    · exact (hf c).duplicatorWins_of_equiv_two_pow f he
    · have hd := hf (f.symm d)
      rw [f.apply_symm_apply] at hd
      exact hd.duplicatorWins_of_equiv_two_pow f he

/-- **Sharp Hanf locality for bounded formulas** ([Libkin, Exercises 4.10 and 4.11][Libkin2004]):
over a finite nonempty structure and a relational language, tuples that are Hanf-equivalent at
radius `2 ^ (n - 1) - 1` satisfy the same bounded formulas of quantifier rank at most `n`. -/
theorem HanfEquiv.realize_iff_of_two_pow [L.IsRelational] [Finite M] [Nonempty M] {n k : ℕ}
    {a : Fin k → M} {b : Fin k → N} (h : HanfEquiv L (2 ^ (n - 1) - 1) a b)
    {φ : L.BoundedFormula Empty k} (hφ : quantifierRank φ ≤ n) :
    φ.Realize default a ↔ φ.Realize default b :=
  h.duplicatorWins_of_two_pow.realize_iff hφ

/-- **Sharp Hanf locality for formulas with free variables**
([Libkin, Exercises 4.10 and 4.11][Libkin2004]). -/
theorem HanfEquiv.formula_realize_iff_of_two_pow [L.IsRelational] [Finite M] [Nonempty M]
    {n k : ℕ} {a : Fin k → M} {b : Fin k → N} (h : HanfEquiv L (2 ^ (n - 1) - 1) a b)
    {φ : L.Formula (Fin k)} (hφ : quantifierRank φ ≤ n) :
    φ.Realize a ↔ φ.Realize b :=
  h.duplicatorWins_of_two_pow.formula_realize_iff hφ

/-- **Sharp Hanf locality for sentences** ([Libkin, Exercises 4.10 and 4.11][Libkin2004]): if a
bijection between a finite nonempty structure `M` and `N` matches points with isomorphic
radius-`(2 ^ (n - 1) - 1)` neighborhoods, then `M` and `N` satisfy the same sentences of
quantifier rank at most `n`. -/
theorem realize_sentence_iff_of_nbhdIso_two_pow [L.IsRelational] [Finite M] [Nonempty M] {n : ℕ}
    (e : M ≃ N)
    (he : ∀ c, NbhdIso L (2 ^ (n - 1) - 1) (fun _ : Fin 1 => c) (fun _ : Fin 1 => e c))
    {φ : L.Sentence} (hφ : quantifierRank φ ≤ n) : M ⊨ φ ↔ N ⊨ φ :=
  (hanfEquiv_zero_iff.2 ⟨e, he⟩ : HanfEquiv L _ (default : Fin 0 → M)
    (default : Fin 0 → N)).realize_iff_of_two_pow hφ

end UpperBounds

/-! ### Matching lower bounds over `FirstOrder.Language.graph` -/

section LowerBounds

/-- `loopReach n` has quantifier rank `n` (`quantifierRank_loopReach`) and asserts that a vertex
with a self-loop (`adj x x`) is reachable within `2 ^ n - 1` steps along `distLE`. -/
def loopReach : ℕ → Language.graph.Formula (Fin 1)
  | 0 => adj.formula₂ (Term.var 0) (Term.var 0)
  | k + 1 => (BoundedFormula.relabel (fun i : Fin 2 => ![Sum.inl 0, Sum.inr 0] i) (distLE k) ⊓
      BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) (loopReach k)).ex

@[simp] theorem quantifierRank_loopReach (n : ℕ) : quantifierRank (loopReach n) = n := by
  induction n with
  | zero =>
    simp only [loopReach, Relations.formula₂, Relations.formula,
      quantifierRank_relations_boundedFormula]
  | succ k ih =>
    simp only [loopReach, quantifierRank_ex, quantifierRank_inf, quantifierRank_relabel,
      quantifierRank_distLE, ih, max_self]

theorem realize_loopReach_zero {M : Type*} [Language.graph.Structure M] (x : M) :
    (loopReach 0).Realize ![x] ↔ RelMap adj ![x, x] := by
  fo_simp [loopReach]

theorem realize_loopReach_succ {M : Type*} [Language.graph.Structure M] (k : ℕ) (x : M) :
    (loopReach (k + 1)).Realize ![x] ↔
      ∃ z, (distLE k).Realize ![x, z] ∧ (loopReach k).Realize ![z] := by
  fo_simp [loopReach, Formula.Realize]
  refine exists_congr fun z => and_congr ?_ ?_
  · apply iff_of_eq
    congr 1
    · ext i; fin_cases i <;> rfl
    · exact Subsingleton.elim _ _
  · apply iff_of_eq
    congr 1
    · ext i; fin_cases i; rfl
    · exact Subsingleton.elim _ _

/-! #### Exactness of the Gaifman locality rank `2 ^ n - 1` -/

/-- A simple graph `G` augmented with self-loops on a vertex set `S`. Its Gaifman graph is `G`
itself, since Gaifman adjacency ignores self-loops. -/
private def loopGraphRel {V : Type*} (G : SimpleGraph V) (S : V → Prop) (x y : V) : Prop :=
  G.Adj x y ∨ (x = y ∧ S x)

private theorem gaifmanGraph_loopGraphRel {V : Type*} (G : SimpleGraph V) (S : V → Prop) :
    @gaifmanGraph Language.graph V (relStructure (loopGraphRel G S)) = G := by
  rw [gaifmanGraph_relStructure]
  ext x y
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, (h | ⟨rfl, _⟩) | (h | ⟨rfl, _⟩)⟩
    · exact h
    · exact absurd rfl hne
    · exact h.symm
    · exact absurd rfl hne
  · intro h
    exact ⟨h.ne, .inl (.inl h)⟩

private theorem realize_distLE_loopGraphRel {V : Type*} (G : SimpleGraph V) (S : V → Prop)
    (k : ℕ) (x y : V) :
    (letI := relStructure (loopGraphRel G S); (distLE k).Realize ![x, y]) ↔
      G.edist x y ≤ ((2 ^ k : ℕ) : ℕ∞) := by
  let := relStructure (loopGraphRel G S)
  induction k generalizing x y with
  | zero =>
    rw [realize_distLE_zero, relMap_relStructure, pow_zero, Nat.cast_one,
      SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp only [loopGraphRel]
    tauto
  | succ k ih =>
    have h2 : ((2 ^ (k + 1) : ℕ) : ℕ∞) = ((2 ^ k : ℕ) : ℕ∞) + ((2 ^ k : ℕ) : ℕ∞) := by
      rw [pow_succ, mul_two, Nat.cast_add]
    rw [realize_distLE_succ]
    simp only [ih]
    exact ⟨fun ⟨z, h1, h2'⟩ => SimpleGraph.edist_triangle.trans (h2 ▸ add_le_add h1 h2'),
      fun h => SimpleGraph.exists_edist_le_of_edist_le_add (by rwa [Nat.cast_add, ← h2])⟩

private theorem realize_loopReach_loopGraphRel {V : Type*} (G : SimpleGraph V) (S : V → Prop)
    (n : ℕ) (x : V) :
    (letI := relStructure (loopGraphRel G S); (loopReach n).Realize ![x]) ↔
      ∃ y, S y ∧ G.edist x y ≤ ((2 ^ n - 1 : ℕ) : ℕ∞) := by
  let := relStructure (loopGraphRel G S)
  induction n generalizing x with
  | zero =>
    rw [realize_loopReach_zero, relMap_relStructure]
    simp only [loopGraphRel, G.loopless.irrefl, false_or, true_and, pow_zero, Nat.sub_self,
      Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ => hxy ▸ hy⟩
  | succ k ih =>
    rw [realize_loopReach_succ]
    simp only [realize_distLE_loopGraphRel, ih]
    have hsum : ((2 ^ (k + 1) - 1 : ℕ) : ℕ∞) = ((2 ^ k : ℕ) : ℕ∞) + ((2 ^ k - 1 : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add, two_pow_add_pred_eq]
    constructor
    · rintro ⟨z, hxz, y, hy, hzy⟩
      exact ⟨y, hy, SimpleGraph.edist_triangle.trans (hsum ▸ add_le_add hxz hzy)⟩
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨z, hxz, hzy⟩ := SimpleGraph.exists_edist_le_of_edist_le_add
        (by rwa [Nat.cast_add, ← hsum])
      exact ⟨z, hxz, y, hy, hzy⟩

private theorem relMap_adj_relStructure {V : Type*} (R : V → V → Prop) (t : Fin 2 → V) :
    (letI := relStructure R; RelMap adj t) ↔ R (t 0) (t 1) := by
  let := relStructure R
  have ht : t = ![t 0, t 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [ht]
  rw [relMap_relStructure]

private theorem edist_sum_pathGraph_inl {m : ℕ} (x y : Fin m) :
    (SimpleGraph.pathGraph m ⊕g SimpleGraph.pathGraph m).edist (.inl x) (.inl y) =
      (SimpleGraph.pathGraph m).edist x y := by
  apply le_antisymm
  · exact (SimpleGraph.Embedding.sumInl (G := SimpleGraph.pathGraph m)
      (H := SimpleGraph.pathGraph m)).toHom.edist_le x y
  · let fold : SimpleGraph.pathGraph m ⊕g SimpleGraph.pathGraph m →g SimpleGraph.pathGraph m :=
      { toFun := Sum.elim id id
        map_rel' := fun {a b} hab => by cases a <;> cases b <;> simp_all }
    exact fold.edist_le (.inl x) (.inl y)

private theorem edist_sum_pathGraph_inr {m : ℕ} (x y : Fin m) :
    (SimpleGraph.pathGraph m ⊕g SimpleGraph.pathGraph m).edist (.inr x) (.inr y) =
      (SimpleGraph.pathGraph m).edist x y := by
  apply le_antisymm
  · exact (SimpleGraph.Embedding.sumInr (G := SimpleGraph.pathGraph m)
      (H := SimpleGraph.pathGraph m)).toHom.edist_le x y
  · let fold : SimpleGraph.pathGraph m ⊕g SimpleGraph.pathGraph m →g SimpleGraph.pathGraph m :=
      { toFun := Sum.elim id id
        map_rel' := fun {a b} hab => by cases a <;> cases b <;> simp_all }
    exact fold.edist_le (.inr x) (.inr y)

/-- **Exactness of the Gaifman locality rank `2 ^ n - 1`** ([Libkin, Exercise 4.11][Libkin2004]):
for every `n ≥ 1` and `r < 2 ^ n - 1`, two vertices of a finite `Language.graph`-structure have
isomorphic radius-`r` neighborhoods while `loopReach n` (of quantifier rank `n`) holds of the first
and fails of the second. -/
theorem exists_nbhdIso_realize_loopReach {n r : ℕ} (hn : 1 ≤ n) (hr : r < 2 ^ n - 1) :
    ∃ (M : Type) (_ : Finite M) (_ : Language.graph.Structure M) (a b : Fin 1 → M),
      NbhdIso Language.graph r a b ∧
      (loopReach n).Realize a ∧
      ¬ (loopReach n).Realize b := by
  have hm : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  set m := 2 ^ n
  let P := SimpleGraph.pathGraph m
  let G := P ⊕g P
  let loopPt : Fin m ⊕ Fin m := .inl ⟨m - 1, by omega⟩
  let S : Fin m ⊕ Fin m → Prop := (· = loopPt)
  let _ : Language.graph.Structure (Fin m ⊕ Fin m) := relStructure (loopGraphRel G S)
  let x₀ : Fin m := ⟨0, by omega⟩
  refine ⟨Fin m ⊕ Fin m, inferInstance, inferInstance, fun _ => .inl x₀, fun _ => .inr x₀,
    ?_, ?_, ?_⟩
  · -- `Sum.swap` is a radius-`r` neighborhood isomorphism (`ball (.inl 0) r` avoids `loopPt`).
    have hswap_edist : ∀ u v : Fin m ⊕ Fin m,
        G.edist (Sum.swap u) (Sum.swap v) = G.edist u v := by
      rintro (u | u) (v | v)
      · exact (edist_sum_pathGraph_inr u v).trans (edist_sum_pathGraph_inl u v).symm
      · simp only [Sum.swap_inl, Sum.swap_inr]
        rw [SimpleGraph.edist_comm, SimpleGraph.edist_eq_top_of_not_reachable
          (SimpleGraph.not_reachable_sum_inl_inr _ _), SimpleGraph.edist_eq_top_of_not_reachable
          (SimpleGraph.not_reachable_sum_inl_inr _ _)]
      · simp only [Sum.swap_inl, Sum.swap_inr]
        rw [SimpleGraph.edist_eq_top_of_not_reachable (SimpleGraph.not_reachable_sum_inl_inr _ _),
          SimpleGraph.edist_comm, SimpleGraph.edist_eq_top_of_not_reachable
          (SimpleGraph.not_reachable_sum_inl_inr _ _)]
      · exact (edist_sum_pathGraph_inl u v).trans (edist_sum_pathGraph_inr u v).symm
    have hball : ∀ u : Fin m ⊕ Fin m,
        u ∈ ball Language.graph (fun _ : Fin 1 => (.inl x₀ : Fin m ⊕ Fin m)) r ↔
          Sum.swap u ∈ ball Language.graph (fun _ : Fin 1 => (.inr x₀ : Fin m ⊕ Fin m)) r := by
      intro u
      simp only [mem_ball_const, gaifmanGraph_loopGraphRel]
      change G.edist (.inl x₀) u ≤ r ↔ G.edist (Sum.swap (.inl x₀)) (Sum.swap u) ≤ r
      rw [hswap_edist]
    have hnotLoop : ∀ u ∈ ball Language.graph (fun _ : Fin 1 => (.inl x₀ : Fin m ⊕ Fin m)) r,
        u ≠ loopPt ∧ Sum.swap u ≠ loopPt := by
      intro u hu
      rw [mem_ball_const, gaifmanGraph_loopGraphRel] at hu
      rcases u with j | j
      · refine ⟨fun h => ?_, Sum.inr_ne_inl⟩
        have hj : (j : ℕ) = m - 1 := congrArg Fin.val (Sum.inl.inj h)
        rw [edist_sum_pathGraph_inl, SimpleGraph.edist_pathGraph, Nat.cast_le] at hu
        simp only [x₀] at hu
        omega
      · exact absurd hu (not_le.2 (by
          rw [SimpleGraph.edist_eq_top_of_not_reachable (SimpleGraph.not_reachable_sum_inl_inr _ _)]
          exact ENat.natCast_lt_top r))
    refine IsNbhdIso.nbhdIso (h := Sum.swap)
      ⟨⟨fun u hu => (hball u).1 hu,
        fun _ _ _ _ h => Function.Involutive.injective Sum.swap_swap h,
        fun v hv => ⟨Sum.swap v, (hball _).2 (by simpa only [Sum.swap_swap] using hv),
          Sum.swap_swap v⟩⟩,
        fun _ => rfl, ?_⟩
    intro l R t ht
    cases R
    have h0 := hnotLoop (t 0) (ht 0)
    have h1 := hnotLoop (t 1) (ht 1)
    rw [relMap_adj_relStructure (loopGraphRel G S) (Sum.swap ∘ t),
      relMap_adj_relStructure (loopGraphRel G S) t]
    simp only [Function.comp_apply, loopGraphRel, S, h0.1, h0.2, and_false, or_false]
    rcases t 0 with u₀ | u₀ <;> rcases t 1 with u₁ | u₁ <;>
      simp [G, SimpleGraph.adj_comm]
  · have hvec : (fun _ : Fin 1 => (.inl x₀ : Fin m ⊕ Fin m)) = ![.inl x₀] := by
      ext i; fin_cases i; rfl
    rw [hvec, realize_loopReach_loopGraphRel]
    refine ⟨loopPt, rfl, ?_⟩
    rw [edist_sum_pathGraph_inl, SimpleGraph.edist_pathGraph, Nat.cast_le]
    simp only [x₀, m]
    omega
  · have hvec : (fun _ : Fin 1 => (.inr x₀ : Fin m ⊕ Fin m)) = ![.inr x₀] := by
      ext i; fin_cases i; rfl
    rw [hvec, realize_loopReach_loopGraphRel]
    rintro ⟨y, rfl, hy⟩
    rw [SimpleGraph.edist_comm, SimpleGraph.edist_eq_top_of_not_reachable
      (SimpleGraph.not_reachable_sum_inl_inr _ _)] at hy
    exact absurd hy (not_le.2 (ENat.natCast_lt_top _))

/-- **Optimality of the Gaifman locality rank `2 ^ n - 1`**
([Libkin, Exercise 4.11][Libkin2004]): any radius function `ρ` giving Gaifman locality on finite
`Language.graph`-structures for `1`-tuples and formulas of quantifier rank at most `n` satisfies
`2 ^ n - 1 ≤ ρ n` for every `n`. -/
theorem two_pow_sub_one_le_of_gaifman_radius {ρ : ℕ → ℕ}
    (hρ : ∀ (n : ℕ) (M : Type) [Finite M] [Language.graph.Structure M] (a b : Fin 1 → M)
      (φ : Language.graph.Formula (Fin 1)), quantifierRank φ ≤ n →
      NbhdIso Language.graph (ρ n) a b → (φ.Realize a ↔ φ.Realize b)) (n : ℕ) :
    2 ^ n - 1 ≤ ρ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · by_contra hlt
    obtain ⟨M, _, _, a, b, hab, ha, hb⟩ := exists_nbhdIso_realize_loopReach hn (not_le.1 hlt)
    exact hb ((hρ n M a b (loopReach n) (quantifierRank_loopReach n).le hab).1 ha)

/-! #### Exactness of the Hanf locality rank `2 ^ (n - 1) - 1` -/

/-- `strictEdge` asserts `x₀ ≠ x₁ ∧ adj x₀ x₁` (quantifier rank `0`). -/
private def strictEdge : Language.graph.Formula (Fin 2) :=
  (Term.equal (Term.var 0) (Term.var 1)).not ⊓ adj.formula₂ (Term.var 0) (Term.var 1)

private theorem quantifierRank_strictEdge : quantifierRank strictEdge = 0 := by
  simp only [strictEdge, quantifierRank_inf, quantifierRank_not, Term.equal,
    quantifierRank_bdEqual, Relations.formula₂, Relations.formula,
    quantifierRank_relations_boundedFormula, max_self]

private theorem realize_strictEdge {M : Type*} [Language.graph.Structure M] (x y : M) :
    strictEdge.Realize ![x, y] ↔ x ≠ y ∧ RelMap adj ![x, y] := by
  fo_simp [strictEdge]

/-- `fwdStrict k` has quantifier rank `k + 1` and states on a directed path with self-loops that a
self-loop occurs strictly before `x₀` within at most `2 ^ (k + 1) - 1` forward steps. -/
private def fwdStrict : ℕ → Language.graph.Formula (Fin 1)
  | 0 => (BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) (loopReach 0) ⊓
      BoundedFormula.relabel (fun i : Fin 2 => ![Sum.inr 0, Sum.inl 0] i) strictEdge).ex
  | k + 1 => (BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) (fwdStrict k) ⊓
      BoundedFormula.relabel (fun i : Fin 2 => ![Sum.inr 0, Sum.inl 0] i) (distLE (k + 1))).ex

private theorem quantifierRank_fwdStrict (k : ℕ) : quantifierRank (fwdStrict k) = k + 1 := by
  induction k with
  | zero =>
    simp only [fwdStrict, quantifierRank_ex, quantifierRank_inf, quantifierRank_relabel,
      quantifierRank_loopReach, quantifierRank_strictEdge, max_self]
  | succ k ih =>
    simp only [fwdStrict, quantifierRank_ex, quantifierRank_inf, quantifierRank_relabel, ih,
      quantifierRank_distLE, max_self]

private theorem realize_fwdStrict_zero {M : Type*} [Language.graph.Structure M] (z : M) :
    (fwdStrict 0).Realize ![z] ↔ ∃ u, (loopReach 0).Realize ![u] ∧ strictEdge.Realize ![u, z] := by
  fo_simp [fwdStrict, Formula.Realize]
  refine exists_congr fun u => and_congr ?_ ?_
  · apply iff_of_eq
    congr 1
    · ext i; fin_cases i; rfl
    · exact Subsingleton.elim _ _
  · apply iff_of_eq
    congr 1
    · ext i; fin_cases i <;> rfl
    · exact Subsingleton.elim _ _

private theorem realize_fwdStrict_succ {M : Type*} [Language.graph.Structure M] (k : ℕ) (z : M) :
    (fwdStrict (k + 1)).Realize ![z] ↔
      ∃ w, (fwdStrict k).Realize ![w] ∧ (distLE (k + 1)).Realize ![w, z] := by
  fo_simp [fwdStrict, Formula.Realize]
  refine exists_congr fun w => and_congr ?_ ?_
  · apply iff_of_eq
    congr 1
    · ext i; fin_cases i; rfl
    · exact Subsingleton.elim _ _
  · apply iff_of_eq
    congr 1
    · ext i; fin_cases i <;> rfl
    · exact Subsingleton.elim _ _

/-- `twoLoopSentence k` has quantifier rank `k + 2` and asks for a midpoint `z` satisfying both
`fwdStrict k` and `loopReach (k + 1)`: on a directed path with self-loops, two distinct self-loops
within `2 ^ (k + 2) - 2` forward steps of one another. -/
private def twoLoopSentence (k : ℕ) : Language.graph.Sentence :=
  (BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) (fwdStrict k) ⊓
    BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) (loopReach (k + 1))).ex

private theorem quantifierRank_twoLoopSentence (k : ℕ) :
    quantifierRank (twoLoopSentence k) = k + 2 := by
  simp only [twoLoopSentence, quantifierRank_ex, quantifierRank_inf, quantifierRank_relabel,
    quantifierRank_fwdStrict, quantifierRank_loopReach, max_self]

private theorem realize_twoLoopSentence {M : Type*} [Language.graph.Structure M] (k : ℕ) :
    M ⊨ twoLoopSentence k ↔ ∃ z : M, (fwdStrict k).Realize ![z] ∧
      (loopReach (k + 1)).Realize ![z] := by
  simp only [Sentence.Realize, twoLoopSentence, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, BoundedFormula.realize_relabel, Formula.Realize]
  refine exists_congr fun z => and_congr ?_ ?_ <;>
  · apply iff_of_eq
    congr 1
    · ext i; fin_cases i; rfl
    · exact Subsingleton.elim _ _

/-- Two disjoint directed paths on `Fin m ⊕ Fin m`, augmented with self-loops on `S`. -/
private def dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (u v : Fin m ⊕ Fin m) : Prop :=
  (match u, v with
    | .inl x, .inl y => (x : ℕ) + 1 = (y : ℕ)
    | .inr x, .inr y => (x : ℕ) + 1 = (y : ℕ)
    | _, _ => False) ∨ (u = v ∧ S u)

private theorem gaifmanGraph_dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) :
    @gaifmanGraph Language.graph (Fin m ⊕ Fin m) (relStructure (dirSumPathRel S)) =
      SimpleGraph.pathGraph m ⊕g SimpleGraph.pathGraph m := by
  rw [gaifmanGraph_relStructure]
  ext u v
  rw [SimpleGraph.fromRel_adj]
  rcases u with x | x <;> rcases v with y | y
  · simp only [dirSumPathRel, SimpleGraph.sum_adj_inl, SimpleGraph.pathGraph_adj, ne_eq,
      Sum.inl.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨hne, (h | ⟨h, _⟩) | (h | ⟨h, _⟩)⟩
      · exact .inl h
      · exact absurd h hne
      · exact .inr h
      · exact absurd h.symm hne
    · rintro (h | h)
      · exact ⟨by omega, .inl (.inl h)⟩
      · exact ⟨by omega, .inr (.inl h)⟩
  · simp [dirSumPathRel]
  · rw [SimpleGraph.adj_comm]
    simp [dirSumPathRel]
  · simp only [dirSumPathRel, SimpleGraph.sum_adj_inr, SimpleGraph.pathGraph_adj, ne_eq,
      Sum.inr.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨hne, (h | ⟨h, _⟩) | (h | ⟨h, _⟩)⟩
      · exact .inl h
      · exact absurd h hne
      · exact .inr h
      · exact absurd h.symm hne
    · rintro (h | h)
      · exact ⟨by omega, .inl (.inl h)⟩
      · exact ⟨by omega, .inr (.inl h)⟩

private theorem realize_distLE_dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (k : ℕ) :
    ∀ u v : Fin m ⊕ Fin m,
      (letI := relStructure (dirSumPathRel S); (distLE k).Realize ![u, v]) ↔
        match u, v with
        | .inl x, .inl y => (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + 2 ^ k
        | .inr x, .inr y => (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + 2 ^ k
        | _, _ => False := by
  let := relStructure (dirSumPathRel S)
  induction k with
  | zero =>
    intro u v
    rw [realize_distLE_zero, relMap_relStructure]
    cases u <;> cases v <;>
      simp only [dirSumPathRel, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and,
        or_false, Fin.ext_iff, pow_zero] <;> omega
  | succ k ih =>
    intro u v
    rw [realize_distLE_succ]
    simp only [ih]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
    cases u with
    | inl x =>
      cases v with
      | inl y =>
        constructor
        · rintro ⟨z | z, hz⟩
          · omega
          · exact False.elim hz.1
        · rintro ⟨hxy, hyx⟩
          refine ⟨.inl ⟨min (y : ℕ) ((x : ℕ) + 2 ^ k), by omega⟩, ?_⟩
          dsimp only
          omega
      | inr y =>
        constructor
        · rintro ⟨z | z, hz⟩
          · exact hz.2
          · exact hz.1
        · exact False.elim
    | inr x =>
      cases v with
      | inl y =>
        constructor
        · rintro ⟨z | z, hz⟩
          · exact hz.1
          · exact hz.2
        · exact False.elim
      | inr y =>
        constructor
        · rintro ⟨z | z, hz⟩
          · exact False.elim hz.1
          · omega
        · rintro ⟨hxy, hyx⟩
          refine ⟨.inr ⟨min (y : ℕ) ((x : ℕ) + 2 ^ k), by omega⟩, ?_⟩
          dsimp only
          omega

private theorem realize_loopReach_dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (n : ℕ) :
    ∀ u : Fin m ⊕ Fin m,
      (letI := relStructure (dirSumPathRel S); (loopReach n).Realize ![u]) ↔
        match u with
        | .inl x => ∃ y : Fin m, S (.inl y) ∧ (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + (2 ^ n - 1)
        | .inr x => ∃ y : Fin m, S (.inr y) ∧ (x : ℕ) ≤ (y : ℕ) ∧
            (y : ℕ) ≤ (x : ℕ) + (2 ^ n - 1) := by
  let := relStructure (dirSumPathRel S)
  induction n with
  | zero =>
    intro u
    rw [realize_loopReach_zero, relMap_relStructure]
    cases u with
    | inl x =>
      simp only [dirSumPathRel, Nat.add_eq_left, one_ne_zero, true_and, false_or, pow_zero,
        Nat.sub_self, add_zero]
      exact ⟨fun hx => ⟨x, hx, le_rfl, le_rfl⟩,
        fun ⟨y, hy, h1, h2⟩ => Fin.ext (le_antisymm h1 h2) ▸ hy⟩
    | inr x =>
      simp only [dirSumPathRel, Nat.add_eq_left, one_ne_zero, true_and, false_or, pow_zero,
        Nat.sub_self, add_zero]
      exact ⟨fun hx => ⟨x, hx, le_rfl, le_rfl⟩,
        fun ⟨y, hy, h1, h2⟩ => Fin.ext (le_antisymm h1 h2) ▸ hy⟩
  | succ k ih =>
    intro u
    rw [realize_loopReach_succ]
    simp only [realize_distLE_dirSumPathRel, ih]
    have hsum := two_pow_add_pred_eq k
    cases u with
    | inl x =>
      constructor
      · rintro ⟨z | z, hxz, y, hy, hzy⟩
        · exact ⟨y, hy, by omega, by omega⟩
        · exact False.elim hxz
      · rintro ⟨y, hy, hxy, hyx⟩
        refine ⟨.inl ⟨min (y : ℕ) ((x : ℕ) + 2 ^ k), by omega⟩, ?_, y, hy, ?_⟩ <;>
          (dsimp only; omega)
    | inr x =>
      constructor
      · rintro ⟨z | z, hxz, y, hy, hzy⟩
        · exact False.elim hxz
        · exact ⟨y, hy, by omega, by omega⟩
      · rintro ⟨y, hy, hxy, hyx⟩
        refine ⟨.inr ⟨min (y : ℕ) ((x : ℕ) + 2 ^ k), by omega⟩, ?_, y, hy, ?_⟩ <;>
          (dsimp only; omega)

private theorem realize_fwdStrict_dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (k : ℕ) :
    ∀ w : Fin m ⊕ Fin m,
      (letI := relStructure (dirSumPathRel S); (fwdStrict k).Realize ![w]) ↔
        match w with
        | .inl z => ∃ u : Fin m, S (.inl u) ∧ (u : ℕ) + 1 ≤ (z : ℕ) ∧
            (z : ℕ) ≤ (u : ℕ) + (2 ^ (k + 1) - 1)
        | .inr z => ∃ u : Fin m, S (.inr u) ∧ (u : ℕ) + 1 ≤ (z : ℕ) ∧
            (z : ℕ) ≤ (u : ℕ) + (2 ^ (k + 1) - 1) := by
  let := relStructure (dirSumPathRel S)
  induction k with
  | zero =>
    intro w
    rw [realize_fwdStrict_zero]
    cases w with
    | inl z =>
      constructor
      · rintro ⟨u | u, huL, huE⟩
        · rw [realize_loopReach_zero, relMap_relStructure] at huL
          rw [realize_strictEdge, relMap_relStructure] at huE
          rcases huE with ⟨hne, hadj⟩
          simp only [dirSumPathRel, Nat.add_eq_left, one_ne_zero, true_and, false_or,
            hne, false_and, or_false] at huL hadj
          exact ⟨u, huL, by omega, by omega⟩
        · rw [realize_strictEdge, relMap_relStructure] at huE
          rcases huE with ⟨_, hadj⟩
          simp only [dirSumPathRel, reduceCtorEq, false_and, or_false] at hadj
      · rintro ⟨u, huS, h1, h2⟩
        have huz : (u : ℕ) + 1 = (z : ℕ) := by omega
        refine ⟨.inl u, ?_, ?_⟩
        · rw [realize_loopReach_zero, relMap_relStructure]
          exact .inr ⟨rfl, huS⟩
        · rw [realize_strictEdge, relMap_relStructure]
          exact ⟨fun h => by have := congrArg Fin.val (Sum.inl.inj h); omega, .inl huz⟩
    | inr z =>
      constructor
      · rintro ⟨u | u, huL, huE⟩
        · rw [realize_strictEdge, relMap_relStructure] at huE
          rcases huE with ⟨_, hadj⟩
          simp only [dirSumPathRel, reduceCtorEq, false_and, or_false] at hadj
        · rw [realize_loopReach_zero, relMap_relStructure] at huL
          rw [realize_strictEdge, relMap_relStructure] at huE
          rcases huE with ⟨hne, hadj⟩
          simp only [dirSumPathRel, Nat.add_eq_left, one_ne_zero, true_and, false_or,
            hne, false_and, or_false] at huL hadj
          exact ⟨u, huL, by omega, by omega⟩
      · rintro ⟨u, huS, h1, h2⟩
        have huz : (u : ℕ) + 1 = (z : ℕ) := by omega
        refine ⟨.inr u, ?_, ?_⟩
        · rw [realize_loopReach_zero, relMap_relStructure]
          exact .inr ⟨rfl, huS⟩
        · rw [realize_strictEdge, relMap_relStructure]
          exact ⟨fun h => by have := congrArg Fin.val (Sum.inr.inj h); omega, .inl huz⟩
  | succ k ih =>
    intro w
    rw [realize_fwdStrict_succ]
    simp only [ih, realize_distLE_dirSumPathRel]
    have hsum := two_pow_add_pred_eq (k + 1)
    cases w with
    | inl z =>
      constructor
      · rintro ⟨v | v, hvF, hvz⟩
        · obtain ⟨u, huS, h1, h2⟩ := hvF
          exact ⟨u, huS, by omega, by omega⟩
        · exact False.elim hvz
      · rintro ⟨u, huS, h1, h2⟩
        refine ⟨.inl ⟨min (z : ℕ) ((u : ℕ) + (2 ^ (k + 1) - 1)), by omega⟩,
          ⟨u, huS, ?_, ?_⟩, ?_⟩ <;>
        · dsimp only
          have := @Nat.one_le_two_pow k
          have : 2 ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
          omega
    | inr z =>
      constructor
      · rintro ⟨v | v, hvF, hvz⟩
        · exact False.elim hvz
        · obtain ⟨u, huS, h1, h2⟩ := hvF
          exact ⟨u, huS, by omega, by omega⟩
      · rintro ⟨u, huS, h1, h2⟩
        refine ⟨.inr ⟨min (z : ℕ) ((u : ℕ) + (2 ^ (k + 1) - 1)), by omega⟩,
          ⟨u, huS, ?_, ?_⟩, ?_⟩ <;>
        · dsimp only
          have := @Nat.one_le_two_pow k
          have : 2 ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
          omega

private theorem exists_dirSumPath_hanfEquiv {k d : ℕ} (hd : d < 2 ^ (k + 1) - 1) :
    ∃ (m : ℕ) (_ : 0 < m) (S₁ S₂ : Fin m ⊕ Fin m → Prop),
      @HanfEquiv Language.graph (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
        (relStructure (dirSumPathRel S₁)) (relStructure (dirSumPathRel S₂))
        0 d Fin.elim0 Fin.elim0 ∧
      (letI := relStructure (dirSumPathRel S₁); (Fin m ⊕ Fin m) ⊨ twoLoopSentence k) ∧
      ¬ (letI := relStructure (dirSumPathRel S₂); (Fin m ⊕ Fin m) ⊨ twoLoopSentence k) := by
  have hk1 : 2 ≤ 2 ^ (k + 1) := by
    have := @Nat.one_le_two_pow k
    rw [pow_succ]
    omega
  have hk2 : 4 ≤ 2 ^ (k + 2) := by
    rw [pow_succ _ (k + 1)]
    omega
  set D := 2 ^ (k + 2) - 2
  have hD_2d : 2 * d + 2 ≤ D := by
    have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
    omega
  set m := D + 1
  let S₁ : Fin m ⊕ Fin m → Prop
    | .inl x => (x : ℕ) = 0 ∨ (x : ℕ) = D
    | .inr _ => False
  let S₂ : Fin m ⊕ Fin m → Prop
    | .inl x => (x : ℕ) = 0
    | .inr x => (x : ℕ) = D
  refine ⟨m, by omega, S₁, S₂, ?_, ?_, ?_⟩
  · -- `M ⇆_d N`: swap `.inl x ↔ .inr x` when `D ≤ x + d`, and keep fixed otherwise.
    let coord : Fin m ⊕ Fin m → Fin m := Sum.elim id id
    let fFun : Fin m ⊕ Fin m → Fin m ⊕ Fin m := fun c =>
      if D ≤ (coord c : ℕ) + d then Sum.swap c else c
    have hf_inv : Function.Involutive fFun := fun c => by
      have hcoord : coord (Sum.swap c) = coord c := by cases c <;> rfl
      by_cases h : D ≤ (coord c : ℕ) + d <;> simp [fFun, h, hcoord]
    let f : Fin m ⊕ Fin m ≃ Fin m ⊕ Fin m :=
      { toFun := fFun, invFun := fFun, left_inv := hf_inv, right_inv := hf_inv }
    refine (@hanfEquiv_zero_iff Language.graph _ _ (relStructure (dirSumPathRel S₁))
      (relStructure (dirSumPathRel S₂)) d _ _).2 ⟨f, fun c => ?_⟩
    have mem_ball_iff : ∀ (S : Fin m ⊕ Fin m → Prop) (u v : Fin m ⊕ Fin m),
        v ∈ @ball Language.graph _ (relStructure (dirSumPathRel S)) 1 (fun _ => u) d ↔
          match u, v with
          | .inl x, .inl y => (y : ℕ) ≤ (x : ℕ) + d ∧ (x : ℕ) ≤ (y : ℕ) + d
          | .inr x, .inr y => (y : ℕ) ≤ (x : ℕ) + d ∧ (x : ℕ) ≤ (y : ℕ) + d
          | _, _ => False := by
      intro S u v
      rw [@mem_ball_const, gaifmanGraph_dirSumPathRel]
      cases u with
      | inl x =>
        cases v with
        | inl y =>
          rw [edist_sum_pathGraph_inl, SimpleGraph.edist_pathGraph, Nat.cast_le]
          omega
        | inr y =>
          rw [SimpleGraph.edist_eq_top_of_not_reachable (SimpleGraph.not_reachable_sum_inl_inr _ _)]
          exact iff_of_false (not_le.2 (ENat.natCast_lt_top d)) id
      | inr x =>
        cases v with
        | inl y =>
          rw [SimpleGraph.edist_comm, SimpleGraph.edist_eq_top_of_not_reachable
            (SimpleGraph.not_reachable_sum_inl_inr _ _)]
          exact iff_of_false (not_le.2 (ENat.natCast_lt_top d)) id
        | inr y =>
          rw [edist_sum_pathGraph_inr, SimpleGraph.edist_pathGraph, Nat.cast_le]
          omega
    by_cases hswap : D ≤ (coord c : ℕ) + d
    · -- Near `D`: `f c = Sum.swap c`, and `Sum.swap` is the local isomorphism.
      have hfc : f c = Sum.swap c := by change fFun c = c.swap; simp only [fFun, hswap, ↓reduceIte]
      rw [hfc]
      refine @IsNbhdIso.nbhdIso Language.graph _ _ (relStructure (dirSumPathRel S₁))
        (relStructure (dirSumPathRel S₂)) 1 d _ _ Sum.swap
        (@IsNbhdIso.mk Language.graph _ _ (relStructure (dirSumPathRel S₁))
          (relStructure (dirSumPathRel S₂)) 1 d _ _ Sum.swap
          ⟨fun u hu => ?_, fun _ _ _ _ h => Function.Involutive.injective Sum.swap_swap h,
            fun v hv => ?_⟩ (fun _ => rfl) (fun {l} R t ht => ?_))
      · rw [mem_ball_iff] at hu ⊢
        cases c <;> cases u <;> exact hu
      · refine ⟨Sum.swap v, ?_, Sum.swap_swap v⟩
        rw [mem_ball_iff] at hv ⊢
        cases c <;> cases v <;> exact hv
      · cases R
        have ht0 := (mem_ball_iff S₁ c (t 0)).1 (ht 0)
        have ht1 := (mem_ball_iff S₁ c (t 1)).1 (ht 1)
        rw [relMap_adj_relStructure (dirSumPathRel S₂) (Sum.swap ∘ t),
          relMap_adj_relStructure (dirSumPathRel S₁) t]
        dsimp only [Function.comp_apply]
        cases c with
        | inl x =>
          cases h0 : t 0 with
          | inl y₀ =>
            rw [h0] at ht0
            cases h1 : t 1 with
            | inl y₁ =>
              simp only [coord, Sum.elim_inl, id_eq] at hswap
              have hy0 : (y₀ : ℕ) ≠ 0 := by omega
              simp only [dirSumPathRel, Sum.swap_inl, S₁, S₂, Sum.inl.injEq, Sum.inr.injEq,
                hy0, false_or]
            | inr y₁ => rw [h1] at ht1; exact False.elim ht1
          | inr y₀ => rw [h0] at ht0; exact False.elim ht0
        | inr x =>
          cases h0 : t 0 with
          | inl y₀ => rw [h0] at ht0; exact False.elim ht0
          | inr y₀ =>
            rw [h0] at ht0
            cases h1 : t 1 with
            | inl y₁ => rw [h1] at ht1; exact False.elim ht1
            | inr y₁ =>
              simp only [coord, Sum.elim_inr, id_eq] at hswap
              have hy0 : (y₀ : ℕ) ≠ 0 := by omega
              simp only [dirSumPathRel, Sum.swap_inr, S₁, S₂, Sum.inl.injEq, Sum.inr.injEq,
                hy0, and_false]
    · -- Away from `D`: `f c = c`, and `id` is the local isomorphism.
      have hfc : f c = c := by change fFun c = c; simp only [fFun, hswap, ↓reduceIte]
      rw [hfc]
      refine @IsNbhdIso.nbhdIso Language.graph _ _ (relStructure (dirSumPathRel S₁))
        (relStructure (dirSumPathRel S₂)) 1 d _ _ id
        (@IsNbhdIso.mk Language.graph _ _ (relStructure (dirSumPathRel S₁))
          (relStructure (dirSumPathRel S₂)) 1 d _ _ id
          ⟨fun u hu => ?_, fun _ _ _ _ h => h, fun v hv => ⟨v, ?_, rfl⟩⟩
          (fun _ => rfl) (fun {l} R t ht => ?_))
      · rw [mem_ball_iff] at hu ⊢; exact hu
      · rw [mem_ball_iff] at hv ⊢; exact hv
      · cases R
        have ht0 := (mem_ball_iff S₁ c (t 0)).1 (ht 0)
        have ht1 := (mem_ball_iff S₁ c (t 1)).1 (ht 1)
        rw [relMap_adj_relStructure (dirSumPathRel S₂) (id ∘ t),
          relMap_adj_relStructure (dirSumPathRel S₁) t]
        dsimp only [Function.comp_apply, id_eq]
        cases c with
        | inl x =>
          cases h0 : t 0 with
          | inl y₀ =>
            rw [h0] at ht0
            cases h1 : t 1 with
            | inl y₁ =>
              simp only [coord, Sum.elim_inl, id_eq] at hswap
              have hy0 : (y₀ : ℕ) ≠ D := by omega
              simp only [dirSumPathRel, S₁, S₂, Sum.inl.injEq, hy0, or_false]
            | inr y₁ => rw [h1] at ht1; exact False.elim ht1
          | inr y₀ => rw [h0] at ht0; exact False.elim ht0
        | inr x =>
          cases h0 : t 0 with
          | inl y₀ => rw [h0] at ht0; exact False.elim ht0
          | inr y₀ =>
            rw [h0] at ht0
            cases h1 : t 1 with
            | inl y₁ => rw [h1] at ht1; exact False.elim ht1
            | inr y₁ =>
              simp only [coord, Sum.elim_inr, id_eq] at hswap
              have hy0 : (y₀ : ℕ) ≠ D := by omega
              simp only [dirSumPathRel, S₁, S₂, Sum.inr.injEq, hy0, and_false]
  · -- `M ⊨ twoLoopSentence k`, witnessed at the midpoint `2 ^ (k + 1) - 1`.
    let _ := relStructure (dirSumPathRel S₁)
    rw [realize_twoLoopSentence]
    have hD_split : D = (2 ^ (k + 1) - 1) + (2 ^ (k + 1) - 1) := by
      have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
      omega
    refine ⟨.inl ⟨2 ^ (k + 1) - 1, by omega⟩, ?_, ?_⟩
    · rw [realize_fwdStrict_dirSumPathRel]
      exact ⟨⟨0, by omega⟩, .inl rfl, by dsimp only; omega, by simp⟩
    · rw [realize_loopReach_dirSumPathRel]
      exact ⟨⟨D, by omega⟩, .inr rfl, by dsimp only; omega, by dsimp only; omega⟩
  · -- `¬ N ⊨ twoLoopSentence k`, since each component of `N` has only one self-loop.
    let _ := relStructure (dirSumPathRel S₂)
    rw [realize_twoLoopSentence]
    rintro ⟨z | z, hzF, hzB⟩
    · rw [realize_fwdStrict_dirSumPathRel] at hzF
      rw [realize_loopReach_dirSumPathRel] at hzB
      obtain ⟨u, hu : (u : ℕ) = 0, hu1, _⟩ := hzF
      obtain ⟨y, hy : (y : ℕ) = 0, hy1, _⟩ := hzB
      omega
    · rw [realize_fwdStrict_dirSumPathRel] at hzF
      rw [realize_loopReach_dirSumPathRel] at hzB
      obtain ⟨u, hu : (u : ℕ) = D, hu1, _⟩ := hzF
      obtain ⟨y, hy : (y : ℕ) = D, hy1, _⟩ := hzB
      omega

/-- **Exactness of the Hanf locality rank `2 ^ (n - 1) - 1` for sentences**
([Libkin, Exercise 4.11][Libkin2004]): for every `n ≥ 2` and `d < 2 ^ (n - 1) - 1`, there exist
finite nonempty `Language.graph`-structures `M` and `N` and a sentence `σ` of quantifier rank `n`
such that `M ⇆_d N` while `M ⊨ σ` and `¬ N ⊨ σ`. -/
theorem exists_hanfEquiv_sentence_not_realize_iff {n d : ℕ} (hn : 2 ≤ n)
    (hd : d < 2 ^ (n - 1) - 1) :
    ∃ (M N : Type) (_ : Finite M) (_ : Nonempty M)
      (_ : Language.graph.Structure M) (_ : Language.graph.Structure N)
      (σ : Language.graph.Sentence),
      quantifierRank σ = n ∧
      HanfEquiv Language.graph d (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) ∧
      M ⊨ σ ∧ ¬ N ⊨ σ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨m, hm, S₁, S₂, hHanf, hM₁, hM₂⟩ := exists_dirSumPath_hanfEquiv hd
  exact ⟨Fin m ⊕ Fin m, Fin m ⊕ Fin m, inferInstance, ⟨.inl ⟨0, hm⟩⟩,
    relStructure (dirSumPathRel S₁), relStructure (dirSumPathRel S₂),
    twoLoopSentence k, quantifierRank_twoLoopSentence k, hHanf, hM₁, hM₂⟩

/-! #### Lifting the Hanf sentence lower bound to `1`-tuples via an isolated vertex -/

/-- Extend a binary relation on `V` to `Option V` by leaving `none` loopless and isolated. -/
private def optRel {V : Type*} (R : V → V → Prop) : Option V → Option V → Prop
  | some x, some y => R x y
  | _, _ => False

private theorem gaifmanGraph_optRel_adj {V : Type*} (R : V → V → Prop) (u v : Option V) :
    (@gaifmanGraph Language.graph (Option V) (relStructure (optRel R))).Adj u v ↔
      match u, v with
      | some x, some y => (@gaifmanGraph Language.graph V (relStructure R)).Adj x y
      | _, _ => False := by
  rw [gaifmanGraph_relStructure, gaifmanGraph_relStructure, SimpleGraph.fromRel_adj]
  rcases u with _ | x <;> rcases v with _ | y <;>
    simp [optRel, SimpleGraph.fromRel_adj]

private theorem walk_optRel_to_base {V : Type*} {R : V → V → Prop} {u v : Option V}
    (p : (@gaifmanGraph Language.graph (Option V) (relStructure (optRel R))).Walk u v)
    {x : V} (hux : u = some x) :
    ∃ (y : V) (q : (@gaifmanGraph Language.graph V (relStructure R)).Walk x y),
      v = some y ∧ q.length = p.length := by
  induction p generalizing x with
  | nil => exact ⟨x, .nil, hux, rfl⟩
  | @cons _ w _ h p ih =>
    subst hux
    rw [gaifmanGraph_optRel_adj] at h
    cases w with
    | none => exact False.elim h
    | some z =>
      obtain ⟨y, q, rfl, hlen⟩ := ih rfl
      exact ⟨y, .cons h q, rfl, congrArg (· + 1) hlen⟩

private theorem edist_optRel_none_some {V : Type*} (R : V → V → Prop) (x : V) :
    (@gaifmanGraph Language.graph (Option V)
      (relStructure (optRel R))).edist none (some x) = ⊤ := by
  refine SimpleGraph.edist_eq_top_of_not_reachable fun ⟨p⟩ => ?_
  cases p with
  | @cons _ w _ h _ =>
    rw [gaifmanGraph_optRel_adj] at h
    exact h

private theorem edist_optRel_some_some {V : Type*} (R : V → V → Prop) (x y : V) :
    (@gaifmanGraph Language.graph (Option V) (relStructure (optRel R))).edist (some x) (some y) =
      (@gaifmanGraph Language.graph V (relStructure R)).edist x y := by
  let G := @gaifmanGraph Language.graph V (relStructure R)
  let GO := @gaifmanGraph Language.graph (Option V) (relStructure (optRel R))
  apply le_antisymm
  · let emb : G →g GO :=
      { toFun := some
        map_rel' := fun {a b} h => (gaifmanGraph_optRel_adj R (some a) (some b)).2 h }
    exact emb.edist_le x y
  · by_cases htop : GO.edist (some x) (some y) = ⊤
    · rw [htop]; exact le_top
    · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
      obtain ⟨y', q, hy', hlen⟩ := walk_optRel_to_base p rfl
      cases Option.some.inj hy'
      rw [← hp, ← hlen]
      exact SimpleGraph.edist_le q

private theorem isNbhdIso_optRel_none {V₁ V₂ : Type*} (R₁ : V₁ → V₁ → Prop)
    (R₂ : V₂ → V₂ → Prop) (d : ℕ) {k : ℕ} :
    @IsNbhdIso Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
      (relStructure (optRel R₂)) k d (fun _ => none) (fun _ => none) (fun _ => none) := by
  have hball₁ : ∀ u : Option V₁,
      u ∈ @ball Language.graph (Option V₁) (relStructure (optRel R₁)) k (fun _ => none) d →
        u = none := by
    intro u hu
    obtain ⟨_, hx⟩ := (@mem_ball Language.graph (Option V₁) (relStructure (optRel R₁))
      k (fun _ => none) d u).1 hu
    cases u with
    | none => rfl
    | some x =>
      rw [edist_optRel_none_some] at hx
      exact absurd hx (not_le.2 (ENat.natCast_lt_top d))
  have hball₂ : ∀ v : Option V₂,
      v ∈ @ball Language.graph (Option V₂) (relStructure (optRel R₂)) k (fun _ => none) d ↔
        ∃ _ : Fin k, v = none := by
    intro v
    rw [@mem_ball Language.graph (Option V₂) (relStructure (optRel R₂))]
    refine exists_congr fun _ => ?_
    cases v with
    | none => simp
    | some y =>
      rw [edist_optRel_none_some]
      exact iff_of_false (not_le.2 (ENat.natCast_lt_top d)) (fun h => by cases h)
  refine @IsNbhdIso.mk Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
    (relStructure (optRel R₂)) k d (fun _ => none) (fun _ => none) (fun _ => none)
    ⟨fun u hu => ?_, fun u hu v hv _ => (hball₁ u hu).trans (hball₁ v hv).symm,
      fun v hv => ?_⟩ (fun _ => rfl) (fun {l} R t ht => ?_)
  · obtain ⟨i, _⟩ := (@mem_ball Language.graph (Option V₁) (relStructure (optRel R₁))
      k (fun _ => none) d u).1 hu
    exact (hball₂ none).2 ⟨i, rfl⟩
  · obtain ⟨i, rfl⟩ := (hball₂ v).1 hv
    exact ⟨none, @mem_ball_self Language.graph (Option V₁) (relStructure (optRel R₁))
      k (fun _ => none) d i, rfl⟩
  · cases R
    rw [relMap_adj_relStructure (optRel R₂) ((fun _ => none) ∘ t),
      relMap_adj_relStructure (optRel R₁) t]
    dsimp only [Function.comp_apply]
    rw [hball₁ (t 0) (ht 0)]
    simp [optRel]

private theorem mem_ball_optRel_some {V : Type*} (R : V → V → Prop) (d : ℕ) (c : V)
    (u : Option V) :
    u ∈ @ball Language.graph (Option V) (relStructure (optRel R)) 1 (fun _ => some c) d ↔
      ∃ x ∈ @ball Language.graph V (relStructure R) 1 (fun _ => c) d, u = some x := by
  rw [@mem_ball_const Language.graph (Option V) (relStructure (optRel R))]
  cases u with
  | none =>
    rw [SimpleGraph.edist_comm, edist_optRel_none_some]
    exact iff_of_false (not_le.2 (ENat.natCast_lt_top d)) fun ⟨_, _, heq⟩ => by cases heq
  | some x =>
    rw [edist_optRel_some_some]
    exact ⟨fun hx => ⟨x, (@mem_ball_const Language.graph V (relStructure R) d c x).2 hx, rfl⟩,
      fun ⟨x', hx', heq⟩ => Option.some.inj heq ▸
        (@mem_ball_const Language.graph V (relStructure R) d c x').1 hx'⟩

private theorem nbhdIso_optRel_some {V₁ V₂ : Type*} {R₁ : V₁ → V₁ → Prop}
    {R₂ : V₂ → V₂ → Prop} {d : ℕ} {c₁ : V₁} {c₂ : V₂}
    (hc : @NbhdIso Language.graph V₁ V₂ (relStructure R₁) (relStructure R₂) 1 d
      (fun _ => c₁) (fun _ => c₂)) :
    @NbhdIso Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
      (relStructure (optRel R₂)) 1 d (fun _ => some c₁) (fun _ => some c₂) := by
  obtain ⟨h, ⟨hmaps, hinj, hsurj⟩, htuple, hrel⟩ :=
    (@nbhdIso_iff Language.graph V₁ V₂ (relStructure R₁) (relStructure R₂)
      1 d (fun _ => c₁) (fun _ => c₂)).1 hc
  refine @IsNbhdIso.nbhdIso Language.graph (Option V₁) (Option V₂)
    (relStructure (optRel R₁)) (relStructure (optRel R₂)) 1 d
    (fun _ => some c₁) (fun _ => some c₂) (Option.map h)
    (@IsNbhdIso.mk Language.graph (Option V₁) (Option V₂)
      (relStructure (optRel R₁)) (relStructure (optRel R₂)) 1 d
      (fun _ => some c₁) (fun _ => some c₂) (Option.map h)
      ⟨fun u hu => ?_, fun u hu v hv huv => ?_, fun v hv => ?_⟩
      (fun i => congrArg some (htuple i)) (fun {l} R t ht => ?_))
  · obtain ⟨x, hx, rfl⟩ := (mem_ball_optRel_some R₁ d c₁ u).1 hu
    exact (mem_ball_optRel_some R₂ d c₂ (some (h x))).2 ⟨h x, hmaps hx, rfl⟩
  · obtain ⟨x₁, hx₁, rfl⟩ := (mem_ball_optRel_some R₁ d c₁ u).1 hu
    obtain ⟨x₂, hx₂, rfl⟩ := (mem_ball_optRel_some R₁ d c₁ v).1 hv
    exact congrArg some (hinj hx₁ hx₂ (Option.some.inj huv))
  · obtain ⟨y, hy, rfl⟩ := (mem_ball_optRel_some R₂ d c₂ v).1 hv
    obtain ⟨x, hx, rfl⟩ := hsurj hy
    exact ⟨some x, (mem_ball_optRel_some R₁ d c₁ (some x)).2 ⟨x, hx, rfl⟩, rfl⟩
  · cases R
    obtain ⟨x₀, hx₀, hx₀_eq⟩ := (mem_ball_optRel_some R₁ d c₁ (t 0)).1 (ht 0)
    obtain ⟨x₁, hx₁, hx₁_eq⟩ := (mem_ball_optRel_some R₁ d c₁ (t 1)).1 (ht 1)
    have hiff := hrel adj ![x₀, x₁] (fun i => by fin_cases i <;> assumption)
    rw [relMap_adj_relStructure R₂ (h ∘ ![x₀, x₁]), relMap_adj_relStructure R₁ ![x₀, x₁] ] at hiff
    rw [relMap_adj_relStructure (optRel R₂) (Option.map h ∘ t),
      relMap_adj_relStructure (optRel R₁) t]
    dsimp only [Function.comp_apply] at hiff ⊢
    rw [hx₀_eq, hx₁_eq]
    exact hiff

private theorem hanfEquiv_optRel_none {V₁ V₂ : Type*} {R₁ : V₁ → V₁ → Prop}
    {R₂ : V₂ → V₂ → Prop} {d : ℕ}
    (H : @HanfEquiv Language.graph V₁ V₂ (relStructure R₁) (relStructure R₂) 0 d
      Fin.elim0 Fin.elim0) :
    @HanfEquiv Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
      (relStructure (optRel R₂)) 1 d (fun _ => none) (fun _ => none) := by
  obtain ⟨f, hf⟩ := (@hanfEquiv_zero_iff Language.graph V₁ V₂ (relStructure R₁)
    (relStructure R₂) d Fin.elim0 Fin.elim0).1 H
  refine (@hanfEquiv_iff Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
    (relStructure (optRel R₂)) 1 d (fun _ => none) (fun _ => none)).2 ⟨Equiv.optionCongr f,
      fun w => ?_⟩
  cases w with
  | none =>
    have e1 : (Fin.snoc (fun _ : Fin 1 => (none : Option V₁)) none : Fin 2 → Option V₁) =
        fun _ => none := by ext i; fin_cases i <;> rfl
    have e2 : (Fin.snoc (fun _ : Fin 1 => (none : Option V₂))
        (Equiv.optionCongr f none) : Fin 2 → Option V₂) = fun _ => none := by
      ext i; fin_cases i <;> rfl
    rw [e1, e2]
    exact @IsNbhdIso.nbhdIso Language.graph (Option V₁) (Option V₂)
      (relStructure (optRel R₁)) (relStructure (optRel R₂)) 2 d _ _ _
      (isNbhdIso_optRel_none R₁ R₂ d)
  | some c =>
    obtain ⟨h₂, H₂⟩ := (@nbhdIso_iff Language.graph (Option V₁) (Option V₂)
      (relStructure (optRel R₁)) (relStructure (optRel R₂)) 1 d _ _).1 (nbhdIso_optRel_some (hf c))
    exact (@IsNbhdIso.snoc Language.graph (Option V₁) (Option V₂)
      (relStructure (optRel R₁)) (relStructure (optRel R₂)) 1 d
      (fun _ => none) (fun _ => none) _ _ _ _ (isNbhdIso_optRel_none R₁ R₂ d (k := 1)) H₂)
      (fun _ => by rw [edist_optRel_none_some]; exact ENat.natCast_lt_top _)
      (fun _ => by rw [edist_optRel_none_some]; exact ENat.natCast_lt_top _)

private theorem realize_distLE_optRel {V : Type*} (R : V → V → Prop) (k : ℕ) :
    ∀ u v : Option V,
      (letI := relStructure (optRel R); (distLE k).Realize ![u, v]) ↔
        match u, v with
        | some x, some y => (letI := relStructure R; (distLE k).Realize ![x, y])
        | none, none => True
        | _, _ => False := by
  induction k with
  | zero =>
    intro u v
    rw [@realize_distLE_zero _ (relStructure (optRel R)), relMap_relStructure]
    rcases u with _ | x <;> rcases v with _ | y
    · simp [optRel]
    · simp [optRel]
    · simp [optRel]
    · dsimp only
      rw [@realize_distLE_zero _ (relStructure R), relMap_relStructure]
      simp [optRel]
  | succ k ih =>
    intro u v
    rw [@realize_distLE_succ _ (relStructure (optRel R))]
    simp only [ih]
    rcases u with _ | x <;> rcases v with _ | y
    · exact ⟨fun _ => trivial, fun _ => ⟨none, trivial, trivial⟩⟩
    · exact ⟨fun ⟨z, hz⟩ => by cases z <;> [exact hz.2; exact hz.1], False.elim⟩
    · exact ⟨fun ⟨z, hz⟩ => by cases z <;> [exact hz.1; exact hz.2], False.elim⟩
    · dsimp only
      rw [@realize_distLE_succ _ (relStructure R)]
      constructor
      · rintro ⟨_ | z, hz⟩
        · exact False.elim hz.1
        · exact ⟨z, hz⟩
      · rintro ⟨z, hz⟩
        exact ⟨some z, hz⟩

private theorem realize_loopReach_optRel {V : Type*} (R : V → V → Prop) (n : ℕ) :
    ∀ u : Option V,
      (letI := relStructure (optRel R); (loopReach n).Realize ![u]) ↔
        match u with
        | some x => (letI := relStructure R; (loopReach n).Realize ![x])
        | none => False := by
  induction n with
  | zero =>
    intro u
    rw [@realize_loopReach_zero _ (relStructure (optRel R)), relMap_relStructure]
    cases u with
    | none => simp [optRel]
    | some x =>
      dsimp only
      rw [@realize_loopReach_zero _ (relStructure R), relMap_relStructure]
      rfl
  | succ k ih =>
    intro u
    rw [@realize_loopReach_succ _ (relStructure (optRel R))]
    simp only [realize_distLE_optRel, ih]
    cases u with
    | none =>
      exact ⟨fun ⟨z, hz⟩ => by cases z <;> [exact hz.2; exact hz.1], False.elim⟩
    | some x =>
      dsimp only
      rw [@realize_loopReach_succ _ (relStructure R)]
      exact ⟨fun ⟨z, hz⟩ => by
          cases z with
          | none => exact False.elim hz.1
          | some z => exact ⟨z, hz⟩,
        fun ⟨z, hz⟩ => ⟨some z, hz⟩⟩

private theorem realize_fwdStrict_optRel {V : Type*} (R : V → V → Prop) (k : ℕ) :
    ∀ w : Option V,
      (letI := relStructure (optRel R); (fwdStrict k).Realize ![w]) ↔
        match w with
        | some z => (letI := relStructure R; (fwdStrict k).Realize ![z])
        | none => False := by
  induction k with
  | zero =>
    intro w
    rw [@realize_fwdStrict_zero _ (relStructure (optRel R))]
    simp only [realize_loopReach_optRel]
    cases w with
    | none =>
      refine ⟨fun ⟨u, huL, huE⟩ => ?_, False.elim⟩
      cases u with
      | none => exact huL
      | some x =>
        rw [@realize_strictEdge _ (relStructure (optRel R)), relMap_relStructure] at huE
        exact huE.2
    | some z =>
      dsimp only
      rw [@realize_fwdStrict_zero _ (relStructure R)]
      constructor
      · rintro ⟨_ | x, hxL, hxE⟩
        · exact False.elim hxL
        · rw [@realize_strictEdge _ (relStructure (optRel R)), relMap_relStructure] at hxE
          refine ⟨x, hxL, ?_⟩
          rw [@realize_strictEdge _ (relStructure R), relMap_relStructure]
          exact ⟨fun h => hxE.1 (congrArg some h), hxE.2⟩
      · rintro ⟨x, hxL, hxE⟩
        rw [@realize_strictEdge _ (relStructure R), relMap_relStructure] at hxE
        refine ⟨some x, hxL, ?_⟩
        rw [@realize_strictEdge _ (relStructure (optRel R)), relMap_relStructure]
        exact ⟨fun h => hxE.1 (Option.some.inj h), hxE.2⟩
  | succ k ih =>
    intro w
    rw [@realize_fwdStrict_succ _ (relStructure (optRel R))]
    simp only [ih, realize_distLE_optRel]
    cases w with
    | none =>
      exact ⟨fun ⟨u, hu⟩ => by cases u <;> [exact hu.1; exact hu.2], False.elim⟩
    | some z =>
      dsimp only
      rw [@realize_fwdStrict_succ _ (relStructure R)]
      exact ⟨fun ⟨u, hu⟩ => by
          cases u with
          | none => exact False.elim hu.1
          | some x => exact ⟨x, hu⟩,
        fun ⟨x, hx⟩ => ⟨some x, hx⟩⟩

private theorem realize_twoLoopSentence_optRel {V : Type*} (R : V → V → Prop) (k : ℕ) :
    (letI := relStructure (optRel R); Option V ⊨ twoLoopSentence k) ↔
      (letI := relStructure R; V ⊨ twoLoopSentence k) := by
  rw [@realize_twoLoopSentence _ (relStructure (optRel R))]
  simp only [realize_fwdStrict_optRel, realize_loopReach_optRel]
  rw [@realize_twoLoopSentence _ (relStructure R)]
  exact ⟨fun ⟨w, hw⟩ => by
      cases w with
      | none => exact False.elim hw.1
      | some z => exact ⟨z, hw⟩,
    fun ⟨z, hz⟩ => ⟨some z, hz⟩⟩

/-- **Exactness of the Hanf locality rank `2 ^ (n - 1) - 1` for `1`-tuples**
([Libkin, Exercise 4.11][Libkin2004]): for every `n ≥ 2` and `d < 2 ^ (n - 1) - 1`, there exist
finite nonempty `Language.graph`-structures `M` and `N`, `1`-tuples `a` and `b`, and a formula `φ`
of quantifier rank `n` such that `(M, a) ⇆_d (N, b)` while `φ` holds of `a` and fails of `b`. -/
theorem exists_hanfEquiv_formula_not_realize_iff {n d : ℕ} (hn : 2 ≤ n)
    (hd : d < 2 ^ (n - 1) - 1) :
    ∃ (M N : Type) (_ : Finite M) (_ : Nonempty M)
      (_ : Language.graph.Structure M) (_ : Language.graph.Structure N)
      (a : Fin 1 → M) (b : Fin 1 → N) (φ : Language.graph.Formula (Fin 1)),
      quantifierRank φ = n ∧
      HanfEquiv Language.graph d a b ∧
      φ.Realize a ∧ ¬ φ.Realize b := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨m, _, S₁, S₂, hHanf, hM₁, hM₂⟩ := exists_dirSumPath_hanfEquiv hd
  refine ⟨Option (Fin m ⊕ Fin m), Option (Fin m ⊕ Fin m), inferInstance, ⟨none⟩,
    relStructure (optRel (dirSumPathRel S₁)), relStructure (optRel (dirSumPathRel S₂)),
    fun _ => none, fun _ => none, Formula.relabel Empty.elim (twoLoopSentence k),
    ?_, hanfEquiv_optRel_none hHanf, ?_, ?_⟩
  · rw [quantifierRank_formula_relabel, quantifierRank_twoLoopSentence]
  · rw [@Formula.realize_relabel _ _ (relStructure (optRel (dirSumPathRel S₁)))]
    have h1 := (realize_twoLoopSentence_optRel (dirSumPathRel S₁) k).2 hM₁
    simp only [Sentence.Realize] at h1
    rwa [Subsingleton.elim ((fun _ : Fin 1 => none) ∘ Empty.elim) _]
  · rw [@Formula.realize_relabel _ _ (relStructure (optRel (dirSumPathRel S₂)))]
    intro h
    refine hM₂ ((realize_twoLoopSentence_optRel (dirSumPathRel S₂) k).1 ?_)
    simp only [Sentence.Realize]
    rwa [Subsingleton.elim ((fun _ : Fin 1 => none) ∘ Empty.elim) _] at h

/-- **Optimality of the Hanf locality rank `2 ^ (n - 1) - 1` for sentences**
([Libkin, Exercise 4.11][Libkin2004]): any radius function `ρ` giving Hanf locality on finite
nonempty `Language.graph`-structures for sentences of quantifier rank at most `n` satisfies
`2 ^ (n - 1) - 1 ≤ ρ n` for every `n`. -/
theorem two_pow_pred_sub_one_le_of_hanf_sentence_radius {ρ : ℕ → ℕ}
    (hρ : ∀ (n : ℕ) (M N : Type) [Finite M] [Nonempty M]
      [Language.graph.Structure M] [Language.graph.Structure N]
      (σ : Language.graph.Sentence), quantifierRank σ ≤ n →
      HanfEquiv Language.graph (ρ n) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) →
      (M ⊨ σ ↔ N ⊨ σ)) (n : ℕ) :
    2 ^ (n - 1) - 1 ≤ ρ n := by
  by_cases hn : 2 ≤ n
  · by_contra hlt
    obtain ⟨M, N, _, _, _, _, σ, hσ, hMN, hM, hN⟩ :=
      exists_hanfEquiv_sentence_not_realize_iff hn (not_le.1 hlt)
    exact hN ((hρ n M N σ hσ.le hMN).1 hM)
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp

/-- **Optimality of the Hanf locality rank `2 ^ (n - 1) - 1` for `1`-tuples**
([Libkin, Exercise 4.11][Libkin2004]): any radius function `ρ` giving Hanf locality on finite
nonempty `Language.graph`-structures for `1`-tuples and formulas of quantifier rank at most `n`
satisfies `2 ^ (n - 1) - 1 ≤ ρ n` for every `n`. -/
theorem two_pow_pred_sub_one_le_of_hanf_radius {ρ : ℕ → ℕ}
    (hρ : ∀ (n : ℕ) (M N : Type) [Finite M] [Nonempty M]
      [Language.graph.Structure M] [Language.graph.Structure N]
      (a : Fin 1 → M) (b : Fin 1 → N) (φ : Language.graph.Formula (Fin 1)),
      quantifierRank φ ≤ n → HanfEquiv Language.graph (ρ n) a b →
      (φ.Realize a ↔ φ.Realize b)) (n : ℕ) :
    2 ^ (n - 1) - 1 ≤ ρ n := by
  by_cases hn : 2 ≤ n
  · by_contra hlt
    obtain ⟨M, N, _, _, _, _, a, b, φ, hφ, hab, ha, hb⟩ :=
      exists_hanfEquiv_formula_not_realize_iff hn (not_le.1 hlt)
    exact hb ((hρ n M N a b φ hφ.le hab).1 ha)
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp

end LowerBounds

end Cslib.Logic.FO.Locality
