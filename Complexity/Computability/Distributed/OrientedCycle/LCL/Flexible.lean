/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Distributed.OrientedCycle.ColeVishkin
public import Complexity.Computability.Distributed.OrientedCycle.LCL.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Flexible LCL problems on oriented cycles in `O(log* n)` rounds

If the LCL problem `R` has a flexible state `q` with flexibility `K` (closed walks `q ⇝ q` of every
length `m ≥ K`, `LCL.IsFlexible`), then a deterministic LOCAL algorithm solves `R` on every
oriented `n`-cycle with `n ≥ K` and identifiers `{0, …, n - 1}` in
`(K - 1) (⌈log* n / 2⌉ + 2 · 3 ^ (K - 1) + 2) + 1` rounds (`LCL.IsFlexible.exists_solvesLCL`).
This is [Chang, Studený and Suomela][ChangStudenySuomela2023], Thm 6.11, credited there (§3.3)
to [Brandt et al.][BrandtEtAl2017]. With the lower bound of
`Complexity.Computability.Distributed.OrientedCycle.LCL.Basic`, a flexible problem without a loop
has round complexity `Θ(log* n)` (`LCL.IsFlexible.exists_solvesLCL_and_logStar_le`), the middle
row of their Table 1 for directed cycles.

The algorithm follows their outline. A distance-`K` anchoring (their Def. 3.8) splits the cycle
into fragments of bounded length, the anchors are labelled `q`, and each fragment is filled with a
closed walk `q ⇝ q` of the right length. Let `k = K - 1`.

1. **Distance-`k` colouring** (`LCL.distColoring`). For each step `j + 1 ≤ k`, the nodes
   `u, u + (j + 1), u + 2 (j + 1), …` form a sequence with distinct identifiers, which the
   Cole–Vishkin algorithm of [Cole and Vishkin][ColeVishkin1986] 3-colours
   (`LCL.threeColoringRule`). The `k` colours are combined as base-3 digits. Nodes at distance
   `1, …, k` then get different colours below `3 ^ k`. This takes `k (s + 3)` rounds when
   `log* n ≤ 2s`.
2. **Anchors** (`LCL.anchorRule`). A node is an anchor if its colour is smaller than all colours
   within distance `k`. Anchors are more than `k` apart, and following decreasing colours shows that
   every node has an anchor at most `2k (3 ^ k - 1)` steps behind it. This takes `k` rounds.
3. **Filling** (`LCL.fillRule`). A node at distance `d` after the previous anchor, in a gap of
   length `g ≥ k + 1` between consecutive anchors, outputs the `d`-th label of a fixed closed walk
   of length `g`. This takes `2k (3 ^ k - 1) + 1` rounds.

The literature describes the anchoring through a maximal independent set in a power of the
cycle. The local minima of a distance colouring used here give such a set directly.

The leading coefficient `(K - 1) / 2` of `log* n` is not tight. The lower bound has `½`, and
closing the gap is left open.

## Main definitions

* `Cslib.Distributed.OrientedCycle.LCL.distColoring`: distance-`k` colouring from a 3-colouring
  rule.
* `Cslib.Distributed.OrientedCycle.LCL.anchorRule`: strict local minima within distance `k`.
* `Cslib.Distributed.OrientedCycle.LCL.fillRule`: filling the gaps between anchors.
* `Cslib.Distributed.OrientedCycle.LCL.flexibleRule`: the three stages composed.

## Main results

* `Cslib.Distributed.OrientedCycle.LCL.distColoring_ne`: nodes at distance `1, …, k` get different
  colours.
* `Cslib.Distributed.OrientedCycle.LCL.anchorRule_exists_sub`: every node has a nearby anchor
  behind it.
* `Cslib.Distributed.OrientedCycle.LCL.fillRule_isSolution`: filling solves `R`.
* `Cslib.Distributed.OrientedCycle.LCL.IsFlexible.exists_solvesLCL`: the `O(log* n)` upper bound.
* `Cslib.Distributed.OrientedCycle.LCL.IsFlexible.exists_solvesLCL_and_logStar_le`: `Θ(log* n)`
  for flexible problems without a loop.

## References

* [Y.-J. Chang, J. Studený and J. Suomela, *Distributed graph problems through an
  automata-theoretic lens*][ChangStudenySuomela2023]
* [S. Brandt et al., *LCL problems on grids*][BrandtEtAl2017]
* [R. Cole and U. Vishkin, *Deterministic coin tossing with applications to optimal parallel list
  ranking*][ColeVishkin1986]
-/

public section

namespace Cslib.Distributed.OrientedCycle.LCL

/-! ### Distance colourings -/

/-- The Cole–Vishkin algorithm `fastThreeColoring s` as a rule of radius `s + 3`. -/
def threeColoringRule (s : ℕ) : LocalRule ℕ ℕ (s + 3) :=
  (fastThreeColoring s).toLocalRule (s + 3)

/-- On the infinite oriented path, `threeColoringRule s` 3-colours every proper colouring with
colours below `N` when `log* N ≤ 2s`: node `0` and node `1` get different colours below `3`. -/
theorem threeColoringRule_toFun {s N : ℕ} {y : ℤ → ℕ} (hy : ∀ i, y i ≠ y (i + 1))
    (hN : ∀ i, y i < N) (hs : Nat.logStar N ≤ 2 * s) :
    (threeColoringRule s).toFun y ≠ (threeColoringRule s).toFun (fun i => y (i + 1)) ∧
      (threeColoringRule s).toFun y < 3 := by
  have h := fastThreeColoring_run (n := 0) (x := y) hy hN hs le_rfl
  have h0 : window (n := 0) y 0 = y := by
    funext j
    simp only [window]
    rw [zero_add]
    rfl
  have h1 : window (n := 0) y 1 = fun i => y (i + 1) := by
    funext j
    simp only [window]
    rw [add_comm]
    rfl
  have e0 := (fastThreeColoring s).run_eq_apply (n := 0) y (s + 3) 0
  have e1 := (fastThreeColoring s).run_eq_apply (n := 0) y (s + 3) 1
  simp only [LocalRule.apply, h0, h1] at e0 e1
  refine ⟨?_, ?_⟩
  · have := h.1 0
    rw [e0, zero_add, e1] at this
    exact this
  · have := h.2 0
    rw [e0] at this
    exact this

/-- A distance-`k` colouring from a rule `T`: the `j`-th base-3 digit of the colour of `u` is the
colour `T` gives (capped at `2`) to the progression `u, u + (j + 1), u + 2 (j + 1), …`. -/
def distColoring {r : ℕ} (T : LocalRule ℕ ℕ r) (k : ℕ) : LocalRule ℕ ℕ (k * r) where
  toFun w := (finFunctionFinEquiv (m := 3) (n := k) fun j : Fin k =>
    Fin.clamp (T.toFun fun i => w (((j : ℕ) + 1 : ℕ) * i)) 2 : ℕ)
  dependsOn w w' h := by
    have : ∀ j : Fin k, T.toFun (fun i => w (((j : ℕ) + 1 : ℕ) * i)) =
        T.toFun (fun i => w' (((j : ℕ) + 1 : ℕ) * i)) := fun j =>
      T.toFun_congr fun i hi₁ hi₂ => by
        have hj : (j : ℤ) + 1 ≤ k := by have := j.isLt; omega
        have h1 : 0 ≤ ((k : ℤ) - ((j : ℤ) + 1)) * ((r : ℤ) - i) :=
          mul_nonneg (by omega) (by omega)
        have h2 : 0 ≤ ((k : ℤ) - ((j : ℤ) + 1)) * ((r : ℤ) + i) :=
          mul_nonneg (by omega) (by omega)
        refine h _ ⟨?_, ?_⟩ <;> push_cast <;> nlinarith
    simp only [this]

theorem distColoring_lt {r : ℕ} (T : LocalRule ℕ ℕ r) (k : ℕ) {n : ℕ} (x : ZMod n → ℕ)
    (v : ZMod n) : (distColoring T k).apply x v < 3 ^ k :=
  Fin.isLt _

/-- **Distance-`k` colouring.** On a cycle with more than `k` nodes and distinct identifiers below
`n`, `distColoring (threeColoringRule s) k` gives different colours to nodes at distance
`1, …, k` when `log* n ≤ 2s`. -/
theorem distColoring_ne {s k n : ℕ} (hkn : k < n) {x : ZMod n → ℕ} (hx : Function.Injective x)
    (hxn : ∀ v, x v < n) (hs : Nat.logStar n ≤ 2 * s) (u : ZMod n) {m : ℕ} (hm₁ : 1 ≤ m)
    (hm₂ : m ≤ k) :
    (distColoring (threeColoringRule s) k).apply x u ≠
      (distColoring (threeColoringRule s) k).apply x (u + m) := by
  intro h
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h' := finFunctionFinEquiv.injective (Fin.val_injective h)
  have hj := congrArg Fin.val (congrFun h' ⟨j, by omega⟩)
  -- the progression with step `j + 1` from `u`
  set y : ℤ → ℕ := fun i => x (u + ((j + 1 : ℕ) : ℤ) * i) with hy
  have hstep : (((j + 1 : ℕ) : ℤ) : ZMod n) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have hyp : ∀ i, y i ≠ y (i + 1) := fun i hi => by
    have := hx hi
    apply hstep
    push_cast at this ⊢
    linear_combination -this
  have hyN : ∀ i, y i < n := fun i => hxn _
  have hT := threeColoringRule_toFun hyp hyN hs
  have hT' := threeColoringRule_toFun (fun i => hyp (i + 1)) (fun i => hyN (i + 1)) hs
  have e0 : (fun i => window x u (((j + 1 : ℕ) : ℤ) * i)) = y := by
    funext i
    simp only [window, hy]
    congr 1
    push_cast
    ring
  have e1 : (fun i => window x (u + ((j + 1 : ℕ) : ZMod n)) (((j + 1 : ℕ) : ℤ) * i)) =
      fun i => y (i + 1) := by
    funext i
    simp only [window, hy]
    congr 1
    push_cast
    ring
  simp only [Fin.coe_clamp] at hj
  rw [e0, e1] at hj
  have := hT.1
  have := hT.2
  have := hT'.2
  omega

/-! ### Anchors -/

/-- A node is an anchor if its colour is smaller than every colour within distance `k`. -/
@[expose] def anchorRule (k : ℕ) : LocalRule ℕ Bool k where
  toFun w := decide (∀ m < k, w 0 < w ((m : ℤ) + 1) ∧ w 0 < w (-((m : ℤ) + 1)))
  dependsOn w w' h := by
    have h0 := h 0 ⟨by omega, by omega⟩
    have hp : ∀ m < k, w ((m : ℤ) + 1) = w' ((m : ℤ) + 1) := fun m hm =>
      h _ ⟨by omega, by omega⟩
    have hm : ∀ m < k, w (-((m : ℤ) + 1)) = w' (-((m : ℤ) + 1)) := fun m hm =>
      h _ ⟨by omega, by omega⟩
    simp only [h0]
    congr 1
    apply propext
    exact forall₂_congr fun m hmk => by rw [hp m hmk, hm m hmk]

theorem anchorRule_apply {k n : ℕ} (c : ZMod n → ℕ) (u : ZMod n) :
    (anchorRule k).apply c u = true ↔
      ∀ m < k, c u < c (u + (m + 1)) ∧ c u < c (u - (m + 1)) := by
  simp only [LocalRule.apply, anchorRule, window, decide_eq_true_eq, Int.cast_zero, add_zero]
  push_cast
  simp only [sub_eq_add_neg]

/-- Anchors are more than `k` apart. -/
theorem anchorRule_spacing {k n : ℕ} (c : ZMod n → ℕ) (u : ZMod n)
    (hu : (anchorRule k).apply c u = true) {m : ℕ} (hm : m < k) :
    (anchorRule k).apply c (u + (m + 1)) = false := by
  rw [← Bool.not_eq_true, anchorRule_apply]
  intro h
  have h1 := ((anchorRule_apply c u).1 hu m hm).1
  have h2 := (h m hm).2
  rw [add_sub_cancel_right] at h2
  omega

/-- Following decreasing colours from a node of colour at most `N` reaches an anchor within
distance `k N`. -/
theorem anchorRule_exists {k n : ℕ} {c : ZMod n → ℕ}
    (hc : ∀ u : ZMod n, ∀ m < k, c u ≠ c (u + (m + 1))) :
    ∀ N : ℕ, ∀ v, c v ≤ N → ∃ e : ℤ, |e| ≤ k * N ∧ (anchorRule k).apply c (v + e) = true := by
  intro N
  induction N with
  | zero =>
    intro v hv
    refine ⟨0, by simp, ?_⟩
    rw [Int.cast_zero, add_zero, anchorRule_apply]
    intro m hm
    have h1 := hc v m hm
    have h2 := hc (v - (m + 1)) m hm
    rw [sub_add_cancel] at h2
    omega
  | succ N ih =>
    intro v hv
    by_cases ha : (anchorRule k).apply c v = true
    · exact ⟨0, by rw [abs_zero]; exact_mod_cast Nat.zero_le _, by rwa [Int.cast_zero, add_zero]⟩
    rw [anchorRule_apply] at ha
    push Not at ha
    obtain ⟨m, hm, hle⟩ := ha
    have hkN : (k : ℤ) * ((N + 1 : ℕ) : ℤ) = k * N + k := by push_cast; ring
    have hmk : (m : ℤ) + 1 ≤ k := by omega
    by_cases h1 : c v < c (v + (m + 1))
    · have h2 := hc (v - (m + 1)) m hm
      rw [sub_add_cancel] at h2
      have h3 := hle h1
      obtain ⟨e, he, hae⟩ := ih (v - (m + 1)) (by omega)
      refine ⟨e - (m + 1), ?_, ?_⟩
      · rw [abs_le] at he ⊢
        constructor <;> linarith [he.1, he.2]
      · convert hae using 2
        push_cast
        ring
    · have h2 := hc v m hm
      obtain ⟨e, he, hae⟩ := ih (v + (m + 1)) (by omega)
      refine ⟨e + (m + 1), ?_, ?_⟩
      · rw [abs_le] at he ⊢
        constructor <;> linarith [he.1, he.2]
      · convert hae using 2
        push_cast
        ring

/-- For a distance-`k` colouring with colours below `C`, every node has an anchor at most
`2k (C - 1)` steps behind it. -/
theorem anchorRule_exists_sub {k n C : ℕ} {c : ZMod n → ℕ}
    (hc : ∀ u : ZMod n, ∀ m < k, c u ≠ c (u + (m + 1))) (hC : ∀ u, c u < C) (v : ZMod n) :
    ∃ d ≤ 2 * (k * (C - 1)), (anchorRule k).apply c (v - d) = true := by
  obtain ⟨e, he, hae⟩ := anchorRule_exists hc (C - 1) (v - ((k * (C - 1) : ℕ) : ZMod n))
    (by have := hC (v - ((k * (C - 1) : ℕ) : ZMod n)); omega)
  have he' : |e| ≤ ((k * (C - 1) : ℕ) : ℤ) := by rwa [Nat.cast_mul]
  rw [abs_le] at he'
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = ((k * (C - 1) : ℕ) : ℤ) - e :=
    ⟨_, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨d, by omega, ?_⟩
  have hv : v - (d : ZMod n) = v - ((k * (C - 1) : ℕ) : ZMod n) + (e : ZMod n) := by
    rw [← Int.cast_natCast (R := ZMod n) d, hd]
    push_cast
    ring
  rw [hv]
  exact hae

/-! ### Filling -/

/-- The least `i < m` with `p i`, or `m` if there is none. -/
private abbrev firstTrue (p : ℕ → Bool) (m : ℕ) : ℕ := (List.range m).findIdx p

private theorem firstTrue_min (p : ℕ → Bool) (m : ℕ) : ∀ i < firstTrue p m, p i = false := by
  intro i hi
  have := List.not_of_lt_findIdx hi
  simpa only [List.getElem_range] using this

private theorem firstTrue_lt (p : ℕ → Bool) (m : ℕ) (h : ∃ i < m, p i = true) :
    firstTrue p m < m := by
  obtain ⟨i, hi, hpi⟩ := h
  have := List.findIdx_lt_length_of_exists (xs := List.range m) (p := p)
    ⟨i, List.mem_range.2 hi, hpi⟩
  simpa only [List.length_range] using this

private theorem firstTrue_spec (p : ℕ → Bool) (m : ℕ) (h : ∃ i < m, p i = true) :
    p (firstTrue p m) = true := by
  have hlt := firstTrue_lt p m h
  have := List.findIdx_getElem (xs := List.range m) (p := p) (w := by simpa using hlt)
  simpa only [List.getElem_range] using this

private theorem firstTrue_eq (p : ℕ → Bool) (m : ℕ) {i : ℕ} (hi : p i = true)
    (hlt : ∀ j < i, p j = false) (hex : ∃ j < m, p j = true) : firstTrue p m = i := by
  rcases lt_trichotomy (firstTrue p m) i with h | h | h
  · have := hlt _ h
    rw [firstTrue_spec p m hex] at this
    exact absurd this (by decide)
  · exact h
  · have := firstTrue_min p m i h
    rw [hi] at this
    exact absurd this (by decide)

private theorem firstTrue_congr {p p' : ℕ → Bool} {m : ℕ} (h : ∀ i < m, p i = p' i) :
    firstTrue p m = firstTrue p' m := by
  have key : ∀ xs : List ℕ, (∀ i ∈ xs, p i = p' i) → xs.findIdx p = xs.findIdx p' := by
    intro xs hxs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.findIdx_cons, hxs x List.mem_cons_self,
        ih fun y hy => hxs y (List.mem_cons_of_mem _ hy)]
  exact key _ fun i hi => h i (List.mem_range.1 hi)

/-- Filling between anchors with closed walks `W g` of length `g`. A node looks back at most `D`
steps for the previous anchor, at distance `d`, and ahead at most `D + 1` steps for the next one,
in a gap of length `g`. It outputs `W g d`. -/
@[expose] def fillRule {L : Type*} (W : ℕ → ℕ → L) (D : ℕ) : LocalRule Bool L (D + 1) where
  toFun w := W ((List.range (D + 1)).findIdx (fun i : ℕ => w (-(i : ℤ))) +
      (List.range (D + 1)).findIdx (fun i : ℕ => w ((i : ℤ) + 1)) + 1)
    ((List.range (D + 1)).findIdx (fun i : ℕ => w (-(i : ℤ))))
  dependsOn w w' h := by
    have e1 : firstTrue (fun i => w (-(i : ℤ))) (D + 1) =
        firstTrue (fun i => w' (-(i : ℤ))) (D + 1) :=
      firstTrue_congr fun i hi => h _ ⟨by omega, by omega⟩
    have e2 : firstTrue (fun i => w ((i : ℤ) + 1)) (D + 1) =
        firstTrue (fun i => w' ((i : ℤ) + 1)) (D + 1) :=
      firstTrue_congr fun i hi => h _ ⟨by omega, by omega⟩
    simp only [e1, e2]

/-- **Filling.** If anchors are more than `k` apart and every node has an anchor at most `D` steps
behind it, and `W m` is a closed walk `q ⇝ q` of length `m` for every `m ≥ k + 1`, then filling the
gaps solves `R`. -/
theorem fillRule_isSolution {L : Type*} {R : L → L → Prop} {q : L} {W : ℕ → ℕ → L} {k : ℕ}
    (hW0 : ∀ m, k + 1 ≤ m → W m 0 = q) (hWm : ∀ m, k + 1 ≤ m → W m m = q)
    (hWR : ∀ m, k + 1 ≤ m → ∀ i < m, R (W m i) (W m (i + 1)))
    {D n : ℕ} {a : ZMod n → Bool}
    (hspace : ∀ u, a u = true → ∀ m < k, a (u + (m + 1)) = false)
    (hcov : ∀ v, ∃ d ≤ D, a (v - d) = true) :
    IsSolution R ((fillRule W D).apply a) := by
  set P : ZMod n → ℕ := fun v => firstTrue (fun i : ℕ => a (v - (i : ZMod n))) (D + 1) with hP
  set Q : ZMod n → ℕ := fun v => firstTrue (fun i : ℕ => a (v + ((i : ZMod n) + 1))) (D + 1)
    with hQ
  have happly : ∀ v, (fillRule W D).apply a v = W (P v + Q v + 1) (P v) := by
    intro v
    have e1 : (fun i : ℕ => window a v (-(i : ℤ))) = fun i : ℕ => a (v - (i : ZMod n)) := by
      funext i
      simp only [window]
      push_cast
      rw [sub_eq_add_neg]
    have e2 : (fun i : ℕ => window a v ((i : ℤ) + 1)) =
        fun i : ℕ => a (v + ((i : ZMod n) + 1)) := by
      funext i
      simp only [window]
      push_cast
      rfl
    simp only [LocalRule.apply, fillRule, e1, e2, hP, hQ]
  have hPspec : ∀ v, P v ≤ D ∧ a (v - P v) = true ∧ ∀ i < P v, a (v - i) = false := by
    intro v
    obtain ⟨d, hd, had⟩ := hcov v
    have hex : ∃ i < D + 1, a (v - (i : ZMod n)) = true := ⟨d, by omega, had⟩
    have hlt : P v < D + 1 := firstTrue_lt _ _ hex
    exact ⟨by omega, firstTrue_spec _ _ hex, firstTrue_min _ _⟩
  have hQspec : ∀ v, Q v ≤ D ∧ a (v + (Q v + 1)) = true ∧
      ∀ i < Q v, a (v + (i + 1)) = false := by
    intro v
    obtain ⟨d, hd, had⟩ := hcov (v + (D + 1))
    have hex : ∃ i < D + 1, a (v + ((i : ZMod n) + 1)) = true := ⟨D - d, by omega, by
      convert had using 2
      rw [Nat.cast_sub hd]
      ring⟩
    have hlt : Q v < D + 1 := firstTrue_lt _ _ hex
    exact ⟨by omega, firstTrue_spec _ _ hex, firstTrue_min _ _⟩
  have hgap : ∀ v, k + 1 ≤ P v + Q v + 1 := by
    intro v
    by_contra hlt
    have h1 := hspace (v - P v) (hPspec v).2.1 (P v + Q v) (by omega)
    have h2 := (hQspec v).2.1
    have : v - (P v : ZMod n) + ((P v + Q v : ℕ) + 1) = v + (Q v + 1) := by
      push_cast
      ring
    rw [this, h2] at h1
    exact absurd h1 (by decide)
  intro v
  rw [happly v, happly (v + 1)]
  by_cases hnext : a (v + 1) = true
  · have hQ0 : Q v = 0 := by
      by_contra h0
      have := (hQspec v).2.2 0 (by omega)
      rw [Nat.cast_zero, zero_add, hnext] at this
      exact absurd this (by decide)
    have hnext0 : a (v + 1 - ((0 : ℕ) : ZMod n)) = true := by
      rwa [Nat.cast_zero, sub_zero]
    have hP1 : P (v + 1) = 0 :=
      firstTrue_eq _ _ hnext0 (fun j hj => absurd hj (Nat.not_lt_zero _)) ⟨0, by omega, hnext0⟩
    have hg1 := hgap (v + 1)
    have hg := hgap v
    rw [hQ0, hP1] at *
    simp only [add_zero, zero_add] at hg hg1 ⊢
    rw [hW0 _ (by omega), ← hWm (P v + 1) (by omega)]
    exact hWR _ (by omega) _ (by omega)
  · have hnext' : a (v + 1) = false := by simpa using hnext
    have hQpos : 1 ≤ Q v := by
      by_contra h0
      have h2 := (hQspec v).2.1
      rw [show Q v = 0 by omega, Nat.cast_zero, zero_add, hnext'] at h2
      exact absurd h2 (by decide)
    have hP1 : P (v + 1) = P v + 1 := by
      obtain ⟨d, hd, had⟩ := hcov (v + 1)
      refine firstTrue_eq _ _ ?_ ?_ ⟨d, by omega, had⟩
      · show a (v + 1 - ((P v + 1 : ℕ) : ZMod n)) = true
        have := (hPspec v).2.1
        convert this using 2
        push_cast
        ring
      · intro j hj
        show a (v + 1 - (j : ZMod n)) = false
        rcases j with _ | j
        · simpa using hnext'
        · have := (hPspec v).2.2 j (by omega)
          convert this using 2
          push_cast
          ring
    have hQ1 : Q (v + 1) = Q v - 1 := by
      have hspec := hQspec v
      have hi : a (v + 1 + (((Q v - 1 : ℕ) : ZMod n) + 1)) = true := by
        convert hspec.2.1 using 2
        rw [Nat.cast_sub hQpos]
        push_cast
        ring
      refine firstTrue_eq _ _ hi ?_ ⟨Q v - 1, by omega, hi⟩
      intro j hj
      show a (v + 1 + ((j : ZMod n) + 1)) = false
      have := hspec.2.2 (j + 1) (by omega)
      convert this using 2
      push_cast
      ring
    rw [hP1, hQ1, show P v + 1 + (Q v - 1) + 1 = P v + Q v + 1 by omega]
    exact hWR _ (hgap v) _ (by omega)

/-! ### The algorithm -/

/-- The radius of `flexibleRule W k s`, equal to `k (s + 2 · 3 ^ k + 2) + 1`
(`flexibleRadius_eq`). -/
abbrev flexibleRadius (k s : ℕ) : ℕ := k * (s + 3) + k + (2 * (k * (3 ^ k - 1)) + 1)

theorem flexibleRadius_eq (k s : ℕ) : flexibleRadius k s = k * (s + 2 * 3 ^ k + 2) + 1 := by
  have h : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by decide)
  obtain ⟨c, hc⟩ : ∃ c, 3 ^ k = c + 1 := ⟨3 ^ k - 1, by omega⟩
  simp only [flexibleRadius, hc, Nat.add_sub_cancel]
  ring

/-- Distance-`k` colouring, anchors and filling with the closed walks `W`. -/
def flexibleRule {L : Type*} (W : ℕ → ℕ → L) (k s : ℕ) : LocalRule ℕ L (flexibleRadius k s) :=
  (fillRule W (2 * (k * (3 ^ k - 1)))).comp
    ((anchorRule k).comp (distColoring (threeColoringRule s) k))

theorem flexibleRule_isSolution {L : Type*} {R : L → L → Prop} {q : L} {W : ℕ → ℕ → L}
    {k s n : ℕ} (hW0 : ∀ m, k + 1 ≤ m → W m 0 = q) (hWm : ∀ m, k + 1 ≤ m → W m m = q)
    (hWR : ∀ m, k + 1 ≤ m → ∀ i < m, R (W m i) (W m (i + 1))) (hkn : k < n)
    (hs : Nat.logStar n ≤ 2 * s) {x : ZMod n → ℕ} (hx : Function.Injective x)
    (hxn : ∀ v, x v < n) : IsSolution R ((flexibleRule W k s).apply x) := by
  rw [flexibleRule, LocalRule.apply_comp, LocalRule.apply_comp]
  set c := (distColoring (threeColoringRule s) k).apply x
  have hc : ∀ u : ZMod n, ∀ m < k, c u ≠ c (u + (m + 1)) := fun u m hm => by
    have := distColoring_ne hkn hx hxn hs u (m := m + 1) (by omega) (by omega)
    push_cast at this
    exact this
  have hC : ∀ u, c u < 3 ^ k := distColoring_lt _ _ x
  exact fillRule_isSolution hW0 hWm hWR (fun u hu m hm => anchorRule_spacing c u hu hm)
    (anchorRule_exists_sub hc hC)

private theorem IsFlexible.exists_walks {L : Type*} {R : L → L → Prop} {q : L} {K : ℕ}
    (h : IsFlexible R q K) : ∃ W : ℕ → ℕ → L, ∀ m, K ≤ m →
      W m 0 = q ∧ W m m = q ∧ ∀ i < m, R (W m i) (W m (i + 1)) := by
  classical
  refine ⟨fun m => if hm : K ≤ m then (h m hm).choose else fun _ => q, fun m hm => ?_⟩
  simp only [dite_eq_left hm]
  exact (h m hm).choose_spec

/-- **Flexible problems in `O(log* n)` rounds** ([Chang, Studený and
Suomela][ChangStudenySuomela2023], Thm 6.11; [Brandt et al.][BrandtEtAl2017]). If `q` is a flexible
state of `R` with flexibility `K`, then for `n ≥ K` and `log* n ≤ 2s` some algorithm solves `R` on
every oriented `n`-cycle with identifiers `{0, …, n - 1}` in
`(K - 1) (s + 2 · 3 ^ (K - 1) + 2) + 1` rounds. -/
theorem IsFlexible.exists_solvesLCL {L : Type*} {R : L → L → Prop} {q : L} {K : ℕ}
    (h : IsFlexible R q K) {n s : ℕ} (hKn : K ≤ n) (hs : Nat.logStar n ≤ 2 * s) :
    ∃ A : Algorithm ℕ (ℤ → ℕ) L,
      A.SolvesLCL R n ((K - 1) * (s + 2 * 3 ^ (K - 1) + 2) + 1) := by
  obtain ⟨W, hW⟩ := h.exists_walks
  refine ⟨(flexibleRule W (K - 1) s).toAlgorithm, fun x hx hxn => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (hxn 0) (Nat.not_lt_zero _)
  have : (flexibleRule W (K - 1) s).toAlgorithm.run x ((K - 1) * (s + 2 * 3 ^ (K - 1) + 2) + 1) =
      (flexibleRule W (K - 1) s).apply x := by
    rw [← flexibleRadius_eq]
    exact funext fun v => LocalRule.toAlgorithm_run _ x v
  rw [this]
  exact flexibleRule_isSolution (fun m hm => (hW m (by omega)).1)
    (fun m hm => (hW m (by omega)).2.1) (fun m hm => (hW m (by omega)).2.2) (by omega) hs hx hxn

/-- **`Θ(log* n)` for flexible problems without a loop** ([Chang, Studený and
Suomela][ChangStudenySuomela2023], Table 1). If `q` is a flexible state of `R` with flexibility
`K` and `R` has no loop, then for `n ≥ K` some algorithm solves `R` on the oriented `n`-cycle in
`(K - 1) (⌈log* n / 2⌉ + 2 · 3 ^ (K - 1) + 2) + 1` rounds, and every `t`-round algorithm solving
`R` has `log* n ≤ 2t + log* |L|`. -/
theorem IsFlexible.exists_solvesLCL_and_logStar_le {L : Type*} [Fintype L] {R : L → L → Prop}
    {q : L} {K : ℕ} (h : IsFlexible R q K) (hR : ∀ a, ¬R a a) {n : ℕ} (hKn : K ≤ n) :
    (∃ (S : Type) (A : Algorithm ℕ S L),
      A.SolvesLCL R n ((K - 1) * ((Nat.logStar n + 1) / 2 + 2 * 3 ^ (K - 1) + 2) + 1)) ∧
      ∀ {S : Type*} (A : Algorithm ℕ S L) (t : ℕ), A.SolvesLCL R n t →
        Nat.logStar n ≤ 2 * t + Nat.logStar (Fintype.card L) :=
  ⟨⟨_, h.exists_solvesLCL hKn (by omega)⟩, fun _ _ hA => hA.logStar_le hR⟩

end Cslib.Distributed.OrientedCycle.LCL
