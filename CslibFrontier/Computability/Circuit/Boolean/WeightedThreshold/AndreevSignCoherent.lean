/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevLowerBound
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.DepthTwoInputs
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.SplitCounting
public import CslibFrontier.Foundations.Combinatorics.CubeSplitting
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Analysis.SpecialFunctions.FiberCount
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import Mathlib.Algebra.Ring.GeomSum

/-!
# Sign-coherent depth-two threshold circuits for Andreev's function need near-quadratic size

Andreev's function `andreev b m` on `n = N + b m` bits, `N = 2 ^ b`, reads a truth table
`x : BitString N` at the parities of `b` address blocks of `m` bits. A bottom gate is
*sign-coherent* (`IsSignCoherent`) if inside every address block its weights are all `≥ 0` or all
`≤ 0`. Every depth-two weighted threshold circuit computing `andreev b m` whose `G` bottom gates are
sign-coherent satisfies, with
`D₀ = max 0 (N - b - 1 - log₂ (G + 1)) / (b + log₂ (G + 1))` (`andreevCubeSplitBound`),
$$m ^ b D₀ ≤ (m ^ b - (m - 1) ^ b) G, \qquad m D₀ ≤ b G,$$
hence `G ≥ min (N ^ 2) (m (N - 3 b - 1) / (3 b ^ 2))`, and `G ≥ N (N - 3 b - 1) / (3 b ^ 3)` when
`b m = N`. This is `Ω(n ^ 2 / log ^ 3 n)`.

## The cube restriction

For `s : Fin b → ℕ`, `andreevCubePoint b m x s` has table `x` and, in block `j`, ones exactly at
the first `s j` positions. A **cube** is `q : Fin b → Fin m`; the `2 ^ b` points `q + z`,
`z : BitString b`, form the subcube in which the positions `q j` are live
(`andreevCubePoint_add`). On it, `andreev` reads `x` at `(q mod 2) + z`, so the restricted function
determines the table (`eq_of_andreev_andreevCubePoint_add`).

* **Lemma 14** (`two_pow_mul_andreevCubeSplitBound_le`): for every circuit of depth at most two
  computing `andreev b m` and every cube `q`, the number of bottom gates splitting `q`
  (`andreevCubeSplitCount`) averages at least `D₀` over the tables. A restricted circuit is
  described by its splitting gates, their nonconstant threshold shifts and one level set of a
  fixed form (`card_image_eval_embedUpdate_le`); the entropy step is the fiber-counting form of
  Jensen's inequality (`Real.card_mul_log_sub_le_of_card_fiber_le`). No sign condition is needed.
* **Lemma 15** (`card_cubes_mem_circuitSplitGates_le`): along each cube, a sign-coherent gate is a
  threshold of a separable unate form, so for every table it splits at most `m ^ b - (m - 1) ^ b`
  cubes (`Cslib.Combinatorics.card_cubeSplits_le`).
* **Theorem 13** (`pow_mul_andreevCubeSplitBound_le`, `mul_andreevCubeSplitBound_le`,
  `min_le_card_outputBottomGates`, `le_card_outputBottomGates_of_balanced`): sum Lemma 14 over
  all cubes and compare with Lemma 15. For circuits built with `depthTwoInputs`, whose `G` is the
  constructor's bottom-gate count, `pow_mul_andreevCubeSplitBound_le_of_depthTwoInputs` and
  `le_of_balanced_of_depthTwoInputs` take sign coherence of each `argWeight (bottom j) (args j)`.

The circuits are arbitrary `Circuit signature n 1` of depth at most two, so the top gate may read
inputs; only the bottom gates (`outputBottomGates c 0`) are required to be sign-coherent.

## References

* Christian Reitwiessner, *Depth-Two Threshold Circuits for Andreev's Function* (preprint,
  November 2026), Theorem 13 and Lemmas 14 and 15.
* [Impagliazzo, Paturi and Saks, Lemma 2.1][ImpagliazzoPaturiSaks1997] for the classical fact
  behind Lemma 15.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset

variable {b m : ℕ}

/-! ### The cube restriction -/

/-- The input with truth table `x` and, in every address block `j`, ones exactly at the first
`s j` positions. -/
def andreevCubePoint (b m : ℕ) (x : BitString (2 ^ b)) (s : Fin b → ℕ) :
    BitString (2 ^ b + b * m) :=
  Fin.append x fun v => decide (((finProdFinEquiv.symm v).2 : ℕ) < s (finProdFinEquiv.symm v).1)

@[simp] theorem andreevCubePoint_andreevTableIndex (x : BitString (2 ^ b)) (s : Fin b → ℕ)
    (idx : Fin (2 ^ b)) : andreevCubePoint b m x s (andreevTableIndex b m idx) = x idx :=
  Fin.append_left _ _ _

@[simp] theorem andreevCubePoint_andreevBlockVar (x : BitString (2 ^ b)) (s : Fin b → ℕ)
    (j : Fin b) (t : Fin m) :
    andreevCubePoint b m x s (andreevBlockVar b m j t) = decide ((t : ℕ) < s j) := by
  rw [andreevCubePoint, andreevBlockVar, Fin.append_right, Equiv.symm_apply_apply]

/-- **The cube restriction**: the points `q + z` of the cube `q` are the embedded updates of the
live positions `q j` of the corner `q`. -/
theorem andreevCubePoint_add (x : BitString (2 ^ b)) (q : Fin b → Fin m) (z : BitString b) :
    andreevCubePoint b m x (fun j => q j + (z j).toNat) =
      embedUpdate (andreevLiveVar b m q) (andreevCubePoint b m x fun j => q j) z := by
  funext i
  refine Fin.addCases (fun idx => ?_) (fun v => ?_) i
  · change andreevCubePoint b m x _ (andreevTableIndex b m idx) = embedUpdate _ _ _
      (andreevTableIndex b m idx)
    rw [embedUpdate_of_notMem _ _ (andreevTableIndex_notMem_image_andreevLiveVar b m q idx)]
    simp
  · obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective v
    change andreevCubePoint b m x _ (andreevBlockVar b m j t) = embedUpdate _ _ _
      (andreevBlockVar b m j t)
    by_cases ht : t = q j
    · subst ht
      change _ = embedUpdate _ _ _ (andreevLiveVar b m q j)
      rw [embedUpdate_emb (andreevLiveVar_injective b m q), andreevCubePoint_andreevBlockVar]
      cases z j <;> simp
    · have hnot : andreevBlockVar b m j t ∉ univ.image (andreevLiveVar b m q) := by
        simp only [mem_image, mem_univ, true_and, not_exists]
        intro j' hj'
        obtain ⟨rfl, h⟩ := andreevBlockVar_joint_injective b m j' (q j') j t hj'
        exact ht h.symm
      rw [embedUpdate_of_notMem _ _ hnot, andreevCubePoint_andreevBlockVar,
        andreevCubePoint_andreevBlockVar]
      have : (t : ℕ) ≠ q j := fun h => ht (Fin.ext h)
      cases z j <;> simp; omega

/-- At a cube point, Andreev's function reads the table at the block counts modulo two. -/
theorem andreev_andreevCubePoint (x : BitString (2 ^ b)) {s : Fin b → ℕ} (hs : ∀ j, s j ≤ m) :
    andreev b m (andreevCubePoint b m x s) =
      x (BitString.equivFin b fun j => decide (s j % 2 = 1)) := by
  rw [andreev_eq_table_parities, andreevTable, andreevCubePoint_andreevTableIndex]
  congr 2
  funext j
  simp only [andreevParities, parity, parityOn, andreevCubePoint_andreevBlockVar,
    decide_eq_true_eq]
  rw [Fin.card_filter_val_lt, min_eq_right (hs j)]

/-- On a cube, the values of Andreev's function determine the table. -/
theorem eq_of_andreev_andreevCubePoint_add {x x' : BitString (2 ^ b)} (q : Fin b → Fin m)
    (h : ∀ z : BitString b, andreev b m (andreevCubePoint b m x fun j => q j + (z j).toNat) =
      andreev b m (andreevCubePoint b m x' fun j => q j + (z j).toNat)) : x = x' := by
  have hs (z : BitString b) (j : Fin b) : q j + (z j).toNat ≤ m := by
    cases z j <;> simp [Nat.succ_le_of_lt (q j).isLt, (q j).isLt.le]
  funext idx
  set p := (BitString.equivFin b).symm idx
  let z : BitString b := fun j => p j ^^ decide ((q j : ℕ) % 2 = 1)
  have hpar (a : ℕ) (c : Bool) : decide ((a + (c ^^ decide (a % 2 = 1)).toNat) % 2 = 1) = c := by
    cases c <;> rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> simp [ha] <;> omega
  have hz : (fun j => decide ((q j + (z j).toNat) % 2 = 1)) = p := funext fun j => hpar _ _
  have := h z
  rwa [andreev_andreevCubePoint x (hs z), andreev_andreevCubePoint x' (hs z), hz,
    Equiv.apply_symm_apply] at this

/-! ### Lemma 14: many gates split each cube -/

/-- The number of bottom gates of `c` that split the cube `q` for the table `x`, i.e. are not
constant on the points `q + z`. -/
noncomputable def andreevCubeSplitCount (c : Circuit signature (2 ^ b + b * m) 1)
    (q : Fin b → Fin m) (x : BitString (2 ^ b)) : ℕ :=
  circuitUnforcedConstCount c 0 (univ.image (andreevLiveVar b m q))
    (andreevCubePoint b m x fun j => q j)

/-- The splitting bound `D₀ = max 0 (2 ^ b - b - 1 - log₂ (G + 1)) / (b + log₂ (G + 1))` of
Lemma 14, for `G` bottom gates. -/
noncomputable def andreevCubeSplitBound (b G : ℕ) : ℝ :=
  max 0 ((2 : ℝ) ^ b - b - 1 - Real.logb 2 (G + 1)) / (b + Real.logb 2 (G + 1))

theorem andreevCubeSplitBound_nonneg (b G : ℕ) : 0 ≤ andreevCubeSplitBound b G :=
  div_nonneg (le_max_left _ _) (add_nonneg (Nat.cast_nonneg _)
    (Real.logb_nonneg one_lt_two (by have : (0 : ℝ) ≤ G := Nat.cast_nonneg G; linarith)))

/-- `D₀` is antitone in the number of gates. -/
theorem andreevCubeSplitBound_anti (b : ℕ) {G G' : ℕ} (h : G ≤ G') :
    andreevCubeSplitBound b G' ≤ andreevCubeSplitBound b G := by
  have hG : (G : ℝ) ≤ G' := Nat.cast_le.mpr h
  have hlog : Real.logb 2 (G + 1) ≤ Real.logb 2 (G' + 1) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.logb 2 (G + 1) :=
    Real.logb_nonneg one_lt_two (by have : (0 : ℝ) ≤ G := Nat.cast_nonneg G; linarith)
  have hlog0' : 0 ≤ Real.logb 2 (G' + 1) := hlog0.trans hlog
  unfold andreevCubeSplitBound
  rcases le_or_gt ((2 : ℝ) ^ b - b - 1 - Real.logb 2 (G' + 1)) 0 with hn | hn
  · rw [max_eq_left hn, zero_div]
    exact div_nonneg (le_max_left _ _) (by positivity)
  · have hb : (1 : ℝ) ≤ b := by
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp at hn; linarith
      · exact Nat.one_le_cast.mpr hb
    exact div_le_div₀ (le_max_left _ _) (max_le_max le_rfl (by linarith)) (by linarith)
      (by linarith)

/-- At most all bottom gates split a cube. -/
theorem andreevCubeSplitCount_le (c : Circuit signature (2 ^ b + b * m) 1) (q : Fin b → Fin m)
    (x : BitString (2 ^ b)) : andreevCubeSplitCount c q x ≤ #(outputBottomGates c 0) := by
  rw [andreevCubeSplitCount, ← card_circuitSplitGates]
  exact card_le_card (circuitSplitGates_subset c 0 _ _)

/-- **Counting tables by splitting gates**: for a circuit of depth at most two computing
`andreev b m` with `G` bottom gates, at most `C(G, D) (2 ^ b - 1) ^ D (2 ^ b + 1)` tables have
exactly `D` bottom gates splitting the cube `q`. -/
theorem card_andreevCubeSplitCount_eq_le (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev b m)))
    (q : Fin b → Fin m) (D : ℕ) :
    #{x : BitString (2 ^ b) | andreevCubeSplitCount c q x = D} ≤
      (#(outputBottomGates c 0)).choose D * (2 ^ b - 1) ^ D * (2 ^ b + 1) := by
  classical
  set F := univ.filter fun x : BitString (2 ^ b) => andreevCubeSplitCount c q x = D
  let P : BitString (2 ^ b) → BitString (2 ^ b + b * m) := fun x =>
    andreevCubePoint b m x fun j => q j
  let f : BitString (2 ^ b + b * m) → BitString b → Bool := fun w u =>
    c.eval interpretation (embedUpdate (andreevLiveVar b m q) w u) 0
  have hcomp' (w : BitString (2 ^ b + b * m)) : c.eval interpretation w 0 = andreev b m w :=
    congrFun (hcomp w) 0
  have hinj : Set.InjOn (f ∘ P) ↑F := fun x _ x' _ h =>
    eq_of_andreev_andreevCubePoint_add q fun z => by
      have := congrFun h z
      simp only [Function.comp_apply, f, P] at this
      rwa [← andreevCubePoint_add, ← andreevCubePoint_add, hcomp', hcomp'] at this
  calc #F = #(F.image (f ∘ P)) := (card_image_of_injOn hinj).symm
    _ = #((F.image P).image f) := by rw [image_image]
    _ ≤ (#(outputBottomGates c 0)).choose D * (2 ^ Fintype.card (Fin b) - 1) ^ D *
          (2 ^ Fintype.card (Fin b) + 1) :=
        card_image_eval_embedUpdate_le c hd 0 (andreevLiveVar_injective b m q) _ D fun w hw => by
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hw
          exact (mem_filter.mp hx).2
    _ = _ := by rw [Fintype.card_fin]

/-- **Lemma 14, multiplicative form**: for a circuit of depth at most two computing `andreev b m`
with `G` bottom gates and every cube `q`,
`2 ^ N (N - b - 1 - log₂ (G + 1)) ≤ (b + log₂ (G + 1)) ∑ₓ d_q(x)`, `N = 2 ^ b`. -/
theorem two_pow_mul_sub_le_mul_sum_andreevCubeSplitCount (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev b m)))
    (q : Fin b → Fin m) :
    (2 : ℝ) ^ 2 ^ b * ((2 : ℝ) ^ b - b - 1 - Real.logb 2 (#(outputBottomGates c 0) + 1)) ≤
      (b + Real.logb 2 (#(outputBottomGates c 0) + 1)) *
        ∑ x : BitString (2 ^ b), (andreevCubeSplitCount c q x : ℝ) := by
  set G := #(outputBottomGates c 0)
  have hfiber (D : ℕ) (_ : D ≤ G) :
      (#{x : BitString (2 ^ b) | andreevCubeSplitCount c q x = D} : ℝ) ≤
        (2 : ℝ) ^ (b + 1) * (((G : ℝ) + 1) * 2 ^ b) ^ D := by
    have hnat : #{x : BitString (2 ^ b) | andreevCubeSplitCount c q x = D} ≤
        2 ^ (b + 1) * ((G + 1) * 2 ^ b) ^ D := by
      refine (card_andreevCubeSplitCount_eq_le c hd hcomp q D).trans ?_
      calc G.choose D * (2 ^ b - 1) ^ D * (2 ^ b + 1)
          ≤ (G + 1) ^ D * (2 ^ b) ^ D * 2 ^ (b + 1) := by
            gcongr
            · exact (Nat.choose_le_pow G D).trans (Nat.pow_le_pow_left (Nat.le_succ G) D)
            · exact Nat.sub_le _ _
            · rw [pow_succ]; have := Nat.one_le_two_pow (n := b); omega
        _ = 2 ^ (b + 1) * ((G + 1) * 2 ^ b) ^ D := by rw [mul_pow]; ring
    exact_mod_cast hnat
  have key := Real.card_mul_log_sub_le_of_card_fiber_le (andreevCubeSplitCount c q)
    (andreevCubeSplitCount_le c q) (by positivity)
    (by have : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ one_le_two
        nlinarith [(Nat.cast_nonneg G : (0 : ℝ) ≤ G)]) hfiber
  have hcard : (Fintype.card (BitString (2 ^ b)) : ℝ) = (2 : ℝ) ^ 2 ^ b := by
    simp [BitString]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hG1 : (0 : ℝ) < G + 1 := by positivity
  rw [hcard, Real.log_pow, Real.log_pow, Real.log_mul hG1.ne' (by positivity), Real.log_pow]
    at key
  have hlogb : Real.log ((G : ℝ) + 1) = Real.logb 2 (G + 1) * Real.log 2 := by
    rw [← Real.log_div_log, div_mul_cancel₀ _ hl2.ne']
  rw [hlogb] at key
  push_cast at key
  refine le_of_mul_le_mul_right ?_ hl2
  nlinarith [key]

/-- **Lemma 14** (Reitwiessner, Lemma 14): for a circuit of depth at most two computing
`andreev b m` with `G` bottom gates and every cube `q`, the number of splitting bottom gates
averages at least `D₀ = andreevCubeSplitBound b G` over the `2 ^ N` tables. -/
theorem two_pow_mul_andreevCubeSplitBound_le (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev b m)))
    (q : Fin b → Fin m) :
    (2 : ℝ) ^ 2 ^ b * andreevCubeSplitBound b #(outputBottomGates c 0) ≤
      ∑ x : BitString (2 ^ b), (andreevCubeSplitCount c q x : ℝ) := by
  set G := #(outputBottomGates c 0)
  have hsum : 0 ≤ ∑ x : BitString (2 ^ b), (andreevCubeSplitCount c q x : ℝ) :=
    sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hL : 0 ≤ Real.logb 2 ((G : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by have : (0 : ℝ) ≤ G := Nat.cast_nonneg G; linarith)
  have hmain := two_pow_mul_sub_le_mul_sum_andreevCubeSplitCount c hd hcomp q
  unfold andreevCubeSplitBound
  rcases le_or_gt ((2 : ℝ) ^ b - b - 1 - Real.logb 2 (G + 1)) 0 with hn | hn
  · rw [max_eq_left hn, zero_div, mul_zero]; exact hsum
  · have hb : (1 : ℝ) ≤ b := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · subst h0; simp at hn; linarith
      · exact Nat.one_le_cast.mpr h0
    rw [max_eq_right hn.le, ← mul_div_assoc, div_le_iff₀ (by linarith), mul_comm _ (_ + _)]
    exact hmain

/-! ### Lemma 15: a sign-coherent gate splits few cubes -/

/-- A gate's weighted sum at a cube point splits into its table part and the block forms
`s ↦ ∑ t < s, a (andreevBlockVar b m j t)`. -/
theorem sum_mul_andreevCubePoint (a : Fin (2 ^ b + b * m) → ℝ) (x : BitString (2 ^ b))
    (s : Fin b → ℕ) :
    ∑ i, a i * (andreevCubePoint b m x s i).toNat =
      (∑ idx, a (andreevTableIndex b m idx) * (x idx).toNat) +
        ∑ j, ∑ t : Fin m, if (t : ℕ) < s j then a (andreevBlockVar b m j t) else 0 := by
  rw [Fin.sum_univ_add]
  congr 1
  · exact sum_congr rfl fun idx _ => by
      rw [show Fin.castAdd (b * m) idx = andreevTableIndex b m idx from rfl,
        andreevCubePoint_andreevTableIndex]
  · rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun j _ => sum_congr rfl fun t _ => ?_
    rw [show Fin.natAdd (2 ^ b) (finProdFinEquiv (j, t)) = andreevBlockVar b m j t from rfl,
      andreevCubePoint_andreevBlockVar]
    split_ifs with h <;> simp [h]

/-- The block form of a block with nonnegative weights is monotone, and with nonpositive weights
antitone. -/
theorem monotone_or_antitone_blockForm {a : Fin (2 ^ b + b * m) → ℝ}
    (ha : IsSignCoherent (andreevBlockVar b m) a) (j : Fin b) :
    Monotone (fun s : ℕ => ∑ t : Fin m, if (t : ℕ) < s then a (andreevBlockVar b m j t) else 0) ∨
      Antitone fun s : ℕ =>
        ∑ t : Fin m, if (t : ℕ) < s then a (andreevBlockVar b m j t) else 0 := by
  rcases ha j with h | h
  · refine Or.inl fun s s' hs => sum_le_sum fun t _ => ?_
    have := h t
    split_ifs <;> first | exact le_rfl | exact this | omega
  · refine Or.inr fun s s' hs => sum_le_sum fun t _ => ?_
    have := h t
    split_ifs <;> first | exact le_rfl | exact this | omega

/-- A gate that splits the cube `q` for the table `x` makes the threshold of its block forms split
`q`. -/
theorem cubeSplits_of_mem_circuitSplitGates {c : Circuit signature (2 ^ b + b * m) 1}
    {q : Fin b → Fin m} {x : BitString (2 ^ b)} {k : Fin c.size}
    (hk : k ∈ circuitSplitGates c 0 (univ.image (andreevLiveVar b m q))
      (andreevCubePoint b m x fun j => q j)) :
    Cslib.Combinatorics.CubeSplits
      (fun j s => ∑ t : Fin m,
        if (t : ℕ) < s then inputWeight c.program k (andreevBlockVar b m j t) else 0)
      ((c.program.lines k).op.threshold -
        ∑ idx, inputWeight c.program k (andreevTableIndex b m idx) * (x idx).toNat) q := by
  have hnf := not_forcedToConst_of_mem_circuitSplitGates hk
  rw [forcedToConst_image_iff (andreevLiveVar_injective b m q)] at hnf
  push Not at hnf
  obtain ⟨u, v, huv⟩ := hnf
  have hval (z : BitString b) :
      ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold
        (embedUpdate (andreevLiveVar b m q) (andreevCubePoint b m x fun j => q j) z) =
      decide ((c.program.lines k).op.threshold -
          ∑ idx, inputWeight c.program k (andreevTableIndex b m idx) * (x idx).toNat ≤
        ∑ j, ∑ t : Fin m, if (t : ℕ) < q j + (z j).toNat then
          inputWeight c.program k (andreevBlockVar b m j t) else 0) := by
    rw [← andreevCubePoint_add, ltfEval, sum_mul_andreevCubePoint]
    exact decide_eq_decide.mpr ⟨fun h => by linarith, fun h => by linarith⟩
  rw [hval, hval] at huv
  rw [Cslib.Combinatorics.cubeSplits_iff]
  by_cases hu : (c.program.lines k).op.threshold -
      ∑ idx, inputWeight c.program k (andreevTableIndex b m idx) * (x idx).toNat ≤
    ∑ j, ∑ t : Fin m, if (t : ℕ) < q j + (u j).toNat then
      inputWeight c.program k (andreevBlockVar b m j t) else 0
  · refine ⟨v, u, ?_, hu⟩
    by_contra hv
    exact huv (by rw [decide_eq_true hu, decide_eq_true (not_lt.mp hv)])
  · refine ⟨u, v, not_le.mp hu, ?_⟩
    by_contra hv
    exact huv (by rw [decide_eq_false hu, decide_eq_false hv])

/-- **Lemma 15** (Reitwiessner, Lemma 15): for every table `x`, a sign-coherent gate splits at most
`m ^ b - (m - 1) ^ b` of the `m ^ b` cubes. -/
theorem card_cubes_mem_circuitSplitGates_le (c : Circuit signature (2 ^ b + b * m) 1)
    {k : Fin c.size} (hk : IsSignCoherent (andreevBlockVar b m) (inputWeight c.program k))
    (x : BitString (2 ^ b)) :
    #{q : Fin b → Fin m | k ∈ circuitSplitGates c 0 (univ.image (andreevLiveVar b m q))
      (andreevCubePoint b m x fun j => q j)} ≤ m ^ b - (m - 1) ^ b := by
  classical
  refine (card_le_card fun q hq => mem_filter.mpr ⟨mem_univ q,
    cubeSplits_of_mem_circuitSplitGates (mem_filter.mp hq).2⟩).trans ?_
  refine (Cslib.Combinatorics.card_cubeSplits_le _ (monotone_or_antitone_blockForm hk)
    _).trans_eq ?_
  rw [Fintype.card_fin]

/-- Summed over all cubes, the splitting gates of a circuit with sign-coherent bottom gates number
at most `G (m ^ b - (m - 1) ^ b)` for every table. -/
theorem sum_andreevCubeSplitCount_le (c : Circuit signature (2 ^ b + b * m) 1)
    (hcoh : ∀ k ∈ outputBottomGates c 0,
      IsSignCoherent (andreevBlockVar b m) (inputWeight c.program k))
    (x : BitString (2 ^ b)) :
    ∑ q : Fin b → Fin m, andreevCubeSplitCount c q x ≤
      #(outputBottomGates c 0) * (m ^ b - (m - 1) ^ b) := by
  classical
  set S : (Fin b → Fin m) → Finset (Fin c.size) := fun q =>
    circuitSplitGates c 0 (univ.image (andreevLiveVar b m q)) (andreevCubePoint b m x fun j => q j)
  have hcount (q : Fin b → Fin m) : andreevCubeSplitCount c q x =
      ∑ k ∈ outputBottomGates c 0, if k ∈ S q then 1 else 0 := by
    rw [andreevCubeSplitCount, ← card_circuitSplitGates, sum_boole, Nat.cast_id]
    congr 1
    exact (filter_mem_eq_inter.trans (inter_eq_right.mpr (circuitSplitGates_subset c 0 _ _))).symm
  simp_rw [hcount]
  rw [sum_comm]
  calc ∑ k ∈ outputBottomGates c 0, ∑ q : Fin b → Fin m, (if k ∈ S q then 1 else 0)
      ≤ ∑ _k ∈ outputBottomGates c 0, (m ^ b - (m - 1) ^ b) := sum_le_sum fun k hk => by
        rw [sum_boole, Nat.cast_id]
        exact card_cubes_mem_circuitSplitGates_le c (hcoh k hk) x
    _ = #(outputBottomGates c 0) * (m ^ b - (m - 1) ^ b) := by rw [sum_const, smul_eq_mul]

/-! ### Theorem 13 -/

/-- **Theorem 13** (Reitwiessner, Theorem 13): a depth-two weighted threshold circuit computing
`andreev b m` whose `G` bottom gates are sign-coherent satisfies
`m ^ b D₀ ≤ (m ^ b - (m - 1) ^ b) G`, i.e. `G ≥ m ^ b / (m ^ b - (m - 1) ^ b) · D₀`. -/
theorem pow_mul_andreevCubeSplitBound_le (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev b m)))
    (hcoh : ∀ k ∈ outputBottomGates c 0,
      IsSignCoherent (andreevBlockVar b m) (inputWeight c.program k)) :
    (m : ℝ) ^ b * andreevCubeSplitBound b #(outputBottomGates c 0) ≤
      ((m ^ b - (m - 1) ^ b : ℕ) : ℝ) * #(outputBottomGates c 0) := by
  set G := #(outputBottomGates c 0)
  have hlow : (m : ℝ) ^ b * ((2 : ℝ) ^ 2 ^ b * andreevCubeSplitBound b G) ≤
      ∑ q : Fin b → Fin m, ∑ x : BitString (2 ^ b), (andreevCubeSplitCount c q x : ℝ) := by
    have := sum_le_sum fun q (_ : q ∈ (univ : Finset (Fin b → Fin m))) =>
      two_pow_mul_andreevCubeSplitBound_le c hd hcomp q
    rwa [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow] at this
  have hup : ∑ q : Fin b → Fin m, ∑ x : BitString (2 ^ b), (andreevCubeSplitCount c q x : ℝ) ≤
      (2 : ℝ) ^ 2 ^ b * (((m ^ b - (m - 1) ^ b : ℕ) : ℝ) * G) := by
    rw [sum_comm]
    have := sum_le_sum fun x (_ : x ∈ (univ : Finset (BitString (2 ^ b)))) =>
      (Nat.cast_le (α := ℝ)).mpr (sum_andreevCubeSplitCount_le c hcoh x)
    simp only [Nat.cast_sum, Nat.cast_mul] at this
    refine this.trans_eq ?_
    rw [sum_const, card_univ, nsmul_eq_mul]
    simp only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast; ring
  have h2 : (0 : ℝ) < 2 ^ 2 ^ b := by positivity
  nlinarith [hlow.trans hup]

/-- `m ^ b - (m - 1) ^ b ≤ b m ^ (b - 1)`. -/
private theorem pow_sub_pred_pow_le (m b : ℕ) :
    ((m ^ b - (m - 1) ^ b : ℕ) : ℝ) ≤ b * (m : ℝ) ^ (b - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · simp only [zero_pow hb.ne', Nat.zero_sub, Nat.sub_self, Nat.cast_zero]; positivity
  have hm1 : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm, Nat.cast_one]
  rw [Nat.cast_sub (Nat.pow_le_pow_left (Nat.sub_le m 1) b), Nat.cast_pow, Nat.cast_pow, hm1,
    ← geom_sum₂_mul, sub_sub_cancel, mul_one]
  calc ∑ i ∈ range b, (m : ℝ) ^ i * ((m : ℝ) - 1) ^ (b - 1 - i)
      ≤ ∑ _i ∈ range b, (m : ℝ) ^ (b - 1) := sum_le_sum fun i hi => by
        have hib := mem_range.mp hi
        have hm0 : (0 : ℝ) ≤ m - 1 := by
          have : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
          linarith
        calc (m : ℝ) ^ i * ((m : ℝ) - 1) ^ (b - 1 - i) ≤ (m : ℝ) ^ i * (m : ℝ) ^ (b - 1 - i) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 (by linarith) _) (by positivity)
          _ = (m : ℝ) ^ (b - 1) := by rw [← pow_add]; congr 1; omega
    _ = b * (m : ℝ) ^ (b - 1) := by rw [sum_const, card_range, nsmul_eq_mul]

/-- **Theorem 13, `m / b` form**: `m D₀ ≤ b G`, i.e. `G ≥ (m / b) D₀`. -/
theorem mul_andreevCubeSplitBound_le (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev b m)))
    (hcoh : ∀ k ∈ outputBottomGates c 0,
      IsSignCoherent (andreevBlockVar b m) (inputWeight c.program k)) :
    (m : ℝ) * andreevCubeSplitBound b #(outputBottomGates c 0) ≤
      b * #(outputBottomGates c 0) := by
  set G := #(outputBottomGates c 0)
  have hmain := pow_mul_andreevCubeSplitBound_le c hd hcomp hcoh
  have hD := andreevCubeSplitBound_nonneg b G
  have hG : (0 : ℝ) ≤ G := Nat.cast_nonneg G
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm, Nat.cast_zero, zero_mul]; positivity
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp only [pow_zero, Nat.sub_self, Nat.cast_zero, zero_mul, one_mul] at hmain
    nlinarith
  have hle := (mul_le_mul_of_nonneg_right (pow_sub_pred_pow_le m b) hG).trans' hmain
  have hpow : (m : ℝ) ^ b = m * (m : ℝ) ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℝ) < (m : ℝ) ^ (b - 1) := by positivity
  rw [hpow] at hle
  nlinarith

/-- **Theorem 13, explicit form**: `G ≥ min (N ^ 2) (m (N - 3 b - 1) / (3 b ^ 2))`, `N = 2 ^ b`. -/
theorem min_le_card_outputBottomGates (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev b m)))
    (hcoh : ∀ k ∈ outputBottomGates c 0,
      IsSignCoherent (andreevBlockVar b m) (inputWeight c.program k)) :
    min (((2 : ℝ) ^ b) ^ 2) ((m : ℝ) * ((2 : ℝ) ^ b - 3 * b - 1) / (3 * (b : ℝ) ^ 2)) ≤
      #(outputBottomGates c 0) := by
  set G := #(outputBottomGates c 0)
  have hG : (0 : ℝ) ≤ G := Nat.cast_nonneg G
  by_cases hbig : ((2 : ℝ) ^ b) ^ 2 ≤ G
  · exact (min_le_left _ _).trans hbig
  refine (min_le_right _ _).trans ?_
  push Not at hbig
  have hmain := mul_andreevCubeSplitBound_le c hd hcomp hcoh
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have hb1 : (1 : ℝ) ≤ b := Nat.one_le_cast.mpr hb
  rcases le_or_gt ((2 : ℝ) ^ b - 3 * b - 1) 0 with hn | hn
  · exact (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hn)
      (by positivity)).trans hG
  -- `G < N ^ 2` gives `log₂ (G + 1) ≤ 2 b`.
  have hL0 : 0 ≤ Real.logb 2 ((G : ℝ) + 1) := Real.logb_nonneg one_lt_two (by linarith)
  have hL : Real.logb 2 ((G : ℝ) + 1) ≤ 2 * b := by
    have hGN : (G : ℝ) + 1 ≤ 2 ^ (2 * b) := by
      have : G < 2 ^ (2 * b) := by
        have h' : (G : ℝ) < ((2 ^ (2 * b) : ℕ) : ℝ) := by
          have : ((2 ^ (2 * b) : ℕ) : ℝ) = ((2 : ℝ) ^ b) ^ 2 := by push_cast; ring
          rw [this]; exact hbig
        exact_mod_cast h'
      exact_mod_cast this
    calc Real.logb 2 ((G : ℝ) + 1) ≤ Real.logb 2 ((2 : ℝ) ^ (2 * b)) :=
          Real.logb_le_logb_of_le one_lt_two (by linarith) hGN
      _ = 2 * b := by exact_mod_cast Real.logb_two_pow (2 * b)
  have hD : ((2 : ℝ) ^ b - 3 * b - 1) / (3 * b) ≤ andreevCubeSplitBound b G := by
    unfold andreevCubeSplitBound
    exact div_le_div₀ (le_max_left _ _) ((by linarith : (2 : ℝ) ^ b - 3 * b - 1 ≤
      (2 : ℝ) ^ b - b - 1 - Real.logb 2 (G + 1)).trans (le_max_right _ _))
      (by linarith) (by linarith)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hstep := (mul_le_mul_of_nonneg_left hD hm0).trans hmain
  rw [div_le_iff₀ (by positivity)]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hstep
  nlinarith

/-- **Theorem 13, balanced form**: if `b m = N = 2 ^ b`, then `G ≥ N (N - 3 b - 1) / (3 b ^ 3)`,
which is `Ω(n ^ 2 / log ^ 3 n)` for `n = 2 N`. -/
theorem le_card_outputBottomGates_of_balanced (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (andreev b m)))
    (hcoh : ∀ k ∈ outputBottomGates c 0,
      IsSignCoherent (andreevBlockVar b m) (inputWeight c.program k))
    (hbal : b * m = 2 ^ b) :
    (2 : ℝ) ^ b * ((2 : ℝ) ^ b - 3 * b - 1) / (3 * (b : ℝ) ^ 3) ≤ #(outputBottomGates c 0) := by
  have hmin := min_le_card_outputBottomGates c hd hcomp hcoh
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp at hbal
    · exact hb
  have hb1 : (1 : ℝ) ≤ b := Nat.one_le_cast.mpr hb
  have hm : (m : ℝ) = (2 : ℝ) ^ b / b := by
    rw [eq_div_iff (by positivity), mul_comm]; exact_mod_cast hbal
  have hG : (0 : ℝ) ≤ #(outputBottomGates c 0) := Nat.cast_nonneg _
  have hN : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ one_le_two
  have heq : (m : ℝ) * ((2 : ℝ) ^ b - 3 * b - 1) / (3 * (b : ℝ) ^ 2) =
      (2 : ℝ) ^ b * ((2 : ℝ) ^ b - 3 * b - 1) / (3 * (b : ℝ) ^ 3) := by
    rw [hm]; field_simp
  rw [heq] at hmin
  rcases le_or_gt ((2 : ℝ) ^ b - 3 * b - 1) 0 with hn | hn
  · exact (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hn)
      (by positivity)).trans hG
  refine le_trans (le_min ?_ le_rfl) hmin
  rw [div_le_iff₀ (by positivity)]
  have hb3 : (1 : ℝ) ≤ 3 * (b : ℝ) ^ 3 := by nlinarith [pow_le_pow_left₀ zero_le_one hb1 3]
  nlinarith

/-! ### Theorem 13 for `depthTwoInputs` circuits -/

/-- **Theorem 13 for `depthTwoInputs`**: if a depth-two circuit `depthTwoInputs bottom args u v θ`
with `G` bottom gates computes `andreev b m` and every bottom gate is sign-coherent on the address
blocks, then `m ^ b D₀ ≤ (m ^ b - (m - 1) ^ b) G` with `D₀ = andreevCubeSplitBound b G`. -/
theorem pow_mul_andreevCubeSplitBound_le_of_depthTwoInputs {G : ℕ} (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin (2 ^ b + b * m)) (u : Fin G → ℝ)
    (v : Fin (2 ^ b + b * m) → ℝ) (θ : ℝ)
    (hcomp : (depthTwoInputs bottom args u v θ).Computes interpretation (single (andreev b m)))
    (hcoh : ∀ j, IsSignCoherent (andreevBlockVar b m) (argWeight (bottom j) (args j))) :
    (m : ℝ) ^ b * andreevCubeSplitBound b G ≤ ((m ^ b - (m - 1) ^ b : ℕ) : ℝ) * G := by
  set c := depthTwoInputs bottom args u v θ
  obtain ⟨top, htop⟩ : ∃ top, c.outputs 0 = .gate top := ⟨_, rfl⟩
  have hB : #(outputBottomGates c 0) ≤ G := by
    have := card_outputBottomGates_lt_size htop
    have hs : c.size = G + 1 := size_depthTwoInputs ..
    omega
  have hmain := pow_mul_andreevCubeSplitBound_le c (depth_depthTwoInputs_le ..) hcomp
    fun k hk => isSignCoherent_inputWeight_depthTwoInputs bottom args u v θ hcoh htop
      (by rwa [outputBottomGates_of_gate htop] at hk)
  calc (m : ℝ) ^ b * andreevCubeSplitBound b G
      ≤ (m : ℝ) ^ b * andreevCubeSplitBound b #(outputBottomGates c 0) :=
        mul_le_mul_of_nonneg_left (andreevCubeSplitBound_anti b hB) (by positivity)
    _ ≤ ((m ^ b - (m - 1) ^ b : ℕ) : ℝ) * #(outputBottomGates c 0) := hmain
    _ ≤ ((m ^ b - (m - 1) ^ b : ℕ) : ℝ) * G :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hB) (Nat.cast_nonneg _)

/-- **Theorem 13 for `depthTwoInputs`, balanced form**: if `b m = N = 2 ^ b`, a sign-coherent
`depthTwoInputs` circuit computing `andreev b m` has `G ≥ N (N - 3 b - 1) / (3 b ^ 3)` bottom
gates. -/
theorem le_of_balanced_of_depthTwoInputs {G : ℕ} (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin (2 ^ b + b * m)) (u : Fin G → ℝ)
    (v : Fin (2 ^ b + b * m) → ℝ) (θ : ℝ)
    (hcomp : (depthTwoInputs bottom args u v θ).Computes interpretation (single (andreev b m)))
    (hcoh : ∀ j, IsSignCoherent (andreevBlockVar b m) (argWeight (bottom j) (args j)))
    (hbal : b * m = 2 ^ b) :
    (2 : ℝ) ^ b * ((2 : ℝ) ^ b - 3 * b - 1) / (3 * (b : ℝ) ^ 3) ≤ G := by
  set c := depthTwoInputs bottom args u v θ
  obtain ⟨top, htop⟩ : ∃ top, c.outputs 0 = .gate top := ⟨_, rfl⟩
  have hB : #(outputBottomGates c 0) ≤ G := by
    have := card_outputBottomGates_lt_size htop
    have hs : c.size = G + 1 := size_depthTwoInputs ..
    omega
  refine (le_card_outputBottomGates_of_balanced c (depth_depthTwoInputs_le ..) hcomp
    (fun k hk => isSignCoherent_inputWeight_depthTwoInputs bottom args u v θ hcoh htop
      (by rwa [outputBottomGates_of_gate htop] at hk)) hbal).trans ?_
  exact_mod_cast hB

end Cslib.Circuits.Boolean.WeightedThreshold
