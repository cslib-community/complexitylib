/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.CapacityCircuit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Direction-menu capacity bounds for weighted threshold circuits

Partition the input-reading gates of a weighted threshold program into `d` directions (`dir : Fin g
→ Fin d`), so that each input-reading gate `gate` has input weight vector
`scale gate • w (dir gate)`. Unlike `DirectionRuns`, gates of different directions may be
arbitrarily interleaved in the topological order.

For each gate, its syntactic *bias menu* (`biasMenu p gate`) is the finite set of all internal sums
`∑ j, gateWeight p gate j * (u j).toNat` over Boolean valuations `u : Fin g → Bool`. Precomputing
the comparison table `(gate, β) ↦ decide (threshold ≤ scale gate * (w a · x) + β)` for all
input-reading gates in direction `a` and all `β ∈ biasMenu p gate` costs a single one-dimensional
scalar block with at most `T_a = ∑_{gate ∈ directionGates p dir a} |biasMenu p gate|` changes
(`changesAtMost_trueMenuTable`). Once the table for direction `a` is precomputed, every gate in
direction `a` becomes a zero-change (`oneDim 0`) lookup from its predecessor gate values.

Choosing for each direction `a` the cheaper of precomputing its menu table (`max 1 (4 * T_a)`) or
evaluating its `q_a` gates individually (`4 ^ q_a`) yields the direction-menu lower bound
(`two_pow_lt_of_directionMenus`, Theorem 7.3 of [*Threshold Circuits as Decision Trees and
Finite-State Programs*][ThresholdCircuitRepresentations2026]), together with its corollaries for
bounded internal fan-in (`two_pow_lt_of_directionMenus_fanIn`, Corollary 7.4) and bounded integer
internal weights (`two_pow_lt_of_directionMenus_intWeight`, `two_pow_lt_of_direction_intWeight`).

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.gateSupport`: earlier gates with nonzero internal weight
  into a gate.
* `Cslib.Circuits.Boolean.WeightedThreshold.biasMenu`: syntactic menu of attainable internal bias
  offsets at a gate.
* `Cslib.Circuits.Boolean.WeightedThreshold.directionGates`: input-reading gates assigned to a
  direction `a : Fin d`.
* `Cslib.Circuits.Boolean.WeightedThreshold.directionMenuSum`: sum of bias-menu cardinalities over
  `directionGates p dir a`.
* `Cslib.Circuits.Boolean.WeightedThreshold.menuBlockDecomposition`: the `(d + g)`-block
  decomposition precomputing menu tables for a chosen subset of directions.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_biasMenu_le_two_pow_gateSupport`: bounded internal
  fan-in `k` bounds `|biasMenu p gate|` by `2 ^ k`.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_biasMenu_le_one_add_sum_natAbs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_biasMenu_le_one_add_mul`: integer internal weights
  of magnitude at most `W` bound `|biasMenu p gate|` by `1 + gate * W`.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_directionMenus`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_of_directionMenus`: Theorem 7.3
  (direction-menu capacity bound).
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_directionMenus_fanIn`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_of_directionMenus_fanIn`:
  Corollary 7.4 (bounded internal fan-in).
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_directionMenus_intWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_of_directionMenus_intWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_direction_intWeight`: bounded integer
  internal weights.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Section 7.2]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g d : ℕ}

/-! ### Internal gate support and syntactic bias menus -/

/-- Earlier gates with a nonzero aggregated internal weight into `gate`. -/
noncomputable def gateSupport (p : Program signature n g) (gate : Fin g) : Finset (Fin g) :=
  open scoped Classical in
  univ.filter fun prior => gateWeight p gate prior ≠ 0

@[simp]
theorem mem_gateSupport (p : Program signature n g) (gate prior : Fin g) :
    prior ∈ gateSupport p gate ↔ gateWeight p gate prior ≠ 0 := by
  classical
  simp [gateSupport]

theorem gateSupport_subset_Iio (p : Program signature n g) (gate : Fin g) :
    ∀ prior ∈ gateSupport p gate, prior < gate := by
  intro prior h
  by_contra hle
  exact (mem_gateSupport p gate prior).mp h (gateWeight_eq_zero_of_le p gate prior (not_lt.mp hle))

/-- The syntactic menu of all possible internal gate biases at `gate` over Boolean valuations of
internal gates. -/
noncomputable def biasMenu (p : Program signature n g) (gate : Fin g) : Finset ℝ :=
  open scoped Classical in
  univ.image fun u : Fin g → Bool => ∑ j, gateWeight p gate j * (u j).toNat

theorem gateBias_mem_biasMenu (p : Program signature n g) (gate : Fin g) (u : Fin g → Bool) :
    (∑ j, gateWeight p gate j * (u j).toNat) ∈ biasMenu p gate := by
  classical
  exact mem_image_of_mem _ (mem_univ u)

theorem card_biasMenu_pos (p : Program signature n g) (gate : Fin g) :
    0 < (biasMenu p gate).card := by
  classical
  exact card_pos.mpr ⟨_, gateBias_mem_biasMenu p gate (fun _ => false)⟩

/-- If `gate` reads at most `k` earlier gates with nonzero weight, its bias menu has size at most
`2 ^ k`. -/
theorem card_biasMenu_le_two_pow_gateSupport (p : Program signature n g) (gate : Fin g) :
    (biasMenu p gate).card ≤ 2 ^ (gateSupport p gate).card := by
  classical
  have hsub : biasMenu p gate ⊆
      univ.image (fun v : gateSupport p gate → Bool =>
        ∑ j : gateSupport p gate, gateWeight p gate j.1 * (v j).toNat) := by
    intro β hβ
    obtain ⟨u, -, rfl⟩ := mem_image.mp hβ
    refine mem_image.mpr ⟨fun j => u j.1, mem_univ _, ?_⟩
    rw [sum_coe_sort (gateSupport p gate) (fun j => gateWeight p gate j * (u j).toNat)]
    refine sum_subset (subset_univ _) fun j _ hj => ?_
    have hj0 : gateWeight p gate j = 0 := not_not.mp ((mem_gateSupport p gate j).not.mp hj)
    simp [hj0]
  calc (biasMenu p gate).card
      ≤ (univ.image (fun v : gateSupport p gate → Bool =>
          ∑ j : gateSupport p gate, gateWeight p gate j.1 * (v j).toNat)).card :=
        card_le_card hsub
    _ ≤ (univ : Finset (gateSupport p gate → Bool)).card := card_image_le
    _ = 2 ^ (gateSupport p gate).card := by
      rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- Integer internal weights `w` bound the bias menu of `gate` by `1 + ∑ j, |w j|`. -/
theorem card_biasMenu_le_one_add_sum_natAbs (p : Program signature n g) (gate : Fin g)
    (w : Fin g → ℤ) (hw : ∀ j, gateWeight p gate j = w j) :
    (biasMenu p gate).card ≤ 1 + ∑ j, (w j).natAbs := by
  classical
  let lo : ℤ := ∑ j, min 0 (w j)
  let hi : ℤ := ∑ j, max 0 (w j)
  have hsub : biasMenu p gate ⊆ (Icc lo hi).image (Int.cast : ℤ → ℝ) := by
    intro β hβ
    obtain ⟨u, -, rfl⟩ := mem_image.mp hβ
    refine mem_image.mpr ⟨∑ j, w j * (u j).toNat, mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · refine sum_le_sum fun j _ => ?_
      cases u j <;> simp
    · refine sum_le_sum fun j _ => ?_
      cases u j <;> simp
    · push_cast
      refine sum_congr rfl fun j _ => ?_
      rw [hw j]
  have hdiff : hi - lo = ∑ j, ((w j).natAbs : ℤ) := by
    dsimp [hi, lo]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    omega
  calc (biasMenu p gate).card
      ≤ ((Icc lo hi).image (Int.cast : ℤ → ℝ)).card := card_le_card hsub
    _ ≤ (Icc lo hi).card := card_image_le
    _ = (hi + 1 - lo).toNat := Int.card_Icc lo hi
    _ = 1 + ∑ j, (w j).natAbs := by
      have : hi + 1 - lo = ((1 + ∑ j, (w j).natAbs : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_sum]
        linarith
      rw [this, Int.toNat_natCast]

/-- Integer internal weights of magnitude at most `W` on earlier gates bound `|biasMenu p gate|` by
`1 + gate.val * W`. -/
theorem card_biasMenu_le_one_add_mul (p : Program signature n g) (gate : Fin g) (W : ℕ)
    (w : Fin g → ℤ) (hw : ∀ j, gateWeight p gate j = w j)
    (hW : ∀ j < gate, (w j).natAbs ≤ W) :
    (biasMenu p gate).card ≤ 1 + gate.val * W := by
  let w' : Fin g → ℤ := fun j => if j < gate then w j else 0
  have hw' (j : Fin g) : gateWeight p gate j = w' j := by
    dsimp [w']
    split_ifs with hj
    · exact hw j
    · simpa using gateWeight_eq_zero_of_le p gate j (not_lt.mp hj)
  have h1 := card_biasMenu_le_one_add_sum_natAbs p gate w' hw'
  have h2 : ∑ j, (w' j).natAbs ≤ gate.val * W := by
    calc ∑ j : Fin g, (w' j).natAbs
        = ∑ j : Fin g, if j < gate then (w j).natAbs else 0 := by
          refine sum_congr rfl fun j _ => ?_
          dsimp [w']
          split_ifs <;> simp
      _ = ∑ j ∈ Iio gate, (w j).natAbs := by
          rw [← sum_filter]
          congr 1
          ext j
          simp
      _ ≤ ∑ _j ∈ Iio gate, W := sum_le_sum fun j hj => hW j (mem_Iio.mp hj)
      _ = gate.val * W := by simp
  omega

/-! ### Direction partition and menu sums -/

/-- Input-reading gates assigned to direction `a`. -/
noncomputable def directionGates (p : Program signature n g) (dir : Fin g → Fin d)
    (a : Fin d) : Finset (Fin g) :=
  (inputGates p).filter fun gate => dir gate = a

@[simp]
theorem mem_directionGates (p : Program signature n g) (dir : Fin g → Fin d)
    (a : Fin d) (gate : Fin g) :
    gate ∈ directionGates p dir a ↔ gate ∈ inputGates p ∧ dir gate = a :=
  mem_filter

/-- Total syntactic bias-menu size of input-reading gates in direction `a`. -/
noncomputable def directionMenuSum (p : Program signature n g) (dir : Fin g → Fin d)
    (a : Fin d) : ℕ :=
  ∑ gate ∈ directionGates p dir a, (biasMenu p gate).card

theorem sum_card_directionGates (p : Program signature n g) (dir : Fin g → Fin d) :
    ∑ a : Fin d, (directionGates p dir a).card = (inputGates p).card := by
  classical
  unfold directionGates
  exact (card_eq_sum_card_fiberwise fun gate _ => mem_univ (dir gate)).symm

theorem directionMenuSum_pos_of_nonempty (p : Program signature n g) (dir : Fin g → Fin d)
    {a : Fin d} (h : (directionGates p dir a).Nonempty) :
    0 < directionMenuSum p dir a := by
  obtain ⟨gate, hgate⟩ := h
  exact lt_of_lt_of_le (card_biasMenu_pos p gate)
    (single_le_sum (f := fun gate => (biasMenu p gate).card) (fun _ _ => Nat.zero_le _) hgate)

/-! ### Static menu precomputation and block decomposition -/

/-- A linear threshold predicate `decide (θ ≤ c * t + β)` changes at most once along `ℝ`. -/
private theorem changesAtMost_linear_threshold (θ c β : ℝ) :
    ChangesAtMost (fun t : ℝ => decide (θ ≤ c * t + β)) 1 := by
  have hbase : ChangesAtMost (fun u : ℝ => decide (θ ≤ u)) 1 := by
    intro z hz S hS
    have hcut (i) (hi : i ∈ S) : z i < θ ∧ θ ≤ z (i + 1) := by
      have hn : ¬ θ ≤ z i := by
        intro hc
        exact hS i hi (by simp [hc, hc.trans (hz (Nat.le_succ i))])
      have hp : θ ≤ z (i + 1) := by
        by_contra hn'
        exact hS i hi (by simp [hn, hn'])
      exact ⟨lt_of_not_ge hn, hp⟩
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (not_lt_of_ge ((hcut i hi).2.trans (hz h))) (hcut j hj).1
    · exact (not_lt_of_ge ((hcut j hj).2.trans (hz h))) (hcut i hi).1
  rcases le_or_gt 0 c with hc | hc
  · exact hbase.comp_monotone ((monotone_id.const_mul hc).add_const β)
  · exact hbase.comp_antitone ((monotone_id.const_mul_of_nonpos hc.le).add_const β)

/-- Type of the precomputed comparison table for direction `a`. -/
abbrev MenuTable (p : Program signature n g) (dir : Fin g → Fin d) (a : Fin d) : Type :=
  (gate : directionGates p dir a) → biasMenu p gate.1 → Bool

/-- The precomputed comparison table for direction `a` at directional projection `t = w a · x`. -/
noncomputable def trueMenuTable (p : Program signature n g) (dir : Fin g → Fin d)
    (scale : Fin g → ℝ) (a : Fin d) (t : ℝ) : MenuTable p dir a :=
  fun gate β => decide ((p.lines gate.1).op.threshold ≤ scale gate.1 * t + β.1)

/-- As a function of the scalar `t`, the menu table for direction `a` changes at most
`directionMenuSum p dir a` times. -/
theorem changesAtMost_trueMenuTable (p : Program signature n g) (dir : Fin g → Fin d)
    (scale : Fin g → ℝ) (a : Fin d) :
    ChangesAtMost (trueMenuTable p dir scale a) (directionMenuSum p dir a) := by
  classical
  have hgate (gate : directionGates p dir a) :
      ChangesAtMost (fun t : ℝ => fun β : biasMenu p gate.1 =>
        decide ((p.lines gate.1).op.threshold ≤ scale gate.1 * t + β.1))
        (biasMenu p gate.1).card := by
    have hpi := ChangesAtMost.pi (ι := biasMenu p gate.1) (T := fun _ => 1)
      (fun β => changesAtMost_linear_threshold (p.lines gate.1).op.threshold (scale gate.1) β.1)
    simpa [Fintype.card_coe] using hpi
  have hall := ChangesAtMost.pi (ι := directionGates p dir a)
    (T := fun gate => (biasMenu p gate.1).card) hgate
  have hsum : (∑ gate : directionGates p dir a, (biasMenu p gate.1).card) =
      directionMenuSum p dir a := by
    unfold directionMenuSum
    exact sum_coe_sort (directionGates p dir a) (fun gate => (biasMenu p gate).card)
  rw [← hsum]
  exact hall

/-- Intermediate state of the `(d + g)`-step menu block decomposition at step `i`. -/
noncomputable def menuHistory (p : Program signature n g) (dir : Fin g → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin g → ℝ) (S : Finset (Fin d))
    (i : ℕ) (x : Fin n → Bool) :
    ((a : Fin d) → MenuTable p dir a) × (Fin g → Bool) :=
  (fun a => if a.val < i ∧ a ∈ S then
      trueMenuTable p dir scale a (∑ k, w a k * (x k).toNat)
    else fun _ _ => false,
   fun gate => if d + gate.val < i then p.eval interpretation x gate else false)

private theorem menuHistory_step_dir (p : Program signature n g) (dir : Fin g → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin g → ℝ) (S : Finset (Fin d)) (a : Fin d) :
    (BlockKind.oneDim (if a ∈ S then directionMenuSum p dir a else 0)).Step
      (menuHistory p dir w scale S a.val)
      (menuHistory p dir w scale S (a.val + 1)) := by
  classical
  by_cases haS : a ∈ S
  · simp only [haS, ite_true, BlockKind.Step]
    refine ⟨w a, fun η t => (Function.update η.1 a (trueMenuTable p dir scale a t), η.2), ?_, ?_⟩
    · intro η
      exact (changesAtMost_trueMenuTable p dir scale a).comp
        (fun tbl => (Function.update η.1 a tbl, η.2))
    · intro x
      refine Prod.ext (funext fun b => ?_) (funext fun gate' => ?_)
      · by_cases hb : b = a
        · subst hb
          simp [menuHistory, haS]
        · have hbv : b.val ≠ a.val := fun h => hb (Fin.ext h)
          have hlt : b.val < a.val + 1 ↔ b.val < a.val := by omega
          dsimp [menuHistory]
          rw [Function.update_of_ne hb]
          simp only [hlt]
      · have h1 : ¬ d + gate'.val < a.val + 1 := by omega
        have h2 : ¬ d + gate'.val < a.val := by omega
        dsimp [menuHistory]
        rw [ite_eq_right h1, ite_eq_right h2]
  · simp only [haS, ite_false, BlockKind.Step]
    refine ⟨fun _ => 0, fun η _ => η, fun _ => ChangesAtMost.const _, fun x => ?_⟩
    refine Prod.ext (funext fun b => ?_) (funext fun gate' => ?_)
    · by_cases hb : b = a
      · subst hb
        simp [menuHistory, haS]
      · have hbv : b.val ≠ a.val := fun h => hb (Fin.ext h)
        have hlt : b.val < a.val + 1 ↔ b.val < a.val := by omega
        dsimp [menuHistory]
        simp only [hlt]
    · have h1 : ¬ d + gate'.val < a.val + 1 := by omega
      have h2 : ¬ d + gate'.val < a.val := by omega
      dsimp [menuHistory]
      rw [ite_eq_right h1, ite_eq_right h2]

private theorem menuHistory_step_gate (p : Program signature n g) (dir : Fin g → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin g → ℝ)
    (hdir : ∀ gate ∈ inputGates p, inputWeight p gate = scale gate • w (dir gate))
    (S : Finset (Fin d)) (gate : Fin g) :
    (BlockKind.oneDim (if gate ∈ inputGates p ∧ dir gate ∉ S then 1 else 0)).Step
      (menuHistory p dir w scale S (d + gate.val))
      (menuHistory p dir w scale S (d + gate.val + 1)) := by
  classical
  have htables (x : Fin n → Bool) :
      (menuHistory p dir w scale S (d + gate.val + 1) x).1 =
        (menuHistory p dir w scale S (d + gate.val) x).1 := by
    funext a
    have h1 : a.val < d + gate.val + 1 := by omega
    have h2 : a.val < d + gate.val := by omega
    dsimp [menuHistory]
    simp only [h1, h2]
  have hgates (x : Fin n → Bool) :
      (menuHistory p dir w scale S (d + gate.val + 1) x).2 =
        Function.update (menuHistory p dir w scale S (d + gate.val) x).2 gate
          (decide ((p.lines gate).op.threshold ≤
            (∑ k, inputWeight p gate k * (x k).toNat) +
            ∑ j, gateWeight p gate j *
              ((menuHistory p dir w scale S (d + gate.val) x).2 j).toNat)) := by
    have heval := eval_gate_eq p x gate
    have hsum : (∑ j, gateWeight p gate j * (p.eval interpretation x j).toNat) =
        ∑ j, gateWeight p gate j *
          ((menuHistory p dir w scale S (d + gate.val) x).2 j).toNat := by
      apply sum_congr rfl
      intro j _
      by_cases hj : j < gate
      · have hj' : d + j.val < d + gate.val := by omega
        dsimp [menuHistory]
        rw [ite_eq_left hj']
      · simp [gateWeight_eq_zero_of_le p gate j (le_of_not_gt hj)]
    rw [hsum] at heval
    funext j
    by_cases hj : j = gate
    · subst hj
      have hj' : d + j.val < d + j.val + 1 := by omega
      simpa [menuHistory, hj'] using heval
    · rw [Function.update_of_ne hj]
      have hv : j.val ≠ gate.val := fun h => hj (Fin.ext h)
      have heq : (d + j.val < d + gate.val + 1) ↔ d + j.val < d + gate.val := by omega
      simp only [menuHistory, heq]
  by_cases hact : gate ∈ inputGates p ∧ dir gate ∉ S
  · rw [ite_eq_left hact]
    dsimp only [BlockKind.Step]
    refine ⟨inputWeight p gate,
      fun η t => (η.1, Function.update η.2 gate (decide ((p.lines gate).op.threshold ≤
        t + ∑ j, gateWeight p gate j * (η.2 j).toNat))), ?_, ?_⟩
    · intro η
      simpa only [one_mul, Function.comp_def] using
        (changesAtMost_linear_threshold (p.lines gate).op.threshold 1
          (∑ j, gateWeight p gate j * (η.2 j).toNat)).comp
          (fun b => (η.1, Function.update η.2 gate b))
    · intro x
      exact Prod.ext (htables x) (hgates x)
  · rw [ite_eq_right hact]
    dsimp only [BlockKind.Step]
    by_cases hin : gate ∈ inputGates p
    · have haS : dir gate ∈ S := by
        by_contra hnot
        exact hact ⟨hin, hnot⟩
      have hdg : gate ∈ directionGates p dir (dir gate) :=
        (mem_directionGates p dir (dir gate) gate).mpr ⟨hin, rfl⟩
      refine ⟨fun _ => 0,
        fun η _ => (η.1, Function.update η.2 gate
          (η.1 (dir gate) ⟨gate, hdg⟩
            ⟨∑ j, gateWeight p gate j * (η.2 j).toNat, gateBias_mem_biasMenu p gate η.2⟩)),
        fun _ => ChangesAtMost.const _, fun x => Prod.ext (htables x) ?_⟩
      rw [hgates x]
      congr 1
      have hlt : (dir gate).val < d + gate.val := by omega
      have hscale_sum : (∑ k, inputWeight p gate k * (x k).toNat) =
          scale gate * ∑ k, w (dir gate) k * (x k).toNat := by
        have hw := hdir gate hin
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        have hwk := congrFun hw k
        simp only [Pi.smul_apply, smul_eq_mul] at hwk
        rw [hwk, mul_assoc]
      simp [menuHistory, hlt, haS, trueMenuTable, hscale_sum]
    · refine ⟨fun _ => 0,
        fun η _ => (η.1, Function.update η.2 gate
          (decide ((p.lines gate).op.threshold ≤
            ∑ j, gateWeight p gate j * (η.2 j).toNat))),
        fun _ => ChangesAtMost.const _, fun x => Prod.ext (htables x) ?_⟩
      simpa only [inputWeight_eq_zero_of_not_mem p hin, zero_mul, sum_const_zero,
        zero_add] using hgates x

/-- The `(d + g)`-block decomposition of `p` that precomputes menu tables for directions in `S` and
evaluates remaining input-reading gates individually. -/
noncomputable def menuBlockDecomposition (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) (dir : Fin g → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin g → ℝ)
    (hdir : ∀ gate ∈ inputGates p, inputWeight p gate = scale gate • w (dir gate))
    (S : Finset (Fin d)) :
    BlockDecomposition (fun x => readout (p.eval interpretation x))
      (((a : Fin d) → MenuTable p dir a) × (Fin g → Bool)) where
  length := d + g
  kind i :=
    if h1 : i < d then
      .oneDim (if ⟨i, h1⟩ ∈ S then directionMenuSum p dir ⟨i, h1⟩ else 0)
    else if h2 : i - d < g then
      .oneDim (if ⟨i - d, h2⟩ ∈ inputGates p ∧ dir ⟨i - d, h2⟩ ∉ S then 1 else 0)
    else .oneDim 0
  history := menuHistory p dir w scale S
  output η := readout η.2
  history_zero x y := by
    refine Prod.ext (funext fun a => ?_) (funext fun gate => ?_) <;> simp [menuHistory]
  step i hi := by
    by_cases h1 : i < d
    · simpa only [dite_eq_left h1] using menuHistory_step_dir p dir w scale S ⟨i, h1⟩
    · have h2 : i - d < g := by omega
      have heq : d + (i - d) = i := by omega
      simp only [dite_eq_right h1, dite_eq_left h2]
      have hstep := menuHistory_step_gate p dir w scale hdir S ⟨i - d, h2⟩
      simpa only [heq] using hstep
  output_history x := by
    dsimp [menuHistory]
    congr 1
    funext gate
    have : d + gate.val < d + g := by omega
    simp [this]

/-- The capacity cost of `menuBlockDecomposition` factors across the `d` directions. -/
theorem cost_menuBlockDecomposition (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) (dir : Fin g → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin g → ℝ)
    (hdir : ∀ gate ∈ inputGates p, inputWeight p gate = scale gate • w (dir gate))
    (S : Finset (Fin d)) :
    (menuBlockDecomposition p readout dir w scale hdir S).cost =
      ∏ a : Fin d, if a ∈ S then max 1 (4 * directionMenuSum p dir a)
        else 4 ^ (directionGates p dir a).card := by
  classical
  simp only [BlockDecomposition.cost, menuBlockDecomposition]
  rw [prod_range_add]
  have hfirst : (∏ i ∈ range d,
      (if h1 : i < d then
        BlockKind.oneDim (if ⟨i, h1⟩ ∈ S then directionMenuSum p dir ⟨i, h1⟩ else 0)
      else if h2 : i - d < g then
        BlockKind.oneDim (if ⟨i - d, h2⟩ ∈ inputGates p ∧ dir ⟨i - d, h2⟩ ∉ S then 1 else 0)
      else BlockKind.oneDim 0).cost) =
      ∏ a : Fin d, if a ∈ S then max 1 (4 * directionMenuSum p dir a) else 1 := by
    rw [← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun a _ => ?_
    simp only [a.isLt, dite_true]
    by_cases ha : a ∈ S
    · simp [ha, cost_oneDim_eq_max]
    · simp [ha, BlockKind.cost]
  have hsecond : (∏ j ∈ range g,
      (if h1 : d + j < d then
        BlockKind.oneDim (if ⟨d + j, h1⟩ ∈ S then directionMenuSum p dir ⟨d + j, h1⟩ else 0)
      else if h2 : d + j - d < g then
        BlockKind.oneDim
          (if ⟨d + j - d, h2⟩ ∈ inputGates p ∧ dir ⟨d + j - d, h2⟩ ∉ S then 1 else 0)
      else BlockKind.oneDim 0).cost) =
      ∏ a : Fin d, if a ∈ S then 1 else 4 ^ (directionGates p dir a).card := by
    rw [← Fin.prod_univ_eq_prod_range]
    have hgate (gate : Fin g) :
        (if h1 : d + gate.val < d then
          BlockKind.oneDim (if ⟨d + gate.val, h1⟩ ∈ S then
            directionMenuSum p dir ⟨d + gate.val, h1⟩ else 0)
        else if h2 : d + gate.val - d < g then
          BlockKind.oneDim
            (if ⟨d + gate.val - d, h2⟩ ∈ inputGates p ∧ dir ⟨d + gate.val - d, h2⟩ ∉ S
              then 1 else 0)
        else BlockKind.oneDim 0).cost =
        if gate ∈ inputGates p then (if dir gate ∈ S then 1 else 4) else 1 := by
      have h1 : ¬ d + gate.val < d := by omega
      have h2 : d + gate.val - d < g := by omega
      rw [dite_eq_right h1, dite_eq_left h2]
      have h3 : (⟨d + gate.val - d, h2⟩ : Fin g) = gate := Fin.ext (Nat.add_sub_cancel_left d _)
      rw [h3]
      by_cases hin : gate ∈ inputGates p <;> by_cases hdS : dir gate ∈ S <;>
        simp [hin, hdS, BlockKind.cost]
    simp only [hgate]
    rw [prod_ite_mem_eq]
    rw [← prod_fiberwise_of_maps_to (t := univ) (g := dir) (fun _ _ => mem_univ _)]
    refine prod_congr rfl fun a _ => ?_
    change (∏ x ∈ directionGates p dir a, if dir x ∈ S then 1 else 4) = _
    have hconst : (∏ x ∈ directionGates p dir a, if dir x ∈ S then 1 else 4) =
        ∏ _x ∈ directionGates p dir a, (if a ∈ S then 1 else 4) := by
      refine prod_congr rfl fun x hx => ?_
      rw [(mem_directionGates p dir a x).mp hx |>.2]
    rw [hconst, prod_const]
    by_cases ha : a ∈ S <;> simp [ha]
  rw [hfirst, hsecond, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  by_cases ha : a ∈ S <;> simp [ha]

/-! ### Theorem 7.3 and corollaries -/

/-- **Theorem 7.3 (Direction-menu lower bound).** If the input-reading gates of `p` are partitioned
into `d` directions (`inputWeight p gate = scale gate • w (dir gate)`), then every Boolean readout
computing a two-sided `K`-rectangle-free function `f` satisfies
`2 ^ n < 4 * K ^ 2 * ∏ a : Fin d, min (4 ^ q_a) (max 1 (4 * T_a))`. -/
theorem two_pow_lt_of_directionMenus (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) (dir : Fin g → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin g → ℝ)
    (hdir : ∀ gate ∈ inputGates p, inputWeight p gate = scale gate • w (dir gate))
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ a : Fin d,
      min (4 ^ (directionGates p dir a).card) (max 1 (4 * directionMenuSum p dir a)) := by
  classical
  let S : Finset (Fin d) := univ.filter fun a =>
    max 1 (4 * directionMenuSum p dir a) ≤ 4 ^ (directionGates p dir a).card
  have h := (menuBlockDecomposition p readout dir w scale hdir S).two_pow_lt_mul_cost
    (fun b => by simpa only [hreadout] using hf b)
  rw [cost_menuBlockDecomposition] at h
  have hmin (a : Fin d) :
      (if a ∈ S then max 1 (4 * directionMenuSum p dir a)
        else 4 ^ (directionGates p dir a).card) =
      min (4 ^ (directionGates p dir a).card) (max 1 (4 * directionMenuSum p dir a)) := by
    simp only [S, mem_filter, mem_univ, true_and]
    split_ifs with hle
    · exact (min_eq_right hle).symm
    · exact (min_eq_left (le_of_not_ge hle)).symm
  simpa only [hmin] using h

/-- **Theorem 7.3 for circuits.** Direction-menu lower bound for a single-output circuit whose
output wire selects a gate. -/
theorem circuit_two_pow_lt_of_directionMenus (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) (dir : Fin c.size → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin c.size → ℝ)
    (hdir : ∀ gate ∈ inputGates c.program, inputWeight c.program gate = scale gate • w (dir gate))
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ a : Fin d,
      min (4 ^ (directionGates c.program dir a).card)
        (max 1 (4 * directionMenuSum c.program dir a)) := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_of_directionMenus c.program (fun z => z gate) dir w scale hdir ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- **Corollary 7.4 (Bounded predecessor fan-in).** If each input-reading gate reads at most `k`
earlier gate outputs with nonzero coefficients, then `T_a ≤ q_a * 2 ^ k` in every direction. -/
theorem two_pow_lt_of_directionMenus_fanIn (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) (dir : Fin g → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin g → ℝ)
    (hdir : ∀ gate ∈ inputGates p, inputWeight p gate = scale gate • w (dir gate))
    (k : ℕ) (hfanIn : ∀ gate ∈ inputGates p, (gateSupport p gate).card ≤ k)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ a : Fin d,
      min (4 ^ (directionGates p dir a).card)
        (max 1 (4 * ((directionGates p dir a).card * 2 ^ k))) := by
  refine (two_pow_lt_of_directionMenus p readout dir w scale hdir hreadout hf).trans_le ?_
  refine Nat.mul_le_mul_left _ (prod_le_prod fun a _ => min_le_min_left _ (max_le_max_left 1 ?_))
  refine Nat.mul_le_mul_left 4 ?_
  calc directionMenuSum p dir a
      ≤ ∑ _gate ∈ directionGates p dir a, 2 ^ k := by
        refine sum_le_sum fun gate hgate => ?_
        exact (card_biasMenu_le_two_pow_gateSupport p gate).trans
          (Nat.pow_le_pow_right Nat.two_pos
            (hfanIn gate ((mem_directionGates p dir a gate).mp hgate).1))
    _ = (directionGates p dir a).card * 2 ^ k := by simp

/-- **Corollary 7.4 for circuits.** Bounded internal fan-in direction-menu bound for a single-output
circuit whose output wire selects a gate. -/
theorem circuit_two_pow_lt_of_directionMenus_fanIn (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) (dir : Fin c.size → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin c.size → ℝ)
    (hdir : ∀ gate ∈ inputGates c.program, inputWeight c.program gate = scale gate • w (dir gate))
    (k : ℕ) (hfanIn : ∀ gate ∈ inputGates c.program, (gateSupport c.program gate).card ≤ k)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ a : Fin d,
      min (4 ^ (directionGates c.program dir a).card)
        (max 1 (4 * ((directionGates c.program dir a).card * 2 ^ k))) := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_of_directionMenus_fanIn c.program (fun z => z gate) dir w scale hdir k hfanIn
    ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- **Bounded integer internal weights.** If every input-reading gate has integer internal weights
of magnitude at most `W`, then `|biasMenu p gate| ≤ 1 + (g - 1) * W`, yielding
`T_a ≤ q_a * (1 + (g - 1) * W)`. -/
theorem two_pow_lt_of_directionMenus_intWeight (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) (dir : Fin g → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin g → ℝ)
    (hdir : ∀ gate ∈ inputGates p, inputWeight p gate = scale gate • w (dir gate))
    (W : ℕ) (w_int : Fin g → Fin g → ℤ)
    (hw_int : ∀ gate ∈ inputGates p, ∀ j, gateWeight p gate j = w_int gate j)
    (hW : ∀ gate ∈ inputGates p, ∀ j < gate, (w_int gate j).natAbs ≤ W)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ a : Fin d,
      min (4 ^ (directionGates p dir a).card)
        (max 1 (4 * ((directionGates p dir a).card * (1 + (g - 1) * W)))) := by
  refine (two_pow_lt_of_directionMenus p readout dir w scale hdir hreadout hf).trans_le ?_
  refine Nat.mul_le_mul_left _ (prod_le_prod fun a _ => min_le_min_left _ (max_le_max_left 1 ?_))
  refine Nat.mul_le_mul_left 4 ?_
  calc directionMenuSum p dir a
      ≤ ∑ _gate ∈ directionGates p dir a, (1 + (g - 1) * W) := by
        refine sum_le_sum fun gate hgate => ?_
        have hin := ((mem_directionGates p dir a gate).mp hgate).1
        have h1 := card_biasMenu_le_one_add_mul p gate W (w_int gate) (hw_int gate hin)
          (hW gate hin)
        have h2 : gate.val * W ≤ (g - 1) * W :=
          Nat.mul_le_mul_right W (by have := gate.isLt; omega)
        omega
    _ = (directionGates p dir a).card * (1 + (g - 1) * W) := by simp

/-- **Bounded integer internal weights for circuits.** -/
theorem circuit_two_pow_lt_of_directionMenus_intWeight (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) (dir : Fin c.size → Fin d)
    (w : Fin d → Fin n → ℝ) (scale : Fin c.size → ℝ)
    (hdir : ∀ gate ∈ inputGates c.program, inputWeight c.program gate = scale gate • w (dir gate))
    (W : ℕ) (w_int : Fin c.size → Fin c.size → ℤ)
    (hw_int : ∀ gate ∈ inputGates c.program, ∀ j, gateWeight c.program gate j = w_int gate j)
    (hW : ∀ gate ∈ inputGates c.program, ∀ j < gate, (w_int gate j).natAbs ≤ W)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ a : Fin d,
      min (4 ^ (directionGates c.program dir a).card)
        (max 1 (4 * ((directionGates c.program dir a).card * (1 + (c.size - 1) * W)))) := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_of_directionMenus_intWeight c.program (fun z => z gate) dir w scale hdir
    W w_int hw_int hW ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- **Single-direction bounded integer internal weights.** When all input-reading gates share one
direction `w` and have integer internal weights of magnitude at most `W`,
`2 ^ n < 4 * K ^ 2 * max 1 (4 * (|inputGates p| * (1 + (g - 1) * W)))`. -/
theorem two_pow_lt_of_direction_intWeight (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) (w : Fin n → ℝ) (scale : Fin g → ℝ)
    (hdir : ∀ gate ∈ inputGates p, inputWeight p gate = scale gate • w)
    (W : ℕ) (w_int : Fin g → Fin g → ℤ)
    (hw_int : ∀ gate ∈ inputGates p, ∀ j, gateWeight p gate j = w_int gate j)
    (hW : ∀ gate ∈ inputGates p, ∀ j < gate, (w_int gate j).natAbs ≤ W)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * max 1 (4 * ((inputGates p).card * (1 + (g - 1) * W))) := by
  have h := two_pow_lt_of_directionMenus_intWeight p readout (fun _ => (0 : Fin 1))
    (fun _ => w) scale hdir W w_int hw_int hW hreadout hf
  have hcard : (directionGates p (fun _ => (0 : Fin 1)) 0).card = (inputGates p).card := by
    simp [directionGates]
  rw [Fin.prod_univ_one, hcard] at h
  exact h.trans_le (Nat.mul_le_mul_left _ (min_le_right _ _))

end Cslib.Circuits.Boolean.WeightedThreshold
