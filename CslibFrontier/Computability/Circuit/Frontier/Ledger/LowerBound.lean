/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Circuit.Frontier.Layouts.Components
public import CslibFrontier.Computability.Circuit.Frontier.Ledger.Aggregate
public import CslibFrontier.Computability.Circuit.Frontier.Ledger.Sweep
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound
import Mathlib.Tactic.Ring

/-!
# The frontier lower bound with gates of unbounded fan-in

**Main theorem** (`eventually_lt_mul_card_of_ledger`). Fix `r ≥ 2` and assume the layout
hypothesis `LayoutBound (r + 1) A`. Let `S_n ⊆ U^n` be dense `K_n`-rectangle-free sets with
`log K_n = o(n)`, as in `Cslib.Circuits.Frontier.eventually_lt_mul_innerSize`, and let
`β(n) = o(n)`. For every `ε > 0` and all large `n`, every circuit deciding `S_n` whose gates have
fan-in at most `r`, except for *special* gates of any fan-in that have a ledger in a monoid `M`
with `log |M| ≤ β(n)`, has `s` ordinary inner gates (inner gates that are not special) with

`(r - 1) s > (1 + 1/A - ε) n`.

Constants and special gates are free; the ledger contributes only to the sublinear error. So the
coefficient of the frontier method survives a sublinear amount of unbounded fan-in. For instance,
`k` special gates that aggregate in a fixed finite commutative monoid `T`, such as unbounded AND,
OR, parity, or counts modulo a fixed `m`, have a ledger with `log |M| = k log |T|`
(`Cslib.Circuits.Frontier.Ledger.ofAggregates`), so `k = o(n)` such gates are allowed
(`eventually_lt_mul_card_of_aggregates`). With the layout hypothesis of coefficient one
(`Cslib.Circuits.Frontier.layoutBound_one`) the bounds are unconditional:
`(r - 1) s > (2 - ε) n` (the module
`CslibFrontier.Computability.Circuit.Frontier.Ledger.Unconditional`).

**Proof.** Erase the special gates and lay out the live network (the graph of the erased program
with every live wire as an output), one connected component after another
(`Cslib.Circuits.Frontier.LayoutBound.exists_layout_componentwise`). Sweep the program along this
layout with the ledger in the messages (`Cslib.Circuits.Frontier.Ledger.sweep`). At each step the
transitions are bounded both by the width of the step and by the number of inputs read in the
component being processed. The frontier counting lemma then finds a component `W` that reads
almost all `n` inputs and whose frontier is wide, up to `3 log |M|` and the usual error terms
(`Cslib.Circuits.Frontier.Ledger.exists_ncard_le`). The cycle rank of `W` is at most
`(r - 1) s + 1` minus the number of inputs it reads
(`Cslib.Circuits.Frontier.Compiler.cycleRankOn_add_ncard_readIn_le`), so `W` alone has the
demand and the supply of a connected graph, and the comparison of demand and supply
(`Cslib.Circuits.Frontier.eventually_lt_of_frontier`, with the ledger in its sublinear slack)
finishes the proof.

## Main results

* `Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger`: the frontier lower bound with a
  ledger, conditional on `LayoutBound`.
* `Cslib.Circuits.Frontier.eventually_lt_mul_card_of_aggregates`: the frontier lower bound with
  aggregate gates, conditional on `LayoutBound`.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics

universe u v w

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The frontier lower bound with a ledger.** Let `r ≥ 2` and assume the layout hypothesis for
maximum degree `r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over
a finite alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`, and let `β(n) = o(n)`. Then for every `ε > 0` and all large `n`,
every circuit deciding `S_n`, over any basis and interpretation on `U`, whose gates have fan-in at
most `r` except for special gates of any fan-in with a ledger in a finite commutative monoid `M`
with `log |M| ≤ β(n)`, has `s` ordinary inner gates, the inner gates that are not special, with
`(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_card_of_ledger {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (M : Type w)
      [CommMonoid M] [Finite M],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        Ledger special c.program I M → Real.log (Nat.card M) ≤ β n → c.Decides I Acc (S n) →
          (1 + 1 / A - ε) * n <
            (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log two_pos (by exact_mod_cast Finite.one_lt_card)
  -- The ledger costs three products in `M`, at most `3 β(n) / log 2` symbols.
  have hβ' : (fun n => 3 * (β n / Real.log 2)) =o[atTop] fun n => (n : ℝ) :=
    (hβ.const_mul_left (3 / Real.log 2)).congr_left fun n => by ring
  obtain ⟨η, hη, H⟩ := eventually_lt_of_frontier hA (r + 2) hSK.isLittleO_log
    hSK.isLittleO_deficit hβ' hε
  obtain ⟨C, hC⟩ := hlayout.exists_layout_componentwise hη
  filter_upwards [H C, hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    eventually_ge_atTop 1] with n hn hfreen hbign hn1
  intro σ I Acc c special _ M _ _ hfan L hM hS
  -- The set decided by the circuit is the set accepted by its program at its output.
  set o := c.outputs 0
  have hSeq : S n = {x | c.program.trace I x o ∈ Acc} := by
    ext x
    exact hS x
  rw [hSeq] at hfreen hbign
  have hK1 := hfreen.pos
  have hKS : K n ≤ {x | c.program.trace I x o ∈ Acc}.ncard :=
    (Nat.le_mul_of_pos_left _ Nat.card_pos).trans
      ((Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero _)).trans hbign)
  -- Lay out the live network one component after another.
  set lc := liveCircuit c.program special
  set V := Nat.card (Compiler.Vertex lc)
  set N := liveNetwork c.program special U
  have hfan' : lc.FanInAtMost r := (Program.fanInAtMost_eraseGates_iff (special := special)).2 hfan
  obtain ⟨π, hπ⟩ := hC _ _ (Compiler.graph lc) Compiler.loopless (Compiler.maxDegreeLE hr hfan')
  obtain ⟨t, ht, hcount⟩ := L.exists_ncard_le π hfreen hKS (card_vertex_liveCircuit_pos hn1)
    fun t ht => union_subset (hπ t ht t le_rfl (by omega)).1 (hπ t ht (t + 1) (by omega) le_rfl).1
  -- The quantities of the comparison: the component `W` of the vertex processed at step `t`, the
  -- width `a` of the step and the inputs `nW` read in `W`.
  set W := N.component (π.symm ⟨t, ht⟩)
  set se := (c.program.innerGates.filter fun g => ¬special g).card
  have hse : lc.innerSize = se := innerSize_liveCircuit
  set a := (N.frontier π t ∪ N.frontier π (t + 1)).ncard + (N.readAt (π.symm ⟨t, ht⟩)).ncard
  set nW := (N.readIn W).ncard
  set s : ℝ := (((r - 1) * se : ℕ) : ℝ)
  have hs : s = (r - 1) * se := by
    simp only [s]
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  -- The width of the step is at most its first frontier and the edges of the vertex processed.
  have ha : (a : ℝ) ≤ (N.frontier π t).ncard + (r + 2) := by
    have hU : (N.frontier π t ∪ N.frontier π (t + 1)).ncard ≤ (N.frontier π t).ncard + (r + 1) :=
      (ncard_le_ncard (union_subset subset_union_left (N.frontier_succ_subset π ht))
        (toFinite _)).trans ((ncard_union_le _ _).trans
          (Nat.add_le_add_left (Compiler.maxDegreeLE hr hfan' _) _))
    have hR : (N.readAt (π.symm ⟨t, ht⟩)).ncard ≤ 1 :=
      Compiler.ncard_readAt_le (I.withConstants (L.readout 1)) (fun _ => univ) _
    have : a ≤ (N.frontier π t).ncard + (r + 2) := by simp only [a]; omega
    exact_mod_cast this
  -- The cycle rank of the component and the inputs it reads.
  have hρ : (N.cycleRankOn W : ℝ) + nW ≤ s + 1 := by
    have h := Compiler.cycleRankOn_add_ncard_readIn_le (I.withConstants (L.readout 1))
      (fun _ => univ) hfan' (N.edgeCut_component (π.symm ⟨t, ht⟩))
      (N.ncard_component_le_ncard_touching_add_one (π.symm ⟨t, ht⟩))
    rw [hse] at h
    simp only [s]
    exact_mod_cast h
  -- The size of the graph: at most `2 r s' + 3 (n + s')` vertices for `s'` ordinary inner gates.
  have hV : (V : ℝ) ≤ 7 * s + 3 * n + 3 := by
    have h := Compiler.card_vertex_le hfan'
    have hlive := card_live_le (p := c.program) (special := special)
    rw [hse] at h hlive
    have : V ≤ 7 * ((r - 1) * se) + 3 * n := by
      have h7 : 2 * r + 3 ≤ 7 * (r - 1) := by omega
      have := Nat.mul_le_mul_right se h7
      simp only [V]
      nlinarith
    have : (V : ℝ) ≤ 7 * s + 3 * n := by simp only [s]; exact_mod_cast this
    linarith
  -- Take logarithms in the counting bound.
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hcount' : ({x | c.program.trace I x o ∈ Acc}.ncard : ℝ) ≤
      (K n : ℝ) ^ 2 * (V + 1) * (Nat.card M : ℝ) ^ 3 * (q : ℝ) ^ (min a nW) := by
    have : (K n - 1) ^ 2 ≤ K n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
    have h := hcount.trans (by gcongr : (K n - 1) ^ 2 * (V + 1) * Nat.card M ^ 3 * q ^ min a nW ≤
      K n ^ 2 * (V + 1) * Nat.card M ^ 3 * q ^ min a nW)
    exact_mod_cast h
  have hSpos : (0 : ℝ) < {x | c.program.trace I x o ∈ Acc}.ncard := by
    have : 0 < {x | c.program.trace I x o ∈ Acc}.ncard := lt_of_lt_of_le hK1 hKS
    exact_mod_cast this
  have hlogS : Real.logb q {x | c.program.trace I x o ∈ Acc}.ncard ≤
      2 * Real.logb q (K n) + Real.logb q (V + 1) + 3 * Real.logb q (Nat.card M) + min a nW := by
    have hK0 : (0 : ℝ) < K n := by exact_mod_cast hK1
    have hM0 : (0 : ℝ) < Nat.card M := by exact_mod_cast hMpos
    calc _ ≤ Real.logb q ((K n : ℝ) ^ 2 * (V + 1) * (Nat.card M : ℝ) ^ 3 * (q : ℝ) ^ (min a nW)) :=
          Real.logb_le_logb_of_le hq hSpos hcount'
      _ = _ := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
            (by positivity), Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
            Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hq]
          push_cast
          ring
  rw [← hSeq] at hlogS
  -- The logarithms of the threshold and of the ledger.
  have hlogM : 3 * Real.logb q (Nat.card M) ≤ 3 * (β n / Real.log 2) := by
    have h0 : 0 ≤ Real.log (Nat.card M) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hMpos.ne')
    have h1 : Real.logb q (Nat.card M) ≤ β n / Real.log 2 :=
      (div_le_div_of_nonneg_left h0 h2 hL2).trans (div_le_div_of_nonneg_right hM h2.le)
    linarith
  have hlogK : 0 ≤ Real.logb q (K n) := Real.logb_nonneg hq (by exact_mod_cast hK1)
  have hmin1 : ((min a nW : ℕ) : ℝ) ≤ a := by exact_mod_cast min_le_left a nW
  have hmin2 : ((min a nW : ℕ) : ℝ) ≤ nW := by exact_mod_cast min_le_right a nW
  rw [← hs]
  refine hn s V (N.cycleRankOn W) (N.frontier π t).ncard (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hV ?_ ?_ (hπ t ht t le_rfl (by omega)).2
  · -- The component reads almost all inputs, so its cycle rank is small.
    linarith
  · -- Some frontier is wide.
    linarith

/-- **The frontier lower bound with aggregate gates.** Under the hypotheses of
`eventually_lt_mul_card_of_ledger`, for every `ε > 0` and all large `n`, every circuit deciding
`S_n`, over any basis and interpretation on `U`, whose gates have fan-in at most `r` except for
`k` special gates of any fan-in that aggregate in a finite commutative monoid `T`, with
`k log |T| ≤ β(n)`, has `s` ordinary inner gates with `(r - 1) s > (1 + 1/A - ε) n`. For instance,
the special gates may compute unbounded AND, OR, parity, or counts modulo a fixed `m`. -/
theorem eventually_lt_mul_card_of_aggregates {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc (S n) →
          (1 + 1 / A - ε) * n <
            (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  filter_upwards [eventually_lt_mul_card_of_ledger.{u, v, w} hr hA hlayout hSK hβ hε] with n hn
  intro σ I Acc c special _ T _ _ hfan hagg hk hS
  refine hn σ I Acc c special _ hfan (Ledger.ofAggregates hagg) ?_ hS
  rw [Nat.card_fun, Nat.cast_pow, Real.log_pow]
  exact hk

end Cslib.Circuits.Frontier
