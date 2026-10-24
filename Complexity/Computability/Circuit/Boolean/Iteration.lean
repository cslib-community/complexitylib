/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Decoder
public import Complexity.Foundations.Combinatorics.FunctionalGraph.Checkpoints
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Circuits for fixed powers

Let `c` be a Boolean circuit with `n` inputs and `n` outputs of size `s`, computing a map `f` on
`n`-bit states. Every fixed power `f^[T]` has a circuit of size at most
`40000 * (L * s + (n + 1) ^ 3 * (L + 2 ^ n / L + 1))` for every `0 < L ≤ 2 ^ n`
(`fixed_power`). More precisely, on a finite set `S` of states with `f '' S ⊆ S`, a circuit of
size at most `40000 * powerBudget n s S.card L` agrees with `f^[T]` on `S` (`fixed_power_on`);
`powerBudget n s M L = L * s + (n + 1) ^ 3 * (L + M / L + 1)`.

The construction follows [Schlesinger2026IteratedFunctions]. Choose at most `|S| / L` checkpoints
in `S` such that the first `L` states of every orbit from `S` repeat or reach a checkpoint within
`2 L` steps (`FunctionalGraph.exists_checkpoints`), and hardwire each checkpoint `h` together
with `f^[T - 2 L] h`. On input `x`, compute the first `2 L + 1` states of the orbit with copies of
`c`, sort them together with the checkpoints, and detect a collision. A checkpoint hit at time
`d` gives `f^[T] x` after `2 L - d` further steps of the stored state; a repeat gives it as a
prefix state at the time congruent to `T`. Short exponents `T < 2 L` use `T` copies of `c`.

The circuit model is CSLib's native De Morgan basis: every NOT, AND and OR gate and every
constant is charged, wiring and fanout are free. The circuits exist for each `T`, `S` and `L`;
the checkpoints are chosen nonconstructively, so nothing here bounds the time to construct them.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.powerBudget`: the size tradeoff.
* `Cslib.Circuits.Boolean.Iteration.FixedPowerOnBound`, `FixedPowerBound`: the tradeoffs with
  some constant.
* `Cslib.Circuits.Boolean.Iteration.fixedOutput`: output function of the fixed-power circuit for a
  given exponent, prefix length, sorting depth, and checkpoint table.

## Main results

* `Cslib.Circuits.Boolean.Iteration.fixed_power_on`: the invariant-set bound with constant 40000.
* `Cslib.Circuits.Boolean.Iteration.fixed_power`: the bound on all states.

## References

* Adapted from lean/Statement.lean and lean/Proofs/{Construction,FixedPower}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

/-- The fixed-power tradeoff `L * s + (n + 1) ^ 3 * (L + M / L + 1)` for states of `n` bits, a
transition circuit of size `s`, `M` relevant states and parameter `L`. -/
def powerBudget (n s M L : ℕ) : ℕ :=
  L * s + (n + 1) ^ 3 * (L + M / L + 1)

/-- Some constant `C` bounds a circuit for every fixed power on every invariant set by
`C * powerBudget`. -/
def FixedPowerOnBound : Prop :=
  ∃ C : ℕ, ∀ (n : ℕ) (c : Circuit signature n n) (S : Finset (BitString n)) (T L : ℕ),
    (∀ x ∈ S, c.eval interpretation x ∈ S) → 0 < L → L ≤ 2 ^ n →
    ∃ d : Circuit signature n n,
      d.ComputesOn interpretation ↑S (c.eval interpretation)^[T] ∧
      d.size ≤ C * powerBudget n c.size S.card L

/-- Some constant `C` bounds a circuit for every fixed power by `C * powerBudget` with all
`2 ^ n` states. -/
def FixedPowerBound : Prop :=
  ∃ C : ℕ, ∀ (n : ℕ) (c : Circuit signature n n) (T L : ℕ), 0 < L → L ≤ 2 ^ n →
    ∃ d : Circuit signature n n,
      d.Computes interpretation (c.eval interpretation)^[T] ∧
      d.size ≤ C * powerBudget n c.size (2 ^ n) L

variable {n w M : ℕ}

/-- The wire functions of `Record.initial` lie in `s` whenever `s` contains the orbit prefix wires
and both Boolean constants. -/
theorem Record.initial_wires_subset (s : Set (BooleanFunction n)) (f : BitString n → BitString n)
    {R : ℕ} (T K : ℕ) (cp : Fin M → BitString n) (hp : prefixWires f K ⊆ s)
    (hc : ∀ b : Bool, (fun _ : BitString n => b) ∈ s) :
    Record.recordsWires (fun x => Record.initial (R := R) (w := w) f T K cp x) ⊆ s := by
  intro fn hfn
  obtain ⟨j, bit, rfl⟩ := Set.mem_iUnion.mp hfn
  dsimp only [Record.initial]
  split_ifs with h1 h2
  · exact hc _
  · induction bit using Fin.addCases with
    | left bit =>
      induction bit using Fin.cases with
      | zero => exact hc false
      | succ bit => simpa [Record.encode, Record.query] using hp (prefix_mem f h2 bit)
    | right bit =>
      simp only [Record.encode, Record.query, Fin.append_right]
      exact hc _
  · exact hc _

/-- The output of the fixed-power circuit for exponent `T`, prefix length `K`, sorting depth `d`
and checkpoints `cp`. -/
def fixedOutput (c : Circuit signature n n) (T K d : ℕ) (cp : Fin M → BitString n)
    (x : BitString n) : BitString n :=
  let pair := Record.detect (Record.sorted d (Record.initial (w := w)
    (c.eval interpretation) T K cp x))
  reconstruct (c.eval interpretation) T K x pair.1 pair.2

/-- There exists a circuit computing `fixedOutput c T K d cp` within the combined gate budget for
orbit generation, sorting, collision detection, and state reconstruction. -/
theorem exists_fixedOutput (c : Circuit signature n n) (T K d : ℕ) (cp : Fin M → BitString n) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (fixedOutput (w := w) c T K d cp) ∧
      out.size ≤ 2 + 5 * K * c.size + (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n w + 1) +
        1000 * (K + 1) * (n + w + 1) ^ 2 := by
  let f := c.eval interpretation
  let constants : Set (BooleanFunction n) := {fun _ => false, fun _ => true}
  have hconst : Synthesis interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let s := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : BitString n => b) ∈ s := by cases b <;> simp [s, constants]
  have hp : Synthesis interpretation s (prefixWires f K) (K * c.size) :=
    Synthesis.orbit c id (fun bit => Or.inl ⟨bit, rfl⟩) K
  let records := fun x => Record.initial (R := BitonicSort.arity d) (w := w) f T K cp x
  let sorted := fun x => Record.sorted d (records x)
  let pair := fun x => Record.detect (sorted x)
  let s1 := s ∪ prefixWires f K
  have hs := Record.synthesis_sorted s1 d records
    (Record.initial_wires_subset s1 f T K cp (fun _ h => Or.inr h) fun b => Or.inl (hc b))
  let s2 := s1 ∪ Record.recordsWires sorted
  have hd := Record.synthesis_detect s2 sorted
    (fun j _ h => Or.inr (Record.wireSet_subset_recordsWires sorted j h))
    fun b => Or.inl (Or.inl (hc b))
  let s3 := s2 ∪ Record.pairWires pair
  have hout := synthesis_reconstruct s3 c T K (fun x => (pair x).1) (fun x => (pair x).2)
    (fun _ h => Or.inr (Record.wireSet_fst_subset pair h))
    (fun _ h => Or.inr (Record.wireSet_snd_subset pair h))
    (fun _ h => Or.inl (Or.inl (Or.inr h))) fun b => Or.inl (Or.inl (Or.inl (hc b)))
  have h := hconst.trans (hp.trans (hs.trans (hd.trans hout)))
  have hfinal : Synthesis interpretation (inputs n)
      (wires (fixedOutput (w := w) c T K d cp))
      (2 + 5 * K * c.size + (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n w + 1) +
        1000 * (K + 1) * (n + w + 1) ^ 2) := by
    apply h.mono Set.Subset.rfl Set.Subset.rfl
    rw [BitonicSort.arity_eq_two_pow]
    ring_nf
    exact le_rfl
  exact hfinal.exists_circuit_outputs

/-- Arithmetic bound bounding the raw `exists_fixedOutput` gate count for prefix length `2 * L` and
time width `n + 2` by `40000 * (L * s + (n + 1) ^ 3 * (L + M + 1))`. -/
theorem construction_cost (n s M L d : ℕ) (hL : 0 < L) (hd : d ≤ n + 2)
    (hR : 2 ^ d ≤ 2 * (M + 2 * L + 1)) :
    2 + 5 * (2 * L) * s + (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n (n + 2) + 1) +
      1000 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 ≤
      40000 * (L * s + (n + 1) ^ 3 * (L + M + 1)) := by
  have h1 : 18 * d ^ 2 + 30 ≤ 102 * (n + 1) ^ 2 := by
    have hs : d ^ 2 ≤ (n + 2) ^ 2 := by gcongr
    nlinarith
  have h2 : Record.width n (n + 2) + 1 ≤ 5 * (n + 1) := by unfold Record.width; omega
  have hs : (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n (n + 2) + 1) ≤
      (102 * (n + 1) ^ 2) * (2 * (M + 2 * L + 1)) * (5 * (n + 1)) := by gcongr
  have h3 : (n + (n + 2) + 1) ^ 2 ≤ 9 * (n + 1) ^ 2 := by nlinarith
  have hh : 1000 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 ≤
      1000 * (3 * L) * (9 * (n + 1) ^ 2) := by gcongr; omega
  nlinarith [Nat.zero_le (L * n ^ 3), Nat.zero_le (M * n ^ 3),
    Nat.zero_le (M * n ^ 2), Nat.zero_le (L * n ^ 2), Nat.zero_le (L * s)]

/-- **Fixed powers on an invariant set.** If `c` maps the finite set `S` into itself, then for
every exponent `T` and every `0 < L ≤ 2 ^ n` some circuit of size at most
`40000 * powerBudget n c.size S.card L` agrees with `T` applications of `c` on `S`. -/
theorem fixed_power_on (n : ℕ) (c : Circuit signature n n) (S : Finset (BitString n))
    (T L : ℕ) (hS : ∀ x ∈ S, c.eval interpretation x ∈ S) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      out.ComputesOn interpretation ↑S (c.eval interpretation)^[T] ∧
      out.size ≤ 40000 * powerBudget n c.size S.card L := by
  classical
  let f := c.eval interpretation
  by_cases hT : T < 2 * L
  · refine ⟨c.iterate T, fun x _ => by rw [Circuit.eval_iterate], ?_⟩
    rw [Circuit.size_iterate]
    have ht : T * c.size ≤ 2 * L * c.size := Nat.mul_le_mul_right _ hT.le
    unfold powerBudget
    nlinarith [Nat.zero_le ((n + 1) ^ 3 * (L + S.card / L + 1))]
  obtain ⟨H, hHS, hcard, hcover⟩ := FunctionalGraph.exists_checkpoints f S hS hL
  let cp : Fin H.card → BitString n := fun j => (H.equivFin.symm j).val
  let d := Nat.clog 2 (H.card + 2 * L + 1)
  have hcapacity : H.card + (2 * L + 1) ≤ BitonicSort.arity d := by
    simpa only [BitonicSort.arity_eq_two_pow, d, Nat.add_assoc] using
      Nat.le_pow_clog (by decide : 1 < 2) (H.card + 2 * L + 1)
  have hN : H.card ≤ 2 ^ n := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using
      Finset.card_le_univ H
  have hd : d ≤ n + 2 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega
  have hR : 2 ^ d ≤ 2 * (H.card + 2 * L + 1) := by
    have hpos : 0 < d := Nat.clog_pos (by decide) (by omega)
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
      (show 1 < H.card + 2 * L + 1 by omega)
    have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by rw [← Nat.pow_succ, show (d - 1).succ = d by omega]
    rw [hpow]
    change 2 ^ (d - 1) < _ at hp
    omega
  have hfit : 2 * L < 2 ^ (n + 2) := by
    simp only [Nat.pow_succ]
    omega
  obtain ⟨out, hout, hsize⟩ := exists_fixedOutput (w := n + 2) c T (2 * L) d cp
  refine ⟨out, fun x hx => ?_, ?_⟩
  · rw [hout x]
    apply reconstruct_spec f T (2 * L) cp x _ _ hfit (by omega)
    apply Record.detect_sorted_witness f T (2 * L) d cp x hcapacity hfit
    rcases hcover x hx with ⟨i, j, hij, hj, heq⟩ | ⟨t, ht, hmem⟩
    · exact Or.inr ⟨i, j, hij, by omega, heq⟩
    · exact Or.inl ⟨t, ht.le, H.equivFin ⟨f^[t] x, hmem⟩, by simp [cp]⟩
  · have hc : H.card ≤ S.card / L := (Nat.le_div_iff_mul_le hL).mpr hcard
    apply hsize.trans ((construction_cost n c.size H.card L d hL hd hR).trans ?_)
    unfold powerBudget
    gcongr

/-- The invariant-set fixed-power bound holds with universal constant `40000`. -/
theorem fixedPowerOnBound : FixedPowerOnBound := ⟨40000, fixed_power_on⟩

/-- **Fixed powers.** For every exponent `T` and every `0 < L ≤ 2 ^ n` some circuit of size at
most `40000 * powerBudget n c.size (2 ^ n) L` computes `T` applications of `c`. -/
theorem fixed_power (n : ℕ) (c : Circuit signature n n) (T L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 40000 * powerBudget n c.size (2 ^ n) L := by
  classical
  obtain ⟨out, hout, hsize⟩ := fixed_power_on n c Finset.univ T L
    (fun _ _ => Finset.mem_univ _) hL hLN
  exact ⟨out, fun x => hout (Finset.mem_coe.mpr (Finset.mem_univ x)), by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      using hsize⟩

/-- The global fixed-power bound holds with universal constant `40000`. -/
theorem fixedPowerBound : FixedPowerBound := ⟨40000, fixed_power⟩

end Cslib.Circuits.Boolean.Iteration
