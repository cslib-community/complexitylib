/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Label
public import Complexity.Computability.Circuit.Boolean.Iteration.Optimization
public import Complexity.Computability.Circuit.Boolean.Iteration.SharedDictionary
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Circuits for canonical cycle labels

Let `c` be a circuit of size `s` computing `f` on `n`-bit states. Some circuit of size at most
`60000 * powerBudget n s (2 ^ n) L` computes the canonical label of every state: the
lexicographically least state of its eventual cycle, the cycle length and its phase
(`cycle_label_circuit`), for every `0 < L ≤ 2 ^ n`; with the balanced parameter the size is at
most `180000 * optimizedBudget n s (2 ^ n)` (`cycle_labels_optimized`).

The construction first applies `f^[(2 ^ n)!]` with a fixed-power circuit. This moves every state
onto its cycle without changing its label. On a periodic state, choose checkpoints as for fixed
powers and hardwire the label of each. The first `2 L + 1` states of the orbit are looked up in
one shared dictionary (`lookupOr`); a checkpoint hit at time `j` gives the label after shifting
its phase back by `j` (`correctLabel_canonicalLabel`). Without a hit the orbit repeats within `L`
steps, so its cycle is short and is read off the orbit prefix (`shortLabel_eq_canonicalLabel`).

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. The checkpoints and their labels are chosen
nonconstructively, so the circuits exist for each `L`; nothing here bounds the time to construct
them.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.labelCost`: the gate count of the checkpoint construction.

## Main results

* `Cslib.Circuits.Boolean.Iteration.cyclic_labels_from_checkpoints`: labels of periodic states
  from given checkpoints.
* `Cslib.Circuits.Boolean.Iteration.cyclic_label_circuit`: labels of periodic states.
* `Cslib.Circuits.Boolean.Iteration.cycle_label_circuit`,
  `Cslib.Circuits.Boolean.Iteration.cycle_labels_optimized`: labels of all states.

## References

* Adapted from lean/Proofs/LabelCircuits.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions], whose
  bounds have the constants `10040000` and `30120000`. The dictionary here is the library's
  `batchOrCircuit` lookup.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

attribute [local instance] lexOrder

variable {n M : ℕ}

/-- The gate count of the label construction from `M` checkpoints with parameter `L`: constants,
the orbit prefix, the shared dictionary, one label correction per prefix state, the short-cycle
label and the final selection. -/
def labelCost (n s M L : ℕ) : ℕ :=
  2 + 2 * L * s +
    48 * ((2 * L + 1) + M + 1) * (Nat.clog 2 ((2 * L + 1) + M) + 1) ^ 2 *
      (n + (labelWidth n + 1) + 1) +
    (2 * L + 1) * (50 * (n + 4) ^ 2) +
    ((2 * L + 1) * (30 * n + 27) + 50 * (n + 4) ^ 2) +
    (2 * L + 1) * (4 * labelWidth n)

/-- **Labels from checkpoints.** Let `cp` be injective checkpoints such that every orbit repeats
among its first `L` states or reaches a checkpoint in fewer than `2 L` steps. Then some circuit of
size at most `labelCost n c.size M L` computes the canonical label of every periodic state. -/
theorem cyclic_labels_from_checkpoints (c : Circuit signature n n) (L : ℕ) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) (cp : Fin M → BitString n) (hcp : Function.Injective cp)
    (hcover : ∀ x, Repeats (c.eval interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval interpretation)^[t] x = cp j) :
    ∃ out : Circuit signature n (labelWidth n),
      (∀ x ∈ Function.periodicPts (c.eval interpretation),
        out.eval interpretation x = canonicalLabel (c.eval interpretation) x) ∧
      out.size ≤ labelCost n c.size M L := by
  let f := c.eval interpretation
  let K := 2 * L
  let W := labelWidth n
  let constants : Set (BooleanFunction n) := {fun _ => false, fun _ => true}
  have hconst : Synthesis interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let s0 := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : BitString n => b) ∈ s0 := by cases b <;> simp [s0, constants]
  have horbit : Synthesis interpretation s0 (prefixWires f K) (K * c.size) :=
    Synthesis.orbit c id (fun bit => Or.inl ⟨bit, rfl⟩) K
  let s1 := s0 ∪ prefixWires f K
  have hp (j : Fin (K + 1)) (bit : Fin n) : (fun x => f^[j.val] x bit) ∈ s1 :=
    Or.inr (prefix_mem f (Nat.le_of_lt_succ j.isLt) bit)
  let stored : Fin M → BitString (W + 1) := fun i => Fin.cons true (canonicalLabel f (cp i))
  let queries : BitString n → Fin (K + 1) → BitString n := fun x j => f^[j.val] x
  have hdict := synthesis_lookupOr s1 cp stored queries fun j bit => hp j bit
  let result := fun x (j : Fin (K + 1)) => lookupOr cp stored (queries x j)
  let s2 := s1 ∪ ⋃ j, wires fun x => result x j
  have hresult (j : Fin (K + 1)) (bit : Fin (W + 1)) : (fun x => result x j bit) ∈ s2 :=
    Or.inr (Set.mem_iUnion.mpr ⟨j, bit, rfl⟩)
  let flags := fun x (j : Fin (K + 1)) => result x j 0
  let records := fun x (j : Fin (K + 1)) (bit : Fin W) => result x j bit.succ
  let corrected := fun (j : Fin (K + 1)) x => correctLabel (records x j) j.val
  have hcorrect := Synthesis.iUnion (fun j => wires (corrected j)) (fun _ => 50 * (n + 4) ^ 2)
    fun j => synthesis_correctLabel s2 (fun x => records x j)
      (by rintro _ ⟨bit, rfl⟩; exact hresult j bit.succ) (fun b => Or.inl (Or.inl (hc b))) j.val
  have hshort := synthesis_shortLabel s2 f id K (fun j bit => Or.inl (hp j bit))
    fun b => Or.inl (Or.inl (hc b))
  let s3 := s2 ∪ ((⋃ j, wires (corrected j)) ∪ wires fun x => shortLabel f K x)
  have hselect := synthesis_chooseRecord s3 flags (fun x j => corrected j x)
    (fun x => shortLabel f K x) (fun j => Or.inl (hresult j 0))
    (fun j bit => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨j, bit, rfl⟩)))
    fun bit => Or.inr (Or.inr ⟨bit, rfl⟩)
  have h := hconst.trans (horbit.trans (hdict.trans ((hcorrect.union hshort).trans hselect)))
  obtain ⟨out, hout, hs⟩ := h.exists_circuit_outputs
  refine ⟨out, fun x hx => ?_, hs.trans ?_⟩
  · rw [hout x]
    change chooseRecord (flags x) (fun j => corrected j x) (shortLabel f K x) (K + 1) =
      canonicalLabel f x
    by_cases hh : ∃ j, flags x j = true
    · obtain ⟨j, -, hj, he⟩ := chooseRecord_spec (flags x) (fun j => corrected j x)
        (shortLabel f K x) (K + 1) (by obtain ⟨j, hj⟩ := hh; exact ⟨j, j.isLt, hj⟩)
      rw [he]
      obtain ⟨i, hi, -⟩ := (decide_eq_true_iff.mp hj : ∃ i, cp i = _ ∧ stored i 0 = true)
      have hrecord : records x j = canonicalLabel f (f^[j.val] x) := by
        funext bit
        change lookupOr cp stored _ bit.succ = _
        rw [lookupOr_of_eq stored hcp hi]
        simp only [stored, Fin.cons_succ, hi]
        rfl
      change correctLabel (records x j) j.val = _
      rw [hrecord]
      apply correctLabel_canonicalLabel
      have := j.isLt
      have := Nat.one_le_two_pow (n := n)
      simp only [K, Nat.pow_succ] at *
      omega
    · have hnone : ∀ j, flags x j = false := fun j => Bool.eq_false_iff.mpr fun hj => hh ⟨j, hj⟩
      rw [chooseRecord_of_forall_eq_false _ _ _ hnone]
      apply shortLabel_eq_canonicalLabel f K hx
      rcases hcover x with ⟨i, j, hij, hj, he⟩ | ⟨t, ht, i, hi⟩
      · have := transientDepth_add_cycleLength_le_of_iterate_eq f x hij he
        omega
      · exfalso
        have hj := hnone ⟨t, by omega⟩
        simp only [flags, result, queries, lookupOr, decide_eq_false_iff_not] at hj
        exact hj ⟨i, hi.symm, rfl⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    unfold labelCost
    simp only [K, W, labelWidth] at hs ⊢
    omega

/-- The label construction is within `20000` times the fixed-power tradeoff. -/
private theorem labelCost_le (n s M L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hM : M ≤ 2 ^ n / L) :
    labelCost n s M L ≤ 20000 * powerBudget n s (2 ^ n) L := by
  unfold labelCost powerBudget
  set N := 2 ^ n with hNdef
  set d := Nat.clog 2 ((2 * L + 1) + M)
  set P := (n + 1) ^ 3
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hMN : M ≤ N := hM.trans (Nat.div_le_self _ _)
  have hd : d ≤ n + 2 := by
    apply Nat.clog_le_of_le_pow
    have h4 : 2 ^ (n + 2) = 4 * N := by rw [hNdef, pow_add]; ring
    omega
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hn1 : n + 1 ≤ P := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < n + 1 by omega) (by decide : 1 ≤ 3)
  have hn2 : (n + 1) ^ 2 ≤ P := Nat.pow_le_pow_right (by omega) (by decide)
  have hdict : 48 * ((2 * L + 1) + M + 1) * (d + 1) ^ 2 * (n + (labelWidth n + 1) + 1) ≤
      13824 * P * (L + N / L + 1) := by
    have h1 : (d + 1) ^ 2 ≤ 9 * (n + 1) ^ 2 := by
      have := Nat.pow_le_pow_left (show d + 1 ≤ 3 * (n + 1) by omega) 2
      nlinarith
    have h2 : n + (labelWidth n + 1) + 1 ≤ 8 * (n + 1) := by unfold labelWidth; omega
    have h3 : (2 * L + 1) + M + 1 ≤ 4 * (L + N / L + 1) := by omega
    calc 48 * ((2 * L + 1) + M + 1) * (d + 1) ^ 2 * (n + (labelWidth n + 1) + 1)
        ≤ 48 * (4 * (L + N / L + 1)) * (9 * (n + 1) ^ 2) * (8 * (n + 1)) := by gcongr
      _ = 13824 * P * (L + N / L + 1) := by simp only [P]; ring
  have hfour : (n + 4) ^ 2 ≤ 16 * (n + 1) ^ 2 := by
    have := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by omega) 2
    nlinarith
  have hrest : (2 * L + 1) * (50 * (n + 4) ^ 2) + ((2 * L + 1) * (30 * n + 27) +
      50 * (n + 4) ^ 2) + (2 * L + 1) * (4 * labelWidth n) + 2 ≤ 6000 * (P * (L + N / L + 1)) := by
    have h3L : 2 * L + 1 ≤ 3 * L := by omega
    have hw : 4 * labelWidth n ≤ 24 * (n + 1) := by unfold labelWidth; omega
    have e1 : (2 * L + 1) * (50 * (n + 4) ^ 2) ≤ 3 * L * (800 * P) :=
      Nat.mul_le_mul h3L (by nlinarith)
    have e2 : (2 * L + 1) * (30 * n + 27) ≤ 3 * L * (57 * P) := Nat.mul_le_mul h3L (by omega)
    have e3 : (2 * L + 1) * (4 * labelWidth n) ≤ 3 * L * (24 * P) :=
      Nat.mul_le_mul h3L (hw.trans (by omega))
    have e4 : 50 * (n + 4) ^ 2 + 2 ≤ 802 * P := by nlinarith
    have hLP : L * P ≤ P * (L + N / L + 1) := by nlinarith
    nlinarith
  nlinarith [Nat.zero_le (L * s)]

/-- **Labels of periodic states.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`20000 * powerBudget n c.size (2 ^ n) L` computes the canonical label of every periodic state. -/
theorem cyclic_label_circuit (c : Circuit signature n n) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n (labelWidth n),
      (∀ x ∈ Function.periodicPts (c.eval interpretation),
        out.eval interpretation x = canonicalLabel (c.eval interpretation) x) ∧
      out.size ≤ 20000 * powerBudget n c.size (2 ^ n) L := by
  classical
  obtain ⟨H, hcard, hcover⟩ := exists_checkpoints_finite (c.eval interpretation) hL
  let cp : Fin H.card → BitString n := fun j => (H.equivFin.symm j).val
  have hcp : Function.Injective cp := fun _ _ h => H.equivFin.symm.injective (Subtype.ext h)
  have hcov (x : BitString n) : Repeats (c.eval interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval interpretation)^[t] x = cp j := by
    rcases hcover x with hr | ⟨t, ht, hm⟩
    · exact Or.inl hr
    · exact Or.inr ⟨t, ht, H.equivFin ⟨_, hm⟩, by simp [cp]⟩
  obtain ⟨out, hout, hs⟩ := cyclic_labels_from_checkpoints c L hL hLN cp hcp hcov
  exact ⟨out, hout, hs.trans (labelCost_le _ _ _ _ hL hLN (by simpa using hcard))⟩

/-- Moving a state onto its cycle with `f^[(2 ^ n)!]` does not change its label. -/
private theorem canonicalLabel_iterate_factorial (f : BitString n → BitString n) (x : BitString n) :
    canonicalLabel f (f^[(2 ^ n).factorial] x) = canonicalLabel f x := by
  have hd := Nat.dvd_factorial (cycleLength_pos f x) (cycleLength_le_two_pow f x)
  simp only [canonicalLabel, canonicalCycle_iterate, cycleLength_iterate, phase_iterate,
    Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, Nat.mod_eq_of_lt (phase_lt f x)]

/-- Iterating `f` on `BitString n` for `(2 ^ n)!` steps lands on a periodic point. -/
theorem iterate_factorial_mem_periodicPts (f : BitString n → BitString n) (x : BitString n) :
    f^[(2 ^ n).factorial] x ∈ Function.periodicPts f := by
  apply (iterate_mem_periodicPts_iff f x _).mpr
  have hd : transientDepth f x < 2 ^ n := by simpa using transientDepth_lt_card f x
  exact hd.le.trans (Nat.self_le_factorial _)

/-- **Cycle labels.** For every `0 < L ≤ 2 ^ n`, some circuit of size at most
`60000 * powerBudget n c.size (2 ^ n) L` computes the canonical label of every state: the
lexicographically least state of its eventual cycle, the cycle length and its phase. -/
theorem cycle_label_circuit (c : Circuit signature n n) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n (labelWidth n),
      out.Computes interpretation (canonicalLabel (c.eval interpretation)) ∧
      out.size ≤ 60000 * powerBudget n c.size (2 ^ n) L := by
  obtain ⟨project, hp, hps⟩ := fixed_power n c (2 ^ n).factorial L hL hLN
  obtain ⟨labels, hl, hls⟩ := cyclic_label_circuit c L hL hLN
  refine ⟨labels.comp project, fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, hp x, hl _ (iterate_factorial_mem_periodicPts _ x),
      canonicalLabel_iterate_factorial]
  · rw [Circuit.size_comp]
    omega

/-- **Square-root cycle labels.** Some circuit of size at most
`180000 * optimizedBudget n c.size (2 ^ n)` computes the canonical label of every state. -/
theorem cycle_labels_optimized (c : Circuit signature n n) :
    ∃ out : Circuit signature n (labelWidth n),
      out.Computes interpretation (canonicalLabel (c.eval interpretation)) ∧
      (out.size : ℝ) ≤ 180000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := cycle_label_circuit c L hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ 60000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
    exact_mod_cast hs
  linarith

end Cslib.Circuits.Boolean.Iteration
