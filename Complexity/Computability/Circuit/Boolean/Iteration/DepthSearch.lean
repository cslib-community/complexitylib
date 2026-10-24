/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.InputTime
public import Complexity.Computability.Circuit.Boolean.Iteration.Permutation
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Transient depths by binary search

A threshold `μ < 2 ^ n` is found with one query `μ ≤ v` per binary digit: keep the largest
candidate below `μ` found so far (`searchBelow`), and output one more than it, or zero
(`searchBelow_result`). Given circuits for the queries, this costs `n + 1` queries and a few word
operations per digit (`synthesis_threshold`).

For the transient depth, the query `transientDepth f x ≤ v` asks whether `f^[v] x` is periodic:
one input-time iteration and one periodicity test. This gives transient depths in at most
`200000 * (n + 1) ^ 2 * powerBudget n s (2 ^ n) L` gates (`depth_circuit`), and
`600000 * (n + 1) ^ 2 * optimizedBudget n s (2 ^ n)` balanced (`depth_circuit_optimized`). The
dictionary construction of `Iteration.Depth` avoids the factor `(n + 1) ^ 2`.

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. They exist for each `L`; nothing here bounds the time
to construct them.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.searchBelow`: the binary search for a threshold.
* `Cslib.Circuits.Boolean.Iteration.depthBudget`: the gate count of the search for depths.

## Main results

* `Cslib.Circuits.Boolean.Iteration.searchBelow_result`: the search finds the threshold.
* `Cslib.Circuits.Boolean.Iteration.synthesis_threshold`: its gate count.
* `Cslib.Circuits.Boolean.Iteration.depth_circuit`,
  `Cslib.Circuits.Boolean.Iteration.depth_circuit_optimized`: transient depths.

## References

* Adapted from lean/Proofs/{BinarySearch,DepthCircuit}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions], whose
  balanced bound has the constant `3000000`.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

/-- After `j` digits, the largest value of the form `searchBelow n μ j' + 2 ^ (n - j' - 1)`
below `μ`, built from the most significant of `n` digits. -/
def searchBelow (n μ : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if searchBelow n μ j + 2 ^ (n - j - 1) < μ
    then searchBelow n μ j + 2 ^ (n - j - 1) else searchBelow n μ j

private theorem searchBelow_bounds (n μ : ℕ) (hμ : μ ≤ 2 ^ n) (j : ℕ) (hj : j ≤ n) :
    (μ = 0 → searchBelow n μ j = 0) ∧
      (0 < μ → searchBelow n μ j < μ ∧ μ ≤ searchBelow n μ j + 2 ^ (n - j)) := by
  induction j with
  | zero => simp [searchBelow, hμ]
  | succ j ih =>
    obtain ⟨hz, hlo⟩ := ih (by omega)
    have hp : 2 ^ (n - j) = 2 ^ (n - j - 1) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    refine ⟨fun h => ?_, fun h => ?_⟩
    · subst h
      simpa only [searchBelow, Nat.not_lt_zero, ite_false] using hz rfl
    · obtain ⟨ha, hb⟩ := hlo h
      rw [hp] at hb
      rw [searchBelow, show n - (j + 1) = n - j - 1 by omega]
      split_ifs <;> constructor <;> omega

private theorem searchBelow_lt (n μ j : ℕ) (hμ : μ < 2 ^ n) (hj : j ≤ n) :
    searchBelow n μ j < 2 ^ n := by
  obtain ⟨hz, hp⟩ := searchBelow_bounds n μ hμ.le j hj
  rcases Nat.eq_zero_or_pos μ with h | h
  · rw [hz h]
    positivity
  · exact (hp h).1.trans hμ

/-- **Binary search.** One more than the last candidate below `μ`, or zero, is `μ`. -/
theorem searchBelow_result (n μ : ℕ) (hμ : μ ≤ 2 ^ n) :
    (if μ = 0 then 0 else searchBelow n μ n + 1) = μ := by
  obtain ⟨-, hp⟩ := searchBelow_bounds n μ hμ n le_rfl
  split_ifs with h
  · exact h.symm
  · obtain ⟨ha, hb⟩ := hp (by omega)
    simp only [Nat.sub_self, pow_zero] at hb
    omega

/-- **Threshold search.** If `μ x < 2 ^ n` and, from any family of available sources containing
`s`, every available `(n + 2)`-bit word `v` gives the query `μ x ≤ v` within `C` gates, then
`μ x` in `n + 2` bits costs `n + 1` queries and `16 * (n + 3)` gates per query for the word
operations. -/
theorem synthesis_threshold {a : ℕ} (s : Set (BooleanFunction a)) (μ : BitString a → ℕ)
    (n C : ℕ) (hμ : ∀ x, μ x < 2 ^ n) (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s)
    (query : ∀ src : Set (BooleanFunction a), s ⊆ src →
      ∀ value : BitString a → BitVec (n + 2), wordWires value ⊆ src →
        Synthesis interpretation src {fun x => decide (μ x ≤ (value x).toNat)} C) :
    Synthesis interpretation s (wordWires fun x => BitVec.ofNat (n + 2) (μ x))
      ((n + 1) * (C + 16 * (n + 3))) := by
  have hbig (j : ℕ) (hj : j ≤ n) : 2 ^ j < 2 ^ (n + 2) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  let value := fun j x => BitVec.ofNat (n + 2) (searchBelow n (μ x) j)
  let q := fun j => wordWires (value j)
  have hv (j : ℕ) (hj : j ≤ n) (x : BitString a) :
      (value j x).toNat = searchBelow n (μ x) j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact (searchBelow_lt n (μ x) j (hμ x) hj).trans (hbig n le_rfl)
  have hz : q 0 ⊆ s := by
    rintro _ ⟨bit, rfl⟩
    simpa [q, value, searchBelow] using hc false
  have hstep (j : ℕ) (hj : j < n) :
      Synthesis interpretation (s ∪ Synthesis.stages q j) (q (j + 1)) (C + 16 * (n + 3)) := by
    let src := s ∪ Synthesis.stages q j
    have hav (i : Fin (n + 2)) : (fun x => (value j x).getLsbD i.val) ∈ src :=
      Or.inr (Synthesis.subset_stages q le_rfl ⟨i, rfl⟩)
    let candidate := fun x => value j x + BitVec.ofNat (n + 2) (2 ^ (n - j - 1))
    have hcand (x : BitString a) :
        (candidate x).toNat = searchBelow n (μ x) j + 2 ^ (n - j - 1) := by
      have hs := searchBelow_lt n (μ x) j (hμ x) hj.le
      have hp : 2 ^ (n - j - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have h4 : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add]; ring
      simp only [candidate, BitVec.toNat_add, hv j hj.le, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 2 ^ (n - j - 1) < 2 ^ (n + 2) by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have hadd := Synthesis.word_add (s := src) (value j)
      (fun _ => BitVec.ofNat (n + 2) (2 ^ (n - j - 1))) hav fun _ => Or.inl (hc _)
    let src1 := src ∪ wordWires candidate
    have htest := query src1 (fun _ h => Or.inl (Or.inl h)) candidate fun _ h => Or.inr h
    have hm := Synthesis.word_mux (s := src1 ∪ {fun x => decide (μ x ≤ (candidate x).toNat)})
      (value j) candidate (fun x => decide (μ x ≤ (candidate x).toNat)) (Or.inr rfl)
      (fun i => Or.inl (Or.inl (hav i))) fun i => Or.inl (Or.inr ⟨i, rfl⟩)
    have he : (fun x => if decide (μ x ≤ (candidate x).toNat) then value j x else candidate x) =
        value (j + 1) := by
      funext x
      apply BitVec.eq_of_toNat_eq
      rw [hv (j + 1) (by omega), searchBelow]
      by_cases hh : searchBelow n (μ x) j + 2 ^ (n - j - 1) < μ x
      · rw [ite_eq_right (by rw [decide_eq_true_iff, hcand]; omega), hcand, ite_eq_left hh]
      · rw [ite_eq_left (by rw [decide_eq_true_iff, hcand]; omega), hv j hj.le, ite_eq_right hh]
    rw [he] at hm
    exact (hadd.trans (htest.trans hm)).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hsteps := Synthesis.steps q (C + 16 * (n + 3)) n hz hstep
  let src := s ∪ Synthesis.stages q n
  have hav (i : Fin (n + 2)) : (fun x => (value n x).getLsbD i.val) ∈ src :=
    Or.inr (Synthesis.subset_stages q le_rfl ⟨i, rfl⟩)
  let plus := fun x => value n x + 1
  have hadd := Synthesis.word_add (s := src) (value n) (fun _ => 1) hav fun _ => Or.inl (hc _)
  let src1 := src ∪ wordWires plus
  have htest := query src1 (fun _ h => Or.inl (Or.inl h)) (fun _ => 0)
    (by rintro _ ⟨i, rfl⟩; exact Or.inl (Or.inl (hc _)))
  have hm := Synthesis.word_mux (s := src1 ∪ {fun x => decide (μ x ≤ (0 : BitVec (n + 2)).toNat)})
    (fun _ => 0) plus (fun x => decide (μ x ≤ (0 : BitVec (n + 2)).toNat)) (Or.inr rfl)
    (fun i => Or.inl (Or.inl (Or.inl (hc _)))) fun i => Or.inl (Or.inr ⟨i, rfl⟩)
  have he : (fun x => if decide (μ x ≤ (0 : BitVec (n + 2)).toNat) then 0 else plus x) =
      fun x => BitVec.ofNat (n + 2) (μ x) := by
    funext x
    have hs := searchBelow_result n (μ x) (hμ x).le
    have h1 : (1 : BitVec (n + 2)).toNat = 1 := by
      change (BitVec.ofNat (n + 2) 1).toNat = 1
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
    have h0 : (0 : BitVec (n + 2)).toNat = 0 := rfl
    by_cases hz : μ x = 0
    · rw [ite_eq_left (by rw [h0, hz]; rfl), hz]
      rfl
    · rw [ite_eq_right hz] at hs
      apply BitVec.eq_of_toNat_eq
      rw [ite_eq_right (by rw [h0, decide_eq_true_iff]; omega), BitVec.toNat_add,
        hv n le_rfl, h1, hs, BitVec.toNat_ofNat]
  rw [he] at hm
  exact (hsteps.trans (hadd.trans (htest.trans hm))).mono Set.Subset.rfl Set.Subset.rfl
    (by rw [Nat.add_one_mul n (C + 16 * (n + 3))]; omega)

variable {n : ℕ}

/-- The gate count of the threshold search for transient depths. -/
def depthBudget (n s L : ℕ) : ℕ :=
  2 + (n + 1) * ((n + 2) * (40000 * powerBudget n s (2 ^ n) L + 4 * n) +
    (40000 * powerBudget n s (2 ^ n) L + (6 * n + 1)) + 16 * (n + 3))

/-- **Transient depths by binary search.** For every `0 < L ≤ 2 ^ n`, some circuit of size at
most `depthBudget n c.size L` computes the transient depth of every state in `n + 2` bits. -/
theorem depth_circuit (c : Circuit signature n n) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n (n + 2),
      (∀ x, word (out.eval interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval interpretation) x)) ∧
      out.size ≤ depthBudget n c.size L := by
  let f := c.eval interpretation
  obtain ⟨cyclic, hcyc, hcs⟩ := periodicPts_circuit c L hL hLN
  let constants : Set (BooleanFunction n) := {fun _ => false, fun _ => true}
  have hconst : Synthesis interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let s0 := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : BitString n => b) ∈ s0 := by cases b <;> simp [s0, constants]
  let C := (n + 2) * (40000 * powerBudget n c.size (2 ^ n) L + 4 * n) + cyclic.size
  have query (src : Set (BooleanFunction n)) (hs : s0 ⊆ src)
      (value : BitString n → BitVec (n + 2)) (hv : wordWires value ⊆ src) :
      Synthesis interpretation src {fun x => decide (transientDepth f x ≤ (value x).toNat)} C := by
    have hi := synthesis_binary_powering (m := n + 2) f _
      (fun j _ => fixed_power n c (2 ^ j) L hL hLN) src id (fun x i => (value x).getLsbD i.val)
      (fun _ h => hs (Or.inl (by obtain ⟨i, rfl⟩ := h; exact ⟨i, rfl⟩)))
      (by rintro _ ⟨i, rfl⟩; exact hv ⟨i, rfl⟩)
    simp only [word_getLsbD, id] at hi
    let current := fun x => f^[(value x).toNat] x
    have hq := Synthesis.circuit (I := interpretation) (s := src ∪ wires current) cyclic
      (fun i x => current x i) fun bit => Or.inr ⟨bit, rfl⟩
    refine (hi.trans hq).mono Set.Subset.rfl ?_ le_rfl
    rintro _ rfl
    refine ⟨0, funext fun x => Bool.eq_iff_iff.mpr ?_⟩
    change cyclic.eval interpretation (current x) 0 = true ↔ _
    rw [hcyc, iterate_mem_periodicPts_iff, decide_eq_true_iff]
  have h := hconst.trans (synthesis_threshold s0 (transientDepth f) n C
    (fun x => by simpa using transientDepth_lt_card f x) hc query)
  obtain ⟨out, hout, hs⟩ := h.exists_circuit_outputs
  refine ⟨out, fun x => by rw [hout x, word_getLsbD], hs.trans ?_⟩
  have hC : C + 16 * (n + 3) ≤ (n + 2) * (40000 * powerBudget n c.size (2 ^ n) L + 4 * n) +
      (40000 * powerBudget n c.size (2 ^ n) L + (6 * n + 1)) + 16 * (n + 3) := by
    simp only [C]
    omega
  have := Nat.mul_le_mul_left (n + 1) hC
  unfold depthBudget
  omega

/-- The threshold search costs at most a factor `(n + 1) ^ 2` more than a fixed power. -/
private theorem depthBudget_le (n s L : ℕ) :
    depthBudget n s L ≤ 200000 * (n + 1) ^ 2 * powerBudget n s (2 ^ n) L := by
  set B := powerBudget n s (2 ^ n) L
  have hb : (n + 1) ^ 3 ≤ B := by
    have h := Nat.mul_le_mul_left ((n + 1) ^ 3) (Nat.le_add_left 1 (L + 2 ^ n / L))
    simp only [B, powerBudget]
    nlinarith
  have hsmall : (n + 2) * (4 * n) + (6 * n + 1) + 16 * (n + 3) + 2 ≤ 100 * (n + 1) ^ 3 := by
    nlinarith [Nat.zero_le (n ^ 3)]
  have hsmall' := Nat.mul_le_mul_left (n + 1) hsmall
  have hB : (n + 1) * ((n + 1) ^ 3) ≤ (n + 1) ^ 2 * B := by
    have := Nat.mul_le_mul_left ((n + 1) ^ 2) hb
    nlinarith
  unfold depthBudget
  nlinarith [Nat.zero_le ((n + 1) ^ 2 * B), Nat.zero_le (n * B)]

/-- **Square-root transient depths by binary search.** Some circuit of size at most
`600000 * (n + 1) ^ 2 * optimizedBudget n c.size (2 ^ n)` computes the transient depth of every
state in `n + 2` bits. -/
theorem depth_circuit_optimized (c : Circuit signature n n) :
    ∃ out : Circuit signature n (n + 2),
      (∀ x, word (out.eval interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval interpretation) x)) ∧
      (out.size : ℝ) ≤ 600000 * (n + 1 : ℝ) ^ 2 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, ho⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := depth_circuit c L hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ 200000 * (n + 1 : ℝ) ^ 2 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
    exact_mod_cast hs.trans (depthBudget_le n c.size L)
  have h := mul_le_mul_of_nonneg_left ho (show 0 ≤ 200000 * (n + 1 : ℝ) ^ 2 by positivity)
  nlinarith

end Cslib.Circuits.Boolean.Iteration
