/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Hastad
public import Complexity.Computability.Circuit.Depth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Data.Nat.Div
import Complexity.Logics.Propositional.Parity
import Mathlib.Tactic.Positivity

/-!
# Håstad's theorem with the sharp exponent

**Håstad's theorem** [Hastad1986], [Jukna, Chapter 12][Jukna2012],
[Arora and Barak, Section 14.1][AroraBarak09] with the exponent `1 / (d - 1)`: a circuit of
negations and unbounded fan-in conjunctions and disjunctions whose AND/OR depth is at most `d`
(the largest number of conjunctions and disjunctions on a path, negations free:
`Circuit.depthWith Unbounded.andOrCost`), computing the parity of `n` bits, has at least `2 ^ s`
conjunctions and disjunctions for every `s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`
(`Unbounded.two_pow_le_card_andOr_of_computes_parity`). In particular it has at least `2 ^ s`
gates whenever `(17 s) ^ (d - 1) ≤ n` and `d ≥ 2`
(`Unbounded.two_pow_le_size_of_computes_parity_of_pow_le`), and at least
`2 ^ (n ^ (1 / (d - 1)) / 17) / 2` gates once `n ≥ 34 ^ (d - 1)`
(`Unbounded.two_rpow_le_two_mul_size_of_computes_parity`), a size `2 ^ Ω(n ^ (1 / (d - 1)))`
with explicit constants. The exponent is optimal: parity has circuits of AND/OR depth `d` with
`2 ^ O(n ^ (1 / (d - 1)))` gates [Hastad1986], and indeed every symmetric function has circuits of
AND/OR depth `d` with at most `2 ^ (C n ^ (1 / (d - 1))) + n` gates [LecomteRamakrishnan2026]
(`Unbounded.exists_circuit_of_isSymmetric`). Korten's top-down argument gives the same exponent
with an unspecified constant (`Unbounded.two_rpow_lt_add_size_of_computes_parity`). Since
negations are free, the bounds hold for `Circuit.depth`, which counts them
(`Circuit.depthWith_le_depth`, `Unbounded.two_pow_le_size_of_computes_parity_of_depth_le`),
improving the exponent `1 / (d + 1)` of `Unbounded.two_pow_le_size_of_computes_parity`, and for
formulas (`Unbounded.two_pow_le_size_of_formula_computes_parity_of_depthWith_le`).

The proof refines the one of `Unbounded.two_pow_le_size_of_computes_parity` in three ways.
* Negations are free: the stages are indexed by AND/OR depth, and only conjunctions and
  disjunctions are switched; a negation is shallow when its argument is
  (`Unbounded.shallow_trace_of_forall_ne_not`).
* The first stage switches conjunctions and disjunctions of literals, formulas in disjunctive
  normal form with terms of one literal, so it leaves a constant fraction `1 / 17` of the bits
  free rather than `1 / (16 s + 1)` (`Unbounded.two_pow_mul_card_filter_not_shallow_le_of_ne_not`
  with `k = 1`).
* There is no last stage: after `d - 1` stages every gate of AND/OR depth at most `d - 1` is
  shallow, so a gate of AND/OR depth `d` is, up to negation, a formula in disjunctive normal form
  with terms of fewer than `s` literals (`Unbounded.exists_dnf_of_shallow`), and such a formula
  cannot compute restricted parity on `s` or more free bits
  (`Cslib.Logic.PL.DNF.not_forall_eval_eq_parity_fill_bne`).

## Main results

* `Cslib.Circuits.Boolean.Unbounded.shallow_trace_of_forall_ne_not`: negations keep wires shallow.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_exists_not_shallow_le_depthWith`:
  random restrictions make the gates of small AND/OR depth shallow, stage by stage.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_card_andOr_of_computes_parity`: Håstad's theorem
  with the sharp exponent, counting conjunctions and disjunctions.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_depthWith_le`,
  `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_pow_le`,
  `Cslib.Circuits.Boolean.Unbounded.two_rpow_le_two_mul_size_of_computes_parity`: the same for the
  number of gates.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_depth_le`,
  `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_depth_le_of_pow_le`,
  `Cslib.Circuits.Boolean.Unbounded.two_rpow_le_two_mul_size_of_computes_parity_of_depth_le`: the
  same when depth counts negations.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity_of_depthWith_le`,
  `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity_of_pow_le`,
  `Cslib.Circuits.Boolean.Unbounded.two_rpow_le_two_mul_size_of_formula_computes_parity`: the same
  for formulas.

## References

* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [Lecomte and Ramakrishnan][LecomteRamakrishnan2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Cslib.BitString Cslib.DecisionTree Cslib.Logic.PL Finset

variable {n s g : ℕ} {ρ : PartialAssignment (Fin n)}

/-! ### Programs, with free negations -/

/-- The wires a conjunction or disjunction reads have smaller AND/OR depth. -/
private theorem wireDepthsWith_lines_add_one_le {p : Program signature n g} {k : Fin g}
    (hop : (p.lines k).op ≠ .not) (a : Fin (p.lines k).op.arity) :
    p.wireDepthsWith andOrCost ((p.lines k).wires a) + 1 ≤ p.depthsWith andOrCost k := by
  have h := p.wireDepthsWith_lines_add_le andOrCost k a
  rwa [andOrCost_eq_one_of_ne_not hop] at h

/-- If every conjunction and disjunction of AND/OR depth at most `j` is shallow under `ρ`, so is
every wire of AND/OR depth at most `j`: inputs are shallow, and negations keep functions
shallow. -/
theorem shallow_trace_of_forall_ne_not {p : Program signature n g} (hs : 2 ≤ s) {j : ℕ}
    (h : ∀ k, (p.lines k).op ≠ .not → p.depthsWith andOrCost k ≤ j →
      Shallow s ρ fun x => p.eval interpretation x k)
    (w : Wire n g) (hw : p.wireDepthsWith andOrCost w ≤ j) :
    Shallow s ρ fun x => p.trace interpretation x w := by
  refine p.wire_induction (P := fun w => p.wireDepthsWith andOrCost w ≤ j →
    Shallow s ρ fun x => p.trace interpretation x w) (fun i _ => shallow_proj hs ρ i) ?_ w hw
  intro k ih hk
  by_cases hop : (p.lines k).op = .not
  · have heq : (fun x => p.trace interpretation x (.gate k)) =
        fun x => !p.trace interpretation x ((p.lines k).wires ⟨0, by simp [hop]⟩) :=
      funext fun x => (p.trace_gate interpretation x k).trans
        (interpretation_of_op_eq_not hop (p.trace interpretation x))
    rw [heq]
    exact (ih _ ((Nat.le_add_right _ _).trans
      ((p.wireDepthsWith_lines_add_le andOrCost k _).trans hk))).not
  · exact h k hop hk

/-- Every wire of AND/OR depth zero, a literal, has decision tree depth at most one under every
restriction. -/
theorem shallow_two_trace_of_wireDepthsWith_eq_zero {p : Program signature n g}
    (ρ : PartialAssignment (Fin n)) (w : Wire n g) (hw : p.wireDepthsWith andOrCost w = 0) :
    Shallow 2 ρ fun x => p.trace interpretation x w :=
  shallow_trace_of_forall_ne_not le_rfl (fun k hop hk => absurd hk (by
    have := p.cost_le_depthsWith andOrCost k
    rw [andOrCost_eq_one_of_ne_not hop] at this
    omega)) w hw.le

/-- **One stage, counted, with free negations.** Let `1 ≤ k < s`. If every gate of AND/OR depth at
most `j` has decision tree depth at most `k` under `ρ`, at most an `H / 2 ^ s` fraction of the
extensions of `ρ` with `ℓ'` free bits make some gate of AND/OR depth at most `j + 1` `s`-deep,
where `H` is the number of conjunctions and disjunctions of AND/OR depth `j + 1`, when `s ≤ ℓ'`
and `(16 k + 1) ℓ'` is at most the number of free bits of `ρ`. -/
private theorem two_pow_mul_card_filter_extensions_le_depthWith {p : Program signature n g}
    {k j ℓ' : ℕ} (hk : 1 ≤ k) (hks : k + 1 ≤ s) (hsℓ' : s ≤ ℓ')
    (hℓ : (16 * k + 1) * ℓ' ≤ #ρ.free)
    (hgood : ∀ k', p.depthsWith andOrCost k' ≤ j →
      Shallow (k + 1) ρ fun x => p.eval interpretation x k') :
    2 ^ s * #{ρ' ∈ ρ.extensions ℓ' | ∃ k', p.depthsWith andOrCost k' ≤ j + 1 ∧
        ¬ Shallow s ρ' fun x => p.eval interpretation x k'} ≤
      #{k' | (p.lines k').op ≠ .not ∧ p.depthsWith andOrCost k' = j + 1} *
        #(ρ.extensions ℓ') := by
  set T : Finset (Fin g) := {k' | (p.lines k').op ≠ .not ∧ p.depthsWith andOrCost k' = j + 1}
  -- a bad extension makes a conjunction or disjunction of AND/OR depth exactly `j + 1` deep
  have hsub : {ρ' ∈ ρ.extensions ℓ' | ∃ k', p.depthsWith andOrCost k' ≤ j + 1 ∧
      ¬ Shallow s ρ' fun x => p.eval interpretation x k'} ⊆
      T.biUnion fun k' => {ρ' ∈ ρ.extensions ℓ' |
        ¬ Shallow s ρ' fun x => p.eval interpretation x k'} := by
    intro ρ' hρ'
    obtain ⟨hext, k₀, hk₀, hdeep⟩ := mem_filter.1 hρ'
    have hext' := (PartialAssignment.mem_extensions.1 hext).1
    by_contra hnot
    refine hdeep (shallow_trace_of_forall_ne_not (by omega) (j := j + 1) (fun k' hop hk' => ?_)
      (.gate k₀) hk₀)
    by_cases hk'j : p.depthsWith andOrCost k' ≤ j
    · exact ((hgood k' hk'j).of_le hks).mono hext'
    · by_contra hdeep'
      exact hnot (mem_biUnion.2 ⟨k', mem_filter.2 ⟨mem_univ _, hop, by omega⟩,
        mem_filter.2 ⟨hext, hdeep'⟩⟩)
  calc 2 ^ s * #{ρ' ∈ ρ.extensions ℓ' | ∃ k', p.depthsWith andOrCost k' ≤ j + 1 ∧
        ¬ Shallow s ρ' fun x => p.eval interpretation x k'}
      ≤ 2 ^ s * ∑ k' ∈ T, #{ρ' ∈ ρ.extensions ℓ' |
          ¬ Shallow s ρ' fun x => p.eval interpretation x k'} :=
        Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ k' ∈ T, 2 ^ s * #{ρ' ∈ ρ.extensions ℓ' |
          ¬ Shallow s ρ' fun x => p.eval interpretation x k'} := mul_sum _ _ _
    _ ≤ ∑ _k' ∈ T, #(ρ.extensions ℓ') := sum_le_sum fun k' hk' => by
        obtain ⟨hop, hdk⟩ := (mem_filter.1 hk').2
        -- gate `k'` is its operation on wires of AND/OR depth at most `j`
        have hgate : (fun x => p.eval interpretation x k') = fun x =>
            interpretation (p.lines k').op fun a =>
              p.trace interpretation x ((p.lines k').wires a) :=
          funext fun x => (p.lines_eval interpretation x k').symm
        rw [hgate]
        refine two_pow_mul_card_filter_not_shallow_le_of_ne_not hop (fun a => ?_) hsℓ' hℓ
        have hlt := wireDepthsWith_lines_add_one_le hop a
        cases hw : (p.lines k').wires a with
        | input i => exact shallow_proj (by omega) ρ i
        | gate k'' =>
          rw [hw, Program.wireDepthsWith_gateWire] at hlt
          exact hgood k'' (by omega)
    _ = #T * #(ρ.extensions ℓ') := by rw [sum_const, smul_eq_mul]

/-- **Random restrictions make the gates of small AND/OR depth shallow.** For `s ≥ 2` and
`s (16 s + 1) ^ e ≤ ⌊n / 17⌋`, after a first stage leaving `⌊n / 17⌋` bits free and `i ≤ e` more
stages each leaving a `1 / (16 s + 1)` fraction of the free bits, at most a `G / 2 ^ s` fraction of
the restrictions make some gate of AND/OR depth at most `i + 1` `s`-deep, where `G` is the number
of conjunctions and disjunctions of AND/OR depth at most `i + 1`. -/
theorem two_pow_mul_card_filter_exists_not_shallow_le_depthWith {p : Program signature n g}
    (hs : 2 ≤ s) {e : ℕ} (hn : s * (16 * s + 1) ^ e ≤ n / 17) (i : ℕ) (hi : i ≤ e) :
    2 ^ s * #{ρ ∈ PartialAssignment.withFree (Fin n) (n / 17 / (16 * s + 1) ^ i) |
        ∃ k, p.depthsWith andOrCost k ≤ i + 1 ∧
          ¬ Shallow s ρ fun x => p.eval interpretation x k} ≤
      #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k ≤ i + 1} *
        #(PartialAssignment.withFree (Fin n) (n / 17 / (16 * s + 1) ^ i)) := by
  have hsm : s ≤ n / 17 / (16 * s + 1) ^ i := Nat.le_div_pow_of_mul_pow_le (by omega) hi hn
  induction i with
  | zero =>
    -- the first stage switches conjunctions and disjunctions of literals
    rw [pow_zero, Nat.div_one] at hsm ⊢
    refine PartialAssignment.mul_card_filter_withFree_le (B := fun _ => False) (G := 0)
      (H := #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k = 0 + 1})
      (Nat.div_le_self n 17) le_rfl (by simp) (fun ρ hρ _ => ?_) ?_
    · refine two_pow_mul_card_filter_extensions_le_depthWith (k := 1) (j := 0) le_rfl hs hsm
        (by rw [PartialAssignment.mem_withFree.1 hρ]; omega) fun k' hk' => ?_
      exact shallow_two_trace_of_wireDepthsWith_eq_zero ρ (.gate k') (Nat.le_zero.1 hk')
    · rw [zero_add]
      refine card_le_card fun k hk => ?_
      simp only [mem_filter, mem_univ, true_and] at hk ⊢
      exact ⟨hk.1, hk.2.le⟩
  | succ i ih =>
    have ih := ih (by omega) (Nat.le_div_pow_of_mul_pow_le (by omega) (by omega) hn)
    set ℓ := n / 17 / (16 * s + 1) ^ i
    set ℓ' := n / 17 / (16 * s + 1) ^ (i + 1)
    have hℓ : (16 * s + 1) * ℓ' ≤ ℓ := Nat.mul_div_pow_succ_le (n / 17) _ i
    have hℓn : ℓ ≤ n := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
    have hℓ'ℓ : ℓ' ≤ ℓ := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hℓ
    -- the conjunctions and disjunctions of AND/OR depth at most `i + 2`
    have hG : #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k ≤ i + 1} +
        #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k = i + 1 + 1} ≤
        #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k ≤ i + 1 + 1} := by
      rw [← card_union_of_disjoint (disjoint_filter.2 fun k _ h₁ h₂ => by
        have := h₁.2
        have := h₂.2
        omega)]
      refine card_le_card fun k hk => ?_
      simp only [mem_union, mem_filter, mem_univ, true_and] at hk ⊢
      rcases hk with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨h₁, by omega⟩
      · exact ⟨h₁, h₂.le⟩
    refine PartialAssignment.mul_card_filter_withFree_le hℓ'ℓ hℓn ih (fun ρ hρ hb => ?_) hG
    -- a later stage switches conjunctions and disjunctions of shallow functions
    have hρℓ := PartialAssignment.mem_withFree.1 hρ
    refine two_pow_mul_card_filter_extensions_le_depthWith (k := s - 1) (j := i + 1) (by omega)
      (by omega) hsm ?_ fun k' hk' => ?_
    · rw [hρℓ]
      refine le_trans (Nat.mul_le_mul_right _ (by omega)) hℓ
    · rw [Nat.sub_add_cancel (by omega)]
      by_contra hdeep
      exact hb ⟨k', hk', hdeep⟩

/-- Under a restriction leaving at least `s ≥ 2` bits free and making every gate of AND/OR depth at
most `j` `s`-shallow, no wire of AND/OR depth at most `j + 1` computes restricted parity, up to
negation. -/
private theorem not_forall_trace_fill_eq_parity_bne {p : Program signature n g} (hs : 2 ≤ s)
    (hsρ : s ≤ #ρ.free) {j : ℕ}
    (h : ∀ k, p.depthsWith andOrCost k ≤ j → Shallow s ρ fun x => p.eval interpretation x k)
    (w : Wire n g) (hw : p.wireDepthsWith andOrCost w ≤ j + 1) (b : Bool) :
    ¬ ∀ y, p.trace interpretation (ρ.fill y) w = (parity n (ρ.fill y) != b) := by
  refine p.wire_induction (P := fun w => p.wireDepthsWith andOrCost w ≤ j + 1 → ∀ b,
    ¬ ∀ y, p.trace interpretation (ρ.fill y) w = (parity n (ρ.fill y) != b)) ?_ ?_ w hw b
  · -- an input is shallow, restricted parity is not
    intro i _ b hi
    have heq : (fun y => ρ.fill y i) = fun y => parity n (ρ.fill y) != b := funext hi
    have h₁ : Shallow s ρ fun x => parity n x != b := by
      change DecisionTree.complexity (fun y => parity n (ρ.fill y) != b) < s
      rw [← heq]
      exact shallow_proj hs ρ i
    refine not_shallow_parity hsρ ?_
    cases b
    · simpa using h₁
    · simpa using h₁.not
  · intro k ih hk b hk'
    by_cases hop : (p.lines k).op = .not
    · -- a negation computes restricted parity exactly when its argument computes its negation
      refine ih ⟨0, by simp [hop]⟩ ((Nat.le_add_right _ _).trans
        ((p.wireDepthsWith_lines_add_le andOrCost k _).trans hk)) (!b) fun y => ?_
      have hy := ((p.trace_gate interpretation (ρ.fill y) k).trans
        (interpretation_of_op_eq_not hop (p.trace interpretation (ρ.fill y)))).symm.trans (hk' y)
      revert hy
      cases p.trace interpretation (ρ.fill y) ((p.lines k).wires ⟨0, by simp [hop]⟩) <;>
        cases parity n (ρ.fill y) <;> cases b <;> simp
    · -- a conjunction or disjunction of shallow functions is a narrow formula in disjunctive
      -- normal form, up to negation
      have hargs : ∀ a, Shallow s ρ fun x => p.trace interpretation x ((p.lines k).wires a) :=
        fun a => by
          have hlt := wireDepthsWith_lines_add_one_le hop a
          cases hw' : (p.lines k).wires a with
          | input i => exact shallow_proj hs ρ i
          | gate k' =>
            rw [hw', Program.wireDepthsWith_gateWire] at hlt
            exact h k' (by change p.depthsWith andOrCost k ≤ j + 1 at hk; omega)
      obtain ⟨D, b', hD, heval⟩ := exists_dnf_of_shallow hop hargs
      refine DNF.not_forall_eval_eq_parity_fill_bne (fun t ht => (hD t ht).1.trans_le hsρ)
        (card_pos.1 (by omega)) (b != b') fun y => ?_
      have hy : interpretation (p.lines k).op
          (fun a => p.trace interpretation (ρ.fill y) ((p.lines k).wires a)) =
          (parity n (ρ.fill y) != b) :=
        (p.lines_eval interpretation (ρ.fill y) k).trans (hk' y)
      rw [heval y, hy]
      cases parity n (ρ.fill y) <;> cases b <;> cases b' <;> rfl

/-! ### Håstad's theorem -/

/-- **Håstad's theorem with the sharp exponent**, for programs: if a wire of AND/OR depth at most
`d` computes the parity of `n` bits, the program has at least `2 ^ s` conjunctions and
disjunctions, for every `s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
private theorem two_pow_le_card_andOr_of_trace_eq_parity {p : Program signature n g} {w : Wire n g}
    (hw : ∀ x, p.trace interpretation x w = parity n x) (hs : 2 ≤ s) {d : ℕ}
    (hd : p.wireDepthsWith andOrCost w ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ #{k | (p.lines k).op ≠ .not} := by
  by_contra! hS
  set e := d - 2
  set ℓ := n / 17 / (16 * s + 1) ^ e
  have hm : s * (16 * s + 1) ^ e ≤ n / 17 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by linarith)
  have hsℓ : s ≤ ℓ := Nat.le_div_pow_of_mul_pow_le (by omega) le_rfl hm
  -- fewer than all restrictions leaving `ℓ` bits free make some gate deep
  have h := two_pow_mul_card_filter_exists_not_shallow_le_depthWith (p := p) hs hm e le_rfl
  have hW : 0 < #(PartialAssignment.withFree (Fin n) ℓ) := by
    rw [PartialAssignment.card_withFree, Fintype.card_fin]
    exact Nat.mul_pos (Nat.choose_pos ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _)))
      (by positivity)
  have hcard : #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k ≤ e + 1} ≤
      #{k | (p.lines k).op ≠ .not} :=
    card_le_card fun k hk => by
      simp only [mem_filter, mem_univ, true_and] at hk ⊢
      exact hk.1
  have hlt : #{ρ ∈ PartialAssignment.withFree (Fin n) ℓ | ∃ k, p.depthsWith andOrCost k ≤ e + 1 ∧
      ¬ Shallow s ρ fun x => p.eval interpretation x k} <
      #(PartialAssignment.withFree (Fin n) ℓ) := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ s) (h.trans_lt ?_)
    exact Nat.mul_lt_mul_of_pos_right (hcard.trans_lt hS) hW
  obtain ⟨ρ, hρ, hgood⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hall : ∀ k, p.depthsWith andOrCost k ≤ e + 1 →
      Shallow s ρ fun x => p.eval interpretation x k := fun k hk => by
    by_contra hdeep
    exact hgood (mem_filter.2 ⟨hρ, k, hk, hdeep⟩)
  exact not_forall_trace_fill_eq_parity_bne hs ((PartialAssignment.mem_withFree.1 hρ).symm ▸ hsℓ)
    hall w (by omega) false fun y => by rw [hw, Bool.bne_false]

/-- **Håstad's theorem with the sharp exponent**, counting conjunctions and disjunctions. A circuit
of negations and unbounded fan-in conjunctions and disjunctions of AND/OR depth at most `d`
computing the parity of `n` bits has at least `2 ^ s` conjunctions and disjunctions, for every
`s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`. Their number is the AND/OR cost
`C.program.cost andOrCost` (`cost_andOrCost_eq_card`). -/
theorem two_pow_le_card_andOr_of_computes_parity {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ}
    (hd : C.depthWith andOrCost ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ #{k | (C.program.lines k).op ≠ .not} :=
  two_pow_le_card_andOr_of_trace_eq_parity (fun x => congrFun (hC x) 0) hs
    ((C.wireDepthsWith_outputs_le_depthWith andOrCost 0).trans hd) hn

/-- **Håstad's theorem with the sharp exponent.** A circuit of negations and unbounded fan-in
conjunctions and disjunctions of AND/OR depth at most `d` computing the parity of `n` bits has at
least `2 ^ s` gates, for every `s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
theorem two_pow_le_size_of_computes_parity_of_depthWith_le {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ}
    (hd : C.depthWith andOrCost ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ C.size :=
  (two_pow_le_card_andOr_of_computes_parity hC hs hd hn).trans
    ((card_filter_le _ _).trans (by simp))

/-! ### Round numbers -/

/-- The hypothesis `(17 s) ^ (d - 1) ≤ n` is stronger than `17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
private theorem mul_pow_le_of_pow_le (hs : 2 ≤ s) {d : ℕ} (hd₂ : 2 ≤ d)
    (hn : (17 * s) ^ (d - 1) ≤ n) : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n := by
  refine le_trans ?_ hn
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [show e + 2 - 2 = e by omega, show e + 2 - 1 = e + 1 by omega, pow_succ']
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) e)

/-- Bounds `2 ^ s ≤ m` for every `s ≥ 2` with `(17 s) ^ (d - 1) ≤ n` give
`2 ^ (n ^ (1 / (d - 1)) / 17) ≤ 2 m` once `n ≥ 34 ^ (d - 1)`. -/
private theorem two_rpow_le_two_mul_of_forall {d m : ℕ} (hd₂ : 2 ≤ d) (hn : 34 ^ (d - 1) ≤ n)
    (h : ∀ s, 2 ≤ s → (17 * s) ^ (d - 1) ≤ n → 2 ^ s ≤ m) :
    (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 17) ≤ 2 * m := by
  set r := (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)
  have hd1 : d - 1 ≠ 0 := by omega
  have hr : r ^ (d - 1) = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) hd1
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg n) _
  -- `r ≥ 34`
  have hr34 : 34 ≤ r := by
    have h34 : ((34 : ℝ) ^ (d - 1)) ^ (((d - 1 : ℕ) : ℝ)⁻¹) = 34 :=
      Real.pow_rpow_inv_natCast (by norm_num) hd1
    rw [← h34]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by positivity)
  set s := ⌊r / 17⌋₊
  have hs : 2 ≤ s := Nat.le_floor (by norm_num; linarith)
  have hsr : (17 * s : ℝ) ≤ r := by
    have := Nat.floor_le (a := r / 17) (by positivity)
    linarith
  have hsn : (17 * s) ^ (d - 1) ≤ n := by
    have : ((17 * s : ℕ) : ℝ) ^ (d - 1) ≤ r ^ (d - 1) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsr) _
    rw [hr] at this
    exact_mod_cast this
  have hsize : (2 : ℝ) ^ s ≤ m := by exact_mod_cast h s hs hsn
  calc (2 : ℝ) ^ (r / 17) ≤ 2 ^ ((s + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by push_cast; exact (Nat.lt_floor_add_one _).le)
    _ = 2 * 2 ^ s := by rw [Real.rpow_natCast, pow_succ']
    _ ≤ 2 * m := by linarith

/-- **Håstad's theorem with the sharp exponent**, in round numbers. A circuit of negations and
unbounded fan-in conjunctions and disjunctions of AND/OR depth at most `d ≥ 2` computing the
parity of `n` bits has at least `2 ^ s` gates, for every `s ≥ 2` with `(17 s) ^ (d - 1) ≤ n`. -/
theorem two_pow_le_size_of_computes_parity_of_pow_le {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ} (hd₂ : 2 ≤ d)
    (hd : C.depthWith andOrCost ≤ d) (hn : (17 * s) ^ (d - 1) ≤ n) : 2 ^ s ≤ C.size :=
  two_pow_le_size_of_computes_parity_of_depthWith_le hC hs hd (mul_pow_le_of_pow_le hs hd₂ hn)

/-- **Håstad's theorem with the sharp exponent**, as a real bound. A circuit of negations and
unbounded fan-in conjunctions and disjunctions of AND/OR depth at most `d ≥ 2` computing the
parity of `n ≥ 34 ^ (d - 1)` bits has at least `2 ^ (n ^ (1 / (d - 1)) / 17) / 2` gates. -/
theorem two_rpow_le_two_mul_size_of_computes_parity {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) {d : ℕ} (hd₂ : 2 ≤ d)
    (hd : C.depthWith andOrCost ≤ d) (hn : 34 ^ (d - 1) ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 17) ≤ 2 * C.size :=
  two_rpow_le_two_mul_of_forall hd₂ hn fun _ hs hsn =>
    two_pow_le_size_of_computes_parity_of_pow_le hC hs hd₂ hd hsn

/-! ### Depth counting negations -/

/-- **Håstad's theorem with the sharp exponent, when depth counts negations.** A circuit of
negations and unbounded fan-in conjunctions and disjunctions of depth at most `d` computing the
parity of `n` bits has at least `2 ^ s` gates, for every `s ≥ 2` with
`17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
theorem two_pow_le_size_of_computes_parity_of_depth_le {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ}
    (hd : C.depth ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) : 2 ^ s ≤ C.size :=
  two_pow_le_size_of_computes_parity_of_depthWith_le hC hs
    ((C.depthWith_le_depth andOrCost_le_one).trans hd) hn

/-- **Håstad's theorem with the sharp exponent, when depth counts negations**, in round numbers:
at least `2 ^ s` gates for every `s ≥ 2` with `(17 s) ^ (d - 1) ≤ n`, when `d ≥ 2`. -/
theorem two_pow_le_size_of_computes_parity_of_depth_le_of_pow_le {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ} (hd₂ : 2 ≤ d)
    (hd : C.depth ≤ d) (hn : (17 * s) ^ (d - 1) ≤ n) : 2 ^ s ≤ C.size :=
  two_pow_le_size_of_computes_parity_of_depth_le hC hs hd (mul_pow_le_of_pow_le hs hd₂ hn)

/-- **Håstad's theorem with the sharp exponent, when depth counts negations**, as a real bound: at
least `2 ^ (n ^ (1 / (d - 1)) / 17) / 2` gates when `d ≥ 2` and `n ≥ 34 ^ (d - 1)`. -/
theorem two_rpow_le_two_mul_size_of_computes_parity_of_depth_le {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) {d : ℕ} (hd₂ : 2 ≤ d)
    (hd : C.depth ≤ d) (hn : 34 ^ (d - 1) ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 17) ≤ 2 * C.size :=
  two_rpow_le_two_mul_of_forall hd₂ hn fun _ hs hsn =>
    two_pow_le_size_of_computes_parity_of_depth_le_of_pow_le hC hs hd₂ hd hsn

/-! ### Formulas -/

/-- **Håstad's theorem with the sharp exponent, for formulas.** A formula of negations and unbounded
fan-in conjunctions and disjunctions of AND/OR depth at most `d` computing the parity of `n` bits
has at least `2 ^ s` operation nodes, for every `s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
theorem two_pow_le_size_of_formula_computes_parity_of_depthWith_le {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) (hs : 2 ≤ s) {d : ℕ}
    (hd : F.depthWith andOrCost ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ F.size :=
  F.size_toCircuit ▸ two_pow_le_size_of_computes_parity_of_depthWith_le hF.toCircuit hs
    ((F.depthWith_toCircuit_le andOrCost).trans hd) hn

/-- **Håstad's theorem with the sharp exponent, for formulas**, in round numbers: at least `2 ^ s`
operation nodes for every `s ≥ 2` with `(17 s) ^ (d - 1) ≤ n`, when `d ≥ 2`. -/
theorem two_pow_le_size_of_formula_computes_parity_of_pow_le {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) (hs : 2 ≤ s) {d : ℕ} (hd₂ : 2 ≤ d)
    (hd : F.depthWith andOrCost ≤ d) (hn : (17 * s) ^ (d - 1) ≤ n) : 2 ^ s ≤ F.size :=
  two_pow_le_size_of_formula_computes_parity_of_depthWith_le hF hs hd
    (mul_pow_le_of_pow_le hs hd₂ hn)

/-- **Håstad's theorem with the sharp exponent, for formulas**, as a real bound: at least
`2 ^ (n ^ (1 / (d - 1)) / 17) / 2` operation nodes when `d ≥ 2` and `n ≥ 34 ^ (d - 1)`. -/
theorem two_rpow_le_two_mul_size_of_formula_computes_parity {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) {d : ℕ} (hd₂ : 2 ≤ d)
    (hd : F.depthWith andOrCost ≤ d) (hn : 34 ^ (d - 1) ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 17) ≤ 2 * F.size :=
  two_rpow_le_two_mul_of_forall hd₂ hn fun _ hs hsn =>
    two_pow_le_size_of_formula_computes_parity_of_pow_le hF hs hd₂ hd hsn

end Cslib.Circuits.Boolean.Unbounded
