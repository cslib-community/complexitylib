/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Negative

/-!
# Razborov's lower bound for monotone circuits computing cliques

Evaluate a monotone circuit computing `k`-clique in the approximate interpretation. On the
complete graphs on `k`-sets the circuit is right, so the approximator at its output is wrong on at
most `C(n, k)`-many of them only if the circuit is large (`Positive.scheme`); if it is right on one,
it is nonempty. A nonempty approximator accepts at least half of the colourings with `k - 1`
colours, on which the circuit is right and says `false`, so it is wrong on half of them, which
again needs a large circuit (`Negative.scheme`). Either way the circuit is large
(`choose_le_or_pow_le_mul_size`), with explicit bounds (`lt_size_of_computes_clique`)
[Razborov][Razborov1985], [Arora and Barak, Theorem 14.7][AroraBarak09].

## Main results

* `Cslib.Circuits.Monotone.choose_le_or_pow_le_mul_size`: the dichotomy.
* `Cslib.Circuits.Monotone.lt_size_of_computes_clique`: the lower bound with explicit parameters.

## References

* [A. A. Razborov, *Lower bounds on the monotone complexity of some Boolean
  functions*][Razborov1985]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 14.3][AroraBarak09]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 9][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

open Cslib.Circuits.Clique Finset Approximator

variable {n k p w : ℕ}

/-- The number of negative errors charged to any gate. -/
def negativeGateCap (n r p w : ℕ) : ℕ :=
  (2 * sunflowerBound p w + sunflowerBound p w ^ 2) * Negative.pluckErrorCap n r p w

private theorem Positive.errorCost_le (op : Op) :
    Positive.errorCost n k p w op ≤ Positive.errorCap n k p w := by
  cases op <;> simp [Positive.errorCost]

private theorem Negative.errorCost_le (hp : 2 ≤ p) (r : ℕ) (op : Op) :
    Negative.errorCost n r p w op ≤ negativeGateCap n r p w := by
  have hB := sunflowerBound_pos hp w
  unfold negativeGateCap
  cases op with
  | const => exact Nat.le_mul_of_pos_left _ (by omega)
  | or => exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  | and => exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

variable [Fact (2 ≤ p)]

/-- The approximator of the output of a circuit. -/
noncomputable def outputApproximator (C : Circuit signature (edgeCount n) 1) : Approximator n p w :=
  C.eval Approximator.interpretation Approximator.input 0

/-- If the circuit is small, the approximator of its output is right on some complete graph on a
`k`-set, and so is nonempty. -/
theorem nonempty_outputApproximator (hw : 2 ≤ w) (hk : w + 1 ≤ k)
    {C : Circuit signature (edgeCount n) 1} (hC : C.Computes interpretation (single (clique n k)))
    (hC' : Positive.errorCap n k p w * C.size < n.choose k) :
    (outputApproximator C : Approximator n p w).terms.Nonempty := by
  classical
  let S := Positive.scheme (n := n) (k := k) (p := p) hw hk
  have hF : (S.failures univ (outputApproximator C) fun _ => true).card ≤
      C.program.cost S.errorCost := S.card_failures_le_cost univ C fun c _ => by
    rw [hC, single, clique_ofFinset (mem_powersetCard.1 c.2).2]
  have hcost : C.program.cost S.errorCost ≤ Positive.errorCap n k p w * C.size :=
    (C.program.cost_mono fun op => Positive.errorCost_le op).trans_eq (C.program.cost_const _)
  obtain ⟨c, hc⟩ : ∃ c, c ∉ S.failures univ (outputApproximator C) fun _ => true := by
    by_contra! h
    have := card_le_card fun c (_ : c ∈ (univ : Finset (CliqueSet n k))) => h c
    rw [card_univ, Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin] at this
    omega
  simp only [S.mem_failures, mem_univ, true_and, not_not] at hc
  obtain ⟨s, hs, -⟩ := decode_eq_true.1 (Bool.eq_true_of_true_le hc)
  exact ⟨s, hs⟩

/-- The approximator of the output of a circuit computing `k`-clique accepts only colourings with
`k - 1` colours on which it is wrong, and so at most as many as the negative cost of the
circuit. -/
private theorem card_acceptedColorings_le (hw : 2 ≤ w) (hk : 0 < k)
    {C : Circuit signature (edgeCount n) 1} (hC : C.Computes interpretation (single (clique n k))) :
    (Negative.acceptedColorings (k - 1) (outputApproximator C : Approximator n p w).terms).card ≤
      C.program.cost (Negative.errorCost n (k - 1) p w) := by
  classical
  let S := Negative.scheme (n := n) (r := k - 1) (p := p) hw
  refine (card_le_card fun c hc => ?_).trans
    (S.card_failures_le_cost univ C (target := fun _ => false) fun c _ => by
      rw [hC, single, clique_ofColoring (by omega)])
  rw [S.mem_failures]
  refine ⟨mem_univ _, ?_⟩
  have : (C.eval Approximator.interpretation Approximator.input 0 : Approximator n p w).decode
      (ofColoring c) = true :=
    decode_eq_true.2 (mem_filter.1 hc).2
  rw [this]
  change ¬(true ≤ false)
  decide

/-- **Razborov's dichotomy.** A monotone circuit computing `k`-clique on `n` vertices exhausts the
positive or the negative error budget of the approximators with `p` petals and width `w`. -/
theorem choose_le_or_pow_le_mul_size (hw : 2 ≤ w) (hk : w + 1 ≤ k) (hr : 2 * w ^ 2 ≤ k - 1)
    {C : Circuit signature (edgeCount n) 1} (hC : C.Computes interpretation (single (clique n k))) :
    n.choose k ≤ Positive.errorCap n k p w * C.size ∨
      (k - 1) ^ n ≤ 2 * negativeGateCap n (k - 1) p w * C.size := by
  refine or_iff_not_imp_left.2 fun hpos => ?_
  have hn : 0 < n := by
    by_contra hn
    have hchoose : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    exact hpos (hchoose ▸ Nat.zero_le _)
  have hne := nonempty_outputApproximator (p := p) hw hk hC (not_le.1 hpos)
  have hhalf := Negative.half_le_card_acceptedColorings (r := k - 1) hn hr
    (outputApproximator C : Approximator n p w).card_le_of_mem hne
  have hcost : C.program.cost (Negative.errorCost n (k - 1) p w) ≤
      negativeGateCap n (k - 1) p w * C.size :=
    (C.program.cost_mono fun op => Negative.errorCost_le Fact.out _ op).trans_eq
      (C.program.cost_const _)
  calc (k - 1) ^ n ≤ 2 * (Negative.acceptedColorings (k - 1)
        (outputApproximator C : Approximator n p w).terms).card := hhalf
    _ ≤ 2 * (negativeGateCap n (k - 1) p w * C.size) :=
        Nat.mul_le_mul_left 2 ((card_acceptedColorings_le hw (by omega) hC).trans hcost)
    _ = 2 * negativeGateCap n (k - 1) p w * C.size := (Nat.mul_assoc _ _ _).symm

omit [Fact (2 ≤ p)] in
/-- **Razborov's lower bound.** Every monotone circuit computing `k`-clique on `n` vertices has more
than `s` gates, for every `s` below both error budgets of the approximators with `p ≥ 2` petals and
width `w ≥ 2`, if `w + 1 ≤ k` and `2 w ^ 2 ≤ k - 1`. -/
theorem lt_size_of_computes_clique (hp : 2 ≤ p) (hw : 2 ≤ w) (hk : w + 1 ≤ k)
    (hr : 2 * w ^ 2 ≤ k - 1) {s : ℕ} (hpos : Positive.errorCap n k p w * s < n.choose k)
    (hneg : 2 * negativeGateCap n (k - 1) p w * s < (k - 1) ^ n)
    {C : Circuit signature (edgeCount n) 1} (hC : C.Computes interpretation (single (clique n k))) :
    s < C.size := by
  have : Fact (2 ≤ p) := ⟨hp⟩
  by_contra! h
  rcases choose_le_or_pow_le_mul_size (p := p) hw hk hr hC with h' | h'
  · exact absurd (h'.trans (Nat.mul_le_mul_left _ h)) (not_le.2 hpos)
  · exact absurd (h'.trans (Nat.mul_le_mul_left _ h)) (not_le.2 hneg)

end Cslib.Circuits.Monotone
