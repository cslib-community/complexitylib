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

The argument reads the circuit only on the two families of test inputs, so it applies to every
monotone circuit separating the graphs with a `k`-clique from the `(k - 1)`-colourable graphs
(`Cslib.Circuits.Clique.Separates`), not only to those computing `k`-clique
(`lt_size_of_separates`). Bounds on such separators transfer to resolution through monotone
feasible interpolation [Krajíček, Section 7][Krajicek1997].

## Main definitions

* `Cslib.Circuits.Monotone.negativeGateCap`: the bound on negative errors charged to any gate.
* `Cslib.Circuits.Monotone.outputApproximator`: the approximator at the output of a circuit.

## Main results

* `Cslib.Circuits.Monotone.separates_of_computes_clique`: a circuit computing `k`-clique separates
  the graphs with a `k`-clique from the `(k - 1)`-colourable graphs.
* `Cslib.Circuits.Monotone.choose_le_or_pow_le_mul_size`: the dichotomy, for separating circuits.
* `Cslib.Circuits.Monotone.lt_size_of_separates`,
  `Cslib.Circuits.Monotone.lt_size_of_computes_clique`: the lower bound with explicit parameters,
  for separating circuits and for circuits computing `k`-clique.

## References

* [A. A. Razborov, *Lower bounds on the monotone complexity of some Boolean
  functions*][Razborov1985]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 14.3][AroraBarak09]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 9][Jukna2012]
* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
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

/-- If the circuit is small and accepts the complete graph on every `k`-set, the approximator of
its output is right on one of them, and so is nonempty. -/
theorem nonempty_outputApproximator (hw : 2 ≤ w) (hk : w + 1 ≤ k)
    {C : Circuit signature (edgeCount n) 1}
    (hC : ∀ s : Finset (Fin n), s.card = k → C.eval interpretation (ofFinset s) 0 = true)
    (hC' : Positive.errorCap n k p w * C.size < n.choose k) :
    (outputApproximator C : Approximator n p w).terms.Nonempty := by
  classical
  let S := Positive.scheme (n := n) (k := k) (p := p) hw hk
  have hF : (S.failures univ (outputApproximator C) fun _ => true).card ≤
      C.program.cost S.errorCost :=
    S.card_failures_le_cost univ C fun c _ => hC c.1 (mem_powersetCard.1 c.2).2
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

/-- The approximator of the output of a circuit rejecting the complete multipartite graphs of the
colourings with `r` colours accepts only colourings on which it is wrong, and so at most as many
as the negative cost of the circuit. -/
private theorem card_acceptedColorings_le (hw : 2 ≤ w) {r : ℕ}
    {C : Circuit signature (edgeCount n) 1}
    (hC : ∀ c : Fin n → Fin r, C.eval interpretation (ofColoring c) 0 = false) :
    (Negative.acceptedColorings r (outputApproximator C : Approximator n p w).terms).card ≤
      C.program.cost (Negative.errorCost n r p w) := by
  classical
  let S := Negative.scheme (n := n) (r := r) (p := p) hw
  refine (card_le_card fun c hc => ?_).trans
    (S.card_failures_le_cost univ C (target := fun _ => false) fun c _ => hC c)
  rw [S.mem_failures]
  refine ⟨mem_univ _, ?_⟩
  have : (C.eval Approximator.interpretation Approximator.input 0 : Approximator n p w).decode
      (ofColoring c) = true :=
    decode_eq_true.2 (mem_filter.1 hc).2
  rw [this]
  change ¬(true ≤ false)
  decide

/-- **Razborov's dichotomy.** A monotone circuit separating the graphs with a `k`-clique from the
`(k - 1)`-colourable graphs on `n` vertices, such as one computing `k`-clique, exhausts the positive
or the negative error budget of the approximators with `p` petals and width `w`. -/
theorem choose_le_or_pow_le_mul_size (hw : 2 ≤ w) (hk : w + 1 ≤ k) (hr : 2 * w ^ 2 ≤ k - 1)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) :
    n.choose k ≤ Positive.errorCap n k p w * C.size ∨
      (k - 1) ^ n ≤ 2 * negativeGateCap n (k - 1) p w * C.size := by
  refine or_iff_not_imp_left.2 fun hpos => ?_
  have hn : 0 < n := by
    by_contra hn
    have hchoose : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    exact hpos (hchoose ▸ Nat.zero_le _)
  have hne := nonempty_outputApproximator (p := p) hw hk (fun _ hs => hC.ofFinset_eq_true hs)
    (not_le.1 hpos)
  have hhalf := Negative.half_le_card_acceptedColorings (r := k - 1) hn hr
    (outputApproximator C : Approximator n p w).card_le_of_mem hne
  have hcost : C.program.cost (Negative.errorCost n (k - 1) p w) ≤
      negativeGateCap n (k - 1) p w * C.size :=
    (C.program.cost_mono fun op => Negative.errorCost_le Fact.out _ op).trans_eq
      (C.program.cost_const _)
  calc (k - 1) ^ n ≤ 2 * (Negative.acceptedColorings (k - 1)
        (outputApproximator C : Approximator n p w).terms).card := hhalf
    _ ≤ 2 * (negativeGateCap n (k - 1) p w * C.size) :=
        Nat.mul_le_mul_left 2 ((card_acceptedColorings_le hw hC.ofColoring_eq_false).trans hcost)
    _ = 2 * negativeGateCap n (k - 1) p w * C.size := (Nat.mul_assoc _ _ _).symm

omit [Fact (2 ≤ p)] in
/-- **Razborov's lower bound for separating circuits.** Every monotone circuit separating the graphs
with a `k`-clique from the `(k - 1)`-colourable graphs on `n` vertices has more than `s` gates, for
every `s` below both error budgets of the approximators with `p ≥ 2` petals and width `w ≥ 2`, if
`w + 1 ≤ k` and `2 w ^ 2 ≤ k - 1`. -/
theorem lt_size_of_separates (hp : 2 ≤ p) (hw : 2 ≤ w) (hk : w + 1 ≤ k)
    (hr : 2 * w ^ 2 ≤ k - 1) {s : ℕ} (hpos : Positive.errorCap n k p w * s < n.choose k)
    (hneg : 2 * negativeGateCap n (k - 1) p w * s < (k - 1) ^ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) :
    s < C.size := by
  have : Fact (2 ≤ p) := ⟨hp⟩
  by_contra! h
  rcases choose_le_or_pow_le_mul_size (p := p) hw hk hr hC with h' | h'
  · exact absurd (h'.trans (Nat.mul_le_mul_left _ h)) (not_le.2 hpos)
  · exact absurd (h'.trans (Nat.mul_le_mul_left _ h)) (not_le.2 hneg)

omit [Fact (2 ≤ p)] in
/-- A circuit computing `k`-clique separates the graphs with a `k`-clique from the `r`-colourable
graphs, for `r < k`. -/
theorem separates_of_computes_clique {r : ℕ} (hr : r < k) {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) :
    Separates k r fun x => C.eval interpretation x 0 := by
  rw [show (fun x => C.eval interpretation x 0) = clique n k from
    funext fun x => by rw [hC, single_apply]]
  exact separates_clique hr

omit [Fact (2 ≤ p)] in
/-- **Razborov's lower bound.** Every monotone circuit computing `k`-clique on `n` vertices has more
than `s` gates, for every `s` below both error budgets of the approximators with `p ≥ 2` petals and
width `w ≥ 2`, if `w + 1 ≤ k` and `2 w ^ 2 ≤ k - 1`. -/
theorem lt_size_of_computes_clique (hp : 2 ≤ p) (hw : 2 ≤ w) (hk : w + 1 ≤ k)
    (hr : 2 * w ^ 2 ≤ k - 1) {s : ℕ} (hpos : Positive.errorCap n k p w * s < n.choose k)
    (hneg : 2 * negativeGateCap n (k - 1) p w * s < (k - 1) ^ n)
    {C : Circuit signature (edgeCount n) 1} (hC : C.Computes interpretation (single (clique n k))) :
    s < C.size :=
  lt_size_of_separates hp hw hk hr hpos hneg (separates_of_computes_clique (by omega) hC)

end Cslib.Circuits.Monotone
