/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Closure.Negative
public import Complexity.Computability.Circuit.Monotone.Clique.Closure.Positive

/-!
# The Alon–Boppana lower bound for monotone clique separators

Evaluate a monotone circuit separating the graphs with a `k`-clique from the `g`-colourable graphs,
for `g < k`, in the closed approximators of width `l` closed under `r`-fold implication
(`Cslib.Circuits.Monotone.Closure.Approximator.interpretation`). The circuit accepts the complete
graphs on `k`-sets, so unless it exhausts the positive budget
(`Cslib.Circuits.Monotone.Closure.Positive.scheme`) the approximator at its output accepts one of
them and is nonempty. If `2 l ^ 2 ≤ g`, a nonempty approximator accepts at least half of the
colourings with `g` colours, on which the circuit says `false`, so the circuit exhausts the
negative budget (`Cslib.Circuits.Monotone.Closure.Negative.scheme`)
(`Cslib.Circuits.Monotone.Closure.choose_le_or_pow_le_mul_size`).

This is the argument of [Alon and Boppana, Lemma 3.10 and Theorem 3.11][AlonBoppana1987], whose
proof reads the circuit only on cliques and on complete multipartite graphs; their `s₂` and
`s₁ - 1` are our `k` and `g`. The output step follows Razborov's dichotomy
(`Cslib.Circuits.Monotone.choose_le_or_pow_le_mul_size`) rather than their case split on whether
the output approximator accepts every graph, and the closure is charged per step with the crude
step bound; both change only constants. The bounds are explicit
(`Cslib.Circuits.Monotone.Closure.lt_size_of_separates`).

## Main definitions

* `Cslib.Circuits.Monotone.Closure.outputApproximator`: the approximator at the output of a circuit.

## Main results

* `Cslib.Circuits.Monotone.Closure.choose_le_or_pow_le_mul_size`: the dichotomy, for separating
  circuits.
* `Cslib.Circuits.Monotone.Closure.lt_size_of_separates`: the lower bound with explicit budgets.

## References

* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*][AlonBoppana1987]
* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*, Theorem 7.2][Krajicek1997]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone.Closure

open Cslib.Circuits.Clique Finset

variable {n k r l : ℕ}

private theorem Positive.errorCost_le (op : Op) :
    Positive.errorCost n k r l op ≤ Positive.errorCap n k r l := by
  cases op <;> simp [Positive.errorCost]

variable [Fact (2 ≤ r)]

/-- The approximator of the output of a circuit. -/
noncomputable def outputApproximator (C : Circuit signature (edgeCount n) 1) : Approximator n r l :=
  C.eval Approximator.interpretation Approximator.input 0

/-- If the circuit is small and accepts the complete graph on every `k`-set, the approximator of
its output is right on one of them, and so is nonempty. -/
theorem nonempty_outputApproximator (hl : 2 ≤ l) (hlk : l ≤ k)
    {C : Circuit signature (edgeCount n) 1}
    (hC : ∀ s : Finset (Fin n), s.card = k → C.eval interpretation (ofFinset s) 0 = true)
    (hC' : Positive.errorCap n k r l * C.size < n.choose k) :
    (outputApproximator C : Approximator n r l).terms.Nonempty := by
  classical
  let S := Positive.scheme (n := n) (k := k) (r := r) hl hlk
  have hF : (S.failures univ (outputApproximator C) fun _ => true).card ≤
      C.program.cost S.errorCost :=
    S.card_failures_le_cost univ C fun c _ => hC c.1 (mem_powersetCard.1 c.2).2
  have hcost : C.program.cost S.errorCost ≤ Positive.errorCap n k r l * C.size :=
    (C.program.cost_mono fun op => Positive.errorCost_le op).trans_eq (C.program.cost_const _)
  obtain ⟨c, hc⟩ : ∃ c, c ∉ S.failures univ (outputApproximator C) fun _ => true := by
    by_contra! h
    have := card_le_card fun c (_ : c ∈ (univ : Finset (CliqueSet n k))) => h c
    rw [card_univ, Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin] at this
    omega
  simp only [S.mem_failures, mem_univ, true_and, not_not] at hc
  obtain ⟨s, hs, -⟩ := Approximator.decode_eq_true.1 (Bool.eq_true_of_true_le hc)
  exact ⟨s, hs⟩

/-- The approximator of the output of a circuit rejecting the complete multipartite graphs of the
colourings with `g` colours accepts only colourings on which it is wrong, and so at most as many
as the negative cost of the circuit. -/
private theorem card_acceptedColorings_le (hl : 2 ≤ l) {g : ℕ}
    {C : Circuit signature (edgeCount n) 1}
    (hC : ∀ c : Fin n → Fin g, C.eval interpretation (ofColoring c) 0 = false) :
    (Monotone.Negative.acceptedColorings g
        (outputApproximator C : Approximator n r l).terms).card ≤
      Negative.errorCap n g r l * C.size := by
  classical
  let S := Negative.scheme (n := n) (g := g) (r := r) hl
  refine (card_le_card fun c hc => ?_).trans
    ((S.card_failures_le_cost univ C (target := fun _ => false) fun c _ => hC c).trans_eq
      (C.program.cost_const _))
  rw [S.mem_failures]
  refine ⟨mem_univ _, ?_⟩
  have : (C.eval Approximator.interpretation Approximator.input 0 : Approximator n r l).decode
      (ofColoring c) = true :=
    Approximator.decode_eq_true.2 (mem_filter.1 hc).2
  rw [this]
  change ¬(true ≤ false)
  decide

/-- **The Alon–Boppana dichotomy.** A monotone circuit separating the graphs with a `k`-clique from
the `g`-colourable graphs on `n` vertices, for `g < k`, exhausts the positive or the negative error
budget of the closed approximators of width `l ≥ 2` with `2 l ^ 2 ≤ g`. -/
theorem choose_le_or_pow_le_mul_size {g : ℕ} (hl : 2 ≤ l) (hg : 2 * l ^ 2 ≤ g) (hgk : g < k)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k g fun x => C.eval interpretation x 0) :
    n.choose k ≤ Positive.errorCap n k r l * C.size ∨
      g ^ n ≤ 2 * Negative.errorCap n g r l * C.size := by
  refine or_iff_not_imp_left.2 fun hpos => ?_
  have hlk : l ≤ k := by
    have := Nat.le_self_pow two_ne_zero l
    omega
  have hn : 0 < n := by
    by_contra hn
    have hchoose : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    exact hpos (hchoose ▸ Nat.zero_le _)
  have hne := nonempty_outputApproximator (r := r) hl hlk (fun _ hs => hC.ofFinset_eq_true hs)
    (not_le.1 hpos)
  have hhalf := Monotone.Negative.half_le_card_acceptedColorings (r := g) hn hg
    (outputApproximator C : Approximator n r l).card_le_of_mem hne
  calc g ^ n ≤ 2 * (Monotone.Negative.acceptedColorings g
        (outputApproximator C : Approximator n r l).terms).card := hhalf
    _ ≤ 2 * (Negative.errorCap n g r l * C.size) :=
        Nat.mul_le_mul_left 2 (card_acceptedColorings_le hl hC.ofColoring_eq_false)
    _ = 2 * Negative.errorCap n g r l * C.size := (Nat.mul_assoc _ _ _).symm

omit [Fact (2 ≤ r)] in
/-- **The Alon–Boppana lower bound for separating circuits, with explicit budgets.** Every monotone
circuit separating the graphs with a `k`-clique from the `g`-colourable graphs on `n` vertices, for
`g < k`, has more than `s` gates, for every `s` below both error budgets of the closed
approximators with `r ≥ 2` implying sets and width `l ≥ 2`, if `2 l ^ 2 ≤ g`. -/
theorem lt_size_of_separates {g : ℕ} (hr : 2 ≤ r) (hl : 2 ≤ l) (hg : 2 * l ^ 2 ≤ g)
    (hgk : g < k) {s : ℕ} (hpos : Positive.errorCap n k r l * s < n.choose k)
    (hneg : 2 * Negative.errorCap n g r l * s < g ^ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k g fun x => C.eval interpretation x 0) :
    s < C.size := by
  have : Fact (2 ≤ r) := ⟨hr⟩
  by_contra! h
  rcases choose_le_or_pow_le_mul_size (r := r) hl hg hgk hC with h' | h'
  · exact absurd (h'.trans (Nat.mul_le_mul_left _ h)) (not_le.2 hpos)
  · exact absurd (h'.trans (Nat.mul_le_mul_left _ h)) (not_le.2 hneg)

end Cslib.Circuits.Monotone.Closure
