/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.BipartiteMatching.Negative
public import Complexity.Computability.Circuit.Monotone.BipartiteMatching.Positive
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith

/-!
# Razborov's lower bound for monotone circuits computing perfect matchings

Evaluate a monotone circuit in the matching approximators
(`Cslib.Circuits.BipartiteMatching.Razborov.Approximator.interpretation`). If the circuit accepts
the perfect matchings of the `n!` permutations, the approximator at its output is wrong on all of
them unless it is nonempty, so either the circuit exhausts the positive budget
(`Cslib.Circuits.BipartiteMatching.Razborov.Positive.scheme`) or the output approximator contains a
matching `W` of at most `s` edges. That matching lies in the graphs of `4 ^ n / 2 ^ #W` of the
`4 ^ n` two-colourings, and if `4 ^ (s + 1) ≤ 2n + 1`, at most `4 ^ n / 2 ^ (s + 1)` of these graphs
have a perfect matching. So the output approximator accepts the graphs of at least
`4 ^ n / 2 ^ (s + 1)` colourings on which a circuit computing perfect matching says `false`, and the
circuit exhausts the negative budget
(`Cslib.Circuits.BipartiteMatching.Razborov.Negative.scheme`)
(`Cslib.Circuits.BipartiteMatching.Razborov.factorial_le_or_four_pow_le_mul_size`). This is the
argument of [Jukna, Theorem 9.38][Jukna2012] for Razborov's theorem [Razborov1985a], with explicit
budgets (`Cslib.Circuits.Monotone.lt_size_of_computes_bipartitePerfectMatching`).

The argument reads the circuit only on the perfect matchings of permutations and on the graphs of
colourings, so it applies to every monotone circuit accepting the former and rejecting the latter
when they have no perfect matching
(`Cslib.Circuits.Monotone.lt_size_of_separates_ofPerm_ofColoring`).

## Main definitions

* `Cslib.Circuits.BipartiteMatching.Razborov.outputApproximator`: the approximator at the output
  of a circuit.

## Main results

* `Cslib.Circuits.BipartiteMatching.Razborov.nonempty_outputApproximator`,
  `Cslib.Circuits.BipartiteMatching.Razborov.card_filter_accepts_le`: the output approximator of a
  small circuit is nonempty, and accepts few graphs of colourings without a perfect matching.
* `Cslib.Circuits.BipartiteMatching.Razborov.factorial_le_or_four_pow_le_mul_size`: the dichotomy.
* `Cslib.Circuits.Monotone.lt_size_of_separates_ofPerm_ofColoring`,
  `Cslib.Circuits.Monotone.lt_size_of_computes_bipartitePerfectMatching`: the lower bound with
  explicit budgets, for separating circuits and for circuits computing perfect matching.

## References

* [A. A. Razborov, *Lower bounds on monotone complexity of the logical permanent*][Razborov1985a]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 9.11][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

open Finset BipartiteMatching
open Cslib.Circuits.Monotone (signature Op)
open scoped Nat

variable {n r s q : ℕ}

namespace BipartiteMatching.Razborov

open Approximator

/-- If `2 ^ (s + 1) #(matchings n s) (2 ^ s - 1) ^ q t < 2 ^ (s q)`, a circuit with `t` gates stays
below the negative budget. -/
theorem two_pow_mul_errorCap_mul_lt {t : ℕ}
    (h : 2 ^ (s + 1) * (matchings n s).card * (2 ^ s - 1) ^ q * t < 2 ^ (s * q)) :
    2 ^ (s + 1) * Negative.errorCap n s q * t < 4 ^ n := by
  refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ (s * q)) ?_
  calc 2 ^ (s + 1) * Negative.errorCap n s q * t * 2 ^ (s * q)
      = 2 ^ (s + 1) * (matchings n s).card * t *
          ((2 ^ s - 1) ^ q * 4 ^ n / 2 ^ (s * q) * 2 ^ (s * q)) := by
        rw [Negative.errorCap, Negative.stepCap]
        ring
    _ ≤ 2 ^ (s + 1) * (matchings n s).card * t * ((2 ^ s - 1) ^ q * 4 ^ n) :=
        Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = (2 ^ (s + 1) * (matchings n s).card * (2 ^ s - 1) ^ q * t) * 4 ^ n := by ring
    _ < 2 ^ (s * q) * 4 ^ n := Nat.mul_lt_mul_of_pos_right h (by positivity)
    _ = 4 ^ n * 2 ^ (s * q) := mul_comm _ _

variable [Fact (2 ≤ r)]

/-- The approximator of the output of a circuit. -/
noncomputable def outputApproximator (C : Circuit signature (n * n) 1) : Approximator n r s :=
  C.eval Approximator.interpretation Approximator.input 0

/-- If the circuit is small and accepts the perfect matching of every permutation, the approximator
of its output is right on one of them, and so is nonempty. -/
theorem nonempty_outputApproximator (hs : 1 ≤ s) {C : Circuit signature (n * n) 1}
    (hC : ∀ σ : Equiv.Perm (Fin n), C.eval Monotone.interpretation (ofPerm σ) 0 = true)
    (hC' : Positive.errorCap n r s * C.size < n !) :
    (outputApproximator C : Approximator n r s).terms.Nonempty := by
  classical
  let S := Positive.scheme (n := n) (r := r) (s := s) hs
  have hF : (S.failures univ (outputApproximator C) fun _ => true).card ≤
      C.program.cost S.errorCost :=
    S.card_failures_le_cost univ C fun σ _ => hC σ
  have hcost : C.program.cost S.errorCost ≤ Positive.errorCap n r s * C.size :=
    (C.program.cost_mono fun op => Positive.errorCost_le op).trans_eq (C.program.cost_const _)
  obtain ⟨σ, hσ⟩ : ∃ σ, σ ∉ S.failures univ (outputApproximator C) fun _ => true := by
    by_contra! h
    have := card_le_card fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm (Fin n)))) => h σ
    rw [card_univ, Fintype.card_perm, Fintype.card_fin] at this
    omega
  simp only [S.mem_failures, mem_univ, true_and, not_not] at hσ
  obtain ⟨W, hW, -⟩ := decode_eq_true.1 (Bool.eq_true_of_true_le hσ)
  exact ⟨W, hW⟩

/-- The approximator of the output of a circuit rejecting the graphs of colourings without a perfect
matching accepts the graphs of at most `errorCap n s q * C.size` of these colourings. -/
theorem card_filter_accepts_le (hs : 1 ≤ s) (hq : (q * s) ^ 2 < r)
    {C : Circuit signature (n * n) 1}
    (hC : ∀ c : Coloring n, bipartitePerfectMatching n (ofColoring c) = false →
      C.eval Monotone.interpretation (ofColoring c) 0 = false) :
    #{c : Coloring n | bipartitePerfectMatching n (ofColoring c) = false ∧
        Accepts (outputApproximator C : Approximator n r s).terms (ofColoring c)} ≤
      Negative.errorCap n s q * C.size := by
  classical
  let S := Negative.scheme (n := n) (r := r) (s := s) (q := q) hs hq
  refine (card_le_card fun c hc => ?_).trans
    ((S.card_failures_le_cost (univ.filter fun c => bipartitePerfectMatching n (ofColoring c) =
      false) C (target := fun _ => false) fun c hc => hC c (mem_filter.1 hc).2).trans
    ((C.program.cost_mono fun op => Negative.errorCost_le op).trans_eq (C.program.cost_const _)))
  obtain ⟨hpm, hacc⟩ := (mem_filter.1 hc).2
  rw [S.mem_failures]
  refine ⟨mem_filter.2 ⟨mem_univ _, hpm⟩, ?_⟩
  have : (C.eval Approximator.interpretation Approximator.input 0 : Approximator n r s).decode
      (ofColoring c) = true :=
    decode_eq_true.2 hacc
  rw [this]
  change ¬(true ≤ false)
  decide

/-- **Razborov's dichotomy for perfect matching.** Let `1 ≤ s`, `(q s) ^ 2 < r` and
`4 ^ (s + 1) ≤ 2n + 1`. A monotone circuit accepting the perfect matchings of permutations and
rejecting the graphs of colourings without a perfect matching, such as one computing perfect
matching, exhausts the positive or the negative error budget of the matching approximators. -/
theorem factorial_le_or_four_pow_le_mul_size (hs : 1 ≤ s) (hq : (q * s) ^ 2 < r)
    (hn : 4 ^ (s + 1) ≤ 2 * n + 1) {C : Circuit signature (n * n) 1}
    (hpos : ∀ σ : Equiv.Perm (Fin n), C.eval Monotone.interpretation (ofPerm σ) 0 = true)
    (hneg : ∀ c : Coloring n, bipartitePerfectMatching n (ofColoring c) = false →
      C.eval Monotone.interpretation (ofColoring c) 0 = false) :
    n ! ≤ Positive.errorCap n r s * C.size ∨
      4 ^ n ≤ 2 ^ (s + 1) * Negative.errorCap n s q * C.size := by
  classical
  refine or_iff_not_imp_left.2 fun hp => ?_
  obtain ⟨W, hW⟩ := nonempty_outputApproximator (r := r) hs hpos (not_le.1 hp)
  have hA := card_filter_contains_ofColoring_mul_two_pow (n := n)
    ((outputApproximator C).isMatching_of_mem hW)
  have hB := card_filter_bipartitePerfectMatching_ofColoring_mul_le (n := n) (s := s) hn
  have hF := card_filter_accepts_le (r := r) (q := q) hs hq hneg
  set X := #{c : Coloring n | Contains (ofColoring c) W}
  set B := #{c : Coloring n | bipartitePerfectMatching n (ofColoring c) = true}
  set F := #{c : Coloring n | bipartitePerfectMatching n (ofColoring c) = false ∧
    Accepts (outputApproximator C : Approximator n r s).terms (ofColoring c)}
  have hXBF : X ≤ B + F := by
    refine (card_le_card fun c hc => ?_).trans (card_union_le _ _)
    rw [mem_union, mem_filter, mem_filter]
    cases hpm : bipartitePerfectMatching n (ofColoring c)
    · exact Or.inr ⟨mem_univ _, rfl, W, hW, (mem_filter.1 hc).2⟩
    · exact Or.inl ⟨mem_univ _, rfl⟩
  have h1 : 4 ^ n ≤ X * 2 ^ s :=
    hA ▸ Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos
      ((outputApproximator C).card_le_of_mem hW))
  have h2 : X * 2 ^ s ≤ B * 2 ^ s + F * 2 ^ s := by
    rw [← add_mul]
    exact Nat.mul_le_mul_right _ hXBF
  calc 4 ^ n ≤ 2 ^ (s + 1) * F := by
        rw [pow_succ] at hB ⊢
        linarith
    _ ≤ 2 ^ (s + 1) * (Negative.errorCap n s q * C.size) := Nat.mul_le_mul_left _ hF
    _ = 2 ^ (s + 1) * Negative.errorCap n s q * C.size := (Nat.mul_assoc _ _ _).symm

end BipartiteMatching.Razborov

namespace Monotone

open BipartiteMatching.Razborov

/-- **Razborov's lower bound for separating circuits, with explicit budgets.** Let `r ≥ 2`,
`1 ≤ s`, `(q s) ^ 2 < r` and `4 ^ (s + 1) ≤ 2n + 1`. Every monotone circuit accepting the perfect
matchings of permutations and rejecting the graphs of two-colourings without a perfect matching has
more than `t` gates, for every `t` below both error budgets of the matching approximators. -/
theorem lt_size_of_separates_ofPerm_ofColoring (hr : 2 ≤ r) (hs : 1 ≤ s) (hq : (q * s) ^ 2 < r)
    (hn : 4 ^ (s + 1) ≤ 2 * n + 1) {t : ℕ} (hpos : Positive.errorCap n r s * t < n !)
    (hneg : 2 ^ (s + 1) * Negative.errorCap n s q * t < 4 ^ n) {C : Circuit signature (n * n) 1}
    (hC₁ : ∀ σ : Equiv.Perm (Fin n), C.eval Monotone.interpretation (ofPerm σ) 0 = true)
    (hC₂ : ∀ c : Coloring n, bipartitePerfectMatching n (ofColoring c) = false →
      C.eval Monotone.interpretation (ofColoring c) 0 = false) :
    t < C.size := by
  have : Fact (2 ≤ r) := ⟨hr⟩
  by_contra! h
  rcases factorial_le_or_four_pow_le_mul_size (r := r) (q := q) hs hq hn hC₁ hC₂ with h' | h'
  · exact absurd (h'.trans (Nat.mul_le_mul_left _ h)) (not_le.2 hpos)
  · exact absurd (h'.trans (Nat.mul_le_mul_left _ h)) (not_le.2 hneg)

/-- **Razborov's lower bound for perfect matching, with explicit budgets** [Razborov1985a],
[Jukna, Theorem 9.38][Jukna2012]. Let `r ≥ 2`, `1 ≤ s`, `(q s) ^ 2 < r` and
`4 ^ (s + 1) ≤ 2n + 1`. Every monotone circuit computing whether a subgraph of `K_{n,n}` has a
perfect matching has more than `t` gates, for every `t` below both error budgets of the matching
approximators. -/
theorem lt_size_of_computes_bipartitePerfectMatching (hr : 2 ≤ r) (hs : 1 ≤ s)
    (hq : (q * s) ^ 2 < r) (hn : 4 ^ (s + 1) ≤ 2 * n + 1) {t : ℕ}
    (hpos : Positive.errorCap n r s * t < n !)
    (hneg : 2 ^ (s + 1) * Negative.errorCap n s q * t < 4 ^ n) {C : Circuit signature (n * n) 1}
    (hC : C.Computes Monotone.interpretation (single (bipartitePerfectMatching n))) :
    t < C.size := by
  have heval (x : BitString (n * n)) :
      C.eval Monotone.interpretation x 0 = bipartitePerfectMatching n x := by
    rw [hC, single_apply]
  refine lt_size_of_separates_ofPerm_ofColoring hr hs hq hn hpos hneg (fun σ => ?_) fun c hc => ?_
  · rw [heval, bipartitePerfectMatching_ofPerm]
  · rw [heval, hc]

end Monotone

end Cslib.Circuits
