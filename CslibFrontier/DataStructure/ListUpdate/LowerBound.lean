/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.ListUpdate.Basic

/-!
# Deterministic `2n/(n+1)` lower bound for list update

No deterministic online list-update strategy over an `n`-element universe has competitive ratio
smaller than `2n / (n + 1) = 2 - 2/(n + 1)`, with any additive constant. This is the standard
"cruel adversary" bound for deterministic list accessing. It is credited to Karp and Raghavan as
reported in [Irani, *Two Results on the List Update Problem*][Irani1991] (the paper's text was not
inspected here); see also [Borodin and El-Yaniv, *Online Computation and Competitive Analysis*,
Chapter 1][BorodinElYaniv1998]. The argument:

1. **Cruel adversary (`cruelRequests`):** always request the item at the end of the online
   strategy's current list (`List.getLastD`). Whatever rearrangement the strategy then makes, it
   pays at least `n` per request (`idxOf_le_inversions_add`), so `m` requests cost it at least
   `m * n` (`le_cost_cruelRequests`).
2. **Two static schedules:** the offline schedule that keeps the initial arrangement `s₀`, and
   the one that reverses it on the first request and then stays put. Each request's positions in
   `s₀` and its reversal add up to `n + 1` (`idxOf_reverse_add_idxOf`), and reversing costs at
   most `n (n - 1) / 2`. So the cheaper of the two schedules costs at most
   `(m (n + 1) + n (n - 1) / 2) / 2`, on every request sequence of length `m`.
3. **Ratio violation:** for `p (n + 1) < 2 n q` (a rational ratio `p / q < 2n / (n + 1)`) and any
   additive constant `b`, taking `m` large enough gives `p * OPT + b < q * ALG`
   (`exists_ratio_violation_of_lt`).

The bound uses only two static offline schedules. The textbook proof averages over all `n!`
static arrangements, which gives the same constant. For `n ≥ 2` no deterministic strategy is
`(1, b)`-competitive (`not_isCompetitive_one`). Move-to-front is `(2, 0)`-competitive
(`CslibFrontier.DataStructure.ListUpdate.MoveToFront`), so `2` is the optimal integer ratio.

## Main definitions

* `Cslib.DataStructure.ListUpdate.cruelRequests`: the adaptive request sequence against a
  deterministic strategy.

## Main results

* `idxOf_getLastD_add_one`: the last item of an arrangement is at position `n`.
* `le_cost_cruelRequests`: the cruel adversary forces cost `≥ n` per request.
* `scheduleCost_static_le`, `sum_idxOf_add_sum_idxOf_reverse`: cost of static offline schedules.
* `exists_ratio_violation_of_lt`, `not_isCompetitiveFrom_of_lt`, `not_isCompetitive_of_lt`,
  `not_isCompetitiveAnyInit_of_lt`, `not_isCompetitive_one`: no deterministic strategy achieves
  a ratio below `2n / (n + 1)`.

## References

* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
* [S. Irani, *Two Results on the List Update Problem*][Irani1991]
* [D. D. Sleator and R. E. Tarjan, *Amortized Efficiency of List Update and Paging
  Rules*][SleatorTarjan1985]
-/

public section

namespace Cslib.DataStructure.ListUpdate

open Cslib.DataStructure.Online

variable {α : Type} [DecidableEq α]

/-- The last item of a nonempty duplicate-free list sits at position `length - 1`. -/
theorem idxOf_getLastD_add_one {l : List α} (hl : l.Nodup) (hne : l ≠ []) (x₀ : α) :
    l.idxOf (l.getLastD x₀) + 1 = l.length := by
  obtain ⟨a, t, ht⟩ : ∃ a t, l.reverse = a :: t := by
    cases h : l.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.1 h) hne
    | cons a t => exact ⟨a, t, rfl⟩
  have hmem : a ∈ l := List.mem_reverse.1 (ht ▸ List.mem_cons_self)
  have h := idxOf_reverse_add_idxOf hl hmem
  rw [ht, List.idxOf_cons_self] at h
  have hlast : l.getLastD x₀ = a := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_head?_reverse, ht, List.head?_cons,
      Option.getD_some]
  rw [hlast]
  omega

variable [Fintype α]

/-- The cruel adversary: `n` requests, each for the last item of the strategy's current list. -/
@[expose]
def cruelRequests (x₀ : α) (A : DetStrategy (problem α)) (s₀ : List α) (m : Nat) : List α :=
  A.adaptiveRequests (fun l => l.getLastD x₀) s₀ m

@[simp]
theorem length_cruelRequests (x₀ : α) (A : DetStrategy (problem α)) (s₀ : List α) (m : Nat) :
    (cruelRequests x₀ A s₀ m).length = m :=
  A.adaptiveRequests_length _ s₀ m

/-- Against the cruel adversary every deterministic strategy pays at least `n` per request. -/
theorem le_cost_cruelRequests (x₀ : α) (A : DetStrategy (problem α)) {s₀ : List α}
    (hs₀ : IsArrangement s₀) (m : Nat) :
    m * Fintype.card α ≤ A.cost s₀ (cruelRequests x₀ A s₀ m) := by
  refine A.le_cost_adaptiveRequests (fun {mem} hmem => ?_) hs₀ m
  have hstep := (A.valid_step ((A.project mem).getLastD x₀) hmem).2
  have hcur : IsArrangement (A.project mem) := hstep.1
  have hnext : IsArrangement (A.project (A.step mem ((A.project mem).getLastD x₀))) := hstep.2
  have hne : A.project mem ≠ [] := List.ne_nil_of_mem (hcur.2 x₀)
  have hpos := idxOf_getLastD_add_one hcur.1 hne x₀
  have hle := idxOf_le_inversions_add hcur hnext ((A.project mem).getLastD x₀)
  rw [hcur.length_eq] at hpos
  change _ ≤ stepCost _ _ _
  rw [stepCost]
  omega

/-- The static schedule that moves to `τ` on the first request and then stays put is valid. -/
theorem validSchedule_static {s₀ τ : List α} (hs₀ : IsArrangement s₀) (hτ : IsArrangement τ)
    (reqs : List α) : (problem α).ValidSchedule s₀ reqs (List.replicate reqs.length τ) := by
  induction reqs generalizing s₀ with
  | nil => trivial
  | cons r rs ih => exact ⟨⟨hs₀, hτ⟩, ih hτ⟩

/-- The static schedule to `τ` costs the inversions between `s₀` and `τ` plus the positions of
the requests in `τ`. -/
theorem scheduleCost_static_le (s₀ τ : List α) (reqs : List α) :
    (problem α).scheduleCost s₀ reqs (List.replicate reqs.length τ) ≤
      inversions s₀ τ + (reqs.map fun r => τ.idxOf r + 1).sum := by
  induction reqs generalizing s₀ with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    change stepCost s₀ r τ + (problem α).scheduleCost τ rs (List.replicate rs.length τ) ≤ _
    have h := ih τ
    rw [inversions_self, Nat.zero_add] at h
    rw [stepCost, List.map_cons, List.sum_cons]
    omega

/-- Each request's positions in `s₀` and in its reversal add up to `n + 1`. -/
theorem sum_idxOf_add_sum_idxOf_reverse {s₀ : List α} (hs₀ : IsArrangement s₀) (reqs : List α) :
    (reqs.map fun r => s₀.idxOf r + 1).sum + (reqs.map fun r => s₀.reverse.idxOf r + 1).sum =
      reqs.length * (Fintype.card α + 1) := by
  induction reqs with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
  | cons r rs ih =>
    have h := idxOf_reverse_add_idxOf hs₀.1 (hs₀.2 r)
    rw [hs₀.length_eq] at h
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Arithmetic core of the ratio violation. -/
private theorem ratio_arith {n p q b K m alg opt I : Nat} (hpq : p * (n + 1) < 2 * n * q)
    (hm : m = p * K + 2 * b + 1) (halg : m * n ≤ alg) (hopt : 2 * opt ≤ m * (n + 1) + I)
    (hI : 2 * I ≤ K) : p * opt + b < q * alg := by
  have h₁ : p * (2 * opt) ≤ p * (m * (n + 1)) + p * I := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left p hopt
  have h₂ : 2 * (p * I) ≤ p * K := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left p hI
  have h₃ : (p * (n + 1) + 1) * m ≤ (2 * n * q) * m := Nat.mul_le_mul_right m hpq
  have h₄ : q * (m * n) ≤ q * alg := Nat.mul_le_mul_left q halg
  have e₁ : p * (2 * opt) = 2 * (p * opt) := Nat.mul_left_comm p 2 opt
  have e₂ : p * (m * (n + 1)) = p * (n + 1) * m := by
    rw [Nat.mul_comm m, Nat.mul_assoc]
  have e₃ : 2 * n * q * m = 2 * (q * (m * n)) := by
    rw [Nat.mul_assoc 2, Nat.mul_assoc 2, Nat.mul_comm n q, Nat.mul_assoc q n m, Nat.mul_comm n m]
  rw [Nat.add_mul, Nat.one_mul] at h₃
  omega

/-- **Deterministic lower bound for list update**: for every deterministic online strategy
over a universe of `n ≥ 1` items, every initial arrangement `s₀`, every rational ratio
`p / q < 2n / (n + 1)` (i.e. `p (n + 1) < 2 n q`) and every additive constant `b`, there are a
request sequence and a valid offline schedule with `p * OPT + b < q * ALG`. -/
theorem exists_ratio_violation_of_lt (A : DetStrategy (problem α)) {s₀ : List α}
    (hs₀ : IsArrangement s₀) {p q : Nat} (hpq : p * (Fintype.card α + 1) < 2 * Fintype.card α * q)
    (b : Nat) :
    ∃ reqs states, (problem α).ValidSchedule s₀ reqs states ∧
      p * (problem α).scheduleCost s₀ reqs states + b < q * A.cost s₀ reqs := by
  obtain ⟨x₀⟩ : Nonempty α := by
    rw [← Fintype.card_pos_iff]
    rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
    · rw [h, Nat.mul_zero, Nat.zero_mul] at hpq
      exact absurd hpq (Nat.not_lt_zero _)
    · exact h
  set K := Fintype.card α * (Fintype.card α - 1)
  set m := p * K + 2 * b + 1 with hm
  set reqs := cruelRequests x₀ A s₀ m
  have hlen : reqs.length = m := length_cruelRequests x₀ A s₀ m
  have halg := le_cost_cruelRequests x₀ A hs₀ m
  have hc₁ := scheduleCost_static_le s₀ s₀ reqs
  have hc₂ := scheduleCost_static_le s₀ s₀.reverse reqs
  have hsum := sum_idxOf_add_sum_idxOf_reverse hs₀ reqs
  have hI := two_mul_inversions_le s₀ s₀.reverse
  rw [inversions_self, Nat.zero_add] at hc₁
  rw [hlen] at hsum
  by_cases hcmp : (problem α).scheduleCost s₀ reqs (List.replicate reqs.length s₀) ≤
      (problem α).scheduleCost s₀ reqs (List.replicate reqs.length s₀.reverse)
  · refine ⟨reqs, _, validSchedule_static hs₀ hs₀ reqs, ?_⟩
    exact ratio_arith hpq hm halg (by omega) hI
  · refine ⟨reqs, _, validSchedule_static hs₀ hs₀.reverse reqs, ?_⟩
    exact ratio_arith hpq hm halg (by omega) hI

/-- No deterministic online list-update strategy is `(c, b)`-competitive from an initial
arrangement `s₀` when `c (n + 1) < 2 n`. -/
theorem not_isCompetitiveFrom_of_lt (A : DetStrategy (problem α)) {s₀ : List α}
    (hs₀ : IsArrangement s₀) {c : Nat} (hc : c * (Fintype.card α + 1) < 2 * Fintype.card α)
    (b : Nat) : ¬ A.IsCompetitiveFrom s₀ c b := by
  intro h
  obtain ⟨reqs, states, hv, hlt⟩ :=
    exists_ratio_violation_of_lt A hs₀ (p := c) (q := 1) (by rwa [Nat.mul_one]) b
  have := h reqs states hv
  omega

/-- No deterministic online list-update strategy is `(c, b)`-competitive when
`c (n + 1) < 2 n`. -/
theorem not_isCompetitive_of_lt (A : DetStrategy (problem α)) {c : Nat}
    (hc : c * (Fintype.card α + 1) < 2 * Fintype.card α) (b : Nat) : ¬ A.IsCompetitive c b :=
  fun h => not_isCompetitiveFrom_of_lt A isArrangement_univ_toList hc b
    (h _ isArrangement_univ_toList)

/-- No deterministic online list-update strategy is `(c, b)`-competitive across arbitrary initial
arrangements when `c (n + 1) < 2 n`. -/
theorem not_isCompetitiveAnyInit_of_lt (A : DetStrategy (problem α)) {c : Nat}
    (hc : c * (Fintype.card α + 1) < 2 * Fintype.card α) (b : Nat) :
    ¬ A.IsCompetitiveAnyInit c b :=
  fun h => not_isCompetitive_of_lt A hc b h.toIsCompetitive

/-- Over at least two items, no deterministic online list-update strategy is `(1, b)`-competitive
for any additive constant `b`. -/
theorem not_isCompetitive_one (A : DetStrategy (problem α)) (hα : 2 ≤ Fintype.card α) (b : Nat) :
    ¬ A.IsCompetitive 1 b :=
  not_isCompetitive_of_lt A (by omega) b

end Cslib.DataStructure.ListUpdate
