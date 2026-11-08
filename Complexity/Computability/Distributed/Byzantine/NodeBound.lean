/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Distributed.Byzantine.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# The `3t + 1` node bound for Byzantine agreement

No deterministic synchronous protocol on `n` processes solves Byzantine agreement against `t`
Byzantine faults when `2 ≤ n ≤ 3t`, in any number of rounds
[Fischer, Lynch and Merritt, Theorem 1 and §3.1][FischerLynchMerritt1985]. The bound was first
proved by [Pease, Shostak and Lamport, §4][PeaseShostakLamport1980] for interactive consistency.

The proof is the covering argument of Fischer, Lynch and Merritt. Split the processes into groups
`A`, `B`, `C` of at most `t` processes each. Take two copies of the network, the first with all
inputs `0` and the second with all inputs `1`, and rewire them so that every edge between `A` and
`C` crosses from one copy to the other; when the groups are single processes this is the hexagon
`A₀ B₀ C₀ A₁ B₁ C₁`. Any two groups of one copy, adjacent in this network, see exactly what they
would see in a run of the original network in which the third group is faulty and replays the
messages of the network (`Protocol.state_eq_coverState`). With `A` faulty, validity forces `C₀`
to decide `0`; with `C` faulty, `A₁` decides `1`; with `B` faulty, `A₁` and `C₀` are the correct
processes of one run, and agreement fails.

Unlike the source, the middle group `B` may be empty, so the argument also covers `n = 2`, where
it is the familiar two-process scenario. The bound is sharp: for `n ≤ 1` agreement is trivial,
and for `t = 1` and `n ≥ 4` it is solved in two rounds
(`Complexity.Computability.Distributed.Byzantine.OralMessages`).

## Main results

* `Cslib.Distributed.Byzantine.Protocol.not_solvesByzantineAgreement_of_partition`: no protocol
  tolerates `t` faults when the processes split into three groups of at most `t`, the first and
  last nonempty.
* `Cslib.Distributed.Byzantine.Protocol.not_solvesByzantineAgreement`: no protocol tolerates `t`
  faults when `2 ≤ n ≤ 3t`.
* `Cslib.Distributed.Byzantine.Protocol.not_solvesByzantineAgreement_three`: three processes do
  not tolerate one fault (the hexagon argument).

## References

* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985]
* [M. Pease, R. Shostak, L. Lamport, *Reaching agreement in the presence of
  faults*][PeaseShostakLamport1980]
-/

public section

namespace Cslib.Distributed.Byzantine

namespace Protocol

variable {P S M : Type*} [DecidableEq P] [Fintype P] (π : Protocol P S M)

/-- **The covering argument** [Fischer, Lynch and Merritt, §3.1][FischerLynchMerritt1985]. If the
processes split, by `g`, into three groups of at most `t` processes, the first containing `a` and
the last containing `c`, then no protocol solves Byzantine agreement against `t` faults, in any
number of rounds. The middle group may be empty. -/
theorem not_solvesByzantineAgreement_of_partition {t R : ℕ} (g : P → Fin 3)
    (hcard : ∀ k, ({i | g i = k} : Finset P).card ≤ t) {a c : P} (ha : g a = 0) (hc : g c = 2) :
    ¬ π.SolvesByzantineAgreement t R := by
  intro h
  -- The double cover: node `(i, b)` runs process `i` on input `b`, and edges between the first
  -- and the last group cross between the two copies.
  let cross : P → P → Bool := fun i j => decide ((g i = 0 ∧ g j = 2) ∨ (g i = 2 ∧ g j = 0))
  let nbr : P × Bool → P → P × Bool := fun p j => (j, p.2 ^^ cross p.1 j)
  let cover := π.coverState Prod.fst Prod.snd nbr
  -- Faulty processes replay the cover to each correct process `i`, placed in copy `σ i`.
  let adv : (P → Bool) → ℕ → P → P → M := fun σ r j i =>
    π.send r j (cover r (nbr (i, σ i) j)) i
  have hmem : ∀ k j, j ∉ ({i | g i = k} : Finset P) ↔ g j ≠ k := by
    intro k j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- With group `k` faulty, a placement `σ` of the other groups compatible with the wiring makes
  -- every correct process behave as its node of the cover.
  have key : ∀ (k : Fin 3) (σ : P → Bool),
      (∀ i j, g i ≠ k → g j ≠ k → (σ i ^^ cross i j) = σ j) →
      ∀ i, g i ≠ k → π.decision {i | g i = k} (adv σ) σ R i = π.output i (cover R (i, σ i)) := by
    intro k σ hσ i hi
    unfold decision
    rw [state_eq_coverState π Prod.fst Prod.snd nbr _ (adv σ) σ (fun i => (i, σ i))
      (fun _ _ => rfl) (fun _ _ => rfl) ?_ (fun _ _ _ _ _ => rfl) R i ((hmem k i).2 hi)]
    intro i hi j hj
    simp only [nbr, Prod.mk.injEq, true_and]
    exact hσ i j ((hmem k i).1 hi) ((hmem k j).1 hj)
  have hc₀ : g c ≠ 0 := by rw [hc]; decide
  have ha₂ : g a ≠ 2 := by rw [ha]; decide
  -- `A` faulty, `B` and `C` correct with input `0`: by validity `C₀` decides `0`.
  have h₀ := h.validity _ (hcard 0) (adv fun _ => false) (fun _ => false) false (fun _ _ => rfl)
    c ((hmem 0 c).2 hc₀)
  rw [key 0 _ (fun i j hi hj => by simp only [cross, hi, hj, false_and, and_false, or_self,
    decide_false, Bool.xor_false]) c hc₀] at h₀
  -- `C` faulty, `A` and `B` correct with input `1`: by validity `A₁` decides `1`.
  have h₂ := h.validity _ (hcard 2) (adv fun _ => true) (fun _ => true) true (fun _ _ => rfl)
    a ((hmem 2 a).2 ha₂)
  rw [key 2 _ (fun i j hi hj => by simp only [cross, hi, hj, false_and, and_false, or_self,
    decide_false, Bool.xor_false]) a ha₂] at h₂
  -- `B` faulty, `A` correct in copy `1` and `C` correct in copy `0`: by agreement `A₁` and `C₀`
  -- decide alike.
  have hfin : ∀ u v : Fin 3, u ≠ 1 → v ≠ 1 →
      (decide (u = 0) ^^ decide ((u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0))) = decide (v = 0) := by
    decide
  have h₁ := h.agreement _ (hcard 1) (adv fun i => decide (g i = 0)) (fun i => decide (g i = 0))
    a ((hmem 1 a).2 (by rw [ha]; decide)) c ((hmem 1 c).2 (by rw [hc]; decide))
  rw [key 1 _ (fun i j hi hj => hfin _ _ hi hj) a (by rw [ha]; decide),
    key 1 _ (fun i j hi hj => hfin _ _ hi hj) c (by rw [hc]; decide)] at h₁
  have h20 : decide ((2 : Fin 3) = 0) = false := by decide
  simp only [ha, hc, decide_true, h20] at h₁
  rw [h₂, h₀] at h₁
  exact Bool.true_eq_false_eq_False h₁

/-- **No Byzantine agreement with `n ≤ 3t` processes**
[Fischer, Lynch and Merritt, Theorem 1][FischerLynchMerritt1985]: a protocol on `n` processes with
`2 ≤ n ≤ 3t` does not solve Byzantine agreement against `t` faults, in any number of rounds. The
processes `0, …, n - 1` are split by residue modulo `3`, so that `0` and `1` lie in the first and
last group. -/
theorem not_solvesByzantineAgreement {t R : ℕ} (h2 : 2 ≤ Fintype.card P)
    (h3 : Fintype.card P ≤ 3 * t) : ¬ π.SolvesByzantineAgreement t R := by
  let e := Fintype.equivFin P
  let g : P → Fin 3 := fun i => ⟨2 * (e i : ℕ) % 3, Nat.mod_lt _ (by omega)⟩
  refine π.not_solvesByzantineAgreement_of_partition g (fun k => ?_)
    (a := e.symm ⟨0, by omega⟩) (c := e.symm ⟨1, by omega⟩) ?_ ?_
  · calc ({i | g i = k} : Finset P).card
        ≤ (Finset.range t).card := Finset.card_le_card_of_injOn (fun i => (e i : ℕ) / 3) ?_ ?_
      _ = t := Finset.card_range t
    · intro i _
      have := (e i).isLt
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro i hi j hj hij
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
      apply e.injective
      have hi' := congrArg Fin.val hi
      have hj' := congrArg Fin.val hj
      simp only [g] at hi' hj' hij
      ext
      omega
  · simp only [g, Equiv.apply_symm_apply]
    rfl
  · simp only [g, Equiv.apply_symm_apply]
    rfl

/-- **The hexagon argument** [Fischer, Lynch and Merritt, §3.1][FischerLynchMerritt1985]: three
processes do not solve Byzantine agreement against one fault, in any number of rounds. -/
theorem not_solvesByzantineAgreement_three {S M : Type*} (π : Protocol (Fin 3) S M) (R : ℕ) :
    ¬ π.SolvesByzantineAgreement 1 R :=
  π.not_solvesByzantineAgreement_of_partition (t := 1) id (by decide) (a := 0) (c := 2) rfl rfl

end Protocol

end Cslib.Distributed.Byzantine
