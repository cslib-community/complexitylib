/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Randomized
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Probability.PMF.Event

/-!
# Unbounded-error communication

A private-coin protocol solves a relation with *unbounded error* when on every pair of inputs its
answer is correct with probability strictly greater than `1 / 2`, that is, its error probability
is less than `1 / 2` (`PrivateCoin.SolvesUnbounded`). The *unbounded-error communication
complexity* is the least depth of such a protocol, over all numbers of private random bits
(`PrivateCoin.uppComplexity`, `PrivateCoin.uppComplexityFun`) [Paturi and Simon][PaturiSimon1986].

The private random strings are finite, of any lengths `a` and `b`, so the error probabilities of a
protocol are multiples of `1 / 2 ^ (a + b)`, and a protocol with unbounded error has error at most
some fixed `ε < 1 / 2` (`PrivateCoin.SolvesUnbounded.exists_solves`). Hence the unbounded-error
complexity is the infimum of the bounded-error complexities `PrivateCoin.ecomplexity ε` over all
`ε < 1 / 2` (`PrivateCoin.uppComplexity_eq_iInf`), which is the definition of `UPP` in
[Sherstov and Wu, eq. (2.8)][SherstovWu2019].

The coins must be private: on finite inputs, players sharing public coins could guess Alice's
input, check the guess with one bit, answer correctly when it is right and flip a fair public coin
otherwise, so every function would have unbounded-error cost at most two.

The sign-rank characterizes the unbounded-error complexity of Boolean functions; see
`CslibFrontier.Computability.Communication.PaturiSimon`.

## Main definitions

* `Cslib.Communication.PrivateCoin.SolvesUnbounded`: solving a relation with unbounded error.
* `Cslib.Communication.PrivateCoin.uppComplexity`,
  `Cslib.Communication.PrivateCoin.uppComplexityFun`: unbounded-error communication complexity.

## Main results

* `Cslib.Communication.PrivateCoin.errorProb_eq_card`: the error probability as a fraction of
  random strings.
* `Cslib.Communication.PrivateCoin.SolvesUnbounded.exists_solves`,
  `Cslib.Communication.PrivateCoin.uppComplexity_eq_iInf`: unbounded error as the limit of bounded
  error.
* `Cslib.Communication.PrivateCoin.uppComplexity_le_ecomplexity`,
  `Cslib.Communication.PrivateCoin.uppComplexity_le_protocol`: unbounded error is at most bounded
  error and deterministic communication.

## References

* [R. Paturi and J. Simon, *Probabilistic communication complexity*][PaturiSimon1986]
* [A. A. Sherstov and P. Wu, *Near-optimal lower bounds on the threshold degree and sign-rank of
  AC⁰*][SherstovWu2019]
-/

open Finset

public section

namespace Cslib.Communication

open Probability

variable {X Y Z X' Y' : Type*}

namespace PrivateCoin

variable {a b : ℕ}

/-- The error probability of a private-coin protocol is the fraction of the `2 ^ a * 2 ^ b` pairs
of random strings on which its output is not related to the inputs. -/
theorem errorProb_eq_card (P : PrivateCoin a b X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y)
    [DecidablePred (R x y)] :
    P.errorProb R x y =
      (#{r : BitString a × BitString b | ¬R x y (P.run (x, r.1) (y, r.2))} : ℝ) /
        (2 ^ a * 2 ^ b) := by
  rw [errorProb, PMF.toOuterMeasure_apply_toReal]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, BitString.card, Set.mem_ofPred_eq]
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp [ENNReal.toReal_inv]

/-- A private-coin protocol solves `R` on `A × B` with *unbounded error* when on every pair of
inputs from `A × B` its output is related to them with probability more than `1 / 2`, that is, its
error probability is less than `1 / 2` [Paturi and Simon][PaturiSimon1986]. -/
@[expose] def SolvesUnbounded (P : PrivateCoin a b X Y Z) (R : X → Y → Z → Prop) (A : Set X)
    (B : Set Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, P.errorProb R x y < 1 / 2

/-- The *unbounded-error communication complexity* of `R` on `A × B`: the least depth of a
private-coin protocol solving it with unbounded error, with any numbers of random bits, or `⊤`
if there is none [Paturi and Simon][PaturiSimon1986]. -/
noncomputable def uppComplexity (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : ℕ∞ :=
  ⨅ (a : ℕ) (b : ℕ) (P : {P : PrivateCoin a b X Y Z // P.SolvesUnbounded R A B}),
    (P.1.depth : ℕ∞)

/-- The unbounded-error communication complexity of computing `f`: `uppComplexity` of the
relation `f x y = z` on all inputs. -/
noncomputable def uppComplexityFun (f : X → Y → Z) : ℕ∞ :=
  uppComplexity (fun x y z => f x y = z) Set.univ Set.univ

variable {P : PrivateCoin a b X Y Z} {R : X → Y → Z → Prop} {A A' : Set X} {B B' : Set Y}
  {ε : ℝ}

theorem SolvesUnbounded.mono (h : P.SolvesUnbounded R A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    P.SolvesUnbounded R A' B' :=
  fun x hx y hy => h x (hA hx) y (hB hy)

/-- A protocol with error at most some `ε < 1 / 2` solves with unbounded error. -/
theorem Solves.solvesUnbounded (h : P.Solves ε R A B) (hε : ε < 1 / 2) :
    P.SolvesUnbounded R A B :=
  fun x hx y hy => (h x hx y hy).trans_lt hε

/-- Conversely, a protocol that solves with unbounded error has error at most some fixed
`ε < 1 / 2` on all inputs, even on infinitely many: its error probabilities are multiples of
`1 / 2 ^ (a + b)`, so they are at most `1 / 2 - 1 / 2 ^ (a + b + 1)`. -/
theorem SolvesUnbounded.exists_solves (h : P.SolvesUnbounded R A B) :
    ∃ ε < 1 / 2, P.Solves ε R A B := by
  refine ⟨1 / 2 - 1 / (2 * (2 ^ a * 2 ^ b)), by
    have : (0 : ℝ) < 2 ^ a * 2 ^ b := by positivity
    have : (0 : ℝ) < 1 / (2 * (2 ^ a * 2 ^ b)) := by positivity
    linarith, fun x hx y hy => ?_⟩
  have hlt := h x hx y hy
  classical
  rw [errorProb_eq_card] at hlt ⊢
  set k := #{r : BitString a × BitString b | ¬R x y (P.run (x, r.1) (y, r.2))}
  have hN : (0 : ℝ) < 2 ^ a * 2 ^ b := by positivity
  rw [div_lt_iff₀ hN] at hlt
  -- `k < 2 ^ a * 2 ^ b / 2` forces `2 k + 1 ≤ 2 ^ a * 2 ^ b`.
  have hk : 2 * k + 1 ≤ 2 ^ a * 2 ^ b := by
    have : (2 * k : ℝ) < 2 ^ a * 2 ^ b := by linarith
    have : 2 * k < 2 ^ a * 2 ^ b := by exact_mod_cast this
    omega
  have hk' : (2 * k + 1 : ℝ) ≤ 2 ^ a * 2 ^ b := by exact_mod_cast hk
  rw [div_le_iff₀ hN]
  field_simp
  linarith

theorem uppComplexity_le_depth (h : P.SolvesUnbounded R A B) : uppComplexity R A B ≤ P.depth :=
  (iInf_le _ a).trans <| (iInf_le _ b).trans <|
    iInf_le (fun P : {P : PrivateCoin a b X Y Z // P.SolvesUnbounded R A B} => (P.1.depth : ℕ∞))
      ⟨P, h⟩

theorem le_uppComplexity_iff {k : ℕ∞} :
    k ≤ uppComplexity R A B ↔
      ∀ a b (P : PrivateCoin a b X Y Z), P.SolvesUnbounded R A B → k ≤ P.depth := by
  simp only [uppComplexity, le_iInf_iff, Subtype.forall]

theorem uppComplexity_le_iff {k : ℕ} :
    uppComplexity R A B ≤ k ↔
      ∃ a b, ∃ P : PrivateCoin a b X Y Z, P.SolvesUnbounded R A B ∧ P.depth ≤ k := by
  refine ⟨fun h => ?_, fun ⟨a, b, P, hP, hk⟩ =>
    (uppComplexity_le_depth hP).trans (by exact_mod_cast hk)⟩
  by_contra! hlt
  have : ((k + 1 : ℕ) : ℕ∞) ≤ uppComplexity R A B :=
    le_uppComplexity_iff.mpr fun a b P hP => by exact_mod_cast hlt a b P hP
  have := this.trans h
  norm_cast at this
  omega

/-- **Unbounded error is the limit of bounded error**: the unbounded-error complexity is the
infimum of the private-coin complexities with error `ε` over all `ε < 1 / 2`
[Sherstov and Wu, eq. (2.8)][SherstovWu2019]. -/
theorem uppComplexity_eq_iInf :
    uppComplexity R A B = ⨅ (ε : ℝ) (_ : ε < 1 / 2), ecomplexity ε R A B := by
  refine le_antisymm (le_iInf₂ fun ε hε => le_ecomplexity_iff.mpr fun a b P hP =>
    uppComplexity_le_depth (hP.solvesUnbounded hε)) ?_
  refine le_uppComplexity_iff.mpr fun a b P hP => ?_
  obtain ⟨ε, hε, h⟩ := hP.exists_solves
  exact (iInf₂_le ε hε).trans (ecomplexity_le_depth h)

/-- Unbounded error is at most bounded error `ε < 1 / 2`. -/
theorem uppComplexity_le_ecomplexity (hε : ε < 1 / 2) :
    uppComplexity R A B ≤ ecomplexity ε R A B := by
  rw [uppComplexity_eq_iInf]
  exact iInf₂_le ε hε

/-- Unbounded error is at most deterministic communication. -/
theorem uppComplexity_le_protocol : uppComplexity R A B ≤ Protocol.ecomplexity R A B :=
  (uppComplexity_le_ecomplexity (by norm_num : (0 : ℝ) < 1 / 2)).trans
    (ecomplexity_le_protocol le_rfl)

/-- Solving a relation with unbounded error on larger sets is harder. -/
theorem uppComplexity_mono (hA : A' ⊆ A) (hB : B' ⊆ B) :
    uppComplexity R A' B' ≤ uppComplexity R A B :=
  le_uppComplexity_iff.mpr fun _ _ _ hP => uppComplexity_le_depth (hP.mono hA hB)

variable {f : X → Y → Z}

theorem uppComplexityFun_le_depth
    (h : P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ) :
    uppComplexityFun f ≤ P.depth :=
  uppComplexity_le_depth h

theorem uppComplexityFun_le_iff {k : ℕ} :
    uppComplexityFun f ≤ k ↔ ∃ a b, ∃ P : PrivateCoin a b X Y Z,
      P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ ∧ P.depth ≤ k :=
  uppComplexity_le_iff

theorem le_uppComplexityFun_iff {k : ℕ∞} :
    k ≤ uppComplexityFun f ↔ ∀ a b (P : PrivateCoin a b X Y Z),
      P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ → k ≤ P.depth :=
  le_uppComplexity_iff

/-- Unbounded error is at most deterministic communication. -/
theorem uppComplexityFun_le_protocol : uppComplexityFun f ≤ Protocol.ecomplexityFun f :=
  uppComplexity_le_protocol

/-- Transforming the inputs does not make a function harder with unbounded error. -/
theorem uppComplexityFun_comap_le (f : X → Y → Z) (g : X' → X) (h : Y' → Y) :
    uppComplexityFun (fun x y => f (g x) (h y)) ≤ uppComplexityFun f := by
  refine le_uppComplexityFun_iff.mpr fun a b P hP => ?_
  refine (uppComplexity_le_depth (P := P.comap (Prod.map g id) (Prod.map h id))
    fun x _ y _ => ?_).trans (by rw [Protocol.depth_comap])
  have := hP (g x) trivial (h y) trivial
  classical
  rw [errorProb_eq_card] at this ⊢
  simpa using this

end PrivateCoin

end Cslib.Communication

end
