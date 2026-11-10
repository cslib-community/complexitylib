/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Randomized
import CslibFrontier.Foundations.Data.ENat.IInf
import CslibFrontier.Probability.Minimax

/-!
# Distributional complexity and Yao's minimax principle

The *distributional complexity* `D^ν_ε(R)` of a relation `R` under a distribution `ν` on the pairs
of inputs is the least depth of a deterministic protocol that errs with probability at most `ε` on
inputs drawn from `ν` (`Protocol.distributionalComplexity`)
[Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997].

*Yao's minimax principle* [Yao1977] says that randomized protocols are exactly as good as
deterministic protocols against the hardest distribution: the public-coin complexity of `R` on
`A × B` with error `ε` is the largest distributional complexity with error `ε` under a
distribution on `A × B` (`PublicCoin.ecomplexity_eq_iSup_distributionalComplexity`), when the
inputs are finite and there is some output. One direction is the averaging argument
(`PublicCoin.distributionalComplexity_le_ecomplexity`): a public-coin protocol erring with
probability at most `ε` on every input draws, for every `ν`, some deterministic protocol erring with
probability at most `ε` on inputs drawn from `ν`. The other follows from von Neumann's minimax
theorem for the game in which one player picks a deterministic protocol sending at most `c` bits
and the other a pair of inputs (`PublicCoin.ecomplexity_le_of_forall_distributionalComplexity_le`,
from `Probability.PMF.exists_forall_toOuterMeasure_le`). So lower bounds on randomized protocols
are exactly lower bounds on deterministic protocols over a well-chosen distribution.

## Main definitions

* `Cslib.Communication.Protocol.distributionalComplexity`: the distributional complexity.

## Main results

* `Cslib.Communication.PublicCoin.distributionalComplexity_le_ecomplexity`: the easy direction of
  Yao's principle.
* `Cslib.Communication.PublicCoin.ecomplexity_le_of_forall_distributionalComplexity_le`: the hard
  direction of Yao's principle.
* `Cslib.Communication.PublicCoin.ecomplexity_eq_iSup_distributionalComplexity`,
  `Cslib.Communication.PublicCoin.ecomplexityFun_eq_iSup_distributionalComplexity`: Yao's
  minimax principle.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

@[expose] public section

namespace Cslib.Communication

open Probability

variable {X Y Z : Type*}

namespace Protocol

/-- The *distributional complexity* `D^ν_ε(R)` of `R` under a distribution `ν` on the pairs of
inputs: the least depth of a deterministic protocol whose output on a pair of inputs drawn from `ν`
is not related to them by `R` with probability at most `ε`, or `⊤` if there is none. -/
noncomputable def distributionalComplexity (ε : ℝ) (R : X → Y → Z → Prop) (ν : PMF (X × Y)) :
    ℕ∞ :=
  ⨅ p : {p : Protocol X Y Z // p.distributionalError ν R ≤ ε}, (p.1.depth : ℕ∞)

variable {p : Protocol X Y Z} {ε ε' : ℝ} {R : X → Y → Z → Prop} {ν : PMF (X × Y)}

theorem distributionalComplexity_le_depth (hp : p.distributionalError ν R ≤ ε) :
    distributionalComplexity ε R ν ≤ p.depth :=
  iInf_le (fun p : {p : Protocol X Y Z // p.distributionalError ν R ≤ ε} => (p.1.depth : ℕ∞))
    ⟨p, hp⟩

theorem le_distributionalComplexity_iff {k : ℕ∞} :
    k ≤ distributionalComplexity ε R ν ↔
      ∀ p : Protocol X Y Z, p.distributionalError ν R ≤ ε → k ≤ p.depth := by
  simp only [distributionalComplexity, le_iInf_iff, Subtype.forall]

theorem distributionalComplexity_le_iff {k : ℕ} :
    distributionalComplexity ε R ν ≤ k ↔
      ∃ p : Protocol X Y Z, p.distributionalError ν R ≤ ε ∧ p.depth ≤ k := by
  simp only [distributionalComplexity, ENat.iInf_natCast_le_natCast_iff, Subtype.exists,
    exists_prop]

/-- Allowing more error makes a relation easier. -/
theorem distributionalComplexity_anti (hε : ε ≤ ε') :
    distributionalComplexity ε' R ν ≤ distributionalComplexity ε R ν :=
  le_distributionalComplexity_iff.mpr fun _ hp => distributionalComplexity_le_depth (hp.trans hε)

end Protocol

namespace PublicCoin

variable {ε : ℝ} {R : X → Y → Z → Prop} {A : Set X} {B : Set Y}

/-- **Yao's principle, the easy direction**: under every distribution `ν` on `A × B`, the
distributional complexity with error `ε` is at most the public-coin complexity on `A × B` with
error `ε`. -/
theorem distributionalComplexity_le_ecomplexity {ν : PMF (X × Y)}
    (hν : ∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B) :
    Protocol.distributionalComplexity ε R ν ≤ ecomplexity ε R A B :=
  le_ecomplexity_iff.mpr fun μ hμ => by
    obtain ⟨p, hp, herr⟩ := hμ.exists_distributionalError_le ν hν
    exact (Protocol.distributionalComplexity_le_depth herr).trans (depth_le_depth hp)

/-- **Yao's principle, the hard direction**: on finite inputs, if under every distribution on
`A × B` some deterministic protocol sending at most `c` bits errs with probability at most `ε`,
then some public-coin protocol sending at most `c` bits errs with probability at most `ε` on every
pair of inputs from `A × B`. The protocol draws from finitely many deterministic protocols. -/
theorem ecomplexity_le_of_forall_distributionalComplexity_le [Finite X] [Finite Y] [Nonempty Z]
    {c : ℕ} (h : ∀ ν : PMF (X × Y), (∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B) →
      Protocol.distributionalComplexity ε R ν ≤ c) :
    ecomplexity ε R A B ≤ c := by
  -- The game: one player picks a protocol sending at most `c` bits, the other a pair of inputs
  -- from `A × B`, and the first loses when the protocol errs.
  have : Nonempty {p : Protocol X Y Z // p.depth ≤ c} :=
    ⟨⟨.output (Classical.arbitrary Z), by simp⟩⟩
  obtain ⟨μ, -, hμ⟩ := PMF.exists_forall_toOuterMeasure_le
    (I := {p : Protocol X Y Z // p.depth ≤ c}) (J := {q : X × Y // q.1 ∈ A ∧ q.2 ∈ B})
    (fun p q => ¬R q.1.1 q.1.2 (p.1.run q.1.1 q.1.2)) (ε := ε) fun ν => by
      obtain ⟨p, hp, hc⟩ := Protocol.distributionalComplexity_le_iff.mp
        (h (ν.map Subtype.val) fun q hq => by
          obtain ⟨q', -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hq
          exact q'.2)
      refine ⟨⟨p, hc⟩, ?_⟩
      rwa [Protocol.distributionalError, PMF.toOuterMeasure_map_apply] at hp
  refine ecomplexity_le_iff.mpr ⟨μ.map Subtype.val, fun x hx y hy => ?_, ?_⟩
  · rw [errorProb, PMF.toOuterMeasure_map_apply]
    exact hμ ⟨(x, y), hx, hy⟩
  · refine depth_le_iff.mpr fun p hp => ?_
    obtain ⟨p', -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    exact_mod_cast p'.2

/-- **Yao's principle**: on finite inputs, the public-coin complexity on `A × B` with error `ε` is
at most `c` exactly when the distributional complexity with error `ε` is at most `c` under every
distribution on `A × B`. -/
theorem ecomplexity_le_iff_forall_distributionalComplexity_le [Finite X] [Finite Y] [Nonempty Z]
    {c : ℕ} :
    ecomplexity ε R A B ≤ c ↔ ∀ ν : PMF (X × Y), (∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B) →
      Protocol.distributionalComplexity ε R ν ≤ c :=
  ⟨fun h _ hν => (distributionalComplexity_le_ecomplexity hν).trans h,
    ecomplexity_le_of_forall_distributionalComplexity_le⟩

/-- **Yao's minimax principle** [Kushilevitz and Nisan, Theorem 3.20][KushilevitzNisan1997]: on
finite inputs, the public-coin complexity on `A × B` with error `ε` is the largest distributional
complexity with error `ε` under a distribution on `A × B`. -/
theorem ecomplexity_eq_iSup_distributionalComplexity [Finite X] [Finite Y] [Nonempty Z] :
    ecomplexity ε R A B = ⨆ (ν : PMF (X × Y)) (_ : ∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B),
      Protocol.distributionalComplexity ε R ν := by
  refine le_antisymm ?_ (iSup₂_le fun _ hν => distributionalComplexity_le_ecomplexity hν)
  cases hsup : ⨆ (ν : PMF (X × Y)) (_ : ∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B),
      Protocol.distributionalComplexity ε R ν using ENat.recTopCoe with
  | top => exact le_top
  | coe c =>
    exact ecomplexity_le_of_forall_distributionalComplexity_le fun ν hν =>
      hsup ▸ le_iSup₂ (f := fun (ν : PMF (X × Y)) (_ : ∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B) =>
        Protocol.distributionalComplexity ε R ν) ν hν

/-- **Yao's minimax principle** for computing a function: on finite inputs, the public-coin
complexity of `f` with error `ε` is the largest distributional complexity of `f` with error `ε`. -/
theorem ecomplexityFun_eq_iSup_distributionalComplexity [Finite X] [Finite Y] [Nonempty Z]
    (f : X → Y → Z) :
    ecomplexityFun ε f = ⨆ ν : PMF (X × Y),
      Protocol.distributionalComplexity ε (fun x y z => f x y = z) ν := by
  rw [ecomplexityFun, ecomplexity_eq_iSup_distributionalComplexity]
  simp only [Set.mem_univ, and_self, implies_true, iSup_pos]

end PublicCoin

end Cslib.Communication
