/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Sensitivity
public import CslibFrontier.Computability.QueryComplexity.OneSided

/-!
# Decision trees from certificates

A certificate for one value of a function and a certificate for another value disagree at some
variable (`IsCertificate.exists_mem_inter_ne`). So querying the variables of a smallest certificate
for the value `1` either confirms the value `1`, or makes every certificate for the value `0` of
the function restricted by the answers shorter. Repeating this computes a Boolean function with at
most `C₀(f) C₁(f)` queries, where `C_b(f)` is the largest certificate complexity at an input of
value `b` (`complexity_le_certificateComplexityFor_mul`) [BlumImpagliazzo1987], [Tardos1989],
[Jukna, Section 14.2][Jukna2012]. In particular, decision tree complexity is at most the square of
certificate complexity.

## Main results

* `Cslib.DecisionTree.complexity_le_card_add`: querying a set of variables and continuing with
  trees for the restricted functions.
* `Cslib.DecisionTree.complexity_le_certificateComplexityFor_mul`: `D(f) ≤ C₀(f) C₁(f)`.
* `Cslib.DecisionTree.complexity_le_certificateComplexity_sq`: `D(f) ≤ C(f) ^ 2`.

## References

* [M. Blum and R. Impagliazzo, *Generic oracles and oracle classes*][BlumImpagliazzo1987]
* [G. Tardos, *Query complexity, or why is it difficult to separate NP^A ∩ coNP^A from P^A by
  random oracles A?*][Tardos1989]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib

open Finset

variable {n : ℕ}

namespace QueryComplexity

/-- A certificate for one value and a certificate for another value disagree at a variable that
both contain. -/
theorem IsCertificate.exists_mem_inter_ne {f : BooleanFunction n} {x w : BitString n}
    {S T : Finset (Fin n)} (hS : IsCertificate f x S) (hT : IsCertificate f w T) (hne : f x ≠ f w) :
    ∃ i ∈ T ∩ S, w i ≠ x i := by
  by_contra! h
  have hvx : f (T.piecewise w x) = f x := hS _ fun i hi => by
    by_cases hiT : i ∈ T
    · simp [hiT, h i (mem_inter.2 ⟨hiT, hi⟩)]
    · simp [hiT]
  have hvw : f (T.piecewise w x) = f w := hT _ fun i hi => by simp [hi]
  exact hne (hvx.symm.trans hvw)

/-- Fixing the variables of `S` to the values `a` turns a certificate `T` at the filled input into
the certificate `T \ S` of the restricted function. -/
theorem IsCertificate.restrict {f : BooleanFunction n} {S T : Finset (Fin n)} {a z : BitString n}
    (hT : IsCertificate f (S.piecewise a z) T) :
    IsCertificate (fun y => f (S.piecewise a y)) z (T \ S) := fun y hy =>
  hT _ fun i hi => by
    by_cases hiS : i ∈ S
    · simp [hiS]
    · simp [hiS, hy i (mem_sdiff.2 ⟨hi, hiS⟩)]

end QueryComplexity

namespace DecisionTree

variable {ι β : Type*} [DecidableEq ι]

/-- Querying the variables of `S` and continuing with a tree for the function restricted by the
answers computes `f` with `#S` more queries. -/
theorem complexity_le_card_add [Finite ι] {f : (ι → Bool) → β} (S : Finset ι) {d : ℕ}
    (h : ∀ a, complexity (fun y => f (S.piecewise a y)) ≤ d) : complexity f ≤ #S + d := by
  choose t ht hd using fun a => complexity_le_iff.1 (h a)
  refine complexity_le_iff.2 ⟨graft S.toList t (fun _ => false), fun y => ?_,
    (depth_graft_le _ _ _ hd).trans_eq (by rw [length_toList])⟩
  rw [eval_graft, ht]
  dsimp only
  congr 1
  funext j
  by_cases hj : j ∈ S <;> simp [hj]

end DecisionTree

namespace QueryComplexity

/-- Restricting by answers on `S` does not lengthen certificates: every certificate for the
function restricted by `a` at `z` is at most as long as a certificate of `f` at the filled input,
minus its variables in `S`. -/
private theorem exists_certificateComplexityAt_restrict_le {f : BooleanFunction n}
    (S : Finset (Fin n)) (a z : BitString n) :
    ∃ T, IsCertificate f (S.piecewise a z) T ∧ #T = certificateComplexityAt f (S.piecewise a z) ∧
      certificateComplexityAt (fun y => f (S.piecewise a y)) z ≤ #(T \ S) := by
  obtain ⟨T, hT, hcard⟩ := exists_isCertificate_card_eq f (S.piecewise a z)
  exact ⟨T, hT, hcard, certificateComplexityAt_le hT.restrict⟩

/-- Restricting by answers on a certificate `S` for a value `b` keeps the certificates of the
other values, minus their variables in `S`, which they all meet. -/
private theorem certificateComplexityFor_restrict_lt {f : BooleanFunction n} {x : BitString n}
    {S : Finset (Fin n)} (hS : IsCertificate f x S) (a : BitString n) {c : Bool}
    (hc : c ≠ f x) {m : ℕ} (hm : certificateComplexityFor f c ≤ m + 1) :
    certificateComplexityFor (fun y => f (S.piecewise a y)) c ≤ m := by
  refine Finset.sup_le fun z hz => ?_
  have hz : f (S.piecewise a z) = c := (mem_filter.1 hz).2
  obtain ⟨T, hT, hTcard, hle⟩ := exists_certificateComplexityAt_restrict_le (f := f) S a z
  obtain ⟨i, hi, -⟩ := hS.exists_mem_inter_ne hT (by rw [hz]; exact hc.symm)
  have := card_sdiff_add_card_inter T S
  have := card_pos.2 ⟨i, hi⟩
  have := (certificateComplexityAt_le_certificateComplexityFor hz).trans hm
  lia

/-- Restricting does not raise certificate complexity for a value. -/
theorem certificateComplexityFor_restrict_le {f : BooleanFunction n} (S : Finset (Fin n))
    (a : BitString n) (c : Bool) :
    certificateComplexityFor (fun y => f (S.piecewise a y)) c ≤ certificateComplexityFor f c := by
  refine Finset.sup_le fun z hz => ?_
  have hz : f (S.piecewise a z) = c := (mem_filter.1 hz).2
  obtain ⟨T, -, hTcard, hle⟩ := exists_certificateComplexityAt_restrict_le (f := f) S a z
  exact hle.trans ((card_le_card sdiff_subset).trans
    (hTcard.trans_le (certificateComplexityAt_le_certificateComplexityFor hz)))

end QueryComplexity

namespace DecisionTree

open QueryComplexity

/-- **Certificates give decision trees.** A Boolean function is computed by a decision tree of
depth at most `C₀(f) C₁(f)`. -/
theorem complexity_le_certificateComplexityFor_mul (f : BooleanFunction n) :
    complexity f ≤ certificateComplexityFor f false * certificateComplexityFor f true := by
  suffices ∀ m (f : BooleanFunction n), certificateComplexityFor f false ≤ m →
      complexity f ≤ m * certificateComplexityFor f true from this _ f le_rfl
  intro m
  induction m with
  | zero =>
    intro f hf
    refine (complexity_eq_zero_iff.2 fun x y => ?_).trans_le (Nat.zero_le _)
    -- With `C₀(f) = 0`, every input of value `0` is certified by no variable.
    by_contra hxy
    wlog hx : f x = false generalizing x y
    · exact this y x (Ne.symm hxy) (by simpa [hx] using hxy)
    obtain ⟨S, hS, hcard⟩ := exists_isCertificate_card_eq f x
    have : S = ∅ := card_eq_zero.1 (hcard.trans (Nat.le_zero.1
      ((certificateComplexityAt_le_certificateComplexityFor hx).trans hf)))
    subst this
    exact hxy (hS y fun _ h => absurd h (notMem_empty _)).symm
  | succ m ih =>
    intro f hf
    by_cases h1 : ∃ x, f x = true
    swap
    · push Not at h1
      exact (complexity_eq_zero_iff.2 fun x y => by simp [h1 x, h1 y]).trans_le (Nat.zero_le _)
    obtain ⟨x, hx⟩ := h1
    obtain ⟨S, hS, hScard⟩ := exists_isCertificate_card_eq f x
    -- Query the certificate of `x`, then continue with a tree for the restricted function.
    refine (complexity_le_card_add S (d := m * certificateComplexityFor f true) fun a =>
      (ih _ (certificateComplexityFor_restrict_lt hS a (by simp [hx]) hf)).trans
        (Nat.mul_le_mul_left m (certificateComplexityFor_restrict_le S a true))).trans ?_
    rw [hScard, Nat.succ_mul, add_comm]
    exact Nat.add_le_add_left (certificateComplexityAt_le_certificateComplexityFor hx) _

/-- Decision tree complexity is at most the square of certificate complexity. -/
theorem complexity_le_certificateComplexity_sq (f : BooleanFunction n) :
    complexity f ≤ certificateComplexity f ^ 2 :=
  (complexity_le_certificateComplexityFor_mul f).trans (by
    rw [sq]
    exact Nat.mul_le_mul (certificateComplexityFor_le_certificateComplexity f false)
      (certificateComplexityFor_le_certificateComplexity f true))

end DecisionTree

end Cslib
