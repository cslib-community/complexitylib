/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Sequential
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.PolynomialAgreement
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The sumcheck protocol with a final evaluation check

The index is a polynomial `P` in `n` variables over a finite field `F` with every individual
degree at most `d`. A claim `(r, c)` at round `i` consists of the challenges `r : Fin i → F` of
the earlier rounds and a value `c`. It states that the sum of `P` over the Boolean hypercube in
the coordinates `i, …, n - 1`, with the coordinates below `i` fixed to `r`, is `c`
(`Sumcheck.rel P i`). At round `0` this is the sumcheck claim `∑_{b ∈ {0,1}ⁿ} P b = c`, and at
round `n` it is the evaluation claim `P r = c`.

This is the protocol of Lund, Fortnow, Karloff and Nisan [LundFortnowKarloffNisan1992] as a
composition of one-round reductions, with each challenge uniform on the field. Each round needs
`i < n`: past the last variable the honest round polynomial is constant, and the round is neither
complete nor round-by-round sound. The TQBF protocol in
`CslibFrontier.Computability.Complexity.Classes.IP.TQBF.Protocol` is a separate, unchanged
development.

## Main definitions

* `Sumcheck.Claim`: for a field `F` and round index `i`, a point of `F^i` and a claimed sum.
* `Sumcheck.point`, `Sumcheck.partialSum`, `Sumcheck.rel`: hypercube point extension, partial sum
  of a multivariate polynomial `P` over the remaining Boolean coordinates, and the round-`i`
  relation.
* `Sumcheck.roundPoly`, `Sumcheck.roundSpec`, `Sumcheck.accepts`, `Sumcheck.round`: honest round
  polynomial, one-round protocol specification, verifier polynomial check, and one-round reduction
  from `rel P i` to `rel P (i + 1)`. Each round sends one univariate polynomial, samples one
  uniform field challenge and appends it to the point.
* `Sumcheck.finalCheck`: final reduction for an `n`-variate polynomial `P` from `rel P n` to
  acceptance by evaluating `P` without interaction.
* `Sumcheck.proof`: rounds zero through `n - 1`, by `Reduction.iterate`, followed by `finalCheck`.

## Main results

* `Sumcheck.round_complete`, `Sumcheck.round_rbrSound`: each round is perfectly complete and
  round-by-round sound with error `d / |F|`.
* `Sumcheck.finalCheck_complete`, `Sumcheck.finalCheck_rbrSound`: the final check is perfectly
  complete and round-by-round sound without error.
* `Sumcheck.proof_complete`, `Sumcheck.proof_sound`: the end-to-end theorems, corollaries of the
  component theorems through the composition theorems. The soundness error `n * (d / |F|)` is the
  sum of the per-round errors, and no step of the composed protocol is reasoned about directly.

## References

* [C. Lund, L. Fortnow, H. Karloff, N. Nisan, *Algebraic methods for interactive proof
  systems*][LundFortnowKarloffNisan1992]
-/

@[expose] public section

namespace Cslib.Interactive.Sumcheck

open scoped ENNReal
open Spec

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (d : ℕ)
  (P : MvPolynomial (Fin n) F)

/-- A claim of round `i`: the challenges of the rounds before `i` and the claimed value. -/
abbrev Claim (F : Type) (i : ℕ) : Type := (Fin i → F) × F

/-- The point of `F^n` equal to `r` on the first `i` coordinates and to the Boolean point `b` on
the others. -/
def point {i : ℕ} (r : Fin i → F) (b : Fin (n - i) → Bool) : Fin n → F :=
  fun j => if h : j.val < i then r ⟨j.val, h⟩ else if b ⟨j.val - i, by omega⟩ then 1 else 0

/-- The sum of `P` over the Boolean hypercube in the coordinates from `i` on, with the coordinates
below `i` fixed to `r`. -/
noncomputable def partialSum {i : ℕ} (r : Fin i → F) : F :=
  ∑ b : Fin (n - i) → Bool, MvPolynomial.eval (point r b) P

/-- The relation of round `i`: the claimed value is the partial sum. There is no witness. -/
def rel (i : ℕ) : Claim F i → Unit → Prop := fun c _ => partialSum P c.1 = c.2

/-- The honest message of round `i`: the partial sum as a polynomial in coordinate `i`. -/
noncomputable def roundPoly {i : ℕ} (r : Fin i → F) : Polynomial F :=
  ∑ b : Fin (n - (i + 1)) → Bool,
    MvPolynomial.aeval (fun j => if h : j.val < i then Polynomial.C (r ⟨j.val, h⟩)
      else if h' : j.val = i then Polynomial.X
      else Polynomial.C (if b ⟨j.val - (i + 1), by omega⟩ then 1 else 0)) P

/-- One round: the prover sends a polynomial, read in full; the verifier sends a field element. -/
abbrev roundSpec (F : Type) [Semiring F] : Spec :=
  [.prover (Polynomial F) (OracleInterface.full _), .verifier F]

/-- The verifier's test of a round polynomial `g` against the claimed value `c`. -/
abbrev accepts (c : F) (g : Polynomial F) : Prop := g.natDegree ≤ d ∧ g.eval 0 + g.eval 1 = c

/-- Round `i` of sumcheck: on the claim `(r, c)` and the challenge `z`, the new claim is
`(Fin.snoc r z, g.eval z)` for the prover's polynomial `g`. -/
noncomputable def round (i : ℕ) :
    Reduction OracleSpec.empty OracleSpec.empty (roundSpec F) (Claim F i) Unit (Claim F (i + 1))
      Unit where
  prover x _ :=
    let g := roundPoly P x.1
    pure (show ProbOracleComp OracleSpec.empty
        (Polynomial F × (F → ProbOracleComp OracleSpec.empty _)) from
      pure (g, fun z => pure ((Fin.snoc x.1 z, g.eval z), ())))
  verifier :=
    { samplers := (ProbComp.uniform F, ())
      decide := fun x c => do
        let g ← OracleComp.query (spec := OracleSpec.empty ⊕ₒ msgSpec (roundSpec F))
          (.inr (.inl ()))
        return if accepts d x.2 g then some (Fin.snoc x.1 c.1, g.eval c.1) else none }

/-- The final check: evaluate `P` at the claimed point, without interaction. -/
noncomputable def finalCheck :
    Reduction OracleSpec.empty OracleSpec.empty [] (Claim F n) Unit Unit Unit where
  prover _ _ := pure ((), ())
  verifier :=
    { samplers := ()
      decide := fun x _ => pure (if MvPolynomial.eval x.1 P = x.2 then some () else none) }

/-- **Sumcheck followed by the final check**: a proof system for the claim `∑_{b ∈ {0,1}ⁿ} P b = c`
(`rel P 0`). -/
noncomputable def proof :
    Reduction OracleSpec.empty OracleSpec.empty (iterSpec (fun _ => roundSpec F) n ++ [])
      (Claim F 0) Unit Unit Unit :=
  (Reduction.iterate (s := fun _ => roundSpec F) (S := Claim F) (W := fun _ => Unit)
    (round d P) n).append (finalCheck P)

/-! ### The round polynomial -/

omit [Fintype F] [DecidableEq F] in
/-- Substituting the variable at coordinate `k` and constants elsewhere gives a polynomial of
degree at most the degree of `P` in `k`. -/
private theorem natDegree_aeval_le (k : Fin n) (φ : Fin n → Polynomial F)
    (hφ : ∀ j, j ≠ k → (φ j).natDegree = 0) (hk : (φ k).natDegree ≤ 1) :
    (MvPolynomial.aeval φ P).natDegree ≤ P.degreeOf k := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.monomial_le_degreeOf k hm)
  calc ∑ j ∈ m.support, ((φ j) ^ m j).natDegree
      ≤ ∑ j ∈ m.support, if k = j then m j else 0 := by
        refine Finset.sum_le_sum fun j _ => Polynomial.natDegree_pow_le.trans ?_
        by_cases hj : k = j
        · subst hj
          simpa only [ite_true, mul_one] using Nat.mul_le_mul_left (m k) hk
        · rw [hφ j (Ne.symm hj), mul_zero]
          exact Nat.zero_le _
    _ ≤ m k := by
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial has degree at most `d`. -/
private theorem natDegree_roundPoly_le (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n)
    (r : Fin i → F) : (roundPoly P r).natDegree ≤ d := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  refine (natDegree_aeval_le P ⟨i, hi⟩ _ (fun j hj => ?_) ?_).trans (hP _)
  · have : j.val ≠ i := fun h => hj (Fin.ext h)
    split_ifs <;> exact Polynomial.natDegree_C _
  · simp

omit [Field F] [Fintype F] [DecidableEq F] in
/-- The coordinate `j < i + 1` of `Fin.snoc r z`. -/
private theorem snoc_mk {i : ℕ} (r : Fin i → F) (z : F) {j : ℕ} (hj : j < i + 1) :
    (Fin.snoc r z : Fin (i + 1) → F) ⟨j, hj⟩ = if h : j < i then r ⟨j, h⟩ else z :=
  rfl

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial at `z` is the partial sum of the next round at the point extended
by `z`. -/
private theorem eval_roundPoly_eq {i : ℕ} (r : Fin i → F) (z : F) :
    (roundPoly P r).eval z = partialSum P (Fin.snoc r z) := by
  rw [roundPoly, Polynomial.eval_finsetSum, partialSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply,
    MvPolynomial.aeval_eq_eval]
  congr 2
  funext j
  simp only [point, snoc_mk]
  split_ifs <;> first | omega | simp

omit [Fintype F] [DecidableEq F] in
/-- Split a Boolean point of length `m + 1` into its first coordinate and the others. -/
private theorem sum_bool_succ {k m : ℕ} (h : k = m + 1) (f : (Fin k → Bool) → F) :
    ∑ b, f b = ∑ c : Bool, ∑ b' : Fin m → Bool,
      f (fun j => if h0 : j.val = 0 then c else b' ⟨j.val - 1, by omega⟩) := by
  subst h
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun c => Fintype.sum_congr _ _ fun b' => congrArg f ?_
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

omit [Fintype F] [DecidableEq F] in
/-- Fixing coordinate `i` to the Boolean value `c` is reading `c` as the first of the Boolean
coordinates of round `i`. -/
private theorem point_snoc {i : ℕ} (r : Fin i → F) (c : Bool) (b : Fin (n - (i + 1)) → Bool) :
    point (Fin.snoc r (if c then (1 : F) else 0)) b =
      point r (fun j => if h0 : j.val = 0 then c else b ⟨j.val - 1, by omega⟩) := by
  funext j
  simp only [point, snoc_mk]
  split_ifs <;> first | omega | simp_all [Nat.sub_sub]

omit [Fintype F] [DecidableEq F] in
/-- The verifier's test passes on the honest round polynomial: its values at `0` and `1` sum to
the partial sum. -/
private theorem roundPoly_eval_zero_add_one {i : ℕ} (hi : i < n) (r : Fin i → F) :
    (roundPoly P r).eval 0 + (roundPoly P r).eval 1 = partialSum P r := by
  rw [eval_roundPoly_eq, eval_roundPoly_eq, add_comm]
  conv_rhs => rw [partialSum, sum_bool_succ (show n - i = n - (i + 1) + 1 by omega),
    Fintype.sum_bool]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => congrArg (MvPolynomial.eval · P) (point_snoc r true b)
  · exact Finset.sum_congr rfl fun b _ => congrArg (MvPolynomial.eval · P) (point_snoc r false b)

omit [Fintype F] [DecidableEq F] in
/-- At round `n` all coordinates are fixed: the partial sum is the evaluation. -/
theorem partialSum_self (r : Fin n → F) : partialSum P r = MvPolynomial.eval r P := by
  rw [partialSum, Finset.sum_eq_single (fun _ => false)]
  · exact congrArg (MvPolynomial.eval · P) (funext fun j => dite_eq_left j.isLt)
  · exact fun b _ hb => absurd (funext fun j => absurd j.isLt (by omega)) hb
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The verifier of round `i` outputs the claim at the challenge if it accepts the message. -/
private theorem round_outputOn (i : ℕ) (x : Claim F i) (τ : Transcript (roundSpec F)) :
    (round d P i).verifier.outputOn x τ =
      if accepts d x.2 τ.1 then some (Fin.snoc x.1 τ.2.1, τ.1.eval τ.2.1) else none :=
  rfl

/-! ### Component theorems (milestone 2) -/

/-- Each round is perfectly complete. -/
theorem round_complete (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n) :
    (round d P i).Complete World.plain (rel P i) (rel P (i + 1)) 0 := by
  intro x w hxw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [round, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample, PMF.pure_bind,
    PMF.bind_bind]
  have hacc : accepts d x.2 (roundPoly P x.1) :=
    ⟨natDegree_roundPoly_le d P hP hi x.1, (roundPoly_eval_zero_add_one P hi x.1).trans hxw⟩
  rw [PMF.toOuterMeasure_bind_apply]
  refine Probability.PMF.tsum_mul_le_of_forall_le _ fun z => le_of_eq ?_
  refine (PMF.toOuterMeasure_pure_apply _ _).trans (ite_eq_right fun h => h ⟨?_, ?_⟩)
  · exact (round_outputOn d P i x _).trans (ite_eq_left hacc)
  · exact (eval_roundPoly_eq P x.1 z).symm

/-- Each round is round-by-round sound with error `d / |F|` (Schwartz–Zippel for one variable). -/
theorem round_rbrSound (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n) :
    (round d P i).verifier.RbrSound (language (rel P i)) (language (rel P (i + 1)))
      ((d : ℝ≥0∞) / Fintype.card F, ()) := by
  refine ⟨fun x p => match p with
    | none => partialSum P x.1 = x.2
    | some (g, none) => accepts d x.2 g ∧ g = roundPoly P x.1
    | some (g, some (z, _)) => accepts d x.2 g ∧ g.eval z = (roundPoly P x.1).eval z,
    fun x hx h => hx ⟨(), h⟩, fun x => ⟨?_, fun g => ⟨?_, fun z => ?_⟩⟩⟩
  · rintro hS m ⟨hacc, rfl⟩
    exact hS ((roundPoly_eval_zero_add_one P hi x.1).symm.trans hacc.2)
  · intro hS
    change (ProbComp.eval (ProbComp.uniform F)).toOuterMeasure
      {c | accepts d x.2 g ∧ g.eval c = (roundPoly P x.1).eval c} ≤ (d : ℝ≥0∞) / Fintype.card F
    by_cases hacc : accepts d x.2 g
    · rw [ProbComp.eval_uniform]
      exact Probability.PMF.toOuterMeasure_uniformOfFintype_le_of_eval_eq
        (fun h => hS ⟨hacc, h⟩) hacc.1 (natDegree_roundPoly_le d P hP hi x.1) fun _ hc => hc.2
    · simp [hacc]
  · rintro hS ⟨x', ⟨_, hx'⟩, hout⟩
    rw [round_outputOn] at hout
    split_ifs at hout with hacc
    obtain rfl := Option.some.inj hout
    exact hS ⟨hacc, hx'.symm.trans (eval_roundPoly_eq P x.1 z).symm⟩

omit [Fintype F] in
/-- The final check is perfectly complete. -/
theorem finalCheck_complete :
    (finalCheck P).Complete World.plain (rel P n) Accept 0 := by
  intro x w hxw
  rw [rel, partialSum_self] at hxw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [finalCheck, runStrategy, plainLaw_bind, plainLaw_pure, PMF.pure_bind]
  refine le_of_eq ((PMF.toOuterMeasure_pure_apply _ _).trans
    (ite_eq_right fun h => h ⟨?_, trivial⟩))
  exact ite_eq_left hxw

omit [Fintype F] in
/-- The final check is round-by-round sound without error. -/
theorem finalCheck_rbrSound :
    (finalCheck P).verifier.RbrSound (language (rel P n)) Set.univ () := by
  refine ⟨fun x _ => MvPolynomial.eval x.1 P = x.2,
    fun x hx h => hx ⟨(), by rw [rel, partialSum_self]; exact h⟩,
    fun x hS ⟨x', _, hout⟩ => hS ?_⟩
  by_contra h
  simp [Verifier.outputOn, finalCheck, h] at hout

/-! ### End-to-end theorems, by composition -/

/-- **Completeness of sumcheck with the final check.** -/
theorem proof_complete (hP : ∀ j, P.degreeOf j ≤ d) :
    (proof d P).Complete World.plain (rel P 0) Accept 0 := by
  have h := (Reduction.Complete.iterate (rel := rel P) n fun i hi =>
    round_complete d P hP hi).append (finalCheck_complete P)
  simp only [Finset.sum_const_zero, add_zero] at h
  exact h

/-- **Soundness of sumcheck with the final check**: a false claim is accepted with probability at
most `n * (d / |F|)`. -/
theorem proof_sound (hP : ∀ j, P.degreeOf j ≤ d) :
    (proof d P).verifier.Sound (oP := OracleSpec.empty) World.plain (language (rel P 0)) Set.univ
      (n * ((d : ℝ≥0∞) / Fintype.card F)) := by
  have h := ((Verifier.RbrSound.iterate (R := round d P) (L := fun i => language (rel P i)) n
    fun i hi => round_rbrSound d P hP hi).append (finalCheck_rbrSound P)).sound
  simp only [PerChallenge.sum_append, PerChallenge.sum_iterate] at h
  simp only [PerChallenge.sum, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  exact h

end Cslib.Interactive.Sumcheck
