/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TQBF
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Logics.Propositional.QBF.Arithmetization
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

/-!
# The interactive proof for quantified Boolean formulas

The protocol of Shamir with Shen's linearization [Shamir][Shamir1992], [Shen][Shen1992],
[Arora and Barak, Section 8.3][AroraBarak09], built on the sum-check protocol of Lund, Fortnow,
Karloff and Nisan [LundFortnowKarloffNisan1992], for an arithmetic formula `e` with operators
`∃`, `∀` and linearization (`Cslib.Logic.PL.ArithQBF`) over a commutative ring `F`. The verifier
(`Cslib.Complexity.QBFProtocol.verify`) checks a claim `e.eval r = c` about the value of `e` at a
point `r`, by recursion on `e`:

* at a variable or a constant it checks the claim directly, and a negation `not e` reduces the
  claim to `e.eval r = 1 - c`;
* at a binary connective it asks the prover for the values `c₁` and `c₂` of the two arguments,
  checks that they combine to `c`, and checks the claims `c₁` and `c₂` in turn;
* at an operator binding `x` it asks the prover for the polynomial `s` that the restriction of the
  body to `x` (`Cslib.Logic.PL.ArithQBF.restrict`) should be, as a list of coefficients of which
  it keeps the first `degBound x + 1`; it checks that the values `s 0` and `s 1` combine to `c`,
  draws `z` from the sampler, and checks the claim that the body has value `s z` at `r` with `x`
  set to `z`.

The verifier is a program with typed calls to the prover (`Cslib.ProbOracleComp`): each query
sends the current subformula and point, each reply is a list of ring elements, and the field
elements are drawn from an arbitrary closed probabilistic program `sampler`. A prover is any
stateful probabilistic strategy `respond` answering the queries, with an arbitrary type of states,
and `Cslib.ProbOracleComp.acceptProbWith` is the probability that the verifier accepts against it;
`Cslib.Complexity.acceptProb` is the case of word queries and replies.

**Completeness.** The honest prover (`Cslib.Complexity.QBFProtocol.honest`) answers with the true
values and restrictions, and is accepted with probability `1` on every true claim
(`Cslib.Complexity.QBFProtocol.acceptProb_honest_verify`).

**Soundness.** If the sampler gives every element probability at most `ε` and `F` is an integral
domain, every prover is accepted on a false claim with probability at most
`e.roundDegree * ε` (`Cslib.Complexity.QBFProtocol.acceptProb_verify_le`): at an operator, a
wrong polynomial agrees with the true restriction, both of degree at most `degBound x`, on at
most `degBound x` points, and otherwise the claim passed on is false again. For the uniform
distribution on a finite field this is `e.roundDegree / |F|`.

For a closed formula `φ`, the arithmetization `φ.arithmetize xs` has value `1` at the origin when
`φ` is true and `0` when it is false (`Cslib.Logic.PL.QBF.eval_arithmetize_zero`), and its round
degrees sum to at most `(2 * |xs| + 1) * size φ ^ 2` when `xs` contains the variables of `φ`. The
claim that it has value `1` at the origin is therefore accepted with probability `1` from a true
formula, and with probability at most `3 * size φ ^ 3 / |F|` from a false one
(`Cslib.Complexity.QBFProtocol.acceptProb_honest_of_mem_TQBF`,
`Cslib.Complexity.QBFProtocol.acceptProb_le_of_notMem_TQBF`). The efficient machine in the
model of `Cslib.Complexity.IP` realizes a variant of this verifier,
`Cslib.Complexity.QBFProtocol.verifyAt`: it reads `D + 1` coefficients in every round, sends the
remaining tokens of the formula with every query, and works over a prime field of polynomial size
with elements drawn from fair coins, each with probability at most `2 / p`
(`Cslib.Complexity.QBFProtocol.isOraclePPTOn_verifier`, `Cslib.Complexity.TQBF_mem_IP`).

## Main definitions

* `Cslib.Complexity.QBFProtocol.verify`: the verifier.
* `Cslib.Complexity.QBFProtocol.honest`: the honest prover.

## Main results

* `Cslib.Complexity.QBFProtocol.acceptProb_honest_verify`: perfect completeness.
* `Cslib.Complexity.QBFProtocol.acceptProb_verify_le`,
  `Cslib.Complexity.QBFProtocol.acceptProb_verify_uniform_le`: soundness against every prover.
* `Cslib.Complexity.QBFProtocol.acceptProb_honest_arithmetize`,
  `Cslib.Complexity.QBFProtocol.acceptProb_arithmetize_le`: the protocol for closed quantified
  Boolean formulas.
* `Cslib.Complexity.QBFProtocol.acceptProb_honest_of_mem_TQBF`,
  `Cslib.Complexity.QBFProtocol.acceptProb_le_of_notMem_TQBF`: the protocol for `TQBF` over a
  finite field.

## References

* [C. Lund, L. Fortnow, H. Karloff, N. Nisan, *Algebraic methods for interactive proof
  systems*][LundFortnowKarloffNisan1992]
* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Polynomial
open Cslib.ProbOracleComp (runWith acceptProbWith)
open scoped ENNReal

variable {V F : Type}

/-! ### Queries -/

/-- A query of the verifier: the subformula whose claim it is checking, and the current point. -/
abbrev Query (V F : Type) := ArithQBF V × (V → F)

/-- Every reply of the prover is a list of ring elements. -/
abbrev Spec (V F : Type) : Query V F → Type := fun _ => List F


/-! ### The verifier -/

variable [DecidableEq V] [CommRing F] [DecidableEq F] (sampler : ProbComp F)

/-- **The verifier** checking the claim that `e` has value `c` at `r`, drawing ring elements from
`sampler`. At a binary connective the reply `[c₁, c₂, …]` gives the claimed values of the
arguments, and at an operator binding `x` the first `degBound x + 1` elements of the reply are the
coefficients of the claimed restriction of the body to `x`; missing entries count as `0`. -/
def verify : ArithQBF V → (V → F) → F → ProbOracleComp (Spec V F) Bool
  | .var v, r, c => pure (decide (r v = c))
  | .top, _, c => pure (decide (c = 1))
  | .bot, _, c => pure (decide (c = 0))
  | .not e, r, c => verify e r (1 - c)
  | .bin o e₁ e₂, r, c => do
    let l ← ProbOracleComp.query (spec := Spec V F) (.bin o e₁ e₂, r)
    if o.apply (l.getD 0 0) (l.getD 1 0) = c then
      let b ← verify e₁ r (l.getD 0 0)
      if b then verify e₂ r (l.getD 1 0) else pure false
    else pure false
  | .op o v e, r, c => do
    let l ← ProbOracleComp.query (spec := Spec V F) (.op o v e, r)
    let s := l.take (e.degBound v + 1)
    if o.apply (r v) (evalCoeffList 0 s) (evalCoeffList 1 s) = c then
      let z ← ProbOracleComp.sample sampler
      verify e (Function.update r v z) (evalCoeffList z s)
    else pure false

/-! ### Completeness -/

/-- The reply of the honest prover: the values of the two arguments of a binary connective, and
the `degBound x + 1` coefficients of the restriction of the body of an operator binding `x`. -/
noncomputable def honestReply : Query V F → List F
  | (.bin _ e₁ e₂, r) => [e₁.eval r, e₂.eval r]
  | (.op _ v e, r) => coeffsBelow (e.restrict r v) (e.degBound v + 1)
  | _ => []

/-- The honest prover, which keeps no state. -/
noncomputable def honest : Query V F → StateT Unit PMF (List F) :=
  fun q s => PMF.pure (honestReply q, s)

/-- Against the honest prover, the verifier accepts every true claim with certainty. -/
private theorem run_honest_verify (e : ArithQBF V) (r : V → F) (s : Unit) :
    runWith honest (verify sampler e r (e.eval r)) s = PMF.pure (true, s) := by
  induction e generalizing r with
  | var v => simp only [verify, ArithQBF.eval_var, decide_true, ProbOracleComp.runWith_pure]
  | top => simp only [verify, ArithQBF.eval_top, decide_true, ProbOracleComp.runWith_pure]
  | bot => simp only [verify, ArithQBF.eval_bot, decide_true, ProbOracleComp.runWith_pure]
  | not e ih => rw [verify, ArithQBF.eval_not, sub_sub_cancel, ih]
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [verify, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    simp only [honest, honestReply, PMF.pure_bind, List.getD_cons_zero, List.getD_cons_succ,
      ArithQBF.eval_bin, ↓reduceIte]
    rw [ProbOracleComp.runWith_bind, ih₁, PMF.pure_bind]
    exact ih₂ r
  | op o v e ih =>
    rw [verify, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    have hlist : (coeffsBelow (e.restrict r v) (e.degBound v + 1)).take (e.degBound v + 1) =
        coeffsBelow (e.restrict r v) (e.degBound v + 1) :=
      List.take_of_length_le (by rw [length_coeffsBelow])
    have hval (z : F) : evalCoeffList z (coeffsBelow (e.restrict r v) (e.degBound v + 1)) =
        e.eval (Function.update r v z) := by
      rw [← eval_ofCoeffList,
        ofCoeffList_coeffsBelow (Nat.lt_succ_of_le (e.natDegree_restrict_le r v)),
        ArithQBF.eval_restrict]
    simp only [honest, honestReply, PMF.pure_bind, hlist, hval, ArithQBF.eval_op, ↓reduceIte]
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, PMF.bind_map]
    simp only [Function.comp_def, ih]
    exact PMF.bind_const _ _

/-- **Perfect completeness**: the honest prover is accepted on every true claim with
probability `1`. -/
theorem acceptProb_honest_verify (e : ArithQBF V) (r : V → F) :
    acceptProbWith honest (verify sampler e r (e.eval r)) () = 1 := by
  rw [acceptProbWith, run_honest_verify, PMF.pure_map, PMF.pure_apply]
  exact ite_eq_left rfl

/-! ### Soundness -/

/-- **Soundness**: over an integral domain, if the sampler gives every element probability at most
`ε`, every prover is accepted on a false claim with probability at most `e.roundDegree * ε`. -/
theorem acceptProb_verify_le [IsDomain F] {ε : ℝ≥0∞}
    (hsampler : ∀ z, ProbComp.eval sampler z ≤ ε) {S : Type}
    (respond : Query V F → StateT S PMF (List F)) (e : ArithQBF V) {r : V → F} {c : F}
    (hc : e.eval r ≠ c) (s : S) :
    acceptProbWith respond (verify sampler e r c) s ≤ e.roundDegree * ε := by
  induction e generalizing r c s with
  | var v =>
    rw [verify, decide_eq_false (show r v ≠ c from hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | top =>
    rw [verify, decide_eq_false (show c ≠ 1 from Ne.symm hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | bot =>
    rw [verify, decide_eq_false (show c ≠ 0 from Ne.symm hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | not e ih =>
    rw [verify, ArithQBF.roundDegree]
    exact ih (fun h => hc (by rw [ArithQBF.eval_not, h, sub_sub_cancel])) s
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [verify, ProbOracleComp.acceptProbWith_query_bind]
    refine Probability.PMF.tsum_mul_le_of_forall_le _ fun x => ?_
    split_ifs with hcheck
    · by_cases h₁ : e₁.eval r = x.1.getD 0 0
      · have h₂ : e₂.eval r ≠ x.1.getD 1 0 := fun h₂ =>
          hc (by rw [ArithQBF.eval_bin, h₁, h₂, hcheck])
        rw [ProbOracleComp.acceptProbWith_bind]
        refine (Probability.PMF.tsum_mul_le_of_forall_le (B := (e₂.roundDegree : ℝ≥0∞) * ε) _
          fun y => ?_).trans ?_
        · cases y.1
          · simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.acceptProbWith_pure]
            exact zero_le
          · simp only [↓reduceIte]
            exact ih₂ h₂ _
        · rw [ArithQBF.roundDegree, Nat.cast_add, add_mul]
          exact le_add_self
      · refine (ProbOracleComp.acceptProbWith_bind_ite_le respond _ _ _).trans ((ih₁ h₁ _).trans ?_)
        rw [ArithQBF.roundDegree, Nat.cast_add, add_mul]
        exact le_self_add
    · rw [ProbOracleComp.acceptProbWith_pure]
      exact zero_le
  | op o v e ih =>
    rw [verify, ProbOracleComp.acceptProbWith_query_bind]
    refine Probability.PMF.tsum_mul_le_of_forall_le _ fun x => ?_
    dsimp only
    split_ifs with hcheck
    · rw [ProbOracleComp.acceptProbWith_sample_bind]
      set g := e.restrict r v
      set p := ofCoeffList (x.1.take (e.degBound v + 1))
      have hp (z : F) : evalCoeffList z (x.1.take (e.degBound v + 1)) = p.eval z :=
        (eval_ofCoeffList z _).symm
      have hg (z : F) : g.eval z = e.eval (Function.update r v z) := e.eval_restrict r v z
      have hne : p - g ≠ 0 := by grind [sub_eq_zero, ArithQBF.eval_op]
      have hdeg : (p - g).natDegree ≤ e.degBound v :=
        (natDegree_sub_le _ _).trans (max_le ((natDegree_ofCoeffList_le _).trans (by
          rw [List.length_take]; omega)) (e.natDegree_restrict_le r v))
      classical
      have hcard : ((p - g).roots.toFinset.card : ℝ≥0∞) ≤ e.degBound v := by
        exact_mod_cast (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdeg)
      refine (Probability.PMF.tsum_mul_le_card_mul_add _ hsampler (p - g).roots.toFinset
        (B := e.roundDegree * ε) fun z => ?_).trans ?_
      · by_cases hz : p.eval z = g.eval z
        · have : z ∈ (p - g).roots.toFinset := by
            rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, hz, sub_self]
          simp only [this, ↓reduceIte]
          exact (ProbOracleComp.acceptProbWith_le_one _ _ _).trans le_self_add
        · rw [hp]
          refine (ih (fun h => hz ?_) _).trans le_add_self
          rw [hg, h]
      · rw [ArithQBF.roundDegree, Nat.cast_add, add_mul]
        gcongr
    · rw [ProbOracleComp.acceptProbWith_pure]
      exact zero_le

/-- **Soundness for uniform samples**: with ring elements drawn uniformly from a finite integral
domain, every prover is accepted on a false claim with probability at most
`e.roundDegree / |F|`. -/
theorem acceptProb_verify_uniform_le [IsDomain F] [Fintype F] {S : Type}
    (respond : Query V F → StateT S PMF (List F)) (e : ArithQBF V) {r : V → F} {c : F}
    (hc : e.eval r ≠ c) (s : S) :
    acceptProbWith respond (verify (ProbComp.uniform F) e r c) s ≤
      e.roundDegree / Fintype.card F := by
  rw [div_eq_mul_inv]
  exact acceptProb_verify_le _
    (fun z => by rw [ProbComp.eval_uniform, Probability.PMF.uniformOfFintype_apply]) respond e hc s

/-! ### Quantified Boolean formulas -/

/-- **Completeness for quantified Boolean formulas**: on a true closed formula, the honest prover
is accepted with probability `1` on the claim that the arithmetization has value `1` at the
origin. -/
theorem acceptProb_honest_arithmetize (xs : List V) {φ : QBF V} (hφ : φ.Closed)
    (htrue : φ.eval (fun _ => false) = true) :
    acceptProbWith honest (verify sampler (φ.arithmetize xs) 0 1) () = 1 := by
  have h := QBF.eval_arithmetize_zero (R := F) xs hφ (fun _ => false)
  simp only [htrue, ↓reduceIte] at h
  have hacc := acceptProb_honest_verify sampler (φ.arithmetize xs) 0
  rwa [h] at hacc

/-- **Soundness for quantified Boolean formulas**: on a false closed formula whose variables are
all in `xs`, every prover is accepted on the claim that the arithmetization has value `1` at the
origin with probability at most `(2 * |xs| + 1) * size φ ^ 2 * ε`, if the sampler gives every
element probability at most `ε`. -/
theorem acceptProb_arithmetize_le [IsDomain F] {ε : ℝ≥0∞}
    (hsampler : ∀ z, ProbComp.eval sampler z ≤ ε) {xs : List V} {φ : QBF V} (hφ : φ.Closed)
    (hxs : ∀ v ∈ φ.vars, v ∈ xs) (hfalse : φ.eval (fun _ => false) = false) {S : Type}
    (respond : Query V F → StateT S PMF (List F)) (s : S) :
    acceptProbWith respond (verify sampler (φ.arithmetize xs) 0 1) s ≤
      ((2 * xs.length + 1) * φ.size ^ 2 : ℕ) * ε := by
  have h := QBF.eval_arithmetize_zero (R := F) xs hφ (fun _ => false)
  simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at h
  refine (acceptProb_verify_le sampler hsampler respond _ (by rw [h]; exact zero_ne_one) s).trans ?_
  gcongr
  exact QBF.roundDegree_arithmetize_le hxs

/-- **Completeness for `TQBF`**: on a true closed formula, the honest prover is accepted with
probability `1`. -/
theorem acceptProb_honest_of_mem_TQBF {φ : QBF ℕ} (hφ : φ ∈ TQBF) :
    acceptProbWith honest (verify sampler (φ.arithmetize φ.vars) 0 1) () = 1 :=
  acceptProb_honest_arithmetize sampler _ hφ.1 hφ.2

/-- **Soundness for `TQBF`**: on a false closed formula `φ`, with field elements drawn uniformly
from a finite field `F`, every prover is accepted with probability at most
`3 * size φ ^ 3 / |F|`. -/
theorem acceptProb_le_of_notMem_TQBF [IsDomain F] [Fintype F] {φ : QBF ℕ} (hφ : φ.Closed)
    (hφ' : φ ∉ TQBF) {S : Type} (respond : Query ℕ F → StateT S PMF (List F)) (s : S) :
    acceptProbWith respond (verify (ProbComp.uniform F) (φ.arithmetize φ.vars) 0 1) s ≤
      ((3 * φ.size ^ 3 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  have hfalse : φ.eval (fun _ => false) = false := Bool.eq_false_iff.2 fun h => hφ' ⟨hφ, h⟩
  have h := QBF.eval_arithmetize_zero (R := F) φ.vars hφ (fun _ => false)
  simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at h
  refine (acceptProb_verify_uniform_le respond _ (by rw [h]; exact zero_ne_one) s).trans ?_
  gcongr
  have hrd := QBF.roundDegree_arithmetize_le (xs := φ.vars) (φ := φ) fun _ hv => hv
  have hlen := QBF.length_vars_le_size φ
  have hs := QBF.one_le_size φ
  refine hrd.trans ?_
  calc (2 * φ.vars.length + 1) * φ.size ^ 2 ≤ (3 * φ.size) * φ.size ^ 2 :=
        Nat.mul_le_mul_right _ (by omega)
    _ = 3 * φ.size ^ 3 := by ring

end Cslib.Complexity.QBFProtocol
