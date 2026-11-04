/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT.AuxClock
public import Complexity.Crypto.Computational.ZeroKnowledge
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Probability.PMF.Bind

/-!
# Clock bridge for auxiliary-input zero knowledge with unbounded auxiliary input

In `AuxiliaryInputZeroKnowledge`, the malicious verifier `Vstar` is a standard `IsOraclePPTOn`
program on `encPair encUnary (encPair enc encBits)`, so its polynomial clock is allowed to depend
on the length of the auxiliary input `z`, and the family `z : ℕ → List Bool` is required to be
polynomially bounded.

When `Vstar` is instead clocked in the primary input `(1^n, a)` (or in the instance `x` alone) via
`IsOraclePPTWithAux`, input-tape prefix locality (`IsOraclePPTWithAux.exists_run_interpret_take`)
shows that `Vstar` reads at most a polynomial prefix `z.take (T_V n a)` of `z` during its run
against any stateful prover `Prover Unit`. Applying `AuxiliaryInputZeroKnowledge` to `Vstar` and
setting `S n a z := S₀ n a (z.take (T_V n a))` yields a primary-input-clocked simulator
(`IsPPTWithAux`) that works for **arbitrary, unbounded** auxiliary inputs `z` against any
distinguisher clocked in the primary input and view (`IsPPTWithAux`) that receives the full
untruncated `z`, both in the security-parameter-indexed family form
(`UnboundedAuxiliaryInputZeroKnowledge`) and in the Goldreich-style instance-indexed (`x`-indexed)
form (`InstanceAuxiliaryInputZeroKnowledge`) where the security parameter is `(enc x).length` and
the simulator is chosen once per `Vstar` before the distinguisher, instance `x`, valid witness `w`,
and unbounded auxiliary input `z`.

Because `AuxiliaryInputZeroKnowledge` quantifies independently over the polynomially bounded
verifier auxiliary input `z_V` and distinguisher auxiliary input `z_A`, the bridge passes the
verifier-sized prefix `z_V n := (z n).take (T_V n (a n))` to `Vstar` and `S₀` (where
`S₀ n (a n) (z_V n) = S n (a n) (z n)` holds definitionally) and the distinguisher-sized prefix
`z_A n := (z n).take (T_A n (a n))` to `adversary`, without requiring any syntactic congruence
condition on `S₀`.

## Main definitions

* `Cslib.Crypto.UnboundedAuxiliaryInputZeroKnowledge`,
  `Cslib.Crypto.ZeroKnowledgeProof.UnboundedAuxiliaryInputZeroKnowledge`: family-indexed
  auxiliary-input zero knowledge against prefix-clocked verifiers (`IsOraclePPTWithAux`) and
  distinguishers (`IsPPTWithAux`) over arbitrary, unbounded auxiliary-input families
  `z : ℕ → List Bool`.
* `Cslib.Crypto.InstanceAuxiliaryInputZeroKnowledge`,
  `Cslib.Crypto.ZeroKnowledgeProof.InstanceAuxiliaryInputZeroKnowledge`: Goldreich-style
  instance-indexed (`x`-indexed) auxiliary-input zero knowledge with unbounded auxiliary input
  `z : List Bool` and quantifier order `∀ Vstar, ∃ S, ∀ adversary, ... ∀ x w z`.

## Main results

* `Cslib.Complexity.Prover.exists_run_take_of_isOraclePPTWithAux`: an `IsOraclePPTWithAux`
  verifier has identical interaction distribution with any stateful `Prover` on `(a, z)` and on
  `(a, z.take m)` whenever `m ≥ c * ((input a).length + 1) ^ d`.
* `Cslib.Crypto.AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge`:
  `AuxiliaryInputZeroKnowledge` implies `UnboundedAuxiliaryInputZeroKnowledge` (with the
  `ZeroKnowledgeProof` projection of the same name).
* `Cslib.Crypto.UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge`,
  `Cslib.Crypto.AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge`:
  `UnboundedAuxiliaryInputZeroKnowledge` and `AuxiliaryInputZeroKnowledge` imply
  `InstanceAuxiliaryInputZeroKnowledge` (with the `ZeroKnowledgeProof` projections).

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* O. Goldreich, *Foundations of Cryptography*, early Chapter 4 draft (`part4N.pdf`), §4.3.3,
  Definition 4.3.8, printed pp. 151–153; and [O. Goldreich, *Foundations of Cryptography:
  Volume 1, Basic Tools*][Goldreich2001], Chapter 4.
-/

@[expose] public section

namespace Cslib.Complexity.Prover

open Cslib.Probability Turing.MultiTapeTM

variable {Operation α β : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {output : β ↪ List Bool}

/-- **Prover interaction prefix truncation for `IsOraclePPTWithAux`.** An oracle verifier clocked
in the primary input `a` has the exact same joint distribution of `(result, finalProverState)`
against every stateful prover `P : Prover Operation` on `(a, z.take m)` as on `(a, z)` whenever
`m ≥ c * ((input a).length + 1) ^ d`. -/
theorem exists_run_take_of_isOraclePPTWithAux
    {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program) :
    ∃ c d : ℕ, ∀ (a : α) (z : List Bool) {m : ℕ},
      c * ((input a).length + 1) ^ d ≤ m →
      ∀ (P : Prover Operation) (s : P.State),
        P.run (program a (z.take m)) s = P.run (program a z) s := by
  obtain ⟨c, d, htake⟩ := h.exists_run_interpret_take
  exact ⟨c, d, fun a z {m} hm P s => htake a z hm P.State P.respond s⟩

end Cslib.Complexity.Prover

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {Operation α β γ : Type} [DecidableEq Operation]
  {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool} {output : γ ↪ List Bool}

/-- Reassociate `IsOraclePPTWithAux (encPair enc₁ enc₂)` into a standard `IsOraclePPTOn`
certificate on `encPair enc₁ (encPair enc₂ encBits)`. -/
theorem IsOraclePPTWithAux.isOraclePPTOn_triple
    {program : α → β → List Bool → WordOracleComp Operation γ}
    (h : IsOraclePPTWithAux (encPair enc₁ enc₂) output (fun (a, b) z => program a b z)) :
    IsOraclePPTOn (encPair enc₁ (encPair enc₂ encBits)) output
      (fun ⟨a, b, z⟩ => program a b z) :=
  h.isOraclePPTOn.preprocess'
    (prepare := fun p : α × β × List Bool => ((p.1, p.2.1), p.2.2)) (by fun_prop)

/-- Truncating the auxiliary input of a three-argument `IsPPTOn` program to a polynomial in the
encoded primary pair `encPair enc₁ enc₂ (a, b)` yields an `IsPPTWithAux (encPair enc₁ enc₂)`
certificate. -/
theorem IsPPTOn.isPPTWithAux_take_triple {program : α → β → List Bool → ProbComp γ}
    (h : IsPPTOn (encPair enc₁ (encPair enc₂ encBits)) output
      (fun ⟨a, b, z⟩ => program a b z))
    (c d : ℕ) :
    IsPPTWithAux (encPair enc₁ enc₂) output
      (fun (a, b) z =>
        program a b (z.take (c * ((encPair enc₁ enc₂ (a, b)).length + 1) ^ d))) := by
  have hpair : IsPPTOn (encPair (encPair enc₁ enc₂) encBits) output
      (fun (p, z) => (fun p : α × β => program p.1 p.2) p z) :=
    h.preprocess (prepare := fun p : (α × β) × List Bool => (p.1.1, p.1.2, p.2)) (by fun_prop)
  exact hpair.isPPTWithAux_take (program := fun p : α × β => program p.1 p.2) c d

/-- Truncating the auxiliary input of a three-argument `IsPPTOn` program to a polynomial in the
encoded primary pair `encPair enc₁ enc₂ (a, b)` preserves `IsPPTOn`. -/
theorem IsPPTOn.take_aux_triple {program : α → β → List Bool → ProbComp γ}
    (h : IsPPTOn (encPair enc₁ (encPair enc₂ encBits)) output
      (fun ⟨a, b, z⟩ => program a b z))
    (c d : ℕ) :
    IsPPTOn (encPair enc₁ (encPair enc₂ encBits)) output
      (fun ⟨a, b, z⟩ =>
        program a b (z.take (c * ((encPair enc₁ enc₂ (a, b)).length + 1) ^ d))) :=
  (h.isPPTWithAux_take_triple c d).isPPTOn.preprocess
    (prepare := fun p : α × β × List Bool => ((p.1, p.2.1), p.2.2)) (by fun_prop)

end Cslib.Probability

namespace Cslib.Crypto

open Probability Complexity Turing.MultiTapeTM
open scoped NNReal ENNReal

variable {α : Type} {enc : α ↪ List Bool}

/-- **Unbounded-`z` family auxiliary-input computational zero knowledge.**
For every malicious verifier `Vstar` clocked in the primary input `(1^n, a)`
(`IsOraclePPTWithAux (encPair encUnary enc) encBits`), there exists a uniform strict PPT
witness-free simulator `S` clocked in `(1^n, a)` (`IsPPTWithAux (encPair encUnary enc) encBits`)
together with a polynomial prefix bound `c, d` in `(1^n, a)` such that:
1. `S` depends only on the first `c * ((encPair encUnary enc (n, a)).length + 1) ^ d` bits of `z`.
2. Across all polynomially bounded instance families `a : ℕ → α`, polynomially bounded valid
   witness families `w : ℕ → List Bool`, and **arbitrary, unbounded** auxiliary-input families
   `z : ℕ → List Bool`, every distinguisher clocked in `((1^n, a), view)` (`IsPPTWithAux`)
   receiving the full untruncated `z n` has negligible distinguishing advantage between the real
   interaction view and the simulated view. -/
def UnboundedAuxiliaryInputZeroKnowledge {α : Type} (enc : α ↪ List Bool)
    (prover : ℕ → α → List Bool → Prover Unit)
    (isWitness : α → List Bool → Bool) : Prop :=
  ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
    IsOraclePPTWithAux (encPair encUnary enc) encBits (fun (n, a) z => Vstar n a z) →
    ∃ (S : ℕ → α → List Bool → ProbComp (List Bool)) (c d : ℕ),
      IsPPTWithAux (encPair encUnary enc) encBits (fun (n, a) z => S n a z) ∧
      (∀ n a z {m : ℕ}, c * ((encPair encUnary enc (n, a)).length + 1) ^ d ≤ m →
        S n a (z.take m) = S n a z) ∧
      ∀ (a : ℕ → α) (w z : ℕ → List Bool),
        PolynomiallyBounded (fun n => (enc (a n)).length) →
        PolynomiallyBounded (fun n => (w n).length) →
        (∀ n, isWitness (a n) (w n) = true) →
        ∀ adversary : ℕ → α → List Bool → List Bool → ProbComp Bool,
          IsPPTWithAux (encPair (encPair encUnary enc) encBits) encBool
            (fun ⟨⟨n, a⟩, view⟩ z => adversary n a z view) →
          Negligible (fun n => Game.advantage
            (distinguishingGame
              (((prover n (a n) (w n)).run (Vstar n (a n) (z n))
                (prover n (a n) (w n)).init).map Prod.fst)
              (adversary n (a n) (z n)))
            (distinguishingGame
              (ProbComp.eval (S n (a n) (z n)))
              (adversary n (a n) (z n))))

/-- Under `UnboundedAuxiliaryInputZeroKnowledge`, the real and simulated view ensembles are
`ComputationallyIndistinguishable` across all polynomially bounded valid `(a, w)` families and
all arbitrary, unbounded auxiliary-input families `z : ℕ → List Bool`. -/
theorem UnboundedAuxiliaryInputZeroKnowledge.computationallyIndistinguishable
    {prover : ℕ → α → List Bool → Prover Unit} {isWitness : α → List Bool → Bool}
    (h : UnboundedAuxiliaryInputZeroKnowledge enc prover isWitness)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTWithAux (encPair encUnary enc) encBits (fun (n, a) z => Vstar n a z)) :
    ∃ (S : ℕ → α → List Bool → ProbComp (List Bool)) (c d : ℕ),
      IsPPTWithAux (encPair encUnary enc) encBits (fun (n, a) z => S n a z) ∧
      (∀ n a z {m : ℕ}, c * ((encPair encUnary enc (n, a)).length + 1) ^ d ≤ m →
        S n a (z.take m) = S n a z) ∧
      ∀ (a : ℕ → α) (w z : ℕ → List Bool),
        PolynomiallyBounded (fun n => (enc (a n)).length) →
        PolynomiallyBounded (fun n => (w n).length) →
        (∀ n, isWitness (a n) (w n) = true) →
        ComputationallyIndistinguishable
          (fun n => ((prover n (a n) (w n)).run (Vstar n (a n) (z n))
            (prover n (a n) (w n)).init).map Prod.fst)
          (fun n => ProbComp.eval (S n (a n) (z n))) := by
  obtain ⟨S, c, d, hS_ppt, hS_take, hS_zk⟩ := h Vstar hV
  refine ⟨S, c, d, hS_ppt, hS_take, fun a w z ha hw hw_sat adversary hadversary => ?_⟩
  have htest_on : IsPPTOn
      (encPair (encPair (encPair encUnary enc) encBits) encBits) encBool
      (fun p : ((ℕ × α) × List Bool) × List Bool => adversary p.1.1.1 p.1.2) :=
    hadversary.preprocess (by fun_prop) (by fun_prop)
  have htest : IsPPTWithAux (encPair (encPair encUnary enc) encBits) encBool
      (fun ⟨⟨n, _⟩, view⟩ _ => adversary n view) := by
    simpa [List.take_nil] using
      htest_on.isPPTWithAux_take (program := fun p : (ℕ × α) × List Bool =>
        fun _ => adversary p.1.1 p.2) 0 0
  exact hS_zk a w z ha hw hw_sat (fun n _ _ view => adversary n view) htest

/-- **Clock bridge for family auxiliary-input zero knowledge.**
Every system satisfying `AuxiliaryInputZeroKnowledge` also satisfies
`UnboundedAuxiliaryInputZeroKnowledge` against verifiers clocked in `(1^n, a)`. -/
theorem AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge
    {prover : ℕ → α → List Bool → Prover Unit} {isWitness : α → List Bool → Bool}
    (h : AuxiliaryInputZeroKnowledge enc prover isWitness) :
    UnboundedAuxiliaryInputZeroKnowledge enc prover isWitness := by
  intro Vstar hV
  obtain ⟨c, d, hV_take⟩ := Prover.exists_run_take_of_isOraclePPTWithAux hV
  let T_V (n : ℕ) (a : α) : ℕ := c * ((encPair encUnary enc (n, a)).length + 1) ^ d
  obtain ⟨S₀, hS₀_ppt, hS₀_zk⟩ := h Vstar hV.isOraclePPTOn_triple
  let S (n : ℕ) (a : α) (z : List Bool) : ProbComp (List Bool) :=
    S₀ n a (z.take (T_V n a))
  have hS_aux : IsPPTWithAux (encPair encUnary enc) encBits (fun (n, a) z => S n a z) :=
    hS₀_ppt.isPPTWithAux_take_triple c d
  refine ⟨S, c, d, hS_aux, ?_, ?_⟩
  · intro n a z m hm
    simp only [S, T_V, List.take_take, Nat.min_eq_left hm]
  · intro a w z ha hw hw_sat adversary hadversary
    obtain ⟨c_R, d_R, hlen_real⟩ := hV.length_le
    obtain ⟨c_S, d_S, hlen_sim⟩ := hS_aux.length_le
    obtain ⟨c_A, d_A, hadv_take⟩ := hadversary.exists_eval_take
    let L_view (n : ℕ) (x : α) : ℕ :=
      c_R * ((encPair encUnary enc (n, x)).length + 1) ^ d_R +
      c_S * ((encPair encUnary enc (n, x)).length + 1) ^ d_S
    let T_A (n : ℕ) (x : α) : ℕ :=
      c_A * ((2 * (encPair encUnary enc (n, x)).length + 1 + L_view n x) + 1) ^ d_A
    let z_V (n : ℕ) : List Bool := (z n).take (T_V n (a n))
    let z_A (n : ℕ) : List Bool := (z n).take (T_A n (a n))
    have hz_V_bound : PolynomiallyBounded
        (fun n => c * ((2 * n + 1 + (enc (a n)).length) + 1) ^ d) := by
      fun_prop
    have hz_V : PolynomiallyBounded (fun n => (z_V n).length) := by
      refine hz_V_bound.mono_of_le fun n => ?_
      have hlen : (z_V n).length ≤ T_V n (a n) := List.length_take_le _ _
      have hpair : (encPair encUnary enc (n, a n)).length = 2 * n + 1 + (enc (a n)).length := by
        simp
      simpa only [T_V, hpair] using hlen
    have hz_A_bound : PolynomiallyBounded
        (fun n =>
          c_A * ((2 * (2 * n + 1 + (enc (a n)).length) + 1 +
            (c_R * ((2 * n + 1 + (enc (a n)).length) + 1) ^ d_R +
             c_S * ((2 * n + 1 + (enc (a n)).length) + 1) ^ d_S)) + 1) ^ d_A) := by
      fun_prop
    have hz_A : PolynomiallyBounded (fun n => (z_A n).length) := by
      refine hz_A_bound.mono_of_le fun n => ?_
      have hlen : (z_A n).length ≤ T_A n (a n) := List.length_take_le _ _
      have hpair : (encPair encUnary enc (n, a n)).length = 2 * n + 1 + (enc (a n)).length := by
        simp
      simpa only [T_A, L_view, hpair] using hlen
    have hprep1 : ComputableInPolyTime
        (fun p : (ℕ × α × List Bool) × List Bool => (p.1.1, p.1.2.1))
        (encPair (encPair encUnary (encPair enc encBits)) encBits)
        (encPair encUnary enc) := by fun_prop
    have hprep2 : ComputableInPolyTime
        (fun p : (ℕ × α × List Bool) × List Bool => ((p.1.1, p.1.2.1), p.2))
        (encPair (encPair encUnary (encPair enc encBits)) encBits)
        (encPair (encPair encUnary enc) encBits) :=
      hprep1.pair (by fun_prop)
    have hprep : ComputableInPolyTime
        (fun p : (ℕ × α × List Bool) × List Bool => (((p.1.1, p.1.2.1), p.2), p.1.2.2))
        (encPair (encPair encUnary (encPair enc encBits)) encBits)
        (encPair (encPair (encPair encUnary enc) encBits) encBits) :=
      hprep2.pair (by fun_prop)
    have hadv_on : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
        (fun ⟨⟨n, x, z'⟩, view⟩ => adversary n x z' view) :=
      hadversary.isPPTOn.preprocess hprep
    have hneg := hS₀_zk a w z_V z_A ha hw hz_V hz_A hw_sat adversary hadv_on
    have hgame_real (n : ℕ) :
        distinguishingGame
          (((prover n (a n) (w n)).run (Vstar n (a n) (z_V n))
            (prover n (a n) (w n)).init).map Prod.fst)
          (adversary n (a n) (z_A n)) =
        distinguishingGame
          (((prover n (a n) (w n)).run (Vstar n (a n) (z n))
            (prover n (a n) (w n)).init).map Prod.fst)
          (adversary n (a n) (z n)) := by
      have hrun_eq :
          (prover n (a n) (w n)).run (Vstar n (a n) (z_V n)) (prover n (a n) (w n)).init =
          (prover n (a n) (w n)).run (Vstar n (a n) (z n)) (prover n (a n) (w n)).init :=
        hV_take (n, a n) (z n) le_rfl (prover n (a n) (w n)) (prover n (a n) (w n)).init
      simp only [distinguishingGame, hrun_eq, PMF.monad_bind_eq_bind, PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun p hp => ?_
      have hview_le : p.1.length ≤ L_view n (a n) := by
        have h1 : (encBits p.1).length ≤
            c_R * ((encPair encUnary enc (n, a n)).length + 1) ^ d_R :=
          hlen_real (n, a n) (z n) (prover n (a n) (w n)).State (prover n (a n) (w n)).respond
            (prover n (a n) (w n)).init p.2 p.1 hp
        simp only [encBits_apply] at h1
        exact le_trans h1 (Nat.le_add_right _ _)
      have hm : c_A * ((encPair (encPair encUnary enc) encBits ((n, a n), p.1)).length + 1) ^ d_A ≤
          T_A n (a n) := by
        have hpair : (encPair encUnary enc (n, a n)).length = 2 * n + 1 + (enc (a n)).length := by
          simp
        have hlen_pair :
            (encPair (encPair encUnary enc) encBits ((n, a n), p.1)).length =
              2 * (2 * n + 1 + (enc (a n)).length) + 1 + p.1.length := by
          simp
        have hle_base :
            (encPair (encPair encUnary enc) encBits ((n, a n), p.1)).length + 1 ≤
              (2 * (encPair encUnary enc (n, a n)).length + 1 + L_view n (a n)) + 1 := by
          omega
        exact Nat.mul_le_mul_left c_A (Nat.pow_le_pow_left hle_base d_A)
      exact hadv_take ((n, a n), p.1) (z n) hm
    have hgame_sim (n : ℕ) :
        distinguishingGame
          (ProbComp.eval (S₀ n (a n) (z_V n)))
          (adversary n (a n) (z_A n)) =
        distinguishingGame
          (ProbComp.eval (S n (a n) (z n)))
          (adversary n (a n) (z n)) := by
      simp only [distinguishingGame, S, z_V, PMF.monad_bind_eq_bind]
      refine PMF.bind_congr_on_support _ _ _ fun view hview => ?_
      have hview_le : view.length ≤ L_view n (a n) := by
        have h1 : (encBits view).length ≤
            c_S * ((encPair encUnary enc (n, a n)).length + 1) ^ d_S :=
          hlen_sim (n, a n) (z n) view hview
        simp only [encBits_apply] at h1
        exact le_trans h1 (Nat.le_add_left _ _)
      have hm :
          c_A * ((encPair (encPair encUnary enc) encBits ((n, a n), view)).length + 1) ^ d_A ≤
            T_A n (a n) := by
        have hpair : (encPair encUnary enc (n, a n)).length = 2 * n + 1 + (enc (a n)).length := by
          simp
        have hlen_pair :
            (encPair (encPair encUnary enc) encBits ((n, a n), view)).length =
              2 * (2 * n + 1 + (enc (a n)).length) + 1 + view.length := by
          simp
        have hle_base :
            (encPair (encPair encUnary enc) encBits ((n, a n), view)).length + 1 ≤
              (2 * (encPair encUnary enc (n, a n)).length + 1 + L_view n (a n)) + 1 := by
          omega
        exact Nat.mul_le_mul_left c_A (Nat.pow_le_pow_left hle_base d_A)
      exact hadv_take ((n, a n), view) (z n) hm
    simpa only [hgame_real, hgame_sim] using hneg

/-- **Goldreich-style instance-indexed (`x`-indexed) auxiliary-input computational zero knowledge
with unbounded auxiliary input.**
For every malicious verifier `Vstar : α → List Bool → WordOracleComp Unit (List Bool)` clocked in
the primary instance `x` (`IsOraclePPTWithAux enc encBits Vstar`), there exists a single uniform
strict PPT witness-free simulator `S : α → List Bool → ProbComp (List Bool)` clocked in `x`
(`IsPPTWithAux enc encBits S`, chosen once per `Vstar` before the distinguisher, polynomial bounds,
instance `x`, witness `w`, and auxiliary input `z`) together with a polynomial prefix bound `c, d`
such that:
1. `S` depends only on the first `c * ((enc x).length + 1) ^ d` bits of `z`.
2. For every distinguisher `adversary : α → List Bool → List Bool → ProbComp Bool` clocked in
   `(x, view)`
   (`IsPPTWithAux (encPair enc encBits) encBool (fun (x, view) z => adversary x z view)`)
   receiving the full untruncated `z`, and every witness-length bound `c_w * (n + 1) ^ d_w` and
   inverse-polynomial degree `k`, for all sufficiently large instance lengths `n = (enc x).length`,
   every valid instance-witness pair `(x, w)` (`isWitness x w = true`,
   `w.length ≤ c_w * (n + 1) ^ d_w`) and every **arbitrary, unbounded** auxiliary input
   `z : List Bool` have distinguishing advantage at most `1 / ((n : ℝ) + 1) ^ k` when interacting
   with `prover (enc x).length x w`. -/
def InstanceAuxiliaryInputZeroKnowledge {α : Type} (enc : α ↪ List Bool)
    (prover : ℕ → α → List Bool → Prover Unit)
    (isWitness : α → List Bool → Bool) : Prop :=
  ∀ Vstar : α → List Bool → WordOracleComp Unit (List Bool),
    IsOraclePPTWithAux enc encBits Vstar →
    ∃ (S : α → List Bool → ProbComp (List Bool)) (c d : ℕ),
      IsPPTWithAux enc encBits S ∧
      (∀ x z {m : ℕ}, c * ((enc x).length + 1) ^ d ≤ m → S x (z.take m) = S x z) ∧
      ∀ adversary : α → List Bool → List Bool → ProbComp Bool,
        IsPPTWithAux (encPair enc encBits) encBool (fun (x, view) z => adversary x z view) →
        ∀ c_w d_w k : ℕ, ∀ᶠ n in Filter.atTop,
          ∀ (x : α) (w z : List Bool),
            (enc x).length = n →
            isWitness x w = true →
            w.length ≤ c_w * (n + 1) ^ d_w →
            (Game.advantage
              (distinguishingGame
                (((prover (enc x).length x w).run (Vstar x z)
                  (prover (enc x).length x w).init).map Prod.fst)
                (adversary x z))
              (distinguishingGame
                (ProbComp.eval (S x z))
                (adversary x z)) : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ k

/-- **Indexing bridge from `UnboundedAuxiliaryInputZeroKnowledge` to Goldreich-style `x`-indexed
auxiliary-input zero knowledge.**
Every system satisfying `UnboundedAuxiliaryInputZeroKnowledge` satisfies
`InstanceAuxiliaryInputZeroKnowledge`. -/
theorem UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge
    {prover : ℕ → α → List Bool → Prover Unit} {isWitness : α → List Bool → Bool}
    (h : UnboundedAuxiliaryInputZeroKnowledge enc prover isWitness) :
    InstanceAuxiliaryInputZeroKnowledge enc prover isWitness := by
  intro Vstar hV
  have hV_lifted : IsOraclePPTWithAux (encPair encUnary enc) encBits (fun (_, x) z => Vstar x z) :=
    hV.preprocess (ComputableInPolyTime.snd encUnary enc)
  obtain ⟨S₀, c₀, d₀, hS₀_aux, hS₀_take, hS₀_zk⟩ := h (fun _ x z => Vstar x z) hV_lifted
  let S (x : α) (z : List Bool) : ProbComp (List Bool) := S₀ (enc x).length x z
  have hS_aux : IsPPTWithAux enc encBits S :=
    hS₀_aux.preprocess (prepare := fun x : α => ((enc x).length, x)) (by fun_prop)
  let c : ℕ := c₀ * 3 ^ d₀
  refine ⟨S, c, d₀, hS_aux, ?_, ?_⟩
  · intro x z m hm
    have hlen_eq : (encPair encUnary enc ((enc x).length, x)).length =
        2 * (enc x).length + 1 + (enc x).length := by
      simp
    have hlen :
        (encPair encUnary enc ((enc x).length, x)).length + 1 ≤ 3 * ((enc x).length + 1) := by
      omega
    have hle : c₀ * ((encPair encUnary enc ((enc x).length, x)).length + 1) ^ d₀ ≤ m := by
      calc c₀ * ((encPair encUnary enc ((enc x).length, x)).length + 1) ^ d₀
        _ ≤ c₀ * (3 * ((enc x).length + 1)) ^ d₀ :=
          Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left hlen d₀)
        _ = c * ((enc x).length + 1) ^ d₀ := by
          dsimp only [c]
          rw [Nat.mul_pow, Nat.mul_assoc]
        _ ≤ m := hm
    exact hS₀_take (enc x).length x z hle
  · intro adversary hadversary c_w d_w k
    classical
    by_contra hnot
    rw [Filter.not_eventually] at hnot
    let Bad (n : ℕ) : Prop :=
      ∃ p : α × List Bool × List Bool,
        (enc p.1).length = n ∧
        isWitness p.1 p.2.1 = true ∧
        p.2.1.length ≤ c_w * (n + 1) ^ d_w ∧
        ¬ (Game.advantage
            (distinguishingGame
              (((prover (enc p.1).length p.1 p.2.1).run (Vstar p.1 p.2.2)
                (prover (enc p.1).length p.1 p.2.1).init).map Prod.fst)
              (adversary p.1 p.2.2))
            (distinguishingGame
              (ProbComp.eval (S p.1 p.2.2))
              (adversary p.1 p.2.2)) : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ k
    have hfreq : ∃ᶠ n in Filter.atTop, Bad n := by
      refine hnot.mono fun n hn => ?_
      push Not at hn
      rcases hn with ⟨x, w, z, hx, hw, hlen, hadv⟩
      exact ⟨(x, w, z), hx, hw, hlen, not_le_of_gt hadv⟩
    obtain ⟨n₀, ⟨x₀, w₀, _⟩, _, hw₀_sat, _, _⟩ := hfreq.exists
    let a (n : ℕ) : α := if hbad : Bad n then hbad.choose.1 else x₀
    let w (n : ℕ) : List Bool := if hbad : Bad n then hbad.choose.2.1 else w₀
    let z (n : ℕ) : List Bool := if hbad : Bad n then hbad.choose.2.2 else []
    have ha_bound : PolynomiallyBounded (fun n => n + (enc x₀).length) := by fun_prop
    have ha : PolynomiallyBounded (fun n => (enc (a n)).length) := by
      refine ha_bound.mono_of_le fun n => ?_
      dsimp only [a]
      split_ifs with hbad
      · have hx := hbad.choose_spec.1
        omega
      · omega
    have hw_bound : PolynomiallyBounded (fun n => c_w * (n + 1) ^ d_w + w₀.length) := by fun_prop
    have hw : PolynomiallyBounded (fun n => (w n).length) := by
      refine hw_bound.mono_of_le fun n => ?_
      dsimp only [w]
      split_ifs with hbad
      · have hlen := hbad.choose_spec.2.2.1
        omega
      · omega
    have hw_sat (n : ℕ) : isWitness (a n) (w n) = true := by
      dsimp only [a, w]
      split_ifs with hbad
      · exact hbad.choose_spec.2.1
      · exact hw₀_sat
    have hadv_lifted : IsPPTWithAux (encPair (encPair encUnary enc) encBits) encBool
        (fun ⟨⟨_, x⟩, view⟩ z => adversary x z view) :=
      hadversary.preprocess
        (prepare := fun p : (ℕ × α) × List Bool => (p.1.2, p.2))
        (by fun_prop)
    have hneg := hS₀_zk a w z ha hw hw_sat (fun _ x z view => adversary x z view) hadv_lifted
    have hev := hneg.eventually_le_inv_polynomial
      (p := fun n => (n + 1) ^ k) (by fun_prop) (fun n => by positivity)
    refine hfreq (hev.mono fun n hn hbad => ?_)
    have hspec := hbad.choose_spec
    have ha_eq : a n = hbad.choose.1 := by simp [a, hbad]
    have hw_eq : w n = hbad.choose.2.1 := by simp [w, hbad]
    have hz_eq : z n = hbad.choose.2.2 := by simp [z, hbad]
    have hlen_n : (enc (a n)).length = n := by rw [ha_eq, hspec.1]
    have hnot_le := hspec.2.2.2
    rw [← ha_eq, ← hw_eq, ← hz_eq] at hnot_le
    dsimp only [S] at hnot_le
    rw [hlen_n] at hnot_le
    apply hnot_le
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hn

/-- **Clock and indexing bridge to Goldreich-style `x`-indexed auxiliary-input zero knowledge.**
Every system satisfying `AuxiliaryInputZeroKnowledge` satisfies
`InstanceAuxiliaryInputZeroKnowledge`. -/
theorem AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge
    {prover : ℕ → α → List Bool → Prover Unit} {isWitness : α → List Bool → Bool}
    (h : AuxiliaryInputZeroKnowledge enc prover isWitness) :
    InstanceAuxiliaryInputZeroKnowledge enc prover isWitness :=
  h.unboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge

namespace ZeroKnowledgeProof

variable {A : Set α}

/-- Unbounded-`z` family auxiliary-input zero knowledge for a bundled `ZeroKnowledgeProof`. -/
def UnboundedAuxiliaryInputZeroKnowledge (zk : ZeroKnowledgeProof enc A) : Prop :=
  Cslib.Crypto.UnboundedAuxiliaryInputZeroKnowledge enc zk.prover zk.isWitness

/-- Goldreich-style `x`-indexed auxiliary-input zero knowledge with unbounded `z` for a bundled
`ZeroKnowledgeProof`. -/
def InstanceAuxiliaryInputZeroKnowledge (zk : ZeroKnowledgeProof enc A) : Prop :=
  Cslib.Crypto.InstanceAuxiliaryInputZeroKnowledge enc zk.prover zk.isWitness

/-- `zk.AuxiliaryInputZeroKnowledge` implies `zk.UnboundedAuxiliaryInputZeroKnowledge`. -/
theorem AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge
    {zk : ZeroKnowledgeProof enc A} (h : zk.AuxiliaryInputZeroKnowledge) :
    zk.UnboundedAuxiliaryInputZeroKnowledge :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge h

/-- `zk.UnboundedAuxiliaryInputZeroKnowledge` implies `zk.InstanceAuxiliaryInputZeroKnowledge`. -/
theorem UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge
    {zk : ZeroKnowledgeProof enc A} (h : zk.UnboundedAuxiliaryInputZeroKnowledge) :
    zk.InstanceAuxiliaryInputZeroKnowledge :=
  Cslib.Crypto.UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge h

/-- `zk.AuxiliaryInputZeroKnowledge` implies `zk.InstanceAuxiliaryInputZeroKnowledge`. -/
theorem AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge
    {zk : ZeroKnowledgeProof enc A} (h : zk.AuxiliaryInputZeroKnowledge) :
    zk.InstanceAuxiliaryInputZeroKnowledge :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge h

end ZeroKnowledgeProof

end Cslib.Crypto
