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

/-!
# Clock bridge for auxiliary-input zero knowledge with unbounded auxiliary input

In `AuxiliaryInputZeroKnowledge`, the malicious verifier `Vstar` is a standard `IsOraclePPTOn`
program on `encPair encUnary (encPair enc encBits)`, so its polynomial clock is allowed to depend
on the length of the auxiliary input `z`, and the family `z : ℕ → List Bool` is required to be
polynomially bounded.

When `Vstar` is instead clocked in the primary input `(1^n, a)` (or in the instance `x` alone) via
`IsOraclePPTWithAux`, input-tape prefix locality (`IsOraclePPTWithAux.exists_run_interpret_take`)
shows that `Vstar` reads at most a polynomial prefix `z.take (T_V n a)` of `z` during its run
against any stateful prover `Prover Unit`. Truncating the simulator `S₀` supplied by
`AuxiliaryInputZeroKnowledge` to that prefix (`S n a z := S₀ n a (z.take (T_V n a))`) therefore
yields a uniform strict PPT simulator that works for **arbitrary, unbounded** auxiliary inputs `z`,
both in the security-parameter-indexed family form (`UnboundedAuxiliaryInputZeroKnowledge`) and in
the Goldreich-style instance-indexed (`x`-indexed) form (`InstanceAuxiliaryInputZeroKnowledge`)
where the security parameter is `(enc x).length` and the simulator is chosen once per `Vstar`
before the distinguisher, instance `x`, valid witness `w`, and unbounded auxiliary input `z`.

## Main definitions

* `Cslib.Crypto.UnboundedAuxiliaryInputZeroKnowledge`,
  `Cslib.Crypto.ZeroKnowledgeProof.UnboundedAuxiliaryInputZeroKnowledge`: family-indexed
  auxiliary-input zero knowledge against prefix-clocked verifiers (`IsOraclePPTWithAux`) over
  arbitrary, unbounded auxiliary-input families `z : ℕ → List Bool`.
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
* `Cslib.Crypto.AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge`:
  `AuxiliaryInputZeroKnowledge` implies `InstanceAuxiliaryInputZeroKnowledge` (with the
  `ZeroKnowledgeProof` projection of the same name).

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001], Chapter 4.
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
encoded primary pair `encPair enc₁ enc₂ (a, b)` preserves `IsPPTOn`. -/
theorem IsPPTOn.take_aux_triple {program : α → β → List Bool → ProbComp γ}
    (h : IsPPTOn (encPair enc₁ (encPair enc₂ encBits)) output
      (fun ⟨a, b, z⟩ => program a b z))
    (c d : ℕ) :
    IsPPTOn (encPair enc₁ (encPair enc₂ encBits)) output
      (fun ⟨a, b, z⟩ =>
        program a b (z.take (c * ((encPair enc₁ enc₂ (a, b)).length + 1) ^ d))) := by
  have hpair : IsPPTOn (encPair (encPair enc₁ enc₂) encBits) output
      (fun (p, z) => (fun p : α × β => program p.1 p.2) p z) :=
    h.preprocess (prepare := fun p : (α × β) × List Bool => (p.1.1, p.1.2, p.2)) (by fun_prop)
  exact (hpair.take_aux (program := fun p : α × β => program p.1 p.2) c d).preprocess
    (prepare := fun p : α × β × List Bool => ((p.1, p.2.1), p.2.2)) (by fun_prop)

end Cslib.Probability

namespace Cslib.Crypto

open Probability Complexity Turing.MultiTapeTM
open scoped NNReal ENNReal

variable {α : Type} {enc : α ↪ List Bool}

/-- **Unbounded-`z` family auxiliary-input computational zero knowledge.**
For every malicious verifier `Vstar` clocked in the primary input `(1^n, a)`
(`IsOraclePPTWithAux (encPair encUnary enc) encBits`), there exists a uniform strict PPT
witness-free simulator `S` together with a polynomial prefix bound `c, d` in `(1^n, a)` such that:
1. `S` depends only on the first `c * ((encPair encUnary enc (n, a)).length + 1) ^ d` bits of `z`.
2. Across all polynomially bounded instance families `a : ℕ → α`, polynomially bounded valid
   witness families `w : ℕ → List Bool`, and **arbitrary, unbounded** auxiliary-input families
   `z : ℕ → List Bool`, every full-input uniform strict PPT distinguisher receiving the active
   prefix of `z n` has negligible distinguishing advantage between the real interaction view and
   the simulated view. -/
def UnboundedAuxiliaryInputZeroKnowledge {α : Type} (enc : α ↪ List Bool)
    (prover : ℕ → α → List Bool → Prover Unit)
    (isWitness : α → List Bool → Bool) : Prop :=
  ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
    IsOraclePPTWithAux (encPair encUnary enc) encBits (fun (n, a) z => Vstar n a z) →
    ∃ (S : ℕ → α → List Bool → ProbComp (List Bool)) (c d : ℕ),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun ⟨n, a, z⟩ => S n a z) ∧
      (∀ n a z {m : ℕ}, c * ((encPair encUnary enc (n, a)).length + 1) ^ d ≤ m →
        S n a (z.take m) = S n a z) ∧
      ∀ (a : ℕ → α) (w z : ℕ → List Bool),
        PolynomiallyBounded (fun n => (enc (a n)).length) →
        PolynomiallyBounded (fun n => (w n).length) →
        (∀ n, isWitness (a n) (w n) = true) →
        ∀ adversary : ℕ → α → List Bool → List Bool → ProbComp Bool,
          IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
            (fun ⟨⟨n, a, z⟩, view⟩ => adversary n a z view) →
          Negligible (fun n => Game.advantage
            (distinguishingGame
              (((prover n (a n) (w n)).run (Vstar n (a n) (z n))
                (prover n (a n) (w n)).init).map Prod.fst)
              (adversary n (a n)
                ((z n).take (c * ((encPair encUnary enc (n, a n)).length + 1) ^ d))))
            (distinguishingGame
              (ProbComp.eval (S n (a n) (z n)))
              (adversary n (a n)
                ((z n).take (c * ((encPair encUnary enc (n, a n)).length + 1) ^ d)))))

/-- Under `UnboundedAuxiliaryInputZeroKnowledge`, the real and simulated view ensembles are
`ComputationallyIndistinguishable` across all polynomially bounded valid `(a, w)` families and
all arbitrary, unbounded auxiliary-input families `z : ℕ → List Bool`. -/
theorem UnboundedAuxiliaryInputZeroKnowledge.computationallyIndistinguishable
    {prover : ℕ → α → List Bool → Prover Unit} {isWitness : α → List Bool → Bool}
    (h : UnboundedAuxiliaryInputZeroKnowledge enc prover isWitness)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTWithAux (encPair encUnary enc) encBits (fun (n, a) z => Vstar n a z)) :
    ∃ (S : ℕ → α → List Bool → ProbComp (List Bool)) (c d : ℕ),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun ⟨n, a, z⟩ => S n a z) ∧
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
  have htest : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun p => adversary p.1.1 p.2) :=
    hadversary.preprocess (by fun_prop) (by fun_prop)
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
  obtain ⟨S₀, hS₀_ppt, hS₀_zk⟩ := h Vstar hV.isOraclePPTOn_triple
  let T (n : ℕ) (a : α) : ℕ := c * ((encPair encUnary enc (n, a)).length + 1) ^ d
  let S (n : ℕ) (a : α) (z : List Bool) : ProbComp (List Bool) :=
    S₀ n a (z.take (T n a))
  refine ⟨S, c, d, hS₀_ppt.take_aux_triple c d, ?_, ?_⟩
  · intro n a z m hm
    simp only [S, T, List.take_take, Nat.min_eq_left hm]
  · intro a w z ha hw hw_sat adversary hadversary
    let z' (n : ℕ) : List Bool := (z n).take (T n (a n))
    have hz'_bound :
        PolynomiallyBounded (fun n => c * ((2 * n + 1 + (enc (a n)).length) + 1) ^ d) := by
      fun_prop
    have hz' : PolynomiallyBounded (fun n => (z' n).length) := by
      refine hz'_bound.mono_of_le fun n => ?_
      have hlen : (z' n).length ≤ T n (a n) := List.length_take_le _ _
      have hpair : (encPair encUnary enc (n, a n)).length = 2 * n + 1 + (enc (a n)).length := by
        simp
      simpa only [T, hpair] using hlen
    have hneg := hS₀_zk a w z' ha hw hz' hw_sat adversary hadversary
    have heq (n : ℕ) :
        (prover n (a n) (w n)).run (Vstar n (a n) (z n)) (prover n (a n) (w n)).init =
          (prover n (a n) (w n)).run (Vstar n (a n) (z' n)) (prover n (a n) (w n)).init :=
      (hV_take (n, a n) (z n) le_rfl (prover n (a n) (w n)) (prover n (a n) (w n)).init).symm
    simpa only [heq, S, z', T] using hneg

/-- **Goldreich-style instance-indexed (`x`-indexed) auxiliary-input computational zero knowledge
with unbounded auxiliary input.**
For every malicious verifier `Vstar : α → List Bool → WordOracleComp Unit (List Bool)` clocked in
the primary instance `x` (`IsOraclePPTWithAux enc encBits Vstar`), there exists a single uniform
strict PPT witness-free simulator `S : α → List Bool → ProbComp (List Bool)` (chosen once per
`Vstar` before the distinguisher, polynomial bounds, instance `x`, witness `w`, and auxiliary input
`z`) together with a polynomial prefix bound `c, d` such that:
1. `S` depends only on the first `c * ((enc x).length + 1) ^ d` bits of `z`.
2. For every uniform strict PPT distinguisher `adversary : α → List Bool → ProbComp Bool` and
   every witness-length bound `c_w * (n + 1) ^ d_w` and inverse-polynomial degree `k`, for all
   sufficiently large instance lengths `n = (enc x).length`, every valid instance-witness pair
   `(x, w)` (`isWitness x w = true`, `w.length ≤ c_w * (n + 1) ^ d_w`) and every **arbitrary,
   unbounded** auxiliary input `z : List Bool` have distinguishing advantage at most
   `1 / ((n : ℝ) + 1) ^ k` when interacting with `prover (enc x).length x w`. -/
def InstanceAuxiliaryInputZeroKnowledge {α : Type} (enc : α ↪ List Bool)
    (prover : ℕ → α → List Bool → Prover Unit)
    (isWitness : α → List Bool → Bool) : Prop :=
  ∀ Vstar : α → List Bool → WordOracleComp Unit (List Bool),
    IsOraclePPTWithAux enc encBits Vstar →
    ∃ (S : α → List Bool → ProbComp (List Bool)) (c d : ℕ),
      IsPPTOn (encPair enc encBits) encBits (fun (x, z) => S x z) ∧
      (∀ x z {m : ℕ}, c * ((enc x).length + 1) ^ d ≤ m → S x (z.take m) = S x z) ∧
      ∀ adversary : α → List Bool → ProbComp Bool,
        IsPPTOn (encPair enc encBits) encBool (fun (x, view) => adversary x view) →
        ∀ c_w d_w k : ℕ, ∀ᶠ n in Filter.atTop,
          ∀ (x : α) (w z : List Bool),
            (enc x).length = n →
            isWitness x w = true →
            w.length ≤ c_w * (n + 1) ^ d_w →
            (Game.advantage
              (distinguishingGame
                (((prover (enc x).length x w).run (Vstar x z)
                  (prover (enc x).length x w).init).map Prod.fst)
                (adversary x))
              (distinguishingGame
                (ProbComp.eval (S x z))
                (adversary x)) : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ k

/-- **Clock and indexing bridge to Goldreich-style `x`-indexed auxiliary-input zero knowledge.**
Every system satisfying `AuxiliaryInputZeroKnowledge` satisfies
`InstanceAuxiliaryInputZeroKnowledge`. -/
theorem AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge
    {prover : ℕ → α → List Bool → Prover Unit} {isWitness : α → List Bool → Bool}
    (h : AuxiliaryInputZeroKnowledge enc prover isWitness) :
    InstanceAuxiliaryInputZeroKnowledge enc prover isWitness := by
  intro Vstar hV
  obtain ⟨c, d, hV_take⟩ := Prover.exists_run_take_of_isOraclePPTWithAux hV
  have hV_lifted : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun ⟨_, x, z⟩ => Vstar x z) :=
    hV.isOraclePPTOn.preprocess' (ComputableInPolyTime.snd encUnary (encPair enc encBits))
  obtain ⟨S₀, hS₀_ppt, hS₀_zk⟩ := h (fun _ x z => Vstar x z) hV_lifted
  let T (x : α) : ℕ := c * ((enc x).length + 1) ^ d
  let S (x : α) (z : List Bool) : ProbComp (List Bool) :=
    S₀ (enc x).length x (z.take (T x))
  have hS_ppt : IsPPTOn (encPair enc encBits) encBits (fun (x, z) => S x z) := by
    have hlen : ComputableInPolyTime (fun p : α × List Bool => (enc p.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.encoding_length enc).comp (.fst enc encBits)
    exact hS₀_ppt.preprocess
      (prepare := fun p : α × List Bool =>
        ((enc p.1).length, p.1, p.2.take (c * ((enc p.1).length + 1) ^ d)))
      (by fun_prop)
  refine ⟨S, c, d, hS_ppt, ?_, ?_⟩
  · intro x z m hm
    simp only [S, T, List.take_take, Nat.min_eq_left hm]
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
              (adversary p.1))
            (distinguishingGame
              (ProbComp.eval (S p.1 p.2.2))
              (adversary p.1)) : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ k
    have hfreq : ∃ᶠ n in Filter.atTop, Bad n := by
      refine hnot.mono fun n hn => ?_
      push Not at hn
      rcases hn with ⟨x, w, z, hx, hw, hlen, hadv⟩
      exact ⟨(x, w, z), hx, hw, hlen, not_le_of_gt hadv⟩
    obtain ⟨n₀, ⟨x₀, w₀, _⟩, _, hw₀_sat, _, _⟩ := hfreq.exists
    let a (n : ℕ) : α := if hbad : Bad n then hbad.choose.1 else x₀
    let w (n : ℕ) : List Bool := if hbad : Bad n then hbad.choose.2.1 else w₀
    let zRaw (n : ℕ) : List Bool := if hbad : Bad n then hbad.choose.2.2 else []
    let z' (n : ℕ) : List Bool := (zRaw n).take (T (a n))
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
    have hz'_bound : PolynomiallyBounded (fun n => c * ((enc (a n)).length + 1) ^ d) := by fun_prop
    have hz' : PolynomiallyBounded (fun n => (z' n).length) :=
      hz'_bound.mono_of_le fun n => List.length_take_le _ _
    have hw_sat (n : ℕ) : isWitness (a n) (w n) = true := by
      dsimp only [a, w]
      split_ifs with hbad
      · exact hbad.choose_spec.2.1
      · exact hw₀_sat
    have hadv_lifted : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
        (fun ⟨⟨_, x, _⟩, view⟩ => adversary x view) :=
      hadversary.preprocess
        (prepare := fun p : (ℕ × α × List Bool) × List Bool => (p.1.2.1, p.2))
        (by fun_prop)
    have hneg := hS₀_zk a w z' ha hw hz' hw_sat (fun _ x _ view => adversary x view) hadv_lifted
    have hev := hneg.eventually_le_inv_polynomial
      (p := fun n => (n + 1) ^ k) (by fun_prop) (fun n => by positivity)
    refine hfreq (hev.mono fun n hn hbad => ?_)
    have hspec := hbad.choose_spec
    have ha_eq : a n = hbad.choose.1 := by simp [a, hbad]
    have hw_eq : w n = hbad.choose.2.1 := by simp [w, hbad]
    have hz_eq : zRaw n = hbad.choose.2.2 := by simp [zRaw, hbad]
    have hlen_n : (enc (a n)).length = n := by rw [ha_eq, hspec.1]
    have hrun :
        (((prover (enc (a n)).length (a n) (w n)).run (Vstar (a n) (zRaw n))
          (prover (enc (a n)).length (a n) (w n)).init).map Prod.fst) =
        (((prover n (a n) (w n)).run (Vstar (a n) (z' n))
          (prover n (a n) (w n)).init).map Prod.fst) := by
      rw [hlen_n]
      exact congrArg (PMF.map Prod.fst)
        ((hV_take (a n) (zRaw n) le_rfl (prover n (a n) (w n))
          (prover n (a n) (w n)).init).symm)
    have hsim : S (a n) (zRaw n) = S₀ n (a n) (z' n) := by
      simp only [S, z', hlen_n]
    have hnot_le := hspec.2.2.2
    rw [← ha_eq, ← hw_eq, ← hz_eq, hrun, hsim] at hnot_le
    apply hnot_le
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hn

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

/-- `zk.AuxiliaryInputZeroKnowledge` implies `zk.InstanceAuxiliaryInputZeroKnowledge`. -/
theorem AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge
    {zk : ZeroKnowledgeProof enc A} (h : zk.AuxiliaryInputZeroKnowledge) :
    zk.InstanceAuxiliaryInputZeroKnowledge :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge h

end ZeroKnowledgeProof

end Cslib.Crypto
