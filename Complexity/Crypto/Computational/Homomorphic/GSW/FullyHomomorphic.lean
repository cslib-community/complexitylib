/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.DepthParameters.Scheme
public import Complexity.Crypto.Computational.Homomorphic.Leveled.Bootstrapping
public import Complexity.Crypto.Computational.Homomorphic.FixedKey.Bootstrapping
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Fully homomorphic encryption from GSW and decision LWE

Gentry's generic bootstrapping constructions are instantiated with GSW at the logarithmic-depth
parameter family. The base scheme is `DepthParameters.scheme`, its decryption circuits are the
actual raw-input decryptors, and its bootstrappability, correctness, widths and native runtime
are proved without computational assumptions. Bootstrappability is for Gentry's gate set
Γ = {identity, NAND}: the schemes evaluate De Morgan circuits by compiling each De Morgan level
into two NAND levels.

The security premise is decision LWE for exactly this family: secret dimension `λ + 1`,
centered-binomial noise of width `λ + 1`, and the quasi-polynomial modulus `2 ^ (16384 * t ^ 2)`
with `t = 1 + ⌈log₂ (λ + 2)⌉`.

* **Leveled FHE.** One uniformly generated polynomial-size decryption circuit family, one natively
  computable decryption algorithm and fixed polynomial widths are chosen first. Then every
  polynomially bounded depth family is covered by an actual scheme with that decryption algorithm,
  assuming only decision LWE [Gentry2009, Definition 3 and Theorem 3]. Security is proved both
  asymptotically (`exists_leveled_of_decisionLWE`) and with a concrete-security reduction matching
  Gentry's Theorem 4 up to a constant factor (`advantage_leveled_eq` and `advantage_leveled_le`,
  [Gentry2009, Section 2, Theorem 4, p. 171], with asymptotic `IsPPT` rather than a multiplicative
  runtime bound relative to the adversary). Native certificates are uniform for each depth family;
  key generation reads only the unary security parameter.
* **Fully homomorphic encryption.** The one-key self-loop construction evaluates every circuit,
  assuming decision LWE for this family *and* the separate one-key circular-security assumption
  `Encryption.CircularSecure` for the base scheme [Gentry2009, Section 2, the self-loop
  construction]. This is a one-key specialization of the KDM security Gentry assumes there.
  Circular security is not derived from LWE.

Neither theorem asserts lattice hardness, a worst-case reduction, or circuit privacy.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.computableInPolyTime_secretWidth`: the base GSW
  secret width is computable in polynomial time in unary.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.isPPT_leveledAdversary`: the unified base reduction
  for the leveled GSW scheme is native strict PPT.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.advantage_leveled_eq`: exact concrete-security
  reduction loss of the leveled GSW scheme to the base GSW scheme.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.advantage_scheme_le`: concrete-security bound for
  the base GSW scheme in terms of decision-LWE advantage and `hidingError`.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.advantage_leveled_le`: concrete-security bound for
  the leveled GSW scheme in terms of decision-LWE advantage and `hidingError`.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.exists_leveled_decrypt_circuits`: uniformly
  generated polynomial-size decryption circuits for the leveled GSW scheme across all budgets.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.exists_leveled_of_decisionLWE`: leveled FHE.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.fullyHomomorphic_of_decisionLWE_of_circularSecure`:
  FHE under the additional circular-security assumption.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, Definitions 1–5,
  Theorems 3 and 4 and the self-loop construction][Gentry2009]
* [C. Gentry, A. Sahai and B. Waters, Sections 3.2–3.4][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW.DepthParameters

open Circuits Probability Turing.MultiTapeTM
open Parameters (dimension noise)
open scoped NNReal

/-- The base GSW secret width `dimension k * width k` is computable in polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_secretWidth :
    ComputableInPolyTime secretWidth encUnary encUnary := by
  have hd := Parameters.computableInPolyTime_dimension
  have hw := computableInPolyTime_width
  unfold secretWidth
  fun_prop

/-- For any polynomial-time unary budget family, the unified base reduction `leveledAdversary`
for the leveled GSW scheme is native strict PPT. -/
theorem isPPT_leveledAdversary {budget : ℕ → ℕ}
    (hbudget : ComputableInPolyTime budget encUnary encUnary)
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT) :
    (Leveled.leveledAdversary scheme (fun k => 2 * budget k) secretWidth adversary).IsPPT := by
  have hdepth : ComputableInPolyTime (fun k => 2 * budget k) encUnary encUnary := by
    fun_prop
  exact Leveled.isPPT_leveledAdversary isPPTOn_encrypt hadversary isPPTOn_keyGen
    hdepth computableInPolyTime_secretWidth

/-- Exact concrete-security reduction loss of the leveled GSW scheme to the base GSW scheme
([Gentry2009], Section 2, Theorem 4, p. 171, up to a constant factor in the loss;
the running-time clause is not formalized). -/
theorem advantage_leveled_eq (budget : ℕ → ℕ) (adversary : Encryption.Adversary)
    (security : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game (Leveled.scheme decryptionCircuits budget).keyGen
        (Leveled.scheme decryptionCircuits budget).encrypt adversary false security))
      (ProbComp.eval (Encryption.game (Leveled.scheme decryptionCircuits budget).keyGen
        (Leveled.scheme decryptionCircuits budget).encrypt adversary true security)) =
    4 * (dyadicSize (2 * budget security) : ℝ≥0) * dyadicSize (secretWidth security) *
      Game.advantage
        (ProbComp.eval (Encryption.game scheme.keyGen scheme.encrypt
          (Leveled.leveledAdversary scheme (fun k => 2 * budget k) secretWidth adversary)
          false security))
        (ProbComp.eval (Encryption.game scheme.keyGen scheme.encrypt
          (Leveled.leveledAdversary scheme (fun k => 2 * budget k) secretWidth adversary)
          true security)) :=
  Leveled.advantage_scheme_eq_leveledAdversary decryptionCircuits budget secretWidth adversary
    security (secretWidth security) (fixedWidth.secret_length security) le_rfl

/-- One uniform reduction bounds the base GSW scheme's chosen-message advantage by twice its
decision-LWE advantage plus `hidingError`. -/
theorem advantage_scheme_le (adversary : Encryption.Adversary) (security : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game scheme.keyGen scheme.encrypt adversary false security))
      (ProbComp.eval (Encryption.game scheme.keyGen scheme.encrypt adversary true security)) ≤
    2 * Game.advantage
      (distinguishingGame
        (LWE.realEnsemble dimension samples width
          (fun k => noiseLaw (width k) (noise k)) security)
        (lweDistinguisher dimension samples width adversary security))
      (distinguishingGame
        (LWE.uniformEnsemble dimension samples width security)
        (lweDistinguisher dimension samples width adversary security)) +
      hidingError (dimension security) (samples security) (width security) := by
  have h := GSW.advantage_game_le dimension samples width noise adversary security
  have hfg :
      Game.advantage
        (ProbComp.eval (Encryption.game scheme.keyGen scheme.encrypt adversary false security))
        (ProbComp.eval (Encryption.game scheme.keyGen scheme.encrypt adversary true security)) =
      Game.advantage
        (ProbComp.eval (Encryption.game
          (fun k => keyGenSerialized (dimension k) (samples k) (width k) (noise k))
          (fun k => encryptSerialized (dimension k) (samples k) (width k))
          adversary false security))
        (ProbComp.eval (Encryption.game
          (fun k => keyGenSerialized (dimension k) (samples k) (width k) (noise k))
          (fun k => encryptSerialized (dimension k) (samples k) (width k))
          adversary true security)) :=
    congrArg₂
      (fun kg enc => Game.advantage
        (ProbComp.eval (Encryption.game kg enc adversary false security))
        (ProbComp.eval (Encryption.game kg enc adversary true security)))
      rfl rfl
  exact hfg.trans_le h

/-- Concrete-security bound for the leveled GSW scheme in terms of the decision-LWE distinguisher
advantage and `hidingError` ([Gentry2009], Section 2, Theorem 4, p. 171, up to a constant factor
in the loss; the running-time clause is not formalized). -/
theorem advantage_leveled_le (budget : ℕ → ℕ) (adversary : Encryption.Adversary)
    (security : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game (Leveled.scheme decryptionCircuits budget).keyGen
        (Leveled.scheme decryptionCircuits budget).encrypt adversary false security))
      (ProbComp.eval (Encryption.game (Leveled.scheme decryptionCircuits budget).keyGen
        (Leveled.scheme decryptionCircuits budget).encrypt adversary true security)) ≤
    4 * (dyadicSize (2 * budget security) : ℝ≥0) * dyadicSize (secretWidth security) *
      (2 * Game.advantage
        (distinguishingGame
          (LWE.realEnsemble dimension samples width
            (fun k => noiseLaw (width k) (noise k)) security)
          (lweDistinguisher dimension samples width
            (Leveled.leveledAdversary scheme (fun k => 2 * budget k) secretWidth adversary)
            security))
        (distinguishingGame
          (LWE.uniformEnsemble dimension samples width security)
          (lweDistinguisher dimension samples width
            (Leveled.leveledAdversary scheme (fun k => 2 * budget k) secretWidth adversary)
            security)) +
        hidingError (dimension security) (samples security) (width security)) :=
  (advantage_leveled_eq budget adversary security).trans_le
    (mul_le_mul_of_nonneg_left
      (advantage_scheme_le
        (Leveled.leveledAdversary scheme (fun k => 2 * budget k) secretWidth adversary) security)
      zero_le)

/-- The leveled GSW scheme's complete tagged decryption algorithm has a uniformly generated family
of polynomial-size circuits on the derived widths
`(3 * secretWidth k + 1) + (ciphertextWidth k + 1)`, shared across all depth budgets and requiring
no computational assumption. -/
theorem exists_leveled_decrypt_circuits :
    ∃ circuits : ∀ k, Circuit Boolean.signature
        ((3 * secretWidth k + 1) + (ciphertextWidth k + 1)) 1,
      ComputableInPolyTime
        (fun k => (⟨_, circuits k⟩ : Σ m, Circuit Boolean.signature m 1))
        encUnary (Boolean.encCircuit 1) ∧
      PolynomiallyBounded (fun k => (circuits k).size) ∧
      ∀ (budget : ℕ → ℕ) k (sk ciphertext : List Bool),
        sk.length = 3 * secretWidth k + 1 →
        ciphertext.length = ciphertextWidth k + 1 →
        (circuits k).eval Boolean.interpretation
            (BitString.ofList ((3 * secretWidth k + 1) + (ciphertextWidth k + 1))
              (sk ++ ciphertext)) 0 =
          (Leveled.scheme decryptionCircuits budget).decrypt k sk ciphertext := by
  have hsecret : ComputableInPolyTime secretWidth encUnary encUnary := by
    have := Parameters.computableInPolyTime_dimension
    have := computableInPolyTime_width
    unfold secretWidth
    fun_prop
  exact Leveled.exists_uniform_decrypt_circuits decryptionCircuits
    computableInPolyTime_decryptionCircuits hsecret

/-- Leveled FHE from GSW under decision LWE for this family, with quasi-polynomial modulus.
One uniformly generated polynomial-size circuit family computes the common decryption algorithm
`Leveled.decrypt decryptionCircuits`, which is natively computable, and the key and ciphertext
widths are fixed polynomials; all of these are chosen before the depth. Every polynomially
bounded depth family is then covered by an actual scheme with an efficiently computable budget
and exactly that decryption algorithm: it is correct for every circuit of the requested depth,
has the fixed widths, native algorithms and IND-CPA security. No circular-security assumption is
used. -/
theorem exists_leveled_of_decisionLWE
    (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k))) :
    ∃ circuits : ∀ k, Circuit Boolean.signature
        ((3 * secretWidth k + 1) + (ciphertextWidth k + 1)) 1,
      ComputableInPolyTime
        (fun k => (⟨_, circuits k⟩ : Σ m, Circuit Boolean.signature m 1))
        encUnary (Boolean.encCircuit 1) ∧
      PolynomiallyBounded (fun k => (circuits k).size) ∧
      (∀ k (sk ciphertext : List Bool), sk.length = 3 * secretWidth k + 1 →
        ciphertext.length = ciphertextWidth k + 1 →
        (circuits k).eval Boolean.interpretation
            (BitString.ofList ((3 * secretWidth k + 1) + (ciphertextWidth k + 1))
              (sk ++ ciphertext)) 0 =
          Leveled.decrypt decryptionCircuits k sk ciphertext) ∧
      ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => Leveled.decrypt decryptionCircuits p.1 p.2.1 p.2.2)
        (encPair encUnary (encPair encBits encBits)) encBool ∧
      PolynomiallyBounded (fun k => 3 * secretWidth k + 1) ∧
      PolynomiallyBounded (fun k => ciphertextWidth k + 1) ∧
      ∀ depth : ℕ → ℕ, PolynomiallyBounded depth →
        ∃ budget : ℕ → ℕ,
          ComputableInPolyTime budget encUnary encUnary ∧
          (∀ k, depth k ≤ budget k) ∧
          (Leveled.scheme decryptionCircuits budget).decrypt =
            Leveled.decrypt decryptionCircuits ∧
          (Leveled.scheme decryptionCircuits budget).Correct ∧
          (∀ k c, c.2.depth ≤ depth k → (Leveled.scheme decryptionCircuits budget).permitted k c) ∧
          (Leveled.scheme decryptionCircuits budget).FixedWidth (fun k => 3 * secretWidth k + 1)
            (fun k => ciphertextWidth k + 1) ∧
          IsPPTOn encUnary (encPair encBits encBits)
            (Leveled.scheme decryptionCircuits budget).keyGen ∧
          IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
            (fun p => (Leveled.scheme decryptionCircuits budget).encrypt p.1 p.2.1 p.2.2) ∧
          IsPPTOn
            (encPair encUnary (encPair encBits
              (encPair (Boolean.encCircuit 1) (encList encBits))))
            encBits
            (fun p =>
              (Leveled.scheme decryptionCircuits budget).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
          Encryption.INDCPA (Leveled.scheme decryptionCircuits budget).keyGen
            (Leveled.scheme decryptionCircuits budget).encrypt := by
  have hD := computableInPolyTime_decryptionCircuits
  obtain ⟨circuits, hgen, hsize, hcircuits⟩ := exists_leveled_decrypt_circuits
  have hdecrypt := (Leveled.computableInPolyTime_scheme_decrypt decryptionCircuits hD
    (fun _ => 0))
  obtain ⟨hsecret, hciphertext⟩ := Leveled.polynomiallyBounded_widths decryptionCircuits hD
  refine ⟨circuits, hgen, hsize, fun k sk c hsk hc => hcircuits (fun _ => 0) k sk c hsk hc,
    hdecrypt, hsecret, hciphertext, fun depth hdepth => ?_⟩
  obtain ⟨budget, hbudget, hle, hcorrect, hpermitted, hwidth, -, -, hkeyGen, hencrypt, -,
      hevaluate, hsecure⟩ :=
    Leveled.exists_scheme_of_polynomiallyBounded decryptionCircuits correct fixedWidth
      bootstrappable (indCPA_scheme hLWE) isPPTOn_keyGen isPPTOn_encrypt isPPTOn_evaluate hD
      hdepth
  exact ⟨budget, hbudget, hle, rfl, hcorrect, hpermitted, hwidth, hkeyGen,
    hencrypt, hevaluate, hsecure⟩

/-- Fully homomorphic encryption from GSW: under decision LWE for this family, with
quasi-polynomial modulus, and the explicit one-key circular-security assumption for the base
scheme, the self-loop construction correctly evaluates every finite circuit. Its widths are those
of GSW, its decryption circuits have polynomial size, its four algorithms are native, and it is
IND-CPA. -/
theorem fullyHomomorphic_of_decisionLWE_of_circularSecure
    (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k)))
    (hcircular : Encryption.CircularSecure scheme.keyGen scheme.encrypt) :
    (FixedKey.scheme decryptionCircuits).Correct ∧
      (∀ k c, (FixedKey.scheme decryptionCircuits).permitted k c) ∧
      (FixedKey.scheme decryptionCircuits).FixedWidth secretWidth ciphertextWidth ∧
      PolynomiallyBounded secretWidth ∧ PolynomiallyBounded ciphertextWidth ∧
      PolynomiallyBounded
        (fun k => ((FixedKey.decryptionCircuits decryptionCircuits).circuit k).size) ∧
      IsPPTOn encUnary (encPair encBits encBits) (FixedKey.scheme decryptionCircuits).keyGen ∧
      IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
        (fun p => (FixedKey.scheme decryptionCircuits).encrypt p.1 p.2.1 p.2.2) ∧
      ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          (FixedKey.scheme decryptionCircuits).decrypt p.1 p.2.1 p.2.2)
        (encPair encUnary (encPair encBits encBits)) encBool ∧
      IsPPTOn
        (encPair encUnary (encPair encBits
          (encPair (Boolean.encCircuit 1) (encList encBits))))
        encBits
        (fun p => (FixedKey.scheme decryptionCircuits).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
      Encryption.INDCPA (FixedKey.scheme decryptionCircuits).keyGen
        (FixedKey.scheme decryptionCircuits).encrypt := by
  obtain ⟨hcorrect, hpermitted, hwidth, hsecret, hciphertext, hsize, hkeyGen, hencrypt,
      hdecrypt, hevaluate, hsecure⟩ :=
    FixedKey.fullyHomomorphic decryptionCircuits correct fixedWidth bootstrappable
      (indCPA_scheme hLWE) hcircular isPPTOn_keyGen isPPTOn_encrypt isPPTOn_evaluate
      computableInPolyTime_decryptionCircuits
  exact ⟨hcorrect, hpermitted, hwidth, hsecret, hciphertext, hsize, hkeyGen, hencrypt,
    hdecrypt, hevaluate, hsecure⟩

end Cslib.Crypto.Homomorphic.GSW.DepthParameters
