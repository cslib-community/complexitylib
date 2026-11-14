/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.Basic
public import CslibFrontier.Crypto.Computational.SIS.Module
import CslibFrontier.Computability.Probabilistic.PPT.Extension

/-!
# Decision Module-LWE

The decision Module-LWE experiments over the negacyclic ring `R_q = ℤ_q[X] / (X^n + 1)`
([LyubashevskyPeikertRegev2010], [DucasEtAl2018]), with polynomials stored as coefficient vectors
`Fin n → ZMod q`. The real experiment `ModuleLWE.realExperiment` draws a uniform module matrix `A`
and gives the distinguisher `A` and the sample `A · s + e` (`ModuleLWE.sample`) for a secret `s`
and an error vector `e`; the random experiment `ModuleLWE.randomExperiment` gives it a uniform
pair. For a secret law and an error law, the real game `ModuleLWE.realGame` draws `s` and `e` and
runs the real experiment, `ModuleLWE.randomGame` runs the random one, and `ModuleLWE.advantage` is
the distance between them. These are the games of the ML-KEM and ML-DSA reductions, whose secrets
are short rather than uniform. Module-LWE is LWE over the ring `Negacyclic (ZMod q) n`
(`ModuleLWE.advantage_eq_lweAdvantage`).

`DecisionModuleLWEWith m d n q secret error` is the asymptotic assumption with an `m κ × d κ`
module matrix over `ℤ_{q κ}[X] / (X^{n κ} + 1)`, a secret law `secret κ` and an error law
`error κ`: every distinguisher that is uniform strict PPT on encodings
(`ModuleLWE.Distinguisher.IsPPT`) has negligible advantage between the real game for these laws and
the random game. A distinguisher machine reads the unary security parameter and the encoded sample
(`ModuleLWE.encInput_apply`). With short secret and error laws, this is the assumption of the
CRYSTALS-Kyber and CRYSTALS-Dilithium submissions ([AvanziEtAl2021], §4.3; [BaiEtAl2021], §6.1).
`DecisionModuleLWE m d n q noise` is the case of a uniform secret and independent polynomial errors
from `noise κ` (`decisionModuleLWE_iff_decisionModuleLWEWith`).

A distinguisher outputs a bit, so `DecisionModuleLWEWith` is the same assumption as the
indistinguishability of the encoded samples `ModuleLWE.realEnsemble` and
`ModuleLWE.uniformEnsemble` against word-level distinguishers (`decisionModuleLWEWith_iff_encoded`).
Clients that reduce on encoded words use `DecisionModuleLWEWith.encoded`.

`DecisionModuleLWEWith` is a hypothesis against uniform classical strict polynomial-time programs.
It makes no assertion of hardness for any particular parameter family or laws, and no relation to
`DecisionLWE` at modulus `2 ^ w` is proved. It is meaningful only for a family whose parameters grow
with the security parameter; at one fixed parameter set it fails unless the real sample is exactly
uniform (see `DecisionModuleLWEWith`).

## Main definitions

* `Cslib.Crypto.ModuleLWE.sample`: the sample `A · s + e`.
* `Cslib.Crypto.ModuleLWE.realExperiment`, `Cslib.Crypto.ModuleLWE.randomExperiment`: the
  fixed-instance experiments.
* `Cslib.Crypto.ModuleLWE.realGame`, `Cslib.Crypto.ModuleLWE.randomGame`,
  `Cslib.Crypto.ModuleLWE.advantage`: the games and advantage for a secret law and an error law.
* `Cslib.Crypto.ModuleLWE.encodeSample`: the encoding of a pair `(A, b)`.
* `Cslib.Crypto.ModuleLWE.Input`, `Cslib.Crypto.ModuleLWE.encInput`: the input of a distinguisher
  and its encoding.
* `Cslib.Crypto.ModuleLWE.Distinguisher`, `Cslib.Crypto.ModuleLWE.Distinguisher.IsPPT`: typed
  distinguishers and their efficiency.
* `Cslib.Crypto.DecisionModuleLWEWith`: the decision Module-LWE assumption for a secret law and
  an error law.
* `Cslib.Crypto.DecisionModuleLWE`: its case with a uniform secret and independent polynomial
  errors.
* `Cslib.Crypto.ModuleLWE.sampleLaw`, `Cslib.Crypto.ModuleLWE.realEnsemble`,
  `Cslib.Crypto.ModuleLWE.uniformEnsemble`: the sample law and the encoded samples.

## Main results

* `Cslib.Crypto.ModuleLWE.flattenPolyVec_sample`: Module-LWE samples flatten to standard LWE
  matrix-vector relations under `expandModuleMatrix`.
* `Cslib.Crypto.ModuleLWE.advantage_eq_lweAdvantage`: Module-LWE is LWE over the ring
  `Negacyclic (ZMod q) n`.
* `Cslib.Crypto.ModuleLWE.realGame_eq_uniform_bind`, `Cslib.Crypto.ModuleLWE.randomGame_eq`: the
  games with the matrix drawn first and with one uniform pair, as key generation draws them.
* `Cslib.Crypto.decisionModuleLWEWith_iff_encoded`: `DecisionModuleLWEWith` is the word-level
  assumption.
* `Cslib.Crypto.decisionModuleLWE_iff_decisionModuleLWEWith`: `DecisionModuleLWE` is the case of a
  uniform secret.

## References

* [V. Lyubashevsky, C. Peikert and O. Regev, *On Ideal Lattices and Learning with Errors over
  Rings*][LyubashevskyPeikertRegev2010]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
* [R. Avanzi et al., *CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation
  (version 3.02)*][AvanziEtAl2021], 4 August 2021, §4.3 (p. 19) and §4.4 (pp. 21–22)
* [S. Bai et al., *CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation
  (Version 3.1)*][BaiEtAl2021], 8 February 2021, §6.1 (p. 23) and §6.2 (p. 24)
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal

namespace ModuleLWE

/-! ### Samples -/

/-- Deterministic Module-LWE noisy linear map `A · s + e` over `ℤ_q[X] / (X^n + 1)`. -/
def sample {m d n q : ℕ}
    (A : Matrix (Fin m) (Fin d) (Fin n → ZMod q))
    (s : Fin d → Fin n → ZMod q)
    (e : Fin m → Fin n → ZMod q) : Fin m → Fin n → ZMod q :=
  moduleSISMap A s + e

/-- **Structured-to-unstructured Module-LWE identity**: flattening `ModuleLWE.sample A s e` gives
the standard LWE vector `expandModuleMatrix A *ᵥ flattenPolyVec s + flattenPolyVec e`. -/
theorem flattenPolyVec_sample {m d n q : ℕ}
    (A : Matrix (Fin m) (Fin d) (Fin n → ZMod q))
    (s : Fin d → Fin n → ZMod q)
    (e : Fin m → Fin n → ZMod q) :
    flattenPolyVec (sample A s e) =
      expandModuleMatrix A *ᵥ flattenPolyVec s + flattenPolyVec e := by
  rw [sample, flattenPolyVec_add, expandModuleMatrix_mulVec]

/-- A Module-LWE sample is the LWE sample `A *ᵥ s + e` over `Negacyclic (ZMod q) n`. -/
theorem ofCoeffs_comp_sample {m d n q : ℕ}
    (A : Matrix (Fin m) (Fin d) (Fin n → ZMod q))
    (s : Fin d → Fin n → ZMod q)
    (e : Fin m → Fin n → ZMod q) :
    Negacyclic.ofCoeffs ∘ sample A s e =
      A.map Negacyclic.ofCoeffs *ᵥ (Negacyclic.ofCoeffs ∘ s) + Negacyclic.ofCoeffs ∘ e := by
  rw [← ofCoeffs_comp_moduleSISMap]
  rfl

/-- Encode a Module-LWE public pair `(A, b)` as a framed pair of the encoded module matrix `A`
and the framed list of natural residue coefficients of `b`. -/
def encodeSample {m d n q : ℕ}
    (pair : Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q)) : List Bool :=
  encPair encBits (encList encNat)
    (ModuleSIS.encodeMatrix pair.1,
      List.ofFn fun c : Fin (m * n) => (flattenPolyVec pair.2 c).val)

/-- Module-LWE pairs of fixed shape are determined by their encodings when `q ≠ 0`. -/
theorem encodeSample_injective {m d n q : ℕ} [NeZero q] :
    Function.Injective (encodeSample (m := m) (d := d) (n := n) (q := q)) := by
  rintro ⟨A, b⟩ ⟨A', b'⟩ h
  simp only [encodeSample, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, List.ofFn_inj] at h
  obtain ⟨hA, hb⟩ := h
  rw [ModuleSIS.encodeMatrix_injective hA,
    flattenPolyVec_injective (funext fun c => ZMod.val_injective q (congrFun hb c))]

/-! ### Fixed-instance experiments -/

section Experiment

variable {m d n q : ℕ} [NeZero q]

/-- The real decision Module-LWE experiment for the secret `s` and error `e`: draw a uniform
module matrix `A` and run the distinguisher on `A` and `A · s + e`. -/
noncomputable def realExperiment (s : Fin d → Fin n → ZMod q) (e : Fin m → Fin n → ZMod q)
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    Experiment := do
  let A ← ProbComp.uniform (Matrix (Fin m) (Fin d) (Fin n → ZMod q))
  distinguisher A (sample A s e)

/-- The random decision Module-LWE experiment: run the distinguisher on a uniform module matrix
`A` and an independent uniform vector `b`. -/
noncomputable def randomExperiment
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    Experiment := do
  let A ← ProbComp.uniform (Matrix (Fin m) (Fin d) (Fin n → ZMod q))
  let b ← ProbComp.uniform (Fin m → Fin n → ZMod q)
  distinguisher A b

@[simp] theorem eval_realExperiment (s : Fin d → Fin n → ZMod q) (e : Fin m → Fin n → ZMod q)
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ProbComp.eval (realExperiment s e distinguisher) =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (Fin n → ZMod q))).bind fun A =>
        ProbComp.eval (distinguisher A (sample A s e)) := by
  simp [realExperiment]

@[simp] theorem eval_randomExperiment
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ProbComp.eval (randomExperiment distinguisher) =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (Fin n → ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → Fin n → ZMod q)).bind fun b =>
          ProbComp.eval (distinguisher A b) := by
  simp [randomExperiment]

/-- The real decision Module-LWE game for a secret law and an error law: draw `s ← secretLaw` and
`e ← errorLaw`, then run `realExperiment s e`. -/
noncomputable def realGame (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q))
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    Game := do
  let s ← secretLaw
  let e ← errorLaw
  ProbComp.eval (realExperiment s e distinguisher)

/-- The random decision Module-LWE game: run `randomExperiment`. -/
noncomputable def randomGame
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    Game :=
  ProbComp.eval (randomExperiment distinguisher)

/-- The decision Module-LWE advantage of a distinguisher for a secret law and an error law. -/
noncomputable def advantage (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q))
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ℝ≥0 :=
  Game.advantage (realGame secretLaw errorLaw distinguisher) (randomGame distinguisher)

/-- The real game with the matrix drawn first, as key generation draws it. -/
theorem realGame_eq_uniform_bind (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q))
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    realGame secretLaw errorLaw distinguisher =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (Fin n → ZMod q))).bind fun A =>
        secretLaw.bind fun s => errorLaw.bind fun e =>
          ProbComp.eval (distinguisher A (sample A s e)) := by
  simp only [realGame, eval_realExperiment, PMF.monad_bind_eq_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype _) secretLaw]
  exact congrArg _ (funext fun s => PMF.bind_comm _ _ _)

/-- The random game draws one uniform pair. -/
theorem randomGame_eq
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    randomGame distinguisher =
      (PMF.uniformOfFintype
        (Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q))).bind fun p =>
          ProbComp.eval (distinguisher p.1 p.2) := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [randomGame, eval_randomExperiment, PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- The real game depends on the distinguisher only through its output distributions. -/
theorem realGame_congr {secretLaw : PMF (Fin d → Fin n → ZMod q)}
    {errorLaw : PMF (Fin m → Fin n → ZMod q)}
    {D D' : Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool}
    (h : ∀ A b, ProbComp.eval (D A b) = ProbComp.eval (D' A b)) :
    realGame secretLaw errorLaw D = realGame secretLaw errorLaw D' := by
  simp only [realGame, eval_realExperiment, h]

/-- The random game depends on the distinguisher only through its output distributions. -/
theorem randomGame_congr
    {D D' : Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool}
    (h : ∀ A b, ProbComp.eval (D A b) = ProbComp.eval (D' A b)) :
    randomGame D = randomGame D' := by
  simp only [randomGame, eval_randomExperiment, h]

/-! ### Module-LWE is LWE over the negacyclic ring -/

/-- A uniform matrix over `Negacyclic (ZMod q) n` is the coefficientwise image of a uniform
module matrix. -/
private theorem uniformOfFintype_map_ofCoeffs {r c : ℕ} :
    (PMF.uniformOfFintype (Matrix (Fin r) (Fin c) (Fin n → ZMod q))).map
        (Matrix.map · Negacyclic.ofCoeffs) =
      PMF.uniformOfFintype (Matrix (Fin r) (Fin c) (Negacyclic (ZMod q) n)) :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv Negacyclic.coeffsEquiv.symm.mapMatrix

/-- A uniform vector over `Negacyclic (ZMod q) n` is the coefficientwise image of a uniform
polynomial vector. -/
private theorem uniformOfFintype_map_comp_ofCoeffs {r : ℕ} :
    (PMF.uniformOfFintype (Fin r → Fin n → ZMod q)).map (Negacyclic.ofCoeffs ∘ ·) =
      PMF.uniformOfFintype (Fin r → Negacyclic (ZMod q) n) :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv
    (Equiv.arrowCongr (Equiv.refl _) Negacyclic.coeffsEquiv.symm)

/-- The real experiment is the LWE real experiment over the ring for the coefficientwise images,
against the distinguisher that reads coefficients. -/
private theorem eval_realExperiment_eq_lwe (s : Fin d → Fin n → ZMod q)
    (e : Fin m → Fin n → ZMod q)
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ProbComp.eval (realExperiment s e distinguisher) =
      ProbComp.eval (LWE.realExperiment (Negacyclic.ofCoeffs ∘ s) (Negacyclic.ofCoeffs ∘ e)
        fun A b => distinguisher (A.map Negacyclic.coeffs) (Negacyclic.coeffs ∘ b)) := by
  rw [eval_realExperiment, LWE.eval_realExperiment, ← uniformOfFintype_map_ofCoeffs, PMF.bind_map]
  refine congrArg _ (funext fun A => ?_)
  simp only [Function.comp_apply]
  rw [← ofCoeffs_comp_sample]
  rfl

/-- The random experiment is the LWE random experiment over the ring, against the distinguisher
that reads coefficients. -/
private theorem eval_randomExperiment_eq_lwe
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ProbComp.eval (randomExperiment distinguisher) =
      ProbComp.eval (LWE.randomExperiment
        fun A b => distinguisher (A.map Negacyclic.coeffs) (Negacyclic.coeffs ∘ b)) := by
  rw [eval_randomExperiment, LWE.eval_randomExperiment, ← uniformOfFintype_map_ofCoeffs,
    ← uniformOfFintype_map_comp_ofCoeffs, PMF.bind_map]
  refine congrArg _ (funext fun A => ?_)
  simp only [Function.comp_apply, PMF.bind_map]
  rfl

/-- **Module-LWE is LWE over `Negacyclic (ZMod q) n`.** The Module-LWE advantage for a secret
law and an error law is the LWE advantage over the ring for their coefficientwise images, against
the distinguisher that reads coefficients. -/
theorem advantage_eq_lweAdvantage (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q))
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    advantage secretLaw errorLaw distinguisher =
      LWE.advantage (secretLaw.map (Negacyclic.ofCoeffs ∘ ·))
        (errorLaw.map (Negacyclic.ofCoeffs ∘ ·))
        (fun A b => distinguisher (A.map Negacyclic.coeffs) (Negacyclic.coeffs ∘ b)) := by
  simp only [advantage, LWE.advantage, realGame, LWE.realGame, randomGame, LWE.randomGame,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, eval_realExperiment_eq_lwe,
    eval_randomExperiment_eq_lwe]

end Experiment

/-! ### Encoded samples -/

/-- Draw a Module-LWE sample `(A, A · s + e)` with secret `s ← secretLaw`, uniform `A` and error
vector `e ← errorLaw`. -/
noncomputable def sampleLaw {m d n q : ℕ} [NeZero q] (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q)) :
    PMF (Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q)) := do
  let secret ← secretLaw
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (Fin n → ZMod q))
  let error ← errorLaw
  return (A, sample A secret error)

/-- Encoded real Module-LWE ensemble at each security parameter, for the secret law `secret κ` and
the error law `error κ`. -/
noncomputable def realEnsemble (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))) (κ : ℕ) : PMF (List Bool) :=
  (sampleLaw (secret κ) (error κ)).map encodeSample

/-- Encoded uniform comparison ensemble `(A, u)` with independent uniform `A` and `u`. -/
noncomputable def uniformEnsemble (m d n q : ℕ → ℕ)
    [∀ security, NeZero (q security)]
    (security : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype
    (Matrix (Fin (m security)) (Fin (d security)) (Fin (n security) → ZMod (q security)) ×
      (Fin (m security) → Fin (n security) → ZMod (q security)))).map encodeSample

/-! ### Distinguishers -/

variable (m d n q : ℕ → ℕ)

/-- The input of a decision Module-LWE distinguisher with an `m κ × d κ` module matrix over
`ℤ_{q κ}[X] / (X^{n κ} + 1)`: the security parameter `κ`, a module matrix `A` and a vector `b`,
which is `A · s + e` in the real experiment and uniform in the random one. -/
structure Input where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The public module matrix. -/
  matrix : Matrix (Fin (m secParam)) (Fin (d secParam)) (Fin (n secParam) → ZMod (q secParam))
  /-- The target vector. -/
  target : Fin (m secParam) → Fin (n secParam) → ZMod (q secParam)

variable {m d n q}

/-- The words a machine reads for a decision Module-LWE input: the security parameter and the
encoded pair `(A, b)`. -/
def Input.words (x : Input m d n q) : ℕ × List Bool :=
  (x.secParam, encodeSample (x.matrix, x.target))

/-- A decision Module-LWE input is determined by its words. -/
theorem Input.words_injective [∀ κ, NeZero (q κ)] :
    Function.Injective (Input.words (m := m) (d := d) (n := n) (q := q)) := by
  rintro ⟨κ, A, b⟩ ⟨κ', A', b'⟩ h
  simp only [Input.words, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (encodeSample_injective h)
  rfl

variable (m d n q) [∀ κ, NeZero (q κ)]

/-- The encoding of a decision Module-LWE input: the framed unary security parameter followed by
the encoded pair `(A, b)` (`encInput_apply`). Its sample part is the word `realEnsemble` and
`uniformEnsemble` sample. -/
def encInput : Input m d n q ↪ List Bool :=
  (⟨Input.words, Input.words_injective⟩ : Input m d n q ↪ _).trans (encPair encUnary encBits)

/-- The decision Module-LWE input layout. -/
theorem encInput_apply (x : Input m d n q) :
    encInput m d n q x =
      frame (encUnary x.secParam) ++ encodeSample (x.matrix, x.target) := by
  simp [encInput, Input.words, encPair, encBits]

/-- A decision Module-LWE distinguisher: given the security parameter `κ`, a module matrix `A`
and a vector `b` of the shape, degree and modulus at `κ`, it outputs a bit.
`Distinguisher.IsPPT` states its efficiency on encodings. -/
abbrev Distinguisher : Type :=
  (κ : ℕ) → Matrix (Fin (m κ)) (Fin (d κ)) (Fin (n κ) → ZMod (q κ)) →
    (Fin (m κ) → Fin (n κ) → ZMod (q κ)) → ProbComp Bool

variable {m d n q} in
/-- A decision Module-LWE distinguisher is PPT when one uniform strict PPT machine reads
`encInput` and writes the distinguisher's output bit. -/
def Distinguisher.IsPPT (D : Distinguisher m d n q) : Prop :=
  IsPPTOn (encInput m d n q) encBool fun x => D x.secParam x.matrix x.target

/-! ### Word-level distinguishers -/

variable {m d n q}

/-- The typed distinguisher that runs a word-level distinguisher on the encoded pair `(A, b)`. -/
def Distinguisher.ofWords (W : Crypto.Distinguisher) : Distinguisher m d n q :=
  fun κ A b => W κ (encodeSample (A, b))

/-- A word-level distinguisher on the encoded real sample runs the real game for the same laws. -/
theorem distinguishingGame_realEnsemble
    (secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))) (W : Crypto.Distinguisher)
    (κ : ℕ) :
    distinguishingGame (realEnsemble m d n q secret error κ) (W κ) =
      realGame (secret κ) (error κ) (Distinguisher.ofWords W κ) := by
  simp only [distinguishingGame_eq_bind, realEnsemble, sampleLaw, realGame, eval_realExperiment,
    Distinguisher.ofWords, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
    PMF.pure_bind, PMF.bind_bind, Function.comp_def]
  congr 1 with s
  rw [PMF.bind_comm]

/-- A word-level distinguisher on the encoded uniform sample runs the random game. -/
theorem distinguishingGame_uniformEnsemble (W : Crypto.Distinguisher) (κ : ℕ) :
    distinguishingGame (uniformEnsemble m d n q κ) (W κ) =
      randomGame (Distinguisher.ofWords (m := m) (d := d) (n := n) (q := q) W κ) := by
  simp only [distinguishingGame_eq_bind, uniformEnsemble, randomGame_eq, Distinguisher.ofWords,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]

end ModuleLWE

/-- The decision Module-LWE assumption with an `m κ × d κ` module matrix over
`ℤ_{q κ}[X] / (X^{n κ} + 1)`, secret law `secret κ` and error law `error κ`: every PPT
distinguisher has negligible advantage between `ModuleLWE.realGame (secret κ) (error κ)` and
`ModuleLWE.randomGame`.

With short laws this is the assumption of the CRYSTALS submissions, in asymptotic form. Kyber v3.02
([AvanziEtAl2021], §4.3, p. 19) defines `Adv^mlwe_{m,k,η}` with `(s, e) ← β_η^k × β_η^m` for the
centered binomial law `β_η`, and its Module-LWER problem without compression (§4.4 and footnote 3,
pp. 21–22) draws `s ← β_{η₁}^k` and `e ← β_{η₂}^m`. Dilithium v3.1 ([BaiEtAl2021], §6.1, p. 23)
defines `MLWE_{m,k,D}` with `s₁ ← D^k` and `s₂ ← D^m`, and §6.2, eq. (6), p. 24 takes `D` uniform
on `S_η`. The sources define concrete advantages and take them to be small at their parameter
sets; here every uniform classical strict PPT distinguisher has negligible advantage over the
family. This is a hypothesis, not a theorem of hardness for any laws, and makes no claim about
quantum adversaries; with uniform errors it holds trivially.

The assumption is meaningful only for a family whose parameters grow with `κ`. When `m`, `d`, `n`,
`q` and the laws do not depend on `κ`, as at any FIPS 203 or FIPS 204 parameter set, the real and
random games are two fixed distributions. Unless the real sample is exactly uniform, a
polynomial-time distinguisher that looks the sample up in a fixed finite table has constant
advantage, so the assumption fails. -/
def DecisionModuleLWEWith (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))) : Prop :=
  Game.Indistinguishable
    (fun (D : ModuleLWE.Distinguisher m d n q) κ =>
      ModuleLWE.realGame (secret κ) (error κ) (D κ))
    (fun D κ => ModuleLWE.randomGame (D κ)) ModuleLWE.Distinguisher.IsPPT

/-- The decision Module-LWE assumption with an `m κ × d κ` module matrix over
`ℤ_{q κ}[X] / (X^{n κ} + 1)` and error law `noise κ` for each polynomial: every PPT distinguisher
has negligible advantage between `ModuleLWE.realGame`, with a uniform secret and independent
errors, and `ModuleLWE.randomGame`. It is `DecisionModuleLWEWith` for these laws
(`decisionModuleLWE_iff_decisionModuleLWEWith`). This is a hypothesis against uniform classical
strict PPT distinguishers, not a theorem of hardness or a claim about quantum adversaries. -/
def DecisionModuleLWE (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (noise : (κ : ℕ) → PMF (Fin (n κ) → ZMod (q κ))) : Prop :=
  DecisionModuleLWEWith m d n q (fun κ => PMF.uniformOfFintype (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
    fun κ => PMF.pi fun _ : Fin (m κ) => noise κ

/-- `DecisionModuleLWE` is `DecisionModuleLWEWith` for a uniform secret and independent polynomial
errors drawn from `noise κ`. -/
theorem decisionModuleLWE_iff_decisionModuleLWEWith (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (noise : (κ : ℕ) → PMF (Fin (n κ) → ZMod (q κ))) :
    DecisionModuleLWE m d n q noise ↔
      DecisionModuleLWEWith m d n q
        (fun κ => PMF.uniformOfFintype (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
        fun κ => PMF.pi fun _ : Fin (m κ) => noise κ :=
  Iff.rfl

/-- **`DecisionModuleLWEWith` is the word-level decision Module-LWE assumption.** Quantifying over
distinguishers that read the encoded sample as a word gives the same assumption as quantifying
over typed distinguishers. A typed distinguisher's machine reads exactly that word; conversely, a
word distinguisher is typed by encoding its input, and a typed one extends to all words by
rerunning its machine (`IsPPTOn.exists_bool_extension`), since its output is a single bit. -/
theorem decisionModuleLWEWith_iff_encoded (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))) :
    DecisionModuleLWEWith m d n q secret error ↔
      ComputationallyIndistinguishable (ModuleLWE.realEnsemble m d n q secret error)
        (ModuleLWE.uniformEnsemble m d n q) := by
  constructor
  · intro h W hW
    have hD : (ModuleLWE.Distinguisher.ofWords W : ModuleLWE.Distinguisher m d n q).IsPPT :=
      hW.on.preprocess (prepare := ModuleLWE.Input.words) (ComputableInPolyTime.of_eq fun _ => rfl)
    simpa only [ModuleLWE.distinguishingGame_realEnsemble,
      ModuleLWE.distinguishingGame_uniformEnsemble] using h _ hD
  · intro h D hD
    obtain ⟨W, hWppt, hW⟩ := hD.exists_bool_extension
    let W' : Distinguisher := fun κ word => W (encPair encUnary encBits (κ, word))
    have hW' : IsPPT encBool W' := hWppt.preprocess ComputableInPolyTime.id'.encoding_comp
    have hgame (κ : ℕ) (A : Matrix (Fin (m κ)) (Fin (d κ)) (Fin (n κ) → ZMod (q κ)))
        (b : Fin (m κ) → Fin (n κ) → ZMod (q κ)) :
        ProbComp.eval (ModuleLWE.Distinguisher.ofWords W' κ A b) = ProbComp.eval (D κ A b) :=
      hW ⟨κ, A, b⟩
    have hneg := h W' hW'
    simpa only [ModuleLWE.distinguishingGame_realEnsemble secret error W',
      ModuleLWE.distinguishingGame_uniformEnsemble W', ModuleLWE.realGame_congr (hgame _),
      ModuleLWE.randomGame_congr (hgame _)] using hneg

/-- Under `DecisionModuleLWEWith`, the encoded real and uniform samples are computationally
indistinguishable to word-level distinguishers. -/
theorem DecisionModuleLWEWith.encoded {m d n q : ℕ → ℕ} [∀ κ, NeZero (q κ)]
    {secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ))}
    {error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))}
    (h : DecisionModuleLWEWith m d n q secret error) :
    ComputationallyIndistinguishable (ModuleLWE.realEnsemble m d n q secret error)
      (ModuleLWE.uniformEnsemble m d n q) :=
  (decisionModuleLWEWith_iff_encoded m d n q secret error).mp h

end Cslib.Crypto
