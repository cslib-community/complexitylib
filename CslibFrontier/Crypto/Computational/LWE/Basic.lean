/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Game.Experiment
public import CslibFrontier.Foundations.Data.Matrix.Binary
public import CslibFrontier.Probability.Product
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Probability.PMF.Uniform

/-!
# Decision LWE

The decision learning-with-errors experiments over a finite commutative ring `R`
([Regev2009], [GentrySahaiWaters2013], Section 2): the real experiment `LWE.realExperiment`
draws a uniform matrix `A` and gives the distinguisher `A` and `A *ᵥ s + e` for a secret `s` and
an error vector `e`; the random experiment `LWE.randomExperiment` gives it a uniform pair. For a
secret law and an error law, the real game `LWE.realGame` draws `s` and `e` and runs the real
experiment, `LWE.randomGame` runs the random one, and `LWE.advantage` is the distance between them.

`DecisionLWE n m w noise` is the asymptotic assumption at modulus `2 ^ w κ`, with `n κ` secret
coordinates and `m κ` samples: every distinguisher that is uniform strict PPT on encodings
(`LWE.Distinguisher.IsPPT`) has negligible advantage between the real game with a uniform secret
and independent errors from `noise κ` and the random game. A distinguisher machine reads the unary
security parameter and the row-major binary word of the matrix `[b | A]` (`LWE.encInput_apply`).

A distinguisher outputs a bit, so `DecisionLWE` is the same assumption as the indistinguishability
of the encoded real and uniform matrices `LWE.realEnsemble` and `LWE.uniformEnsemble` against
word-level distinguishers (`decisionLWE_iff_encoded`). Clients that reduce on encoded words use
`DecisionLWE.encoded`.

`DecisionLWE` is a hypothesis against uniform classical strict polynomial-time programs. It makes no
assertion of hardness for any particular parameter or error family. In particular, using a bounded
noise distribution does not identify it with a discrete Gaussian or establish a worst-case lattice
reduction.

## Main definitions

* `Cslib.Crypto.LWE.realExperiment`, `Cslib.Crypto.LWE.randomExperiment`: the fixed-instance
  experiments over a finite commutative ring.
* `Cslib.Crypto.LWE.realGame`, `Cslib.Crypto.LWE.randomGame`, `Cslib.Crypto.LWE.advantage`: the
  games and advantage for a secret law and an error law.
* `Cslib.Crypto.LWE.augmentedMatrix`: the matrix `[b | A]` of an LWE sample.
* `Cslib.Crypto.LWE.Input`, `Cslib.Crypto.LWE.encInput`: the input of a distinguisher at modulus
  `2 ^ w κ` and its encoding.
* `Cslib.Crypto.LWE.Distinguisher`, `Cslib.Crypto.LWE.Distinguisher.IsPPT`: typed distinguishers
  and their efficiency.
* `Cslib.Crypto.DecisionLWE`: the decision-LWE assumption.
* `Cslib.Crypto.DecisionLWEWithErrors`: the same assumption with a joint law on the error vector.
* `Cslib.Crypto.LWE.publicMatrix`, `Cslib.Crypto.LWE.publicMatrixLaw`: the matrix `[B * t + e | B]`
  and its law, as produced by key generation.
* `Cslib.Crypto.LWE.realEnsemble`, `Cslib.Crypto.LWE.uniformEnsemble`: the encoded matrices.

## Main results

* `Cslib.Crypto.decisionLWE_iff_encoded`: `DecisionLWE` is the word-level assumption.
* `Cslib.Crypto.decisionLWE_iff_decisionLWEWithErrors`: `DecisionLWE` is the case of independent
  error coordinates.
* `Cslib.Crypto.LWE.realGame_uniform_error_eq_randomGame`,
  `Cslib.Crypto.LWE.advantage_uniform_error_eq_zero`: with uniform errors the real game is the
  random game, so every distinguisher has advantage `0`.
* `Cslib.Crypto.LWE.uniformOfFintype_augmentedMatrix`: `[b | A]` of a uniform pair is uniform.
* `Cslib.Crypto.LWE.length_of_mem_support_realEnsemble`: every real sample has the declared length.
* `Cslib.Crypto.LWE.length_of_mem_support_uniformEnsemble`: the comparison uses the same length.

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and
  cryptography*][Regev2009]
* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 2][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal

namespace LWE

/-! ### Encoded matrices -/

/-- The deterministic LWE public matrix `[B * t + error | B]`. -/
def publicMatrix {n m w : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (t : Fin n → ZMod (2 ^ w)) (error : Fin m → ZMod (2 ^ w)) :
    Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) :=
  fun i => Fin.cons ((B *ᵥ t) i + error i) (B i)

/-- Draw the public matrix `[B * t + e | B]`. The errors are independent of one another, of
the uniform matrix, and of the uniform secret shared by all rows. -/
noncomputable def publicMatrixLaw (n m w : ℕ) (noise : PMF (ZMod (2 ^ w))) :
    PMF (Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) := do
  let secret ← PMF.uniformOfFintype (Fin n → ZMod (2 ^ w))
  let publicPart ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
  let error ← PMF.pi (fun _ : Fin m => noise)
  return publicMatrix publicPart secret error

/-- Binary decision-LWE samples, using `w` bits per residue and a uniform secret. -/
noncomputable def realEnsemble (n m w : ℕ → ℕ)
    (noise : (security : ℕ) → PMF (ZMod (2 ^ w security))) (security : ℕ) : PMF (List Bool) :=
  (publicMatrixLaw (n security) (m security) (w security) (noise security)).map Matrix.toBinary

/-- Encode a uniform matrix with exactly the real experiment's dimensions and modulus. -/
noncomputable def uniformEnsemble (n m w : ℕ → ℕ) (security : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype
    (Matrix (Fin (m security)) (Fin (n security + 1)) (ZMod (2 ^ w security)))).map Matrix.toBinary

/-- The real public word contains exactly one fixed-width residue for each matrix entry. -/
theorem length_of_mem_support_realEnsemble {n m w : ℕ → ℕ}
    {noise : (security : ℕ) → PMF (ZMod (2 ^ w security))} {security : ℕ} {word : List Bool}
    (h : word ∈ (realEnsemble n m w noise security).support) :
    word.length = m security * (n security + 1) * w security := by
  obtain ⟨A, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact Matrix.length_toBinary A

/-- Uniform public words have the same complete serialized length as real public words. -/
theorem length_of_mem_support_uniformEnsemble {n m w : ℕ → ℕ} {security : ℕ} {word : List Bool}
    (h : word ∈ (uniformEnsemble n m w security).support) :
    word.length = m security * (n security + 1) * w security := by
  obtain ⟨A, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact Matrix.length_toBinary A

/-! ### Fixed-instance experiments -/

section Experiment

variable {R : Type} [CommRing R] [Fintype R] {n m : ℕ}

/-- The real decision-LWE experiment for the secret `s` and error `e`: draw a uniform matrix `A`
and run the distinguisher on `A` and `A *ᵥ s + e`. -/
noncomputable def realExperiment (s : Fin n → R) (e : Fin m → R)
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) : Experiment := do
  let A ← ProbComp.uniform (Matrix (Fin m) (Fin n) R)
  distinguisher A (A *ᵥ s + e)

/-- The random decision-LWE experiment: run the distinguisher on a uniform matrix `A` and an
independent uniform vector `b`. -/
noncomputable def randomExperiment
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) : Experiment := do
  let A ← ProbComp.uniform (Matrix (Fin m) (Fin n) R)
  let b ← ProbComp.uniform (Fin m → R)
  distinguisher A b

@[simp] theorem eval_realExperiment (s : Fin n → R) (e : Fin m → R)
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) :
    ProbComp.eval (realExperiment s e distinguisher) =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) R)).bind fun A =>
        ProbComp.eval (distinguisher A (A *ᵥ s + e)) := by
  simp [realExperiment]

@[simp] theorem eval_randomExperiment
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) :
    ProbComp.eval (randomExperiment distinguisher) =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) R)).bind fun A =>
        (PMF.uniformOfFintype (Fin m → R)).bind fun b => ProbComp.eval (distinguisher A b) := by
  simp [randomExperiment]

/-- The real decision-LWE game for a secret law and an error law: draw `s ← secretLaw` and
`e ← errorLaw`, then run `realExperiment s e`. -/
noncomputable def realGame (secretLaw : PMF (Fin n → R)) (errorLaw : PMF (Fin m → R))
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) : Game := do
  let s ← secretLaw
  let e ← errorLaw
  ProbComp.eval (realExperiment s e distinguisher)

/-- The random decision-LWE game: run `randomExperiment`. -/
noncomputable def randomGame
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) : Game :=
  ProbComp.eval (randomExperiment distinguisher)

/-- The decision-LWE advantage of a distinguisher for a secret law and an error law. -/
noncomputable def advantage (secretLaw : PMF (Fin n → R)) (errorLaw : PMF (Fin m → R))
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (realGame secretLaw errorLaw distinguisher) (randomGame distinguisher)

/-- The real game depends on the distinguisher only through its output distributions. -/
theorem realGame_congr {secretLaw : PMF (Fin n → R)} {errorLaw : PMF (Fin m → R)}
    {D D' : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool}
    (h : ∀ A b, ProbComp.eval (D A b) = ProbComp.eval (D' A b)) :
    realGame secretLaw errorLaw D = realGame secretLaw errorLaw D' := by
  simp only [realGame, eval_realExperiment, h]

/-- The random game depends on the distinguisher only through its output distributions. -/
theorem randomGame_congr {D D' : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool}
    (h : ∀ A b, ProbComp.eval (D A b) = ProbComp.eval (D' A b)) :
    randomGame D = randomGame D' := by
  simp only [randomGame, eval_randomExperiment, h]

/-- With uniform errors the real game is the random game, for every secret law: `A *ᵥ s + e` is
uniform and independent of `(A, s)`. -/
theorem realGame_uniform_error_eq_randomGame (secretLaw : PMF (Fin n → R))
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) :
    realGame secretLaw (PMF.uniformOfFintype (Fin m → R)) distinguisher =
      randomGame distinguisher := by
  simp only [realGame, randomGame, eval_realExperiment, eval_randomExperiment,
    PMF.monad_bind_eq_bind]
  refine Eq.trans ?_ (PMF.bind_const secretLaw _)
  congr 1 with s : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin m → R))]
  congr 1 with A : 1
  exact Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addLeft (A *ᵥ s))
    fun b => ProbComp.eval (distinguisher A b)

/-- With uniform errors every distinguisher has advantage `0`, for every secret law. -/
theorem advantage_uniform_error_eq_zero (secretLaw : PMF (Fin n → R))
    (distinguisher : Matrix (Fin m) (Fin n) R → (Fin m → R) → ProbComp Bool) :
    advantage secretLaw (PMF.uniformOfFintype (Fin m → R)) distinguisher = 0 := by
  rw [advantage, realGame_uniform_error_eq_randomGame, Game.advantage_self]

end Experiment

/-! ### The matrix of a sample -/

section Augmented

variable {R : Type} {n m : ℕ}

/-- The matrix `[b | A]` of an LWE sample: row `i` is `b i` followed by row `i` of `A`. -/
def augmentedMatrix (A : Matrix (Fin m) (Fin n) R) (b : Fin m → R) :
    Matrix (Fin m) (Fin (n + 1)) R :=
  fun i => Fin.cons (b i) (A i)

/-- Splitting off the first column identifies pairs `(A, b)` with matrices `[b | A]`. -/
def augmentedMatrixEquiv :
    Matrix (Fin m) (Fin n) R × (Fin m → R) ≃ Matrix (Fin m) (Fin (n + 1)) R where
  toFun p := augmentedMatrix p.1 p.2
  invFun M := (fun i j => M i j.succ, fun i => M i 0)
  left_inv p := by ext <;> simp [augmentedMatrix]
  right_inv M := by
    ext i j
    induction j using Fin.cases <;> simp [augmentedMatrix]

@[simp] theorem augmentedMatrixEquiv_apply (p : Matrix (Fin m) (Fin n) R × (Fin m → R)) :
    augmentedMatrixEquiv p = augmentedMatrix p.1 p.2 := rfl

/-- `[b | A]` determines `A` and `b`. -/
theorem augmentedMatrix_inj {A A' : Matrix (Fin m) (Fin n) R} {b b' : Fin m → R} :
    augmentedMatrix A b = augmentedMatrix A' b' ↔ A = A' ∧ b = b' := by
  rw [← Prod.mk.injEq]
  exact augmentedMatrixEquiv.injective.eq_iff (a := (A, b)) (b := (A', b'))

/-- `[b | A]` for a uniform matrix `A` and an independent uniform vector `b` is uniform. -/
theorem uniformOfFintype_augmentedMatrix [Zero R] [Fintype R] :
    ((PMF.uniformOfFintype (Matrix (Fin m) (Fin n) R)).bind fun A =>
      (PMF.uniformOfFintype (Fin m → R)).map fun b => augmentedMatrix A b) =
      PMF.uniformOfFintype (Matrix (Fin m) (Fin (n + 1)) R) := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv augmentedMatrixEquiv,
    ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, augmentedMatrixEquiv_apply]

end Augmented

/-- The public matrix `[B * t + e | B]` is the matrix of the sample `(B, B *ᵥ t + e)`. -/
theorem publicMatrix_eq_augmentedMatrix {n m w : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (t : Fin n → ZMod (2 ^ w)) (e : Fin m → ZMod (2 ^ w)) :
    publicMatrix B t e = augmentedMatrix B (B *ᵥ t + e) :=
  rfl

/-! ### Distinguishers at modulus `2 ^ w` -/

variable (n m w : ℕ → ℕ)

/-- The input of a decision-LWE distinguisher with `n κ` secret coordinates, `m κ` samples and
modulus `2 ^ w κ`: the security parameter `κ`, a matrix `A` and a vector `b`, which is
`A *ᵥ s + e` in the real experiment and uniform in the random one. -/
structure Input where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The public matrix. -/
  matrix : Matrix (Fin (m secParam)) (Fin (n secParam)) (ZMod (2 ^ w secParam))
  /-- The target vector. -/
  target : Fin (m secParam) → ZMod (2 ^ w secParam)

variable {n m w}

/-- The words a machine reads for a decision-LWE input: the security parameter and the binary
word of the matrix `[b | A]`. -/
def Input.words (x : Input n m w) : ℕ × List Bool :=
  (x.secParam, Matrix.toBinary (augmentedMatrix x.matrix x.target))

/-- A decision-LWE input is determined by its words. -/
theorem Input.words_injective : Function.Injective (Input.words (n := n) (m := m) (w := w)) := by
  rintro ⟨κ, A, b⟩ ⟨κ', A', b'⟩ h
  simp only [Input.words, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have h := congrArg (Matrix.ofBinary (m κ) (n κ + 1) (w κ)) h
  simp only [Matrix.ofBinary_toBinary, augmentedMatrix_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

variable (n m w)

/-- The encoding of a decision-LWE input: the framed unary security parameter followed by the
row-major binary word of `[b | A]` (`encInput_apply`). Its matrix part is the word `realEnsemble`
and `uniformEnsemble` sample. -/
def encInput : Input n m w ↪ List Bool :=
  (⟨Input.words, Input.words_injective⟩ : Input n m w ↪ _).trans (encPair encUnary encBits)

/-- The decision-LWE input layout. -/
theorem encInput_apply (x : Input n m w) :
    encInput n m w x =
      frame (encUnary x.secParam) ++ Matrix.toBinary (augmentedMatrix x.matrix x.target) := by
  simp [encInput, Input.words, encPair, encBits]

/-- A decision-LWE distinguisher: given the security parameter `κ`, a matrix `A` and a vector `b`
of the dimensions and modulus at `κ`, it outputs a bit. `Distinguisher.IsPPT` states its
efficiency on encodings. -/
abbrev Distinguisher : Type :=
  (κ : ℕ) → Matrix (Fin (m κ)) (Fin (n κ)) (ZMod (2 ^ w κ)) → (Fin (m κ) → ZMod (2 ^ w κ)) →
    ProbComp Bool

variable {n m w} in
/-- A decision-LWE distinguisher is PPT when one uniform strict PPT machine reads `encInput` and
writes the distinguisher's output bit. -/
def Distinguisher.IsPPT (D : Distinguisher n m w) : Prop :=
  IsPPTOn (encInput n m w) encBool fun x => D x.secParam x.matrix x.target

/-! ### Word-level distinguishers -/

variable {n m w}

/-- The typed distinguisher that runs a word-level distinguisher on the binary word of `[b | A]`. -/
def Distinguisher.ofWords (W : Crypto.Distinguisher) : Distinguisher n m w :=
  fun κ A b => W κ (Matrix.toBinary (augmentedMatrix A b))

/-- A word-level distinguisher on the encoded real matrix runs the real game with a uniform secret
and independent errors from `noise κ`. -/
theorem distinguishingGame_realEnsemble (noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ)))
    (W : Crypto.Distinguisher) (κ : ℕ) :
    distinguishingGame (realEnsemble n m w noise κ) (W κ) =
      realGame (PMF.uniformOfFintype (Fin (n κ) → ZMod (2 ^ w κ)))
        (PMF.pi fun _ : Fin (m κ) => noise κ) (Distinguisher.ofWords W κ) := by
  simp only [distinguishingGame_eq_bind, realEnsemble, publicMatrixLaw, realGame,
    eval_realExperiment, Distinguisher.ofWords, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_map, PMF.pure_bind, PMF.bind_bind, Function.comp_def]
  congr 1 with s
  rw [PMF.bind_comm]
  rfl

/-- A word-level distinguisher on the encoded uniform matrix runs the random game. -/
theorem distinguishingGame_uniformEnsemble (W : Crypto.Distinguisher) (κ : ℕ) :
    distinguishingGame (uniformEnsemble n m w κ) (W κ) =
      randomGame (Distinguisher.ofWords (n := n) (m := m) (w := w) W κ) := by
  rw [distinguishingGame_eq_bind, uniformEnsemble, ← uniformOfFintype_augmentedMatrix]
  simp only [randomGame, eval_randomExperiment, Distinguisher.ofWords, PMF.monad_bind_eq_bind,
    PMF.bind_map, PMF.bind_bind, Function.comp_def]

end LWE

/-- The decision-LWE assumption with `n κ` secret coordinates, `m κ` samples, modulus `2 ^ w κ`
and a joint law `errors κ` on the whole error vector: every PPT distinguisher has negligible
advantage between `LWE.realGame`, with a uniform secret and an error vector drawn from `errors κ`,
and `LWE.randomGame`. The coordinates of the error vector need not be independent or identically
distributed, which is the form needed when a noisy source supplies the errors, as in the LWE fuzzy
extractor. `DecisionLWE` is the case of independent coordinates. This is a hypothesis against
uniform classical strict PPT distinguishers, not a theorem of hardness or a claim about quantum
adversaries; whether it holds depends on the error laws. -/
def DecisionLWEWithErrors (n m w : ℕ → ℕ)
    (errors : (κ : ℕ) → PMF (Fin (m κ) → ZMod (2 ^ w κ))) : Prop :=
  Game.Indistinguishable
    (fun (D : LWE.Distinguisher n m w) κ =>
      LWE.realGame (PMF.uniformOfFintype (Fin (n κ) → ZMod (2 ^ w κ))) (errors κ) (D κ))
    (fun D κ => LWE.randomGame (D κ)) LWE.Distinguisher.IsPPT

/-- The decision-LWE assumption with `n κ` secret coordinates, `m κ` samples, modulus `2 ^ w κ`
and error law `noise κ` for each coordinate: every PPT distinguisher has negligible advantage
between `LWE.realGame`, with a uniform secret and independent errors, and `LWE.randomGame`. It is
`DecisionLWEWithErrors` for the product error law (`decisionLWE_iff_decisionLWEWithErrors`). This
is a hypothesis against uniform classical strict PPT distinguishers, not a theorem of hardness or a
claim about quantum adversaries. -/
def DecisionLWE (n m w : ℕ → ℕ) (noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ))) : Prop :=
  DecisionLWEWithErrors n m w fun κ => PMF.pi fun _ : Fin (m κ) => noise κ

/-- `DecisionLWE` is `DecisionLWEWithErrors` for the error vector with independent coordinates
drawn from `noise κ`. -/
theorem decisionLWE_iff_decisionLWEWithErrors (n m w : ℕ → ℕ)
    (noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ))) :
    DecisionLWE n m w noise ↔
      DecisionLWEWithErrors n m w fun κ => PMF.pi fun _ : Fin (m κ) => noise κ :=
  Iff.rfl

/-- **`DecisionLWE` is the word-level decision-LWE assumption.** Quantifying over distinguishers
that read the encoded matrix `[b | A]` as a word gives the same assumption as quantifying over
typed distinguishers. A typed distinguisher's machine reads exactly that word; conversely, a word
distinguisher is typed by encoding its input, and a typed one is a word distinguisher run on that
word (`IsPPTOn.exists_bool_factor`), since its output is a single bit. -/
theorem decisionLWE_iff_encoded (n m w : ℕ → ℕ) (noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ))) :
    DecisionLWE n m w noise ↔
      ComputationallyIndistinguishable (LWE.realEnsemble n m w noise)
        (LWE.uniformEnsemble n m w) := by
  constructor
  · intro h W hW
    have hD : (LWE.Distinguisher.ofWords W : LWE.Distinguisher n m w).IsPPT :=
      hW.on.preprocess (prepare := LWE.Input.words) (ComputableInPolyTime.of_eq fun _ => rfl)
    simpa only [LWE.distinguishingGame_realEnsemble, LWE.distinguishingGame_uniformEnsemble]
      using h _ hD
  · intro h D hD
    obtain ⟨W, hW, hWD⟩ := hD.exists_bool_factor (words := encPair encUnary encBits)
      (toWords := LWE.Input.words) fun _ => rfl
    let W' : Distinguisher := fun κ word => W (κ, word)
    obtain rfl : D = LWE.Distinguisher.ofWords W' := funext₃ fun κ A b => hWD ⟨κ, A, b⟩
    simpa only [LWE.distinguishingGame_realEnsemble noise W',
      LWE.distinguishingGame_uniformEnsemble W'] using h W' hW

/-- Under `DecisionLWE`, the encoded real and uniform matrices are computationally
indistinguishable to word-level distinguishers. -/
theorem DecisionLWE.encoded {n m w : ℕ → ℕ} {noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ))}
    (h : DecisionLWE n m w noise) :
    ComputationallyIndistinguishable (LWE.realEnsemble n m w noise) (LWE.uniformEnsemble n m w) :=
  (decisionLWE_iff_encoded n m w noise).mp h

end Cslib.Crypto
