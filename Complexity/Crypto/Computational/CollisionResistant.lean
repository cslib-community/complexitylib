/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.BitString
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Keyed collision-resistant hash families and compression functions

In the uniform PPT model, an unkeyed deterministic function `H : List Bool → List Bool` with
unrestricted inputs (`valid := fun _ _ => true`, or any domain predicate that accepts a fixed pair
at every security parameter `n`) cannot be collision-resistant whenever a single colliding pair
`(m₁, m₂)` exists, because one uniform algorithm can hardcode `(m₁, m₂)` as a constant and win for
every `n`. (In the length-indexed compression setting `validCompressionInput n x :=
(x.length == 2 * n)`, by contrast, a single hardcoded pair has fixed length and is valid at most at
one parameter `n`.) Standard uniform formulations therefore index both compression and hash families
`H : List Bool → List Bool → List Bool` by a public key `k ← {0, 1}^n` sampled uniformly at
security parameter `n`; the adversary receives `(1^n, k)` and wins by outputting a pair `(m₁, m₂)`
of valid inputs with `m₁ ≠ m₂` and `H k m₁ = H k m₂` ([BonehShoup2023], Sections 8.1–8.2;
[KatzLindell2020], Section 5.1).

Parameterizing the experiment by a validity predicate `valid : ℕ → List Bool → Bool` accommodates
both fixed-input-length compression families (`validCompressionInput n x := (x.length == 2 * n)`,
mapping `2n`-bit inputs to `n`-bit outputs under an `n`-bit key) and arbitrary-input-length hash
families (`valid := fun _ _ => true`).

## Main definitions

* `Cslib.Crypto.CollisionFinder`: uniform adversary taking `(n, k)` and outputting candidate
  messages `(m₁, m₂)`.
* `Cslib.Crypto.isCollision`, `Cslib.Crypto.collisionGame`: Boolean collision test and keyed
  collision-finding experiment.
* `Cslib.Crypto.CollisionResistantOn`, `Cslib.Crypto.CollisionResistant`: negligible collision
  probability against every uniform strict PPT adversary.
* `Cslib.Crypto.validCompressionInput`, `Cslib.Crypto.CompressionFamily`: `2n → n` collision-
  resistant compression families.
* `Cslib.Crypto.HashFamily`: unrestricted collision-resistant hash families on arbitrary bit
  strings.

## Main results

* `Cslib.Crypto.isPPTOn_collisionGame`, `Cslib.Crypto.isPPT_collisionGame`: strict PPT certificates
  for the collision experiment.
* `Cslib.Crypto.CollisionResistantOn.negligible`,
  `Cslib.Crypto.CollisionResistantOn.of_negligible`: equivalence with negligible collision-finding
  probability.
* `Cslib.Crypto.succProbability_collisionGame_le_of_extract`,
  `Cslib.Crypto.CollisionResistantOn.of_extract`: deterministic polynomial-time collision
  extraction transfers collision resistance between hash families.
* `Cslib.Crypto.CollisionResistantOn.mono`: restricting the valid input domain preserves collision
  resistance.
* `Cslib.Crypto.not_collisionResistantOn_of_le_succProbability`: finding collisions with
  probability bounded away from zero refutes collision resistance.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.1.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 5.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- A collision finder receives the unary security parameter `n` and public hash key `k` and
outputs a pair `(m₁, m₂)` of candidate colliding messages. -/
abbrev CollisionFinder := ℕ → List Bool → ProbComp (List Bool × List Bool)

/-- Test whether `(m₁, m₂)` is a valid collision for `H k` at security parameter `n` under the
domain predicate `valid`. -/
def isCollision (H : List Bool → List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (n : ℕ) (k m₁ m₂ : List Bool) : Bool :=
  valid n m₁ && valid n m₂ && (m₁ != m₂) && (H k m₁ == H k m₂)

@[simp]
theorem isCollision_eq_true_iff {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {n : ℕ} {k m₁ m₂ : List Bool} :
    isCollision H valid n k m₁ m₂ = true ↔
      valid n m₁ = true ∧ valid n m₂ = true ∧ m₁ ≠ m₂ ∧ H k m₁ = H k m₂ := by
  simp only [isCollision, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc]

/-- Collision testing is symmetric in the two candidate messages. -/
theorem isCollision_comm (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (n : ℕ) (k m₁ m₂ : List Bool) :
    isCollision H valid n k m₁ m₂ = isCollision H valid n k m₂ m₁ := by
  rw [Bool.eq_iff_iff, isCollision_eq_true_iff, isCollision_eq_true_iff]
  tauto

@[simp]
theorem isCollision_self (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (n : ℕ) (k m : List Bool) :
    isCollision H valid n k m m = false := by
  simp [isCollision]

@[local fun_prop]
private theorem computableTidilyInPolyTime_isCollision
    {H : List Bool → List Bool → List Bool} {valid : ℕ → List Bool → Bool}
    (hH : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hvalid : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {k m₁ m₂ : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hk : ComputableTidilyInPolyTime k encIn encBits)
    (hm₁ : ComputableTidilyInPolyTime m₁ encIn encBits)
    (hm₂ : ComputableTidilyInPolyTime m₂ encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => isCollision H valid (n a) (k a) (m₁ a) (m₂ a)) encIn encBool := by
  have hv₁ : ComputableTidilyInPolyTime (fun a => valid (n a) (m₁ a)) encIn encBool :=
    hvalid.comp (hn.prod hm₁)
  have hv₂ : ComputableTidilyInPolyTime (fun a => valid (n a) (m₂ a)) encIn encBool :=
    hvalid.comp (hn.prod hm₂)
  have hH₁ : ComputableTidilyInPolyTime (fun a => H (k a) (m₁ a)) encIn encBits :=
    hH.comp (hk.prod hm₁)
  have hH₂ : ComputableTidilyInPolyTime (fun a => H (k a) (m₂ a)) encIn encBits :=
    hH.comp (hk.prod hm₂)
  unfold isCollision
  polytime

/-- Testing whether `(m₁, m₂)` is a valid collision is polynomial-time when `H` and `valid` are
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_isCollision
    {H : List Bool → List Bool → List Bool} {valid : ℕ → List Bool → Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool =>
        isCollision H valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool := by
  apply ComputableInPolyTime.of_tidy
  exact computableTidilyInPolyTime_isCollision hH.tidy hvalid.tidy
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- The keyed collision-finding experiment: sample a uniform `n`-bit key `k`, run `adversary n k`
to obtain a candidate pair `(m₁, m₂)`, and accept when `isCollision H valid n k m₁ m₂` holds. -/
noncomputable def collisionGame (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (adversary : CollisionFinder) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let pair ← adversary n k
  return isCollision H valid n k pair.1 pair.2

/-- Run the complete collision experiment on its unary security parameter. -/
@[program_certificate]
theorem isPPTOn_collisionGame {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {adversary : CollisionFinder}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (ha : IsPPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (collisionGame H valid adversary) := by
  have hHt := hH.tidy
  have hvt := hvalid.tidy
  unfold collisionGame
  ppt

/-- The collision experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_collisionGame {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {adversary : CollisionFinder}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (ha : IsPPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => collisionGame H valid adversary n) :=
  ((isPPTOn_collisionGame hH hvalid ha).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Collision resistance of a keyed hash family `H` on the valid input domain `valid`: every
uniform strict PPT collision finder has negligible success probability. -/
def CollisionResistantOn (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (collisionGame H valid adversary n))
    (fun _ _ => PMF.pure false)
    (IsPPT (encPair encBits encBits))

/-- Unrestricted collision resistance on all bit strings `List Bool`. -/
abbrev CollisionResistant (H : List Bool → List Bool → List Bool) : Prop :=
  CollisionResistantOn H (fun _ _ => true)

/-- Collision resistance gives negligible collision-finding probability for every strict PPT
adversary. -/
theorem CollisionResistantOn.negligible {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (h : CollisionResistantOn H valid)
    (adversary : CollisionFinder) (hPPT : IsPPT (encPair encBits encBits) adversary) :
    Negligible
      (fun n => Game.succProbability (ProbComp.eval (collisionGame H valid adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- Establish collision resistance by bounding every strict PPT adversary's success probability. -/
theorem CollisionResistantOn.of_negligible {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool}
    (h : ∀ adversary : CollisionFinder, IsPPT (encPair encBits encBits) adversary →
      Negligible
        (fun n => Game.succProbability (ProbComp.eval (collisionGame H valid adversary n)))) :
    CollisionResistantOn H valid := by
  intro adversary hPPT
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- If a deterministic map `extract` turns every valid `H₁`-collision under an `n`-bit key `k`
into a valid `H₂`-collision under `k`, then postprocessing `adversary` by `extract` at parameter `n`
never decreases the collision success probability. -/
theorem succProbability_collisionGame_le_of_extract
    {H₁ H₂ : List Bool → List Bool → List Bool} {valid₁ valid₂ : ℕ → List Bool → Bool}
    (extract : ℕ → List Bool → List Bool → List Bool → List Bool × List Bool)
    (adversary : CollisionFinder) (n : ℕ)
    (himp : ∀ k, k.length = n → ∀ m₁ m₂,
      isCollision H₁ valid₁ n k m₁ m₂ = true →
      isCollision H₂ valid₂ n k (extract n k m₁ m₂).1 (extract n k m₁ m₂).2 = true) :
    Game.succProbability (ProbComp.eval (collisionGame H₁ valid₁ adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (collisionGame H₂ valid₂
          (fun m k => do
            let pair ← adversary m k
            return extract m k pair.1 pair.2) n)) := by
  unfold Game.succProbability
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  simp only [collisionGame, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  apply PMF.bind_apply_mono_on_support
  intro k hk
  have hklen : k.length = n := by
    rw [BitString.eval_sampleList] at hk
    exact BitString.length_of_mem_support_uniformList hk
  apply PMF.bind_apply_mono_on_support
  intro pair _
  cases hcol : isCollision H₁ valid₁ n k pair.1 pair.2
  · simp
  · rw [himp k hklen pair.1 pair.2 hcol]

/-- **Deterministic collision-extraction reduction**: if a polynomial-time function `extract`
turns every `H₁`-collision at parameter `n` (for all sufficiently large `n` and `n`-bit keys `k`)
into an `H₂`-collision under the same key `k`, then collision resistance of `H₂` implies collision
resistance of `H₁`. -/
theorem CollisionResistantOn.of_extract
    {H₁ H₂ : List Bool → List Bool → List Bool} {valid₁ valid₂ : ℕ → List Bool → Bool}
    (hCR : CollisionResistantOn H₂ valid₂)
    (extract : ℕ → List Bool → List Bool → List Bool → List Bool × List Bool)
    (hextract : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => extract p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encBits encBits)))
      (encPair encBits encBits))
    (himp : ∀ᶠ n in Filter.atTop, ∀ k, k.length = n → ∀ m₁ m₂,
      isCollision H₁ valid₁ n k m₁ m₂ = true →
      isCollision H₂ valid₂ n k (extract n k m₁ m₂).1 (extract n k m₁ m₂).2 = true) :
    CollisionResistantOn H₁ valid₁ := by
  apply CollisionResistantOn.of_negligible
  intro adversary hadversary
  let redAdversary : CollisionFinder := fun n k => do
    let pair ← adversary n k
    return extract n k pair.1 pair.2
  have hpost : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × (List Bool × List Bool) =>
        extract p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encBits) (encPair encBits encBits))
      (encPair encBits encBits) :=
    hextract.tidy.comp
      ((ComputableTidilyInPolyTime.fst _ _).fst'.prod
        ((ComputableTidilyInPolyTime.fst _ _).snd'.prod (ComputableTidilyInPolyTime.snd _ _)))
  have hredPPT : IsPPT (encPair encBits encBits) redAdversary := by
    change IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => redAdversary p.1 p.2)
    exact hadversary.bind_with hpost.isPPTOn
  refine negligible_of_eventually_le (hCR.negligible redAdversary hredPPT) ?_
  filter_upwards [himp] with n hn
  exact succProbability_collisionGame_le_of_extract extract adversary n hn

/-- Restricting the valid input domain preserves collision resistance. -/
theorem CollisionResistantOn.mono
    {H : List Bool → List Bool → List Bool} {valid₁ valid₂ : ℕ → List Bool → Bool}
    (hCR : CollisionResistantOn H valid₂)
    (hsub : ∀ᶠ n in Filter.atTop, ∀ m, valid₁ n m = true → valid₂ n m = true) :
    CollisionResistantOn H valid₁ := by
  refine hCR.of_extract (fun _ _ m₁ m₂ => (m₁, m₂)) (by polytime) ?_
  filter_upwards [hsub] with n hn k _ m₁ m₂ hcol
  rw [isCollision_eq_true_iff] at hcol ⊢
  exact ⟨hn m₁ hcol.1, hn m₂ hcol.2.1, hcol.2.2.1, hcol.2.2.2⟩

/-- **Finding collisions with probability bounded away from zero refutes collision resistance**:
a strict PPT adversary whose success probability is at least a fixed `c > 0` at every security
parameter. -/
theorem not_collisionResistantOn_of_le_succProbability
    {H : List Bool → List Bool → List Bool} {valid : ℕ → List Bool → Bool}
    {c : ℝ≥0} (hc : c ≠ 0) (adversary : CollisionFinder)
    (hPPT : IsPPT (encPair encBits encBits) adversary)
    (h : ∀ n, c ≤ Game.succProbability (ProbComp.eval (collisionGame H valid adversary n))) :
    ¬ CollisionResistantOn H valid :=
  fun hCR => not_negligible_const hc (negligible_of_le (hCR.negligible adversary hPPT) h)

/-- Validity predicate for a fixed-input-length `2n → n` compression family: at security parameter
`n`, valid inputs have length `2 * n`. -/
def validCompressionInput (n : ℕ) (x : List Bool) : Bool :=
  x.length == 2 * n

@[simp]
theorem validCompressionInput_eq_true_iff {n : ℕ} {x : List Bool} :
    validCompressionInput n x = true ↔ x.length = 2 * n :=
  beq_iff_eq

@[local fun_prop]
private theorem computableTidilyInPolyTime_validCompressionInput :
    ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => validCompressionInput p.1 p.2)
      (encPair encUnary encBits) encBool := by
  unfold validCompressionInput
  polytime

/-- Testing whether an input has length `2 * n` is computable in plain polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_validCompressionInput :
    ComputableInPolyTime
      (fun p : ℕ × List Bool => validCompressionInput p.1 p.2)
      (encPair encUnary encBits) encBool :=
  .of_tidy computableTidilyInPolyTime_validCompressionInput

/-- A keyed `2n → n` collision-resistant compression family ([BonehShoup2023], Section 8.2):
computable in deterministic polynomial time, mapping `2n`-bit inputs under an `n`-bit key to
`n`-bit outputs, and collision-resistant on `2n`-bit inputs. -/
structure CompressionFamily (h : List Bool → List Bool → List Bool) : Prop where
  /-- Deterministic polynomial-time evaluation of `(k, x) ↦ h k x`. -/
  polyTime : ComputableInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
    (encPair encBits encBits) encBits
  /-- Compressing a `2n`-bit input under an `n`-bit key produces an `n`-bit digest. -/
  length_eq : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length
  /-- Finding two distinct `2n`-bit inputs with the same digest under a uniform `n`-bit key is
  hard for every uniform strict PPT adversary. -/
  collisionResistant : CollisionResistantOn h validCompressionInput

/-- A keyed collision-resistant hash family on arbitrary-length bit strings (`List Bool`), mapping
every message under an `n`-bit key to an `n`-bit digest. -/
structure HashFamily (H : List Bool → List Bool → List Bool) : Prop where
  /-- Deterministic polynomial-time evaluation of `(k, msg) ↦ H k msg`. -/
  polyTime : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
    (encPair encBits encBits) encBits
  /-- Hashing any message under an `n`-bit key produces an `n`-bit digest. -/
  length_eq : ∀ k msg, (H k msg).length = k.length
  /-- Finding two distinct bit strings of any lengths with the same digest under a uniform `n`-bit
  key is hard for every uniform strict PPT adversary. -/
  collisionResistant : CollisionResistant H

end Cslib.Crypto
