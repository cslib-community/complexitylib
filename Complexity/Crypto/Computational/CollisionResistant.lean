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

Following [BonehShoup2023], Section 8.1.1 (Definition 8.2 and Fig. 8.3, printed pp. 290–291), we
define the general setup-parameterized notions `CollisionFinderFor`, `isCollisionFor`,
`collisionGameFor`, `CollisionResistantForOn`, and `CollisionResistantFor` for hash families
`H : (d : Param) → List Bool → Digest d` indexed by a public system parameter `d ← setup n`
(where `setup : ℕ → PMF Param` need not be efficiently sampleable, matching `PrimeOrderGroupFamily`
in `DiscreteLog` and `DiffieHellman`, and where `d` subsumes any hash key per footnote 1 on printed
p. 290). Standard keyed word-level collision resistance (`CollisionFinder`, `CollisionResistantOn`,
`CollisionResistant`) is the `abbrev` specialization `Param = List Bool`, `Digest _ = List Bool`,
`encParam = encBits`, `setup n = ProbComp.eval (BitString.sampleList n)`.

## Main definitions

* `Cslib.Crypto.CollisionFinderFor`, `Cslib.Crypto.isCollisionFor`,
  `Cslib.Crypto.collisionGameFor`, `Cslib.Crypto.CollisionResistantForOn`,
  `Cslib.Crypto.CollisionResistantFor`: setup-parameterized collision-finding experiment and
  collision resistance for families `H : (d : Param) → List Bool → Digest d` indexed by a public
  setup parameter `d ← setup n` (used for group-indexed $\mathbb{Z}_q$-valued hashes such as
  $H' : \mathbb{G}^3 \to \mathbb{Z}_q$ in Cramer–Shoup).
* `Cslib.Crypto.CollisionFinder`, `Cslib.Crypto.isCollision`, `Cslib.Crypto.collisionGame`,
  `Cslib.Crypto.CollisionResistantOn`, `Cslib.Crypto.CollisionResistant`: uniform keyed word-level
  collision resistance (`Param = List Bool`, `setup n = ProbComp.eval (BitString.sampleList n)`).
* `Cslib.Crypto.validCompressionInput`, `Cslib.Crypto.CompressionFamily`: `2n → n` collision-
  resistant compression families.
* `Cslib.Crypto.HashFamily`: unrestricted collision-resistant hash families on arbitrary bit
  strings.

## Main results

* `Cslib.Crypto.CollisionResistantForOn.negligible`,
  `Cslib.Crypto.CollisionResistantForOn.of_negligible`,
  `Cslib.Crypto.not_collisionResistantForOn_of_le_succProbability`,
  `Cslib.Crypto.succProbability_collisionGameFor_map_le`,
  `Cslib.Crypto.CollisionResistantForOn.of_map`,
  `Cslib.Crypto.CollisionResistantOn.collisionResistantForOn`: setup-parameterized collision
  resistance properties and injective-digest reductions (including the specialization from
  word-level `CollisionResistantOn`).
* `Cslib.Crypto.isPPTOn_collisionGame`, `Cslib.Crypto.isPPT_collisionGame`: strict PPT certificates
  for the keyed word-level collision experiment.
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

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 8.1 (Definition 8.2 and Fig. 8.3, printed pp. 290–291).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 5.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Setup-parameterized collision-resistant hash families ([BonehShoup2023], Section 8.1.1)

Verbatim from [BonehShoup2023], Section 8.1.1 (printed pp. 290–291):

> **Definition 8.2 (Keyless hash functions).** A **(keyless) hash function** is an efficient
> algorithm $H$, along with two families of spaces with system parameterization $P$:
> $$\mathcal{M} = \{\mathcal{M}_{\lambda, \Lambda}\}_{\lambda, \Lambda}, \quad \text{and} \quad
> \mathcal{T} = \{\mathcal{T}_{\lambda, \Lambda}\}_{\lambda, \Lambda},$$
> such that
> 1. $\mathcal{M}$, and $\mathcal{T}$ are efficiently recognizable.
> 2. Algorithm $H$ is an efficient deterministic algorithm that on input
>    $\lambda \in \mathbb{Z}_{\ge 1}$, $\Lambda \in \text{Supp}(P(\lambda))$, and
>    $m \in \mathcal{M}_{\lambda, \Lambda}$, outputs an element of $\mathcal{T}_{\lambda, \Lambda}$.
>
> In defining collision resistance, we parameterize Attack Game 8.1 by the security parameter
> $\lambda$. The asymptotic game is shown in Fig. 8.3. The advantage $\text{CRadv}[\mathcal{A}, H]$
> is then a function of $\lambda$. Definition 8.1 should be read as saying that
> $\text{CRadv}[\mathcal{A}, H](\lambda)$ is a negligible function.
-/

/-- A setup-parameterized collision finder receives the unary security parameter `n` and the public
system parameter `d : Param` (which may be a hash key `k : List Bool`, a group description
`d : F.Desc`, or a pair `(d, k)`), and outputs a candidate colliding pair `(m₁, m₂)`. -/
abbrev CollisionFinderFor (Param : Type) :=
  ℕ → Param → ProbComp (List Bool × List Bool)

/-- Test whether `(m₁, m₂)` is a valid collision for `H d` at security parameter `n` and public
parameter `d` under the domain predicate `valid`. -/
def isCollisionFor {Param : Type} {Digest : Param → Type} [∀ d, DecidableEq (Digest d)]
    (H : (d : Param) → List Bool → Digest d)
    (valid : ℕ → Param → List Bool → Bool)
    (n : ℕ) (d : Param) (m₁ m₂ : List Bool) : Bool :=
  valid n d m₁ && valid n d m₂ && (m₁ != m₂) && decide (H d m₁ = H d m₂)

@[simp]
theorem isCollisionFor_eq_true_iff {Param : Type} {Digest : Param → Type}
    [∀ d, DecidableEq (Digest d)] {H : (d : Param) → List Bool → Digest d}
    {valid : ℕ → Param → List Bool → Bool} {n : ℕ} {d : Param} {m₁ m₂ : List Bool} :
    isCollisionFor H valid n d m₁ m₂ = true ↔
      valid n d m₁ = true ∧ valid n d m₂ = true ∧ m₁ ≠ m₂ ∧ H d m₁ = H d m₂ := by
  simp only [isCollisionFor, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, and_assoc]

/-- Parameterized collision testing is symmetric in the two candidate messages. -/
theorem isCollisionFor_comm {Param : Type} {Digest : Param → Type} [∀ d, DecidableEq (Digest d)]
    (H : (d : Param) → List Bool → Digest d)
    (valid : ℕ → Param → List Bool → Bool) (n : ℕ) (d : Param) (m₁ m₂ : List Bool) :
    isCollisionFor H valid n d m₁ m₂ = isCollisionFor H valid n d m₂ m₁ := by
  rw [Bool.eq_iff_iff, isCollisionFor_eq_true_iff, isCollisionFor_eq_true_iff]
  tauto

@[simp]
theorem isCollisionFor_self {Param : Type} {Digest : Param → Type} [∀ d, DecidableEq (Digest d)]
    (H : (d : Param) → List Bool → Digest d)
    (valid : ℕ → Param → List Bool → Bool) (n : ℕ) (d : Param) (m : List Bool) :
    isCollisionFor H valid n d m m = false := by
  simp [isCollisionFor]

/-- The setup-parameterized collision-finding experiment ([BonehShoup2023], Section 8.1.1,
Definition 8.2 and Fig. 8.3, printed pp. 290–291): draw `d ← setup n` (where `setup` is an
arbitrary setup distribution and need not be efficiently sampleable, matching `DiscreteLog` and
`DDH`), run `adversary n d` to obtain `(m₁, m₂)`, and accept when
`isCollisionFor H valid n d m₁ m₂` holds. -/
noncomputable def collisionGameFor {Param : Type} {Digest : Param → Type}
    [∀ d, DecidableEq (Digest d)]
    (setup : ℕ → PMF Param) (H : (d : Param) → List Bool → Digest d)
    (valid : ℕ → Param → List Bool → Bool)
    (adversary : CollisionFinderFor Param) (n : ℕ) : Game := do
  let d ← setup n
  let pair ← ProbComp.eval (adversary n d)
  return isCollisionFor H valid n d pair.1 pair.2

/-- Collision resistance of a setup-parameterized hash family `H` on `valid` against every
uniform strict PPT collision finder ([BonehShoup2023], Section 8.1.1, Definition 8.2 and Fig. 8.3,
printed pp. 290–291). The setup distribution `setup : ℕ → PMF Param` need not be efficiently
sampleable. -/
def CollisionResistantForOn {Param : Type} {Digest : Param → Type}
    [∀ d, DecidableEq (Digest d)]
    (encParam : Param ↪ List Bool) (setup : ℕ → PMF Param)
    (H : (d : Param) → List Bool → Digest d)
    (valid : ℕ → Param → List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (collisionGameFor setup H valid)
    (fun _ _ => PMF.pure false)
    (fun adversary =>
      IsPPTOn (encPair encUnary encParam) (encPair encBits encBits)
        (fun p => adversary p.1 p.2))

/-- Unrestricted collision resistance of a setup-parameterized hash family `H`. -/
abbrev CollisionResistantFor {Param : Type} {Digest : Param → Type}
    [∀ d, DecidableEq (Digest d)]
    (encParam : Param ↪ List Bool) (setup : ℕ → PMF Param)
    (H : (d : Param) → List Bool → Digest d) : Prop :=
  CollisionResistantForOn encParam setup H (fun _ _ _ => true)

/-- Setup-parameterized collision resistance gives negligible collision-finding probability for
every strict PPT collision finder. -/
theorem CollisionResistantForOn.negligible {Param : Type} {Digest : Param → Type}
    [∀ d, DecidableEq (Digest d)] {encParam : Param ↪ List Bool}
    {setup : ℕ → PMF Param} {H : (d : Param) → List Bool → Digest d}
    {valid : ℕ → Param → List Bool → Bool}
    (h : CollisionResistantForOn encParam setup H valid)
    (adversary : CollisionFinderFor Param)
    (hPPT : IsPPTOn (encPair encUnary encParam) (encPair encBits encBits)
      (fun p => adversary p.1 p.2)) :
    Negligible (fun n => Game.succProbability (collisionGameFor setup H valid adversary n)) := by
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- Establish setup-parameterized collision resistance by bounding every strict PPT adversary's
success probability. -/
theorem CollisionResistantForOn.of_negligible {Param : Type} {Digest : Param → Type}
    [∀ d, DecidableEq (Digest d)] {encParam : Param ↪ List Bool}
    {setup : ℕ → PMF Param} {H : (d : Param) → List Bool → Digest d}
    {valid : ℕ → Param → List Bool → Bool}
    (h : ∀ adversary : CollisionFinderFor Param,
      IsPPTOn (encPair encUnary encParam) (encPair encBits encBits)
        (fun p => adversary p.1 p.2) →
      Negligible (fun n => Game.succProbability (collisionGameFor setup H valid adversary n))) :
    CollisionResistantForOn encParam setup H valid := by
  intro adversary hPPT
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- **Finding collisions with probability bounded away from zero refutes
`CollisionResistantForOn`**: a strict PPT collision finder whose success probability is at least a
fixed `c > 0` at every security parameter. -/
theorem not_collisionResistantForOn_of_le_succProbability
    {Param : Type} {Digest : Param → Type} [∀ d, DecidableEq (Digest d)]
    {encParam : Param ↪ List Bool} {setup : ℕ → PMF Param}
    {H : (d : Param) → List Bool → Digest d} {valid : ℕ → Param → List Bool → Bool}
    {c : ℝ≥0} (hc : c ≠ 0) (adversary : CollisionFinderFor Param)
    (hPPT : IsPPTOn (encPair encUnary encParam) (encPair encBits encBits)
      (fun p => adversary p.1 p.2))
    (h : ∀ n, c ≤ Game.succProbability (collisionGameFor setup H valid adversary n)) :
    ¬ CollisionResistantForOn encParam setup H valid :=
  fun hCR => not_negligible_const hc (negligible_of_le (hCR.negligible adversary hPPT) h)

/-- Pushing a setup distribution `setup₁ n` forward along `f n : Param₁ → Param₂` and post-composing
`H₁` with a digest map that is injective on valid `H₁ p₁`-outputs for `p₁ ∈ (setup₁ n).support`
never increases collision-finding success probability. -/
theorem succProbability_collisionGameFor_map_le
    {Param₁ Param₂ : Type} {Digest₁ : Param₁ → Type} {Digest₂ : Param₂ → Type}
    [∀ p₁, DecidableEq (Digest₁ p₁)] [∀ p₂, DecidableEq (Digest₂ p₂)]
    (setup₁ : ℕ → PMF Param₁) (f : ℕ → Param₁ → Param₂)
    (H₁ : (p₁ : Param₁) → List Bool → Digest₁ p₁)
    (H₂ : (p₂ : Param₂) → List Bool → Digest₂ p₂)
    (valid₁ : ℕ → Param₁ → List Bool → Bool)
    (valid₂ : ℕ → Param₂ → List Bool → Bool)
    (adversary : CollisionFinderFor Param₂) (n : ℕ)
    (hinj : ∀ p₁ ∈ (setup₁ n).support, ∀ m₁ m₂,
      valid₂ n (f n p₁) m₁ = true → valid₂ n (f n p₁) m₂ = true →
      H₂ (f n p₁) m₁ = H₂ (f n p₁) m₂ →
      valid₁ n p₁ m₁ = true ∧ valid₁ n p₁ m₂ = true ∧ H₁ p₁ m₁ = H₁ p₁ m₂) :
    Game.succProbability
      (collisionGameFor (fun m => (setup₁ m).map (f m)) H₂ valid₂ adversary n) ≤
      Game.succProbability
        (collisionGameFor setup₁ H₁ valid₁ (fun m p₁ => adversary m (f m p₁)) n) := by
  unfold Game.succProbability
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  simp only [collisionGameFor, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
  apply PMF.bind_apply_mono_on_support
  intro p₁ hp₁
  apply PMF.bind_apply_mono_on_support
  intro pair _
  cases hcol : isCollisionFor H₂ valid₂ n (f n p₁) pair.1 pair.2
  · simp
  · rw [isCollisionFor_eq_true_iff] at hcol
    obtain ⟨hv₁, hv₂, hH₁⟩ := hinj p₁ hp₁ pair.1 pair.2 hcol.1 hcol.2.1 hcol.2.2.2
    have hcol' : isCollisionFor H₁ valid₁ n p₁ pair.1 pair.2 = true := by
      rw [isCollisionFor_eq_true_iff]
      exact ⟨hv₁, hv₂, hcol.2.2.1, hH₁⟩
    rw [hcol']

/-- **Parameter-map and injective-digest reduction for `CollisionResistantForOn`**: if `f` is
computable in polynomial time and every `H₂ (f n p₁)`-collision on `p₁ ∈ (setup₁ n).support` is a
valid `H₁ p₁`-collision, then `CollisionResistantForOn` for `H₁` implies `CollisionResistantForOn`
for `H₂` under `fun n => (setup₁ n).map (f n)`. -/
theorem CollisionResistantForOn.of_map
    {Param₁ Param₂ : Type} {Digest₁ : Param₁ → Type} {Digest₂ : Param₂ → Type}
    [∀ p₁, DecidableEq (Digest₁ p₁)] [∀ p₂, DecidableEq (Digest₂ p₂)]
    {encParam₁ : Param₁ ↪ List Bool} {encParam₂ : Param₂ ↪ List Bool}
    {setup₁ : ℕ → PMF Param₁} {f : ℕ → Param₁ → Param₂}
    {H₁ : (p₁ : Param₁) → List Bool → Digest₁ p₁}
    {H₂ : (p₂ : Param₂) → List Bool → Digest₂ p₂}
    {valid₁ : ℕ → Param₁ → List Bool → Bool}
    {valid₂ : ℕ → Param₂ → List Bool → Bool}
    (hCR : CollisionResistantForOn encParam₁ setup₁ H₁ valid₁)
    (hf : ComputableInPolyTime (fun p : ℕ × Param₁ => f p.1 p.2)
      (encPair encUnary encParam₁) encParam₂)
    (hinj : ∀ᶠ n in Filter.atTop, ∀ p₁ ∈ (setup₁ n).support, ∀ m₁ m₂,
      valid₂ n (f n p₁) m₁ = true → valid₂ n (f n p₁) m₂ = true →
      H₂ (f n p₁) m₁ = H₂ (f n p₁) m₂ →
      valid₁ n p₁ m₁ = true ∧ valid₁ n p₁ m₂ = true ∧ H₁ p₁ m₁ = H₁ p₁ m₂) :
    CollisionResistantForOn encParam₂ (fun m => (setup₁ m).map (f m)) H₂ valid₂ := by
  apply CollisionResistantForOn.of_negligible
  intro adversary hadversary
  let redAdversary : CollisionFinderFor Param₁ := fun n p₁ => adversary n (f n p₁)
  have hpre : ComputableInPolyTime
      (fun p : ℕ × Param₁ => (p.1, f p.1 p.2))
      (encPair encUnary encParam₁)
      (encPair encUnary encParam₂) :=
    (by fun_prop : ComputableInPolyTime (fun p : ℕ × Param₁ => p.1) _ encUnary).prod hf
  have hredPPT :
      IsPPTOn (encPair encUnary encParam₁) (encPair encBits encBits)
        (fun p => redAdversary p.1 p.2) :=
    hadversary.preprocess hpre
  refine negligible_of_eventually_le (hCR.negligible redAdversary hredPPT) ?_
  filter_upwards [hinj] with n hn
  exact succProbability_collisionGameFor_map_le setup₁ f H₁ H₂ valid₁ valid₂ adversary n hn

/-! ### Keyed word-level collision-resistant hash families (`Param = List Bool`) -/

/-- A collision finder receives the unary security parameter `n` and public hash key `k` and
outputs a pair `(m₁, m₂)` of candidate colliding messages. -/
abbrev CollisionFinder := CollisionFinderFor (List Bool)

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

@[simp]
theorem isCollisionFor_eq_isCollision (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (n : ℕ) (k m₁ m₂ : List Bool) :
    isCollisionFor (Param := List Bool) (Digest := fun _ => List Bool)
      H (fun m _ => valid m) n k m₁ m₂ = isCollision H valid n k m₁ m₂ := by
  rw [Bool.eq_iff_iff, isCollisionFor_eq_true_iff, isCollision_eq_true_iff]

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
  have hv₁ : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool × List Bool =>
      valid p.1 p.2.2.1) (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool :=
    hvalid.comp (.prod (.fst _ _) (by fun_prop))
  have hv₂ : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool × List Bool =>
      valid p.1 p.2.2.2) (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool :=
    hvalid.comp (.prod (.fst _ _) (by fun_prop))
  have hH₁ : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool × List Bool =>
      H p.2.1 p.2.2.1) (encPair encUnary (encPair encBits (encPair encBits encBits))) encBits :=
    hH.comp (.prod (by fun_prop) (by fun_prop))
  have hH₂ : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool × List Bool =>
      H p.2.1 p.2.2.2) (encPair encUnary (encPair encBits (encPair encBits encBits))) encBits :=
    hH.comp (.prod (by fun_prop) (by fun_prop))
  unfold isCollision
  fun_prop

/-- The keyed collision-finding experiment: sample a uniform `n`-bit key `k`, run `adversary n k`
to obtain a candidate pair `(m₁, m₂)`, and accept when `isCollision H valid n k m₁ m₂` holds. -/
noncomputable def collisionGame (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (adversary : CollisionFinder) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let pair ← adversary n k
  return isCollision H valid n k pair.1 pair.2

/-- The keyed `collisionGame` is the `Param = List Bool`, `setup n = ProbComp.eval (sampleList n)`
specialization of `collisionGameFor`. -/
theorem collisionGameFor_sampleList_eq (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (adversary : CollisionFinder) (n : ℕ) :
    collisionGameFor (Param := List Bool) (Digest := fun _ => List Bool)
      (fun m => ProbComp.eval (BitString.sampleList m)) H (fun m _ => valid m) adversary n =
      ProbComp.eval (collisionGame H valid adversary n) := by
  simp only [collisionGameFor, collisionGame, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, isCollisionFor_eq_isCollision]

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

/-- Collision resistance of a keyed hash family `H` on the valid input domain `valid`:
specialization of `CollisionResistantForOn` to `Param = List Bool`, `Digest _ = List Bool`,
`encParam = encBits`, and `setup n = ProbComp.eval (BitString.sampleList n)`. -/
abbrev CollisionResistantOn (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) : Prop :=
  CollisionResistantForOn (Param := List Bool) (Digest := fun _ => List Bool) encBits
    (fun n => ProbComp.eval (BitString.sampleList n)) H (fun n _ => valid n)

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
  simpa only [collisionGameFor_sampleList_eq] using
    CollisionResistantForOn.negligible h adversary hPPT

/-- Establish collision resistance by bounding every strict PPT adversary's success probability. -/
theorem CollisionResistantOn.of_negligible {H : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool}
    (h : ∀ adversary : CollisionFinder, IsPPT (encPair encBits encBits) adversary →
      Negligible
        (fun n => Game.succProbability (ProbComp.eval (collisionGame H valid adversary n)))) :
    CollisionResistantOn H valid := by
  apply CollisionResistantForOn.of_negligible
  intro adversary hPPT
  simpa only [collisionGameFor_sampleList_eq] using h adversary hPPT

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
    ¬ CollisionResistantOn H valid := by
  refine not_collisionResistantForOn_of_le_succProbability hc adversary hPPT ?_
  intro n
  simpa only [collisionGameFor_sampleList_eq] using h n

/-- **Bridge from word-level `CollisionResistantOn` to `CollisionResistantForOn` over
`(d n, k) : Param × List Bool`**: when `d : ℕ → Param` is computable in polynomial time and
`toDigest (d n)` is eventually injective on valid `H k`-outputs for `n`-bit keys `k`, collision
resistance of `H` implies parameterized collision resistance of
`fun pk x => toDigest pk.1 (H pk.2 x)` under
`setup n = (ProbComp.eval (BitString.sampleList n)).map (fun k => (d n, k))`. -/
theorem CollisionResistantOn.collisionResistantForOn {Param : Type} {Digest : Param → Type}
    [∀ d, DecidableEq (Digest d)] {encParam : Param ↪ List Bool}
    {d : ℕ → Param} {H : List Bool → List Bool → List Bool}
    {toDigest : (p : Param) → List Bool → Digest p}
    {valid : ℕ → List Bool → Bool}
    (hCR : CollisionResistantOn H valid)
    (hd : ComputableInPolyTime d encUnary encParam)
    (hinj : ∀ᶠ n in Filter.atTop, ∀ k, k.length = n → ∀ m₁ m₂,
      valid n m₁ = true → valid n m₂ = true →
      toDigest (d n) (H k m₁) = toDigest (d n) (H k m₂) → H k m₁ = H k m₂) :
    CollisionResistantForOn (encPair encParam encBits)
      (fun m => (ProbComp.eval (BitString.sampleList m)).map (fun k => (d m, k)))
      (fun pk x => toDigest pk.1 (H pk.2 x)) (fun m _ x => valid m x) := by
  have hf : ComputableInPolyTime (fun p : ℕ × List Bool => (d p.1, p.2))
      (encPair encUnary encBits) (encPair encParam encBits) := by
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool => p.1)
        (encPair encUnary encBits) encUnary := by fun_prop
    have hk : ComputableInPolyTime (fun p : ℕ × List Bool => p.2)
        (encPair encUnary encBits) encBits := by fun_prop
    exact (hd.comp hn).prod hk
  refine hCR.of_map (Digest₂ := fun pk : Param × List Bool => Digest pk.1) hf ?_
  filter_upwards [hinj] with n hn k hk m₁ m₂ hv₁ hv₂ hcol
  have hklen : k.length = n := by
    rw [BitString.eval_sampleList] at hk
    exact BitString.length_of_mem_support_uniformList hk
  exact ⟨hv₁, hv₂, hn k hklen m₁ m₂ hv₁ hv₂ hcol⟩

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
