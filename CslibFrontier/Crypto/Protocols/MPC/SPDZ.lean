/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Beaver
public import CslibFrontier.Probability.LinearCombination
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TransferInstance

/-!
# SPDZ Authenticated Secret Sharing, Online Operations, and Batch `MACCheck` Soundness

This module formalizes the SPDZ authenticated secret-sharing representation and its linear and
Beaver-triple online operations ([DamgardPastroSmartZakarias2012]), together with the
commit-then-open batch `MACCheck` protocol and the $2 / p$ bound for its standalone
cheating-equation game over prime fields `ZMod p`
([DamgardKellerLarraiaPastroSchollSmart2013]).

## Source map

Locators refer to the IACR ePrint full versions: [DamgardPastroSmartZakarias2012] is ePrint
2011/535 (revision of 2012-11-05) and [DamgardKellerLarraiaPastroSchollSmart2013] is ePrint 2012/642
(revision of 2013-08-20). LNCS page and figure numbers are not verified.

* **DPSZ12, §2 "Representation of values and MACs" and "Computations"; online phase Fig. 1:** the
  authenticated representation with public modifier $\delta$ (`AuthShare`, `AuthShare.Valid`),
  constant addition (`AuthShare.addConst`), and Beaver multiplication (`AuthShare.mulOnline`).
  DPSZ12 works over $\mathbb{F}_{p^k}$; this module works over `ZMod p` only.
* **DKLPSS13, §2:** the representation without $\delta$ (dropped from the MAC definition there).
* **DKLPSS13, App. D.1, Fig. 10:** `MACCheck`. `checkResidual` and `verifyResiduals` adapt its
  check $\sigma_i = \gamma_i - \alpha_i \cdot a$ to DPSZ12's $\delta$-representation; at
  $\delta = 0$ they are the source check. `macCheckProtocol` models steps 5–9 of Fig. 10
  (commitment and opening of the residual shares); steps 1–4 (coin-flipping a seed and expanding it
  with a PRG into the weights) are replaced by weights supplied as inputs.
* **DKLPSS13, §5.1, Lemma 1** (correct, and sound except with probability $2 / p$) and **App. D.3**
  (its proof game): `macCheckSoundnessGame` and `macCheckSoundnessAdvGame` formalize the App. D.3
  game, and `eval_macCheckSoundnessGame_le` its $2 / p$ bound. As in App. D.3, tampering with the
  corrupt parties' MAC shares is absorbed into the adversarial shift (`deltaOpen` / `deltaShift`).

## Contents


1. **SPDZ Authenticated Secret Sharing (`AuthShare`):** represents an authenticated value
   $\langle a \rangle = (\delta, (a_0, \dots, a_{n-1}), (\gamma_0, \dots, \gamma_{n-1}))$ over
   `ZMod p` with reconstructed secret $a = \sum_i a_i$, MAC sum $\gamma = \sum_i \gamma_i$, and
   global MAC invariant `AuthShare.Valid alpha` ($\gamma = \alpha \cdot (a + \delta)$).
2. **Linear & Online Beaver Operations (`AuthShare.add`, `AuthShare.neg`, `AuthShare.sub`,
   `AuthShare.smul`, `AuthShare.addConst`, `AuthShare.mulOnline`):** local share addition,
   negation, subtraction, public scalar multiplication, public constant addition (updating party
   `0`'s value share and shifting the public modifier $\delta \mapsto \delta - e$), and online
   Beaver multiplication
   $\langle x \cdot y \rangle = e \cdot \langle a \rangle + d \cdot \langle b \rangle + \langle c
   \rangle + d \cdot e$, all preserving `AuthShare.Valid alpha`, matching
   `Cslib.Crypto.Protocols.MPC.Beaver.beaverMulShare` on each party's value share
   (`AuthShare.valShares_mulOnline_eq_beaverMulShare`), and reconstructing $x \cdot y$ when
   $d = x - a$, $e = y - b$, and $c = a \cdot b$ (`AuthShare.secret_mulOnline_eq_mul`).
3. **Batch `MACCheck` Protocol & Completeness (`OpenedValue`, `PartyCheckInput`, `ResidualOpening`,
   `checkResidual`, `macCheckProtocol`, `eval_snd_macCheckProtocol_eq_pure_true`):** two-round
   commit-then-open protocol over `CslibFrontier.Crypto.Protocols.MPC.Basic` and
   `CslibFrontier.Crypto.Protocols.MPC.Broadcast` checking a batch of $T$ publicly opened values via
   linear combination weights $e \in (\mathbb{Z}_p)^T$ supplied as inputs (steps 5–9 of
   [DamgardKellerLarraiaPastroSchollSmart2013], App. D.1, Fig. 10, adapted to the
   $\delta$-representation). Honest executions satisfy
   $\sum_i \sigma_i = 0$ (`sum_checkResidual_eq_zero`) and accept with probability `1`.
4. **Residual Cheating Equation & $2 / p$ Standalone Cheating-Equation Game Bound
   (`sum_checkResidual_eq_neg_mul`, `sum_checkResidual_add_eq_zero_iff`, `linearCombZeroGame`,
   `macCheckSoundnessGame`, `eval_macCheckSoundnessGame_le`, `eval_macCheckSoundnessAdvGame_le`):**
   for prime `p` and any nonzero vector of opening errors `err ≠ 0` (even against an adaptive
   residual shift `deltaShift : (Fin T → ZMod p) → ZMod p` chosen as a function of the public
   weights `e`, or generated from prior randomized adversary state `adv : ProbComp S` independent
   of `alpha`), the `MACCheck` cheating equation
   `alpha * linearCombAddHom err e = deltaShift e` (standalone game) holds with probability at
   most $2 / p$ ([DamgardKellerLarraiaPastroSchollSmart2013], §5.1, Lemma 1; App. D.3):
   - Stage 1 (`eval_linearCombZeroGame_eq`): $\Pr_e[\sum_\ell e_\ell \cdot \mathrm{err}_\ell = 0]
     = 1 / p$, proved via `Cslib.Probability.toOuterMeasure_uniform_linearComb_eq_zero`.
   - Stage 2 (`eval_macKey_guess_le`): whenever
     $L = \sum_\ell e_\ell \cdot \mathrm{err}_\ell \neq 0$, a uniform key
     $\alpha \in \mathbb{Z}_p$ satisfies $\alpha \cdot L = \Delta(e)$ with probability $1 / p$,
     proved via `Cslib.Probability.toOuterMeasure_uniform_linearComb_eq` on `Unit`.

Scope note: `macCheckProtocol` is parameterized over an abstract deterministic commitment map
`commit : ZMod p → Coins → Comm` (checking equality of Round-1 commitments and Round-2 openings);
weights are supplied as inputs (`PartyCheckInput.weights`) whose joint generation after the
openings is not modeled, `alpha` is not sampled by the protocol, and the `AddCommMonoid` structures
on `Coins`, `Comm`, and `ResidualOpening` are only used by the `broadcastSteps` combinator.
The games `macCheckSoundnessGame` and `macCheckSoundnessAdvGame` analyze the standalone algebraic
information-theoretic cheating equation given an independent uniform MAC key
$\alpha \in \mathbb{Z}_p$ and public weights $e \in (\mathbb{Z}_p)^T$. The game's $\alpha$ plays
the role of an honest party's key share $\alpha_H$, uniform and unknown to the adversary; the
corrupt parties' contribution $\alpha_C \cdot L$ is part of `deltaShift`. The games are analyzed
directly, not as an execution of `macCheckProtocol`, a computational commitment binding
reduction, a UC emulation proof, or a polynomial-time simulator certificate. Generalizing the
$2 / p$ bound to an arbitrary finite field and removing the `AddCommMonoid` requirement from
`broadcastSteps` are left as follow-ups.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.secret`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.macSum`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.Valid`: SPDZ `⟨·⟩`-authenticated secret sharing and
  MAC invariant.
* `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.add`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.neg`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.sub`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.smul`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.addConst`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.mulOnline`: homomorphic linear operations and online
  Beaver multiplication on authenticated shares.
* `Cslib.Crypto.Protocols.MPC.SPDZ.OpenedValue`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.PartyCheckInput`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.PartyCheckInput.AuthenticFor`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.PartyCheckInput.Honest`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.ResidualOpening`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.checkResidual`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.verifyResiduals`: batch `MACCheck` inputs, local residuals, and
  verification predicate.
* `Cslib.Crypto.Protocols.MPC.SPDZ.macCheckSchedule`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.macCheckProtocol`: two-round commit-then-open `MACCheck`
  protocol over `CslibFrontier.Crypto.Protocols.MPC.Basic`.
* `Cslib.Crypto.Protocols.MPC.SPDZ.linearCombZeroGame`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.macCheckSoundnessGame`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.macCheckSoundnessAdvGame`: standalone `ProbComp`
  cheating-equation games.

## Main results

* `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.Valid.add`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.Valid.neg`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.Valid.sub`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.Valid.smul`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.Valid.addConst`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.Valid.mulOnline`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.valShares_mulOnline_eq_beaverMulShare`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.secret_mulOnline_eq_mul`: MAC-invariant preservation,
  value-share agreement with `Beaver.beaverMulShare`, and online product correctness.
* `Cslib.Crypto.Protocols.MPC.SPDZ.sum_checkResidual_eq_zero`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.eval_snd_macCheckProtocol_eq_pure_true`: honest completeness of
  batch `MACCheck`.
* `Cslib.Crypto.Protocols.MPC.SPDZ.sum_checkResidual_eq_neg_mul`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.sum_checkResidual_add_eq_zero_iff`: algebraic residual identity
  and cheating equation for forged openings.
* `Cslib.Crypto.Protocols.MPC.SPDZ.eval_linearCombZeroGame_eq`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.eval_linearCombZeroGame_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.toReal_eval_linearCombZeroGame_le`: Stage 1 weight-cancellation
  probability $1 / p$.
* `Cslib.Crypto.Protocols.MPC.SPDZ.eval_macKey_guess_le`: Stage 2 key-guessing probability bound.
* `Cslib.Crypto.Protocols.MPC.SPDZ.eval_macCheckSoundnessGame_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.toReal_eval_macCheckSoundnessGame_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.succProbability_macCheckSoundnessGame_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.eval_macCheckSoundnessAdvGame_le`: concrete $2 / p$ bound for the
  standalone `MACCheck` cheating-equation game.

## References

* [I. Damgård, V. Pastro, N. P. Smart, S. Zakarias, *Multiparty Computation from Somewhat
  Homomorphic Encryption*][DamgardPastroSmartZakarias2012].
* [I. Damgård, M. Keller, E. Larraia, V. Pastro, P. Scholl, N. P. Smart, *Practical Covertly
  Secure MPC for Dishonest Majority — Or: Breaking the SPDZ
  Limits*][DamgardKellerLarraiaPastroSchollSmart2013].
-/

public section

namespace Cslib.Crypto.Protocols.MPC.SPDZ

open Cslib.Probability Cslib.ProbComp Cslib.Crypto
open Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.Beaver
open scoped ENNReal NNReal

/-! ### SPDZ `⟨·⟩`-authenticated secret sharing and online operations -/

/-- SPDZ authenticated secret sharing `⟨a⟩ = (δ, (a_0, …, a_{n-1}), (γ_0, …, γ_{n-1}))` over
`ZMod p` among `n` parties ([DamgardPastroSmartZakarias2012]). -/
@[ext] structure AuthShare (p n : ℕ) where
  /-- Public modifier `δ` tracked identically by all parties. -/
  delta : ZMod p
  /-- Party `i`'s additive share `a_i` of the secret `a = ∑ i, a_i`. -/
  valShares : Fin n → ZMod p
  /-- Party `i`'s additive share `γ_i` of the MAC `γ(a) = ∑ i, γ_i`. -/
  macShares : Fin n → ZMod p
  deriving DecidableEq, Inhabited

namespace AuthShare

/-- Underlying secret `a = ∑ i, a_i` represented by `s`. -/
@[expose] def secret {p n : ℕ} (s : AuthShare p n) : ZMod p :=
  ∑ i : Fin n, s.valShares i

/-- Sum `γ(a) = ∑ i, γ_i` of all `n` parties' MAC shares. -/
@[expose] def macSum {p n : ℕ} (s : AuthShare p n) : ZMod p :=
  ∑ i : Fin n, s.macShares i

/-- Global SPDZ MAC relation `∑ i, γ_i = α * ((∑ i, a_i) + δ)` under global key `alpha : ZMod p`. -/
@[expose] def Valid {p n : ℕ} (alpha : ZMod p) (s : AuthShare p n) : Prop :=
  s.macSum = alpha * (s.secret + s.delta)

instance {p n : ℕ} (alpha : ZMod p) (s : AuthShare p n) : Decidable (s.Valid alpha) :=
  inferInstanceAs (Decidable (s.macSum = alpha * (s.secret + s.delta)))

/-- Coordinatewise addition `⟨a⟩ + ⟨b⟩` of authenticated shares. -/
@[expose] def add {p n : ℕ} (s₁ s₂ : AuthShare p n) : AuthShare p n where
  delta := s₁.delta + s₂.delta
  valShares i := s₁.valShares i + s₂.valShares i
  macShares i := s₁.macShares i + s₂.macShares i

instance {p n : ℕ} : Add (AuthShare p n) := ⟨add⟩

/-- Coordinatewise negation `-⟨a⟩` of an authenticated share. -/
@[expose] def neg {p n : ℕ} (s : AuthShare p n) : AuthShare p n where
  delta := -s.delta
  valShares i := -s.valShares i
  macShares i := -s.macShares i

instance {p n : ℕ} : Neg (AuthShare p n) := ⟨neg⟩

/-- Coordinatewise subtraction `⟨a⟩ - ⟨b⟩` of authenticated shares. -/
@[expose] def sub {p n : ℕ} (s₁ s₂ : AuthShare p n) : AuthShare p n where
  delta := s₁.delta - s₂.delta
  valShares i := s₁.valShares i - s₂.valShares i
  macShares i := s₁.macShares i - s₂.macShares i

instance {p n : ℕ} : Sub (AuthShare p n) := ⟨sub⟩

/-- Public scalar multiplication `c • ⟨a⟩` of an authenticated share by `c : ZMod p`. -/
@[expose] def smul {p n : ℕ} (c : ZMod p) (s : AuthShare p n) : AuthShare p n where
  delta := c * s.delta
  valShares i := c * s.valShares i
  macShares i := c * s.macShares i

instance {p n : ℕ} : SMul (ZMod p) (AuthShare p n) := ⟨smul⟩

/-- Addition of a public constant `e : ZMod p` to `⟨a⟩` ([DamgardPastroSmartZakarias2012]):
party `0` adds `e` to its value share while the public modifier shifts to `δ - e`, leaving all
MAC shares unchanged. -/
@[expose] def addConst {p n : ℕ} (e : ZMod p) (s : AuthShare p n) : AuthShare p n where
  delta := s.delta - e
  valShares i := if i.val = 0 then s.valShares i + e else s.valShares i
  macShares := s.macShares

/-- SPDZ online Beaver multiplication `⟨x * y⟩ = e • ⟨a⟩ + d • ⟨b⟩ + ⟨c⟩ + d * e` given
authenticated Beaver triple `⟨a⟩, ⟨b⟩, ⟨c⟩` and public masked openings `d` (claimed `x - a`)
and `e` (claimed `y - b`) ([DamgardPastroSmartZakarias2012]). The opened scalars `d` and `e` are
audited in batch by `MACCheck`. -/
@[expose] def mulOnline {p n : ℕ} (sa sb sc : AuthShare p n) (d e : ZMod p) : AuthShare p n :=
  addConst (d * e) ((e • sa + d • sb) + sc)

@[simp] theorem secret_add {p n : ℕ} (s₁ s₂ : AuthShare p n) :
    (s₁ + s₂).secret = s₁.secret + s₂.secret := by
  change (∑ i : Fin n, (s₁.valShares i + s₂.valShares i)) = _
  exact Finset.sum_add_distrib

@[simp] theorem macSum_add {p n : ℕ} (s₁ s₂ : AuthShare p n) :
    (s₁ + s₂).macSum = s₁.macSum + s₂.macSum := by
  change (∑ i : Fin n, (s₁.macShares i + s₂.macShares i)) = _
  exact Finset.sum_add_distrib

@[simp] theorem delta_add {p n : ℕ} (s₁ s₂ : AuthShare p n) :
    (s₁ + s₂).delta = s₁.delta + s₂.delta := rfl

@[simp] theorem secret_neg {p n : ℕ} (s : AuthShare p n) :
    (-s).secret = -s.secret := by
  change (∑ i : Fin n, -s.valShares i) = -∑ i : Fin n, s.valShares i
  exact Finset.sum_neg_distrib ..

@[simp] theorem macSum_neg {p n : ℕ} (s : AuthShare p n) :
    (-s).macSum = -s.macSum := by
  change (∑ i : Fin n, -s.macShares i) = -∑ i : Fin n, s.macShares i
  exact Finset.sum_neg_distrib ..

@[simp] theorem delta_neg {p n : ℕ} (s : AuthShare p n) :
    (-s).delta = -s.delta := rfl

@[simp] theorem secret_sub {p n : ℕ} (s₁ s₂ : AuthShare p n) :
    (s₁ - s₂).secret = s₁.secret - s₂.secret := by
  change (∑ i : Fin n, (s₁.valShares i - s₂.valShares i)) =
    (∑ i : Fin n, s₁.valShares i) - ∑ i : Fin n, s₂.valShares i
  exact Finset.sum_sub_distrib _ _

@[simp] theorem macSum_sub {p n : ℕ} (s₁ s₂ : AuthShare p n) :
    (s₁ - s₂).macSum = s₁.macSum - s₂.macSum := by
  change (∑ i : Fin n, (s₁.macShares i - s₂.macShares i)) =
    (∑ i : Fin n, s₁.macShares i) - ∑ i : Fin n, s₂.macShares i
  exact Finset.sum_sub_distrib _ _

@[simp] theorem delta_sub {p n : ℕ} (s₁ s₂ : AuthShare p n) :
    (s₁ - s₂).delta = s₁.delta - s₂.delta := rfl

@[simp] theorem secret_smul {p n : ℕ} (c : ZMod p) (s : AuthShare p n) :
    (c • s).secret = c * s.secret := by
  change (∑ i : Fin n, c * s.valShares i) = _
  rw [← Finset.mul_sum]
  rfl

@[simp] theorem macSum_smul {p n : ℕ} (c : ZMod p) (s : AuthShare p n) :
    (c • s).macSum = c * s.macSum := by
  change (∑ i : Fin n, c * s.macShares i) = _
  rw [← Finset.mul_sum]
  rfl

@[simp] theorem delta_smul {p n : ℕ} (c : ZMod p) (s : AuthShare p n) :
    (c • s).delta = c * s.delta := rfl

@[simp] theorem secret_addConst {p n : ℕ} [NeZero n] (e : ZMod p) (s : AuthShare p n) :
    (addConst e s).secret = s.secret + e := by
  have h0 : ∀ i : Fin n,
      (if i = 0 then s.valShares i + e else s.valShares i) =
        s.valShares i + if i = 0 then e else 0 := fun i => by
    by_cases hi : i = 0 <;> simp [hi]
  simp [secret, addConst, h0, Finset.sum_add_distrib]

@[simp] theorem macSum_addConst {p n : ℕ} (e : ZMod p) (s : AuthShare p n) :
    (addConst e s).macSum = s.macSum := rfl

@[simp] theorem delta_addConst {p n : ℕ} (e : ZMod p) (s : AuthShare p n) :
    (addConst e s).delta = s.delta - e := rfl

/-- `Valid alpha` is preserved under share addition `s₁ + s₂`. -/
theorem Valid.add {p n : ℕ} {alpha : ZMod p} {s₁ s₂ : AuthShare p n}
    (h₁ : s₁.Valid alpha) (h₂ : s₂.Valid alpha) :
    (s₁ + s₂).Valid alpha := by
  simp only [Valid, macSum_add, secret_add, delta_add] at h₁ h₂ ⊢
  linear_combination h₁ + h₂

/-- `Valid alpha` is preserved under share negation `-s`. -/
theorem Valid.neg {p n : ℕ} {alpha : ZMod p} {s : AuthShare p n}
    (hs : s.Valid alpha) :
    (-s).Valid alpha := by
  simp only [Valid, macSum_neg, secret_neg, delta_neg] at hs ⊢
  linear_combination -hs

/-- `Valid alpha` is preserved under share subtraction `s₁ - s₂`. -/
theorem Valid.sub {p n : ℕ} {alpha : ZMod p} {s₁ s₂ : AuthShare p n}
    (h₁ : s₁.Valid alpha) (h₂ : s₂.Valid alpha) :
    (s₁ - s₂).Valid alpha := by
  simp only [Valid, macSum_sub, secret_sub, delta_sub] at h₁ h₂ ⊢
  linear_combination h₁ - h₂

/-- `Valid alpha` is preserved under public scalar multiplication `c • s`. -/
theorem Valid.smul {p n : ℕ} {alpha : ZMod p} (c : ZMod p) {s : AuthShare p n}
    (hs : s.Valid alpha) :
    (c • s).Valid alpha := by
  simp only [Valid, macSum_smul, secret_smul, delta_smul] at hs ⊢
  linear_combination c * hs

/-- `Valid alpha` is preserved under public constant addition `addConst e s` (`n > 0`). -/
theorem Valid.addConst {p n : ℕ} [NeZero n] {alpha : ZMod p} (e : ZMod p) {s : AuthShare p n}
    (hs : s.Valid alpha) :
    (addConst e s).Valid alpha := by
  simp only [Valid, macSum_addConst, secret_addConst, delta_addConst] at hs ⊢
  linear_combination hs

/-- `Valid alpha` is preserved by `mulOnline` (`n > 0`) whenever the triple shares `sa, sb, sc`
satisfy `Valid alpha` (even for arbitrary candidate public openings `d, e`). -/
theorem Valid.mulOnline {p n : ℕ} [NeZero n] {alpha : ZMod p}
    {sa sb sc : AuthShare p n} (d e : ZMod p)
    (ha : sa.Valid alpha) (hb : sb.Valid alpha) (hc : sc.Valid alpha) :
    (mulOnline sa sb sc d e).Valid alpha :=
  Valid.addConst (d * e) (((Valid.smul e ha).add (Valid.smul d hb)).add hc)

/-- Each party `i`'s value share in `mulOnline` agrees with `Beaver.beaverMulShare` applied to
the party's value-share triple `⟨sa.valShares i, sb.valShares i, sc.valShares i⟩`. -/
theorem valShares_mulOnline_eq_beaverMulShare {p n : ℕ}
    (sa sb sc : AuthShare p n) (d e : ZMod p) (i : Fin n) :
    (mulOnline sa sb sc d e).valShares i =
      beaverMulShare i (d, e) ⟨sa.valShares i, sb.valShares i, sc.valShares i⟩ := by
  change (if i.val = 0 then ((e * sa.valShares i + d * sb.valShares i) + sc.valShares i) + d * e
      else (e * sa.valShares i + d * sb.valShares i) + sc.valShares i) =
    (if i.val = 0 then d * e else 0) + d * sb.valShares i + e * sa.valShares i + sc.valShares i
  split_ifs <;> ring

/-- Reconstructed secret of `mulOnline` before substituting `d` and `e`. -/
@[simp] theorem secret_mulOnline {p n : ℕ} [NeZero n]
    (sa sb sc : AuthShare p n) (d e : ZMod p) :
    (mulOnline sa sb sc d e).secret =
      e * sa.secret + d * sb.secret + sc.secret + d * e := by
  simp [mulOnline]

/-- Online multiplication correctness ([DamgardPastroSmartZakarias2012]): when the public
openings satisfy `d = sx.secret - sa.secret` and `e = sy.secret - sb.secret` and the triple
satisfies `sc.secret = sa.secret * sb.secret`, `mulOnline` reconstructs `sx.secret * sy.secret`. -/
theorem secret_mulOnline_eq_mul {p n : ℕ} [NeZero n]
    (sx sy sa sb sc : AuthShare p n) (d e : ZMod p)
    (hd : d = sx.secret - sa.secret) (he : e = sy.secret - sb.secret)
    (hc : sc.secret = sa.secret * sb.secret) :
    (mulOnline sa sb sc d e).secret = sx.secret * sy.secret := by
  rw [secret_mulOnline, hd, he, hc]
  ring

end AuthShare

/-! ### Batch `MACCheck` data structures, residual equations, and commit-then-open protocol -/

/-- Publicly opened value `(a'_ℓ, δ_ℓ)` audited during SPDZ `MACCheck`. -/
@[ext] structure OpenedValue (p : ℕ) where
  /-- Claimed public value `a'_ℓ` reconstructed by opening `⟨a_ℓ⟩`. -/
  value : ZMod p
  /-- Public modifier `δ_ℓ` associated with `⟨a_ℓ⟩`. -/
  delta : ZMod p
  deriving DecidableEq, Inhabited, Repr

/-- Party `i`'s local input to a batch `MACCheck` over `T` opened values
([DamgardKellerLarraiaPastroSchollSmart2013], App. D.1, Fig. 10). -/
@[ext] structure PartyCheckInput (p T : ℕ) where
  /-- The `T` publicly opened values and modifiers `(a'_ℓ, δ_ℓ)`. -/
  opened : Fin T → OpenedValue p
  /-- Party `i`'s local MAC shares `γ(a_ℓ)_i` for `ℓ : Fin T`. -/
  macShares : Fin T → ZMod p
  /-- Party `i`'s additive share `α_i` of the global MAC key `α = ∑ i, α_i`. -/
  keyShare : ZMod p
  /-- Public random linear-combination weights `(e_0, …, e_{T-1})`. -/
  weights : Fin T → ZMod p
  deriving DecidableEq, Inhabited

/-- Round-2 opening message `(σ_j, decommit_j)` broadcast by party `j` in `macCheckProtocol`. -/
@[ext] structure ResidualOpening (p : ℕ) (Coins : Type) where
  /-- Party `j`'s claimed residual share `σ_j`. -/
  sigma : ZMod p
  /-- Decommitment randomness matching party `j`'s Round-1 commitment. -/
  decommit : Coins
  deriving DecidableEq, Inhabited

/-- Equivalence between `ResidualOpening p Coins` and `ZMod p × Coins`, used to transport
`AddCommMonoid` from `ZMod p × Coins` for `broadcastSteps`. -/
@[expose] def ResidualOpening.equivProd (p : ℕ) (Coins : Type) :
    ResidualOpening p Coins ≃ ZMod p × Coins where
  toFun u := (u.sigma, u.decommit)
  invFun | (sigma, decommit) => ⟨sigma, decommit⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {p : ℕ} {Coins : Type} [AddCommMonoid Coins] :
    AddCommMonoid (ResidualOpening p Coins) :=
  (ResidualOpening.equivProd p Coins).addCommMonoid

/-- Party `i`'s local `MACCheck` residual share
`σ_i = (∑ ℓ, e_ℓ * γ(a_ℓ)_i) - α_i * (∑ ℓ, e_ℓ * (a'_ℓ + δ_ℓ))`: an adaptation of the check
`σ_i = γ_i - α_i * a` of [DamgardKellerLarraiaPastroSchollSmart2013] (App. D.1, Fig. 10) to the
`δ`-representation of [DamgardPastroSmartZakarias2012]; at `δ = 0` it is the source check. -/
@[expose] def checkResidual {p T : ℕ} (inp : PartyCheckInput p T) : ZMod p :=
  (∑ l : Fin T, inp.weights l * inp.macShares l) -
    inp.keyShare * ∑ l : Fin T, inp.weights l * ((inp.opened l).value + (inp.opened l).delta)

/-- Verify that every party's Round-2 residual opening matches its Round-1 commitment and that the
opened residual shares sum to `0` ([DamgardKellerLarraiaPastroSchollSmart2013], App. D.1,
Fig. 10). -/
@[expose] def verifyResiduals {p n : ℕ} {Coins Comm : Type} [DecidableEq Comm]
    (commit : ZMod p → Coins → Comm)
    (commits : Fin n → Comm) (openings : Fin n → ResidualOpening p Coins) : Bool :=
  decide ((∀ j : Fin n, commit (openings j).sigma (openings j).decommit = commits j) ∧
    (∑ j : Fin n, (openings j).sigma) = 0)

/-- Predicate stating that `inp : Fin n → PartyCheckInput p T` arises from validly authenticated
shares `shares : Fin T → AuthShare p n` under global key `alpha = ∑ i, α_i` with common public
`opened` values and common public `weights` `e` (allowing `opened` to differ from the true secrets
by `err_ℓ = (opened ℓ).value - (shares ℓ).secret`). Following
[DamgardKellerLarraiaPastroSchollSmart2013], App. D.3, tampering with the corrupt parties' MAC
shares is not modeled here; it is absorbed into the adversarial shift `deltaOpen` /
`deltaShift`. -/
structure PartyCheckInput.AuthenticFor {p n T : ℕ} (alpha : ZMod p)
    (shares : Fin T → AuthShare p n) (opened : Fin T → OpenedValue p)
    (e : Fin T → ZMod p) (inp : Fin n → PartyCheckInput p T) : Prop where
  /-- Every party sees the same public opened values `opened`. -/
  opened_eq : ∀ i, (inp i).opened = opened
  /-- Every party uses the same public random weights `e`. -/
  weights_eq : ∀ i, (inp i).weights = e
  /-- Every party holds its corresponding MAC share of each `shares ℓ`. -/
  macShares_eq : ∀ i l, (inp i).macShares l = (shares l).macShares i
  /-- Each public modifier `(opened ℓ).delta` matches `(shares ℓ).delta`. -/
  delta_eq : ∀ l, (opened l).delta = (shares l).delta
  /-- The key shares sum to the global MAC key `alpha`. -/
  sum_keyShare : (∑ i : Fin n, (inp i).keyShare) = alpha
  /-- Each authenticated share in the batch satisfies the SPDZ MAC invariant under `alpha`. -/
  valid_shares : ∀ l, (shares l).Valid alpha

/-- Predicate stating that `inp` is a completely honest `MACCheck` instance in which every opened
value `(opened ℓ).value` equals the true shared secret `(shares ℓ).secret`. -/
structure PartyCheckInput.Honest {p n T : ℕ} (alpha : ZMod p)
    (shares : Fin T → AuthShare p n) (opened : Fin T → OpenedValue p)
    (e : Fin T → ZMod p) (inp : Fin n → PartyCheckInput p T) : Prop extends
    PartyCheckInput.AuthenticFor alpha shares opened e inp where
  /-- Every opened value equals the true secret `(shares ℓ).secret`. -/
  value_eq : ∀ l, (opened l).value = (shares l).secret

/-- Core algebraic residual identity of SPDZ `MACCheck` (the `δ`-adapted check of
[DamgardKellerLarraiaPastroSchollSmart2013], App. D.1, Fig. 10): when `inp` is authenticated
for `shares` with claimed public openings `opened`,
`∑ i, checkResidual (inp i) = - alpha * ∑ ℓ, e_ℓ * ((opened ℓ).value - (shares ℓ).secret)`. -/
theorem sum_checkResidual_eq_neg_mul {p n T : ℕ} {alpha : ZMod p}
    {shares : Fin T → AuthShare p n} {opened : Fin T → OpenedValue p}
    {e : Fin T → ZMod p} {inp : Fin n → PartyCheckInput p T}
    (hauth : PartyCheckInput.AuthenticFor alpha shares opened e inp) :
    (∑ i : Fin n, checkResidual (inp i)) =
      -alpha * linearCombAddHom (fun l => (opened l).value - (shares l).secret) e := by
  have h1 :
      (∑ i : Fin n, ∑ l : Fin T, (inp i).weights l * (inp i).macShares l) =
        alpha * ∑ l : Fin T, e l * ((shares l).secret + (shares l).delta) := by
    simp_rw [hauth.weights_eq, hauth.macShares_eq]
    rw [Finset.sum_comm]
    calc (∑ l : Fin T, ∑ i : Fin n, e l * (shares l).macShares i)
        = ∑ l : Fin T, e l * (shares l).macSum := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [← Finset.mul_sum]; rfl
      _ = ∑ l : Fin T, e l * (alpha * ((shares l).secret + (shares l).delta)) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hauth.valid_shares l]
      _ = alpha * ∑ l : Fin T, e l * ((shares l).secret + (shares l).delta) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => by ring
  have h2 :
      (∑ i : Fin n, (inp i).keyShare *
          ∑ l : Fin T, (inp i).weights l * (((inp i).opened l).value + ((inp i).opened l).delta)) =
        alpha * ∑ l : Fin T, e l * ((opened l).value + (shares l).delta) := by
    simp_rw [hauth.weights_eq, hauth.opened_eq, hauth.delta_eq, ← Finset.sum_mul,
      hauth.sum_keyShare]
  simp only [checkResidual, Finset.sum_sub_distrib, h1, h2, linearCombAddHom_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hsub :
      (∑ l : Fin T, (e l * ((shares l).secret + (shares l).delta) -
          e l * ((opened l).value + (shares l).delta))) =
        -(∑ l : Fin T, e l * ((opened l).value - (shares l).secret)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => by ring
  rw [hsub]
  ring

/-- Honest completeness of `checkResidual`: when all opened values match the true secrets, the
parties' residuals sum to `0`. -/
theorem sum_checkResidual_eq_zero {p n T : ℕ} {alpha : ZMod p}
    {shares : Fin T → AuthShare p n} {opened : Fin T → OpenedValue p}
    {e : Fin T → ZMod p} {inp : Fin n → PartyCheckInput p T}
    (hhon : PartyCheckInput.Honest alpha shares opened e inp) :
    (∑ i : Fin n, checkResidual (inp i)) = 0 := by
  rw [sum_checkResidual_eq_neg_mul hhon.toAuthenticFor]
  simp [hhon.value_eq]

/-- Cheating equation equivalence ([DamgardKellerLarraiaPastroSchollSmart2013], App. D.3): adding an
adversarial residual shift `deltaOpen` to the honest residual sum yields `0` if and only if
`alpha * linearCombAddHom err e = deltaOpen`. -/
theorem sum_checkResidual_add_eq_zero_iff {p n T : ℕ} {alpha : ZMod p}
    {shares : Fin T → AuthShare p n} {opened : Fin T → OpenedValue p}
    {e : Fin T → ZMod p} {inp : Fin n → PartyCheckInput p T}
    (hauth : PartyCheckInput.AuthenticFor alpha shares opened e inp) (deltaOpen : ZMod p) :
    (∑ i : Fin n, checkResidual (inp i)) + deltaOpen = 0 ↔
      alpha * linearCombAddHom (fun l => (opened l).value - (shares l).secret) e = deltaOpen := by
  rw [sum_checkResidual_eq_neg_mul hauth]
  constructor <;> intro h <;> linear_combination -h

/-- Schedule for the two-round commit-then-open `macCheckProtocol`: Round 1 broadcasts commitments
`Comm` and Round 2 broadcasts `ResidualOpening p Coins`. -/
@[expose, reducible] def macCheckSchedule (p n : ℕ) (Coins Comm : Type) : Schedule n noOracleSpec :=
  broadcastSchedule n noOracleSpec Comm ++
    broadcastSchedule n noOracleSpec (ResidualOpening p Coins)

/-- Two-round commit-then-open `MACCheck` protocol over `CslibFrontier.Crypto.Protocols.MPC.Basic`,
modeling steps 5–9 of [DamgardKellerLarraiaPastroSchollSmart2013], App. D.1, Fig. 10 (steps 1–4,
which coin-flip a seed and expand it with a PRG into the weights, are replaced by the input
weights `PartyCheckInput.weights`), with the residual adapted to the `δ`-representation:
1. Each party `i` samples commitment coins `r_i ← sampleCoins`, computes `σ_i = checkResidual`,
   and broadcasts `commit σ_i r_i` in Round 1.
2. Each party `i` broadcasts `⟨σ_i, r_i⟩ : ResidualOpening p Coins` in Round 2.
3. Each party outputs `verifyResiduals commit commits openings`. -/
def macCheckProtocol (p n T : ℕ) {Coins Comm : Type}
    [AddCommMonoid Coins] [AddCommMonoid Comm] [DecidableEq Comm]
    (sampleCoins : ProbComp Coins) (commit : ZMod p → Coins → Comm) :
    Protocol n noOracleSpec (macCheckSchedule p n Coins Comm)
      (fun _ => PartyCheckInput p T) (fun _ => Coins) (fun _ => Bool) where
  sampleCoins _ := sampleCoins
  steps :=
    Steps.append
      (broadcastSteps n (spec := noOracleSpec)
        (State := fun _ => PartyCheckInput p T × Coins)
        (Out := fun _ => (PartyCheckInput p T × Coins) × (Fin n → Comm))
        (fun _ (inp_i, r_i) => commit (checkResidual inp_i) r_i)
        (fun _ st commits => (st, commits)))
      (broadcastSteps n (spec := noOracleSpec)
        (State := fun _ => (PartyCheckInput p T × Coins) × (Fin n → Comm))
        (Out := fun _ => Bool)
        (fun _ ((inp_i, r_i), _) => (⟨checkResidual inp_i, r_i⟩ : ResidualOpening p Coins))
        (fun _ (_, commits) openings => verifyResiduals commit commits openings))

/-- Honest completeness of `macCheckProtocol`: for every commitment scheme `(sampleCoins, commit)`
and every honest `PartyCheckInput.Honest` batch, all `n` parties output `true` with probability `1`.
-/
theorem eval_snd_macCheckProtocol_eq_pure_true {p n T : ℕ} {Coins Comm : Type}
    [AddCommMonoid Coins] [AddCommMonoid Comm] [DecidableEq Comm]
    (sampleCoins : ProbComp Coins) (commit : ZMod p → Coins → Comm)
    {alpha : ZMod p} {shares : Fin T → AuthShare p n}
    {opened : Fin T → OpenedValue p} {e : Fin T → ZMod p}
    {inp : Fin n → PartyCheckInput p T}
    (hhon : PartyCheckInput.Honest alpha shares opened e inp) :
    ((macCheckProtocol p n T sampleCoins commit).evalWith noOracleWorld inp).map Prod.snd =
      PMF.pure (fun _ => true) := by
  set P := macCheckProtocol p n T sampleCoins commit
  rw [Protocol.evalWith_eq, PMF.map_bind]
  have hconst : ∀ r : Fin n → Coins,
      ((P.steps.evalWith noOracleWorld (fun i => (inp i, r i))).map
        (fun recv =>
          let views : (i : Fin n) → PartyView _ _ _ i := fun i => ⟨inp i, r i, recv i⟩
          (views, fun i => P.outputOfView i (views i)))).map
        Prod.snd = PMF.pure (fun _ => true) := by
    intro r
    simp only [P, macCheckProtocol, Steps.evalWith_append, evalWith_broadcastSteps,
      outputAt_broadcastSteps, PMF.pure_bind, PMF.pure_map,
      Protocol.outputOfView, Steps.outputAt_append]
    congr 1
    ext i
    simp [verifyResiduals, sum_checkResidual_eq_zero hhon]
  rw [show (fun a : Fin n → Coins =>
        PMF.map Prod.snd
          (PMF.map
            (fun recv =>
              let views : (i : Fin n) → PartyView _ _ _ i := fun i => ⟨inp i, a i, recv i⟩
              (views, fun i => P.outputOfView i (views i)))
            (P.steps.evalWith noOracleWorld fun i => (inp i, a i)))) =
        fun _ => PMF.pure (fun _ => true) from funext hconst]
  exact PMF.bind_const _ _

/-! ### Concrete $2 / p$ bound for the standalone `MACCheck` cheating-equation game -/

/-- Stage-1 `ProbComp` game testing whether random weights `e ← ProbComp.uniform (Fin T → ZMod p)`
annihilate a fixed nonzero error vector `err : Fin T → ZMod p`. -/
noncomputable def linearCombZeroGame (p T : ℕ) [NeZero p] (err : Fin T → ZMod p) :
    ProbComp Bool := do
  let e ← ProbComp.uniform (Fin T → ZMod p)
  return decide (linearCombAddHom err e = 0)

/-- Standalone `MACCheck` cheating-equation game, the game from the proof of
[DamgardKellerLarraiaPastroSchollSmart2013], §5.1, Lemma 1 (App. D.3):
samples an independent uniform MAC key `alpha ← ProbComp.uniform (ZMod p)` and public weights
`e ← ProbComp.uniform (Fin T → ZMod p)`, and tests whether the adversary's (possibly `e`-adaptive)
residual shift `deltaShift e` satisfies the cheating equation
`alpha * linearCombAddHom err e = deltaShift e`. -/
noncomputable def macCheckSoundnessGame (p T : ℕ) [NeZero p]
    (err : Fin T → ZMod p) (deltaShift : (Fin T → ZMod p) → ZMod p) : ProbComp Bool := do
  let alpha ← ProbComp.uniform (ZMod p)
  let e ← ProbComp.uniform (Fin T → ZMod p)
  return decide (alpha * linearCombAddHom err e = deltaShift e)

/-- Stateful randomized-adversary standalone `MACCheck` cheating-equation game (the game of
[DamgardKellerLarraiaPastroSchollSmart2013], App. D.3, paralleling
`CslibFrontier.Crypto.Protocols.VOLE.MulCheck`): an arbitrary prior computation `adv : ProbComp S`
selects state `s` determining both the opening error vector `err s` and the `e`-adaptive shift
`deltaShift s` before the independent key `alpha` is sampled, winning if `err s ≠ 0` and
`alpha * linearCombAddHom (err s) e = deltaShift s e`. -/
noncomputable def macCheckSoundnessAdvGame (p T : ℕ) [NeZero p] {S : Type}
    (adv : ProbComp S) (err : S → Fin T → ZMod p)
    (deltaShift : S → (Fin T → ZMod p) → ZMod p) : ProbComp Bool := do
  let s ← adv
  let alpha ← ProbComp.uniform (ZMod p)
  let e ← ProbComp.uniform (Fin T → ZMod p)
  return decide (err s ≠ 0 ∧ alpha * linearCombAddHom (err s) e = deltaShift s e)

/-- Stage 1 exact probability: for prime `p` and `err ≠ 0`, `linearCombZeroGame p T err` outputs
`true` with exact probability `p⁻¹` (via `toOuterMeasure_uniform_linearComb_eq_zero`). -/
theorem eval_linearCombZeroGame_eq {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0) :
    (ProbComp.eval (linearCombZeroGame p T err)) true = (p : ℝ≥0∞)⁻¹ := by
  obtain ⟨l₀, hl₀⟩ := Function.ne_iff.mp herr
  simp only [linearCombZeroGame, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_uniform,
    ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hpre : (fun e : Fin T → ZMod p => decide (linearCombAddHom err e = 0)) ⁻¹' {true} =
      {e | ∑ l, e l * err l = 0} := by
    ext e
    simp
  rw [hpre, toOuterMeasure_uniform_linearComb_eq_zero hl₀, ZMod.card, one_div]

/-- Stage 1 upper bound in `ℝ≥0∞`. -/
theorem eval_linearCombZeroGame_le {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0) :
    (ProbComp.eval (linearCombZeroGame p T err)) true ≤ (p : ℝ≥0∞)⁻¹ :=
  (eval_linearCombZeroGame_eq herr).le

/-- Stage 1 real-valued probability bound `≤ 1 / p`. -/
theorem toReal_eval_linearCombZeroGame_le {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0) :
    ((ProbComp.eval (linearCombZeroGame p T err)) true).toReal ≤ 1 / (p : ℝ) := by
  rw [eval_linearCombZeroGame_eq herr, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

/-- Stage-2 pointwise key-guessing bound: for any `L, d : ZMod p`, a uniform key `alpha : ZMod p`
satisfies `alpha * L = d` with probability at most `(if L = 0 then 1 else 0) + p⁻¹` (proved in the
`L ≠ 0` branch via `toOuterMeasure_uniform_linearComb_eq` on `Unit`). -/
theorem eval_macKey_guess_le {p : ℕ} [Fact (Nat.Prime p)] (L d : ZMod p) :
    ((PMF.uniformOfFintype (ZMod p)).map fun alpha => decide (alpha * L = d)) true ≤
      (if L = 0 then (1 : ℝ≥0∞) else 0) + (p : ℝ≥0∞)⁻¹ := by
  by_cases hL : L = 0
  · simp only [hL, ↓reduceIte]
    exact (PMF.coe_le_one _ _).trans le_self_add
  · simp only [hL, ↓reduceIte, zero_add]
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      ← Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.funUnique Unit (ZMod p)),
      PMF.toOuterMeasure_map_apply]
    have hpre : (Equiv.funUnique Unit (ZMod p) ⁻¹'
        ((fun alpha : ZMod p => decide (alpha * L = d)) ⁻¹' {true})) =
        {r : Unit → ZMod p | ∑ i : Unit, r i * L = d} := by
      ext r
      simp
    rw [hpre, toOuterMeasure_uniform_linearComb_eq (d := fun _ => L) (i₀ := ()) hL d,
      ZMod.card, one_div]

/-- Concrete $2 / p$ bound for the standalone `MACCheck` cheating-equation game
([DamgardKellerLarraiaPastroSchollSmart2013], §5.1, Lemma 1; App. D.3): for prime `p`, any
nonzero opening error vector `err ≠ 0`, and any `e`-adaptive residual shift `deltaShift`,
`macCheckSoundnessGame p T err deltaShift` outputs `true` with probability at most `2 / p`. -/
theorem eval_macCheckSoundnessGame_le {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0)
    (deltaShift : (Fin T → ZMod p) → ZMod p) :
    (ProbComp.eval (macCheckSoundnessGame p T err deltaShift)) true ≤ 2 / (p : ℝ≥0∞) := by
  obtain ⟨l₀, hl₀⟩ := Function.ne_iff.mp herr
  simp only [macCheckSoundnessGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm, PMF.bind_apply]
  let μ := PMF.uniformOfFintype (Fin T → ZMod p)
  let S : Set (Fin T → ZMod p) := {e | ∑ l, e l * err l = 0}
  have hstep : ∀ e : Fin T → ZMod p,
      μ e * ((PMF.uniformOfFintype (ZMod p)).bind
        (fun alpha => PMF.pure (decide (alpha * linearCombAddHom err e = deltaShift e)))) true ≤
      S.indicator μ e + μ e * (p : ℝ≥0∞)⁻¹ := by
    intro e
    have hm :
        ((PMF.uniformOfFintype (ZMod p)).bind
          (fun alpha => PMF.pure (decide (alpha * linearCombAddHom err e = deltaShift e)))) =
        (PMF.uniformOfFintype (ZMod p)).map
          (fun alpha => decide (alpha * linearCombAddHom err e = deltaShift e)) := by
      rw [PMF.map]; rfl
    have hkey := eval_macKey_guess_le (linearCombAddHom err e) (deltaShift e)
    rw [← hm] at hkey
    refine (mul_le_mul_right hkey (μ e)).trans ?_
    by_cases he : e ∈ S
    · have he0 : ∑ l, e l * err l = 0 := he
      simp [he, he0, mul_add]
    · have he0 : ∑ l, e l * err l ≠ 0 := he
      simp [he, he0]
  calc ∑' e, μ e *
        ((PMF.uniformOfFintype (ZMod p)).bind
          (fun alpha => PMF.pure (decide (alpha * linearCombAddHom err e = deltaShift e)))) true
      ≤ ∑' e, (S.indicator μ e + μ e * (p : ℝ≥0∞)⁻¹) := tsum_le_tsum hstep
    _ = μ.toOuterMeasure S + (p : ℝ≥0∞)⁻¹ := by
        rw [tsum_add, ← PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right,
          PMF.tsum_coe, one_mul]
    _ = (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ := by
        rw [toOuterMeasure_uniform_linearComb_eq_zero hl₀, ZMod.card, one_div]
    _ = 2 / (p : ℝ≥0∞) := by rw [div_eq_mul_inv, two_mul]

/-- Real-valued `2 / p` bound for `macCheckSoundnessGame`. -/
theorem toReal_eval_macCheckSoundnessGame_le {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0)
    (deltaShift : (Fin T → ZMod p) → ZMod p) :
    ((ProbComp.eval (macCheckSoundnessGame p T err deltaShift)) true).toReal ≤ 2 / (p : ℝ) := by
  have h := eval_macCheckSoundnessGame_le herr deltaShift
  have hne_top : (2 : ℝ≥0∞) / (p : ℝ≥0∞) ≠ ⊤ := by
    rw [div_eq_mul_inv]
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.inv_ne_top.mpr ?_)
    exact Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).pos.ne'
  have htr := ENNReal.toReal_mono hne_top h
  rwa [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at htr

/-- `Game.succProbability` form of the `2 / p` bound for `macCheckSoundnessGame`. -/
theorem succProbability_macCheckSoundnessGame_le {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0)
    (deltaShift : (Fin T → ZMod p) → ZMod p) :
    (Game.succProbability (ProbComp.eval (macCheckSoundnessGame p T err deltaShift)) : ℝ) ≤
      2 / (p : ℝ) :=
  toReal_eval_macCheckSoundnessGame_le herr deltaShift

/-- Standalone `MACCheck` cheating-equation bound against any prior randomized adversary
`adv : ProbComp S` that selects state `s` (fixing `err s` and `deltaShift s`) before the
independent uniform key `alpha : ZMod p` is sampled. -/
theorem eval_macCheckSoundnessAdvGame_le {p T : ℕ} [Fact (Nat.Prime p)] {S : Type}
    (adv : ProbComp S) (err : S → Fin T → ZMod p)
    (deltaShift : S → (Fin T → ZMod p) → ZMod p) :
    (ProbComp.eval (macCheckSoundnessAdvGame p T adv err deltaShift)) true ≤ 2 / (p : ℝ≥0∞) := by
  unfold macCheckSoundnessAdvGame
  rw [ProbComp.eval_bind]
  apply Cslib.Probability.PMF.bind_apply_le_on_support
  intro s _
  by_cases herr : err s = 0
  · simp [herr]
  · have heq :
        (ProbComp.eval do
          let alpha ← ProbComp.uniform (ZMod p)
          let e ← ProbComp.uniform (Fin T → ZMod p)
          return decide (err s ≠ 0 ∧ alpha * linearCombAddHom (err s) e = deltaShift s e)) =
        ProbComp.eval (macCheckSoundnessGame p T (err s) (deltaShift s)) := by
      simp only [herr, ne_eq, not_false_eq_true, true_and, macCheckSoundnessGame]
    rw [heq]
    exact eval_macCheckSoundnessGame_le herr (deltaShift s)

end Cslib.Crypto.Protocols.MPC.SPDZ
