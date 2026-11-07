/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.Beaver
public import Complexity.Probability.LinearCombination
import Complexity.Probability.PMF.Bind
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TransferInstance

/-!
# SPDZ Authenticated Secret Sharing, Online Operations, and Batch `MACCheck` Soundness

This module formalizes the SPDZ authenticated secret-sharing representation, its linear and
Beaver-triple online operations, and the two-round commit-then-open batch `MACCheck` protocol and
its $2 / p$ soundness bound over prime fields `ZMod p` ([DamgardPastroSmartZakarias2012]):

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
   commit-then-open protocol over `Complexity.Crypto.Protocols.MPC.Basic` and
   `Complexity.Crypto.Protocols.MPC.Broadcast` checking a batch of $T$ publicly opened values via
   random linear combination weights $e \in (\mathbb{Z}_p)^T$. Honest executions satisfy
   $\sum_i \sigma_i = 0$ (`sum_checkResidual_eq_zero`) and accept with probability `1`.
4. **Residual Cheating Equation & $2 / p$ Soundness (`sum_checkResidual_eq_neg_mul`,
   `sum_checkResidual_add_eq_zero_iff`, `linearCombZeroGame`, `macCheckSoundnessGame`,
   `eval_macCheckSoundnessGame_le`, `eval_macCheckSoundness_bind_le`):** for prime `p` and any
   nonzero vector of opening errors `err ≠ 0` (even against an adaptive residual shift
   `deltaShift : (Fin T → ZMod p) → ZMod p` chosen as a function of the public weights `e`, or
   generated from prior randomized adversary state `adv : ProbComp S` independent of `alpha`),
   `MACCheck` accepts with probability at most $2 / p$:
   - Stage 1 (`eval_linearCombZeroGame_eq`): $\Pr_e[\sum_\ell e_\ell \cdot \mathrm{err}_\ell = 0]
     = 1 / p$, proved via `Cslib.Probability.uniformOfFintype_map_linearComb`.
   - Stage 2 (`card_filter_macKey_eq_le_one`, `eval_macKey_guess_le`): whenever
     $L = \sum_\ell e_\ell \cdot \mathrm{err}_\ell \neq 0$, at most one key
     $\alpha \in \mathbb{Z}_p$ satisfies $\alpha \cdot L = \Delta(e)$.

Scope note: `macCheckProtocol` is parameterized over an abstract deterministic commitment map
`commit : ZMod p → Coins → Comm` (checking equality of Round-1 commitments and Round-2 openings),
and `macCheckSoundnessGame` / `macCheckSoundnessAdvGame` analyze the standalone algebraic
information-theoretic cheating equation given an independent uniform global MAC key
$\alpha \in \mathbb{Z}_p$ and public weights $e \in (\mathbb{Z}_p)^T$ (modeling the sum
$\alpha = \sum_i \alpha_i$ when at least one party's additive key share is uniform and unknown to
the adversary), rather than a computational commitment binding reduction, UC emulation proof, or
polynomial-time simulator certificate.

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
  protocol over `Complexity.Crypto.Protocols.MPC.Basic`.
* `Cslib.Crypto.Protocols.MPC.SPDZ.errorLinearComb`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.linearCombZeroGame`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.macCheckSoundnessGame`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.macCheckSoundnessAdvGame`: weighted error combination and
  `ProbComp` soundness games.

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
* `Cslib.Crypto.Protocols.MPC.SPDZ.map_errorLinearComb_uniform`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.card_filter_errorLinearComb_eq_zero_mul_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.eval_linearCombZeroGame_eq`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.eval_linearCombZeroGame_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.toReal_eval_linearCombZeroGame_le`: Stage 1 weight-cancellation
  probability $1 / p$.
* `Cslib.Crypto.Protocols.MPC.SPDZ.card_filter_macKey_eq_le_one`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.eval_macKey_guess_le`: Stage 2 key-guessing uniqueness.
* `Cslib.Crypto.Protocols.MPC.SPDZ.eval_macCheckSoundnessGame_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.toReal_eval_macCheckSoundnessGame_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.succProbability_macCheckSoundnessGame_le`,
  `Cslib.Crypto.Protocols.MPC.SPDZ.eval_macCheckSoundness_bind_le`: concrete $2 / p$ soundness of
  SPDZ `MACCheck`.

## References

* [I. Damgård, V. Pastro, N. P. Smart, S. Zakarias, *Multiparty Computation from Somewhat
  Homomorphic Encryption*][DamgardPastroSmartZakarias2012].
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
  exact @Finset.sum_neg_distrib _ (ZMod p) _ _ _

@[simp] theorem macSum_neg {p n : ℕ} (s : AuthShare p n) :
    (-s).macSum = -s.macSum := by
  change (∑ i : Fin n, -s.macShares i) = -∑ i : Fin n, s.macShares i
  exact @Finset.sum_neg_distrib _ (ZMod p) _ _ _

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
([DamgardPastroSmartZakarias2012]). -/
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
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {p : ℕ} {Coins : Type} [AddCommMonoid Coins] :
    AddCommMonoid (ResidualOpening p Coins) :=
  (ResidualOpening.equivProd p Coins).addCommMonoid

/-- Party `i`'s local `MACCheck` residual share ([DamgardPastroSmartZakarias2012]):
`σ_i = (∑ ℓ, e_ℓ * γ(a_ℓ)_i) - α_i * (∑ ℓ, e_ℓ * (a'_ℓ + δ_ℓ))`. -/
@[expose] def checkResidual {p T : ℕ} (inp : PartyCheckInput p T) : ZMod p :=
  (∑ l : Fin T, inp.weights l * inp.macShares l) -
    inp.keyShare * ∑ l : Fin T, inp.weights l * ((inp.opened l).value + (inp.opened l).delta)

/-- Weighted linear combination `∑ ℓ, e_ℓ * err_ℓ` of opening errors `err_ℓ = a'_ℓ - a_ℓ`. -/
@[expose] def errorLinearComb {p T : ℕ} (e err : Fin T → ZMod p) : ZMod p :=
  ∑ l : Fin T, e l * err l

@[simp] theorem errorLinearComb_apply {p T : ℕ} (e err : Fin T → ZMod p) :
    errorLinearComb e err = ∑ l : Fin T, e l * err l := rfl

/-- Verify that every party's Round-2 residual opening matches its Round-1 commitment and that the
opened residual shares sum to `0` ([DamgardPastroSmartZakarias2012]). -/
@[expose] def verifyResiduals {p n : ℕ} {Coins Comm : Type} [DecidableEq Comm]
    (commit : ZMod p → Coins → Comm)
    (commits : Fin n → Comm) (openings : Fin n → ResidualOpening p Coins) : Bool :=
  decide ((∀ j : Fin n, commit (openings j).sigma (openings j).decommit = commits j) ∧
    (∑ j : Fin n, (openings j).sigma) = 0)

/-- Predicate stating that `inp : Fin n → PartyCheckInput p T` arises from validly authenticated
shares `shares : Fin T → AuthShare p n` under global key `alpha = ∑ i, α_i` with common public
`opened` values and common public `weights` `e` (allowing `opened` to differ from the true secrets
by `err_ℓ = (opened ℓ).value - (shares ℓ).secret`). -/
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

/-- Core algebraic residual identity of SPDZ `MACCheck` ([DamgardPastroSmartZakarias2012]):
when `inp` is authenticated for `shares` with claimed public openings `opened`,
`∑ i, checkResidual (inp i) = - alpha * ∑ ℓ, e_ℓ * ((opened ℓ).value - (shares ℓ).secret)`. -/
theorem sum_checkResidual_eq_neg_mul {p n T : ℕ} {alpha : ZMod p}
    {shares : Fin T → AuthShare p n} {opened : Fin T → OpenedValue p}
    {e : Fin T → ZMod p} {inp : Fin n → PartyCheckInput p T}
    (hauth : PartyCheckInput.AuthenticFor alpha shares opened e inp) :
    (∑ i : Fin n, checkResidual (inp i)) =
      -alpha * errorLinearComb e (fun l => (opened l).value - (shares l).secret) := by
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
  simp only [checkResidual, Finset.sum_sub_distrib, h1, h2, errorLinearComb_apply]
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

/-- Cheating equation equivalence ([DamgardPastroSmartZakarias2012]): adding an adversarial
residual shift `deltaOpen` to the honest residual sum yields `0` if and only if
`alpha * errorLinearComb e err = deltaOpen`. -/
theorem sum_checkResidual_add_eq_zero_iff {p n T : ℕ} {alpha : ZMod p}
    {shares : Fin T → AuthShare p n} {opened : Fin T → OpenedValue p}
    {e : Fin T → ZMod p} {inp : Fin n → PartyCheckInput p T}
    (hauth : PartyCheckInput.AuthenticFor alpha shares opened e inp) (deltaOpen : ZMod p) :
    (∑ i : Fin n, checkResidual (inp i)) + deltaOpen = 0 ↔
      alpha * errorLinearComb e (fun l => (opened l).value - (shares l).secret) = deltaOpen := by
  rw [sum_checkResidual_eq_neg_mul hauth]
  constructor <;> intro h <;> linear_combination -h

/-- Schedule for the two-round commit-then-open `macCheckProtocol`: Round 1 broadcasts commitments
`Comm` and Round 2 broadcasts `ResidualOpening p Coins`. -/
@[expose, reducible] def macCheckSchedule (p n : ℕ) (Coins Comm : Type) : Schedule n noOracleSpec :=
  broadcastSchedule n noOracleSpec Comm ++
    broadcastSchedule n noOracleSpec (ResidualOpening p Coins)

/-- Two-round commit-then-open `MACCheck` protocol over `Complexity.Crypto.Protocols.MPC.Basic`
([DamgardPastroSmartZakarias2012]):
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

/-! ### Concrete $2 / p$ soundness of SPDZ `MACCheck` over prime fields -/

/-- Stage-1 `ProbComp` game testing whether random weights `e ← ProbComp.uniform (Fin T → ZMod p)`
annihilate a fixed nonzero error vector `err : Fin T → ZMod p`. -/
noncomputable def linearCombZeroGame (p T : ℕ) [NeZero p] (err : Fin T → ZMod p) :
    ProbComp Bool := do
  let e ← ProbComp.uniform (Fin T → ZMod p)
  return decide (errorLinearComb e err = 0)

/-- Full SPDZ `MACCheck` soundness game ([DamgardPastroSmartZakarias2012]): samples an independent
uniform MAC key `alpha ← ProbComp.uniform (ZMod p)` and public weights
`e ← ProbComp.uniform (Fin T → ZMod p)`, and tests whether the adversary's (possibly `e`-adaptive)
residual shift `deltaShift e` satisfies the cheating equation
`alpha * errorLinearComb e err = deltaShift e`. -/
noncomputable def macCheckSoundnessGame (p T : ℕ) [NeZero p]
    (err : Fin T → ZMod p) (deltaShift : (Fin T → ZMod p) → ZMod p) : ProbComp Bool := do
  let alpha ← ProbComp.uniform (ZMod p)
  let e ← ProbComp.uniform (Fin T → ZMod p)
  return decide (alpha * errorLinearComb e err = deltaShift e)

/-- Stateful randomized-adversary `MACCheck` soundness game (paralleling
`Complexity.Crypto.Protocols.VOLE.MulCheck`): an arbitrary prior computation `adv : ProbComp S`
selects state `s` determining both the opening error vector `err s` and the `e`-adaptive shift
`deltaShift s` before the independent key `alpha` is sampled, winning if `err s ≠ 0` and
`alpha * errorLinearComb e (err s) = deltaShift s e`. -/
noncomputable def macCheckSoundnessAdvGame (p T : ℕ) [NeZero p] {S : Type}
    (adv : ProbComp S) (err : S → Fin T → ZMod p)
    (deltaShift : S → (Fin T → ZMod p) → ZMod p) : ProbComp Bool := do
  let s ← adv
  let alpha ← ProbComp.uniform (ZMod p)
  let e ← ProbComp.uniform (Fin T → ZMod p)
  return decide (err s ≠ 0 ∧ alpha * errorLinearComb e (err s) = deltaShift s e)

/-- For prime `p` and any nonzero error vector `err ≠ 0`, `errorLinearComb · err` maps the uniform
distribution on `Fin T → ZMod p` to the uniform distribution on `ZMod p` (via
`Cslib.Probability.uniformOfFintype_map_linearComb`). -/
theorem map_errorLinearComb_uniform {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0) :
    (PMF.uniformOfFintype (Fin T → ZMod p)).map (fun e => errorLinearComb e err) =
      PMF.uniformOfFintype (ZMod p) := by
  obtain ⟨l₀, hl₀⟩ := Function.ne_iff.mp herr
  exact uniformOfFintype_map_linearComb hl₀

/-- Stage-1 rank-nullity counting bound: for prime `p` and `err ≠ 0`, the hyperplane
`{e : Fin T → ZMod p | errorLinearComb e err = 0}` has cardinality satisfying `card * p ≤ p ^ T`
(in fact equality holds, via `Cslib.Probability.card_mul_card_filter_eq_of_shift`). -/
theorem card_filter_errorLinearComb_eq_zero_mul_le {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0) :
    (Finset.univ.filter fun e : Fin T → ZMod p => errorLinearComb e err = 0).card * p ≤
      p ^ T := by
  obtain ⟨l₀, hl₀⟩ := Function.ne_iff.mp herr
  have hshift : ∀ c : ZMod p, ∃ σ : Equiv.Perm (Fin T → ZMod p),
      ∀ e, errorLinearComb (σ e) err = errorLinearComb e err + c := by
    intro c
    obtain ⟨g, rfl⟩ := linearCombAddHom_surjective hl₀ c
    refine ⟨Equiv.addRight g, fun e => ?_⟩
    simpa only [Equiv.coe_addRight, errorLinearComb, linearCombAddHom_apply] using
      (linearCombAddHom err).map_add e g
  have hcard := card_mul_card_filter_eq_of_shift (f := fun e => errorLinearComb e err) hshift 0
  simp only [ZMod.card, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hcard
  linarith

/-- Stage 1 exact probability: for prime `p` and `err ≠ 0`, `linearCombZeroGame p T err` outputs
`true` with exact probability `p⁻¹`. -/
theorem eval_linearCombZeroGame_eq {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0) :
    (ProbComp.eval (linearCombZeroGame p T err)) true = (p : ℝ≥0∞)⁻¹ := by
  simp only [linearCombZeroGame, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_uniform]
  have hcomp :
      (PMF.uniformOfFintype (Fin T → ZMod p)).map (fun e => decide (errorLinearComb e err = 0)) =
        ((PMF.uniformOfFintype (Fin T → ZMod p)).map (fun e => errorLinearComb e err)).map
          (fun v => decide (v = 0)) := by
    rw [PMF.map_comp]; rfl
  rw [hcomp, map_errorLinearComb_uniform herr, PMF.map_apply]
  rw [tsum_eq_single (0 : ZMod p)]
  · simp [PMF.uniformOfFintype_apply, ZMod.card]
  · intro v hv
    simp [hv]

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

/-- Stage-2 key-guessing uniqueness: for prime `p` and any nonzero field element `L ≠ 0`, at most
one key `alpha : ZMod p` satisfies `alpha * L = d`. -/
theorem card_filter_macKey_eq_le_one {p : ℕ} [Fact (Nat.Prime p)]
    {L : ZMod p} (hL : L ≠ 0) (d : ZMod p) :
    (Finset.univ.filter fun alpha : ZMod p => alpha * L = d).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a₁ ha₁ a₂ ha₂ => ?_
  have h₁ := (Finset.mem_filter.mp ha₁).2
  have h₂ := (Finset.mem_filter.mp ha₂).2
  exact mul_right_cancel₀ hL (h₁.trans h₂.symm)

/-- Stage-2 pointwise key-guessing bound: for any `L, d : ZMod p`, a uniform key `alpha : ZMod p`
satisfies `alpha * L = d` with probability at most `(if L = 0 then 1 else 0) + p⁻¹`. -/
theorem eval_macKey_guess_le {p : ℕ} [Fact (Nat.Prime p)] (L d : ZMod p) :
    ((PMF.uniformOfFintype (ZMod p)).map fun alpha => decide (alpha * L = d)) true ≤
      (if L = 0 then (1 : ℝ≥0∞) else 0) + (p : ℝ≥0∞)⁻¹ := by
  by_cases hL : L = 0
  · simp only [hL, ↓reduceIte]
    exact (PMF.coe_le_one _ _).trans le_self_add
  · simp only [hL, ↓reduceIte, zero_add]
    rw [PMF.map_apply, tsum_eq_single (d * L⁻¹)]
    · by_cases hsat : (d * L⁻¹) * L = d
      · simp [hsat, PMF.uniformOfFintype_apply, ZMod.card]
      · simp [hsat]
    · intro alpha hne
      have hmul : alpha * L ≠ d := fun h => hne (by rw [← h, mul_inv_cancel_right₀ hL])
      simp [hmul]

/-- Concrete $2 / p$ soundness of SPDZ `MACCheck` ([DamgardPastroSmartZakarias2012]): for prime
`p`, any nonzero opening error vector `err ≠ 0`, and any `e`-adaptive residual shift `deltaShift`,
`macCheckSoundnessGame p T err deltaShift` outputs `true` with probability at most `2 / p`. -/
theorem eval_macCheckSoundnessGame_le {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0)
    (deltaShift : (Fin T → ZMod p) → ZMod p) :
    (ProbComp.eval (macCheckSoundnessGame p T err deltaShift)) true ≤ 2 / (p : ℝ≥0∞) := by
  simp only [macCheckSoundnessGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm, PMF.bind_apply]
  let S : Finset (Fin T → ZMod p) :=
    Finset.univ.filter fun e : Fin T → ZMod p => errorLinearComb e err = 0
  have hpoint : ∀ e : Fin T → ZMod p,
      ((PMF.uniformOfFintype (ZMod p)).bind
        (fun alpha => PMF.pure (decide (alpha * errorLinearComb e err = deltaShift e)))) true ≤
      (if e ∈ S then (1 : ℝ≥0∞) else 0) + (p : ℝ≥0∞)⁻¹ := by
    intro e
    have hm :
        ((PMF.uniformOfFintype (ZMod p)).bind
          (fun alpha => PMF.pure (decide (alpha * errorLinearComb e err = deltaShift e)))) =
        (PMF.uniformOfFintype (ZMod p)).map
          (fun alpha => decide (alpha * errorLinearComb e err = deltaShift e)) := by
      rw [PMF.map]; rfl
    rw [hm]
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using
      eval_macKey_guess_le (errorLinearComb e err) (deltaShift e)
  have hμ : ∀ e : Fin T → ZMod p,
      PMF.uniformOfFintype (Fin T → ZMod p) e ≤ ((p : ℝ≥0∞) ^ T)⁻¹ := by
    intro e
    simp [PMF.uniformOfFintype_apply, ZMod.card]
  have hsum :=
    Cslib.Probability.PMF.tsum_mul_le_card_mul_add
      (PMF.uniformOfFintype (Fin T → ZMod p)) hμ S hpoint
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp_ne_zero : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
  have hp_ne_top : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hpT_ne_zero : (p : ℝ≥0∞) ^ T ≠ 0 := pow_ne_zero T hp_ne_zero
  have hpT_ne_top : (p : ℝ≥0∞) ^ T ≠ ⊤ := ENNReal.pow_ne_top hp_ne_top
  have hcard_cast : (S.card : ℝ≥0∞) * (p : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ T := by
    exact_mod_cast card_filter_errorLinearComb_eq_zero_mul_le herr
  have hstage1 : (S.card : ℝ≥0∞) * ((p : ℝ≥0∞) ^ T)⁻¹ ≤ (p : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le, mul_right_comm]
    calc (S.card : ℝ≥0∞) * (p : ℝ≥0∞) * ((p : ℝ≥0∞) ^ T)⁻¹
        ≤ (p : ℝ≥0∞) ^ T * ((p : ℝ≥0∞) ^ T)⁻¹ := by gcongr
      _ = 1 := ENNReal.mul_inv_cancel hpT_ne_zero hpT_ne_top
  calc ∑' e, PMF.uniformOfFintype (Fin T → ZMod p) e *
        ((PMF.uniformOfFintype (ZMod p)).bind
          (fun alpha => PMF.pure (decide (alpha * errorLinearComb e err = deltaShift e)))) true
      ≤ S.card * ((p : ℝ≥0∞) ^ T)⁻¹ + (p : ℝ≥0∞)⁻¹ := hsum
    _ ≤ (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ := by gcongr
    _ = 2 / (p : ℝ≥0∞) := by rw [div_eq_mul_inv, two_mul]

/-- Real-valued `2 / p` soundness bound for `macCheckSoundnessGame`. -/
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

/-- `Game.succProbability` form of the `2 / p` soundness bound for `macCheckSoundnessGame`. -/
theorem succProbability_macCheckSoundnessGame_le {p T : ℕ} [Fact (Nat.Prime p)]
    {err : Fin T → ZMod p} (herr : err ≠ 0)
    (deltaShift : (Fin T → ZMod p) → ZMod p) :
    (Game.succProbability (ProbComp.eval (macCheckSoundnessGame p T err deltaShift)) : ℝ) ≤
      2 / (p : ℝ) :=
  toReal_eval_macCheckSoundnessGame_le herr deltaShift

/-- Soundness of `MACCheck` against any prior randomized adversary `adv : ProbComp S` that selects
state `s` (fixing `err s` and `deltaShift s`) before the independent uniform key `alpha : ZMod p`
is sampled. -/
theorem eval_macCheckSoundness_bind_le {p T : ℕ} [Fact (Nat.Prime p)] {S : Type}
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
          return decide (err s ≠ 0 ∧ alpha * errorLinearComb e (err s) = deltaShift s e)) =
        ProbComp.eval (macCheckSoundnessGame p T (err s) (deltaShift s)) := by
      simp only [herr, ne_eq, not_false_eq_true, true_and, macCheckSoundnessGame]
    rw [heq]
    exact eval_macCheckSoundnessGame_le herr (deltaShift s)

end Cslib.Crypto.Protocols.MPC.SPDZ
