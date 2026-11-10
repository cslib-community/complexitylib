/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Computability.Interactive.Security.Repeat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT

/-!
# Eavesdropping security of Schnorr identification in the strict-PPT model

In an eavesdropping attack on an identification scheme ([BonehShoup2023], Section 18.2, Attack
Game 18.2), the adversary first overhears `Q n` honest conversations between the prover and the
verifier for the public key `u = α • g` before attempting impersonation. For an idealized simulator
that samples `ZMod q` uniformly, special HVZK makes simulated conversations identically distributed
to honest ones ([BonehShoup2023], Theorems 19.3 and 19.5; `schnorr_eavesdropAttack_eq_directAttack`
in `CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrIdentification`).

In the uniform strict-PPT model, fair-coin machines with a fixed polynomial clock cannot sample
`ZMod q` exactly when the prime group order `q` is not a power of two. Instead, exponent sampling
uses `F.sampleExp n d` (`ProbComp.sampleModNat`), which is within statistical distance `1 / 2 ^ n`
of uniform on `ZMod q` (`closeTo_uniform_sampleExp`). Consequently:

* **Per-conversation statistical closeness**:
  * A strict-PPT simulated conversation `schnorrSimulatedTranscript` (using `schnorrSimulateWord` on
    the public key without the secret key) is within statistical distance (`CloseTo`)
    `1 / 2 ^ n` of an ideal honest conversation `schnorrHonestTranscript`
    (`closeTo_schnorrHonestTranscript_simulated`).
  * A strict-PPT honest conversation `schnorrRealTranscript` (where the honest prover also samples
    its commitment exponent with `sampleExp`) is within `1 / 2 ^ n` of `schnorrHonestTranscript`
    (`closeTo_schnorrRealTranscript_honest`) and hence within `2 / 2 ^ n` of
    `schnorrSimulatedTranscript` (`closeTo_schnorrRealTranscript_simulated`).
* **Multi-conversation statistical closeness**:
  * Across `Q` independent conversations over the infinite word space
    `List (List Bool × List Bool × List Bool)`, `CloseTo.iid`, `CloseTo.iid_replicate`, and
    `CloseTo.eval_replicate` bound the statistical distance by `Q / 2 ^ n` against ideal honest
    conversations (`closeTo_iid_schnorrHonestTranscript_replicate_simulated`) and by
    `2 * Q / 2 ^ n` against strict-PPT honest conversations
    (`closeTo_replicate_schnorrRealTranscript_simulated`).
* **Reduction to direct attacks and discrete logarithms**:
  * `SchnorrEavesdropAdversary.toDirect` converts any eavesdropping adversary `A` into a direct
    impersonator that generates `Q n` simulated conversations on the public key before running
    `A.commit`. It is uniform strict PPT whenever `A`, the challenge length `k`, and the
    conversation count `Q` are (`isPPT_toDirect`, `isPPTOn_rewind_toDirect`).
  * At each security parameter where every supported group has order at least `2 ^ k n`,
    `succProbability_schnorrIdealEavesdropGame_le` and `succProbability_schnorrEavesdropGame_le`
    give the explicit bounds

      `ε ≤ Q n / 2 ^ n + 1 / 2 ^ k n + √ε'`   and   `ε ≤ 2 * Q n / 2 ^ n + 1 / 2 ^ k n + √ε'`,

    where `ε'` is the discrete-logarithm success probability of the rewinding extractor
    `((A.toDirect k Q).rewind k)`.
  * Under the discrete-logarithm assumption `F.DiscreteLog setup`, for any polynomial-time `k` and
    `Q` with negligible `1 / 2 ^ k n`, every uniform strict PPT eavesdropping adversary succeeds
    with negligible probability (`negligible_schnorrEavesdropGame`,
    `negligible_schnorrIdealEavesdropGame`, `schnorr_isEavesdropSecure_of_discreteLogHard`,
    `schnorr_isIdealEavesdropSecure_of_discreteLogHard`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrEavesdropAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrEavesdropAdversary.IsPPT`: two-stage eavesdropping
  adversaries and uniform strict PPT admissibility.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrHonestTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRealTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSimulatedTranscript`: ideal honest, strict-PPT honest,
  and strict-PPT simulated Schnorr conversations with `m`-bit challenges.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrEavesdropGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrIdealEavesdropGame`: eavesdropping attack games with
  strict-PPT and ideal honest conversations ([BonehShoup2023], Attack Game 18.2).
* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrEavesdropAdversary.toDirect`: reduction from an
  eavesdropping adversary to a direct impersonator by simulating `Q n` conversations.
* `Cslib.Crypto.PrimeOrderGroupFamily.IsEavesdropSecure`,
  `Cslib.Crypto.PrimeOrderGroupFamily.IsIdealEavesdropSecure`: security against all uniform strict
  PPT eavesdropping adversaries for all polynomial-time conversation counts.

## Main results

* `Cslib.Probability.CloseTo.iid`, `Cslib.Probability.CloseTo.iid_replicate`,
  `Cslib.Probability.CloseTo.eval_replicate`: statistical closeness of `k` independent draws and
  `OracleComp.replicate` runs without finiteness assumptions.
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_schnorrRealTranscript_honest`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_schnorrHonestTranscript_simulated`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_schnorrRealTranscript_simulated`: per-conversation
  statistical closeness (`1 / 2 ^ n` and `2 / 2 ^ n`).
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_iid_schnorrHonestTranscript_replicate_simulated`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_replicate_schnorrRealTranscript_simulated`:
  `Q`-conversation statistical closeness (`Q / 2 ^ n` and `2 * Q / 2 ^ n`).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_schnorrIdealEavesdropGame_schnorrDirectGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_schnorrEavesdropGame_schnorrDirectGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_schnorrIdealEavesdropGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_schnorrEavesdropGame_le`: quantitative
  eavesdropping-to-direct and eavesdropping-to-DL bounds (Theorems 19.3 and 19.5).
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrRealTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrSimulatedTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_toDirect`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_rewind_toDirect`: strict-PPT certificates for
  conversation generation, the direct-attack reduction, and the composed rewinding DL adversary.
* `Cslib.Crypto.PrimeOrderGroupFamily.negligible_schnorrIdealEavesdropGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.negligible_schnorrEavesdropGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorr_isIdealEavesdropSecure_of_discreteLogHard`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorr_isEavesdropSecure_of_discreteLogHard`: eavesdropping
  security of Schnorr identification under the discrete-logarithm assumption.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 18.2 and 19.1 (Attack Game 18.2 and Theorems 19.1, 19.3,
  and 19.5).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Theorem 13.2.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Interactive
open scoped ENNReal NNReal

variable {F : PrimeOrderGroupFamily}

/-- Encoding of a single Schnorr conversation `(t, c, z)` of bit words. -/
abbrev encTranscript : (List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

variable (F) in
/-- A uniform eavesdropping adversary against Schnorr identification ([BonehShoup2023], Attack
Game 18.2). Its first stage sees the security parameter, the group description, the encoded public
key, and a list of overheard conversations `(t, c, z)`, and returns a commitment word and a state
word; its second stage sees the security parameter, the state and the challenge word. -/
structure SchnorrEavesdropAdversary where
  /-- Commit from the group description, encoded public key and overheard conversations, keeping a
  state word. -/
  commit : ℕ → F.Desc × List Bool × List (List Bool × List Bool × List Bool) →
    ProbComp (List Bool × List Bool)
  /-- Respond to a challenge word from the state word. -/
  respond : ℕ → List Bool × List Bool → ProbComp (List Bool)

/-- Both stages of an eavesdropping adversary are uniform strict PPT in their whole inputs. -/
def SchnorrEavesdropAdversary.IsPPT (A : F.SchnorrEavesdropAdversary) : Prop :=
  IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encList encTranscript))))
      (encPair encBits encBits) (fun input => A.commit input.1 input.2) ∧
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun input => A.respond input.1 input.2)

/-! ### Ideal honest, strict-PPT honest, and strict-PPT simulated conversations -/

variable (F) in
/-- An ideal honest Schnorr conversation with an `m`-bit challenge ([BonehShoup2023], Section 19.1):
sample a uniform commitment exponent `r : ZMod (F.order d)` and a uniform `m`-bit challenge `c`,
and output the encoded commitment `r • g`, the challenge `c`, and the binary response
`(r + c * α).val.bits`. -/
noncomputable def schnorrHonestTranscript (d : F.Desc) (α : ZMod (F.order d)) (m : ℕ) :
    PMF (List Bool × List Bool × List Bool) := do
  let r ← PMF.uniformOfFintype (ZMod (F.order d))
  let c ← BitString.uniformList m
  return (F.encode d (r • F.generator d), c,
    (r + (ofBits c : ZMod (F.order d)) * α).val.bits)

variable (F) in
/-- A strict-PPT honest Schnorr conversation at security parameter `n` with an `m`-bit challenge:
sample the commitment exponent `r` with `F.sampleExp n d` and the challenge `c` with
`BitString.sampleList m`, and output `(encode (r • g), c, ((r + ofBits c * α) % q).bits)`. -/
noncomputable def schnorrRealTranscript (n : ℕ) (d : F.Desc) (α : ZMod (F.order d)) (m : ℕ) :
    ProbComp (List Bool × List Bool × List Bool) := do
  let r ← F.sampleExp n d
  let c ← BitString.sampleList m
  return (F.smul (d, r, F.encode d (F.generator d)), c,
    ((r + ofBits c * α.val) % F.order d).bits)

variable (F) in
/-- A strict-PPT simulated Schnorr conversation at security parameter `n` with an `m`-bit
challenge ([BonehShoup2023], Example 19.3 and Theorem 19.3): sample a uniform `m`-bit challenge `c`
and run `F.schnorrSimulateWord ((n, d), u, c)` on the encoded public key `u` to obtain `(t, z)`,
returning `(t, c, z)` without using the secret key. -/
noncomputable def schnorrSimulatedTranscript (n : ℕ) (d : F.Desc) (u : List Bool) (m : ℕ) :
    ProbComp (List Bool × List Bool × List Bool) := do
  let c ← BitString.sampleList m
  let tz ← F.schnorrSimulateWord ((n, d), u, c)
  return (tz.1, c, tz.2)

/-! ### Statistical closeness of single and repeated conversations -/

private theorem eval_schnorrRealTranscript (n : ℕ) (d : F.Desc) (α : ZMod (F.order d)) (m : ℕ) :
    ProbComp.eval (F.schnorrRealTranscript n d α m) =
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).bind fun r =>
        (BitString.uniformList m).map fun c =>
          (F.encode d (r • F.generator d), c,
            (r + (ofBits c : ZMod (F.order d)) * α).val.bits) := by
  have hresp (r : ℕ) (c : List Bool) :
      (r + ofBits c * α.val) % F.order d =
        ((r : ZMod (F.order d)) + (ofBits c : ZMod (F.order d)) * α).val := by
    rw [← ZMod.val_natCast (F.order d), Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  simp only [schnorrRealTranscript, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.bind_map, Function.comp_def, F.smul_encode, hresp]
  refine congrArg (PMF.bind _) (funext fun r => ?_)
  rw [← PMF.bind_pure_comp]
  rfl

private theorem eval_schnorrSimulateWord_bits (n : ℕ) (d : F.Desc) (u : F.Carrier d)
    (c : List Bool) :
    ProbComp.eval (F.schnorrSimulateWord ((n, d), F.encode d u, c)) =
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map
        fun z => (F.encode d (z • F.generator d - (ofBits c : ZMod (F.order d)) • u),
          z.val.bits) := by
  have hneg : ((F.order d - ofBits c % F.order d : ℕ) : ZMod (F.order d)) =
      -(ofBits c : ZMod (F.order d)) := by
    rw [Nat.cast_sub (Nat.mod_lt _ (F.prime_order d).pos).le, ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  rw [schnorrSimulateWord, ProbComp.eval_bind, PMF.map_comp]
  simp only [ProbComp.eval_pure, F.smul_encode, F.add_encode, hneg, neg_smul, ← sub_eq_add_neg]
  rw [← PMF.bind_pure_comp]
  congr 1 with a : 1
  simp only [Function.comp_apply, ZMod.val_natCast]

private theorem eval_schnorrSimulatedTranscript (n : ℕ) (d : F.Desc) (u : F.Carrier d) (m : ℕ) :
    ProbComp.eval (F.schnorrSimulatedTranscript n d (F.encode d u) m) =
      (BitString.uniformList m).bind fun c =>
        ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map
          fun z => (F.encode d (z • F.generator d - (ofBits c : ZMod (F.order d)) • u),
            c, z.val.bits) := by
  rw [schnorrSimulatedTranscript, ProbComp.eval_bind, BitString.eval_sampleList]
  refine congrArg (PMF.bind _) (funext fun c => ?_)
  rw [ProbComp.eval_bind, eval_schnorrSimulateWord_bits, PMF.bind_map, ← PMF.bind_pure_comp]
  rfl

private theorem schnorrHonestTranscript_eq_bind_uniform (d : F.Desc) (α : ZMod (F.order d))
    (m : ℕ) :
    F.schnorrHonestTranscript d α m =
      (BitString.uniformList m).bind fun c =>
        (PMF.uniformOfFintype (ZMod (F.order d))).map fun z =>
          (F.encode d (z • F.generator d - (ofBits c : ZMod (F.order d)) • (α • F.generator d)),
            c, z.val.bits) := by
  simp only [schnorrHonestTranscript, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun c => ?_)
  conv_lhs =>
    rw [← PMF.uniformOfFintype_map_equiv (Equiv.subRight ((ofBits c : ZMod (F.order d)) * α))]
  rw [PMF.bind_map, ← PMF.bind_pure_comp]
  congr 1 with z : 1
  simp only [Function.comp_apply, Equiv.subRight_apply, sub_smul, mul_smul, sub_add_cancel]

variable (F) in
/-- A strict-PPT honest Schnorr conversation is within statistical distance `1 / 2 ^ n` of an ideal
honest conversation. -/
theorem closeTo_schnorrRealTranscript_honest (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m : ℕ) :
    CloseTo (ProbComp.eval (F.schnorrRealTranscript n d α m))
      (F.schnorrHonestTranscript d α m) (1 / 2 ^ n : ℝ≥0) := by
  rw [eval_schnorrRealTranscript, schnorrHonestTranscript]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ← PMF.bind_pure_comp]
  exact (F.closeTo_uniform_sampleExp n d).symm.bind_left _

variable (F) in
/-- An ideal honest Schnorr conversation is within statistical distance `1 / 2 ^ n` of a strict-PPT
simulated conversation on the public key `encode (α • g)`. -/
theorem closeTo_schnorrHonestTranscript_simulated (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m : ℕ) :
    CloseTo (F.schnorrHonestTranscript d α m)
      (ProbComp.eval (F.schnorrSimulatedTranscript n d (F.encode d (α • F.generator d)) m))
      (1 / 2 ^ n : ℝ≥0) := by
  rw [schnorrHonestTranscript_eq_bind_uniform, eval_schnorrSimulatedTranscript]
  exact CloseTo.bind_right (BitString.uniformList m) fun c _ =>
    (F.closeTo_uniform_sampleExp n d).map _

variable (F) in
/-- A strict-PPT honest Schnorr conversation is within statistical distance `2 / 2 ^ n` of a
strict-PPT simulated conversation on the public key `encode (α • g)`. -/
theorem closeTo_schnorrRealTranscript_simulated (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m : ℕ) :
    CloseTo (ProbComp.eval (F.schnorrRealTranscript n d α m))
      (ProbComp.eval (F.schnorrSimulatedTranscript n d (F.encode d (α • F.generator d)) m))
      (2 / 2 ^ n : ℝ≥0) := by
  have h := (F.closeTo_schnorrRealTranscript_honest n d α m).trans
    (F.closeTo_schnorrHonestTranscript_simulated n d α m)
  have hadd : ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) + ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) = (2 / 2 ^ n : ℝ≥0) := by
    rw [← ENNReal.coe_add]
    congr 1
    ring
  rwa [hadd] at h

variable (F) in
/-- `Q` independent ideal honest Schnorr conversations are within statistical distance `Q / 2 ^ n`
of `Q` strict-PPT simulated conversations on the public key `encode (α • g)`. -/
theorem closeTo_iid_schnorrHonestTranscript_replicate_simulated (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m Q : ℕ) :
    CloseTo ((PMF.iid (F.schnorrHonestTranscript d α m) Q).map List.ofFn)
      (ProbComp.eval (OracleComp.replicate Q
        (F.schnorrSimulatedTranscript n d (F.encode d (α • F.generator d)) m)))
      (Q / 2 ^ n : ℝ≥0) := by
  have h := (F.closeTo_schnorrHonestTranscript_simulated n d α m).iid_replicate Q
  have hmul : (Q : ℝ≥0∞) * ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) = (Q / 2 ^ n : ℝ≥0) := by
    rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, mul_one_div]
  rwa [hmul] at h

variable (F) in
/-- `Q` independent strict-PPT honest Schnorr conversations are within statistical distance
`2 * Q / 2 ^ n` of `Q` strict-PPT simulated conversations on the public key `encode (α • g)`. -/
theorem closeTo_replicate_schnorrRealTranscript_simulated (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m Q : ℕ) :
    CloseTo
      (ProbComp.eval (OracleComp.replicate Q (F.schnorrRealTranscript n d α m)))
      (ProbComp.eval (OracleComp.replicate Q
        (F.schnorrSimulatedTranscript n d (F.encode d (α • F.generator d)) m)))
      (2 * Q / 2 ^ n : ℝ≥0) := by
  have h := (F.closeTo_schnorrRealTranscript_simulated n d α m).eval_replicate Q
  have hmul : (Q : ℝ≥0∞) * ((2 / 2 ^ n : ℝ≥0) : ℝ≥0∞) = (2 * Q / 2 ^ n : ℝ≥0) := by
    rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul]
    congr 1
    ring
  rwa [hmul] at h

/-! ### Eavesdropping games and reduction to direct attacks -/

variable (F) in
/-- The eavesdropping impersonation attack on Schnorr identification in the strict-PPT model
([BonehShoup2023], Attack Game 18.2): before committing, the adversary overhears `Q n` independent
conversations generated by the strict-PPT honest prover (`schnorrRealTranscript`) with `k n`-bit
challenges. -/
noncomputable def schnorrEavesdropGame (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let views ← ProbComp.eval (OracleComp.replicate (Q n) (F.schnorrRealTranscript n d α (k n)))
  let ts ← ProbComp.eval (A.commit n (d, F.encode d (α • F.generator d), views))
  let c ← BitString.uniformList (k n)
  let z ← ProbComp.eval (A.respond n (ts.2, c))
  return decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
    (ofBits c : ZMod (F.order d)) • (α • F.generator d)))

variable (F) in
/-- The eavesdropping impersonation attack on Schnorr identification with exact honest
conversations ([BonehShoup2023], Attack Game 18.2): before committing, the adversary overhears
`Q n` independent ideal honest conversations (`schnorrHonestTranscript`) with `k n`-bit
challenges. -/
noncomputable def schnorrIdealEavesdropGame (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let views ← (PMF.iid (F.schnorrHonestTranscript d α (k n)) (Q n)).map List.ofFn
  let ts ← ProbComp.eval (A.commit n (d, F.encode d (α • F.generator d), views))
  let c ← BitString.uniformList (k n)
  let z ← ProbComp.eval (A.respond n (ts.2, c))
  return decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
    (ofBits c : ZMod (F.order d)) • (α • F.generator d)))

/-- Turn an eavesdropping adversary into a direct impersonator ([BonehShoup2023], Theorem 19.3 and
Figure 19.2): before committing, simulate `Q n` conversations on the public key using
`schnorrSimulatedTranscript`. -/
noncomputable def SchnorrEavesdropAdversary.toDirect (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) : F.SchnorrImpersonator where
  commit n := fun (d, u) => do
    let views ← OracleComp.replicate (Q n) (F.schnorrSimulatedTranscript n d u (k n))
    A.commit n (d, u, views)
  respond := A.respond

/-- Replacing `Q n` ideal honest conversations by strict-PPT simulated ones changes the game
advantage by at most `Q n / 2 ^ n`. -/
theorem advantage_schnorrIdealEavesdropGame_schnorrDirectGame_le
    (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ) (A : F.SchnorrEavesdropAdversary) (n : ℕ) :
    Game.advantage (F.schnorrIdealEavesdropGame setup k Q A n)
      (F.schnorrDirectGame setup k (A.toDirect k Q) n) ≤ Q n / 2 ^ n := by
  simp only [schnorrIdealEavesdropGame, schnorrDirectGame, SchnorrEavesdropAdversary.toDirect,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
  refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  refine Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun α => ?_
  exact Game.advantage_bind_le_of_closeTo
    (F.closeTo_iid_schnorrHonestTranscript_replicate_simulated n d α (k n) (Q n)) _

/-- Replacing `Q n` strict-PPT honest conversations by strict-PPT simulated ones changes the game
advantage by at most `2 * Q n / 2 ^ n`. -/
theorem advantage_schnorrEavesdropGame_schnorrDirectGame_le
    (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ) (A : F.SchnorrEavesdropAdversary) (n : ℕ) :
    Game.advantage (F.schnorrEavesdropGame setup k Q A n)
      (F.schnorrDirectGame setup k (A.toDirect k Q) n) ≤ 2 * Q n / 2 ^ n := by
  simp only [schnorrEavesdropGame, schnorrDirectGame, SchnorrEavesdropAdversary.toDirect,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
  refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  refine Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun α => ?_
  exact Game.advantage_bind_le_of_closeTo
    (F.closeTo_replicate_schnorrRealTranscript_simulated n d α (k n) (Q n)) _

/-- **Schnorr identification against eavesdropping with ideal honest conversations, exact form**
([BonehShoup2023], Theorems 19.3 and 19.5): at each security parameter where every supported group
has at least `2 ^ k n` elements, an eavesdropper's success probability is at most
`Q n / 2 ^ n + 1 / 2 ^ k n + √ε'`, where `ε'` is the discrete-logarithm success probability of the
rewinding adversary `(A.toDirect k Q).rewind k`. -/
theorem succProbability_schnorrIdealEavesdropGame_le
    (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ) (A : F.SchnorrEavesdropAdversary) (n : ℕ)
    (hkq : ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d) :
    (Game.succProbability (F.schnorrIdealEavesdropGame setup k Q A n) : ℝ) ≤
      Q n / 2 ^ n + 1 / 2 ^ k n +
        √(Game.succProbability (F.discreteLogGame setup ((A.toDirect k Q).rewind k) n)) := by
  have hhop : Game.succProbability (F.schnorrIdealEavesdropGame setup k Q A n) ≤
      Q n / 2 ^ n + Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) := by
    calc Game.succProbability (F.schnorrIdealEavesdropGame setup k Q A n)
        ≤ Game.advantage (F.schnorrIdealEavesdropGame setup k Q A n)
            (F.schnorrDirectGame setup k (A.toDirect k Q) n) +
          Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) := by
          simpa only [Game.advantage_pure_false] using
            Game.advantage_triangle
              (F.schnorrIdealEavesdropGame setup k Q A n)
              (F.schnorrDirectGame setup k (A.toDirect k Q) n)
              (PMF.pure false)
      _ ≤ Q n / 2 ^ n +
          Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) :=
        add_le_add (advantage_schnorrIdealEavesdropGame_schnorrDirectGame_le setup k Q A n) le_rfl
  have hhopR : (Game.succProbability (F.schnorrIdealEavesdropGame setup k Q A n) : ℝ) ≤
      Q n / 2 ^ n +
        (Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) : ℝ) := by
    exact_mod_cast hhop
  have hdir := succProbability_schnorrDirectGame_le setup k (A.toDirect k Q) n hkq
  linarith

/-- **Schnorr identification against eavesdropping in the strict-PPT model, exact form**
([BonehShoup2023], Theorems 19.3 and 19.5): at each security parameter where every supported group
has at least `2 ^ k n` elements, an eavesdropper's success probability is at most
`2 * Q n / 2 ^ n + 1 / 2 ^ k n + √ε'`, where `ε'` is the discrete-logarithm success probability of
the rewinding adversary `(A.toDirect k Q).rewind k`. -/
theorem succProbability_schnorrEavesdropGame_le
    (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ) (A : F.SchnorrEavesdropAdversary) (n : ℕ)
    (hkq : ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d) :
    (Game.succProbability (F.schnorrEavesdropGame setup k Q A n) : ℝ) ≤
      2 * Q n / 2 ^ n + 1 / 2 ^ k n +
        √(Game.succProbability (F.discreteLogGame setup ((A.toDirect k Q).rewind k) n)) := by
  have hhop : Game.succProbability (F.schnorrEavesdropGame setup k Q A n) ≤
      2 * Q n / 2 ^ n + Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) := by
    calc Game.succProbability (F.schnorrEavesdropGame setup k Q A n)
        ≤ Game.advantage (F.schnorrEavesdropGame setup k Q A n)
            (F.schnorrDirectGame setup k (A.toDirect k Q) n) +
          Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) := by
          simpa only [Game.advantage_pure_false] using
            Game.advantage_triangle
              (F.schnorrEavesdropGame setup k Q A n)
              (F.schnorrDirectGame setup k (A.toDirect k Q) n)
              (PMF.pure false)
      _ ≤ 2 * Q n / 2 ^ n +
          Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) :=
        add_le_add (advantage_schnorrEavesdropGame_schnorrDirectGame_le setup k Q A n) le_rfl
  have hhopR : (Game.succProbability (F.schnorrEavesdropGame setup k Q A n) : ℝ) ≤
      2 * Q n / 2 ^ n +
        (Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) : ℝ) := by
    exact_mod_cast hhop
  have hdir := succProbability_schnorrDirectGame_le setup k (A.toDirect k Q) n hkq
  linarith

/-! ### Efficiency of conversation generation and the eavesdropping reduction -/

/-- `schnorrRealTranscript` is uniform strict PPT when the security parameter, group description,
secret exponent, and challenge length are computable in polynomial time. -/
theorem isPPTOn_schnorrRealTranscript {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc} {α : γ → ℕ} {m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hα : ComputableInPolyTime α encIn encNat)
    (hm : ComputableInPolyTime m encIn encUnary) :
    IsPPTOn encIn encTranscript
      (fun a => F.schnorrRealTranscript (n a) (d a) (α a) (m a)) := by
  have hα_val (a : γ) : ((α a : ZMod (F.order (d a)))).val = α a % F.order (d a) :=
    ZMod.val_natCast (F.order (d a)) (α a)
  unfold schnorrRealTranscript
  simp only [hα_val]
  refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
  have hm' : ComputableInPolyTime (fun p : γ × ℕ => m p.1) (encPair encIn encNat) encUnary :=
    hm.comp (by fun_prop)
  refine hm'.sampleList.bind_with ?_
  let encMid := encPair (encPair encIn encNat) encBits
  have hd' : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => d p.1.1) encMid F.encDesc :=
    hd.comp (by fun_prop)
  have hα' : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => α p.1.1) encMid encNat :=
    hα.comp (by fun_prop)
  have hr : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => p.1.2) encMid encNat := by
    fun_prop
  have hc : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => p.2) encMid encBits := by
    fun_prop
  have hq := F.computableInPolyTime_order.comp hd'
  have hg := F.computableInPolyTime_generator.comp hd'
  have ht := F.computableInPolyTime_smul.comp (hd'.prod (hr.prod hg))
  have hc_nat : ComputableTidilyInPolyTime (fun p : (γ × ℕ) × List Bool => ofBits p.2)
      encMid encNat :=
    ComputableTidilyInPolyTime.bitsToNat.comp hc.tidy
  have hz : ComputableInPolyTime
      (fun p : (γ × ℕ) × List Bool =>
        ((p.1.2 + ofBits p.2 * (α p.1.1 % F.order (d p.1.1))) % F.order (d p.1.1)).bits)
      encMid encBits :=
    .of_tidy (ComputableTidilyInPolyTime.natBits.comp
      (.binary_mod'
        (.binary_add' hr.tidy (.binary_mul' hc_nat (.binary_mod' hα'.tidy hq.tidy)))
        hq.tidy))
  exact (ht.prod (hc.prod hz)).isPPTOn

/-- `schnorrSimulatedTranscript` is uniform strict PPT when the security parameter, group
description, encoded public key, and challenge length are computable in polynomial time. -/
theorem isPPTOn_schnorrSimulatedTranscript {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc} {u : γ → List Bool} {m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hu : ComputableInPolyTime u encIn encBits)
    (hm : ComputableInPolyTime m encIn encUnary) :
    IsPPTOn encIn encTranscript
      (fun a => F.schnorrSimulatedTranscript (n a) (d a) (u a) (m a)) := by
  have hn_t := hn.tidy
  have hd_t := hd.tidy
  have hu_t := hu.tidy
  have hsim := F.isPPTOn_schnorrSimulateWord
  unfold schnorrSimulatedTranscript
  refine hm.sampleList.bind_with ?_
  refine (hsim.preprocess
    (prepare := fun p : γ × List Bool => ((n p.1, d p.1), u p.1, p.2))
    (by fun_prop)).bind_with ?_
  exact ComputableTidilyInPolyTime.isPPTOn (by fun_prop)

/-- **The direct impersonator `A.toDirect k Q` is uniform strict PPT** when the eavesdropping
adversary `A` is and both `k` and `Q` are computable in polynomial time. -/
theorem isPPT_toDirect {k Q : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {A : F.SchnorrEavesdropAdversary} (hA : A.IsPPT) :
    (A.toDirect k Q).IsPPT := by
  refine ⟨?_, hA.2⟩
  let encIn := encPair encUnary (encPair F.encDesc encBits)
  have hk_t := hk.tidy
  have hQ_t := hQ.tidy
  have hn : ComputableInPolyTime (fun p : ℕ × F.Desc × List Bool => p.1) encIn encUnary := by
    fun_prop
  have hd : ComputableInPolyTime (fun p : ℕ × F.Desc × List Bool => p.2.1) encIn F.encDesc := by
    fun_prop
  have hu : ComputableInPolyTime (fun p : ℕ × F.Desc × List Bool => p.2.2) encIn encBits := by
    fun_prop
  have hm : ComputableInPolyTime (fun p : ℕ × F.Desc × List Bool => k p.1) encIn encUnary := by
    fun_prop
  have hcount : ComputableInPolyTime (fun p : ℕ × F.Desc × List Bool => Q p.1) encIn encUnary := by
    fun_prop
  have hrep := (F.isPPTOn_schnorrSimulatedTranscript hn hd hu hm).replicate hcount
  change IsPPTOn encIn (encPair encBits encBits) fun p =>
    OracleComp.replicate (Q p.1) (F.schnorrSimulatedTranscript p.1 p.2.1 p.2.2 (k p.1)) >>=
      fun views => A.commit p.1 (p.2.1, p.2.2, views)
  exact hrep.bind_with (hA.1.preprocess
    (prepare := fun p : (ℕ × F.Desc × List Bool) × List (List Bool × List Bool × List Bool) =>
      (p.1.1, (p.1.2.1, p.1.2.2, p.2))) (by fun_prop))

/-- **The rewinding discrete-logarithm adversary built from an eavesdropper is uniform strict PPT**
when the eavesdropper is and `k` and `Q` are computable in polynomial time. -/
theorem isPPTOn_rewind_toDirect {k Q : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {A : F.SchnorrEavesdropAdversary} (hA : A.IsPPT) :
    IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => (A.toDirect k Q).rewind k input.1 input.2) :=
  isPPTOn_rewind hk (isPPT_toDirect hk hQ hA)

/-! ### Asymptotic eavesdropping security under the discrete-logarithm assumption -/

variable (F) in
/-- Schnorr identification with challenge length `k` is secure against eavesdropping attacks
([BonehShoup2023], Definition 18.1 and Attack Game 18.2) in the uniform strict-PPT model: for every
polynomial-time conversation count `Q` and every uniform strict PPT eavesdropping adversary `A`,
the success probability in `schnorrEavesdropGame` is negligible. -/
def IsEavesdropSecure (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ) : Prop :=
  ∀ (Q : ℕ → ℕ), ComputableInPolyTime Q encUnary encUnary →
    ∀ (A : F.SchnorrEavesdropAdversary), A.IsPPT →
      Negligible fun n => Game.succProbability (F.schnorrEavesdropGame setup k Q A n)

variable (F) in
/-- Schnorr identification with challenge length `k` is secure against eavesdropping attacks with
ideal honest conversations (`schnorrIdealEavesdropGame`) for every polynomial-time conversation
count `Q` and every uniform strict PPT eavesdropping adversary `A`. -/
def IsIdealEavesdropSecure (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ) : Prop :=
  ∀ (Q : ℕ → ℕ), ComputableInPolyTime Q encUnary encUnary →
    ∀ (A : F.SchnorrEavesdropAdversary), A.IsPPT →
      Negligible fun n => Game.succProbability (F.schnorrIdealEavesdropGame setup k Q A n)

/-- When `Q` is computable in polynomial time on unary inputs, `(Q n : ℝ≥0) / 2 ^ n` is
negligible. -/
theorem negligible_div_two_pow_of_polyTime {Q : ℕ → ℕ}
    (hQ : ComputableInPolyTime Q encUnary encUnary) :
    Negligible fun n => (Q n : ℝ≥0) / 2 ^ n := by
  have hpoly : PolynomiallyBounded Q := hQ.tidy.polynomiallyBounded
  have hgeom : Negligible fun n => (2⁻¹ : ℝ≥0) ^ n :=
    negligible_geometric (by norm_num)
  refine (hgeom.polynomiallyBounded_mul hpoly).congr fun n => ?_
  rw [div_eq_mul_inv, inv_pow]

/-- **Schnorr identification is secure against eavesdropping with ideal honest conversations under
the discrete-logarithm assumption** ([BonehShoup2023], Theorem 19.5). -/
theorem negligible_schnorrIdealEavesdropGame {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {k Q : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hkq : ∀ n, ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d)
    (hchallenge : Negligible fun n => 1 / 2 ^ k n)
    {A : F.SchnorrEavesdropAdversary} (hA : A.IsPPT) :
    Negligible fun n => Game.succProbability (F.schnorrIdealEavesdropGame setup k Q A n) := by
  have hdir := negligible_schnorrDirectGame hDL hk hkq hchallenge (isPPT_toDirect hk hQ hA)
  have hsim := negligible_div_two_pow_of_polyTime hQ
  refine negligible_of_le (hsim.add hdir) fun n => ?_
  calc Game.succProbability (F.schnorrIdealEavesdropGame setup k Q A n)
      ≤ Game.advantage (F.schnorrIdealEavesdropGame setup k Q A n)
          (F.schnorrDirectGame setup k (A.toDirect k Q) n) +
        Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) := by
        simpa only [Game.advantage_pure_false] using
          Game.advantage_triangle
            (F.schnorrIdealEavesdropGame setup k Q A n)
            (F.schnorrDirectGame setup k (A.toDirect k Q) n)
            (PMF.pure false)
    _ ≤ Q n / 2 ^ n +
        Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) :=
      add_le_add (advantage_schnorrIdealEavesdropGame_schnorrDirectGame_le setup k Q A n) le_rfl

/-- **Schnorr identification is secure against eavesdropping in the strict-PPT model under the
discrete-logarithm assumption** ([BonehShoup2023], Theorem 19.5; [KatzLindell2020],
Theorem 13.2). -/
theorem negligible_schnorrEavesdropGame {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {k Q : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hkq : ∀ n, ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d)
    (hchallenge : Negligible fun n => 1 / 2 ^ k n)
    {A : F.SchnorrEavesdropAdversary} (hA : A.IsPPT) :
    Negligible fun n => Game.succProbability (F.schnorrEavesdropGame setup k Q A n) := by
  have hdir := negligible_schnorrDirectGame hDL hk hkq hchallenge (isPPT_toDirect hk hQ hA)
  have h2Q : ComputableInPolyTime (fun n => 2 * Q n) encUnary encUnary := by
    have hQ_t := hQ.tidy
    exact .of_tidy (by fun_prop)
  have hsim := negligible_div_two_pow_of_polyTime h2Q
  refine negligible_of_le (hsim.add hdir) fun n => ?_
  calc Game.succProbability (F.schnorrEavesdropGame setup k Q A n)
      ≤ Game.advantage (F.schnorrEavesdropGame setup k Q A n)
          (F.schnorrDirectGame setup k (A.toDirect k Q) n) +
        Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) := by
        simpa only [Game.advantage_pure_false] using
          Game.advantage_triangle
            (F.schnorrEavesdropGame setup k Q A n)
            (F.schnorrDirectGame setup k (A.toDirect k Q) n)
            (PMF.pure false)
    _ ≤ (2 * Q n : ℕ) / 2 ^ n +
        Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        add_le_add (advantage_schnorrEavesdropGame_schnorrDirectGame_le setup k Q A n) le_rfl

/-- **Schnorr identification satisfies `IsIdealEavesdropSecure` under the discrete-logarithm
assumption** ([BonehShoup2023], Theorem 19.5). -/
theorem schnorr_isIdealEavesdropSecure_of_discreteLogHard
    {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    (hkq : ∀ n, ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d)
    (hchallenge : Negligible fun n => 1 / 2 ^ k n) :
    F.IsIdealEavesdropSecure setup k :=
  fun _ hQ _ hA => negligible_schnorrIdealEavesdropGame hDL hk hQ hkq hchallenge hA

/-- **Schnorr identification satisfies `IsEavesdropSecure` under the discrete-logarithm assumption**
([BonehShoup2023], Theorem 19.5; [KatzLindell2020], Theorem 13.2). -/
theorem schnorr_isEavesdropSecure_of_discreteLogHard
    {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    (hkq : ∀ n, ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d)
    (hchallenge : Negligible fun n => 1 / 2 ^ k n) :
    F.IsEavesdropSecure setup k :=
  fun _ hQ _ hA => negligible_schnorrEavesdropGame hDL hk hQ hkq hchallenge hA

end Cslib.Crypto.PrimeOrderGroupFamily
