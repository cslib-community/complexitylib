/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Parity
public import Complexity.Computability.Circuit.Pi
public import Complexity.Crypto.Protocols.MPC.CircuitEval

/-!
# Multi-Party Protocol Composition, Randomized Wrapper, and Completeness of $\text{OT}_1^4$

This module formalizes the $m$-party semi-honest composition theorem, the reduction from
randomized functionalities to deterministic functionalities via shared coin-tossing, and the
resulting information-theoretic reduction of any randomized $m$-party Boolean circuit
functionality to $\text{OT}_1^4$ from Goldreich's *Foundations of Cryptography, Volume 2: Basic
Applications*:

1. **$k$-ary Subprotocol Composition (`Round.embed`, `Schedule.compose`, `Schedule.ComposedCoins`,
   `Protocol.compose`, `composeSim`, `PerfectSemiHonestPrivate.compose`):**
   generalizes the 2-party composition theorem (Section 7.3.1, Definitions 7.3.1–7.3.2 on print
   p. 636 and Theorem 7.3.3 on print pp. 637–638) to $m$-party protocols making $k$-ary ideal
   oracle calls (Section 7.5.2.1, Definitions 7.5.5–7.5.6 on print pp. 701–702 and Theorem 7.5.7 on
   print pp. 702–703). Replacing each `.oracle op parties` round of an outer protocol `P` with the
   embedded execution of a perfectly private $k$-party subprotocol `Sub op` yields a perfectly
   private $m$-party protocol `P.compose Sub` in the lower-level oracle world `W₂`.
2. **Reduction of Randomized Functionalities to Deterministic Ones (`randomizedFunctionality`,
   `detOfRandomized`, `Protocol.randomizedWrapper`, `randomizedWrapperSim`,
   `perfectSemiHonestPrivate_randomizedWrapper`):**
   formalizes Equation 7.48 (Section 7.5.2.4, print p. 707) and Proposition 7.3.4 (Section 7.3.1,
   print pp. 639–640) combined with the composition theorem ("Application: Reducing Private
   Computation of General Functionalities to Deterministic Ones", Section 7.3.1, print pp. 638–639,
   Equation 7.19). Each party `i : Fin m` samples a uniform private coin share
   `r_i : BitString coins` and runs a deterministic protocol on `(x_i, r_i)` that evaluates
   `g (∑ i : Fin m, r_i) x`. Against every proper static coalition `I ≠ Finset.univ`, the sum
   `∑ i : Fin m, r_i` is uniform and independent of the coalition's coin shares `I.restrict r`.
   `perfectSemiHonestPrivate_randomizedWrapper` is proved directly rather than via
   `PerfectSemiHonestPrivate.compose` because the coin-sharing reduction is only private against
   proper coalitions `I ≠ Finset.univ`, whereas `PerfectSemiHonestPrivate.compose` requires all-`I`
   privacy of the outer protocol. Note that restricting to `I ≠ Finset.univ` is narrower than
   Goldreich's quantifier over all $I \subseteq [m]$ in Definition 7.5.1 (print p. 696, where
   $I = [m]$ is called "always trivial" on print pp. 697 and 703): under the joint view-and-output
   equation (Eq. 7.40) for randomized functionalities, $I = [m]$ is not trivial when coin shares
   are simulated independently of the output (for $m = 2$, Definition 7.2.1 considers only
   single-party views, so Proposition 7.3.4 itself is fully covered).
3. **XOR Prelude Circuit and $\text{OT}_1^4$-Hybrid GMW Protocol (`xorPreludeCircuit`,
   `eval_xorPreludeCircuit`, `gmwOT14Protocol`, `gmwOT14RandomizedProtocol`,
   `perfectSemiHonestPrivateProper_gmwOT14Randomized`):**
   constructs a Boolean circuit `xorPreludeCircuit m n coins` (reusing
   `Cslib.Circuits.Program.appendXor` and `Cslib.Circuits.Circuit.pi`) that unpacks the `m` party
   input-coin blocks `(x_i, r_i)` into `Fin.append (BitString.blocksEquiv.symm x) (∑ i : Fin m,
   r_i)`, composes `gmwCircuitProtocol` (M3) with `multiPartyMulProtocol` and
   `twoPartyMulProtocol` (M2) to obtain `gmwOT14Protocol` and `gmwOT14RandomizedProtocol`, and
   establishes Theorem 7.5.12 (Section 7.5.2.4, print p. 707; generalizing Theorem 7.3.11,
   Section 7.3.4, print p. 648) at the circuit level for all proper coalitions `I ≠ Finset.univ`.
   Throughout this module, security is stated as exact `PMF` distributional equality with
   unrestricted `ProbComp` simulators, whereas Goldreich's Definitions 7.2.1 and 7.5.1 use
   computational indistinguishability and PPT simulators (polynomial-time efficiency is certified in
   M5). Because `gmwCircuitProtocol` in M3 includes one `sharedMulSpec m` share-refresh call per
   output coordinate `(r, j) : Fin m × Fin k` (in addition to one `sharedMulSpec m` call per
   `.and`/`.or` gate in Step 2), composing with `multiPartyMulProtocol m` and `twoPartyMulProtocol`
   expands each such call into $m(m-1)/2$ pairwise invocations of `ot14Spec` (an extra
   $m \cdot k \cdot m(m-1)/2$ calls to `ot14Spec` from Step 3, polynomial in
   $m, n, k, C.\text{size}$).

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Round.embed`, `Cslib.Crypto.Protocols.MPC.Schedule.compose`,
  `Cslib.Crypto.Protocols.MPC.Schedule.ComposedCoins`: schedule and coin-type composition for
  $k$-ary oracle replacement (Definitions 7.5.5–7.5.6, pp. 701–702).
* `Cslib.Crypto.Protocols.MPC.Protocol.compose`, `Cslib.Crypto.Protocols.MPC.composeSim`:
  protocol and coalition-simulator composition (Theorem 7.5.7, pp. 702–703).
* `Cslib.Crypto.Protocols.MPC.Protocol.mapInput`, `Cslib.Crypto.Protocols.MPC.mapInputSim`:
  precomposing a protocol and coalition simulator with local party input encodings.
* `Cslib.Crypto.Protocols.MPC.randomizedFunctionality`,
  `Cslib.Crypto.Protocols.MPC.detOfRandomized`,
  `Cslib.Crypto.Protocols.MPC.Protocol.randomizedWrapper`,
  `Cslib.Crypto.Protocols.MPC.randomizedWrapperSim`: randomized-to-deterministic wrapper
  (Eq. 7.19, p. 638; Proposition 7.3.4, pp. 639–640; Eq. 7.48, p. 707).
* `Cslib.Crypto.Protocols.MPC.xorPreludeCircuit`: Boolean prelude circuit combining party coin
  shares by bitwise XOR.
* `Cslib.Crypto.Protocols.MPC.gmwOT14Protocol`,
  `Cslib.Crypto.Protocols.MPC.gmwOT14Sim`,
  `Cslib.Crypto.Protocols.MPC.gmwOT14RandomizedProtocol`,
  `Cslib.Crypto.Protocols.MPC.gmwOT14RandomizedSim`: $\text{OT}_1^4$-hybrid GMW protocols and
  coalition simulators.

## Main results

* `Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivate.compose`: Theorem 7.5.7 (print pp. 702–703;
  cf. Theorem 7.3.3, print pp. 637–638), multi-party composition theorem for perfect semi-honest
  privacy.
* `Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivate.mapInput`: preservation of perfect
  semi-honest privacy under local party input encodings.
* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_randomizedWrapper`: Proposition 7.3.4
  (print pp. 639–640) combined with the composition theorem (Section 7.3.1 Application, print
  pp. 638–639, Eq. 7.19) and Section 7.5.2.4 Eq. 7.48 (print p. 707), proper-coalition privacy of
  the randomized-functionality wrapper.
* `Cslib.Crypto.Protocols.MPC.eval_xorPreludeCircuit`,
  `Cslib.Crypto.Protocols.MPC.size_xorPreludeCircuit`: correctness and gate count of
  `xorPreludeCircuit`.
* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_gmwOT14`: full-coalition perfect privacy of
  deterministic `gmwOT14Protocol` in `ot14World`.
* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivateProper_gmwOT14Randomized`: Theorem 7.5.12
  (print p. 707; cf. Theorem 7.3.11, print p. 648), proper-coalition perfect privacy of
  `gmwOT14RandomizedProtocol` in `ot14World`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.1 (Definitions 7.3.1–7.3.2 on p. 636, Theorem 7.3.3 on pp. 637–638, Eq. 7.19 on
  p. 638, Proposition 7.3.4 on pp. 639–640), Section 7.3.4 (Theorem 7.3.11, p. 648),
  Section 7.5.2.1 (Definitions 7.5.5–7.5.6 on pp. 701–702, Theorem 7.5.7 on pp. 702–703), and
  Section 7.5.2.4 (Eq. 7.48, Theorem 7.5.12, p. 707).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp Cslib.Circuits

/-! ### Part 1: $k$-ary Subprotocol Composition (Theorem 7.5.7) -/

/-- Lift a `k`-party round `r : Round k spec` to an `m`-party round along a party embedding
`parties : Fin k ↪ Fin m` (Goldreich Definition 7.5.5, pp. 701–702). -/
@[expose, reducible] def Round.embed {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) : Round k spec → Round m spec
  | .message s r Msg => .message (parties s) (parties r) Msg
  | .oracle op subParties => .oracle op (subParties.trans parties)

/-- Replace each `.oracle op parties` round in `sc₁` with the lifted schedule
`(sc₂ op).map (Round.embed parties)`, taking `sc₂` first and matching `sc₁` after the colon
(Goldreich Definitions 7.5.5–7.5.6 and Theorem 7.5.7, pp. 701–703). -/
@[expose, reducible] def Schedule.compose {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    (sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂) :
    Schedule m spec₁ → Schedule m spec₂
  | [] => []
  | .message s r Msg :: rest => .message s r Msg :: Schedule.compose sc₂ rest
  | .oracle op parties :: rest =>
    (sc₂ op).map (Round.embed parties) ++ Schedule.compose sc₂ rest

/-- Per-party subprotocol coins needed along an outer schedule `sc₁ : Schedule m spec₁`:
for each `.oracle op parties` round, party `i` holds `(s : Fin (spec₁.arity op)) → (parties s = i)
→ Coins₂ op s` (proof-domain indexed so parties outside `parties` hold a canonical subsingleton). -/
@[expose, reducible] def Schedule.SubCoins {m : ℕ} {spec₁ : MultiOracleSpec}
    (Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type) :
    Schedule m spec₁ → Fin m → Type
  | [], _ => Unit
  | .message _ _ _ :: rest, i => Schedule.SubCoins Coins₂ rest i
  | .oracle op parties :: rest, i =>
    ((s : Fin (spec₁.arity op)) → (parties s = i) → Coins₂ op s) ×
      Schedule.SubCoins Coins₂ rest i

/-- Combined coin type for party `i : Fin m` in `Π.compose Sub`: outer coins `Coins₁ i` paired with
the sequence of subprotocol coins `Schedule.SubCoins Coins₂ sc₁ i`. -/
@[expose, reducible] def Schedule.ComposedCoins {m : ℕ} {spec₁ : MultiOracleSpec}
    (Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type)
    (Coins₁ : Fin m → Type) (sc₁ : Schedule m spec₁) (i : Fin m) : Type :=
  Coins₁ i × Schedule.SubCoins Coins₂ sc₁ i

namespace Composition

/-! #### Independent product helper for single-party slot sampling -/

private theorem eval_pi_single {m : ℕ} {β : Type} (i₀ : Fin m) (p : ProbComp β) :
    ProbComp.eval (OracleComp.pi fun i : Fin m =>
      if h : i₀ = i then
        (fun (c : β) (_ : i₀ = i) => c) <$> p
      else
        pure (fun h' : i₀ = i => (h h').elim)) =
      (ProbComp.eval p).map (fun (c : β) (i : Fin m) (_ : i₀ = i) => c) := by
  induction m with
  | zero => exact i₀.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun j₀ => ?_) i₀
    · have h00 : (if h : (0 : Fin (m + 1)) = 0 then
          (fun (c : β) (_ : (0 : Fin (m + 1)) = 0) => c) <$> p
        else
          pure (fun h' : (0 : Fin (m + 1)) = 0 => (h h').elim)) =
          (fun (c : β) (_ : (0 : Fin (m + 1)) = 0) => c) <$> p := rfl
      have hrest : (fun i : Fin m =>
          if h : (0 : Fin (m + 1)) = i.succ then
            (fun (c : β) (_ : (0 : Fin (m + 1)) = i.succ) => c) <$> p
          else
            pure (fun h' : (0 : Fin (m + 1)) = i.succ => (h h').elim)) =
          fun i : Fin m =>
            pure (fun h' : (0 : Fin (m + 1)) = i.succ => (Fin.succ_ne_zero i h'.symm).elim) := by
        funext i
        have hne : ¬ ((0 : Fin (m + 1)) = i.succ) := fun h => Fin.succ_ne_zero i h.symm
        simp [hne]
      rw [OracleComp.pi_succ, h00, hrest]
      simp only [eval_pi_pure, ProbComp.eval_bind, ProbComp.eval_map, PMF.pure_map,
        PMF.bind_map, Function.comp_def]
      refine congrArg (PMF.map · (ProbComp.eval p)) (funext fun c => ?_)
      ext i h
      refine Fin.cases (fun _ => rfl) (fun j hj => (Fin.succ_ne_zero j hj.symm).elim) i h
    · have h0 : ¬ (j₀.succ = (0 : Fin (m + 1))) := Fin.succ_ne_zero j₀
      have h0_Br : (if h : j₀.succ = (0 : Fin (m + 1)) then
          (fun (c : β) (_ : j₀.succ = 0) => c) <$> p
        else
          pure (fun h' : j₀.succ = 0 => (h h').elim)) =
          pure (fun h' : j₀.succ = 0 => (h0 h').elim) := by
        simp [h0]
      have hrest : (fun i : Fin m =>
          if h : j₀.succ = i.succ then
            (fun (c : β) (_ : j₀.succ = i.succ) => c) <$> p
          else
            pure (fun h' : j₀.succ = i.succ => (h h').elim)) =
          fun i : Fin m =>
            (fun (f : (j₀ = i) → β) (h' : j₀.succ = i.succ) => f (Fin.succ_inj.1 h')) <$>
              (if h : j₀ = i then
                (fun (c : β) (_ : j₀ = i) => c) <$> p
              else
                pure (fun h' : j₀ = i => (h h').elim)) := by
        funext i
        by_cases h : j₀ = i
        · subst h
          simp [Functor.map_map]
        · have hs : ¬ (j₀.succ = i.succ) := fun hs => h (Fin.succ_inj.1 hs)
          simp [hs, h]
      rw [OracleComp.pi_succ, h0_Br, hrest]
      simp only [ProbComp.eval_pi_map, ih j₀,
        ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_bind, PMF.map_comp]
      refine congrArg (PMF.map · (ProbComp.eval p)) (funext fun c => ?_)
      ext i h
      refine Fin.cases (fun h0' => (h0 h0').elim) (fun _ _ => rfl) i h

/-! #### Induced sub-coalitions, tuple pushforwards, and subprotocol coin sampling -/

/-- Induced sub-coalition in `Fin k` of an outer coalition `I : Finset (Fin m)` along an embedding
`parties : Fin k ↪ Fin m` (Goldreich Theorem 7.5.7 Proof Sketch, pp. 702–703). Defined via
`Finset.univ.filter` rather than `Finset.preimage` so that `subCoalition` and `expandSimSteps`
remain computable. -/
@[expose] def subCoalition {k m : ℕ} (parties : Fin k ↪ Fin m) (I : Finset (Fin m)) :
    Finset (Fin k) :=
  Finset.univ.filter fun s => parties s ∈ I

@[simp] theorem mem_subCoalition {k m : ℕ} {parties : Fin k ↪ Fin m}
    {I : Finset (Fin m)} {s : Fin k} :
    s ∈ subCoalition parties I ↔ parties s ∈ I := by
  simp [subCoalition]

/-- Push a `k`-party tuple `c_k : (s : Fin k) → F s` forward along `parties : Fin k ↪ Fin m` to the
proof-domain indexed `m`-party family `fun i s _ => c_k s`. -/
@[expose] def pushTuple {k m : ℕ} (parties : Fin k ↪ Fin m) {F : Fin k → Type}
    (c_k : (s : Fin k) → F s) (i : Fin m) :
    (s : Fin k) → (parties s = i) → F s :=
  fun s _ => c_k s

/-- Push a coalition-restricted `J`-tuple `c_J : (s : subCoalition parties I) → F s.1` forward
along `parties : Fin k ↪ Fin m` to `(i : I) → (s : Fin k) → (parties s = i.1) → F s`. -/
@[expose] def pushTupleRestrict {k m : ℕ} (parties : Fin k ↪ Fin m) (I : Finset (Fin m))
    {F : Fin k → Type} (c_J : (s : subCoalition parties I) → F s.1) (i : I) :
    (s : Fin k) → (parties s = i.1) → F s :=
  fun s hs => c_J ⟨s, mem_subCoalition.2 (hs.symm ▸ i.2)⟩

private theorem restrict_pushTuple {k m : ℕ} (parties : Fin k ↪ Fin m) (I : Finset (Fin m))
    {F : Fin k → Type} (c_k : (s : Fin k) → F s) :
    I.restrict (pushTuple parties c_k) =
      pushTupleRestrict parties I ((subCoalition parties I).restrict c_k) :=
  rfl

/-- Sample party `i`'s proof-domain indexed subcoins `(s : Fin k) → (parties s = i) → Coins_k s`
from `sample_k : (s : Fin k) → ProbComp (Coins_k s)`. -/
@[expose] noncomputable def sampleSlotCoins {k m : ℕ} (parties : Fin k ↪ Fin m)
    {Coins_k : Fin k → Type} (sample_k : (s : Fin k) → ProbComp (Coins_k s)) (i : Fin m) :
    ProbComp ((s : Fin k) → (parties s = i) → Coins_k s) :=
  OracleComp.pi fun s : Fin k =>
    if h : parties s = i then
      (fun (c : Coins_k s) (_ : parties s = i) => c) <$> sample_k s
    else
      pure (fun h' : parties s = i => (h h').elim)

/-- Joint distribution of `sampleSlotCoins parties sample_k` across all `m` outer parties equals the
pushforward of `OracleComp.pi sample_k` along `pushTuple parties`. -/
theorem eval_pi_sampleSlotCoins {k m : ℕ} (parties : Fin k ↪ Fin m)
    {Coins_k : Fin k → Type} (sample_k : (s : Fin k) → ProbComp (Coins_k s)) :
    ProbComp.eval (OracleComp.pi (sampleSlotCoins parties sample_k)) =
      (ProbComp.eval (OracleComp.pi sample_k)).map (pushTuple parties) := by
  unfold sampleSlotCoins
  rw [eval_pi_comm]
  have hpi := ProbComp.eval_pi_congr fun s : Fin k =>
    (eval_pi_single (parties s) (sample_k s)).trans (ProbComp.eval_map _ _).symm
  rw [hpi, ProbComp.eval_pi_map, PMF.map_comp]
  rfl

/-- Sample party `i`'s sequence of subprotocol coins along an outer schedule `sc₁`. -/
@[expose] noncomputable def sampleSubCoins {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)) :
    (sc₁ : Schedule m spec₁) → (i : Fin m) → ProbComp (Schedule.SubCoins Coins₂ sc₁ i)
  | [], _ => pure ()
  | .message _ _ _ :: rest, i => sampleSubCoins Sub rest i
  | .oracle op parties :: rest, i => do
    let c_head ← sampleSlotCoins parties (Sub op).sampleCoins i
    let c_tail ← sampleSubCoins Sub rest i
    return (c_head, c_tail)

/-! #### Embedded round/schedule transcripts and `Steps.embed` -/

/-- Pull a received record in `Round.embed parties r` at party `i` back to slot `s : Fin k`
given `hs : parties s = i`. -/
@[expose] def pullRoundReceived {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (r : Round k spec) {s : Fin k} {i : Fin m}
    (hs : parties s = i) (recv_i : (Round.embed parties r).Received i) : r.Received s :=
  match r with
  | .message _ _ _ => fun hr => recv_i (hs.symm.trans (congrArg parties hr))
  | .oracle _ _ => fun t ht => recv_i t ((congrArg parties ht).trans hs)

/-- Pull a received transcript in `sc.map (Round.embed parties)` at party `i` back to slot
`s : Fin k` given `hs : parties s = i`. -/
@[expose] def pullScheduleReceived {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) :
    (sc : Schedule k spec) → {s : Fin k} → {i : Fin m} → (hs : parties s = i) →
      Schedule.Received (sc.map (Round.embed parties)) i → sc.Received s
  | [], _, _, _, () => ()
  | r :: sc, _, _, hs, (r_head, r_tail) =>
    (pullRoundReceived parties r hs r_head, pullScheduleReceived parties sc hs r_tail)

/-- Push a `k`-party received record `recv_k : (s : Fin k) → r.Received s` forward to all `m`
parties in `Round.embed parties r`. -/
@[expose] def pushRoundReceived {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (r : Round k spec)
    (recv_k : (s : Fin k) → r.Received s) (i : Fin m) :
    (Round.embed parties r).Received i :=
  match r with
  | .message _ r₀ _ => fun _ => recv_k r₀ rfl
  | .oracle _ subParties => fun t _ => recv_k (subParties t) t rfl

/-- Push a `k`-party received transcript `recv_k : (s : Fin k) → sc.Received s` forward to all `m`
parties in `sc.map (Round.embed parties)`. -/
@[expose] def pushScheduleReceived {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) :
    (sc : Schedule k spec) → ((s : Fin k) → sc.Received s) →
      (i : Fin m) → Schedule.Received (sc.map (Round.embed parties)) i
  | [], _, _ => ()
  | r :: sc, recv_k, i =>
    (pushRoundReceived parties r (fun s => (recv_k s).1) i,
      pushScheduleReceived parties sc (fun s => (recv_k s).2) i)

/-- Push a coalition-restricted received record `recv_J : (s : subCoalition parties I) → r.Received
s.1` forward to `(i : I) → (Round.embed parties r).Received i.1`. -/
@[expose] def pushRoundReceivedRestrict {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (I : Finset (Fin m)) (r : Round k spec)
    (recv_J : (s : subCoalition parties I) → r.Received s.1) (i : I) :
    (Round.embed parties r).Received i.1 :=
  match r with
  | .message _ r₀ _ =>
    fun hr => recv_J ⟨r₀, mem_subCoalition.2 (hr ▸ i.2)⟩ rfl
  | .oracle _ subParties =>
    fun t ht => recv_J ⟨subParties t, mem_subCoalition.2 (ht.symm ▸ i.2)⟩ t rfl

/-- Push a coalition-restricted received transcript
`recv_J : (s : subCoalition parties I) → sc.Received s.1` forward to
`(i : I) → Schedule.Received (sc.map (Round.embed parties)) i.1`. -/
@[expose] def pushScheduleReceivedRestrict {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (I : Finset (Fin m)) :
    (sc : Schedule k spec) → ((s : subCoalition parties I) → sc.Received s.1) →
      (i : I) → Schedule.Received (sc.map (Round.embed parties)) i.1
  | [], _, _ => ()
  | r :: sc, recv_J, i =>
    (pushRoundReceivedRestrict parties I r (fun s => (recv_J s).1) i,
      pushScheduleReceivedRestrict parties I sc (fun s => (recv_J s).2) i)

private theorem restrict_pushRoundReceived {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (I : Finset (Fin m)) (r : Round k spec)
    (recv_k : (s : Fin k) → r.Received s) :
    I.restrict (pushRoundReceived parties r recv_k) =
      pushRoundReceivedRestrict parties I r ((subCoalition parties I).restrict recv_k) := by
  cases r <;> rfl

private theorem restrict_pushScheduleReceived {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (I : Finset (Fin m)) (sc : Schedule k spec)
    (recv_k : (s : Fin k) → sc.Received s) :
    I.restrict (pushScheduleReceived parties sc recv_k) =
      pushScheduleReceivedRestrict parties I sc ((subCoalition parties I).restrict recv_k) := by
  induction sc with
  | nil => rfl
  | cons r sc ih =>
    funext i
    exact Prod.ext (congrFun (restrict_pushRoundReceived parties I r (fun s => (recv_k s).1)) i)
      (congrFun (ih (fun s => (recv_k s).2)) i)

@[simp] private theorem pullRoundReceived_pushRoundReceived {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (r : Round k spec) (recv_k : (s : Fin k) → r.Received s)
    {s : Fin k} {i : Fin m} (hs : parties s = i) :
    pullRoundReceived parties r hs (pushRoundReceived parties r recv_k i) = recv_k s := by
  cases r with
  | message s₀ r₀ Msg =>
    funext hr
    subst hr
    rfl
  | oracle op subParties =>
    funext t ht
    subst ht
    rfl

@[simp] private theorem pullScheduleReceived_pushScheduleReceived {k m : ℕ}
    {spec : MultiOracleSpec} (parties : Fin k ↪ Fin m) (sc : Schedule k spec)
    (recv_k : (s : Fin k) → sc.Received s) {s : Fin k} {i : Fin m} (hs : parties s = i) :
    pullScheduleReceived parties sc hs (pushScheduleReceived parties sc recv_k i) = recv_k s := by
  induction sc with
  | nil =>
    cases recv_k s
    rfl
  | cons r sc ih =>
    simp [pullScheduleReceived, pushScheduleReceived, ih (fun s' => (recv_k s').2)]

/-- Embed a `k`-party step computation `steps : Steps State_k Out_k sc` along `parties : Fin k ↪
Fin m`, threading an arbitrary `m`-party outer state `Outer : Fin m → Type` unchanged through the
first state component. -/
@[expose] def Steps.embed {k m : ℕ} {spec : MultiOracleSpec} (parties : Fin k ↪ Fin m)
    (Outer : Fin m → Type) {State_k Out_k : Fin k → Type} {sc : Schedule k spec}
    (steps : Steps State_k Out_k sc) :
    Steps (fun i => Outer i × ((s : Fin k) → (parties s = i) → State_k s))
      (fun i => Outer i × ((s : Fin k) → (parties s = i) → Out_k s))
      (sc.map (Round.embed parties)) :=
  match steps with
  | .done output =>
    .done (fun _ st_i => (st_i.1, fun s hs => output s (st_i.2 s hs)))
  | .message (sender := s₀) (receiver := r₀) (Msg := Msg) send next =>
    .message (sender := parties s₀) (receiver := parties r₀)
      (fun st_sender => send (st_sender.2 s₀ rfl))
      ((Steps.embed parties Outer next).mapState fun _ st_i =>
        (st_i.1.1, fun s hs =>
          (st_i.1.2 s hs,
            pullRoundReceived parties (.message s₀ r₀ Msg) hs st_i.2)))
  | .oracle (op := op) (parties := subParties) query next =>
    .oracle (op := op) (parties := subParties.trans parties)
      (fun t st_party => query t (st_party.2 (subParties t) rfl))
      ((Steps.embed parties Outer next).mapState fun _ st_i =>
        (st_i.1.1, fun s hs =>
          (st_i.1.2 s hs,
            pullRoundReceived parties (.oracle op subParties) hs st_i.2)))

@[simp] private theorem outputAt_embed {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (Outer : Fin m → Type)
    {State_k Out_k : Fin k → Type} {sc : Schedule k spec}
    (steps : Steps State_k Out_k sc) (i : Fin m)
    (out_i : Outer i) (st_k_i : (s : Fin k) → (parties s = i) → State_k s)
    (recv_i : Schedule.Received (sc.map (Round.embed parties)) i) :
    (Steps.embed parties Outer steps).outputAt i (out_i, st_k_i) recv_i =
      (out_i, fun s hs =>
        steps.outputAt s (st_k_i s hs) (pullScheduleReceived parties sc hs recv_i)) := by
  induction steps with
  | done output =>
    cases recv_i
    rfl
  | message send next ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simpa [Steps.embed, Steps.outputAt, pullScheduleReceived] using
      ih (fun s hs => (st_k_i s hs, pullRoundReceived parties _ hs r_head)) r_tail
  | oracle query next ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simpa [Steps.embed, Steps.outputAt, pullScheduleReceived] using
      ih (fun s hs => (st_k_i s hs, pullRoundReceived parties _ hs r_head)) r_tail

private theorem evalWith_embed {k m : ℕ} {spec : MultiOracleSpec}
    (parties : Fin k ↪ Fin m) (Outer : Fin m → Type)
    {State_k Out_k : Fin k → Type} {sc : Schedule k spec}
    (steps : Steps State_k Out_k sc) (W : MultiOracleWorld spec)
    (out : (i : Fin m) → Outer i) (st_k : (s : Fin k) → State_k s) :
    (Steps.embed parties Outer steps).evalWith W (fun i => (out i, fun s _ => st_k s)) =
      (steps.evalWith W st_k).map (pushScheduleReceived parties sc) := by
  induction steps with
  | done output =>
    simp [Steps.embed, pushScheduleReceived]
  | @message _ _ s₀ r₀ Msg _ send next ih =>
    have hhead :
        Round.deliverMessage (spec := spec) (sender := parties s₀) (receiver := parties r₀)
          (send (st_k s₀)) =
        pushRoundReceived parties (.message s₀ r₀ Msg) (Round.deliverMessage (send (st_k s₀))) :=
      rfl
    simp only [Steps.embed, Steps.evalWith_message, Steps.evalWith_mapState, hhead,
      pullRoundReceived_pushRoundReceived,
      ih (fun s => (st_k s, Round.deliverMessage (send (st_k s₀)) s)),
      PMF.map_comp]
    rfl
  | @oracle _ _ op subParties _ query next ih =>
    simp only [Steps.embed, Steps.evalWith_oracle, Steps.evalWith_mapState, PMF.map_bind]
    refine congrArg (ProbComp.eval _).bind (funext fun ans => ?_)
    have hhead :
        Round.deliverOracle (spec := spec) (subParties.trans parties) ans =
          pushRoundReceived parties (.oracle op subParties) (Round.deliverOracle subParties ans) :=
      rfl
    simp only [hhead, pullRoundReceived_pushRoundReceived,
      ih (fun s => (st_k s, Round.deliverOracle subParties ans s)),
      PMF.map_comp]
    rfl

/-! #### Composing `Steps`, `Protocol`, and `CoalitionSimulator` -/

/-- Replace each `.oracle op parties` node in `steps : Steps State Out sc₁` with the embedded
execution of `(Sub op).steps` along `parties`. -/
@[expose] def Steps.compose {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (steps : Steps State Out sc₁) :
    Steps (fun i => State i × Schedule.SubCoins Coins₂ sc₁ i)
      Out (Schedule.compose sc₂ sc₁) :=
  match steps with
  | .done output =>
    .done (fun i st_i => output i st_i.1)
  | .message (sender := s₀) (receiver := r₀) send next =>
    .message (sender := s₀) (receiver := r₀)
      (fun st_sender => send st_sender.1)
      ((Steps.compose Sub next).mapState fun _ st_i =>
        ((st_i.1.1, st_i.2), st_i.1.2))
  | .oracle (op := op) (parties := parties) (sc := rest) query next =>
    (((Steps.embed parties (fun i => State i × Schedule.SubCoins Coins₂ rest i)
        (Sub op).steps).mapState
      (fun i st_i =>
        ((st_i.1, st_i.2.2),
          fun (s : Fin (spec₁.arity op)) (hs : parties s = i) =>
            (query s (hs.symm ▸ st_i.1), st_i.2.1 s hs)))).append
      ((Steps.compose Sub next).mapState fun _ st_i =>
        ((st_i.1.1, st_i.2), st_i.1.2)))

/-- Expand a simulated outer execution along `steps : Steps State Out sc₁` by invoking the inner
simulator `S₂ op (subCoalition parties I)` at every `.oracle op parties` round (Goldreich Theorem
7.5.7 Proof Sketch, pp. 702–703). -/
@[expose] def expandSimSteps {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (steps : Steps State Out sc₁)
    (stI : (i : I) → State i.1) (recvI : (i : I) → sc₁.Received i.1) :
    ProbComp ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.1 ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.1) :=
  match steps with
  | .done _ =>
    pure (fun _ => ((), ()))
  | .message _ next => do
    let rest ← expandSimSteps S₂ I next
      (fun i => (stI i, (recvI i).1)) (fun i => (recvI i).2)
    return fun i => ((rest i).1, ((recvI i).1, (rest i).2))
  | .oracle (op := op) (parties := parties) query next => do
    let J := subCoalition parties I
    let qJ : (s : J) → spec₁.Query op s.1 :=
      fun s => query s.1 (stI ⟨parties s.1, mem_subCoalition.1 s.2⟩)
    let aJ : (s : J) → spec₁.Answer op s.1 :=
      fun s => (recvI ⟨parties s.1, mem_subCoalition.1 s.2⟩).1 s.1 rfl
    let v_sub ← S₂ op J qJ aJ
    let rest ← expandSimSteps S₂ I next
      (fun i => (stI i, (recvI i).1)) (fun i => (recvI i).2)
    return fun i =>
      ((pushTupleRestrict parties I (fun s => (v_sub s).coins) i, (rest i).1),
        Schedule.Received.append
          (pushScheduleReceivedRestrict parties I (sc₂ op) (fun s => (v_sub s).received) i)
          (rest i).2)

/-- Hybrid equivalence lemma for `Steps.compose`: for any `steps : Steps State Out sc₁` and initial
states `st : (i : Fin m) → State i`, running `steps` in `W₁` and expanding the coalition `I`'s
transcript via `expandSimSteps S₂ I` produces the exact same joint distribution over
`((i : I) → SubCoins × ComposedReceived) × ((i : Fin m) → Out i)` as sampling `sampleSubCoins Sub
sc₁` and running `Steps.compose Sub steps` in `W₂` (Goldreich Theorem 7.5.7 Proof Sketch,
pp. 702–703). -/
private theorem evalWith_compose_steps_eq_hybrid {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    {W₁ : MultiOracleWorld spec₁} {W₂ : MultiOracleWorld spec₂}
    {Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)}
    {S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J}
    (hSub : ∀ op, PerfectSemiHonestPrivate (Sub op) W₂ (W₁ op) (S₂ op))
    (I : Finset (Fin m)) (steps : Steps State Out sc₁) (st : (i : Fin m) → State i) :
    ((steps.evalWith W₁ st).bind fun recv₁ =>
      (ProbComp.eval (expandSimSteps S₂ I steps (I.restrict st) (I.restrict recv₁))).map
        fun sub => (sub, fun i => steps.outputAt i (st i) (recv₁ i))) =
    (ProbComp.eval (OracleComp.pi (sampleSubCoins Sub sc₁))).bind fun c_sub =>
      ((Steps.compose Sub steps).evalWith W₂ (fun i => (st i, c_sub i))).map fun recv₂ =>
        (fun i : I => (c_sub i.1, recv₂ i.1),
          fun i => (Steps.compose Sub steps).outputAt i (st i, c_sub i) (recv₂ i)) := by
  induction steps with
  | done output =>
    simp [Steps.compose, expandSimSteps, sampleSubCoins, eval_pi_pure, Steps.outputAt]
  | @message _ _ s₀ r₀ _ _ send next ih =>
    simp only [Steps.compose, expandSimSteps, sampleSubCoins, Steps.evalWith_message,
      Steps.evalWith_mapState, ProbComp.eval_map, bind_pure_comp,
      PMF.bind_map, PMF.map_comp, Function.comp_def, Finset.restrict_def,
      Steps.outputAt, Steps.outputAt_mapState]
    have hih := ih (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
    simp only [Finset.restrict_def] at hih
    have hmap := congrArg (PMF.map fun res : ((i : I) → Schedule.SubCoins Coins₂ _ i.1 ×
          Schedule.Received (Schedule.compose sc₂ _) i.1) × ((i : Fin m) → _) =>
        (fun i : I => ((res.1 i).1,
          (Round.deliverMessage (spec := spec₂) (sender := s₀) (receiver := r₀)
            (send (st s₀)) i.1, (res.1 i).2)), res.2)) hih
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hmap
    exact hmap
  | @oracle _ _ op parties rest query next ih =>
    let q : (s : Fin (spec₁.arity op)) → spec₁.Query op s := fun s => query s (st (parties s))
    let J : Finset (Fin (spec₁.arity op)) := subCoalition parties I
    -- 1. Rewrite the LHS using `idealJoint` of `W₁ op` and `S₂ op J`.
    have hlhs :
        (((Steps.oracle query next).evalWith W₁ st).bind fun recv₁ =>
          (ProbComp.eval (expandSimSteps S₂ I (Steps.oracle query next)
              (I.restrict st) (I.restrict recv₁))).map
            fun sub => (sub, fun i => (Steps.oracle query next).outputAt i (st i) (recv₁ i))) =
        (ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)).bind fun ⟨v_sub, ans⟩ =>
          (((next.evalWith W₁ (fun i => (st i, Round.deliverOracle parties ans i))).bind
            fun r_tail =>
              (ProbComp.eval (expandSimSteps S₂ I next
                (I.restrict (fun i => (st i, Round.deliverOracle parties ans i)))
                (I.restrict r_tail))).map
                fun sub_tail =>
                  (sub_tail, fun i =>
                    next.outputAt i (st i, Round.deliverOracle parties ans i) (r_tail i))).map
            fun ⟨sub_tail, y⟩ =>
              (fun i : I =>
                ((pushTupleRestrict parties I (fun s => (v_sub s).coins) i, (sub_tail i).1),
                  Schedule.Received.append
                    (pushScheduleReceivedRestrict parties I (sc₂ op)
                      (fun s => (v_sub s).received) i)
                    (sub_tail i).2),
                y)) := by
      simp only [Steps.evalWith_oracle, expandSimSteps, idealJoint,
        ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
        PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
      refine congrArg (ProbComp.eval (W₁ op q)).bind (funext fun ans => ?_)
      rw [PMF.bind_comm]
      rfl
    -- 2. Apply subprotocol privacy `hSub op J q` and the induction hypothesis `ih`.
    rw [hlhs, hSub op J q]
    simp only [ih (fun i => (st i, Round.deliverOracle parties _ i))]
    -- 3. Unfold `(Sub op).realJoint W₂ J q` and the RHS of `Steps.compose`.
    simp only [Protocol.realJoint, Protocol.evalWith_eq, Protocol.outputOfView,
      Steps.compose, sampleSubCoins, eval_pi_pair, eval_pi_sampleSlotCoins,
      Steps.evalWith_append, Steps.evalWith_mapState,
      PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
      Prod.map_apply, Finset.restrict_def, id_eq]
    refine congrArg (ProbComp.eval (OracleComp.pi (Sub op).sampleCoins)).bind (funext fun c_k => ?_)
    -- Swap the `c_tail` and `r_sub` binds on the RHS so both sides bind `c_tail` then `r_sub`.
    rw [PMF.bind_comm]
    refine congrArg (ProbComp.eval (OracleComp.pi (sampleSubCoins Sub rest))).bind
      (funext fun c_tail => ?_)
    have hslot (i : Fin m) (s : Fin (spec₁.arity op)) (hs : parties s = i) :
        (query s (hs.symm ▸ st i), pushTuple parties c_k i s hs) = (q s, c_k s) := by
      subst hs
      rfl
    have hst_k :
        (fun i : Fin m =>
          ((st i, c_tail i),
            fun (s : Fin (spec₁.arity op)) (hs : parties s = i) =>
              (query s (hs.symm ▸ st i), pushTuple parties c_k i s hs))) =
        fun i : Fin m =>
          ((st i, c_tail i),
            fun (s : Fin (spec₁.arity op)) (_ : parties s = i) => (q s, c_k s)) := by
      funext i
      exact Prod.ext rfl (funext fun s => funext fun hs => hslot i s hs)
    rw [hst_k, evalWith_embed]
    simp only [PMF.bind_map, Function.comp_def,
      outputAt_embed, pullScheduleReceived_pushScheduleReceived, hslot,
      Steps.outputAt_append, Steps.outputAt_mapState]
    refine congrArg ((Sub op).steps.evalWith W₂ (fun s => (q s, c_k s))).bind
      (funext fun r_sub => ?_)
    have hdeliv :
        (fun i : Fin m =>
          ((st i, fun s hs => (Sub op).steps.outputAt s (q s, c_k s) (r_sub s)), c_tail i)) =
        fun i : Fin m =>
          ((st i,
            Round.deliverOracle parties (fun s => (Sub op).steps.outputAt s (q s, c_k s) (r_sub s))
              i),
            c_tail i) := rfl
    rw [hdeliv]
    refine congrArg (PMF.map · _) (funext fun r_tail => ?_)
    refine Prod.ext (funext fun i => ?_) rfl
    exact Prod.ext rfl
      (congrArg (Schedule.Received.append · (r_tail i.1))
        (congrFun (restrict_pushScheduleReceived parties I (sc₂ op) r_sub) i).symm)

end Composition

open _root_.Cslib.Crypto.Protocols.MPC.Composition

/-- Compose an `m`-party protocol `P` over `spec₁` with `k`-party subprotocols `Sub op` over
`spec₂` (Goldreich Section 7.5.2.1, Theorem 7.5.7, pp. 702–703; generalizing Section 7.3.1,
Theorem 7.3.3, pp. 637–638). -/
@[expose] noncomputable def Protocol.compose {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {sc₁ : Schedule m spec₁} {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {In Coins₁ Out : Fin m → Type}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)) :
    Protocol m spec₂ (Schedule.compose sc₂ sc₁) In
      (Schedule.ComposedCoins Coins₂ Coins₁ sc₁) Out where
  sampleCoins i := do
    let c₁ ← P.sampleCoins i
    let c_sub ← sampleSubCoins Sub sc₁ i
    return (c₁, c_sub)
  steps :=
    (Steps.compose Sub P.steps).mapState fun _ ⟨x_i, c₁_i, c_sub_i⟩ =>
      ((x_i, c₁_i), c_sub_i)

/-- Composed coalition simulator for `P.compose Sub` (Goldreich Section 7.5.2.1, Theorem 7.5.7
Proof Sketch, pp. 702–703; cf. Section 7.3.1, Theorem 7.3.3 Proof Sketch, pp. 637–638): runs the
outer simulator `S₁ I xI yI` to obtain simulated outer views `v₁` and expands each oracle call in
`P.steps` using the inner simulator `S₂ op (subCoalition parties I)`. -/
@[expose] noncomputable def composeSim {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {sc₁ : Schedule m spec₁} {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {In Coins₁ Out : Fin m → Type}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (S₁ : (I : Finset (Fin m)) → CoalitionSimulator sc₁ In Coins₁ Out I)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) :
    CoalitionSimulator (Schedule.compose sc₂ sc₁) In
      (Schedule.ComposedCoins Coins₂ Coins₁ sc₁) Out I :=
  fun xI yI => do
    let v₁ ← S₁ I xI yI
    let sub ← expandSimSteps S₂ I P.steps
      (fun i => (xI i, (v₁ i).coins)) (fun i => (v₁ i).received)
    return fun i => ⟨xI i, ((v₁ i).coins, (sub i).1), (sub i).2⟩

/-- Theorem 7.5.7 (Goldreich Section 7.5.2.1, pp. 702–703; cf. Theorem 7.3.3, pp. 637–638):
composing a perfectly private `m`-party outer protocol `P` with perfectly private `k`-party
subprotocols `Sub op` yields a perfectly private `m`-party protocol `P.compose Sub` in `W₂`. -/
theorem PerfectSemiHonestPrivate.compose {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
    {sc₁ : Schedule m spec₁} {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
    {In Coins₁ Out : Fin m → Type}
    {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}
    {P : Protocol m spec₁ sc₁ In Coins₁ Out}
    {W₁ : MultiOracleWorld spec₁} {W₂ : MultiOracleWorld spec₂}
    {f : Functionality m In Out}
    {S₁ : (I : Finset (Fin m)) → CoalitionSimulator sc₁ In Coins₁ Out I}
    {Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)}
    {S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J}
    (hP : PerfectSemiHonestPrivate P W₁ f S₁)
    (hSub : ∀ op, PerfectSemiHonestPrivate (Sub op) W₂ (W₁ op) (S₂ op)) :
    PerfectSemiHonestPrivate (P.compose Sub) W₂ f (composeSim P S₁ S₂) := by
  intro I x
  have houter :
      ProbComp.eval (idealJoint f I (composeSim P S₁ S₂ I) x) =
        (P.realJoint W₁ I x).bind fun ⟨v₁, y⟩ =>
          (ProbComp.eval (expandSimSteps S₂ I P.steps
            (fun i => (x i.1, (v₁ i).coins)) (fun i => (v₁ i).received))).map fun sub =>
              (fun i : I => ⟨x i.1, ((v₁ i).coins, (sub i).1), (sub i).2⟩, y) := by
    rw [← hP I x]
    simp [idealJoint, composeSim, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [houter]
  simp only [Protocol.realJoint, Protocol.evalWith_eq, Protocol.outputOfView, Protocol.compose,
    eval_pi_pair, Steps.evalWith_mapState, Steps.outputAt_mapState,
    PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    Prod.map_apply, Finset.restrict_def, id_eq]
  refine congrArg (ProbComp.eval (OracleComp.pi P.sampleCoins)).bind (funext fun c₁ => ?_)
  have hsteps := evalWith_compose_steps_eq_hybrid hSub I P.steps (fun i => (x i, c₁ i))
  have hmap := congrArg (PMF.map fun res : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.1 ×
        Schedule.Received (Schedule.compose sc₂ sc₁) i.1) × ((i : Fin m) → Out i) =>
      (fun i : I =>
        (⟨x i.1, (c₁ i.1, (res.1 i).1), (res.1 i).2⟩ :
          PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁) (Schedule.compose sc₂ sc₁) i.1),
        res.2)) hsteps
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
    Finset.restrict_def] at hmap ⊢
  exact hmap

/-! ### Part 2: Randomized-to-Deterministic Wrapper (Proposition 7.3.4 & Eq. 7.48) -/

/-- Randomized `m`-party functionality defined by sampling a uniform shared coin string
`r : BitString coins` and evaluating `g r x` (Goldreich Section 7.3.1, pp. 638–639;
Section 7.5.2.4, p. 707). -/
@[expose] noncomputable def randomizedFunctionality {m : ℕ} {In Out : Fin m → Type} (coins : ℕ)
    (g : BitString coins → ((i : Fin m) → In i) → (i : Fin m) → Out i) :
    Functionality m In Out := fun x => do
  let r ← ProbComp.uniform (BitString coins)
  return g r x

/-- Deterministic functionality associated to `g` via shared coin-tossing (Goldreich
Section 7.5.2.4, Eq. 7.48, p. 707; generalizing Section 7.3.1, Eq. 7.19 on p. 638 and
Proposition 7.3.4 on p. 639): takes party inputs `(x_i, r_i)` and evaluates
`g (∑ i : Fin m, r_i) x`, where addition on `BitString coins` is bitwise XOR. -/
@[expose] def detOfRandomized {m : ℕ} {In Out : Fin m → Type} (coins : ℕ)
    (g : BitString coins → ((i : Fin m) → In i) → (i : Fin m) → Out i)
    (xr : (i : Fin m) → In i × BitString coins) : (i : Fin m) → Out i :=
  g (∑ i : Fin m, (xr i).2) (fun i => (xr i).1)

/-- Precompose an `m`-party protocol `P` with local party input encodings
`enc : (i : Fin m) → In i → In' i`. -/
@[expose] def Protocol.mapInput {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In In' Coins Out : Fin m → Type}
    (enc : (i : Fin m) → In i → In' i)
    (P : Protocol m spec sc In' Coins Out) :
    Protocol m spec sc In Coins Out where
  sampleCoins := P.sampleCoins
  steps := P.steps.mapState fun i ⟨x_i, c_i⟩ => (enc i x_i, c_i)

/-- Coalition simulator for `P.mapInput enc`. -/
@[expose] def mapInputSim {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In In' Coins Out : Fin m → Type}
    (enc : (i : Fin m) → In i → In' i)
    (S : (I : Finset (Fin m)) → CoalitionSimulator sc In' Coins Out I)
    (I : Finset (Fin m)) :
    CoalitionSimulator sc In Coins Out I :=
  fun xI yI => do
    let v ← S I (fun i => enc i.1 (xI i)) yI
    return fun i => ⟨xI i, (v i).coins, (v i).received⟩

/-- Perfect semi-honest privacy is preserved under local input encodings `Protocol.mapInput`. -/
theorem PerfectSemiHonestPrivate.mapInput {m : ℕ} {spec : MultiOracleSpec}
    {sc : Schedule m spec} {In In' Coins Out : Fin m → Type}
    {enc : (i : Fin m) → In i → In' i}
    {P : Protocol m spec sc In' Coins Out}
    {W : MultiOracleWorld spec}
    {f : Functionality m In' Out}
    {S : (I : Finset (Fin m)) → CoalitionSimulator sc In' Coins Out I}
    (hP : PerfectSemiHonestPrivate P W f S) :
    PerfectSemiHonestPrivate (P.mapInput enc) W
      (fun x => f (fun i => enc i (x i))) (mapInputSim enc S) := by
  intro I x
  have h := hP I (fun i => enc i (x i))
  have hmap := congrArg (PMF.map fun res :
        ((i : I) → PartyView In' Coins sc i.1) × ((i : Fin m) → Out i) =>
      (fun i : I =>
        (⟨x i.1, (res.1 i).coins, (res.1 i).received⟩ : PartyView In Coins sc i.1),
        res.2)) h
  simp only [idealJoint, mapInputSim, Protocol.realJoint, Protocol.evalWith_eq,
    Protocol.outputOfView, Protocol.mapInput, Steps.evalWith_mapState, Steps.outputAt_mapState,
    ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
    PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.map_apply, Finset.restrict_def, id_eq]
    at hmap ⊢
  exact hmap

/-- Wrap a deterministic-input protocol `P` expecting `(x_i, r_i)` into a protocol for input `x_i`
in which each party `i` independently samples a uniform `r_i : BitString coins` as part of its
private random tape (Goldreich Section 7.3.1, Proposition 7.3.4, p. 639; Section 7.5.2.4,
Eq. 7.48, p. 707). -/
@[expose] noncomputable def Protocol.randomizedWrapper {m : ℕ} {spec : MultiOracleSpec}
    {sc : Schedule m spec} {In Coins Out : Fin m → Type} (coins : ℕ)
    (P : Protocol m spec sc (fun i => In i × BitString coins) Coins Out) :
    Protocol m spec sc In (fun i => BitString coins × Coins i) Out where
  sampleCoins i := do
    let r_i ← ProbComp.uniform (BitString coins)
    let c_i ← P.sampleCoins i
    return (r_i, c_i)
  steps :=
    P.steps.mapState fun _ ⟨x_i, r_i, c_i⟩ => ((x_i, r_i), c_i)

/-- Coalition simulator for `P.randomizedWrapper coins` (Goldreich Section 7.3.1, Proposition 7.3.4
Proof, pp. 639–640; Section 7.5.2.4, p. 707): samples independent uniform coin shares `rI i` for
each coalition party `i ∈ I`, runs the deterministic simulator `S I (fun i => (xI i, rI i)) yI`, and
combines `(rI i, (v i).coins)` into the simulated coin tape. -/
@[expose] noncomputable def randomizedWrapperSim {m : ℕ} {spec : MultiOracleSpec}
    {sc : Schedule m spec} {In Coins Out : Fin m → Type} (coins : ℕ)
    (S : (I : Finset (Fin m)) →
      CoalitionSimulator sc (fun i => In i × BitString coins) Coins Out I)
    (I : Finset (Fin m)) :
    CoalitionSimulator sc In (fun i => BitString coins × Coins i) Out I :=
  fun xI yI => do
    let rI ←
      OracleComp.piRestrict (α := fun _ => BitString coins) I
        (fun _ : I => ProbComp.uniform (BitString coins))
    let v ← S I (fun i => (xI i, rI i)) yI
    return fun i => ⟨xI i, (rI i, (v i).coins), (v i).received⟩

private theorem eval_pi_uniform_bitString (m coins : ℕ) :
    ProbComp.eval (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins))) =
      PMF.uniformOfFintype (Fin m → BitString coins) := by
  rw [ProbComp.eval_pi]
  simp only [ProbComp.eval_uniform]
  exact PMF.pi_uniformOfFintype

private theorem restrict_update_of_notMem {m : ℕ} {α : Fin m → Type}
    {I : Finset (Fin m)} {ℓ : Fin m} (hℓ : ℓ ∉ I)
    (r : (i : Fin m) → α i) (v : α ℓ) :
    I.restrict (Function.update r ℓ v) = I.restrict r := by
  funext ⟨i, hi⟩
  have hne : i ≠ ℓ := fun h => hℓ (h ▸ hi)
  exact Function.update_of_ne hne v r

/-- Key independence lemma for Eq. 7.48 (p. 707) and Proposition 7.3.4 (pp. 639–640): for any proper
coalition `I ≠ Finset.univ`, when `r : Fin m → BitString coins` is sampled with independent uniform
coordinates, the pair `(I.restrict r, ∑ i : Fin m, r i)` has the exact same joint distribution as
sampling `rI` via `OracleComp.piRestrict I` and independently sampling a uniform sum
`s : BitString coins`. -/
private theorem bind_restrict_and_sum_pi_uniform {m : ℕ} (coins : ℕ) {β : Type}
    {I : Finset (Fin m)} (hI : I ≠ Finset.univ)
    (k : (I → BitString coins) → BitString coins → PMF β) :
    (ProbComp.eval (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins)))).bind
        (fun r => k (I.restrict r) (∑ j : Fin m, r j)) =
      (ProbComp.eval
        (OracleComp.piRestrict (α := fun _ => BitString coins) I
          (fun _ : I => ProbComp.uniform (BitString coins)))).bind
        fun rI =>
          (ProbComp.eval (ProbComp.uniform (BitString coins))).bind fun s =>
            k rI s := by
  classical
  have hex : ∃ ℓ : Fin m, ℓ ∉ I := by
    by_contra h
    apply hI
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨ℓ, hℓ⟩ := hex
  have hstep1 :
      (ProbComp.eval (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins)))).bind
          (fun r => k (I.restrict r) (∑ j : Fin m, r j)) =
      (ProbComp.eval (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins)))).bind
        fun r =>
          (ProbComp.eval (ProbComp.uniform (BitString coins))).bind fun s =>
            k (I.restrict r) s := by
    rw [eval_pi_uniform_bitString]
    conv_lhs => rw [← PMF.uniformOfFintype_update ℓ, PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def, ProbComp.eval_uniform]
    rw [PMF.bind_comm]
    refine congrArg (PMF.uniformOfFintype (Fin m → BitString coins)).bind (funext fun r => ?_)
    have hsum :
        ((PMF.uniformOfFintype (BitString coins)).bind fun v =>
          k (I.restrict (Function.update r ℓ v)) (∑ j : Fin m, Function.update r ℓ v j)) =
        ((PMF.uniformOfFintype (BitString coins)).map
          (fun v => ∑ j : Fin m, Function.update r ℓ v j)).bind (k (I.restrict r)) := by
      simp only [restrict_update_of_notMem hℓ, PMF.bind_map, Function.comp_def]
    rw [hsum, PMF.uniformOfFintype_map_sum_update r ℓ]
  rw [hstep1]
  exact ProbComp.eval_bind_restrict_pi I (fun _ : Fin m => ProbComp.uniform (BitString coins))
    (fun rI => (ProbComp.eval (ProbComp.uniform (BitString coins))).bind (k rI))

/-- Proposition 7.3.4 (Goldreich Section 7.3.1, pp. 639–640) combined with the composition theorem
(Section 7.3.1 Application, pp. 638–639, Eq. 7.19) and Section 7.5.2.4 Eq. 7.48 (p. 707):
if `P` is perfectly semi-honest private for `detOfRandomized coins g`, then
`P.randomizedWrapper coins` is perfectly semi-honest private for `randomizedFunctionality coins g`
against every proper static coalition `I ≠ Finset.univ`.

This is proved directly rather than via `PerfectSemiHonestPrivate.compose`, because the coin-sharing
reduction is only private against proper coalitions `I ≠ Finset.univ`, whereas
`PerfectSemiHonestPrivate.compose` requires all-`I` privacy of the outer protocol. Note that
restricting to `I ≠ Finset.univ` is narrower than Goldreich's quantifier over all `I ⊆ [m]` in
Definition 7.5.1 (p. 696, where `I = [m]` is called trivial on pp. 697, 703): under the joint
view-and-output equation Eq. 7.40 for randomized functionalities, `I = Finset.univ` is not
satisfied by an output-independent coin simulator (for `m = 2`, Definition 7.2.1 considers only
single-party views, so Proposition 7.3.4 itself is fully covered). Moreover, this theorem proves
exact `PMF` equality with an unrestricted `ProbComp` simulator rather than Goldreich's computational
indistinguishability with PPT simulators. -/
theorem perfectSemiHonestPrivate_randomizedWrapper {m : ℕ}
    {spec : MultiOracleSpec} {sc : Schedule m spec} {In Coins Out : Fin m → Type}
    (coins : ℕ) (g : BitString coins → ((i : Fin m) → In i) → (i : Fin m) → Out i)
    (P : Protocol m spec sc (fun i => In i × BitString coins) Coins Out)
    (W : MultiOracleWorld spec)
    (S : (I : Finset (Fin m)) →
      CoalitionSimulator sc (fun i => In i × BitString coins) Coins Out I)
    (hP : PerfectSemiHonestPrivate P W
      (Functionality.ofDeterministic (detOfRandomized coins g)) S) :
    PerfectSemiHonestPrivateProper (P.randomizedWrapper coins) W
      (randomizedFunctionality coins g) (randomizedWrapperSim coins S) := by
  intro I hI x
  -- 1. Express the real execution of `P.randomizedWrapper coins` as binding `r` then `P.realJoint`.
  have hreal :
      (P.randomizedWrapper coins).realJoint W I x =
        (ProbComp.eval (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins)))).bind
          fun r =>
            (P.realJoint W I (fun i => (x i, r i))).map fun res =>
              (fun i : I =>
                (⟨x i.1, (r i.1, (res.1 i).coins), (res.1 i).received⟩ :
                  PartyView In (fun i => BitString coins × Coins i) sc i.1),
                res.2) := by
    simp only [Protocol.realJoint, Protocol.evalWith_eq, Protocol.outputOfView,
      Protocol.randomizedWrapper, eval_pi_pair, Steps.evalWith_mapState, Steps.outputAt_mapState,
      PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
      Prod.map_apply, Finset.restrict_def, id_eq]
  -- 2. Substitute `← hP I (fun i => (x i, r i))` inside the `r` bind.
  have hsub :
      (P.randomizedWrapper coins).realJoint W I x =
        (ProbComp.eval (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins)))).bind
          fun r =>
            (ProbComp.eval (S I (fun i => (x i.1, I.restrict r i))
              (I.restrict (g (∑ j : Fin m, r j) x)))).map fun v =>
                (fun i : I =>
                  (⟨x i.1, (I.restrict r i, (v i).coins), (v i).received⟩ :
                    PartyView In (fun i => BitString coins × Coins i) sc i.1),
                  g (∑ j : Fin m, r j) x) := by
    rw [hreal]
    refine congrArg (ProbComp.eval _).bind (funext fun r => ?_)
    rw [← hP I (fun i => (x i, r i))]
    simp [idealJoint, Functionality.ofDeterministic, detOfRandomized,
      PMF.map_comp, Function.comp_def, Finset.restrict_def]
  -- 3. Apply `bind_restrict_and_sum_pi_uniform` to decouple `I.restrict r` from `∑ j, r j`.
  rw [hsub, bind_restrict_and_sum_pi_uniform coins hI (k := fun rI s =>
    (ProbComp.eval (S I (fun i => (x i.1, rI i)) (I.restrict (g s x)))).map fun v =>
      (fun i : I =>
        (⟨x i.1, (rI i, (v i).coins), (v i).received⟩ :
          PartyView In (fun i => BitString coins × Coins i) sc i.1),
        g s x))]
  -- 4. Swap the `rI` and `s` binds to match `idealJoint` of `randomizedFunctionality`.
  symm
  rw [PMF.bind_comm]
  simp [idealJoint, randomizedFunctionality, randomizedWrapperSim, Finset.restrict_def]

/-! ### Part 3: XOR Prelude Circuit and $\text{OT}_1^4$-Hybrid GMW Protocol (Theorem 7.5.12) -/

namespace XORPrelude

/-- Single-output 4-gate De Morgan circuit computing `a c + b c` (`a c ^^ b c`) at coordinate
`c : Fin coins` of `Fin.append a b : BitString (coins + coins)`, built from
`Cslib.Circuits.Program.appendXor`. -/
@[expose] def xorBitAtCircuit (coins : ℕ) (c : Fin coins) :
    Cslib.Circuits.Circuit Boolean.signature (coins + coins) 1 where
  program :=
    Cslib.Circuits.Program.empty.appendXor
      (.input (Fin.castAdd coins c)) (.input (Fin.natAdd coins c))
  outputs _ := .gate (Fin.last 3)

@[simp] private theorem eval_xorBitAtCircuit (coins : ℕ) (c : Fin coins)
    (a b : BitString coins) :
    (xorBitAtCircuit coins c).eval Boolean.interpretation (Fin.append a b) 0 = (a + b) c := by
  have h :=
    Cslib.Circuits.Program.trace_appendXor Cslib.Circuits.Program.empty
      (.input (Fin.castAdd coins c)) (.input (Fin.natAdd coins c)) (Fin.append a b)
  change (Cslib.Circuits.Program.empty.appendXor
    (.input (Fin.castAdd coins c)) (.input (Fin.natAdd coins c))).trace Boolean.interpretation
    (Fin.append a b) (.gate (Fin.last 3)) = (a c ^^ b c)
  rw [h]
  change (Fin.append a b (Fin.castAdd coins c) ^^ Fin.append a b (Fin.natAdd coins c)) =
    (a c ^^ b c)
  rw [Fin.append_left, Fin.append_right]

@[simp] private theorem size_xorBitAtCircuit (coins : ℕ) (c : Fin coins) :
    (xorBitAtCircuit coins c).size = 4 :=
  rfl

/-- Single-gate Boolean circuit outputting `0 : BitString coins` via `.const false`. -/
@[expose] def zeroBitStringCircuit (w coins : ℕ) :
    Cslib.Circuits.Circuit Boolean.signature w coins where
  size := 1
  program := .gate .empty ⟨.const false, Fin.elim0⟩
  outputs := fun _ => .gate 0

private theorem eval_zeroBitStringCircuit (w coins : ℕ) (u : BitString w) :
    (zeroBitStringCircuit w coins).eval Boolean.interpretation u = 0 :=
  rfl

/-- Coordinatewise XOR circuit of size `4 * coins` on two `coins`-bit strings, constructed side by
side via `Cslib.Circuits.Circuit.pi` from `xorBitAtCircuit`. -/
@[expose] def xorBitStringsCircuit (coins : ℕ) :
    Cslib.Circuits.Circuit Boolean.signature (coins + coins) coins :=
  Cslib.Circuits.Circuit.pi (xorBitAtCircuit coins)

private theorem eval_xorBitStringsCircuit (coins : ℕ) (a b : BitString coins) :
    (xorBitStringsCircuit coins).eval Boolean.interpretation (Fin.append a b) = a + b := by
  ext c
  simp [xorBitStringsCircuit]

private theorem size_xorBitStringsCircuit (coins : ℕ) :
    (xorBitStringsCircuit coins).size = 4 * coins := by
  simp [xorBitStringsCircuit, Nat.mul_comm]

/-- Boolean circuit summing `m` blocks of width `coins` by coordinatewise XOR. -/
@[expose] def sumBlocksCircuit :
    (m coins : ℕ) → Cslib.Circuits.Circuit Boolean.signature (m * coins) coins
  | 0, coins => zeroBitStringCircuit (0 * coins) coins
  | m + 1, coins =>
    (xorBitStringsCircuit coins).comp
      (((sumBlocksCircuit m coins).comp
          (Circuit.wiring Boolean.signature
            (Fin.castLE (Nat.mul_le_mul_right coins (Nat.le_succ m))))).append
        (Circuit.wiring Boolean.signature fun c => finProdFinEquiv (Fin.last m, c)))

private theorem eval_sumBlocksCircuit (m coins : ℕ) (r : Fin m → BitString coins) :
    (sumBlocksCircuit m coins).eval Boolean.interpretation
      ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := coins)).symm r) =
    ∑ i : Fin m, r i := by
  induction m with
  | zero =>
    simp [sumBlocksCircuit, eval_zeroBitStringCircuit]
  | succ m ih =>
    simp only [sumBlocksCircuit, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring]
    have hfirst :
        (Cslib.BitString.blocksEquiv (α := Bool) (m := m + 1) (k := coins)).symm r ∘
          Fin.castLE (Nat.mul_le_mul_right coins (Nat.le_succ m)) =
        (Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := coins)).symm
          (fun i : Fin m => r i.castSucc) := by
      funext idx
      obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective idx
      have hcast :
          Fin.castLE (Nat.mul_le_mul_right coins (Nat.le_succ m)) (finProdFinEquiv (i, c)) =
            finProdFinEquiv (i.castSucc, c) := by
        ext
        rfl
      simp [Function.comp_apply, hcast]
    have hlast :
        ((Cslib.BitString.blocksEquiv (α := Bool) (m := m + 1) (k := coins)).symm r ∘
          fun c => finProdFinEquiv (Fin.last m, c)) =
        r (Fin.last m) := by
      funext c
      simp
    rw [hfirst, hlast, ih, eval_xorBitStringsCircuit, Fin.sum_univ_castSucc]

/-- Zero-gate wiring circuit extracting the `m * n` party input bits from `m` blocks of width
`n + coins`. -/
@[expose] def extractInputsCircuit (m n coins : ℕ) :
    Cslib.Circuits.Circuit Boolean.signature (m * (n + coins)) (m * n) :=
  Circuit.wiring Boolean.signature fun idx =>
    let ij := finProdFinEquiv.symm idx
    finProdFinEquiv (ij.1, Fin.castAdd coins ij.2)

private theorem eval_extractInputsCircuit (m n coins : ℕ)
    (x : Fin m → BitString n) (r : Fin m → BitString coins) :
    (extractInputsCircuit m n coins).eval Boolean.interpretation
      ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n + coins)).symm
        (fun i => Fin.append (x i) (r i))) =
    (Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n)).symm x := by
  funext idx
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective idx
  simp only [extractInputsCircuit, Circuit.eval_wiring, Function.comp_apply,
    Cslib.BitString.blocksEquiv_symm_apply, Equiv.symm_apply_apply, Fin.append_left]

/-- Zero-gate wiring circuit extracting the `m * coins` party coin bits from `m` blocks of width
`n + coins`. -/
@[expose] def extractCoinsCircuit (m n coins : ℕ) :
    Cslib.Circuits.Circuit Boolean.signature (m * (n + coins)) (m * coins) :=
  Circuit.wiring Boolean.signature fun idx =>
    let ic := finProdFinEquiv.symm idx
    finProdFinEquiv (ic.1, Fin.natAdd n ic.2)

private theorem eval_extractCoinsCircuit (m n coins : ℕ)
    (x : Fin m → BitString n) (r : Fin m → BitString coins) :
    (extractCoinsCircuit m n coins).eval Boolean.interpretation
      ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n + coins)).symm
        (fun i => Fin.append (x i) (r i))) =
    (Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := coins)).symm r := by
  funext idx
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective idx
  simp only [extractCoinsCircuit, Circuit.eval_wiring, Function.comp_apply,
    Cslib.BitString.blocksEquiv_symm_apply, Equiv.symm_apply_apply, Fin.append_right]

private theorem size_sumBlocksCircuit (m coins : ℕ) :
    (sumBlocksCircuit m coins).size = 1 + m * (4 * coins) := by
  induction m with
  | zero => simp [sumBlocksCircuit, zeroBitStringCircuit]
  | succ m ih =>
    simp [sumBlocksCircuit, ih, size_xorBitStringsCircuit, Nat.add_mul, Nat.add_assoc]

end XORPrelude

open _root_.Cslib.Crypto.Protocols.MPC.XORPrelude

/-- XOR-combining prelude circuit (Goldreich Section 7.5.2.4, Eq. 7.48, p. 707): takes `m` party
blocks `(x_i, r_i)` of width `n + coins` and outputs the `m * n` packed party inputs
`BitString.blocksEquiv.symm x` followed by the `coins`-bit XOR sum `∑ i : Fin m, r i`. -/
@[expose] def xorPreludeCircuit (m n coins : ℕ) :
    Cslib.Circuits.Circuit Boolean.signature (m * (n + coins)) (m * n + coins) :=
  (extractInputsCircuit m n coins).append
    ((sumBlocksCircuit m coins).comp (extractCoinsCircuit m n coins))

/-- Correctness of `xorPreludeCircuit`: evaluating `xorPreludeCircuit m n coins` on the packed
input-coin blocks `fun i => Fin.append (x i) (r i)` yields `Fin.append (BitString.blocksEquiv.symm
x) (∑ i : Fin m, r i)`. -/
@[simp] theorem eval_xorPreludeCircuit (m n coins : ℕ)
    (x : Fin m → BitString n) (r : Fin m → BitString coins) :
    (xorPreludeCircuit m n coins).eval Boolean.interpretation
      ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n + coins)).symm
        (fun i => Fin.append (x i) (r i))) =
    Fin.append
      ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n)).symm x)
      (∑ i : Fin m, r i) := by
  simp [xorPreludeCircuit, eval_extractInputsCircuit, eval_extractCoinsCircuit,
    eval_sumBlocksCircuit]

/-- Gate count of `xorPreludeCircuit m n coins`. -/
@[simp] theorem size_xorPreludeCircuit (m n coins : ℕ) :
    (xorPreludeCircuit m n coins).size = 1 + m * (4 * coins) := by
  simp [xorPreludeCircuit, extractInputsCircuit, extractCoinsCircuit, size_sumBlocksCircuit]

/-- Deterministic `m`-party $\text{OT}_1^4$-hybrid GMW protocol composed from
`gmwCircuitProtocol m n k C` (Construction 7.5.10, p. 706), `multiPartyMulProtocol m`
(Construction 7.5.8, p. 704), and `twoPartyMulProtocol` (Construction 7.3.7, p. 643).
Because `gmwCircuitProtocol m n k C` makes one `sharedMulSpec m` call per `.and`/`.or` gate in
Step 2 plus `m * k` `sharedMulSpec m` share-refresh calls in Step 3 (`coordSchedule`), composing
with `multiPartyMulProtocol m` (`m * (m - 1) / 2` calls to `sharedMulSpec 2`) and
`twoPartyMulProtocol` (1 call to `ot14Spec`) expands each `sharedMulSpec m` call into
`m * (m - 1) / 2` pairwise calls to `ot14Spec`. -/
@[expose] noncomputable def gmwOT14Protocol (m n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)) :=
  ((gmwCircuitProtocol m n k C).compose (fun _ => multiPartyMulProtocol m)).compose
    (fun _ => twoPartyMulProtocol)

/-- Composed coalition simulator for `gmwOT14Protocol m n k C`. -/
@[expose] noncomputable def gmwOT14Sim (m n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)) :=
  composeSim
    ((gmwCircuitProtocol m n k C).compose (fun _ => multiPartyMulProtocol m))
    (composeSim (gmwCircuitProtocol m n k C)
      (gmwCircuitSim m n k C)
      (fun _ => multiPartyMulSim m))
    (fun _ => twoPartyMulSim)

/-- Full-coalition perfect semi-honest privacy of the deterministic `gmwOT14Protocol m n k C` in
`ot14World` (combining Proposition 7.5.11, pp. 706–707; Proposition 7.5.9, pp. 704–705;
Proposition 7.3.8, p. 644; and Theorem 7.5.7, pp. 702–703). -/
theorem perfectSemiHonestPrivate_gmwOT14 (m n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)) :
    PerfectSemiHonestPrivate (gmwOT14Protocol m n k C) ot14World
      (Functionality.ofDeterministic (circuitFunctionality m n k C))
      (gmwOT14Sim m n k C) :=
  ((perfectSemiHonestPrivate_gmwCircuit m n k C).compose
    (fun _ => perfectSemiHonestPrivate_multiPartyMul m)).compose
    (fun _ => perfectSemiHonestPrivate_twoPartyMul)

/-- Randomized `m`-party $\text{OT}_1^4$-hybrid GMW protocol (Goldreich Section 7.5.2.4,
Eq. 7.48 and Theorem 7.5.12, p. 707; cf. Section 7.3.4, Theorem 7.3.11, p. 648): runs
`Protocol.randomizedWrapper coins` around `gmwOT14Protocol m (n + coins) k (C.comp
(xorPreludeCircuit m n coins))` precomposed with `Protocol.mapInput` packing `(x_i, r_i)` into
`Fin.append x_i r_i : BitString (n + coins)`. -/
@[expose] noncomputable def gmwOT14RandomizedProtocol (m coins n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n + coins) (m * k)) :=
  ((gmwOT14Protocol m (n + coins) k (C.comp (xorPreludeCircuit m n coins))).mapInput
    (fun _ (xr : BitString n × BitString coins) => Fin.append xr.1 xr.2)).randomizedWrapper coins

/-- Coalition simulator for `gmwOT14RandomizedProtocol m coins n k C`. -/
@[expose] noncomputable def gmwOT14RandomizedSim (m coins n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n + coins) (m * k)) :=
  randomizedWrapperSim coins
    (mapInputSim (fun _ (xr : BitString n × BitString coins) => Fin.append xr.1 xr.2)
      (gmwOT14Sim m (n + coins) k (C.comp (xorPreludeCircuit m n coins))))

/-- Theorem 7.5.12 (Goldreich Section 7.5.2.4, p. 707; generalizing Theorem 7.3.11, Section 7.3.4,
p. 648): for any randomized `m`-party Boolean circuit `C : Circuit Boolean.signature (m * n + coins)
(m * k)`, `gmwOT14RandomizedProtocol m coins n k C` perfectly and privately computes the randomized
functionality of `C` in `ot14World` against every proper static coalition `I ≠ Finset.univ`.

Note that the proper-coalition quantifier `I ≠ Finset.univ` (`PerfectSemiHonestPrivateProper`) is
narrower than Goldreich's Definition 7.5.1 and Theorem 7.5.12 (which quantify over all `I ⊆ [m]`,
p. 696, treating `I = [m]` as trivial on pp. 697, 703), because under the joint view-and-output
equation Eq. 7.40 for randomized functionalities, `I = Finset.univ` is not satisfied when coin
shares are simulated independently of the output. Furthermore, this theorem establishes exact `PMF`
distributional equality with an unrestricted `ProbComp` simulator (`gmwOT14RandomizedSim`), whereas
Goldreich states computational indistinguishability with PPT simulators (uniform polynomial-time
efficiency is certified in M5). -/
theorem perfectSemiHonestPrivateProper_gmwOT14Randomized (m coins n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n + coins) (m * k)) :
    PerfectSemiHonestPrivateProper (gmwOT14RandomizedProtocol m coins n k C) ot14World
      (randomizedFunctionality coins (fun r x i =>
        Cslib.BitString.block
          (C.eval Boolean.interpretation
            (Fin.append
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n)).symm x) r)) i))
      (gmwOT14RandomizedSim m coins n k C) := by
  apply perfectSemiHonestPrivate_randomizedWrapper
  have hmap :=
    (perfectSemiHonestPrivate_gmwOT14 m (n + coins) k
      (C.comp (xorPreludeCircuit m n coins))).mapInput
      (enc := fun _ (xr : BitString n × BitString coins) => Fin.append xr.1 xr.2)
  have hfunc :
      (fun xr : Fin m → BitString n × BitString coins =>
        Functionality.ofDeterministic
          (circuitFunctionality m (n + coins) k (C.comp (xorPreludeCircuit m n coins)))
          (fun i => Fin.append (xr i).1 (xr i).2)) =
      Functionality.ofDeterministic
        (detOfRandomized coins (fun r x i =>
          Cslib.BitString.block
            (C.eval Boolean.interpretation
              (Fin.append
                ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n)).symm x) r)) i)) := by
    funext xr
    dsimp [Functionality.ofDeterministic, detOfRandomized]
    congr 1
    funext i
    dsimp [circuitFunctionality]
    rw [Circuit.eval_comp, eval_xorPreludeCircuit]
  rw [← hfunc]
  exact hmap

end Cslib.Crypto.Protocols.MPC
