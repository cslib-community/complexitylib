/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PedersenCommitment.PublicOperations
public import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Game.FourHop
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Languages.Probabilistic.UniformNat.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Fair-coin realization of Pedersen commitments and key generation

`PrimeOrderGroupFamily.pedersenCommitProb` and `PrimeOrderGroupFamily.pedersenKeyGenProb` sample
their exponents using the bounded `sampleExp` program (`ProbComp.sampleModNat`) and evaluate the
public commitment and key-generation operations. Their native strict-PPT certificates charge the
unary accuracy parameter, the group description or advertised public-key encoding
`pedersenScheme.encodeKey`, and the message word. Each `sampleExp` draw uses `n + |encNat q|` fair
bits for `q = F.order d`, within statistical distance `1 / 2 ^ n` of exact uniform on `ZMod q`, and
every opening has at most `|encNat q|` bits.

Replacing ideal commitment sampling (`pedersenScheme.commitDist`) with `pedersenCommitProb`, or
ideal key generation (`pedersenKeyDist`) with `pedersenKeyDistProb`, changes any randomized Boolean
continuation by at most `1 / 2 ^ n`. Combining this with the exact hiding and binding reductions in
`PedersenCommitment.lean` yields concrete and asymptotic hiding and binding bounds for:

* `pedersenHidingProbForKey` (chosen-message hiding with `pedersenCommitProb` at a fixed key
  `h ≠ 0`, with advantage at most `2 / 2 ^ n`),
* `pedersenHidingProbGame` and its executable `ProbComp Bool` realization
  `pedersenHidingProbExperiment` (where both key generation `pedersenKeyDistProb` and challenge
  commitment sampling `pedersenCommitProb` use `sampleExp`, with advantage at most
  `1 / m + 4 / 2 ^ n` and uniform strict-PPT certificate `isPPTOn_pedersenHidingProbExperiment`),
  and
* `pedersenScheme.hidingGame (F.pedersenKeyDistProb setup)` and
  `pedersenScheme.bindingGame (F.pedersenKeyDistProb setup)` (`StatisticalHiding`,
  `ComputationalHiding`, and `Binding` under `F.DiscreteLog setup`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenCommitProb`: bounded fair-coin commitment and opening.
* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenKeyGenProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.pedersenKeyDistProb`: bounded fair-coin Pedersen key
  generation and setup distribution.
* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenHidingProbForKey`,
  `Cslib.Crypto.PrimeOrderGroupFamily.pedersenHidingProbGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.pedersenHidingProbExperiment`: chosen-message hiding games and
  executable experiment using `pedersenCommitProb` and `pedersenKeyGenProb`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_pedersenCommitProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_pedersenKeyGenProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_pedersenHidingProbExperiment`: uniform strict-PPT
  certificates for commitment sampling, key generation, and the native hiding experiment.
* `Cslib.Crypto.PrimeOrderGroupFamily.eval_pedersenCommitProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.eval_pedersenKeyGenProb`: exact output laws.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_pedersenCommitProb_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_pedersenKeyGenProb_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_pedersenKeyDistProb_le`: continuation error at
  most `1 / 2 ^ n` against the ideal distributions.
* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenVerify_of_mem_support_pedersenCommitProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.length_opening_pedersenCommitProb_le`: support correctness
  and opening-length bound.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_pedersenHidingProbForKey_le_of_ne_zero`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_pedersenHidingProbGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.negligible_advantage_pedersenHidingProbGame`: concrete and
  asymptotic hiding for `pedersenHidingProbForKey` and `pedersenHidingProbGame`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_pedersenHidingGame_pedersenKeyDistProb_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.pedersenScheme_statisticalHiding_pedersenKeyDistProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DiscreteLog.pedersenScheme_binding_pedersenKeyDistProb`:
  `StatisticalHiding` and computational `Binding` of `pedersenScheme` under `pedersenKeyDistProb`.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-- Sample a bounded approximately uniform exponent, then evaluate Pedersen's public commitment
operations on its canonical bit representation. The accuracy parameter controls the sampling
error; the ideal law remains `pedersenScheme.commitDist`. -/
@[expose] noncomputable def pedersenCommitProb (n : ℕ) (key : F.PedersenKey) (message : List Bool) :
    ProbComp (List Bool × List Bool) := do
  let r ← F.sampleExp n key.1
  return F.pedersenPublicOperations.commit key message r.bits

/-- Pedersen commitment sampling is uniformly strict PPT in the unary accuracy parameter, actual
public key encoding, and message word. -/
theorem isPPTOn_pedersenCommitProb :
    IsPPTOn (encPair encUnary (encPair F.pedersenScheme.encodeKey encBits))
      (encPair encBits encBits)
      (fun ((n, key, msg) : ℕ × F.PedersenKey × List Bool) => F.pedersenCommitProb n key msg) := by
  let E := encPair encUnary (encPair F.pedersenScheme.encodeKey encBits)
  have hn := ComputableInPolyTime.fst encUnary (encPair F.pedersenScheme.encodeKey encBits)
  have hrest := ComputableInPolyTime.snd encUnary (encPair F.pedersenScheme.encodeKey encBits)
  have hk := (ComputableInPolyTime.fst F.pedersenScheme.encodeKey encBits).comp hrest
  have hm := (ComputableInPolyTime.snd F.pedersenScheme.encodeKey encBits).comp hrest
  have hkey : ComputableInPolyTime
      (fun k : F.PedersenKey => (k.1, F.encode k.1 k.2))
      F.pedersenScheme.encodeKey (encPair F.encDesc encBits) := .of_eq fun _ => rfl
  have hd := (hkey.comp hk).fst'
  have hs := F.isPPTOn_sampleExp hn hd
  have hinput := ComputableInPolyTime.fst E encNat
  have hr : ComputableInPolyTime
      (fun p : (ℕ × F.PedersenKey × List Bool) × ℕ => p.2.bits)
      (encPair E encNat) encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp (ComputableInPolyTime.snd E encNat)
  have heval := F.pedersenPublicOperations.computableInPolyTime_commit
    (hk.comp hinput) (hm.comp hinput) hr
  unfold pedersenCommitProb
  exact hs.bind_with heval.isPPTOn

/-- The sampled output is the existing Pedersen commitment-and-opening map applied to the
approximately uniform residue law. -/
theorem eval_pedersenCommitProb (n : ℕ) (key : F.PedersenKey) (message : List Bool) :
    ProbComp.eval (F.pedersenCommitProb n key message) =
      ((ProbComp.eval (F.sampleExp n key.1)).map
        (Nat.cast : ℕ → ZMod (F.order key.1))).map
        (fun r =>
          (F.encode key.1 (F.pedersenCommit key.1 key.2 (ofBits message) r), r.val.bits)) := by
  simp only [pedersenCommitProb, ProbComp.eval_bind, ProbComp.eval_pure]
  change (ProbComp.eval (F.sampleExp n key.1)).map
      (fun r => F.pedersenPublicOperations.commit key message r.bits) = _
  rw [PMF.map_comp]
  apply PMF.map_congr_on_support
  intro r hr
  have hlt := ProbComp.lt_of_mem_support_sampleModNat (F.prime_order key.1).pos hr
  have hval : (r : ZMod (F.order key.1)).val = r := ZMod.val_natCast_of_lt hlt
  simp only [pedersenPublicOperations, encodePedersenCommit_encode, ofBits_bits,
    Function.comp_apply, hval]

/-- Every randomized Boolean continuation changes by at most `1 / 2 ^ n` when the sampled
commitment is replaced with the existing ideal commitment law. -/
theorem advantage_bind_pedersenCommitProb_le (n : ℕ) (key : F.PedersenKey)
    (message : List Bool) (continuation : (List Bool × List Bool) → Game) :
    Game.advantage ((ProbComp.eval (F.pedersenCommitProb n key message)).bind continuation)
      ((F.pedersenScheme.commitDist key message).bind continuation) ≤ 1 / 2 ^ n := by
  rw [F.eval_pedersenCommitProb]
  simpa only [pedersenScheme, pedersenCommitPairLaw, PMF.bind_map, Function.comp_def] using
    F.advantage_bind_sampleExp_le n key.1
      (fun r => continuation
        (F.encode key.1 (F.pedersenCommit key.1 key.2 (ofBits message) r), r.val.bits))

/-- A sampled commitment and opening verify whenever the message is valid. -/
theorem pedersenVerify_of_mem_support_pedersenCommitProb (n : ℕ) (key : F.PedersenKey)
    {message : List Bool} {co : List Bool × List Bool}
    (hm : F.pedersenScheme.ValidMessage key message)
    (hco : co ∈ (ProbComp.eval (F.pedersenCommitProb n key message)).support) :
    F.pedersenScheme.verify key message co.1 co.2 = true := by
  rw [F.eval_pedersenCommitProb, PMF.support_map] at hco
  obtain ⟨r, _, rfl⟩ := hco
  apply F.pedersenScheme.verify_of_mem_support key message _ hm
  simp only [pedersenScheme, pedersenCommitPairLaw, PMF.support_map]
  exact ⟨r, by simp, rfl⟩

/-- Every supported opening has at most the bit length of the public group order. -/
theorem length_opening_pedersenCommitProb_le (n : ℕ) (key : F.PedersenKey)
    {message : List Bool} {co : List Bool × List Bool}
    (hco : co ∈ (ProbComp.eval (F.pedersenCommitProb n key message)).support) :
    co.2.length ≤ (encNat (F.order key.1)).length := by
  rw [F.eval_pedersenCommitProb, PMF.support_map] at hco
  obtain ⟨r, _, rfl⟩ := hco
  simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
    Nat.size_le_size (ZMod.val_lt r).le

/-! ### Bounded fair-coin Pedersen key generation -/

/-- Sample a bounded approximately uniform key exponent `α ← F.sampleExp n d` and return the
Pedersen commitment key `⟨d, (α : ZMod (F.order d)) • F.generator d⟩`. -/
@[expose] noncomputable def pedersenKeyGenProb (n : ℕ) (d : F.Desc) : ProbComp F.PedersenKey := do
  let α ← F.sampleExp n d
  return ⟨d, (α : ZMod (F.order d)) • F.generator d⟩

/-- `pedersenKeyGenProb` is uniformly strict PPT in `(n, d)` with output encoding
`F.pedersenScheme.encodeKey`. -/
theorem isPPTOn_pedersenKeyGenProb :
    IsPPTOn (encPair encUnary F.encDesc) F.pedersenScheme.encodeKey
      (fun p : ℕ × F.Desc => F.pedersenKeyGenProb p.1 p.2) := by
  have hn := ComputableInPolyTime.fst encUnary F.encDesc
  have hd := ComputableInPolyTime.snd encUnary F.encDesc
  have hs := F.isPPTOn_sampleExp hn hd
  have hg := F.computableInPolyTime_generator.tidy
  have hsmul := F.computableInPolyTime_smul.tidy
  have hpair : ComputableInPolyTime
      (fun q : (ℕ × F.Desc) × ℕ =>
        (q.1.2, F.smul (q.1.2, q.2, F.encode q.1.2 (F.generator q.1.2))))
      (encPair (encPair encUnary F.encDesc) encNat) (encPair F.encDesc encBits) := by
    fun_prop
  have hmk : ComputableInPolyTime
      (fun q : (ℕ × F.Desc) × ℕ =>
        (⟨q.1.2, (q.2 : ZMod (F.order q.1.2)) • F.generator q.1.2⟩ : F.PedersenKey))
      (encPair (encPair encUnary F.encDesc) encNat) F.pedersenScheme.encodeKey :=
    ComputableInPolyTime.of_enc_eq hpair fun q => by
      simp only [pedersenScheme_encodeKey, F.smul_encode]
  unfold pedersenKeyGenProb
  exact hs.bind_with hmk.isPPTOn

/-- The output law of `pedersenKeyGenProb n d` is the key map `α ↦ ⟨d, α • g⟩` applied to the
approximately uniform residue law `(ProbComp.eval (F.sampleExp n d)).map Nat.cast`. -/
theorem eval_pedersenKeyGenProb (n : ℕ) (d : F.Desc) :
    ProbComp.eval (F.pedersenKeyGenProb n d) =
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map
        (fun α => (⟨d, α • F.generator d⟩ : F.PedersenKey)) := by
  simp only [pedersenKeyGenProb, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp]
  rfl

/-- Every randomized Boolean continuation changes by at most `1 / 2 ^ n` when `pedersenKeyGenProb`
is replaced by an exact uniform exponent `α ← PMF.uniformOfFintype (ZMod (F.order d))`. -/
theorem advantage_bind_pedersenKeyGenProb_le (n : ℕ) (d : F.Desc)
    (continuation : F.PedersenKey → Game) :
    Game.advantage ((ProbComp.eval (F.pedersenKeyGenProb n d)).bind continuation)
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        continuation ⟨d, α • F.generator d⟩) ≤ 1 / 2 ^ n := by
  rw [F.eval_pedersenKeyGenProb]
  simpa only [PMF.bind_map, Function.comp_def] using
    F.advantage_bind_sampleExp_le n d (fun α => continuation ⟨d, α • F.generator d⟩)

/-- Draw `d ← setup n` and run `F.pedersenKeyGenProb n d` to sample a Pedersen key using
bounded fair-coin exponent sampling. -/
@[expose] noncomputable def pedersenKeyDistProb (setup : ℕ → PMF F.Desc) (n : ℕ) :
    PMF F.PedersenKey := do
  let d ← setup n
  ProbComp.eval (F.pedersenKeyGenProb n d)

/-- Replacing `pedersenKeyDistProb setup n` with the ideal key distribution
`pedersenKeyDist setup n` changes any Boolean game continuation by at most `1 / 2 ^ n`. -/
theorem advantage_bind_pedersenKeyDistProb_le (setup : ℕ → PMF F.Desc) (n : ℕ)
    (continuation : F.PedersenKey → Game) :
    Game.advantage ((F.pedersenKeyDistProb setup n).bind continuation)
      ((F.pedersenKeyDist setup n).bind continuation) ≤ 1 / 2 ^ n := by
  simp only [pedersenKeyDistProb, pedersenKeyDist, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  exact Game.advantage_bind_le_nnreal (setup n) _ _ fun d =>
    F.advantage_bind_pedersenKeyGenProb_le n d continuation

/-! ### Chosen-message hiding and binding for `pedersenCommitProb` and `pedersenKeyDistProb` -/

/-- Chosen-message hiding at a fixed Pedersen key `key` when the challenger samples the challenge
commitment using `F.pedersenCommitProb n key msg` instead of the ideal `commitDist`. -/
noncomputable def pedersenHidingProbForKey (key : F.PedersenKey)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let choice ← ProbComp.eval (adversary.choose n (F.pedersenScheme.encodeKey key))
  let msgs := choice.1
  let msg :=
    if bit && F.validPedersenMessageBool key.1 msgs.1 &&
        F.validPedersenMessageBool key.1 msgs.2 then msgs.2
    else msgs.1
  let co ← ProbComp.eval (F.pedersenCommitProb n key msg)
  ProbComp.eval (adversary.guess n choice.2 co.1)

private theorem advantage_pedersenHidingProbForKey_hidingForKey_le (key : F.PedersenKey)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    Game.advantage (F.pedersenHidingProbForKey key adversary bit n)
      (F.pedersenScheme.hidingForKey key adversary bit n) ≤ 1 / 2 ^ n := by
  have hmsg (msgs : List Bool × List Bool) :
      (if bit && F.validPedersenMessageBool key.1 msgs.1 &&
          F.validPedersenMessageBool key.1 msgs.2 then msgs.2 else msgs.1) =
        open Classical in
        if bit ∧ F.pedersenScheme.ValidMessage key msgs.1 ∧
            F.pedersenScheme.ValidMessage key msgs.2 then msgs.2 else msgs.1 := by
    have hcond :
        ((bit && F.validPedersenMessageBool key.1 msgs.1 &&
            F.validPedersenMessageBool key.1 msgs.2) = true) ↔
          (bit = true ∧ F.pedersenScheme.ValidMessage key msgs.1 ∧
            F.pedersenScheme.ValidMessage key msgs.2) := by
      simp only [Bool.and_eq_true, F.validPedersenMessageBool_eq_true_iff, pedersenScheme,
        and_assoc]
    classical
    exact if_ctx_congr hcond (fun _ => rfl) (fun _ => rfl)
  simp only [pedersenHidingProbForKey, CommitmentScheme.hidingForKey, PMF.monad_bind_eq_bind, hmsg]
  exact Game.advantage_bind_le_nnreal _ _ _ fun choice =>
    F.advantage_bind_pedersenCommitProb_le n key _
      (fun co => ProbComp.eval (adversary.guess n choice.2 co.1))

/-- For any non-identity commitment key `h ≠ 0`, any (even computationally unbounded)
`Encryption.WordAdversary` has distinguishing advantage at most `2 / 2 ^ n` between `bit = false`
and `bit = true` in `pedersenHidingProbForKey ⟨d, h⟩`. -/
theorem advantage_pedersenHidingProbForKey_le_of_ne_zero (d : F.Desc) {h : F.Carrier d}
    (hh : h ≠ 0) (adversary : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage (F.pedersenHidingProbForKey ⟨d, h⟩ adversary false n)
      (F.pedersenHidingProbForKey ⟨d, h⟩ adversary true n) ≤ 2 / 2 ^ n := by
  have hmid : Game.advantage (F.pedersenScheme.hidingForKey ⟨d, h⟩ adversary false n)
      (F.pedersenScheme.hidingForKey ⟨d, h⟩ adversary true n) = 0 := by
    rw [F.pedersenHidingForKey_eq_of_ne_zero d hh adversary false true n, Game.advantage_self]
  calc Game.advantage (F.pedersenHidingProbForKey ⟨d, h⟩ adversary false n)
        (F.pedersenHidingProbForKey ⟨d, h⟩ adversary true n)
      ≤ 1 / 2 ^ n +
          Game.advantage (F.pedersenScheme.hidingForKey ⟨d, h⟩ adversary false n)
            (F.pedersenScheme.hidingForKey ⟨d, h⟩ adversary true n) +
          1 / 2 ^ n :=
        Game.advantage_four_hop_le
          (F.advantage_pedersenHidingProbForKey_hidingForKey_le ⟨d, h⟩ adversary false n)
          (F.advantage_pedersenHidingProbForKey_hidingForKey_le ⟨d, h⟩ adversary true n)
    _ = 2 / 2 ^ n := by rw [hmid]; ring

/-- Chosen-message hiding game where both key generation (`pedersenKeyDistProb setup n`) and
challenge commitment sampling (`pedersenCommitProb`) use bounded fair-coin exponent sampling. -/
noncomputable def pedersenHidingProbGame (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let key ← F.pedersenKeyDistProb setup n
  F.pedersenHidingProbForKey key adversary bit n

private theorem advantage_pedersenHidingProbGame_hidingGame_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    Game.advantage (F.pedersenHidingProbGame setup adversary bit n)
      (F.pedersenScheme.hidingGame (F.pedersenKeyDist setup) adversary bit n) ≤ 2 / 2 ^ n := by
  let Gmid : Game :=
    (F.pedersenKeyDist setup n).bind fun key => F.pedersenHidingProbForKey key adversary bit n
  have hkey : Game.advantage (F.pedersenHidingProbGame setup adversary bit n) Gmid ≤ 1 / 2 ^ n :=
    F.advantage_bind_pedersenKeyDistProb_le setup n
      (fun key => F.pedersenHidingProbForKey key adversary bit n)
  have hcom : Game.advantage Gmid
      (F.pedersenScheme.hidingGame (F.pedersenKeyDist setup) adversary bit n) ≤ 1 / 2 ^ n :=
    Game.advantage_bind_le_nnreal _ _ _ fun key =>
      F.advantage_pedersenHidingProbForKey_hidingForKey_le key adversary bit n
  calc Game.advantage (F.pedersenHidingProbGame setup adversary bit n)
        (F.pedersenScheme.hidingGame (F.pedersenKeyDist setup) adversary bit n)
      ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n :=
        (Game.advantage_triangle _ Gmid _).trans (add_le_add hkey hcom)
    _ = 2 / 2 ^ n := by ring

/-- **Unconditional hiding bound for `pedersenHidingProbGame`**: when every supported group at
parameter `n` has order at least `m > 0`, any (even computationally unbounded)
`Encryption.WordAdversary` has distinguishing advantage at most `1 / m + 4 / 2 ^ n` in
`pedersenHidingProbGame`. -/
theorem advantage_pedersenHidingProbGame_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage (F.pedersenHidingProbGame setup adversary false n)
      (F.pedersenHidingProbGame setup adversary true n) ≤ 1 / m + 4 / 2 ^ n := by
  have hmid := F.advantage_pedersenHidingGame_le setup adversary n m hm0 hm
  calc Game.advantage (F.pedersenHidingProbGame setup adversary false n)
        (F.pedersenHidingProbGame setup adversary true n)
      ≤ 2 / 2 ^ n +
          Game.advantage (F.pedersenScheme.hidingGame (F.pedersenKeyDist setup) adversary false n)
            (F.pedersenScheme.hidingGame (F.pedersenKeyDist setup) adversary true n) +
          2 / 2 ^ n :=
        Game.advantage_four_hop_le
          (F.advantage_pedersenHidingProbGame_hidingGame_le setup adversary false n)
          (F.advantage_pedersenHidingProbGame_hidingGame_le setup adversary true n)
    _ ≤ 2 / 2 ^ n + 1 / m + 2 / 2 ^ n :=
        add_le_add_left (add_le_add_right hmid _) _
    _ = 1 / m + 4 / 2 ^ n := by ring

/-- **Asymptotic unconditional hiding for `pedersenHidingProbGame`**: when every supported
group at parameter `n` has order at least `m n > 0` and `1 / m n` is negligible, every (even
computationally unbounded) `Encryption.WordAdversary` has negligible advantage in
`pedersenHidingProbGame`. -/
theorem negligible_advantage_pedersenHidingProbGame (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    Negligible fun n =>
      Game.advantage (F.pedersenHidingProbGame setup adversary false n)
        (F.pedersenHidingProbGame setup adversary true n) := by
  have h4 : Negligible fun n => (4 : ℝ≥0) / 2 ^ n := by
    simpa only [mul_one_div] using
      (negligible_one_div_two_pow.const_mul (4 : ℝ≥0))
  refine negligible_of_le (hinv.add h4) fun n => ?_
  exact F.advantage_pedersenHidingProbGame_le setup adversary n (m n) (hm0 n) (hm n)

/-- Executable `ProbComp Bool` hiding experiment at group description `d`: sample a key with
`pedersenKeyGenProb n d`, run `adversary.choose` on the encoded key, check message validity with
`validPedersenMessageBool`, sample the challenge commitment with `pedersenCommitProb`, and run
`adversary.guess`. -/
noncomputable def pedersenHidingProbExperiment (adversary : Encryption.WordAdversary)
    (bit : Bool) (n : ℕ) (d : F.Desc) : ProbComp Bool := do
  let key ← F.pedersenKeyGenProb n d
  let choice ← adversary.choose n (F.pedersenScheme.encodeKey key)
  let msgs := choice.1
  let msg :=
    if bit && F.validPedersenMessageBool key.1 msgs.1 &&
        F.validPedersenMessageBool key.1 msgs.2 then msgs.2
    else msgs.1
  let co ← F.pedersenCommitProb n key msg
  adversary.guess n choice.2 co.1

/-- Evaluating `pedersenHidingProbExperiment` at a fixed group description `d` runs
`pedersenKeyGenProb n d` followed by `pedersenHidingProbForKey`. -/
theorem eval_pedersenHidingProbExperiment (adversary : Encryption.WordAdversary)
    (bit : Bool) (n : ℕ) (d : F.Desc) :
    ProbComp.eval (F.pedersenHidingProbExperiment adversary bit n d) =
      (ProbComp.eval (F.pedersenKeyGenProb n d)).bind fun key =>
        F.pedersenHidingProbForKey key adversary bit n := by
  simp only [pedersenHidingProbExperiment, pedersenHidingProbForKey, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]

/-- Averaging `pedersenHidingProbExperiment` over `d ← setup n` yields
`pedersenHidingProbGame`. -/
theorem bind_eval_pedersenHidingProbExperiment (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    ((setup n).bind fun d => ProbComp.eval (F.pedersenHidingProbExperiment adversary bit n d)) =
      F.pedersenHidingProbGame setup adversary bit n := by
  simp only [eval_pedersenHidingProbExperiment, pedersenHidingProbGame, pedersenKeyDistProb,
    PMF.monad_bind_eq_bind, PMF.bind_bind]

/-- `pedersenHidingProbExperiment` is uniformly strict PPT in `(n, d)` whenever `adversary` is a
uniform strict PPT `Encryption.WordAdversary`. -/
theorem isPPTOn_pedersenHidingProbExperiment {adversary : Encryption.WordAdversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary F.encDesc) encBool
      (fun p : ℕ × F.Desc => F.pedersenHidingProbExperiment adversary bit p.1 p.2) := by
  let E0 := encPair encUnary F.encDesc
  let E1 := encPair E0 F.pedersenScheme.encodeKey
  let E2 := encPair E1 (Encryption.encChoiceOut encBits)
  let E3 := encPair E2 (encPair encBits encBits)
  have hkey_pair : ComputableInPolyTime
      (fun k : F.PedersenKey => (k.1, F.encode k.1 k.2))
      F.pedersenScheme.encodeKey (encPair F.encDesc encBits) := .of_eq fun _ => rfl
  have hchoose : IsPPTOn E1 (Encryption.encChoiceOut encBits)
      (fun p : (ℕ × F.Desc) × F.PedersenKey =>
        adversary.choose p.1.1 (F.pedersenScheme.encodeKey p.2)) := by
    have hn : ComputableInPolyTime (fun p : (ℕ × F.Desc) × F.PedersenKey => p.1.1) E1 encUnary := by
      fun_prop
    have hk : ComputableInPolyTime (fun p : (ℕ × F.Desc) × F.PedersenKey => p.2) E1
        F.pedersenScheme.encodeKey := by
      fun_prop
    have henc : ComputableInPolyTime
        (fun k : F.PedersenKey => F.pedersenScheme.encodeKey k)
        F.pedersenScheme.encodeKey encBits := .of_eq fun _ => rfl
    exact hA.choose.preprocess
      (parameter := fun p : (ℕ × F.Desc) × F.PedersenKey => p.1.1)
      (auxiliary := fun p : (ℕ × F.Desc) × F.PedersenKey => F.pedersenScheme.encodeKey p.2)
      hn.tidy (henc.comp hk).tidy
  have hmsg : ComputableInPolyTime
      (fun q : ((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool) =>
        if bit && F.validPedersenMessageBool q.1.2.1 q.2.1.1 &&
            F.validPedersenMessageBool q.1.2.1 q.2.1.2 then q.2.1.2
        else q.2.1.1)
      E2 encBits := by
    have hk : ComputableInPolyTime
        (fun q : ((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool) => q.1.2)
        E2 F.pedersenScheme.encodeKey := by fun_prop
    have hd : ComputableInPolyTime
        (fun q : ((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool) => q.1.2.1)
        E2 F.encDesc := (hkey_pair.comp hk).fst'
    fun_prop
  have hcommit : IsPPTOn E2 (encPair encBits encBits)
      (fun q : ((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool) =>
        F.pedersenCommitProb q.1.1.1 q.1.2
          (if bit && F.validPedersenMessageBool q.1.2.1 q.2.1.1 &&
              F.validPedersenMessageBool q.1.2.1 q.2.1.2 then q.2.1.2
          else q.2.1.1)) := by
    refine F.isPPTOn_pedersenCommitProb.preprocess
      (prepare := fun q : ((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool) =>
        (q.1.1.1, q.1.2,
          if bit && F.validPedersenMessageBool q.1.2.1 q.2.1.1 &&
              F.validPedersenMessageBool q.1.2.1 q.2.1.2 then q.2.1.2
          else q.2.1.1)) ?_
    have hn : ComputableInPolyTime
        (fun q : ((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool) => q.1.1.1)
        E2 encUnary := by fun_prop
    have hk : ComputableInPolyTime
        (fun q : ((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool) => q.1.2)
        E2 F.pedersenScheme.encodeKey := by fun_prop
    exact hn.prod (hk.prod hmsg)
  have hguess : IsPPTOn E3 encBool
      (fun r : (((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool)) ×
          (List Bool × List Bool) =>
        adversary.guess r.1.1.1.1 r.1.2.2 r.2.1) :=
    hA.guess.preprocess
      (prepare := fun r : (((ℕ × F.Desc) × F.PedersenKey) × Encryption.ChoiceOut (List Bool)) ×
          (List Bool × List Bool) =>
        (r.1.1.1.1, r.1.2.2, r.2.1))
      (by fun_prop)
  unfold pedersenHidingProbExperiment
  exact F.isPPTOn_pedersenKeyGenProb.bind_with
    (hchoose.bind_with (hcommit.bind_with hguess))

private theorem advantage_pedersenHidingGame_pedersenKeyDistProb_hidingGame_le
    (setup : ℕ → PMF F.Desc) (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    Game.advantage (F.pedersenScheme.hidingGame (F.pedersenKeyDistProb setup) adversary bit n)
      (F.pedersenScheme.hidingGame (F.pedersenKeyDist setup) adversary bit n) ≤ 1 / 2 ^ n :=
  F.advantage_bind_pedersenKeyDistProb_le setup n
    (fun key => F.pedersenScheme.hidingForKey key adversary bit n)

/-- **Unconditional hiding bound for `pedersenScheme` under `pedersenKeyDistProb`**: when every
supported group at parameter `n` has order at least `m > 0`, any (even computationally unbounded)
`Encryption.WordAdversary` has distinguishing advantage at most `1 / m + 2 / 2 ^ n` in
`F.pedersenScheme.hidingGame (F.pedersenKeyDistProb setup)`. -/
theorem advantage_pedersenHidingGame_pedersenKeyDistProb_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage (F.pedersenScheme.hidingGame (F.pedersenKeyDistProb setup) adversary false n)
      (F.pedersenScheme.hidingGame (F.pedersenKeyDistProb setup) adversary true n) ≤
      1 / m + 2 / 2 ^ n := by
  have hmid := F.advantage_pedersenHidingGame_le setup adversary n m hm0 hm
  calc Game.advantage (F.pedersenScheme.hidingGame (F.pedersenKeyDistProb setup) adversary false n)
        (F.pedersenScheme.hidingGame (F.pedersenKeyDistProb setup) adversary true n)
      ≤ 1 / 2 ^ n +
          Game.advantage (F.pedersenScheme.hidingGame (F.pedersenKeyDist setup) adversary false n)
            (F.pedersenScheme.hidingGame (F.pedersenKeyDist setup) adversary true n) +
          1 / 2 ^ n :=
        Game.advantage_four_hop_le
          (F.advantage_pedersenHidingGame_pedersenKeyDistProb_hidingGame_le setup adversary false n)
          (F.advantage_pedersenHidingGame_pedersenKeyDistProb_hidingGame_le setup adversary true n)
    _ ≤ 1 / 2 ^ n + 1 / m + 1 / 2 ^ n :=
        add_le_add_left (add_le_add_right hmid _) _
    _ = 1 / m + 2 / 2 ^ n := by ring

/-- **Asymptotic unconditional hiding of `pedersenScheme` under `pedersenKeyDistProb`**. -/
theorem negligible_advantage_pedersenHidingGame_pedersenKeyDistProb (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    Negligible fun n =>
      Game.advantage (F.pedersenScheme.hidingGame (F.pedersenKeyDistProb setup) adversary false n)
        (F.pedersenScheme.hidingGame (F.pedersenKeyDistProb setup) adversary true n) := by
  negligible using fun n =>
    F.advantage_pedersenHidingGame_pedersenKeyDistProb_le setup adversary n (m n) (hm0 n) (hm n)

/-- **Statistical hiding (`CommitmentScheme.StatisticalHiding`) of `pedersenScheme` under
`pedersenKeyDistProb`**. -/
theorem pedersenScheme_statisticalHiding_pedersenKeyDistProb (setup : ℕ → PMF F.Desc)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    F.pedersenScheme.StatisticalHiding (F.pedersenKeyDistProb setup) :=
  fun adversary _ =>
    F.negligible_advantage_pedersenHidingGame_pedersenKeyDistProb setup adversary hm0 hm hinv

/-- **Computational hiding (`CommitmentScheme.ComputationalHiding`) of `pedersenScheme` under
`pedersenKeyDistProb`**. -/
theorem pedersenScheme_computationalHiding_pedersenKeyDistProb (setup : ℕ → PMF F.Desc)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    F.pedersenScheme.ComputationalHiding (F.pedersenKeyDistProb setup) :=
  (F.pedersenScheme_statisticalHiding_pedersenKeyDistProb setup hm0 hm hinv).computationalHiding

private theorem advantage_pedersenBindingGame_pedersenKeyDistProb_bindingGame_le
    (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → List Bool →
      ProbComp (List Bool × (List Bool × List Bool) × (List Bool × List Bool)))
    (n : ℕ) :
    Game.advantage (F.pedersenScheme.bindingGame (F.pedersenKeyDistProb setup) adversary n)
      (F.pedersenScheme.bindingGame (F.pedersenKeyDist setup) adversary n) ≤ 1 / 2 ^ n :=
  F.advantage_bind_pedersenKeyDistProb_le setup n fun key =>
    (ProbComp.eval (adversary n (F.pedersenScheme.encodeKey key))).bind fun out =>
      pure (F.pedersenScheme.isBindingCollision key out)

/-- **Binding-to-discrete-logarithm bound under `pedersenKeyDistProb`**: at parameter `n`, the
binding success probability under `pedersenKeyDistProb setup` is at most the discrete-logarithm
success probability of `pedersenToDLAdversary adversary` plus `1 / 2 ^ n`. -/
theorem succProbability_pedersenBindingGame_pedersenKeyDistProb_le (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → List Bool →
      ProbComp (List Bool × (List Bool × List Bool) × (List Bool × List Bool)))
    (n : ℕ) :
    Game.succProbability
      (F.pedersenScheme.bindingGame (F.pedersenKeyDistProb setup) adversary n) ≤
      Game.succProbability (F.discreteLogGame setup (F.pedersenToDLAdversary adversary) n) +
        1 / 2 ^ n :=
  (Game.succProbability_le_add_of_advantage_le
    (F.advantage_pedersenBindingGame_pedersenKeyDistProb_bindingGame_le setup adversary n)).trans
    (add_le_add (F.succProbability_pedersenBindingGame_le_discreteLogGame setup adversary n) le_rfl)

/-- **Computational binding of Pedersen commitments under `pedersenKeyDistProb` and the
discrete-logarithm assumption**. -/
theorem DiscreteLog.pedersenBinding_pedersenKeyDistProb {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    (adversary : ℕ → List Bool →
      ProbComp (List Bool × (List Bool × List Bool) × (List Bool × List Bool)))
    (hA : IsPPTOn (encPair encUnary encBits)
      (encPair encBits (encPair (encPair encBits encBits) (encPair encBits encBits)))
      (fun input => adversary input.1 input.2)) :
    Negligible fun n =>
      Game.succProbability
        (F.pedersenScheme.bindingGame (F.pedersenKeyDistProb setup) adversary n) := by
  have hdl := hDL (F.pedersenToDLAdversary adversary) (F.isPPTOn_pedersenToDLAdversary hA)
  negligible using fun n =>
    F.succProbability_pedersenBindingGame_pedersenKeyDistProb_le setup adversary n

/-- **Computational binding (`CommitmentScheme.Binding`) of `pedersenScheme` under
`pedersenKeyDistProb` and the discrete-logarithm assumption**. -/
theorem DiscreteLog.pedersenScheme_binding_pedersenKeyDistProb {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup) :
    F.pedersenScheme.Binding (F.pedersenKeyDistProb setup) :=
  fun adversary hA => hDL.pedersenBinding_pedersenKeyDistProb adversary hA

end Cslib.Crypto.PrimeOrderGroupFamily
