/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Crypto.Computational.Commitment.Basic
public import CslibFrontier.Crypto.Computational.OneWayToPRG
public import CslibFrontier.Crypto.Computational.Stretch
public import CslibFrontier.Crypto.Computational.Hybrid.Sequence
public import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Tactic.PMFSwap

/-!
# Naor's bit commitment scheme from pseudorandom generators

Naor's statistically binding, computationally hiding bit commitment scheme [Naor1991] commits to a
bit `b : Bool` under a receiver string `r : List Bool` and a uniform seed `seed : List Bool` of
length `n` using a pseudorandom generator `generator`:
`naorCommit generator r b seed` outputs `generator seed` when `b = false`, and
`BitString.listXor (generator seed).length [generator seed, r]` when `b = true`.

The general public-parameter interface is in `Commitment/Basic`.

## Main definitions

* `Cslib.Crypto.naorCommit`: commit to a single bit using a generator, receiver string, and seed.
* `Cslib.Crypto.naorCommitEnsemble`: the commitment distribution for a family of receiver strings
  and bits.
* `Cslib.Crypto.CommitmentReceiver`, `Cslib.Crypto.CommitmentReceiver.IsPPT`: a two-stage
  randomized stateful PPT receiver that outputs `((r, (b₀, b₁)), state)` in the first stage and
  distinguishes `(state, c)` in the second stage.
* `Cslib.Crypto.commitmentHidingGame`, `Cslib.Crypto.StatefulHiding`: the two-stage commitment
  hiding game and computational hiding against randomized stateful PPT receivers.
* `Cslib.Crypto.naorReceiverDistinguisher`: PRG distinguisher induced by a stateful commitment
  receiver.
* `Cslib.Crypto.NaorBinding`: statistical binding at seed length `n` for receiver string `r`,
  requiring that no two seeds of length `n` open to `false` and `true` with the same commitment.
* `Cslib.Crypto.naorBindingProb`, `Cslib.Crypto.naorBindingError`: the probability over a uniform
  receiver string `r` of length `length n` that `NaorBinding generator n r` fails.
* `Cslib.Crypto.encBitOpening`: the encoding of a bit-commitment opening `(b, seed)`.
* `Cslib.Crypto.BitCommitmentScheme`: a two-message statistically binding, computationally hiding
  bit commitment scheme.

## Main results

* `Cslib.Crypto.OneWay.exists_pseudorandomGenerator_three_mul`: any one-way function yields a
  pseudorandom generator with expansion `fun n => 3 * n + 1`.
* `Cslib.Crypto.uniformList_map_naorCommit_id`: replacing the generator output with a uniform
  word of length `m` makes the commitment distribution exactly `BitString.uniformList m` for
  every receiver string `r` and committed bit `b`.
* `Cslib.Crypto.PseudorandomGenerator.naorCommit_indistinguishable_uniform`,
  `Cslib.Crypto.PseudorandomGenerator.naorCommit_hiding`: computational hiding of Naor commitments
  for deterministic polynomial-time families of receiver strings `r : ℕ → List Bool` and bit
  families `b₀ b₁ : ℕ → Bool`.
* `Cslib.Crypto.advantage_commitmentHidingGame_naorCommit_le`,
  `Cslib.Crypto.PseudorandomGenerator.naorStatefulHiding`: computational hiding of Naor commitments
  against randomized stateful PPT receivers, and `Cslib.Crypto.StatefulHiding.computational_hiding`
  connecting stateful-receiver hiding to the deterministic-family interface.
* `Cslib.Crypto.naorBindingProb_le`, `Cslib.Crypto.naorBindingProb_le_of_three_mul_add_one`,
  `Cslib.Crypto.negligible_naorBindingError`: statistical binding when `3 * n ≤ length n`.
* `Cslib.Crypto.PseudorandomGenerator.naorBitCommitment`,
  `Cslib.Crypto.OneWay.exists_bitCommitmentScheme`: packaged Naor bit commitment scheme from a
  pseudorandom generator or one-way function.

## References

* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001],
  Section 4.4.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Stretching a one-way function to `3 * n + 1` bits -/

/-- Any one-way function yields a pseudorandom generator stretching `n` bits to `3 * n + 1` bits. -/
theorem OneWay.exists_pseudorandomGenerator_three_mul {f : List Bool → List Bool}
    (hf : OneWay f) :
    ∃ generator : List Bool → List Bool,
      PseudorandomGenerator generator (fun n => 3 * n + 1) := by
  obtain ⟨g, hg⟩ := hf.exists_pseudorandomGenerator
  exact ⟨_, hg.amplify (fun n => 3 * n + 1)
    (((ComputableInPolyTime.const 3).unary_mul' .id').unary_add' (.const 1)) (fun n => by lia)⟩

/-! ### Naor bit commitment -/

/-- Naor's bit commitment: evaluate `generator seed`, and XOR with `r` when `b = true`. -/
def naorCommit (generator : List Bool → List Bool) (r : List Bool) (b : Bool)
    (seed : List Bool) : List Bool :=
  let y := generator seed
  if b then BitString.listXor y.length [y, r] else y

@[simp] theorem naorCommit_false (generator : List Bool → List Bool) (r seed : List Bool) :
    naorCommit generator r false seed = generator seed := rfl

@[simp] theorem naorCommit_true (generator : List Bool → List Bool) (r seed : List Bool) :
    naorCommit generator r true seed =
      BitString.listXor (generator seed).length [generator seed, r] := rfl

/-- `naorCommit` factors through the identity generator `naorCommit id r b`. -/
theorem naorCommit_eq_comp_id (generator : List Bool → List Bool) (r : List Bool) (b : Bool)
    (seed : List Bool) :
    naorCommit generator r b seed = naorCommit id r b (generator seed) := rfl

@[simp] theorem length_naorCommit (generator : List Bool → List Bool) (r : List Bool)
    (b : Bool) (seed : List Bool) :
    (naorCommit generator r b seed).length = (generator seed).length := by
  cases b <;> simp only [naorCommit, Bool.false_eq_true, ↓reduceIte, BitString.length_listXor]

/-- Naor commitment is computable in plain polynomial time when its inputs are. -/
@[fun_prop]
theorem computableInPolyTime_naorCommit {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {r : α → List Bool} {b : α → Bool} {seed : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hr : ComputableInPolyTime r input encBits)
    (hb : ComputableInPolyTime b input encBool)
    (hseed : ComputableInPolyTime seed input encBits) :
    ComputableInPolyTime (fun a => naorCommit generator (r a) (b a) (seed a))
      input encBits :=
  let hy := hg.comp' hseed
  hb.ite (ComputableInPolyTime.bitsXorWithInput hy.length_bits_comp
    (hy.cons' (hr.cons' (.const [])))) hy

/-! ### Algebraic and distributional laws -/

/-- Applying `naorCommit id r b` to a uniform `m`-bit word yields a uniform `m`-bit word for
every receiver string `r` and bit `b`. -/
@[simp] theorem uniformList_map_naorCommit_id (m : ℕ) (r : List Bool) (b : Bool) :
    (BitString.uniformList m).map (naorCommit id r b) = BitString.uniformList m := by
  cases b
  · exact PMF.map_id _
  · refine (Probability.PMF.map_congr_on_support _ _
      (fun y => BitString.listXor m [y, r]) ?_).trans (BitString.uniformList_map_listXor m r)
    intro y hy
    simp only [naorCommit_true, id_eq, BitString.length_of_mem_support_uniformList hy]

/-! ### Computational hiding -/

/-- The commitment ensemble on a uniform `n`-bit seed for receiver string `r n` and bit `b n`. -/
noncomputable def naorCommitEnsemble (generator : List Bool → List Bool)
    (r : ℕ → List Bool) (b : ℕ → Bool) (n : ℕ) : PMF (List Bool) :=
  (BitString.uniformList n).map (naorCommit generator (r n) (b n))

theorem naorCommitEnsemble_eq_map (generator : List Bool → List Bool)
    (r : ℕ → List Bool) (b : ℕ → Bool) (n : ℕ) :
    naorCommitEnsemble generator r b n =
      (generatorEnsemble generator n).map (naorCommit id (r n) (b n)) := by
  simp only [naorCommitEnsemble, generatorEnsemble, PMF.map_comp]
  rfl

/-- For any polynomial-time receiver family `r` and bit family `b`, the Naor commitment ensemble
is computationally indistinguishable from uniform words of length `length n`. -/
theorem PseudorandomGenerator.naorCommit_indistinguishable_uniform
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    {r : ℕ → List Bool} {b : ℕ → Bool}
    (hr : ComputableInPolyTime r encUnary encBits)
    (hb : ComputableInPolyTime b encUnary encBool) :
    ComputationallyIndistinguishable (naorCommitEnsemble generator r b)
      (fun n => BitString.uniformList (length n)) := by
  have h1 := ComputableInPolyTime.fst encUnary encBits
  have hind := hG.indistinguishable.map (f := fun n y => naorCommit id (r n) (b n) y)
    (computableInPolyTime_naorCommit .id' (hr.comp' h1) (hb.comp' h1)
      (ComputableInPolyTime.snd encUnary encBits))
  simpa only [← naorCommitEnsemble_eq_map, uniformList_map_naorCommit_id] using hind

/-- **Computational hiding of Naor bit commitment (deterministic-family formulation).**
Commitments to any two deterministic polynomial-time bit families `b₀` and `b₁` under any
deterministic polynomial-time receiver string family `r : ℕ → List Bool` are computationally
indistinguishable against uniform strict PPT distinguishers. See
`PseudorandomGenerator.naorStatefulHiding` below for hiding against a randomized stateful PPT
receiver. -/
theorem PseudorandomGenerator.naorCommit_hiding
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    {r : ℕ → List Bool} {b₀ b₁ : ℕ → Bool}
    (hr : ComputableInPolyTime r encUnary encBits)
    (hb₀ : ComputableInPolyTime b₀ encUnary encBool)
    (hb₁ : ComputableInPolyTime b₁ encUnary encBool) :
    ComputationallyIndistinguishable
      (naorCommitEnsemble generator r b₀)
      (naorCommitEnsemble generator r b₁) :=
  (hG.naorCommit_indistinguishable_uniform hr hb₀).trans
    (hG.naorCommit_indistinguishable_uniform hr hb₁).symm

/-! ### Stateful-receiver commitment hiding -/

/-- A two-stage randomized stateful receiver for a bit commitment scheme [Naor1991, Goldreich2001].
In the first stage, `choose n aux` receives the unary security parameter `n` and auxiliary input
`aux`, and outputs a receiver challenge string `r`, two challenge bits `(b₀, b₁)`, and an internal
`state` passed to the second stage. In the second stage, `guess n state c` receives the security
parameter `n`, the saved `state`, and the commitment `c`, and outputs a distinguishing bit. -/
structure CommitmentReceiver where
  /-- First stage: output `((r, (b₀, b₁)), state)`. -/
  choose : ℕ → List Bool → ProbComp ((List Bool × Bool × Bool) × List Bool)
  /-- Second stage: distinguish the commitment `c` using the saved `state`. -/
  guess : ℕ → List Bool → List Bool → ProbComp Bool

/-- A commitment receiver is strict PPT if both stages run in polynomial time in their full encoded
inputs (charging for the auxiliary input `aux` in `choose` and for the saved `state` and commitment
`c` in `guess`). -/
structure CommitmentReceiver.IsPPT (receiver : CommitmentReceiver) : Prop where
  /-- The first stage is a strict PPT family from `(n, aux)` to `((r, (b₀, b₁)), state)`. -/
  choose :
    Probability.IsPPT (encPair (encPair encBits (encPair encBool encBool)) encBits) receiver.choose
  /-- The second stage is strict PPT on `(n, state, c)`. -/
  guess :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
      (fun ⟨n, state, c⟩ => receiver.guess n state c)

/-- The two-stage commitment-hiding experiment against a stateful receiver `receiver` with
auxiliary input `aux` and hidden bit selector `bit : Bool` at security parameter `n`.
The receiver outputs `((r, (b₀, b₁)), state) ← receiver.choose n aux`, the challenger samples a
uniform `n`-bit seed `seed ← BitString.sampleList n` and commits to `b₁` (when `bit = true`) or
`b₀` (when `bit = false`) under `r`, and `receiver.guess n state c` outputs a guess bit. -/
noncomputable def commitmentHidingGame (commit : List Bool → Bool → List Bool → List Bool)
    (receiver : CommitmentReceiver) (aux : List Bool) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let choice ← receiver.choose n aux
  let seed ← BitString.sampleList n
  let ((r, b₀, b₁), state) := choice
  receiver.guess n state
    (commit r (if bit then b₁ else b₀) seed)

/-- Opening `(b, seed)` of a bit commitment: the committed bit `b`, then the commitment seed as a
bit word. The bit is framed. A committer takes it after the receiver string `r`, as
`encPair encBits encBitOpening`, and a verifier after `(1ⁿ, r, c)`. -/
abbrev encBitOpening : Bool × List Bool ↪ List Bool :=
  encPair encBool encBits

/-- The commitment-hiding experiment runs in strict PPT on `(n, aux, bit)` whenever `commit` is
computable in plain polynomial time and `receiver` is strict PPT. -/
theorem isPPTOn_commitmentHidingGame {commit : List Bool → Bool → List Bool → List Bool}
    {receiver : CommitmentReceiver}
    (hcommit : ComputableInPolyTime
      (fun ⟨r, b, seed⟩ => commit r b seed)
      (encPair encBits encBitOpening) encBits)
    (hR : receiver.IsPPT) :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBool
      (fun ⟨n, aux, bit⟩ => commitmentHidingGame commit receiver aux bit n) := by
  let E0 := encPair encUnary (encPair encBits encBool)
  let EChoice := encPair (encPair encBits (encPair encBool encBool)) encBits
  let E1 := encPair E0 EChoice
  let hn0 := ComputableInPolyTime.fst encUnary (encPair encBits encBool)
  let hrest0 := ComputableInPolyTime.snd encUnary (encPair encBits encBool)
  let hp2 := ComputableInPolyTime.fst E1 encBits
  let h0_2 := hp2.fst'
  let hchoice2 := hp2.snd'
  let hseed2 := ComputableInPolyTime.snd E1 encBits
  have harg := h0_2.fst'.prod (hchoice2.snd'.prod
    (hcommit.comp' (hchoice2.fst'.fst'.prod
      ((h0_2.snd'.snd'.ite hchoice2.fst'.snd'.snd' hchoice2.fst'.snd'.fst').prod hseed2))))
  exact (IsPPTOn.preprocess hR.choose (hn0.prod hrest0.fst')).bind_with
    ((hn0.comp' (ComputableInPolyTime.fst E0 EChoice)).sampleList.bind_with
      (IsPPTOn.preprocess hR.guess harg))

/-- For any fixed challenge selector `bit`, the commitment-hiding experiment is a strict PPT
indexed family on `(n, aux)`. -/
theorem isPPT_commitmentHidingGame {commit : List Bool → Bool → List Bool → List Bool}
    {receiver : CommitmentReceiver}
    (hcommit : ComputableInPolyTime
      (fun ⟨r, b, seed⟩ => commit r b seed)
      (encPair encBits encBitOpening) encBits)
    (hR : receiver.IsPPT) (bit : Bool) :
    IsPPT encBool (fun n aux => commitmentHidingGame commit receiver aux bit n) :=
  (isPPTOn_commitmentHidingGame hcommit hR).preprocess
    ((ComputableInPolyTime.fst encUnary encBits).prod
      ((ComputableInPolyTime.snd encUnary encBits).prod (.const bit)))

/-- For any polynomial-time auxiliary family `aux`, the commitment-hiding experiment is strict PPT
in the unary security parameter `n`. -/
theorem isPPTOn_commitmentHidingGame_aux {commit : List Bool → Bool → List Bool → List Bool}
    {receiver : CommitmentReceiver} {aux : ℕ → List Bool}
    (hcommit : ComputableInPolyTime
      (fun ⟨r, b, seed⟩ => commit r b seed)
      (encPair encBits encBitOpening) encBits)
    (hR : receiver.IsPPT)
    (haux : ComputableInPolyTime aux encUnary encBits) (bit : Bool) :
    IsPPTOn encUnary encBool (fun n => commitmentHidingGame commit receiver (aux n) bit n) :=
  IsPPTOn.preprocess (isPPT_commitmentHidingGame hcommit hR bit)
    (ComputableInPolyTime.id'.prod haux)

/-- Computational hiding against a randomized stateful PPT receiver: for every polynomial-time
auxiliary family `aux : ℕ → List Bool`, no strict PPT `CommitmentReceiver` can distinguish
commitments to its first chosen bit (`bit = false`) from commitments to its second chosen bit
(`bit = true`) with non-negligible advantage. -/
def StatefulHiding (commit : List Bool → Bool → List Bool → List Bool) : Prop :=
  ∀ (aux : ℕ → List Bool),
    ComputableInPolyTime aux encUnary encBits →
    Game.Indistinguishable
      (fun receiver n => ProbComp.eval (commitmentHidingGame commit receiver (aux n) false n))
      (fun receiver n => ProbComp.eval (commitmentHidingGame commit receiver (aux n) true n))
      CommitmentReceiver.IsPPT

/-- Specialization of `StatefulHiding` to the empty auxiliary string `[]`. -/
theorem StatefulHiding.empty {commit : List Bool → Bool → List Bool → List Bool}
    (h : StatefulHiding commit) :
    Game.Indistinguishable
      (fun receiver n => ProbComp.eval (commitmentHidingGame commit receiver [] false n))
      (fun receiver n => ProbComp.eval (commitmentHidingGame commit receiver [] true n))
      CommitmentReceiver.IsPPT :=
  h (fun _ => []) (.const [])

/-- Package deterministic families `(r, b₀, b₁)` and a distinguisher `D` as a stateless
`CommitmentReceiver`. -/
def CommitmentReceiver.ofDeterministic (r : ℕ → List Bool) (b₀ b₁ : ℕ → Bool)
    (D : Distinguisher) : CommitmentReceiver where
  choose n _ := pure ((r n, (b₀ n, b₁ n)), [])
  guess n _ c := D n c

/-- `CommitmentReceiver.ofDeterministic r b₀ b₁ D` is strict PPT whenever `r`, `b₀`, `b₁` are
computable in plain polynomial time and `D` is a strict PPT distinguisher. -/
theorem CommitmentReceiver.isPPT_ofDeterministic {r : ℕ → List Bool} {b₀ b₁ : ℕ → Bool}
    {D : Distinguisher}
    (hr : ComputableInPolyTime r encUnary encBits)
    (hb₀ : ComputableInPolyTime b₀ encUnary encBool)
    (hb₁ : ComputableInPolyTime b₁ encUnary encBool)
    (hD : Probability.IsPPT encBool D) :
    (CommitmentReceiver.ofDeterministic r b₀ b₁ D).IsPPT :=
  let hn := ComputableInPolyTime.fst encUnary encBits
  ⟨(((hr.comp' hn).prod ((hb₀.comp' hn).prod (hb₁.comp' hn))).prod (.const [])).isPPTOn,
    IsPPTOn.preprocess hD ((ComputableInPolyTime.fst encUnary (encPair encBits encBits)).prod
      (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd')⟩

@[simp] theorem eval_commitmentHidingGame_ofDeterministic
    (commit : List Bool → Bool → List Bool → List Bool)
    (r : ℕ → List Bool) (b₀ b₁ : ℕ → Bool) (D : Distinguisher)
    (aux : List Bool) (bit : Bool) (n : ℕ) :
    ProbComp.eval
        (commitmentHidingGame commit (CommitmentReceiver.ofDeterministic r b₀ b₁ D) aux bit n) =
      distinguishingGame
        ((BitString.uniformList n).map (commit (r n) (if bit then b₁ n else b₀ n))) (D n) := by
  simp only [pmf_norm, commitmentHidingGame, CommitmentReceiver.ofDeterministic,
    distinguishingGame_eq_bind, BitString.eval_sampleList]

/-- Stateful-receiver hiding implies the deterministic-family hiding interface: any commitment
function satisfying `StatefulHiding` hides commitments for all deterministic polynomial-time
families `r : ℕ → List Bool` and `b₀ b₁ : ℕ → Bool`. -/
theorem StatefulHiding.computational_hiding {commit : List Bool → Bool → List Bool → List Bool}
    (h : StatefulHiding commit)
    {r : ℕ → List Bool} {b₀ b₁ : ℕ → Bool}
    (hr : ComputableInPolyTime r encUnary encBits)
    (hb₀ : ComputableInPolyTime b₀ encUnary encBool)
    (hb₁ : ComputableInPolyTime b₁ encUnary encBool) :
    ComputationallyIndistinguishable
      (fun n => (BitString.uniformList n).map (commit (r n) (b₀ n)))
      (fun n => (BitString.uniformList n).map (commit (r n) (b₁ n))) := by
  intro D hD
  simpa only [eval_commitmentHidingGame_ofDeterministic, ↓reduceIte, Bool.false_eq_true] using
    h.empty (CommitmentReceiver.ofDeterministic r b₀ b₁ D)
      (CommitmentReceiver.isPPT_ofDeterministic hr hb₀ hb₁ hD)

/-- PRG distinguisher induced by a stateful commitment receiver `receiver`, auxiliary input family
`aux`, and hidden bit selector `bit`. On security parameter `n` and candidate pad `pad`, it runs
`choice ← receiver.choose n (aux n)`, forms the commitment `naorCommit id r b_bit pad`, and runs
`receiver.guess n choice.2 c`. -/
noncomputable def naorReceiverDistinguisher (receiver : CommitmentReceiver)
    (aux : ℕ → List Bool) (bit : Bool) : Distinguisher :=
  fun n pad => do
    let choice ← receiver.choose n (aux n)
    let ((r, b₀, b₁), state) := choice
    receiver.guess n state
      (naorCommit id r (if bit then b₁ else b₀) pad)

/-- `naorReceiverDistinguisher receiver aux bit` is a strict PPT distinguisher whenever `receiver`
is strict PPT and `aux` is computable in plain polynomial time. -/
theorem isPPT_naorReceiverDistinguisher {receiver : CommitmentReceiver}
    {aux : ℕ → List Bool} (hR : receiver.IsPPT)
    (haux : ComputableInPolyTime aux encUnary encBits) (bit : Bool) :
    IsPPT encBool (naorReceiverDistinguisher receiver aux bit) := by
  let E0 := encPair encUnary encBits
  let EChoice := encPair (encPair encBits (encPair encBool encBool)) encBits
  let hn0 := ComputableInPolyTime.fst encUnary encBits
  let hp1 := ComputableInPolyTime.fst E0 EChoice
  let hchoice1 := ComputableInPolyTime.snd E0 EChoice
  have harg := hp1.fst'.prod (hchoice1.snd'.prod
    (computableInPolyTime_naorCommit .id' hchoice1.fst'.fst'
      ((ComputableInPolyTime.const (encOut := encBool) bit).ite
        hchoice1.fst'.snd'.snd' hchoice1.fst'.snd'.fst')
      hp1.snd'))
  exact (IsPPTOn.preprocess hR.choose (hn0.prod (haux.comp' hn0))).bind_with
    (IsPPTOn.preprocess hR.guess harg)

/-- Running `commitmentHidingGame (naorCommit generator)` against `receiver` coincides with running
`naorReceiverDistinguisher receiver aux bit` against the PRG output `generatorEnsemble generator n`.
-/
theorem eval_commitmentHidingGame_naorCommit (generator : List Bool → List Bool)
    (receiver : CommitmentReceiver) (aux : ℕ → List Bool) (bit : Bool) (n : ℕ) :
    ProbComp.eval (commitmentHidingGame (naorCommit generator) receiver (aux n) bit n) =
      distinguishingGame (generatorEnsemble generator n)
        (naorReceiverDistinguisher receiver aux bit n) := by
  rw [distinguishingGame_eq_bind]
  unfold commitmentHidingGame generatorEnsemble naorReceiverDistinguisher
  simp only [pmf_norm, BitString.eval_sampleList]
  exact PMF.bind_comm _ _ _

/-- On a truly uniform `m`-bit pad, `naorReceiverDistinguisher receiver aux bit n` presents an
independent uniform `m`-bit commitment to `receiver.guess` regardless of the receiver's chosen
challenge string `r` and bit selector `bit`. -/
theorem distinguishingGame_uniformList_naorReceiverDistinguisher (m : ℕ)
    (receiver : CommitmentReceiver) (aux : ℕ → List Bool) (bit : Bool) (n : ℕ) :
    distinguishingGame (BitString.uniformList m)
        (naorReceiverDistinguisher receiver aux bit n) =
      (ProbComp.eval (receiver.choose n (aux n))).bind fun choice =>
        (BitString.uniformList m).bind fun c =>
          ProbComp.eval (receiver.guess n choice.2 c) := by
  rw [distinguishingGame_eq_bind]
  unfold naorReceiverDistinguisher
  simp only [ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  pmf_swap with choice
  have h := congrArg
    (fun p : PMF (List Bool) => p.bind fun c => ProbComp.eval (receiver.guess n choice.2 c))
    (uniformList_map_naorCommit_id m choice.1.1 (if bit then choice.1.2.2 else choice.1.2.1))
  simpa only [PMF.bind_map, Function.comp_def] using h

/-- Under a truly uniform `m`-bit pad, the `false` and `true` commitment-hiding experiments are
identically distributed for every stateful receiver `receiver`. -/
theorem distinguishingGame_uniformList_naorReceiverDistinguisher_false_eq_true (m : ℕ)
    (receiver : CommitmentReceiver) (aux : ℕ → List Bool) (n : ℕ) :
    distinguishingGame (BitString.uniformList m)
        (naorReceiverDistinguisher receiver aux false n) =
      distinguishingGame (BitString.uniformList m)
        (naorReceiverDistinguisher receiver aux true n) := by
  rw [distinguishingGame_uniformList_naorReceiverDistinguisher,
    distinguishingGame_uniformList_naorReceiverDistinguisher]

/-- **Quantitative stateful-receiver hiding bound for Naor's bit commitment scheme**: the
commitment-hiding advantage of any stateful receiver `receiver` at security parameter `n` is bounded
by the sum of the PRG distinguishing advantages of `naorReceiverDistinguisher receiver aux false`
and `naorReceiverDistinguisher receiver aux true` against `BitString.uniformList m`. -/
theorem advantage_commitmentHidingGame_naorCommit_le
    (generator : List Bool → List Bool) (m : ℕ)
    (receiver : CommitmentReceiver) (aux : ℕ → List Bool) (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (commitmentHidingGame (naorCommit generator) receiver (aux n) false n))
      (ProbComp.eval
        (commitmentHidingGame (naorCommit generator) receiver (aux n) true n)) ≤
      Game.advantage
        (distinguishingGame (generatorEnsemble generator n)
          (naorReceiverDistinguisher receiver aux false n))
        (distinguishingGame (BitString.uniformList m)
          (naorReceiverDistinguisher receiver aux false n)) +
      Game.advantage
        (distinguishingGame (generatorEnsemble generator n)
          (naorReceiverDistinguisher receiver aux true n))
        (distinguishingGame (BitString.uniformList m)
          (naorReceiverDistinguisher receiver aux true n)) := by
  rw [eval_commitmentHidingGame_naorCommit, eval_commitmentHidingGame_naorCommit]
  refine (Game.advantage_triangle _
    (distinguishingGame (BitString.uniformList m)
      (naorReceiverDistinguisher receiver aux false n)) _).trans ?_
  rw [distinguishingGame_uniformList_naorReceiverDistinguisher_false_eq_true,
    Game.advantage_comm (distinguishingGame (BitString.uniformList m) _)]

/-- **Stateful-receiver computational hiding of Naor bit commitment** [Naor1991]: for any
pseudorandom generator `generator`, `naorCommit generator` satisfies `StatefulHiding` against all
randomized stateful PPT receivers. -/
theorem PseudorandomGenerator.naorStatefulHiding
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) :
    StatefulHiding (naorCommit generator) := by
  intro aux haux receiver hR
  have hfalse := hG.indistinguishable (naorReceiverDistinguisher receiver aux false)
    (isPPT_naorReceiverDistinguisher hR haux false)
  have htrue := hG.indistinguishable (naorReceiverDistinguisher receiver aux true)
    (isPPT_naorReceiverDistinguisher hR haux true)
  exact negligible_of_le (hfalse.add htrue) fun n =>
    advantage_commitmentHidingGame_naorCommit_le generator (length n) receiver aux n

/-! ### Statistical binding -/

/-- A receiver string `r` is binding for seed length `n` if no two seeds of length `n` produce
the same commitment for `false` and `true`. -/
def NaorBinding (generator : List Bool → List Bool) (n : ℕ) (r : List Bool) : Prop :=
  ∀ s₀ s₁ : List Bool, s₀.length = n → s₁.length = n →
    naorCommit generator r false s₀ ≠ naorCommit generator r true s₁

/-- Equivalence between `NaorBinding` on lists of length `n` and on `BitString n`. -/
theorem naorBinding_iff_bitString (generator : List Bool → List Bool) (n : ℕ) (r : List Bool) :
    NaorBinding generator n r ↔
      ∀ s₀ s₁ : BitString n,
        naorCommit generator r false (List.ofFn s₀) ≠
          naorCommit generator r true (List.ofFn s₁) := by
  constructor
  · intro h s₀ s₁
    exact h (List.ofFn s₀) (List.ofFn s₁) (List.length_ofFn) (List.length_ofFn)
  · intro h s₀ s₁ hs₀ hs₁
    rw [← BitString.ofFn_ofList hs₀, ← BitString.ofFn_ofList hs₁]
    exact h _ _

instance decidablePredNaorBinding (generator : List Bool → List Bool) (n : ℕ) :
    DecidablePred (NaorBinding generator n) :=
  fun r => decidable_of_iff' _ (naorBinding_iff_bitString generator n r)

/-- If a commitment opened as `false` with `s₀` equals a commitment opened as `true` with `s₁`,
then `s₀` and `s₁` must open to the same bit whenever `NaorBinding` holds. -/
theorem NaorBinding.eq_of_naorCommit_eq {generator : List Bool → List Bool} {n : ℕ} {r : List Bool}
    (hbind : NaorBinding generator n r) {b₀ b₁ : Bool} {s₀ s₁ : List Bool}
    (hs₀ : s₀.length = n) (hs₁ : s₁.length = n)
    (heq : naorCommit generator r b₀ s₀ = naorCommit generator r b₁ s₁) : b₀ = b₁ := by
  cases b₀ <;> cases b₁
  · rfl
  · exact False.elim (hbind s₀ s₁ hs₀ hs₁ heq)
  · exact False.elim (hbind s₁ s₀ hs₁ hs₀ heq.symm)
  · rfl

/-- The bad receiver string determined by a pair of seeds `(s₀, s₁)`. -/
def naorBadShift (generator : List Bool → List Bool) (m n : ℕ)
    (pair : BitString n × BitString n) : BitString m :=
  BitString.ofList m (generator (List.ofFn pair.1)) +
    BitString.ofList m (generator (List.ofFn pair.2))

/-- If `NaorBinding generator n r` fails, then `ofList (length n) r` is the XOR of two generator
outputs on `n`-bit seeds. -/
theorem mem_image_naorBadShift_of_not_naorBinding {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ s, (generator s).length = length s.length)
    {n : ℕ} {r : List Bool} (hnot : ¬ NaorBinding generator n r) :
    BitString.ofList (length n) r ∈
      Finset.univ.image (naorBadShift generator (length n) n) := by
  rw [naorBinding_iff_bitString] at hnot
  push Not at hnot
  obtain ⟨s₀, s₁, heq⟩ := hnot
  rw [Finset.mem_image]
  refine ⟨(s₀, s₁), Finset.mem_univ _, ?_⟩
  have hlen₁ : (generator (List.ofFn s₁)).length = length n := by
    simpa only [List.length_ofFn] using hlen (List.ofFn s₁)
  have hbit := congrArg (BitString.ofList (length n)) heq
  rw [naorCommit_false, naorCommit_true, hlen₁, BitString.ofList_listXor_pair] at hbit
  let y₀ := BitString.ofList (length n) (generator (List.ofFn s₀))
  let y₁ := BitString.ofList (length n) (generator (List.ofFn s₁))
  let r' := BitString.ofList (length n) r
  change y₀ = y₁ + r' at hbit
  change y₀ + y₁ = r'
  rw [hbit, add_right_comm, BitString.add_self, zero_add]

/-- At most `2 ^ (2 * n)` receiver strings of length `length n` violate `NaorBinding`. -/
theorem card_not_naorBinding_le {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = length s.length) (n : ℕ) :
    (Finset.univ.filter (fun r : BitString (length n) =>
      ¬ NaorBinding generator n (List.ofFn r))).card ≤ 2 ^ (2 * n) := by
  have hsub : Finset.univ.filter (fun r : BitString (length n) =>
      ¬ NaorBinding generator n (List.ofFn r)) ⊆
        Finset.univ.image (naorBadShift generator (length n) n) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    simpa only [BitString.ofList_ofFn] using mem_image_naorBadShift_of_not_naorBinding hlen hr.2
  calc
    (Finset.univ.filter (fun r : BitString (length n) =>
        ¬ NaorBinding generator n (List.ofFn r))).card
      ≤ (Finset.univ.image (naorBadShift generator (length n) n)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (BitString n × BitString n)).card := Finset.card_image_le
    _ = 2 ^ (2 * n) := by
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_bool, ← pow_add, two_mul]

/-- The `ENNReal` probability that a uniform receiver string of length `length n` fails to be
binding for `n`-bit seeds. -/
noncomputable def naorBindingProb (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (n : ℕ) : ℝ≥0∞ :=
  (BitString.uniformList (length n)).toOuterMeasure {r | ¬ NaorBinding generator n r}

/-- The nonnegative real probability that a uniform receiver string of length `length n` fails to
be binding for `n`-bit seeds. -/
noncomputable def naorBindingError (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (n : ℕ) : ℝ≥0 :=
  (naorBindingProb generator length n).toNNReal

/-- The binding failure probability is at most `2 ^ (2 * n) / 2 ^ (length n)`. -/
theorem naorBindingProb_le {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = length s.length) (n : ℕ) :
    naorBindingProb generator length n ≤ (2 ^ (2 * n) : ℝ≥0∞) / 2 ^ (length n) := by
  classical
  rw [naorBindingProb, BitString.uniformList, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_uniformOfFintype]
  simp only [Set.preimage, Set.mem_ofPred_eq, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  gcongr
  exact_mod_cast card_not_naorBinding_le hlen n

private theorem two_pow_div_two_pow_le {a b k : ℕ} (h : a + k ≤ b) :
    (2 ^ a : ℝ≥0∞) / 2 ^ b ≤ (1 / 2 : ℝ≥0∞) ^ k := by
  have hpow : (2 : ℝ≥0∞) ^ b = (2 : ℝ≥0∞) ^ a * (2 : ℝ≥0∞) ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le (by lia)]
  have hne : (2 : ℝ≥0∞) ^ a ≠ 0 := pow_ne_zero _ two_ne_zero
  have htop : (2 : ℝ≥0∞) ^ a ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [hpow, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hne) (Or.inl htop),
    ← mul_assoc, ENNReal.mul_inv_cancel hne htop, one_mul, one_div, ← ENNReal.inv_pow]
  exact ENNReal.inv_le_inv.mpr (pow_le_pow_right' (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by lia))

/-- When `3 * n ≤ length n`, the binding failure probability is at most `(1 / 2) ^ n`. -/
theorem naorBindingProb_le_of_three_mul {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = length s.length) (n : ℕ) (hstretch : 3 * n ≤ length n) :
    naorBindingProb generator length n ≤ (1 / 2 : ℝ≥0∞) ^ n :=
  (naorBindingProb_le hlen n).trans (two_pow_div_two_pow_le (by lia))

/-- When `3 * n + 1 ≤ length n`, the binding failure probability is at most `(1 / 2) ^ (n + 1)`. -/
theorem naorBindingProb_le_of_three_mul_add_one {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ s, (generator s).length = length s.length) (n : ℕ)
    (hstretch : 3 * n + 1 ≤ length n) :
    naorBindingProb generator length n ≤ (1 / 2 : ℝ≥0∞) ^ (n + 1) :=
  (naorBindingProb_le hlen n).trans (two_pow_div_two_pow_le (by lia))

/-- When `3 * n ≤ length n`, the nonnegative real binding failure probability is at most
`(1 / 2) ^ n`. -/
theorem naorBindingError_le_of_three_mul {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = length s.length) (n : ℕ) (hstretch : 3 * n ≤ length n) :
    naorBindingError generator length n ≤ (1 / 2 : ℝ≥0) ^ n := by
  have h := ENNReal.toNNReal_mono (by simp) (naorBindingProb_le_of_three_mul hlen n hstretch)
  simpa only [naorBindingError, one_div, ENNReal.toNNReal_pow, ENNReal.toNNReal_inv,
    ENNReal.toNNReal_ofNat] using h

/-- **Statistical binding of Naor bit commitment.** When `3 * n ≤ length n` for all `n`, the
binding failure probability is negligible. -/
theorem negligible_naorBindingError {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = length s.length) (hstretch : ∀ n, 3 * n ≤ length n) :
    Negligible (naorBindingError generator length) :=
  negligible_of_le (negligible_geometric (by norm_num : (1 / 2 : ℝ≥0) < 1))
    (fun n => naorBindingError_le_of_three_mul hlen n (hstretch n))

/-! ### Selective-opening batch commitments -/

/-- Commit to one bit using `seed` when `openFlag = true`, or a pre-expanded `pad` when
`openFlag = false`. -/
def naorCommitAt (generator : List Bool → List Bool) (r : List Bool)
    (openFlag b : Bool) (seed pad : List Bool) : List Bool :=
  if openFlag then naorCommit generator r b seed else naorCommit id r b pad

@[simp] theorem naorCommitAt_true (generator : List Bool → List Bool) (r : List Bool)
    (b : Bool) (seed pad : List Bool) :
    naorCommitAt generator r true b seed pad = naorCommit generator r b seed := rfl

@[simp] theorem naorCommitAt_false (generator : List Bool → List Bool) (r : List Bool)
    (b : Bool) (seed pad : List Bool) :
    naorCommitAt generator r false b seed pad = naorCommit id r b pad := rfl

@[fun_prop]
theorem computableInPolyTime_naorCommitAt {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {r : α → List Bool} {openFlag b : α → Bool}
    {seed pad : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hr : ComputableInPolyTime r input encBits)
    (hopen : ComputableInPolyTime openFlag input encBool)
    (hb : ComputableInPolyTime b input encBool)
    (hseed : ComputableInPolyTime seed input encBits)
    (hpad : ComputableInPolyTime pad input encBits) :
    ComputableInPolyTime
      (fun a => naorCommitAt generator (r a) (openFlag a) (b a) (seed a) (pad a))
      input encBits :=
  hopen.ite (computableInPolyTime_naorCommit hg hr hb hseed)
    (computableInPolyTime_naorCommit .id' hr hb hpad)

/-- When the unopened pad is drawn uniformly from `BitString.uniformList m`, the committed bit at
an unopened coordinate is information-theoretically hidden and may be replaced by
`openFlag && b`. -/
theorem uniformList_map_naorCommitAt (m : ℕ) (generator : List Bool → List Bool)
    (r : List Bool) (openFlag b : Bool) (seed : List Bool) :
    (BitString.uniformList m).map (naorCommitAt generator r openFlag b seed) =
      (BitString.uniformList m).map (naorCommitAt generator r openFlag (openFlag && b) seed) := by
  have h : naorCommitAt generator r openFlag b seed =
      naorCommitAt generator r openFlag (openFlag && b) seed ∘ naorCommit id r b := by
    funext u
    cases openFlag <;> simp only [naorCommitAt, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
      Bool.true_and, Function.comp_apply, naorCommit_false, id_eq]
  rw [h, ← PMF.map_comp, uniformList_map_naorCommit_id]

/-- Keep the bits at opened coordinates and zero out unopened coordinates to `false`. -/
def naorMaskBits : List Bool → List Bool → List Bool
  | _, [] => []
  | openFlags, b :: bits =>
    (openFlags.headD false && b) :: naorMaskBits openFlags.tail bits

@[simp] theorem length_naorMaskBits (openFlags bits : List Bool) :
    (naorMaskBits openFlags bits).length = bits.length := by
  induction bits generalizing openFlags with
  | nil => rfl
  | cons b bits ih => simp only [naorMaskBits, List.length_cons, ih]

theorem getD_naorMaskBits (openFlags bits : List Bool) (i : ℕ) :
    (naorMaskBits openFlags bits).getD i false =
      (openFlags.getD i false && bits.getD i false) := by
  induction bits generalizing openFlags i with
  | nil => simp only [naorMaskBits, List.getD_nil, Bool.and_false]
  | cons b bits ih =>
    cases i with
    | zero => cases openFlags <;> simp only [naorMaskBits, List.headD_nil, List.headD_cons,
        List.getD_cons_zero, List.getD_nil]
    | succ i =>
      cases openFlags with
      | nil =>
        simpa only [naorMaskBits, List.tail_nil, List.getD_cons_succ, List.getD_nil] using ih [] i
      | cons flag flags =>
        simpa only [naorMaskBits, List.tail_cons, List.getD_cons_succ] using ih flags i

/-- A list of length `n` whose entries, read with `getD`, are `g i` is `(List.range n).map g`. -/
private theorem eq_map_range_of_getD {α : Type} {l : List α} {d : α} {n : ℕ} {g : ℕ → α}
    (hl : l.length = n) (h : ∀ i < n, l.getD i d = g i) : l = (List.range n).map g := by
  subst hl
  apply List.ext_getElem (by simp only [List.length_map, List.length_range])
  intro i hi _
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem_map, List.getElem_range] using h i hi

theorem naorMaskBits_eq_map (openFlags bits : List Bool) :
    naorMaskBits openFlags bits =
      (List.range bits.length).map (fun i => openFlags.getD i false && bits.getD i false) :=
  eq_map_range_of_getD (length_naorMaskBits _ _) fun i _ => getD_naorMaskBits openFlags bits i

@[fun_prop]
theorem computableInPolyTime_naorMaskBits {α : Type} {input : α ↪ List Bool}
    {openFlags bits : α → List Bool}
    (hopen : ComputableInPolyTime openFlags input encBits)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => naorMaskBits (openFlags a) (bits a))
      input encBits := by
  simp_rw [naorMaskBits_eq_map]
  have hp := ComputableInPolyTime.fst input encUnary
  have hi := ComputableInPolyTime.snd input encUnary
  exact ComputableInPolyTime.mapToBitsWithInput hbits.length_bits_comp.unary_range'
    ((ComputableInPolyTime.bitsGetDWithInput (hopen.comp' hp) hi false).bool_and'
      (ComputableInPolyTime.bitsGetDWithInput (hbits.comp' hp) hi false))

/-- Batch commitment using `seeds` at opened coordinates and pre-expanded `pads` at unopened
coordinates. -/
def naorCommitSplit (generator : List Bool → List Bool) (r : List Bool) :
    List Bool → List Bool → List (List Bool) → List (List Bool) → List (List Bool)
  | _, [], _, _ => []
  | openFlags, b :: bits, seeds, pads =>
    naorCommitAt generator r (openFlags.headD false) b (seeds.headD []) (pads.headD []) ::
      naorCommitSplit generator r openFlags.tail bits seeds.tail pads.tail

@[simp] theorem length_naorCommitSplit (generator : List Bool → List Bool) (r : List Bool)
    (openFlags bits : List Bool) (seeds pads : List (List Bool)) :
    (naorCommitSplit generator r openFlags bits seeds pads).length = bits.length := by
  induction bits generalizing openFlags seeds pads with
  | nil => rfl
  | cons b bits ih => simp only [naorCommitSplit, List.length_cons, ih]

private theorem getD_tail {α : Type} (xs : List α) (i : ℕ) (d : α) :
    xs.tail.getD i d = xs.getD (i + 1) d := by
  cases xs <;> simp only [List.tail_nil, List.tail_cons, List.getD_nil, List.getD_cons_succ]

theorem getD_naorCommitSplit (generator : List Bool → List Bool) (r : List Bool)
    (openFlags bits : List Bool) (seeds pads : List (List Bool)) (i : ℕ)
    (hi : i < bits.length) :
    (naorCommitSplit generator r openFlags bits seeds pads).getD i [] =
      naorCommitAt generator r (openFlags.getD i false) (bits.getD i false)
        (seeds.getD i []) (pads.getD i []) := by
  induction bits generalizing openFlags seeds pads i with
  | nil => contradiction
  | cons b bits ih =>
    cases i with
    | zero =>
      cases openFlags <;> cases seeds <;> cases pads <;>
        simp only [naorCommitSplit, List.headD_nil, List.headD_cons, List.getD_cons_zero,
          List.getD_nil]
    | succ i =>
      simpa only [naorCommitSplit, List.getD_cons_succ, getD_tail] using
        ih openFlags.tail seeds.tail pads.tail i (Nat.lt_of_succ_lt_succ hi)

theorem naorCommitSplit_eq_map (generator : List Bool → List Bool) (r : List Bool)
    (openFlags bits : List Bool) (seeds pads : List (List Bool)) :
    naorCommitSplit generator r openFlags bits seeds pads =
      (List.range bits.length).map (fun i =>
        naorCommitAt generator r (openFlags.getD i false) (bits.getD i false)
          (seeds.getD i []) (pads.getD i [])) :=
  eq_map_range_of_getD (length_naorCommitSplit ..) fun i hi =>
    getD_naorCommitSplit generator r openFlags bits seeds pads i hi

@[fun_prop]
theorem computableInPolyTime_naorCommitSplit {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {r openFlags bits : α → List Bool}
    {seeds pads : α → List (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hr : ComputableInPolyTime r input encBits)
    (hopen : ComputableInPolyTime openFlags input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (hseeds : ComputableInPolyTime seeds input (encList encBits))
    (hpads : ComputableInPolyTime pads input (encList encBits)) :
    ComputableInPolyTime
      (fun a => naorCommitSplit generator (r a) (openFlags a) (bits a) (seeds a) (pads a))
      input (encList encBits) := by
  simp_rw [naorCommitSplit_eq_map]
  have hp := ComputableInPolyTime.fst input encUnary
  have hi := ComputableInPolyTime.snd input encUnary
  exact ComputableInPolyTime.mapWithInput hbits.length_bits_comp.unary_range'
    (computableInPolyTime_naorCommitAt hg (hr.comp' hp)
      (ComputableInPolyTime.bitsGetDWithInput (hopen.comp' hp) hi false)
      (ComputableInPolyTime.bitsGetDWithInput (hbits.comp' hp) hi false)
      (ComputableInPolyTime.listGetDWithInput (hseeds.comp' hp) hi [])
      (ComputableInPolyTime.listGetDWithInput (hpads.comp' hp) hi []))

/-- When the unopened pads are drawn independently from `BitString.sampleList m`, the distribution
of `naorCommitSplit` depends only on the masked bits `naorMaskBits openFlags bits`. -/
theorem eval_replicate_map_naorCommitSplit (m : ℕ) (generator : List Bool → List Bool)
    (r openFlags bits : List Bool) (seeds : List (List Bool)) :
    ProbComp.eval ((naorCommitSplit generator r openFlags bits seeds) <$>
        OracleComp.replicate bits.length (BitString.sampleList m)) =
      ProbComp.eval ((naorCommitSplit generator r openFlags (naorMaskBits openFlags bits) seeds) <$>
        OracleComp.replicate bits.length (BitString.sampleList m)) := by
  induction bits generalizing openFlags seeds with
  | nil => rfl
  | cons b bits ih =>
    simp only [pmf_norm, List.length_cons, OracleComp.replicate_succ, BitString.eval_sampleList,
      naorCommitSplit, naorMaskBits, List.headD_cons, List.tail_cons]
    have htail := ih openFlags.tail seeds.tail
    simp only [ProbComp.eval_map] at htail
    have hstep (f : List Bool → List Bool) (g : List (List Bool) → List (List Bool)) :
        (BitString.uniformList m).bind (fun u =>
          (ProbComp.eval (OracleComp.replicate bits.length (BitString.sampleList m))).map
            (fun rest => f u :: g rest)) =
        ((BitString.uniformList m).map f).bind (fun head =>
          ((ProbComp.eval (OracleComp.replicate bits.length (BitString.sampleList m))).map g).map
            (head :: ·)) := by
      simp only [pmf_norm]
    rw [hstep, uniformList_map_naorCommitAt, htail, ← hstep]

/-- `naorMaskBits` distributes over list append when the first segments have equal length. -/
theorem naorMaskBits_append {flags₁ flags₂ bits₁ bits₂ : List Bool}
    (h : flags₁.length = bits₁.length) :
    naorMaskBits (flags₁ ++ flags₂) (bits₁ ++ bits₂) =
      naorMaskBits flags₁ bits₁ ++ naorMaskBits flags₂ bits₂ := by
  induction bits₁ generalizing flags₁ with
  | nil =>
    cases flags₁ with
    | nil => rfl
    | cons _ _ => simp only [List.length_cons, List.length_nil, Nat.succ_ne_zero] at h
  | cons b bits₁ ih =>
    cases flags₁ with
    | nil => simp only [List.length_nil, List.length_cons, Nat.zero_ne_add_one] at h
    | cons f flags₁ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.cons_append, naorMaskBits, List.headD_cons, List.tail_cons, ih h]

/-- `naorCommitSplit` distributes over list append when the first segments have equal length. -/
theorem naorCommitSplit_append (generator : List Bool → List Bool) (r : List Bool)
    {flags₁ flags₂ bits₁ bits₂ : List Bool} {seeds₁ seeds₂ pads₁ pads₂ : List (List Bool)}
    (hflags : flags₁.length = bits₁.length) (hseeds : seeds₁.length = bits₁.length)
    (hpads : pads₁.length = bits₁.length) :
    naorCommitSplit generator r (flags₁ ++ flags₂) (bits₁ ++ bits₂)
        (seeds₁ ++ seeds₂) (pads₁ ++ pads₂) =
      naorCommitSplit generator r flags₁ bits₁ seeds₁ pads₁ ++
        naorCommitSplit generator r flags₂ bits₂ seeds₂ pads₂ := by
  induction bits₁ generalizing flags₁ seeds₁ pads₁ with
  | nil =>
    cases flags₁ <;> cases seeds₁ <;> cases pads₁ <;>
      try simp only [List.length_nil, List.length_cons, Nat.succ_ne_zero] at hflags hseeds hpads
    rfl
  | cons b bits₁ ih =>
    cases flags₁ with
    | nil => simp only [List.length_nil, List.length_cons, Nat.zero_ne_add_one] at hflags
    | cons f flags₁ =>
      cases seeds₁ with
      | nil => simp only [List.length_nil, List.length_cons, Nat.zero_ne_add_one] at hseeds
      | cons s seeds₁ =>
        cases pads₁ with
        | nil => simp only [List.length_nil, List.length_cons, Nat.zero_ne_add_one] at hpads
        | cons p pads₁ =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hflags hseeds hpads
          simp only [List.cons_append, naorCommitSplit, List.headD_cons, List.tail_cons,
            ih hflags hseeds hpads]

/-- Select seeds of width `s` at opened coordinates and pad unopened coordinates with `s` false
bits. -/
def naorSelectSeeds (s : ℕ) : List Bool → List Bool → List (List Bool) → List (List Bool)
  | _, [], _ => []
  | openFlags, _ :: bits, seeds =>
    (if openFlags.headD false then BitString.listRow s 0 (seeds.headD [])
     else List.replicate s false) ::
      naorSelectSeeds s openFlags.tail bits seeds.tail

@[simp] theorem length_naorSelectSeeds (s : ℕ) (openFlags bits : List Bool)
    (seeds : List (List Bool)) :
    (naorSelectSeeds s openFlags bits seeds).length = bits.length := by
  induction bits generalizing openFlags seeds with
  | nil => rfl
  | cons _ bits ih => simp only [naorSelectSeeds, List.length_cons, ih]

theorem length_mem_naorSelectSeeds {s : ℕ} {openFlags bits : List Bool}
    {seeds : List (List Bool)} {w : List Bool}
    (hw : w ∈ naorSelectSeeds s openFlags bits seeds) : w.length = s := by
  induction bits generalizing openFlags seeds w with
  | nil => simp only [naorSelectSeeds, List.not_mem_nil] at hw
  | cons _ bits ih =>
    simp only [naorSelectSeeds, List.mem_cons] at hw
    rcases hw with rfl | hw
    · split_ifs <;> simp only [BitString.length_listRow, List.length_replicate]
    · exact ih hw

theorem getD_naorSelectSeeds (s : ℕ) (openFlags bits : List Bool)
    (seeds : List (List Bool)) (i : ℕ) (hi : i < bits.length) :
    (naorSelectSeeds s openFlags bits seeds).getD i [] =
      if openFlags.getD i false then BitString.listRow s 0 (seeds.getD i [])
      else List.replicate s false := by
  induction bits generalizing openFlags seeds i with
  | nil => contradiction
  | cons _ bits ih =>
    cases i with
    | zero =>
      cases openFlags <;> cases seeds <;> rfl
    | succ i =>
      simpa only [naorSelectSeeds, List.getD_cons_succ, getD_tail] using
        ih openFlags.tail seeds.tail i (Nat.lt_of_succ_lt_succ hi)

theorem naorSelectSeeds_eq_map (s : ℕ) (openFlags bits : List Bool)
    (seeds : List (List Bool)) :
    naorSelectSeeds s openFlags bits seeds =
      (List.range bits.length).map (fun i =>
        if openFlags.getD i false then BitString.listRow s 0 (seeds.getD i [])
        else List.replicate s false) :=
  eq_map_range_of_getD (length_naorSelectSeeds ..) fun i hi =>
    getD_naorSelectSeeds s openFlags bits seeds i hi

@[simp] theorem naorSelectSeeds_naorMaskBits (s : ℕ) (openFlags bits : List Bool)
    (seeds : List (List Bool)) :
    naorSelectSeeds s openFlags (naorMaskBits openFlags bits) seeds =
      naorSelectSeeds s openFlags bits seeds := by
  simp only [naorSelectSeeds_eq_map, length_naorMaskBits]

@[fun_prop]
theorem computableInPolyTime_naorSelectSeeds {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {openFlags bits : α → List Bool} {seeds : α → List (List Bool)}
    (hs : ComputableInPolyTime s input encUnary)
    (hopen : ComputableInPolyTime openFlags input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (hseeds : ComputableInPolyTime seeds input (encList encBits)) :
    ComputableInPolyTime
      (fun a => naorSelectSeeds (s a) (openFlags a) (bits a) (seeds a))
      input (encList encBits) := by
  simp_rw [naorSelectSeeds_eq_map]
  have hp := ComputableInPolyTime.fst input encUnary
  have hi := ComputableInPolyTime.snd input encUnary
  have hs' := hs.comp' hp
  exact ComputableInPolyTime.mapWithInput hbits.length_bits_comp.unary_range'
    ((ComputableInPolyTime.bitsGetDWithInput (hopen.comp' hp) hi false).ite
      (ComputableInPolyTime.bitsRowWithInput hs' (.const 0)
        (ComputableInPolyTime.listGetDWithInput (hseeds.comp' hp) hi []))
      ((ComputableInPolyTime.bitsReplicate false).comp' hs'))

/-- Select `generator seed` at opened coordinates and `pad` at unopened coordinates. -/
def naorSelectPads (generator : List Bool → List Bool) :
    List Bool → List Bool → List (List Bool) → List (List Bool) → List (List Bool)
  | _, [], _, _ => []
  | openFlags, _ :: bits, seeds, pads =>
    (if openFlags.headD false then generator (seeds.headD []) else pads.headD []) ::
      naorSelectPads generator openFlags.tail bits seeds.tail pads.tail

/-- `naorCommitSplit` depends on `seeds` and `pads` only through `naorSelectPads`. -/
theorem naorCommitSplit_eq_naorSelectPads (generator : List Bool → List Bool) (r : List Bool)
    (openFlags bits : List Bool) (seeds pads : List (List Bool)) :
    naorCommitSplit generator r openFlags bits seeds pads =
      naorCommitSplit id r (List.replicate bits.length false) bits []
        (naorSelectPads generator openFlags bits seeds pads) := by
  induction bits generalizing openFlags seeds pads with
  | nil => rfl
  | cons b bits ih =>
    simp only [naorCommitSplit, naorSelectPads, List.length_cons, List.replicate_succ,
      List.headD_cons, List.tail_cons, naorCommitAt_false]
    congr 1
    · cases openFlags.headD false with
      | false => rfl
      | true => exact naorCommit_eq_comp_id generator r b (seeds.headD [])
    · exact ih openFlags.tail seeds.tail pads.tail

/-- When `pads` are drawn from `generator <$> BitString.sampleList s` and `seeds` from
`BitString.sampleList s`, the joint law of `(naorSelectPads, naorSelectSeeds)` is identical to
using `seeds` at all coordinates (`openFlags = List.replicate bits.length true`). -/
theorem eval_replicate_naorSelectPads (s : ℕ) (generator : List Bool → List Bool)
    (openFlags bits : List Bool) :
    ProbComp.eval (do
        let seeds ← OracleComp.replicate bits.length (BitString.sampleList s)
        let pads ← OracleComp.replicate bits.length (generator <$> BitString.sampleList s)
        return (naorSelectPads generator openFlags bits seeds pads,
          naorSelectSeeds s openFlags bits seeds)) =
    ProbComp.eval ((fun seeds : List (List Bool) =>
        (naorSelectPads generator (List.replicate bits.length true) bits seeds [],
          naorSelectSeeds s openFlags bits seeds)) <$>
      OracleComp.replicate bits.length (BitString.sampleList s)) := by
  induction bits generalizing openFlags with
  | nil => simp only [List.length_nil, OracleComp.replicate_zero, pure_bind, ProbComp.eval_pure,
      naorSelectPads, naorSelectSeeds, map_pure]
  | cons b bits ih =>
    simp only [pmf_norm, List.length_cons, OracleComp.replicate_succ, BitString.eval_sampleList,
      naorSelectPads, naorSelectSeeds, List.replicate_succ, List.headD_cons, List.tail_cons,
      List.tail_nil, ↓reduceIte]
    have htail := ih openFlags.tail
    simp only [pmf_norm] at htail
    set D_s := ProbComp.eval (OracleComp.replicate bits.length (BitString.sampleList s))
    set D_p := ProbComp.eval
      (OracleComp.replicate bits.length (generator <$> BitString.sampleList s))
    have hstep (u v : List Bool) :
        D_s.bind (fun rest_s => D_p.bind (fun rest_p => PMF.pure
          ((if openFlags.headD false then generator u else v) ::
            naorSelectPads generator openFlags.tail bits rest_s rest_p,
            (if openFlags.headD false then BitString.listRow s 0 u else List.replicate s false) ::
            naorSelectSeeds s openFlags.tail bits rest_s))) =
        D_s.map (fun rest_s =>
          ((if openFlags.headD false then generator u else v) ::
            naorSelectPads generator (List.replicate bits.length true) bits rest_s [],
            (if openFlags.headD false then BitString.listRow s 0 u else List.replicate s false) ::
            naorSelectSeeds s openFlags.tail bits rest_s)) := by
      have hcongr := congrArg (PMF.map (fun q : List (List Bool) × List (List Bool) =>
        ((if openFlags.headD false then generator u else v) :: q.1,
          (if openFlags.headD false then BitString.listRow s 0 u else List.replicate s false) ::
            q.2))) htail
      simpa only [pmf_norm, D_s, D_p]
        using hcongr
    simp_rw [PMF.bind_comm D_s (BitString.uniformList s), hstep]
    cases openFlags.headD false <;>
      simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_const, D_s]

/-! ### Packaged bit commitment scheme -/

/-- Verification of a Naor bit commitment opening `(b, seed)` against seed length `n`, receiver
string `r`, and commitment `c`. -/
def naorVerify (generator : List Bool → List Bool) (n : ℕ) (r c : List Bool) (b : Bool)
    (seed : List Bool) : Bool :=
  decide (seed.length = n) && (c == naorCommit generator r b seed)

/-- Naor commitment verification is computable in plain polynomial time when its inputs are. -/
@[fun_prop]
theorem computableInPolyTime_naorVerify {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {n : α → ℕ} {r c : α → List Bool}
    {b : α → Bool} {seed : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hn : ComputableInPolyTime n input encUnary)
    (hr : ComputableInPolyTime r input encBits)
    (hc : ComputableInPolyTime c input encBits)
    (hb : ComputableInPolyTime b input encBool)
    (hseed : ComputableInPolyTime seed input encBits) :
    ComputableInPolyTime
      (fun a => naorVerify generator (n a) (r a) (c a) (b a) (seed a))
      input encBool :=
  (hseed.length_bits_comp.decide_eq' hn).bool_and'
    (hc.beq (computableInPolyTime_naorCommit hg hr hb hseed))

theorem naorVerify_naorCommit {generator : List Bool → List Bool} {n : ℕ}
    (r : List Bool) (b : Bool) {seed : List Bool} (hseed : seed.length = n) :
    naorVerify generator n r (naorCommit generator r b seed) b seed = true := by
  simp only [naorVerify, hseed, decide_true, beq_self_eq_true, Bool.and_self]

theorem eq_naorCommit_of_naorVerify {generator : List Bool → List Bool} {n : ℕ}
    {r c : List Bool} {b : Bool} {seed : List Bool}
    (h : naorVerify generator n r c b seed = true) :
    seed.length = n ∧ c = naorCommit generator r b seed := by
  simpa only [naorVerify, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using h

/-- A two-message statistically binding, computationally hiding bit commitment scheme [Naor1991].
At security parameter `n`, the receiver sends a uniform challenge string `r` of length
`challengeLength n`, the committer commits to `b : Bool` using a uniform seed `seed` of length `n`
via `commit r b seed` of length `commitLength n`, and openings are verified by
`verify n r c b seed`. Hiding (`stateful_hiding`) holds against any two-stage randomized stateful
PPT receiver (`CommitmentReceiver`). -/
structure BitCommitmentScheme where
  /-- Length of the receiver's first-round challenge at security parameter `n`. -/
  challengeLength : ℕ → ℕ
  /-- Length of the commitment string at security parameter `n`. -/
  commitLength : ℕ → ℕ
  /-- Commitment function taking receiver string `r`, bit `b`, and `n`-bit seed `seed`. -/
  commit : List Bool → Bool → List Bool → List Bool
  /-- Verification of an opening `(b, seed)` against `(n, r, c)`. -/
  verify : ℕ → List Bool → List Bool → Bool → List Bool → Bool
  /-- `challengeLength` is computable in plain polynomial time in unary. -/
  polyTime_challengeLength : ComputableInPolyTime challengeLength encUnary encUnary
  /-- `commitLength` is computable in plain polynomial time in unary. -/
  polyTime_commitLength : ComputableInPolyTime commitLength encUnary encUnary
  /-- `commit` is computable in plain polynomial time. -/
  polyTime_commit :
    ComputableInPolyTime (fun ⟨r, b, seed⟩ => commit r b seed)
      (encPair encBits encBitOpening) encBits
  /-- `verify` is computable in plain polynomial time. -/
  polyTime_verify :
    ComputableInPolyTime
      (fun ⟨n, r, c, b, seed⟩ => verify n r c b seed)
      (encPair encUnary (encPair encBits (encPair encBits encBitOpening))) encBool
  /-- Honest commitments have length `commitLength n` when `seed.length = n`. -/
  length_commit : ∀ (n : ℕ) (r : List Bool) (b : Bool) (seed : List Bool),
    seed.length = n → (commit r b seed).length = commitLength n
  /-- Correctness: an honest commitment is accepted by `verify`. -/
  verify_commit : ∀ (n : ℕ) (r : List Bool) (b : Bool) (seed : List Bool),
    seed.length = n → verify n r (commit r b seed) b seed = true
  /-- Soundness of `verify`: if `verify n r c b seed = true`, then `seed.length = n` and
  `c = commit r b seed`. -/
  eq_commit_of_verify : ∀ {n : ℕ} {r c : List Bool} {b : Bool} {seed : List Bool},
    verify n r c b seed = true → seed.length = n ∧ c = commit r b seed
  /-- Statistical binding: the probability over a uniform receiver challenge `r` of length
  `challengeLength n` that two `n`-bit seeds open to `false` and `true` with the same commitment
  is negligible in `n`. -/
  statistical_binding :
    Negligible (fun n =>
      ((BitString.uniformList (challengeLength n)).toOuterMeasure
        {r | ¬ ∀ s₀ s₁ : List Bool, s₀.length = n → s₁.length = n →
          commit r false s₀ ≠ commit r true s₁}).toNNReal)
  /-- Computational hiding against a randomized stateful PPT receiver: for every polynomial-time
  auxiliary family `aux : ℕ → List Bool`, no strict PPT `CommitmentReceiver` can distinguish
  commitments to its first chosen bit (`bit = false`) from commitments to its second chosen bit
  (`bit = true`) with non-negligible advantage. -/
  stateful_hiding : StatefulHiding commit

/-- Deterministic-family computational hiding derived from `BitCommitmentScheme.stateful_hiding`:
for every deterministic polynomial-time family of receiver strings `r : ℕ → List Bool` and any two
deterministic polynomial-time families of committed bits `b₀ b₁ : ℕ → Bool`, the commitment
ensembles for `b₀` and `b₁` are computationally indistinguishable against uniform strict PPT
distinguishers. -/
theorem BitCommitmentScheme.computational_hiding (h : BitCommitmentScheme) :
    ∀ (r : ℕ → List Bool) (b₀ b₁ : ℕ → Bool),
      ComputableInPolyTime r encUnary encBits →
      ComputableInPolyTime b₀ encUnary encBool →
      ComputableInPolyTime b₁ encUnary encBool →
      ComputationallyIndistinguishable
        (fun n => (BitString.uniformList n).map (h.commit (r n) (b₀ n)))
        (fun n => (BitString.uniformList n).map (h.commit (r n) (b₁ n))) :=
  fun _ _ _ hr hb₀ hb₁ => h.stateful_hiding.computational_hiding hr hb₀ hb₁

/-- **Naor's bit commitment scheme** built from any pseudorandom generator with stretch at least
`3 * n` [Naor1991]. -/
def PseudorandomGenerator.naorBitCommitment
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ n, 3 * n ≤ length n) :
    BitCommitmentScheme where
  challengeLength := length
  commitLength := length
  commit := naorCommit generator
  verify := naorVerify generator
  polyTime_challengeLength := PRG.polyTime_length hG.polyTime hG.length_eq
  polyTime_commitLength := PRG.polyTime_length hG.polyTime hG.length_eq
  polyTime_commit :=
    let hrest := ComputableInPolyTime.snd encBits (encPair encBool encBits)
    computableInPolyTime_naorCommit hG.polyTime
      (ComputableInPolyTime.fst encBits (encPair encBool encBits)) hrest.fst' hrest.snd'
  polyTime_verify :=
    let E3 := encPair encBits (encPair encBool encBits)
    let E4 := encPair encBits E3
    let h1 := ComputableInPolyTime.snd encUnary E4
    let h2 := h1.snd'
    let h3 := h2.snd'
    computableInPolyTime_naorVerify hG.polyTime
      (ComputableInPolyTime.fst encUnary E4) h1.fst' h2.fst' h3.fst' h3.snd'
  length_commit _ _ _ _ hseed := by rw [length_naorCommit, hG.length_eq, hseed]
  verify_commit _ r b _ hseed := naorVerify_naorCommit r b hseed
  eq_commit_of_verify h := eq_naorCommit_of_naorVerify h
  statistical_binding := negligible_naorBindingError hG.length_eq hstretch
  stateful_hiding := hG.naorStatefulHiding

/-- **Existence of bit commitments from one-way functions** [Naor1991]: if a one-way function
exists, then there exists a statistically binding, computationally hiding bit commitment scheme
(with hiding against randomized stateful PPT receivers, `BitCommitmentScheme.stateful_hiding`). -/
theorem OneWay.exists_bitCommitmentScheme {f : List Bool → List Bool} (hf : OneWay f) :
    Nonempty BitCommitmentScheme := by
  obtain ⟨generator, hG⟩ := hf.exists_pseudorandomGenerator_three_mul
  exact ⟨hG.naorBitCommitment (fun n => Nat.le_succ (3 * n))⟩

end Cslib.Crypto
