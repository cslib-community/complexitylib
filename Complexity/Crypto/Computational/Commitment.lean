/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Foundations.Data.BitString.List.Operations
public import Complexity.Crypto.Computational.Encryption.Basic
public import Complexity.Crypto.Computational.OneWayToPRG
public import Complexity.Crypto.Computational.Stretch
public import Complexity.Crypto.Computational.Hybrid.Sequence
public import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF.Uniform
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Probability.BitString.List
import Complexity.Tactic.PPT

/-!
# Naor's bit commitment scheme from pseudorandom generators

Naor's statistically binding, computationally hiding bit commitment scheme [Naor1991] commits to a
bit `b : Bool` under a receiver string `r : List Bool` and a uniform seed `seed : List Bool` of
length `n` using a pseudorandom generator `generator`:
`naorCommit generator r b seed` outputs `generator seed` when `b = false`, and
`BitString.listXor (generator seed).length [generator seed, r]` when `b = true`.

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
* `Cslib.Crypto.BitCommitmentScheme`: a two-message statistically binding, computationally hiding
  bit commitment scheme.
* `Cslib.Crypto.CommitmentScheme`, `Cslib.Crypto.CommitmentScheme.hidingForKey`,
  `Cslib.Crypto.CommitmentScheme.hidingGame`, `Cslib.Crypto.CommitmentScheme.StatisticalHiding`,
  `Cslib.Crypto.CommitmentScheme.ComputationalHiding`,
  `Cslib.Crypto.CommitmentScheme.isBindingCollision`,
  `Cslib.Crypto.CommitmentScheme.bindingGame`, `Cslib.Crypto.CommitmentScheme.Binding`: general
  public-parameter commitment scheme `(C, V)` reusing `Encryption.WordAdversary`, with its
  chosen-message hiding and binding experiments ([BonehShoup2023], Section 8.12, Definition 8.8).

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
* `Cslib.Crypto.CommitmentScheme.hidingForKey_eq_of_map_fst_commitDist_eq`,
  `Cslib.Crypto.CommitmentScheme.advantage_hidingForKey_eq_zero`,
  `Cslib.Crypto.CommitmentScheme.StatisticalHiding.computationalHiding`: general hiding lemmas for
  `CommitmentScheme`.

## References

* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001],
  Section 4.4.1.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 8.12 (Definition 8.8, p. 344).
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
  have htarget : ComputableTidilyInPolyTime (fun n => 3 * n + 1) encUnary encUnary := by fun_prop
  exact ⟨_, hg.amplify (fun n => 3 * n + 1) (.of_tidy htarget) (fun n => by lia)⟩

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
  cases b <;> simp [naorCommit]

/-- Naor commitment is computable in plain polynomial time when its inputs are. -/
@[fun_prop]
theorem computableInPolyTime_naorCommit {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {r : α → List Bool} {b : α → Bool} {seed : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hr : ComputableInPolyTime r input encBits)
    (hb : ComputableInPolyTime b input encBool)
    (hseed : ComputableInPolyTime seed input encBits) :
    ComputableInPolyTime (fun a => naorCommit generator (r a) (b a) (seed a))
      input encBits := by
  have hg := hg.tidy
  have hr := hr.tidy
  have hb := hb.tidy
  have hseed := hseed.tidy
  refine .of_tidy ?_
  unfold naorCommit
  fun_prop

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
  have hr := hr.tidy
  have hb := hb.tidy
  have hmap : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => naorCommit id (r p.1) (b p.1) p.2)
      (encPair encUnary encBits) encBits := by
    apply ComputableInPolyTime.tidy
    apply computableInPolyTime_naorCommit <;> exact .of_tidy (by fun_prop)
  have hind := hG.indistinguishable.map (f := fun n y => naorCommit id (r n) (b n) y)
    (.of_tidy hmap)
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
      (fun p => receiver.guess p.1 p.2.1 p.2.2)

/-- The two-stage commitment-hiding experiment against a stateful receiver `receiver` with
auxiliary input `aux` and hidden bit selector `bit : Bool` at security parameter `n`.
The receiver outputs `((r, (b₀, b₁)), state) ← receiver.choose n aux`, the challenger samples a
uniform `n`-bit seed `seed ← BitString.sampleList n` and commits to `b₁` (when `bit = true`) or
`b₀` (when `bit = false`) under `r`, and `receiver.guess n state c` outputs a guess bit. -/
noncomputable def commitmentHidingGame (commit : List Bool → Bool → List Bool → List Bool)
    (receiver : CommitmentReceiver) (aux : List Bool) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let choice ← receiver.choose n aux
  let seed ← BitString.sampleList n
  receiver.guess n choice.2
    (commit choice.1.1 (if bit then choice.1.2.2 else choice.1.2.1) seed)

/-- The commitment-hiding experiment runs in strict PPT on `(n, aux, bit)` whenever `commit` is
computable in plain polynomial time and `receiver` is strict PPT. -/
theorem isPPTOn_commitmentHidingGame {commit : List Bool → Bool → List Bool → List Bool}
    {receiver : CommitmentReceiver}
    (hcommit : ComputableInPolyTime
      (fun p : List Bool × Bool × List Bool => commit p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBool encBits)) encBits)
    (hR : receiver.IsPPT) :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBool
      (fun p => commitmentHidingGame commit receiver p.2.1 p.2.2 p.1) := by
  have hcommit_tidy := hcommit.tidy
  have hchoose := hR.choose
  have hguess := hR.guess
  unfold commitmentHidingGame
  ppt

/-- For any fixed challenge selector `bit`, the commitment-hiding experiment is a strict PPT
indexed family on `(n, aux)`. -/
theorem isPPT_commitmentHidingGame {commit : List Bool → Bool → List Bool → List Bool}
    {receiver : CommitmentReceiver}
    (hcommit : ComputableInPolyTime
      (fun p : List Bool × Bool × List Bool => commit p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBool encBits)) encBits)
    (hR : receiver.IsPPT) (bit : Bool) :
    IsPPT encBool (fun n aux => commitmentHidingGame commit receiver aux bit n) := by
  have hcommit_tidy := hcommit.tidy
  have hchoose := hR.choose
  have hguess := hR.guess
  unfold commitmentHidingGame
  ppt

/-- For any polynomial-time auxiliary family `aux`, the commitment-hiding experiment is strict PPT
in the unary security parameter `n`. -/
theorem isPPTOn_commitmentHidingGame_aux {commit : List Bool → Bool → List Bool → List Bool}
    {receiver : CommitmentReceiver} {aux : ℕ → List Bool}
    (hcommit : ComputableInPolyTime
      (fun p : List Bool × Bool × List Bool => commit p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBool encBits)) encBits)
    (hR : receiver.IsPPT)
    (haux : ComputableInPolyTime aux encUnary encBits) (bit : Bool) :
    IsPPTOn encUnary encBool (fun n => commitmentHidingGame commit receiver (aux n) bit n) := by
  have hcommit_tidy := hcommit.tidy
  have haux_tidy := haux.tidy
  have hchoose := hR.choose
  have hguess := hR.guess
  unfold commitmentHidingGame
  ppt

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
  h (fun _ => []) (by fun_prop)

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
    (CommitmentReceiver.ofDeterministic r b₀ b₁ D).IsPPT := by
  have hr_tidy := hr.tidy
  have hb₀_tidy := hb₀.tidy
  have hb₁_tidy := hb₁.tidy
  constructor
  · dsimp only [CommitmentReceiver.ofDeterministic]
    ppt
  · dsimp only [CommitmentReceiver.ofDeterministic]
    ppt

@[simp] theorem eval_commitmentHidingGame_ofDeterministic
    (commit : List Bool → Bool → List Bool → List Bool)
    (r : ℕ → List Bool) (b₀ b₁ : ℕ → Bool) (D : Distinguisher)
    (aux : List Bool) (bit : Bool) (n : ℕ) :
    ProbComp.eval
        (commitmentHidingGame commit (CommitmentReceiver.ofDeterministic r b₀ b₁ D) aux bit n) =
      distinguishingGame
        ((BitString.uniformList n).map (commit (r n) (if bit then b₁ n else b₀ n))) (D n) := by
  simp [commitmentHidingGame, CommitmentReceiver.ofDeterministic, distinguishingGame,
    PMF.bind_map, Function.comp_def]

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
    receiver.guess n choice.2
      (naorCommit id choice.1.1 (if bit then choice.1.2.2 else choice.1.2.1) pad)

/-- `naorReceiverDistinguisher receiver aux bit` is a strict PPT distinguisher whenever `receiver`
is strict PPT and `aux` is computable in plain polynomial time. -/
theorem isPPT_naorReceiverDistinguisher {receiver : CommitmentReceiver}
    {aux : ℕ → List Bool} (hR : receiver.IsPPT)
    (haux : ComputableInPolyTime aux encUnary encBits) (bit : Bool) :
    IsPPT encBool (naorReceiverDistinguisher receiver aux bit) := by
  have haux_tidy := haux.tidy
  have hchoose := hR.choose
  have hguess := hR.guess
  unfold naorReceiverDistinguisher naorCommit
  ppt

/-- Running `commitmentHidingGame (naorCommit generator)` against `receiver` coincides with running
`naorReceiverDistinguisher receiver aux bit` against the PRG output `generatorEnsemble generator n`.
-/
theorem eval_commitmentHidingGame_naorCommit (generator : List Bool → List Bool)
    (receiver : CommitmentReceiver) (aux : ℕ → List Bool) (bit : Bool) (n : ℕ) :
    ProbComp.eval (commitmentHidingGame (naorCommit generator) receiver (aux n) bit n) =
      distinguishingGame (generatorEnsemble generator n)
        (naorReceiverDistinguisher receiver aux bit n) := by
  unfold commitmentHidingGame distinguishingGame generatorEnsemble naorReceiverDistinguisher
  simp only [ProbComp.eval_bind, BitString.eval_sampleList, PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def]
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
  unfold distinguishingGame naorReceiverDistinguisher
  simp only [ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  rw [PMF.bind_comm]
  congr 1
  funext choice
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
    exact h (List.ofFn s₀) (List.ofFn s₁) (by simp) (by simp)
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
    simpa using hlen (List.ofFn s₁)
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
    simpa [BitString.ofList_ofFn] using mem_image_naorBadShift_of_not_naorBinding hlen hr.2
  calc
    (Finset.univ.filter (fun r : BitString (length n) =>
        ¬ NaorBinding generator n (List.ofFn r))).card
      ≤ (Finset.univ.image (naorBadShift generator (length n) n)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (BitString n × BitString n)).card := Finset.card_image_le
    _ = 2 ^ (2 * n) := by
        simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, ← pow_add, two_mul]

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
      input encBits := by
  have hg := hg.tidy
  have hr := hr.tidy
  have hopen := hopen.tidy
  have hb := hb.tidy
  have hseed := hseed.tidy
  have hpad := hpad.tidy
  refine .of_tidy ?_
  have hopened := (computableInPolyTime_naorCommit
    (.of_tidy hg) (.of_tidy hr) (.of_tidy hb) (.of_tidy hseed)).tidy
  have hclosed := (computableInPolyTime_naorCommit
    (.of_tidy ComputableTidilyInPolyTime.id') (.of_tidy hr) (.of_tidy hb) (.of_tidy hpad)).tidy
  unfold naorCommitAt
  fun_prop

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
    cases openFlag <;> simp [naorCommitAt]
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
  | cons b bits ih => simp [naorMaskBits, ih]

theorem getD_naorMaskBits (openFlags bits : List Bool) (i : ℕ) :
    (naorMaskBits openFlags bits).getD i false =
      (openFlags.getD i false && bits.getD i false) := by
  induction bits generalizing openFlags i with
  | nil => simp [naorMaskBits]
  | cons b bits ih =>
    cases i with
    | zero => cases openFlags <;> simp [naorMaskBits]
    | succ i =>
      cases openFlags with
      | nil => simpa [naorMaskBits] using ih [] i
      | cons flag flags => simpa [naorMaskBits] using ih flags i

theorem naorMaskBits_eq_map (openFlags bits : List Bool) :
    naorMaskBits openFlags bits =
      (List.range bits.length).map (fun i => openFlags.getD i false && bits.getD i false) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have h := getD_naorMaskBits openFlags bits i
  simpa [List.getD, List.getElem?_eq_getElem hi] using h

@[fun_prop]
theorem computableInPolyTime_naorMaskBits {α : Type} {input : α ↪ List Bool}
    {openFlags bits : α → List Bool}
    (hopen : ComputableInPolyTime openFlags input encBits)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => naorMaskBits (openFlags a) (bits a))
      input encBits := by
  have hopen := hopen.tidy
  have hbits := hbits.tidy
  refine .of_tidy ?_
  have h : (fun a => naorMaskBits (openFlags a) (bits a)) =
      fun a => (List.range (bits a).length).map
        (fun i => ((openFlags a)[i]?.getD false) && ((bits a)[i]?.getD false)) := by
    funext a
    simp only [naorMaskBits_eq_map, List.getD_eq_getElem?_getD]
  rw [h]
  fun_prop

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
  | cons b bits ih => simp [naorCommitSplit, ih]

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
      cases openFlags <;> cases seeds <;> cases pads <;> simp [naorCommitSplit]
    | succ i =>
      have hi' : i < bits.length := Nat.lt_of_succ_lt_succ hi
      have hrec := ih openFlags.tail seeds.tail pads.tail i hi'
      have hopen : openFlags.tail.getD i false = openFlags.getD (i + 1) false := by
        cases openFlags <;> simp
      have hseed : seeds.tail.getD i [] = seeds.getD (i + 1) [] := by
        cases seeds <;> simp
      have hpad : pads.tail.getD i [] = pads.getD (i + 1) [] := by
        cases pads <;> simp
      simpa [naorCommitSplit, hopen, hseed, hpad] using hrec

theorem naorCommitSplit_eq_map (generator : List Bool → List Bool) (r : List Bool)
    (openFlags bits : List Bool) (seeds pads : List (List Bool)) :
    naorCommitSplit generator r openFlags bits seeds pads =
      (List.range bits.length).map (fun i =>
        naorCommitAt generator r (openFlags.getD i false) (bits.getD i false)
          (seeds.getD i []) (pads.getD i [])) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hlt : i < bits.length := by simpa using hi
  have h := getD_naorCommitSplit generator r openFlags bits seeds pads i hlt
  simpa [List.getD, List.getElem?_eq_getElem hi] using h

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
  have hg := hg.tidy
  have hr := hr.tidy
  have hopen := hopen.tidy
  have hbits := hbits.tidy
  have hseeds := hseeds.tidy
  have hpads := hpads.tidy
  refine .of_tidy ?_
  have h : (fun a => naorCommitSplit generator (r a) (openFlags a) (bits a) (seeds a) (pads a)) =
      fun a => (List.range (bits a).length).map (fun i =>
        naorCommitAt generator (r a) ((openFlags a)[i]?.getD false) ((bits a)[i]?.getD false)
          ((seeds a)[i]?.getD []) ((pads a)[i]?.getD [])) := by
    funext a
    simp only [naorCommitSplit_eq_map, List.getD_eq_getElem?_getD]
  rw [h]
  apply ComputableTidilyInPolyTime.mapWithInput (encA := encUnary) (by fun_prop)
  apply ComputableInPolyTime.tidy
  apply computableInPolyTime_naorCommitAt (.of_tidy hg) <;> exact .of_tidy (by fun_prop)

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
    simp only [List.length_cons, OracleComp.replicate_succ, ProbComp.eval_map,
      ProbComp.eval_bind, BitString.eval_sampleList, PMF.map_bind, PMF.map_comp,
      Function.comp_def, naorCommitSplit, naorMaskBits, List.headD_cons, List.tail_cons]
    have hhead := uniformList_map_naorCommitAt m generator r (openFlags.headD false) b
      (seeds.headD [])
    have htail := ih openFlags.tail seeds.tail
    simp only [ProbComp.eval_map] at htail
    calc
      (BitString.uniformList m).bind (fun u =>
          (ProbComp.eval (OracleComp.replicate bits.length (BitString.sampleList m))).map
            (fun rest => naorCommitAt generator r (openFlags.headD false) b (seeds.headD []) u ::
              naorCommitSplit generator r openFlags.tail bits seeds.tail rest))
        = ((BitString.uniformList m).map
            (naorCommitAt generator r (openFlags.headD false) b (seeds.headD []))).bind
            (fun head =>
              ((ProbComp.eval (OracleComp.replicate bits.length (BitString.sampleList m))).map
                (naorCommitSplit generator r openFlags.tail bits seeds.tail)).map
                  (head :: ·)) := by
          simp only [PMF.bind_map, PMF.map_comp, Function.comp_def]
      _ = ((BitString.uniformList m).map
            (naorCommitAt generator r (openFlags.headD false)
              (openFlags.headD false && b) (seeds.headD []))).bind
            (fun head =>
              ((ProbComp.eval (OracleComp.replicate bits.length (BitString.sampleList m))).map
                (naorCommitSplit generator r openFlags.tail
                  (naorMaskBits openFlags.tail bits) seeds.tail)).map
                  (head :: ·)) := by
          rw [hhead, htail]
      _ = _ := by
          simp only [PMF.bind_map, PMF.map_comp, Function.comp_def]

/-- `naorMaskBits` distributes over list append when the first segments have equal length. -/
theorem naorMaskBits_append {flags₁ flags₂ bits₁ bits₂ : List Bool}
    (h : flags₁.length = bits₁.length) :
    naorMaskBits (flags₁ ++ flags₂) (bits₁ ++ bits₂) =
      naorMaskBits flags₁ bits₁ ++ naorMaskBits flags₂ bits₂ := by
  induction bits₁ generalizing flags₁ with
  | nil =>
    cases flags₁ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons b bits₁ ih =>
    cases flags₁ with
    | nil => simp at h
    | cons f flags₁ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [naorMaskBits, ih h]

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
    | nil => simp at hflags
    | cons f flags₁ =>
      cases seeds₁ with
      | nil => simp at hseeds
      | cons s seeds₁ =>
        cases pads₁ with
        | nil => simp at hpads
        | cons p pads₁ =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hflags hseeds hpads
          simp [naorCommitSplit, ih hflags hseeds hpads]

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
  | cons _ bits ih => simp [naorSelectSeeds, ih]

theorem length_mem_naorSelectSeeds {s : ℕ} {openFlags bits : List Bool}
    {seeds : List (List Bool)} {w : List Bool}
    (hw : w ∈ naorSelectSeeds s openFlags bits seeds) : w.length = s := by
  induction bits generalizing openFlags seeds w with
  | nil => simp [naorSelectSeeds] at hw
  | cons _ bits ih =>
    simp only [naorSelectSeeds, List.mem_cons] at hw
    rcases hw with rfl | hw
    · split_ifs <;> simp
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
      cases openFlags <;> cases seeds <;> simp [naorSelectSeeds]
    | succ i =>
      have hi' : i < bits.length := Nat.lt_of_succ_lt_succ hi
      have hrec := ih openFlags.tail seeds.tail i hi'
      have hopen : openFlags.tail.getD i false = openFlags.getD (i + 1) false := by
        cases openFlags <;> simp
      have hseed : seeds.tail.getD i [] = seeds.getD (i + 1) [] := by
        cases seeds <;> simp
      simpa [naorSelectSeeds, hopen, hseed] using hrec

theorem naorSelectSeeds_eq_map (s : ℕ) (openFlags bits : List Bool)
    (seeds : List (List Bool)) :
    naorSelectSeeds s openFlags bits seeds =
      (List.range bits.length).map (fun i =>
        if openFlags.getD i false then BitString.listRow s 0 (seeds.getD i [])
        else List.replicate s false) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hlt : i < bits.length := by simpa using hi
  have h := getD_naorSelectSeeds s openFlags bits seeds i hlt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  exact h

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
  have hs := hs.tidy
  have hopen := hopen.tidy
  have hbits := hbits.tidy
  have hseeds := hseeds.tidy
  refine .of_tidy ?_
  have h : (fun a => naorSelectSeeds (s a) (openFlags a) (bits a) (seeds a)) =
      fun a => (List.range (bits a).length).map (fun i =>
        if (openFlags a)[i]?.getD false then
          BitString.listRow (s a) 0 ((seeds a)[i]?.getD [])
        else List.replicate (s a) false) := by
    funext a
    simp only [naorSelectSeeds_eq_map, List.getD_eq_getElem?_getD]
  rw [h]
  fun_prop

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
    · cases openFlags.headD false <;> simp [naorCommitAt, naorCommit_eq_comp_id]
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
  | nil => simp [naorSelectPads, naorSelectSeeds]
  | cons b bits ih =>
    simp only [List.length_cons, OracleComp.replicate_succ, ProbComp.eval_map,
      ProbComp.eval_bind, BitString.eval_sampleList, PMF.map_bind, PMF.bind_map,
      PMF.map_comp, Function.comp_def, PMF.bind_bind, ProbComp.eval_pure,
      naorSelectPads, naorSelectSeeds, List.replicate_succ, List.headD_cons, List.tail_cons,
      List.tail_nil, ↓reduceIte]
    have htail := ih openFlags.tail
    simp only [ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure] at htail
    let D_s := ProbComp.eval (OracleComp.replicate bits.length (BitString.sampleList s))
    let D_p := ProbComp.eval
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
      simpa only [PMF.map_bind, PMF.pure_map, PMF.map_comp, Function.comp_def, D_s, D_p]
        using hcongr
    have hswap : (BitString.uniformList s).bind (fun u => D_s.bind (fun rest_s =>
        (BitString.uniformList s).bind (fun u' => D_p.bind (fun rest_p => PMF.pure
          ((if openFlags.headD false then generator u else generator u') ::
            naorSelectPads generator openFlags.tail bits rest_s rest_p,
            (if openFlags.headD false then BitString.listRow s 0 u else List.replicate s false) ::
            naorSelectSeeds s openFlags.tail bits rest_s))))) =
        (BitString.uniformList s).bind (fun u => (BitString.uniformList s).bind (fun u' =>
          D_s.bind (fun rest_s => D_p.bind (fun rest_p => PMF.pure
            ((if openFlags.headD false then generator u else generator u') ::
              naorSelectPads generator openFlags.tail bits rest_s rest_p,
              (if openFlags.headD false then BitString.listRow s 0 u else List.replicate s false) ::
              naorSelectSeeds s openFlags.tail bits rest_s))))) := by
      congr 1
      funext u
      exact PMF.bind_comm _ _ _
    change (BitString.uniformList s).bind (fun u => D_s.bind (fun rest_s =>
        (BitString.uniformList s).bind (fun u' => D_p.bind (fun rest_p => PMF.pure
          ((if openFlags.headD false then generator u else generator u') ::
            naorSelectPads generator openFlags.tail bits rest_s rest_p,
            (if openFlags.headD false then BitString.listRow s 0 u else List.replicate s false) ::
            naorSelectSeeds s openFlags.tail bits rest_s))))) = _
    rw [hswap]
    simp only [hstep]
    cases openFlags.headD false
    · simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_const, D_s]
    · simp only [↓reduceIte, PMF.bind_const, D_s]

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
      input encBool := by
  have hcommit := (computableInPolyTime_naorCommit hg hr hb hseed).tidy
  have hn := hn.tidy
  have hc := hc.tidy
  have hseed := hseed.tidy
  refine .of_tidy ?_
  dsimp only [naorVerify]
  fun_prop

theorem naorVerify_naorCommit {generator : List Bool → List Bool} {n : ℕ}
    (r : List Bool) (b : Bool) {seed : List Bool} (hseed : seed.length = n) :
    naorVerify generator n r (naorCommit generator r b seed) b seed = true := by
  simp [naorVerify, hseed]

theorem eq_naorCommit_of_naorVerify {generator : List Bool → List Bool} {n : ℕ}
    {r c : List Bool} {b : Bool} {seed : List Bool}
    (h : naorVerify generator n r c b seed = true) :
    seed.length = n ∧ c = naorCommit generator r b seed := by
  simpa [naorVerify] using h

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
    ComputableInPolyTime (fun p : List Bool × Bool × List Bool => commit p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBool encBits)) encBits
  /-- `verify` is computable in plain polynomial time. -/
  polyTime_verify :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × Bool × List Bool =>
        verify p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair encUnary (encPair encBits (encPair encBits (encPair encBool encBits)))) encBool
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
  polyTime_challengeLength := (PRG.polyTime_length hG.polyTime hG.length_eq)
  polyTime_commitLength := (PRG.polyTime_length hG.polyTime hG.length_eq)
  polyTime_commit := by
    have hg := hG.polyTime.tidy
    fun_prop
  polyTime_verify := by
    have hg := hG.polyTime.tidy
    fun_prop
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

/-! ### Public-parameter commitment schemes ([BonehShoup2023], Section 8.12) -/

/-- A commitment scheme `(C, V)` with public parameters ([BonehShoup2023], Section 8.12, p. 344,
and Definition 8.8):
* `encodeKey k`: the encoded public parameter string presented to the adversary for key `k`.
  This encoding is injective: equal public strings determine the same key and hence the same
  valid messages, commitment distributions, and verification results.
  Injectivity is an information-theoretic condition; decoding and evaluating honest operations
  from this string need separate efficiency certificates.
* `ValidMessage k m`: predicate characterizing valid message words `m` in the message space for key
  `k`.
* `commitDist k msg`: the distribution of `(c, o)` (encoded commitment string `c` and encoded
  opening string `o`) produced by `C(msg)` under key `k`. `commitDist` is modeled as a `PMF` rather
  than a `ProbComp` so that group-based schemes such as Pedersen commitment can use the exact
  uniform distribution on `ZMod q` (matching `DiscreteLog`'s `PMF` setup; strict-PPT `ProbComp`
  machines sample `ZMod q` only approximately via `sampleModNat`).
* `verify k m c o`: the deterministic verification algorithm `V(m, c, o)` returning `true` to accept
  or `false` to reject. Neither `commitDist` nor `verify` bundles a polynomial-time complexity
  certificate in `CommitmentScheme`, keeping the general scheme interface at the distributional
  layer; concrete instantiations certify their encoded evaluation and reduction algorithms
  separately (e.g., `computableInPolyTime_encodePedersenCommit` and
  `isPPTOn_pedersenToDLAdversary`).
* `validMessage_of_verify` and `verify_of_mem_support`: `verify` accepts only valid message words
  and accepts every `(c, o)` in the support of `commitDist k m` for any valid message word `m`.

Chosen-message hiding reuses `Encryption.WordAdversary` (`Encryption.AdversaryOf (List Bool)` from
`Complexity/Crypto/Computational/Encryption/Basic.lean`), matching Boneh–Shoup's semantic-security
formulation of commitment hiding. -/
structure CommitmentScheme (Key : Type) where
  /-- Faithful encoding of the entire public parameter presented to the adversary. -/
  encodeKey : Key ↪ List Bool
  /-- Predicate characterizing valid message words in the message space for key `k`. -/
  ValidMessage : Key → List Bool → Prop
  /-- Distribution of `(c, o)` (encoded commitment string and encoded opening string) for message
  word `msg` under key `k`. -/
  commitDist : Key → List Bool → PMF (List Bool × List Bool)
  /-- Verification algorithm `V(m, c, o)` ([BonehShoup2023], Section 8.12, p. 344). -/
  verify : Key → List Bool → List Bool → List Bool → Bool
  /-- Only valid message words are accepted by `verify`. -/
  validMessage_of_verify : ∀ k m c o, verify k m c o = true → ValidMessage k m
  /-- Correctness: every `(c, o)` in the support of `commitDist k m` for a valid message word `m`
  is accepted by `verify k m co.1 co.2`. -/
  verify_of_mem_support : ∀ k m co, ValidMessage k m → co ∈ (commitDist k m).support →
    verify k m co.1 co.2 = true

/-- The chosen-message hiding experiment ([BonehShoup2023], Section 8.12, p. 344, and
Definition 8.8) at a fixed commitment key `k : Key` for hidden bit `bit : Bool`: the adversary
receives `S.encodeKey k`, chooses `((m₀, m₁), st)`, and receives the commitment string `c = co.1`
(without the opening `co.2`) for `co ← S.commitDist k m_bit`. Following Boneh–Shoup Section 8.12
(`m₀, m₁ ∈ M`), the challenger commits to `m_bit` when both chosen words satisfy `S.ValidMessage k`,
and defaults to `m₀` otherwise so that invalid challenge pairs produce identical distributions in
both worlds. -/
noncomputable def CommitmentScheme.hidingForKey {Key : Type}
    (S : CommitmentScheme Key) (k : Key)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let choice ← ProbComp.eval (adversary.choose n (S.encodeKey k))
  let msg := open Classical in
    if bit ∧ S.ValidMessage k choice.1.1 ∧ S.ValidMessage k choice.1.2 then choice.1.2
    else choice.1.1
  let co ← S.commitDist k msg
  ProbComp.eval (adversary.guess n choice.2 co.1)

/-- If the commitment-string marginal `(S.commitDist k msg).map Prod.fst` is independent of the
message word, then `S.hidingForKey k` produces the exact same output distribution for any two hidden
bits `b₁` and `b₂`, against every (even computationally unbounded) `Encryption.WordAdversary`. -/
theorem CommitmentScheme.hidingForKey_eq_of_map_fst_commitDist_eq {Key : Type}
    (S : CommitmentScheme Key) {k : Key}
    (hk : ∀ msg₁ msg₂ : List Bool,
      (S.commitDist k msg₁).map Prod.fst = (S.commitDist k msg₂).map Prod.fst)
    (adversary : Encryption.WordAdversary) (b₁ b₂ : Bool) (n : ℕ) :
    S.hidingForKey k adversary b₁ n = S.hidingForKey k adversary b₂ n := by
  simp only [CommitmentScheme.hidingForKey, PMF.monad_bind_eq_bind]
  congr 1; funext choice
  have hbind (msg : List Bool) :
      (S.commitDist k msg).bind (fun co => ProbComp.eval (adversary.guess n choice.2 co.1)) =
        ((S.commitDist k msg).map Prod.fst).bind
          (fun c => ProbComp.eval (adversary.guess n choice.2 c)) := by
    rw [PMF.bind_map]
    rfl
  rw [hbind, hbind, hk]

/-- When `(S.commitDist k msg).map Prod.fst` is independent of the message word, the hiding
advantage of any (computationally unbounded) adversary at key `k` between `bit = false` and
`bit = true` is `0`. -/
theorem CommitmentScheme.advantage_hidingForKey_eq_zero {Key : Type}
    (S : CommitmentScheme Key) {k : Key}
    (hk : ∀ msg₁ msg₂ : List Bool,
      (S.commitDist k msg₁).map Prod.fst = (S.commitDist k msg₂).map Prod.fst)
    (adversary : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage (S.hidingForKey k adversary false n)
      (S.hidingForKey k adversary true n) = 0 := by
  rw [S.hidingForKey_eq_of_map_fst_commitDist_eq hk adversary false true n, Game.advantage_self]

/-- The chosen-message hiding experiment ([BonehShoup2023], Section 8.12, p. 344, and
Definition 8.8) under a key distribution `keyDist : ℕ → PMF Key`. -/
noncomputable def CommitmentScheme.hidingGame {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let k ← keyDist n
  S.hidingForKey k adversary bit n

/-- Statistical hiding ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8): every (even
computationally unbounded) `Encryption.WordAdversary` has negligible distinguishing advantage in
`S.hidingGame keyDist`. -/
def CommitmentScheme.StatisticalHiding {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key) : Prop :=
  Game.Indistinguishable
    (fun adversary n => S.hidingGame keyDist adversary false n)
    (fun adversary n => S.hidingGame keyDist adversary true n)
    (fun _ => True)

/-- Computational hiding ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8): every
uniform strict PPT `Encryption.WordAdversary` has negligible distinguishing advantage in
`S.hidingGame keyDist`. -/
def CommitmentScheme.ComputationalHiding {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key) : Prop :=
  Game.Indistinguishable
    (fun adversary n => S.hidingGame keyDist adversary false n)
    (fun adversary n => S.hidingGame keyDist adversary true n)
    Encryption.WordAdversary.IsPPT

/-- Statistical hiding implies computational hiding against uniform strict PPT adversaries. -/
theorem CommitmentScheme.StatisticalHiding.computationalHiding {Key : Type}
    {S : CommitmentScheme Key} {keyDist : ℕ → PMF Key}
    (h : S.StatisticalHiding keyDist) :
    S.ComputationalHiding keyDist :=
  fun adversary _ => h adversary trivial

/-- Boolean predicate testing whether `(c, (m₀, o₀), (m₁, o₁))` is a valid binding collision under
`S.verify k` ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8): `m₀ ≠ m₁` and both
openings `(m₀, o₀)` and `(m₁, o₁)` are accepted by `S.verify k` for the commitment string `c`. -/
def CommitmentScheme.isBindingCollision {Key : Type} (S : CommitmentScheme Key) (k : Key)
    (out : List Bool × (List Bool × List Bool) × (List Bool × List Bool)) : Bool :=
  decide (out.2.1.1 ≠ out.2.2.1) &&
    S.verify k out.2.1.1 out.1 out.2.1.2 &&
    S.verify k out.2.2.1 out.1 out.2.2.2

/-- The commitment binding experiment ([BonehShoup2023], Section 8.12, p. 344, and
Definition 8.8): draw `k ← keyDist n`, give `S.encodeKey k` to `adversary`, and accept when the
output `(c, (m₀, o₀), (m₁, o₁))` satisfies `S.isBindingCollision k` (`m₀ ≠ m₁` and both openings
verify under `S.verify k`). -/
noncomputable def CommitmentScheme.bindingGame {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key)
    (adversary : ℕ → List Bool →
      ProbComp (List Bool × (List Bool × List Bool) × (List Bool × List Bool)))
    (n : ℕ) : Game := do
  let k ← keyDist n
  let out ← ProbComp.eval (adversary n (S.encodeKey k))
  return S.isBindingCollision k out

/-- Computational binding ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8): every
uniform strict PPT adversary has negligible success probability in `S.bindingGame keyDist`. -/
def CommitmentScheme.Binding {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key) : Prop :=
  ∀ adversary : ℕ → List Bool →
      ProbComp (List Bool × (List Bool × List Bool) × (List Bool × List Bool)),
    IsPPTOn (encPair encUnary encBits)
      (encPair encBits (encPair (encPair encBits encBits) (encPair encBits encBits)))
      (fun input => adversary input.1 input.2) →
    Negligible fun n => Game.succProbability (S.bindingGame keyDist adversary n)

end Cslib.Crypto
