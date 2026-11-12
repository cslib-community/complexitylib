/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Kilian
import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Rewinding.Consistency
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.SuppCases

/-!
# Computational soundness of Kilian's protocol

A cheating prover for Kilian's protocol (`KilianProver`) is a two-stage program, as in
`CommitmentReceiver`: on the security parameter `n` and the hash key `k` it outputs a statement
`x`, a root and a saved state; on the state and the verifier's random strings it outputs the
openings. It chooses `x` after seeing the key. The soundness experiment (`kilianSoundnessGame`)
accepts when `x ∉ L` and the verifier accepts; membership in `L` is decided classically, and no
reduction ever decides it. Kilian's protocol is computationally sound (`KilianSound`) when every
uniform strict PPT cheating prover wins with negligible probability.

**The reduction.** `kilianBindingAdversary P` runs the first stage of `P` once and the second stage
twice, on independent challenges, and outputs the first pair of openings, one from each run, of a
common position to different bits (`kilianBindingOutput`). When both runs are accepted, these are
two accepted openings of one position of one root to different leaves
(`merkleBreaksBinding_kilianBindingOutput`): a break of `MerklePositionBinding`. The reduction is
strict PPT (`isPPT_kilianBindingAdversary`).

**The exact bound** (`succProbability_kilianSoundnessGame_le`). If every statement that `P` can
output at parameter `n` has a compact table of at most `M` entries, then

`Pr[x ∉ L ∧ accept] ≤ 2⁻ⁿ + M · √Adv^bind(kilianBindingAdversary P, n)`.

The proof is `Cslib.Probability.Rewinding.le_add_mul_sqrt_disagreement`: at each saved state, a
run that accepts while its opened bits agree with a fixed table makes the PCP verifier accept the
proof spelled by that table on all `n` independent random strings, which happens with
probability at most `2⁻ⁿ` when `x ∉ L` (`IsPCPVerifier`'s soundness); otherwise two runs disagree.
Composing with `succProbability_merkleBindingGame_le` bounds the advantage by that of the collision
finder `merkleCollisionFinder H (kilianBindingAdversary P)`.

**Asymptotics.** For a polynomial-time PCP verifier for `L` with `O(log n)` random bits and a
`HashFamily H`, every efficient prover outputs statements of polynomial length, so `M` is
polynomial, and Kilian's protocol is computationally sound (`HashFamily.kilianSound`). With the
PCP theorem, every `L ∈ NP` has such a verifier (`CslibFrontier.Crypto.Computational.Kilian.NP`):
an interactive argument whose honest prover is efficient on the compact tables accepted by
`PCPVerifier.tableVerifier`, an NP relation for `L`. Prover efficiency for an arbitrary given NP
relation would need a polynomial-time map from its witnesses to PCP proofs, which the library does
not have.

**Relation to [BarakGoldreich2001].** Construction 3.4 is analysed there in Lemma 3.5 as a weak
proof of knowledge against non-uniform provers, with a reverse-sampling extractor for oracles of
superpolynomial length. Here statements and tables have polynomial length, adversaries are uniform
(as in `CollisionResistant`), and the bound is computational soundness with an explicit loss; the
statement and its constants are our own packaging. Succinctness accounting (communication and
verifier time) is in `CslibFrontier.Crypto.Computational.Kilian.Succinct`.

## Main definitions

* `Cslib.Crypto.KilianProver`, `Cslib.Crypto.KilianProver.IsPPT`: cheating provers.
* `Cslib.Crypto.kilianSoundnessGame`, `Cslib.Crypto.KilianSound`: the soundness experiment and
  computational soundness.
* `Cslib.Crypto.kilianOpenings`, `Cslib.Crypto.kilianConflict`, `Cslib.Crypto.kilianBindingOutput`,
  `Cslib.Crypto.kilianBindingAdversary`: the reduction to position binding.
* `Cslib.Crypto.kilianProof`: the PCP proof spelled by a compact position table.

## Main results

* `Cslib.Crypto.merkleBreaksBinding_kilianBindingOutput`: two accepted runs that open a position
  to different bits give a binding break.
* `Cslib.Crypto.accepts_kilianProof`: an accepted response consistent with a position table makes
  the PCP verifier accept `kilianProof`.
* `Cslib.Crypto.toOuterMeasure_kilianChallenges_accepts_le`: a fixed proof of a false statement
  passes `m` independent PCP repetitions with probability at most `(1 / 2) ^ m`; Micali's
  Fiat–Shamir bound uses it too.
* `Cslib.Crypto.succProbability_kilianSoundnessGame_le`: the exact soundness bound.
* `Cslib.Crypto.isPPT_kilianBindingAdversary`: the reduction is efficient.
* `Cslib.Crypto.succProbability_kilianSoundnessGame_le_collision`: the same bound in terms of
  collision finding.
* `Cslib.Crypto.HashFamily.kilianSound`: computational soundness from collision resistance.

## References

* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992]
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4 and Lemma 3.5.
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability Turing.MultiTapeTM

variable {α : Type} (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)

/-! ### Cheating provers and the soundness experiment -/

/-- A cheating prover for Kilian's protocol. The first stage `commit n k` receives the unary
security parameter and the hash key, and outputs a statement, a root and a saved state; the second
stage `answer n state ρs` receives the saved state and the verifier's random strings, and outputs
the openings. -/
structure KilianProver (α : Type) where
  /-- First stage: output `((x, root), state)`. -/
  commit : ℕ → List Bool → ProbComp ((α × List Bool) × List Bool)
  /-- Second stage: answer the random strings `ρs` from the saved `state`. -/
  answer : ℕ → List Bool → List (List Bool) → ProbComp KilianResponse

/-- A cheating prover is strict PPT if both stages run in polynomial time in their full encoded
inputs, the saved state and the random strings included. -/
structure KilianProver.IsPPT (enc : α ↪ List Bool) (P : KilianProver α) : Prop where
  /-- The first stage is a strict PPT family from `(n, k)` to `((x, root), state)`. -/
  commit : Probability.IsPPT (encPair (encPair enc encBits) encBits) P.commit
  /-- The second stage is strict PPT on `(n, state, ρs)`. -/
  answer : IsPPTOn (encPair encUnary (encPair encBits (encList encBits))) encKilianResponse
    (fun ⟨n, state, ρs⟩ => P.answer n state ρs)

open Classical in
/-- The soundness experiment of Kilian's protocol against `P` at security parameter `n`: the
verifier samples a key, `P` chooses a statement and a root, the verifier samples its challenges,
`P` answers, and `P` wins when the statement is outside `L` and the verifier accepts. -/
noncomputable def kilianSoundnessGame (L : Set α) (P : KilianProver α) (n : ℕ) :
    ProbComp Bool := do
  let k ← BitString.sampleList n
  let out ← P.commit n k
  let ((x, root), state) := out
  let ρs ← kilianChallenges V n x
  let response ← P.answer n state ρs
  return (decide (x ∉ L) && kilianVerify H V k x root ρs response)

/-- **Computational soundness** of Kilian's protocol for `L`: every uniform strict PPT cheating
prover, which may choose its statement after seeing the hash key, convinces the verifier of a
statement outside `L` with negligible probability. -/
def KilianSound (enc : α ↪ List Bool) (L : Set α) : Prop :=
  ∀ P : KilianProver α, P.IsPPT enc →
    Negligible fun n => Game.succProbability (ProbComp.eval (kilianSoundnessGame H V L P n))

/-! ### The reduction to position binding -/

/-- The openings of a response, each with the PCP address it opens. -/
def kilianOpenings (x : α) (ρs : List (List Bool)) (response : KilianResponse) :
    List (ℕ × KilianOpening) :=
  (ρs.zip response).flatMap fun (ρ, answers) => (V.queries (x, ρ)).zip answers

/-- The first pair of openings, one from each list, of a common position to different bits. -/
def kilianConflict (x : α) (openings₁ openings₂ : List (ℕ × KilianOpening)) :
    Option ((ℕ × KilianOpening) × (ℕ × KilianOpening)) :=
  (openings₁.flatMap fun o₁ => openings₂.map fun o₂ => (o₁, o₂)).find?
    fun ((a₁, o₁), (a₂, o₂)) =>
      kilianPosition V x a₁ == kilianPosition V x a₂ && o₁.bit != o₂.bit

/-- The binding adversary's output from two lists of openings against `root`: the conflicting
pair found by `kilianConflict`, as two openings of its position with one-bit leaves. -/
def kilianBindingOutput (x : α) (root : List Bool)
    (openings₁ openings₂ : List (ℕ × KilianOpening)) : MerkleBindingOutput :=
  (kilianConflict V x openings₁ openings₂).elim ((root, 0), ([], []), ([], []))
    fun ((a, o₁), (_, o₂)) =>
      ((root, kilianPosition V x a), ([o₁.bit], o₁.path), ([o₂.bit], o₂.path))

/-- The position-binding adversary built from a cheating prover: run its first stage once and its
second stage on two independent challenges, and output a conflicting pair of openings. -/
noncomputable def kilianBindingAdversary (P : KilianProver α) : MerkleBindingAdversary :=
  fun n k => do
    let out ← P.commit n k
    let ((x, root), state) := out
    let ρs₁ ← kilianChallenges V n x
    let response₁ ← P.answer n state ρs₁
    let ρs₂ ← kilianChallenges V n x
    let response₂ ← P.answer n state ρs₂
    return kilianBindingOutput V x root (kilianOpenings V x ρs₁ response₁)
      (kilianOpenings V x ρs₂ response₂)

variable {H V}

/-- Every opening of an accepted response passes `merkleVerify` at its position. -/
theorem merkleVerify_of_mem_kilianOpenings {k : List Bool} {x : α} {root : List Bool}
    {ρs : List (List Bool)} {response : KilianResponse}
    (h : kilianVerify H V k x root ρs response = true) {a : ℕ} {o : KilianOpening}
    (ho : (a, o) ∈ kilianOpenings V x ρs response) :
    merkleVerify H k (kilianDepth V x) root (kilianPosition V x a) [o.bit] o.path = true := by
  simp only [kilianVerify, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  simp only [kilianOpenings, List.mem_flatMap] at ho
  obtain ⟨⟨ρ, answers⟩, hmem, ho⟩ := ho
  have hc := h.2 _ hmem
  simp only [kilianCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  exact hc.1.2 _ ho

/-- **Two accepted runs that disagree break position binding**: if two responses against one root
are accepted and open some common position to different bits, the binding adversary's output
breaks binding. -/
theorem merkleBreaksBinding_kilianBindingOutput {k : List Bool} {x : α} {root : List Bool}
    {ρs₁ ρs₂ : List (List Bool)} {response₁ response₂ : KilianResponse}
    (h₁ : kilianVerify H V k x root ρs₁ response₁ = true)
    (h₂ : kilianVerify H V k x root ρs₂ response₂ = true) {a₁ a₂ : ℕ} {o₁ o₂ : KilianOpening}
    (ho₁ : (a₁, o₁) ∈ kilianOpenings V x ρs₁ response₁)
    (ho₂ : (a₂, o₂) ∈ kilianOpenings V x ρs₂ response₂)
    (hpos : kilianPosition V x a₁ = kilianPosition V x a₂) (hb : o₁.bit ≠ o₂.bit) :
    merkleBreaksBinding H k (kilianBindingOutput V x root (kilianOpenings V x ρs₁ response₁)
      (kilianOpenings V x ρs₂ response₂)) = true := by
  set openings₁ := kilianOpenings V x ρs₁ response₁
  set openings₂ := kilianOpenings V x ρs₂ response₂
  have hsome : (kilianConflict V x openings₁ openings₂).isSome = true := by
    refine List.find?_isSome.mpr ⟨((a₁, o₁), (a₂, o₂)),
      List.mem_flatMap.mpr ⟨_, ho₁, List.mem_map.mpr ⟨_, ho₂, rfl⟩⟩, ?_⟩
    simpa [hpos] using hb
  obtain ⟨⟨p₁, p₂⟩, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have hp := List.find?_some hfind
  obtain ⟨q₁, hq₁, hq⟩ := List.mem_flatMap.mp (List.mem_of_find?_eq_some hfind)
  obtain ⟨q₂, hq₂, hqeq⟩ := List.mem_map.mp hq
  simp only [Prod.mk.injEq] at hqeq
  obtain ⟨rfl, rfl⟩ := hqeq
  obtain ⟨c₁, o₁'⟩ := q₁
  obtain ⟨c₂, o₂'⟩ := q₂
  have v₁ := merkleVerify_of_mem_kilianOpenings h₁ hq₁
  have v₂ := merkleVerify_of_mem_kilianOpenings h₂ hq₂
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq] at hp
  rw [kilianBindingOutput, hfind]
  have hlen : o₁'.path.length = kilianDepth V x := by
    simp only [merkleVerify, Bool.and_eq_true, beq_iff_eq] at v₁
    exact v₁.1.1
  simp only [Option.elim, merkleBreaksBinding, hlen, Bool.and_eq_true, bne_iff_ne, ne_eq,
    List.cons.injEq, and_true]
  exact ⟨⟨v₁, hp.1 ▸ v₂⟩, hp.2⟩

/-! ### Acceptance with a consistent table -/

/-- The PCP proof spelled by a table `π` of the positions of `x`: the bit at address `a` is the
table's bit at the position of `a`. Only addresses up to the sum of the address table are
spelled; the others are never queried. -/
def kilianProof (V : PCPVerifier α) (x : α) (π : ℕ → Bool) : List Bool :=
  (List.range ((V.queryTable x).sum + 1)).map fun a => π (kilianPosition V x a)

/-- Opened positions lie inside the compact table. -/
private theorem kilianPosition_lt_of_mem_kilianOpenings {x : α} {ρs : List (List Bool)}
    {response : KilianResponse} (hρs : ∀ ρ ∈ ρs, ρ.length = V.coins x)
    {o : ℕ × KilianOpening} (ho : o ∈ kilianOpenings V x ρs response) :
    kilianPosition V x o.1 < (V.queryTable x).length := by
  simp only [kilianOpenings, List.mem_flatMap] at ho
  obtain ⟨⟨ρ, answers⟩, hmem, ho⟩ := ho
  exact kilianPosition_lt (hρs ρ (List.of_mem_zip hmem).1) (List.of_mem_zip ho).1

/-- An accepted response whose opened bits agree with the table `π` makes the PCP verifier accept
the proof spelled by `π` on every random string of the right length. -/
theorem accepts_kilianProof {k : List Bool} {x : α} {root : List Bool}
    {ρs : List (List Bool)} {response : KilianResponse}
    (h : kilianVerify H V k x root ρs response = true) {π : ℕ → Bool}
    (hcons : ∀ o ∈ kilianOpenings V x ρs response, o.2.bit = π (kilianPosition V x o.1))
    {ρ : List Bool} (hρ : ρ ∈ ρs) (hlen : ρ.length = V.coins x) :
    V.accepts x (kilianProof V x π) ρ = true := by
  simp only [kilianVerify, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hρ
  have hi' : i < response.length := h.1 ▸ hi
  have hmem : (ρs[i], response[i]) ∈ ρs.zip response :=
    List.mem_iff_getElem.mpr ⟨i, by simp [hi, hi'], by simp⟩
  have hc := h.2 _ hmem
  simp only [kilianCheck, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hlenA, -⟩, hverdict⟩ := hc
  unfold PCPVerifier.accepts PCPVerifier.answers
  convert hverdict using 3
  refine List.ext_getElem (by simp [hlenA]) fun m h₁ h₂ => ?_
  have hmq : m < (V.queries (x, ρs[i])).length := by simpa using h₁
  have hm : m < response[i].length := by simpa using h₂
  simp only [List.getElem_map]
  set q := (V.queries (x, ρs[i]))[m]
  have hzip : (q, response[i][m]) ∈ (V.queries (x, ρs[i])).zip response[i] :=
    List.mem_iff_getElem.mpr ⟨m, by simp [hmq, hm], by simp [q]⟩
  have hopen : (q, response[i][m]) ∈ kilianOpenings V x ρs response :=
    List.mem_flatMap.mpr ⟨_, hmem, hzip⟩
  rw [hcons _ hopen]
  have hq := V.mem_queryTable hlen (List.getElem_mem hmq)
  have hlt : q < (V.queryTable x).sum + 1 := Nat.lt_succ_of_le (List.le_sum_of_mem hq)
  simp [kilianProof, List.getD_eq_getElem?_getD, hlt]


/-! ### The exact bound -/

variable (H V)

/-- The first stage of the soundness experiment: the key and the prover's first message. -/
private noncomputable def kilianFirst (P : KilianProver α) (n : ℕ) :
    PMF (List Bool × (α × List Bool) × List Bool) :=
  ProbComp.eval do
    let k ← BitString.sampleList n
    let out ← P.commit n k
    return (k, out)

/-- The second stage of the soundness experiment from a saved first stage: the challenges and the
prover's response. -/
private noncomputable def kilianRun (P : KilianProver α) (n : ℕ)
    (s : List Bool × (α × List Bool) × List Bool) : PMF (List (List Bool) × KilianResponse) :=
  ProbComp.eval do
    let ρs ← kilianChallenges V n s.2.1.1
    let response ← P.answer n s.2.2 ρs
    return (ρs, response)

open Classical in
/-- The prover wins a run: the statement is outside `L` and the verifier accepts. -/
private noncomputable def kilianWins (L : Set α) (s : List Bool × (α × List Bool) × List Bool)
    (r : List (List Bool) × KilianResponse) : Bool :=
  decide (s.2.1.1 ∉ L) && kilianVerify H V s.1 s.2.1.1 s.2.1.2 r.1 r.2

/-- A run opens position `j` to the bit `b`. -/
private def kilianOpens (s : List Bool × (α × List Bool) × List Bool)
    (r : List (List Bool) × KilianResponse) (j : ℕ) (b : Bool) : Bool :=
  (kilianOpenings V s.2.1.1 r.1 r.2).any fun o =>
    kilianPosition V s.2.1.1 o.1 == j && o.2.bit == b

private theorem eval_kilianSoundnessGame (L : Set α) (P : KilianProver α) (n : ℕ) :
    ProbComp.eval (kilianSoundnessGame H V L P n) =
      Rewinding.acceptance (kilianFirst P n) (kilianRun V P n) (kilianWins H V L) := by
  simp only [kilianSoundnessGame, Rewinding.acceptance, kilianFirst, kilianRun, kilianWins,
    ProbComp.eval_bind, ProbComp.eval_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

private theorem disagreement_le_merkleBindingGame (L : Set α) (P : KilianProver α) (n M : ℕ) :
    Rewinding.disagreement (kilianFirst P n) (kilianRun V P n) (kilianWins H V L)
        (kilianOpens V) M true ≤
      ProbComp.eval (merkleBindingGame H (kilianBindingAdversary V P) n) true := by
  simp only [Rewinding.disagreement, merkleBindingGame, kilianBindingAdversary, kilianFirst,
    kilianRun, ProbComp.eval_bind, ProbComp.eval_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun k _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun out _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun ρs₁ _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun response₁ _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun ρs₂ _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun response₂ _ => ?_
  by_cases hE : (kilianWins H V L (k, out) (ρs₁, response₁) &&
      kilianWins H V L (k, out) (ρs₂, response₂) && (List.range M).any fun j =>
        kilianOpens V (k, out) (ρs₁, response₁) j false &&
          kilianOpens V (k, out) (ρs₂, response₂) j true) = true
  · rw [hE]
    simp only [kilianWins, kilianOpens, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      beq_iff_eq] at hE
    obtain ⟨⟨⟨-, h₁⟩, -, h₂⟩, j, -, ⟨⟨a₁, o₁⟩, ho₁, hj₁, hb₁⟩,
      ⟨⟨a₂, o₂⟩, ho₂, hj₂, hb₂⟩⟩ := hE
    rw [merkleBreaksBinding_kilianBindingOutput h₁ h₂ ho₁ ho₂ (hj₁.trans hj₂.symm)
      (by simp only at hb₁ hb₂; rw [hb₁, hb₂]; decide)]
  · rw [Bool.not_eq_true] at hE
    rw [hE]
    simp

variable {H V}

private theorem mem_support_kilianFirst {P : KilianProver α} {n : ℕ}
    {s : List Bool × (α × List Bool) × List Bool} (hs : s ∈ (kilianFirst P n).support) :
    s.1.length = n ∧ s.2 ∈ (ProbComp.eval (P.commit n s.1)).support := by
  supp_cases hs [kilianFirst, BitString.eval_sampleList] with ⟨k, hk, out, hout, rfl⟩
  exact ⟨BitString.length_of_mem_support_uniformList hk, hout⟩

private theorem length_of_mem_support_kilianRun {P : KilianProver α} {n : ℕ}
    {s : List Bool × (α × List Bool) × List Bool} {r : List (List Bool) × KilianResponse}
    (hr : r ∈ (kilianRun V P n s).support) : ∀ ρ ∈ r.1, ρ.length = V.coins s.2.1.1 := by
  supp_cases hr [kilianRun] with ⟨ρs, hρs, response, -, rfl⟩
  rw [kilianChallenges, ProbComp.mem_support_replicate_iff] at hρs
  intro ρ hρ
  exact BitString.length_of_mem_support_uniformList (by simpa using hρs.2 ρ hρ)

private theorem map_fst_kilianRun (P : KilianProver α) (n : ℕ)
    (s : List Bool × (α × List Bool) × List Bool) :
    (kilianRun V P n s).map Prod.fst = ProbComp.eval (kilianChallenges V n s.2.1.1) := by
  simp only [kilianRun, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
    PMF.bind_const, PMF.bind_pure]

variable (V) in
/-- One PCP repetition accepts a fixed candidate proof `π` of a statement `x` with soundness
bound `2 * acceptCount ... ≤ 2 ^ V.coins x` with probability at most `1 / 2` in `ℝ≥0∞`. -/
theorem toOuterMeasure_sampleList_accepts_le {x : α} {π : List Bool}
    (hsound : 2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x) :
    (ProbComp.eval (BitString.sampleList (V.coins x))).toOuterMeasure
      {ρ | V.accepts x π ρ = true} ≤ 1 / 2 := by
  have hmap : (ProbComp.eval (BitString.sampleList (V.coins x))).toOuterMeasure
      {ρ | V.accepts x π ρ = true} =
      ((BitString.uniformList (V.coins x)).map fun ρ => V.accepts x π ρ) true := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      BitString.eval_sampleList]
    rfl
  rw [hmap, uniformList_acceptCount (V := fun y => V.accepts y.1 π y.2),
    ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (by finiteness))]
  calc (acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) : ENNReal)
      = 1 / 2 * (2 * (acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) : ENNReal)) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 1 / 2 * (2 : ENNReal) ^ V.coins x := by
        gcongr
        exact_mod_cast hsound

variable (V) in
/-- Across `m` independent PCP challenge strings `kilianChallenges V m x`, a fixed candidate proof
`π` for `x` with per-repetition soundness error `≤ 1 / 2` is accepted on all `m` repetitions with
probability at most `(1 / 2) ^ m`. -/
theorem toOuterMeasure_kilianChallenges_accepts_le (m : ℕ) {x : α} {π : List Bool}
    (hsound : 2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x) :
    (ProbComp.eval (kilianChallenges V m x)).toOuterMeasure
      {ρs | ∀ ρ ∈ ρs, V.accepts x π ρ = true} ≤ (1 / 2) ^ m := by
  rw [kilianChallenges, ProbComp.toOuterMeasure_replicate_forall]
  exact pow_le_pow_left' (toOuterMeasure_sampleList_accepts_le V hsound) m

/-- **Exact soundness of Kilian's protocol.** For a PCP verifier whose soundness error on
statements outside `L` is at most one half per repetition, and a cheating prover `P` all of whose
statements at parameter `n` have compact tables of at most `M` entries,
`Pr[x ∉ L ∧ accept] ≤ 2⁻ⁿ + M · √Adv^bind(kilianBindingAdversary P, n)`. The proof is
original packaging (see the module documentation); it makes no efficiency assumption. -/
theorem succProbability_kilianSoundnessGame_le (L : Set α) (P : KilianProver α) (n M : ℕ)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    (hM : ∀ k : List Bool, k.length = n → ∀ x root state,
      ((x, root), state) ∈ (ProbComp.eval (P.commit n k)).support →
        (V.queryTable x).length ≤ M) :
    Game.succProbability (ProbComp.eval (kilianSoundnessGame H V L P n)) ≤
      (1 / 2) ^ n + M * NNReal.sqrt (Game.succProbability
        (ProbComp.eval (merkleBindingGame H (kilianBindingAdversary V P) n))) := by
  have hcore := Rewinding.le_add_mul_sqrt_disagreement (kilianFirst P n) (kilianRun V P n)
    (kilianWins H V L) (kilianOpens V) M (ε := (1 / 2) ^ n) ?hpos ?hcons
  case hpos =>
    intro s hs r hr j b hwin hopen
    obtain ⟨hk, hout⟩ := mem_support_kilianFirst hs
    simp only [kilianOpens, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hopen
    obtain ⟨o, ho, rfl, -⟩ := hopen
    exact (kilianPosition_lt_of_mem_kilianOpenings (length_of_mem_support_kilianRun hr)
      ho).trans_le (hM _ hk _ _ _ hout)
  case hcons =>
    intro s hs π
    by_cases hx : s.2.1.1 ∈ L
    · have hempty : {r | kilianWins H V L s r = true ∧
          ∀ j b, kilianOpens V s r j b = true → b = π j} = ∅ := by
        ext r
        simp [kilianWins, hx]
      rw [hempty, MeasureTheory.measure_empty, ENNReal.toReal_zero]
      positivity
    · have hsub : (kilianRun V P n s).toOuterMeasure {r | kilianWins H V L s r = true ∧
          ∀ j b, kilianOpens V s r j b = true → b = π j} ≤
          (kilianRun V P n s).toOuterMeasure (Prod.fst ⁻¹'
            {ρs | ∀ ρ ∈ ρs, V.accepts s.2.1.1 (kilianProof V s.2.1.1 π) ρ = true}) := by
        rw [← PMF.toOuterMeasure_apply_inter_support]
        refine MeasureTheory.measure_mono fun r ⟨⟨hwin, hcons⟩, hr⟩ => ?_
        simp only [kilianWins, Bool.and_eq_true] at hwin
        intro ρ hρ
        refine accepts_kilianProof hwin.2 (fun o ho => ?_) hρ
          (length_of_mem_support_kilianRun hr ρ hρ)
        exact hcons (kilianPosition V s.2.1.1 o.1) o.2.bit
          (List.any_eq_true.mpr ⟨o, ho, by simp⟩)
      rw [← PMF.toOuterMeasure_map_apply, map_fst_kilianRun] at hsub
      refine (ENNReal.toReal_mono (by simp) (hsub.trans
        (toOuterMeasure_kilianChallenges_accepts_le V n (hsound _ hx _)))).trans_eq ?_
      simp
  rw [eval_kilianSoundnessGame] at *
  have hdis := disagreement_le_merkleBindingGame H V L P n M
  rw [← NNReal.coe_le_coe]
  simp only [Game.succProbability, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_natCast, Real.coe_sqrt, ENNReal.coe_toNNReal_eq_toReal, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat]
  refine hcore.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hdis)) (Nat.cast_nonneg _)))

/-! ### The reduction is efficient -/

section Efficiency

variable {enc : α ↪ List Bool} {c : ℕ}

/-- The encoding of an opening together with its address. -/
private abbrev encAddressed : ℕ × KilianOpening ↪ List Bool := encPair encNat encKilianOpening

private theorem computableInPolyTime_kilianOpenings (hV : V.PolyTime enc) :
    ComputableInPolyTime
      (fun p : α × List (List Bool) × KilianResponse => kilianOpenings V p.1 p.2.1 p.2.2)
      (encPair enc (encPair (encList encBits) encKilianResponse)) (encList encAddressed) := by
  have hx := ComputableInPolyTime.fst enc (encPair (encList encBits) encKilianResponse)
  have hrest := ComputableInPolyTime.snd enc (encPair (encList encBits) encKilianResponse)
  have hρs := (ComputableInPolyTime.fst (encList encBits) encKilianResponse).comp hrest
  have hresponse := (ComputableInPolyTime.snd (encList encBits) encKilianResponse).comp hrest
  have hpf := ComputableInPolyTime.fst (encPair enc (encPair (encList encBits)
    encKilianResponse)) (encPair encBits (encList encKilianOpening))
  have hps := ComputableInPolyTime.snd (encPair enc (encPair (encList encBits)
    encKilianResponse)) (encPair encBits (encList encKilianOpening))
  have hρ := (ComputableInPolyTime.fst encBits (encList encKilianOpening)).comp hps
  have hanswers := (ComputableInPolyTime.snd encBits (encList encKilianOpening)).comp hps
  have hqueries := hV.2.1.comp ((hx.comp hpf).prod hρ)
  unfold kilianOpenings
  exact ComputableInPolyTime.flatMapWithInput
    (f := fun (p : α × List (List Bool) × KilianResponse) (q : List Bool × List KilianOpening) =>
      (V.queries (p.1, q.1)).zip q.2)
    ((ComputableInPolyTime.zip encBits (encList encKilianOpening)).comp
      (hρs.prod hresponse))
    ((ComputableInPolyTime.zip encNat encKilianOpening).comp (hqueries.prod hanswers))

private theorem computableInPolyTime_kilianBindingOutput (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun p : (α × List Bool) × List (ℕ × KilianOpening) × List (ℕ × KilianOpening) =>
        kilianBindingOutput V p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair enc encBits) (encPair (encList encAddressed) (encList encAddressed)))
      encMerkleBindingOutput := by
  set E := encPair (encPair enc encBits) (encPair (encList encAddressed) (encList encAddressed))
  have hcommon := ComputableInPolyTime.fst (encPair enc encBits)
    (encPair (encList encAddressed) (encList encAddressed))
  have hlists := ComputableInPolyTime.snd (encPair enc encBits)
    (encPair (encList encAddressed) (encList encAddressed))
  have hx := (ComputableInPolyTime.fst enc encBits).comp hcommon
  have hroot := (ComputableInPolyTime.snd enc encBits).comp hcommon
  have ho₁ := (ComputableInPolyTime.fst (encList encAddressed) (encList encAddressed)).comp
    hlists
  have ho₂ := (ComputableInPolyTime.snd (encList encAddressed) (encList encAddressed)).comp
    hlists
  have htable := (PCPVerifier.isPolyTime_queryTable hV hcoins).comp hx
  -- The list of all pairs.
  have hpairs : ComputableInPolyTime
      (fun g : (α × List Bool) × List (ℕ × KilianOpening) × List (ℕ × KilianOpening) =>
        g.2.1.flatMap fun o₁ => g.2.2.map fun o₂ => (o₁, o₂))
      E (encList (encPair encAddressed encAddressed)) :=
    ComputableInPolyTime.flatMapWithInput
      (f := fun (g : (α × List Bool) × List (ℕ × KilianOpening) × List (ℕ × KilianOpening))
        (o₁ : ℕ × KilianOpening) => g.2.2.map fun o₂ => (o₁, o₂)) ho₁
      (ComputableInPolyTime.mapWithInput
        (f := fun (q : ((α × List Bool) × List (ℕ × KilianOpening) × List (ℕ × KilianOpening)) ×
          (ℕ × KilianOpening)) (o₂ : ℕ × KilianOpening) => (q.2, o₂))
        (ho₂.comp (ComputableInPolyTime.fst E encAddressed))
        (((ComputableInPolyTime.snd E encAddressed).comp
          (ComputableInPolyTime.fst (encPair E encAddressed) encAddressed)).prod
          (ComputableInPolyTime.snd (encPair E encAddressed) encAddressed)))
  -- The conflict test and the output on a conflict, on `(g, (o₁, o₂))`.
  have hg := ComputableInPolyTime.fst E (encPair encAddressed encAddressed)
  have hq := ComputableInPolyTime.snd E (encPair encAddressed encAddressed)
  have hq₁ := (ComputableInPolyTime.fst encAddressed encAddressed).comp hq
  have hq₂ := (ComputableInPolyTime.snd encAddressed encAddressed).comp hq
  have ha₁ := (ComputableInPolyTime.fst encNat encKilianOpening).comp hq₁
  have ha₂ := (ComputableInPolyTime.fst encNat encKilianOpening).comp hq₂
  have hop₁ := (ComputableInPolyTime.snd encNat encKilianOpening).comp hq₁
  have hop₂ := (ComputableInPolyTime.snd encNat encKilianOpening).comp hq₂
  have hb₁ := encKilianOpening_bit_polyTime hop₁
  have hb₂ := encKilianOpening_bit_polyTime hop₂
  have hpath₁ := encKilianOpening_path_polyTime hop₁
  have hpath₂ := encKilianOpening_path_polyTime hop₂
  have hpos₁ := ComputableInPolyTime.idxOfWithInput (htable.comp hg) ha₁
  have hpos₂ := ComputableInPolyTime.idxOfWithInput (htable.comp hg) ha₂
  have htest := ComputableInPolyTime.bool_and.comp ((ComputableInPolyTime.beq hpos₁ hpos₂).prod
    (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.beq hb₁ hb₂)))
  have hconflict := ComputableInPolyTime.findWithInput
    (test := fun (g : (α × List Bool) × List (ℕ × KilianOpening) × List (ℕ × KilianOpening))
      (q : (ℕ × KilianOpening) × (ℕ × KilianOpening)) =>
        kilianPosition V g.1.1 q.1.1 == kilianPosition V g.1.1 q.2.1 && q.1.2.bit != q.2.2.bit)
    hpairs htest
  have hbody := ((hroot.comp hg).prod hpos₁).prod
    ((ComputableInPolyTime.bitsCons hb₁ (ComputableInPolyTime.const [])).prod hpath₁ |>.prod
      ((ComputableInPolyTime.bitsCons hb₂ (ComputableInPolyTime.const [])).prod
        hpath₂))
  unfold kilianBindingOutput kilianConflict
  exact ComputableInPolyTime.optionElimWithInput
    (body := fun (g : (α × List Bool) × List (ℕ × KilianOpening) × List (ℕ × KilianOpening))
      (q : (ℕ × KilianOpening) × (ℕ × KilianOpening)) =>
        ((g.1.2, kilianPosition V g.1.1 q.1.1), ([q.1.2.bit], q.1.2.path),
          ([q.2.2.bit], q.2.2.path)))
    hconflict ((hroot.prod (ComputableInPolyTime.const 0)).prod
      (ComputableInPolyTime.const ((([] : List Bool), ([] : List (List Bool))),
        (([] : List Bool), ([] : List (List Bool)))))) hbody

/-- **The reduction is efficient**: the binding adversary of a strict PPT cheating prover is strict
PPT, for a polynomial-time PCP verifier with `O(log n)` random bits. -/
theorem isPPT_kilianBindingAdversary (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) {P : KilianProver α}
    (hP : P.IsPPT enc) : IsPPT encMerkleBindingOutput (kilianBindingAdversary V P) := by
  have hcommit := hP.commit.on
  have hanswer : IsPPTOn (encPair encUnary (encPair encBits (encList encBits))) encKilianResponse
      (fun p : ℕ × List Bool × List (List Bool) => P.answer p.1 p.2.1 p.2.2) := hP.answer
  have hchal := isPPTOn_kilianChallenges hV hcoins
  have hopen := computableInPolyTime_kilianOpenings hV
  have hout := computableInPolyTime_kilianBindingOutput hV hcoins
  -- The encodings of the growing context.
  set I := encPair encUnary encBits
  set O := encPair (encPair enc encBits) encBits
  set C₁ := encPair I O
  set C₂ := encPair C₁ (encList encBits)
  set C₃ := encPair C₂ encKilianResponse
  set C₄ := encPair C₃ (encList encBits)
  set C₅ := encPair C₄ encKilianResponse
  change IsPPTOn I encMerkleBindingOutput fun a => do
    let out ← P.commit a.1 a.2
    let ρs₁ ← kilianChallenges V a.1 out.1.1
    let response₁ ← P.answer a.1 out.2 ρs₁
    let ρs₂ ← kilianChallenges V a.1 out.1.1
    let response₂ ← P.answer a.1 out.2 ρs₂
    return kilianBindingOutput V out.1.1 out.1.2 (kilianOpenings V out.1.1 ρs₁ response₁)
      (kilianOpenings V out.1.1 ρs₂ response₂)
  refine IsPPTOn.bind_with hcommit ?_
  refine IsPPTOn.bind_with (hchal.preprocess
    (prepare := fun p : (ℕ × List Bool) × (α × List Bool) × List Bool => (p.1.1, p.2.1.1))
    (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hanswer.preprocess
    (prepare := fun p : ((ℕ × List Bool) × (α × List Bool) × List Bool) × List (List Bool) =>
      (p.1.1.1, p.1.2.2, p.2)) (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hchal.preprocess
    (prepare := fun p : (((ℕ × List Bool) × (α × List Bool) × List Bool) × List (List Bool)) ×
      KilianResponse => (p.1.1.1.1, p.1.1.2.1.1)) (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hanswer.preprocess
    (prepare := fun p : ((((ℕ × List Bool) × (α × List Bool) × List Bool) × List (List Bool)) ×
      KilianResponse) × List (List Bool) => (p.1.1.1.1.1, p.1.1.1.2.2, p.2)) (by fun_prop)) ?_
  have hx : ComputableInPolyTime (fun q : ((((((ℕ × List Bool) × (α × List Bool) × List Bool) ×
      List (List Bool)) × KilianResponse) × List (List Bool)) × KilianResponse) =>
      q.1.1.1.1.2.1.1) C₅ enc := by fun_prop
  have hroot : ComputableInPolyTime (fun q : ((((((ℕ × List Bool) × (α × List Bool) ×
      List Bool) × List (List Bool)) × KilianResponse) × List (List Bool)) × KilianResponse) =>
      q.1.1.1.1.2.1.2) C₅ encBits := by fun_prop
  have hρs₁ : ComputableInPolyTime (fun q : ((((((ℕ × List Bool) × (α × List Bool) ×
      List Bool) × List (List Bool)) × KilianResponse) × List (List Bool)) × KilianResponse) =>
      q.1.1.1.2) C₅ (encList encBits) := by fun_prop
  have hr₁ : ComputableInPolyTime (fun q : ((((((ℕ × List Bool) × (α × List Bool) ×
      List Bool) × List (List Bool)) × KilianResponse) × List (List Bool)) × KilianResponse) =>
      q.1.1.2) C₅ encKilianResponse := by fun_prop
  have hρs₂ : ComputableInPolyTime (fun q : ((((((ℕ × List Bool) × (α × List Bool) ×
      List Bool) × List (List Bool)) × KilianResponse) × List (List Bool)) × KilianResponse) =>
      q.1.2) C₅ (encList encBits) := by fun_prop
  have hr₂ : ComputableInPolyTime (fun q : ((((((ℕ × List Bool) × (α × List Bool) ×
      List Bool) × List (List Bool)) × KilianResponse) × List (List Bool)) × KilianResponse) =>
      q.2) C₅ encKilianResponse := by fun_prop
  exact (hout.comp ((hx.prod hroot).prod ((hopen.comp (hx.prod (hρs₁.prod hr₁))).prod
    (hopen.comp (hx.prod (hρs₂.prod hr₂)))))).isPPTOn

end Efficiency

/-! ### Computational soundness -/

/-- The exact soundness bound composed with the reduction of `HashFamily.merklePositionBinding`:
`Pr[x ∉ L ∧ accept] ≤ 2⁻ⁿ + M · √Adv^CR(merkleCollisionFinder H (kilianBindingAdversary P), n)`. -/
theorem succProbability_kilianSoundnessGame_le_collision (L : Set α) (P : KilianProver α) (n M : ℕ)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    (hM : ∀ k : List Bool, k.length = n → ∀ x root state,
      ((x, root), state) ∈ (ProbComp.eval (P.commit n k)).support →
        (V.queryTable x).length ≤ M) :
    Game.succProbability (ProbComp.eval (kilianSoundnessGame H V L P n)) ≤
      (1 / 2) ^ n + M * NNReal.sqrt (Game.succProbability (ProbComp.eval
        (collisionGame H (fun _ _ => true) (merkleCollisionFinder H (kilianBindingAdversary V P))
          n))) :=
  (succProbability_kilianSoundnessGame_le L P n M hsound hM).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (NNReal.sqrt_le_sqrt.mpr (succProbability_merkleBindingGame_le _ n)) (by positivity)))

/-- **Kilian's protocol is computationally sound** ([BarakGoldreich2001], Construction 3.4 and
Lemma 3.5, for uniform adversaries and compact tables): for a polynomial-time PCP verifier for `L`
with `O(log n)` random bits and any number of queries, and a collision-resistant `HashFamily`,
every uniform strict PPT cheating prover convinces the verifier of a statement outside `L` with
negligible probability. -/
theorem HashFamily.kilianSound (hH : HashFamily H) {enc : α ↪ List Bool} {L : Set α} {c : ℕ}
    {q : ℕ → ℕ} (hV : V.PolyTime enc)
    (hpcp : IsPCPVerifier enc (fun m => c * (Nat.log 2 m + 1)) q V L) :
    KilianSound H V enc L := by
  intro P hP
  have hcoins := hpcp.1
  obtain ⟨c₁, d₁, hlen₁⟩ := hP.commit.on.length_le
  have hq : ComputableInPolyTime (fun out : (α × List Bool) × List Bool => V.queryTable out.1.1)
      (encPair (encPair enc encBits) encBits) (encList encNat) :=
    (PCPVerifier.isPolyTime_queryTable hV hcoins).comp (by fun_prop)
  obtain ⟨c₂, d₂, hlen₂⟩ := hq.polyBounded_length.exists_le
  have hM (n : ℕ) (k : List Bool) (hk : k.length = n) (x : α) (root state : List Bool)
      (hout : ((x, root), state) ∈ (ProbComp.eval (P.commit n k)).support) :
      (V.queryTable x).length ≤ c₂ * (c₁ * (3 * n + 2) ^ d₁ + 1) ^ d₂ := by
    have h₁ := hlen₁ (n, k) _ hout
    have hin : (encPair encUnary encBits (n, k)).length + 1 = 3 * n + 2 := by
      simp [hk]
      ring
    rw [hin] at h₁
    calc (V.queryTable x).length ≤ (encList encNat (V.queryTable x)).length :=
          length_le_length_encList _ _
      _ ≤ c₂ * ((encPair (encPair enc encBits) encBits ((x, root), state)).length + 1) ^ d₂ :=
          hlen₂ ((x, root), state)
      _ ≤ c₂ * (c₁ * (3 * n + 2) ^ d₁ + 1) ^ d₂ := by gcongr
  have hpoly : PolynomiallyBounded fun n => c₂ * (c₁ * (3 * n + 2) ^ d₁ + 1) ^ d₂ := by
    fun_prop
  have hbind := hH.merklePositionBinding.negligible _ (isPPT_kilianBindingAdversary hV hcoins hP)
  refine negligible_of_le ((negligible_geometric (by norm_num : (1 / 2 : NNReal) < 1)).add
    (hbind.sqrt.polynomiallyBounded_mul hpoly)) fun n => ?_
  exact succProbability_kilianSoundnessGame_le L P n _ hpcp.2.2.2 (hM n)

end Cslib.Crypto
