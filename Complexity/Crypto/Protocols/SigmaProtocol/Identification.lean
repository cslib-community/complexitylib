/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Crypto.Protocols.SigmaProtocol.Basic
public import Complexity.Probability.IID
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF
import Complexity.Probability.Rewinding

/-!
# Identification from Sigma protocols

A Sigma protocol together with a key generator for its relation is an identification scheme
([BonehShoup2023], Section 19.6): the key generator samples a witness-statement pair `(x, y)`,
the statement `y` is the public verification key, and the prover proves knowledge of `x`. This
module states the exact, finite security reductions of Boneh and Shoup's Chapter 19 for such
schemes. There is no efficiency claim here: the reductions are explicit programs, and the
theorems relate the success probabilities of explicit experiments at a fixed security level.

An `Impersonator` commits from what it sees, keeps a private state, and answers the verifier's
challenge from that state, possibly with fresh randomness. In a direct attack it sees only the
verification key (`directAttack`, Attack Game 18.1); in an eavesdropping attack it also sees `Q`
honest conversations (`eavesdropAttack`, Attack Game 18.2). `oneWayGame` is the one-way key
generation experiment (Attack Game 19.2).

* **Extraction** (Theorem 19.14). If `extract` is a witness extractor for the statements the key
  generator produces (`SpecialSoundOn`, implied by `SpecialSoundness`), rewinding an impersonator
  with direct-attack success probability `ε` recovers a witness for the key with probability at
  least `ε ^ 2 - ε / N`, where `N` is the number of challenges; consequently `ε ≤ 1 / N + √ε'`.
  The generated pairs need not be in the relation.
* **Simulation** (Theorems 19.3 and 19.15). If the protocol is special HVZK, an eavesdropper
  succeeds with exactly the probability of the direct impersonator that simulates the
  conversations itself, provided the key generator only outputs pairs in the relation.

Both reductions only run the given impersonator and the simulator or extractor. Their
efficiency, and the corresponding asymptotic statements under a hardness assumption, are
separate obligations.

The experiments are `Game`s, that is `PMF Bool`, written in `do` notation; the `PMF` monad lives
in a single universe, so the protocol's types and the impersonator's state are in `Type` here,
although `SigmaProtocol` itself is universe-polymorphic.

## Main definitions

* `SigmaProtocol.Impersonator`: a two-stage prover strategy.
* `SigmaProtocol.directAttack`, `SigmaProtocol.eavesdropAttack`: impersonation experiments.
* `SigmaProtocol.oneWayGame`: recover a witness for a generated statement.
* `SigmaProtocol.SpecialSoundOn`: special soundness for the statements of a key generator.
* `SigmaProtocol.Impersonator.rewind`: the rewinding witness extractor.
* `SigmaProtocol.simulateConversation`, `SigmaProtocol.Impersonator.withSimulatedViews`: replace
  eavesdropped conversations by simulated ones.

## Main results

* `SigmaProtocol.sq_sub_le_oneWayGame_rewind`: `ε ^ 2 - ε / N ≤ ε'` (Theorem 19.14).
* `SigmaProtocol.succProbability_directAttack_le`: `ε ≤ 1 / N + √ε'` (Theorem 19.14).
* `SigmaProtocol.eavesdropAttack_eq_directAttack`: eavesdropping is no stronger than a direct
  attack (Theorems 19.3 and 19.15).
* `SigmaProtocol.succProbability_eavesdropAttack_le`: the two combined.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 18.2, 19.1 and 19.6.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability

variable {X Y T C Z : Type}

/-- An impersonator: from its view it commits to `t` and keeps a private state, and from that
state it answers the verifier's challenge, possibly with fresh randomness. -/
structure Impersonator (View T C Z : Type) where
  /-- The impersonator's private state between its two messages. -/
  State : Type
  /-- Commit from the view, keeping a private state. -/
  commit : View → PMF (T × State)
  /-- Answer a challenge from the private state. -/
  respond : State → C → PMF Z

variable [Fintype C] [Nonempty C]

/-- A direct impersonation attack ([BonehShoup2023], Attack Game 18.1): a key pair is generated,
the impersonator sees the verification key `y`, commits, receives a uniform challenge, and
responds; it wins when the conversation is accepting for `y`. -/
noncomputable def directAttack (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y))
    (A : Impersonator Y T C Z) : Game := do
  let key ← keyGen
  let ts ← A.commit key.2
  let c ← PMF.uniformOfFintype C
  let z ← A.respond ts.2 c
  return P.verify key.2 ts.1 c z

/-- An eavesdropping impersonation attack ([BonehShoup2023], Attack Game 18.2): as
`directAttack`, but the impersonator first sees `Q` independent honest conversations between the
prover and the verifier for the generated key. -/
noncomputable def eavesdropAttack (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y)) (Q : ℕ)
    (A : Impersonator (Y × (Fin Q → T × C × Z)) T C Z) : Game := do
  let key ← keyGen
  let views ← PMF.iid (P.conversation key.1 key.2) Q
  let ts ← A.commit (key.2, views)
  let c ← PMF.uniformOfFintype C
  let z ← A.respond ts.2 c
  return P.verify key.2 ts.1 c z

omit [Fintype C] [Nonempty C] in
/-- One-way key generation ([BonehShoup2023], Attack Game 19.2): the adversary sees a generated
statement and wins when it outputs a witness for it, not necessarily the generated one. -/
noncomputable def oneWayGame (keyGen : PMF (X × Y)) (R : X → Y → Prop)
    [∀ x y, Decidable (R x y)] (B : Y → PMF X) : Game := do
  let key ← keyGen
  let x ← B key.2
  return decide (R x key.2)

/-! ### Extraction by rewinding -/

/-- The rewinding extractor (proof of [BonehShoup2023], Theorem 19.14): run the impersonator to
its commitment, answer two independent uniform challenges from the same state, and apply the
extractor to the two conversations. -/
noncomputable def Impersonator.rewind (A : Impersonator Y T C Z)
    (extract : Y → T → C → Z → C → Z → X) (y : Y) : PMF X := do
  let ts ← A.commit y
  let c ← PMF.uniformOfFintype C
  let c' ← PMF.uniformOfFintype C
  let z ← A.respond ts.2 c
  let z' ← A.respond ts.2 c'
  return extract y ts.1 c z c' z'

/-- The first stage of a direct attack: the verification key and the impersonator's
commitment with its state. -/
private noncomputable def directFirst (keyGen : PMF (X × Y)) (A : Impersonator Y T C Z) :
    PMF (Y × (T × A.State)) := do
  let key ← keyGen
  let ts ← A.commit key.2
  return (key.2, ts)

/-- A direct attack is one run of the two-stage experiment of the rewinding lemma. -/
private theorem directAttack_eq_once (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y))
    (A : Impersonator Y T C Z) :
    P.directAttack keyGen A = Rewinding.once (directFirst keyGen A)
      (fun _ => PMF.uniformOfFintype C)
      (fun s c => A.respond s.2.2 c) fun s c z => P.verify s.1 s.2.1 c z := by
  simp only [directAttack, Rewinding.once, directFirst, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

variable {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop}
  [∀ x y, Decidable (R x y)] {extract : Y → T → C → Z → C → Z → X}

/-- Special soundness for the statements a key generator can produce: from two accepting
conversations with a common commitment and distinct challenges for such a statement, `extract`
computes a witness. It follows from `SpecialSoundness`, and suffices for extraction. -/
def SpecialSoundOn (P : SigmaProtocol X Y T C Z) (keyGen : PMF (X × Y)) (R : X → Y → Prop)
    (extract : Y → T → C → Z → C → Z → X) : Prop :=
  ∀ key ∈ keyGen.support, ∀ t c z c' z', c ≠ c' → P.Accepts key.2 t c z →
    P.Accepts key.2 t c' z' → R (extract key.2 t c z c' z') key.2

omit [Fintype C] [Nonempty C] [∀ x y, Decidable (R x y)] in
/-- Special soundness gives special soundness for every key generator. -/
theorem SpecialSoundness.specialSoundOn (hP : P.SpecialSoundness R extract)
    (keyGen : PMF (X × Y)) : P.SpecialSoundOn keyGen R extract :=
  fun key _ => hP key.2

/-- Two accepting runs with distinct challenges lead the rewinding extractor to a witness. -/
private theorem twice_le_oneWayGame [DecidableEq C] {keyGen : PMF (X × Y)}
    (hP : P.SpecialSoundOn keyGen R extract) (A : Impersonator Y T C Z) :
    Rewinding.twice (directFirst keyGen A) (fun _ => PMF.uniformOfFintype C)
        (fun s c => A.respond s.2.2 c)
        (fun s c z => P.verify s.1 s.2.1 c z) true ≤
      oneWayGame keyGen R (A.rewind extract) true := by
  simp only [Rewinding.twice, oneWayGame, Impersonator.rewind, directFirst,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun key hkey => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun ts _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun c _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun c' _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun z _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun z' _ => ?_
  by_cases hwin : (P.verify key.2 ts.1 c z && P.verify key.2 ts.1 c' z' && c != c') = true
  · simp only [Bool.and_eq_true, bne_iff_ne] at hwin
    have hR := hP key hkey ts.1 c z c' z' hwin.2 hwin.1.1 hwin.1.2
    calc _ ≤ 1 := PMF.coe_le_one _ _
      _ = _ := by simp [hR]
  · simp [Bool.eq_false_iff.mpr hwin]

/-- **Extraction from an impersonator** ([BonehShoup2023], Theorem 19.14, Equation 19.17): with
special soundness on the generated statements, the rewinding extractor recovers a witness with
probability at least `ε ^ 2 - ε / N`, where `ε` is the direct-attack success probability and `N`
the number of challenges. -/
theorem sq_sub_le_oneWayGame_rewind {keyGen : PMF (X × Y)}
    (hP : P.SpecialSoundOn keyGen R extract) (A : Impersonator Y T C Z) :
    (Game.succProbability (P.directAttack keyGen A) : ℝ) ^ 2 -
        Game.succProbability (P.directAttack keyGen A) / Fintype.card C ≤
      Game.succProbability (oneWayGame keyGen R (A.rewind extract)) := by
  classical
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  rw [directAttack_eq_once]
  exact (Rewinding.sq_sub_le_twice _ _ _).trans
    (ENNReal.toReal_mono (PMF.apply_ne_top _ _) (twice_le_oneWayGame hP A))

/-- **Security against direct attacks** ([BonehShoup2023], Theorem 19.14, Equation 19.18): with
special soundness on the generated statements, the direct-attack success probability is at most
`1 / N + √ε'`, where `ε'` is the success probability of the rewinding extractor in the one-way
game. -/
theorem succProbability_directAttack_le {keyGen : PMF (X × Y)}
    (hP : P.SpecialSoundOn keyGen R extract) (A : Impersonator Y T C Z) :
    (Game.succProbability (P.directAttack keyGen A) : ℝ) ≤
      1 / Fintype.card C + √(Game.succProbability (oneWayGame keyGen R (A.rewind extract))) := by
  classical
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  rw [directAttack_eq_once]
  exact (Rewinding.le_inv_add_sqrt_twice _ _ _).trans (add_le_add le_rfl (Real.sqrt_le_sqrt
    (ENNReal.toReal_mono (PMF.apply_ne_top _ _) (twice_le_oneWayGame hP A))))

/-! ### Eavesdropping by simulation -/

/-- A simulated conversation: a uniform challenge and the simulator's commitment and response for
it. Under special HVZK this is the law of an honest conversation
(`SpecialHVZK.conversation_eq`). -/
noncomputable def simulateConversation (simulate : Y → C → PMF (T × Z)) (y : Y) :
    PMF (T × C × Z) := do
  let c ← PMF.uniformOfFintype C
  let tz ← simulate y c
  return (tz.1, c, tz.2)

/-- An eavesdropper turned into a direct impersonator ([BonehShoup2023], Theorem 19.3 and
Figure 19.2): it simulates the `Q` conversations it would have overheard. -/
noncomputable def Impersonator.withSimulatedViews (simulate : Y → C → PMF (T × Z)) {Q : ℕ}
    (A : Impersonator (Y × (Fin Q → T × C × Z)) T C Z) : Impersonator Y T C Z where
  State := A.State
  commit y := do
    let views ← PMF.iid (simulateConversation simulate y) Q
    A.commit (y, views)
  respond := A.respond

omit [∀ x y, Decidable (R x y)] in
/-- **Eavesdropping does not help** ([BonehShoup2023], Theorems 19.3 and 19.15): for a special
HVZK protocol and a key generator whose pairs are in the relation, an eavesdropper succeeds with
exactly the probability of the direct impersonator that simulates its views. -/
theorem eavesdropAttack_eq_directAttack {simulate : Y → C → PMF (T × Z)}
    (hP : P.SpecialHVZK R simulate) {keyGen : PMF (X × Y)}
    (hkey : ∀ key ∈ keyGen.support, R key.1 key.2) {Q : ℕ}
    (A : Impersonator (Y × (Fin Q → T × C × Z)) T C Z) :
    P.eavesdropAttack keyGen Q A = P.directAttack keyGen (A.withSimulatedViews simulate) := by
  simp only [eavesdropAttack, directAttack, Impersonator.withSimulatedViews,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_bind]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun key hk => ?_
  rw [hP.conversation_eq (hkey key hk)]
  rfl

/-- Security of a special-sound, special-HVZK identification scheme against eavesdropping
([BonehShoup2023], Theorems 19.14 and 19.15 combined): `ε ≤ 1 / N + √ε'`, for the rewinding
extractor of the simulating direct impersonator. -/
theorem succProbability_eavesdropAttack_le {simulate : Y → C → PMF (T × Z)}
    (hsound : P.SpecialSoundness R extract) (hzk : P.SpecialHVZK R simulate)
    {keyGen : PMF (X × Y)} (hkey : ∀ key ∈ keyGen.support, R key.1 key.2) {Q : ℕ}
    (A : Impersonator (Y × (Fin Q → T × C × Z)) T C Z) :
    (Game.succProbability (P.eavesdropAttack keyGen Q A) : ℝ) ≤
      1 / Fintype.card C + √(Game.succProbability
        (oneWayGame keyGen R ((A.withSimulatedViews simulate).rewind extract))) := by
  rw [eavesdropAttack_eq_directAttack hzk hkey]
  exact succProbability_directAttack_le (hsound.specialSoundOn keyGen) _

end Cslib.Crypto.Protocols.SigmaProtocol
