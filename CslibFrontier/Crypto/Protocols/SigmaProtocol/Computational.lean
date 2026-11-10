/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Computational special honest-verifier zero knowledge

Boneh and Shoup's computational relaxation of special HVZK ([BonehShoup2023], Section 20.4.2,
Attack Game 20.4 and Definition 20.6, p. 840) for an indexed family of Sigma protocols `P i`
equipped with word encodings `enc : SigmaProtocol.Encoding I Y T C Z`, witness encodings
`encW : ∀ i, X i ↪ List Bool`, and a parameter distribution `setup : ℕ → PMF I` ([BonehShoup2023],
Section 2.3.4).

In Attack Game 20.4, at security parameter `n`, the challenger draws `i ← setup n` and gives
`(n, i)` to `adversary.choose`, which outputs an encoded witness-statement pair `(xw, yw)` together
with a saved state word. When `(xw, yw)` decodes to `(x, y)` in `R i` (uniquely, by injectivity of
`encW i` and `enc.statement i`):

* **Experiment 0** (`chvzkRealGame`) samples an honest conversation
  `(t, c, z) ← (P i).conversation x y`, encodes `(t, c, z)` into words, and passes it with the
  saved state to `adversary.guess`.
* **Experiment 1** (`chvzkSimGame`) samples a uniform challenge `c ← PMF.uniformOfFintype (C i)`,
  runs the simulator program `sim` on `(i, enc.statement i y, enc.challenge i c)` without using `x`
  to obtain `(tw, zw)`, and passes `(tw, enc.challenge i c, zw)` with the saved state to
  `adversary.guess`.

When `(xw, yw)` is not an encoded pair in `R i`, both experiments output `false`, matching the
admissibility convention of `Cslib.Crypto.Encryption.gameOn` so invalid choices contribute zero
advantage without requiring `R i` to be efficiently decidable by the challenger.

`ComputationalSpecialHVZK P R enc encW setup sim δ` bundles:

1. Uniform strict PPT admissibility of `sim` on `(i, yw, cw)`.
2. Acceptance on every `(i, y, c)` with probability at least `1 - δ i` (exact Definition 20.6
   acceptance when `δ = 0`; relaxed by `δ` when a strict PPT fair-coin simulator approximates a
   non-dyadic distribution).
3. Negligible distinguishing advantage between `chvzkRealGame` and `chvzkSimGame` for every uniform
   strict PPT `CHVZKAdversary`.

Every `EfficientSpecialHVZK` protocol whose realization error `δ` is bounded along `setup` by a
negligible function satisfies `ComputationalSpecialHVZK` — in fact against arbitrary, even
computationally unbounded adversaries at each security parameter
(`SimulatorRealizedBy.advantage_chvzkGame_le`,
`EfficientSpecialHVZK.exists_computationalSpecialHVZK`). As in `EfficientSpecialHVZK`, `δ` is an
explicit parameter of `ComputationalSpecialHVZK` rather than a bundled `Negligible` condition on the
acceptance error alone; exact Definition 20.6 acceptance corresponds to `δ = fun _ => 0` (which
Schnorr's word simulator achieves in `PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr`).

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.CHVZKAdversary`,
  `Cslib.Crypto.Protocols.SigmaProtocol.CHVZKAdversary.IsPPT`: two-stage adversaries and uniform
  strict PPT admissibility for Attack Game 20.4.
* `Cslib.Crypto.Protocols.SigmaProtocol.encodedConversation`,
  `Cslib.Crypto.Protocols.SigmaProtocol.simulatedConversation`: honest and simulated encoded
  conversation distributions.
* `Cslib.Crypto.Protocols.SigmaProtocol.chvzkBranch`,
  `Cslib.Crypto.Protocols.SigmaProtocol.chvzkGameWith`,
  `Cslib.Crypto.Protocols.SigmaProtocol.chvzkRealGame`,
  `Cslib.Crypto.Protocols.SigmaProtocol.chvzkSimGame`: Attack Game 20.4 experiments.
* `Cslib.Crypto.Protocols.SigmaProtocol.ComputationalSpecialHVZK`: Definition 20.6 with explicit
  simulator and acceptance error `δ`.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.chvzkBranch_valid`,
  `Cslib.Crypto.Protocols.SigmaProtocol.chvzkBranch_invalid`: reduction of Attack Game 20.4's
  validity check on valid and invalid witness-statement pairs.
* `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.closeTo_conversation`: statistical
  closeness of honest and simulated encoded conversations.
* `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.advantage_chvzkGame_le`: concrete
  advantage bound in Attack Game 20.4 against arbitrary adversaries.
* `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.computationalSpecialHVZK_of_accepts`,
  `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.computationalSpecialHVZK`,
  `Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialHVZK.exists_computationalSpecialHVZK`:
  statistical special HVZK with negligible realization error along `setup` implies computational
  special HVZK.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 2.3.4 and Section 20.4.2 (Attack Game 20.4 and
  Definition 20.6, p. 840).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Turing.MultiTapeTM Interactive
open scoped ENNReal NNReal

/-- A two-stage adversary for Attack Game 20.4 ([BonehShoup2023], Section 20.4.2, p. 840) over
index type `I`. Stage 1 (`choose`) receives the security parameter and the sampled index, outputs
an encoded witness-statement pair `(xw, yw)` together with a saved state word; Stage 2 (`guess`)
receives the security parameter, the saved state, and an encoded conversation `(tw, cw, zw)`, and
outputs a distinguishing bit. -/
structure CHVZKAdversary (I : Type) where
  /-- Compute an encoded `(witness, statement)` pair and save state for the guessing phase. -/
  choose : ℕ → I → ProbComp ((List Bool × List Bool) × List Bool)
  /-- Distinguish an honest encoded conversation from a simulated one using the saved state. -/
  guess : ℕ → List Bool → List Bool × List Bool × List Bool → ProbComp Bool

/-- Uniform strict PPT admissibility for both stages of a `CHVZKAdversary`, charging the unary
security parameter, the index encoding `encIdx`, and the full saved state. -/
structure CHVZKAdversary.IsPPT {I : Type} (encIdx : I ↪ List Bool)
    (adversary : CHVZKAdversary I) : Prop where
  /-- Choosing the encoded witness-statement pair and saved state is uniform strict PPT. -/
  choose : IsPPTOn (encPair encUnary encIdx)
    (encPair (encPair encBits encBits) encBits)
    (fun ⟨n, i⟩ => adversary.choose n i)
  /-- Guessing from the security parameter, saved state and encoded conversation is uniform strict
  PPT. -/
  guess : IsPPTOn
    (encPair encUnary (encPair encBits (encPair encBits (encPair encBits encBits))))
    encBool
    (fun ⟨n, state, conv⟩ => adversary.guess n state conv)

variable {I : Type} {X Y T C Z : I → Type}

/-- Honest conversation of `P i` on `(x, y)`, encoded into bit words via `enc`. -/
noncomputable def encodedConversation
    (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (enc : Encoding I Y T C Z) (i : I) (x : X i) (y : Y i) :
    PMF (List Bool × List Bool × List Bool) :=
  ((P i).conversation x y).map fun ⟨t, c, z⟩ =>
    (enc.commitment i t, enc.challenge i c, enc.response i z)

/-- Simulated encoded conversation on `(i, y)`: sample a uniform challenge `c : C i`, run `sim` on
`(i, enc.statement i y, enc.challenge i c)` to obtain `(tw, zw)`, and return
`(tw, enc.challenge i c, zw)` ([BonehShoup2023], Section 20.4.2, Attack Game 20.4, Experiment 1,
p. 840). -/
noncomputable def simulatedConversation
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (enc : Encoding I Y T C Z)
    (sim : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (i : I) (y : Y i) : PMF (List Bool × List Bool × List Bool) := do
  let c ← PMF.uniformOfFintype (C i)
  let ⟨tw, zw⟩ ← ProbComp.eval (sim (i, enc.statement i y, enc.challenge i c))
  return (tw, enc.challenge i c, zw)

open Classical in
/-- Challenger continuation of Attack Game 20.4 after `adversary.choose` outputs `((xw, yw), state)`
at `(n, i)`: if `(xw, yw)` decodes via `encW i` and `enc.statement i` to a valid pair `(x, y)` in
`R i`, sample a conversation with `sampleConv i x y` and run `adversary.guess`; otherwise return
`false`. -/
noncomputable def chvzkBranch
    (R : ∀ i, X i → Y i → Prop)
    (enc : Encoding I Y T C Z) (encW : ∀ i, X i ↪ List Bool)
    (sampleConv : ∀ i, X i → Y i → PMF (List Bool × List Bool × List Bool))
    (adversary : CHVZKAdversary I) (n : ℕ) (i : I)
    (xw yw state : List Bool) : Game :=
  if h : ∃ p : X i × Y i, encW i p.1 = xw ∧ enc.statement i p.2 = yw ∧ R i p.1 p.2 then
    (sampleConv i h.choose.1 h.choose.2).bind fun conv =>
      ProbComp.eval (adversary.guess n state conv)
  else
    PMF.pure false

/-- On an encoded valid pair `(encW i x, enc.statement i y)` with `R i x y`, `chvzkBranch` selects
`(x, y)` uniquely by injectivity of `encW i` and `enc.statement i`. -/
@[simp] theorem chvzkBranch_valid
    {R : ∀ i, X i → Y i → Prop}
    {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool}
    (sampleConv : ∀ i, X i → Y i → PMF (List Bool × List Bool × List Bool))
    (adversary : CHVZKAdversary I) (n : ℕ) (i : I)
    {x : X i} {y : Y i} (hxy : R i x y) (state : List Bool) :
    chvzkBranch R enc encW sampleConv adversary n i (encW i x) (enc.statement i y) state =
      ((sampleConv i x y).bind fun conv => ProbComp.eval (adversary.guess n state conv)) := by
  classical
  have hex : ∃ p : X i × Y i,
      encW i p.1 = encW i x ∧ enc.statement i p.2 = enc.statement i y ∧ R i p.1 p.2 :=
    ⟨(x, y), rfl, rfl, hxy⟩
  rw [chvzkBranch, dite_eq_left hex]
  have hp : hex.choose = (x, y) :=
    Prod.ext ((encW i).injective hex.choose_spec.1)
      ((enc.statement i).injective hex.choose_spec.2.1)
  rw [hp]

/-- When `(xw, yw)` does not decode to a valid witness-statement pair in `R i`, `chvzkBranch`
outputs `false`. -/
theorem chvzkBranch_invalid
    {R : ∀ i, X i → Y i → Prop}
    {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool}
    (sampleConv : ∀ i, X i → Y i → PMF (List Bool × List Bool × List Bool))
    (adversary : CHVZKAdversary I) (n : ℕ) (i : I)
    {xw yw : List Bool} (state : List Bool)
    (hinv : ¬ ∃ p : X i × Y i, encW i p.1 = xw ∧ enc.statement i p.2 = yw ∧ R i p.1 p.2) :
    chvzkBranch R enc encW sampleConv adversary n i xw yw state = PMF.pure false := by
  classical
  rw [chvzkBranch, dite_eq_right hinv]

/-- Shared Attack Game 20.4 experiment parameterized by the challenger's conversation sampler
`sampleConv`. -/
noncomputable def chvzkGameWith
    (R : ∀ i, X i → Y i → Prop)
    (enc : Encoding I Y T C Z) (encW : ∀ i, X i ↪ List Bool)
    (setup : ℕ → PMF I)
    (sampleConv : ∀ i, X i → Y i → PMF (List Bool × List Bool × List Bool))
    (adversary : CHVZKAdversary I) (n : ℕ) : Game := do
  let i ← setup n
  let ⟨⟨xw, yw⟩, state⟩ ← ProbComp.eval (adversary.choose n i)
  chvzkBranch R enc encW sampleConv adversary n i xw yw state

/-- Experiment 0 of Attack Game 20.4 ([BonehShoup2023], Section 20.4.2, p. 840): on a valid encoded
witness-statement pair `(x, y)` chosen by `adversary`, give `adversary.guess` an honest encoded
conversation of `P i` on `(x, y)`. -/
noncomputable def chvzkRealGame
    (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (R : ∀ i, X i → Y i → Prop)
    (enc : Encoding I Y T C Z) (encW : ∀ i, X i ↪ List Bool)
    (setup : ℕ → PMF I) (adversary : CHVZKAdversary I) (n : ℕ) : Game :=
  chvzkGameWith R enc encW setup (encodedConversation P enc) adversary n

/-- Experiment 1 of Attack Game 20.4 ([BonehShoup2023], Section 20.4.2, p. 840): on a valid encoded
witness-statement pair `(x, y)` chosen by `adversary`, give `adversary.guess` a simulated
conversation produced from `y` and a uniform challenge without using `x`. -/
noncomputable def chvzkSimGame
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (R : ∀ i, X i → Y i → Prop)
    (enc : Encoding I Y T C Z) (encW : ∀ i, X i ↪ List Bool)
    (setup : ℕ → PMF I)
    (sim : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (adversary : CHVZKAdversary I) (n : ℕ) : Game :=
  chvzkGameWith R enc encW setup (fun i _ y => simulatedConversation enc sim i y) adversary n

/-- **Computational special honest-verifier zero knowledge** ([BonehShoup2023], Section 20.4.2,
Definition 20.6, p. 840), for a family `P` of Sigma protocols over `setup` with explicit word
simulator `sim` and acceptance error `δ`: `sim` is uniform strict PPT, outputs an encoded accepting
conversation on every `(i, y, c)` with probability at least `1 - δ i` (exact Definition 20.6
acceptance when `δ = fun _ => 0`), and every uniform strict PPT `CHVZKAdversary` has negligible
distinguishing advantage between `chvzkRealGame` and `chvzkSimGame`. -/
structure ComputationalSpecialHVZK
    (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (R : ∀ i, X i → Y i → Prop)
    (enc : Encoding I Y T C Z) (encW : ∀ i, X i ↪ List Bool)
    (setup : ℕ → PMF I)
    (sim : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (δ : I → ℝ≥0∞) : Prop where
  /-- The simulator is uniform strict PPT in the index and the encoded statement and challenge. -/
  ppt : IsPPTOn (encSimulatorInput enc.index) (encPair encBits encBits) sim
  /-- On every statement and challenge, `sim` outputs an encoded accepting conversation with
  probability at least `1 - δ i`. -/
  accepts : ∀ i (y : Y i) (c : C i), 1 - δ i ≤
    (ProbComp.eval (sim (i, enc.statement i y, enc.challenge i c))).toOuterMeasure
      {w | ∃ t z, w = (enc.commitment i t, enc.response i z) ∧ (P i).Accepts y t c z}
  /-- Honest and simulated conversations are computationally indistinguishable in Attack Game
  20.4. -/
  indistinguishable :
    Game.Indistinguishable (chvzkRealGame P R enc encW setup)
      (chvzkSimGame R enc encW setup sim) (CHVZKAdversary.IsPPT enc.index)

/-- Relaxing the acceptance-error bound preserves `ComputationalSpecialHVZK`. -/
theorem ComputationalSpecialHVZK.mono_error
    {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    {R : ∀ i, X i → Y i → Prop}
    {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool}
    {setup : ℕ → PMF I}
    {sim : I × List Bool × List Bool → ProbComp (List Bool × List Bool)}
    {δ δ' : I → ℝ≥0∞}
    (h : ComputationalSpecialHVZK P R enc encW setup sim δ) (hle : ∀ i, δ i ≤ δ' i) :
    ComputationalSpecialHVZK P R enc encW setup sim δ' where
  ppt := h.ppt
  accepts i y c := (tsub_le_tsub_left (hle i) 1).trans (h.accepts i y c)
  indistinguishable := h.indistinguishable

/-! ### Bridging statistical `EfficientSpecialHVZK` to `ComputationalSpecialHVZK` -/

section StatisticalBridge

variable {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
  [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
  {R : ∀ i, X i → Y i → Prop}
  {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool}
  {setup : ℕ → PMF I}
  {simulate : ∀ i, Y i → C i → PMF (T i × Z i)}
  {sim : I × List Bool × List Bool → ProbComp (List Bool × List Bool)}
  {δ : I → ℝ≥0∞}

/-- A program realizing a perfect special HVZK simulator up to `δ i` produces simulated encoded
conversations within statistical distance `δ i` of honest encoded conversations, for every valid
witness-statement pair. -/
theorem SimulatorRealizedBy.closeTo_conversation
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy enc simulate sim δ)
    {i : I} {x : X i} {y : Y i} (hxy : R i x y) :
    CloseTo (encodedConversation P enc i x y) (simulatedConversation enc sim i y) (δ i) := by
  let post (c : C i) (p : List Bool × List Bool) : List Bool × List Bool × List Bool :=
    (p.1, enc.challenge i c, p.2)
  have henc : encodedConversation P enc i x y =
      (PMF.uniformOfFintype (C i)).bind fun c =>
        ((simulate i y c).map (Prod.map (enc.commitment i) (enc.response i))).map (post c) := by
    rw [encodedConversation, (hS i).conversation_eq hxy]
    simp only [pmf_norm]
    apply congrArg (PMF.bind _)
    funext c
    rw [← PMF.bind_pure_comp]
    rfl
  have hsim : simulatedConversation enc sim i y =
      (PMF.uniformOfFintype (C i)).bind fun c =>
        (ProbComp.eval (sim (i, enc.statement i y, enc.challenge i c))).map (post c) := by
    simp only [simulatedConversation, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    apply congrArg (PMF.bind _)
    funext c
    rw [← PMF.bind_pure_comp]
    rfl
  rw [henc, hsim]
  exact CloseTo.bind_right (PMF.uniformOfFintype (C i)) fun c _ => (h i y c).map (post c)

/-- When `δ i ≤ ε` on `(setup n).support`, a program realizing a perfect special HVZK simulator has
Attack Game 20.4 advantage at most `ε` against *every* adversary (including computationally
unbounded adversaries). -/
theorem SimulatorRealizedBy.advantage_chvzkGame_le
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy enc simulate sim δ)
    {n : ℕ} {ε : ℝ≥0} (hδ : ∀ i ∈ (setup n).support, δ i ≤ ε)
    (adversary : CHVZKAdversary I) :
    Game.advantage (chvzkRealGame P R enc encW setup adversary n)
      (chvzkSimGame R enc encW setup sim adversary n) ≤ ε := by
  simp only [chvzkRealGame, chvzkSimGame, chvzkGameWith, PMF.monad_bind_eq_bind]
  refine Game.advantage_bind_le_of_support (setup n) _ _ fun i hi => ?_
  refine Game.advantage_bind_le_nnreal (ProbComp.eval (adversary.choose n i)) _ _
    fun ⟨⟨xw, yw⟩, state⟩ => ?_
  classical
  by_cases hv : ∃ p : X i × Y i, encW i p.1 = xw ∧ enc.statement i p.2 = yw ∧ R i p.1 p.2
  · obtain ⟨⟨x, y⟩, rfl, rfl, hxy⟩ := hv
    simp only [chvzkBranch_valid _ _ _ _ hxy]
    exact Game.advantage_bind_le_of_closeTo ((h.closeTo_conversation hS hxy).mono (hδ i hi)) _
  · simp only [chvzkBranch_invalid _ _ _ _ _ hv, Game.advantage_self, zero_le]

/-- A strict PPT program realizing a perfect special HVZK simulator with negligible statistical
error along `setup` gives `ComputationalSpecialHVZK`, retaining any independently proved acceptance
error `δ'`. -/
theorem SimulatorRealizedBy.computationalSpecialHVZK_of_accepts
    {δ' : I → ℝ≥0∞}
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (hppt : IsPPTOn (encSimulatorInput enc.index) (encPair encBits encBits) sim)
    (hreal : SimulatorRealizedBy enc simulate sim δ)
    (hacc : ∀ i (y : Y i) (c : C i), 1 - δ' i ≤
      (ProbComp.eval (sim (i, enc.statement i y, enc.challenge i c))).toOuterMeasure
        {w | ∃ t z, w = (enc.commitment i t, enc.response i z) ∧ (P i).Accepts y t c z})
    (hnegl : ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, ∀ i ∈ (setup n).support, δ i ≤ ε n) :
    ComputationalSpecialHVZK P R enc encW setup sim δ' where
  ppt := hppt
  accepts := hacc
  indistinguishable adversary _ := by
    obtain ⟨ε, hε, hle⟩ := hnegl
    exact negligible_of_le hε fun n => hreal.advantage_chvzkGame_le hS (hle n) adversary

/-- A strict PPT program realizing a perfect special HVZK simulator with negligible statistical
error along `setup` satisfies `ComputationalSpecialHVZK` with acceptance error `δ`. -/
theorem SimulatorRealizedBy.computationalSpecialHVZK
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (hppt : IsPPTOn (encSimulatorInput enc.index) (encPair encBits encBits) sim)
    (hreal : SimulatorRealizedBy enc simulate sim δ)
    (hnegl : ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, ∀ i ∈ (setup n).support, δ i ≤ ε n) :
    ComputationalSpecialHVZK P R enc encW setup sim δ :=
  hreal.computationalSpecialHVZK_of_accepts hS hppt (hreal.one_sub_le_accepts hS) hnegl

/-- **Efficient statistical special HVZK implies computational special HVZK** whenever the
realization error `δ` is bounded along `setup` by a negligible function. -/
theorem EfficientSpecialHVZK.exists_computationalSpecialHVZK
    (h : EfficientSpecialHVZK P R enc simulate δ)
    (encW : ∀ i, X i ↪ List Bool) (setup : ℕ → PMF I)
    (hnegl : ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, ∀ i ∈ (setup n).support, δ i ≤ ε n) :
    ∃ sim, ComputationalSpecialHVZK P R enc encW setup sim δ := by
  obtain ⟨sim, hppt, hreal⟩ := h.realized
  exact ⟨sim, hreal.computationalSpecialHVZK h.specialHVZK hppt hnegl⟩

end StatisticalBridge

end Cslib.Crypto.Protocols.SigmaProtocol
