/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Basic
import CslibFrontier.Tactic.PMFSwap

/-!
# Rerandomizable garbling schemes

A *rerandomizable garbling scheme* (RGS), adapting Acharya, Hazay, Kolesnikov and Prabhakaran
[AcharyaHazayKolesnikovPrabhakaran2024, Definition 3] (full version, ePrint 2024/383), is a
projective garbling scheme with an extra algorithm `rerand` that takes a garbled circuit `gc` and
returns a fresh-looking garbled circuit `gc'` together with one label permutation per input wire.
Applying the permutations to the input labels of `gc` gives the input labels of `gc'`, so an
evaluator holding an encoding for `gc` can move to `gc'` without the garbler. All randomness is
explicit: `garble f r` garbles `f` with coins `r`, returning a `Garbled` record (the circuit and
its label pairs), and `rerand gc r'` rerandomizes with coins `r'`, returning a `Rerandomized`
record (the new circuit and its wire permutations). Decoding is folded into `evaluate`.
Unlike `Cslib.Crypto.Garbling.Scheme`
(`CslibFrontier/Crypto/Primitives/Garbling/Scheme.lean`), which is typed by `List Bool`,
indexed by a security parameter, and intentionally omits projective structure,
`RerandomizableGarbling` exposes per-wire label pairs so per-wire permutations can act directly
on encodings.

*Randomness composition* (`RandomnessComposition`) says that a rerandomized garbling
(`rerandGarbled`) is itself an honest garbling, with coins `explainGb r r'` computed from the
garbling coins and the rerandomization coins, and that two rerandomizations (`rerandTwice`)
compose into one with coins `explainRerand r₁ r₂`. The garbling half adapts the
randomness-composition property of Definition 3, while `explainRerand` is an explicit two-step
rerandomization-composition axiom of this formalization. With `garble_explainGb`, correctness of
fresh garblings implies correctness of rerandomized ones (`rerandCorrect_of_correct`).

Two security notions are compared. Each has a view record handed to the distinguisher, a real
and an ideal sampler of that view, the two experiments running a distinguisher on the sampled
view, and an advantage; the projective encoding is `encode`, and `permEncoding` and `permInput`
apply wire permutations.

* **Rerandomization privacy** (`RerandView`, `rerandRealView`, `rerandIdealView`; adapting
  Definition 3): given the garbling coins `r`, the rerandomized circuit and the rerandomized
  encoding of `x` look like a fresh garbling of `f` with an honest encoding of `x`.
* **Explainability** (adapting Definition 9, p. 33 of ePrint 2024/383). Explainable garbling
  (`ExplainGbView`, `explainGbRealView`, `explainGbIdealView`): given an encoding of `x` for `gc`
  and a rerandomization of `gc` over uniformly sampled garbling and rerandomization coins, the
  coins `explainGb r r'` look like the coins of a fresh garbling. Explainable rerandomization
  (`ExplainRerandView`, `explainRerandRealView`, `explainRerandIdealView`): given a
  rerandomization `gc₁` of `gc` and a rerandomization `gc₂` of `gc₁` over uniformly sampled coins,
  the coins `explainRerand r₁ r₂` look like coins that rerandomize `gc` directly.

This development proves two generic single-instance reductions relating sampled-coin
explainability to rerandomization privacy under explicit algebraic invertibility hypotheses
(`RandomnessComposition.Invertible`). The advantage of any distinguisher against explainable
garbling *equals* the rerandomization-privacy advantage of `explainGbReduction`
(`explainGbAdvantage_eq`). The advantage against explainable rerandomization is at most the sum of
the rerandomization-privacy advantages of two reductions (`explainRerandAdvantage_le`), through one
intermediate hybrid: the right reduction run on the ideal rerandomization-privacy view, which has
the same law as the left reduction on that view. Running the right reduction on the real view is
the ideal explainable-rerandomization experiment, by definition
(`rerandRealExperiment_explainRerandReductionRight`). Both reductions use the inverse data of
`RandomnessComposition.Invertible` (introduced for this development): the garbling explanation is
a bijection in the garbling coins with an explicit inverse, the rerandomization explanation is a
bijection in its first argument, and some rerandomization coins undo each rerandomization step.
The rerandomization bound also assumes that the label action respects composition of permutations.

When the explanation maps are bijective in their *second* argument, rerandomization privacy and the
stronger fixed-coin explainability variants (`explainGbFixedRealView`,
`explainRerandFixedRealView`, which hold the base coins `r` and `r₁` fixed rather than sampling
them) hold with zero error, as equalities of view laws (`eval_explainGbFixedRealView`,
`eval_explainRerandFixedRealView`, `eval_rerandRealView`).

## Scope

In `explainGbRealView`/`explainGbIdealView` and `explainRerandRealView`/`explainRerandIdealView`,
the garbling and rerandomization coins are sampled uniformly (matching the sampled-coin experiment
structure of Definition 9 in ePrint 2024/383, p. 33): each samples the base coins and runs its
fixed-coin variant `explainGbFixed*View` or `explainRerandFixed*View`, which appear in the
zero-error bijectivity lemmas. On the hypothesis side, `rerandRealView` samples `r` uniformly
whereas Definition 3 quantifies over fixed `r`; because privacy at every fixed `r` implies privacy
for uniformly sampled `r`, the sampled-`r` assumption used by the reductions is weaker. The generic
reductions `explainGbAdvantage_eq` and `explainRerandAdvantage_le`, together with the two-step
composition field `explainRerand` and the inverse structure `RandomnessComposition.Invertible`, are
results and hypotheses of this development rather than transcriptions of a numbered theorem in the
paper. All statements are single-instance: the function, input and distinguisher are fixed, and
running time is not tracked, so no asymptotic security or efficiency of the reductions is claimed.

## Main definitions

* `Cslib.Crypto.Garbling.RerandomizableGarbling`: an RGS with explicit coins, with outputs
  `Cslib.Crypto.Garbling.RerandomizableGarbling.Garbled` and
  `Cslib.Crypto.Garbling.RerandomizableGarbling.Rerandomized`.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.encode`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.permEncoding`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.permInput`: projective encoding and permutations.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.evalGarbled`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandGarbled`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandTwice`: evaluating a garbling, and
  rerandomizing it once or twice.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.Correct`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.RerandCorrect`: correctness.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.RandomnessComposition`: randomness composition.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.RandomnessComposition.Invertible`: the inverse
  data used by the reductions.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.RerandView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.ExplainGbView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.ExplainRerandView`: what the distinguisher sees.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandRealView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandIdealView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbRealView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbIdealView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandRealView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandIdealView`, and the fixed-coin
  variants `explainGbFixedRealView`, `explainGbFixedIdealView`, `explainRerandFixedRealView`,
  `explainRerandFixedIdealView`: the view samplers.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandRealExperiment`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandIdealExperiment`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbRealExperiment`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbIdealExperiment`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandRealExperiment`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandIdealExperiment`: the experiments.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbReduction`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandReductionLeft`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandReductionRight`: the reductions.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandAdvantage`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbAdvantage`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandAdvantage`: distinguishing
  advantages.

## Main results

* `Cslib.Crypto.Garbling.RerandomizableGarbling.encode_permEncoding`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.permInput_comp`,
  `RerandomizableGarbling.RandomnessComposition.Invertible.permInput_invRerand`,
  `RerandomizableGarbling.RandomnessComposition.Invertible.explainGb_bijective`:
  algebraic lemmas.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandCorrect_of_correct`.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbAdvantage_eq`.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandAdvantage_le`, with
  `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandRealExperiment_explainRerandReductionRight`.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.eval_rerandRealView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.eval_explainGbFixedRealView`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.eval_explainRerandFixedRealView`: zero error
  under bijectivity in the second argument.

## References

* [A. Acharya, C. Hazay, V. Kolesnikov, M. Prabhakaran, *Malicious Security for SCALES:
  Outsourced Computation with Ephemeral Servers*][AcharyaHazayKolesnikovPrabhakaran2024];
  definition and theorem numbers refer to the full version, ePrint 2024/383.
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open Probability
open scoped NNReal

/-- The output of garbling: a garbled circuit and, for each of the `m` input wires, its pair of
labels for the bits `false` and `true`. -/
@[ext] structure RerandomizableGarbling.Garbled (GC Label : Type) (m : ℕ) where
  /-- The garbled circuit. -/
  circuit : GC
  /-- The labels of each input wire, for the bits `false` and `true`. -/
  labels : Fin m → Label × Label

/-- The output of rerandomization: a rerandomized circuit and one label permutation per input
wire, carrying the labels of the old circuit to those of the new one. -/
@[ext] structure RerandomizableGarbling.Rerandomized (GC Perm : Type) (m : ℕ) where
  /-- The rerandomized circuit. -/
  circuit : GC
  /-- The label permutation of each input wire. -/
  perm : Fin m → Perm

/-- A projective rerandomizable garbling scheme for functions `F` on `m` input bits, with explicit
garbling coins `Coins` and rerandomization coins `RerandCoins`. `garble f r` returns a garbled
circuit and one pair of labels per input wire (for bits `false` and `true`); `rerand gc r'`
returns a rerandomized circuit and one label permutation per input wire, acting on labels by
`act`; `comp p q` is meant as the permutation `p` followed by `q`, a property that is not part of
the structure and is assumed where needed (`explainRerandAdvantage_le`). -/
structure RerandomizableGarbling (F : Type) (m : ℕ) where
  /-- Garbled circuits. -/
  GC : Type
  /-- Wire labels. -/
  Label : Type
  /-- Label permutations. -/
  Perm : Type
  /-- Garbling coins. -/
  Coins : Type
  /-- Rerandomization coins. -/
  RerandCoins : Type
  /-- Outputs. -/
  Out : Type
  [fintypeCoins : Fintype Coins]
  [nonemptyCoins : Nonempty Coins]
  [fintypeRerandCoins : Fintype RerandCoins]
  [nonemptyRerandCoins : Nonempty RerandCoins]
  /-- The function computed by a description. -/
  evalFn : F → (Fin m → Bool) → Out
  /-- Garbling with given coins. -/
  garble : F → Coins → RerandomizableGarbling.Garbled GC Label m
  /-- Rerandomization with given coins. -/
  rerand : GC → RerandCoins → RerandomizableGarbling.Rerandomized GC Perm m
  /-- The action of permutations on labels. -/
  act : Perm → Label → Label
  /-- Composition of permutations, meant as `p` followed by `q`. -/
  comp : Perm → Perm → Perm
  /-- Evaluation of a garbled circuit on one label per input wire. -/
  evaluate : GC → (Fin m → Label) → Out

attribute [instance] RerandomizableGarbling.fintypeCoins RerandomizableGarbling.nonemptyCoins
  RerandomizableGarbling.fintypeRerandCoins RerandomizableGarbling.nonemptyRerandCoins

namespace RerandomizableGarbling

variable {F : Type} {m : ℕ} (G : RerandomizableGarbling F m)

/-! ### Encodings and correctness -/

/-- The projective input encoding: the label of bit `x i` on each wire `i`. -/
def encode (e : Fin m → G.Label × G.Label) (x : Fin m → Bool) : Fin m → G.Label :=
  fun i => if x i then (e i).2 else (e i).1

/-- Apply one permutation per wire to both labels of an encoding table. -/
def permEncoding (π : Fin m → G.Perm) (e : Fin m → G.Label × G.Label) :
    Fin m → G.Label × G.Label :=
  fun i => (G.act (π i) (e i).1, G.act (π i) (e i).2)

/-- Apply one permutation per wire to an encoded input. -/
def permInput (π : Fin m → G.Perm) (X : Fin m → G.Label) : Fin m → G.Label :=
  fun i => G.act (π i) (X i)

/-- Encoding commutes with permuting the labels. -/
theorem encode_permEncoding (π : Fin m → G.Perm) (e : Fin m → G.Label × G.Label)
    (x : Fin m → Bool) : G.encode (G.permEncoding π e) x = G.permInput π (G.encode e x) := by
  funext i
  simp only [encode, permEncoding, permInput]
  split <;> rfl

/-- Evaluate a garbling on input `x`: run its circuit on the encoding of `x`. -/
def evalGarbled (g : Garbled G.GC G.Label m) (x : Fin m → Bool) : G.Out :=
  G.evaluate g.circuit (G.encode g.labels x)

/-- Rerandomize a garbling with coins `r'`: the rerandomized circuit, with the labels permuted by
the rerandomization's wire permutations. -/
def rerandGarbled (g : Garbled G.GC G.Label m) (r' : G.RerandCoins) :
    Garbled G.GC G.Label m :=
  let q := G.rerand g.circuit r'
  { circuit := q.circuit, labels := G.permEncoding q.perm g.labels }

/-- Rerandomize `gc` with coins `r₁` and then `r₂`: the final circuit, with each wire's two
permutations composed. -/
def rerandTwice (gc : G.GC) (r₁ r₂ : G.RerandCoins) : Rerandomized G.GC G.Perm m :=
  let q₁ := G.rerand gc r₁
  let q₂ := G.rerand q₁.circuit r₂
  { circuit := q₂.circuit, perm := fun i => G.comp (q₁.perm i) (q₂.perm i) }

/-- Correctness of fresh garblings: evaluating `garble f r` on `x` gives `f x`. -/
def Correct : Prop :=
  ∀ (f : F) (x : Fin m → Bool) (r : G.Coins), G.evalGarbled (G.garble f r) x = G.evalFn f x

/-- Correctness of rerandomized garblings: evaluating the rerandomization of `garble f r` on `x`
gives `f x`. -/
def RerandCorrect : Prop :=
  ∀ (f : F) (x : Fin m → Bool) (r : G.Coins) (r' : G.RerandCoins),
    G.evalGarbled (G.rerandGarbled (G.garble f r) r') x = G.evalFn f x

/-- Randomness composition. A rerandomization of `garble f r` with coins `r'`, with its permuted
encoding table, is the honest garbling of `f` with coins `explainGb r r'`; and rerandomizing
`garble f r` with coins `r₁` and then `r₂` gives the rerandomization with coins
`explainRerand r₁ r₂`, with the composed permutations. -/
structure RandomnessComposition where
  /-- The garbling coins that explain a rerandomized garbling. -/
  explainGb : G.Coins → G.RerandCoins → G.Coins
  /-- The rerandomization coins that explain two rerandomization steps. -/
  explainRerand : G.RerandCoins → G.RerandCoins → G.RerandCoins
  garble_explainGb : ∀ (f : F) (r : G.Coins) (r' : G.RerandCoins),
    G.garble f (explainGb r r') = G.rerandGarbled (G.garble f r) r'
  rerand_explainRerand : ∀ (f : F) (r : G.Coins) (r₁ r₂ : G.RerandCoins),
    G.rerand (G.garble f r).circuit (explainRerand r₁ r₂) =
      G.rerandTwice (G.garble f r).circuit r₁ r₂

variable {G}

/-- Under randomness composition, correctness of fresh garblings gives correctness of
rerandomized ones. -/
theorem rerandCorrect_of_correct (rc : G.RandomnessComposition) (h : G.Correct) :
    G.RerandCorrect := by
  intro f x r r'
  rw [← rc.garble_explainGb]
  exact h f x (rc.explainGb r r')

/-- Inverse data for randomness composition, used by the reductions from rerandomization privacy
to explainability: `unexplainGb · r'` inverts `explainGb · r'`, `explainRerand` is a bijection in
its first argument, and the coins `invRerand r'` undo a rerandomization step with coins `r'`, on
the circuit and on every label. -/
structure RandomnessComposition.Invertible (rc : G.RandomnessComposition) where
  /-- The inverse of `explainGb · r'`. -/
  unexplainGb : G.Coins → G.RerandCoins → G.Coins
  unexplainGb_explainGb : ∀ r r', unexplainGb (rc.explainGb r r') r' = r
  explainGb_unexplainGb : ∀ r r', rc.explainGb (unexplainGb r r') r' = r
  explainRerand_bijective : ∀ r₂, Function.Bijective (rc.explainRerand · r₂)
  /-- Coins that undo a rerandomization step. -/
  invRerand : G.RerandCoins ≃ G.RerandCoins
  rerand_invRerand : ∀ (gc : G.GC) (r' : G.RerandCoins),
    (G.rerand (G.rerand gc r').circuit (invRerand r')).circuit = gc
  act_invRerand : ∀ (gc : G.GC) (r' : G.RerandCoins) (i : Fin m) (L : G.Label),
    G.act ((G.rerand (G.rerand gc r').circuit (invRerand r')).perm i)
      (G.act ((G.rerand gc r').perm i) L) = L

variable (G)

/-! ### Views -/

/-- What a rerandomization-privacy distinguisher sees. -/
structure RerandView where
  /-- The coins of the base garbling. -/
  coins : G.Coins
  /-- The challenge circuit. -/
  circuit : G.GC
  /-- The evaluator's input labels for the challenge circuit. -/
  input : Fin m → G.Label

/-- What an explainable-garbling distinguisher sees. -/
structure ExplainGbView where
  /-- The evaluator's input labels for the base circuit. -/
  input : Fin m → G.Label
  /-- The base circuit. -/
  base : G.GC
  /-- The challenge circuit. -/
  candidate : G.GC
  /-- The garbling coins claimed to produce the challenge circuit. -/
  coins : G.Coins

/-- What an explainable-rerandomization distinguisher sees. -/
structure ExplainRerandView where
  /-- The base circuit. -/
  base : G.GC
  /-- The evaluator's input labels for the first rerandomization. -/
  input : Fin m → G.Label
  /-- The first rerandomization of the base circuit. -/
  rerandomized : G.GC
  /-- The challenge circuit. -/
  candidate : G.GC
  /-- The rerandomization coins claimed to carry the base circuit to the challenge circuit. -/
  coins : G.RerandCoins

/-! ### View samplers -/

/-- Rerandomization privacy, real view: garble with uniform coins `r`, rerandomize with uniform
coins, and show `r`, the rerandomized circuit and the permuted encoding of `x`. -/
noncomputable def rerandRealView (f : F) (x : Fin m → Bool) : ProbComp G.RerandView := do
  let r ← ProbComp.uniform G.Coins
  let r' ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let q := G.rerand g.circuit r'
  return { coins := r, circuit := q.circuit, input := G.permInput q.perm (G.encode g.labels x) }

/-- Rerandomization privacy, ideal view: uniform coins `r` together with an independent fresh
garbling and the encoding of `x`. -/
noncomputable def rerandIdealView (f : F) (x : Fin m → Bool) : ProbComp G.RerandView := do
  let r ← ProbComp.uniform G.Coins
  let s ← ProbComp.uniform G.Coins
  let g := G.garble f s
  return { coins := r, circuit := g.circuit, input := G.encode g.labels x }

/-- Explainable garbling with fixed garbling coins `r`, real view: the encoding of `x` and the
circuit of `garble f r`, a rerandomization of that circuit with uniform coins `r'`, and the
explanation `explainGb r r'`. -/
noncomputable def explainGbFixedRealView (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool) (r : G.Coins) : ProbComp G.ExplainGbView := do
  let r' ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  return {
    input := G.encode g.labels x, base := g.circuit,
    candidate := (G.rerand g.circuit r').circuit, coins := rc.explainGb r r' }

/-- Explainable garbling with fixed garbling coins `r`, ideal view: the challenge is a fresh
garbled circuit and its coins. -/
noncomputable def explainGbFixedIdealView (f : F) (x : Fin m → Bool) (r : G.Coins) :
    ProbComp G.ExplainGbView := do
  let s ← ProbComp.uniform G.Coins
  let g := G.garble f r
  return {
    input := G.encode g.labels x, base := g.circuit,
    candidate := (G.garble f s).circuit, coins := s }

/-- Explainable garbling, real view (sampled garbling coins). -/
noncomputable def explainGbRealView (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool) :
    ProbComp G.ExplainGbView := do
  let r ← ProbComp.uniform G.Coins
  G.explainGbFixedRealView rc f x r

/-- Explainable garbling, ideal view (sampled garbling coins). -/
noncomputable def explainGbIdealView (f : F) (x : Fin m → Bool) : ProbComp G.ExplainGbView := do
  let r ← ProbComp.uniform G.Coins
  G.explainGbFixedIdealView f x r

/-- Explainable rerandomization with fixed coins `r` and `r₁`, real view: garble with coins `r`,
rerandomize with `r₁` and then uniform `r₂`, and show the base circuit, the encoding of `x` for
the first rerandomization, both rerandomized circuits and the explanation `explainRerand r₁ r₂`. -/
noncomputable def explainRerandFixedRealView (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool) (r : G.Coins) (r₁ : G.RerandCoins) : ProbComp G.ExplainRerandView := do
  let r₂ ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let q := G.rerand g.circuit r₁
  return {
    base := g.circuit, input := G.permInput q.perm (G.encode g.labels x),
    rerandomized := q.circuit, candidate := (G.rerand q.circuit r₂).circuit,
    coins := rc.explainRerand r₁ r₂ }

/-- Explainable rerandomization with fixed coins `r` and `r₁`, ideal view: the challenge is a
direct rerandomization of the base circuit and its coins. -/
noncomputable def explainRerandFixedIdealView (f : F) (x : Fin m → Bool) (r : G.Coins)
    (r₁ : G.RerandCoins) : ProbComp G.ExplainRerandView := do
  let s ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let q := G.rerand g.circuit r₁
  return {
    base := g.circuit, input := G.permInput q.perm (G.encode g.labels x),
    rerandomized := q.circuit, candidate := (G.rerand g.circuit s).circuit, coins := s }

/-- Explainable rerandomization, real view (sampled coins). -/
noncomputable def explainRerandRealView (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool) : ProbComp G.ExplainRerandView := do
  let r ← ProbComp.uniform G.Coins
  let r₁ ← ProbComp.uniform G.RerandCoins
  G.explainRerandFixedRealView rc f x r r₁

/-- Explainable rerandomization, ideal view (sampled coins). -/
noncomputable def explainRerandIdealView (f : F) (x : Fin m → Bool) :
    ProbComp G.ExplainRerandView := do
  let r ← ProbComp.uniform G.Coins
  let r₁ ← ProbComp.uniform G.RerandCoins
  G.explainRerandFixedIdealView f x r r₁

/-! ### Experiments and advantages -/

/-- The real rerandomization-privacy experiment: `D` guesses on the real view. -/
noncomputable def rerandRealExperiment (f : F) (x : Fin m → Bool)
    (D : G.RerandView → ProbComp Bool) : ProbComp Bool := do
  let v ← G.rerandRealView f x
  D v

/-- The ideal rerandomization-privacy experiment: `D` guesses on the ideal view. -/
noncomputable def rerandIdealExperiment (f : F) (x : Fin m → Bool)
    (D : G.RerandView → ProbComp Bool) : ProbComp Bool := do
  let v ← G.rerandIdealView f x
  D v

/-- The real explainable-garbling experiment: `D` guesses on the real view. -/
noncomputable def explainGbRealExperiment (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool) (D : G.ExplainGbView → ProbComp Bool) : ProbComp Bool := do
  let v ← G.explainGbRealView rc f x
  D v

/-- The ideal explainable-garbling experiment: `D` guesses on the ideal view. -/
noncomputable def explainGbIdealExperiment (f : F) (x : Fin m → Bool)
    (D : G.ExplainGbView → ProbComp Bool) : ProbComp Bool := do
  let v ← G.explainGbIdealView f x
  D v

/-- The real explainable-rerandomization experiment: `D` guesses on the real view. -/
noncomputable def explainRerandRealExperiment (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool) (D : G.ExplainRerandView → ProbComp Bool) : ProbComp Bool := do
  let v ← G.explainRerandRealView rc f x
  D v

/-- The ideal explainable-rerandomization experiment: `D` guesses on the ideal view. -/
noncomputable def explainRerandIdealExperiment (f : F) (x : Fin m → Bool)
    (D : G.ExplainRerandView → ProbComp Bool) : ProbComp Bool := do
  let v ← G.explainRerandIdealView f x
  D v

/-- The advantage of `D` in telling the real rerandomization-privacy view from the ideal one. -/
noncomputable def rerandAdvantage (f : F) (x : Fin m → Bool)
    (D : G.RerandView → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (G.rerandRealExperiment f x D))
    (ProbComp.eval (G.rerandIdealExperiment f x D))

/-- The advantage of `D` in telling the real explainable-garbling view from the ideal one. -/
noncomputable def explainGbAdvantage (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool)
    (D : G.ExplainGbView → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (G.explainGbRealExperiment rc f x D))
    (ProbComp.eval (G.explainGbIdealExperiment f x D))

/-- The advantage of `D` in telling the real explainable-rerandomization view from the ideal
one. -/
noncomputable def explainRerandAdvantage (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool) (D : G.ExplainRerandView → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (G.explainRerandRealExperiment rc f x D))
    (ProbComp.eval (G.explainRerandIdealExperiment f x D))

/-! ### Reductions -/

/-- The rerandomization-privacy distinguisher built from an explainable-garbling distinguisher:
it shows `D` the challenge input labels and circuit as the base, and the circuit of
`garble f v.coins` with those coins as the challenge. -/
def explainGbReduction (f : F) (D : G.ExplainGbView → ProbComp Bool) :
    G.RerandView → ProbComp Bool :=
  fun v => D {
    input := v.input, base := v.circuit, candidate := (G.garble f v.coins).circuit,
    coins := v.coins }

/-- The first rerandomization-privacy distinguisher built from an explainable-rerandomization
distinguisher: it samples `s`, takes the base circuit garbled with coins `unexplainGb v.coins s`,
and shows `D` that base, the challenge input labels and circuit, the base's rerandomization with
coins `s`, and `s`. -/
noncomputable def explainRerandReductionLeft {rc : G.RandomnessComposition}
    (hinv : rc.Invertible) (f : F) (D : G.ExplainRerandView → ProbComp Bool) :
    G.RerandView → ProbComp Bool := fun v => do
  let s ← ProbComp.uniform G.RerandCoins
  let base := (G.garble f (hinv.unexplainGb v.coins s)).circuit
  D {
    base := base, input := v.input, rerandomized := v.circuit,
    candidate := (G.rerand base s).circuit, coins := s }

/-- The second rerandomization-privacy distinguisher built from an explainable-rerandomization
distinguisher: it samples `s`, takes the base circuit garbled with coins `v.coins`, and shows `D`
that base, the challenge input labels and circuit, the base's rerandomization with coins `s`, and
`s`. -/
noncomputable def explainRerandReductionRight (f : F)
    (D : G.ExplainRerandView → ProbComp Bool) : G.RerandView → ProbComp Bool := fun v => do
  let s ← ProbComp.uniform G.RerandCoins
  let base := (G.garble f v.coins).circuit
  D {
    base := base, input := v.input, rerandomized := v.circuit,
    candidate := (G.rerand base s).circuit, coins := s }

/-! ### Permutation lemmas -/

variable {G}

/-- Permuting by composed permutations is permuting twice, when the action respects
composition. -/
theorem permInput_comp
    (hcomp : ∀ (p q : G.Perm) (L : G.Label), G.act (G.comp p q) L = G.act q (G.act p L))
    (π₁ π₂ : Fin m → G.Perm) (X : Fin m → G.Label) :
    G.permInput (fun i => G.comp (π₁ i) (π₂ i)) X = G.permInput π₂ (G.permInput π₁ X) :=
  funext fun i => hcomp (π₁ i) (π₂ i) (X i)

/-- The permutations of the undoing rerandomization step invert those of the original step. -/
theorem RandomnessComposition.Invertible.permInput_invRerand {rc : G.RandomnessComposition}
    (hinv : rc.Invertible) (gc : G.GC) (r' : G.RerandCoins) (X : Fin m → G.Label) :
    G.permInput (G.rerand (G.rerand gc r').circuit (hinv.invRerand r')).perm
      (G.permInput (G.rerand gc r').perm X) = X :=
  funext fun i => hinv.act_invRerand gc r' i (X i)

/-- `explainGb · r'` is a bijection. -/
theorem RandomnessComposition.Invertible.explainGb_bijective {rc : G.RandomnessComposition}
    (hinv : rc.Invertible) (r' : G.RerandCoins) : Function.Bijective (rc.explainGb · r') :=
  Function.bijective_iff_has_inverse.mpr ⟨(hinv.unexplainGb · r'),
    fun r => hinv.unexplainGb_explainGb r r', fun r => hinv.explainGb_unexplainGb r r'⟩

/-! ### Reindexing uniform samples -/

section Reindex

variable {α β γ δ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
  [Fintype δ] [Nonempty δ]

/-- Substituting a bijection into a uniform sample does not change the experiment. -/
private theorem bind_uniform_comp {f : α → β} (hf : Function.Bijective f) {k : β → PMF γ}
    {k' : α → PMF γ} (hk : ∀ a, k' a = k (f a)) :
    (PMF.uniformOfFintype α).bind k' = (PMF.uniformOfFintype β).bind k := by
  rw [show k' = k ∘ Equiv.ofBijective f hf from funext hk, ← PMF.bind_map,
    PMF.uniformOfFintype_map_equiv]

/-- Move the first of three uniform samples innermost and swap the other two. -/
private theorem bind_uniform_rotate (M : α → δ → β → PMF γ) :
    ((PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype δ).bind fun d =>
        (PMF.uniformOfFintype β).bind fun c => M a d c) =
      (PMF.uniformOfFintype β).bind fun c => (PMF.uniformOfFintype δ).bind fun d =>
        (PMF.uniformOfFintype α).bind fun a => M a d c := by
  pmf_swap

/-- Two-sample change of variables `(a, b) ↦ (g b a, h b)`. -/
private theorem bind_bind_uniform_reindex (g : β → α → α) (hg : ∀ b, Function.Bijective (g b))
    (h : β ≃ β) {K K' : α → β → PMF γ} (hK : ∀ a b, K' a b = K (g b a) (h b)) :
    ((PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind (K' a)) =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind (K a) := by
  calc ((PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind (K' a))
      = (PMF.uniformOfFintype β).bind fun b => (PMF.uniformOfFintype α).bind fun a => K' a b :=
        PMF.bind_comm _ _ _
    _ = (PMF.uniformOfFintype β).bind fun b => (PMF.uniformOfFintype α).bind fun a => K a (h b) :=
        congrArg _ (funext fun b => bind_uniform_comp (hg b) fun a => hK a b)
    _ = (PMF.uniformOfFintype β).bind fun b => (PMF.uniformOfFintype α).bind fun a => K a b :=
        bind_uniform_comp h.bijective fun _ => rfl
    _ = _ := (PMF.bind_comm _ _ _).symm

/-- Change of the first of three samples, `a ↦ g c a`, depending on the third. -/
private theorem bind_bind_bind_uniform_reindex_fst (g : β → α → α)
    (hg : ∀ c, Function.Bijective (g c)) {K K' : α → δ → β → PMF γ}
    (hK : ∀ a d c, K' a d c = K (g c a) d c) :
    ((PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype δ).bind fun d =>
        (PMF.uniformOfFintype β).bind fun c => K' a d c) =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype δ).bind fun d =>
        (PMF.uniformOfFintype β).bind fun c => K a d c := by
  rw [bind_uniform_rotate K', bind_uniform_rotate K]
  exact congrArg _ (funext fun c => congrArg _ (funext fun d =>
    bind_uniform_comp (hg c) fun a => hK a d c))

/-- Three-sample change of variables `(a, b, c) ↦ (g (k b c) a, h c, k b c)`. -/
private theorem bind_bind_bind_uniform_reindex (g : β → α → α)
    (hg : ∀ c, Function.Bijective (g c)) (k : β → β → β) (hk : ∀ c, Function.Bijective (k · c))
    (h : β ≃ β) {K K' : α → β → β → PMF γ}
    (hK : ∀ a b c, K' a b c = K (g (k b c) a) (h c) (k b c)) :
    ((PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind fun b =>
        (PMF.uniformOfFintype β).bind fun c => K' a b c) =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind fun b =>
        (PMF.uniformOfFintype β).bind fun c => K a b c := by
  rw [bind_uniform_rotate K', bind_uniform_rotate K]
  calc ((PMF.uniformOfFintype β).bind fun c => (PMF.uniformOfFintype β).bind fun b =>
          (PMF.uniformOfFintype α).bind fun a => K' a b c)
      = (PMF.uniformOfFintype β).bind fun c => (PMF.uniformOfFintype β).bind fun b =>
          (PMF.uniformOfFintype α).bind fun a => K a (h c) (k b c) :=
        congrArg _ (funext fun c => congrArg _ (funext fun b =>
          bind_uniform_comp (hg (k b c)) fun a => hK a b c))
    _ = (PMF.uniformOfFintype β).bind fun c => (PMF.uniformOfFintype β).bind fun s =>
          (PMF.uniformOfFintype α).bind fun a => K a (h c) s :=
        congrArg _ (funext fun c => bind_uniform_comp (hk c) fun _ => rfl)
    _ = (PMF.uniformOfFintype β).bind fun c => (PMF.uniformOfFintype β).bind fun s =>
          (PMF.uniformOfFintype α).bind fun a => K a c s :=
        bind_uniform_comp h.bijective fun _ => rfl
    _ = _ := PMF.bind_comm _ _ _

end Reindex

/-! ### Explainability from rerandomization privacy -/

/-- **Explainable garbling from rerandomization privacy.** For every distinguisher `D`, the
explainable-garbling advantage of `D` equals the rerandomization-privacy advantage of
`explainGbReduction f D`. -/
theorem explainGbAdvantage_eq (rc : G.RandomnessComposition) (hinv : rc.Invertible) (f : F)
    (x : Fin m → Bool) (D : G.ExplainGbView → ProbComp Bool) :
    G.explainGbAdvantage rc f x D = G.rerandAdvantage f x (G.explainGbReduction f D) := by
  have hreal : ProbComp.eval (G.explainGbRealExperiment rc f x D) =
      ProbComp.eval (G.rerandRealExperiment f x (G.explainGbReduction f D)) := by
    simp only [explainGbRealExperiment, explainGbRealView, explainGbFixedRealView,
      rerandRealExperiment, rerandRealView, explainGbReduction, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform]
    refine bind_bind_uniform_reindex (fun r' r => rc.explainGb r r') hinv.explainGb_bijective
      hinv.invRerand fun r r' => ?_
    rw [rc.garble_explainGb]
    dsimp only [rerandGarbled]
    rw [hinv.rerand_invRerand, encode_permEncoding, hinv.permInput_invRerand]
  have hideal : ProbComp.eval (G.explainGbIdealExperiment f x D) =
      ProbComp.eval (G.rerandIdealExperiment f x (G.explainGbReduction f D)) := by
    simp only [explainGbIdealExperiment, explainGbIdealView, explainGbFixedIdealView,
      rerandIdealExperiment, rerandIdealView, explainGbReduction, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform]
    exact PMF.bind_comm _ _ _
  rw [explainGbAdvantage, rerandAdvantage, hreal, hideal]

/-- Running the right reduction on the real rerandomization-privacy view is the ideal
explainable-rerandomization experiment. -/
@[simp] theorem rerandRealExperiment_explainRerandReductionRight (f : F) (x : Fin m → Bool)
    (D : G.ExplainRerandView → ProbComp Bool) :
    G.rerandRealExperiment f x (G.explainRerandReductionRight f D) =
      G.explainRerandIdealExperiment f x D :=
  rfl

/-- **Explainable rerandomization from rerandomization privacy.** If the label action respects
composition of permutations, then for every distinguisher `D` the explainable-rerandomization
advantage of `D` is at most the sum of the rerandomization-privacy advantages of
`explainRerandReductionLeft hinv f D` and `explainRerandReductionRight f D`. The intermediate
hybrid is the right reduction on the ideal view, which equals the left reduction on the ideal
view. -/
theorem explainRerandAdvantage_le (rc : G.RandomnessComposition) (hinv : rc.Invertible)
    (hcomp : ∀ (p q : G.Perm) (L : G.Label), G.act (G.comp p q) L = G.act q (G.act p L))
    (f : F) (x : Fin m → Bool) (D : G.ExplainRerandView → ProbComp Bool) :
    G.explainRerandAdvantage rc f x D ≤
      G.rerandAdvantage f x (G.explainRerandReductionLeft hinv f D) +
        G.rerandAdvantage f x (G.explainRerandReductionRight f D) := by
  have hreal : ProbComp.eval (G.explainRerandRealExperiment rc f x D) =
      ProbComp.eval (G.rerandRealExperiment f x (G.explainRerandReductionLeft hinv f D)) := by
    simp only [explainRerandRealExperiment, explainRerandRealView, explainRerandFixedRealView,
      rerandRealExperiment, rerandRealView, explainRerandReductionLeft, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform]
    refine bind_bind_bind_uniform_reindex (fun s r => rc.explainGb r s) hinv.explainGb_bijective
      rc.explainRerand hinv.explainRerand_bijective hinv.invRerand fun r r₁ r₂ => ?_
    rw [hinv.unexplainGb_explainGb, rc.garble_explainGb]
    dsimp only [rerandGarbled]
    rw [rc.rerand_explainRerand]
    dsimp only [rerandTwice]
    rw [hinv.rerand_invRerand, encode_permEncoding, permInput_comp hcomp,
      hinv.permInput_invRerand]
  have hhyb : ProbComp.eval (G.rerandIdealExperiment f x (G.explainRerandReductionRight f D)) =
      ProbComp.eval (G.rerandIdealExperiment f x (G.explainRerandReductionLeft hinv f D)) := by
    simp only [rerandIdealExperiment, rerandIdealView, explainRerandReductionRight,
      explainRerandReductionLeft, bind_assoc, pure_bind, ProbComp.eval_bind,
      ProbComp.eval_uniform]
    refine bind_bind_bind_uniform_reindex_fst (fun s r => rc.explainGb r s)
      hinv.explainGb_bijective fun r t s => ?_
    rw [hinv.unexplainGb_explainGb]
  calc G.explainRerandAdvantage rc f x D
      ≤ Game.advantage (ProbComp.eval (G.explainRerandRealExperiment rc f x D))
          (ProbComp.eval (G.rerandIdealExperiment f x (G.explainRerandReductionRight f D))) +
        Game.advantage
          (ProbComp.eval (G.rerandIdealExperiment f x (G.explainRerandReductionRight f D)))
          (ProbComp.eval (G.explainRerandIdealExperiment f x D)) :=
        Game.advantage_triangle _ _ _
    _ = _ := by
        rw [rerandAdvantage, rerandAdvantage, rerandRealExperiment_explainRerandReductionRight,
          Game.advantage_comm (ProbComp.eval (G.explainRerandIdealExperiment f x D)), hreal, hhyb]

/-! ### Zero error under bijectivity in the second argument -/

/-- If `explainGb r` is a bijection for every `r`, rerandomization privacy holds with zero
error: the real and ideal views have the same law. -/
theorem eval_rerandRealView (rc : G.RandomnessComposition)
    (h : ∀ r, Function.Bijective (rc.explainGb r)) (f : F) (x : Fin m → Bool) :
    ProbComp.eval (G.rerandRealView f x) = ProbComp.eval (G.rerandIdealView f x) := by
  simp only [rerandRealView, rerandIdealView, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  refine congrArg _ (funext fun r => bind_uniform_comp (h r) fun r' => ?_)
  rw [rc.garble_explainGb]
  dsimp only [rerandGarbled]
  rw [encode_permEncoding]

/-- If `explainGb r` is a bijection, explainable garbling with fixed coins `r` holds with zero
error. -/
theorem eval_explainGbFixedRealView (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool)
    (r : G.Coins) (h : Function.Bijective (rc.explainGb r)) :
    ProbComp.eval (G.explainGbFixedRealView rc f x r) =
      ProbComp.eval (G.explainGbFixedIdealView f x r) := by
  simp only [explainGbFixedRealView, explainGbFixedIdealView, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure]
  refine bind_uniform_comp h fun r' => ?_
  rw [rc.garble_explainGb]
  rfl

/-- If `explainRerand r₁` is a bijection, explainable rerandomization with fixed coins `r` and
`r₁` holds with zero error. -/
theorem eval_explainRerandFixedRealView (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool) (r : G.Coins) (r₁ : G.RerandCoins)
    (h : Function.Bijective (rc.explainRerand r₁)) :
    ProbComp.eval (G.explainRerandFixedRealView rc f x r r₁) =
      ProbComp.eval (G.explainRerandFixedIdealView f x r r₁) := by
  simp only [explainRerandFixedRealView, explainRerandFixedIdealView, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure]
  refine bind_uniform_comp h fun r₂ => ?_
  rw [rc.rerand_explainRerand]
  rfl

end RerandomizableGarbling

end Cslib.Crypto.Garbling
