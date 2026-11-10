/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Basic

/-!
# Rerandomizable garbling schemes

A *rerandomizable garbling scheme* (RGS), adapting Acharya, Hazay, Kolesnikov and Prabhakaran
[AcharyaHazayKolesnikovPrabhakaran2024, Definition 3] (full version, ePrint 2024/383), is a
projective garbling scheme with an extra algorithm `rerand` that takes a garbled circuit `gc` and
returns a fresh-looking garbled circuit `gc'` together with one label permutation per input wire.
Applying the permutations to the input labels of `gc` gives the input labels of `gc'`, so an
evaluator holding an encoding for `gc` can move to `gc'` without the garbler. All randomness is
explicit: `garble f r` garbles `f` with coins `r`, and `rerand gc r'` rerandomizes with coins `r'`.
Decoding is folded into `evaluate`.
Unlike `Cslib.Crypto.Garbling.Scheme`
(`CslibFrontier/Crypto/Primitives/Garbling/Scheme.lean`), which is typed by `List Bool`,
indexed by a security parameter, and intentionally omits projective structure,
`RerandomizableGarbling` exposes per-wire label pairs so per-wire permutations can act directly
on encodings.

*Randomness composition* (`RandomnessComposition`) says that a rerandomized garbling is itself an
honest garbling, with coins `explainGb r r'` computed from the garbling coins and the
rerandomization coins, and that two rerandomizations compose into one with coins
`explainRerand r₁ r₂`. The garbling half adapts the randomness-composition property of
Definition 3, while `explainRerand` is an explicit two-step rerandomization-composition axiom of
this formalization. With `garble_explainGb`, correctness of fresh garblings implies correctness of
rerandomized ones (`rerandCorrect_of_correct`).

Two security notions are compared, each as a pair of probabilistic programs; the projective
encoding is `encode`, and `permEncoding` and `permInput` apply wire permutations.

* **Rerandomization privacy** (`rerandReal`, `rerandIdeal`; adapting Definition 3): given the
  garbling coins `r`, the rerandomized circuit and the rerandomized encoding of `x` look like a
  fresh garbling of `f` with an honest encoding of `x`.
* **Explainability** (adapting Definition 9, p. 33 of ePrint 2024/383). Explainable garbling
  (`explainGbReal`, `explainGbIdeal`): given an encoding of `x` for `gc` and a rerandomization of
  `gc` over uniformly sampled garbling and rerandomization coins, the coins `explainGb r r'` look
  like the coins of a fresh garbling. Explainable rerandomization (`explainRerandReal`,
  `explainRerandIdeal`): given a rerandomization `gc₁` of `gc` and a rerandomization `gc₂` of
  `gc₁` over uniformly sampled coins, the coins `explainRerand r₁ r₂` look like coins that
  rerandomize `gc` directly.

This development proves two generic single-instance reductions relating sampled-coin
explainability to rerandomization privacy under explicit algebraic invertibility hypotheses
(`RandomnessComposition.Invertible`). The advantage of any distinguisher against explainable
garbling *equals* the rerandomization-privacy advantage of `explainGbReduction`
(`explainGbAdvantage_eq`). The advantage against explainable rerandomization is at most the sum of
the rerandomization-privacy advantages of two reductions (`explainRerandAdvantage_le`), through one
intermediate hybrid. Both reductions use the inverse data of `RandomnessComposition.Invertible`
(introduced for this development): the garbling explanation is a bijection in the garbling coins
with an explicit inverse, the rerandomization explanation is a bijection in its first argument, and
some rerandomization coins undo each rerandomization step. The rerandomization bound also assumes
that the label action respects composition of permutations.

When the explanation maps are bijective in their *second* argument, rerandomization privacy and the
stronger fixed-coin explainability variants (`explainGbFixedReal`, `explainRerandFixedReal`, which
hold the base coins `r` and `r₁` fixed rather than sampling them) hold with zero error
(`eval_explainGbFixedReal`, `eval_explainRerandFixedReal`, `eval_rerandReal`).

## Scope

In `explainGbReal`/`explainGbIdeal` and `explainRerandReal`/`explainRerandIdeal`, the garbling and
rerandomization coins are sampled uniformly (matching the sampled-coin experiment structure of
Definition 9 in ePrint 2024/383, p. 33), whereas the fixed-coin variants `explainGbFixed*` and
`explainRerandFixed*` appear in the zero-error bijectivity lemmas. On the hypothesis side,
`rerandReal` samples `r` uniformly whereas Definition 3 quantifies over fixed `r`; because privacy
at every fixed `r` implies privacy for uniformly sampled `r`, the sampled-`r` assumption used by
the reductions is weaker. The generic reductions `explainGbAdvantage_eq` and
`explainRerandAdvantage_le`, together with the two-step composition field `explainRerand` and the
inverse structure `RandomnessComposition.Invertible`, are results and hypotheses of this
development rather than transcriptions of a numbered theorem in the paper. All statements are
single-instance: the function, input and distinguisher are fixed, and running time is not tracked,
so no asymptotic security or efficiency of the reductions is claimed.

## Main definitions

* `Cslib.Crypto.Garbling.RerandomizableGarbling`: an RGS with explicit coins.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.encode`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.permEncoding`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.permInput`: projective encoding and permutations.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.Correct`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.RerandCorrect`: correctness.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.RandomnessComposition`: randomness composition.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.RandomnessComposition.Invertible`: the inverse
  data used by the reductions.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandReal`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.rerandIdeal`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbReal`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainGbIdeal`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandReal`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandIdeal`, and the fixed-coin
  variants `explainGbFixedReal`, `explainGbFixedIdeal`, `explainRerandFixedReal`,
  `explainRerandFixedIdeal`: the experiments.
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
* `Cslib.Crypto.Garbling.RerandomizableGarbling.explainRerandAdvantage_le`.
* `Cslib.Crypto.Garbling.RerandomizableGarbling.eval_rerandReal`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.eval_explainGbFixedReal`,
  `Cslib.Crypto.Garbling.RerandomizableGarbling.eval_explainRerandFixedReal`: zero error under
  bijectivity in the second argument.

## References

* [A. Acharya, C. Hazay, V. Kolesnikov, M. Prabhakaran, *Malicious Security for SCALES:
  Outsourced Computation with Ephemeral Servers*][AcharyaHazayKolesnikovPrabhakaran2024];
  definition and theorem numbers refer to the full version, ePrint 2024/383.
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open Probability
open scoped NNReal

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
  garble : F → Coins → GC × (Fin m → Label × Label)
  /-- Rerandomization with given coins. -/
  rerand : GC → RerandCoins → GC × (Fin m → Perm)
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

/-- Correctness of fresh garblings: evaluating `garble f r` on the encoding of `x` gives `f x`. -/
def Correct : Prop :=
  ∀ (f : F) (x : Fin m → Bool) (r : G.Coins),
    G.evaluate (G.garble f r).1 (G.encode (G.garble f r).2 x) = G.evalFn f x

/-- Correctness of rerandomized garblings: evaluating the rerandomized circuit on the encoding
of `x` under the permuted encoding table gives `f x`. -/
def RerandCorrect : Prop :=
  ∀ (f : F) (x : Fin m → Bool) (r : G.Coins) (r' : G.RerandCoins),
    G.evaluate (G.rerand (G.garble f r).1 r').1
      (G.encode (G.permEncoding (G.rerand (G.garble f r).1 r').2 (G.garble f r).2) x) =
      G.evalFn f x

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
    G.garble f (explainGb r r') =
      ((G.rerand (G.garble f r).1 r').1,
        G.permEncoding (G.rerand (G.garble f r).1 r').2 (G.garble f r).2)
  rerand_explainRerand : ∀ (f : F) (r : G.Coins) (r₁ r₂ : G.RerandCoins),
    G.rerand (G.garble f r).1 (explainRerand r₁ r₂) =
      ((G.rerand (G.rerand (G.garble f r).1 r₁).1 r₂).1,
        fun i => G.comp ((G.rerand (G.garble f r).1 r₁).2 i)
          ((G.rerand (G.rerand (G.garble f r).1 r₁).1 r₂).2 i))

variable {G}

/-- Under randomness composition, correctness of fresh garblings gives correctness of
rerandomized ones. -/
theorem rerandCorrect_of_correct (rc : G.RandomnessComposition) (h : G.Correct) :
    G.RerandCorrect := by
  intro f x r r'
  have hg := rc.garble_explainGb f r r'
  rw [← h f x (rc.explainGb r r'), hg]

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
    (G.rerand (G.rerand gc r').1 (invRerand r')).1 = gc
  act_invRerand : ∀ (gc : G.GC) (r' : G.RerandCoins) (i : Fin m) (L : G.Label),
    G.act ((G.rerand (G.rerand gc r').1 (invRerand r')).2 i) (G.act ((G.rerand gc r').2 i) L) = L

variable (G)

/-! ### Experiments -/

/-- Rerandomization privacy, real: garble with uniform coins `r`, rerandomize with uniform coins,
and output `r`, the rerandomized circuit and the permuted encoding of `x`. -/
noncomputable def rerandReal (f : F) (x : Fin m → Bool) :
    ProbComp (G.Coins × G.GC × (Fin m → G.Label)) := do
  let r ← ProbComp.uniform G.Coins
  let r' ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let q := G.rerand g.1 r'
  return (r, q.1, G.permInput q.2 (G.encode g.2 x))

/-- Rerandomization privacy, ideal: output uniform coins `r` together with an independent fresh
garbling and the encoding of `x`. -/
noncomputable def rerandIdeal (f : F) (x : Fin m → Bool) :
    ProbComp (G.Coins × G.GC × (Fin m → G.Label)) := do
  let r ← ProbComp.uniform G.Coins
  let s ← ProbComp.uniform G.Coins
  let g := G.garble f s
  return (r, g.1, G.encode g.2 x)

/-- Explainable garbling, real (sampled garbling coins): output the encoding of `x` and the
circuit of a garbling with uniform coins `r`, a rerandomization of that circuit with uniform
coins `r'`, and the explanation `explainGb r r'`. -/
noncomputable def explainGbReal (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool) :
    ProbComp ((Fin m → G.Label) × G.GC × G.GC × G.Coins) := do
  let r ← ProbComp.uniform G.Coins
  let r' ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  return (G.encode g.2 x, g.1, (G.rerand g.1 r').1, rc.explainGb r r')

/-- Explainable garbling, ideal (sampled garbling coins): the third and fourth components are a
fresh garbled circuit and its coins. -/
noncomputable def explainGbIdeal (f : F) (x : Fin m → Bool) :
    ProbComp ((Fin m → G.Label) × G.GC × G.GC × G.Coins) := do
  let r ← ProbComp.uniform G.Coins
  let s ← ProbComp.uniform G.Coins
  let g := G.garble f r
  return (G.encode g.2 x, g.1, (G.garble f s).1, s)

/-- Explainable rerandomization, real (sampled coins): garble with coins `r`, rerandomize with
`r₁` and then `r₂`, and output the base circuit, the encoding of `x` for the first
rerandomization, both rerandomized circuits and the explanation `explainRerand r₁ r₂`. -/
noncomputable def explainRerandReal (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool) :
    ProbComp (G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins) := do
  let r ← ProbComp.uniform G.Coins
  let r₁ ← ProbComp.uniform G.RerandCoins
  let r₂ ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let q := G.rerand g.1 r₁
  return (g.1, G.permInput q.2 (G.encode g.2 x), q.1, (G.rerand q.1 r₂).1, rc.explainRerand r₁ r₂)

/-- Explainable rerandomization, ideal (sampled coins): the fourth and fifth components are a
direct rerandomization of the base circuit and its coins. -/
noncomputable def explainRerandIdeal (f : F) (x : Fin m → Bool) :
    ProbComp (G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins) := do
  let r ← ProbComp.uniform G.Coins
  let r₁ ← ProbComp.uniform G.RerandCoins
  let s ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let q := G.rerand g.1 r₁
  return (g.1, G.permInput q.2 (G.encode g.2 x), q.1, (G.rerand g.1 s).1, s)

/-- Explainable garbling with fixed garbling coins `r`, real. -/
noncomputable def explainGbFixedReal (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool)
    (r : G.Coins) : ProbComp ((Fin m → G.Label) × G.GC × G.GC × G.Coins) := do
  let r' ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  return (G.encode g.2 x, g.1, (G.rerand g.1 r').1, rc.explainGb r r')

/-- Explainable garbling with fixed garbling coins `r`, ideal. -/
noncomputable def explainGbFixedIdeal (f : F) (x : Fin m → Bool) (r : G.Coins) :
    ProbComp ((Fin m → G.Label) × G.GC × G.GC × G.Coins) := do
  let s ← ProbComp.uniform G.Coins
  let g := G.garble f r
  return (G.encode g.2 x, g.1, (G.garble f s).1, s)

/-- Explainable rerandomization with fixed coins `r` and `r₁`, real. -/
noncomputable def explainRerandFixedReal (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool) (r : G.Coins) (r₁ : G.RerandCoins) :
    ProbComp (G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins) := do
  let r₂ ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let q := G.rerand g.1 r₁
  return (g.1, G.permInput q.2 (G.encode g.2 x), q.1, (G.rerand q.1 r₂).1, rc.explainRerand r₁ r₂)

/-- Explainable rerandomization with fixed coins `r` and `r₁`, ideal. -/
noncomputable def explainRerandFixedIdeal (f : F) (x : Fin m → Bool) (r : G.Coins)
    (r₁ : G.RerandCoins) :
    ProbComp (G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins) := do
  let s ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let q := G.rerand g.1 r₁
  return (g.1, G.permInput q.2 (G.encode g.2 x), q.1, (G.rerand g.1 s).1, s)

/-! ### Advantages and reductions -/

/-- The advantage of `D` in telling `rerandReal` from `rerandIdeal`. -/
noncomputable def rerandAdvantage (f : F) (x : Fin m → Bool)
    (D : G.Coins × G.GC × (Fin m → G.Label) → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (do let v ← G.rerandReal f x; D v))
    (ProbComp.eval (do let v ← G.rerandIdeal f x; D v))

/-- The advantage of `D` in telling `explainGbReal` from `explainGbIdeal`. -/
noncomputable def explainGbAdvantage (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool)
    (D : (Fin m → G.Label) × G.GC × G.GC × G.Coins → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (do let v ← G.explainGbReal rc f x; D v))
    (ProbComp.eval (do let v ← G.explainGbIdeal f x; D v))

/-- The advantage of `D` in telling `explainRerandReal` from `explainRerandIdeal`. -/
noncomputable def explainRerandAdvantage (rc : G.RandomnessComposition) (f : F)
    (x : Fin m → Bool)
    (D : G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (do let v ← G.explainRerandReal rc f x; D v))
    (ProbComp.eval (do let v ← G.explainRerandIdeal f x; D v))

/-- The rerandomization-privacy distinguisher built from an explainable-garbling distinguisher:
on `(r, gc, X)` it runs `D` on `X`, `gc`, the circuit of `garble f r` and the coins `r`. -/
def explainGbReduction (f : F)
    (D : (Fin m → G.Label) × G.GC × G.GC × G.Coins → ProbComp Bool) :
    G.Coins × G.GC × (Fin m → G.Label) → ProbComp Bool :=
  fun (r, gc, X) => D (X, gc, (G.garble f r).1, r)

/-- The first rerandomization-privacy distinguisher built from an explainable-rerandomization
distinguisher: on `(r, gc, X)` it samples `s`, takes the base circuit garbled with coins
`unexplainGb r s`, and runs `D` on it, `X`, `gc`, its rerandomization with coins `s`, and `s`. -/
noncomputable def explainRerandReductionLeft {rc : G.RandomnessComposition}
    (hinv : rc.Invertible) (f : F)
    (D : G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins → ProbComp Bool) :
    G.Coins × G.GC × (Fin m → G.Label) → ProbComp Bool := fun (r, gc, X) => do
  let s ← ProbComp.uniform G.RerandCoins
  let base := (G.garble f (hinv.unexplainGb r s)).1
  D (base, X, gc, (G.rerand base s).1, s)

/-- The second rerandomization-privacy distinguisher built from an explainable-rerandomization
distinguisher: on `(r, gc, X)` it samples `s`, takes the base circuit garbled with coins `r`,
and runs `D` on it, `X`, `gc`, its rerandomization with coins `s`, and `s`. -/
noncomputable def explainRerandReductionRight (f : F)
    (D : G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins → ProbComp Bool) :
    G.Coins × G.GC × (Fin m → G.Label) → ProbComp Bool := fun (r, gc, X) => do
  let s ← ProbComp.uniform G.RerandCoins
  let base := (G.garble f r).1
  D (base, X, gc, (G.rerand base s).1, s)

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
    G.permInput (G.rerand (G.rerand gc r').1 (hinv.invRerand r')).2
      (G.permInput (G.rerand gc r').2 X) = X :=
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
  rw [PMF.bind_comm (PMF.uniformOfFintype α)]
  calc ((PMF.uniformOfFintype δ).bind fun d => (PMF.uniformOfFintype α).bind fun a =>
          (PMF.uniformOfFintype β).bind fun c => M a d c)
      = (PMF.uniformOfFintype δ).bind fun d => (PMF.uniformOfFintype β).bind fun c =>
          (PMF.uniformOfFintype α).bind fun a => M a d c :=
        congrArg _ (funext fun d => PMF.bind_comm _ _ _)
    _ = _ := PMF.bind_comm _ _ _

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
    (x : Fin m → Bool) (D : (Fin m → G.Label) × G.GC × G.GC × G.Coins → ProbComp Bool) :
    G.explainGbAdvantage rc f x D = G.rerandAdvantage f x (G.explainGbReduction f D) := by
  have hreal : ProbComp.eval (do let v ← G.explainGbReal rc f x; D v) =
      ProbComp.eval (do let v ← G.rerandReal f x; G.explainGbReduction f D v) := by
    simp only [explainGbReal, rerandReal, explainGbReduction, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform]
    refine bind_bind_uniform_reindex (fun r' r => rc.explainGb r r') hinv.explainGb_bijective
      hinv.invRerand fun r r' => ?_
    rw [rc.garble_explainGb]
    dsimp only
    rw [hinv.rerand_invRerand, encode_permEncoding, hinv.permInput_invRerand]
  have hideal : ProbComp.eval (do let v ← G.explainGbIdeal f x; D v) =
      ProbComp.eval (do let v ← G.rerandIdeal f x; G.explainGbReduction f D v) := by
    simp only [explainGbIdeal, rerandIdeal, explainGbReduction, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform]
    exact PMF.bind_comm _ _ _
  rw [explainGbAdvantage, rerandAdvantage, hreal, hideal]

variable (G) in
/-- The intermediate hybrid of the explainable-rerandomization argument: the encoding and the
first rerandomized circuit come from an independent fresh garbling. -/
private noncomputable def explainRerandHybrid (f : F)
    (x : Fin m → Bool) : ProbComp (G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins) := do
  let r ← ProbComp.uniform G.Coins
  let t ← ProbComp.uniform G.Coins
  let s ← ProbComp.uniform G.RerandCoins
  let g := G.garble f r
  let h := G.garble f t
  return (g.1, G.encode h.2 x, h.1, (G.rerand g.1 s).1, s)

/-- **Explainable rerandomization from rerandomization privacy.** If the label action respects
composition of permutations, then for every distinguisher `D` the explainable-rerandomization
advantage of `D` is at most the sum of the rerandomization-privacy advantages of
`explainRerandReductionLeft hinv f D` and `explainRerandReductionRight f D`. -/
theorem explainRerandAdvantage_le (rc : G.RandomnessComposition) (hinv : rc.Invertible)
    (hcomp : ∀ (p q : G.Perm) (L : G.Label), G.act (G.comp p q) L = G.act q (G.act p L))
    (f : F) (x : Fin m → Bool)
    (D : G.GC × (Fin m → G.Label) × G.GC × G.GC × G.RerandCoins → ProbComp Bool) :
    G.explainRerandAdvantage rc f x D ≤
      G.rerandAdvantage f x (G.explainRerandReductionLeft hinv f D) +
        G.rerandAdvantage f x (G.explainRerandReductionRight f D) := by
  have hreal : ProbComp.eval (do let v ← G.explainRerandReal rc f x; D v) =
      ProbComp.eval (do let v ← G.rerandReal f x; G.explainRerandReductionLeft hinv f D v) := by
    simp only [explainRerandReal, rerandReal, explainRerandReductionLeft, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform]
    refine bind_bind_bind_uniform_reindex (fun s r => rc.explainGb r s) hinv.explainGb_bijective
      rc.explainRerand hinv.explainRerand_bijective hinv.invRerand fun r r₁ r₂ => ?_
    rw [hinv.unexplainGb_explainGb, rc.garble_explainGb, rc.rerand_explainRerand]
    dsimp only
    rw [hinv.rerand_invRerand, encode_permEncoding, permInput_comp hcomp,
      hinv.permInput_invRerand]
  have hhyb : ProbComp.eval (do let v ← explainRerandHybrid G f x; D v) =
      ProbComp.eval (do let v ← G.rerandIdeal f x; G.explainRerandReductionLeft hinv f D v) := by
    simp only [explainRerandHybrid, rerandIdeal, explainRerandReductionLeft, bind_assoc,
      pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform]
    refine bind_bind_bind_uniform_reindex_fst (fun s r => rc.explainGb r s)
      hinv.explainGb_bijective fun r t s => ?_
    rw [hinv.unexplainGb_explainGb]
  have hhyb' : ProbComp.eval (do let v ← explainRerandHybrid G f x; D v) =
      ProbComp.eval (do let v ← G.rerandIdeal f x; G.explainRerandReductionRight f D v) := by
    simp only [explainRerandHybrid, rerandIdeal, explainRerandReductionRight, bind_assoc,
      pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform]
  have hideal : ProbComp.eval (do let v ← G.explainRerandIdeal f x; D v) =
      ProbComp.eval (do let v ← G.rerandReal f x; G.explainRerandReductionRight f D v) := by
    simp only [explainRerandIdeal, rerandReal, explainRerandReductionRight, bind_assoc, pure_bind,
      ProbComp.eval_bind, ProbComp.eval_uniform]
  calc G.explainRerandAdvantage rc f x D
      ≤ Game.advantage (ProbComp.eval (do let v ← G.explainRerandReal rc f x; D v))
          (ProbComp.eval (do let v ← explainRerandHybrid G f x; D v)) +
        Game.advantage (ProbComp.eval (do let v ← explainRerandHybrid G f x; D v))
          (ProbComp.eval (do let v ← G.explainRerandIdeal f x; D v)) :=
        Game.advantage_triangle _ _ _
    _ = _ := by
        rw [rerandAdvantage, rerandAdvantage, Game.advantage_comm
          (ProbComp.eval (do let v ← G.rerandReal f x; G.explainRerandReductionRight f D v))]
        exact congrArg₂ (· + ·) (by rw [hreal, hhyb]) (by rw [hhyb', hideal])

/-! ### Zero error under bijectivity in the second argument -/

/-- If `explainGb r` is a bijection for every `r`, rerandomization privacy holds with zero
error. -/
theorem eval_rerandReal (rc : G.RandomnessComposition)
    (h : ∀ r, Function.Bijective (rc.explainGb r)) (f : F) (x : Fin m → Bool) :
    ProbComp.eval (G.rerandReal f x) = ProbComp.eval (G.rerandIdeal f x) := by
  simp only [rerandReal, rerandIdeal, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  refine congrArg _ (funext fun r => bind_uniform_comp (h r) fun r' => ?_)
  rw [rc.garble_explainGb, encode_permEncoding]

/-- If `explainGb r` is a bijection, explainable garbling with fixed coins `r` holds with zero
error. -/
theorem eval_explainGbFixedReal (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool)
    (r : G.Coins) (h : Function.Bijective (rc.explainGb r)) :
    ProbComp.eval (G.explainGbFixedReal rc f x r) =
      ProbComp.eval (G.explainGbFixedIdeal f x r) := by
  simp only [explainGbFixedReal, explainGbFixedIdeal, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  refine bind_uniform_comp h fun r' => ?_
  rw [rc.garble_explainGb]

/-- If `explainRerand r₁` is a bijection, explainable rerandomization with fixed coins `r` and
`r₁` holds with zero error. -/
theorem eval_explainRerandFixedReal (rc : G.RandomnessComposition) (f : F) (x : Fin m → Bool)
    (r : G.Coins) (r₁ : G.RerandCoins) (h : Function.Bijective (rc.explainRerand r₁)) :
    ProbComp.eval (G.explainRerandFixedReal rc f x r r₁) =
      ProbComp.eval (G.explainRerandFixedIdeal f x r r₁) := by
  simp only [explainRerandFixedReal, explainRerandFixedIdeal, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure]
  refine bind_uniform_comp h fun r₂ => ?_
  rw [rc.rerand_explainRerand]

end RerandomizableGarbling

end Cslib.Crypto.Garbling
