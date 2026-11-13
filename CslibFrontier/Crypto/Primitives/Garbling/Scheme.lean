/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.BitString

/-!
# Garbling schemes: syntax, correctness and side information

A garbling scheme in the sense of Bellare, Hoang and Rogaway [BellareHoangRogaway2012],
Section 3, is a tuple `(Gb, En, De, Ev, ev)`. The probabilistic garbling algorithm `Gb` maps a
security parameter and a function `f` to a garbled function `F`, encoding information `e` and
decoding information `d`; the deterministic algorithms `En`, `Ev` and `De` encode an input,
evaluate a garbled function and decode a garbled output; and `ev` gives the semantics of `f`.
Functions are an abstract type `Fn` carrying length readers, so the development is parametric in
the function representation (for a concrete point-and-permute circuit garbling construction over
`Cslib.Circuits.Circuit`, see `CslibFrontier.Crypto.Primitives.Garbling.Basic` and
`CslibFrontier.Crypto.Primitives.Garbling.Privacy`).

The randomness of `Gb` is explicit: a scheme fixes a coin-length function and a deterministic
garbling map on coin strings, and `Scheme.garble` samples the coins uniformly. This makes the
output distribution of garbling a `PMF` via `ProbComp.eval`, and the support of that
distribution is characterised by `Scheme.mem_support_eval_garble_iff`.

Side-information functions `Φ : Fn → Λ` ([BellareHoangRogaway2012], Section 3.3) describe what
a garbled function is allowed to reveal about `f`. The side information is `Φ`-compatible with a
scheme when it determines the length readers, and the two inversion properties of Section 4.1
(`SideInfo.IsEvInverter` and `SideInfo.IsInverter`) are the hypotheses under which the
indistinguishability and simulation notions of
`CslibFrontier.Crypto.Primitives.Garbling.Foundations` coincide.

Efficiency requirements (polynomial-time algorithms, efficiently computable inverters) and the
projective encoding structure of [BellareHoangRogaway2012], Section 3.2, are not part of this
module.

## Main definitions

* `Cslib.Crypto.Garbling.Scheme.Garbled`: the garbled triple `(F, e, d)` output by `Gb`.
* `Cslib.Crypto.Garbling.Query`: a query `(f, x)` of a function description and an input.
* `Cslib.Crypto.Garbling.Scheme`: the syntax `(Gb, En, De, Ev, ev)` with explicit coins.
* `Cslib.Crypto.Garbling.Scheme.garble`: the probabilistic garbling algorithm `Gb(1^k, f)`.
* `Cslib.Crypto.Garbling.Scheme.IsValid`: the length condition, non-degeneracy and correctness.
* `Cslib.Crypto.Garbling.Scheme.WellTyped`: the output-length typing of `ev` and `De`.
* `Cslib.Crypto.Garbling.SideInfo`: side-information functions with length readers.
* `Cslib.Crypto.Garbling.SideInfo.IsEvInverter`, `Cslib.Crypto.Garbling.SideInfo.IsInverter`:
  the inversion properties of [BellareHoangRogaway2012], Section 4.1.

## Main results

* `Cslib.Crypto.Garbling.Scheme.mem_support_eval_garble_iff`: the garbled triples a scheme can
  output are exactly the images of coin strings of the right length.
* `Cslib.Crypto.Garbling.SideInfo.circ_isInverter`: the identity side information is invertible.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

namespace Scheme

/-- A garbled function together with its encoding and decoding information, the output
`(F, e, d)` of the garbling algorithm. -/
structure Garbled where
  /-- The garbled function `F`. -/
  fn : List Bool
  /-- The encoding information `e`. -/
  encInfo : List Bool
  /-- The decoding information `d`. -/
  decInfo : List Bool
  deriving DecidableEq

end Scheme

/-- A query `(f, x)` to a garbling scheme: a function description and an input. -/
structure Query (Fn : Type) where
  /-- The function description `f`. -/
  fn : Fn
  /-- The input `x`. -/
  input : List Bool
  deriving DecidableEq

/-- A garbling scheme over a type `Fn` of function descriptions, following
[BellareHoangRogaway2012], Section 3.1. The probabilistic algorithm `Gb` is split into a
coin-length function and a deterministic map `gb` on coin strings; see `Scheme.garble` for the
sampled version. -/
structure Scheme (Fn : Type) where
  /-- The input length `f.n` of a function description. -/
  inLen : Fn → ℕ
  /-- The output length `f.m` of a function description. -/
  outLen : Fn → ℕ
  /-- The size `|f|` of a function description. -/
  size : Fn → ℕ
  /-- The semantics `ev(f, x)` of a function description. -/
  ev : Fn → List Bool → List Bool
  /-- The number of coins used by `Gb`, as a function of the security parameter and the input
  length, output length and size of `f`. -/
  coinLen : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- The deterministic core of `Gb(1^k, f; r)`. -/
  gb : ℕ → Fn → List Bool → Scheme.Garbled
  /-- The encoding algorithm `En(e, x)`. -/
  encode : List Bool → List Bool → List Bool
  /-- The evaluation algorithm `Ev(F, X)`. -/
  evalGarbled : List Bool → List Bool → List Bool
  /-- The decoding algorithm `De(d, Y)`, with `none` for the failure symbol `⊥`. -/
  decode : List Bool → List Bool → Option (List Bool)

namespace Scheme

variable {Fn : Type} (G : Scheme Fn)

/-- The number of coins `Gb(1^k, f)` consumes. -/
def coins (k : ℕ) (f : Fn) : ℕ :=
  G.coinLen k (G.inLen f) (G.outLen f) (G.size f)

/-- The probabilistic garbling algorithm `Gb(1^k, f)`: sample the coins uniformly and apply the
deterministic core. -/
noncomputable def garble (k : ℕ) (f : Fn) : ProbComp Garbled := do
  let coins ← BitString.sampleList (G.coins k f)
  return G.gb k f coins

@[simp] theorem eval_garble (k : ℕ) (f : Fn) :
    ProbComp.eval (G.garble k f) = (BitString.uniformList (G.coins k f)).map (G.gb k f) := by
  simp only [garble, ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
  rfl

/-- The garbled triples a scheme can output are exactly the images of coin strings of the
right length. -/
theorem mem_support_eval_garble_iff {k : ℕ} {f : Fn} {g : Garbled} :
    g ∈ (ProbComp.eval (G.garble k f)).support ↔
      ∃ coins : List Bool, coins.length = G.coins k f ∧ G.gb k f coins = g := by
  simp only [eval_garble, PMF.mem_support_map_iff, BitString.mem_support_uniformList_iff]

/-- Two function descriptions have the same shape when their length readers agree. -/
def SameShape (f f' : Fn) : Prop :=
  G.inLen f = G.inLen f' ∧ G.outLen f = G.outLen f' ∧ G.size f = G.size f'

/-- The length condition of [BellareHoangRogaway2012], Section 3.1: the lengths of `F`, `e` and
`d` depend only on `k` and the shape of `f`. -/
def LengthCondition : Prop :=
  ∀ k, 0 < k → ∀ f f' : Fn, G.SameShape f f' →
    ∀ g ∈ (ProbComp.eval (G.garble k f)).support, ∀ g' ∈ (ProbComp.eval (G.garble k f')).support,
      g.fn.length = g'.fn.length ∧ g.encInfo.length = g'.encInfo.length ∧
        g.decInfo.length = g'.decInfo.length

/-- Non-degeneracy of [BellareHoangRogaway2012], Section 3.1: on the same coins, functions of the
same shape receive the same encoding and decoding information. -/
def NonDegenerate : Prop :=
  ∀ k, 0 < k → ∀ f f' : Fn, G.SameShape f f' → ∀ coins : List Bool, coins.length = G.coins k f →
    (G.gb k f coins).encInfo = (G.gb k f' coins).encInfo ∧
      (G.gb k f coins).decInfo = (G.gb k f' coins).decInfo

/-- Correctness of [BellareHoangRogaway2012], Section 3.1: decoding the evaluation of an encoded
input recovers `ev(f, x)`. -/
def Correct : Prop :=
  ∀ k, 0 < k → ∀ (f : Fn) (x : List Bool), x.length = G.inLen f →
    ∀ g ∈ (ProbComp.eval (G.garble k f)).support,
      G.decode g.decInfo (G.evalGarbled g.fn (G.encode g.encInfo x)) = some (G.ev f x)

/-- A garbling scheme is valid when it satisfies the length condition, non-degeneracy and
correctness. -/
structure IsValid : Prop where
  /-- The length condition. -/
  length : G.LengthCondition
  /-- Non-degeneracy. -/
  nonDegenerate : G.NonDegenerate
  /-- Correctness. -/
  correct : G.Correct

/-- A scheme is well typed when `ev` returns `f.m` bits on inputs of `f.n` bits and, for every
honestly garbled `(F, e, d)`, any successful decoding `De(d, Y) = y` of an arbitrary string `Y`
returns `f.m` bits. -/
def WellTyped : Prop :=
  (∀ (f : Fn) (x : List Bool), x.length = G.inLen f → (G.ev f x).length = G.outLen f) ∧
    ∀ k, 0 < k → ∀ (f : Fn), ∀ g ∈ (ProbComp.eval (G.garble k f)).support,
      ∀ (Y : List Bool), ∀ y ∈ G.decode g.decInfo Y, y.length = G.outLen f

end Scheme

/-- A side-information function `Φ : Fn → Λ` together with length readers on `Λ`, following
[BellareHoangRogaway2012], Section 3.3. -/
structure SideInfo (Fn Λ : Type) where
  /-- The side information `Φ(f)`. -/
  phi : Fn → Λ
  /-- The input length read from side information. -/
  inLen : Λ → ℕ
  /-- The output length read from side information. -/
  outLen : Λ → ℕ
  /-- The size read from side information. -/
  size : Λ → ℕ

namespace SideInfo

variable {Fn Λ : Type} (Φ : SideInfo Fn Λ)

/-- Side information is compatible with a scheme when it determines the length readers of the
scheme. -/
def Compatible (G : Scheme Fn) : Prop :=
  ∀ f, Φ.inLen (Φ.phi f) = G.inLen f ∧ Φ.outLen (Φ.phi f) = G.outLen f ∧
    Φ.size (Φ.phi f) = G.size f

variable {Φ} in
/-- Functions with the same compatible side information have the same input length. -/
theorem Compatible.inLen_eq {G : Scheme Fn} (h : Φ.Compatible G) {f f' : Fn}
    (hphi : Φ.phi f = Φ.phi f') : G.inLen f = G.inLen f' :=
  (h f).1.symm.trans ((congrArg Φ.inLen hphi).trans (h f').1)

/-- `M` is an `ev`-inverter for `Φ` ([BellareHoangRogaway2012], Section 4.1): from `Φ(f)` and
`y = ev(f, x)` it produces a query `(f', x')` with `Φ(f') = Φ(f)`, `x'` of the right length and
`ev(f', x') = y`. -/
def IsEvInverter (G : Scheme Fn) (M : Λ → List Bool → Query Fn) : Prop :=
  ∀ (f : Fn) (x : List Bool), x.length = G.inLen f →
    let q := M (Φ.phi f) (G.ev f x)
    Φ.phi q.fn = Φ.phi f ∧ q.input.length = G.inLen q.fn ∧ G.ev q.fn q.input = G.ev f x

/-- `M` inverts `Φ` ([BellareHoangRogaway2012], Section 4.1): from `Φ(f)` it produces some `f'`
with `Φ(f') = Φ(f)`. -/
def IsInverter (M : Λ → Fn) : Prop :=
  ∀ f : Fn, Φ.phi (M (Φ.phi f)) = Φ.phi f

/-- The side information `Φ_circ` revealing the function description itself. -/
def circ (G : Scheme Fn) : SideInfo Fn Fn where
  phi := id
  inLen := G.inLen
  outLen := G.outLen
  size := G.size

theorem circ_compatible (G : Scheme Fn) : (circ G).Compatible G :=
  fun _ => ⟨rfl, rfl, rfl⟩

theorem circ_isInverter (G : Scheme Fn) : (circ G).IsInverter id :=
  fun _ => rfl

end SideInfo

end Cslib.Crypto.Garbling
