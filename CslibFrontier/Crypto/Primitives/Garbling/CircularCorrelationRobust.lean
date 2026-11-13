/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.OneHot
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount

/-!
# Circular correlation robustness

A tweakable hash `H : L → T → M` is *circular correlation robust* when, for a secret offset drawn
from a key, the oracle that answers a query `(x, t, b)` with `H (x + Δ) t`, plus the output offset
`Δ'` when `b` is set, looks like a uniform random function. Choi, Katz, Kumaresan and Zhou
[ChoiKatzKumaresanZhou2012] introduced circular correlation robustness to prove the Free-XOR
technique of Kolesnikov and Schneider [KolesnikovSchneider2008] secure; Guo, Katz, Wang and Yu
[GuoKatzWangYu2020] gave the tweakable form, and Zahur, Rosulek and Evans [ZahurRosulekEvans2015]
and Heath, Kolesnikov and Ng [HeathKolesnikovNg2024], Definition 1, use it for half gates and
one-hot garbling.

`CCR.oracle H Δ Δ' q` is that oracle, with the input offset `Δ : L` and the output offset
`Δ' : M` given separately, and `CCR.advantage H δ δ' A` is the advantage of `A` in telling
`CCR.oracle H (δ k) (δ' k)` under a uniform key `k` from a uniform random function, in the finite
PRF game `Cslib.Crypto.PRF.advantage`. Three Boolean garbling schemes of this library rest on it
(the point-and-permute scheme of `Cslib.Crypto.Garbling.Privacy` rests on PRF security instead):

* Free-XOR (`Cslib.Crypto.Garbling.FreeXOR`): the hash reads only a key `x : K`, labels are
  `K × Bool`, and the offsets are `δ` and `(δ, true)`.
* half gates (`Cslib.Crypto.Garbling.HalfGates`): the hash reads the whole label, colour bit
  included, and both offsets are `(δ, true)`.
* one-hot garbling (`Cslib.Crypto.Garbling.BinaryToOneHot`): labels form a `ZMod 2`-module, both
  offsets are `δ k` for a key map `δ`, which can fix the colour bit of the offset.

The input and output offsets live in different groups only for Free-XOR, whose hash ignores the
colour bit. Reading that hash on whole labels instead would make the assumption false: the distinct
queries `((x, false), t, b)` and `((x, true), t, b)` would get equal answers, which a uniform random
function rarely gives.

Heath's arithmetic garbling [Heath2024] uses an arithmetic variant (`CCR.Arithmetic`): labels lie
in an `R`-module, the shift is a scalar, and the ideal oracle answers every query with a fresh
uniform label. It is a different assumption, and no implication between it and `CCR.advantage` is
formalized. The mixed-modulus assumption of Ball, Malkin and Rosulek [BallMalkinRosulek2016],
Definition 1, has its own dependent query type and lives in
`Cslib.Crypto.Garbling.MixedModulus`.

## Main definitions

* `Cslib.Crypto.Garbling.CCR.Query`: a query of a label, a tweak and a bit.
* `Cslib.Crypto.Garbling.CCR.oracle`: the circular oracle under an input and an output offset.
* `Cslib.Crypto.Garbling.CCR.advantage`: the circular correlation robustness advantage.
* `Cslib.Crypto.Garbling.CCR.Arithmetic.advantage`: the arithmetic variant, with
  `Cslib.Crypto.Garbling.CCR.Arithmetic.IsTweakUnique`.

## Implementation notes

The definition of [GuoKatzWangYu2020] only allows adversaries that never ask both `(x, t, false)`
and `(x, t, true)`, whose answers reveal the offset (`CCR.oracle_true_sub_oracle_false`). Here
`advantage` is defined for every adversary, and the restriction is a property of the adversary at
hand: the Free-XOR, half-gates and one-hot reductions ask every tweak at most once. The same holds
for the arithmetic variant, whose restriction `IsTweakUnique` is formalized.

## References

* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
* [C. Guo, J. Katz, X. Wang, Y. Yu, *Efficient and Secure Multiparty Computation from Fixed-Key
  Block Ciphers*][GuoKatzWangYu2020]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [D. Heath, V. Kolesnikov, L. K. L. Ng, *Garbled Circuit Lookup Tables with Logarithmic Number of
  Ciphertexts*][HeathKolesnikovNg2024]
* [D. Heath, *Efficient Arithmetic in Garbled Circuits*][Heath2024]
* [M. Ball, T. Malkin, M. Rosulek, *Garbling Gadgets for Boolean and Arithmetic
  Circuits*][BallMalkinRosulek2016]
-/

public section

namespace Cslib.Crypto.Garbling.CCR

/-- A query to the circular oracle: a label, a tweak and a bit. -/
structure Query (L T : Type) where
  /-- The label, shifted by the input offset before hashing. -/
  label : L
  /-- The tweak passed to the hash. -/
  tweak : T
  /-- Whether the answer also gets the output offset. -/
  bit : Bool
  deriving DecidableEq, Fintype

/-- Adversaries against circular correlation robustness: oracle algorithms with private coins
that ask queries of a label, a tweak and a bit, get answers in `M`, and output a guess. -/
abbrev Adversary (L T M : Type) : Type := PRF.Adversary (Query L T) M

variable {L T M Key : Type} [AddCommGroup L] [AddCommGroup M]

/-- The circular oracle under the input offset `Δ` and the output offset `Δ'`: the query
`(x, t, b)` gets `H (x + Δ) t`, plus `Δ'` when `b` is set. -/
@[expose] def oracle (H : L → T → M) (Δ : L) (Δ' : M) (q : Query L T) : M :=
  H (q.label + Δ) q.tweak + bitOffset Δ' q.bit

@[simp] theorem oracle_apply (H : L → T → M) (Δ : L) (Δ' : M) (x : L) (t : T) (b : Bool) :
    oracle H Δ Δ' ⟨x, t, b⟩ = H (x + Δ) t + bitOffset Δ' b :=
  rfl

/-- The answers to `(x, t, true)` and `(x, t, false)` differ by the output offset, so an
adversary that asks both learns it. -/
theorem oracle_true_sub_oracle_false (H : L → T → M) (Δ : L) (Δ' : M) (x : L) (t : T) :
    oracle H Δ Δ' ⟨x, t, true⟩ - oracle H Δ Δ' ⟨x, t, false⟩ = Δ' := by
  rw [oracle_apply, oracle_apply, bitOffset_true, bitOffset_false, add_zero, add_sub_cancel_left]

/-- The keyed circular oracle: the key `k` selects the input offset `δ k` and the output offset
`δ' k`. -/
@[expose] def keyed (H : L → T → M) (δ : Key → L) (δ' : Key → M) (k : Key) : Query L T → M :=
  oracle H (δ k) (δ' k)

/-- The circular correlation robustness advantage of `A` against `H` with offsets `δ` and `δ'`:
its advantage in telling the keyed circular oracle under a uniform key from a uniform random
function. -/
@[expose] noncomputable def advantage [Fintype Key] [Nonempty Key] [Fintype L] [DecidableEq L]
    [Fintype T] [DecidableEq T] [Fintype M] [Nonempty M] (H : L → T → M) (δ : Key → L)
    (δ' : Key → M) (A : Adversary L T M) : NNReal :=
  PRF.advantage (keyed H δ δ') A

/-! ### The arithmetic variant -/

namespace Arithmetic

variable {R : Type} [CommRing R] [Module R L]

/-- A query to the arithmetic circular oracle: a label, a tweak and a scalar shift. -/
structure Query (L R : Type) where
  /-- The label, shifted by minus the offset before hashing. -/
  label : L
  /-- The tweak passed to the hash. -/
  tweak : ℕ
  /-- The multiple of the offset added to the answer. -/
  shift : R

/-- The oracle keyed by the offset `Δ`: the query `(k, t, s)` gets `H (k - Δ) t + s • Δ`. -/
@[expose] def oracle (H : L → ℕ → L) (Δ : L) (q : Query L R) : L :=
  H (q.label - Δ) q.tweak + q.shift • Δ

@[simp] theorem oracle_apply (H : L → ℕ → L) (Δ k : L) (t : ℕ) (s : R) :
    oracle H Δ ⟨k, t, s⟩ = H (k - Δ) t + s • Δ :=
  rfl

/-- An arithmetic CCR adversary: a test with private coins and oracle access to queries
`(k, t, s)`. -/
abbrev Adversary (R L : Type) := PRF.Adversary (Query L R) L

/-- The keyed experiment: the law of the PRF real experiment keyed by a uniform offset of colour
`1`, answering with `oracle`. -/
@[expose] noncomputable def realGame (H : L → ℕ → L) (col : L →+ ZMod 2) [Fintype L]
    [Nonempty {Δ : L // col Δ = 1}] (adversary : Adversary R L) : Game :=
  ProbComp.eval (PRF.realExperiment (fun Δ : {Δ : L // col Δ = 1} => oracle H Δ.1) adversary)

/-- The ideal experiment: answer every query with a fresh uniform label. -/
@[expose] noncomputable def idealGame [Fintype L] (adversary : Adversary R L) : Game :=
  ProbComp.eval
    (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun _ => ProbComp.uniform L)
      adversary)

/-- The arithmetic CCR advantage of `adversary` against `H`. The assumption that it is small is
meant only for adversaries that never repeat a tweak (`IsTweakUnique`): repeating a query
distinguishes the fresh oracle from the keyed one. -/
noncomputable abbrev advantage (H : L → ℕ → L) (col : L →+ ZMod 2) [Fintype L]
    [Nonempty {Δ : L // col Δ = 1}] (adversary : Adversary R L) : NNReal :=
  Game.advantage (realGame H col adversary) (idealGame adversary)

/-- The adversary never repeats a tweak: on every path it makes at most one query with each
tweak `t`. -/
@[expose] def IsTweakUnique (adversary : Adversary R L) : Prop :=
  ∀ t : ℕ, OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) fun q : Query L R => if q.tweak = t then 1 else 0) adversary 1

end Arithmetic

end Cslib.Crypto.Garbling.CCR
