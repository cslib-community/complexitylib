/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Circular correlation robustness

A hash `H : K → T → K × Bool` with tweaks in `T` is *circular correlation robust* when, for a
secret uniform offset `δ : K`, the oracle that answers a query `(x, t, b)` with `H (x + δ) t`,
plus `(δ, true)` when `b` is set, looks like a uniform random function. Choi, Katz, Kumaresan and
Zhou [ChoiKatzKumaresanZhou2012] introduced circular correlation robustness to prove the Free-XOR
technique of Kolesnikov and Schneider [KolesnikovSchneider2008] secure, and Guo, Katz, Wang and Yu
[GuoKatzWangYu2020] gave the tweakable form that this file follows. Labels live in `K × Bool`: a
key and the colour bit of the point-and-permute technique.

The assumption comes in two forms. In `circular`, used by Free-XOR, the hash reads only the key.
In `circularLabel`, used by the half-gates scheme of Zahur, Rosulek and Evans
[ZahurRosulekEvans2015], the hash `H : K × Bool → T → K × Bool` reads the whole label, colour bit
included, and the query `(a, t, b)` gets `H (a + (δ, true)) t`, plus `(δ, true)` when `b` is set.
A hash that ignores the colour gives back the key-only form (`circularLabel_fst`).

## Main definitions

* `Cslib.Crypto.Garbling.CorrelationRobust.circular`: the circular oracle under an offset.
* `Cslib.Crypto.Garbling.CorrelationRobust.advantage`: the advantage of an adversary in telling
  the circular oracle under a uniform offset from a uniform random function.
* `Cslib.Crypto.Garbling.CorrelationRobust.circularLabel`,
  `Cslib.Crypto.Garbling.CorrelationRobust.advantageLabel`: the same for a hash on whole labels.

## Implementation notes

The definition of [GuoKatzWangYu2020] only allows adversaries that never ask both `(x, t, false)`
and `(x, t, true)`, whose answers reveal the offset (`circular_sub_circular`). Here `advantage` is
defined for every adversary, and the restriction is a property of the adversary at hand: the
Free-XOR reduction in `Cslib.Crypto.Garbling.FreeXOR` asks every tweak at most once, and so does the
half-gates reduction `Cslib.Crypto.Garbling.HalfGates.reduction`. The same holds for
`advantageLabel` (`circularLabel_sub_circularLabel`).

## References

* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
* [C. Guo, J. Katz, X. Wang, Y. Yu, *Efficient and Secure Multiparty Computation from Fixed-Key
  Block Ciphers*][GuoKatzWangYu2020]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
-/

public section

namespace Cslib.Crypto.Garbling.CorrelationRobust

/-- Adversaries against circular correlation robustness: oracle algorithms that ask queries
`(x, t, b)` of a key, a tweak and a bit, get labels back, and output a guess. -/
abbrev Adversary (K T : Type) : Type := PRF.Adversary (K × T × Bool) (K × Bool)

variable {K T : Type} [AddCommGroup K]

/-- The circular oracle under the offset `δ`: the query `(x, t, b)` gets `H (x + δ) t`, plus the
offset `(δ, true)` when `b` is set. -/
def circular (H : K → T → K × Bool) (δ : K) (q : K × T × Bool) : K × Bool :=
  H (q.1 + δ) q.2.1 + if q.2.2 then (δ, true) else 0

theorem circular_apply (H : K → T → K × Bool) (δ x : K) (t : T) (b : Bool) :
    circular H δ (x, t, b) = H (x + δ) t + if b then (δ, true) else 0 := by
  simp only [circular]

/-- The answers to `(x, t, true)` and `(x, t, false)` differ by the offset, so an adversary that
asks both learns it. -/
theorem circular_sub_circular (H : K → T → K × Bool) (δ x : K) (t : T) :
    circular H δ (x, t, true) - circular H δ (x, t, false) = (δ, true) := by
  rw [circular_apply, circular_apply, ite_eq_left rfl, ite_eq_right Bool.false_ne_true, add_zero,
    add_sub_cancel_left]

/-- The circular correlation robustness advantage of `A` against `H`: its advantage in telling
the circular oracle under a uniform offset from a uniform random function. -/
@[expose] noncomputable def advantage [Fintype K] [Nonempty K] [DecidableEq K] [Fintype T]
    [DecidableEq T] (H : K → T → K × Bool) (A : Adversary K T) : NNReal :=
  PRF.advantage (circular H) A

/-! ### Hashes on whole labels -/

/-- Adversaries against circular correlation robustness of a hash on whole labels: oracle
algorithms that ask queries `(a, t, b)` of a label, a tweak and a bit, get labels back, and output
a guess. -/
abbrev LabelAdversary (K T : Type) : Type := PRF.Adversary ((K × Bool) × T × Bool) (K × Bool)

/-- The circular oracle under the offset `δ` for a hash on whole labels: the query `(a, t, b)` gets
`H (a + (δ, true)) t`, plus the offset `(δ, true)` when `b` is set. -/
def circularLabel (H : K × Bool → T → K × Bool) (δ : K) (q : (K × Bool) × T × Bool) : K × Bool :=
  H (q.1 + (δ, true)) q.2.1 + if q.2.2 then (δ, true) else 0

theorem circularLabel_apply (H : K × Bool → T → K × Bool) (δ : K) (a : K × Bool) (t : T)
    (b : Bool) :
    circularLabel H δ (a, t, b) = H (a + (δ, true)) t + if b then (δ, true) else 0 := by
  simp only [circularLabel]

/-- A hash that reads only the key is the special case of `circularLabel`: on a label of any
colour, its answer is the answer of `circular` on the key. -/
theorem circularLabel_fst (H : K → T → K × Bool) (δ x : K) (c : Bool) (t : T) (b : Bool) :
    circularLabel (fun a => H a.1) δ ((x, c), t, b) = circular H δ (x, t, b) := by
  simp only [circularLabel, circular, Prod.fst_add]

/-- The answers to `(a, t, true)` and `(a, t, false)` differ by the offset, so an adversary that
asks both learns it. -/
theorem circularLabel_sub_circularLabel (H : K × Bool → T → K × Bool) (δ : K) (a : K × Bool)
    (t : T) : circularLabel H δ (a, t, true) - circularLabel H δ (a, t, false) = (δ, true) := by
  rw [circularLabel_apply, circularLabel_apply, ite_eq_left rfl, ite_eq_right Bool.false_ne_true,
    add_zero, add_sub_cancel_left]

/-- The circular correlation robustness advantage of `A` against a hash `H` on whole labels: its
advantage in telling `circularLabel H` under a uniform offset from a uniform random function. -/
@[expose] noncomputable def advantageLabel [Fintype K] [Nonempty K] [DecidableEq K] [Fintype T]
    [DecidableEq T] (H : K × Bool → T → K × Bool) (A : LabelAdversary K T) : NNReal :=
  PRF.advantage (circularLabel H) A

end Cslib.Crypto.Garbling.CorrelationRobust
