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
key and the colour bit of the point-and-permute technique. The hash reads only the key.

## Main definitions

* `Cslib.Crypto.Garbling.CorrelationRobust.circular`: the circular oracle under an offset.
* `Cslib.Crypto.Garbling.CorrelationRobust.advantage`: the advantage of an adversary in telling
  the circular oracle under a uniform offset from a uniform random function.

## Implementation notes

The definition of [GuoKatzWangYu2020] only allows adversaries that never ask both `(x, t, false)`
and `(x, t, true)`, whose answers reveal the offset (`circular_sub_circular`). Here `advantage` is
defined for every adversary, and the restriction is a property of the adversary at hand: the
Free-XOR reduction in `Cslib.Crypto.Garbling.FreeXOR` asks every tweak at most once.

## References

* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
* [C. Guo, J. Katz, X. Wang, Y. Yu, *Efficient and Secure Multiparty Computation from Fixed-Key
  Block Ciphers*][GuoKatzWangYu2020]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
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

end Cslib.Crypto.Garbling.CorrelationRobust
