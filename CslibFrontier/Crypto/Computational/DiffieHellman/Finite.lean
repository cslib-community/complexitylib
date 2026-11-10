/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Single-instance Decision Diffie–Hellman games

Fix an additive group `G`, an element `g : G` and a modulus `q`. The real Decision Diffie–Hellman
(DDH) game draws independent uniform exponents `a, b : ZMod q` and gives a distinguisher `D` the
triple `(a.val • g, b.val • g, (a * b).val • g)`. The random game draws a third independent
uniform exponent `c : ZMod q` and gives `D` the triple `(a.val • g, b.val • g, c.val • g)`. This
is [BonehShoup2023], Attack Game 10.6, written additively. The advantage of `D` is the
distinguishing advantage of the two games.

These are the concrete games for one fixed group, used as the target of concrete reductions such
as the receiver-privacy reduction in `CslibFrontier/Crypto/Protocols/MPC/DDHOT.lean`. The
definitions place no hypothesis on `G`, `g` or `q`; results that use them state what they need,
for example that `g` generates `G` and `Fintype.card G = q`. The asymptotic assumption over a
family of prime-order groups is `Cslib.Crypto.PrimeOrderGroupFamily.DDH` in
`CslibFrontier/Crypto/Computational/DiffieHellman.lean`.

## Main definitions

* `Cslib.Crypto.DDH.realGame`, `Cslib.Crypto.DDH.randomGame`: the real and random DDH games.
* `Cslib.Crypto.DDH.advantage`: their distinguishing advantage.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Attack Game 10.6.
-/

public section

namespace Cslib.Crypto.DDH

open scoped NNReal

variable {G : Type} [AddCommGroup G]

/-- Real DDH game over `(G, g, q)`: samples `a, b ← ZMod q` and feeds
`(a.val • g, b.val • g, (a * b).val • g)` to `D`. -/
@[expose] noncomputable def realGame (g : G) (q : ℕ) [NeZero q]
    (D : G × G × G → ProbComp Bool) : Game :=
  ProbComp.eval do
    let a ← ProbComp.uniform (ZMod q)
    let b ← ProbComp.uniform (ZMod q)
    D (a.val • g, b.val • g, (a * b).val • g)

/-- Random DDH game over `(G, g, q)`: samples `a, b, c ← ZMod q` and feeds
`(a.val • g, b.val • g, c.val • g)` to `D`. -/
@[expose] noncomputable def randomGame (g : G) (q : ℕ) [NeZero q]
    (D : G × G × G → ProbComp Bool) : Game :=
  ProbComp.eval do
    let a ← ProbComp.uniform (ZMod q)
    let b ← ProbComp.uniform (ZMod q)
    let c ← ProbComp.uniform (ZMod q)
    D (a.val • g, b.val • g, c.val • g)

/-- Concrete DDH distinguishing advantage of `D` over `(G, g, q)`. -/
@[expose] noncomputable def advantage (g : G) (q : ℕ) [NeZero q]
    (D : G × G × G → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (realGame g q D) (randomGame g q D)

end Cslib.Crypto.DDH
