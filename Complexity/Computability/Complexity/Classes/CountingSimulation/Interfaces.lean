/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.Certificate
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Foundations.Data.Nat.CeilDiv
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Interfaces of the deterministic counting simulation

The deterministic simulation of nondeterministic and probabilistic time by blocking and tensor
contraction (#1833) has two ingredients that are formalized separately. This module states them as
interfaces, so that the assembly (`Cslib.Complexity.CountingSimulation.exists_computableInO_count`)
can be proved from them, and each can be discharged on its own.

**Parameters.** A run of `t` steps is cut into `numBlocks t = ⌈t / b⌉` intervals of
`blockLength t = b = ⌈log₂ (t + 2)⌉` steps and padded to `paddedTime t = numBlocks t * b ≥ t`
steps. Each of `heads` blocked heads moves by at most one block per interval, so a run has one of
at most `3 ^ (heads * numBlocks t)` movement schedules.

**Networks** (`Cslib.Complexity.CountingSimulation.NetworkFamily`). A network for each input `x`,
clock `t` and schedule `σ`, built in polynomial time from `x`, `t` in unary and `σ` in binary,
whose values sum to the count being simulated at the padded time. Each network is admissible for
the contraction algorithm at size `t`, with a constant of the family. This is the block-counting
step of #1833 (milestone H3): blocking after Hopcroft, Paul and Valiant, with a Boolean tensor
network for each schedule whose contraction counts the accepting choice strings with that
schedule. It is new mathematics, not a cited result.

**Contraction** (`Cslib.Complexity.CountingSimulation.ContractionAlgorithm`). One native machine
that, given a precision `P` and a network `G`, outputs `value G % 2 ^ P`, and that, on networks
admissible at a size `s ≥ 2` with `1 ≤ P ≤ D * s`, runs within time
`K * (n + 1) ^ K * 2 ^ (K * s / √⌊log₂ s⌋)` and space `K * (n + 1) ^ K`, where `n` is the encoded
length of `(P, G)` and `K` depends only on the constants. This is the form in which the
simulation uses the Boolean tensor contraction theorem [OpenAI2026ETH, Theorem D.1] with `ℓ = 1`
and maximum degree `O(log s)` (milestone T2 of #1833), with the exponent in the natural-number
scale of `Nat.exists_three_pow_mul_le_two_pow_div_sqrt_log_two`. Like Theorem D.1 it is
parameterized by a size `s` bounding the number of edges and the precision, rather than by the
number of edges itself.

Both interfaces are generic in the representation of networks: their type `N`, its encoding, the
contracted `value : N → ℕ` and the admissibility predicate `Admissible C s G` are parameters. The
intended instance takes `N` to be an explicit Boolean tensor network with its number of row
vertices, `value` its contraction, and `Admissible C s G` to say that `G` is bipartite with at
most `C * s` edges and maximum degree at most `C * log₂ s`. This is
`Cslib.Complexity.CountingSimulation.ExplicitAdmissible`, which also bounds the vertices and asks
for full tables and at least `s` edges; the block-counting networks discharge the network
interface with it (`Cslib.Complexity.CountingSimulation.networkFamilies_explicitAdmissible`).

## Main definitions

* `Cslib.Complexity.CountingSimulation.blockLength`, `numBlocks`, `paddedTime`, `scheduleCount`:
  the blocking parameters.
* `Cslib.Complexity.CountingSimulation.ContractionAlgorithm`: the contraction interface.
* `Cslib.Complexity.CountingSimulation.NetworkFamily`: the network interface.

## Main results

* `Cslib.Complexity.CountingSimulation.le_paddedTime`: padding never shortens a run.
* `Cslib.Complexity.CountingSimulation.paddedTime_add_one_le`: from `t = 2` on, the padded time
  and one more fit in `2 * t`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (contraction).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Turing.MultiTapeTM Cslib.GenericRAM

/-! ### Blocking parameters -/

/-- The length `⌈log₂ (t + 2)⌉` of a time interval for a clock `t`. -/
@[expose] def blockLength (t : ℕ) : ℕ := Nat.clog 2 (t + 2)

/-- The number `⌈t / blockLength t⌉` of time intervals for a clock `t`. -/
@[expose] def numBlocks (t : ℕ) : ℕ := t ⌈/⌉ blockLength t

/-- The padded running time `numBlocks t * blockLength t`, a whole number of intervals. -/
@[expose] def paddedTime (t : ℕ) : ℕ := numBlocks t * blockLength t

/-- The number `3 ^ (heads * numBlocks t)` of movement schedules of `heads` blocked heads. -/
@[expose] def scheduleCount (heads t : ℕ) : ℕ := 3 ^ (heads * numBlocks t)

/-- An interval has at least one step. -/
theorem one_le_blockLength (t : ℕ) : 1 ≤ blockLength t :=
  Nat.succ_le_of_lt (Nat.clog_pos one_lt_two (by omega))

/-- **Padding never shortens a run**: `t ≤ paddedTime t`. -/
theorem le_paddedTime (t : ℕ) : t ≤ paddedTime t :=
  Nat.le_ceilDiv_mul (one_le_blockLength t)

private theorem add_two_le_two_pow {t : ℕ} (ht : 2 ≤ t) : t + 2 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- An interval is no longer than the clock, from `t = 2` on. -/
theorem blockLength_le {t : ℕ} (ht : 2 ≤ t) : blockLength t ≤ t :=
  Nat.clog_le_of_le_pow (add_two_le_two_pow ht)

/-- **The padded time stays linear**: from `t = 2` on, `paddedTime t + 1 ≤ 2 * t`, since padding
adds less than one interval. -/
theorem paddedTime_add_one_le {t : ℕ} (ht : 2 ≤ t) : paddedTime t + 1 ≤ 2 * t := by
  have h := Nat.ceilDiv_mul_lt (a := t) (one_le_blockLength t)
  have := blockLength_le ht
  unfold paddedTime numBlocks
  omega

/-! ### The interfaces -/

/-- **The contraction interface** (the Boolean tensor contraction theorem, as the simulation uses
it). One native certificate computes `value G % 2 ^ P` from the precision `P` in binary and the
network `G`. For all constants `C` and `D` there is `K` such that on every network admissible at a
size `s ≥ 2` with constant `C`, and every precision `1 ≤ P ≤ D * s`, the certificate's time is at
most `K * (n + 1) ^ K * 2 ^ (K * s / √⌊log₂ s⌋)` and its space at most `K * (n + 1) ^ K`, where `n`
is the encoded length of `(P, G)`. Outside admissible inputs the certificate need only be
correct. -/
structure ContractionAlgorithm {N : Type} (encN : N ↪ List Bool) (value : N → ℕ)
    (Admissible : ℕ → ℕ → N → Prop) where
  /-- The native contraction modulo `2 ^ P`. -/
  certificate : NativeCertificate (fun p : ℕ × N => value p.2 % 2 ^ p.1) (encPair encNat encN)
    encNat
  /-- Its time and space on admissible inputs. -/
  bound : ∀ C D : ℕ, ∃ K : ℕ, ∀ (s P : ℕ) (G : N), 2 ≤ s → 1 ≤ P → P ≤ D * s →
    Admissible C s G →
      certificate.time (P, G) ≤ K * ((encPair encNat encN (P, G)).length + 1) ^ K *
          2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        certificate.space (P, G) ≤ K * ((encPair encNat encN (P, G)).length + 1) ^ K

/-- **The network interface** (the block-counting lemma, as the simulation uses it), for a count
`count x τ` of the inputs `x` at padded time `τ`, such as the number of accepting choice strings of
length `τ` of a fair-coin machine. The family has a number of blocked heads and an admissibility
constant. Its network for the input `x`, the clock `t` and the schedule `σ` is computable in
polynomial time from `x`, `t` in unary and `σ` in binary. Whenever `|x| ≤ t` and `2 ≤ t`, the
values of the networks of the `scheduleCount heads t` schedules sum to `count x (paddedTime t)`,
and each of these networks is admissible at size `t`. -/
structure NetworkFamily {N : Type} (encN : N ↪ List Bool) (value : N → ℕ)
    (Admissible : ℕ → ℕ → N → Prop) (count : List Bool → ℕ → ℕ) where
  /-- The number of blocked heads. -/
  heads : ℕ
  /-- The admissibility constant. -/
  constant : ℕ
  /-- The network of an input, a clock and a schedule. -/
  net : List Bool × ℕ × ℕ → N
  /-- The networks are built in polynomial time, with the clock in unary. -/
  polyTime : ComputableInPolyTime net (encPair encBits (encPair encUnary encNat)) encN
  /-- **The counting identity**: the values of the networks of all schedules sum to the count at
  the padded time. -/
  sum_value : ∀ x t, x.length ≤ t → 2 ≤ t →
    ∑ σ ∈ Finset.range (scheduleCount heads t), value (net (x, t, σ)) = count x (paddedTime t)
  /-- Every network of a schedule is admissible at size `t`. -/
  admissible : ∀ x t σ, x.length ≤ t → 2 ≤ t → σ < scheduleCount heads t →
    Admissible constant t (net (x, t, σ))

end Cslib.Complexity.CountingSimulation
