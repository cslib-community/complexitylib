/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.Basic
public import CslibFrontier.Computability.Circuit.Boolean.Oracle.LocalCircuit
import CslibFrontier.Computability.MCSP.Magnification.MergeTree.Circuit

/-!
# `MCSP[s]` in a local circuit class

This module states the \[MMW19\] bullet of
[ChenHiraharaOliveiraPichRajgopalSanthanam2020, Proposition 63] in the local circuit class
`Cslib.Circuits.Boolean.LocalCircuitClass` (their Definition 11). It wraps the
McKay–Murray–Williams merge-tree circuit `Cslib.MCSP.MergeTree.mmwCircuit` and its counts.

At input length `m`, with `n = log₂ m`, the class gets the merge-tree circuit for `MCSP[s(n)]`
on `2 ^ n`-bit truth tables. The class's bounds are the circuit's divided by `s(n)`: at most
`128 m / s + 1` oracle gates (`Cslib.MCSP.MergeTree.mul_cost_program_mmwCircuit_le`), each of
fan-in at most `12 s ⁴` (`Cslib.MCSP.MergeTree.fanInAtMost_mmwCircuit`, which bounds every gate
and so the oracle gates), at most `n / ⌊log₂ s⌋ + 1` oracle gates on any path
(`Cslib.MCSP.MergeTree.depthWith_mmwCircuit_le`), and at most `129 m / s + 3` gates
(`Cslib.MCSP.MergeTree.mul_size_mmwCircuit_le`). The oracle is `Cslib.MCSP.MergeTree.oracle` at
every length. The lengths that are not powers of two carry no instances
(`Cslib.Circuits.Boolean.LocalCircuitClass.of_two_pow`); the constant `3` in the size bound
already pays for the constant gate at length `0`.

The exact bounds hold for every `s` with `max 2 n ≤ s(n)`. When also `s(n) ≤ 2 ^ n = N`, they
read as `[O(N / s), O(s ⁴), O(n / log s)]–Circuit[O(N / s)]`: the bullet's
`[O(N / poly(s)), poly(s), O(n / log s)]–Circuit[N / poly(s)]` with `poly(s) = s` in the counts
and `s ⁴` in the fan-in. (For `s ≫ 2 ^ n` the quantity and adaptivity bounds are `Θ(1)`, not
`O(N / s)` and `O(n / log s)`.) As Definition 11 allows, no bound on the complexity of the oracle
is claimed.

Deviations from the source, which assumes only a constructive `s(n) ≤ 2 ^ n / poly(n)`:
* *Range of `s`.* The hypotheses `n ≤ s(n)` and `2 ≤ s(n)` restrict the bullet: they exclude
  `s(n) < n`, which the source allows. In the other direction the source's upper bound
  `s(n) ≤ 2 ^ n / poly(n)` is not needed for the exact bounds, and only `s(n) ≤ 2 ^ n`, which is
  weaker, for their `O`-reading.
* *Uniformity is not formalized.* `LocalCircuitClass` (Definition 11 as formalized) is
  nonuniform, so the theorem gives nonuniform oracle circuits, with the same fixed oracle
  `MergeTree.oracle` at every length, and it assumes nothing about how `s` is computed.

Source locator: ECCC TR19-168, Appendix A.2, Proposition 63, seventh bullet (p. 52).

## Main results

* `Cslib.MCSP.localCircuitClass_MCSP`: for `max 2 n ≤ s(n)` (a restriction of the source's range
  of `s`), `MCSP[s]` is in
  `[128 m / s + 1, 12 s ⁴, log₂ m / ⌊log₂ s⌋ + 1]–Circuit[129 m / s + 3]` on input length `m`,
  with `s` evaluated at `log₂ m`.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond natural
  proofs: hardness magnification and locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
* [D. McKay, C. D. Murray, R. R. Williams, *Weak Lower Bounds on Resource-Bounded Compression
  Imply Strong Separations of Complexity Classes*][McKayMurrayWilliams2019]
-/

public section

namespace Cslib.MCSP

open Circuits Circuits.Boolean MergeTree

/-- Dividing a bound `s x ≤ a + c s` by `s > 0`. -/
private theorem le_div_add_of_mul_le {s x a c : ℕ} (hs : 0 < s) (h : s * x ≤ a + c * s) :
    x ≤ a / s + c := by
  have h' : (x - c) * s ≤ a := by
    rw [Nat.sub_mul, Nat.mul_comm x]
    omega
  have := (Nat.le_div_iff_mul_le hs).2 h'
  omega

/-- **The \[MMW19\] bullet of [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Proposition 63]**
[ChenHiraharaOliveiraPichRajgopalSanthanam2020, Appendix A.2, p. 52; Section 2.5, Definition 11,
p. 13], with the range of `s` restricted. Whenever `n ≤ s(n)` and `2 ≤ s(n)` for every `n`,
`MCSP[s]` (the yes-instances `GapMCSP.yesSet s` and the no-instances `GapMCSP.noSet s`, with no
gap) is in the local circuit class with, at input length `m` and `n = Nat.log 2 m`,
- at most `128 m / s(n) + 1` oracle gates (quantity),
- each of fan-in at most `12 s(n) ^ 4` (locality),
- at most `n / ⌊log₂ s(n)⌋ + 1` oracle gates on any path (adaptivity),
- at most `129 m / s(n) + 3` gates.

The oracle is `MergeTree.oracle` at every length. Each truth-table length `m = 2 ^ n` is covered
by `MergeTree.mmwCircuit n (s n)`; the other lengths carry no instances, so any circuit within
the bounds will do (`LocalCircuitClass.of_two_pow`), and the size bound is at least `3` there.
Deviations: the source assumes only a constructive `s(n) ≤ 2 ^ n / poly(n)`. The hypotheses
`n ≤ s(n)` and `2 ≤ s(n)` exclude `s(n) < n`; the source's upper bound is not needed for these
exact bounds, which read as its `O`-bounds once also `s(n) ≤ 2 ^ n`. The circuits are
nonuniform; the source's constructivity of `s` (uniformity) is not formalized. -/
theorem localCircuitClass_MCSP {s : ℕ → ℕ} (hns : ∀ n, n ≤ s n) (hs : ∀ n, 2 ≤ s n) :
    LocalCircuitClass (fun m => 128 * m / s (Nat.log 2 m) + 1)
      (fun m => 12 * s (Nat.log 2 m) ^ 4)
      (fun m => Nat.log 2 m / Nat.log 2 (s (Nat.log 2 m)) + 1)
      (fun m => 129 * m / s (Nat.log 2 m) + 3)
      (GapMCSP.yesSet s) (GapMCSP.noSet s) := by
  -- `1 ≤ S 0` holds as stated (`S 0 = 3`), so unlike `localCircuitClass_gapMCSP` no `+ 1` is added.
  refine LocalCircuitClass.of_two_pow oracle (Nat.le_add_left _ _)
    (fun _ ⟨n, h, _⟩ => ⟨n, h⟩) (fun _ ⟨n, h, _⟩ => ⟨n, h⟩) fun n => ?_
  have hs0 : 0 < s n := by have := hs n; omega
  have hc := mul_cost_program_mmwCircuit_le (hns n)
  have hS := mul_size_mmwCircuit_le (hns n)
  simp only [Nat.log_pow Nat.one_lt_two]
  refine ⟨mmwCircuit n (s n), le_div_add_of_mul_le hs0 hS, le_div_add_of_mul_le hs0 (by omega),
    .of_fanInAtMost (fanInAtMost_mmwCircuit (hns n) (hs n)), depthWith_mmwCircuit_le n (s n),
    fun x hx => ?_, fun x hx => ?_⟩
  · rw [eval_mmwCircuit, Language.slice_eq_true_iff]
    exact hx
  · rw [GapMCSP.ofFn_mem_noSet_iff] at hx
    rw [eval_mmwCircuit, Bool.eq_false_iff, Ne, GapMCSP.slice_yesSet_eq_true_iff]
    omega

end Cslib.MCSP
