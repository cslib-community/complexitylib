/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Tactic.PolyTime


import Diag1155.Measure
/-!
# Quantitative certificates for polynomial PRG stretch

Keep a seed of the original length at the front of a word. Each iteration expands that seed by one
bit and retains the previously emitted suffix. Efficiency (`polyTime_iterate`, `polyTime_stretch`)
only needs a bounded seed prefix; the one-bit length promise is used separately to prove output
lengths.

Under the genuine one-bit length invariant (`(generator s).length = s.length + 1`), `iterate` and
`stretch` also admit plain cumulative certificates (`ComputableInTimeAndSpace`) that stream the
emitted bits in forward generation order followed by the reversed final seed (`forwardIterate`),
charging `O(n + k + ∑_{i < k} (tGen(seed_i) + n + 1))` time and `O(Q + n + 1)` workspace during
the streaming loop. Workspace counts only work-tape cells; emitted output is not charged to it.
The proof then uses a linear-time zero-workspace tidy reversal
(`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.reverse_bits`), whose composition charges the
`(n + k)`-bit reversal buffer to restore the exact original output order.

## Main definitions

* `Cslib.Crypto.PRGStretch.step`, `Cslib.Crypto.PRGStretch.iterate`,
  `Cslib.Crypto.PRGStretch.stretch`: repeatedly expand a fixed-width seed prefix and retain
  emitted bits.
* `Cslib.Crypto.PRGStretch.seedStep`, `Cslib.Crypto.PRGStretch.emitBit`,
  `Cslib.Crypto.PRGStretch.seedAt`, `Cslib.Crypto.PRGStretch.forwardIterate`: seed trajectory and
  forward-streamed intermediate representation before final reversal.

## Main results

* `Cslib.Crypto.PRGStretch.polyTime_iterate`, `Cslib.Crypto.PRGStretch.polyTime_stretch`: captured
  functional iteration and stretch have uniform polynomial-time TM certificates without a length
  promise on the generator.
* `Cslib.Crypto.PRGStretch.forwardIterate_eq`: the forward representation emits each round's bit in
  generation order, then the reversed final seed.
* `Cslib.Crypto.PRGStretch.reverse_forwardIterate_eq_iterate`: the reverse of forward iteration
  matches `iterate` under the stated length hypothesis.
* `Cslib.Crypto.PRGStretch.computableInTimeAndSpace_forwardIterate`,
  `Cslib.Crypto.PRGStretch.computableInTimeAndSpace_forwardIterate_captured`: streaming `k`
  expansions in forward order with cumulative time and `k`-independent workspace `O(Q + n + 1)`,
  their proofs use `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum`.
* `Cslib.Crypto.PRGStretch.computableInTimeAndSpace_iterate_pair`,
  `Cslib.Crypto.PRGStretch.computableInTimeAndSpace_iterate_captured`,
  `Cslib.Crypto.PRGStretch.computableInTimeAndSpace_stretch`,
  `Cslib.Crypto.PRGStretch.computableInDegree_stretch`,
  `Cslib.Crypto.PRGStretch.polyTime_stretch_of_length_eq`: quantitative cumulative-time, workspace
  and degree certificates for `iterate` (unparameterized and with captured parameters) and
  `stretch`, preserving the exact reverse-generation output order and recovering
  `ComputableInPolyTime`.

## References

* [B. Barak, *Pseudorandomness*, CS 127][Barak2016PRG], length extension for PRGs.
  We retain the final seed and reverse the order of the emitted bits.
-/

@[expose] public section

namespace Cslib.Crypto.PRGStretch

open Turing.MultiTapeTM

/-- Expand the first `n` bits, preserving the previously emitted suffix. -/
def step (generator : List Bool → List Bool) (n : ℕ) (word : List Bool) : List Bool :=
  generator (word.take n) ++ word.drop n

/-- Repeat seed expansion a specified number of times. -/
def iterate (generator : List Bool → List Bool) (n count : ℕ) (word : List Bool) : List Bool :=
  (step generator n)^[count] word

/-- A one-bit generator yields `count n` additional bits from an `n`-bit seed. -/
def stretch (generator : List Bool → List Bool) (count : ℕ → ℕ) (seed : List Bool) : List Bool :=
  iterate generator seed.length (count seed.length) seed

/-- Each call increases the whole word's length by one, even on short intermediate words. -/
theorem length_step {generator : List Bool → List Bool}
    (hlen : ∀ seed, (generator seed).length = seed.length + 1) (n : ℕ) (word : List Bool) :
    (step generator n word).length = word.length + 1 := by
  simp only [step, List.length_append, hlen, List.length_take, List.length_drop]
  lia

/-- The loop's length invariant. -/
theorem length_iterate {generator : List Bool → List Bool}
    (hlen : ∀ seed, (generator seed).length = seed.length + 1) (n count : ℕ) (word : List Bool) :
    (iterate generator n count word).length = word.length + count := by
  induction count with
  | zero => simp [iterate]
  | succ count ih =>
    simp only [iterate, Function.iterate_succ_apply', length_step hlen]
    simp only [iterate] at ih
    lia

/-- A generator need only expand seeds at the specified length. Longer input words carry a
saved suffix, and every subsequent iteration again uses a correctly sized seed prefix. -/
theorem length_iterate_of_le {generator : List Bool → List Bool} {seedBits : ℕ}
    (hlen : ∀ seed, seed.length = seedBits → (generator seed).length = seedBits + 1)
    (count : ℕ) (word : List Bool) (hword : seedBits ≤ word.length) :
    (iterate generator seedBits count word).length = word.length + count := by
  induction count with
  | zero => simp [iterate]
  | succ count ih =>
    rw [iterate, Function.iterate_succ_apply']
    change (step generator seedBits (iterate generator seedBits count word)).length = _
    rw [step, List.length_append, hlen _ (by
      rw [List.length_take, ih]
      exact Nat.min_eq_left (by lia)), List.length_drop, ih]
    lia

/-- A valid seed prefix is expanded independently of the saved suffix. -/
theorem step_append (generator : List Bool → List Bool) {n : ℕ} (seed suffix : List Bool)
    (hlen : seed.length = n) : step generator n (seed ++ suffix) = generator seed ++ suffix := by
  subst n
  simp [step]

/-- Iteration may capture an arbitrary encoded input. Every call reads only a bounded seed
prefix, so polynomial time follows without a length promise on the generator. -/
theorem polyTime_iterate {α : Type} {input : α ↪ List Bool}
    {generator : α → List Bool → List Bool} {seedBits count : α → ℕ} {word : α → List Bool}
    (hgenerator : ComputableInPolyTime (fun pair => generator pair.1 pair.2)
      (encPair input encBits) encBits)
    (hseedBits : ComputableInPolyTime seedBits input encUnary)
    (hcount : ComputableInPolyTime count input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => iterate (generator a) (seedBits a) (count a) (word a))
      input encBits := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hgenerator
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hseedBits
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hcount
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hword
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  obtain ⟨c, d, hlength⟩ := hgenerator.polyBounded_length.exists_le
  have hpoly : PolyBounded (fun a => (input a).length)
      (fun a => c * (2 * (input a).length + seedBits a + 2) ^ d) :=
    ComputableTidilyInPolyTime.polyBounded (by fun_prop)
  have hgrowth (a : α) (state : List Bool) :
      (generator a (state.take (seedBits a)) ++ state.drop (seedBits a)).length ≤
        state.length + c * (2 * (input a).length + seedBits a + 2) ^ d := by
    have h := hlength (a, state.take (seedBits a))
    simp only [length_encPair, encBits_apply, List.length_take] at h
    have hbound : (generator a (state.take (seedBits a))).length ≤
        c * (2 * (input a).length + seedBits a + 2) ^ d :=
      h.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    simp only [List.length_append, List.length_drop]
    lia
  unfold iterate step
  polytime

attribute [program_certificate] polyTime_iterate

/-- Any efficiently computed iteration count gives an efficient generator. -/
theorem polyTime_stretch {generator : List Bool → List Bool} {count : ℕ → ℕ}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    ComputableInPolyTime (stretch generator count) encBits encBits := by
  unfold stretch
  polytime

/-! ### Quantitative cumulative-time and workspace certificates -/

/-- The next seed produced by one expansion: all but the last bit of `generator seed`. -/
def seedStep (generator : List Bool → List Bool) (seed : List Bool) : List Bool :=
  (generator seed).dropLast

/-- The single output bit emitted by one expansion, as a 0-or-1-element list. -/
def emitBit (generator : List Bool → List Bool) (seed : List Bool) : List Bool :=
  (generator seed).getLast?.toList

/-- The seed at round `i` of one-bit expansion starting from `seed`. -/
def seedAt (generator : List Bool → List Bool) (seed : List Bool) (i : ℕ) : List Bool :=
  (seedStep generator)^[i] seed

/-- Forward streaming representation of `count` PRG expansions from `seed`: emits each round's bit
in forward generation order, followed by the reversed final seed
`(seedAt generator seed count).reverse`. Reversing this word once yields
`iterate generator seed.length count seed`. -/
def forwardIterate (generator : List Bool → List Bool) (count : ℕ) (seed : List Bool) :
    List Bool :=
  streamEmit (fun p : List Bool × Bool => seedStep generator p.1)
    (fun p => emitBit generator p.1) seed (List.replicate count true) ++
    (seedAt generator seed count).reverse

@[simp]
theorem seedAt_zero (generator : List Bool → List Bool) (seed : List Bool) :
    seedAt generator seed 0 = seed := rfl

theorem seedAt_succ (generator : List Bool → List Bool) (seed : List Bool) (i : ℕ) :
    seedAt generator seed (i + 1) = seedStep generator (seedAt generator seed i) :=
  Function.iterate_succ_apply' _ _ _

/-- A non-empty generator output splits into its next-seed prefix and its emitted bit. -/
theorem seedStep_append_emitBit (generator : List Bool → List Bool) (seed : List Bool)
    (hne : generator seed ≠ []) :
    seedStep generator seed ++ emitBit generator seed = generator seed := by
  unfold seedStep emitBit
  rw [List.getLast?_eq_some_getLast hne, Option.toList_some, List.dropLast_append_getLast hne]

/-- Under the one-bit length promise at width `n`, `seedStep` preserves width `n`. -/
theorem length_seedStep_of_eq {generator : List Bool → List Bool} {n : ℕ}
    (hlen : ∀ s, s.length = n → (generator s).length = n + 1) {s : List Bool} (hs : s.length = n) :
    (seedStep generator s).length = n := by
  simp [seedStep, List.length_dropLast, hlen s hs]

/-- Under the one-bit length promise at width `n`, `emitBit` has length `1`. -/
theorem length_emitBit_of_eq {generator : List Bool → List Bool} {n : ℕ}
    (hlen : ∀ s, s.length = n → (generator s).length = n + 1) {s : List Bool} (hs : s.length = n) :
    (emitBit generator s).length = 1 := by
  have hne : generator s ≠ [] := List.ne_nil_of_length_pos (by have := hlen s hs; omega)
  simp [emitBit, List.getLast?_eq_some_getLast hne]

/-- `emitBit` has at most one element, so reversing it is the identity. -/
@[simp]
theorem reverse_emitBit (generator : List Bool → List Bool) (s : List Bool) :
    (emitBit generator s).reverse = emitBit generator s := by
  unfold emitBit
  cases (generator s).getLast? <;> rfl

/-- Under the one-bit length promise at `seed.length`, every round seed `seedAt generator seed i`
has length `seed.length`. -/
theorem length_seedAt {generator : List Bool → List Bool} {seed : List Bool}
    (hlen : ∀ s, s.length = seed.length → (generator s).length = seed.length + 1) (i : ℕ) :
    (seedAt generator seed i).length = seed.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [seedAt_succ]
    exact length_seedStep_of_eq hlen ih

/-- The streaming fold state after `j ≤ count` unary tokens equals `seedAt generator seed j`. -/
theorem streamState_replicate_eq_seedAt (generator : List Bool → List Bool) (seed : List Bool)
    (count j : ℕ) (hj : j ≤ count) :
    streamState seed (fun p : List Bool × Bool => seedStep generator p.1)
      (List.replicate count true) j = seedAt generator seed j :=
  streamState_replicate (seedStep generator) seed true hj

/-- Expanding `seed ++ suffix` for `count` rounds produces `seedAt generator seed count`, followed
by the emitted bits in reverse generation order, followed by `suffix`. -/
theorem iterate_append_eq_seedAt_append_streamEmit_reverse {generator : List Bool → List Bool}
    {n : ℕ} (hlen : ∀ s, s.length = n → (generator s).length = n + 1)
    (count : ℕ) {seed : List Bool} (hseed : seed.length = n) (suffix : List Bool) :
    iterate generator n count (seed ++ suffix) =
      seedAt generator seed count ++
        (streamEmit (fun p : List Bool × Bool => seedStep generator p.1)
          (fun p => emitBit generator p.1) seed (List.replicate count true)).reverse ++
        suffix := by
  induction count generalizing seed suffix with
  | zero => simp [iterate, seedAt, streamEmit]
  | succ count ih =>
    have hne : generator seed ≠ [] :=
      List.ne_nil_of_length_pos (by have := hlen seed hseed; omega)
    have hstep_len : (seedStep generator seed).length = n :=
      length_seedStep_of_eq hlen hseed
    rw [iterate, Function.iterate_succ_apply, ← iterate, step_append generator seed suffix hseed,
      ← seedStep_append_emitBit generator seed hne, List.append_assoc,
      ih hstep_len (emitBit generator seed ++ suffix),
      List.replicate_succ, streamEmit, List.reverse_append, reverse_emitBit]
    simp only [seedAt, Function.iterate_succ_apply, List.append_assoc]

/-- Reversing `forwardIterate generator count seed` recovers the exact output of
`iterate generator seed.length count seed` (final seed followed by emitted bits in reverse
generation order). -/
theorem reverse_forwardIterate_eq_iterate {generator : List Bool → List Bool} {seed : List Bool}
    (hlen : ∀ s, s.length = seed.length → (generator s).length = seed.length + 1) (count : ℕ) :
    (forwardIterate generator count seed).reverse =
      iterate generator seed.length count seed := by
  have h := iterate_append_eq_seedAt_append_streamEmit_reverse hlen count rfl []
  simpa only [forwardIterate, List.append_nil, List.reverse_append,
    List.reverse_reverse] using h.symm

/-- `forwardIterate generator count seed` has length `seed.length + count`. -/
theorem length_forwardIterate {generator : List Bool → List Bool} {seed : List Bool}
    (hlen : ∀ s, s.length = seed.length → (generator s).length = seed.length + 1) (count : ℕ) :
    (forwardIterate generator count seed).length = seed.length + count := by
  rw [← List.length_reverse, reverse_forwardIterate_eq_iterate hlen count,
    length_iterate_of_le hlen count seed le_rfl]

theorem length_seedAt_of_forall {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (i : ℕ) :
    (seedAt generator seed i).length = seed.length :=
  length_seedAt (fun s hs => by rw [hlen, hs]) i

theorem reverse_forwardIterate_eq_iterate_of_forall {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    (forwardIterate generator count seed).reverse =
      iterate generator seed.length count seed :=
  reverse_forwardIterate_eq_iterate (fun s hs => by rw [hlen, hs]) count

theorem length_forwardIterate_of_forall {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    (forwardIterate generator count seed).length = seed.length + count :=
  length_forwardIterate (fun s hs => by rw [hlen, hs]) count

/-- `forwardIterate` emits the bits of the rounds in generation order, then the reversed final
seed. -/
theorem forwardIterate_eq (generator : List Bool → List Bool) (count : ℕ) (seed : List Bool) :
    forwardIterate generator count seed =
      ((List.range count).map fun i => emitBit generator (seedAt generator seed i)).flatten ++
        (seedAt generator seed count).reverse := by
  rw [forwardIterate, streamEmit_eq, List.length_replicate]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  simp [hi', streamState_replicate_eq_seedAt generator seed count i hi'.le]

private theorem iterate_seedStep (generator : List Bool → List Bool) (seed : List Bool) (i : ℕ) :
    (seedStep generator)^[i] seed = seedAt generator seed i := rfl

/-- A captured parameter stays fixed while the seed follows its trajectory. -/
private theorem iterate_seedStep_captured {α : Type} (generator : α → List Bool → List Bool)
    (q : α × List Bool) (i : ℕ) :
    (fun q : α × List Bool => (q.1, seedStep (generator q.1) q.2))^[i] q =
      (q.1, seedAt (generator q.1) q.2 i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, seedAt_succ]

/-- Reversing a forward certificate yields `iterate`, charging the `(n + k)`-bit reversal
buffer. -/
private theorem iterate_of_forwardIterate {γ : Type} {encIn : γ ↪ List Bool}
    {generator : γ → List Bool → List Bool} {seed : γ → List Bool} {count : γ → ℕ}
    (hlen : ∀ x s, (generator x s).length = s.length + 1) {t s : γ → ℕ}
    (h : ComputableTidilyInTimeAndSpace (fun x => forwardIterate (generator x) (count x) (seed x))
      encIn encBits t s) :
    ∃ c, ComputableTidilyInTimeAndSpace
      (fun x => iterate (generator x) (seed x).length (count x) (seed x)) encIn encBits
      (fun x => c * (t x + (seed x).length + count x + 1))
      (fun x => c * (s x + (seed x).length + count x + 1)) := by
  obtain ⟨c, hrev⟩ := ComputableTidilyInTimeAndSpace.reverse_bits.comp h
  have heq : (List.reverse ∘ fun x => forwardIterate (generator x) (count x) (seed x)) =
      fun x => iterate (generator x) (seed x).length (count x) (seed x) :=
    funext fun x => reverse_forwardIterate_eq_iterate_of_forall (hlen x) (seed x) (count x)
  rw [heq] at hrev
  refine ⟨c + 13, hrev.mono (fun x => ?_) (fun x => ?_)⟩ <;>
  · simp only [encBits_apply, length_forwardIterate_of_forall (hlen x)]
    nlinarith

/-- **Quantitative streaming certificate for `forwardIterate`.** On input `(seed, count)` encoded
with `encPair encBits encUnary`, `forwardIterate` streams `count` rounds directly from the unary
suffix on the input tape, emitting each round's bit in generation order and finishing with the
reversed final seed. Each round runs the generator twice, once for the next seed and once for the
emitted bit, and both runs are charged; workspace is `O(Q + seed.length + 1)`, independent of the
round count `count`. -/
theorem computableInTimeAndSpace_forwardIterate
    {generator : List Bool → List Bool} {tGen sGen : List Bool → ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgen : ComputableInTimeAndSpace generator encBits encBits tGen sGen)
    {Q : List Bool × ℕ → ℕ}
    (hspace : ∀ p i, i < p.2 → sGen (seedAt generator p.1 i) ≤ Q p) :
    ∃ c, ComputableInTimeAndSpace
      (fun p : List Bool × ℕ => forwardIterate generator p.2 p.1)
      (encPair encBits encUnary) encBits
      (fun p => c * (p.1.length + p.2 +
        (∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1)) + 1))
      (fun p => c * (Q p + p.1.length + 1)) := by
  have build
      {generator : List Bool → List Bool} {tGen sGen : List Bool → ℕ}
      (hlen : ∀ s, (generator s).length = s.length + 1)
      (hgen : ComputableTidilyInTimeAndSpace generator encBits encBits tGen sGen)
      {Q : List Bool × ℕ → ℕ}
      (hspace : ∀ p i, i < p.2 → sGen (seedAt generator p.1 i) ≤ Q p) :
      ∃ c, ComputableTidilyInTimeAndSpace
        (fun p : List Bool × ℕ => forwardIterate generator p.2 p.1)
        (encPair encBits encUnary) encBits
        (fun p => c * (p.1.length + p.2 +
          (∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1)) + 1))
        (fun p => c * (Q p + p.1.length + 1)) := by
    obtain ⟨c₁, hnext₀⟩ := ComputableTidilyInTimeAndSpace.dropLast_bits.comp hgen
    obtain ⟨c₂, hemit₀⟩ := ComputableTidilyInTimeAndSpace.getLast?_toList_bits.comp hgen
    obtain ⟨K, hK⟩ : ∃ K, K = c₁ + c₂ + 30 := ⟨_, rfl⟩
    have hnext : ComputableTidilyInTimeAndSpace (seedStep generator) encBits encBits
        (fun s => tGen s + K * (s.length + 1)) (fun s => sGen s + K * (s.length + 1)) :=
      hnext₀.mono (fun s => by simp only [encBits_apply, hlen]; nlinarith)
        (fun s => by simp only [encBits_apply, hlen]; nlinarith)
    have hemit : ComputableTidilyInTimeAndSpace (emitBit generator) encBits encBits
        (fun s => tGen s + K * (s.length + 1)) (fun s => sGen s + K * (s.length + 1)) :=
      hemit₀.mono (fun s => by simp only [encBits_apply, hlen]; nlinarith)
        (fun s => by simp only [encBits_apply, hlen]; nlinarith)
    obtain ⟨c, h⟩ := hnext.iterate_unary_stream_sum hemit
      ComputableTidilyInTimeAndSpace.reverse_bits
      (R := fun p i => (2 * K + 2) * (tGen (seedAt generator p.1 i) + p.1.length + 1))
      (Q := fun p => 2 * Q p + 2 * K * (p.1.length + 1)) (B := fun p => p.1.length)
      (fun p i _ => by
        simp only [iterate_seedStep, encBits_apply, length_seedAt_of_forall hlen]
        nlinarith)
      (fun p i hi => by
        have := hspace p i hi
        simp only [iterate_seedStep, length_seedAt_of_forall hlen]
        nlinarith)
      (fun p i _ => by
        simp only [iterate_seedStep, encBits_apply, length_seedAt_of_forall hlen]
        rfl)
    refine ⟨c * (2 * K + 6), ?_⟩
    simp only [forwardIterate_eq]
    refine h.mono (fun p => ?_) (fun p => ?_) <;>
      simp only [iterate_seedStep, length_seedAt_of_forall hlen,
        ← Finset.mul_sum, Nat.mul_assoc] <;>
      refine Nat.mul_le_mul_left c ?_
    · generalize ∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1) = S
      nlinarith [Nat.zero_le (K * p.1.length), Nat.zero_le (K * p.2)]
    · nlinarith [Nat.zero_le (K * Q p)]
  have hcharged := hgen.mono (fun _ => le_rfl)
    (fun seed => Nat.le_add_right (sGen seed) (seed.length + 1))
  obtain ⟨a, hclean, _⟩ := hcharged.computableTidilyInO (fun seed => by
    simp only [encBits_apply, hlen]
    omega)
  obtain ⟨c, h⟩ := build hlen hclean
    (Q := fun p => a * (Q p + p.1.length + 2)) (fun p i hi => by
      have hs := hspace p i hi
      simp only [length_seedAt_of_forall hlen]
      exact Nat.mul_le_mul_left a (by omega))
  refine ⟨c * (2 * a + 3), h.computableInTimeAndSpace.mono ?_ ?_⟩
  · intro p
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    have hsum := Finset.sum_le_sum (s := Finset.range p.2)
      (fun i _ => show a * (tGen (seedAt generator p.1 i) + 1) + p.1.length + 1 ≤
        (a + 1) * (tGen (seedAt generator p.1 i) + p.1.length + 1) by nlinarith)
    rw [← Finset.mul_sum] at hsum
    calc
      _ ≤ p.1.length + p.2 + (a + 1) *
          (∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1)) + 1 := by
        omega
      _ ≤ (a + 1) * (p.1.length + p.2 +
          (∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1)) + 1) := by
        nlinarith [Nat.zero_le (a * (p.1.length + p.2 + 1))]
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · intro p
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith [Nat.zero_le (a * (Q p + p.1.length))]

/-- **Quantitative cumulative-time and workspace certificate for `PRGStretch.iterate`.**
The proof composes `forwardIterate` with the linear-time zero-workspace tidy reversal primitive
`ComputableTidilyInTimeAndSpace.reverse_bits` produces the exact output of
`iterate generator p.1.length p.2 p.1`. The time bound remains
`O(n + k + ∑_{i < k} (tGen(seed_i) + n + 1))`, while the workspace bound `O(Q + n + k + 1)`
explicitly includes the `(n + k)`-bit intermediate reversal buffer. -/
theorem computableInTimeAndSpace_iterate_pair
    {generator : List Bool → List Bool} {tGen sGen : List Bool → ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgen : ComputableInTimeAndSpace generator encBits encBits tGen sGen)
    {Q : List Bool × ℕ → ℕ}
    (hspace : ∀ p i, i < p.2 → sGen (seedAt generator p.1 i) ≤ Q p) :
    ∃ c, ComputableInTimeAndSpace
      (fun p : List Bool × ℕ => iterate generator p.1.length p.2 p.1)
      (encPair encBits encUnary) encBits
      (fun p => c * (p.1.length + p.2 +
        (∑ i ∈ Finset.range p.2, (tGen (seedAt generator p.1 i) + p.1.length + 1)) + 1))
      (fun p => c * (Q p + p.1.length + p.2 + 1)) := by
  obtain ⟨c, hfwd⟩ := computableInTimeAndSpace_forwardIterate hlen hgen hspace
  have hcharged := hfwd.mono (fun _ => le_rfl)
    (fun p => show c * (Q p + p.1.length + 1) ≤
      (c + 1) * (Q p + p.1.length + p.2 + 1) by nlinarith [Nat.zero_le (c * p.2)])
  obtain ⟨a, hclean, _⟩ := hcharged.computableTidilyInO (fun p => by
    simp only [encBits_apply, length_forwardIterate_of_forall hlen]
    nlinarith [Nat.zero_le (c * (Q p + p.1.length + p.2 + 1))])
  obtain ⟨b, h⟩ := iterate_of_forwardIterate (generator := (fun _ => generator))
    (seed := Prod.fst) (count := Prod.snd) (fun _ => hlen) hclean
  refine ⟨b * (a * (c + 2) + 1), h.computableInTimeAndSpace.mono ?_ ?_⟩
  · intro p
    let T := p.1.length + p.2 + (∑ i ∈ Finset.range p.2,
          (tGen (seedAt generator p.1 i) + p.1.length + 1)) + 1
    have hbase : p.1.length + p.2 + 1 ≤ T := by dsimp only [T]; omega
    have hpos : 1 ≤ T := by omega
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left b
    change a * (c * T + 1) + p.1.length + p.2 + 1 ≤ (a * (c + 2) + 1) * T
    have hscaled := Nat.mul_le_mul_left a (show c * T + 1 ≤ (c + 1) * T by nlinarith)
    nlinarith [Nat.zero_le (a * T)]
  · intro p
    let S := Q p + p.1.length + p.2 + 1
    have hbase : p.1.length + p.2 + 1 ≤ S := by dsimp only [S]; omega
    have hpos : 1 ≤ S := by omega
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left b
    change a * ((c + 1) * S + 1) + p.1.length + p.2 + 1 ≤
      (a * (c + 2) + 1) * S
    have hscaled := Nat.mul_le_mul_left a (show (c + 1) * S + 1 ≤ (c + 2) * S by nlinarith)
    nlinarith

/-- **Quantitative cumulative-time and workspace certificate for `PRGStretch.stretch`.**
On input `seed : List Bool` of length `n` with `k = count n`, `stretch generator count` runs in
time `O(tCount n + n + k + ∑_{i < k} (tGen(seed_i) + n + 1))` and workspace
`O(sCount n + Q seed + n + k + 1)`, charging `count`, pair assembly, every round's generator
callbacks and seed copying, and the `(n + k)`-bit reversal buffer. -/
theorem computableInTimeAndSpace_stretch
    {generator : List Bool → List Bool} {count : ℕ → ℕ}
    {tGen sGen : List Bool → ℕ} {tCount sCount : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgen : ComputableInTimeAndSpace generator encBits encBits tGen sGen)
    (hcount : ComputableInTimeAndSpace count encUnary encUnary tCount sCount)
    {Q : List Bool → ℕ}
    (hspace : ∀ seed i, i < count seed.length → sGen (seedAt generator seed i) ≤ Q seed) :
    ∃ c, ComputableInTimeAndSpace (stretch generator count) encBits encBits
      (fun seed => c * (tCount seed.length + seed.length + count seed.length +
        (∑ i ∈ Finset.range (count seed.length),
          (tGen (seedAt generator seed i) + seed.length + 1)) + 1))
      (fun seed => c * (sCount seed.length + Q seed + seed.length + count seed.length + 1)) := by
  have hcountCharged := hcount.mono (fun _ => le_rfl)
    (fun n => Nat.le_add_right (sCount n) (count n))
  obtain ⟨a, hcountClean, _⟩ := hcountCharged.computableTidilyInO (fun n => by
    simp only [encUnary_apply, List.length_replicate]
    omega)
  obtain ⟨c₁, hcnt_seed⟩ := hcountClean.comp ComputableTidilyInTimeAndSpace.length_bits
  obtain ⟨c₂, hpair⟩ := Internal.NormalForm.bigO
    (PairEncoding.pair_mono (enc := encPair encBits encUnary)
      (computableTidilyInTimeAndSpace_id (enc := encBits)).computableInTimeAndSpace
      hcnt_seed.computableInTimeAndSpace)
  obtain ⟨c₃, hiter⟩ := computableInTimeAndSpace_iterate_pair hlen hgen
    (Q := fun p => Finset.sup (Finset.range p.2) (fun i => sGen (seedAt generator p.1 i)))
    (fun p i hi => Finset.le_sup (f := fun j => sGen (seedAt generator p.1 j))
      (Finset.mem_range.mpr hi))
  have hiterCharged := hiter.mono (fun _ => le_rfl)
    (fun p => Nat.mul_le_mul_right _ (Nat.le_add_right c₃ 1))
  obtain ⟨b, hiterClean, _⟩ := hiterCharged.computableTidilyInO (fun p => by
    simp only [encBits_apply, length_iterate hlen]
    nlinarith [Nat.zero_le (c₃ * (Finset.sup (Finset.range p.2)
      (fun i => sGen (seedAt generator p.1 i)) + p.1.length + p.2 + 1))])
  obtain ⟨c₄, hcomp⟩ := hiterClean.comp hpair
  have heq : ((fun p : List Bool × ℕ => iterate generator p.1.length p.2 p.1) ∘
      fun seed : List Bool => (id seed, (count ∘ List.length) seed)) =
      stretch generator count := rfl
  rw [heq] at hcomp
  let C := c₂ * a + c₂ * c₁ + 50 * c₂ + b * c₃ + 3 * b + c₄ + 50
  refine ⟨C, hcomp.computableInTimeAndSpace.mono (fun seed => ?_) (fun seed => ?_)⟩
  · let T := tCount seed.length + seed.length + count seed.length +
        (∑ i ∈ Finset.range (count seed.length),
          (tGen (seedAt generator seed i) + seed.length + 1)) + 1
    have ht : tCount seed.length + 1 ≤ T := by dsimp only [T]; omega
    have hn : seed.length + 1 ≤ T := by dsimp only [T]; omega
    have hi : seed.length + count seed.length +
        (∑ i ∈ Finset.range (count seed.length),
          (tGen (seedAt generator seed i) + seed.length + 1)) + 1 ≤ T := by
      dsimp only [T]; omega
    have hpos : 0 < T := by omega
    simp only [Function.comp_apply, id_eq, length_encPair, encBits_apply, encUnary_apply,
      List.length_replicate]
    change _ ≤ C * T
    calc
      _ ≤ (c₂ * a + 22 * c₂ + b * (c₃ + 1) + 13) * T := by
        nlinarith [Nat.mul_le_mul_left (c₂ * a) ht,
          Nat.mul_le_mul_left c₂ (show 10 * seed.length + 22 ≤ 22 * T by omega),
          Nat.mul_le_mul_left (b * c₃) hi, Nat.le_mul_of_pos_right b hpos,
          show 8 * seed.length + 4 * count seed.length + 13 ≤ 13 * T by
            dsimp only [T]; omega]
      _ ≤ C * T := Nat.mul_le_mul_right T (by dsimp only [C]; nlinarith)
  · let S := sCount seed.length + Q seed + seed.length + count seed.length + 1
    have hs : sCount seed.length + count seed.length + 1 ≤ S := by dsimp only [S]; omega
    have hn : seed.length + count seed.length + 1 ≤ S := by dsimp only [S]; omega
    have hpos : 0 < S := by omega
    have hQle : Finset.sup (Finset.range (count seed.length))
        (fun i => sGen (seedAt generator seed i)) ≤ Q seed :=
      Finset.sup_le fun i hi => hspace seed i (Finset.mem_range.mp hi)
    have hi : Finset.sup (Finset.range (count seed.length))
        (fun i => sGen (seedAt generator seed i)) + seed.length + count seed.length + 1 ≤ S := by
      dsimp only [S]; omega
    simp only [Function.comp_apply, id_eq, length_encPair, encBits_apply, encUnary_apply,
      List.length_replicate]
    change _ ≤ C * S
    calc
      _ ≤ (c₂ * a + c₂ * c₁ + 9 * c₂ + b * (c₃ + 2) + 15 + c₄) * S := by
        nlinarith [Nat.mul_le_mul_left (c₂ * a) hs,
          Nat.mul_le_mul_left c₂ (show 7 * seed.length + count seed.length + 2 ≤ 9 * S by omega),
          Nat.le_mul_of_pos_right (c₂ * c₁) hpos,
          Nat.mul_le_mul_left (b * (c₃ + 1)) hi, Nat.le_mul_of_pos_right b hpos,
          Nat.le_mul_of_pos_right c₄ hpos,
          show 10 * seed.length + 5 * count seed.length + 5 ≤ 15 * S by omega]
      _ ≤ C * S := Nat.mul_le_mul_right S (by dsimp only [C]; nlinarith)

/-- **Degree-level quantitative certificate for `PRGStretch.stretch`.**
If `generator` is computable in degree `(dGen, eGen)` and `count` is computable in degree
`(dCount, eCount)`, then under the one-bit length promise `(generator s).length = s.length + 1`,
`stretch generator count` is computable in time/space degree `max dCount (eCount + max dGen 1)` and
output-size degree `max 1 eCount`. -/
theorem computableInDegree_stretch
    {generator : List Bool → List Bool} {count : ℕ → ℕ}
    {dGen eGen dCount eCount : ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgen : ComputableInDegree generator encBits encBits dGen eGen)
    (hcount : ComputableInDegree count encUnary encUnary dCount eCount) :
    ComputableInDegree (stretch generator count) encBits encBits
      (max dCount (eCount + max dGen 1)) (max 1 eCount) := by
  obtain ⟨⟨tGen, sGen, ⟨ctG, hctG⟩, ⟨csG, hcsG⟩, hgen_ts⟩, -⟩ := hgen
  obtain ⟨⟨tCount, sCount, ⟨ctC, hctC⟩, ⟨csC, hcsC⟩, hcount_ts⟩, ⟨clC, hclC⟩⟩ := hcount
  obtain ⟨c, hstretch⟩ := computableInTimeAndSpace_stretch hlen hgen_ts hcount_ts
    (Q := fun seed => csG * (seed.length + 1) ^ dGen)
    (fun seed i _ => by
      simpa only [encBits_apply, length_seedAt_of_forall hlen] using
        hcsG (seedAt generator seed i))
  let size : List Bool → ℕ := fun seed => (encBits seed).length
  let d := max dCount (eCount + max dGen 1)
  have hdCount : dCount ≤ d := le_max_left _ _
  have heGen : eCount + max dGen 1 ≤ d := le_max_right _ _
  have hdGen : dGen ≤ d := (le_max_left dGen 1).trans ((Nat.le_add_left _ eCount).trans heGen)
  have h1 : 1 ≤ d := (le_max_right dGen 1).trans ((Nat.le_add_left _ eCount).trans heGen)
  have heCount : eCount ≤ d := (Nat.le_add_right eCount (max dGen 1)).trans heGen
  have htC : DegreeBounded size (fun seed => tCount seed.length) d :=
    DegreeBounded.mono_deg ⟨ctC, fun s => by simpa [size] using hctC s.length⟩ hdCount
  have hsC : DegreeBounded size (fun seed => sCount seed.length) d :=
    DegreeBounded.mono_deg ⟨csC, fun s => by simpa [size] using hcsC s.length⟩ hdCount
  have hlC_e : DegreeBounded size (fun seed => count seed.length) eCount :=
    ⟨clC, fun s => by simpa [size] using hclC s.length⟩
  have hlC : DegreeBounded size (fun seed => count seed.length) d :=
    hlC_e.mono_deg heCount
  have hseed : DegreeBounded size List.length d :=
    DegreeBounded.self.mono_deg h1
  have hQ : DegreeBounded size (fun seed => csG * (seed.length + 1) ^ dGen) d :=
    DegreeBounded.mono_deg ⟨csG, fun _ => le_rfl⟩ hdGen
  have hround : DegreeBounded size
      (fun seed => ctG * (seed.length + 1) ^ dGen + seed.length + 1) (max dGen 1) :=
    ((DegreeBounded.mono_deg ⟨ctG, fun _ => le_rfl⟩ (le_max_left dGen 1)).add
      (DegreeBounded.self.mono_deg (le_max_right dGen 1))).add_const 1
  have hsum : DegreeBounded size
      (fun seed => ∑ i ∈ Finset.range (count seed.length),
        (tGen (seedAt generator seed i) + seed.length + 1)) d := by
    refine ((hlC_e.mul hround).mono_deg heGen).mono (fun seed => ?_)
    calc ∑ i ∈ Finset.range (count seed.length),
          (tGen (seedAt generator seed i) + seed.length + 1)
      _ ≤ ∑ _i ∈ Finset.range (count seed.length),
          (ctG * (seed.length + 1) ^ dGen + seed.length + 1) := by
        apply Finset.sum_le_sum
        intro i _
        have ht := hctG (seedAt generator seed i)
        simp only [encBits_apply, length_seedAt_of_forall hlen] at ht
        omega
      _ = count seed.length * (ctG * (seed.length + 1) ^ dGen + seed.length + 1) := by
        simp [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hout : DegreeBounded size (fun seed => (encBits (stretch generator count seed)).length)
      (max 1 eCount) := by
    refine ((DegreeBounded.self.mono_deg (le_max_left 1 eCount)).add
      (hlC_e.mono_deg (le_max_right 1 eCount))).mono (fun seed => ?_)
    simp [stretch, length_iterate hlen, size]
  exact ⟨⟨_, _, (((htC.add hseed).add hlC).add hsum).add_const 1 |>.smul c,
    (((hsC.add hQ).add hseed).add hlC).add_const 1 |>.smul c, hstretch⟩, hout⟩

/-- Recover `ComputableInPolyTime (stretch generator count)` directly as a corollary of the
quantitative streaming theorem `computableInTimeAndSpace_stretch` (via
`computableInDegree_stretch`). -/
theorem polyTime_stretch_of_length_eq {generator : List Bool → List Bool} {count : ℕ → ℕ}
    (hlen : ∀ s, (generator s).length = s.length + 1)
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    ComputableInPolyTime (stretch generator count) encBits encBits := by
  have hgenerator := hgenerator.tidy
  have hcount := hcount.tidy
  obtain ⟨clG, dlG, hclG⟩ := (ComputableInPolyTime.of_tidy hgenerator).polyBounded_length.exists_le
  obtain ⟨tG, sG, htG, hsG, hgen_ts⟩ := hgenerator
  obtain ⟨ctG, dtG, hctG⟩ := htG.exists_le
  obtain ⟨csG, dsG, hcsG⟩ := hsG.exists_le
  obtain ⟨clC, dlC, hclC⟩ := (ComputableInPolyTime.of_tidy hcount).polyBounded_length.exists_le
  obtain ⟨tC, sC, htC, hsC, hcount_ts⟩ := hcount
  obtain ⟨ctC, dtC, hctC⟩ := htC.exists_le
  obtain ⟨csC, dsC, hcsC⟩ := hsC.exists_le
  have hgen_deg : ComputableInDegree generator encBits encBits (max dtG dsG) dlG :=
    ⟨⟨tG, sG, DegreeBounded.mono_deg ⟨ctG, hctG⟩ (le_max_left _ _),
      DegreeBounded.mono_deg ⟨csG, hcsG⟩ (le_max_right _ _),
      hgen_ts.computableInTimeAndSpace⟩, ⟨clG, hclG⟩⟩
  have hcount_deg : ComputableInDegree count encUnary encUnary (max dtC dsC) dlC :=
    ⟨⟨tC, sC, DegreeBounded.mono_deg ⟨ctC, hctC⟩ (le_max_left _ _),
      DegreeBounded.mono_deg ⟨csC, hcsC⟩ (le_max_right _ _),
      hcount_ts.computableInTimeAndSpace⟩, ⟨clC, hclC⟩⟩
  exact (computableInDegree_stretch hlen hgen_deg hcount_deg).computableInPolyTime

/-- **Quantitative streaming certificate for `forwardIterate` with a captured parameter.** On input
`((a, seed), count)` encoded with `encPair (encPair encParam encBits) encUnary`, the streaming state
holds `(a, seed_i)` on `encPair encParam encBits`, so the captured parameter length
`(encParam a).length` is charged alongside `seed.length` in each round's copying cost and in the
workspace bound, which stays independent of `count`. -/
theorem computableInTimeAndSpace_forwardIterate_captured {α : Type}
    {encParam : α ↪ List Bool} {generator : α → List Bool → List Bool}
    {tGen sGen : α × List Bool → ℕ}
    (hlen : ∀ a s, (generator a s).length = s.length + 1)
    (hgen : ComputableInTimeAndSpace (fun p : α × List Bool => generator p.1 p.2)
      (encPair encParam encBits) encBits tGen sGen)
    {Q : (α × List Bool) × ℕ → ℕ}
    (hspace : ∀ x i, i < x.2 → sGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) ≤ Q x) :
    ∃ c, ComputableInTimeAndSpace
      (fun x : (α × List Bool) × ℕ => forwardIterate (generator x.1.1) x.2 x.1.2)
      (encPair (encPair encParam encBits) encUnary) encBits
      (fun x => c * ((encParam x.1.1).length + x.1.2.length + x.2 +
        (∑ i ∈ Finset.range x.2,
          (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
            (encParam x.1.1).length + x.1.2.length + 1)) + 1))
      (fun x => c * (Q x + (encParam x.1.1).length + x.1.2.length + 1)) := by
  -- Retain the captured streaming construction as a proof-local raw witness.
  have build {α : Type}
      {encParam : α ↪ List Bool} {generator : α → List Bool → List Bool}
      {tGen sGen : α × List Bool → ℕ}
      (hlen : ∀ a s, (generator a s).length = s.length + 1)
      (hgen : ComputableTidilyInTimeAndSpace (fun p : α × List Bool => generator p.1 p.2)
        (encPair encParam encBits) encBits tGen sGen)
      {Q : (α × List Bool) × ℕ → ℕ}
      (hspace : ∀ x i, i < x.2 → sGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) ≤ Q x) :
      ∃ c, ComputableTidilyInTimeAndSpace
        (fun x : (α × List Bool) × ℕ => forwardIterate (generator x.1.1) x.2 x.1.2)
        (encPair (encPair encParam encBits) encUnary) encBits
        (fun x => c * ((encParam x.1.1).length + x.1.2.length + x.2 +
          (∑ i ∈ Finset.range x.2,
            (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
              (encParam x.1.1).length + x.1.2.length + 1)) + 1))
        (fun x => c * (Q x + (encParam x.1.1).length + x.1.2.length + 1)) := by
    let encS := encPair encParam encBits
    obtain ⟨cpar, hpar⟩ := Internal.NormalForm.linear
      (PairEncoding.fst (enc₁ := encParam) (enc₂ := encBits) (enc := encS))
    obtain ⟨csnd, hsnd⟩ := Internal.NormalForm.linear
      (PairEncoding.snd (enc₁ := encParam) (enc₂ := encBits) (enc := encS))
    obtain ⟨c₁, hdrop⟩ := ComputableTidilyInTimeAndSpace.dropLast_bits.comp hgen
    obtain ⟨cpair, hnext₀⟩ := Internal.NormalForm.bigO
      (PairEncoding.pair_mono (enc := encS)
        (ComputableTidilyInTimeAndSpace.computableInTimeAndSpace hpar)
        hdrop.computableInTimeAndSpace)
    obtain ⟨c₂, hemit₀⟩ := ComputableTidilyInTimeAndSpace.getLast?_toList_bits.comp hgen
    obtain ⟨c₃, hfin₀⟩ := ComputableTidilyInTimeAndSpace.reverse_bits.comp hsnd
    obtain ⟨K, hK⟩ : ∃ K, K = cpair * (cpar + c₁ + 30) + c₂ + c₃ + csnd + 30 := ⟨_, rfl⟩
    have hseed (q : α × List Bool) : q.2.length + 1 ≤ (encS q).length + 1 := by
      simp only [encS, length_encPair, encBits_apply]
      omega
    have hnext : ComputableTidilyInTimeAndSpace
        (fun q : α × List Bool => (q.1, seedStep (generator q.1) q.2)) encS encS
        (fun q => cpair * tGen q + K * ((encS q).length + 1))
        (fun q => cpair * sGen q + K * ((encS q).length + 1)) := by
      refine ComputableTidilyInTimeAndSpace.mono hnext₀ (fun q => ?_) (fun q => ?_) <;>
      · have hd : (encS (q.1, (generator q.1 q.2).dropLast)).length = (encS q).length := by
          simp only [encS, length_encPair, encBits_apply, List.length_dropLast, hlen,
            Nat.add_sub_cancel]
        have hs := hseed q
        have hKE := Nat.mul_le_mul_right ((encS q).length + 1)
          (show cpair * (cpar + c₁ + 30) ≤ K by omega)
        have hc := Nat.mul_le_mul_left cpair (show 8 * q.2.length + 26 + c₁ + (encS q).length ≤
          (c₁ + 30) * ((encS q).length + 1) by nlinarith)
        simp only [Function.comp_apply, encBits_apply, hlen, hd]
        nlinarith
    have hemit : ComputableTidilyInTimeAndSpace
        (fun q : α × List Bool => emitBit (generator q.1) q.2) encS encBits
        (fun q => tGen q + K * ((encS q).length + 1))
        (fun q => sGen q + K * ((encS q).length + 1)) := by
      refine hemit₀.mono (fun q => ?_) (fun q => ?_) <;>
      · have hs := hseed q
        have hKE := Nat.mul_le_mul_right ((encS q).length + 1) (show c₂ + 30 ≤ K by omega)
        simp only [encBits_apply, hlen]
        nlinarith
    have hfin : ComputableTidilyInTimeAndSpace (fun q : α × List Bool => q.2.reverse) encS encBits
        (fun q => K * ((encS q).length + 1)) (fun q => K * ((encS q).length + 1)) := by
      refine hfin₀.mono (fun q => ?_) (fun q => ?_) <;>
      · have hs := hseed q
        have hKE := Nat.mul_le_mul_right ((encS q).length + 1) (show csnd + c₃ + 30 ≤ K by omega)
        simp only [encBits_apply]
        nlinarith
    have hS (x : (α × List Bool) × ℕ) (i : ℕ) :
        (encS (x.1.1, seedAt (generator x.1.1) x.1.2 i)).length =
          2 * (encParam x.1.1).length + x.1.2.length + 1 := by
      simp only [encS, length_encPair, encBits_apply, length_seedAt_of_forall (hlen x.1.1)]
      omega
    obtain ⟨c, h⟩ := hnext.iterate_unary_stream_sum hemit hfin
      (R := fun x i => (cpair + 4 * K + 6) * (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
        (encParam x.1.1).length + x.1.2.length + 1))
      (Q := fun x => (cpair + 1) * Q x + 4 * K * ((encParam x.1.1).length + x.1.2.length + 1))
      (B := fun x => 2 * (encParam x.1.1).length + x.1.2.length + 1)
      (fun x i _ => by
        simp only [iterate_seedStep_captured, hS]
        nlinarith)
      (fun x i hi => by
        have := hspace x i hi
        simp only [iterate_seedStep_captured, hS]
        nlinarith)
      (fun x i _ => by simp only [iterate_seedStep_captured, hS]; rfl)
    simp only [iterate_seedStep_captured, hS] at h
    refine ⟨c * (cpair + 6 * K + 10), ?_⟩
    simp only [forwardIterate_eq]
    refine h.mono (fun x => ?_) (fun x => ?_) <;>
      simp only [← Finset.mul_sum, Nat.mul_assoc] <;> refine Nat.mul_le_mul_left c ?_
    · generalize ∑ i ∈ Finset.range x.2, (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
        (encParam x.1.1).length + x.1.2.length + 1) = S
      nlinarith [Nat.zero_le (K * (encParam x.1.1).length), Nat.zero_le (K * x.1.2.length),
        Nat.zero_le (K * x.2), Nat.zero_le (cpair * x.2)]
    · nlinarith [Nat.zero_le (K * Q x), Nat.zero_le (cpair * Q x)]
  have hcharged := hgen.mono (fun _ => le_rfl)
    (fun q => Nat.le_add_right (sGen q) ((encParam q.1).length + q.2.length + 1))
  obtain ⟨a, hclean, _⟩ := hcharged.computableTidilyInO (fun q => by
    simp only [encBits_apply, hlen]
    omega)
  obtain ⟨c, h⟩ := build hlen hclean
    (Q := fun x => a * (Q x + (encParam x.1.1).length + x.1.2.length + 2))
    (fun x i hi => by
      have hs := hspace x i hi
      simp only [length_seedAt_of_forall (hlen x.1.1)]
      exact Nat.mul_le_mul_left a (by omega))
  refine ⟨c * (2 * a + 3), h.computableInTimeAndSpace.mono ?_ ?_⟩
  · intro x
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    have hsum := Finset.sum_le_sum (s := Finset.range x.2)
      (fun i _ => show
        a * (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) + 1) +
          (encParam x.1.1).length + x.1.2.length + 1 ≤
        (a + 1) * (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
          (encParam x.1.1).length + x.1.2.length + 1) by nlinarith)
    rw [← Finset.mul_sum] at hsum
    calc
      _ ≤ (encParam x.1.1).length + x.1.2.length + x.2 + (a + 1) *
          (∑ i ∈ Finset.range x.2, (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
            (encParam x.1.1).length + x.1.2.length + 1)) + 1 := by omega
      _ ≤ (a + 1) * ((encParam x.1.1).length + x.1.2.length + x.2 +
          (∑ i ∈ Finset.range x.2, (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
            (encParam x.1.1).length + x.1.2.length + 1)) + 1) := by
        nlinarith [Nat.zero_le (a * ((encParam x.1.1).length + x.1.2.length + x.2 + 1))]
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · intro x
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith [Nat.zero_le (a * (Q x + (encParam x.1.1).length + x.1.2.length))]

/-- **Quantitative cumulative-time and workspace certificate for `PRGStretch.iterate` with a
captured parameter.** On input `((a, seed), count)` encoded with
`encPair (encPair encParam encBits) encUnary`, the streaming state holds `(a, seed_i)` on
`encPair encParam encBits`, so the captured parameter length `(encParam a).length` is charged
alongside `seed.length` in each round's copying cost and in the workspace bound. -/
theorem computableInTimeAndSpace_iterate_captured {α : Type}
    {encParam : α ↪ List Bool} {generator : α → List Bool → List Bool}
    {tGen sGen : α × List Bool → ℕ}
    (hlen : ∀ a s, (generator a s).length = s.length + 1)
    (hgen : ComputableInTimeAndSpace (fun p : α × List Bool => generator p.1 p.2)
      (encPair encParam encBits) encBits tGen sGen)
    {Q : (α × List Bool) × ℕ → ℕ}
    (hspace : ∀ x i, i < x.2 → sGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) ≤ Q x) :
    ∃ c, ComputableInTimeAndSpace
      (fun x : (α × List Bool) × ℕ => iterate (generator x.1.1) x.1.2.length x.2 x.1.2)
      (encPair (encPair encParam encBits) encUnary) encBits
      (fun x => c * ((encParam x.1.1).length + x.1.2.length + x.2 +
        (∑ i ∈ Finset.range x.2,
          (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
            (encParam x.1.1).length + x.1.2.length + 1)) + 1))
      (fun x => c * (Q x + (encParam x.1.1).length + x.1.2.length + x.2 + 1)) := by
  obtain ⟨c, hfwd⟩ := computableInTimeAndSpace_forwardIterate_captured hlen hgen hspace
  have hcharged := hfwd.mono (fun _ => le_rfl)
    (fun x => show c * (Q x + (encParam x.1.1).length + x.1.2.length + 1) ≤
      (c + 1) * (Q x + (encParam x.1.1).length + x.1.2.length + x.2 + 1) by
        nlinarith [Nat.zero_le (c * x.2)])
  obtain ⟨a, hclean, _⟩ := hcharged.computableTidilyInO (fun x => by
    simp only [encBits_apply, length_forwardIterate_of_forall (hlen x.1.1)]
    nlinarith [Nat.zero_le (c * (Q x + (encParam x.1.1).length + x.1.2.length + x.2 + 1))])
  obtain ⟨b, h⟩ := iterate_of_forwardIterate
    (generator := fun x : (α × List Bool) × ℕ => generator x.1.1)
    (seed := (fun x => x.1.2)) (count := Prod.snd) (fun x => hlen x.1.1) hclean
  refine ⟨b * (a * (c + 2) + 1), h.computableInTimeAndSpace.mono ?_ ?_⟩
  · intro x
    let T := (encParam x.1.1).length + x.1.2.length + x.2 + (∑ i ∈ Finset.range x.2,
          (tGen (x.1.1, seedAt (generator x.1.1) x.1.2 i) +
            (encParam x.1.1).length + x.1.2.length + 1)) + 1
    have hbase : (encParam x.1.1).length + x.1.2.length + x.2 + 1 ≤ T := by dsimp only [T]; omega
    have hpos : 1 ≤ T := by omega
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left b
    change a * (c * T + 1) + x.1.2.length + x.2 + 1 ≤ (a * (c + 2) + 1) * T
    have hscaled := Nat.mul_le_mul_left a (show c * T + 1 ≤ (c + 1) * T by nlinarith)
    nlinarith [Nat.zero_le (a * T)]
  · intro x
    let S := Q x + (encParam x.1.1).length + x.1.2.length + x.2 + 1
    have hbase : (encParam x.1.1).length + x.1.2.length + x.2 + 1 ≤ S := by dsimp only [S]; omega
    have hpos : 1 ≤ S := by omega
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left b
    change a * ((c + 1) * S + 1) + x.1.2.length + x.2 + 1 ≤
      (a * (c + 2) + 1) * S
    have hscaled := Nat.mul_le_mul_left a (show (c + 1) * S + 1 ≤ (c + 2) * S by nlinarith)
    nlinarith

end Cslib.Crypto.PRGStretch
