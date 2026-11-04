/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.ZeroKnowledge.AuxClock
public import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
# Zero-knowledge proof systems with parameterized and negligible soundness

`Cslib.Crypto.ZeroKnowledgeProof` bundles a computational zero-knowledge proof system with a fixed
constant soundness bound `1 / 3`. Sequential repetition amplifies soundness from `1 / 3` to
`(1 / 3) ^ (k n)`, a function of the security parameter `n`.

This module defines `Cslib.Crypto.ZKProof enc A soundness`, parameterized by a soundness bound
`soundness : ℕ → ENNReal`:

* `ZeroKnowledgeProof.toZKProof` embeds any constant-soundness `ZeroKnowledgeProof enc A` as a
  `ZKProof enc A (fun _ => 1 / 3)`.
* `ZKProof.NegligibleSoundness` asserts that `soundness n ≠ ⊤` for all `n` and
  `fun n => (soundness n).toNNReal` is `Negligible`. Requiring finiteness rules out the degenerate
  `soundness n = ⊤` case where `ENNReal.toNNReal ⊤ = 0`, and implies that against every family of
  cheating provers on false instances, the real-valued acceptance probability is negligible
  (`ZKProof.NegligibleSoundness.acceptProb_toNNReal_negligible`) and that `A ∈ IP enc`
  (`ZKProof.NegligibleSoundness.mem_IP`).
* `Cslib.Crypto.negligible_pow_of_lt_one` and `Cslib.Crypto.negligible_one_third_pow` establish
  that `(1 / 3) ^ (k n)` is negligible whenever `∀ n, n ≤ k n`.
* `ZKProof` carries the same zero-knowledge predicates and clock/indexing bridges as
  `ZeroKnowledgeProof` (`GenerableZeroKnowledge`, `AuxiliaryInputZeroKnowledge`,
  `UnboundedAuxiliaryInputZeroKnowledge`, and `InstanceAuxiliaryInputZeroKnowledge`).

## Main definitions

* `Cslib.Crypto.ZKProof`: computational zero-knowledge interactive proof system with soundness
  function `soundness : ℕ → ENNReal`.
* `Cslib.Crypto.ZeroKnowledgeProof.toZKProof`: coercion from constant `1 / 3` soundness.
* `Cslib.Crypto.ZKProof.NegligibleSoundness`: finiteness and negligible decay of `soundness`.

## Main results

* `Cslib.Crypto.ZKProof.NegligibleSoundness.acceptProb_toNNReal_negligible`: negligible acceptance
  probability on false-instance and cheating-prover families.
* `Cslib.Crypto.ZKProof.NegligibleSoundness.mem_IP`: any `ZKProof` with negligible soundness places
  `A ∈ IP enc`.
* `Cslib.Crypto.negligible_pow_of_lt_one`, `Cslib.Crypto.negligible_one_third_pow`,
  `Cslib.Crypto.ZKProof.negligibleSoundness_one_third_pow`: geometric soundness decay under
  repetition count `n ≤ k n`.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal
open Cslib.Probability Cslib.Complexity Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- A computational zero-knowledge interactive proof system for `A : Set α` (with instance encoding
`enc : α ↪ List Bool`) and security-parameter-indexed soundness bound `soundness : ℕ → ENNReal`.

This generalizes `ZeroKnowledgeProof enc A` (which fixes `soundness := fun _ => 1 / 3`) so that
soundness-amplified protocols with negligible soundness error `(1 / 3) ^ (k n)` can be represented
directly. -/
structure ZKProof (enc : α ↪ List Bool) (A : Set α) (soundness : ℕ → ENNReal) where
  /-- The honest verifier, indexed by security parameter `n` and instance `a`. -/
  verifier : ℕ → α → WordOracleComp Unit Bool
  /-- The honest prover strategy, taking security parameter `n`, instance `a`, and witness `w`. -/
  prover : ℕ → α → List Bool → Prover Unit
  /-- The polynomial-time witness check used by the honest prover. -/
  isWitness : α → List Bool → Bool
  /-- `isWitness` is computable in plain polynomial time. -/
  polyTime_isWitness :
    ComputableInPolyTime (fun p : α × List Bool => isWitness p.1 p.2)
      (encPair enc encBits) encBool
  /-- `a ∈ A` if and only if some witness `w` satisfies `isWitness a w = true`. -/
  mem_iff_exists_witness : ∀ a, a ∈ A ↔ ∃ w, isWitness a w = true
  /-- The honest verifier is uniform strict oracle PPT in `(1^n, a)`. -/
  isOraclePPT_verifier :
    IsOraclePPTOn (encPair encUnary enc) encBool (fun p : ℕ × α => verifier p.1 p.2)
  /-- The PPT program realizing the honest prover's interaction with a verifier program. -/
  interact : ℕ → α → List Bool → WordOracleComp Unit (List Bool) → ProbComp (List Bool)
  /-- `interact` has the exact output distribution of `prover.run`. -/
  eval_interact : ∀ n a w prog,
    ProbComp.eval (interact n a w prog) =
      ((prover n a w).run prog (prover n a w).init).map Prod.fst
  /-- Running any uniform strict oracle PPT verifier against the honest prover is uniform strict
  PPT in `(1^n, a, w, z)`. -/
  isPPT_interact :
    ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
      IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun ⟨n, a, z⟩ => Vstar n a z) →
      IsPPTOn (encPair encUnary (encPair enc (encPair encBits encBits))) encBits
        (fun ⟨n, a, w, z⟩ =>
          interact n a w (Vstar n a z))
  /-- Perfect completeness: for every valid witness `w` of `a`, the honest prover convinces the
  honest verifier with probability `1`. -/
  complete : ∀ n a w, isWitness a w = true → acceptProb (verifier n a) (prover n a w) = 1
  /-- Soundness: for every `a ∉ A` and every computationally unbounded stateful prover `P`, the
  verifier accepts with probability at most `soundness n`. -/
  sound : ∀ n, ∀ a ∉ A, ∀ P : Prover Unit, acceptProb (verifier n a) P ≤ soundness n
  /-- Uniform computational zero-knowledge with poly-time-generable auxiliary input against all
  uniform strict oracle PPT malicious verifiers. -/
  zero_knowledge : GenerableZeroKnowledge enc prover isWitness

/-- Embed a constant-soundness `ZeroKnowledgeProof enc A` as a `ZKProof enc A (fun _ => 1 / 3)`. -/
def ZeroKnowledgeProof.toZKProof (zk : ZeroKnowledgeProof enc A) :
    ZKProof enc A (fun _ => 1 / 3) where
  verifier := zk.verifier
  prover := zk.prover
  isWitness := zk.isWitness
  polyTime_isWitness := zk.polyTime_isWitness
  mem_iff_exists_witness := zk.mem_iff_exists_witness
  isOraclePPT_verifier := zk.isOraclePPT_verifier
  interact := zk.interact
  eval_interact := zk.eval_interact
  isPPT_interact := zk.isPPT_interact
  complete := zk.complete
  sound := zk.sound
  zero_knowledge := zk.zero_knowledge

namespace ZKProof

variable {soundness soundness' : ℕ → ENNReal}

/-- Weaken the soundness bound of a `ZKProof` along a pointwise inequality. -/
def mono (zk : ZKProof enc A soundness) (hle : ∀ n, soundness n ≤ soundness' n) :
    ZKProof enc A soundness' :=
  { zk with sound := fun n a ha P => (zk.sound n a ha P).trans (hle n) }

/-- Named projection for the restricted polynomial-time-generable zero-knowledge property bundled by
`ZKProof`. -/
theorem generableZeroKnowledge (zk : ZKProof enc A soundness) :
    GenerableZeroKnowledge enc zk.prover zk.isWitness :=
  zk.zero_knowledge

/-- General auxiliary-input computational zero-knowledge for a bundled `ZKProof` system, ranging
over arbitrary polynomially bounded instance, valid-witness, and auxiliary-input families. -/
def AuxiliaryInputZeroKnowledge (zk : ZKProof enc A soundness) : Prop :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge enc zk.prover zk.isWitness

/-- General auxiliary-input zero-knowledge for `zk` implies the bundled restricted
`GenerableZeroKnowledge` guarantee. -/
theorem AuxiliaryInputZeroKnowledge.generableZeroKnowledge {zk : ZKProof enc A soundness}
    (h : zk.AuxiliaryInputZeroKnowledge) :
    GenerableZeroKnowledge enc zk.prover zk.isWitness :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge.generableZeroKnowledge h

/-- Unbounded-`z` family auxiliary-input zero knowledge for a bundled `ZKProof`. -/
def UnboundedAuxiliaryInputZeroKnowledge (zk : ZKProof enc A soundness) : Prop :=
  Cslib.Crypto.UnboundedAuxiliaryInputZeroKnowledge enc zk.prover zk.isWitness

/-- Goldreich-style `x`-indexed auxiliary-input zero knowledge with unbounded `z` for a bundled
`ZKProof`. -/
def InstanceAuxiliaryInputZeroKnowledge (zk : ZKProof enc A soundness) : Prop :=
  Cslib.Crypto.InstanceAuxiliaryInputZeroKnowledge enc zk.prover zk.isWitness

/-- `zk.AuxiliaryInputZeroKnowledge` implies `zk.UnboundedAuxiliaryInputZeroKnowledge`. -/
theorem AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge
    {zk : ZKProof enc A soundness} (h : zk.AuxiliaryInputZeroKnowledge) :
    zk.UnboundedAuxiliaryInputZeroKnowledge :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge h

/-- `zk.UnboundedAuxiliaryInputZeroKnowledge` implies `zk.InstanceAuxiliaryInputZeroKnowledge`. -/
theorem UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge
    {zk : ZKProof enc A soundness} (h : zk.UnboundedAuxiliaryInputZeroKnowledge) :
    zk.InstanceAuxiliaryInputZeroKnowledge :=
  Cslib.Crypto.UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge h

/-- `zk.AuxiliaryInputZeroKnowledge` implies `zk.InstanceAuxiliaryInputZeroKnowledge`. -/
theorem AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge
    {zk : ZKProof enc A soundness} (h : zk.AuxiliaryInputZeroKnowledge) :
    zk.InstanceAuxiliaryInputZeroKnowledge :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge h

/-- At any security parameter `n`, the honest verifier of a `ZKProof` is an interactive proof for
`A` with completeness `2 / 3` and soundness `soundness n`. -/
theorem isInteractiveProof (zk : ZKProof enc A soundness) (n : ℕ) :
    IsInteractiveProof (zk.verifier n) A (2 / 3) (soundness n) where
  complete a ha := by
    obtain ⟨w, hw⟩ := (zk.mem_iff_exists_witness a).mp ha
    refine ⟨zk.prover n a w, ?_⟩
    rw [zk.complete n a w hw]
    exact ENNReal.div_le_of_le_mul (by norm_num)
  sound a ha P := zk.sound n a ha P

/-- Any `ZKProof` whose soundness bound is at most `1 / 3` at some security parameter `n` places
`A ∈ IP enc`. -/
theorem mem_IP (zk : ZKProof enc A soundness) (h : ∃ n, soundness n ≤ 1 / 3) :
    A ∈ IP enc := by
  obtain ⟨n, hn⟩ := h
  refine ⟨zk.verifier n, ?_, ⟨fun a ha => (zk.isInteractiveProof n).complete a ha,
    fun a ha P => (zk.sound n a ha P).trans hn⟩⟩
  have hV := zk.isOraclePPT_verifier
  fun_prop

/-- **Negligible soundness** for a `ZKProof`: the soundness bound is finite at every security
parameter (`∀ n, soundness n ≠ ⊤`, ruling out the degenerate `ENNReal.toNNReal ⊤ = 0` case) and
its nonnegative real value `fun n => (soundness n).toNNReal` is `Negligible`. -/
def NegligibleSoundness (_zk : ZKProof enc A soundness) : Prop :=
  (∀ n, soundness n ≠ ⊤) ∧ Negligible (fun n => (soundness n).toNNReal)

theorem NegligibleSoundness.soundness_ne_top {zk : ZKProof enc A soundness}
    (h : zk.NegligibleSoundness) (n : ℕ) : soundness n ≠ ⊤ :=
  h.1 n

theorem NegligibleSoundness.negligible_toNNReal {zk : ZKProof enc A soundness}
    (h : zk.NegligibleSoundness) : Negligible (fun n => (soundness n).toNNReal) :=
  h.2

/-- Under `NegligibleSoundness`, any family of false instances `a : ℕ → α` (`∀ n, a n ∉ A`) and
any family of computationally unbounded stateful provers `P : ℕ → Prover Unit` have negligible
acceptance probability. -/
theorem NegligibleSoundness.acceptProb_toNNReal_negligible {zk : ZKProof enc A soundness}
    (h : zk.NegligibleSoundness) {a : ℕ → α} (ha : ∀ n, a n ∉ A) (P : ℕ → Prover Unit) :
    Negligible (fun n => (acceptProb (zk.verifier n (a n)) (P n)).toNNReal) :=
  negligible_of_le h.2 fun n =>
    ENNReal.toNNReal_mono (h.1 n) (zk.sound n (a n) (ha n) (P n))

/-- A pointwise smaller soundness bound preserves `NegligibleSoundness`. -/
theorem NegligibleSoundness.of_le {zk : ZKProof enc A soundness}
    {zk' : ZKProof enc A soundness'} (h : zk.NegligibleSoundness)
    (hle : ∀ n, soundness' n ≤ soundness n) : zk'.NegligibleSoundness :=
  ⟨fun n => ne_top_of_le_ne_top (h.1 n) (hle n),
    negligible_of_le h.2 fun n => ENNReal.toNNReal_mono (h.1 n) (hle n)⟩

/-- Any `ZKProof` with negligible soundness places `A ∈ IP enc`. -/
theorem NegligibleSoundness.mem_IP {zk : ZKProof enc A soundness}
    (h : zk.NegligibleSoundness) : A ∈ IP enc := by
  have hev := h.2.eventually_le_inv_polynomial
    (p := fun _ => 3) (PolynomiallyBounded.const 3) (fun _ => by decide)
  obtain ⟨n, hn⟩ := hev.exists
  refine zk.mem_IP ⟨n, ?_⟩
  rw [← ENNReal.coe_toNNReal (h.1 n)]
  have hle : ((soundness n).toNNReal : ℝ≥0) ≤ (1 / 3 : ℝ≥0) := by
    exact_mod_cast hn
  exact (ENNReal.coe_le_coe.mpr hle).trans (by norm_num)

end ZKProof

@[simp]
theorem ZeroKnowledgeProof.auxiliaryInputZeroKnowledge_toZKProof_iff
    (zk : ZeroKnowledgeProof enc A) :
    zk.toZKProof.AuxiliaryInputZeroKnowledge ↔ zk.AuxiliaryInputZeroKnowledge :=
  Iff.rfl

/-- Geometric decay `fun n => ratio ^ k n` is negligible for any ratio `ratio < 1` and repetition
count `k : ℕ → ℕ` satisfying `∀ n, n ≤ k n`. -/
theorem negligible_pow_of_lt_one {ratio : ℝ≥0} (hratio : ratio < 1) {k : ℕ → ℕ}
    (hk : ∀ n, n ≤ k n) :
    Negligible (fun n => ratio ^ k n) :=
  negligible_of_le (negligible_geometric hratio) fun n =>
    pow_le_pow_of_le_one ratio.coe_nonneg hratio.le (hk n)

/-- The amplified soundness bound `fun n => ((1 / 3 : ENNReal) ^ k n).toNNReal` is negligible
whenever `∀ n, n ≤ k n`. -/
theorem negligible_one_third_pow {k : ℕ → ℕ} (hk : ∀ n, n ≤ k n) :
    Negligible (fun n => ((1 / 3 : ENNReal) ^ k n).toNNReal) := by
  have hlt : ((1 / 3 : ENNReal).toNNReal) < 1 := by
    rw [ENNReal.toNNReal_div, ENNReal.toNNReal_one, ENNReal.toNNReal_ofNat]
    norm_num
  simpa only [ENNReal.toNNReal_pow] using negligible_pow_of_lt_one hlt hk

/-- A `ZKProof` with soundness `(1 / 3) ^ (k n)` for `∀ n, n ≤ k n` has negligible soundness. -/
theorem ZKProof.negligibleSoundness_one_third_pow {k : ℕ → ℕ}
    (zk : ZKProof enc A (fun n => (1 / 3 : ENNReal) ^ k n)) (hk : ∀ n, n ≤ k n) :
    zk.NegligibleSoundness :=
  ⟨fun n => ENNReal.pow_ne_top (by norm_num), negligible_one_third_pow hk⟩

end Cslib.Crypto
