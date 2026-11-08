/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Randomized.Counting
public import Complexity.Foundations.Data.BitString.Basic

/-!
# The classical query complexity of Bernstein–Vazirani

**The Bernstein–Vazirani problem** [Bernstein, Vazirani][BernsteinVazirani1997], as stated in
[de Wolf, §2.4.2][deWolf2019]: the input `x ∈ {0,1}^N`, with `N = 2^n` query positions identified
with the bit strings `a ∈ {0,1}^n`, is the truth table `x_a = s ⬝ᵥ a` of a linear function for an
unknown `s ∈ {0,1}^n`; the goal is to find `s`. The positions `Fin N` are identified with the bit
strings `K → Bool` by an equivalence `e`, and `Cslib.QueryComplexity.linearTable e s` is the input.

**Upper bound.** Querying the `n` unit vectors reads off `s` coordinate by coordinate:
`Cslib.QueryComplexity.linearDecode e` recovers `s` from `linearTable e s`
(`Cslib.QueryComplexity.linearDecode_linearTable`), and the decision tree
`Cslib.QueryComplexity.linearDecodeTree e` computes it with depth at most `n`.

**Lower bound.** The `2^n` inputs have distinct answers, and a decision tree of depth `q` takes at
most `2^q` values. So every deterministic decision tree recovering `s` has depth at least `n`
(`Cslib.QueryComplexity.card_le_depth_of_linearTable`), and every randomized decision tree that
recovers `s` with error at most `ε` on every input has depth `q` with `2^n (1 - ε) ≤ 2^q`
(`Cslib.QueryComplexity.linearTable_randomized_lower_bound`); for `ε < 1/2` this forces `q ≥ n`
(`Cslib.QueryComplexity.card_le_depth_of_linearTable_randomized`). The search problem is a promise
problem, so the lower bounds take any total `F` that answers `s` on the inputs `linearTable e s`.
Hence the deterministic complexity and every bounded-error randomized complexity of
`linearDecode e` are exactly `n` (`Cslib.QueryComplexity.complexity_linearDecode`,
`Cslib.QueryComplexity.randomizedComplexity_linearDecode`), against the single quantum query of
`Complexity/Computability/QueryComplexity/Quantum/BernsteinVazirani.lean`. de Wolf §2.4.2 notes
that classically `n` queries are needed; the counting argument and its randomized form are
formulated here.

## Main definitions

* `Cslib.QueryComplexity.linearTable`: the truth table of the linear function `a ↦ s ⬝ᵥ a`.
* `Cslib.QueryComplexity.linearDecode`: read off `s` at the unit vectors.
* `Cslib.QueryComplexity.linearDecodeTree`: the decision tree querying the unit vectors.

## Main results

* `Cslib.QueryComplexity.card_le_depth_of_linearTable`: a deterministic tree recovering `s` has
  depth at least `n`.
* `Cslib.QueryComplexity.linearTable_randomized_lower_bound`: `2^n (1 - ε) ≤ 2^q`.
* `Cslib.QueryComplexity.card_le_depth_of_linearTable_randomized`: depth at least `n` for error
  `ε < 1/2`.
* `Cslib.QueryComplexity.complexity_linearDecode`,
  `Cslib.QueryComplexity.randomizedComplexity_linearDecode`: `D = R_ε = n` for `0 ≤ ε < 1/2`.

## References

* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §2.4.2
-/

public section

namespace Cslib.QueryComplexity

open Finset BitString

variable {N : ℕ} {K : Type*} [Fintype K]

/-- The truth table of the linear function `a ↦ s ⬝ᵥ a`, with the query positions identified with
the bit strings by `e`. -/
@[expose] def linearTable (e : Fin N ≃ (K → Bool)) (s : K → Bool) : Fin N → Bool :=
  fun i => s ⬝ᵥ e i

section Decode

variable [DecidableEq K]

/-- Read off the hidden string at the unit vectors: coordinate `k` is the queried bit at the
position of the unit vector `e_k`. -/
@[expose] def linearDecode (e : Fin N ≃ (K → Bool)) (X : Fin N → Bool) : K → Bool :=
  fun k => X (e.symm (Pi.single k true))

/-- Decoding the truth table of `a ↦ s ⬝ᵥ a` recovers `s`. -/
@[simp] theorem linearDecode_linearTable (e : Fin N ≃ (K → Bool)) (s : K → Bool) :
    linearDecode e (linearTable e s) = s := by
  funext k
  simp only [linearDecode, linearTable, Equiv.apply_symm_apply, dotProduct_single]
  cases s k <;> rfl

end Decode

/-- The truth table determines the hidden string. -/
theorem linearTable_injective (e : Fin N ≃ (K → Bool)) : Function.Injective (linearTable e) := by
  classical
  exact Function.LeftInverse.injective (linearDecode_linearTable e)

section Decode

variable [DecidableEq K]

/-- The decision tree that queries the `n` unit vectors and outputs the decoded string. -/
noncomputable def linearDecodeTree (e : Fin N ≃ (K → Bool)) : DecisionTree (Fin N) (K → Bool) :=
  DecisionTree.queryAll (linearDecode e)
    ((univ : Finset K).toList.map fun k => e.symm (Pi.single k true)) fun _ => false

/-- The unit-vector tree computes `linearDecode e` on every input. -/
theorem linearDecodeTree_computes (e : Fin N ≃ (K → Bool)) :
    (linearDecodeTree e).Computes (linearDecode e) := by
  intro X
  rw [linearDecodeTree, DecisionTree.eval_queryAll]
  funext k
  simp [linearDecode]

/-- The unit-vector tree has depth at most `n`. -/
theorem depth_linearDecodeTree_le (e : Fin N ≃ (K → Bool)) :
    (linearDecodeTree e).depth ≤ Fintype.card K := by
  refine (DecisionTree.depth_queryAll_le _ _ _).trans ?_
  simp

/-- The truth tables of the linear functions: `2^n` inputs with distinct answers. -/
private theorem card_image_linearTable (e : Fin N ≃ (K → Bool)) :
    ((univ : Finset (K → Bool)).image (linearTable e)).card = 2 ^ Fintype.card K := by
  rw [card_image_of_injective _ (linearTable_injective e), card_univ, Fintype.card_fun,
    Fintype.card_bool]

/-- `F` answers `s` on the image of `linearTable e`, so it is injective there. -/
private theorem injOn_of_linearTable {e : Fin N ≃ (K → Bool)} {F : (Fin N → Bool) → K → Bool}
    (hF : ∀ s, F (linearTable e s) = s) :
    Set.InjOn F ((univ : Finset (K → Bool)).image (linearTable e) : Set (Fin N → Bool)) := by
  intro X hX Y hY hXY
  obtain ⟨s, -, rfl⟩ := mem_image.mp hX
  obtain ⟨u, -, rfl⟩ := mem_image.mp hY
  rw [hF, hF] at hXY
  rw [hXY]

end Decode

/-- **The deterministic lower bound for Bernstein–Vazirani**: a decision tree that recovers `s`
from the truth table of `a ↦ s ⬝ᵥ a` for every `s` has depth at least `n`. -/
theorem card_le_depth_of_linearTable (e : Fin N ≃ (K → Bool)) (t : DecisionTree (Fin N) (K → Bool))
    (ht : ∀ s, t.eval (linearTable e s) = s) : Fintype.card K ≤ t.depth := by
  classical
  have h := DecisionTree.card_le_two_pow_depth_of_injOn t (F := fun X => linearDecode e X)
    (S := (univ : Finset (K → Bool)).image (linearTable e))
    (injOn_of_linearTable fun s => linearDecode_linearTable e s)
    (fun X hX => by
      obtain ⟨s, -, rfl⟩ := mem_image.mp hX
      rw [ht, linearDecode_linearTable])
  rw [card_image_linearTable] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

/-- **The randomized lower bound for Bernstein–Vazirani**: a randomized decision tree that
recovers `s` from the truth table of `a ↦ s ⬝ᵥ a` with error at most `ε` for every `s` (as the
restriction of a total function `F`) has depth `q` with `2^n (1 - ε) ≤ 2^q`. -/
theorem linearTable_randomized_lower_bound (e : Fin N ≃ (K → Bool))
    (μ : RandomizedDecisionTree (Fin N) (K → Bool)) {F : (Fin N → Bool) → K → Bool}
    (hF : ∀ s, F (linearTable e s) = s) {ε : ℝ} (hμ : ∀ s, μ.errorProb F (linearTable e s) ≤ ε) :
    (2 : ℝ) ^ Fintype.card K * (1 - ε) ≤ 2 ^ μ.depth := by
  classical
  have h := μ.card_mul_one_sub_le_two_pow_depth (injOn_of_linearTable hF) (ε := ε)
    (fun X hX => by
      obtain ⟨s, -, rfl⟩ := mem_image.mp hX
      exact hμ s)
  rw [card_image_linearTable] at h
  exact_mod_cast h

/-- **Bounded-error randomized decision trees need `n` queries for Bernstein–Vazirani**: for error
`ε < 1/2`, a randomized decision tree that recovers `s` from the truth table of `a ↦ s ⬝ᵥ a` has
depth at least `n`. -/
theorem card_le_depth_of_linearTable_randomized (e : Fin N ≃ (K → Bool))
    (μ : RandomizedDecisionTree (Fin N) (K → Bool)) {F : (Fin N → Bool) → K → Bool}
    (hF : ∀ s, F (linearTable e s) = s) {ε : ℝ} (hε : ε < 1 / 2)
    (hμ : ∀ s, μ.errorProb F (linearTable e s) ≤ ε) : Fintype.card K ≤ μ.depth := by
  by_contra hlt
  push Not at hlt
  have h := linearTable_randomized_lower_bound e μ hF hμ
  have hpow : (2 : ℝ) ^ μ.depth * 2 ≤ 2 ^ Fintype.card K := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) hlt
  have hpos : (0 : ℝ) < 2 ^ μ.depth := by positivity
  nlinarith

section Decode

variable [DecidableEq K]

/-- **The deterministic query complexity of Bernstein–Vazirani is `n`.** -/
theorem complexity_linearDecode (e : Fin N ≃ (K → Bool)) :
    DecisionTree.complexity (linearDecode e) = Fintype.card K := by
  refine le_antisymm ((DecisionTree.complexity_le_depth (linearDecodeTree_computes e)).trans
    (depth_linearDecodeTree_le e)) ?_
  obtain ⟨t, ht, hd⟩ := DecisionTree.exists_computes_depth_eq_complexity (linearDecode e)
  rw [← hd]
  exact card_le_depth_of_linearTable e t fun s => by rw [ht, linearDecode_linearTable]

/-- **The bounded-error randomized query complexity of Bernstein–Vazirani is `n`**, for every error
`0 ≤ ε < 1/2`. -/
theorem randomizedComplexity_linearDecode (e : Fin N ≃ (K → Bool)) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε < 1 / 2) : randomizedComplexity ε (linearDecode e) = Fintype.card K := by
  refine le_antisymm ((DecisionTree.randomizedComplexity_le_complexity hε₀ _).trans
    (complexity_linearDecode e).le) ?_
  obtain ⟨μ, hμ, hd⟩ := exists_computes_depth_eq_randomizedComplexity hε₀ (linearDecode e)
  rw [← hd]
  exact card_le_depth_of_linearTable_randomized e μ (linearDecode_linearTable e) hε
    fun s => hμ _

end Decode

end Cslib.QueryComplexity
