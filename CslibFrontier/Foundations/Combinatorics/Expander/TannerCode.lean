/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Cayley
public import CslibFrontier.Foundations.Data.BitString.Weight
public import CslibFrontier.Foundations.Data.Code.Linear
import CslibFrontier.Foundations.Combinatorics.Expander.BipartiteTanner
import CslibFrontier.Foundations.Data.BitString.Parity.DotProduct

/-!
# Tanner codes on small-bias Cayley graphs

A *Tanner code* [Tanner, Section II][Tanner1981] places bits on the edges of a regular graph and
requires the bits around every vertex, ordered by port, to lie in a fixed *local code*. Here the
graph is the bipartite double cover of a Cayley graph of the cube `Fin ℓ → Bool` with generators
`s₁, …, s_d` (`Cslib.RotationMap.cubeCayley`): left vertex `u` is joined by its port-`j` edge to
right vertex `u + sⱼ`, and edge words are bit strings on `(Fin ℓ → Bool) × Fin d`. The local code
is the kernel of a matrix `A` with `c` rows (`Cslib.BitString.Tanner.IsWord`).

* **Local codes** (`Cslib.BitString.exists_forall_weight_le`): if fewer than `2 ^ c` nonzero strings
  of length `d` have weight at most `h`, some `c × d` matrix rejects all of them, so its kernel has
  minimum distance more than `h`. A union bound: a nonzero string lies in the kernel of exactly
  `2 ^ ((d - 1) c)` of the `2 ^ (d c)` matrices (`Cslib.BitString.card_kernel`), since its inner
  product with a uniform row is a balanced parity.
* **Distance** (`Cslib.BitString.Tanner.le_weight_of_isWord`): if the local code has distance more
  than `h` and the generators are `ε`-biased with `ε ≥ 0`, every nonzero Tanner word `x` has
  `(h + 1) (h + 1 - ε d) 2 ^ ℓ ≤ d · weight x`. The vertices `U`, `V` touched by `x` on the two
  sides each see at least `h + 1` of its bits, while all its bits are edges between `U` and `V`,
  which the mixing estimate (`Cslib.RotationMap.card_interedges_cubeCayley_le`) bounds.
* **Shortening** (`Cslib.BitString.Tanner.le_weight_of_shortRow`): keeping `m` of the edges, by an
  embedding `Fin m ↪ (Fin ℓ → Bool) × Fin d`, gives `2 · 2 ^ ℓ · c` explicit rows on `Fin m`
  (`Cslib.BitString.Tanner.shortRow`), each with at most `d` ones
  (`Cslib.BitString.Tanner.weight_shortRow_le`), whose nonzero kernel strings obey the same bound,
  again for `ε ≥ 0`.

These are the local-code, distance and shortening steps in the proof of
[OpenAI2026ETH, Lemma 6.1], which builds the initial parity tests from such a code.

## Main definitions

* `Cslib.BitString.Tanner.IsWord`: the Tanner code of a local check matrix.
* `Cslib.BitString.Tanner.shortRow`: the rows of the shortened code.

## Main results

* `Cslib.BitString.exists_forall_weight_le`: local codes of given distance by the union bound.
* `Cslib.BitString.Tanner.le_weight_of_isWord`: the distance of the Tanner code.
* `Cslib.BitString.Tanner.weight_shortRow_le`: the rows of the shortened code are sparse.
* `Cslib.BitString.Tanner.le_weight_of_shortRow`: the distance of the shortened code.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1
* [R. M. Tanner, *A recursive approach to low complexity codes*][Tanner1981]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Cslib.RotationMap Cslib.Probability.PMF

section LocalCode

variable {c d : ℕ}

/-- **Local codes by the union bound**: if fewer than `2 ^ c` nonzero strings have weight at most
`h`, some matrix with `c` rows rejects them all. -/
theorem exists_forall_weight_le {h : ℕ}
    (hlt : #{w : Fin d → Bool | w ≠ 0 ∧ weight w ≤ h} < 2 ^ c) :
    ∃ A : Fin c → Fin d → Bool, ∀ w, w ≠ 0 → weight w ≤ h → ∃ i, A i ⬝ᵥ w = true := by
  by_contra hne
  simp only [not_exists, not_forall, exists_prop, Bool.not_eq_true] at hne
  set W := ({w : Fin d → Bool | w ≠ 0 ∧ weight w ≤ h} : Finset _)
  have hcover : (univ : Finset (Fin c → Fin d → Bool)) ⊆
      W.biUnion fun w => {A : Fin c → Fin d → Bool | ∀ i, A i ⬝ᵥ w = false} := by
    intro A _
    obtain ⟨w, hw, hwh, hA⟩ := hne A
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, W]
    exact ⟨w, ⟨hw, hwh⟩, hA⟩
  have h1 := (card_le_card hcover).trans card_biUnion_le
  rw [Finset.sum_congr rfl fun w hw => card_kernel (c := c) (mem_filter.mp hw).2.1, sum_const,
    smul_eq_mul, card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_fin] at h1
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : W = ∅ := by
      ext w; simp only [W, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h' => h'.1 (funext fun i => i.elim0)
    obtain ⟨w, hw, -, -⟩ := hne (fun _ i => i.elim0)
    exact hw (funext fun i => i.elim0)
  have e : (2 ^ d) ^ c = 2 ^ c * (2 ^ (d - 1)) ^ c := by
    rw [← mul_pow, ← pow_succ', Nat.sub_add_cancel hd]
  rw [e] at h1
  have hpos : 0 < (2 ^ (d - 1)) ^ c := by positivity
  have := Nat.le_of_mul_le_mul_right h1 hpos
  omega

end LocalCode

namespace Tanner

variable {ℓ d c : ℕ}

/-- The edge word at the left vertex `u`: the bits of its `d` edges, by port. -/
def leftWord (x : (Fin ℓ → Bool) × Fin d → Bool) (u : Fin ℓ → Bool) : Fin d → Bool :=
  fun j => x (u, j)

/-- The edge word at the right vertex `v`: its port-`j` edge comes from `v + s j`. -/
def rightWord (s : Fin d → Fin ℓ → Bool) (x : (Fin ℓ → Bool) × Fin d → Bool)
    (v : Fin ℓ → Bool) : Fin d → Bool :=
  fun j => x (v + s j, j)

/-- The Tanner code: every vertex sees a local word in the kernel of `A`. -/
def IsWord (s : Fin d → Fin ℓ → Bool) (A : Fin c → Fin d → Bool)
    (x : (Fin ℓ → Bool) × Fin d → Bool) : Prop :=
  (∀ u i, A i ⬝ᵥ leftWord x u = false) ∧ ∀ v i, A i ⬝ᵥ rightWord s x v = false

private theorem add_add_cancel (x y : Fin ℓ → Bool) : x + y + y = x := by
  rw [add_assoc, show y + y = 0 from funext fun i => by
    simp only [Pi.add_apply, Pi.zero_apply]; cases y i <;> rfl, add_zero]

/-- The weight of an edge word is the sum of the weights of its left words. -/
theorem weight_eq_sum_left (x : (Fin ℓ → Bool) × Fin d → Bool) :
    weight x = ∑ u, weight (leftWord x u) := by
  rw [weight_eq_hammingNorm, BipartiteTanner.hammingNorm_eq_sum_left]
  exact Finset.sum_congr rfl fun u _ => (weight_eq_hammingNorm _).symm

/-- The weight of an edge word is the sum of the weights of its right words. -/
theorem weight_eq_sum_right (s : Fin d → Fin ℓ → Bool) (x : (Fin ℓ → Bool) × Fin d → Bool) :
    weight x = ∑ v, weight (rightWord s x v) := by
  rw [weight_eq_hammingNorm, BipartiteTanner.hammingNorm_eq_sum_right (cubeCayley s).doubleCover]
  exact Finset.sum_congr rfl fun v _ => (weight_eq_hammingNorm _).symm

/-- **The distance of the Tanner code.** If every nonzero local word accepted by `A` has weight
more than `h`, and the generators are `ε`-biased with `ε ≥ 0`, then every nonzero Tanner word `x`
has `(h + 1) (h + 1 - ε d) 2 ^ ℓ ≤ d · weight x`. -/
theorem le_weight_of_isWord [NeZero d] (s : Fin d → Fin ℓ → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : IsSmallBias ε ((uniformOfFintype (Fin d)).map s)) (A : Fin c → Fin d → Bool) {h : ℕ}
    (hA : ∀ w : Fin d → Bool, w ≠ 0 → (∀ i, A i ⬝ᵥ w = false) → h < weight w)
    {x : (Fin ℓ → Bool) × Fin d → Bool} (hx : IsWord s A x) (hx0 : x ≠ 0) :
    ((h + 1 : ℕ) : ℝ) * ((h + 1 : ℕ) - ε * d) * 2 ^ ℓ ≤ d * weight x := by
  have _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (NeZero.pos d)
  let C : Submodule Bool (Fin d → Bool) := Code.parityCheckCode (Matrix.of A)
  have hC : ∀ w₁ ∈ (C : Set (Fin d → Bool)), ∀ w₂ ∈ (C : Set (Fin d → Bool)), w₁ ≠ w₂ →
      ((h + 1 : ℕ) : ℝ) ≤ hammingDist w₁ w₂ := by
    intro w₁ hw₁ w₂ hw₂ hne
    have hsum : w₁ + w₂ ∈ C := C.add_mem hw₁ hw₂
    have hsum0 : w₁ + w₂ ≠ 0 := fun h0 => hne (sub_eq_zero.1 (funext fun i => by
      simpa only [Pi.sub_apply, BooleanRing.sub_eq_add, Pi.add_apply, Pi.zero_apply] using
        congrFun h0 i))
    rw [hammingDist_eq_weight_add]
    exact_mod_cast hA _ hsum0 fun i => by
      simpa [C, Code.mem_parityCheckCode, Matrix.mulVec, Pi.zero_apply, Bool.zero_eq_false] using
        congrFun (Code.mem_parityCheckCode.1 hsum) i
  have hxC : x ∈ BipartiteTanner.code (cubeCayley s).doubleCover (C : Set _) (C : Set _) := by
    refine ⟨fun u => ?_, fun v => ?_⟩ <;>
      simp only [SetLike.mem_coe, C, Code.mem_parityCheckCode, funext_iff, Matrix.mulVec,
        Matrix.of_apply, Pi.zero_apply]
    · exact fun i => hx.1 u i
    · exact fun i => hx.2 v i
  have hlam : (cubeCayley s).doubleCover.nontrivialSingularValue ≤ ε := by
    rw [BipartiteRotationMap.nontrivialSingularValue_doubleCover]
    exact spectralExpansion_cubeCayley_le s hε hs
  have hdist := BipartiteTanner.mul_sub_card_le_of_hammingDist (cubeCayley s).doubleCover
    (by positivity) hC hC hlam hxC (BipartiteTanner.submodule _ C C).zero_mem hx0
  simpa [hammingDist_zero_right, ← weight_eq_hammingNorm, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool] using hdist

/-! ### Shortening -/

variable {m : ℕ}

/-- The row of the shortened Tanner code for the check `i` at a vertex: on the left vertex `u`
(`side = false`) or the right vertex `u` (`side = true`), coordinate `e` reads the port of the
retained edge `emb e` if that edge is incident to the vertex. -/
def shortRow (s : Fin d → Fin ℓ → Bool) (A : Fin c → Fin d → Bool)
    (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (r : Bool × (Fin ℓ → Bool) × Fin c) : Fin m → Bool :=
  fun e => if (if r.1 then (emb e).1 + s (emb e).2 else (emb e).1) = r.2.1 then
    A r.2.2 (emb e).2 else false

/-- A left row of the shortened code checks the left word of the extension. -/
theorem shortRow_dotProduct_left (s : Fin d → Fin ℓ → Bool) (A : Fin c → Fin d → Bool)
    (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (z : Fin m → Bool) (u : Fin ℓ → Bool) (i : Fin c) :
    shortRow s A emb (false, u, i) ⬝ᵥ z = A i ⬝ᵥ leftWord (Code.extend emb z) u := by
  simp only [shortRow, dotProduct, leftWord, Code.extend_eq_sum, Finset.mul_sum,
    Bool.false_eq_true, ite_false]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_eq_single (emb e).2]
  · by_cases h : (emb e).1 = u
    · have h' : emb e = (u, (emb e).2) := Prod.ext h rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h')]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (congrArg Prod.fst h'))]
      cases A i (emb e).2 <;> cases z e <;> rfl
  · intro j _ hj; simp [Prod.ext_iff, Ne.symm hj]
  · simp

/-- A right row of the shortened code checks the right word of the extension. -/
theorem shortRow_dotProduct_right (s : Fin d → Fin ℓ → Bool) (A : Fin c → Fin d → Bool)
    (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (z : Fin m → Bool) (v : Fin ℓ → Bool) (i : Fin c) :
    shortRow s A emb (true, v, i) ⬝ᵥ z = A i ⬝ᵥ rightWord s (Code.extend emb z) v := by
  simp only [shortRow, dotProduct, rightWord, Code.extend_eq_sum, Finset.mul_sum, ite_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_eq_single (emb e).2]
  · by_cases h : (emb e).1 + s (emb e).2 = v
    · have : (emb e).1 = v + s (emb e).2 := by rw [← h, add_add_cancel]
      have h' : emb e = (v + s (emb e).2, (emb e).2) := Prod.ext this rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h')]
    · have : (emb e).1 ≠ v + s (emb e).2 := fun h' => h (by rw [h', add_add_cancel])
      rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_right_of_eq_false _ _ (eq_false fun h' => this (congrArg Prod.fst h'))]
      cases A i (emb e).2 <;> cases z e <;> rfl
  · intro j _ hj; simp [Prod.ext_iff, Ne.symm hj]
  · simp

/-- Each row of the shortened code has at most `d` ones: the retained edges at a vertex have
distinct ports. -/
theorem weight_shortRow_le (s : Fin d → Fin ℓ → Bool) (A : Fin c → Fin d → Bool)
    (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (r : Bool × (Fin ℓ → Bool) × Fin c) :
    weight (shortRow s A emb r) ≤ d := by
  refine (Finset.card_le_card_of_injOn (t := (univ : Finset (Fin d))) (fun e => (emb e).2)
    (fun _ _ => mem_univ _) ?_).trans (by simp)
  intro e he e' he' hee'
  replace he := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
  replace he' := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
  simp only [shortRow] at he he'
  have hv : (if r.1 then (emb e).1 + s (emb e).2 else (emb e).1) = r.2.1 := by
    by_contra h; rw [ite_eq_right_of_eq_false _ _ (eq_false h)] at he; exact Bool.false_ne_true he
  have hv' : (if r.1 then (emb e').1 + s (emb e').2 else (emb e').1) = r.2.1 := by
    by_contra h; rw [ite_eq_right_of_eq_false _ _ (eq_false h)] at he'
    exact Bool.false_ne_true he'
  simp only at hee'
  refine emb.injective (Prod.ext ?_ hee')
  cases hr : r.1
  · simp only [hr, Bool.false_eq_true, ite_false] at hv hv'
    rw [hv, hv']
  · simp only [hr, ite_true] at hv hv'
    rw [← add_add_cancel (emb e).1 (s (emb e).2), hv, hee', ← hv', add_add_cancel]

/-- **The shortened Tanner code.** Under the hypotheses of `le_weight_of_isWord`, including
`ε ≥ 0`, every nonzero `z` orthogonal to all the rows `shortRow` has
`(h + 1) (h + 1 - ε d) 2 ^ ℓ ≤ d · weight z`. -/
theorem le_weight_of_shortRow [NeZero d] (s : Fin d → Fin ℓ → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : IsSmallBias ε ((uniformOfFintype (Fin d)).map s)) (A : Fin c → Fin d → Bool) {h : ℕ}
    (hA : ∀ w : Fin d → Bool, w ≠ 0 → (∀ i, A i ⬝ᵥ w = false) → h < weight w)
    (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) {z : Fin m → Bool}
    (hz : ∀ r, shortRow s A emb r ⬝ᵥ z = false) (hz0 : z ≠ 0) :
    ((h + 1 : ℕ) : ℝ) * ((h + 1 : ℕ) - ε * d) * 2 ^ ℓ ≤ d * weight z := by
  have hx : IsWord s A (Code.extend emb z) :=
    ⟨fun u i => by rw [← shortRow_dotProduct_left]; exact hz _,
      fun v i => by rw [← shortRow_dotProduct_right]; exact hz _⟩
  have hx0 : Code.extend emb z ≠ 0 := fun h0 => hz0 (funext fun e => by
    rw [← Code.extend_emb emb z e, h0]; rfl)
  have hwt : weight (Code.extend emb z) = weight z := by
    simp only [weight_eq_hammingNorm, Code.hammingNorm_extend]
  rw [← hwt]
  exact le_weight_of_isWord s hε hs A hA hx hx0

end Tanner

end Cslib.BitString
