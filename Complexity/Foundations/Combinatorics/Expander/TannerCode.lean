/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Cayley
public import Complexity.Foundations.Data.BitString.Weight
import Complexity.Foundations.Data.BitString.Parity.DotProduct

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

/-- The rows orthogonal to a nonzero `w`: `2 ^ (d - 1)` of the `2 ^ d`. -/
theorem card_dotProduct_eq_false {w : Fin d → Bool} (hw : w ≠ 0) :
    #{x : Fin d → Bool | x ⬝ᵥ w = false} = 2 ^ (d - 1) := by
  obtain ⟨j, hj⟩ : ∃ j, w j = true := by
    by_contra h
    simp only [not_exists, Bool.not_eq_true] at h
    exact hw (funext h)
  simp only [dotProduct_eq_parityOn]
  rw [card_filter_parityOn_eq ⟨j, by simpa using hj⟩, Fintype.card_fin]

/-- Matrices with `c` rows whose kernel contains a nonzero `w`: `2 ^ ((d - 1) c)`. -/
theorem card_kernel {w : Fin d → Bool} (hw : w ≠ 0) :
    #{A : Fin c → Fin d → Bool | ∀ i, A i ⬝ᵥ w = false} = (2 ^ (d - 1)) ^ c := by
  rw [← card_dotProduct_eq_false hw, ← Fintype.card_piFinset_const]
  congr 1
  ext A
  simp [Fintype.mem_piFinset]

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
  simp only [weight_eq_sum_toNat, leftWord, Fintype.sum_prod_type]

/-- The weight of an edge word is the sum of the weights of its right words. -/
theorem weight_eq_sum_right (s : Fin d → Fin ℓ → Bool) (x : (Fin ℓ → Bool) × Fin d → Bool) :
    weight x = ∑ v, weight (rightWord s x v) := by
  rw [weight_eq_sum_left]
  simp only [weight_eq_sum_toNat, leftWord, rightWord]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun v j => (x (v + s j, j)).toNat)]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (Fintype.sum_equiv (Equiv.addRight (s j)) _ _ fun v => by simp).symm

/-- **The distance of the Tanner code.** If every nonzero local word accepted by `A` has weight
more than `h`, and the generators are `ε`-biased with `ε ≥ 0`, then every nonzero Tanner word `x`
has `(h + 1) (h + 1 - ε d) 2 ^ ℓ ≤ d · weight x`. -/
theorem le_weight_of_isWord [NeZero d] (s : Fin d → Fin ℓ → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : IsSmallBias ε ((uniformOfFintype (Fin d)).map s)) (A : Fin c → Fin d → Bool) {h : ℕ}
    (hA : ∀ w : Fin d → Bool, w ≠ 0 → (∀ i, A i ⬝ᵥ w = false) → h < weight w)
    {x : (Fin ℓ → Bool) × Fin d → Bool} (hx : IsWord s A x) (hx0 : x ≠ 0) :
    ((h + 1 : ℕ) : ℝ) * ((h + 1 : ℕ) - ε * d) * 2 ^ ℓ ≤ d * weight x := by
  set U := ({u | leftWord x u ≠ 0} : Finset (Fin ℓ → Bool))
  set V := ({v | rightWord s x v ≠ 0} : Finset (Fin ℓ → Bool))
  set k : ℝ := ((h + 1 : ℕ) : ℝ)
  set W : ℝ := (weight x : ℝ)
  -- lower bounds from the local distance
  have hU : k * #U ≤ W := by
    have : (h + 1) * #U ≤ weight x := by
      rw [weight_eq_sum_left, ← sum_filter_add_sum_filter_not univ (fun u => leftWord x u ≠ 0)]
      refine le_add_right ?_
      rw [mul_comm, ← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun u hu => hA _ (mem_filter.mp hu).2 (hx.1 u)
    simp only [k, W]
    exact_mod_cast this
  have hV : k * #V ≤ W := by
    have : (h + 1) * #V ≤ weight x := by
      rw [weight_eq_sum_right s, ← sum_filter_add_sum_filter_not univ
        (fun v => rightWord s x v ≠ 0)]
      refine le_add_right ?_
      rw [mul_comm, ← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun v hv => hA _ (mem_filter.mp hv).2 (hx.2 v)
    simp only [k, W]
    exact_mod_cast this
  -- every edge of `x` joins `U` to `V`
  have hE : weight x ≤ #((cubeCayley s).interedges U V) := by
    refine card_le_card fun p hp => ?_
    obtain ⟨u, j⟩ := p
    simp only [mem_filter, mem_univ, true_and] at hp
    rw [mem_interedges, cubeCayley_neighbor]
    refine ⟨?_, ?_⟩
    · simp only [U, mem_filter, mem_univ, true_and]
      intro h0; have := congrFun h0 j; simp [leftWord, hp] at this
    · simp only [V, mem_filter, mem_univ, true_and]
      intro h0; have := congrFun h0 j; simp [rightWord, add_add_cancel, hp] at this
  have hmix := card_interedges_cubeCayley_le s hε hs U V
  simp only [Fintype.card_fin] at hmix
  have hWE : W ≤ (#((cubeCayley s).interedges U V) : ℝ) := by simp only [W]; exact_mod_cast hE
  -- `U` and `V` are nonempty
  obtain ⟨⟨u₀, j₀⟩, hp₀⟩ : ∃ p, x p = true := by
    by_contra hne
    simp only [not_exists, Bool.not_eq_true] at hne
    exact hx0 (funext hne)
  have hu₀ : u₀ ∈ U := by
    simp only [U, mem_filter, mem_univ, true_and]
    intro h0; have := congrFun h0 j₀; simp [leftWord, hp₀] at this
  have hv₀ : u₀ + s j₀ ∈ V := by
    simp only [V, mem_filter, mem_univ, true_and]
    intro h0; have := congrFun h0 j₀; simp [rightWord, add_add_cancel, hp₀] at this
  have ha : (1 : ℝ) ≤ #U := by exact_mod_cast card_pos.mpr ⟨u₀, hu₀⟩
  have hb : (1 : ℝ) ≤ #V := by exact_mod_cast card_pos.mpr ⟨_, hv₀⟩
  set t : ℝ := √((#U : ℝ) * #V)
  have ht2 : t ^ 2 = (#U : ℝ) * #V := Real.sq_sqrt (by positivity)
  have ht1 : 1 ≤ t := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hk0 : 0 ≤ k := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hq : (0 : ℝ) < 2 ^ ℓ := by positivity
  -- `k t ≤ W`, the geometric mean of the two lower bounds
  have hkt : k * t ≤ W := by
    have hW0 : 0 ≤ W := by positivity
    have h2 : (k * t) ^ 2 ≤ W ^ 2 := by
      rw [mul_pow, ht2]; nlinarith [mul_le_mul hU hV (by positivity) hW0]
    exact (pow_le_pow_iff_left₀ (by positivity) hW0 two_ne_zero).mp h2
  -- `k ≤ d t / q + ε d`
  have hup : k * t ≤ d * t ^ 2 / 2 ^ ℓ + ε * d * t := by
    have e : (d : ℝ) * (#U * #V) / 2 ^ ℓ = d * #U * #V / 2 ^ ℓ := by ring
    rw [ht2, e]; linarith
  have hkey : (k - ε * d) * 2 ^ ℓ ≤ d * t := by
    have : k * t * 2 ^ ℓ ≤ d * t ^ 2 + ε * d * t * 2 ^ ℓ := by
      have := mul_le_mul_of_nonneg_right hup hq.le
      rwa [add_mul, div_mul_cancel₀ _ hq.ne'] at this
    nlinarith
  rcases le_or_gt (k - ε * d) 0 with hneg | hpos
  · nlinarith [mul_nonneg hk0 hq.le, mul_nonneg hd0 (show (0:ℝ) ≤ W by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left hkey hk0, mul_le_mul_of_nonneg_left hkt hd0]

/-! ### Shortening -/

variable {m : ℕ}

/-- The row of the shortened Tanner code for the check `i` at a vertex: on the left vertex `u`
(`side = false`) or the right vertex `u` (`side = true`), coordinate `e` reads the port of the
retained edge `emb e` if that edge is incident to the vertex. -/
def shortRow (s : Fin d → Fin ℓ → Bool) (A : Fin c → Fin d → Bool)
    (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (r : Bool × (Fin ℓ → Bool) × Fin c) : Fin m → Bool :=
  fun e => if (if r.1 then (emb e).1 + s (emb e).2 else (emb e).1) = r.2.1 then
    A r.2.2 (emb e).2 else false

/-- The edge word extending `z` by zero outside the retained edges. -/
def extend (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (z : Fin m → Bool) :
    (Fin ℓ → Bool) × Fin d → Bool :=
  fun p => ∑ e, if emb e = p then z e else 0

/-- The extension agrees with `z` on the retained edges. -/
theorem extend_emb (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (z : Fin m → Bool) (e : Fin m) :
    extend emb z (emb e) = z e := by
  rw [extend, Finset.sum_eq_single e (fun e' _ he' => by simp [emb.injective.ne he'])
    (by simp)]
  simp

/-- The extension vanishes off the retained edges. -/
theorem extend_of_notMem (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (z : Fin m → Bool)
    {p} (hp : ∀ e, emb e ≠ p) : extend emb z p = 0 := by
  simp [extend, hp]

/-- Extending by zero preserves the weight. -/
theorem weight_extend (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (z : Fin m → Bool) :
    weight (extend emb z) = weight z := by
  symm
  refine Finset.card_bij (fun e _ => emb e) (fun e he => ?_) (fun _ _ _ _ h => emb.injective h)
    (fun p hp => ?_)
  · simp only [mem_filter, mem_univ, true_and] at he ⊢
    rw [extend_emb, he]
  · simp only [mem_filter, mem_univ, true_and] at hp
    by_contra hne
    simp only [mem_filter, mem_univ, true_and, not_exists] at hne
    have : ∀ e, emb e ≠ p := fun e he => hne e (by rw [← he, extend_emb] at hp; exact hp) he
    rw [extend_of_notMem emb z this] at hp
    exact Bool.false_ne_true hp

/-- A left row of the shortened code checks the left word of the extension. -/
theorem shortRow_dotProduct_left (s : Fin d → Fin ℓ → Bool) (A : Fin c → Fin d → Bool)
    (emb : Fin m ↪ (Fin ℓ → Bool) × Fin d) (z : Fin m → Bool) (u : Fin ℓ → Bool) (i : Fin c) :
    shortRow s A emb (false, u, i) ⬝ᵥ z = A i ⬝ᵥ leftWord (extend emb z) u := by
  simp only [shortRow, dotProduct, leftWord, extend, Finset.mul_sum, Bool.false_eq_true,
    ite_false]
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
    shortRow s A emb (true, v, i) ⬝ᵥ z = A i ⬝ᵥ rightWord s (extend emb z) v := by
  simp only [shortRow, dotProduct, rightWord, extend, Finset.mul_sum, ite_true]
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
  have hx : IsWord s A (extend emb z) :=
    ⟨fun u i => by rw [← shortRow_dotProduct_left]; exact hz _,
      fun v i => by rw [← shortRow_dotProduct_right]; exact hz _⟩
  have hx0 : extend emb z ≠ 0 := fun h0 => hz0 (funext fun e => by
    rw [← extend_emb emb z e, h0]; rfl)
  rw [← weight_extend emb z]
  exact le_weight_of_isWord s hε hs A hA hx hx0

end Tanner

end Cslib.BitString
