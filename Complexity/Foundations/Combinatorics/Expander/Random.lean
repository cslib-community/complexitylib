/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Perm
import Complexity.Foundations.Data.Nat.Choose
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Random permutations move small sets

Thirty permutations of a finite set `V` can be chosen so that every set `S` of at most half of the
points has at least a tenth of its points moved out of `S` by one of them
(`exists_perms_card_le_mul_card_filter_notMem`). By `Cslib.RotationMap.le_edgeExpansion_ofPerms`
this makes the `60`-regular multigraph of the permutations an edge expander, which is the classical
probabilistic proof that constant-degree expanders exist
[Hoory, Linial and Wigderson, Theorem 4.16][HooryLinialWigderson2006]
[Arora and Barak, Chapter 21][AroraBarak09].

The proof is a counting argument; it is the probabilistic method with the probabilities
multiplied out. Let `n = |V|` and let `S` have `s` points, `1 ≤ s ≤ n / 2`. A permutation fails
`S` when it moves fewer than `s / 10` points of `S` out of `S`; it then keeps some `k`-element
subset `K ⊆ S` inside `S`, where `k = s - ⌊(s - 1) / 10⌋ ≥ 9 s / 10`. For a fixed `K` this
happens for at most `s (s - 1) ⋯ (s - k + 1) (n - k)!` of the `n!` permutations, a fraction at
most `(s / n)^k`. Taking the `C(s, k) ≤ 3^s / 2^k` choices of `K` into account, a uniformly
random permutation fails `S` with probability at most `3^s (s / 2n)^k`, and thirty independent
ones all fail it with probability at most `3^{30 s} (s / 2n)^{27 s}`. As there are at most
`(3 n / s)^s` sets of size `s`, thirty random permutations all fail some set of size `s` with
probability at most `(3^{31} / 2^{53})^s ≤ 8^{-s}`. Summed over `s ≥ 1`, this is less than one.

## Main results

* `Cslib.exists_perms_card_le_mul_card_filter_notMem`: thirty permutations that move a tenth of
  every set of at most half of the points out of it.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib

open Finset Equiv
open scoped Nat

section Count

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At most `(n - k)!` permutations of an `n`-element type agree with a given injective map on a
`k`-element set `K`: on the complement of `K` they are embeddings into the complement of its image.
-/
private theorem card_filter_forall_eq_le (K : Finset V) (g : K → V)
    (hg : Function.Injective g) :
    #{σ : Perm V | ∀ v : K, σ v = g v} ≤ (Fintype.card V - #K)! := by
  set R : Finset V := (univ.image g)ᶜ with hR
  have hRcard : #R = Fintype.card V - #K := by
    rw [hR, card_compl, card_image_of_injective _ hg, card_univ, Fintype.card_coe]
  calc #{σ : Perm V | ∀ v : K, σ v = g v}
      ≤ Fintype.card ({v // v ∈ Kᶜ} ↪ {v // v ∈ R}) := by
        rw [← Fintype.card_coe]
        refine Fintype.card_le_of_injective (fun σ ↦ ⟨fun v ↦ ⟨σ.1 v, ?_⟩, fun a b h ↦
          Subtype.ext (σ.1.injective (congrArg Subtype.val h))⟩) fun σ τ h ↦ ?_
        · rw [hR, mem_compl, mem_image]
          rintro ⟨w, -, hw⟩
          rw [← (mem_filter.1 σ.2).2 w] at hw
          exact (mem_compl.1 v.2) (σ.1.injective hw ▸ w.2)
        · refine Subtype.ext (Equiv.ext fun v ↦ ?_)
          by_cases hv : v ∈ K
          · rw [(mem_filter.1 σ.2).2 ⟨v, hv⟩, (mem_filter.1 τ.2).2 ⟨v, hv⟩]
          · exact congrArg Subtype.val (DFunLike.congr_fun h ⟨v, mem_compl.2 hv⟩)
    _ = (Fintype.card V - #K)! := by
        rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe, hRcard, card_compl,
          Nat.descFactorial_self]

/-- At most `s (s - 1) ⋯ (s - k + 1) (n - k)!` permutations of an `n`-element type map a
`k`-element set `K` into an `s`-element set `S`: on `K` such a permutation is one of the
`s (s - 1) ⋯ (s - k + 1)` embeddings of `K` into `S`. -/
private theorem card_filter_forall_mem_le (K S : Finset V) :
    #{σ : Perm V | ∀ v ∈ K, σ v ∈ S} ≤ (#S).descFactorial #K * (Fintype.card V - #K)! := by
  have h : ({σ : Perm V | ∀ v ∈ K, σ v ∈ S} : Finset (Perm V)) ⊆
      (univ : Finset (K ↪ S)).biUnion fun g ↦ {σ : Perm V | ∀ v : K, σ v = g v} := by
    intro σ hσ
    rw [mem_filter] at hσ
    exact mem_biUnion.2 ⟨⟨fun v ↦ ⟨σ v, hσ.2 v v.2⟩,
      fun a b h ↦ Subtype.ext (σ.injective (congrArg Subtype.val h))⟩, mem_univ _,
      mem_filter.2 ⟨mem_univ _, fun _ ↦ rfl⟩⟩
  calc #{σ : Perm V | ∀ v ∈ K, σ v ∈ S}
      ≤ ∑ g : K ↪ S, #{σ : Perm V | ∀ v : K, σ v = g v} :=
        (card_le_card h).trans card_biUnion_le
    _ ≤ ∑ _g : K ↪ S, (Fintype.card V - #K)! :=
        sum_le_sum fun g _ ↦ card_filter_forall_eq_le K (fun v ↦ g v)
          fun a b h ↦ g.injective (Subtype.ext h)
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe,
          smul_eq_mul]

/-- At most `C(s, k) s (s - 1) ⋯ (s - k + 1) (n - k)!` permutations of an `n`-element type keep at
least `k` points of an `s`-element set `S` inside `S`. -/
private theorem card_filter_le_card_filter_mem_le (S : Finset V) (k : ℕ) :
    #{σ : Perm V | k ≤ #{v ∈ S | σ v ∈ S}} ≤
      (#S).choose k * ((#S).descFactorial k * (Fintype.card V - k)!) :=
  calc #{σ : Perm V | k ≤ #{v ∈ S | σ v ∈ S}}
      ≤ #((S.powersetCard k).biUnion fun K ↦ {σ : Perm V | ∀ v ∈ K, σ v ∈ S}) := by
        refine card_le_card fun σ hσ ↦ ?_
        obtain ⟨K, hK, hKc⟩ := exists_subset_card_eq (mem_filter.1 hσ).2
        exact mem_biUnion.2 ⟨K, mem_powersetCard.2 ⟨hK.trans (filter_subset _ _), hKc⟩,
          mem_filter.2 ⟨mem_univ _, fun v hv ↦ (mem_filter.1 (hK hv)).2⟩⟩
    _ ≤ ∑ K ∈ S.powersetCard k, #{σ : Perm V | ∀ v ∈ K, σ v ∈ S} := card_biUnion_le
    _ ≤ ∑ K ∈ S.powersetCard k, (#S).descFactorial k * (Fintype.card V - k)! :=
        sum_le_sum fun K hK ↦ (mem_powersetCard.1 hK).2 ▸ card_filter_forall_mem_le K S
    _ = _ := by rw [sum_const, card_powersetCard, smul_eq_mul]

/-- A single term of the binomial expansion of `(2 + 1)^s`: `C(s, k) 2^k ≤ 3^s`. -/
private theorem choose_mul_two_pow_le (s k : ℕ) : s.choose k * 2 ^ k ≤ 3 ^ s := by
  rcases le_or_gt k s with hk | hk
  · calc s.choose k * 2 ^ k = 2 ^ k * 1 ^ (s - k) * s.choose k := by ring
      _ ≤ ∑ m ∈ range (s + 1), 2 ^ m * 1 ^ (s - m) * s.choose m :=
        single_le_sum (f := fun m ↦ 2 ^ m * 1 ^ (s - m) * s.choose m) (fun _ _ ↦ Nat.zero_le _)
          (mem_range.2 (Nat.lt_succ_of_le hk))
      _ = (2 + 1) ^ s := (add_pow 2 1 s).symm
      _ = 3 ^ s := by norm_num
  · rw [Nat.choose_eq_zero_of_lt hk, zero_mul]
    exact Nat.zero_le _

/-- A uniformly random permutation of an `n`-element type keeps at least `k` points of an
`s`-element set `S` inside `S` with probability at most `3^s (s / 2n)^k`. -/
private theorem card_filter_mul_pow_le (S : Finset V) {k : ℕ} (hk : k ≤ Fintype.card V) :
    #{σ : Perm V | k ≤ #{v ∈ S | σ v ∈ S}} * (2 * Fintype.card V) ^ k ≤
      3 ^ #S * #S ^ k * (Fintype.card V)! := by
  set n := Fintype.card V
  calc #{σ : Perm V | k ≤ #{v ∈ S | σ v ∈ S}} * (2 * n) ^ k
      ≤ (#S).choose k * ((#S).descFactorial k * (n - k)!) * (2 * n) ^ k :=
        Nat.mul_le_mul_right _ (card_filter_le_card_filter_mem_le S k)
    _ = ((#S).choose k * 2 ^ k) * ((#S).descFactorial k * n ^ k) * (n - k)! := by
        rw [mul_pow]
        ring
    _ ≤ 3 ^ #S * (#S ^ k * n.descFactorial k) * (n - k)! :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (choose_mul_two_pow_le _ _)
          (Nat.descFactorial_mul_pow_le (card_le_univ S) k))
    _ = 3 ^ #S * #S ^ k * ((n - k)! * n.descFactorial k) := by ring
    _ = 3 ^ #S * #S ^ k * n ! := by rw [Nat.factorial_mul_descFactorial hk]

end Count

/-- For any natural number `s`, `s ^ s / s! ≤ 3 ^ s`. -/
private theorem pow_div_factorial_le_three_pow (s : ℕ) : (s : ℝ) ^ s / s ! ≤ 3 ^ s :=
  (Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg s) s).trans <| by
    rw [← mul_one (s : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (Real.exp_one_lt_d9.le.trans (by norm_num)) s

/-- The arithmetic of the union bound: for `1 ≤ s`, `2 s ≤ n` and `9 s ≤ 10 k`, the `C(n, s)`
sets of size `s`, each failed by thirty permutations with probability at most
`(3^s (s / 2n)^k)^30`, are failed with probability at most `2^{-s} / 4` in total. -/
private theorem choose_mul_pow_le {n s k : ℕ} (hs : 0 < s) (hsn : 2 * s ≤ n)
    (hk : 9 * s ≤ 10 * k) :
    (n.choose s : ℝ) * (3 ^ s * (s / (2 * n)) ^ k) ^ 30 ≤ (1 / 2) ^ s / 4 := by
  have hs' : (0 : ℝ) < s := Nat.cast_pos.2 hs
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  set x : ℝ := s / (2 * n) with hx
  have hx0 : 0 < x := by positivity
  have hx4 : x ≤ 1 / 4 := by
    rw [hx, div_le_iff₀ (by positivity)]
    have : (2 * s : ℝ) ≤ n := by exact_mod_cast hsn
    linarith
  have hchoose : (n.choose s : ℝ) ≤ (3 / (2 * x)) ^ s := by
    have h3 := pow_div_factorial_le_three_pow s
    calc (n.choose s : ℝ) ≤ n ^ s / s ! := Nat.choose_le_pow_div s n
      _ = (n / s) ^ s * (s ^ s / s !) := by
        rw [div_pow]
        field_simp
      _ ≤ (n / s) ^ s * 3 ^ s := by gcongr
      _ = (3 / (2 * x)) ^ s := by
        rw [← mul_pow, hx]
        congr 1
        field_simp
  have hpow : (3 ^ s * x ^ k) ^ 30 ≤ (3 ^ 30) ^ s * (x ^ 27) ^ s := by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm s 30]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0.le (by linarith) (by omega))
      (by positivity)
  calc (n.choose s : ℝ) * (3 ^ s * x ^ k) ^ 30
      ≤ (3 / (2 * x)) ^ s * ((3 ^ 30) ^ s * (x ^ 27) ^ s) := by gcongr
    _ = (3 ^ 31 * x ^ 26 / 2) ^ s := by
        rw [← mul_pow, ← mul_pow]
        congr 1
        field_simp
    _ ≤ (1 / 8) ^ s := by
        refine pow_le_pow_left₀ (by positivity) ?_ s
        calc 3 ^ 31 * x ^ 26 / 2 ≤ 3 ^ 31 * (1 / 4) ^ 26 / 2 := by gcongr
          _ ≤ 1 / 8 := by norm_num
    _ = (1 / 2) ^ s * (1 / 4) ^ s := by rw [← mul_pow]; norm_num
    _ ≤ (1 / 2) ^ s * (1 / 4) :=
        mul_le_mul_of_nonneg_left (pow_le_of_le_one (by norm_num) (by norm_num) hs.ne')
          (by positivity)
    _ = (1 / 2) ^ s / 4 := by ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Thirty uniformly random permutations all keep more than nine tenths of a nonempty set `S` of
at most half of the points inside `S` with probability at most `2^{-|S|} / (4 C(n, |S|))`. -/
private theorem card_filter_pow_le {S : Finset V} (hS : 0 < #S)
    (hSn : 2 * #S ≤ Fintype.card V) :
    (#{σ : Perm V | #S - (#S - 1) / 10 ≤ #{v ∈ S | σ v ∈ S}} : ℝ) ^ 30 ≤
      ((Fintype.card V)! : ℝ) ^ 30 * ((1 / 2) ^ #S / 4 / (Fintype.card V).choose #S) := by
  set n := Fintype.card V
  set k := #S - (#S - 1) / 10
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hc : (#{σ : Perm V | k ≤ #{v ∈ S | σ v ∈ S}} : ℝ) * (2 * n) ^ k ≤
      3 ^ #S * #S ^ k * n ! := by
    exact_mod_cast card_filter_mul_pow_le S (k := k) (by omega)
  have h1 : (#{σ : Perm V | k ≤ #{v ∈ S | σ v ∈ S}} : ℝ) ≤
      n ! * (3 ^ #S * (#S / (2 * n)) ^ k) := by
    have h2 : (0 : ℝ) < (2 * n) ^ k := by positivity
    calc (#{σ : Perm V | k ≤ #{v ∈ S | σ v ∈ S}} : ℝ)
        = #{σ : Perm V | k ≤ #{v ∈ S | σ v ∈ S}} * (2 * n) ^ k / (2 * n) ^ k := by field_simp
      _ ≤ (3 : ℝ) ^ #S * (#S : ℝ) ^ k * (n ! : ℝ) / (2 * n) ^ k := by gcongr
      _ = _ := by rw [div_pow]; ring
  have hC : (0 : ℝ) < n.choose #S := Nat.cast_pos.2 (Nat.choose_pos (by omega))
  calc _ ≤ ((n ! : ℝ) * (3 ^ #S * (#S / (2 * n)) ^ k)) ^ 30 := by gcongr
    _ = (n ! : ℝ) ^ 30 * (3 ^ #S * (#S / (2 * n)) ^ k) ^ 30 := mul_pow _ _ _
    _ ≤ _ := by
        gcongr
        rw [le_div_iff₀' hC]
        exact choose_mul_pow_le hS hSn (by omega)

/-- Summing the 30-tuple failure bound over all `S` with `0 < #S` and `2 * #S ≤ |V|` gives at
most `(|V|!)^30 / 2`. -/
private theorem sum_card_filter_pow_thirty_le :
    ∑ S ∈ ({S : Finset V | 0 < #S ∧ 2 * #S ≤ Fintype.card V} : Finset (Finset V)),
      (#{τ : Perm V | #S - (#S - 1) / 10 ≤ #{v ∈ S | τ v ∈ S}} : ℝ) ^ 30 ≤
      ((Fintype.card V)! : ℝ) ^ 30 / 2 := by
  set n := Fintype.card V
  set 𝒮 : Finset (Finset V) := {S | 0 < #S ∧ 2 * #S ≤ n}
  calc _ ≤ ∑ S ∈ 𝒮, (n ! : ℝ) ^ 30 * ((1 / 2) ^ #S / 4 / n.choose #S) :=
        sum_le_sum fun S hS ↦ card_filter_pow_le (mem_filter.1 hS).2.1 (mem_filter.1 hS).2.2
    _ ≤ ∑ S : Finset V, (n ! : ℝ) ^ 30 * ((1 / 2) ^ #S / 4 / n.choose #S) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ by positivity
    _ = ∑ m ∈ range (n + 1), (n ! : ℝ) ^ 30 / 4 * (1 / 2) ^ m := by
        have := sum_powerset_apply_card
          (fun m ↦ (n ! : ℝ) ^ 30 * ((1 / 2) ^ m / 4 / n.choose m)) (x := (univ : Finset V))
        rw [← powerset_univ, this, card_univ]
        refine sum_congr rfl fun m hm ↦ ?_
        have : (n.choose m : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.lt_succ_iff.1 (mem_range.1 hm))).ne'
        rw [nsmul_eq_mul]
        field_simp
        rfl
    _ ≤ (n ! : ℝ) ^ 30 / 4 * 2 := by
        rw [← mul_sum]
        gcongr
        exact sum_geometric_two_le _
    _ = (n ! : ℝ) ^ 30 / 2 := by ring

variable (V) in
/-- **Random permutations move small sets**: there are thirty permutations of a finite type `V` such
that every set `S` of at most half of the points has at least a tenth of its points moved out of `S`
by one of them. This is the counting form of the probabilistic proof that constant-degree expanders
exist [Hoory, Linial and Wigderson, Theorem 4.16][HooryLinialWigderson2006]
[Arora and Barak, Chapter 21][AroraBarak09]. -/
theorem exists_perms_card_le_mul_card_filter_notMem :
    ∃ σ : Fin 30 → Perm V, ∀ S : Finset V, 2 * #S ≤ Fintype.card V →
      ∃ i, #S ≤ 10 * #{v ∈ S | σ i v ∉ S} := by
  by_contra! h
  set n := Fintype.card V
  set 𝒮 : Finset (Finset V) := {S | 0 < #S ∧ 2 * #S ≤ n}
  -- Every tuple fails some nonempty set `S ∈ 𝒮`: each of its permutations keeps more than nine
  -- tenths of `S` inside `S`.
  have hcover : (univ : Finset (Fin 30 → Perm V)) ⊆ 𝒮.biUnion fun S ↦
      Fintype.piFinset fun _ ↦ {τ : Perm V | #S - (#S - 1) / 10 ≤ #{v ∈ S | τ v ∈ S}} := by
    intro σ _
    obtain ⟨S, hS, hσ⟩ := h σ
    have hpos : 0 < #S := by
      have := hσ 0
      omega
    refine mem_biUnion.2 ⟨S, mem_filter.2 ⟨mem_univ _, hpos, hS⟩,
      Fintype.mem_piFinset.2 fun i ↦ mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have := hσ i
    have := card_filter_add_card_filter_not (s := S) fun v ↦ σ i v ∈ S
    omega
  have hlow : ((n ! : ℕ) : ℝ) ^ 30 ≤
      ∑ S ∈ 𝒮, (#{τ : Perm V | #S - (#S - 1) / 10 ≤ #{v ∈ S | τ v ∈ S}} : ℝ) ^ 30 := by
    have := (card_le_card hcover).trans card_biUnion_le
    simp only [card_univ, Fintype.card_pi, Fintype.card_perm, prod_const, Fintype.card_fin,
      Fintype.card_piFinset] at this
    exact_mod_cast this
  have hup := sum_card_filter_pow_thirty_le (V := V)
  have : (0 : ℝ) < (n ! : ℝ) ^ 30 := by positivity
  linarith

end Cslib
