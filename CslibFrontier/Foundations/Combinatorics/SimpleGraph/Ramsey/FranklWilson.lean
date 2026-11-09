/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Ramsey.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Ramsey.Basic
public import Mathlib.Data.Nat.Prime.Defs
import CslibFrontier.Foundations.Combinatorics.SetFamily.RayChaudhuriWilson
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Frankl–Wilson Ramsey graph

The Frankl–Wilson graph `SimpleGraph.franklWilsonGraph α p d` has the `d`-element subsets of `α`
as vertices, two of them adjacent when the size of their intersection is not congruent to `d`
mod `p`. A vertex meets itself in `d` points, so the graph is loopless. With `n = |α|`:

* a clique is a `d`-uniform family whose pairwise intersection sizes avoid `d` mod `p`. For a
  prime `p` with `d ≡ -1 (mod p)` the allowed residues are the `p - 1` residues other than `-1`,
  and the modular Frankl–Wilson bound gives at most `C(n, p - 1)` members
  (`SimpleGraph.cliqueFree_franklWilsonGraph`);
* an independent set is a `d`-uniform family whose pairwise intersection sizes are congruent to `d`
  mod `p` and less than `d`, so lie among the `⌊d / p⌋` values `m p + (d mod p)`; the
  Ray-Chaudhuri–Wilson theorem gives at most `C(n, ⌊d / p⌋)` members
  (`SimpleGraph.indepSetFree_franklWilsonGraph`).

Frankl and Wilson take `n = p³` and `d = p² - 1` [FranklWilson1981]: the graph has `C(p³, p² - 1)`
vertices and neither a clique nor an independent set of more than `C(p³, p - 1)` vertices
(`SimpleGraph.choose_lt_ramseyNumber_franklWilson`). With `k = C(p³, p - 1) + 1` this is
`k ^ Θ(log k / log log k)` vertices, superpolynomial in `k`;
`SimpleGraph.pow_lt_ramseyNumber_franklWilson` records `k ^ c < R(k, k)` for every prime
`p ≥ 6 c + 3`. Nagy's graph (`SimpleGraph.nagyGraph`) gives only `Θ(k ^ 3)` vertices.
Polynomial-time names and adjacency are in
`CslibFrontier.Computability.Complexity.ExplicitRamsey.FranklWilson`.

## Main definitions

* `SimpleGraph.franklWilsonGraph α p d`: the Frankl–Wilson graph on the `d`-subsets of `α`.

## Main results

* `SimpleGraph.cliqueFree_franklWilsonGraph`: no clique of size `C(|α|, p - 1) + 1` when `p` is
  prime and `d ≡ -1 (mod p)`.
* `SimpleGraph.indepSetFree_franklWilsonGraph`: no independent set of size
  `C(|α|, ⌊d / p⌋) + 1`.
* `SimpleGraph.choose_lt_ramseyNumber_franklWilson`:
  `C(p³, p² - 1) < R(C(p³, p - 1) + 1, C(p³, p - 1) + 1)` for every prime `p`.
* `SimpleGraph.pow_lt_ramseyNumber_franklWilson`: with `k = C(p³, p - 1) + 1`, `k ^ c < R(k, k)`
  for every prime `p ≥ 6 c + 3`.

## References

* [P. Frankl, R. M. Wilson, *Intersection theorems with geometric consequences*][FranklWilson1981]
* [S. Jukna, *Extremal Combinatorics*][Jukna2011]
-/

public section

open Finset

namespace SimpleGraph

/-- The **Frankl–Wilson graph**: the `d`-element subsets of `α`, two of them adjacent when the size
of their intersection is not congruent to `d` mod `p` [FranklWilson1981]. -/
def franklWilsonGraph (α : Type*) [DecidableEq α] (p d : ℕ) :
    SimpleGraph {s : Finset α // #s = d} where
  Adj s t := #(s.1 ∩ t.1) % p ≠ d % p
  symm := ⟨fun s t h => by rwa [inter_comm]⟩
  loopless := ⟨fun s h => by rw [inter_self, s.2] at h; exact h rfl⟩

variable {α : Type*} [DecidableEq α]

theorem franklWilsonGraph_adj {p d : ℕ} {s t : {s : Finset α // #s = d}} :
    (franklWilsonGraph α p d).Adj s t ↔ #(s.1 ∩ t.1) % p ≠ d % p := Iff.rfl

variable [Fintype α]

/-- For a prime `p` and `d ≡ -1 (mod p)`, the Frankl–Wilson graph has no clique of size
`C(|α|, p - 1) + 1`, by the modular Frankl–Wilson bound. -/
theorem cliqueFree_franklWilsonGraph {p d : ℕ} [hp : Fact p.Prime] (hd : d % p = p - 1) :
    (franklWilsonGraph α p d).CliqueFree ((Fintype.card α).choose (p - 1) + 1) := by
  intro t ht
  set L : Finset (ZMod p) := univ.erase (d : ZMod p) with hL
  have hLc : #L = p - 1 := by rw [hL, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have h := Fintype.card_le_choose_of_card_inter_mem_zmod (ι := t) (fun s => s.1.1) L
    (fun s => s.1.2) (fun i j hij => ?_) (by rw [hL]; exact notMem_erase _ _) (by rw [hLc, hd])
  · rw [Fintype.card_coe, ht.2, hLc] at h
    omega
  · rw [hL, mem_erase]
    refine ⟨fun h => ?_, mem_univ _⟩
    rw [ZMod.natCast_eq_natCast_iff'] at h
    exact ht.1 i.2 j.2 (fun h' => hij (Subtype.ext h')) h

/-- For `p > 0`, the Frankl–Wilson graph has no independent set of size `C(|α|, ⌊d / p⌋) + 1`, by
the Ray-Chaudhuri–Wilson theorem. -/
theorem indepSetFree_franklWilsonGraph {p d : ℕ} (hp : 0 < p) :
    (franklWilsonGraph α p d).IndepSetFree ((Fintype.card α).choose (d / p) + 1) := by
  intro t ht
  set L : Finset ℕ := (range (d / p)).image (fun m => m * p + d % p) with hL
  have hLc : #L = d / p := by
    rw [hL, card_image_of_injective _ (fun a b h =>
      Nat.eq_of_mul_eq_mul_right hp (Nat.add_right_cancel h)), card_range]
  have h := Fintype.card_le_choose_of_card_inter_mem_of_lt (ι := t) (fun s => s.1.1) L
    (fun s => s.1.2) (fun i j hij => ?_) ?_
  · rw [Fintype.card_coe, ht.2, hLc] at h
    omega
  · have hne : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
    have hmod : #(i.1.1 ∩ j.1.1) % p = d % p := not_ne_iff.1 (ht.1 i.2 j.2 hne)
    have hlt : #(i.1.1 ∩ j.1.1) < d := by
      refine lt_of_le_of_ne ((card_le_card inter_subset_left).trans_eq i.1.2) fun h3 => hne ?_
      apply Subtype.ext
      have h1 : i.1.1 ∩ j.1.1 = i.1.1 :=
        eq_of_subset_of_card_le inter_subset_left (by rw [h3, i.1.2])
      have h2 : i.1.1 ∩ j.1.1 = j.1.1 :=
        eq_of_subset_of_card_le inter_subset_right (by rw [h3, j.1.2])
      rw [← h1, h2]
    have e1 := Nat.div_add_mod (#(i.1.1 ∩ j.1.1)) p
    have e2 := Nat.div_add_mod d p
    rw [hL, mem_image]
    refine ⟨#(i.1.1 ∩ j.1.1) / p, mem_range.2 ?_, ?_⟩
    · by_contra hc
      have := Nat.mul_le_mul_left p (not_lt.1 hc)
      omega
    · rw [← hmod, Nat.mul_comm]
      omega
  · intro l hl
    obtain ⟨m, hm, rfl⟩ := mem_image.1 hl
    have e2 := Nat.div_add_mod d p
    have := Nat.mul_le_mul_right p (mem_range.1 hm)
    rw [Nat.succ_mul] at this
    have : d / p * p = p * (d / p) := Nat.mul_comm _ _
    omega

private theorem sq_sub_one_eq (p : ℕ) (hp : 0 < p) : p ^ 2 - 1 = (p - 1) + p * (p - 1) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  rw [show (q + 1) ^ 2 = q + (q + 1) * q + 1 by ring]
  omega

private theorem sq_sub_one_mod (p : ℕ) (hp : 0 < p) : (p ^ 2 - 1) % p = p - 1 := by
  rw [sq_sub_one_eq p hp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private theorem sq_sub_one_div (p : ℕ) (hp : 0 < p) : (p ^ 2 - 1) / p = p - 1 := by
  rw [sq_sub_one_eq p hp, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), Nat.zero_add]

/-- **The Frankl–Wilson bound**: for every prime `p`, `C(p³, p² - 1) < R(k, k)` with
`k = C(p³, p - 1) + 1`, witnessed by `SimpleGraph.franklWilsonGraph (Fin (p ^ 3)) p (p ^ 2 - 1)`
[FranklWilson1981]. -/
theorem choose_lt_ramseyNumber_franklWilson (p : ℕ) [hp : Fact p.Prime] :
    (p ^ 3).choose (p ^ 2 - 1) <
      ramseyNumber ((p ^ 3).choose (p - 1) + 1) ((p ^ 3).choose (p - 1) + 1) := by
  have hp0 := hp.out.pos
  have h := card_lt_ramseyNumber_iff (k := (p ^ 3).choose (p - 1) + 1)
    (l := (p ^ 3).choose (p - 1) + 1) (V := {s : Finset (Fin (p ^ 3)) // #s = p ^ 2 - 1})
  rw [Fintype.card_finset_len, Fintype.card_fin] at h
  refine h.2 ⟨franklWilsonGraph (Fin (p ^ 3)) p (p ^ 2 - 1), ?_, ?_⟩
  · have hc := cliqueFree_franklWilsonGraph (α := Fin (p ^ 3)) (sq_sub_one_mod p hp0)
    rwa [Fintype.card_fin] at hc
  · have hi := indepSetFree_franklWilsonGraph (α := Fin (p ^ 3)) (d := p ^ 2 - 1) hp0
    rwa [Fintype.card_fin, sq_sub_one_div p hp0] at hi

/-- The Frankl–Wilson parameters grow superpolynomially: with `k = C(p³, p - 1) + 1`,
`k ^ c < C(p³, p² - 1)` whenever `p ≥ 6 c + 3`. The proof uses `k ≤ p ^ (3 p)` and
`(p - 1) ^ (p² - 1) ≤ C(p³, p² - 1)`. -/
private theorem pow_lt_choose_franklWilson {p c : ℕ} (hpc : 6 * c + 3 ≤ p) :
    ((p ^ 3).choose (p - 1) + 1) ^ c < (p ^ 3).choose (p ^ 2 - 1) := by
  have hp3 : 3 ≤ p := by omega
  -- `k ≤ (p³) ^ p`.
  have hk : (p ^ 3).choose (p - 1) + 1 ≤ p ^ (3 * p) := by
    have h1 := Nat.choose_le_pow (p ^ 3) (p - 1)
    have h2 : (p ^ 3) ^ (p - 1) * p ^ 3 = p ^ (3 * p) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      have : p - 1 + 1 = p := by omega
      calc 3 * (p - 1) + 3 = 3 * (p - 1 + 1) := by ring
        _ = 3 * p := by rw [this]
    have h3 : 2 ≤ p ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) p)
    have h4 : 1 ≤ (p ^ 3) ^ (p - 1) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  -- `(p - 1) ^ (p² - 1) ≤ C(p³, p² - 1)`.
  have hN : (p - 1) ^ (p ^ 2 - 1) ≤ (p ^ 3).choose (p ^ 2 - 1) := by
    set r := p ^ 2 - 1 with hr
    have hpr : r < p ^ 2 := by
      have : 0 < p ^ 2 := by positivity
      omega
    have h1 := Nat.pow_sub_le_descFactorial (p ^ 3) r
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
    have h2 : r.factorial ≤ (p ^ 2) ^ r :=
      (Nat.factorial_le_pow r).trans (Nat.pow_le_pow_left hpr.le r)
    have h3 : p ^ 2 * (p - 1) ≤ p ^ 3 + 1 - r := by
      have : p ^ 3 = p ^ 2 * (p - 1) + p ^ 2 := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt (by omega : 0 < p)
        simp only [Nat.zero_add, Nat.add_sub_cancel]
        ring
      omega
    have h4 : (p ^ 2) ^ r * (p - 1) ^ r ≤ (p ^ 2) ^ r * (p ^ 3).choose r := by
      calc (p ^ 2) ^ r * (p - 1) ^ r = (p ^ 2 * (p - 1)) ^ r := (mul_pow _ _ _).symm
        _ ≤ (p ^ 3 + 1 - r) ^ r := Nat.pow_le_pow_left h3 r
        _ ≤ r.factorial * (p ^ 3).choose r := h1
        _ ≤ (p ^ 2) ^ r * (p ^ 3).choose r := Nat.mul_le_mul_right _ h2
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)
  -- `p ^ (3 p c) ≤ (p - 1) ^ (6 p c) < (p - 1) ^ (p² - 1)`.
  have hsq : p ≤ (p - 1) ^ 2 := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp3
    simp only [show 3 + q - 1 = q + 2 by omega]
    nlinarith
  have hexp : 6 * p * c < p ^ 2 - 1 := by
    have : 6 * p * c + p * 3 ≤ p * p := by nlinarith
    have : p ^ 2 = p * p := sq p
    omega
  calc ((p ^ 3).choose (p - 1) + 1) ^ c ≤ (p ^ (3 * p)) ^ c := Nat.pow_le_pow_left hk c
    _ = p ^ (3 * p * c) := (pow_mul _ _ _).symm
    _ ≤ ((p - 1) ^ 2) ^ (3 * p * c) := Nat.pow_le_pow_left hsq _
    _ = (p - 1) ^ (6 * p * c) := by rw [← pow_mul]; ring_nf
    _ < (p - 1) ^ (p ^ 2 - 1) := Nat.pow_lt_pow_right (by omega) hexp
    _ ≤ (p ^ 3).choose (p ^ 2 - 1) := hN

/-- **Superpolynomial explicit Ramsey bound**: with `k = C(p³, p - 1) + 1`, `k ^ c < R(k, k)` for
every prime `p ≥ 6 c + 3`, witnessed by the Frankl–Wilson graph [FranklWilson1981]. -/
theorem pow_lt_ramseyNumber_franklWilson {p c : ℕ} [Fact p.Prime] (hpc : 6 * c + 3 ≤ p) :
    ((p ^ 3).choose (p - 1) + 1) ^ c <
      ramseyNumber ((p ^ 3).choose (p - 1) + 1) ((p ^ 3).choose (p - 1) + 1) :=
  (pow_lt_choose_franklWilson hpc).trans (choose_lt_ramseyNumber_franklWilson p)

end SimpleGraph

end
