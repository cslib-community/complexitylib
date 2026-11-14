/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lautemann's covering lemma

Let `S` be a subset of a finite group `G`. If `S` is large, a few shifts of `S` cover `G`; if `S`
is small, they do not. Precisely, if `|G| |G \ S| ^ k < |G| ^ k`, then some `k` elements `u i`
satisfy `∀ g, ∃ i, g * u i ∈ S` (`exists_forall_exists_mul_mem_of_card_mul_card_compl_pow_lt`),
by the union bound over `g` for uniformly random shifts (`card_filter_exists_forall_mul_mem_le`).
Conversely, if `k |S| < |G|`, then no `k` shifts do (`exists_forall_mul_notMem_of_mul_card_lt`),
as the `k` translates have at most `k |S|` elements in all. Each of these statements has an
additive version, with `g + u i` in place of `g * u i`.

On strings of `m` bits, with xor as the group operation, this is the combinatorial heart of the
Sipser–Gács–Lautemann theorem `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`: if `A` decides `L` with error at most `1 / (2 m)`
over random strings of `m` bits, then `x ∈ L` iff some `m` shifts `u i` make `A x (r + u i)` true
for one `i` at every string `r` (`BitString.mem_iff_exists_forall_exists`), and iff for all `m`
shifts some `r` makes every `A x (r + u i)` true (`BitString.mem_iff_forall_exists_forall`).
The bound `m ≥ 2` is needed: at `m = 1`, an error of `1 / 2` carries no information.

## Main results

* `Cslib.card_filter_exists_forall_mul_mem_le`, `Cslib.card_filter_exists_mul_mem_le`: union-bound
  cardinality bounds for shift tuples and shifted sets.
* `Cslib.exists_forall_exists_mul_mem_of_card_mul_card_compl_pow_lt`: the union-bound form of the
  covering lemma; `Cslib.exists_forall_exists_mul_mem_of_mul_card_compl_le` is its density form.
* `Cslib.exists_forall_mul_notMem_of_mul_card_lt`: the converse, by counting;
  `Cslib.exists_forall_mul_notMem_of_mul_card_le` is its density form.
* `Cslib.BitString.exists_forall_exists_add_mem_of_two_pow_mul_card_compl_le`,
  `Cslib.BitString.exists_forall_add_notMem_of_two_pow_mul_card_le`,
  `Cslib.BitString.two_mul_card_filter_exists_add_mem_le`,
  `Cslib.BitString.two_mul_card_filter_exists_forall_add_mem_le`: the two claims in Arora and
  Barak's proof of the Sipser–Gács theorem and their half-density soundness bounds, for sets of
  strings of density `1 - 2 ^ (-n)` and `2 ^ (-n)`.
* `Cslib.BitString.mem_iff_exists_forall_exists`, `Cslib.BitString.mem_iff_forall_exists_forall`:
  the `∃ ∀ ∃` and `∀ ∃ ∀` forms of a language decided with error at most `1 / (2 m)`.

## References

* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.5.2][AroraBarak09]
-/

@[expose] public section

namespace Cslib

open Finset

section Group

variable {G : Type*} [Group G] [Fintype G]

/-- For any subset `S` of a finite group `G`, at most `|G| |S| ^ k` tuples `u : Fin k → G` have some
`g : G` with `g * u i ∈ S` for every `i`. -/
@[to_additive
/-- For any subset `S` of a finite additive group `G`, at most `|G| |S| ^ k` tuples `u : Fin k → G`
have some `g : G` with `g + u i ∈ S` for every `i`. -/]
theorem card_filter_exists_forall_mul_mem_le [DecidableEq G] (S : Finset G) (k : ℕ) :
    #{u : Fin k → G | ∃ g : G, ∀ i, g * u i ∈ S} ≤ Fintype.card G * #S ^ k := by
  let bad (g : G) : Finset (Fin k → G) := univ.filter fun u => ∀ i, g * u i ∈ S
  have hsub : (univ.filter fun u : Fin k → G => ∃ g : G, ∀ i, g * u i ∈ S) ⊆
      univ.biUnion bad := fun u hu => by
    obtain ⟨g, hg⟩ := (mem_filter.1 hu).2
    exact mem_biUnion.2 ⟨g, mem_univ _, mem_filter.2 ⟨mem_univ _, hg⟩⟩
  have hbad (g : G) : #(bad g) = #S ^ k := by
    have hg : Fintype.card {x : G // g * x ∈ S} = #S := by
      rw [Fintype.card_subtype]
      exact card_nbij' (g * ·) (g⁻¹ * ·) (fun _ => by simp) (fun _ => by simp)
        (fun _ _ => by simp) (fun _ _ => by simp)
    calc #(bad g)
        = Fintype.card {u : Fin k → G // ∀ i, g * u i ∈ S} := by simp [bad, Fintype.card_subtype]
      _ = Fintype.card (Fin k → {x : G // g * x ∈ S}) :=
          Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : Fin k) (x : G) => g * x ∈ S))
      _ = #S ^ k := by simp [hg]
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [sum_const_nat fun g _ => hbad g, card_univ]

/-- **Lautemann's covering lemma**, union-bound form: if `S` is a subset of a finite group `G`
with `|G| |G \ S| ^ k < |G| ^ k`, then some `k` shifts `u i` carry every `g : G` into `S` by right
multiplication, `g * u i ∈ S`. -/
@[to_additive exists_forall_exists_add_mem_of_card_mul_card_compl_pow_lt
/-- **Lautemann's covering lemma**, union-bound form: if `S` is a subset of a finite additive
group `G` with `|G| |G \ S| ^ k < |G| ^ k`, then some `k` shifts `u i` carry every `g : G` into `S`
by addition, `g + u i ∈ S`. -/]
theorem exists_forall_exists_mul_mem_of_card_mul_card_compl_pow_lt [DecidableEq G] (S : Finset G)
    {k : ℕ}
    (h : Fintype.card G * #Sᶜ ^ k < Fintype.card G ^ k) :
    ∃ u : Fin k → G, ∀ g, ∃ i, g * u i ∈ S := by
  have hlt : #{u : Fin k → G | ∃ g : G, ∀ i, g * u i ∈ Sᶜ} < #(univ : Finset (Fin k → G)) := by
    simpa [card_univ] using (card_filter_exists_forall_mul_mem_le Sᶜ k).trans_lt h
  obtain ⟨u, -, hu⟩ := exists_mem_notMem_of_card_lt_card hlt
  exact ⟨u, by simpa using hu⟩

/-- **Lautemann's covering lemma**, density form: if `S` misses at most a `1 / q` fraction of the
finite group `G`, that is `q |G \ S| ≤ |G|`, and `|G| < q ^ k`, then some `k` shifts `u i` carry
every `g : G` into `S` by right multiplication, `g * u i ∈ S`. -/
@[to_additive exists_forall_exists_add_mem_of_mul_card_compl_le
/-- **Lautemann's covering lemma**, density form: if `S` misses at most a `1 / q` fraction of the
finite additive group `G`, that is `q |G \ S| ≤ |G|`, and `|G| < q ^ k`, then some `k` shifts `u i`
carry every `g : G` into `S` by addition, `g + u i ∈ S`. -/]
theorem exists_forall_exists_mul_mem_of_mul_card_compl_le [DecidableEq G] (S : Finset G) {q k : ℕ}
    (hS : q * #Sᶜ ≤ Fintype.card G) (hk : Fintype.card G < q ^ k) :
    ∃ u : Fin k → G, ∀ g, ∃ i, g * u i ∈ S := by
  refine exists_forall_exists_mul_mem_of_card_mul_card_compl_pow_lt S
    (Nat.lt_of_mul_lt_mul_left (a := q ^ k) ?_)
  calc q ^ k * (Fintype.card G * #Sᶜ ^ k) = Fintype.card G * (q * #Sᶜ) ^ k := by ring
    _ ≤ Fintype.card G * Fintype.card G ^ k := by gcongr
    _ < q ^ k * Fintype.card G ^ k := Nat.mul_lt_mul_of_pos_right hk (pow_pos Fintype.card_pos k)

/-- For any `k` shifts `u i` of a subset `S` of a finite group `G`, at most `k |S|` elements `g : G`
satisfy `g * u i ∈ S` for some `i`. -/
@[to_additive
/-- For any `k` shifts `u i` of a subset `S` of a finite additive group `G`, at most `k |S|`
elements `g : G` satisfy `g + u i ∈ S` for some `i`. -/]
theorem card_filter_exists_mul_mem_le [DecidableEq G] (S : Finset G) {k : ℕ} (u : Fin k → G) :
    #{g : G | ∃ i, g * u i ∈ S} ≤ k * #S := by
  have hsub : (univ.filter fun g : G => ∃ i, g * u i ∈ S) ⊆
      univ.biUnion fun i => {g | g * u i ∈ S} := fun g hg => by
    obtain ⟨i, hi⟩ := (mem_filter.1 hg).2
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, hi⟩⟩
  have hcard (i : Fin k) : #{g | g * u i ∈ S} = #S :=
    card_nbij' (· * u i) (· * (u i)⁻¹) (fun _ => by simp) (fun _ => by simp) (fun _ _ => by simp)
      (fun _ _ => by simp)
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [sum_const_nat fun i _ => hcard i, card_univ, Fintype.card_fin]

/-- **The converse of Lautemann's covering lemma**: if `k |S| < |G|`, then for any `k` shifts
`u i` of the finite group `G`, some `g : G` has `g * u i ∉ S` for every `i`. -/
@[to_additive exists_forall_add_notMem_of_mul_card_lt
/-- **The converse of Lautemann's covering lemma**: if `k |S| < |G|`, then for any `k` shifts
`u i` of the finite additive group `G`, some `g : G` has `g + u i ∉ S` for every `i`. -/]
theorem exists_forall_mul_notMem_of_mul_card_lt (S : Finset G) {k : ℕ}
    (h : k * #S < Fintype.card G) (u : Fin k → G) : ∃ g, ∀ i, g * u i ∉ S := by
  classical
  have hlt : #{g : G | ∃ i, g * u i ∈ S} < #(univ : Finset G) := by
    simpa [card_univ] using (card_filter_exists_mul_mem_le S u).trans_lt h
  obtain ⟨g, -, hg⟩ := exists_mem_notMem_of_card_lt_card hlt
  exact ⟨g, by simpa using hg⟩

/-- **The converse of Lautemann's covering lemma**, density form: if `S` is at most a `1 / q`
fraction of the finite group `G`, that is `q |S| ≤ |G|`, and `k < q`, then for any `k` shifts
`u i`, some `g : G` has `g * u i ∉ S` for every `i`. -/
@[to_additive exists_forall_add_notMem_of_mul_card_le
/-- **The converse of Lautemann's covering lemma**, density form: if `S` is at most a `1 / q`
fraction of the finite additive group `G`, that is `q |S| ≤ |G|`, and `k < q`, then for any `k`
shifts `u i`, some `g : G` has `g + u i ∉ S` for every `i`. -/]
theorem exists_forall_mul_notMem_of_mul_card_le (S : Finset G) {q k : ℕ}
    (hS : q * #S ≤ Fintype.card G) (hk : k < q) (u : Fin k → G) : ∃ g, ∀ i, g * u i ∉ S := by
  refine exists_forall_mul_notMem_of_mul_card_lt S ?_ u
  rcases (#S).eq_zero_or_pos with h | h
  · simpa [h] using Fintype.card_pos
  · exact (Nat.mul_lt_mul_of_pos_right hk h).trans_le hS

end Group

section BitString

variable {m : ℕ}

/-- **Lautemann's covering lemma** for bit strings, with xor as the group operation
[Arora and Barak, Section 7.5.2][AroraBarak09]: if a set `S` of strings of `m` bits misses at most
a `2 ^ (-n)` fraction of them, that is `2 ^ n |Sᶜ| ≤ 2 ^ m`, and `m < n k`, then some `k` shifts
`u i` carry every string `r` into `S`, `r + u i ∈ S`. -/
theorem BitString.exists_forall_exists_add_mem_of_two_pow_mul_card_compl_le {n k : ℕ}
    (S : Finset (BitString m)) (hS : 2 ^ n * #Sᶜ ≤ 2 ^ m) (hk : m < n * k) :
    ∃ u : Fin k → BitString m, ∀ r, ∃ i, r + u i ∈ S := by
  refine exists_forall_exists_add_mem_of_mul_card_compl_le S (q := 2 ^ n)
    (by rwa [BitString.card]) ?_
  rw [BitString.card, ← pow_mul]
  exact Nat.pow_lt_pow_right (by norm_num) hk

/-- **The converse of Lautemann's covering lemma** for bit strings, with xor as the group
operation [Arora and Barak, Section 7.5.2][AroraBarak09]: if a set `S` of strings of `m` bits is at
most a `2 ^ (-n)` fraction of them, that is `2 ^ n |S| ≤ 2 ^ m`, and `k < 2 ^ n`, then for any `k`
shifts `u i`, some string `r` has `r + u i ∉ S` for every `i`. -/
theorem BitString.exists_forall_add_notMem_of_two_pow_mul_card_le {n k : ℕ}
    (S : Finset (BitString m)) (hS : 2 ^ n * #S ≤ 2 ^ m) (hk : k < 2 ^ n)
    (u : Fin k → BitString m) : ∃ r, ∀ i, r + u i ∉ S :=
  exists_forall_add_notMem_of_mul_card_le S (by rwa [BitString.card]) hk u

/-- If `S` is at most a `2 ^ (-n)` fraction of the strings of `m` bits and `2 * k ≤ 2 ^ n`, then for
any `k` shifts `u i`, at most half of the strings `r` have `r + u i ∈ S` for some `i`. -/
theorem BitString.two_mul_card_filter_exists_add_mem_le {n k : ℕ} (S : Finset (BitString m))
    (hS : 2 ^ n * #S ≤ 2 ^ m) (hk : 2 * k ≤ 2 ^ n) (u : Fin k → BitString m) :
    2 * #{r : BitString m | ∃ i, r + u i ∈ S} ≤ 2 ^ m := by
  refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < 2 ^ n)
  calc 2 ^ n * (2 * #{r : BitString m | ∃ i, r + u i ∈ S})
      ≤ 2 ^ n * (2 * (k * #S)) := by gcongr; exact card_filter_exists_add_mem_le S u
    _ = 2 * k * (2 ^ n * #S) := by ring
    _ ≤ 2 ^ n * 2 ^ m := Nat.mul_le_mul hk hS

/-- If `S` is at most a `2 ^ (-n)` fraction of the strings of `m` bits and `m < n * k`, then at most
half of the `k`-tuples of shifts `u : Fin k → BitString m` have some string `r` with
`r + u i ∈ S` for every `i`. -/
theorem BitString.two_mul_card_filter_exists_forall_add_mem_le {n k : ℕ} (S : Finset (BitString m))
    (hS : 2 ^ n * #S ≤ 2 ^ m) (hk : m < n * k) :
    2 * #{u : Fin k → BitString m | ∃ r : BitString m, ∀ i, r + u i ∈ S} ≤
      2 ^ (k * m) := by
  have hpow : 2 * 2 ^ m ≤ (2 ^ n) ^ k := by
    rw [← pow_succ', ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hk
  refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < (2 ^ n) ^ k)
  calc (2 ^ n) ^ k * (2 * #{u : Fin k → BitString m | ∃ r : BitString m, ∀ i, r + u i ∈ S})
      ≤ (2 ^ n) ^ k * (2 * (Fintype.card (BitString m) * #S ^ k)) := by
        gcongr
        exact card_filter_exists_forall_add_mem_le S k
    _ = 2 * 2 ^ m * (2 ^ n * #S) ^ k := by
        rw [BitString.card]
        ring
    _ ≤ (2 ^ n) ^ k * (2 ^ m) ^ k :=
        Nat.mul_le_mul hpow (Nat.pow_le_pow_left hS k)
    _ = (2 ^ n) ^ k * 2 ^ (k * m) := by rw [← pow_mul 2 m k, Nat.mul_comm m k]

private theorem two_pow_lt_two_mul_pow (hm : 2 ≤ m) : 2 ^ m < (2 * m) ^ m := by
  rw [mul_pow]
  exact lt_mul_of_one_lt_right (by positivity) (Nat.one_lt_pow (by omega) (by omega))

variable {α : Type*} {L : Set α} {A : α → BitString m → Bool}

/-- **The finite core of the Sipser–Gács–Lautemann theorem**, `∃ ∀ ∃` form
([Lautemann][Lautemann1983], [Arora and Barak, Theorem 7.15][AroraBarak09]): let `A x r` decide
`x ∈ L` with error at most `1 / (2 m)` over the strings `r` of `m ≥ 2` bits, that is, for each `x`,
it is wrong for at most `2 ^ m / (2 m)` strings `r`. Then `x ∈ L` iff there are `m` shifts `u i`
such that, for every string `r`, `A x (r + u i)` holds for some `i`, where `+` is xor. -/
theorem BitString.mem_iff_exists_forall_exists (hm : 2 ≤ m)
    (hmem : ∀ x ∈ L, 2 * m * #{r | A x r = false} ≤ 2 ^ m)
    (hnotMem : ∀ x ∉ L, 2 * m * #{r | A x r = true} ≤ 2 ^ m) (x : α) :
    x ∈ L ↔ ∃ u : Fin m → BitString m, ∀ r, ∃ i, A x (r + u i) = true := by
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := exists_forall_exists_add_mem_of_mul_card_compl_le {r | A x r = true}
      (q := 2 * m) (k := m) (by simpa [compl_filter, BitString.card] using hmem x hx)
      (by rw [BitString.card]; exact two_pow_lt_two_mul_pow hm)
    exact ⟨u, fun r => by simpa using hu r⟩
  · rintro ⟨u, hu⟩
    by_contra hx
    obtain ⟨r, hr⟩ := exists_forall_add_notMem_of_mul_card_le {r | A x r = true} (q := 2 * m)
      (by rw [BitString.card]; exact hnotMem x hx) (by omega) u
    obtain ⟨i, hi⟩ := hu r
    exact hr i (mem_filter.2 ⟨mem_univ _, hi⟩)

/-- **The finite core of the Sipser–Gács–Lautemann theorem**, `∀ ∃ ∀` form
([Lautemann][Lautemann1983], [Arora and Barak, Theorem 7.15][AroraBarak09]): let `A x r` decide
`x ∈ L` with error at most `1 / (2 m)` over the strings `r` of `m ≥ 2` bits, that is, for each `x`,
it is wrong for at most `2 ^ m / (2 m)` strings `r`. Then `x ∈ L` iff for all `m` shifts `u i`
there is a string `r` such that `A x (r + u i)` holds for every `i`, where `+` is xor. -/
theorem BitString.mem_iff_forall_exists_forall (hm : 2 ≤ m)
    (hmem : ∀ x ∈ L, 2 * m * #{r | A x r = false} ≤ 2 ^ m)
    (hnotMem : ∀ x ∉ L, 2 * m * #{r | A x r = true} ≤ 2 ^ m) (x : α) :
    x ∈ L ↔ ∀ u : Fin m → BitString m, ∃ r, ∀ i, A x (r + u i) = true := by
  have h := mem_iff_exists_forall_exists (L := Lᶜ) (A := fun x r => !A x r) hm
    (by simpa using hnotMem) (by simpa using hmem) x
  rw [← not_iff_not, ← Set.mem_compl_iff, h]
  simp

end BitString

end Cslib
