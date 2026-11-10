/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.DeltaMatroid.Basic
public import Complexity.Foundations.Data.BitString.Hamming
public import Mathlib.Logic.Relation

/-!
# Transport and feasible moves in delta-matroids

Twists and coordinate equivalences preserve the one-sided exchange contract and evenness.
Feasible tuples of an even delta-matroid are connected by two-coordinate flips; each move
toward a fixed feasible target reduces the Hamming distance by exactly two.

The four-coordinate consequences isolate the exchange arguments in the proof of Lemma 35,
p. 17 of arXiv:1602.03124v6 [KazdaKolmogorovRolinek2018], reused in Lemma 37, pp. 18–19.
They are statements about one relation, not the paper's full DAG lemmas. The four coordinates
are pairwise distinct and the relation is even. The transport and connectivity proofs here
are direct arguments, not claims to formalize additional named results of that paper.

## Main results

* `IsDeltaMatroid.twist`, `IsDeltaMatroid.reindex`: transport of exchange.
* `IsEvenDeltaMatroid.twist`, `IsEvenDeltaMatroid.reindex`: transport of evenness.
* `IsEvenDeltaMatroid.exists_exchange_hammingDist`: a feasible move exactly two closer.
* `IsEvenDeltaMatroid.connected`: connectivity by feasible two-coordinate flips.
* `IsEvenDeltaMatroid.mem_flipOn_four_of_not_mem_cross`: a forced four-coordinate flip.
* `IsEvenDeltaMatroid.mem_pair_or_mem_cross_of_mem_flipOn_four`: a feasible pair alternative.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {R : Set (ι → Bool)} {x y : ι → Bool}

/-- Flips at two sets commute, even when the sets overlap. -/
theorem flipOn_comm (S T : Finset ι) (x : ι → Bool) :
    flipOn S (flipOn T x) = flipOn T (flipOn S x) := by
  funext i
  by_cases hi : i ∈ S <;> by_cases hj : i ∈ T <;> simp [flipOn, hi, hj]

/-- Twisting a relation by a fixed set of coordinates preserves delta-matroid exchange. -/
theorem IsDeltaMatroid.twist (hR : IsDeltaMatroid R) (S : Finset ι) :
    IsDeltaMatroid (flipOn S ⁻¹' R) where
  nonempty := by
    obtain ⟨x, hx⟩ := hR.nonempty
    exact ⟨flipOn S x, by simpa using hx⟩
  exchange := by
    intro x y hx hy i hi
    have hi' : flipOn S x i ≠ flipOn S y i := by
      by_cases h : i ∈ S <;> simpa [flipOn, h] using hi
    obtain ⟨j, hj, hf⟩ := hR.exchange hx hy hi'
    refine ⟨j, ?_, ?_⟩
    · by_cases h : j ∈ S <;> simpa [flipOn, h] using hj
    · change flipOn S (flipOn {i, j} x) ∈ R
      rwa [flipOn_comm]

/-- Renaming coordinates by an equivalence preserves delta-matroid exchange. -/
theorem IsDeltaMatroid.reindex (hR : IsDeltaMatroid R) (e : ι ≃ κ) :
    IsDeltaMatroid {y | (fun i => y (e i)) ∈ R} where
  nonempty := by
    obtain ⟨x, hx⟩ := hR.nonempty
    exact ⟨fun k => x (e.symm k), by simpa using hx⟩
  exchange := by
    intro x y hx hy k hk
    obtain ⟨j, hj, hf⟩ := hR.exchange hx hy (i := e.symm k) (by simpa using hk)
    refine ⟨e j, hj, ?_⟩
    change (fun i => flipOn {k, e j} x (e i)) ∈ R
    have he : ({k, e j} : Finset κ) = ({e.symm k, j} : Finset ι).map e.toEmbedding := by
      simp
    rw [he]
    have hr : (fun i => flipOn (({e.symm k, j} : Finset ι).map e.toEmbedding) x (e i)) =
        flipOn {e.symm k, j} (fun i => x (e i)) := by
      convert flipOn_reindex e x {e.symm k, j} using 1
      funext i
      exact congrFun (flipOn_congr_decidableEq _ _) (e i)
    rw [hr]
    exact hf

variable [Fintype ι]

/-- The parity change caused by a twist is independent of the tuple. -/
theorem parityOn_univ_flipOn (S : Finset ι) (x : ι → Bool) :
    parityOn univ (flipOn S x) = (parityOn univ x ^^ decide (S.card % 2 = 1)) := by
  induction S using Finset.induction with
  | empty => simp
  | @insert i S hi ih =>
    rw [flipOn_insert hi, parityOn_univ_flipOn_singleton, ih, card_insert_of_notMem hi]
    rcases Nat.mod_two_eq_zero_or_one S.card with h | h <;>
      cases parityOn univ x <;> simp [Nat.add_mod, h]

/-- Twists preserve evenness; they may interchange the two parity classes. -/
theorem IsEvenDeltaMatroid.twist (hR : IsEvenDeltaMatroid R) (S : Finset ι) :
    IsEvenDeltaMatroid (flipOn S ⁻¹' R) where
  isDeltaMatroid := hR.isDeltaMatroid.twist S
  parity_eq := by
    intro x y hx hy
    have h := hR.parity_eq hx hy
    simpa only [parityOn_univ_flipOn, Bool.xor_left_inj] using h

omit [DecidableEq ι] [DecidableEq κ] in
/-- Total parity is unchanged by a bijective renaming of coordinates. -/
theorem parityOn_univ_reindex [Fintype κ] (e : ι ≃ κ) (x : κ → Bool) :
    parityOn univ (fun i => x (e i)) = parityOn univ x := by
  simp only [parityOn_eq_sum]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Renaming coordinates by an equivalence preserves evenness. -/
theorem IsEvenDeltaMatroid.reindex [Fintype κ] (hR : IsEvenDeltaMatroid R) (e : ι ≃ κ) :
    IsEvenDeltaMatroid {y | (fun i => y (e i)) ∈ R} where
  isDeltaMatroid := hR.isDeltaMatroid.reindex e
  parity_eq := by
    intro x y hx hy
    simpa only [parityOn_univ_reindex] using hR.parity_eq hx hy

/-- Correcting two distinct disagreeing coordinates reduces the distance by exactly two. -/
theorem hammingDist_flipOn_pair_add_two {i j : ι} (hij : i ≠ j)
    (hi : x i ≠ y i) (hj : x j ≠ y j) :
    hammingDist (flipOn {i, j} x) y + 2 = hammingDist x y := by
  have hj' : flipOn {i} x j ≠ y j := by
    simpa only [flipOn_singleton_of_ne hij.symm] using hj
  have h₁ := hammingDist_flip_eq_add_one (flipOn {i} x) y i (by
    rw [flipOn_singleton_self]
    cases hx : x i <;> cases hy : y i <;> simp_all)
  have h₂ := hammingDist_flip_eq_add_one (flipOn {j} (flipOn {i} x)) y j (by
    rw [flipOn_singleton_self]
    cases hx : flipOn {i} x j <;> cases hy : y j <;> simp_all)
  rw [flipOn_flipOn] at h₁ h₂
  rw [flipOn_insert (by simpa using hij), flipOn_comm {i} {j}]
  omega

/-- Exchange makes a feasible step exactly two coordinates closer to a feasible target. -/
theorem IsEvenDeltaMatroid.exists_exchange_hammingDist (hR : IsEvenDeltaMatroid R)
    (hx : x ∈ R) (hy : y ∈ R) (hne : x ≠ y) :
    ∃ i j, i ≠ j ∧ x i ≠ y i ∧ x j ≠ y j ∧ flipOn {i, j} x ∈ R ∧
      hammingDist (flipOn {i, j} x) y + 2 = hammingDist x y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨j, hji, hj, hf⟩ := hR.exchange hx hy hi
  exact ⟨i, j, hji.symm, hi, hj, hf, hammingDist_flipOn_pair_add_two hji.symm hi hj⟩

/-- Any two feasible tuples are joined by feasible two-coordinate flips.
Both endpoints of every step lie in the relation. -/
theorem IsEvenDeltaMatroid.connected (hR : IsEvenDeltaMatroid R)
    (hx : x ∈ R) (hy : y ∈ R) :
    Relation.ReflTransGen (fun u v => u ∈ R ∧ v ∈ R ∧
      ∃ i j, i ≠ j ∧ v = flipOn {i, j} u) x y := by
  generalize hn : hammingDist x y = n
  induction n using Nat.strong_induction_on generalizing x with
  | ind n ih =>
    by_cases hxy : x = y
    · subst y
      exact .refl
    · obtain ⟨i, j, hij, _, _, hf, hd⟩ := hR.exists_exchange_hammingDist hx hy hxy
      have hlt : hammingDist (flipOn {i, j} x) y < n := by omega
      exact (Relation.ReflTransGen.single ⟨hx, hf, i, j, hij, rfl⟩).trans
        (ih _ hlt hf rfl)

/-- The four-coordinate exchange consequence used for property (5) in the proof of
Lemma 35 of [KazdaKolmogorovRolinek2018], p. 17, and reused in Lemma 37.
Here `a,b,c,d` correspond to the paper's `u,v,x,y`. The two forbidden cross-pairs force
the four-coordinate flip. The feasible base tuple is not needed for this local consequence. -/
theorem IsEvenDeltaMatroid.mem_flipOn_four_of_not_mem_cross
    (hR : IsEvenDeltaMatroid R) {a b c d : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habx : flipOn {a, b} x ∈ R) (hcdx : flipOn {c, d} x ∈ R)
    (hacx : flipOn {a, c} x ∉ R) (hadx : flipOn {a, d} x ∉ R) :
    flipOn {a, b, c, d} x ∈ R := by
  obtain ⟨j, hja, hj, hf⟩ := hR.exchange hcdx habx (i := a) (by
    simp [flipOn, hab, hac, had])
  have hmem : j = a ∨ j = b ∨ j = c ∨ j = d := by
    by_contra h
    push Not at h
    simp [flipOn, h.1, h.2.1, h.2.2.1, h.2.2.2] at hj
  rcases hmem with h | h | h | h
  · exact (hja h).elim
  · subst j
    convert hf using 1
    funext k
    by_cases hka : k = a <;> by_cases hkb : k = b <;>
      by_cases hkc : k = c <;> by_cases hkd : k = d <;> simp_all [flipOn]
  · subst j
    apply False.elim <| hadx ?_
    convert hf using 1
    funext k
    by_cases hka : k = a <;> by_cases hkc : k = c <;>
      by_cases hkd : k = d <;> simp_all [flipOn]
  · subst j
    apply False.elim <| hacx ?_
    convert hf using 1
    funext k
    by_cases hka : k = a <;> by_cases hkc : k = c <;>
      by_cases hkd : k = d <;> simp_all [flipOn]

/-- The four-coordinate exchange alternative used for the no-shortcuts argument in the proof
of Lemma 35 of [KazdaKolmogorovRolinek2018], p. 17, and reused in Lemma 37.
Exchange at `b` from the four-coordinate flip toward the feasible base gives one of these
three pairs; no simultaneous exchange conclusion is asserted. -/
theorem IsEvenDeltaMatroid.mem_pair_or_mem_cross_of_mem_flipOn_four
    (hR : IsEvenDeltaMatroid R) {a b c d : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hx : x ∈ R) (hf : flipOn {a, b, c, d} x ∈ R) :
    flipOn {c, d} x ∈ R ∨ flipOn {a, c} x ∈ R ∨ flipOn {a, d} x ∈ R := by
  obtain ⟨j, hjb, hj, hflip⟩ := hR.exchange hf hx (i := b) (by simp [flipOn])
  have hmem : j = a ∨ j = b ∨ j = c ∨ j = d := by
    by_contra h
    push Not at h
    simp [flipOn, h.1, h.2.1, h.2.2.1, h.2.2.2] at hj
  rcases hmem with h | h | h | h
  · subst j
    left
    convert hflip using 1
    funext k
    by_cases hka : k = a <;> by_cases hkb : k = b <;>
      by_cases hkc : k = c <;> by_cases hkd : k = d <;> simp_all [flipOn]
  · exact (hjb h).elim
  · subst j
    right; right
    convert hflip using 1
    funext k
    by_cases hka : k = a <;> by_cases hkb : k = b <;>
      by_cases hkc : k = c <;> by_cases hkd : k = d <;> simp_all [flipOn]
  · subst j
    right; left
    convert hflip using 1
    funext k
    by_cases hka : k = a <;> by_cases hkb : k = b <;>
      by_cases hkc : k = c <;> by_cases hkd : k = d <;> simp_all [flipOn]

end Cslib.BitString
