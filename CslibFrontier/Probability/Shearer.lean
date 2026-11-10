/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Entropy
import CslibFrontier.Probability.Divergence

/-!
# Shearer's lemma and Han's inequality

Let `P` be the law of a tuple `X = (X_i)_{i ∈ ι}` of random variables with finite alphabets, and
for a finite set `s` of coordinates write `X_s` for the restriction to `s`, whose law is
`P.map s.restrict`. For a family `S j`, `j ∈ J`, of coordinate sets covering every coordinate at
least `k` times, **Shearer's lemma** states `k H(X) ≤ ∑ j, H(X_{S j})`. Taking the sets
`univ.erase i` gives **Han's inequality** `(n - 1) H(X) ≤ ∑ i, H(X_{-i})`, and taking singletons
gives the subadditivity `H(X) ≤ ∑ i, H(X_i)`. The form of Han's inequality proved here compares
only subsets of sizes `n - 1` and `n`; it is the last step of the monotone chain of averages in
[CoverThomas2006], Theorem 17.6.1, not the full chain.

The proof orders the coordinates and uses the chain rule
`H(X_s) = ∑ i ∈ s, H(X_i | X_{j ∈ s, j < i})` together with the fact that conditioning on more
coordinates cannot increase entropy (`conditionalEntropy_map_fst_ge`).

Applied to the uniform distribution on a finite set of tuples, Shearer's lemma bounds its size
by the sizes of its projections: `|A| ^ k ≤ ∏ j, |A restricted to S j|`. For `α i = Bool` this
is the original statement of Chung, Graham, Frankl and Shearer about families of sets.

## Main results

* `Cslib.Probability.PMF.entropy_map_restrict_eq_sum`: the chain rule over ordered coordinates.
* `Cslib.Probability.PMF.mul_entropy_le_sum_entropy_map_restrict`: Shearer's lemma.
* `Cslib.Probability.PMF.sub_one_mul_entropy_le_sum_entropy_map_restrict_erase`: Han's
  inequality.
* `Cslib.Probability.PMF.entropy_le_sum_entropy_map_eval`: subadditivity of entropy.
* `Cslib.Finset.card_pow_le_prod_card_image_restrict`: Shearer's lemma for counting.

## References

* [F. R. K. Chung, R. L. Graham, P. Frankl, J. B. Shearer, *Some intersection theorems for
  ordered sets and graphs*][ChungGrahamFranklShearer1986]
* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006],
  Theorems 2.5.1 (chain rule), 2.6.6 (independence bound on entropy) and 17.6.1 (Han's
  inequality, of which only the comparison of sizes `n - 1` and `n` is formalized).
-/

@[expose] public section

open Finset

namespace Cslib.Probability.PMF

variable {ι : Type*} {α : ι → Type*} [∀ i, Finite (α i)]

/-- Conditioning a coordinate on a larger set of coordinates cannot increase its entropy. -/
theorem conditionalEntropy_map_restrict_le (P : PMF (∀ i, α i)) {s t : Finset ι}
    (hst : s ⊆ t) (i : ι) :
    conditionalEntropy (P.map fun x => (t.restrict x, x i)) ≤
      conditionalEntropy (P.map fun x => (s.restrict x, x i)) := by
  have h := conditionalEntropy_map_fst_ge (P.map fun x => (t.restrict x, x i))
    (Finset.restrict₂ hst)
  rwa [PMF.map_comp] at h

/-- Restricting a tuple to `insert a s` records exactly its restriction to `s` and its value at
`a`, when `a ∉ s`. -/
private theorem entropy_map_restrict_insert [DecidableEq ι] (P : PMF (∀ i, α i))
    {a : ι} {s : Finset ι} (ha : a ∉ s) :
    entropy (P.map (insert a s).restrict) =
      entropy (P.map s.restrict) + conditionalEntropy (P.map fun x => (s.restrict x, x a)) := by
  let split (y : ∀ i : ↥(insert a s), α i) : (∀ i : ↥s, α i) × α a :=
    (fun i => y ⟨i, mem_insert_of_mem i.2⟩, y ⟨a, mem_insert_self a s⟩)
  have hsplit : Function.Injective split := by
    intro y z hyz
    funext ⟨i, hi⟩
    rcases mem_insert.mp hi with rfl | hi
    · exact congrArg Prod.snd hyz
    · exact congrFun (congrArg Prod.fst hyz) ⟨i, hi⟩
  have hmap : P.map (fun x => (s.restrict x, x a)) = (P.map (insert a s).restrict).map split := by
    rw [PMF.map_comp]; rfl
  have hfst : (P.map fun x => (s.restrict x, x a)).map Prod.fst = P.map s.restrict := by
    rw [PMF.map_comp]; rfl
  rw [conditionalEntropy, hfst, hmap, entropy_map_of_injective _ hsplit]
  ring

/-- **The chain rule** over linearly ordered coordinates ([CoverThomas2006], Theorem 2.5.1): the
entropy of the restriction to `s` is the sum, over `i ∈ s`, of the entropy of `X_i` given the
earlier coordinates of `s`. -/
theorem entropy_map_restrict_eq_sum [LinearOrder ι] (P : PMF (∀ i, α i)) (s : Finset ι) :
    entropy (P.map s.restrict) =
      ∑ i ∈ s, conditionalEntropy (P.map fun x => ((s.filter (· < i)).restrict x, x i)) := by
  induction s using Finset.induction_on_max with
  | empty =>
    rw [sum_empty]
    apply entropy_eq_zero_of_subsingleton_support
    intro y _ z _
    funext i
    exact absurd i.2 (notMem_empty _)
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [entropy_map_restrict_insert P ha, sum_insert ha, ih, add_comm]
    have hself : (insert a s).filter (· < a) = s := by
      ext i
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hi, hia⟩
        · exact absurd hia (lt_irrefl _)
        · exact hi
      · intro hi
        exact ⟨Or.inr hi, hlt i hi⟩
    rw [hself]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hfilter : (insert a s).filter (· < i) = s.filter (· < i) := by
      rw [filter_insert, ite_eq_right_iff.mpr fun h => absurd h (not_lt.mpr (hlt i hi).le)]
    rw [hfilter]

/-- The restriction of a tuple to all coordinates carries the tuple's entropy. -/
theorem entropy_map_restrict_univ [Fintype ι] (P : PMF (∀ i, α i)) :
    entropy (P.map (univ : Finset ι).restrict) = entropy P := by
  apply entropy_map_of_injective
  intro x y hxy
  funext i
  exact congrFun hxy ⟨i, mem_univ i⟩

/-- **Shearer's lemma**: if every coordinate lies in at least `k` of the sets `S j`, then `k`
times the entropy of the tuple is at most the sum of the entropies of its restrictions to the
sets `S j`. -/
theorem mul_entropy_le_sum_entropy_map_restrict [Finite ι] [DecidableEq ι] {J : Type*}
    [Fintype J] (P : PMF (∀ i, α i)) (S : J → Finset ι) {k : ℕ}
    (hk : ∀ i, k ≤ #{j | i ∈ S j}) :
    k * entropy P ≤ ∑ j, entropy (P.map (S j).restrict) := by
  let := Fintype.ofFinite ι
  let order : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let h (i : ι) := conditionalEntropy
    (P.map fun x => ((univ.filter (· < i)).restrict x, x i))
  have hchain : entropy P = ∑ i, h i := by
    rw [← entropy_map_restrict_univ, entropy_map_restrict_eq_sum]
  have hset (j : J) : ∑ i ∈ S j, h i ≤ entropy (P.map (S j).restrict) := by
    rw [entropy_map_restrict_eq_sum]
    exact sum_le_sum fun i _ =>
      conditionalEntropy_map_restrict_le P (filter_subset_filter _ (subset_univ _)) i
  have hcount : ∑ j, ∑ i ∈ S j, h i = ∑ i, (#{j | i ∈ S j} : ℝ) * h i := by
    rw [sum_comm' (t' := univ) (s' := fun i => univ.filter fun j => i ∈ S j)
      (fun j i => by simp)]
    simp only [sum_const, nsmul_eq_mul]
  calc (k : ℝ) * entropy P = ∑ i, (k : ℝ) * h i := by rw [hchain, mul_sum]
    _ ≤ ∑ i, (#{j | i ∈ S j} : ℝ) * h i :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hk i)
        (conditionalEntropy_nonneg _)
    _ = ∑ j, ∑ i ∈ S j, h i := hcount.symm
    _ ≤ ∑ j, entropy (P.map (S j).restrict) := sum_le_sum fun j _ => hset j

/-- **Han's inequality**: for `n` coordinates, `n - 1` times the entropy of the tuple is at most
the sum of the entropies of the tuples with one coordinate deleted. This is the comparison of
the averages over subsets of sizes `n - 1` and `n` in [CoverThomas2006], Theorem 17.6.1; the
comparison of smaller sizes is not formalized. -/
theorem sub_one_mul_entropy_le_sum_entropy_map_restrict_erase [Fintype ι] [DecidableEq ι]
    (P : PMF (∀ i, α i)) :
    ((Fintype.card ι : ℝ) - 1) * entropy P ≤
      ∑ i, entropy (P.map (univ.erase i).restrict) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hcard | hcard
  · rw [hcard, Nat.cast_zero, zero_sub, neg_one_mul]
    exact (neg_nonpos.mpr (entropy_nonneg P)).trans
      (sum_nonneg fun i _ => entropy_nonneg _)
  have h := mul_entropy_le_sum_entropy_map_restrict P (fun i => univ.erase i)
    (k := Fintype.card ι - 1) (fun i => by
      rw [show (univ.filter fun j => i ∈ univ.erase j) = univ.erase i by
        ext j; simp [eq_comm], card_erase_of_mem (mem_univ i), card_univ])
  rwa [Nat.cast_sub hcard, Nat.cast_one] at h

/-- **Subadditivity of entropy**: the entropy of a tuple is at most the sum of the entropies of
its coordinates ([CoverThomas2006], Theorem 2.6.6). -/
theorem entropy_le_sum_entropy_map_eval [Fintype ι] (P : PMF (∀ i, α i)) :
    entropy P ≤ ∑ i, entropy (P.map fun x => x i) := by
  classical
  have h := mul_entropy_le_sum_entropy_map_restrict P (fun i => {i}) (k := 1)
    (fun i => by
      rw [show (univ.filter fun j => i ∈ ({j} : Finset ι)) = {i} by ext; simp [eq_comm],
        card_singleton])
  have heval (i : ι) :
      entropy (P.map ({i} : Finset ι).restrict) = entropy (P.map fun x => x i) := by
    have hmap : P.map (fun x => x i) =
        (P.map ({i} : Finset ι).restrict).map (fun y => y ⟨i, mem_singleton_self i⟩) := by
      rw [PMF.map_comp]; rfl
    have hinj : Function.Injective
        (fun y : ∀ j : ↥({i} : Finset ι), α j => y ⟨i, mem_singleton_self i⟩) := by
      intro y z hyz
      funext ⟨j, hj⟩
      obtain rfl := mem_singleton.mp hj
      exact hyz
    rw [hmap, entropy_map_of_injective _ hinj]
  simpa only [Nat.cast_one, one_mul, heval] using h

end Cslib.Probability.PMF

namespace Cslib.Finset

open Cslib.Probability.PMF

variable {ι : Type*} {α : ι → Type*} [∀ i, Finite (α i)]

/-- **Shearer's lemma for counting**: if every coordinate lies in at least `k ≥ 1` of the sets
`S j`, the `k`-th power of the size of a finite set of tuples is at most the product of the sizes
of its restrictions to the sets `S j`. For Boolean coordinates this bounds a family of sets by
its traces. -/
theorem card_pow_le_prod_card_image_restrict [Finite ι] [DecidableEq ι]
    [∀ i, DecidableEq (α i)] {J : Type*} [Fintype J] (A : Finset (∀ i, α i))
    (S : J → Finset ι) {k : ℕ} (hk0 : 0 < k) (hk : ∀ i, k ≤ #{j | i ∈ S j}) :
    #A ^ k ≤ ∏ j, #(A.image (S j).restrict) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [zero_pow hk0.ne']
  have hlog := mul_entropy_le_sum_entropy_map_restrict (uniformOfFinset A hA) S hk
  rw [entropy_uniformOfFinset] at hlog
  have hproj (j : J) : entropy ((uniformOfFinset A hA).map (S j).restrict) ≤
      Real.logb 2 #(A.image (S j).restrict) := by
    apply entropy_le_logb_card_of_support_subset
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    rw [mem_support_uniformOfFinset_iff] at hx
    exact mem_coe.mpr (mem_image_of_mem _ hx)
  have himage (j : J) : 0 < #(A.image (S j).restrict) := (hA.image _).card_pos
  have h := hlog.trans (sum_le_sum fun j _ => hproj j)
  rw [← Real.logb_pow, ← Real.logb_prod _ _ (fun j _ => by exact_mod_cast (himage j).ne')] at h
  have hpos : (0 : ℝ) < #A ^ k := by exact_mod_cast pow_pos hA.card_pos k
  have hprod : (0 : ℝ) < ∏ j, (#(A.image (S j).restrict) : ℝ) :=
    prod_pos fun j _ => by exact_mod_cast himage j
  have := (Real.logb_le_logb (b := 2) (by norm_num) hpos hprod).mp h
  exact_mod_cast this

end Cslib.Finset
