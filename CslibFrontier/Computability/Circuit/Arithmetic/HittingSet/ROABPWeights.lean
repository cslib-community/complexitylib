/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ROABPMonomials
public import CslibFrontier.Foundations.Data.Bracketing
public import CslibFrontier.Foundations.LinearAlgebra.IsolatedBasis
public import CslibFrontier.Foundations.NumberTheory.ModularWeights
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A weight that isolates a spanning set of the coefficients of a branching program

Let `M` be the layers of a read-once oblivious branching program of width `w` that reads the
variables of a list `l` without repetition, with entries of degree at most `δ`. For a prime `p`
larger than `2 n² w⁸` and `δ` there are `a₁, …, a_h < p`, `h ≤ ⌈lg n⌉`, such that the weight
`levelWeight p (n δ p + 1) [a_h, …, a₁]` isolates a set of at most `w²` monomials among the
coefficient matrices `segmentCoeff M l` of the program (`exists_isolating_weight`), in the sense
of `Cslib.Isolates`. This is Lemma 8 of Agrawal, Gurjar, Korwar and Saxena
[AgrawalGurjarKorwarSaxena2015] for univariate layers.

## Proof

Take a bracketing of `l` of height at most `⌈lg n⌉` (`Cslib.Bracketing.exists_leaves_eq`). By
induction on `h`, some weight of level `h` isolates at most `w²` monomials in the segment of
every subtree of height at most `h` (`exists_isolates_subtrees`).

* For `h = 0` the subtrees are single layers, and the weight `1` on every variable separates the
  powers of one variable; a greedy choice gives the isolated set
  (`Cslib.exists_isolates_of_injOn`).
* For `h + 1`, let `S l`, `S r` be the isolated sets of the two halves of a subtree. Among the
  weights `Cslib.modWeight p a`, `a < p`, one separates the at most `w⁸` pairs of `S l + S r`
  for all subtrees at once (`Cslib.exists_modWeight_separating`). The new weight is `B` times
  the old one plus this one, with `B` larger than every value of the latter: it keeps the strict
  inequalities of the old weight, so the two halves are still isolated, and it is injective on
  `S l + S r`, so `Cslib.exists_isolates_add` applies.

## Departures from the source

The source builds the weight of all levels as one sum `∑ wᵣ B ^ (log d - r)` and pairs the
factors level by level; here the levels are added one at a time along a bracketing. The source
takes the weights `(δ + 1) ^ i mod q` over the first primes `q`; here they are
`a ^ (i + 1) mod p` for one prime `p`.

## Main definitions

* `levelWeight`: the weight of a list of parameters.

## Main results

* `exists_isolating_weight`: [AgrawalGurjarKorwarSaxena2015, Lemma 8], for univariate layers.
* `levelWeight_le`: the weights are at most `(B + p) ^ h`.

## References

* [M. Agrawal, R. Gurjar, A. Korwar, N. Saxena, *Hitting-sets for ROABP and sum of
  set-multilinear circuits*][AgrawalGurjarKorwarSaxena2015], §3, Lemma 8
-/

public section

open scoped Polynomial Pointwise

namespace Cslib.Circuits.Arithmetic

open Finset

variable {F : Type*} [Field F] {n w : ℕ}

/-- The weight of a list of parameters, the most recent level first: `1` for the empty list, and
`B` times the weight of the earlier levels plus the modular weight of the new parameter. -/
def levelWeight (p B : ℕ) : List ℕ → Fin n → ℕ
  | [] => fun _ => 1
  | a :: as => fun i => B * levelWeight p B as i + modWeight p a i

theorem one_le_levelWeight {p B : ℕ} (hB : 0 < B) :
    ∀ (a : List ℕ) (i : Fin n), 1 ≤ levelWeight p B a i
  | [], _ => le_rfl
  | _ :: as, i => (Nat.mul_le_mul hB (one_le_levelWeight hB as i)).trans (Nat.le_add_right _ _)

/-- The weights of `h` levels are at most `(B + p) ^ h`. -/
theorem levelWeight_le {p B : ℕ} (hp : 0 < p) (hB : 0 < B) :
    ∀ (a : List ℕ) (i : Fin n), levelWeight p B a i ≤ (B + p) ^ a.length
  | [], _ => le_rfl
  | a :: as, i => by
    have h1 := one_le_levelWeight (p := p) hB as i
    have h2 := levelWeight_le hp hB as i
    have h3 := (modWeight_lt hp a i).le
    calc B * levelWeight p B as i + modWeight p a i
        ≤ B * levelWeight p B as i + p * levelWeight p B as i :=
          Nat.add_le_add_left (h3.trans (Nat.le_mul_of_pos_right _ h1)) _
      _ = (B + p) * levelWeight p B as i := (add_mul _ _ _).symm
      _ ≤ (B + p) * (B + p) ^ as.length := Nat.mul_le_mul_left _ h2
      _ = (B + p) ^ (a :: as).length := by rw [List.length_cons, pow_succ']

private theorem eq_of_mul_add_eq {B x y u v : ℕ} (hu : u < B) (hv : v < B)
    (h : B * x + u = B * y + v) : x = y ∧ u = v := by
  have hB : 0 < B := (Nat.zero_le u).trans_lt hu
  have hx : x = y := by
    have h' := congrArg (· / B) h
    simpa [Nat.mul_add_div hB, Nat.div_eq_of_lt hu, Nat.div_eq_of_lt hv] using h'
  subst hx
  exact ⟨rfl, Nat.add_left_cancel h⟩

private theorem mul_add_lt_mul_add {B x x' u u' : ℕ} (hx : x' < x) (hu : u' < B) :
    B * x' + u' < B * x + u :=
  calc B * x' + u' < B * x' + B := Nat.add_lt_add_left hu _
    _ = B * (x' + 1) := (Nat.mul_succ _ _).symm
    _ ≤ B * x := Nat.mul_le_mul_left _ hx
    _ ≤ B * x + u := Nat.le_add_right _ _

variable {p δ : ℕ}

/-- The pairs of distinct monomials in `S l + S r` over the subtrees `node l r` of a bracketing
of height at most `h + 1`. -/
private noncomputable def levelPairs (S : Bracketing (Fin n) → Finset (Fin n →₀ ℕ))
    (h : ℕ) (t : Bracketing (Fin n)) : Finset ((Fin n →₀ ℕ) × (Fin n →₀ ℕ)) := by
  classical
  exact (t.subtrees.toFinset.filter fun s => s.height ≤ h + 1).biUnion fun s =>
    match s with
    | .node l r => (S l + S r).offDiag
    | .leaf _ => ∅

/-- The two halves of a subtree of a bracketing without repeated entries have disjoint
entries. -/
private theorem disjoint_leaves {t l r : Bracketing (Fin n)} (ht : t.leaves.Nodup)
    (hs : Bracketing.node l r ∈ t.subtrees) : l.leaves.Disjoint r.leaves :=
  List.disjoint_of_nodup_append
    ((Bracketing.sublist_leaves_of_mem_subtrees hs).nodup ht)

/-- Some weight of level `h` isolates at most `w ^ 2` monomials in the segment of every subtree
of height at most `h`. -/
private theorem exists_isolates_subtrees [Fact p.Prime] (hp : 2 * n * (w ^ 2) ^ 4 * n < p)
    (hδ : δ < p) (M : Fin n → Matrix (Fin w) (Fin w) F[X]) {t : Bracketing (Fin n)}
    (ht : t.leaves.Nodup) (h : ℕ) :
    ∃ a : List ℕ, a.length = h ∧ (∀ x ∈ a, x < p) ∧ ∀ s ∈ t.subtrees, s.height ≤ h →
      ∃ S : Finset (Fin n →₀ ℕ), S.card ≤ w ^ 2 ∧
        Isolates F (Finsupp.weight (levelWeight p (n * δ * p + 1) a))
          (segmentCoeff M s.leaves) (monomialsLE s.leaves δ) S := by
  classical
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  have hrank : Module.finrank F (Matrix (Fin w) (Fin w) F) = w ^ 2 := by
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, sq]
  induction h with
  | zero =>
    refine ⟨[], rfl, fun x hx => absurd hx List.not_mem_nil, fun s _ hsh => ?_⟩
    cases s with
    | node l r => exact absurd hsh (Nat.succ_ne_zero _ ∘ Nat.le_zero.1)
    | leaf i =>
      have hwt : ∀ m ∈ monomialsLE [i] δ,
          Finsupp.weight (levelWeight p (n * δ * p + 1) []) m = m i := fun m hm => by
        rw [Finsupp.weight_apply, Finsupp.sum, sum_eq_single i (fun j _ hj => by
            rw [(mem_monomialsLE.1 hm).2 j (by simpa using hj), zero_smul])
          (fun hi => by rw [Finsupp.notMem_support_iff.1 hi, zero_smul])]
        simp [levelWeight]
      have hinj : Set.InjOn (Finsupp.weight (levelWeight p (n * δ * p + 1) []))
          (↑(monomialsLE [i] δ) : Set (Fin n →₀ ℕ)) := fun m hm m' hm' hmm => by
        rw [mem_coe] at hm hm'
        rw [hwt m hm, hwt m' hm'] at hmm
        ext j
        by_cases hj : j = i
        · rw [hj, hmm]
        · rw [(mem_monomialsLE.1 hm).2 j (by simpa using hj),
            (mem_monomialsLE.1 hm').2 j (by simpa using hj)]
      obtain ⟨S, hS, hiso⟩ := exists_isolates_of_injOn (F := F)
        (D := segmentCoeff M (Bracketing.leaf i).leaves) hinj
      exact ⟨S, hS.trans_eq hrank, hiso⟩
  | succ h ih =>
    obtain ⟨a, hlen, hap, hS⟩ := ih
    choose! S hScard hSiso using hS
    set B := n * δ * p + 1 with hB
    set c := levelWeight (n := n) p B a with hc
    -- the pairs to separate
    set P := levelPairs S h t with hPdef
    have hTsub : ∀ {l r : Bracketing (Fin n)}, Bracketing.node l r ∈ t.subtrees →
        l.height ≤ h → r.height ≤ h →
        S l + S r ⊆ monomialsLE (l.leaves ++ r.leaves) δ := fun {l r} hs hl hr => by
      rw [monomialsLE_append (disjoint_leaves ht hs)]
      exact add_subset_add
        (hSiso l (Bracketing.mem_subtrees_of_node hs).1 hl).1
        (hSiso r (Bracketing.mem_subtrees_of_node hs).2 hr).1
    have hheight : ∀ {l r : Bracketing (Fin n)}, (Bracketing.node l r).height ≤ h + 1 →
        l.height ≤ h ∧ r.height ≤ h := fun {l r} hh => by
      rw [Bracketing.height] at hh
      exact ⟨(le_max_left _ _).trans (Nat.le_of_succ_le_succ hh),
        (le_max_right _ _).trans (Nat.le_of_succ_le_succ hh)⟩
    have hPmem : ∀ x ∈ P, ∃ l r, Bracketing.node l r ∈ t.subtrees ∧ l.height ≤ h ∧
        r.height ≤ h ∧ x ∈ (S l + S r).offDiag := fun x hx => by
      rw [hPdef, levelPairs, mem_biUnion] at hx
      obtain ⟨s, hs, hxs⟩ := hx
      rw [mem_filter, List.mem_toFinset] at hs
      cases s with
      | leaf i => exact absurd hxs (notMem_empty x)
      | node l r => exact ⟨l, r, hs.1, (hheight hs.2).1, (hheight hs.2).2, hxs⟩
    have hP : ∀ x ∈ P, x.1 ≠ x.2 ∧ (∀ i, x.1 i ≤ δ) ∧ ∀ i, x.2 i ≤ δ := fun x hx => by
      obtain ⟨l, r, hs, hl, hr, hxs⟩ := hPmem x hx
      rw [mem_offDiag] at hxs
      exact ⟨hxs.2.2, (mem_monomialsLE.1 (hTsub hs hl hr hxs.1)).1,
        (mem_monomialsLE.1 (hTsub hs hl hr hxs.2.1)).1⟩
    have hPcard : P.card * n < p := by
      refine lt_of_le_of_lt (Nat.mul_le_mul_right n ?_) hp
      rw [hPdef, levelPairs]
      refine card_biUnion_le.trans ((sum_le_card_nsmul _ _ ((w ^ 2) ^ 4) fun s hs => ?_).trans ?_)
      · rw [mem_filter, List.mem_toFinset] at hs
        cases s with
        | leaf i => simp
        | node l r =>
          have hl := hScard l (Bracketing.mem_subtrees_of_node hs.1).1 (hheight hs.2).1
          have hr := hScard r (Bracketing.mem_subtrees_of_node hs.1).2 (hheight hs.2).2
          have hadd : (S l + S r).card ≤ w ^ 2 * w ^ 2 :=
            (card_add_le).trans (Nat.mul_le_mul hl hr)
          calc (S l + S r).offDiag.card ≤ (S l + S r).card * (S l + S r).card := by
                rw [offDiag_card]
                exact Nat.sub_le _ _
            _ ≤ (w ^ 2 * w ^ 2) * (w ^ 2 * w ^ 2) := Nat.mul_le_mul hadd hadd
            _ = (w ^ 2) ^ 4 := by ring
      · rw [smul_eq_mul]
        refine Nat.mul_le_mul_right _ ((card_filter_le _ _).trans
          ((List.toFinset_card_le _).trans ?_))
        have h1 := t.length_subtrees
        have h2 : t.leaves.length ≤ n := by
          simpa using ht.length_le_card
        omega
    obtain ⟨a', ha'p, hsep⟩ := exists_modWeight_separating hδ P hP hPcard
    set c' := levelWeight (n := n) p B (a' :: a) with hc'
    have hw' : ∀ m : Fin n →₀ ℕ, Finsupp.weight c' m =
        B * Finsupp.weight c m + Finsupp.weight (modWeight (n := n) p a') m :=
      fun m => weight_mul_add B c _ m
    have hsmall : ∀ {L : List (Fin n)} {m : Fin n →₀ ℕ}, m ∈ monomialsLE L δ →
        Finsupp.weight (modWeight (n := n) p a') m < B := fun hm =>
      Nat.lt_succ_of_le (weight_le_of_mem_monomialsLE (fun i => (modWeight_lt hpp a' i).le) hm)
    have htransfer : ∀ s ∈ t.subtrees, s.height ≤ h →
        Isolates F (Finsupp.weight c') (segmentCoeff M s.leaves) (monomialsLE s.leaves δ)
          (S s) := fun s hs hsh => by
      have hiso := hSiso s hs hsh
      refine hiso.mono_weight (fun m hm m' hm' hlt => ?_) fun x hx y hy hxy => ?_
      · rw [hw', hw']
        exact mul_add_lt_mul_add hlt (hsmall hm')
      · rw [hw', hw'] at hxy
        exact hiso.2.1 hx hy
          (eq_of_mul_add_eq (hsmall (hiso.1 hx)) (hsmall (hiso.1 hy)) hxy).1
    refine ⟨a' :: a, by rw [List.length_cons, hlen], fun x hx => ?_, fun s hs hsh => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      exacts [ha'p, hap x hx]
    · rcases Nat.lt_or_ge s.height (h + 1) with hlt | hge
      · exact ⟨S s, hScard s hs (Nat.lt_succ_iff.1 hlt), htransfer s hs (Nat.lt_succ_iff.1 hlt)⟩
      · cases s with
        | leaf i => exact absurd hge (by simp [Bracketing.height])
        | node l r =>
          obtain ⟨hl, hr⟩ := hheight hsh
          have hd := disjoint_leaves ht hs
          have hinj : Set.InjOn (Finsupp.weight c')
              (↑(S l + S r) : Set (Fin n →₀ ℕ)) := by
            intro x hx y hy hxy
            by_contra hne
            rw [hw', hw'] at hxy
            have hxT := hTsub hs hl hr hx
            have hyT := hTsub hs hl hr hy
            refine hsep (x, y) ?_ (eq_of_mul_add_eq (hsmall hxT) (hsmall hyT) hxy).2
            rw [hPdef, levelPairs, mem_biUnion]
            exact ⟨_, mem_filter.2 ⟨List.mem_toFinset.2 hs, hsh⟩,
              mem_offDiag.2 ⟨hx, hy, hne⟩⟩
          obtain ⟨S', -, hcard, hiso⟩ := exists_isolates_add
            (htransfer l (Bracketing.mem_subtrees_of_node hs).1 hl)
            (htransfer r (Bracketing.mem_subtrees_of_node hs).2 hr)
            (D := segmentCoeff M (l.leaves ++ r.leaves))
            (fun m₁ hm₁ m₂ hm₂ => segmentCoeff_append_add M hd hm₁ hm₂) hinj
          rw [← monomialsLE_append hd] at hiso
          exact ⟨S', hcard.trans_eq hrank, hiso⟩

/-- **A weight isolating the coefficients of a branching program**
([AgrawalGurjarKorwarSaxena2015], Lemma 8, for univariate layers). For a prime `p` above
`2 n² w⁸` and `δ`, some weight of at most `⌈lg n⌉` levels with parameters below `p` isolates a
set of monomials among the coefficient matrices of the layers `M`, of degree at most `δ`, read
in the order of a list without repetition. -/
theorem exists_isolating_weight [Fact p.Prime] (hp : 2 * n * (w ^ 2) ^ 4 * n < p) (hδ : δ < p)
    (M : Fin n → Matrix (Fin w) (Fin w) F[X]) {l : List (Fin n)} (hl : l.Nodup) :
    ∃ a : List ℕ, a.length ≤ Nat.clog 2 n ∧ (∀ x ∈ a, x < p) ∧ ∃ S : Finset (Fin n →₀ ℕ),
      Isolates F (Finsupp.weight (levelWeight p (n * δ * p + 1) a))
        (segmentCoeff M l) (monomialsLE l δ) S := by
  classical
  rcases eq_or_ne l [] with rfl | hne
  · refine ⟨[], Nat.zero_le _, fun x hx => absurd hx List.not_mem_nil, {0}, ?_, ?_, ?_⟩
    · exact singleton_subset_iff.2 (mem_monomialsLE.2 ⟨fun _ => Nat.zero_le _, fun _ _ => rfl⟩)
    · rw [coe_singleton]
      exact Set.injOn_singleton _ _
    · intro m hm hm0
      exact absurd (mem_singleton.2 (Finsupp.ext fun i =>
        (mem_monomialsLE.1 hm).2 i List.not_mem_nil)) hm0
  · obtain ⟨t, rfl, hth⟩ := Bracketing.exists_leaves_eq l hne
    obtain ⟨a, hlen, hap, hS⟩ := exists_isolates_subtrees (F := F) hp hδ M hl t.height
    obtain ⟨S, -, hiso⟩ := hS t t.self_mem_subtrees le_rfl
    refine ⟨a, ?_, hap, S, hiso⟩
    rw [hlen]
    exact hth.trans (Nat.clog_mono_right 2 (by simpa using hl.length_le_card))

end Cslib.Circuits.Arithmetic
