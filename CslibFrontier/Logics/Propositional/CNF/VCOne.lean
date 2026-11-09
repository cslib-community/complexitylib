/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOneCounting
public import CslibFrontier.Logics.Propositional.CNF.Parity
public import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# Explicit relations of VC dimension at most one

The table representation of [ChenJiangZhu2027], Theorem 1.3 and Section 6
(PDF pp. 18–21). Tables are finite sets of Boolean tuples, so repeated input rows
are identified. Every coordinate, including constant coordinates, remains declared.
The VC promise uses Mathlib's finite set-family dimension via positive supports.
`listedClosure` incrementally generates only pair-compatible prefixes, with a
proved quadratic bound on attempted extensions under the VC promise. The global
compiler uses that listing to enumerate equations. No polynomial-bit-time rank
implementation or sharper counting runtime is asserted.
-/

public section

noncomputable section

namespace Cslib.Logic.PL.VCOne

variable {V : Type*} [Fintype V]

/-- Positive coordinates of a tuple, for the standard set-family VC API. -/
@[expose] def support (x : V → Bool) : Finset V := Finset.univ.filter fun i => x i = true

open scoped Classical in
/-- A finite Boolean table as Mathlib's family of positive supports. -/
@[expose] def family (R : Finset (V → Bool)) : Finset (Finset V) := R.image support

open scoped Classical in
/-- The standard VC dimension promise on the actual input table. -/
@[expose] def DimensionOne (R : Finset (V → Bool)) : Prop := (family R).vcDim ≤ 1

private theorem support_injective : Function.Injective (support (V := V)) := by
  classical
  intro x y h
  funext i
  have hi := Finset.ext_iff.mp h i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  cases hx : x i <;> cases hy : y i <;> simp_all

instance instDecidableEqOnFinset (s : Finset V) (x y : V → Bool) :
    Decidable (Set.EqOn x y (s : Set V)) :=
  inferInstanceAs (Decidable (∀ i ∈ s, x i = y i))

open scoped Classical in
/-- Binary closure: every projection on at most two coordinates occurs in the table. -/
@[expose] def closure (R : Finset (V → Bool)) : Finset (V → Bool) :=
  Finset.univ.filter fun y => ∀ s : Finset V, s.card ≤ 2 → ∃ x ∈ R, Set.EqOn x y s

/-- Membership without exposing the enumeration's decidability instances. -/
theorem mem_closure (R : Finset (V → Bool)) (y : V → Bool) :
    y ∈ closure R ↔ ∀ s : Finset V, s.card ≤ 2 → ∃ x ∈ R, Set.EqOn x y s := by
  classical
  simp only [closure, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every original tuple survives the unary and binary restrictions. -/
theorem subset_closure (R : Finset (V → Bool)) : R ⊆ closure R := by
  classical
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => ⟨x, hx, fun _ _ => rfl⟩⟩

private theorem projection {R : Finset (V → Bool)} {y : V → Bool}
    (hy : y ∈ closure R) (s : Finset V) (hs : s.card ≤ 2) : ∃ x ∈ R, Set.EqOn x y s := by
  classical
  exact (Finset.mem_filter.mp hy).2 s hs

open scoped Classical in
private theorem shatters_pair {R : Finset (V → Bool)} {i j : V} (hij : i ≠ j)
    (h : ∀ a b : Bool, ∃ x ∈ R, x i = a ∧ x j = b) :
    (family R).Shatters {i, j} := by
  classical
  intro t ht
  obtain ⟨x, hx, hi, hj⟩ := h (decide (i ∈ t)) (decide (j ∈ t))
  refine ⟨support x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
  ext k
  by_cases hki : k = i
  · subst k; simp [support, hi, hij]
  by_cases hkj : k = j
  · subst k; simp [support, hj]
  have hk : k ∉ t := fun hk => by simpa [hki, hkj] using ht hk
  simp [support, hki, hkj, hk]

open scoped Classical in
/-- Shattering two coordinates realizes every ordered Boolean pattern. -/
theorem patterns_of_shatters_pair (R : Finset (V → Bool)) {i j : V} (hij : i ≠ j)
    (hp : (family R).Shatters {i, j}) (a b : Bool) :
    ∃ x ∈ R, x i = a ∧ x j = b := by
  classical
  let t : Finset V := ({i, j} : Finset V).filter fun k => if k = i then a else b
  obtain ⟨u, hu, he⟩ := hp (Finset.filter_subset _ _ : t ⊆ {i, j})
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  refine ⟨x, hx, ?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simpa [t, support] using Finset.ext_iff.mp he i
  · apply Bool.eq_iff_iff.mpr
    simpa [t, support, Ne.symm hij] using Finset.ext_iff.mp he j

/-- Check the standard VC promise by exhibiting one missing pattern per pair. -/
theorem dimensionOne_of_missing (R : Finset (V → Bool))
    (h : ∀ i j : V, i ≠ j → ∃ a b : Bool, ∀ x ∈ R, ¬ (x i = a ∧ x j = b)) :
    DimensionOne R := by
  classical
  apply Finset.sup_le
  intro s hs
  by_contra hn
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < s.card by omega)
  have hp := (Finset.mem_shatterer.mp hs).mono_right
    (show ({i, j} : Finset V) ⊆ s by simp [Finset.insert_subset_iff, hi, hj])
  obtain ⟨a, b, hab⟩ := h i j hij
  obtain ⟨x, hx, hxi, hxj⟩ := patterns_of_shatters_pair R hij hp a b
  exact hab x hx ⟨hxi, hxj⟩

/-- The binary closure retains the dimension promise, independently of table size. -/
theorem dimensionOne_closure (R : Finset (V → Bool)) (hR : DimensionOne R) :
    DimensionOne (closure R) := by
  classical
  apply Finset.sup_le
  intro s hs
  by_contra hn
  have hcard : 1 < s.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  have hp := (Finset.mem_shatterer.mp hs).mono_right
    (show ({i, j} : Finset V) ⊆ s by simp [Finset.insert_subset_iff, hi, hj])
  have hpat (a b : Bool) : ∃ x ∈ R, x i = a ∧ x j = b := by
    obtain ⟨y, hy, hyi, hyj⟩ := patterns_of_shatters_pair (closure R) hij hp a b
    obtain ⟨x, hx, hag⟩ := projection hy {i, j} (by simp [hij])
    exact ⟨x, hx, (@hag i (by simp)).trans hyi, (@hag j (by simp)).trans hyj⟩
  have hh := (shatters_pair hij hpat).card_le_vcDim
  have hh' : 2 ≤ (family R).vcDim := by simpa [hij] using hh
  unfold DimensionOne at hR
  omega

/-- Sauer–Shelah specialized to these Boolean tables, reusing Mathlib's theorem. -/
theorem card_le (R : Finset (V → Bool)) (hR : DimensionOne R) :
    R.card ≤ Fintype.card V + 1 := by
  classical
  have h₁ := Finset.card_le_card_shatterer (family R)
  have h₂ := Finset.card_shatterer_le_sum_vcDim (𝒜 := family R)
  have h₃ : ∑ k ∈ Finset.Iic (family R).vcDim, (Fintype.card V).choose k ≤
      ∑ k ∈ Finset.Iic 1, (Fintype.card V).choose k :=
    Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hR)
  have hc : (family R).card = R.card := Finset.card_image_of_injective _ support_injective
  rw [hc] at h₁
  have hs : (∑ k ∈ Finset.Iic 1, (Fintype.card V).choose k) = Fintype.card V + 1 := by
    rw [show (Finset.Iic 1 : Finset ℕ) = {0, 1} by decide]
    simp [Nat.add_comm]
  omega

/-- The number of unwanted closure points has the sharp deficit bound. -/
theorem separators_bound (R : Finset (V → Bool)) (hR : DimensionOne R) :
    (closure R \ R).card ≤ Fintype.card V + 1 - R.card := by
  classical
  rw [Finset.card_sdiff_of_subset (subset_closure R)]
  exact Nat.sub_le_sub_right (card_le _ (dimensionOne_closure R hR)) _

private theorem no_pair (R : Finset (V → Bool)) (hR : DimensionOne R)
    {i j : V} (hij : i ≠ j) (hp : ∀ a b : Bool, ∃ x ∈ R, x i = a ∧ x j = b) : False := by
  classical
  have hh := (shatters_pair hij hp).card_le_vcDim
  have hd : 2 ≤ (family R).vcDim := by simpa [hij] using hh
  unfold DimensionOne at hR
  omega

section Listing

variable [DecidableEq V]

/-- Test only listed unary/binary projections on the processed coordinates.
The nonempty test handles a zero-coordinate empty table. -/
@[expose] def PairCompatible (R : Finset (V → Bool)) (s : Finset V) (y : V → Bool) : Prop :=
  R.Nonempty ∧ ∀ i ∈ s, ∀ j ∈ s, ∃ x ∈ R, x i = y i ∧ x j = y j

instance (R : Finset (V → Bool)) (s : Finset V) (y : V → Bool) :
    Decidable (PairCompatible R s y) :=
  inferInstanceAs (Decidable (R.Nonempty ∧
    ∀ i ∈ s, ∀ j ∈ s, ∃ x ∈ R, x i = y i ∧ x j = y j))

/-- Original pair-compatible-prefix variant of the listing in Lemma 6.1.
Extend retained prefixes by one bit, then scan the table projections.
Unprocessed coordinates are zero placeholders, not additional branching choices.
No Boolean cube or set of coordinate subsets is enumerated. -/
@[expose] def prefixes (R : Finset (V → Bool)) : List V → Finset (V → Bool)
  | [] => if R.Nonempty then {fun _ => false} else ∅
  | i :: todo =>
      let previous := prefixes R todo
      ((previous.image (fun x => Function.update x i false)) ∪
        (previous.image (fun x => Function.update x i true))).filter
          (PairCompatible R (i :: todo).toFinset)

/-- The retained rows are exactly the pair-compatible prefixes, with zero padding. -/
theorem mem_prefixes (R : Finset (V → Bool)) (todo : List V) (hn : todo.Nodup)
    (y : V → Bool) :
    y ∈ prefixes R todo ↔ PairCompatible R todo.toFinset y ∧
      ∀ i, i ∉ todo → y i = false := by
  induction todo generalizing y with
  | nil =>
    simp only [prefixes, List.toFinset_nil, PairCompatible, Finset.notMem_empty,
      false_implies, implies_true, forall_const, and_true, List.not_mem_nil, not_false_eq_true]
    split_ifs with h
    · simp only [Finset.mem_singleton, h, true_and]
      exact ⟨fun e i => congrFun e i, fun h => funext h⟩
    · simp [h]
  | cons i todo ih =>
    have hi : i ∉ todo := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    simp only [prefixes, Finset.mem_filter]
    constructor
    · rintro ⟨hm, hp⟩
      refine ⟨hp, ?_⟩
      rcases Finset.mem_union.mp hm with hm | hm <;>
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm <;>
        intro j hj <;>
        rw [Function.update_of_ne (fun h => hj (List.mem_cons.mpr (Or.inl h)))] <;>
        exact (ih ht x).mp hx |>.2 j (fun h => hj (List.mem_cons.mpr (Or.inr h)))
    · rintro ⟨hp, hz⟩
      let x := Function.update y i false
      have hx : x ∈ prefixes R todo := by
        apply (ih ht x).mpr
        refine ⟨⟨hp.1, ?_⟩, ?_⟩
        · intro j hj k hk
          obtain ⟨z, hzr, hzj, hzk⟩ := hp.2 j (by simp [hj]) k (by simp [hk])
          refine ⟨z, hzr, ?_, ?_⟩
          · have hji : j ≠ i := fun h => hi (h ▸ List.mem_toFinset.mp hj)
            simpa [x, Function.update_of_ne hji] using hzj
          · have hki : k ≠ i := fun h => hi (h ▸ List.mem_toFinset.mp hk)
            simpa [x, Function.update_of_ne hki] using hzk
        · intro j hj
          by_cases he : j = i
          · simp [x, he]
          · change Function.update y i false j = false
            rw [Function.update_of_ne he]
            exact hz j (by simp [he, hj])
      have he : Function.update x i (y i) = y := by
        funext j
        by_cases hj : j = i <;> simp [x, hj]
      refine ⟨Finset.mem_union.mpr ?_, hp⟩
      cases hb : y i
      · exact Or.inl (Finset.mem_image.mpr ⟨x, hx, hb ▸ he⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨x, hx, hb ▸ he⟩)

omit [DecidableEq V] in
/-- Pair tests are equivalent to the semantic closure, including empty scopes. -/
theorem pairCompatible_univ (R : Finset (V → Bool)) (y : V → Bool) :
    PairCompatible R Finset.univ y ↔ y ∈ closure R := by
  classical
  rw [mem_closure]
  constructor
  · rintro ⟨hne, hp⟩ s hs
    rcases s.eq_empty_or_nonempty with rfl | hneS
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
    obtain ⟨i, hi⟩ := hneS
    by_cases hsingle : s = {i}
    · obtain ⟨x, hx, hxi, _⟩ := hp i (Finset.mem_univ _) i (Finset.mem_univ _)
      exact ⟨x, hx, fun j hj => (Finset.mem_singleton.mp (hsingle ▸ hj)) ▸ hxi⟩
    have htwo : 1 < s.card := by
      by_contra h
      have he := Finset.card_le_one.mp (show s.card ≤ 1 by omega) i hi
      apply hsingle
      ext j
      simp only [Finset.mem_singleton]
      exact ⟨fun hj => (he j hj).symm, fun h => h ▸ hi⟩
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (s := s) htwo i
    have he : s = {i, j} := by
      symm
      apply Finset.eq_of_subset_of_card_le (by simp [Finset.insert_subset_iff, hi, hj])
      simpa [Ne.symm hji] using hs
    obtain ⟨x, hx, hxi, hxj⟩ := hp i (Finset.mem_univ _) j (Finset.mem_univ _)
    refine ⟨x, hx, fun k hk => ?_⟩
    rcases Finset.mem_insert.mp (he ▸ hk) with rfl | hk
    · exact hxi
    · exact (Finset.mem_singleton.mp hk) ▸ hxj
  · intro h
    obtain ⟨x, hx, _⟩ := h ∅ (by simp)
    refine ⟨⟨x, hx⟩, fun i _ j _ => ?_⟩
    obtain ⟨x, hx, he⟩ := h {i, j} (by
      simpa only [Finset.card_singleton] using Finset.card_insert_le i {j})
    exact ⟨x, hx, he (by simp), he (by simp)⟩

/-- Executable closure listing in coordinate order. -/
@[expose] def listedClosure [LinearOrder V] (R : Finset (V → Bool)) : Finset (V → Bool) :=
  prefixes R (Finset.univ.sort (· ≤ ·))

/-- The executable listing and the semantic closure have exactly the same rows. -/
theorem listedClosure_eq [LinearOrder V] (R : Finset (V → Bool)) :
    listedClosure R = closure R := by
  ext y
  rw [listedClosure, mem_prefixes _ _ (Finset.sort_nodup _ _)]
  simpa only [Finset.sort_toFinset, Finset.mem_sort, Finset.mem_univ, not_true_eq_false,
    false_implies, implies_true, forall_const, and_true] using pairCompatible_univ R y

/-- Every intermediate frontier has at most `w + 1` rows, not `2^w`.
Each extension therefore tests at most `2 * (w + 1)` candidates. -/
theorem prefixes_card (R : Finset (V → Bool)) (hR : DimensionOne R)
    (todo : List V) (hn : todo.Nodup) :
    (prefixes R todo).card ≤ Fintype.card V + 1 := by
  classical
  apply card_le
  apply dimensionOne_of_missing
  intro i j hij
  by_cases hi : i ∈ todo
  · by_cases hj : j ∈ todo
    · have hm : ∃ a b : Bool, ∀ x ∈ R, ¬ (x i = a ∧ x j = b) := by
        by_contra h
        push Not at h
        exact no_pair R hR hij h
      obtain ⟨a, b, hab⟩ := hm
      refine ⟨a, b, fun y hy he => ?_⟩
      obtain ⟨x, hx, hxi, hxj⟩ := ((mem_prefixes R todo hn y).mp hy).1.2
        i (List.mem_toFinset.mpr hi) j (List.mem_toFinset.mpr hj)
      exact hab x hx ⟨hxi.trans he.1, hxj.trans he.2⟩
    · exact ⟨false, true, fun y hy he => by
        have hz := ((mem_prefixes R todo hn y).mp hy).2 j hj
        simp_all⟩
  · exact ⟨true, false, fun y hy he => by
      have hz := ((mem_prefixes R todo hn y).mp hy).2 i hi
      simp_all⟩

/-- Number of one-bit extensions attempted by the actual recursion, before
merging duplicates or testing projections. This counts both bit choices. -/
@[expose] def prefixCandidates (R : Finset (V → Bool)) : List V → ℕ
  | [] => 0
  | _ :: todo => prefixCandidates R todo + 2 * (prefixes R todo).card

/-- The complete traversal attempts only quadratically many extensions.
Each projection test scans at most `|todo|²` pairs and the explicit table;
function comparison for deduplication examines only the declared coordinates. -/
theorem prefixCandidates_le (R : Finset (V → Bool)) (hR : DimensionOne R)
    (todo : List V) (hn : todo.Nodup) :
    prefixCandidates R todo ≤ 2 * todo.length * (Fintype.card V + 1) := by
  induction todo with
  | nil => simp [prefixCandidates]
  | cons i todo ih =>
    have ht := (List.nodup_cons.mp hn).2
    have hb := prefixes_card R hR todo ht
    have hi := ih ht
    simp only [prefixCandidates, List.length_cons]
    nlinarith

/-- Enumerate the unwanted closure tuples using the constructive listing.
The semantic subtype's proof does not trigger enumeration of the Boolean cube. -/
@[instance_reducible] def listedDifferenceFintype [LinearOrder V] (R : Finset (V → Bool)) :
    Fintype ↥(closure R \ R) where
  elems := (listedClosure R \ R).attach.map
    { toFun := fun y : ↥(listedClosure R \ R) =>
        ⟨y.val, by simpa only [listedClosure_eq] using y.property⟩
      inj' := fun _ _ h => Subtype.ext
        (congrArg (fun y : ↥(closure R \ R) => y.val) h) }
  complete := fun y => Finset.mem_map.mpr
    ⟨⟨y.val, by simpa only [listedClosure_eq] using y.property⟩, Finset.mem_attach _ _, rfl⟩

end Listing

section Greedy

variable [DecidableEq V]

/-- Delete a coordinate exactly when the remaining projection still misses the
unwanted tuple. Each step scans the table; no powerset search is used. -/
@[expose] def trim (R : Finset (V → Bool)) (y : V → Bool) : List V → Finset V → Finset V
  | [], s => s
  | i :: rest, s => trim R y rest
      (if ∃ x ∈ R, Set.EqOn x y (s.erase i) then s else s.erase i)

omit [Fintype V] in
/-- Greedy deletion keeps failure of agreement and supplies a witnessing table
row for each retained coordinate already visited. -/
theorem trim_spec (R : Finset (V → Bool)) (y : V → Bool) (todo : List V) (s : Finset V)
    (ho : ¬ ∃ x ∈ R, Set.EqOn x y s) :
    trim R y todo s ⊆ s ∧ (¬ ∃ x ∈ R, Set.EqOn x y (trim R y todo s)) ∧
      ∀ i ∈ trim R y todo s, i ∈ todo →
        ∃ x ∈ R, Set.EqOn x y ((trim R y todo s).erase i) := by
  induction todo generalizing s with
  | nil => exact ⟨Finset.Subset.refl _, ho, fun _ _ hi => False.elim (List.not_mem_nil hi)⟩
  | cons i rest ih =>
    simp only [trim]
    split_ifs with hm
    · obtain ⟨hsub, hfail, hw⟩ := ih s ho
      refine ⟨hsub, hfail, fun j hj hjtodo => ?_⟩
      rcases List.mem_cons.mp hjtodo with rfl | hjrest
      · obtain ⟨x, hx, hag⟩ := hm
        exact ⟨x, hx, fun k hk => @hag k (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hk).1, hsub (Finset.mem_erase.mp hk).2⟩)⟩
      · exact hw j hj hjrest
    · obtain ⟨hsub, hfail, hw⟩ := ih (s.erase i) hm
      refine ⟨hsub.trans (Finset.erase_subset _ _), hfail, fun j hj hjtodo => ?_⟩
      rcases List.mem_cons.mp hjtodo with rfl | hjrest
      · exact False.elim ((Finset.mem_erase.mp (hsub hj)).1 rfl)
      · exact hw j hj hjrest

end Greedy

/-- The actual greedy separator scope; coordinate enumeration includes constants. -/
@[expose] def greedyScope [LinearOrder V] (R : Finset (V → Bool)) (y : V → Bool) : Finset V :=
  trim R y (Finset.univ.sort (· ≤ ·)) Finset.univ

/-- The greedy scope is a failed projection, and erasing any retained coordinate
makes that projection occur in the original table. -/
theorem greedyScope_spec [LinearOrder V] (R : Finset (V → Bool)) (y : V → Bool)
    (hy : y ∉ R) :
    (¬ ∃ x ∈ R, Set.EqOn x y (greedyScope R y)) ∧
      ∀ i ∈ greedyScope R y, ∃ x ∈ R, Set.EqOn x y ((greedyScope R y).erase i) := by
  have ho : ¬ ∃ x ∈ R, Set.EqOn x y (Finset.univ : Finset V) := by
    rintro ⟨x, hx, he⟩
    exact hy ((funext fun i => @he i (Finset.mem_univ _)) ▸ hx)
  obtain ⟨_, hf, hw⟩ := trim_spec R y (Finset.univ.sort (· ≤ ·)) Finset.univ ho
  exact ⟨hf, fun i hi => hw i hi (by simp)⟩

/-- The separator of Lemma 6.2: every allowed tuple has exactly one disagreement
with the unwanted closure tuple. No affine separator or representation is assumed. -/
theorem greedy_separator [LinearOrder V] (R : Finset (V → Bool)) (hR : DimensionOne R)
    (y : V → Bool) (hy : y ∈ closure R) (hn : y ∉ R) :
    3 ≤ (greedyScope R y).card ∧
      (∀ x ∈ R, ExactOne.Holds (greedyScope R y) (fun i => !(y i)) x) ∧
      ¬ ExactOne.Holds (greedyScope R y) (fun i => !(y i)) y := by
  classical
  let s := greedyScope R y
  obtain ⟨ho, hm⟩ := greedyScope_spec R y hn
  have hs : 3 ≤ s.card := by
    by_contra hn
    exact ho (projection hy s (by omega))
  have witness (i : V) (hi : i ∈ s) :
      ∃ x ∈ R, x i = !(y i) ∧ ∀ j ∈ s, j ≠ i → x j = y j := by
    obtain ⟨x, hx, hag⟩ := hm i hi
    have hxi : x i ≠ y i := by
      intro he
      apply ho
      exact ⟨x, hx, fun j hj => by
        by_cases hji : j = i
        · simpa [hji] using he
        · exact @hag j (Finset.mem_erase.mpr ⟨hji, hj⟩)⟩
    refine ⟨x, hx, ?_, fun j hj hji => @hag j (Finset.mem_erase.mpr ⟨hji, hj⟩)⟩
    cases hx : x i <;> cases hy : y i <;> simp_all
  refine ⟨hs, ?_, ?_⟩
  · intro x hx
    have hd : ∃ i ∈ s, x i ≠ y i := by
      by_contra hn
      push Not at hn
      exact ho ⟨x, hx, hn⟩
    obtain ⟨i, hi, hxi⟩ := hd
    have hxip : x i = !(y i) := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    refine ⟨i, hi, hxip, fun j hj hxj => ?_⟩
    by_contra hji
    have hij : i ≠ j := Ne.symm hji
    obtain ⟨k, hk, hki, hkj⟩ : ∃ k ∈ s, k ≠ i ∧ k ≠ j := by
      have hc : 0 < (s \ {i, j}).card := by
        have hb : ({i, j} : Finset V).card ≤ 2 := by simp [hij]
        have hd := Finset.card_sdiff_add_card_inter s {i, j}
        have he := Finset.card_le_card (Finset.inter_subset_right : s ∩ {i, j} ⊆ {i, j})
        omega
      obtain ⟨k, hk⟩ := Finset.card_pos.mp hc
      simpa only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        not_or] using (show ∃ k, k ∈ s \ {i, j} from ⟨k, hk⟩)
    obtain ⟨xi, hxiR, hii, hij'⟩ := witness i hi
    obtain ⟨xj, hxjR, hjj, hji'⟩ := witness j hj
    obtain ⟨xk, hxkR, _, hki'⟩ := witness k hk
    have hp (a b : Bool) : ∃ z ∈ R, z i = a ∧ z j = b := by
      have h₁ := hij' j hj hji
      have h₂ := hji' i hi hij
      have h₃ := hki' i hi (Ne.symm hki)
      have h₄ := hki' j hj (Ne.symm hkj)
      by_cases ha : a = y i <;> by_cases hb : b = y j
      · exact ⟨xk, hxkR, h₃.trans ha.symm, h₄.trans hb.symm⟩
      · refine ⟨xj, hxjR, h₂.trans ha.symm, ?_⟩
        cases hb' : b <;> cases hy' : y j <;> simp_all
      · refine ⟨xi, hxiR, ?_, h₁.trans hb.symm⟩
        cases ha' : a <;> cases hy' : y i <;> simp_all
      · refine ⟨x, hx, ?_, ?_⟩
        · cases ha' : a <;> cases hy' : y i <;> simp_all
        · cases hb' : b <;> cases hy' : y j <;> simp_all
    exact no_pair R hR hij hp
  · rintro ⟨i, _, hi, _⟩
    cases h : y i <;> simp_all

open scoped Classical in
/-- One separator per unwanted closure tuple, derived from the table. -/
@[expose] def separatorScope [LinearOrder V] (R : Finset (V → Bool))
    (y : ↥(closure R \ R)) : Finset V :=
  greedyScope R y

/-- Each constructed equation holds on the table and excludes its own index. -/
theorem separatorScope_spec [LinearOrder V] (R : Finset (V → Bool)) (hR : DimensionOne R)
    (y : ↥(closure R \ R)) :
    3 ≤ (separatorScope R y).card ∧
      (∀ x ∈ R, ExactOne.Holds (separatorScope R y) (fun i => !(y.val i)) x) ∧
      ¬ ExactOne.Holds (separatorScope R y) (fun i => !(y.val i)) y.val := by
  classical
  exact greedy_separator R hR y (Finset.mem_sdiff.mp y.property).1
    (Finset.mem_sdiff.mp y.property).2

section Binary

variable [LinearOrder V]

open scoped Classical in
/-- Forbid exactly the missing unary/binary patterns (duplicates removed).
The empty clause also handles an empty input table. -/
@[expose] def binary (R : Finset (V → Bool)) : CNF V :=
  ((ExactOne.binaryUniverse (V := V)).filter fun c => ∀ x ∈ R, c.eval x = true).dedup

/-- Compute binary restrictions by scanning only the explicitly listed table.
This is the compiler implementation of `binary`: the default decidability of a
finite forall in that definition would enumerate the entire Boolean cube. -/
@[expose] def scanBinary (R : Finset (V → Bool)) : CNF V :=
  ((ExactOne.binaryUniverse (V := V)).filter fun c =>
    @decide (∀ x ∈ R, c.eval x = true) Finset.decidableDforallFinset).dedup

/-- Replacing generic finite forall with bounded table scanning preserves syntax,
not just satisfying assignments. The compiler uses this proved equality. -/
@[csimp] theorem binary_eq_scanBinary : @binary = @scanBinary := by
  funext V _ _ R
  unfold binary scanBinary
  congr 1
  apply List.filter_congr
  intro c _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

/-- The table's side formula has width at most two. -/
theorem binary_width (R : Finset (V → Bool)) (c : Clause V) (hc : c ∈ binary R) :
    c.length ≤ 2 := by
  classical
  exact ExactOne.binaryUniverse_width c (List.mem_filter.mp (List.mem_dedup.mp hc)).1

/-- A quadratic clause budget independent of the number of listed tuples. -/
theorem binary_length (R : Finset (V → Bool)) :
    (binary R).length ≤ 1 + 2 * Fintype.card V + 4 * Fintype.card V ^ 2 := by
  classical
  exact ExactOne.dedup_binary_length _ fun c hc =>
    ExactOne.binaryUniverse_width c (List.mem_filter.mp hc).1

/-- The actual side CNF defines precisely the binary closure. -/
theorem binary_eval (R : Finset (V → Bool)) (y : V → Bool) :
    (binary R).eval y = true ↔ y ∈ closure R := by
  classical
  rw [CNF.eval_eq_true_iff]
  constructor
  · intro h
    rw [mem_closure]
    intro s hs
    by_contra hn
    have hc : Clause.exclude s y ∈ binary R := by
      apply List.mem_dedup.mpr
      apply List.mem_filter.mpr
      refine ⟨ExactOne.mem_binaryUniverse _ (by simpa using hs), ?_⟩
      simp only [decide_eq_true_eq]
      intro x hx
      rw [Clause.eval_exclude_eq_true_iff]
      by_contra he
      push Not at he
      exact hn ⟨x, hx, he⟩
    obtain ⟨i, _, hi⟩ := Clause.eval_exclude_eq_true_iff _ _ _ |>.mp (h _ hc)
    exact hi rfl
  · intro hy c hc
    have hall := (List.mem_filter.mp (List.mem_dedup.mp hc)).2
    have hw := binary_width R c hc
    let s : Finset V := (c.map Prod.fst).toFinset
    have hs : s.card ≤ 2 := (List.toFinset_card_le _).trans (by simpa using hw)
    obtain ⟨x, hx, hag⟩ := projection hy s hs
    obtain ⟨l, hl, he⟩ := (Clause.eval_eq_true_iff x c).mp (of_decide_eq_true hall x hx)
    apply (Clause.eval_eq_true_iff y c).mpr
    refine ⟨l, hl, ?_⟩
    have hg := @hag l.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, rfl⟩))
    simpa only [Literal.eval, hg] using he

/-- Theorem 1.3's pointwise representation on exactly the original coordinates.
It covers empty tables too; no new variables or multiplicities are introduced. -/
theorem representation_iff (R : Finset (V → Bool)) (hR : DimensionOne R) (x : V → Bool) :
    x ∈ R ↔ (binary R).eval x = true ∧
      ∀ y : ↥(closure R \ R),
        ExactOne.Holds (separatorScope R y) (fun i => !(y.val i)) x := by
  classical
  constructor
  · intro hx
    exact ⟨(binary_eval R x).mpr (subset_closure R hx),
      fun y => (separatorScope_spec R hR y).2.1 x hx⟩
  · rintro ⟨hb, he⟩
    by_contra hn
    let y : ↥(closure R \ R) := ⟨x, Finset.mem_sdiff.mpr ⟨(binary_eval R x).mp hb, hn⟩⟩
    exact (separatorScope_spec R hR y).2.2 (he y)

/-- Both quantitative budgets of the representation are derived from the table. -/
theorem representation_bounds (R : Finset (V → Bool)) (hR : DimensionOne R) :
    (binary R).length ≤ 1 + 2 * Fintype.card V + 4 * Fintype.card V ^ 2 ∧
      Fintype.card ↥(closure R \ R) ≤ Fintype.card V + 1 - R.card := by
  classical
  exact ⟨binary_length R, by simpa only [Fintype.card_coe] using separators_bound R hR⟩

end Binary

end Cslib.Logic.PL.VCOne
