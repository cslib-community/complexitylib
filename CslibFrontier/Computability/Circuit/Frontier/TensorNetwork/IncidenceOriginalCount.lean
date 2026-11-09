/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceSelectionSum
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceCountReconstruction
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceSelectionSum
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceGroupCoefficients
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceColumnWeights
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryCorrectness
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceCountReconstruction
import all CslibFrontier.Computability.GenericRAM.Native.HeavyBranchFold
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Original assignment-count reconstruction from native incidence contractions

Transport the capped block families through the actual residue-class/local-test-position
bijection to original equation subset families. Canonical listed integer monomial counts equal
the finite equation lifts. The transport preserves total incidence degree, per-test coefficient
products and the weight of every declared variable, including free variables.

The polynomial identity is exact over integers at every cap; the listed degree bound is needed
only for count recovery at the computed cap. The native count theorem requires positive declared
size. `IncidenceOriginalCounter` supplies the separate zero-variable direct dispatch.
High-incidence branching, parity queries, sparsification and sharper time composition remain
separate from this original-input semantic endpoint.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.selectionPolynomial_eq_incidenceSum`: exact transport
  to original equations, without an assumed polynomial/output identity.
* `Cslib.Circuits.Frontier.IncidenceNetwork.trunc_selectionPolynomial_eq_systemIncidencePolynomial`:
  the computed truncated-ring bridge.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sumArrays_eq_rootCount`: actual native scalar output
  equals the original assignment count on canonical, declared, degree-bounded input with n≥1.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp.55–56, equations (D.1)–(D.2) and the
  test-group coefficient/declared-variable weight/contraction-sum paragraphs.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString Cslib.GenericRAM Cslib.Complexity Polynomial Finset

private abbrev GroupTest (J a : ℕ) := Σ g : Fin J, Fin (List.residueClass J a g).length

private def originalTest (J a : ℕ) (p : GroupTest J a) : Fin a :=
  ⟨(List.residueClass J a p.1).get p.2,
    List.mem_range.mp (List.mem_filter.mp (List.get_mem _ _)).1⟩

private theorem originalTest_mod (J a : ℕ) (p : GroupTest J a) :
    (originalTest J a p).val % J = p.1.val :=
  of_decide_eq_true (List.mem_filter.mp (List.get_mem (List.residueClass J a p.1) p.2)).2

private theorem originalTest_bijective (J a : ℕ) (hJ : 0 < J) :
    Function.Bijective (originalTest J a) := by
  constructor
  · intro p q he
    rcases p with ⟨g, t⟩
    rcases q with ⟨h, u⟩
    have hg : g = h := Fin.ext ((originalTest_mod J a ⟨g, t⟩).symm.trans
      ((congrArg (fun i : Fin a => i.val % J) he).trans (originalTest_mod J a ⟨h, u⟩)))
    subst h
    have ht : t = u := ((List.nodup_range.filter _).injective_get (congrArg Fin.val he))
    subst u
    rfl
  · intro i
    let g : Fin J := ⟨i % J, Nat.mod_lt _ hJ⟩
    have hi : i.val ∈ List.residueClass J a g := by
      simp [List.residueClass, g, i.isLt]
    obtain ⟨t, ht, he⟩ := List.getElem_of_mem hi
    exact ⟨⟨g, ⟨t, ht⟩⟩, Fin.ext he⟩

private noncomputable def originalTestEquiv (J a : ℕ) (hJ : 0 < J) : GroupTest J a ≃ Fin a :=
  Equiv.ofBijective (originalTest J a) (originalTest_bijective J a hJ)

private theorem mobius_image {α β M : Type*} [DecidableEq β]
    [AddCommGroup M] (e : α ↪ β) (f : Finset β → M) (S : Finset α) :
    subsetMobius f (S.image e) = subsetMobius (fun T => f (T.image e)) S := by
  classical
  rw [subsetMobius, subsetMobius, powerset_image, sum_image]
  · apply sum_congr rfl
    intro T _
    rw [card_image_of_injective S e.injective, card_image_of_injective T e.injective]
  · exact fun T _ U _ h => Finset.image_injective e.injective h

private def tag {n : ℕ} (t : ℕ) (v : Fin n) : ℕ × ℕ := (t, v.val)

private theorem tag_injective (n t : ℕ) : Function.Injective (tag (n := n) t) :=
  fun _ _ h => Fin.ext (congrArg Prod.snd h)

private theorem monomialsIn_image {n : ℕ} {eq : List (List ℕ)}
    (hc : IsCanonicalEquation eq) (hv : ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (t : ℕ) (S : Finset (Fin n)) :
    monomialsIn eq t (S.image (tag t)).toList =
      #{M ∈ HeavyBranchFold.toFinsetEquation n eq | M ⊆ S} := by
  classical
  let f (m : List ℕ) := univ.filter fun i : Fin n => i.val ∈ m
  have hinj : ∀ m ∈ eq, ∀ u ∈ eq, f m = f u → m = u := by
    intro m hm u hu he
    apply (hc.2 m hm).eq_of_toFinset_eq (hc.2 u hu)
    ext v
    simp only [List.mem_toFinset]
    constructor
    · intro h
      have hs : (⟨v, hv m hm v h⟩ : Fin n) ∈ f u :=
        he ▸ mem_filter.mpr ⟨mem_univ _, h⟩
      exact (mem_filter.mp hs).2
    · intro h
      have hs : (⟨v, hv u hu v h⟩ : Fin n) ∈ f m :=
        he.symm ▸ mem_filter.mpr ⟨mem_univ _, h⟩
      exact (mem_filter.mp hs).2
  have hn : (eq.map f).Nodup := hc.1.map_on hinj
  change _ = #((eq.map f).toFinset.filter (fun M => M ⊆ S))
  have he : ((eq.map f).filter (fun M => decide (M ⊆ S))).toFinset =
      (eq.map f).toFinset.filter (fun M => M ⊆ S) := by
    ext M
    simp
  rw [← he, List.toFinset_card_of_nodup (hn.filter _),
    ← List.countP_eq_length_filter, List.countP_map]
  unfold monomialsIn
  apply List.countP_congr
  intro m hm
  simp only [List.all_eq_true, decide_eq_true_eq, Finset.mem_toList, mem_image,
    tag, Prod.mk.injEq, true_and, Function.comp_apply, subset_iff, f, mem_filter,
    mem_univ, true_and]
  constructor
  · intro h v hvm
    obtain ⟨w, hw, he⟩ := h v hvm
    exact (Fin.ext he : w = v) ▸ hw
  · intro h v hvm
    exact ⟨⟨v, hv m hm v hvm⟩, h hvm, rfl⟩

private theorem mem_pairInc_tag (J n : ℕ) (sys : List (List (List ℕ)))
    (g : Fin J) (t : Fin (List.residueClass J sys.length g).length) (v : Fin n) (h : ℕ) :
    tag t v ∈ pairInc J sys g h ↔ v.val % J = h ∧
      v ∈ equationScope (HeavyBranchFold.toFinsetEquation n
        sys[(originalTest J sys.length ⟨g, t⟩).val]) := by
  have he : sys.getD (List.residueClass J sys.length g)[t.val] [] =
      sys[(originalTest J sys.length ⟨g, t⟩).val] :=
    List.getD_eq_getElem _ _ (originalTest J sys.length ⟨g, t⟩).isLt
  have hs : v ∈ equationScope (HeavyBranchFold.toFinsetEquation n
      sys[(originalTest J sys.length ⟨g, t⟩).val]) ↔
      v.val ∈ equationVars sys[(originalTest J sys.length ⟨g, t⟩).val] := by
    simp only [equationScope, HeavyBranchFold.toFinsetEquation, mem_biUnion,
      List.mem_toFinset, List.mem_map, mem_equationVars]
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, hvm⟩
      exact ⟨m, hm, (mem_filter.mp hvm).2⟩
    · rintro ⟨m, hm, hvm⟩
      exact ⟨_, ⟨m, hm, rfl⟩, mem_filter.mpr ⟨mem_univ _, hvm⟩⟩
  rw [hs]
  simp only [pairInc, List.mem_flatMap, List.exists_mem_zipIdx', List.mem_map,
    List.mem_filter, decide_eq_true_eq, tag, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, a, ⟨ha, hh⟩, hit, hav⟩
    subst i
    subst a
    exact ⟨hh, he ▸ ha⟩
  · rintro ⟨hh, ha⟩
    exact ⟨t, t.isLt, v, ⟨he.symm ▸ ha, hh⟩, rfl, rfl⟩

private noncomputable def rowSet {J n : ℕ} (sys : List (List (List ℕ)))
    (S : GroupTest J sys.length → Finset (Fin n)) (g : Fin J) : Finset (ℕ × ℕ) :=
  univ.biUnion fun t : Fin (List.residueClass J sys.length g).length =>
    (S ⟨g, t⟩).image (tag t)

private theorem mem_rowSet {J n : ℕ} (sys : List (List (List ℕ)))
    (S : GroupTest J sys.length → Finset (Fin n)) (g : Fin J) (p : ℕ × ℕ) :
    p ∈ rowSet sys S g ↔ ∃ t, ∃ v ∈ S ⟨g, t⟩, tag t v = p := by
  classical
  simp [rowSet]

private theorem rowSet_filter {J n : ℕ} (sys : List (List (List ℕ)))
    (S : GroupTest J sys.length → Finset (Fin n)) (g : Fin J)
    (t : Fin (List.residueClass J sys.length g).length) :
    (rowSet sys S g).filter (fun p => p.1 = t.val) = (S ⟨g, t⟩).image (tag t) := by
  classical
  ext p
  simp only [mem_filter, mem_rowSet, mem_image]
  constructor
  · rintro ⟨⟨u, v, hv, rfl⟩, he⟩
    have hu : u = t := Fin.ext he
    subst u
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨t, v, hv, rfl⟩, rfl⟩

private theorem local_tests_get (J : ℕ) (sys : List (List (List ℕ)))
    (g : Fin J) (t : Fin (List.residueClass J sys.length g).length) :
    ((List.residueClass J sys.length g).map (sys.getD · [])).getD t [] =
      sys[(originalTest J sys.length ⟨g, t⟩).val] := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
  exact List.getD_eq_getElem _ _ (originalTest J sys.length ⟨g, t⟩).isLt

private theorem rowSet_coefficient {J n : ℕ} (sys : List (List (List ℕ)))
    (hc : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (S : GroupTest J sys.length → Finset (Fin n)) (g : Fin J) (ℓ : ℕ) :
    subsetMobius
      (rowPolynomial ℓ ((List.residueClass J sys.length g).map (sys.getD · [])))
      (rowSet sys S g) =
    ∏ t : Fin (List.residueClass J sys.length g).length,
      parityCoeff ℓ (HeavyBranchFold.toFinsetEquation n
        sys[(originalTest J sys.length ⟨g, t⟩).val]) (S ⟨g, t⟩) := by
  classical
  rw [subsetMobius_rowPolynomial]
  · simp only [List.length_map]
    rw [← Fin.prod_univ_eq_prod_range]
    apply prod_congr rfl
    intro t _
    rw [rowSet_filter, local_tests_get]
    have hi := mobius_image (⟨tag t, tag_injective n t⟩ : Fin n ↪ ℕ × ℕ)
      (fun T => parityFactor ℓ (monomialsIn
        sys[(originalTest J sys.length ⟨g, t⟩).val] t T.toList : ℤ)) (S ⟨g, t⟩)
    simp only [Function.Embedding.coeFn_mk] at hi
    rw [hi]
    unfold parityCoeff
    congr 1
    funext T
    congr 1
    exact_mod_cast monomialsIn_image
      (hc _ (List.getElem_mem (originalTest J sys.length ⟨g, t⟩).isLt))
      (hv _ (List.getElem_mem (originalTest J sys.length ⟨g, t⟩).isLt)) t T
  · intro p hp
    obtain ⟨t, v, _, rfl⟩ := (mem_rowSet sys S g p).mp hp
    simpa only [List.length_map, tag] using t.isLt

private noncomputable def partsOf {J n : ℕ} (sys : List (List (List ℕ)))
    (S : GroupTest J sys.length → Finset (Fin n)) (b : Fin (J * J)) : List (ℕ × ℕ) :=
  (pairInc J sys (b / J) (b % J)).filter (fun p => decide (p ∈ rowSet sys S b.divNat))

private theorem partsOf_mem {J n : ℕ} (sys : List (List (List ℕ)))
    (S : GroupTest J sys.length → Finset (Fin n)) :
    partsOf sys S ∈ selectionFamilies J sys := by
  rw [mem_selectionFamilies]
  intro b
  exact List.filter_sublist

private theorem mem_selectionRow {J : ℕ} (parts : Fin (J * J) → List (ℕ × ℕ))
    (g : Fin J) (p : ℕ × ℕ) :
    p ∈ selectionRow J parts g ↔
      ∃ h : Fin J, p ∈ parts ⟨g * J + h, by nlinarith [g.isLt, h.isLt]⟩ := by
  simp [selectionRow]

private theorem block_div (J : ℕ) (hJ : 0 < J) (g h : Fin J) :
    ((⟨g * J + h, by nlinarith [g.isLt, h.isLt]⟩ : Fin (J * J)).divNat : Fin J) = g := by
  apply Fin.ext
  change (g.val * J + h.val) / J = g.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt h.isLt, Nat.zero_add]

private theorem block_mod (J : ℕ) (g h : Fin J) :
    (g.val * J + h.val) % J = h.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.isLt]

private theorem selectionRow_partsOf {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ))) (S : GroupTest J sys.length → Finset (Fin n))
    (hS : ∀ p, S p ⊆ equationScope
      (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val])) (g : Fin J) :
    (selectionRow J (partsOf sys S) g).toFinset = rowSet sys S g := by
  classical
  ext p
  rw [List.mem_toFinset, mem_selectionRow]
  constructor
  · rintro ⟨h, hp⟩
    have hm := of_decide_eq_true (List.mem_filter.mp hp).2
    simpa only [block_div J hJ g h] using hm
  · intro hp
    obtain ⟨t, v, hv, rfl⟩ := (mem_rowSet sys S g p).mp hp
    let h : Fin J := ⟨v % J, Nat.mod_lt _ hJ⟩
    refine ⟨h, List.mem_filter.mpr ⟨?_, ?_⟩⟩
    · have hd : (g.val * J + h.val) / J = g.val :=
        congrArg Fin.val (block_div J hJ g h)
      change tag t v ∈ pairInc J sys _ _
      rw [hd, block_mod]
      exact (mem_pairInc_tag J n sys g t v h).mpr ⟨rfl, hS ⟨g, t⟩ hv⟩
    · apply decide_eq_true
      simpa only [block_div J hJ g h] using (mem_rowSet sys S g (tag t v)).mpr ⟨t, v, hv, rfl⟩

private noncomputable def familyOf {J n a : ℕ}
    (parts : Fin (J * J) → List (ℕ × ℕ)) (p : GroupTest J a) : Finset (Fin n) :=
  univ.filter fun v => tag p.2 v ∈ selectionRow J parts p.1

private theorem familyOf_partsOf {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ))) (S : GroupTest J sys.length → Finset (Fin n))
    (hS : ∀ p, S p ⊆ equationScope
      (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val])) :
    familyOf (a := sys.length) (partsOf sys S) = S := by
  classical
  funext p
  ext v
  simp only [familyOf, mem_filter, mem_univ, true_and, ← List.mem_toFinset,
    selectionRow_partsOf hJ sys S hS, mem_rowSet]
  constructor
  · rintro ⟨t, w, hw, he⟩
    have ht : t = p.2 := Fin.ext (congrArg Prod.fst he)
    have hwv : w = v := Fin.ext (congrArg Prod.snd he)
    subst t
    subst w
    exact hw
  · intro hv
    exact ⟨p.2, v, hv, rfl⟩

private theorem selectionRow_sublist {J : ℕ} (sys : List (List (List ℕ)))
    (parts : Fin (J * J) → List (ℕ × ℕ)) (hp : parts ∈ selectionFamilies J sys) (g : Fin J)
    (hJ : 0 < J) :
    (selectionRow J parts g).Sublist ((rowBlocks J sys [] g).flatMap Prod.fst) := by
  rw [rowBlocks, List.flatMap_map, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  unfold selectionRow
  apply List.Sublist.flatMap_right
  intro h _
  have hb := (mem_selectionFamilies J sys parts).mp hp
    ⟨g * J + h, by nlinarith [g.isLt, h.isLt]⟩
  have hd : (g.val * J + h.val) / J = g.val := congrArg Fin.val (block_div J hJ g h)
  simpa only [hd, block_mod] using hb

private theorem selectionRow_declared {J n : ℕ} (sys : List (List (List ℕ)))
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (parts : Fin (J * J) → List (ℕ × ℕ)) (hp : parts ∈ selectionFamilies J sys)
    (g : Fin J) (hJ : 0 < J) {p : ℕ × ℕ} (hpm : p ∈ selectionRow J parts g) :
    p.1 < (List.residueClass J sys.length g).length ∧ p.2 < n := by
  obtain ⟨h, hh⟩ := (mem_selectionRow parts g p).mp hpm
  have hb := ((mem_selectionFamilies J sys parts).mp hp
    ⟨g * J + h, by nlinarith [g.isLt, h.isLt]⟩).subset hh
  have hd : (g.val * J + h.val) / J = g.val :=
        congrArg Fin.val (block_div J hJ g h)
  simp only [hd, block_mod] at hb
  refine ⟨first_lt_of_mem_pairInc hb, ?_⟩
  obtain ⟨q, hq, hqp⟩ := List.mem_flatMap.mp hb
  obtain ⟨v, hvm, rfl⟩ := List.mem_map.mp hqp
  have hi : q.1 < sys.length :=
    List.mem_range.mp (List.mem_filter.mp (List.fst_mem_of_mem_zipIdx hq)).1
  rw [List.getD_eq_getElem _ _ hi] at hvm
  obtain ⟨m, hm, hvv⟩ := mem_equationVars.mp (List.mem_filter.mp hvm).1
  exact hv _ (List.getElem_mem hi) m hm v hvv

private theorem familyOf_scope {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ))) (parts : Fin (J * J) → List (ℕ × ℕ))
    (hp : parts ∈ selectionFamilies J sys) :
    ∀ p, familyOf (n := n) parts p ⊆ equationScope
      (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val]) := by
  intro p v hv
  have hvp := (mem_filter.mp hv).2
  obtain ⟨h, hh⟩ := (mem_selectionRow parts p.1 (tag p.2 v)).mp hvp
  have hb := ((mem_selectionFamilies J sys parts).mp hp
    ⟨p.1 * J + h, by nlinarith [p.1.isLt, h.isLt]⟩).subset hh
  have hd : (p.1.val * J + h.val) / J = p.1.val :=
    congrArg Fin.val (block_div J hJ p.1 h)
  rw [hd, block_mod] at hb
  exact ((mem_pairInc_tag J n sys p.1 p.2 v h).mp hb).2

private theorem rowSet_familyOf {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ)))
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (parts : Fin (J * J) → List (ℕ × ℕ)) (hp : parts ∈ selectionFamilies J sys) (g : Fin J) :
    rowSet sys (familyOf (n := n) parts) g = (selectionRow J parts g).toFinset := by
  classical
  ext p
  rw [mem_rowSet, List.mem_toFinset]
  constructor
  · rintro ⟨t, v, hv, rfl⟩
    exact (mem_filter.mp hv).2
  · intro hpm
    have hd := selectionRow_declared sys hv parts hp g hJ hpm
    exact ⟨⟨p.1, hd.1⟩, ⟨p.2, hd.2⟩, mem_filter.mpr ⟨mem_univ _, hpm⟩, rfl⟩

private theorem filter_of_sublist {α : Type*} [DecidableEq α] {xs ys : List α}
    (hn : xs.Nodup) (hy : ys.Sublist xs) :
    xs.filter (fun a => decide (a ∈ ys)) = ys := by
  induction hy with
  | slnil => rfl
  | @cons ys xs a h ih =>
    have ha : a ∉ ys := fun hm => (List.nodup_cons.mp hn).1 (h.subset hm)
    simpa only [List.filter_cons, decide_eq_false ha, Bool.false_eq_true, ↓reduceIte] using
      ih (List.nodup_cons.mp hn).2
  | @cons_cons ys xs a h ih =>
    rw [List.filter_cons, ite_eq_left (by simp)]
    apply congrArg (a :: ·)
    calc
      xs.filter (fun b => decide (b ∈ a :: ys)) = xs.filter (fun b => decide (b ∈ ys)) := by
        apply List.filter_congr
        intro b hb
        have hbne : b ≠ a := fun he => (List.nodup_cons.mp hn).1 (he ▸ hb)
        simp [hbne]
      _ = ys := ih (List.nodup_cons.mp hn).2

private theorem sublists_eq_of_mem {α : Type*} {xs ys zs : List α}
    (hn : xs.Nodup) (hy : ys.Sublist xs) (hz : zs.Sublist xs)
    (he : ∀ x, x ∈ ys ↔ x ∈ zs) : ys = zs := by
  classical
  rw [← filter_of_sublist hn hy, ← filter_of_sublist hn hz]
  apply List.filter_congr
  intro x _
  simp [he x]

private theorem partsOf_familyOf {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ)))
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (parts : Fin (J * J) → List (ℕ × ℕ)) (hp : parts ∈ selectionFamilies J sys) :
    partsOf sys (familyOf (n := n) parts) = parts := by
  classical
  funext b
  apply sublists_eq_of_mem (nodup_pairInc _ _ _ _) List.filter_sublist
    ((mem_selectionFamilies J sys parts).mp hp b)
  intro p
  simp only [List.mem_filter, decide_eq_true_eq, rowSet_familyOf hJ sys hv parts hp,
    List.mem_toFinset]
  constructor
  · rintro ⟨hb, hr⟩
    obtain ⟨h, hh⟩ := (mem_selectionRow parts b.divNat p).mp hr
    have hhmod := mod_eq_of_mem_pairInc
      (((mem_selectionFamilies J sys parts).mp hp
        ⟨b.divNat * J + h, by nlinarith [b.divNat.isLt, h.isLt]⟩).subset hh)
    have hmod := mod_eq_of_mem_pairInc hb
    rw [block_mod] at hhmod
    have hheq : h.val = b.val % J := hhmod.symm.trans hmod
    have hbeq : (⟨b.divNat * J + h, by nlinarith [b.divNat.isLt, h.isLt]⟩ : Fin (J * J)) = b := by
      apply Fin.ext
      change b.val / J * J + h.val = b.val
      rw [hheq, Nat.div_add_mod']
    simpa only [hbeq] using hh
  · intro hpm
    refine ⟨((mem_selectionFamilies J sys parts).mp hp b).subset hpm, ?_⟩
    apply (mem_selectionRow parts b.divNat p).mpr
    refine ⟨b.modNat, ?_⟩
    have hbeq : (⟨b.divNat * J + b.modNat,
        by nlinarith [b.divNat.isLt, b.modNat.isLt]⟩ : Fin (J * J)) = b := by
      apply Fin.ext
      exact Nat.div_add_mod' b.val J
    simpa only [hbeq] using hpm

private theorem sum_row_lengths {J : ℕ} (parts : Fin (J * J) → List (ℕ × ℕ)) :
    (∑ g : Fin J, (selectionRow J parts g).length) = ∑ b, (parts b).length := by
  simp only [selectionRow, List.length_flatMap, ← Fin.sum_univ_def]
  have he := (finProdFinEquiv : Fin J × Fin J ≃ Fin (J * J)).sum_comp
    (fun b => (parts b).length)
  rw [Fintype.sum_prod_type] at he
  convert he using 2
  congr 1
  funext h
  congr 2
  apply Fin.ext
  simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

private theorem card_rowSet {J n : ℕ} (sys : List (List (List ℕ)))
    (S : GroupTest J sys.length → Finset (Fin n)) (g : Fin J) :
    #(rowSet sys S g) = ∑ t, #(S ⟨g, t⟩) := by
  classical
  rw [rowSet, card_biUnion]
  · exact sum_congr rfl fun t _ => card_image_of_injective _ (tag_injective n t)
  · intro t _ u _ htu
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨v, _, hv⟩ := mem_image.mp hp
    obtain ⟨w, _, hw⟩ := mem_image.mp hq
    exact htu (Fin.ext (congrArg Prod.fst (hv.trans hw.symm)))

private theorem degree_partsOf {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ))) (S : GroupTest J sys.length → Finset (Fin n))
    (hS : ∀ p, S p ⊆ equationScope
      (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val])) :
    (∑ b, (partsOf sys S b).length) = ∑ p, #(S p) := by
  rw [← sum_row_lengths, Fintype.sum_sigma]
  apply sum_congr rfl
  intro g _
  rw [← card_rowSet sys S g, ← selectionRow_partsOf hJ sys S hS]
  symm
  apply List.toFinset_card_of_nodup
  exact (nodup_rowBlocks J sys [] g).sublist
    (selectionRow_sublist sys (partsOf sys S) (partsOf_mem sys S) g hJ)

private theorem used_partsOf {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ))) (S : GroupTest J sys.length → Finset (Fin n))
    (hS : ∀ p, S p ⊆ equationScope
      (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val])) (v : Fin n) :
    v.val ∈ ((List.finRange J).flatMap (selectionRow J (partsOf sys S))).map Prod.snd ↔
      ∃ p, v ∈ S p := by
  classical
  simp only [List.mem_map, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨p, ⟨g, hp⟩, hval⟩
    have hp' : p ∈ rowSet sys S g := by
      rw [← selectionRow_partsOf hJ sys S hS, List.mem_toFinset]
      exact hp
    obtain ⟨t, w, hw, he⟩ := (mem_rowSet sys S g p).mp hp'
    have hwv : w = v := Fin.ext ((congrArg Prod.snd he).trans hval)
    exact ⟨⟨g, t⟩, hwv ▸ hw⟩
  · rintro ⟨⟨g, t⟩, hv⟩
    refine ⟨tag t v, ⟨g, ?_⟩, rfl⟩
    rw [← List.mem_toFinset, selectionRow_partsOf hJ sys S hS]
    exact (mem_rowSet sys S g _).mpr ⟨t, v, hv, rfl⟩

private theorem weight_partsOf {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ))) (S : GroupTest J sys.length → Finset (Fin n))
    (hS : ∀ p, S p ⊆ equationScope
      (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val])) :
    C ((2 : ℤ) ^ unselectedCount (List.range n)
        ((List.finRange J).flatMap (selectionRow J (partsOf sys S)))) =
      (incidenceWeight S : ℤ[X]) := by
  classical
  rw [unselectedCount_eq_sum, ← List.map_coe_finRange_eq_range, List.map_map,
    ← Fin.sum_univ_def]
  simp only [Function.comp_def, used_partsOf hJ sys S hS]
  rw [incidenceWeight]
  simp only [← prod_pow_eq_pow_sum, map_prod]
  apply prod_congr rfl
  intro v _
  by_cases hv : ∃ p, v ∈ S p <;> simp [hv]

private theorem selectionPolynomial_eq_groupSum {J n : ℕ} (hJ : 0 < J)
    (sys : List (List (List ℕ)))
    (hc : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) (ℓ K : ℕ) :
    selectionPolynomial ℓ J K n sys = incidenceSum
      (fun p : GroupTest J sys.length => equationScope
        (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val]))
      (fun p => parityCoeff ℓ
        (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val])) K := by
  classical
  let I := fun p : GroupTest J sys.length => equationScope
    (HeavyBranchFold.toFinsetEquation n sys[(originalTest J sys.length p).val])
  have hs (S : GroupTest J sys.length → Finset (Fin n))
      (h : S ∈ Fintype.piFinset (fun p => (I p).powerset)) : ∀ p, S p ⊆ I p := by
    intro p
    exact mem_powerset.mp (Fintype.mem_piFinset.mp h p)
  rw [selectionPolynomial, incidenceSum]
  symm
  apply sum_bij (fun S _ => partsOf sys S)
  · intro S hS
    obtain ⟨hm, hd⟩ := mem_filter.mp hS
    exact mem_filter.mpr ⟨partsOf_mem sys S, (degree_partsOf hJ sys S (hs S hm)) ▸ hd⟩
  · intro S hS T hT he
    have hss := familyOf_partsOf hJ sys S (hs S (mem_filter.mp hS).1)
    have htt := familyOf_partsOf hJ sys T (hs T (mem_filter.mp hT).1)
    exact hss.symm.trans ((congrArg (familyOf (a := sys.length)) he).trans htt)
  · intro parts hp
    obtain ⟨hm, hd⟩ := mem_filter.mp hp
    let S := familyOf (n := n) (a := sys.length) parts
    have hsc : ∀ p, S p ⊆ I p := familyOf_scope hJ sys parts hm
    have he : partsOf sys S = parts := partsOf_familyOf hJ sys hv parts hm
    have hdeg := degree_partsOf hJ sys S hsc
    rw [he] at hdeg
    refine ⟨S, mem_filter.mpr ⟨?_, hdeg ▸ hd⟩, he⟩
    exact Fintype.mem_piFinset.mpr fun p => mem_powerset.mpr (hsc p)
  · intro S hS
    have hsc := hs S (mem_filter.mp hS).1
    rw [weight_partsOf hJ sys S hsc]
    simp only [selectionRow_partsOf hJ sys S hsc, rowSet_coefficient sys hc hv]
    rw [Fintype.prod_sigma (fun p : GroupTest J sys.length =>
      parityCoeff ℓ (HeavyBranchFold.toFinsetEquation n
        sys[(originalTest J sys.length p).val]) (S p))]

/-- The complete capped family sum is the original per-equation incidence polynomial.
The proof transports local test positions, canonical integer lifts, degree and free-variable
weights. It is exact over integer polynomials, before truncation or modular reduction. -/
theorem selectionPolynomial_eq_incidenceSum {J n : ℕ} (hJ : 0 < J)
    {sys : List (List (List ℕ))}
    (hc : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) (ℓ K : ℕ) :
    selectionPolynomial ℓ J K n sys = incidenceSum
      (fun i : Fin sys.length => equationScope (HeavyBranchFold.toFinsetEquation n sys[i]))
      (fun i => parityCoeff ℓ (HeavyBranchFold.toFinsetEquation n sys[i])) K := by
  classical
  rw [selectionPolynomial_eq_groupSum hJ sys hc hv]
  let e := originalTestEquiv J sys.length hJ
  let P := fun i : Fin sys.length => HeavyBranchFold.toFinsetEquation n sys[i]
  change incidenceSum (fun p => equationScope (P (e p)))
    (fun p => parityCoeff ℓ (P (e p))) K = _
  rw [incidenceSum, incidenceSum]
  symm
  apply sum_bij (fun S _ => fun p : GroupTest J sys.length => S (e p))
  · intro S hS
    obtain ⟨hs, hd⟩ := mem_filter.mp hS
    apply mem_filter.mpr
    constructor
    · exact Fintype.mem_piFinset.mpr fun p => Fintype.mem_piFinset.mp hs (e p)
    · simpa only [e.sum_comp (fun i => #(S i))] using hd
  · intro S _ T _ he
    funext i
    have h := congrFun he (e.symm i)
    simpa only [e.apply_symm_apply] using h
  · intro T hT
    obtain ⟨hs, hd⟩ := mem_filter.mp hT
    refine ⟨fun i => T (e.symm i), mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      simpa only [e.apply_symm_apply] using Fintype.mem_piFinset.mp hs (e.symm i)
    · simpa only [e.symm.sum_comp (fun p => #(T p))] using hd
    · funext p
      exact congrArg T (e.symm_apply_apply p)
  · intro S _
    rw [e.prod_comp (fun i => parityCoeff ℓ (P i) (S i))]
    congr 1
    unfold incidenceWeight
    apply prod_congr rfl
    intro v _
    have he : (∃ p, v ∈ S (e p)) ↔ ∃ i, v ∈ S i := by
      constructor
      · rintro ⟨p, hp⟩
        exact ⟨e p, hp⟩
      · rintro ⟨i, hi⟩
        exact ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩
    by_cases h : ∃ i, v ∈ S i <;> simp [he, h]

/-- The precise truncated-ring bridge for the computed quarter-root grouping and degree cap.
Canonicality and declared-variable membership suffice even before using the listed degree bound. -/
theorem trunc_selectionPolynomial_eq_systemIncidencePolynomial {k n : ℕ}
    (hn : 1 ≤ n) {sys : List (List (List ℕ))}
    (hc : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) :
    truncRingHom (n + 1) (n + 1)
      (selectionPolynomial (n + 1) (Nat.ceilQuarter n) (degreeCap k (n, sys)) n sys) =
    truncRingHom (n + 1) (n + 1) (systemIncidencePolynomial k (n, sys)) := by
  rw [selectionPolynomial_eq_incidenceSum (Nat.ceilQuarter_pos hn) hc hv]
  rfl

/-- The actual native stream counts original assignments, including variables absent from every
scope. All incidence, coefficient and residue identities are derived; no answer is a premise. -/
theorem sumArrays_eq_rootCount {k n : ℕ} (hn : 1 ≤ n)
    {sys : List (List (List ℕ))}
    (hc : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hk : ∀ eq ∈ sys, ∀ m ∈ eq, m.length ≤ k) :
    sumArrays k (n, sys) = HeavyBranchFold.rootCount n sys := by
  rw [← sumArrays_eq_selectionResidue k (n, sys) hn,
    selectionPolynomial_eq_incidenceSum (Nat.ceilQuarter_pos hn) hc hv]
  exact rootCount_eq_incidenceResidue hc hv hk

end Cslib.Circuits.Frontier.IncidenceNetwork
