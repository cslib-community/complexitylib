/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.KServer.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Deterministic lower bound `k` for the `k`-server problem

This file proves the deterministic lower bound of [Manasse, McGeoch and Sleator, *Competitive
algorithms for server problems*][ManasseMcGeochSleator1990] (Theorem 6 with `h = k`, and
Corollary 7): on any metric space with at least `k + 1` points, no deterministic online `k`-server
algorithm is `c`-competitive for any `c < k`, whatever the additive constant. More generally no
rational ratio `p / q < k` is achievable (`exists_ratio_violation`). The argument follows the
source proof: a lazy online algorithm, its nemesis request sequence, and an ensemble of offline
algorithms whose average cost is a `1 / k` fraction of the online cost. The source theorem also
compares against `h < k` offline servers, giving `k / (k - h + 1)`; that case is not formalized.
See also [Borodin and El-Yaniv, *Online Computation and Competitive Analysis*, Chapter
10][BorodinElYaniv1998].

## Proof structure

1. **Lazy normalization (`lazify`, `cost_lazify_le`).** Any online strategy `A` can be simulated
   by one that moves at most one server per request, and only when the request is uncovered. By
   the triangle inequality this never costs more than `A`.
2. **Adversary.** Fix `k + 1` points `S` (the initial `k` distinct positions and one more point
   `z`). The adversary always requests the unique point of `S` not covered by the lazy simulation.
   The simulation then pays exactly the length of the request path, and at least `1` per request
   (`lazy_costFrom_ge`).
3. **Shadow schedules (`shadowStates`, `exists_shadow_le`).** For each initial server position
   there is an offline schedule that keeps exactly that point of `S` uncovered after the first
   request. When it must serve its hole it moves the server sitting on the previous request.
   Summed over the `k` holes, these schedules pay the path length once, plus the initial distances
   to `z` (`sum_holeCost`). So the cheapest pays at most a `1 / k` fraction.

## Main definitions

* `Cslib.DataStructure.KServer.lazify`: lazy normalization of an online strategy.
* `Cslib.DataStructure.KServer.shadowStates`: the offline shadow schedule.

## Main results

* `cost_lazify_le`: the lazy simulation never costs more than the original strategy.
* `exists_shadow_le`: some shadow schedule costs at most a `1 / k` fraction of the request path
  plus the initial distances to `z`.
* `exists_ratio_violation`: no rational ratio `p / q < k` with any additive constant.
* `not_isCompetitiveFrom_of_lt`, `not_isCompetitive_of_lt`, `not_isCompetitiveAnyInit_of_lt`:
  no integer ratio `c < k`.

## References

* [M. S. Manasse, L. A. McGeoch and D. D. Sleator, *Competitive algorithms for server
  problems*][ManasseMcGeochSleator1990]
* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
-/

public section

namespace Cslib.DataStructure.KServer

open Cslib.DataStructure.Online

variable {α : Type} (M : NatMetric α) {k : Nat}

/-! ### Lazy normalization -/

/-- One lazy response at current configuration `c` when the simulated strategy is at `a`: stay
if `r` is covered, otherwise move the server whose label covers `r` in `a`. -/
noncomputable def lazyNext (c a : Fin k → α) (r : α) : Fin k → α :=
  open Classical in
  if ∃ i, c i = r then c
  else if h : ∃ j, a j = r then Function.update c (Classical.choose h) r else c

private theorem moveCost_update_add_le (c a : Fin k → α) (j : Fin k) (r : α) (hj : a j = r) :
    moveCost M c (Function.update c j r) + moveCost M (Function.update c j r) a ≤
      moveCost M c a := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = j
  · subst hi
    simp only [Function.update_self, hj, M.dist_self, Nat.add_zero, le_refl]
  · simp only [Function.update_of_ne hi, M.dist_self, Nat.zero_add, le_refl]

theorem lazyNext_spec (c a : Fin k → α) (r : α) (ha : ∃ j, a j = r) :
    (∃ i, lazyNext c a r i = r) ∧
      (lazyNext c a r = c ∨ ∃ j, a j = r ∧ lazyNext c a r = Function.update c j r) := by
  classical
  unfold lazyNext
  by_cases hc : ∃ i, c i = r
  · simp only [hc, ↓reduceIte, true_or, and_true]
  · simp only [hc, ↓reduceIte, ha, ↓reduceDIte]
    refine ⟨⟨Classical.choose ha, Function.update_self _ _ _⟩, Or.inr ⟨_, Classical.choose_spec ha,
      rfl⟩⟩

/-- One lazy step costs no more than following the simulated strategy, measured with the
distance between the two configurations as a potential. -/
theorem moveCost_lazyNext_add_le (c a a' : Fin k → α) (r : α) (ha : ∃ j, a' j = r) :
    moveCost M c (lazyNext c a' r) + moveCost M (lazyNext c a' r) a' ≤
      moveCost M c a + moveCost M a a' := by
  have htri := moveCost_triangle M c a a'
  rcases (lazyNext_spec c a' r ha).2 with h | ⟨j, hj, h⟩
  · rw [h, moveCost_self]
    omega
  · rw [h]
    classical
    have := moveCost_update_add_le M c a' j r hj
    omega

/-- Lazy normalization of an online strategy: simulate `A` and move at most one server per
request, only when the request is uncovered. -/
noncomputable def lazify (A : DetStrategy (problem M k)) : DetStrategy (problem M k) where
  Mem := A.Mem × (Fin k → α)
  ValidMem x := A.ValidMem x.1
  project x := x.2
  init s := (A.init s, s)
  step x r := (A.step x.1 r, lazyNext x.2 (A.project (A.step x.1 r)) r)
  valid_init _ := ⟨(A.valid_init trivial).1, rfl⟩
  valid_step r hm := ⟨(A.valid_step r hm).1,
    (lazyNext_spec _ _ r (A.valid_step r hm).2).1⟩

private theorem costFrom_lazify_le (A : DetStrategy (problem M k)) (m : A.Mem) (hm : A.ValidMem m)
    (c : Fin k → α) (reqs : List α) :
    (lazify M A).costFrom (m, c) reqs ≤ A.costFrom m reqs + moveCost M c (A.project m) := by
  induction reqs generalizing m c with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    have hstep := A.valid_step r hm
    have h1 := ih (A.step m r) hstep.1 (lazyNext c (A.project (A.step m r)) r)
    have h2 := moveCost_lazyNext_add_le M c (A.project m) (A.project (A.step m r)) r hstep.2
    change moveCost M c (lazyNext c (A.project (A.step m r)) r) +
        (lazify M A).costFrom (A.step m r, lazyNext c (A.project (A.step m r)) r) rs ≤
      moveCost M (A.project m) (A.project (A.step m r)) + A.costFrom (A.step m r) rs +
        moveCost M c (A.project m)
    omega

/-- The lazy simulation never costs more than the original strategy. -/
theorem cost_lazify_le (A : DetStrategy (problem M k)) (s₀ : Fin k → α) (reqs : List α) :
    (lazify M A).cost s₀ reqs ≤ A.cost s₀ reqs := by
  rw [(lazify M A).cost_eq_costFrom trivial, A.cost_eq_costFrom trivial]
  have h := costFrom_lazify_le M A (A.init s₀) (A.valid_init trivial).1 s₀ reqs
  rw [(A.valid_init (P := problem M k) trivial).2, moveCost_self, Nat.add_zero] at h
  exact h

/-! ### Offline shadow schedules -/

section Shadow

variable [DecidableEq α]

/-- Move every server located at `x` to `y`. -/
def relocate (s : Fin k → α) (x y : α) : Fin k → α :=
  fun i => if s i = x then y else s i

/-- Shadow schedule: stay when the request is covered, otherwise move the server at the
previous request `q` to the new request. -/
def shadowStates (s : Fin k → α) (q : α) : List α → List (Fin k → α)
  | [] => []
  | r :: rs =>
    let s' := if ∃ i, s i = r then s else relocate s q r
    s' :: shadowStates s' r rs

/-- Cost of the shadow schedule whose uncovered point is `h`, after previous request `q`. -/
def holeCost (h q : α) : List α → Nat
  | [] => 0
  | r :: rs => if r = h then M.dist q r + holeCost q r rs else holeCost h r rs

/-- Length of the path `q, r₁, r₂, …`. -/
def pathLen (q : α) : List α → Nat
  | [] => 0
  | r :: rs => M.dist q r + pathLen r rs

private theorem moveCost_relocate {s : Fin k → α} (hs : Function.Injective s) {q r : α}
    (hq : ∃ i, s i = q) : moveCost M s (relocate s q r) = M.dist q r := by
  obtain ⟨i, rfl⟩ := hq
  unfold moveCost relocate
  rw [Fintype.sum_eq_single i]
  · simp only [↓reduceIte]
  · intro j hj
    have : s j ≠ s i := fun h => hj (hs h)
    simp only [this, ↓reduceIte, M.dist_self]

private theorem relocate_injective {s : Fin k → α} (hs : Function.Injective s) {q r : α}
    (hr : ∀ i, s i ≠ r) : Function.Injective (relocate s q r) := by
  intro i j hij
  unfold relocate at hij
  by_cases hi : s i = q <;> by_cases hj : s j = q <;>
    simp only [hi, hj, ↓reduceIte] at hij
  · exact hs (hi.trans hj.symm)
  · exact absurd hij.symm (hr j)
  · exact absurd hij (hr i)
  · exact hs hij

private theorem mem_range_relocate_iff {s : Fin k → α} {q r x : α} (hq : ∃ i, s i = q) :
    (∃ i, relocate s q r i = x) ↔ x = r ∨ (x ≠ q ∧ ∃ i, s i = x) := by
  obtain ⟨i₀, hi₀⟩ := hq
  unfold relocate
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : s i = q
    · simp only [h, ↓reduceIte] at hi
      exact Or.inl hi.symm
    · simp only [h, ↓reduceIte] at hi
      exact Or.inr ⟨hi ▸ h, i, hi⟩
  · rintro (rfl | ⟨hxq, i, rfl⟩)
    · exact ⟨i₀, by simp only [hi₀, ↓reduceIte]⟩
    · exact ⟨i, by simp only [hxq, ↓reduceIte]⟩

/-- If `s` covers exactly `S \ {h}` with distinct servers, and the previous request `q` lies in
`S \ {h}`, then the shadow schedule is valid on requests from `S` and costs `holeCost h q rs`. -/
theorem shadowStates_spec (S : Finset α) {rs : List α} (hrs : ∀ r ∈ rs, r ∈ S) :
    ∀ {s : Fin k → α} {h q : α}, Function.Injective s →
      (∀ x, (∃ i, s i = x) ↔ x ∈ S ∧ x ≠ h) → q ∈ S → q ≠ h →
      (problem M k).ValidSchedule s rs (shadowStates s q rs) ∧
        (problem M k).scheduleCost s rs (shadowStates s q rs) = holeCost M h q rs := by
  induction rs with
  | nil => intro s h q _ _ _ _; exact ⟨trivial, rfl⟩
  | cons r rs ih =>
    intro s h q hs hrange hqS hqh
    have hrS := hrs r List.mem_cons_self
    have hrs' : ∀ x ∈ rs, x ∈ S := fun x hx => hrs x (List.mem_cons_of_mem r hx)
    have hq : ∃ i, s i = q := (hrange q).2 ⟨hqS, hqh⟩
    by_cases hrh : r = h
    · subst hrh
      have hcov : ¬ ∃ i, s i = r := fun hc => ((hrange r).1 hc).2 rfl
      have hnot : ∀ i, s i ≠ r := fun i hi => hcov ⟨i, hi⟩
      have hinj := relocate_injective hs (q := q) hnot
      have hrange' : ∀ x, (∃ i, relocate s q r i = x) ↔ x ∈ S ∧ x ≠ q := by
        intro x
        rw [mem_range_relocate_iff hq, hrange x]
        constructor
        · rintro (rfl | ⟨hxq, hxS, _⟩)
          · exact ⟨hrS, Ne.symm hqh⟩
          · exact ⟨hxS, hxq⟩
        · rintro ⟨hxS, hxq⟩
          by_cases hxr : x = r
          · exact Or.inl hxr
          · exact Or.inr ⟨hxq, hxS, hxr⟩
      obtain ⟨hv, hc⟩ := ih hrs' hinj hrange' hrS (Ne.symm hqh)
      simp only [shadowStates, hcov, ↓reduceIte, holeCost]
      refine ⟨⟨(mem_range_relocate_iff hq).2 (Or.inl rfl), hv⟩, ?_⟩
      change moveCost M s (relocate s q r) + _ = _
      rw [moveCost_relocate M hs hq, hc]
    · have hcov : ∃ i, s i = r := (hrange r).2 ⟨hrS, hrh⟩
      obtain ⟨hv, hc⟩ := ih hrs' hs hrange hrS hrh
      simp only [shadowStates, hcov, ↓reduceIte, holeCost, hrh]
      refine ⟨⟨hcov, hv⟩, ?_⟩
      change moveCost M s s + _ = _
      rw [moveCost_self, hc, Nat.zero_add]

/-- Summing the shadow costs over all holes gives the path length. -/
theorem sum_holeCost (S : Finset α) {rs : List α} (hrs : ∀ r ∈ rs, r ∈ S) :
    ∀ {q : α}, q ∈ S → ∑ h ∈ S.erase q, holeCost M h q rs = pathLen M q rs := by
  induction rs with
  | nil => intro q _; exact Finset.sum_eq_zero fun _ _ => rfl
  | cons r rs ih =>
    intro q hqS
    have hrS := hrs r List.mem_cons_self
    have ih' := ih (fun x hx => hrs x (List.mem_cons_of_mem r hx)) hrS
    simp only [holeCost, pathLen]
    by_cases hrq : r = q
    · subst hrq
      have hsum : ∀ h ∈ S.erase r, (if r = h then M.dist r r + holeCost M r r rs
          else holeCost M h r rs) = holeCost M h r rs := fun h hh => by
        have hne : r ≠ h := fun hrh => (Finset.ne_of_mem_erase hh) hrh.symm
        simp only [hne, ↓reduceIte]
      rw [Finset.sum_congr rfl hsum, ih', M.dist_self r, Nat.zero_add]
    · have hr : r ∈ S.erase q := Finset.mem_erase.2 ⟨hrq, hrS⟩
      have hq : q ∈ S.erase r := Finset.mem_erase.2 ⟨Ne.symm hrq, hqS⟩
      rw [← Finset.add_sum_erase _ _ hr, ite_eq_left rfl, ← ih',
        ← Finset.add_sum_erase _ _ hq, Finset.erase_right_comm, Nat.add_assoc]
      congr 2
      refine Finset.sum_congr rfl fun h hh => ?_
      have hne : r ≠ h := fun hrh =>
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hh)) hrh.symm
      simp only [hne, ↓reduceIte]

private theorem card_insert_image {s₀ : Fin k → α} (hs₀ : Function.Injective s₀) {z : α}
    (hz : ∀ i, s₀ i ≠ z) : (insert z (Finset.univ.image s₀)).card = k + 1 := by
  have hzim : z ∉ Finset.univ.image s₀ := fun h => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
    exact hz i hi
  rw [Finset.card_insert_of_notMem hzim, Finset.card_image_of_injective _ hs₀,
    Finset.card_univ, Fintype.card_fin]

private theorem range_iff_insert_image {s₀ : Fin k → α} {z : α} (hz : ∀ i, s₀ i ≠ z) (x : α) :
    (∃ i, s₀ i = x) ↔ x ∈ insert z (Finset.univ.image s₀) ∧ x ≠ z := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hz i⟩
  · rintro ⟨hxS, hxz⟩
    rcases Finset.mem_insert.1 hxS with h | h
    · exact absurd h hxz
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
      exact ⟨i, hi⟩

/-- Averaging over the `k` shadow schedules: if the first request is the extra point `z` and all
later requests lie in the `(k + 1)`-point set, some valid offline schedule costs at most a `1 / k`
fraction of the request path plus the initial distances to `z`. -/
theorem exists_shadow_le {s₀ : Fin k → α} (hs₀ : Function.Injective s₀) {z : α}
    (hz : ∀ i, s₀ i ≠ z) (hk : 0 < k) {rest : List α}
    (hrest : ∀ r ∈ rest, r ∈ insert z (Finset.univ.image s₀)) :
    ∃ offStates, (problem M k).ValidSchedule s₀ (z :: rest) offStates ∧
      k * (problem M k).scheduleCost s₀ (z :: rest) offStates ≤
        (∑ i, M.dist (s₀ i) z) + pathLen M z rest := by
  set S := insert z (Finset.univ.image s₀)
  have hzS : z ∈ S := Finset.mem_insert_self _ _
  have hreq : ∀ r ∈ z :: rest, r ∈ S := by grind
  have hspec := fun i => shadowStates_spec M S hreq hs₀ (range_iff_insert_image hz)
    ((range_iff_insert_image hz (s₀ i)).1 ⟨i, rfl⟩).1 (hz i)
  have hsum : ∑ i, holeCost M z (s₀ i) (z :: rest) =
      (∑ i, M.dist (s₀ i) z) + pathLen M z rest := by
    have hh : ∀ i, holeCost M z (s₀ i) (z :: rest) =
        M.dist (s₀ i) z + holeCost M (s₀ i) z rest :=
      fun i => by simp only [holeCost, ↓reduceIte]
    simp only [hh, Finset.sum_add_distrib]
    congr 1
    have herase : S.erase z = Finset.univ.image s₀ := by
      refine Finset.erase_insert fun h => ?_
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
      exact hz i hi
    rw [← sum_holeCost M S hrest hzS, herase, Finset.sum_image fun i _ j _ h => hs₀ h]
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i => holeCost M z (s₀ i) (z :: rest)) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  refine ⟨shadowStates s₀ (s₀ i) (z :: rest), (hspec i).1, ?_⟩
  rw [(hspec i).2, ← hsum]
  calc k * holeCost M z (s₀ i) (z :: rest)
      = ∑ _j : Fin k, holeCost M z (s₀ i) (z :: rest) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun j _ => hi j (Finset.mem_univ j)

end Shadow

/-! ### The adversary: request the uncovered point -/

open Classical in
/-- A point of `S` not occupied by `c` (default `x₀` if none). -/
private noncomputable def uncovered (S : Finset α) (x₀ : α) (c : Fin k → α) : α :=
  if h : ∃ x ∈ S, ∀ i, c i ≠ x then Classical.choose h else x₀

private theorem uncovered_spec {S : Finset α} (hS : S.card = k + 1) (x₀ : α) (c : Fin k → α) :
    uncovered S x₀ c ∈ S ∧ ∀ i, c i ≠ uncovered S x₀ c := by
  classical
  have hlt : (Finset.univ.image c).card < S.card := by grind [Finset.card_univ, Fintype.card_fin]
  obtain ⟨x, hxS, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have h : ∃ x ∈ S, ∀ i, c i ≠ x :=
    ⟨x, hxS, fun i hi => hx (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)⟩
  unfold uncovered
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

private theorem uncovered_unique {S : Finset α} (hS : S.card = k + 1) {c : Fin k → α}
    (hc : Function.Injective c) (hcS : ∀ i, c i ∈ S) {x y : α} (hx : x ∈ S) (hy : y ∈ S)
    (hxc : ∀ i, c i ≠ x) (hyc : ∀ i, c i ≠ y) : x = y := by
  classical
  by_contra hxy
  have hsub : Finset.univ.image c ⊆ (S.erase x).erase y := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hz
    exact Finset.mem_erase.2 ⟨hyc i, Finset.mem_erase.2 ⟨hxc i, hcS i⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 : 0 < (S.erase x).card :=
    Finset.card_pos.2 ⟨y, Finset.mem_erase.2 ⟨Ne.symm hxy, hy⟩⟩
  rw [Finset.card_erase_of_mem hx, hS] at h2
  rw [Finset.card_image_of_injective _ hc, Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hxy, hy⟩), Finset.card_erase_of_mem hx,
    hS] at h1
  omega

/-- One step of the lazy simulation on the uncovered request: the configuration stays injective
inside `S`, and the cost is the distance from the request to the next uncovered point. -/
private theorem lazy_uncovered_step {S : Finset α} (hS : S.card = k + 1) (x₀ : α)
    {c a : Fin k → α} (hc : Function.Injective c) (hcS : ∀ i, c i ∈ S)
    (ha : ∃ j, a j = uncovered S x₀ c) :
    let r := uncovered S x₀ c
    let c' := lazyNext c a r
    Function.Injective c' ∧ (∀ i, c' i ∈ S) ∧ moveCost M c c' = M.dist r (uncovered S x₀ c') ∧
      r ≠ uncovered S x₀ c' := by
  intro r c'
  obtain ⟨hrS, hrc⟩ := uncovered_spec hS x₀ c
  rcases (lazyNext_spec c a r ha).2 with h | ⟨j, _, h⟩
  · exact absurd ((lazyNext_spec c a r ha).1) (by rw [h]; exact fun ⟨i, hi⟩ => hrc i hi)
  · have hc' : c' = Function.update c j r := h
    have hinj : Function.Injective c' := by
      rw [hc']
      intro i₁ i₂ hi
      by_cases h₁ : i₁ = j <;> by_cases h₂ : i₂ = j
      · rw [h₁, h₂]
      · rw [h₁, Function.update_self, Function.update_of_ne h₂] at hi
        exact absurd hi.symm (hrc i₂)
      · rw [h₂, Function.update_self, Function.update_of_ne h₁] at hi
        exact absurd hi (hrc i₁)
      · rw [Function.update_of_ne h₁, Function.update_of_ne h₂] at hi
        exact hc hi
    have hc'S : ∀ i, c' i ∈ S := by
      intro i
      rw [hc']
      by_cases hi : i = j
      · rw [hi, Function.update_self]; exact hrS
      · rw [Function.update_of_ne hi]; exact hcS i
    obtain ⟨hr'S, hr'c⟩ := uncovered_spec hS x₀ c'
    have hcj : uncovered S x₀ c' = c j := by
      refine uncovered_unique hS hinj hc'S hr'S (hcS j) hr'c fun i hi => ?_
      rw [hc'] at hi
      by_cases hij : i = j
      · rw [hij, Function.update_self] at hi
        exact hrc j hi.symm
      · rw [Function.update_of_ne hij] at hi
        exact hij (hc hi)
    refine ⟨hinj, hc'S, ?_, ?_⟩
    · rw [hcj, hc', moveCost_update, M.dist_comm]
    · rw [hcj]
      exact fun h => hrc j h.symm

/-- Against the uncovered-point adversary, the lazy simulation pays the request path length, and
at least `1` per request. -/
private theorem lazy_costFrom_ge {S : Finset α} (hS : S.card = k + 1) (x₀ : α)
    (A : DetStrategy (problem M k)) (n : Nat) :
    ∀ (m : A.Mem) (c : Fin k → α), A.ValidMem m → Function.Injective c → (∀ i, c i ∈ S) →
      pathLen M (uncovered S x₀ c)
          ((lazify M A).adaptiveRequestsFrom (uncovered S x₀) (m, c) n).tail ≤
        (lazify M A).costFrom (m, c)
          ((lazify M A).adaptiveRequestsFrom (uncovered S x₀) (m, c) n) ∧
      n ≤ (lazify M A).costFrom (m, c)
        ((lazify M A).adaptiveRequestsFrom (uncovered S x₀) (m, c) n) := by
  induction n with
  | zero => intro m c _ _ _; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | succ n ih =>
    intro m c hm hc hcS
    set r := uncovered S x₀ c
    have hstep := A.valid_step r hm
    set c' := lazyNext c (A.project (A.step m r)) r
    obtain ⟨hinj, hc'S, hcost, hne⟩ := lazy_uncovered_step M hS x₀ hc hcS hstep.2
    change moveCost M c c' = M.dist r (uncovered S x₀ c') at hcost
    change r ≠ uncovered S x₀ c' at hne
    change Function.Injective c' at hinj
    change ∀ i, c' i ∈ S at hc'S
    obtain ⟨ih1, ih2⟩ := ih (A.step m r) c' hstep.1 hinj hc'S
    have hpos := M.dist_pos_of_ne hne
    change pathLen M r ((lazify M A).adaptiveRequestsFrom (uncovered S x₀) (A.step m r, c') n) ≤
        moveCost M c c' + (lazify M A).costFrom (A.step m r, c')
          ((lazify M A).adaptiveRequestsFrom (uncovered S x₀) (A.step m r, c') n) ∧
      n + 1 ≤ moveCost M c c' + (lazify M A).costFrom (A.step m r, c')
          ((lazify M A).adaptiveRequestsFrom (uncovered S x₀) (A.step m r, c') n)
    refine ⟨?_, by omega⟩
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      change M.dist r (uncovered S x₀ c') + pathLen M (uncovered S x₀ c')
        ((lazify M A).adaptiveRequestsFrom (uncovered S x₀) (A.step m r, c') (n + 1)).tail ≤ _
      rw [hcost]
      omega

/-! ### The lower bound -/

/-- **Manasse–McGeoch–Sleator lower bound, rational form.** Let `s₀` place the `k` servers on
distinct points and let `z` be a further point. For every deterministic online strategy `A`,
every rational ratio `p / q < k` and every additive constant `b`, some request sequence and valid
offline schedule from `s₀` satisfy `p * OPT + b < q * cost_A`. -/
theorem exists_ratio_violation {s₀ : Fin k → α} (hs₀ : Function.Injective s₀) {z : α}
    (hz : ∀ i, s₀ i ≠ z) (A : DetStrategy (problem M k)) {p q : Nat} (hpq : p < k * q)
    (b : Nat) :
    ∃ reqs offStates, (problem M k).ValidSchedule s₀ reqs offStates ∧
      p * (problem M k).scheduleCost s₀ reqs offStates + b < q * A.cost s₀ reqs := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; omega
  set S := insert z (Finset.univ.image s₀)
  have hS := card_insert_image hs₀ hz
  have hs₀S : ∀ i, s₀ i ∈ S := fun i => ((range_iff_insert_image hz (s₀ i)).1 ⟨i, rfl⟩).1
  have hu : uncovered S z s₀ = z := by
    obtain ⟨h1, h2⟩ := uncovered_spec hS z s₀
    exact uncovered_unique hS hs₀ hs₀S h1 (Finset.mem_insert_self _ _) h2 hz
  set I := ∑ i, M.dist (s₀ i) z
  set n := p * (b + q * I) + b
  set reqs := (lazify M A).adaptiveRequests (uncovered S z) s₀ (n + 1) with hreqs
  have hmem : ∀ r ∈ reqs, r ∈ S := fun r hr =>
    (lazify M A).mem_adaptiveRequests (Q := (· ∈ S))
      (fun {_} _ => (uncovered_spec hS z _).1) trivial hr
  have hhead : reqs = z :: reqs.tail := by
    change uncovered S z s₀ :: _ = _
    rw [hu]
    rfl
  obtain ⟨off, hv, hoff⟩ := exists_shadow_le M hs₀ hz hk (rest := reqs.tail)
    fun r hr => hmem r (List.mem_of_mem_tail hr)
  rw [← hhead] at hv hoff
  obtain ⟨h1, h2⟩ := lazy_costFrom_ge M hS z A (n + 1) (A.init s₀) s₀
    (A.valid_init trivial).1 hs₀ hs₀S
  have hL : (lazify M A).cost s₀ reqs =
      (lazify M A).costFrom (A.init s₀, s₀) reqs := (lazify M A).cost_eq_costFrom trivial reqs
  rw [hu] at h1
  change pathLen M z reqs.tail ≤ (lazify M A).costFrom (A.init s₀, s₀) reqs at h1
  change n + 1 ≤ (lazify M A).costFrom (A.init s₀, s₀) reqs at h2
  have hA := cost_lazify_le M A s₀ reqs
  rw [hL] at hA
  refine ⟨reqs, off, hv, ?_⟩
  set O := (problem M k).scheduleCost s₀ reqs off
  set C := A.cost s₀ reqs
  have hpath : pathLen M z reqs.tail ≤ C := by omega
  have hn : n + 1 ≤ C := by omega
  have hO : k * O ≤ I + C := by omega
  have hqO : k * q * O ≤ q * I + q * C := by
    calc k * q * O = q * (k * O) := by rw [Nat.mul_comm k q, Nat.mul_assoc]
      _ ≤ q * (I + C) := Nat.mul_le_mul_left q hO
      _ = q * I + q * C := Nat.mul_add q I C
  have hpO : (p + 1) * O ≤ k * q * O := Nat.mul_le_mul_right O hpq
  by_contra hcon
  have hcon' : q * C ≤ p * O + b := by omega
  rw [Nat.add_one_mul] at hpO
  have hOb : O ≤ b + q * I := by omega
  have : p * O ≤ p * (b + q * I) := Nat.mul_le_mul_left p hOb
  have hq : 0 < q := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hpq; omega
  have hqC : C ≤ q * C := Nat.le_mul_of_pos_left C hq
  omega

/-- **Manasse–McGeoch–Sleator lower bound.** From `k` distinct initial positions avoiding some
further point, no deterministic online `k`-server strategy is `(c, b)`-competitive for `c < k`. -/
theorem not_isCompetitiveFrom_of_lt {s₀ : Fin k → α} (hs₀ : Function.Injective s₀) {z : α}
    (hz : ∀ i, s₀ i ≠ z) (A : DetStrategy (problem M k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitiveFrom s₀ c b := by
  intro h
  obtain ⟨reqs, offStates, hv, hlt⟩ :=
    exists_ratio_violation M hs₀ hz A (p := c) (q := 1) (by omega) b
  have := h reqs offStates hv
  omega

/-- On any metric with `k + 1` distinct points, no deterministic online `k`-server strategy is
`(c, b)`-competitive for `c < k`. -/
theorem not_isCompetitive_of_lt {s : Fin (k + 1) → α} (hs : Function.Injective s)
    (A : DetStrategy (problem M k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitive c b := fun h =>
  not_isCompetitiveFrom_of_lt M (s₀ := s ∘ Fin.castSucc) (hs.comp (Fin.castSucc_injective k))
    (z := s (Fin.last k)) (fun i hi => (Fin.castSucc_lt_last i).ne (hs hi)) A hc b (h _ trivial)

/-- The lower bound also refutes competitiveness against offline schedules from arbitrary
initial configurations. -/
theorem not_isCompetitiveAnyInit_of_lt {s : Fin (k + 1) → α} (hs : Function.Injective s)
    (A : DetStrategy (problem M k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitiveAnyInit c b := fun h =>
  not_isCompetitive_of_lt M hs A hc b h.toIsCompetitive

end Cslib.DataStructure.KServer
