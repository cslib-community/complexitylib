/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Clique
public import Complexity.Computability.Circuit.FanIn
public import Cslib.Computability.Circuit.Complexity
public import Complexity.Computability.Circuit.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Every edge is essential to the clique function

For `2 ≤ k ≤ n`, every edge is essential to every Boolean function separating the graphs with a
`k`-clique from the `(k - 1)`-colourable graphs (`Cslib.Circuits.Clique.Separates.essentialAt`).
Colour a `k`-set through the edge injectively, except that the two endpoints share a colour: the
complete multipartite graph of that colouring is `(k - 1)`-colourable, and adding the edge completes
the `k`-clique on the set. In particular the `k`-clique function depends on every edge
(`essentialAt_clique`). A monotone circuit has fan-in at most two, so a separating one has at least
`n.choose 2 - 1` gates (`edgeCount_le_succ_size_of_separates`, `edgeCount_le_succ_size`). This
settles small clique sizes, where the method of approximations says nothing.

It also records that monotone circuits compute the clique function at all, as the disjunction over
the `k`-sets of the conjunction of their edges (`exists_computes_clique`), so that the lower bounds
for it are not vacuous.

## Main results

* `Cslib.Circuits.Monotone.exists_computes_clique`: some monotone circuit computes `k`-clique.
* `Cslib.Circuits.Clique.Separates.essentialAt`: every edge is essential to a function separating
  the graphs with a `k`-clique from the `(k - 1)`-colourable graphs.
* `Cslib.Circuits.Monotone.essentialAt_clique`: every edge is essential to `k`-clique.
* `Cslib.Circuits.Monotone.edgeCount_le_succ_size_of_separates`,
  `Cslib.Circuits.Monotone.edgeCount_le_two_pow_depth_of_separates`,
  `Cslib.Circuits.Monotone.edgeCount_le_succ_size`,
  `Cslib.Circuits.Monotone.edgeCount_le_two_pow_depth`: the resulting size and depth bounds, for
  separating circuits and for circuits computing `k`-clique.
-/
@[expose] public section

namespace Cslib.Circuits

open Finset

variable {n k : ℕ}

namespace Clique

/-- For `2 ≤ k ≤ n`, every edge is essential to a function separating the graphs with a `k`-clique
from the `(k - 1)`-colourable graphs. Choose a `k`-set `t` through the edge `{u, v}` and colour
`t \ {v}` injectively with `k - 1` colours, giving `v` (and every vertex outside `t`) the colour of
`u`. The complete multipartite graph of this colouring is `(k - 1)`-colourable, and adding the edge
`{u, v}` makes `t` a `k`-clique. -/
theorem Separates.essentialAt (hk : 2 ≤ k) (hkn : k ≤ n) {f : BooleanFunction (edgeCount n)}
    (hf : Separates k (k - 1) f) (i : Fin (edgeCount n)) : EssentialAt f i := by
  classical
  obtain ⟨⟨e, he⟩, rfl⟩ := (edgeEquiv n).surjective i
  induction e using Sym2.ind with | h u v => ?_
  have huv : u ≠ v := by simpa using he
  have hcard : (s(u, v) : Sym2 (Fin n)).toFinset.card ≤ k := by
    rw [Sym2.card_toFinset_of_not_isDiag _ he]
    exact hk
  obtain ⟨t, hut, -, ht⟩ := exists_subsuperset_card_eq (subset_univ _) hcard (by simpa using hkn)
  have hv : v ∈ t := hut (by simp)
  have hu : u ∈ t.erase v := mem_erase.2 ⟨huv, hut (by simp)⟩
  let ρ : Fin n → t.erase v := fun w => if h : w ∈ t.erase v then ⟨w, h⟩ else ⟨u, hu⟩
  let φ : t.erase v ≃ Fin (k - 1) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, card_erase_of_mem hv, ht])
  let c : Fin n → Fin (k - 1) := fun w => φ (ρ w)
  -- Only the endpoints of `{u, v}` share a colour inside `t`.
  have hc : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → c a = c b → s(a, b) = s(u, v) := by
    have hρ (w : Fin n) (hw : w ∈ t) : (ρ w : Fin n) = if w = v then u else w := by
      by_cases hwv : w = v
      · simp [ρ, hwv]
      · simp [ρ, hwv, hw]
    intro a ha b hb hab hab'
    have h := congrArg Subtype.val (φ.injective hab')
    rw [hρ a ha, hρ b hb] at h
    split_ifs at h with ha' hb' hb'
    · exact absurd (ha'.trans hb'.symm) hab
    · rw [ha', ← h]
      exact Sym2.eq_swap
    · rw [hb', h]
    · exact absurd h hab
  have htrue : f (Function.update (ofColoring c) (edgeEquiv n ⟨s(u, v), he⟩) true) = true := by
    refine hf.1 _ (decide_eq_true ⟨t, ht, fun e' he' => ?_⟩)
    by_cases hee : e' = ⟨s(u, v), he⟩
    · rw [hee, Function.update_self]
    · rw [Function.update_of_ne ((edgeEquiv n).injective.ne hee)]
      simp only [ofColoring, Equiv.symm_apply_apply, decide_eq_true_iff]
      intro a ha b hb hab'
      by_contra hab
      refine hee (Subtype.ext ?_)
      rw [Sym2.mem_toFinset] at ha hb
      rw [(Sym2.mem_and_mem_iff hab).1 ⟨ha, hb⟩]
      exact hc a (he' (Sym2.mem_toFinset.2 ha)) b (he' (Sym2.mem_toFinset.2 hb)) hab hab'
  refine ⟨ofColoring c, Function.update (ofColoring c) (edgeEquiv n ⟨s(u, v), he⟩) true,
    fun j hj => (Function.update_of_ne hj _ _).symm, ?_⟩
  rw [hf.ofColoring_eq_false c, htrue]
  exact Bool.false_ne_true

end Clique

namespace Monotone

open Clique

/-- Monotone programs have fan-in at most two. -/
theorem program_fanInAtMost_two {g : ℕ} (p : Program signature n g) : p.FanInAtMost 2 := by
  induction p with
  | empty => trivial
  | gate p line ih => exact ⟨ih, by cases line.op <;> simp⟩

private theorem fold_and_eq_true {ι : Type*} (t : Finset ι) (f : ι → Bool) :
    t.fold (· && ·) true f = true ↔ ∀ i ∈ t, f i = true := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => simp [Finset.fold_insert hi, ih]

private theorem fold_or_eq_true {ι : Type*} (t : Finset ι) (f : ι → Bool) :
    t.fold (· || ·) false f = true ↔ ∃ i ∈ t, f i = true := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => simp [Finset.fold_insert hi, ih]

/-- **Monotone circuits compute cliques**: the disjunction over the `k`-sets of the conjunction
of their edges. -/
theorem exists_computes_clique (n k : ℕ) :
    ∃ C : Circuit signature (edgeCount n) 1, C.Computes interpretation (single (clique n k)) := by
  classical
  have hand (f g : BooleanFunction (edgeCount n)) :
      Synthesis interpretation {f, g} {fun x => f x && g x} 1 := by
    simpa [interpretation] using Synthesis.gate (I := interpretation) (s := {f, g}) Op.and
      (fun i => if (i : ℕ) = 0 then f else g) fun i => by split <;> simp
  have hor (f g : BooleanFunction (edgeCount n)) :
      Synthesis interpretation {f, g} {fun x => f x || g x} 1 := by
    simpa [interpretation] using Synthesis.gate (I := interpretation) (s := {f, g}) Op.or
      (fun i => if (i : ℕ) = 0 then f else g) fun i => by split <;> simp
  have hconst (b : Bool) : Synthesis interpretation (inputs (edgeCount n)) {fun _ => b} 1 := by
    simpa [interpretation] using Synthesis.nullary (I := interpretation)
      (s := inputs (edgeCount n)) (.const b) rfl
  have h := Synthesis.finset_fold (· || ·) 1 hor ((univ : Finset (Fin n)).powersetCard k)
    (f := fun t x => (univ.filter fun e : Edge n => e.1.toFinset ⊆ t).fold (· && ·) true
      fun e => x (edgeEquiv n e)) (hconst false) fun t _ =>
      Synthesis.finset_fold (· && ·) 1 hand _ (hconst true) fun e _ =>
        Synthesis.of_mem ⟨edgeEquiv n e, rfl⟩
  obtain ⟨C, hC, -⟩ := h.exists_circuit
  refine ⟨C, fun x => (hC x).trans (funext fun _ => ?_)⟩
  change (univ.powersetCard k).fold (· || ·) false (fun t =>
    (univ.filter fun e : Edge n => e.1.toFinset ⊆ t).fold (· && ·) true
      fun e => x (edgeEquiv n e)) = clique n k x
  rw [Bool.eq_iff_iff, fold_or_eq_true, clique, decide_eq_true_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, (mem_powersetCard.1 ht).2, fun e he =>
      (fold_and_eq_true _ _).1 h e (mem_filter.2 ⟨mem_univ _, he⟩)⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, mem_powersetCard.2 ⟨subset_univ _, ht⟩,
      (fold_and_eq_true _ _).2 fun e he => h e (mem_filter.1 he).2⟩

/-- The monotone circuit complexity of `k`-clique is finite. -/
theorem ecomplexity_clique_ne_top (n k : ℕ) :
    ecomplexity interpretation (single (clique n k)) ≠ ⊤ :=
  ecomplexity_ne_top_iff.2 (exists_computes_clique n k)

/-- For `2 ≤ k ≤ n`, every edge is essential to `k`-clique. -/
theorem essentialAt_clique (hk : 2 ≤ k) (hkn : k ≤ n) (i : Fin (edgeCount n)) :
    EssentialAt (single (clique n k)) i := by
  obtain ⟨x, y, hxy, hne⟩ := (separates_clique (r := k - 1) (by omega)).essentialAt hk hkn i
  exact ⟨x, y, hxy, fun h => hne (by simpa using congrFun h 0)⟩

/-- Every edge is essential to the output of a circuit separating the graphs with a `k`-clique from
the `(k - 1)`-colourable graphs. -/
private theorem essentialAt_eval_of_separates (hk : 2 ≤ k) (hkn : k ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) (i : Fin (edgeCount n)) :
    EssentialAt (C.eval interpretation) i := by
  obtain ⟨x, y, hxy, hne⟩ := hC.essentialAt hk hkn i
  exact ⟨x, y, hxy, fun h => hne (congrFun h 0)⟩

/-- For `2 ≤ k ≤ n`, a monotone circuit separating the graphs with a `k`-clique from the
`(k - 1)`-colourable graphs has at least `n.choose 2 - 1` gates. -/
theorem edgeCount_le_succ_size_of_separates (hk : 2 ≤ k) (hkn : k ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) : edgeCount n ≤ 1 + C.size := by
  simpa using C.essential_le_size (target := C.eval interpretation) (fun _ => rfl)
    (selected := univ) (fun i _ => essentialAt_eval_of_separates hk hkn hC i)
    (program_fanInAtMost_two C.program)

/-- For `2 ≤ k ≤ n`, a monotone circuit separating the graphs with a `k`-clique from the
`(k - 1)`-colourable graphs has depth at least `log₂ C(n, 2)`. -/
theorem edgeCount_le_two_pow_depth_of_separates (hk : 2 ≤ k) (hkn : k ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : Separates k (k - 1) fun x => C.eval interpretation x 0) :
    edgeCount n ≤ 2 ^ C.depth := by
  simpa using C.essential_le_depth (target := C.eval interpretation) (fun _ => rfl)
    (selected := univ) (fun i _ => essentialAt_eval_of_separates hk hkn hC i)
    (program_fanInAtMost_two C.program)

/-- For `2 ≤ k ≤ n`, a monotone circuit computing `k`-clique has at least `n.choose 2 - 1`
gates. -/
theorem edgeCount_le_succ_size (hk : 2 ≤ k) (hkn : k ≤ n) {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) : edgeCount n ≤ 1 + C.size := by
  simpa using C.essential_le_size hC (selected := univ) (fun i _ => essentialAt_clique hk hkn i)
    (program_fanInAtMost_two C.program)

/-- For `2 ≤ k ≤ n`, a monotone circuit computing `k`-clique has depth at least `log₂ C(n, 2)`. -/
theorem edgeCount_le_two_pow_depth (hk : 2 ≤ k) (hkn : k ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) : edgeCount n ≤ 2 ^ C.depth := by
  simpa using C.essential_le_depth hC (selected := univ) (fun i _ => essentialAt_clique hk hkn i)
    (program_fanInAtMost_two C.program)

/-- There are at least `(n / 2) ^ 2` possible edges. -/
theorem sq_half_le_edgeCount (n : ℕ) : (n / 2) ^ 2 ≤ edgeCount n := by
  rw [edgeCount_eq_choose, Nat.choose_two_right, Nat.le_div_iff_mul_le (by decide)]
  have h := Nat.div_mul_le_self n 2
  set m := n / 2
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]

end Monotone

end Cslib.Circuits
