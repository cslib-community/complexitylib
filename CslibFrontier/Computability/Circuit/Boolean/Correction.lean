/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Cslib.Computability.Circuit.RelativeComplexity
public import Mathlib.Data.Nat.Dist
import CslibFrontier.Computability.Circuit.Complexity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sparse corrections of Boolean circuits

Let `f` and `g` be Boolean functions with `m` outputs on `n` inputs that differ only on the
inputs in a set `s`, and only in the outputs selected by `select : Fin k → Fin m`. A circuit for
`g` is corrected into one for `f` as follows. Compute the indicator of `s` once, and compute the
selected outputs of `f ⊕ g` by a single circuit that is only required to be correct on `s`. Mask
each of these labels with the indicator and add it, by an exclusive or, to the corresponding
output of `g`; the other outputs of `g` are kept. The mask and the exclusive or cost five De
Morgan gates per selected output, so with `1_s` the indicator of `s` and `C^s` complexity on `s`,
`C(f | g) ≤ C(1_s) + C^s((f ⊕ g) ∘ select) + 5 k` (`complexityGiven_le_of_cover`). Correcting
in both directions bounds `|C(f) - C(g)|` by the same quantity (`dist_complexity_le_of_cover`).
For a single output, the indicator of the inputs where `f` and `g` differ is `f ⊕ g` itself, so
`|C(f) - C(g)| ≤ C(f ⊕ g) + 4` (`dist_complexity_single_le_complexity_xor`).

The point of keeping the indicator and the labels as two circuits shared by all outputs is that
both can be much cheaper than the truth tables they encode: when `s` is small, `1_s` is a sparse
function and the labels form a partial function defined on few inputs. Bounds for the
complexity of such functions turn these corrections into continuity estimates for circuit
complexity; see `CslibFrontier.Computability.Circuit.Boolean.SparseSynthesis`. The case of a single
changed input is `Cslib.Circuits.Boolean.complexity_update_le`.

## Main results

* `Cslib.Circuits.Boolean.complexityGiven_le_of_cover`: the cost of a sparse correction, given
  the function being corrected.
* `Cslib.Circuits.Boolean.dist_complexity_le_of_cover`,
  `Cslib.Circuits.Boolean.dist_complexity_le_sum_of_cover`: sparse corrections change the
  complexity by at most their cost.
* `Cslib.Circuits.Boolean.dist_complexity_single_le_complexity_xor`: `|C(f) - C(g)| ≤ C(f ⊕ g) + 4`.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean Finset

variable {n m k : ℕ}

namespace Boolean

/-- Correcting a single output: the complexities of `f` and `g` differ by at most the complexity
of `f ⊕ g`, the indicator of the inputs on which they differ, plus four gates. -/
theorem dist_complexity_single_le_complexity_xor (f g : BooleanFunction n) :
    Nat.dist (complexity interpretation (single f)) (complexity interpretation (single g)) ≤
      complexity interpretation (single fun x => f x ^^ g x) + 4 := by
  have hf' : (fun x => g x ^^ (f x ^^ g x)) = f := funext fun x => by
    cases f x <;> cases g x <;> rfl
  have hg' : (fun x => f x ^^ (f x ^^ g x)) = g := funext fun x => by
    cases f x <;> cases g x <;> rfl
  have hf : complexity interpretation (single f) ≤ complexity interpretation (single g) +
      complexity interpretation (single fun x => f x ^^ g x) + 4 := by
    simpa only [hf'] using complexity_xor_le g fun x => f x ^^ g x
  have hg : complexity interpretation (single g) ≤ complexity interpretation (single f) +
      complexity interpretation (single fun x => f x ^^ g x) + 4 := by
    simpa only [hg'] using complexity_xor_le f fun x => f x ^^ g x
  unfold Nat.dist
  omega

/-- The output wire carrying output `j` of the corrected function, in the inputs of `patch`. -/
private abbrev oldWire (j : Fin m) : Fin (m + (1 + k)) := Fin.castAdd (1 + k) j

/-- The input wire carrying the indicator, in the inputs of `patch`. -/
private abbrev supportWire : Fin (m + (1 + k)) := Fin.natAdd m (Fin.castAdd k 0)

/-- The input wire carrying label `i`, in the inputs of `patch`. -/
private abbrev labelWire (i : Fin k) : Fin (m + (1 + k)) := Fin.natAdd m (Fin.natAdd 1 i)

/-- The final stage of a correction. It reads the outputs of the function being corrected, the
indicator, and the labels, and adds the masked label of some `i` with `select i = j` to output
`j`, keeping the outputs not selected. -/
private noncomputable def patch (select : Fin k → Fin m) :
    BitString (m + (1 + k)) → BitString m :=
  fun z j => if h : ∃ i, select i = j then
    z (oldWire j) ^^ (z supportWire && z (labelWire h.choose)) else z (oldWire j)

/-- The final stage of a correction costs five gates for each index of `select`. -/
private theorem exists_computes_patch (select : Fin k → Fin m) :
    ∃ c : Circuit signature (m + (1 + k)) m,
      c.Computes interpretation (patch select) ∧ c.size ≤ 5 * k := by
  have input (w : Fin (m + (1 + k))) :
      Synthesis interpretation (inputs (m + (1 + k))) {fun z => z w} 0 :=
    Synthesis.of_mem ⟨w, rfl⟩
  have each (j : Fin m) : Synthesis interpretation (inputs (m + (1 + k)))
      {fun z => patch select z j} (if ∃ i, select i = j then 5 else 0) := by
    by_cases h : ∃ i, select i = j
    · simpa only [patch, h, dite_true, ite_true] using
        (input (oldWire j)).xor ((input supportWire).and (input (labelWire h.choose)))
    · simpa only [patch, h, dite_false, ite_false] using input (oldWire j)
  obtain ⟨c, hc, hsize⟩ := (Synthesis.family _ _ each).exists_circuit_outputs
  refine ⟨c, hc, hsize.trans ?_⟩
  rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_comm]
  have himage : ({j | ∃ i, select i = j} : Finset (Fin m)) = univ.image select := by
    ext j
    simp
  rw [himage]
  exact Nat.mul_le_mul_left 5 (card_image_le.trans (by simp))

/-- **Sparse correction.** Suppose that `f` and `g` agree outside `s`, and agree on every output
outside the range of `select`. Given the values of `g`, computing `f` costs at most the
complexity of the indicator of `s`, plus the complexity on `s` of the outputs of `f ⊕ g`
selected by `select`, plus five gates for each of the `k` indices of `select`. -/
theorem complexityGiven_le_of_cover (f g : BitString n → BitString m) (s : Finset (BitString n))
    (select : Fin k → Fin m) (hs : ∀ x ∉ s, f x = g x)
    (hselect : ∀ j ∉ Set.range select, ∀ x, f x j = g x j) :
    complexityGiven interpretation f g ≤
      complexity interpretation (single fun x => decide (x ∈ s)) +
        complexityOn interpretation s (fun x i => f x (select i) ^^ g x (select i)) + 5 * k := by
  obtain ⟨cp, hcp, hcp_size⟩ := exists_computes_patch select
  obtain ⟨cs, hcs, hcs_size⟩ := exists_computes_size_eq_complexity (I := interpretation)
    (f := single fun x => decide (x ∈ s))
  obtain ⟨cl, hcl, hcl_size⟩ := exists_computesOn_size_eq_complexityOn (I := interpretation)
    (S := (s : Set (BitString n))) (f := fun x i => f x (select i) ^^ g x (select i))
  let read : Circuit signature (n + m) n := Circuit.wiring signature (Fin.castAdd m)
  let old : Circuit signature (n + m) m := Circuit.wiring signature (Fin.natAdd n)
  let c := cp.comp (old.append ((cs.comp read).append (cl.comp read)))
  have hc (x : BitString n) : c.eval interpretation (Fin.append x (g x)) = f x := by
    simp only [c, old, read, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring,
      Fin.append_comp_castAdd, Fin.append_comp_natAdd, hcp _, hcs x]
    funext j
    by_cases h : ∃ i, select i = j
    · have hi := h.choose_spec
      simp only [patch, h, dite_true, oldWire, supportWire, labelWire, Fin.append_left,
        Fin.append_right, single_apply]
      by_cases hx : x ∈ s
      · rw [show cl.eval interpretation x = _ from hcl (Finset.mem_coe.mpr hx)]
        simp only [hx, decide_true, Bool.true_and, hi]
        cases f x j <;> cases g x j <;> rfl
      · simp [hx, hs x hx]
    · simp only [patch, h, dite_false, oldWire, Fin.append_left]
      exact (hselect j (fun ⟨i, hi⟩ => h ⟨i, hi⟩) x).symm
  have hle := ecomplexityGiven_le_of_eval f g c hc
  rw [← natCast_complexityGiven] at hle
  have hsize : c.size ≤ complexity interpretation (single fun x => decide (x ∈ s)) +
      complexityOn interpretation s (fun x i => f x (select i) ^^ g x (select i)) + 5 * k := by
    simp only [c, old, read, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring]
    omega
  exact (by exact_mod_cast hle : complexityGiven interpretation f g ≤ c.size).trans hsize

/-- **Sparse correction changes complexity little.** If `f` and `g` agree outside `s`, and agree
on every output outside the range of `select`, then their complexities differ by at most the
complexity of the indicator of `s`, plus the complexity on `s` of the outputs of `f ⊕ g` selected
by `select`, plus five gates for each of the `k` indices of `select`. -/
theorem dist_complexity_le_of_cover (f g : BitString n → BitString m) (s : Finset (BitString n))
    (select : Fin k → Fin m) (hs : ∀ x ∉ s, f x = g x)
    (hselect : ∀ j ∉ Set.range select, ∀ x, f x j = g x j) :
    Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
      complexity interpretation (single fun x => decide (x ∈ s)) +
        complexityOn interpretation s (fun x i => f x (select i) ^^ g x (select i)) + 5 * k := by
  have hf := (complexity_le_add_complexityGiven (I := interpretation) f g).trans
    (Nat.add_le_add_left (complexityGiven_le_of_cover f g s select hs hselect) _)
  have hg := (complexity_le_add_complexityGiven (I := interpretation) g f).trans
    (Nat.add_le_add_left (complexityGiven_le_of_cover g f s select (fun x hx => (hs x hx).symm)
      fun j hj x => (hselect j hj x).symm) _)
  simp only [Bool.xor_comm (g _ _)] at hg
  unfold Nat.dist
  omega

/-- Computing `k` functions on `s` side by side costs at most the sum of their complexities on
`s`. -/
private theorem complexityOn_pi_le (s : Set (BitString n)) (f : Fin k → BooleanFunction n) :
    complexityOn interpretation s (fun x i => f i x) ≤
      ∑ i, complexityOn interpretation s (single (f i)) := by
  choose c hc hsize using fun i =>
    exists_computesOn_size_eq_complexityOn (I := interpretation) (S := s) (f := single (f i))
  have hcongr : Set.EqOn (fun x i => f i x) (fun x i => (c i).eval interpretation x 0) s :=
    fun x hx => funext fun i => (Circuit.computesOn_single_iff.1 (hc i) x hx).symm
  rw [complexityOn_congr hcongr]
  refine complexityOn_le_complexity.trans ((complexity_pi_le _).trans
    (sum_le_sum fun i _ => ?_))
  rw [← hsize i]
  refine complexity_le_of_computes (c i) (Circuit.computes_single_iff.2 fun _ => rfl)

/-- **Sparse correction with separate labels.** If `f` and `g` agree outside `s`, and agree on
every output outside the range of `select`, then their complexities differ by at most the
complexity of the indicator of `s`, plus the sum over the indices `i` of `select` of the
complexity on `s` of output `select i` of `f ⊕ g`, plus five gates for each of the `k` indices
of `select`. -/
theorem dist_complexity_le_sum_of_cover (f g : BitString n → BitString m)
    (s : Finset (BitString n)) (select : Fin k → Fin m) (hs : ∀ x ∉ s, f x = g x)
    (hselect : ∀ j ∉ Set.range select, ∀ x, f x j = g x j) :
    Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
      complexity interpretation (single fun x => decide (x ∈ s)) +
        ∑ i, complexityOn interpretation s (single fun x => f x (select i) ^^ g x (select i)) +
          5 * k :=
  (dist_complexity_le_of_cover f g s select hs hselect).trans
    (Nat.add_le_add_right (Nat.add_le_add_left
      (complexityOn_pi_le s fun i x => f x (select i) ^^ g x (select i)) _) _)

end Boolean

end Cslib.Circuits
