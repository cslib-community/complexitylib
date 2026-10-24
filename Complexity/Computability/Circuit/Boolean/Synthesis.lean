/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Circuit/Boolean/Synthesis.lean` and
-- `Cslib/Computability/Circuit/Boolean/Complexity.lean`)

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Complexity.Computability.Circuit.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# More synthesis rules over the De Morgan basis

Rules for synthesis bounds stated through the truth values of their targets, which is how
semantic arguments (simulations, reductions) produce Boolean functions: change a target to one
with the same truth values (`Synthesis.congr_iff`), a constant, bounded disjunctions and
conjunctions with uniform costs, disjunctions of conjunctions of literals, that is of available
functions and their negations (`Synthesis.any_all_literal`), exclusive ors and their finite
sums, and arbitrary functions of a few selected inputs (`Synthesis.selected`). Also bounds on
the circuit complexity of negations, conjunctions, disjunctions and exclusive ors, as instances
of `Cslib.Circuits.complexity_single_unary_le` and `Cslib.Circuits.complexity_single_binary_le`.

## Main results

* `Cslib.Circuits.Synthesis.congr_iff`, `Cslib.Circuits.Synthesis.of_forall_eq_const`.
* `Cslib.Circuits.Synthesis.exists_exists_mem`, `Cslib.Circuits.Synthesis.exists_forall_mem`.
* `Cslib.Circuits.Synthesis.literal`, `Cslib.Circuits.Synthesis.all_literal`,
  `Cslib.Circuits.Synthesis.any_all_literal`.
* `Cslib.Circuits.Synthesis.xor`: an exclusive or costs four gates.
* `Cslib.Circuits.Synthesis.sum`: a finite exclusive or costs four gates per term.
* `Cslib.Circuits.Synthesis.selected`: any function of `k` selected inputs costs
  `2 ^ k * (2 * k + 2) + 1` gates.
* `Cslib.Circuits.Boolean.complexity_not_le`, `Cslib.Circuits.Boolean.complexity_and_le`,
  `Cslib.Circuits.Boolean.complexity_or_le`, `Cslib.Circuits.Boolean.complexity_xor_le`.
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean

variable {n : ℕ}

namespace Synthesis

variable {s : Set (BooleanFunction n)} {f g : BooleanFunction n} {a b : ℕ}

/-- Change the target of a synthesis bound to a function with the same truth values. -/
theorem congr_iff (h : Synthesis interpretation s {f} a) (hfg : ∀ x, f x = true ↔ g x = true) :
    Synthesis interpretation s {g} a := by
  have : f = g := funext fun x => Bool.eq_iff_iff.2 (hfg x)
  exact this ▸ h

/-- A constant function costs one gate. -/
theorem of_forall_eq_const (b : Bool) (h : ∀ x, f x = b) : Synthesis interpretation s {f} 1 :=
  congr_iff (Synthesis.const b) fun x => by rw [h]

/-- A bounded disjunction, with a uniform bound `c` on the cost of its terms and a bound `m` on
their number. -/
theorem exists_exists_mem {ι : Type*} (indices : Finset ι) (F : ι → BooleanFunction n)
    {c m : ℕ} (hcard : indices.card ≤ m) (h : ∀ i ∈ indices, Synthesis interpretation s {F i} c) :
    ∃ g : BooleanFunction n, (∀ x, g x = true ↔ ∃ i ∈ indices, F i x = true) ∧
      Synthesis interpretation s {g} (m * (c + 1) + 1) := by
  refine ⟨_, fun x => decide_eq_true_iff, ?_⟩
  refine (Synthesis.exists_mem indices F (fun _ => c) h).mono Set.Subset.rfl Set.Subset.rfl ?_
  rw [Finset.sum_const, Nat.nsmul_eq_mul]
  have := Nat.mul_le_mul_right (c + 1) hcard
  omega

/-- A bounded conjunction, with a uniform bound `c` on the cost of its terms and a bound `m` on
their number. -/
theorem exists_forall_mem {ι : Type*} (indices : Finset ι) (F : ι → BooleanFunction n)
    {c m : ℕ} (hcard : indices.card ≤ m) (h : ∀ i ∈ indices, Synthesis interpretation s {F i} c) :
    ∃ g : BooleanFunction n, (∀ x, g x = true ↔ ∀ i ∈ indices, F i x = true) ∧
      Synthesis interpretation s {g} (m * (c + 1) + 1) := by
  refine ⟨_, fun x => decide_eq_true_iff, ?_⟩
  refine (Synthesis.forall_mem indices F (fun _ => c) h).mono Set.Subset.rfl Set.Subset.rfl ?_
  rw [Finset.sum_const, Nat.nsmul_eq_mul]
  have := Nat.mul_le_mul_right (c + 1) hcard
  omega

/-- A literal, an available function `f` asked to take the value `b`, costs at most one gate. -/
theorem literal (hf : f ∈ s) (b : Bool) :
    Synthesis interpretation s {fun x => decide (f x = b)} 1 := by
  cases b
  · exact congr_iff (Synthesis.of_mem hf).not fun x => by cases f x <;> simp
  · exact congr_iff ((Synthesis.of_mem hf).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le 1))
      fun x => by cases f x <;> simp

/-- A conjunction of literals over available functions costs two gates per literal and a
constant. -/
theorem all_literal {c : List (BooleanFunction n × Bool)} (hc : ∀ l ∈ c, l.1 ∈ s) :
    Synthesis interpretation s {fun x => c.all fun l => decide (l.1 x = l.2)}
      (2 * c.length + 1) := by
  have hval : (fun x => c.foldr (fun l acc => decide (l.1 x = l.2) && acc) true) =
      fun x => c.all fun l => decide (l.1 x = l.2) := by
    funext x
    clear hc
    induction c with
    | nil => rfl
    | cons l c ih => simp [ih]
  have h := Synthesis.foldr (I := interpretation) (s := s) (· && ·) 1
    (fun f g => ((Synthesis.of_mem (by simp)).and (Synthesis.of_mem (by simp))).mono
      Set.Subset.rfl Set.Subset.rfl le_rfl) c (f := fun l x => decide (l.1 x = l.2))
    (cost := fun _ => 1) (Synthesis.const true) fun l hl => literal (hc l hl) l.2
  rw [hval] at h
  refine h.mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  omega

/-- A disjunction of conjunctions of at most `w` literals over available functions. -/
theorem any_all_literal {D : List (List (BooleanFunction n × Bool))} {w : ℕ}
    (hw : ∀ c ∈ D, c.length ≤ w) (hD : ∀ c ∈ D, ∀ l ∈ c, l.1 ∈ s) :
    Synthesis interpretation s {fun x => D.any fun c => c.all fun l => decide (l.1 x = l.2)}
      (D.length * (2 * w + 2) + 1) := by
  have hval : (fun x => D.foldr (fun c acc => (c.all fun l => decide (l.1 x = l.2)) || acc)
      false) = fun x => D.any fun c => c.all fun l => decide (l.1 x = l.2) := by
    funext x
    clear hw hD
    induction D with
    | nil => rfl
    | cons c D ih => simp [ih]
  have h := Synthesis.foldr (I := interpretation) (s := s) (· || ·) 1
    (fun f g => ((Synthesis.of_mem (by simp)).or (Synthesis.of_mem (by simp))).mono
      Set.Subset.rfl Set.Subset.rfl le_rfl) D
    (f := fun c x => c.all fun l => decide (l.1 x = l.2)) (cost := fun _ => 2 * w + 1)
    (Synthesis.const false) fun c hc => (all_literal (hD c hc)).mono Set.Subset.rfl
      Set.Subset.rfl (by have := hw c hc; omega)
  rw [hval] at h
  refine h.mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]

/-- The exclusive or `f ⊕ g = (f ∨ g) ∧ ¬(f ∧ g)` costs four gates beyond its arguments. -/
theorem xor (hf : Synthesis interpretation s {f} a) (hg : Synthesis interpretation s {g} b) :
    Synthesis interpretation s {fun x => f x ^^ g x} (a + b + 4) := by
  have hf' : Synthesis interpretation {f, g} {f} 0 := of_mem (by simp)
  have hg' : Synthesis interpretation {f, g} {g} 0 := of_mem (by simp)
  have h := (hf'.or hg').and (hf'.and hg').not
  have heq : (fun x => (f x || g x) && !(f x && g x)) = fun x => f x ^^ g x := by
    funext x
    cases f x <;> cases g x <;> rfl
  rw [heq] at h
  exact hf.combine hg h

/-- A finite sum in the Boolean ring, an exclusive or of its terms, costs four gates per term
and a constant. -/
theorem sum {ι : Type*} (indices : Finset ι) (F : ι → BooleanFunction n) (cost : ι → ℕ)
    (h : ∀ i ∈ indices, Synthesis interpretation s {F i} (cost i)) :
    Synthesis interpretation s {fun x => ∑ i ∈ indices, F i x}
      ((∑ i ∈ indices, (cost i + 4)) + 1) := by
  have hop (f g : BooleanFunction n) :
      Synthesis interpretation {f, g} {fun x => f x + g x} 4 :=
    (Synthesis.of_mem (by simp)).xor (Synthesis.of_mem (by simp))
  have h' := Synthesis.finset_fold (· + ·) 4 hop indices (Synthesis.const false) h
  simp only [Finset.sum_eq_fold]
  exact h'

/-- A function of `k` selected inputs costs at most `2 ^ k * (2 * k + 2) + 1` gates: its
disjunctive normal form tests every accepted assignment of the selected inputs. Selectors may
repeat inputs. -/
theorem selected {k : ℕ} (wires : Fin k → Fin n) (φ : BooleanFunction k) :
    Synthesis interpretation (inputs n) {fun x => φ (x ∘ wires)} (2 ^ k * (2 * k + 2) + 1) := by
  classical
  let accepted := Finset.univ.filter fun q : BitString k => φ q = true
  have h := Synthesis.exists_mem accepted
    (fun q x => decide ((fun i => x (wires i)) = q)) (fun _ => 2 * k + 1)
    fun q _ => synthesis_minterm wires q
  refine (congr_iff h fun x => ?_).mono Set.Subset.rfl Set.Subset.rfl ?_
  · simp [accepted, Function.comp_def]
  · rw [Finset.sum_const, smul_eq_mul, show 2 * k + 1 + 1 = 2 * k + 2 by omega]
    have hcard : accepted.card ≤ 2 ^ k := by
      simpa [BitString, Fintype.card_fun] using Finset.card_le_univ accepted
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hcard) 1

end Synthesis

namespace Boolean

/-! ### Complexity of Boolean operations -/

/-- Negating the output costs one gate. -/
theorem complexity_not_le (f : BooleanFunction n) :
    complexity interpretation (single fun x => !f x) ≤
      complexity interpretation (single f) + 1 :=
  (complexity_single_unary_le not f).trans
    (Nat.add_le_add_left (Synthesis.of_mem (s := inputs 1) ⟨0, rfl⟩).not.complexity_le _)

/-- Combining two outputs with a binary operation that costs `c` gates on two inputs costs `c`
gates. -/
private theorem complexity_binary_le (f g : BooleanFunction n) (op : Bool → Bool → Bool) {c : ℕ}
    (hop : Synthesis interpretation (inputs 2) {fun y : Fin 2 → Bool => op (y 0) (y 1)} c) :
    complexity interpretation (single fun x => op (f x) (g x)) ≤
      complexity interpretation (single f) + complexity interpretation (single g) + c :=
  (complexity_single_binary_le op f g).trans (Nat.add_le_add_left hop.complexity_le _)

/-- A conjunction of two outputs costs one gate. -/
theorem complexity_and_le (f g : BooleanFunction n) :
    complexity interpretation (single fun x => f x && g x) ≤
      complexity interpretation (single f) + complexity interpretation (single g) + 1 :=
  complexity_binary_le f g (· && ·)
    ((Synthesis.of_mem (s := inputs 2) ⟨0, rfl⟩).and (Synthesis.of_mem ⟨1, rfl⟩))

/-- A disjunction of two outputs costs one gate. -/
theorem complexity_or_le (f g : BooleanFunction n) :
    complexity interpretation (single fun x => f x || g x) ≤
      complexity interpretation (single f) + complexity interpretation (single g) + 1 :=
  complexity_binary_le f g (· || ·)
    ((Synthesis.of_mem (s := inputs 2) ⟨0, rfl⟩).or (Synthesis.of_mem ⟨1, rfl⟩))

/-- An exclusive or of two outputs costs four gates. -/
theorem complexity_xor_le (f g : BooleanFunction n) :
    complexity interpretation (single fun x => f x ^^ g x) ≤
      complexity interpretation (single f) + complexity interpretation (single g) + 4 :=
  complexity_binary_le f g (· ^^ ·)
    ((Synthesis.of_mem (s := inputs 2) ⟨0, rfl⟩).xor (Synthesis.of_mem ⟨1, rfl⟩))

end Boolean

end Cslib.Circuits
