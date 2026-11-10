/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Affine
public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# XOR-SAT in polynomial time

The input is an ordinary list of parity equations on natural-number variable labels, with
arbitrary repetitions and Boolean right-hand sides. Labels use the existing binary `encNat`,
equations use the existing pair encoding, and systems use the existing framed-list encoding.
No bound on the numerical value of a variable label is imposed.

The compiler lists the occurring labels without duplicates and computes each coefficient as the
parity of its occurrences. This gives a dense system of polynomial size, decided by the native
Gaussian-elimination algorithm in `XORSAT.Dense`. The semantics count repeated occurrences
modulo two. Both constant equations and the empty system are supported.

This implements the normalization and elimination argument after [Chen2006CSP], Theorem 4.3,
printed p. 16 (arXiv version 1). The separate affine normal-form theorem does not assert an
efficient transformation of a variable truth table into equations: for fixed relation templates,
the chosen equations are fixed independently of the input.

## Main definitions

* `Cslib.Complexity.XORSAT.encoding`: lists of equations with binary variable labels.
* `Cslib.Complexity.XORSAT.compile`: compress labels and cancel repeated occurrences.
* `Cslib.Complexity.XORSAT.solve`: compile, then perform Gaussian elimination.

## Main results

* `Cslib.Complexity.XORSAT.solve_eq_true_iff`: correctness for ordinary parity systems.
* `Cslib.Complexity.XORSAT.solve_polyTime`: a native multi-tape polynomial-time certificate.
* `Cslib.Complexity.XORSAT.satisfiable_mem_P`: ordinary XOR-SAT is in `P`.
-/

public section

namespace Cslib.Complexity.XORSAT

open Turing.MultiTapeTM Cslib.Logic.PL

/-- A conjunction of parity equations on arbitrarily large natural-number variable labels. -/
abbrev System := AffineSystem ℕ

/-- A row is encoded by a framed list of binary labels and a Boolean right-hand side. -/
@[expose] def equationEncoding : AffineEquation ℕ ↪ List Bool :=
  encPair (encList encNat) encBool

/-- Ordinary framed-list encoding of sparse equations with binary labels. -/
@[expose] def encoding : System ↪ List Bool := encList equationEncoding

/-- The occurring variable labels, each retained once, in order of first occurrence. -/
@[expose] def labels (F : System) : List ℕ :=
  (F.flatMap Prod.fst).eraseDupsBy fun a b => Decidable.decide (a = b)

/-- The coefficient of a variable is the parity of its occurrences. -/
@[expose] def coefficient (vs : List ℕ) (v : ℕ) : Bool :=
  (vs.map fun w => Decidable.decide (w = v)).sum

/-- Compress occurring labels, keeping one Boolean coefficient for each label. -/
@[expose] def compile (F : System) : ℕ × Dense.System :=
  ((labels F).length, F.map fun e => ((labels F).map (coefficient e.1), e.2))

/-- Native dense Gaussian elimination after compression of binary variable labels. -/
@[expose] def solve (F : System) : Bool := Dense.decide (compile F)

/-- Ordinary satisfiability, with no restriction on the assignment away from occurring labels. -/
@[expose] def Satisfiable (F : System) : Prop := ∃ a : ℕ → Bool, F.Holds a

/-- The compressed label list contains precisely the occurring labels. -/
theorem mem_labels {F : System} {v : ℕ} :
    v ∈ labels F ↔ ∃ e ∈ F, v ∈ e.1 := by
  simp only [labels, List.mem_eraseDupsBy_eq, List.mem_flatMap]

/-- There is one compressed coordinate per distinct occurring variable. -/
theorem nodup_labels (F : System) : (labels F).Nodup :=
  List.nodup_eraseDupsBy_eq _

/-- Compression allocates at most one column per variable occurrence in the input. -/
theorem length_labels_le (F : System) :
    (labels F).length ≤ (F.flatMap Prod.fst).length :=
  (List.eraseDupsBy_sublist _).length_le

/-- Every compiled row has exactly the declared width. -/
theorem width_compile (F : System) : Dense.Width (compile F).1 (compile F).2 := by
  intro r hr
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hr
  exact List.length_map _

private theorem dot_map (l : List ℕ) (f g : ℕ → Bool) :
    Dense.dot (l.map f) (l.map g) = (l.map fun v => f v * g v).sum := by
  induction l with
  | nil => rfl
  | cons v l ih => simp only [List.map_cons, Dense.dot, List.sum_cons, ih]

private theorem sum_single (l : List ℕ) (hl : l.Nodup) (v : ℕ) (a : ℕ → Bool) :
    (l.map fun w => Decidable.decide (v = w) * a w).sum =
      if v ∈ l then a v else 0 := by
  have heq (w : ℕ) : Decidable.decide (v = w) * a w = if w = v then a w else 0 := by
    by_cases h : w = v
    · subst w
      simp only [decide_true, ite_true]
      rfl
    · simp only [Ne.symm h, decide_false, h, ite_false]
      rfl
  simp_rw [heq]
  rw [← List.sum_toFinset _ hl]
  simp

private theorem sum_coefficients (l vs : List ℕ) (hl : l.Nodup)
    (hvs : ∀ v ∈ vs, v ∈ l) (a : ℕ → Bool) :
    (l.map fun v => coefficient vs v * a v).sum = (vs.map a).sum := by
  induction vs with
  | nil => simp [coefficient]
  | cons v vs ih =>
    have hv := hvs v (by simp)
    have ht : ∀ w ∈ vs, w ∈ l := fun w hw => hvs w (by simp [hw])
    simp only [coefficient, List.map_cons, List.sum_cons, add_mul]
    rw [List.sum_map_add, sum_single l hl v a, ite_eq_left hv]
    exact congrArg (a v + ·) (ih ht)

/-- Compiled rows evaluate exactly as their sparse input equations, including repetitions. -/
theorem dot_compile_row (F : System) (e : AffineEquation ℕ) (he : e ∈ F) (a : ℕ → Bool) :
    Dense.dot ((labels F).map (coefficient e.1)) ((labels F).map a) =
      (e.1.map a).sum := by
  rw [dot_map]
  exact sum_coefficients _ _ (nodup_labels F)
    (fun v hv => mem_labels.mpr ⟨e, he, hv⟩) a

/-- The compiler preserves the satisfaction relation on every assignment. -/
theorem holds_compile (F : System) (a : ℕ → Bool) :
    Dense.Holds (compile F).2 ((labels F).map a) ↔ F.Holds a := by
  constructor
  · intro h e he
    have hh := h _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    change Dense.dot ((labels F).map (coefficient e.1)) ((labels F).map a) = e.2 at hh
    rwa [dot_compile_row F e he a] at hh
  · intro h r hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    rw [dot_compile_row F e he a]
    exact h e he

private theorem exists_assignment {l : List ℕ} (hl : l.Nodup) {a : List Bool}
    (ha : a.length = l.length) : ∃ f : ℕ → Bool, l.map f = a := by
  induction l generalizing a with
  | nil =>
    have : a = [] := List.eq_nil_of_length_eq_zero ha
    exact ⟨fun _ => false, this.symm⟩
  | cons v l ih =>
    cases a with
    | nil => simp at ha
    | cons b a =>
      obtain ⟨hv, hl⟩ := List.nodup_cons.mp hl
      obtain ⟨f, hf⟩ := ih hl (Nat.add_right_cancel ha)
      refine ⟨Function.update f v b, ?_⟩
      rw [List.map_cons, Function.update_self]
      congr 1
      rw [← hf]
      apply List.map_congr_left
      intro w hw
      have hwv : w ≠ v := by rintro rfl; exact hv hw
      exact Function.update_of_ne hwv _ _

/-- Sparse satisfiability is equivalent to satisfiability of the compressed dense system. -/
theorem satisfiable_compile_iff (F : System) :
    Dense.Satisfiable (compile F).1 (compile F).2 ↔ Satisfiable F := by
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨f, hf⟩ := exists_assignment (nodup_labels F) ha
    refine ⟨f, (holds_compile F f).mp ?_⟩
    rwa [hf]
  · rintro ⟨a, ha⟩
    exact ⟨(labels F).map a, List.length_map _, (holds_compile F a).mpr ha⟩

/-- The executable solver decides ordinary sparse systems with binary variable labels. -/
theorem solve_eq_true_iff (F : System) : solve F = true ↔ Satisfiable F := by
  rw [solve, Dense.decide_eq_true_iff, and_iff_right (width_compile F), satisfiable_compile_iff]

private theorem labels_polyTime :
    ComputableInPolyTime labels encoding (encList encNat) := by
  unfold labels encoding equationEncoding
  fun_prop

private theorem sum_polyTime :
    ComputableTidilyInPolyTime (fun l : List Bool => l.sum) encBits encBool := by
  simpa only [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false] using
    ComputableTidilyInPolyTime.bitsFoldlWithInput Bool.xor
      (ComputableTidilyInPolyTime.id' (encIn := encBits))
      (ComputableTidilyInPolyTime.const false)

@[fun_prop] private theorem coefficient_polyTime : ComputableTidilyInPolyTime
    (fun q : List ℕ × ℕ => coefficient q.1 q.2)
      (encPair (encList encNat) encNat) encBool := by
  have hbits : ComputableTidilyInPolyTime
      (fun q : List ℕ × ℕ => q.1.map fun w => Decidable.decide (w = q.2))
      (encPair (encList encNat) encNat) encBits := by
    fun_prop
  exact sum_polyTime.comp hbits

/-- Label compression is itself a native polynomial-time computation. Binary labels are only
compared, never expanded into a table indexed by their numerical value. -/
theorem compile_polyTime : ComputableInPolyTime compile encoding Dense.encInput := by
  have hvars := labels_polyTime.tidy
  apply ComputableInPolyTime.of_tidy
  unfold compile Dense.encInput Dense.encSystem Dense.encRow
  unfold encoding equationEncoding at hvars ⊢
  fun_prop

/-- Ordinary XOR-SAT is decided in polynomial time by native multi-tape machines. -/
theorem solve_polyTime : ComputableInPolyTime solve encoding encBool :=
  Dense.decide_polyTime.comp compile_polyTime

/-- Ordinary systems of affine parity equations, with sparse binary variable labels, are in P. -/
theorem satisfiable_mem_P : {F : System | Satisfiable F} ∈ P encoding :=
  ⟨solve, solve_polyTime, fun F => (solve_eq_true_iff F).symm⟩

end Cslib.Complexity.XORSAT
