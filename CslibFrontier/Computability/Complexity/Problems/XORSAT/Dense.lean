/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import CslibFrontier.Computability.Complexity.Classes.P
public import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Tactic.FunProp

/-!
# Dense Gaussian elimination over the Boolean ring

Each equation consists of a Boolean coefficient row and a Boolean right-hand side. A column
step selects a row whose leading coefficient is one, adds it to all other rows with leading
coefficient one, and drops the column. The selected row becomes `0 = 0`; retaining it keeps the
number of equations fixed. If the column is zero, the step simply drops it. Repeating once per
column leaves only constant equations. This is the elimination argument following Theorem 4.3
of [Chen2006CSP], printed p. 16 (arXiv version 1).

The native multi-tape certificate composes the library's list operations and bounded iteration.
Every step weakly decreases the complete encoded state length, including on malformed rows.
The explicit width is unary; coefficient words and right-hand sides use their ordinary binary
encodings. Inputs with a row of a different width are rejected.

## Main definitions

* `Cslib.Complexity.XORSAT.Dense.Row`: Boolean coefficient word and right-hand side.
* `Cslib.Complexity.XORSAT.Dense.step`: one elimination column.
* `Cslib.Complexity.XORSAT.Dense.decide`: the dense-system decision algorithm.
-/

public section

namespace Cslib.Complexity.XORSAT.Dense

open Turing.MultiTapeTM

/-- A Boolean coefficient word and right-hand side. -/
abbrev Row := List Bool × Bool

/-- A list of dense equations. -/
abbrev System := List Row

/-- Dot product over the Boolean ring; missing coordinates have value zero. -/
@[expose] def dot : List Bool → List Bool → Bool
  | b :: bs, x :: xs => b * x + dot bs xs
  | _, _ => false

/-- Every row has the declared number of coefficients. -/
@[expose] def Width (n : ℕ) (F : System) : Prop := ∀ e ∈ F, e.1.length = n

/-- An assignment satisfies every equation. -/
@[expose] def Holds (F : System) (a : List Bool) : Prop := ∀ e ∈ F, dot e.1 a = e.2

/-- A solution has exactly the declared width. -/
@[expose] def Satisfiable (n : ℕ) (F : System) : Prop :=
  ∃ a : List Bool, a.length = n ∧ Holds F a

/-- Substitute the first variable using a pivot equation, then drop that variable. -/
@[expose] def clear (p e : Row) : Row :=
  if e.1.headD false then (e.1.tail.zipWith Bool.xor p.1.tail, e.2 ^^ p.2)
  else (e.1.tail, e.2)

/-- One column of Gaussian elimination. A missing pivot means that the column is zero. -/
@[expose] def step (F : System) : System :=
  let p := (F.find? fun e => e.1.headD false).getD ([], false)
  F.map (clear p)

/-- Framed rows with raw binary coefficient words. -/
@[expose] def encRow : Row ↪ List Bool := encPair encBits encBool

/-- A framed list of rows. -/
@[expose] def encSystem : System ↪ List Bool := encList encRow

/-- Unary declared width and a framed list of rows. -/
@[expose] def encInput : (ℕ × System) ↪ List Bool := encPair encUnary encSystem

/-- Check the row widths, eliminate all columns, then reject a remaining equation `0 = 1`. -/
@[expose] def decide (q : ℕ × System) : Bool :=
  q.2.all (fun e => Decidable.decide (e.1.length = q.1)) &&
    (step^[q.1] q.2).all (fun e => !e.2)

private theorem dot_xor {v w : List Bool} (h : v.length = w.length) (a : List Bool) :
    dot (v.zipWith Bool.xor w) a = dot v a + dot w a := by
  induction v generalizing w a with
  | nil => cases w <;> simp_all [dot, Bool.zero_eq_false]
  | cons b bs ih =>
    cases w with
    | nil => simp at h
    | cons c cs =>
      cases a with
      | nil => simp [dot, Bool.zero_eq_false]
      | cons x xs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h
        simp only [List.zipWith_cons_cons, dot, ← Bool.add_eq_xor, add_mul, ih h]
        abel

private theorem dot_cons (e : Row) (b : Bool) (a : List Bool) :
    dot e.1 (b :: a) = e.1.headD false * b + dot e.1.tail a := by
  cases e.1 <;> rfl

/-- Clearing a row preserves its equation whenever the pivot equation holds. -/
theorem clear_holds_iff (p e : Row) (h : e.1.length = p.1.length)
    (b : Bool) (a : List Bool) (hp : p.1.headD false = true)
    (hpa : dot p.1 (b :: a) = p.2) :
    dot (clear p e).1 a = (clear p e).2 ↔ dot e.1 (b :: a) = e.2 := by
  rw [dot_cons, hp, show (true : Bool) = 1 from rfl, one_mul] at hpa
  rw [dot_cons]
  unfold clear
  split
  · rename_i he
    rw [dot_xor (by simpa using congrArg (fun n => n - 1) h)]
    simp only [he, show (true : Bool) = 1 from rfl, one_mul]
    rw [← hpa, ← Bool.add_eq_xor]
    have halg (b u v r : Bool) : (u + v = r + (b + v)) ↔ b + u = r := by
      cases b <;> cases u <;> cases v <;> cases r <;> decide
    exact halg _ _ _ _
  · rename_i he
    have he' : e.1.headD false = false := Bool.eq_false_of_not_eq_true he
    rw [he']
    simp only [← Bool.zero_eq_false, zero_mul, zero_add]

/-- The residual system has one fewer column. -/
theorem width_step {n : ℕ} {F : System} (hF : Width (n + 1) F) : Width n (step F) := by
  intro e he
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
  unfold clear
  split
  · rename_i h
    have hp : ∃ p, F.find? (fun r => r.1.headD false) = some p := by
      cases hp : F.find? (fun r => r.1.headD false) with
      | some p => exact ⟨p, rfl⟩
      | none =>
        have hh := List.find?_eq_none.mp hp r hr
        simp_all
    obtain ⟨p, hp⟩ := hp
    simp only [hp, Option.getD_some, List.length_zipWith, List.length_tail]
    rw [hF r hr, hF p (List.mem_of_find?_eq_some hp)]
    simp
  · simp only [List.length_tail, hF r hr, Nat.add_sub_cancel]

/-- One elimination column preserves existence of a solution. -/
theorem satisfiable_step_iff {n : ℕ} {F : System} (hF : Width (n + 1) F) :
    Satisfiable n (step F) ↔ Satisfiable (n + 1) F := by
  cases hfind : F.find? (fun r => r.1.headD false) with
  | none =>
    have hz (r : Row) (hr : r ∈ F) : r.1.headD false = false :=
      Bool.eq_false_of_not_eq_true (List.find?_eq_none.mp hfind r hr)
    have hstep : step F = F.map (fun r => (r.1.tail, r.2)) := by
      simp only [step, hfind, Option.getD_none]
      apply List.map_congr_left
      intro r hr
      dsimp only [clear]
      rw [hz r hr]
      rfl
    rw [hstep]
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨false :: a, by simp [ha], fun r hr => ?_⟩
      rw [dot_cons, hz r hr]
      simpa only [← Bool.zero_eq_false, zero_mul, zero_add] using
        h (r.1.tail, r.2) (List.mem_map.mpr ⟨r, hr, rfl⟩)
    · rintro ⟨a, ha, h⟩
      cases a with
      | nil => simp at ha
      | cons b a =>
        refine ⟨a, by simpa using ha, ?_⟩
        intro e he
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
        have hh := h r hr
        rw [dot_cons, hz r hr] at hh
        simpa only [← Bool.zero_eq_false, zero_mul, zero_add] using hh
  | some p =>
    have hpmem := List.mem_of_find?_eq_some hfind
    have hp : p.1.headD false = true :=
      List.find?_some (p := fun r : Row => r.1.headD false) hfind
    have hstep : step F = F.map (clear p) := by simp only [step, hfind, Option.getD_some]
    rw [hstep]
    constructor
    · rintro ⟨a, ha, h⟩
      let b := p.2 + dot p.1.tail a
      have hpa : dot p.1 (b :: a) = p.2 := by
        rw [dot_cons, hp]
        change p.2 + dot p.1.tail a + dot p.1.tail a = p.2
        rw [add_assoc, BooleanRing.add_self, add_zero]
      refine ⟨b :: a, by simp [ha], fun r hr => ?_⟩
      exact (clear_holds_iff p r ((hF r hr).trans (hF p hpmem).symm) b a hp hpa).mp
        (h _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    · rintro ⟨a, ha, h⟩
      cases a with
      | nil => simp at ha
      | cons b a =>
        refine ⟨a, by simpa using ha, ?_⟩
        intro e he
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
        exact (clear_holds_iff p r ((hF r hr).trans (hF p hpmem).symm) b a hp
          (h p hpmem)).mpr (h r hr)

/-- Elimination decides dense systems of the declared width. -/
theorem elimination_correct {n : ℕ} {F : System} (hF : Width n F) :
    (step^[n] F).all (fun e => !e.2) = true ↔ Satisfiable n F := by
  induction n generalizing F with
  | zero =>
    simp only [Function.iterate_zero_apply, List.all_eq_true, Bool.not_eq_true']
    constructor
    · intro h
      exact ⟨[], rfl, fun e he => by simpa [dot] using (h e he).symm⟩
    · rintro ⟨a, ha, h⟩ e he
      have heq : e.1 = [] := List.eq_nil_of_length_eq_zero (hF e he)
      simpa [heq, dot] using (h e he).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (width_step hF), satisfiable_step_iff hF]

/-- The Boolean decider rejects malformed row widths and otherwise decides satisfiability. -/
theorem decide_eq_true_iff (q : ℕ × System) :
    decide q = true ↔ Width q.1 q.2 ∧ Satisfiable q.1 q.2 := by
  simp only [decide, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact and_congr_right fun h => by simpa only [List.all_eq_true] using elimination_correct h

/-- A column operation never lengthens an individual coefficient word. -/
theorem length_clear_le (p e : Row) : (clear p e).1.length ≤ e.1.length := by
  unfold clear
  split <;> simp only [List.length_zipWith, List.length_tail]
  · exact (Nat.min_le_left _ _).trans (Nat.sub_le _ _)
  · exact Nat.sub_le _ _

private theorem length_encSystem_map_le (f : Row → Row)
    (hf : ∀ e, (f e).1.length ≤ e.1.length) (F : System) :
    (encSystem (F.map f)).length ≤ (encSystem F).length := by
  induction F with
  | nil => rfl
  | cons e F ih =>
    have he := hf e
    simp only [encSystem, List.map_cons, encList_cons, List.length_append, length_frame,
      encRow, length_encPair, encBits_apply, encBool_apply, List.length_singleton] at *
    omega

/-- The complete encoded state weakly decreases at every iteration; there is no growth hidden
in repeated substitution or in the framing of rows. -/
theorem length_step_le (F : System) : (encSystem (step F)).length ≤ (encSystem F).length :=
  length_encSystem_map_le _ (length_clear_le _) F

private theorem clear_polyTime : ComputableTidilyInPolyTime
    (fun q : Row × Row => clear q.1 q.2) (encPair encRow encRow) encRow := by
  unfold clear encRow
  fun_prop

private theorem step_polyTime : ComputableTidilyInPolyTime step encSystem encSystem := by
  have hp : ComputableTidilyInPolyTime
      (fun F : System => (F.find? fun e => e.1.headD false).getD ([], false))
      encSystem encRow := by
    unfold encSystem encRow
    fun_prop
  exact ComputableTidilyInPolyTime.mapWith clear_polyTime hp
    ComputableTidilyInPolyTime.id'

/-- The actual Gaussian-elimination decider is computable in polynomial time on native
multi-tape Turing machines, with unary width and raw binary coefficient words. -/
theorem decide_polyTime : ComputableInPolyTime decide encInput encBool := by
  have hloop : ComputableTidilyInPolyTime
      (fun q : ℕ × System => step^[q.1] q.2) encInput encSystem :=
    .iterate_of_bounded_growth (.fst encUnary encSystem) (.snd encUnary encSystem)
      step_polyTime (growth := 0) (fun F => by simpa using length_step_le F)
  apply ComputableInPolyTime.of_tidy
  unfold decide
  have hwidth : ComputableTidilyInPolyTime
      (fun q : ℕ × System => q.2.all (fun e => Decidable.decide (e.1.length = q.1)))
      encInput encBool := by
    unfold encInput encSystem encRow
    fun_prop
  have hend : ComputableTidilyInPolyTime (fun F : System => F.all (fun e => !e.2))
      encSystem encBool := by
    unfold encSystem encRow
    fun_prop
  exact hwidth.bool_and' (hend.comp hloop)

/-- Dense XOR-SAT is in the native Turing-machine class `P`. -/
theorem satisfiable_mem_P :
    {q : ℕ × System | Width q.1 q.2 ∧ Satisfiable q.1 q.2} ∈ P encInput :=
  ⟨decide, decide_polyTime, fun q => (decide_eq_true_iff q).symm⟩

end Cslib.Complexity.XORSAT.Dense
