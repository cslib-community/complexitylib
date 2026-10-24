/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Mul
public import Complexity.Computability.WordRAM.Multiword.Sub

/-!
# Framed checked multiword arithmetic

The arithmetic programs reserve registers zero through three for workspace. Their frame
preserves memory and every other register outside the destination list, including registers
that are not source operands. Register lists are fixed when constructing the code.

## Main definitions

* `Arithmetic.Frame`: preservation of all digit registers outside a destination list.
* `Difference.truncatingProgram`: subtraction with a branch that clears an underflowed result.

## Main results

* `Schoolbook.preserves_program`: the syntactic register frame for schoolbook multiplication.
* `Schoolbook.exec_framed`: full multiplication with the digit-register frame.
* `Schoolbook.exec_eighteen_framed`: arbitrary layouts of eighteen-digit operands and a
  thirty-six-digit product, in exactly 2465 instructions.
* `Difference.exec_framed`: nonnegative subtraction with the digit-register frame.
* `Difference.exec_eighteen_framed`: eighteen-digit nonnegative subtraction in exactly
  112 instructions.
* `Difference.exec_eighteen_truncating`: general eighteen-digit natural-number subtraction
  in at most 132 instructions, with the full digit-register frame.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword

variable {r : ℕ}

namespace Arithmetic

/-- Arithmetic preserves memory and all registers outside the destinations and the four
reserved workspace registers. -/
def Frame (x y : Data (r + 4)) (ds : List (Fin (r + 4))) : Prop :=
  y.mem = x.mem ∧ ∀ i, 4 ≤ i.val → i ∉ ds → y.regs i = x.regs i

end Arithmetic

namespace Schoolbook

/-- A multiplication cell writes only its output digit and arithmetic workspace. -/
private theorem preserves_cell (a b d i : Fin (r + 4)) (hi : Workspace.IsDigit i) (hid : i ≠ d) :
    (cell a b d).Preserves i := by
  obtain ⟨ht, hc, _, _⟩ := Workspace.digit_ne hi
  simp only [cell, Code.Preserves, Op.dest_bin, ne_eq, Option.some.injEq]
  exact ⟨Ne.symm ht, Ne.symm ht, Ne.symm ht, Ne.symm hid, Ne.symm hc⟩

/-- Every digit register outside a row's destinations is syntactically preserved. -/
private theorem preserves_row (a : Fin (r + 4)) (bs ds : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : Workspace.IsDigit i) (hid : i ∉ ds) :
    (row a bs ds).Preserves i := by
  have hc := (Workspace.digit_ne hi).2.1
  induction bs generalizing ds with
  | nil =>
    simpa only [row, Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using Ne.symm hc
  | cons b bs ih =>
    cases ds with
    | nil =>
      simpa only [row, Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using Ne.symm hc
    | cons d ds =>
      exact ⟨preserves_cell a b d i hi (fun he => hid (by simp [he])),
        ih ds (fun hm => hid (by simp [hm]))⟩

/-- Every digit register outside all row destinations is syntactically preserved. -/
private theorem preserves_rows (as bs ds os : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : Workspace.IsDigit i) (hid : i ∉ ds ++ os) :
    (rows as bs ds os).Preserves i := by
  have hc := (Workspace.digit_ne hi).2.1
  induction as generalizing bs ds os with
  | nil =>
    simpa only [rows, Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using Ne.symm hc
  | cons a as ih =>
    cases os with
    | nil =>
      simpa only [rows, Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using Ne.symm hc
    | cons d os =>
      simp only [rows, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
      refine ⟨Ne.symm hc, preserves_row a bs ds i hi (fun hm => hid (by simp [hm])),
        ?_, ih (Workspace.zero :: bs) (ds ++ [d]) os ?_⟩
      · simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using
          (show d ≠ i from fun he => hid (by simp [he]))
      · intro hm
        apply hid
        simpa only [List.mem_append, List.mem_singleton, List.mem_cons, or_assoc,
          List.not_mem_nil, false_or] using hm

/-- Clearing an accumulator preserves every digit register outside it. -/
private theorem preserves_clear (ds : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : Workspace.IsDigit i) (hid : i ∉ ds) :
    (clear ds).Preserves i := by
  induction ds with
  | nil =>
    simpa only [clear, Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using
      Ne.symm (Workspace.digit_ne hi).2.1
  | cons d ds ih =>
    refine ⟨?_, ih (fun hm => hid (by simp [hm]))⟩
    simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using
      (show d ≠ i from fun he => hid (by simp [he]))

/-- Radix initialization writes only the four reserved workspace registers. -/
private theorem preserves_setup (i : Fin (r + 4)) (hi : Workspace.IsDigit i) :
    (Workspace.setup (r := r)).Preserves i := by
  obtain ⟨ht, hc, hb, hz⟩ := Workspace.digit_ne hi
  simp only [Workspace.setup, Code.Preserves, Op.width, Op.bin, Op.dest,
    ne_eq, Option.some.injEq]
  exact ⟨Ne.symm ht, Ne.symm hc, Ne.symm hb, Ne.symm hc, Ne.symm hb, Ne.symm hz⟩

/-- Multiplication writes only destination digits and the four reserved workspace registers. -/
theorem preserves_program (as bs ds os : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : Workspace.IsDigit i) (hid : i ∉ ds ++ os) :
    (program as bs ds os).Preserves i :=
  ⟨preserves_setup i hi, preserves_clear ds i hi (fun hm => hid (by simp [hm])),
    preserves_rows as bs ds os i hi hid⟩

/-- Clear a digit list, with its full frame and exact cost. -/
private theorem exec_clear_framed {w : ℕ} (ds : List (Fin (r + 4)))
    (hds : ∀ i ∈ ds, Workspace.IsDigit i) (hnd : ds.Nodup) (x : Data (r + 4)) :
    ∃ y, Exec w (clear ds) x y (ds.length + 1) ∧
      (∀ i ∈ ds, y.regs i = 0) ∧ Arithmetic.Frame x y ds := by
  induction ds generalizing x with
  | nil =>
    let y := x.set Workspace.carry (x.regs Workspace.carry)
    have he : Exec w (clear []) x y 1 := by ram_eval [clear, y]
    exact ⟨y, he, by simp, rfl, fun i hi hid =>
      he.regs_eq (preserves_clear [] i hi hid)⟩
  | cons d ds ih =>
    let z := x.set d 0
    obtain ⟨y, hey, hy, hyf⟩ := ih (fun i hi => hds i (by simp [hi]))
      (List.nodup_cons.mp hnd).2 z
    have hez : Exec w (.op (.const (B := .standard) d 0)) x z 1 := by ram_eval [z]
    have he : Exec w (clear (d :: ds)) x y ((d :: ds).length + 1) := by
      simpa only [clear, List.length_cons, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hez.seq hey
    refine ⟨y, he, ?_, hyf.1, fun i hi hid =>
      he.regs_eq (preserves_clear (d :: ds) i hi hid)⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hyf.2 i (hds i (by simp)) (List.nodup_cons.mp hnd).1]
      simp [z]
    · exact hy i hi

/-- Full multiplication preserves every non-destination digit register. The destination lists
and operands have arbitrary fixed lengths and arbitrary disjoint register layouts. -/
theorem exec_framed {w : ℕ} (hw : 2 ≤ w) (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length)
    (hin : ∀ i ∈ as ++ bs, Workspace.IsDigit i) (hout : ∀ i ∈ ds ++ os, Workspace.IsDigit i)
    (hnd : (ds ++ os).Nodup) (hdis : List.Disjoint (ds ++ os) (as ++ bs))
    (x : Data (r + 4))
    (ha : Multiword.Bounded (radix w) x as) (hb : Multiword.Bounded (radix w) x bs) :
    ∃ y, Exec w (program as bs ds os) x y
        (7 + bs.length + rowCost as.length bs.length) ∧
      Multiword.Bounded (radix w) y (ds ++ os) ∧
      Multiword.value (radix w) y (ds ++ os) =
        Multiword.value (radix w) x as * Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y (ds ++ os) := by
  obtain ⟨y, he, hy, hv, hm, _⟩ := exec hw as bs ds os hlen hos hin hout hnd hdis x ha hb
  exact ⟨y, he, hy, hv, hm, fun i hi hid =>
    he.regs_eq (preserves_program as bs ds os i hi hid)⟩

/-- An arbitrary eighteen-digit layout computes all thirty-six product digits in 2465
instructions while preserving every other digit register and memory. -/
theorem exec_eighteen_framed {w : ℕ} (hw : 2 ≤ w)
    (as bs ds os : List (Fin (r + 4)))
    (has : as.length = 18) (hbs : bs.length = 18)
    (hds : ds.length = 18) (hos : os.length = 18)
    (hin : ∀ i ∈ as ++ bs, Workspace.IsDigit i) (hout : ∀ i ∈ ds ++ os, Workspace.IsDigit i)
    (hnd : (ds ++ os).Nodup) (hdis : List.Disjoint (ds ++ os) (as ++ bs))
    (x : Data (r + 4))
    (ha : Multiword.Bounded (radix w) x as) (hb : Multiword.Bounded (radix w) x bs) :
    ∃ y, Exec w (program as bs ds os) x y 2465 ∧
      Multiword.Bounded (radix w) y (ds ++ os) ∧
      Multiword.value (radix w) y (ds ++ os) =
        Multiword.value (radix w) x as * Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y (ds ++ os) := by
  simpa only [has, hbs, rowCost] using
    exec_framed hw as bs ds os (hbs.trans hds.symm) (hos.trans has.symm)
      hin hout hnd hdis x ha hb

end Schoolbook

namespace Difference

/-- Subtraction without a sign hypothesis, retaining the exact final borrow equation.
This is the arithmetic core used before clearing a negative result. -/
private theorem exec_borrow_framed {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds) :
    ∃ y, Exec w (program w bs ds) x y (6 * ds.length + 4) ∧
      Multiword.Bounded (radix w) y ds ∧ y.regs borrow ≤ 1 ∧ y.regs one = 1 ∧
      Multiword.value (radix w) y ds + Multiword.value (radix w) x bs =
        Multiword.value (radix w) x ds + radix w ^ ds.length * y.regs borrow ∧
      Arithmetic.Frame x y ds := by
  let z := ((x.set base (radix w)).set one 1).set borrow 0
  have hz (i : Fin (r + 4)) (hi : IsDigit i) : z.regs i = x.regs i := by
    have hne : i ≠ borrow ∧ i ≠ base ∧ i ≠ one := by
      dsimp only [IsDigit] at hi
      simp only [ne_eq, Fin.ext_iff, borrow, base, one]
      omega
    simp only [z, Data.set_regs, Function.update_apply, hne.1, hne.2.1, hne.2.2,
      ↓reduceIte]
  have hzvalue (es : List (Fin (r + 4))) (hes : ∀ i ∈ es, IsDigit i) :
      Multiword.value (radix w) z es = Multiword.value (radix w) x es := by
    unfold Multiword.value
    congr 1
    exact List.map_congr_left fun i hi => hz i (hes i hi)
  obtain ⟨y, he, hyd, hyc, hyeq, hyf⟩ := exec_digits hw bs ds hlen hbs hds hnd hdis z
    (by simp [z, base, one, borrow]) (by simp [z, one, borrow])
    (fun i hi => by rw [hz i (hbs i hi)]; exact hb i hi)
    (fun i hi => by rw [hz i (hds i hi)]; exact hd i hi) (by simp [z])
  have hsetup : Exec (B := .standard) w
      (ram[base ← #(radix w); one ← #1; borrow ← #0]) x z 3 := by
    ram_eval [z, radix_fits hw, fits_one (by omega : w ≠ 0), base, one, borrow]
  have he' : Exec w (program w bs ds) x y (6 * ds.length + 4) := by
    convert hsetup.seq he using 1 <;> [rfl; omega]
  refine ⟨y, he', hyd, hyc, ?_, ?_, hyf.1,
    fun i hi hid => he'.regs_eq (preserves_program w bs ds i hi hid)⟩
  · rw [hyf.2 one (fun hm => ?_) (by simp [one, total]) (by simp [one, borrow])]
    · simp [z, one, borrow]
    · have := hds one hm
      simp [IsDigit] at this
  · have hzb : z.regs borrow = 0 := by simp [z]
    simpa only [hzvalue bs hbs, hzvalue ds hds, hzb, Nat.add_zero] using hyeq

/-- Subtraction followed by clearing its output exactly when the final borrow is one.
The second alternative is a self-copy, so both branches are executable for empty lists. -/
def truncatingProgram (w : ℕ) (bs ds : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq (program w bs ds)
    (.branch (.eq borrow one) (Schoolbook.clear ds) (.op (.copy borrow borrow)))

/-- Truncating subtraction writes only its destinations and reserved workspace. -/
theorem preserves_truncatingProgram (w : ℕ) (bs ds : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : IsDigit i) (hid : i ∉ ds) :
    (truncatingProgram w bs ds).Preserves i := by
  refine ⟨preserves_program w bs ds i hi hid, Schoolbook.preserves_clear ds i hi hid, ?_⟩
  have hc : i ≠ borrow := by
    dsimp only [IsDigit] at hi
    simp only [ne_eq, Fin.ext_iff, borrow]
    omega
  simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using Ne.symm hc

/-- Exact static size of truncating subtraction, including both branch bodies. -/
theorem size_truncatingProgram (w : ℕ) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) :
    (truncatingProgram w bs ds).size = 7 * ds.length + 8 := by
  simp only [truncatingProgram, Code.size, size_program w bs ds hlen, Schoolbook.size_clear]
  omega

/-- General natural-number subtraction, including underflow. The result is `Nat.sub`,
with bounded digits and preservation of every non-destination digit register and memory.
The clear branch costs `ds.length + 2`; the other branch costs three instructions. -/
theorem exec_truncating {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds) :
    ∃ y, ExecWithin w (truncatingProgram w bs ds) x y
        (6 * ds.length + 4 + max (ds.length + 2) 3) ∧
      Multiword.Bounded (radix w) y ds ∧
      Multiword.value (radix w) y ds =
        Multiword.value (radix w) x ds - Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y ds := by
  obtain ⟨z, he, hzd, hzc, hzo, hzeq, hzf⟩ :=
    exec_borrow_framed hw bs ds hlen hbs hds hnd hdis x hb hd
  by_cases hc : z.regs borrow = 1
  · obtain ⟨y, hey, hy, hyf⟩ := Schoolbook.exec_clear_framed (w := w) ds hds hnd z
    have hbranch : Exec w
        (.branch (.eq borrow one) (Schoolbook.clear ds) (.op (.copy borrow borrow)))
        z y (ds.length + 2) := by
      exact hey.branch_pos (show (Cond.eq borrow one).Holds z from hc.trans hzo.symm)
    have he' := he.seq hbranch
    have hlt : Multiword.value (radix w) x ds < Multiword.value (radix w) x bs := by
      have hyv : Multiword.value (radix w) z ds < radix w ^ ds.length := by
        exact Nat.ofDigits_lt_base_pow_length (one_lt_radix hw)
          (by
            intro a ha
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
            exact hzd i hi) |>.trans_eq (by simp)
      rw [hc, Nat.mul_one] at hzeq
      omega
    refine ⟨y, ⟨_, ?_, he'⟩, ?_, ?_, hyf.1.trans hzf.1,
      fun i hi hid => he'.regs_eq (preserves_truncatingProgram w bs ds i hi hid)⟩
    · exact Nat.add_le_add_left (le_max_left _ _) _
    · intro i hi
      rw [hy i hi]
      have := one_lt_radix hw
      omega
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
      unfold Multiword.value
      have hm : ds.map y.regs = List.replicate ds.length 0 := by
        simpa only [List.map_const'] using List.map_congr_left hy
      rw [hm, Nat.ofDigits_replicate_zero]
  · have hc0 : z.regs borrow = 0 := by omega
    let y := z.set borrow (z.regs borrow)
    have hey : Exec w (.op (.copy (B := .standard) borrow borrow)) z y 1 := by
      ram_eval [y]
    have hbranch := hey.branch_neg (pos := Schoolbook.clear ds)
      (show ¬(Cond.eq borrow one).Holds z from fun h => hc (h.trans hzo))
    have he' := he.seq hbranch
    have hyi (i : Fin (r + 4)) : y.regs i = z.regs i := by
      simp [y, Data.set_regs]
    have hyvalue : Multiword.value (radix w) y ds = Multiword.value (radix w) z ds := by
      unfold Multiword.value
      congr 1
      exact List.map_congr_left fun i _ => hyi i
    refine ⟨y, ⟨_, ?_, he'⟩, ?_, ?_, rfl.trans hzf.1,
      fun i hi hid => he'.regs_eq (preserves_truncatingProgram w bs ds i hi hid)⟩
    · exact Nat.add_le_add_left (le_max_right _ _) _
    · intro i hi
      rw [hyi]
      exact hzd i hi
    · rw [hyvalue]
      simp only [hc0, Nat.mul_zero, Nat.add_zero] at hzeq
      omega

/-- General eighteen-digit natural-number subtraction takes at most 132 instructions. -/
theorem exec_eighteen_truncating {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hbslen : bs.length = 18) (hdslen : ds.length = 18)
    (hbs : ∀ b ∈ bs, IsDigit b) (hds : ∀ d ∈ ds, IsDigit d)
    (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds) :
    ∃ y, ExecWithin w (truncatingProgram w bs ds) x y 132 ∧
      Multiword.Bounded (radix w) y ds ∧
      Multiword.value (radix w) y ds =
        Multiword.value (radix w) x ds - Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y ds := by
  simpa [hdslen, max_def] using
    exec_truncating hw bs ds (hbslen.trans hdslen.symm) hbs hds hnd hdis x hb hd

/-- Nonnegative subtraction preserves every digit register outside its in-place output. -/
theorem exec_framed {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds)
    (hle : Multiword.value (radix w) x bs ≤ Multiword.value (radix w) x ds) :
    ∃ y, Exec w (program w bs ds) x y (6 * ds.length + 4) ∧
      Multiword.Bounded (radix w) y ds ∧ y.regs borrow = 0 ∧
      Multiword.value (radix w) y ds =
        Multiword.value (radix w) x ds - Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y ds := by
  obtain ⟨y, he, hy, hc, hv, hm, _⟩ := exec hw bs ds hlen hbs hds hnd hdis x hb hd hle
  exact ⟨y, he, hy, hc, hv, hm, fun i hi hid =>
    he.regs_eq (preserves_program w bs ds i hi hid)⟩

/-- Eighteen-digit nonnegative subtraction has an exact 112-instruction execution and
preserves memory and every digit register outside the in-place destination list. -/
theorem exec_eighteen_framed {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hbslen : bs.length = 18) (hdslen : ds.length = 18)
    (hbs : ∀ b ∈ bs, IsDigit b) (hds : ∀ d ∈ ds, IsDigit d)
    (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds)
    (hle : Multiword.value (radix w) x bs ≤ Multiword.value (radix w) x ds) :
    ∃ y, Exec w (program w bs ds) x y 112 ∧
      Multiword.Bounded (radix w) y ds ∧ y.regs borrow = 0 ∧
      Multiword.value (radix w) y ds =
        Multiword.value (radix w) x ds - Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y ds := by
  simpa only [hdslen, Nat.reduceMul, Nat.reduceAdd] using
    exec_framed hw bs ds (hbslen.trans hdslen.symm) hbs hds hnd hdis x hb hd hle

end Difference

end Cslib.WordRAM.Multiword
