/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Digits

/-!
# Checked multiword subtraction

Digits use the half-word radix `β = 2 ^ (w / 2)`. A subtraction cell computes
`t = β + a - b - c`, then returns `t % β` and borrow `1 - t / β`.
For digits `a, b < β` and incoming borrow `c ≤ 1`, all intermediate values fit
the physical word, even at width two. In particular, no modular overflow is used.

## Main definitions

* `Difference.total`, `Difference.borrow`, `Difference.base`, `Difference.one`,
  `Difference.IsDigit`, `Difference.Frame`: reserved workspace registers, digit-register
  predicate, and frame relation.
* `Difference.cell`, `Difference.cellResult`: six standard instructions for a digit and
  outgoing borrow, and their mathematical state update.
* `Difference.digits`, `Difference.program`: unrolled digit cells and the fixed-length,
  in-place multiword difference routine.

## Main results

* `Difference.exec_cell`: checked execution and the exact borrow equation.
* `Difference.exec`: execution and reconstruction of a nonnegative difference.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Difference

variable {r : ℕ}

/-- Arithmetic workspace. -/
abbrev total : Fin (r + 4) := ⟨0, by omega⟩
/-- Incoming and outgoing borrow. -/
abbrev borrow : Fin (r + 4) := ⟨1, by omega⟩
/-- Half-word radix. -/
abbrev base : Fin (r + 4) := ⟨2, by omega⟩
/-- Preserved one. -/
abbrev one : Fin (r + 4) := ⟨3, by omega⟩

/-- Registers available for operand digits. -/
def IsDigit (i : Fin (r + 4)) : Prop := 4 ≤ i.val

private theorem digit_ne {i : Fin (r + 4)} (hi : IsDigit i) :
    i ≠ total ∧ i ≠ borrow ∧ i ≠ base ∧ i ≠ one := by
  dsimp only [IsDigit] at hi
  simp only [ne_eq, Fin.ext_iff, total, borrow, base, one]
  omega

/-- Only destination digits and the two arithmetic workspaces may change. -/
def Frame (x y : Data (r + 4)) (ds : List (Fin (r + 4))) : Prop :=
  y.mem = x.mem ∧ ∀ i, i ∉ ds → i ≠ total → i ≠ borrow → y.regs i = x.regs i

/-- Subtract one digit and the incoming borrow, replacing the minuend digit. -/
def cell (b d : Fin (r + 4)) : Code .standard (r + 4) := ram[
  total ← base + d;
  total ← total - b;
  total ← total - borrow;
  d ← total % base;
  borrow ← total / base;
  borrow ← one - borrow ]

/-- Exact result, including arithmetic workspace. -/
def cellResult (x : Data (r + 4)) (b d : Fin (r + 4)) : Data (r + 4) :=
  let t := x.regs base + x.regs d - x.regs b - x.regs borrow
  ((x.set total t).set d (t % x.regs base)).set borrow (1 - t / x.regs base)

/-- Every cell uses six instructions, with a zero-or-one outgoing borrow and exact
reconstruction. The equality accounts for the borrow at both ends. -/
theorem exec_cell {w : ℕ} (hw : 2 ≤ w) (x : Data (r + 4))
    (b d : Fin (r + 4)) (hb : IsDigit b) (hd : IsDigit d)
    (hbase : x.regs base = radix w) (hone : x.regs one = 1)
    (hxb : x.regs b < radix w) (hxd : x.regs d < radix w)
    (hc : x.regs borrow ≤ 1) :
    Exec w (cell b d) x (cellResult x b d) 6 ∧
      (cellResult x b d).regs d < radix w ∧
      (cellResult x b d).regs borrow ≤ 1 ∧
      (cellResult x b d).regs d + x.regs b + x.regs borrow =
        x.regs d + radix w * (cellResult x b d).regs borrow ∧
      Frame x (cellResult x b d) [d] := by
  obtain ⟨hbt, hbc, hbb, hbo⟩ := digit_ne hb
  obtain ⟨hdt, hdc, hdb, hdo⟩ := digit_ne hd
  let β := radix w
  let t := β + x.regs d - x.regs b - x.regs borrow
  have hβ : 1 < β := one_lt_radix hw
  have hsum : Fits w (β + x.regs d) := by
    have hs := radix_sq_le w
    unfold Fits
    dsimp only [β] at *
    nlinarith
  have hs₁ := hsum.of_le (Nat.sub_le (β + x.regs d) (x.regs b))
  have hs₂ := hs₁.of_le
    (Nat.sub_le (β + x.regs d - x.regs b) (x.regs borrow))
  have hm := hs₂.of_le (Nat.mod_le t β)
  have hq := hs₂.of_le (Nat.div_le_self t β)
  have ho : Fits w (1 - t / β) := (fits_one (by omega : w ≠ 0)).of_le
    (Nat.sub_le 1 _)
  have ht : t < 2 * β := by dsimp only [t]; omega
  have hquot : t / β ≤ 1 := by
    have := (Nat.div_lt_iff_lt_mul (by omega : 0 < β)).mpr ht
    omega
  have heq : t + x.regs b + x.regs borrow = β + x.regs d := by
    dsimp only [t]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ram_eval [cell, cellResult, hbt, hbc, hdt, hdc, hdb, hdo,
      Ne.symm hdt, Ne.symm hdb, Ne.symm hdo, total, borrow, base, one, Fin.mk.injEq,
      hbase, hone, hsum, hs₁, hs₂, hm, hq, ho, β, t]
    simp only [Data.set, Function.update_idem]
  · simpa only [cellResult, Data.set_regs, Function.update_apply, hdc, ↓reduceIte,
      hbase] using Nat.mod_lt t (by omega : 0 < β)
  · simp only [cellResult, Data.set_regs, Function.update_self]
    exact Nat.sub_le 1 _
  · simp only [cellResult, Data.set_regs, Function.update_apply, hdc, ↓reduceIte,
      hbase]
    have hm' := Nat.mod_add_div t β
    change t % β + x.regs b + x.regs borrow = x.regs d + β * (1 - t / β)
    have hsub : 1 - t / β + t / β = 1 := Nat.sub_add_cancel hquot
    nlinarith
  · refine ⟨rfl, ?_⟩
    intro i hi hit hic
    simp only [List.mem_singleton] at hi
    simp only [cellResult, Data.set_regs, Function.update_apply, hi, hit, hic, ↓reduceIte]

/-- Unroll the digit cells. The final self-copy also handles an empty list. -/
def digits : List (Fin (r + 4)) → List (Fin (r + 4)) → Code .standard (r + 4)
  | b :: bs, d :: ds => .seq (cell b d) (digits bs ds)
  | _, _ => .op (.copy borrow borrow)

/-- Unrolling `ds.length` subtraction cells takes `6 * ds.length + 1` instructions. -/
theorem size_digits (bs ds : List (Fin (r + 4))) (hlen : bs.length = ds.length) :
    (digits bs ds).size = 6 * ds.length + 1 := by
  induction bs generalizing ds with
  | nil => cases ds <;> simp_all [digits]
  | cons b bs ih =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [digits, Code.size, cell, ih ds hlen, List.length_cons]
      omega

private theorem value_cons (β : ℕ) (x : Data (r + 4)) (d : Fin (r + 4))
    (ds : List (Fin (r + 4))) :
    value β x (d :: ds) = x.regs d + β * value β x ds := rfl

/-- Execute an entire subtraction, retaining a possible final borrow. Source digits and
all registers outside the destinations and arithmetic workspaces are preserved. -/
theorem exec_digits {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4)) (hbase : x.regs base = radix w) (hone : x.regs one = 1)
    (hb : Bounded (radix w) x bs) (hd : Bounded (radix w) x ds)
    (hc : x.regs borrow ≤ 1) :
    ∃ y, Exec w (digits bs ds) x y (6 * ds.length + 1) ∧
      Bounded (radix w) y ds ∧ y.regs borrow ≤ 1 ∧
      value (radix w) y ds + value (radix w) x bs + x.regs borrow =
        value (radix w) x ds + radix w ^ ds.length * y.regs borrow ∧
      Frame x y ds := by
  induction bs generalizing ds x with
  | nil =>
    cases ds with
    | nil =>
      refine ⟨x.set borrow (x.regs borrow), ?_, ?_, ?_, ?_, ?_⟩
      · ram_eval [digits]
      · simp [Bounded]
      · simpa using hc
      · simp [value]
      · exact ⟨rfl, fun i _ _ hi => by
          simp only [Data.set_regs, Function.update_apply, hi, ↓reduceIte]⟩
    | cons => simp_all
  | cons b bs ih =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      have hlen' : bs.length = ds.length := by simpa using hlen
      have hd0 := hds d (by simp)
      obtain ⟨he, hzd, hzc, hzeq, hzf⟩ := exec_cell hw x b d
        (hbs b (by simp)) hd0 hbase hone (hb b (by simp)) (hd d (by simp)) hc
      let z := cellResult x b d
      have hzbs (i : Fin (r + 4)) (hi : i ∈ bs) : z.regs i = x.regs i :=
        hzf.2 i (by
          simp only [List.mem_singleton]
          rintro rfl
          exact List.disjoint_left.mp hdis (List.mem_cons_of_mem b hi) (List.mem_cons_self))
          (digit_ne (hbs i (by simp [hi]))).1
          (digit_ne (hbs i (by simp [hi]))).2.1
      have hzds (i : Fin (r + 4)) (hi : i ∈ ds) : z.regs i = x.regs i :=
        hzf.2 i (by
          simp only [List.mem_singleton]
          rintro rfl
          exact (List.nodup_cons.mp hnd).1 hi)
          (digit_ne (hds i (by simp [hi]))).1
          (digit_ne (hds i (by simp [hi]))).2.1
      have hzb : z.regs base = radix w := by
        rw [hzf.2 base (by simp [Ne.symm (digit_ne hd0).2.2.1])
          (by simp [base, total]) (by simp [base, borrow])]
        exact hbase
      have hzo : z.regs one = 1 := by
        rw [hzf.2 one (by simp [Ne.symm (digit_ne hd0).2.2.2])
          (by simp [one, total]) (by simp [one, borrow])]
        exact hone
      obtain ⟨y, hey, hyd, hyc, hyeq, hyf⟩ := ih ds hlen'
        (fun i hi => hbs i (by simp [hi])) (fun i hi => hds i (by simp [hi]))
        (List.nodup_cons.mp hnd).2
        (List.disjoint_left.mpr fun i hi hj =>
          List.disjoint_left.mp hdis (List.mem_cons_of_mem b hi) (List.mem_cons_of_mem d hj))
        z hzb hzo
        (fun i hi => by rw [hzbs i hi]; exact hb i (by simp [hi]))
        (fun i hi => by rw [hzds i hi]; exact hd i (by simp [hi])) hzc
      have hyd0 : y.regs d = z.regs d :=
        hyf.2 d (List.nodup_cons.mp hnd).1 (digit_ne hd0).1 (digit_ne hd0).2.1
      have hvalbs : value (radix w) z bs = value (radix w) x bs := by
        unfold value
        congr 1
        exact List.map_congr_left hzbs
      have hvalds : value (radix w) z ds = value (radix w) x ds := by
        unfold value
        congr 1
        exact List.map_congr_left hzds
      refine ⟨y, ?_, ?_, hyc, ?_, ?_⟩
      · have hseq := he.seq hey
        simpa only [digits, List.length_cons, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hseq
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [hyd0]; exact hzd
        · exact hyd i hi
      · rw [value_cons, value_cons, value_cons, hyd0, List.length_cons, pow_succ]
        rw [hvalbs, hvalds] at hyeq
        nlinarith
      · refine ⟨hyf.1.trans hzf.1, ?_⟩
        intro i hi hit hic
        have hine : i ≠ d := fun h => hi (List.mem_cons.mpr (Or.inl h))
        have him : i ∉ ds := fun hm => hi (by simp [hm])
        exact (hyf.2 i him hit hic).trans (hzf.2 i (by simp [hine]) hit hic)

/-- Width-only constants, followed by a zero incoming borrow and the unrolled cells. -/
def program (w : ℕ) (bs ds : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq (ram[base ← #(radix w); one ← #1; borrow ← #0]) (digits bs ds)

/-- Exact instruction count of `program`, including the three constant-setup instructions. -/
theorem size_program (w : ℕ) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) : (program w bs ds).size = 6 * ds.length + 4 := by
  simp only [program, Code.size, size_digits bs ds hlen]
  omega

/-- Only destinations and the four named workspace registers are written. -/
theorem preserves_program (w : ℕ) (bs ds : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : IsDigit i) (hid : i ∉ ds) :
    (program w bs ds).Preserves i := by
  obtain ⟨ht, hc, hb, ho⟩ := digit_ne hi
  have hcell (b d : Fin (r + 4)) (hd : d ≠ i) : (cell b d).Preserves i := by
    simp only [cell, Code.Preserves, Op.dest_bin, ne_eq, Option.some.injEq]
    exact ⟨Ne.symm ht, Ne.symm ht, Ne.symm ht, hd, Ne.symm hc, Ne.symm hc⟩
  have hds : (digits bs ds).Preserves i := by
    induction bs generalizing ds with
    | nil => simpa only [digits, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
        using Ne.symm hc
    | cons b bs ih =>
      cases ds with
      | nil => simpa only [digits, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
          using Ne.symm hc
      | cons d ds =>
        exact ⟨hcell b d (fun he => hid (by simp [he])),
          ih ds (fun hm => hid (by simp [hm]))⟩
  refine ⟨?_, hds⟩
  simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
  exact ⟨Ne.symm hb, Ne.symm ho, Ne.symm hc⟩

/-- Nonnegative multiword subtraction, with charged constant installation and no preloaded
radix or borrow. The running time depends only on the number of digits. -/
theorem exec {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4)) (hb : Bounded (radix w) x bs) (hd : Bounded (radix w) x ds)
    (hle : value (radix w) x bs ≤ value (radix w) x ds) :
    ∃ y, Exec w (program w bs ds) x y (6 * ds.length + 4) ∧
      Bounded (radix w) y ds ∧ y.regs borrow = 0 ∧
      value (radix w) y ds = value (radix w) x ds - value (radix w) x bs ∧
      y.mem = x.mem ∧ ∀ i ∈ bs, y.regs i = x.regs i := by
  let z := ((x.set base (radix w)).set one 1).set borrow 0
  have hz (i : Fin (r + 4)) (hi : IsDigit i) : z.regs i = x.regs i := by
    obtain ⟨_, hc, hb, ho⟩ := digit_ne hi
    simp only [z, Data.set_regs, Function.update_apply, hc, hb, ho, ↓reduceIte]
  have hzbs : value (radix w) z bs = value (radix w) x bs := by
    unfold value
    congr 1
    exact List.map_congr_left fun i hi => hz i (hbs i hi)
  have hzds : value (radix w) z ds = value (radix w) x ds := by
    unfold value
    congr 1
    exact List.map_congr_left fun i hi => hz i (hds i hi)
  obtain ⟨y, he, hyd, hyc, hyeq, hyf⟩ := exec_digits hw bs ds hlen hbs hds hnd hdis z
    (by simp [z, base, one, borrow]) (by simp [z, one, borrow])
    (fun i hi => by rw [hz i (hbs i hi)]; exact hb i hi)
    (fun i hi => by rw [hz i (hds i hi)]; exact hd i hi) (by simp [z])
  have hzbor : z.regs borrow = 0 := by simp [z]
  rw [hzbs, hzds, hzbor, Nat.add_zero] at hyeq
  have hzero : y.regs borrow = 0 := by
    by_contra hn
    have hh : y.regs borrow = 1 := by omega
    rw [hh, Nat.mul_one] at hyeq
    have hyv : value (radix w) y ds < radix w ^ ds.length := by
      exact Nat.ofDigits_lt_base_pow_length (one_lt_radix hw)
        (by
          intro a ha
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
          exact hyd i hi) |>.trans_eq (by simp)
    -- A final borrow says the minuend is strictly smaller than the subtrahend.
    omega
  refine ⟨y, ?_, hyd, hzero, ?_, hyf.1, ?_⟩
  · have hsetup : Exec (B := .standard) w
        (ram[base ← #(radix w); one ← #1; borrow ← #0]) x z 3 := by
      ram_eval [z, radix_fits hw, fits_one (by omega : w ≠ 0), base, one, borrow]
    have hh := hsetup.seq he
    convert hh using 1
    · rfl
    · omega
  · simp only [hzero, Nat.mul_zero, Nat.add_zero] at hyeq
    omega
  · intro i hi
    exact (hyf.2 i (fun him => List.disjoint_left.mp hdis hi him)
      (digit_ne (hbs i hi)).1 (digit_ne (hbs i hi)).2.1).trans (hz i (hbs i hi))

end Cslib.WordRAM.Multiword.Difference
