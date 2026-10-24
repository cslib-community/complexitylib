/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Workspace

/-!
# Checked transfers between scalar words and digit lists

Register lists and supplied constants determine the unrolled standard-basis code. Digits are
little endian in the half-word radix. Registers zero through three are reserved workspace.

## Main definitions

* `Cslib.WordRAM.Multiword.Transfer.copy`: copy disjoint equal-length register lists.
* `Cslib.WordRAM.Multiword.Transfer.constants`: install a supplied list of constants.
* `Cslib.WordRAM.Multiword.Transfer.accumulate`, `Cslib.WordRAM.Multiword.Transfer.assemble`:
  Horner accumulation and scalar reconstruction from digit registers.
* `Cslib.WordRAM.Multiword.Transfer.extract`, `Cslib.WordRAM.Multiword.Transfer.split`: digit
  extraction and splitting of a physical scalar into digit registers.

## Main results

* `Cslib.WordRAM.Multiword.Transfer.exec_copy`: exact copying and register preservation.
* `Cslib.WordRAM.Multiword.Transfer.exec_constants`: exact installation of bounded constants.
* `Cslib.WordRAM.Multiword.Transfer.exec_assemble`: reconstruction when the scalar fits.
* `Cslib.WordRAM.Multiword.Transfer.exec_split_eighteen`: exact eighteen-digit conversion.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Transfer

open Workspace

variable {r : ℕ}

/-- Copy one register per instruction, with a final workspace self-copy. -/
def copy : List (Fin (r + 4)) → List (Fin (r + 4)) → Code .standard (r + 4)
  | a :: as, d :: ds => .seq (.op (.copy d a)) (copy as ds)
  | _, _ => .op (.copy carry carry)

/-- Exact width-independent code size. -/
theorem size_copy (as ds : List (Fin (r + 4))) (hlen : as.length = ds.length) :
    (copy as ds).size = ds.length + 1 := by
  induction as generalizing ds with
  | nil => cases ds <;> simp_all [copy]
  | cons a as ih => cases ds <;> simp_all [copy, Code.size, Nat.add_comm]

/-- Copying preserves the exact digit sequence, memory, and every register outside the outputs.
Source registers need not be distinct. -/
theorem exec_copy {w : ℕ} (as ds : List (Fin (r + 4)))
    (hlen : as.length = ds.length) (hnd : ds.Nodup) (hdis : List.Disjoint ds as)
    (x : Data (r + 4)) :
    ∃ y, Exec w (copy as ds) x y (ds.length + 1) ∧
      ds.map y.regs = as.map x.regs ∧ Frame x y ds ∧
      ∀ i ∉ ds, y.regs i = x.regs i := by
  induction as generalizing ds x with
  | nil =>
    cases ds with
    | cons => simp_all
    | nil =>
      refine ⟨x.set carry (x.regs carry), Exec.copy, ?_, ?_, ?_⟩
      · rfl
      · exact ⟨rfl, fun i _ _ _ => by simp⟩
      · intro i _; simp
  | cons a as ih =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      have hlen' : as.length = ds.length := by simpa using hlen
      have hdis' : List.Disjoint ds as := by
        exact List.disjoint_left.mpr fun i hi hj =>
          List.disjoint_left.mp hdis (List.mem_cons_of_mem d hi)
            (List.mem_cons_of_mem a hj)
      let z := x.set d (x.regs a)
      have hz (i : Fin (r + 4)) (hi : i ∈ a :: as) : z.regs i = x.regs i := by
        have hn : i ≠ d := by
          rintro rfl
          exact List.disjoint_left.mp hdis (by simp) hi
        simp [z, hn]
      obtain ⟨y, hey, hym, hyf, hyp⟩ := ih ds hlen' (List.nodup_cons.mp hnd).2 hdis' z
      have hp : ∀ i ∉ d :: ds, y.regs i = x.regs i := by
        intro i hi
        rw [hyp i (fun hm => hi (by simp [hm]))]
        simp [z, show i ≠ d by intro h; exact hi (by simp [h])]
      refine ⟨y, ?_, ?_, ⟨hyf.1, fun i hi _ _ => hp i hi⟩, hp⟩
      · simpa only [copy, List.length_cons, Nat.add_comm 1] using
          (show Exec w (.op (.copy (B := .standard) d a)) x z 1 from Exec.copy).seq hey
      · simp only [List.map_cons]
        congr 1
        · rw [hyp d (List.nodup_cons.mp hnd).1]; simp [z]
        · rw [hym]
          exact List.map_congr_left fun i hi => hz i (by simp [hi])

/-- Exact reconstruction follows from the copied digit sequence, at any radix. -/
theorem value_copy {β : ℕ} {x y : Data (r + 4)} {as ds : List (Fin (r + 4))}
    (h : ds.map y.regs = as.map x.regs) : value β y ds = value β x as := by
  unfold value
  rw [h]

/-- Copying an exact digit sequence preserves its digit bound. -/
theorem bounded_copy {β : ℕ} {x y : Data (r + 4)} {as ds : List (Fin (r + 4))}
    (h : ds.map y.regs = as.map x.regs) (hb : Bounded β x as) : Bounded β y ds := by
  intro i hi
  have hm : y.regs i ∈ as.map x.regs := by
    rw [← h]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact hb j hj

/-- Install supplied constants; they may depend on the physical width but not runtime data. -/
def constants : List (Fin (r + 4)) → List ℕ → Code .standard (r + 4)
  | d :: ds, c :: cs => .seq (.op (.const d c)) (constants ds cs)
  | _, _ => .op (.copy carry carry)

/-- Exact width-independent instruction count for supplied constants. -/
theorem size_constants (ds : List (Fin (r + 4))) (cs : List ℕ)
    (hlen : ds.length = cs.length) : (constants ds cs).size = ds.length + 1 := by
  induction ds generalizing cs with
  | nil => cases cs <;> simp_all [constants]
  | cons d ds ih =>
    cases cs with
    | nil => simp_all
    | cons c cs =>
      have hlen' : ds.length = cs.length := by simpa using hlen
      simp only [constants, Code.size, ih cs hlen', List.length_cons]
      omega

/-- Constants are checked against the physical width. No initial destination contents matter. -/
theorem exec_constants {w : ℕ} (ds : List (Fin (r + 4))) (cs : List ℕ)
    (hlen : ds.length = cs.length) (hnd : ds.Nodup) (hfit : ∀ c ∈ cs, Fits w c)
    (x : Data (r + 4)) :
    ∃ y, Exec w (constants ds cs) x y (ds.length + 1) ∧
      ds.map y.regs = cs ∧ Frame x y ds ∧ ∀ i ∉ ds, y.regs i = x.regs i := by
  induction ds generalizing cs x with
  | nil =>
    cases cs with
    | cons => simp_all
    | nil =>
      refine ⟨x.set carry (x.regs carry), Exec.copy, rfl, ?_, ?_⟩
      · exact ⟨rfl, fun i _ _ _ => by simp⟩
      · intro i _; simp
  | cons d ds ih =>
    cases cs with
    | nil => simp_all
    | cons c cs =>
      have hlen' : ds.length = cs.length := by simpa using hlen
      let z := x.set d c
      obtain ⟨y, hey, hym, hyf, hyp⟩ := ih cs hlen' (List.nodup_cons.mp hnd).2
        (fun c hc => hfit c (by simp [hc])) z
      have hp : ∀ i ∉ d :: ds, y.regs i = x.regs i := by
        intro i hi
        rw [hyp i (fun hm => hi (by simp [hm]))]
        simp [z, show i ≠ d by intro h; exact hi (by simp [h])]
      refine ⟨y, ?_, ?_, ⟨hyf.1, fun i hi _ _ => hp i hi⟩, hp⟩
      · simpa only [constants, List.length_cons, Nat.add_comm 1] using
          (show Exec w (.op (.const (B := .standard) d c)) x z 1 from
            Exec.const (hfit c (by simp))).seq hey
      · simp only [List.map_cons, List.cons.injEq]
        refine ⟨?_, hym⟩
        rw [hyp d (List.nodup_cons.mp hnd).1]; simp [z]

/-- Installing bounded digits gives the requested value in the half-word radix. -/
theorem exec_digits {w : ℕ} (hw : 2 ≤ w) (ds : List (Fin (r + 4))) (cs : List ℕ)
    (hlen : ds.length = cs.length) (hnd : ds.Nodup) (hb : ∀ c ∈ cs, c < radix w)
    (x : Data (r + 4)) :
    ∃ y, Exec w (constants ds cs) x y (ds.length + 1) ∧
      Bounded (radix w) y ds ∧ value (radix w) y ds = Nat.ofDigits (radix w) cs ∧
      Frame x y ds ∧ ∀ i ∉ ds, y.regs i = x.regs i := by
  obtain ⟨y, he, hm, hf, hp⟩ := exec_constants ds cs hlen hnd
    (fun c hc => (hb c hc).trans (radix_fits hw)) x
  refine ⟨y, he, ?_, ?_, hf, hp⟩
  · intro i hi
    apply hb
    rw [← hm]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  · unfold value
    rw [hm]

/-- Reconstruct by Horner evaluation, high digits first, into workspace register zero. -/
def accumulate : List (Fin (r + 4)) → Code .standard (r + 4)
  | [] => .op (.const total 0)
  | a :: as => .seq (accumulate as)
      (ram[ total ← total * base; total ← total + a ])

/-- Horner evaluation costs two instructions per digit plus initialization. -/
theorem size_accumulate (as : List (Fin (r + 4))) :
    (accumulate as).size = 2 * as.length + 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [accumulate, Code.size, ih, List.length_cons]; omega

private theorem exec_accumulate {w : ℕ} (hw : 2 ≤ w) (as : List (Fin (r + 4)))
    (hin : ∀ i ∈ as, IsDigit i) (x : Data (r + 4)) (hbase : x.regs base = radix w)
    (hfit : Fits w (value (radix w) x as)) :
    ∃ y, Exec w (accumulate as) x y (2 * as.length + 1) ∧
      y.regs total = value (radix w) x as ∧ y.mem = x.mem ∧
      ∀ i, i ≠ total → y.regs i = x.regs i := by
  induction as generalizing x with
  | nil =>
    refine ⟨x.set total 0, Exec.const (fits_zero w), rfl, rfl, ?_⟩
    intro i hi
    exact Function.update_of_ne hi _ _
  | cons a as ih =>
    have hβ : 1 ≤ radix w := by have := one_lt_radix hw; omega
    have hv : value (radix w) x as ≤ value (radix w) x (a :: as) := by
      change _ ≤ x.regs a + radix w * value (radix w) x as
      nlinarith
    obtain ⟨z, hez, hzv, hzm, hzp⟩ := ih (fun i hi => hin i (by simp [hi])) x
      hbase (hfit.of_le hv)
    have hzb : z.regs base = radix w := by
      rw [hzp base (by simp [base, total])]; exact hbase
    have hza : z.regs a = x.regs a := hzp a (digit_ne (hin a (by simp))).1
    have hp : Fits w (z.regs total * z.regs base) := by
      rw [hzv, hzb]
      apply hfit.of_le
      change _ ≤ x.regs a + radix w * value (radix w) x as
      nlinarith
    have hs : Fits w (z.regs total * z.regs base + z.regs a) := by
      rw [hzv, hzb, hza]
      simpa only [value, List.map_cons, Nat.ofDigits_cons, Nat.mul_comm,
        Nat.add_comm] using hfit
    let y := (z.set total (z.regs total * z.regs base)).set total
      (z.regs total * z.regs base + z.regs a)
    have hey : Exec w (ram[ total ← total * base; total ← total + a ]) z y 2 := by
      ram_eval [y, hp, hs, (digit_ne (hin a (by simp))).1]
    refine ⟨y, ?_, ?_, hzm, ?_⟩
    · simpa only [accumulate, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc] using hez.seq hey
    · simp only [y, Data.set_regs, Function.update_self, hzv, hzb, hza]
      change _ = x.regs a + radix w * value (radix w) x as
      ring
    · intro i hi
      simpa only [y, Data.set_regs, Function.update_of_ne hi] using hzp i hi

/-- Initialize the radix, reconstruct, and copy to the physical destination register. -/
def assemble (as : List (Fin (r + 4))) (d : Fin (r + 4)) : Code .standard (r + 4) :=
  .seq Workspace.setup (.seq (accumulate as) (.op (.copy d total)))

/-- Assembly has a linear instruction count independent of the physical width. -/
theorem size_assemble (as : List (Fin (r + 4))) (d : Fin (r + 4)) :
    (assemble as d).size = 2 * as.length + 8 := by
  simp only [assemble, Code.size, Workspace.setup, size_accumulate]
  omega

/-- Reconstruction is checked at the original physical width. All intermediate Horner values
fit because the nonnegative final scalar fits. Inputs are preserved when disjoint from `d`.
The frame includes the radix and zero workspace alongside the destination. -/
theorem exec_assemble {w : ℕ} (hw : 2 ≤ w) (as : List (Fin (r + 4)))
    (d : Fin (r + 4)) (hin : ∀ i ∈ as, IsDigit i) (x : Data (r + 4))
    (hfit : Fits w (value (radix w) x as)) :
    ∃ y, Exec w (assemble as d) x y (2 * as.length + 8) ∧
      y.regs d = value (radix w) x as ∧ Frame x y [base, zero, d] ∧
      ∀ i, IsDigit i → i ≠ d → y.regs i = x.regs i := by
  let z := Workspace.setupResult w x
  have hval : value (radix w) z as = value (radix w) x as := by
    unfold value
    congr 1
    exact List.map_congr_left fun i hi => Workspace.setup_digit w x (hin i hi)
  have hbase : z.regs base = radix w := by
    simp [z, Workspace.setupResult, base, zero]
  obtain ⟨u, heu, huv, hum, hup⟩ := exec_accumulate hw as hin z hbase
    (by rwa [hval])
  let y := u.set d (u.regs total)
  have hp (i : Fin (r + 4)) (hi : IsDigit i) (hid : i ≠ d) :
      y.regs i = x.regs i := by
    rw [show y.regs i = u.regs i by simp [y, hid], hup i (digit_ne hi).1]
    exact Workspace.setup_digit w x hi
  refine ⟨y, ?_, ?_, ⟨hum, ?_⟩, hp⟩
  · have hecopy : Exec w (.op (.copy (B := .standard) d total)) u y 1 := Exec.copy
    unfold assemble
    convert (Workspace.exec_setup hw x).seq (heu.seq hecopy) using 1
    omega
  · simpa only [y, Data.set_regs, Function.update_self, hval] using huv
  · intro i hi ht hc
    have hb : i ≠ base := by intro h; exact hi (by simp [h])
    have hz : i ≠ zero := by intro h; exact hi (by simp [h])
    have hd : i ≠ d := by intro h; exact hi (by simp [h])
    simp only [y, Data.set_regs, Function.update_of_ne hd, hup i ht,
      z, Workspace.setupResult, Function.update_of_ne ht, Function.update_of_ne hc,
      Function.update_of_ne hb, Function.update_of_ne hz]

/-- Extract low digits by remainder and division, retaining the final quotient in `total`. -/
def extract : List (Fin (r + 4)) → Code .standard (r + 4)
  | [] => .op (.copy carry carry)
  | d :: ds => .seq (ram[ d ← total % base; total ← total / base ]) (extract ds)

/-- Two checked instructions per extracted digit, followed by a workspace self-copy. -/
theorem size_extract (ds : List (Fin (r + 4))) :
    (extract ds).size = 2 * ds.length + 1 := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [extract, Code.size, ih, List.length_cons]; omega

private theorem exec_extract {w : ℕ} (hw : 2 ≤ w) (ds : List (Fin (r + 4)))
    (hout : ∀ i ∈ ds, IsDigit i) (hnd : ds.Nodup) (x : Data (r + 4))
    (hbase : x.regs base = radix w) (hfit : Fits w (x.regs total)) :
    ∃ y, Exec w (extract ds) x y (2 * ds.length + 1) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds + radix w ^ ds.length * y.regs total = x.regs total ∧
      Fits w (y.regs total) ∧ y.mem = x.mem ∧
      ∀ i, i ∉ ds → i ≠ total → y.regs i = x.regs i := by
  induction ds generalizing x with
  | nil =>
    refine ⟨x.set carry (x.regs carry), Exec.copy, by simp [Bounded], ?_, ?_, rfl, ?_⟩
    · simp [value, total, carry]
    · simpa [total, carry] using hfit
    · intro i _ _; simp
  | cons d ds ih =>
    obtain ⟨hdt, _, hdb, _⟩ := digit_ne (hout d (by simp))
    have hm := hfit.of_le (Nat.mod_le (x.regs total) (x.regs base))
    have hq := hfit.of_le (Nat.div_le_self (x.regs total) (x.regs base))
    let z := (x.set d (x.regs total % x.regs base)).set total
      (x.regs total / x.regs base)
    have hez : Exec w (ram[ d ← total % base; total ← total / base ]) x z 2 := by
      ram_eval [z, hm, hq, Ne.symm hdt, Ne.symm hdb]
    have hzq : z.regs total = x.regs total / radix w := by simp [z, hbase]
    have hzd : z.regs d = x.regs total % radix w := by
      simp only [z, Data.set_regs, Function.update_of_ne hdt, Function.update_self, hbase]
    have hzb : z.regs base = radix w := by
      simp [z, Ne.symm hdb, base, total, hbase]
    obtain ⟨y, hey, hyb, hyv, hyfit, hym, hyp⟩ := ih
      (fun i hi => hout i (by simp [hi])) (List.nodup_cons.mp hnd).2 z hzb
      (by simpa only [hzq, hbase] using hq)
    have hyd : y.regs d = x.regs total % radix w :=
      (hyp d (List.nodup_cons.mp hnd).1 hdt).trans hzd
    have hp : ∀ i, i ∉ d :: ds → i ≠ total → y.regs i = x.regs i := by
      intro i hi ht
      rw [hyp i (fun hm => hi (by simp [hm])) ht]
      have hd : i ≠ d := by intro h; exact hi (by simp [h])
      simp only [z, Data.set_regs, Function.update_of_ne ht, Function.update_of_ne hd]
    refine ⟨y, ?_, ?_, ?_, hyfit, hym, hp⟩
    · unfold extract
      convert hez.seq hey using 1
      simp only [List.length_cons]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hyd]
        exact Nat.mod_lt _ (by have := one_lt_radix hw; omega)
      · exact hyb i hi
    · change y.regs d + radix w * value (radix w) y ds +
        radix w ^ (ds.length + 1) * y.regs total = x.regs total
      rw [hyd, pow_succ]
      rw [hzq] at hyv
      have hmod := Nat.mod_add_div (x.regs total) (radix w)
      nlinarith [congrArg (radix w * ·) hyv]

/-- Initialize the half-word radix and extract a scalar into fixed output registers. -/
def split (a : Fin (r + 4)) (ds : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq Workspace.setup (.seq (.op (.copy total a)) (extract ds))

/-- Conversion has a linear width-independent instruction count, including radix setup. -/
theorem size_split (a : Fin (r + 4)) (ds : List (Fin (r + 4))) :
    (split a ds).size = 2 * ds.length + 8 := by
  simp only [split, Code.size, Workspace.setup, size_extract]
  omega

/-- Exact conversion when the supplied digit list has enough capacity. The input may occur
among the outputs: its value is copied into workspace before any digit is written. -/
theorem exec_split {w : ℕ} (hw : 2 ≤ w) (a : Fin (r + 4))
    (ds : List (Fin (r + 4))) (ha : IsDigit a) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (x : Data (r + 4)) (hfit : Fits w (x.regs a))
    (hcap : x.regs a < radix w ^ ds.length) :
    ∃ y, Exec w (split a ds) x y (2 * ds.length + 8) ∧
      Bounded (radix w) y ds ∧ value (radix w) y ds = x.regs a ∧
      Frame x y (base :: zero :: ds) ∧
      ∀ i, IsDigit i → i ∉ ds → y.regs i = x.regs i := by
  let z := Workspace.setupResult w x
  let u := z.set total (z.regs a)
  have hua : u.regs total = x.regs a := by
    simp only [u, Data.set_regs, Function.update_self]
    exact Workspace.setup_digit w x ha
  have hub : u.regs base = radix w := by
    simp [u, z, Workspace.setupResult, base, total, zero]
  obtain ⟨y, hey, hyb, hyv, _, hym, hyp⟩ := exec_extract hw ds hout hnd u hub
    (by rwa [hua])
  rw [hua] at hyv
  have hyzero : y.regs total = 0 := by
    by_contra hn
    have hm := Nat.mul_le_mul_left (radix w ^ ds.length)
      (show 1 ≤ y.regs total by omega)
    simp only [mul_one] at hm
    omega
  have hp (i : Fin (r + 4)) (hi : IsDigit i) (hid : i ∉ ds) :
      y.regs i = x.regs i := by
    rw [hyp i hid (digit_ne hi).1]
    simp only [u, Data.set_regs, Function.update_of_ne (digit_ne hi).1]
    exact Workspace.setup_digit w x hi
  refine ⟨y, ?_, hyb, ?_, ⟨hym, ?_⟩, hp⟩
  · have hecopy : Exec w (.op (.copy (B := .standard) total a)) z u 1 := Exec.copy
    unfold split
    convert (Workspace.exec_setup hw x).seq (hecopy.seq hey) using 1
    omega
  · simpa only [hyzero, mul_zero, add_zero] using hyv
  · intro i hi ht hc
    have hb : i ≠ base := by intro h; exact hi (by simp [h])
    have hz : i ≠ zero := by intro h; exact hi (by simp [h])
    have hd : i ∉ ds := fun hm => hi (by simp [hm])
    rw [hyp i hd ht]
    simp only [u, z, Workspace.setupResult, Data.set_regs,
      Function.update_of_ne ht, Function.update_of_ne hc,
      Function.update_of_ne hb, Function.update_of_ne hz]

/-- Eighteen half-word digits suffice for every physical scalar at widths at least two,
including odd widths. This conversion always executes exactly 44 instructions. -/
theorem exec_split_eighteen {w : ℕ} (hw : 2 ≤ w) (a : Fin (r + 4))
    (ds : List (Fin (r + 4))) (hlen : ds.length = 18) (ha : IsDigit a)
    (hout : ∀ i ∈ ds, IsDigit i) (hnd : ds.Nodup)
    (x : Data (r + 4)) (hfit : Fits w (x.regs a)) :
    ∃ y, Exec w (split a ds) x y 44 ∧
      Bounded (radix w) y ds ∧ value (radix w) y ds = x.regs a ∧
      Frame x y (base :: zero :: ds) ∧
      ∀ i, IsDigit i → i ∉ ds → y.regs i = x.regs i := by
  have hpow : 2 ^ w ≤ radix w ^ ds.length := by
    rw [radix, ← pow_mul, hlen]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  simpa only [hlen] using exec_split hw a ds ha hout hnd x hfit (hfit.trans_le hpow)

end Cslib.WordRAM.Multiword.Transfer

end
