/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Callee
import Batteries.Data.Fin.Lemmas

/-!
# A finite exhaustive native Exact Triangle callee

This reference implementation enumerates the actual triples, loads all three encoded matrix
weights, and compares the sums of their positive and negative magnitudes. No solver instruction,
host execution premise or precomputed verdict occurs in its code. It is library code because its
certification witnesses that `Host.Callee` can be satisfied by a concrete finite program.

## Main definitions

* `program`: one fixed 24-register native triple scan.
* `callee`: a concrete certified finite block with charged cubic time and logarithmic width.

This exhaustive native implementation and its certification are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host.Slow

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Raw number of vertices per part. -/
abbrev side : Fin 24 := 0
/-- AB matrix pointer. -/
abbrev ab : Fin 24 := 2
/-- BC matrix pointer. -/
abbrev bc : Fin 24 := 3
/-- AC matrix pointer. -/
abbrev ac : Fin 24 := 4
/-- The free-pointer argument is overwritten by zero after entry. -/
abbrev zero : Fin 24 := 5
/-- Raw Boolean return value. -/
abbrev out : Fin 24 := 6
/-- Next flattened triple. -/
abbrev current : Fin 24 := 7
/-- Number of cells per matrix. -/
abbrev area : Fin 24 := 8
/-- Number of triples. -/
abbrev stop : Fin 24 := 9
/-- Loop increment. -/
abbrev one : Fin 24 := 10
/-- Sign-and-magnitude radix. -/
abbrev two : Fin 24 := 11
/-- First vertex index. -/
abbrev iReg : Fin 24 := 12
/-- Second vertex index. -/
abbrev jReg : Fin 24 := 13
/-- Third vertex index. -/
abbrev kReg : Fin 24 := 14
/-- Actual matrix-load address. -/
abbrev address : Fin 24 := 15
/-- The three actual loaded edge words. -/
def word (j : Fin 3) : Fin 24 := ⟨16 + j.val, by omega⟩
/-- Sum of positive magnitudes. -/
abbrev positive : Fin 24 := 19
/-- Sum of negative magnitudes. -/
abbrev negative : Fin 24 := 20
/-- Magnitude of the current encoded edge. -/
abbrev magnitude : Fin 24 := 21
/-- Sign bit of the current encoded edge. -/
abbrev sign : Fin 24 := 22
/-- Flattened second and third vertex indices. -/
abbrev remainder : Fin 24 := 23

private def positivePart (v : ℕ) : ℕ := if v % 2 = 0 then v / 2 else 0
private def negativePart (v : ℕ) : ℕ := if v % 2 = 0 then 0 else v / 2

private theorem zero_iff (a b c : ℕ) : decode a + decode b + decode c = 0 ↔
    positivePart a + positivePart b + positivePart c =
      negativePart a + negativePart b + negativePart c := by
  unfold decode positivePart negativePart
  split_ifs <;> omega

private theorem parts_le (v : ℕ) : positivePart v ≤ v / 2 ∧ negativePart v ≤ v / 2 := by
  unfold positivePart negativePart
  split_ifs <;> omega

/-- Add one encoded edge to its positive or negative magnitude sum. -/
def accumulate (j : Fin 3) : Code .standard 24 :=
  let v := word j
  ram[ magnitude ← v / two; sign ← v % two;
    if sign = zero then [ positive ← positive + magnitude ]
      else [ negative ← negative + magnitude ] ]

/-- Compute three indices and load the three corresponding matrix cells. -/
def loadTriple : Code .standard 24 :=
  let va := word 0
  let vb := word 1
  let vc := word 2
  ram[ iReg ← current / area; remainder ← current % area;
    jReg ← remainder / side; kReg ← remainder % side;
    address ← iReg * side; address ← address + jReg; address ← ab + address; va ← *address;
    address ← jReg * side; address ← address + kReg; address ← bc + address; vb ← *address;
    address ← iReg * side; address ← address + kReg; address ← ac + address; vc ← *address;
    positive ← #0; negative ← #0 ]

/-- Retain a found zero-weight triangle and advance to the next triple. -/
def finish : Code .standard 24 := ram[
  if positive = negative then [ out ← one ] else [ out ← out ];
  current ← current + one ]

/-- One fully charged triple scan. -/
def body : Code .standard 24 :=
  .seq loadTriple (.seq (accumulate 0) (.seq (accumulate 1) (.seq (accumulate 2) finish)))

/-- Initialize every scratch value used before the first triple. -/
def setup : Code .standard 24 := ram[
  current ← #0; area ← side * side; stop ← area * side;
  one ← #1; two ← #2; zero ← #0; out ← #0 ]

/-- Exhaust all `t³` triples using native division/remainder and actual matrix loads. -/
def program : Code .standard 24 := .seq setup (.loop (.lt current stop) body)

private def triangleAt {t : ℕ} (A B C : Fin t → Fin t → ℤ)
    (q : Fin (t * (t * t))) : Prop :=
  A q.divNat q.modNat.divNat + B q.modNat.divNat q.modNat.modNat +
    C q.divNat q.modNat.modNat = 0

private theorem exists_triangleAt {t : ℕ} (A B C : Fin t → Fin t → ℤ) :
    (∃ q, triangleAt A B C q) ↔ Cslib.Algorithms.ExactTriangle.HasZeroTriangle A B C := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.divNat, q.modNat.divNat, q.modNat.modNat, hq⟩
  · rintro ⟨i, j, k, h⟩
    refine ⟨Fin.mkDivMod i (Fin.mkDivMod j k), ?_⟩
    simpa only [triangleAt, Fin.divNat_mkDivMod, Fin.modNat_mkDivMod] using h

private theorem accumulate_preserves (j : Fin 3) :
    ∀ i : Fin 24, i.val < 19 → (accumulate j).Preserves i := by
  fin_cases j <;> decide

private theorem exec_accumulate {w v : ℕ} (j : Fin 3) (x : Data 24)
    (hv : x.regs (word j) = v) (h2 : x.regs two = 2) (h0 : x.regs zero = 0)
    (h2fit : Fits w 2) (hmag : Fits w (v / 2))
    (hp : Fits w (x.regs positive + v / 2))
    (hn : Fits w (x.regs negative + v / 2)) :
    ∃ y, ExecWithin w (accumulate j) x y 5 ∧
      y.regs positive = x.regs positive + positivePart v ∧
      y.regs negative = x.regs negative + negativePart v ∧ y.mem = x.mem := by
  have hsign : Fits w (v % 2) := h2fit.of_le (by omega)
  let a := x.set magnitude (v / 2) |>.set sign (v % 2)
  let y := if v % 2 = 0 then a.set positive (x.regs positive + v / 2)
    else a.set negative (x.regs negative + v / 2)
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · refine ⟨if v % 2 = 0 then 4 else 5, by split_ifs <;> decide, ?_⟩
    fin_cases j <;> norm_num [word] at hv
    all_goals by_cases h : v % 2 = 0 <;>
      ram_eval [accumulate, word, y, a, hv, h2, h0, hmag, hsign, hp, hn, h,
        positive, negative, magnitude, sign, two, zero, Fin.mk.injEq]
    all_goals simp +decide [hv, h2, h0, hmag, hsign, hp, hn, h]
  · by_cases h : v % 2 = 0 <;>
      simp +decide [y, a, h, positivePart, positive, negative, magnitude, sign]
  · by_cases h : v % 2 = 0 <;>
      simp +decide [y, a, h, negativePart, positive, negative, magnitude, sign]
  · by_cases h : v % 2 = 0 <;> simp [y, a, h]

private structure Control (t abp bcp acp : ℕ) (x : Data 24) : Prop where
  side : x.regs side = t
  ab : x.regs ab = abp
  bc : x.regs bc = bcp
  ac : x.regs ac = acp
  area : x.regs area = t * t
  stop : x.regs stop = t * (t * t)
  one : x.regs one = 1
  two : x.regs two = 2
  zero : x.regs zero = 0

private theorem Control.congr {t abp bcp acp : ℕ} {x y : Data 24}
    (h : Control t abp bcp acp x)
    (heq : ∀ i : Fin 24, i.val < 12 → i ≠ current → i ≠ out → y.regs i = x.regs i) :
    Control t abp bcp acp y := by
  constructor
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.side
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.ab
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.bc
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.ac
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.area
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.stop
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.one
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.two
  · exact (heq _ (by decide) (by decide) (by decide)).trans h.zero

private theorem load_preserves : ∀ i : Fin 24, i.val < 12 → loadTriple.Preserves i := by decide

private theorem exec_loadTriple {w t F abp bcp acp free v₀ v₁ v₂ : ℕ}
    (x : Data 24) (h : Control t abp bcp acp x) (q : Fin (t * (t * t)))
    (hq : x.regs current = q.val)
    (hbc : abp + t * t ≤ bcp) (hac : bcp + t * t ≤ acp) (hf : acp + t * t ≤ free)
    (hfit : Fits w (free + t * (t * t) + 6 * F + 10))
    (hv₀ : x.mem (abp + q.divNat.val * t + q.modNat.divNat.val) = v₀)
    (hv₁ : x.mem (bcp + q.modNat.divNat.val * t + q.modNat.modNat.val) = v₁)
    (hv₂ : x.mem (acp + q.divNat.val * t + q.modNat.modNat.val) = v₂) :
    ∃ y, ExecWithin w loadTriple x y 18 ∧ Control t abp bcp acp y ∧
      y.regs (word 0) = v₀ ∧ y.regs (word 1) = v₁ ∧ y.regs (word 2) = v₂ ∧
      y.regs positive = 0 ∧ y.regs negative = 0 ∧ y.mem = x.mem := by
  let i := q.divNat
  let j := q.modNat.divNat
  let k := q.modNat.modNat
  have hcell (a b : Fin t) : a.val * t + b.val < t * t := by
    simpa only [Fin.coe_mkDivMod, Nat.mul_comm] using (Fin.mkDivMod a b).isLt
  have hfree : Fits w free := hfit.of_le (by omega)
  have harea : t * t ≤ free := by omega
  have htfree : t ≤ free := (Nat.le_mul_self t).trans harea
  have hif : Fits w i.val := hfree.of_le (by have := i.isLt; omega)
  have hjf : Fits w j.val := hfree.of_le (by have := j.isLt; omega)
  have hkf : Fits w k.val := hfree.of_le (by have := k.isLt; omega)
  have hrf : Fits w q.modNat.val := hfree.of_le (by have := q.modNat.isLt; omega)
  have hip : Fits w (i.val * t) := hfree.of_le (by have := hcell i j; omega)
  have hjp : Fits w (j.val * t) := hfree.of_le (by have := hcell j k; omega)
  have hij : Fits w (i.val * t + j.val) := hfree.of_le (by have := hcell i j; omega)
  have hjk : Fits w (j.val * t + k.val) := hfree.of_le (by have := hcell j k; omega)
  have hik : Fits w (i.val * t + k.val) := hfree.of_le (by have := hcell i k; omega)
  have habf : Fits w (abp + (i.val * t + j.val)) :=
    hfree.of_le (by have := hcell i j; omega)
  have hbcf : Fits w (bcp + (j.val * t + k.val)) :=
    hfree.of_le (by have := hcell j k; omega)
  have hacf : Fits w (acp + (i.val * t + k.val)) :=
    hfree.of_le (by have := hcell i k; omega)
  simp only [i, j, k, Fin.coe_divNat, Fin.coe_modNat,
    Nat.add_assoc] at hif hjf hkf hrf hip hjp hij hjk hik habf hbcf hacf hv₀ hv₁ hv₂
  let y := x.set iReg i.val |>.set remainder q.modNat.val |>.set jReg j.val |>.set kReg k.val
    |>.set address (i.val * t) |>.set address (i.val * t + j.val)
    |>.set address (abp + (i.val * t + j.val)) |>.set (word 0) v₀
    |>.set address (j.val * t) |>.set address (j.val * t + k.val)
    |>.set address (bcp + (j.val * t + k.val)) |>.set (word 1) v₁
    |>.set address (i.val * t) |>.set address (i.val * t + k.val)
    |>.set address (acp + (i.val * t + k.val)) |>.set (word 2) v₂
    |>.set positive 0 |>.set negative 0
  have he : ExecWithin w loadTriple x y 18 := by
    ram_eval [loadTriple, word, y, h.side, h.area, h.ab, h.bc, h.ac, hq,
      hif, hjf, hkf, hrf, hip, hjp, hij, hjk, hik, habf, hbcf, hacf,
      hv₀, hv₁, hv₂, i, j, k, Fin.coe_divNat, Fin.coe_modNat, Nat.add_assoc,
      side, ab, bc, ac, current, area, iReg, jReg, kReg, remainder, address,
      positive, negative, Fin.mk.injEq, Fin.reduceFinMk, Fin.isValue]
  refine ⟨y, he, h.congr (fun a ha _ _ => he.regs_eq (load_preserves a ha)),
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals simp +decide [y, word, positive, negative, iReg, jReg, kReg, remainder, address]

private theorem magnitude_le {F : ℕ} {z : ℤ} (h : |z| ≤ (F : ℤ)) : encode z / 2 ≤ F := by
  rw [encode_div_two]
  have h' : (z.natAbs : ℤ) ≤ (F : ℤ) := by simpa only [Int.natCast_natAbs] using h
  exact_mod_cast h'

private theorem finish_preserves : ∀ i : Fin 24,
    i.val < 12 → i ≠ current → i ≠ out → finish.Preserves i := by decide

private theorem exec_finish {w q : ℕ} (x : Data 24)
    (ho : x.regs one = 1) (hq : x.regs current = q) (hinc : Fits w (q + 1)) :
    ∃ y, ExecWithin w finish x y 4 ∧ y.regs current = q + 1 ∧
      y.regs out = (if x.regs positive = x.regs negative then 1 else x.regs out) ∧
      y.mem = x.mem := by
  let b := if x.regs positive = x.regs negative then 1 else x.regs out
  let y := x.set out b |>.set current (q + 1)
  refine ⟨y, ?_, ?_, ?_, rfl⟩
  · by_cases h : x.regs positive = x.regs negative <;>
      ram_eval [finish, y, b, ho, hq, hinc, h, one, current, out, positive, negative, Fin.mk.injEq]
  · simp [y]
  · simp +decide [y, b, out, current]

private theorem exec_body {w t F abp bcp acp free : ℕ}
    (A B C : Fin t → Fin t → ℤ) (x : Data 24) (h : Control t abp bcp acp x)
    (q : Fin (t * (t * t))) (hq : x.regs current = q.val) (hbool : x.regs out ≤ 1)
    (hbc : abp + t * t ≤ bcp) (hac : bcp + t * t ≤ acp) (hf : acp + t * t ≤ free)
    (hfit : Fits w (free + t * (t * t) + 6 * F + 10))
    (hmA : ∀ i j, x.mem (abp + i.val * t + j.val) = encode (A i j))
    (hmB : ∀ i j, x.mem (bcp + i.val * t + j.val) = encode (B i j))
    (hmC : ∀ i j, x.mem (acp + i.val * t + j.val) = encode (C i j))
    (hA : ∀ i j, |A i j| ≤ (F : ℤ)) (hB : ∀ i j, |B i j| ≤ (F : ℤ))
    (hC : ∀ i j, |C i j| ≤ (F : ℤ)) :
    ∃ y, ExecWithin w body x y 37 ∧ Control t abp bcp acp y ∧
      y.regs current = q.val + 1 ∧ y.regs out ≤ 1 ∧
      (y.regs out = 1 ↔ x.regs out = 1 ∨ triangleAt A B C q) ∧ y.mem = x.mem := by
  let za := A q.divNat q.modNat.divNat
  let zb := B q.modNat.divNat q.modNat.modNat
  let zc := C q.divNat q.modNat.modNat
  have hva : encode za / 2 ≤ F := magnitude_le (hA _ _)
  have hvb : encode zb / 2 ≤ F := magnitude_le (hB _ _)
  have hvc : encode zc / 2 ≤ F := magnitude_le (hC _ _)
  have h2fit : Fits w 2 := hfit.of_le (by omega)
  have hsum : Fits w (3 * F) := hfit.of_le (by omega)
  obtain ⟨a, ha, hpa, ha₀, ha₁, ha₂, hap, han, ham⟩ :=
    exec_loadTriple (v₀ := encode za) (v₁ := encode zb) (v₂ := encode zc) x h q hq
      hbc hac hf hfit (hmA _ _) (hmB _ _) (hmC _ _)
  obtain ⟨b, hb, hbp, hbn, hbm⟩ := exec_accumulate 0 a ha₀ hpa.two hpa.zero h2fit
    (hsum.of_le (by omega)) (hsum.of_le (by rw [hap]; omega))
    (hsum.of_le (by rw [han]; omega))
  have hpb : Control t abp bcp acp b :=
    hpa.congr (fun i hi _ _ => hb.regs_eq (accumulate_preserves 0 i (by omega)))
  have hbpF : b.regs positive ≤ F := by
    rw [hbp, hap, Nat.zero_add]
    exact (parts_le _).1.trans hva
  have hbnF : b.regs negative ≤ F := by
    rw [hbn, han, Nat.zero_add]
    exact (parts_le _).2.trans hva
  have hb₁ : b.regs (word 1) = encode zb :=
    (hb.regs_eq (accumulate_preserves 0 _ (by decide))).trans ha₁
  obtain ⟨c, hc, hcp, hcn, hcm⟩ := exec_accumulate 1 b hb₁ hpb.two hpb.zero h2fit
    (hsum.of_le (by omega)) (hsum.of_le (by omega)) (hsum.of_le (by omega))
  have hpc : Control t abp bcp acp c :=
    hpb.congr (fun i hi _ _ => hc.regs_eq (accumulate_preserves 1 i (by omega)))
  have hcpF : c.regs positive ≤ 2 * F := by
    rw [hcp]
    have := (parts_le (encode zb)).1
    omega
  have hcnF : c.regs negative ≤ 2 * F := by
    rw [hcn]
    have := (parts_le (encode zb)).2
    omega
  have hc₂ : c.regs (word 2) = encode zc :=
    (hc.regs_eq (accumulate_preserves 1 _ (by decide))).trans
      ((hb.regs_eq (accumulate_preserves 0 _ (by decide))).trans ha₂)
  obtain ⟨d, hd, hdp, hdn, hdm⟩ := exec_accumulate 2 c hc₂ hpc.two hpc.zero h2fit
    (hsum.of_le (by omega)) (hsum.of_le (by omega)) (hsum.of_le (by omega))
  have hpd : Control t abp bcp acp d :=
    hpc.congr (fun i hi _ _ => hd.regs_eq (accumulate_preserves 2 i (by omega)))
  have hkeep (i : Fin 24) (hi : i.val < 12) : d.regs i = x.regs i :=
    (hd.regs_eq (accumulate_preserves 2 i (by omega))).trans
      ((hc.regs_eq (accumulate_preserves 1 i (by omega))).trans
        ((hb.regs_eq (accumulate_preserves 0 i (by omega))).trans
          (ha.regs_eq (load_preserves i hi))))
  have hhit : d.regs positive = d.regs negative ↔ triangleAt A B C q := by
    rw [hdp, hcp, hbp, hap, hdn, hcn, hbn, han]
    simp only [Nat.zero_add]
    simpa only [decode_encode, za, zb, zc, triangleAt] using
      (zero_iff (encode za) (encode zb) (encode zc)).symm
  obtain ⟨y, hy, hyq, hyo, hym⟩ := exec_finish d hpd.one
    ((hkeep current (by decide)).trans hq) (hfit.of_le (by have := q.isLt; omega))
  refine ⟨y, (ha.seq (hb.seq (hc.seq (hd.seq hy)))).mono (by decide),
    hpd.congr (fun i hi hq ho => hy.regs_eq (finish_preserves i hi hq ho)), hyq, ?_, ?_, ?_⟩
  · rw [hyo, hkeep out (by decide)]
    split_ifs <;> omega
  · rw [hyo, hkeep out (by decide)]
    by_cases hz : d.regs positive = d.regs negative
    · simp only [hz, ↓reduceIte, hhit.mp hz, or_true]
    · simp only [hz, ↓reduceIte, hhit.not.mp hz, or_false]
  · exact hym.trans (hdm.trans (hcm.trans (hbm.trans ham)))

private theorem exec_scan {w t F abp bcp acp free : ℕ}
    (A B C : Fin t → Fin t → ℤ) (x : Data 24)
    (ht : x.regs side = t) (hab : x.regs ab = abp)
    (hbc : x.regs bc = bcp) (hac : x.regs ac = acp)
    (hABBC : abp + t * t ≤ bcp) (hBCAC : bcp + t * t ≤ acp)
    (hfree : acp + t * t ≤ free)
    (hfit : Fits w (free + t * (t * t) + 6 * F + 10))
    (hmA : ∀ i j, x.mem (abp + i.val * t + j.val) = encode (A i j))
    (hmB : ∀ i j, x.mem (bcp + i.val * t + j.val) = encode (B i j))
    (hmC : ∀ i j, x.mem (acp + i.val * t + j.val) = encode (C i j))
    (hA : ∀ i j, |A i j| ≤ (F : ℤ)) (hB : ∀ i j, |B i j| ≤ (F : ℤ))
    (hC : ∀ i j, |C i j| ≤ (F : ℤ)) :
    ∃ y, ExecWithin w program x y (39 * (t * (t * t)) + 9) ∧ y.regs out ≤ 1 ∧
      (y.regs out = 1 ↔ Cslib.Algorithms.ExactTriangle.HasZeroTriangle A B C) ∧
      y.mem = x.mem := by
  have h2 : Fits w 2 := hfit.of_le (by omega)
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have harea : Fits w (t * t) := hfit.of_le (by omega)
  have hstop : Fits w ((t * t) * t) := hfit.of_le (by rw [Nat.mul_assoc]; omega)
  rw [Nat.mul_assoc] at hstop
  let a := x.set current 0 |>.set area (t * t) |>.set stop (t * (t * t))
    |>.set one 1 |>.set two 2 |>.set zero 0 |>.set out 0
  have ha : ExecWithin w setup x a 7 := by
    ram_eval [setup, a, ht, harea, hstop, h1, h2, side, current, area, stop,
      one, two, zero, out, Nat.mul_assoc, Fin.mk.injEq]
  have hpa : Control t abp bcp acp a := by
    constructor <;> simp +decide [a, side, ab, bc, ac, current, area, stop,
      one, two, zero, out, ht, hab, hbc, hac]
  let I (y : Data 24) : Prop := Control t abp bcp acp y ∧
    y.regs current ≤ t * (t * t) ∧ y.regs out ≤ 1 ∧
    (y.regs out = 1 ↔ ∃ q : Fin (t * (t * t)), q.val < y.regs current ∧ triangleAt A B C q) ∧
    y.mem = x.mem
  have hbody (y : Data 24) (hy : I y) (hc : (Cond.lt current stop).Holds y) :
      ∃ z, ExecWithin w body y z 37 ∧ I z ∧
        t * (t * t) - z.regs current < t * (t * t) - y.regs current := by
    obtain ⟨hyp, hyq, hyb, hyo, hym⟩ := hy
    have hlt : y.regs current < t * (t * t) := by
      change y.regs current < y.regs stop at hc
      exact hc.trans_eq hyp.stop
    let q : Fin (t * (t * t)) := ⟨y.regs current, hlt⟩
    obtain ⟨z, hz, hzp, hzq, hzb, hzo, hzm⟩ := exec_body A B C y hyp q rfl hyb
      hABBC hBCAC hfree hfit (by simpa only [hym] using hmA)
      (by simpa only [hym] using hmB) (by simpa only [hym] using hmC) hA hB hC
    refine ⟨z, hz, ⟨hzp, by dsimp only [q] at hzq; omega, hzb, ?_, hzm.trans hym⟩, ?_⟩
    · rw [hzo, hyo, hzq]
      constructor
      · rintro (⟨p, hp, hh⟩ | hh)
        · exact ⟨p, by dsimp only [q]; omega, hh⟩
        · exact ⟨q, by omega, hh⟩
      · rintro ⟨p, hp, hh⟩
        by_cases h : p.val < y.regs current
        · exact Or.inl ⟨p, h, hh⟩
        · have heq : p = q := Fin.ext (by dsimp only [q] at *; omega)
          exact Or.inr (heq ▸ hh)
    · dsimp only [q] at hzq
      omega
  have hx : I a := by
    refine ⟨hpa, ?_, ?_, ?_, rfl⟩
    · simp +decide [a, current, area, stop, one, two, zero, out]
    · simp +decide [a, current, area, stop, one, two, zero, out]
    · simp +decide [a, current, area, stop, one, two, zero, out]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => t * (t * t) - y.regs current) hbody hx
  obtain ⟨hyp, hyq, hyb, hyo, hym⟩ := hy
  have hend : y.regs current = t * (t * t) := by
    change ¬y.regs current < y.regs stop at hc
    have := hyp.stop
    omega
  refine ⟨y, (ha.seq he).mono ?_, hyb, ?_, hym⟩
  · simp +decide only [a, Data.set_regs, Function.update_apply, current, area, stop,
      one, two, zero, out, ↓reduceIte, Nat.sub_zero, Nat.reduceAdd]
    omega
  · refine (hyo.trans ?_).trans (exists_triangleAt A B C)
    constructor
    · rintro ⟨q, _, hq⟩
      exact ⟨q, hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, by rw [hend]; exact q.isLt, hq⟩

private theorem fits_budget {w t F abp bcp acp free : ℕ}
    (ht : 0 < t) (hF : 0 < F)
    (hABBC : abp + t * t ≤ bcp) (hBCAC : bcp + t * t ≤ acp)
    (hfree : acp + t * t ≤ free)
    (hw : 8 * Nat.clog 2 (free + F + t + 2) ≤ w) :
    Fits w (free + t * (t * t) + 6 * F + 10) := by
  let S := free + F + t + 2
  have htt : 0 < t * t := Nat.mul_pos ht ht
  have hs : 7 ≤ S := by dsimp only [S]; omega
  have hts : t ≤ S := by dsimp only [S]; omega
  have hfs : free ≤ S := by dsimp only [S]; omega
  have hFs : F ≤ S := by dsimp only [S]; omega
  have hs3 : S ≤ S ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ S by omega)
      (show 1 ≤ 3 by decide)
  have ht3 : t * (t * t) ≤ S ^ 3 := by
    simpa only [pow_succ, pow_zero, one_mul, Nat.mul_assoc] using Nat.pow_le_pow_left hts 3
  have hf3 := hfs.trans hs3
  have hF3 := hFs.trans hs3
  have h10 : 10 ≤ S ^ 3 := (by decide : 10 ≤ 7 ^ 3).trans (Nat.pow_le_pow_left hs 3)
  have h9 : 9 ≤ S ^ 2 := (by decide : 9 ≤ 7 ^ 2).trans (Nat.pow_le_pow_left hs 2)
  have hbound : free + t * (t * t) + 6 * F + 10 < S ^ 6 := by
    calc _ ≤ 9 * S ^ 3 := by omega
      _ ≤ S ^ 2 * S ^ 3 := Nat.mul_le_mul_right _ h9
      _ = S ^ 5 := by ring
      _ < S ^ 6 := Nat.pow_lt_pow_right (by omega) (by decide)
  apply hbound.trans_le
  calc S ^ 6 ≤ (2 ^ Nat.clog 2 S) ^ 6 :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) S) 6
    _ = 2 ^ (6 * Nat.clog 2 S) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by change 8 * Nat.clog 2 S ≤ w at hw; omega)

/-- Actual finite cubic-time solver used to inhabit the complete host's callee contract.
It preserves all memory, works on arbitrary signed matrices, and never reads physical width. -/
def callee : Callee 17 where
  code := program
  time t _ := 40 * (t * (t * t)) + 16
  widthCoefficient := 8
  coefficient_pos := by decide
  not_readsWidth := by decide
  exec := by
    intro w t F abp bcp acp free x A B C ht hF hABBC hBCAC hfree hw
      hside _ hab hbc hac _ hmA hmB hmC hA hB hC
    have hfit := fits_budget ht hF hABBC hBCAC hfree hw
    obtain ⟨y, he, hb, hans, hm⟩ := exec_scan A B C x hside hab hbc hac
      hABBC hBCAC hfree hfit hmA hmB hmC hA hB hC
    exact ⟨y, he.mono (by omega), hb, hans, fun a _ => congrFun hm a⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Host.Slow
