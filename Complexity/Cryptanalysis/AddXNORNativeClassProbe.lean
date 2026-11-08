/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeProbe

/-!
# Termination and completeness of the native opposite-class iterator

The existing streaming iterator of [WangLvShenZhang2027], Lemma 8/Theorem 7,
PDF pp. 21–22, visits packed middle-quarter words in increasing order and scans
only their computed buckets. A hit exits with the current witness; exhaustion
certifies that every admissible word and every record in its bucket missed.
These component contracts distinguish the physical dictionary lookup predicate
from the construction and original-chain interpretation of the stored witnesses.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- The actual projected forward query for a packed third-quarter word. -/
def classQuery {m p : ℕ} (as : List (BitVec m)) (g : BitVec p) (v : ℕ) : BitVec p :=
  eval ((decode as.length v).zip (as.map (BitVec.setWidth p))) g

/-- A physical dictionary hit in one of the computed bucket's records. -/
def ClassHit {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (mem : ℕ → ℕ) (D v : ℕ) : Prop :=
  ∃ r ∈ rs (classQuery as g v), mem (Dictionary.slot D
    (backward ((decode as.length v).zip as) (BitVec.ofNat m r.1)).toNat) ≠ 0

/-- Exact behavior of one existing native class iteration, including early exit. -/
theorem probeClassBody_exec {W m p b q h D boundary L v : ℕ}
    (as : List (BitVec m)) (g : BitVec p) (rs : BitVec p → List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs fullBase = b) (hq : x.regs projectedBase = q)
    (hm : x.regs fullModulus = 2 ^ m) (hp : x.regs projectedModulus = 2 ^ p)
    (hc : x.regs count = as.length) (hg : x.regs initial = g.toNat)
    (hh : x.regs heads = h) (hd : x.regs Dictionary.table = D)
    (hv : x.regs operators = v) (hs : x.regs stop = L)
    (hz : x.regs zero = 0) (hvL : v < L)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hproject : ∀ i (hi : i < (as.map (BitVec.setWidth p)).length),
      x.mem (q + i) = (as.map (BitVec.setWidth p))[i].toNat)
    (hlinked : ∀ k, Linked x.mem boundary (x.mem (h + k.toNat)) (rs k))
    (hstates : ∀ k, ∀ r ∈ rs k, r.1 < 2 ^ m)
    (hfit : Fits W (D + boundary + h + q + b + as.length + 8 * 2 ^ m +
      2 * 2 ^ p + 2 ^ as.length + L + 8)) :
    ∃ y, ExecWithin W probeClassBody x y
        ((rs (classQuery as g v)).length * (18 * as.length + 39) + 11 * as.length + 20) ∧
      y.mem = x.mem ∧ y.regs one = 1 ∧
      (y.regs operand ≠ 0 ↔ ClassHit as g rs x.mem D v) ∧
      (y.regs operand = 0 → y.regs operators = v + 1 ∧ y.regs stop = L) ∧
      (y.regs operand ≠ 0 → y.regs operators = v ∧ y.regs stop = v ∧
        ∃ r ∈ rs (classQuery as g v), y.regs firstOperators = r.2 ∧
          y.regs state = (backward ((decode as.length v).zip as)
            (BitVec.ofNat m r.1)).toNat ∧
          y.regs operand = x.mem (Dictionary.slot D (y.regs state)) ∧
          y.regs bits = x.mem (Dictionary.slot D (y.regs state) + 1)) := by
  have hN := Nat.two_pow_pos as.length
  let low := x.set base q |>.set modulus (2 ^ p) |>.set state g.toNat
  have setup : ExecWithin (B := .standard) W
      (ram[ base ← projectedBase; modulus ← projectedModulus; state ← initial ]) x low 3 := by
    ram_eval [low, hq, hp, hg, base, projectedBase, modulus, projectedModulus, state, initial,
      Fin.mk.injEq]
  obtain ⟨z, he, zs, _, _, zm, zone, _⟩ := evaluate_exec (b := q) (v := v)
    (as.map (BitVec.setWidth p)) g low
    (by simp +decide [low, base, modulus, state])
    (by simpa +decide [low, count, base, modulus, state, List.length_map] using hc)
    (by simp +decide [low, modulus, state]) (by simp [low])
    (by simpa +decide [low, operators, base, modulus, state] using hv)
    (hfit.of_le (by omega)) (by simpa only [low, Data.set_mem] using hproject)
    (hfit.of_le (by simp only [List.length_map]; omega))
  have ez := setup.seq he
  have frame (r : Fin 32) (hr : (Code.seq (B := .standard)
      (ram[ base ← projectedBase; modulus ← projectedModulus; state ← initial ])
      evaluate).Preserves r) : z.regs r = x.regs r := ez.regs_eq hr
  let k := classQuery as g v
  have zk : z.regs state = k.toNat := by simpa only [k, classQuery, List.length_map] using zs
  have zmem : z.mem = x.mem := by simpa only [low, Data.set_mem] using zm
  have ha : Fits W (h + k.toNat) := hfit.of_le (by have := k.isLt; omega)
  let ready := z.set address (h + k.toNat) |>.set link (x.mem (h + k.toNat))
    |>.set base b |>.set modulus (2 ^ m) |>.set operand 0
  have transfer : ExecWithin (B := .standard) W
      (ram[ address ← heads + state; link ← *address;
        base ← fullBase; modulus ← fullModulus; operand ← #0 ]) z ready 5 := by
    have zh : z.regs heads = h := (frame heads (by decide)).trans hh
    have zb : z.regs fullBase = b := (frame fullBase (by decide)).trans hb
    have zn : z.regs fullModulus = 2 ^ m := (frame fullModulus (by decide)).trans hm
    ram_eval [ready, zh, zk, zmem, zb, zn, ha, fits_zero, address, heads, state, link,
      base, fullBase, modulus, fullModulus, operand, Fin.mk.injEq]
  have et := ez.seq transfer
  obtain ⟨u, hu, um, _, uone, uops, uh, uw⟩ := probeScan_witness_exec
    (W := W) (b := b) (D := D) (boundary := boundary) (v := v)
    (ptr := x.mem (h + k.toNat)) as (rs k) ready
    (by simp +decide [ready, base, modulus, operand])
    ((et.regs_eq (by decide)).trans hc) (by simp +decide [ready, modulus, operand])
    ((et.regs_eq (by decide)).trans hv) (hfit.of_le (by omega))
    (by simp +decide [ready, link, base, modulus, operand])
    ((et.regs_eq (by decide)).trans hd) (by
      rw [transfer.regs_eq (by decide)]; exact zone)
    ((et.regs_eq (by decide)).trans hz) (by simp [ready])
    (by simpa only [ready, Data.set_mem, zmem] using hlinked k)
    (hstates k) (by simpa only [ready, Data.set_mem, zmem] using hinput)
    (hfit.of_le (by omega))
  have umem : u.mem = x.mem := by simpa only [ready, Data.set_mem, zmem] using um
  have uzero : u.regs zero = 0 := ((et.seq hu).regs_eq (by decide)).trans hz
  have ust : u.regs stop = L := ((et.seq hu).regs_eq (by decide)).trans hs
  by_cases hit : u.regs operand = 0
  · let y := u.set operators (v + 1)
    have step : ExecWithin (B := .standard) W (ram[ operators ← operators + one ]) u y 1 := by
      ram_eval [y, uops, uone, hfit.of_le (show v + 1 ≤ _ by omega), operators, one,
        Fin.mk.injEq]
    have branch : ExecWithin (B := .standard) W
        (.branch (.eq operand zero) (ram[ operators ← operators + one ])
          (ram[ stop ← operators ])) u y 3 :=
      (ExecWithin.branch_pos (by simp [Cond.holds_eq, hit, uzero]) step).mono (by omega)
    refine ⟨y, ?_, umem, ?_, ?_, ?_, ?_⟩
    · exact (setup.seq (he.seq (transfer.seq (hu.seq branch)))).mono (by
        simp only [List.length_map, k]; omega)
    · simpa +decide [y, one, operators] using uone
    · simpa +decide [y, operand, operators, umem, ready, zmem, ClassHit, k] using uh
    · intro _; exact ⟨by simp [y], by simpa +decide [y, stop, operators] using ust⟩
    · intro h; exact (h (by simpa +decide [y, operand, operators] using hit)).elim
  · let y := u.set stop v
    have step : ExecWithin (B := .standard) W (ram[ stop ← operators ]) u y 1 := by
      simpa only [y, uops] using (ExecWithin.copy (B := .standard) (w := W)
        (x := u) (d := stop) (s := operators))
    have branch : ExecWithin (B := .standard) W
        (.branch (.eq operand zero) (ram[ operators ← operators + one ])
          (ram[ stop ← operators ])) u y 3 :=
      ExecWithin.branch_neg (by simpa only [Cond.holds_eq, uzero] using hit) step
    refine ⟨y, ?_, umem, ?_, ?_, ?_, ?_⟩
    · exact (setup.seq (he.seq (transfer.seq (hu.seq branch)))).mono (by
        simp only [List.length_map, k]; omega)
    · simpa +decide [y, one, stop] using uone
    · simpa +decide [y, operand, stop, umem, ready, zmem, ClassHit, k] using uh
    · intro h; exact (hit (by simpa +decide [y, operand, stop] using h)).elim
    · intro _
      obtain ⟨r, hr, ur, uv, us, ut, ub⟩ := uw hit
      refine ⟨?_, by simp [y], r, hr, ?_, ?_, ?_, ?_⟩
      · simpa +decide [y, operators, stop] using uv
      · simpa +decide [y, firstOperators, stop] using ur
      · simpa +decide [y, state, stop] using us
      · simpa +decide [y, operand, state, stop, ready, zmem] using ut
      · simpa +decide [y, bits, state, stop, ready, zmem] using ub

/-- Instruction budget for a suffix of the actual packed-index stream.
Only proof-observed bucket lengths enter this budget, never machine inputs. -/
def classProbeTime {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j : ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => (rs (classQuery as g j)).length * (18 * as.length + 39) +
      11 * as.length + 20 + classProbeTime as g rs (j + 1) n + 2

/-- Number of indexed records in a finite suffix of the native opposite stream. -/
def classProbeHits {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (rs (classQuery as g j)).length + classProbeHits as g rs (j + 1) n

/-- The full-stream budget charges actual bucket hits, not a materialized list
of every possible opposite pair. Early exits use at most this budget. -/
theorem classProbeTime_eq {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j n : ℕ) :
    classProbeTime as g rs j n = classProbeHits as g rs j n * (18 * as.length + 39) +
      n * (11 * as.length + 22) + 2 := by
  induction n generalizing j with
  | zero => simp [classProbeTime, classProbeHits]
  | succ n ih =>
    simp only [classProbeTime, classProbeHits, ih, Nat.add_mul, Nat.succ_mul]
    ring

private theorem classProbeTime_ge {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j n : ℕ) : 2 ≤ classProbeTime as g rs j n := by
  cases n <;> simp only [classProbeTime] <;> omega

/-- General termination and exact coverage of a finite suffix of the existing
native loop. The remaining index count decreases after a miss; a hit makes the
loop condition false immediately, preserving all witness registers. -/
theorem probeClassLoop_exec {W m p b q h D boundary j n : ℕ}
    (as : List (BitVec m)) (g : BitVec p) (rs : BitVec p → List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs fullBase = b) (hq : x.regs projectedBase = q)
    (hm : x.regs fullModulus = 2 ^ m) (hp : x.regs projectedModulus = 2 ^ p)
    (hc : x.regs count = as.length) (hg : x.regs initial = g.toNat)
    (hh : x.regs heads = h) (hd : x.regs Dictionary.table = D)
    (hv : x.regs operators = j) (hs : x.regs stop = j + n)
    (hz : x.regs zero = 0) (htag : x.regs operand = 0)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hproject : ∀ i (hi : i < (as.map (BitVec.setWidth p)).length),
      x.mem (q + i) = (as.map (BitVec.setWidth p))[i].toNat)
    (hlinked : ∀ k, Linked x.mem boundary (x.mem (h + k.toNat)) (rs k))
    (hstates : ∀ k, ∀ r ∈ rs k, r.1 < 2 ^ m)
    (hfit : Fits W (D + boundary + h + q + b + as.length + 8 * 2 ^ m +
      2 * 2 ^ p + 2 ^ as.length + (j + n) + 8)) :
    ∃ y, ExecWithin W (.loop (.lt operators stop) probeClassBody) x y
        (classProbeTime as g rs j n) ∧ y.mem = x.mem ∧
      (y.regs operand ≠ 0 ↔ ∃ v, j ≤ v ∧ v < j + n ∧ ClassHit as g rs x.mem D v) ∧
      (y.regs operand = 0 → y.regs operators = j + n ∧ y.regs stop = j + n) ∧
      (y.regs operand ≠ 0 → j ≤ y.regs operators ∧ y.regs operators < j + n ∧
        y.regs stop = y.regs operators ∧
        ∃ r ∈ rs (classQuery as g (y.regs operators)), y.regs firstOperators = r.2 ∧
          y.regs state = (backward ((decode as.length (y.regs operators)).zip as)
            (BitVec.ofNat m r.1)).toNat ∧
          y.regs operand = x.mem (Dictionary.slot D (y.regs state)) ∧
          y.regs bits = x.mem (Dictionary.slot D (y.regs state) + 1)) := by
  induction n generalizing j x with
  | zero =>
    refine ⟨x, ?_, rfl, ?_, ?_, ?_⟩
    · exact ExecWithin.loop_exit (by simp [Cond.holds_lt, hv, hs])
    · simp only [htag, ne_eq, not_true_eq_false, Nat.add_zero, false_iff]
      rintro ⟨v, hv, hv', _⟩; omega
    · intro _; exact ⟨by simpa only [Nat.add_zero] using hv, hs⟩
    · intro h; exact (h htag).elim
  | succ n ih =>
    obtain ⟨z, he, zm, zo, zh, zn, zw⟩ := probeClassBody_exec as g rs x hb hq hm hp
      hc hg hh hd hv hs hz (by omega) hinput hproject hlinked hstates hfit
    by_cases hit : z.regs operand = 0
    · obtain ⟨zv, zs⟩ := zn hit
      obtain ⟨y, hy, ym, yh, yn, yw⟩ := ih (j := j + 1) z
        ((he.regs_eq (by decide)).trans hb) ((he.regs_eq (by decide)).trans hq)
        ((he.regs_eq (by decide)).trans hm) ((he.regs_eq (by decide)).trans hp)
        ((he.regs_eq (by decide)).trans hc) ((he.regs_eq (by decide)).trans hg)
        ((he.regs_eq (by decide)).trans hh) ((he.regs_eq (by decide)).trans hd) zv
        (by omega) ((he.regs_eq (by decide)).trans hz) hit
        (by simpa only [zm] using hinput) (by simpa only [zm] using hproject)
        (by simpa only [zm] using hlinked)
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hfit)
      refine ⟨y, ?_, ym.trans zm, ?_, ?_, ?_⟩
      · exact (ExecWithin.loop_iter (by simp only [Cond.holds_lt, hv, hs]; omega) he hy).mono
          (by simp only [classProbeTime]; omega)
      · rw [yh]
        simp only [zm]
        have miss : ¬ClassHit as g rs x.mem D j := fun h => (zh.mpr h) hit
        constructor
        · rintro ⟨v, hv, hv', hh⟩; exact ⟨v, by omega, by omega, hh⟩
        · rintro ⟨v, hv, hv', hh⟩
          have : v ≠ j := by intro h; subst v; exact miss hh
          exact ⟨v, by omega, by omega, hh⟩
      · intro h
        obtain ⟨hv', hs'⟩ := yn h
        constructor <;> omega
      · intro h
        obtain ⟨hv', hv'', hs', r, hr, hu, ht, hp, hb⟩ := yw h
        refine ⟨by omega, by omega, hs', r, hr, hu, ht, ?_, ?_⟩
        · simpa only [zm] using hp
        · simpa only [zm] using hb
    · obtain ⟨zv, zs, r, hr, zu, zt, zp, zb⟩ := zw hit
      refine ⟨z, ?_, zm, ?_, ?_, ?_⟩
      · exact (ExecWithin.loop_once (by simp only [Cond.holds_lt, hv, hs]; omega) he
          (by simp [Cond.holds_lt, zv, zs])).mono
          (by have := classProbeTime_ge as g rs (j + 1) n; simp only [classProbeTime]; omega)
      · exact ⟨fun _ => ⟨j, le_rfl, by omega, zh.mp hit⟩, fun _ => hit⟩
      · intro h; exact (hit h).elim
      · intro _
        refine ⟨by omega, by omega, by omega, r, ?_, zu, ?_, zp, zb⟩
        · simpa only [zv] using hr
        · simpa only [zv] using zt

/-- All admissible packed middle-quarter indices are visited unless a valid
physical dictionary hit exits early. A zero tag certifies absence for the entire
stream, including empty buckets and coincident records. -/
theorem probeClass_exec {W m p b q h D boundary : ℕ}
    (as : List (BitVec m)) (g : BitVec p) (rs : BitVec p → List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs fullBase = b) (hq : x.regs projectedBase = q)
    (hm : x.regs fullModulus = 2 ^ m) (hp : x.regs projectedModulus = 2 ^ p)
    (hc : x.regs count = as.length) (hg : x.regs initial = g.toNat)
    (hh : x.regs heads = h) (hd : x.regs Dictionary.table = D)
    (hs : x.regs stop = 2 ^ as.length)
    (hinput : ∀ i (hi : i < as.reverse.length), x.mem (b + i) = as.reverse[i].toNat)
    (hproject : ∀ i (hi : i < (as.map (BitVec.setWidth p)).length),
      x.mem (q + i) = (as.map (BitVec.setWidth p))[i].toNat)
    (hlinked : ∀ k, Linked x.mem boundary (x.mem (h + k.toNat)) (rs k))
    (hstates : ∀ k, ∀ r ∈ rs k, r.1 < 2 ^ m)
    (hfit : Fits W (D + boundary + h + q + b + as.length + 8 * 2 ^ m +
      2 * 2 ^ p + 2 ^ as.length + 2 ^ as.length + 8)) :
    ∃ y, ExecWithin W probeClass x y (4 + classProbeTime as g rs 0 (2 ^ as.length)) ∧
      y.mem = x.mem ∧
      (y.regs operand ≠ 0 ↔ ∃ v < 2 ^ as.length, ClassHit as g rs x.mem D v) ∧
      (y.regs operand = 0 → y.regs operators = 2 ^ as.length ∧
        y.regs stop = 2 ^ as.length) ∧
      (y.regs operand ≠ 0 → y.regs operators < 2 ^ as.length ∧
        y.regs stop = y.regs operators ∧
        ∃ r ∈ rs (classQuery as g (y.regs operators)), y.regs firstOperators = r.2 ∧
          y.regs state = (backward ((decode as.length (y.regs operators)).zip as)
            (BitVec.ofNat m r.1)).toNat ∧
          y.regs operand = x.mem (Dictionary.slot D (y.regs state)) ∧
          y.regs bits = x.mem (Dictionary.slot D (y.regs state) + 1)) := by
  let start := x.set operators 0 |>.set operand 0 |>.set zero 0 |>.set one 1
  have setup : ExecWithin (B := .standard) W
      (ram[ operators ← #0; operand ← #0; zero ← #0; one ← #1 ]) x start 4 := by
    have h0 : Fits W 0 := fits_zero _
    have h1 : Fits W 1 := hfit.of_le (by have := Nat.two_pow_pos as.length; omega)
    ram_eval [start, h0, h1, operators, operand, zero, one, Fin.mk.injEq]
  obtain ⟨y, hy, ym, yh, yn, yw⟩ := probeClassLoop_exec (j := 0) (n := 2 ^ as.length)
    as g rs start
    ((setup.regs_eq (by decide)).trans hb) ((setup.regs_eq (by decide)).trans hq)
    ((setup.regs_eq (by decide)).trans hm) ((setup.regs_eq (by decide)).trans hp)
    ((setup.regs_eq (by decide)).trans hc) ((setup.regs_eq (by decide)).trans hg)
    ((setup.regs_eq (by decide)).trans hh) ((setup.regs_eq (by decide)).trans hd)
    (by simp +decide [start, operators, operand, zero, one])
    (by simpa only [Nat.zero_add] using (setup.regs_eq (by decide)).trans hs)
    (by simp +decide [start, zero, one])
    (by simp +decide [start, operand, zero, one]) hinput hproject hlinked hstates
    (by simpa only [Nat.zero_add] using hfit)
  refine ⟨y, setup.seq hy, ym, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add, Nat.zero_le, true_and, start, Data.set_mem] using yh
  · simpa only [Nat.zero_add] using yn
  · intro hit
    simpa only [Nat.zero_add, start, Data.set_mem] using (yw hit).2

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
