/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeProbe
public import Complexity.Cryptanalysis.AddXNORNativeDictionaryComplete
import all Complexity.Cryptanalysis.AddXNORNativeRetain

/-!
# Native construction of an entire retained low-bit class

Enumerate every packed second-quarter index, compute its inverse projected query,
consume the actual first-quarter bucket, and retain each full-state witness.
The dictionary insertion stream, release chain and finite execution are conclusions
of the native stores. These are components of [WangLvShenZhang2027], Lemma 8
and Theorem 7, PDF pp. 21–22, in the sparse word-RAM model.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Retained-side inverse projected query. -/
def retainQuery {m p : ℕ} (as : List (BitVec m)) (g : BitVec p) (v : ℕ) : BitVec p :=
  backward ((decode as.length v).zip (as.map (BitVec.setWidth p))) g

/-- One actual inverse query and direct full-state retention, without an output array. -/
@[expose] def retainClassBody : Code .standard 32 :=
  .seq (ram[ base ← projectedBase; modulus ← projectedModulus; state ← initial ])
    (.seq backwardEvaluate
      (.seq (ram[ address ← heads + state; link ← *address; base ← fullBase;
        modulus ← fullModulus; one ← #1 ])
        (.seq retainLoop (ram[ operators ← operators + one ]))))

/-- Initialize and visit all packed second-quarter words, keeping one dictionary. -/
@[expose] def retainClass : Code .standard 32 :=
  .seq (ram[ operators ← #0; zero ← #0; one ← #1;
    stop ← one <<< count; Dictionary.top ← #0 ]) (.loop (.lt operators stop) retainClassBody)

/-- The exact insertion stream observed across a finite interval of packed words. -/
def classEntries {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j : ℕ) : ℕ → List Dictionary.Entry
  | 0 => []
  | n + 1 => retainedEntries as j (rs (retainQuery as g j)) ++ classEntries as g rs (j + 1) n

/-- Charged native execution time for that interval, including all loop tests. -/
def classRetainTime {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j : ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => (rs (retainQuery as g j)).length * (11 * as.length + 30) +
      18 * as.length + 33 + classRetainTime as g rs (j + 1) n + 2

/-- The budget is linear in actual retained hits and packed second-quarter words. -/
theorem classRetainTime_eq {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j n : ℕ) :
    classRetainTime as g rs j n = (classEntries as g rs j n).length * (11 * as.length + 30) +
      n * (18 * as.length + 35) + 2 := by
  induction n generalizing j with
  | zero => simp [classRetainTime, classEntries]
  | succ n ih =>
    simp only [classRetainTime, classEntries, List.length_append, retainedEntries,
      List.length_map, ih, Nat.add_mul, Nat.succ_mul]
    ring

/-- All stores and counter advancement for one packed second-quarter index. -/
theorem retainClassBody_exec {W m p a b q h D boundary L v t : ℕ}
    (as : List (BitVec m)) (g : BitVec p) (rs : BitVec p → List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs fullBase = b) (hq : x.regs projectedBase = q)
    (hm : x.regs fullModulus = 2 ^ m) (hp : x.regs projectedModulus = 2 ^ p)
    (hc : x.regs count = as.length) (hg : x.regs initial = g.toNat)
    (hh : x.regs heads = h) (hd : x.regs Dictionary.table = D)
    (hv : x.regs operators = v) (ht : x.regs Dictionary.top = t)
    (hs : x.regs stop = L) (hz : x.regs zero = 0) (hvL : v < L)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hproject : ∀ i (hi : i < (as.map (BitVec.setWidth p)).reverse.length),
      x.mem (q + i) = (as.map (BitVec.setWidth p)).reverse[i].toNat)
    (hlinked : ∀ k, Linked x.mem boundary (x.mem (h + k.toNat)) (rs k))
    (hstates : ∀ k, ∀ r ∈ rs k, r.1 < 2 ^ m)
    (hindices : ∀ k, ∀ r ∈ rs k, r.2 < 2 ^ a)
    (hboundary : boundary ≤ D) (hinputEnd : b + as.length ≤ D)
    (hfit : Fits W (D + boundary + h + q + b + as.length + 8 * 2 ^ m +
      2 * 2 ^ p + 2 ^ as.length + 2 ^ a + L + 8)) :
    ∃ y, ExecWithin W retainClassBody x y
        ((rs (retainQuery as g v)).length * (11 * as.length + 30) + 18 * as.length + 33) ∧
      y.mem = Dictionary.filledMemory D (retainedEntries as v (rs (retainQuery as g v)))
        x.mem t ∧
      y.regs Dictionary.top = Dictionary.filledTop D
        (retainedEntries as v (rs (retainQuery as g v))) x.mem t ∧
      y.regs operators = v + 1 ∧ y.regs one = 1 ∧ y.regs zero = 0 := by
  have hN := Nat.two_pow_pos as.length
  have hA := Nat.two_pow_pos a
  let low := x.set base q |>.set modulus (2 ^ p) |>.set state g.toNat
  have setup : ExecWithin (B := .standard) W
      (ram[ base ← projectedBase; modulus ← projectedModulus; state ← initial ]) x low 3 := by
    ram_eval [low, hq, hp, hg, base, projectedBase, modulus, projectedModulus, state, initial,
      Fin.mk.injEq]
  obtain ⟨z, he, zs, zv, zm⟩ := backwardEvaluate_exec (b := q) (v := v)
    (as.map (BitVec.setWidth p)) g low
    (by simp +decide [low, base, modulus, state])
    (by simpa +decide [low, count, base, modulus, state, List.length_map] using hc)
    (by simp +decide [low, modulus, state]) (by simp [low])
    (by simpa +decide [low, operators, base, modulus, state] using hv)
    (hfit.of_le (by omega)) (by simpa only [low, Data.set_mem] using hproject)
    (hfit.of_le (by simp only [List.length_map]; omega))
  have ez := setup.seq he
  let k := retainQuery as g v
  have zk : z.regs state = k.toNat := by
    simpa only [k, retainQuery, List.length_map] using zs
  have zmem : z.mem = x.mem := by simpa only [low, Data.set_mem] using zm
  have frame (r : Fin 32) (hr : (Code.seq (B := .standard)
      (ram[ base ← projectedBase; modulus ← projectedModulus; state ← initial ])
      backwardEvaluate).Preserves r) : z.regs r = x.regs r := ez.regs_eq hr
  let ready := z.set address (h + k.toNat) |>.set link (x.mem (h + k.toNat))
    |>.set base b |>.set modulus (2 ^ m) |>.set one 1
  have transfer : ExecWithin (B := .standard) W
      (ram[ address ← heads + state; link ← *address; base ← fullBase;
        modulus ← fullModulus; one ← #1 ]) z ready 5 := by
    have zh : z.regs heads = h := (frame heads (by decide)).trans hh
    have zb : z.regs fullBase = b := (frame fullBase (by decide)).trans hb
    have zn : z.regs fullModulus = 2 ^ m := (frame fullModulus (by decide)).trans hm
    have ha : Fits W (h + k.toNat) := hfit.of_le (by have := k.isLt; omega)
    have h1 : Fits W 1 := hfit.of_le (by omega)
    ram_eval [ready, zh, zk, zmem, zb, zn, ha, h1, address, heads, state, link,
      base, fullBase, modulus, fullModulus, one, Fin.mk.injEq]
  have et := ez.seq transfer
  obtain ⟨u, hu, um, ut, _, uone, uzero⟩ := retainLoop_exec
    (W := W) (a := a) (b := b) (D := D) (boundary := boundary) (v := v) (t := t)
    (ptr := x.mem (h + k.toNat)) as (rs k) ready
    (by simp +decide [ready, base, modulus, one])
    ((et.regs_eq (by decide)).trans hc) (by simp +decide [ready, modulus, one])
    (by simpa +decide [ready, operators, address, link, base, modulus, one] using zv)
    (hfit.of_le (by omega)) (by simp +decide [ready, link, base, modulus, one])
    ((et.regs_eq (by decide)).trans hd) ((et.regs_eq (by decide)).trans ht)
    (by simp [ready]) ((et.regs_eq (by decide)).trans hz)
    (by simpa only [ready, Data.set_mem, zmem] using hlinked k)
    hboundary hinputEnd (by simpa only [ready, Data.set_mem, zmem] using hinput)
    (hstates k) (hindices k) (hfit.of_le (by omega))
  have uops : u.regs operators = v := by
    rw [hu.regs_eq (by decide)]
    simpa +decide [ready, operators, address, link, base, modulus, one] using zv
  let y := u.set operators (v + 1)
  have ha : Fits W (v + 1) := hfit.of_le (by omega)
  have advance : ExecWithin (B := .standard) W (ram[ operators ← operators + one ]) u y 1 := by
    ram_eval [y, uops, uone, ha, operators, one,
      Fin.mk.injEq]
  refine ⟨y, ?_, ?_, ?_, by simp [y], ?_, ?_⟩
  · exact (setup.seq (he.seq (transfer.seq (hu.seq advance)))).mono (by
      simp only [List.length_map, k]; omega)
  · simpa only [y, Data.set_mem, ready, Data.set_mem, zmem, k] using um
  · simpa +decide [y, Dictionary.top, operators, ready, zmem, k] using ut
  · simpa +decide [y, one, operators] using uone
  · simpa +decide [y, zero, operators] using uzero

/-- Exact execution of a complete finite suffix of second-quarter words. The
remaining counter decreases by one; memory below the dictionary is invariant. -/
theorem retainClassLoop_exec {W m p a b q h D boundary j n t : ℕ}
    (as : List (BitVec m)) (g : BitVec p) (rs : BitVec p → List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs fullBase = b) (hq : x.regs projectedBase = q)
    (hm : x.regs fullModulus = 2 ^ m) (hp : x.regs projectedModulus = 2 ^ p)
    (hc : x.regs count = as.length) (hg : x.regs initial = g.toNat)
    (hh : x.regs heads = h) (hd : x.regs Dictionary.table = D)
    (hv : x.regs operators = j) (ht : x.regs Dictionary.top = t)
    (hs : x.regs stop = j + n) (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hproject : ∀ i (hi : i < (as.map (BitVec.setWidth p)).reverse.length),
      x.mem (q + i) = (as.map (BitVec.setWidth p)).reverse[i].toNat)
    (hlinked : ∀ k, Linked x.mem boundary (x.mem (h + k.toNat)) (rs k))
    (hstates : ∀ k, ∀ r ∈ rs k, r.1 < 2 ^ m)
    (hindices : ∀ k, ∀ r ∈ rs k, r.2 < 2 ^ a)
    (hboundary : boundary ≤ D) (hheadEnd : h + 2 ^ p ≤ D)
    (hinputEnd : b + as.length ≤ D) (hprojectEnd : q + as.length ≤ D)
    (hfit : Fits W (D + boundary + h + q + b + as.length + 8 * 2 ^ m +
      2 * 2 ^ p + 2 ^ as.length + 2 ^ a + (j + n) + 8)) :
    ∃ y, ExecWithin W (.loop (.lt operators stop) retainClassBody) x y
        (classRetainTime as g rs j n) ∧
      y.mem = Dictionary.filledMemory D (classEntries as g rs j n) x.mem t ∧
      y.regs Dictionary.top = Dictionary.filledTop D (classEntries as g rs j n) x.mem t ∧
      y.regs operators = j + n ∧ y.regs one = 1 ∧ y.regs zero = 0 := by
  induction n generalizing j x t with
  | zero =>
    exact ⟨x, ExecWithin.loop_exit (by simp [Cond.holds_lt, hv, hs]), rfl, ht,
      by simpa only [Nat.add_zero] using hv, ho, hz⟩
  | succ n ih =>
    obtain ⟨u, hu, um, ut, uv, uo, uz⟩ := retainClassBody_exec as g rs x
      hb hq hm hp hc hg hh hd hv ht hs hz (by omega) hinput hproject hlinked
      hstates hindices hboundary hinputEnd hfit
    have frame (k : ℕ) (hk : k < D) : u.mem k = x.mem k := by
      rw [um, Dictionary.filledMemory_below _ _ _ _ _ hk]
    have linked (k : BitVec p) : Linked u.mem boundary (u.mem (h + k.toNat)) (rs k) := by
      rw [frame _ (by have := k.isLt; omega)]
      exact (hlinked k).frame (fun z hz => frame z (by omega))
    obtain ⟨y, hy, ym, yt, yv, yo, yz⟩ := ih (j := j + 1) u
      ((hu.regs_eq (by decide)).trans hb) ((hu.regs_eq (by decide)).trans hq)
      ((hu.regs_eq (by decide)).trans hm) ((hu.regs_eq (by decide)).trans hp)
      ((hu.regs_eq (by decide)).trans hc) ((hu.regs_eq (by decide)).trans hg)
      ((hu.regs_eq (by decide)).trans hh) ((hu.regs_eq (by decide)).trans hd) uv ut
      (by have := hu.regs_eq (by decide : retainClassBody.Preserves stop); omega) uz uo
      (by intro i hi; rw [frame _ (by omega)]; exact hinput i hi)
      (by intro i hi; rw [frame _ (by
        simp only [List.length_reverse, List.length_map] at hi; omega)]; exact hproject i hi)
      linked (by simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hfit)
    refine ⟨y, ?_, ?_, ?_, by omega, yo, yz⟩
    · exact (ExecWithin.loop_iter (by simp only [Cond.holds_lt, hv, hs]; omega) hu hy).mono
        (by simp only [classRetainTime]; omega)
    · rw [ym, um]
      exact (Dictionary.filled_append D (retainedEntries as j (rs (retainQuery as g j)))
        (classEntries as g rs (j + 1) n) x.mem t).1.symm
    · rw [yt, um]
      exact (Dictionary.filled_append D (retainedEntries as j (rs (retainQuery as g j)))
        (classEntries as g rs (j + 1) n) x.mem t).2.symm

/-- Native complete retained-class construction, with a derived valid release
chain and exact restoration after release. Only initial empty dictionary cells
are required; neither final dictionary validity nor a traversal conclusion is assumed. -/
theorem retainClass_exec {W m p a b q h D boundary : ℕ}
    (as : List (BitVec m)) (g : BitVec p) (rs : BitVec p → List (ℕ × ℕ)) (x : Data 32)
    (hb : x.regs fullBase = b) (hq : x.regs projectedBase = q)
    (hm : x.regs fullModulus = 2 ^ m) (hp : x.regs projectedModulus = 2 ^ p)
    (hc : x.regs count = as.length) (hg : x.regs initial = g.toNat)
    (hh : x.regs heads = h) (hd : x.regs Dictionary.table = D)
    (hinput : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hproject : ∀ i (hi : i < (as.map (BitVec.setWidth p)).reverse.length),
      x.mem (q + i) = (as.map (BitVec.setWidth p)).reverse[i].toNat)
    (hlinked : ∀ k, Linked x.mem boundary (x.mem (h + k.toNat)) (rs k))
    (hstates : ∀ k, ∀ r ∈ rs k, r.1 < 2 ^ m)
    (hindices : ∀ k, ∀ r ∈ rs k, r.2 < 2 ^ a)
    (hboundary : boundary ≤ D) (hheadEnd : h + 2 ^ p ≤ D)
    (hinputEnd : b + as.length ≤ D) (hprojectEnd : q + as.length ≤ D)
    (hzero : ∀ k, D ≤ k → x.mem k = 0)
    (hfit : Fits W (D + boundary + h + q + b + as.length + 8 * 2 ^ m +
      2 * 2 ^ p + 2 ^ as.length + 2 ^ a + 2 ^ as.length + 8)) :
    let es := classEntries as g rs 0 (2 ^ as.length)
    ∃ y, ExecWithin W retainClass x y (5 + classRetainTime as g rs 0 (2 ^ as.length)) ∧
      y.mem = Dictionary.filledMemory D es x.mem 0 ∧
      y.regs Dictionary.top = Dictionary.filledTop D es x.mem 0 ∧
      y.regs operators = 2 ^ as.length ∧
      ∃ keys, Dictionary.Valid y.mem D (y.regs Dictionary.top) keys ∧
        keys.length ≤ es.length ∧ Dictionary.erasedMemory y.mem D keys = x.mem := by
  dsimp only
  have hN := Nat.two_pow_pos as.length
  have hA := Nat.two_pow_pos a
  let start := x.set operators 0 |>.set zero 0 |>.set one 1
    |>.set stop (2 ^ as.length) |>.set Dictionary.top 0
  have setup : ExecWithin (B := .standard) W
      (ram[ operators ← #0; zero ← #0; one ← #1;
        stop ← one <<< count; Dictionary.top ← #0 ]) x start 5 := by
    have h0 : Fits W 0 := fits_zero _
    have h1 : Fits W 1 := hfit.of_le (by omega)
    have hn : Fits W (2 ^ as.length) := hfit.of_le (by omega)
    ram_eval [start, h0, h1, hn, hc, Nat.shiftLeft_eq, one_mul, operators, zero, one,
      stop, count, Dictionary.top, Fin.mk.injEq]
  obtain ⟨y, hy, ym, yt, yv, _, _⟩ := retainClassLoop_exec
    (a := a) (t := 0) (j := 0) (n := 2 ^ as.length)
    as g rs start
    ((setup.regs_eq (by decide)).trans hb) ((setup.regs_eq (by decide)).trans hq)
    ((setup.regs_eq (by decide)).trans hm) ((setup.regs_eq (by decide)).trans hp)
    ((setup.regs_eq (by decide)).trans hc) ((setup.regs_eq (by decide)).trans hg)
    ((setup.regs_eq (by decide)).trans hh) ((setup.regs_eq (by decide)).trans hd)
    (by simp +decide [start, operators, zero, one, stop, Dictionary.top]) (by simp [start])
    (by simp +decide [start, stop, Dictionary.top])
    (by simp +decide [start, zero, one, stop, Dictionary.top])
    (by simp +decide [start, one, stop, Dictionary.top]) hinput hproject hlinked
    hstates hindices hboundary hheadEnd hinputEnd hprojectEnd
    (by simpa only [Nat.zero_add] using hfit)
  obtain ⟨keys, hk, hl, _, hr⟩ := Dictionary.filled_release
    (classEntries as g rs 0 (2 ^ as.length)) hzero
  refine ⟨y, setup.seq hy, ym, yt, ?_, keys, ?_, hl, ?_⟩
  · simpa only [Nat.zero_add] using yv
  · simpa only [ym, yt, start, Data.set_mem] using hk
  · simpa only [ym, start, Data.set_mem] using hr

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
