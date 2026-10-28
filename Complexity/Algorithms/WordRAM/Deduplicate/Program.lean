/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Deduplicate.Count

/-!
# Complete native adjacent deduplication and multiplicity arrays

The input is a sorted array. The program counts one maximal adjacent run, emits its key and
full count, and repeats. The output consists of two adjacent arrays, each with capacity equal
to the input length. All run tests, loads, stores, address calculations and control instructions
are charged. The total time is linear, including repeated keys and empty inputs.

## Main definitions

* `flush`: store one key/count pair and advance the output cursor.
* `body`: count and emit one complete run.
* `code`: the full adjacent deduplication program.

## Main results

* `exec`: full unique-key and multiplicity output with a linear native instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Deduplicate

open Cslib.WordRAM

/-- Store one key/count pair and advance the output cursor. -/
def flush : Code .standard 16 := ram[
  addr ← keys + out; *addr ← key;
  addr ← counts + out; *addr ← count; out ← out + one ]

/-- Count and emit the next maximal run. -/
def body : Code .standard 16 :=
  .seq (ram[ addr ← src + idx; key ← *addr; count ← #0; active ← #1 ])
    (.seq Count.code flush)

/-- Initialize the two cursors and count all adjacent runs. -/
def code : Code .standard 16 :=
  .seq (ram[ one ← #1; idx ← #0; out ← #0 ]) (.loop (.lt idx len) body)

private theorem flush_exec {w : ℕ} (x : Data 16) (ho : x.regs one = 1)
    (hk : Fits w (x.regs keys + x.regs out))
    (hc : Fits w (x.regs counts + x.regs out)) (hi : Fits w (x.regs out + 1)) :
    ∃ y, ExecWithin w flush x y 5 ∧ y.regs out = x.regs out + 1 ∧
      y.mem = Function.update (Function.update x.mem (x.regs keys + x.regs out) (x.regs key))
        (x.regs counts + x.regs out) (x.regs count) := by
  refine ⟨?_, ?run, ?_, ?_⟩
  case run => ram_eval [flush, ho, hk, hc, hi]
  all_goals simp +decide [Data.set_regs, Data.write_mem]

/-- Emit each distinct key once and its full multiplicity in at most `29n+5` instructions.
The input precedes the two output blocks; no input cells or cells outside the output blocks
change. Counts are ordinary unsigned words bounded by `n`. No restriction on key signs or
canonical encodings is needed: in particular canonical `Signed.encode` inputs are admitted. -/
theorem exec {w s base : ℕ} (xs : List ℕ) (x : Data 16)
    (hn : x.regs len = xs.length) (hs : x.regs src = s)
    (hk : x.regs keys = base) (hc : x.regs counts = base + xs.length)
    (hmem : Block.HoldsList s xs x.mem) (hsorted : xs.Pairwise (· ≤ ·))
    (hbelow : s + xs.length ≤ base) (hfit : Fits w (base + 2 * xs.length))
    (h1 : Fits w 1) :
    ∃ y rs, ExecWithin w code x y (29 * xs.length + 5) ∧
      RunEncoding xs rs ∧ y.regs out = rs.length ∧
      Block.HoldsList base (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (base + xs.length) (rs.map Prod.snd) y.mem ∧
      Block.HoldsList s xs y.mem ∧
      Modifies (Block.mk base (2 * xs.length)).footprint x.mem y.mem := by
  let n := xs.length
  let I (y : Data 16) : Prop :=
    y.regs len = n ∧ y.regs src = s ∧ y.regs keys = base ∧
    y.regs counts = base + n ∧ y.regs one = 1 ∧ y.regs idx ≤ n ∧
    Block.HoldsList s xs y.mem ∧
    Modifies (Block.mk base (2 * n)).footprint x.mem y.mem ∧
    ∃ rs, RunEncoding (xs.take (y.regs idx)) rs ∧ y.regs out = rs.length ∧
      Block.HoldsList base (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (base + n) (rs.map Prod.snd) y.mem ∧
      ∀ p ∈ rs, ∀ v ∈ xs.drop (y.regs idx), p.1 < v
  have hbody (y : Data 16) (hy : I y) (hcond : (Cond.lt idx len).Holds y) :
      ∃ z T, ExecWithin w body y z T ∧ I z ∧
        T + 2 + 29 * (n - z.regs idx) ≤ 29 * (n - y.regs idx) := by
    obtain ⟨hyn, hys, hyk, hyc, hyo, hiy, hym, hyf, rs, hrs, hyout, hyrk, hyrc, hrlt⟩ := hy
    have hi : y.regs idx < xs.length := by simpa only [Cond.holds_lt, hyn] using hcond
    have htail := hsorted.sublist (List.drop_sublist (y.regs idx) xs)
    rw [List.drop_eq_getElem_cons hi] at htail
    obtain ⟨c, rest, hcp, heq, hrest⟩ := first_run xs[y.regs idx] (xs.drop (y.regs idx + 1)) htail
    have hdrop : xs.drop (y.regs idx) = List.replicate c xs[y.regs idx] ++ rest := by
      rw [List.drop_eq_getElem_cons hi, heq]
    have hlen := congrArg List.length hdrop
    simp only [List.length_drop, List.length_append, List.length_replicate] at hlen
    have hstop : y.regs idx + c ≤ n := by omega
    have hdrop' : xs.drop (y.regs idx + c) = rest := by
      rw [← List.drop_drop, hdrop]
      exact List.drop_left' (by simp)
    have htake : xs.take (y.regs idx + c) =
        xs.take (y.regs idx) ++ List.replicate c xs[y.regs idx] := by
      rw [List.take_add, hdrop, List.take_left' (by simp)]
    have hrun (j : ℕ) (hlo : y.regs idx ≤ j) (hhi : j < y.regs idx + c) :
        y.mem (s + j) = xs[y.regs idx] := by
      rw [hym.get j (by omega)]
      have hh : (xs.drop (y.regs idx))[j - y.regs idx]'(by simp only [List.length_drop]; omega) =
          xs[y.regs idx] := by
        simp [hdrop, show j - y.regs idx < c from by omega]
      simpa only [List.getElem_drop, show y.regs idx + (j - y.regs idx) = j from by omega] using hh
    have hnext (hlt : y.regs idx + c < n) :
        y.mem (s + (y.regs idx + c)) ≠ xs[y.regs idx] := by
      rw [hym.get _ hlt]
      have hmember : xs[y.regs idx + c] ∈ rest := by
        rw [← hdrop']
        have hh := List.getElem_mem (l := xs.drop (y.regs idx + c))
          (n := 0) (by simp only [List.length_drop]; omega)
        simpa using hh
      have := hrest _ hmember
      omega
    let y₀ := (((y.set addr (s + y.regs idx)).set key xs[y.regs idx]).set count 0).set active 1
    have hinit : ExecWithin (B := .standard) w
        (ram[ addr ← src + idx; key ← *addr; count ← #0; active ← #1 ]) y y₀ 4 := by
      have had : Fits w (y.regs src + y.regs idx) := by
        rw [hys]; exact hfit.of_le (by omega)
      have hread : y.mem (y.regs src + y.regs idx) = xs[y.regs idx] := by
        rw [hys]; exact hym.get _ hi
      have had' : Fits w (s + y.regs idx) := hfit.of_le (by omega)
      have hread' : y.mem (s + y.regs idx) = xs[y.regs idx] := hym.get _ hi
      ram_eval [y₀, had, had', hread, hread', hys, h1]
    obtain ⟨u, hu, hui, huc, hum⟩ := Count.exec (k := xs[y.regs idx]) y₀
      (by simpa +decide [y₀] using hyn) (by simpa +decide [y₀] using hys)
      (by simp +decide [y₀]) (by simp +decide [y₀])
      (by simp +decide [y₀]) (by simp +decide [y₀])
      (by simpa +decide [y₀] using hyo) (show y.regs idx ≤ y.regs idx + c by omega)
      hstop (by simpa only [y₀, Data.set_mem] using hrun)
      (by simpa only [y₀, Data.set_mem] using hnext) (hfit.of_le (by omega))
    have huc' : u.regs count = c := by simpa using huc
    have hur (j : Fin 16) (hj : Count.code.Preserves j) : u.regs j = y₀.regs j := hu.regs_eq hj
    have hun : u.regs len = n := by
      simpa +decide [y₀]
        using (hur len (by decide)).trans
          (by simpa +decide [y₀] using hyn)
    have hus : u.regs src = s := by
      simpa +decide [y₀]
        using (hur src (by decide)).trans
          (by simpa +decide [y₀] using hys)
    have huk : u.regs keys = base := by
      simpa +decide [y₀]
        using (hur keys (by decide)).trans
          (by simpa +decide [y₀] using hyk)
    have hucb : u.regs counts = base + n := by
      simpa +decide [y₀]
        using (hur counts (by decide)).trans
          (by simpa +decide [y₀] using hyc)
    have huo : u.regs one = 1 := by
      simpa +decide [y₀]
        using (hur one (by decide)).trans
          (by simpa +decide [y₀] using hyo)
    have huout : u.regs out = rs.length := by
      simpa +decide [y₀]
        using (hur out (by decide)).trans
          (by simpa +decide [y₀] using hyout)
    have hukey : u.regs key = xs[y.regs idx] := by simpa +decide [y₀] using hur key (by decide)
    have hrl : rs.length ≤ y.regs idx := by
      have hh := length_le_expand hrs.positive
      rw [hrs.reconstruct, List.length_take_of_le hiy] at hh
      exact hh
    obtain ⟨z, hz, hzout, hzm⟩ := flush_exec u huo
      (by rw [huk, huout]; exact hfit.of_le (by omega))
      (by rw [hucb, huout]; exact hfit.of_le (by omega))
      (by rw [huout]; exact hfit.of_le (by omega))
    have hzmem : z.mem = Function.update
        (Function.update y.mem (base + rs.length) xs[y.regs idx]) (base + n + rs.length) c := by
      simpa only [huk, hucb, huout, hukey, huc', hum, y₀, Data.set_mem] using hzm
    have hzi : z.regs idx = y.regs idx + c := (hz.regs_eq (by decide)).trans hui
    have hzf : Modifies (Block.mk base (2 * n)).footprint y.mem z.mem := by
      intro a hnot
      have ha : ¬(base ≤ a ∧ a < base + 2 * n) := by
        simpa only [Block.mem_footprint, Block.Owns] using hnot
      rw [hzmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hkeyrep : Block.HoldsList base
        ((rs ++ [(xs[y.regs idx], c)]).map Prod.fst) z.mem := by
      rw [List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [hzmem]
      have hkr : Block.HoldsList base (rs.map Prod.fst ++ [xs[y.regs idx]])
          (Function.update y.mem (base + rs.length) xs[y.regs idx]) := by
        simpa only [List.length_map] using hyrk.append_one xs[y.regs idx]
      apply hkr.frame
      intro a hlo hhi
      rw [Function.update_of_ne (by
        simp only [List.length_append, List.length_map, List.length_singleton] at hhi
        omega)]
    have hcountrep : Block.HoldsList (base + n)
        ((rs ++ [(xs[y.regs idx], c)]).map Prod.snd) z.mem := by
      rw [List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [hzmem]
      have hcr : Block.HoldsList (base + n) (rs.map Prod.snd)
          (Function.update y.mem (base + rs.length) xs[y.regs idx]) := by
        apply hyrc.frame
        intro a hlo hhi
        rw [Function.update_of_ne (by omega)]
      simpa only [List.length_map] using hcr.append_one c
    have hrs' : RunEncoding (xs.take (y.regs idx + c)) (rs ++ [(xs[y.regs idx], c)]) := by
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hrs.positive p hp
        · have hp' := List.mem_singleton.mp hp
          subst p
          exact hcp
      · apply List.pairwise_append.mpr
        refine ⟨hrs.ordered, by simp, ?_⟩
        intro p hp q hq
        have hq' : q = (xs[y.regs idx], c) := List.mem_singleton.mp hq
        subst q
        apply hrlt p hp
        rw [List.drop_eq_getElem_cons hi]
        exact List.mem_cons_self
      · rw [expand_append, expand_singleton, hrs.reconstruct, htake]
    refine ⟨z, 8 * c + 19, ?_, ?_, ?_⟩
    · have hall := hinit.seq (hu.seq hz)
      exact hall.mono (by omega)
    · refine ⟨(hz.regs_eq (by decide)).trans hun, (hz.regs_eq (by decide)).trans hus,
        (hz.regs_eq (by decide)).trans huk, (hz.regs_eq (by decide)).trans hucb,
        (hz.regs_eq (by decide)).trans huo, by omega, ?_, ?_,
        rs ++ [(xs[y.regs idx], c)], by simpa only [hzi] using hrs', ?_, hkeyrep, hcountrep, ?_⟩
      · apply hym.frame
        intro a hlo hhi
        apply hzf
        rw [Block.mem_footprint]
        change ¬(base ≤ a ∧ a < base + 2 * n)
        omega
      · intro a ha
        exact (hzf a ha).trans (hyf a ha)
      · rw [hzout, huout, List.length_append, List.length_singleton]
      · intro p hp v hv
        rw [hzi, hdrop'] at hv
        rcases List.mem_append.mp hp with hp | hp
        · apply hrlt p hp
          rw [hdrop]
          exact List.mem_append_right _ hv
        · have hp' : p = (xs[y.regs idx], c) := List.mem_singleton.mp hp
          subst p
          exact hrest v hv
    · rw [hzi]
      omega
  let x₀ := ((x.set one 1).set idx 0).set out 0
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hmem, Modifies.refl _ _, [], ?_, ?_, ?_, ?_, ?_⟩
    · simpa +decide [x₀] using hn
    · simpa +decide [x₀] using hs
    · simpa +decide [x₀] using hk
    · simpa +decide [x₀] using hc
    · simp +decide [x₀]
    · simp +decide [x₀]
    · refine ⟨by simp, by simp, ?_⟩
      simp +decide [x₀, expand]
    · simp [x₀]
    · exact Block.holdsList_nil _ _
    · exact Block.holdsList_nil _ _
    · simp
  obtain ⟨y, he, hy, hcond⟩ := ExecWithin.loop_potential I
    (fun y => 29 * (n - y.regs idx)) hbody hx₀
  obtain ⟨hyn, _, _, _, _, hiy, hym, hyf, rs, hrs, hyout, hyrk, hyrc, _⟩ := hy
  have hend : y.regs idx = xs.length := by
    simp only [Cond.holds_lt, hyn] at hcond
    omega
  have hinit : ExecWithin (B := .standard) w (ram[ one ← #1; idx ← #0; out ← #0 ]) x x₀ 3 := by
    ram_eval [x₀, h1]
  refine ⟨y, rs, ?_, by simpa only [hend, List.take_length] using hrs,
    hyout, hyrk, hyrc, hym, hyf⟩
  have hall := hinit.seq he
  convert hall using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, idx, out, one,
      ↓reduceIte, Nat.sub_zero, n]
    omega

end Cslib.Algorithms.WordRAM.Deduplicate
