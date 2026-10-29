/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PrimeTable
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Query
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Native least-prime collision searches

The search scans the prime bitmap in increasing order. A candidate runs the complete native
three-set collision query. Its first acceptance is retained while the remaining candidates
are visited without further bitmap reads. If no candidate is accepted, the answer is one, matching
`ChanHe.minOrOne`.

## Main definitions

* `Search.program`: a fixed native prime search using charged collision queries.

## Main results

* `Search.exec`: exact minimum/default selection with native fits, frames and charged cost.
* `Search.preserves_caller`: the upper five caller registers are preserved.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Search

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum.ChanHe

/-- Largest candidate prime. -/
abbrev limit : Fin 64 := 40
/-- Prime bitmap base. -/
abbrev primes : Fin 64 := 41
/-- Factor multiplied by the candidate prime. -/
abbrev factor : Fin 64 := 43
/-- Current candidate. -/
abbrev cursor : Fin 64 := 47
/-- One past the largest candidate. -/
abbrev stop : Fin 64 := 48
/-- Selected prime, or the default one. -/
abbrev answer : Fin 64 := 49
/-- Whether an acceptance has already occurred. -/
abbrev found : Fin 64 := 50
/-- Constant one. -/
abbrev one : Fin 64 := 51
/-- Constant zero. -/
abbrev zero : Fin 64 := 52
/-- Constant two, for positive signed encoding. -/
abbrev two : Fin 64 := 53
/-- Unencoded candidate modulus. -/
abbrev rawModulus : Fin 64 := 54
/-- Bitmap address scratch. -/
abbrev addr : Fin 64 := 55
/-- Loaded primality bit. -/
abbrev bit : Fin 64 := 56
/-- Encoded candidate modulus. -/
abbrev modulus : Fin 64 := CountCall.modulus
/-- Acceptance flag returned by the collision query. -/
abbrev good : Fin 64 := CollisionTest.good

/-- Compute and encode the candidate modulus, then run the full collision query. -/
def query : Code .standard 64 :=
  .seq (ram[ rawModulus ← factor * cursor; modulus ← rawModulus * two ]) Query.program

/-- Record an accepted candidate, or retain the previous answer. -/
def pick : Code .standard 64 := ram[
  if good = one then [ answer ← cursor; found ← one ] else [ answer ← answer ] ]

/-- A charged instruction that retains the answer. -/
def nop : Code .standard 64 := ram[ answer ← answer ]

/-- Load a bitmap entry. -/
def load : Code .standard 64 := ram[ addr ← primes + cursor; bit ← *addr ]

/-- Before the first acceptance, run the query exactly on prime candidates. -/
def inner : Code .standard 64 :=
  .branch (.eq found zero)
    (.seq load (.branch (.eq bit one) (.seq query pick) nop)) nop

/-- One candidate and its charged cursor increment. -/
def body : Code .standard 64 := .seq inner (ram[ cursor ← cursor + one ])

/-- Initialize the selector and scan the entire bounded candidate range. -/
def program : Code .standard 64 :=
  .seq (ram[ one ← #1; zero ← #0; two ← #2; cursor ← #0;
    stop ← limit + one; answer ← one; found ← zero ]) (.loop (.lt cursor stop) body)

/-- The five upper caller registers survive the complete native search. -/
theorem preserves_caller (i : Fin 64) (hi : 59 ≤ i.val) : program.Preserves i := by
  fin_cases i <;> norm_num at hi <;> decide

private abbrev Fixed (i : Fin 64) : Prop := (28 ≤ i.val ∧ i.val ≤ 35) ∨ (40 ≤ i.val ∧ i.val ≤ 46)

private abbrev Control (i : Fin 64) : Prop :=
  (28 ≤ i.val ∧ i.val ≤ 35) ∨ (40 ≤ i.val ∧ i.val ≤ 53)

private def Stable (x y : Data 64) : Prop :=
  (∀ i, Fixed i → y.regs i = x.regs i) ∧
    ∀ a < x.regs CountCall.scratch, y.mem a = x.mem a

private def Status (A : ℕ → Prop) (k : ℕ) (y : Data 64) : Prop :=
  (y.regs found = 0 ∧ y.regs answer = 1 ∧ ∀ q < k, ¬(q.Prime ∧ A q)) ∨
  (y.regs found = 1 ∧ y.regs answer < k ∧ (y.regs answer).Prime ∧ A (y.regs answer) ∧
    ∀ q < y.regs answer, ¬(q.Prime ∧ A q))

private theorem exec_nop {w : ℕ} (x : Data 64) : ExecWithin w nop x x 1 := by
  have hx : x.set answer (x.regs answer) = x := Data.ext (Function.update_eq_self _ _) rfl
  simpa only [nop, hx] using (ExecWithin.copy (B := .standard) (w := w)
    (x := x) (d := answer) (s := answer))

private theorem exec_pick {w : ℕ} (x : Data 64) (A : Prop) [Decidable A]
    (ho : x.regs one = 1) (hg : x.regs good = if A then 1 else 0) :
    ∃ y, ExecWithin w pick x y 3 ∧ y.mem = x.mem ∧
      y.regs answer = (if A then x.regs cursor else x.regs answer) ∧
      y.regs found = (if A then 1 else x.regs found) ∧
      ∀ i, i ≠ answer → i ≠ found → y.regs i = x.regs i := by
  by_cases hA : A
  · let y := (x.set answer (x.regs cursor)).set found 1
    refine ⟨y, ?_, rfl, ?_, ?_, ?_⟩
    · ram_eval [pick, y, ho, hg, hA, good, one, cursor, answer, found, Fin.mk.injEq]
    · simp +decide [y, hA, answer, found]
    · simp [y, hA]
    · intro i ha hf
      simp only [y, Data.set_regs, Function.update_of_ne ha, Function.update_of_ne hf]
  · refine ⟨x, ?_, rfl, by simp [hA], by simp [hA], fun _ _ _ => rfl⟩
    have hc : ¬(Cond.eq good one).Holds x := by simp [hg, hA, ho]
    exact ExecWithin.branch_neg hc (exec_nop x)

private theorem status_min {A : ℕ → Prop} [DecidablePred A] {m : ℕ} {y : Data 64}
    (h : Status A (m + 1) y) :
    y.regs answer = minOrOne {q ∈ Nat.primesLE m | A q} := by
  let S := {q ∈ Nat.primesLE m | A q}
  rcases h with ⟨hf, ha, hn⟩ | ⟨hf, hk, hp, hA, hn⟩
  · have hs : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hmem := Finset.mem_filter.mp (by
        simpa only [Nat.primesLE_eq_filter_range] using hq'.1)
      exact hn q (Finset.mem_range.mp hmem.1) ⟨hmem.2, hq'.2⟩
    rw [ha]
    change 1 = minOrOne S
    simp [hs, minOrOne]
  · have hmem : y.regs answer ∈ S := by
      simp only [S, Finset.mem_filter, Nat.primesLE_eq_filter_range, Finset.mem_range]
      exact ⟨⟨hk, hp⟩, hA⟩
    have hs : S.Nonempty := ⟨_, hmem⟩
    have hmin : S.min' hs = y.regs answer := by
      apply le_antisymm (Finset.min'_le _ _ hmem)
      apply Finset.le_min'
      intro q hq
      by_contra hnot
      have hq' := Finset.mem_filter.mp hq
      have hpq := (Finset.mem_filter.mp (by
        simpa only [Nat.primesLE_eq_filter_range] using hq'.1)).2
      exact hn q (by omega) ⟨hpq, hq'.2⟩
    change y.regs answer = minOrOne S
    simp only [minOrOne, dite_eq_left hs, hmin]


private theorem fixed_ne_high {i j : Fin 64} (hi : Fixed i) (hj : 47 ≤ j.val) : i ≠ j := by
  intro h
  have := congrArg Fin.val h
  dsimp [Fixed] at hi
  omega

private theorem stable_set_high {x y : Data 64} (h : Stable x y) (i : Fin 64)
    (hi : 47 ≤ i.val) (v : ℕ) : Stable x (y.set i v) := by
  exact ⟨fun j hj => by
    simpa only [Data.set_regs, Function.update_of_ne (fixed_ne_high hj hi)] using h.1 j hj,
    h.2⟩

private theorem status_of_regs {A : ℕ → Prop} {k : ℕ} {x y : Data 64}
    (hf : y.regs found = x.regs found) (ha : y.regs answer = x.regs answer)
    (h : Status A k x) : Status A k y := by
  simpa only [Status, hf, ha] using h

private theorem status_extend {A : ℕ → Prop} {k : ℕ} {y : Data 64}
    (h : Status A k y) (hnew : y.regs found = 0 → ¬(k.Prime ∧ A k)) :
    Status A (k + 1) y := by
  rcases h with ⟨hf, ha, hn⟩ | ⟨hf, hk, hp, hA, hn⟩
  · exact Or.inl ⟨hf, ha, fun q hq => by
      by_cases hqk : q < k
      · exact hn q hqk
      · have : q = k := by omega
        subst q
        exact hnew hf⟩
  · exact Or.inr ⟨hf, by omega, hp, hA, hn⟩

private theorem exec_driver {w T : ℕ} (x : Data 64) (A : ℕ → Prop) [DecidablePred A]
    (hfit : Fits w (x.regs limit + 3))
    (haddr : Fits w (x.regs primes + (x.regs limit + 1)))
    (hbefore : x.regs primes + (x.regs limit + 1) ≤ x.regs CountCall.scratch)
    (hbitmap : ∀ q ≤ x.regs limit, x.mem (x.regs primes + q) = if q.Prime then 1 else 0)
    (hquery : ∀ y, Stable x y → y.regs cursor ≤ x.regs limit →
      y.regs one = 1 → y.regs zero = 0 → y.regs two = 2 → (y.regs cursor).Prime →
      ∃ z, ExecWithin w query y z T ∧ Stable x z ∧
        z.regs good = (if A (y.regs cursor) then 1 else 0) ∧
        ∀ i, Control i → z.regs i = y.regs i) :
    ∃ y, ExecWithin w program x y ((x.regs limit + 1) * (T + 15) + 9) ∧
      Stable x y ∧ y.regs answer = minOrOne {q ∈ Nat.primesLE (x.regs limit) | A q} := by
  let m := x.regs limit
  let I (y : Data 64) : Prop := Stable x y ∧ y.regs stop = m + 1 ∧
    y.regs one = 1 ∧ y.regs zero = 0 ∧ y.regs two = 2 ∧ y.regs cursor ≤ m + 1 ∧
    Status A (y.regs cursor) y
  have hbody (y : Data 64) (hy : I y) (hc : (Cond.lt cursor stop).Holds y) :
      ∃ z, ExecWithin w body y z (T + 13) ∧ I z ∧
        m + 1 - z.regs cursor < m + 1 - y.regs cursor := by
    obtain ⟨hstable, hstop, ho, hz, ht, hi, hstatus⟩ := hy
    have hlt : y.regs cursor < m + 1 := by simpa only [Cond.holds_lt, hstop] using hc
    have hinner : ∃ z, ExecWithin w inner y z (T + 12) ∧ Stable x z ∧
        z.regs stop = m + 1 ∧ z.regs one = 1 ∧ z.regs zero = 0 ∧ z.regs two = 2 ∧
        z.regs cursor = y.regs cursor ∧ Status A (y.regs cursor + 1) z := by
      rcases hstatus with hnone | hsome
      · obtain ⟨hf, ha, hn⟩ := hnone
        have hfound : (Cond.eq found zero).Holds y := by simp [hf, hz]
        have hpr : y.regs primes = x.regs primes := hstable.1 _ (by decide)
        have hread : y.mem (y.regs primes + y.regs cursor) =
            if (y.regs cursor).Prime then 1 else 0 := by
          rw [hpr, hstable.2 (x.regs primes + y.regs cursor) (by omega)]
          exact hbitmap _ (by change y.regs cursor ≤ m; omega)
        have had : Fits w (y.regs primes + y.regs cursor) := haddr.of_le (by rw [hpr]; omega)
        let u := (y.set addr (y.regs primes + y.regs cursor)).set bit
          (if (y.regs cursor).Prime then 1 else 0)
        have hload : ExecWithin w load y u 2 := by
          ram_eval [load, u, had, hread, addr, bit, primes, cursor, Fin.mk.injEq]
        have hu (i : Fin 64) (hC : Control i) : u.regs i = y.regs i := by
          have hia : i ≠ addr := by intro h; subst i; norm_num [Control, addr] at hC
          have hib : i ≠ bit := by intro h; subst i; norm_num [Control, bit] at hC
          simp only [u, Data.set_regs, Function.update_of_ne hia, Function.update_of_ne hib]
        have hus : Stable x u := stable_set_high
          (stable_set_high hstable addr (by decide) _) bit (by decide) _
        have huo : u.regs one = 1 := (hu one (by decide)).trans ho
        have huz : u.regs zero = 0 := (hu zero (by decide)).trans hz
        have hut : u.regs two = 2 := (hu two (by decide)).trans ht
        have hui : u.regs cursor = y.regs cursor := hu cursor (by decide)
        have husp : u.regs stop = m + 1 := (hu stop (by decide)).trans hstop
        have huf : u.regs found = 0 := (hu found (by decide)).trans hf
        have hua : u.regs answer = 1 := (hu answer (by decide)).trans ha
        by_cases hp : (y.regs cursor).Prime
        · have hbit : (Cond.eq bit one).Holds u := by
            simp only [Cond.holds_eq, huo]
            simp +decide [u, bit, addr, hp]
          obtain ⟨v, hv, hvs, hvg, hvr⟩ := hquery u hus (by rw [hui]; change _ ≤ m; omega)
            huo huz hut (by simpa only [hui] using hp)
          have hvo : v.regs one = 1 := (hvr one (by decide)).trans huo
          obtain ⟨z, hpick, hzm, hza, hzf, hzr⟩ := exec_pick v (A (y.regs cursor)) hvo
            (by simpa only [hui] using hvg)
          have hzctrl (i : Fin 64) (hC : Control i) (hia : i ≠ answer) (hif : i ≠ found) :
              z.regs i = y.regs i :=
            (hzr i hia hif).trans ((hvr i hC).trans (hu i hC))
          have hzs : Stable x z := ⟨fun i hF =>
            (hzr i (fixed_ne_high hF (by decide)) (fixed_ne_high hF (by decide))).trans
              (hvs.1 i hF), fun a ha => by rw [hzm]; exact hvs.2 a ha⟩
          have hvi : v.regs cursor = y.regs cursor := (hvr cursor (by decide)).trans hui
          have hvf : v.regs found = 0 := (hvr found (by decide)).trans huf
          have hva : v.regs answer = 1 := (hvr answer (by decide)).trans hua
          refine ⟨z, ?_, hzs, ?_, ?_, ?_, ?_, hzctrl cursor (by decide) (by decide) (by decide), ?_⟩
          · exact (ExecWithin.branch_pos hfound
              (hload.seq (ExecWithin.branch_pos hbit (hv.seq hpick)))).mono (by omega)
          · exact (hzctrl stop (by decide) (by decide) (by decide)).trans hstop
          · exact (hzctrl one (by decide) (by decide) (by decide)).trans ho
          · exact (hzctrl zero (by decide) (by decide) (by decide)).trans hz
          · exact (hzctrl two (by decide) (by decide) (by decide)).trans ht
          · by_cases hA : A (y.regs cursor)
            · have hanswer : z.regs answer = y.regs cursor := by
                simpa only [hA, ↓reduceIte, hvi] using hza
              refine Or.inr ⟨by simpa only [hA, ↓reduceIte] using hzf, ?_, ?_, ?_, ?_⟩
              · rw [hanswer]; omega
              · simpa only [hanswer] using hp
              · simpa only [hanswer] using hA
              · simpa only [hanswer] using hn
            · have hanswer : z.regs answer = 1 := by simpa only [hA, ↓reduceIte, hva] using hza
              refine Or.inl ⟨by simpa only [hA, ↓reduceIte, hvf] using hzf, hanswer, ?_⟩
              intro q hq hqA
              by_cases hqk : q < y.regs cursor
              · exact hn q hqk hqA
              · have hqeq : q = y.regs cursor := by omega
                subst q
                exact hA hqA.2
        · have hbit : ¬(Cond.eq bit one).Holds u := by
            simp only [Cond.holds_eq, huo]
            simp +decide [u, bit, addr, hp]
          have hnop := exec_nop (w := w) u
          refine ⟨u, ?_, hus, husp, huo, huz, hut, hui, Or.inl ⟨huf, hua, ?_⟩⟩
          · exact (ExecWithin.branch_pos hfound
              (hload.seq (ExecWithin.branch_neg hbit hnop))).mono (by omega)
          · intro q hq hqA
            by_cases hqk : q < y.regs cursor
            · exact hn q hqk hqA
            · have hqeq : q = y.regs cursor := by omega
              subst q
              exact hp hqA.1
      · have hfound : ¬(Cond.eq found zero).Holds y := by
          simp only [Cond.holds_eq, hsome.1, hz]; omega
        refine ⟨y, (ExecWithin.branch_neg hfound (exec_nop y)).mono (by omega),
          hstable, hstop, ho, hz, ht, rfl, ?_⟩
        exact status_extend (Or.inr hsome) (fun h0 => by rw [hsome.1] at h0; omega)
    obtain ⟨z, he, hs, hsp, hzo, hzz, hzt, hzi, hstat⟩ := hinner
    have hinc : Fits w (z.regs cursor + z.regs one) :=
      hfit.of_le (by rw [hzi, hzo]; change _ ≤ m + 3; omega)
    have hstep : ExecWithin w (Code.op (.bin .add cursor cursor one)) z
        (z.set cursor (z.regs cursor + 1)) 1 := by
      simpa only [BinOp.eval, hzo] using (ExecWithin.bin (f := .add) (d := cursor) (i := cursor)
        (j := one) hinc)
    refine ⟨z.set cursor (z.regs cursor + 1), he.seq hstep, ?_, ?_⟩
    · refine ⟨stable_set_high hs cursor (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [stop, cursor] using hsp
      · simpa +decide [one, cursor] using hzo
      · simpa +decide [zero, cursor] using hzz
      · simpa +decide [two, cursor] using hzt
      · simpa only [Data.set_regs, Function.update_self, hzi] using Nat.succ_le_of_lt hlt
      · simpa only [Data.set_regs, Function.update_self] using
          status_of_regs (x := z) (y := z.set cursor (z.regs cursor + 1))
            (by simp +decide [found, cursor])
            (by simp +decide [answer, cursor]) (by simpa only [hzi] using hstat)
    · simp only [Data.set_regs, Function.update_self, hzi]
      omega
  let x₀ := ((((((x.set one 1).set zero 0).set two 2).set cursor 0).set stop (m + 1)).set
    answer 1).set found 0
  have hinit : ExecWithin w (ram[
      one ← #1; zero ← #0; two ← #2; cursor ← #0; stop ← limit + one;
      answer ← one; found ← zero]) x x₀ 7 := by
    have h1 : Fits w 1 := hfit.of_le (by omega)
    have h2 : Fits w 2 := hfit.of_le (by omega)
    have h0 : Fits w 0 := hfit.of_le (by omega)
    have hm : Fits w (m + 1) := hfit.of_le (by change m + 1 ≤ m + 3; omega)
    ram_eval [x₀, m, one, zero, two, cursor, stop, limit, answer, found,
      h1, h2, h0, hm, Fin.mk.injEq]
  have hi : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
    · exact stable_set_high (stable_set_high (stable_set_high (stable_set_high
        (stable_set_high (stable_set_high (stable_set_high ⟨fun _ _ => rfl,
          fun _ _ => rfl⟩ one (by decide) _) zero (by decide) _) two (by decide) _)
            cursor (by decide) _) stop (by decide) _) answer (by decide) _) found (by decide) _
    all_goals simp +decide [x₀, stop, one, zero, two, cursor, answer, found]
  obtain ⟨y, he, hy, hexit⟩ := ExecWithin.loop_invariant I
    (fun y => m + 1 - y.regs cursor) hbody hi
  obtain ⟨hs, hsp, hyo, hyz, hyt, hyi, hstat⟩ := hy
  have hcur : y.regs cursor = m + 1 := by
    simp only [Cond.holds_lt, hsp] at hexit
    omega
  refine ⟨y, (hinit.seq he).mono ?_, hs, ?_⟩
  · have hcur₀ : x₀.regs cursor = 0 := by
      simp +decide [x₀, cursor, found, answer, stop]
    rw [hcur₀]
    simp only [Nat.sub_zero]
    change 7 + ((m + 1) * (T + 13 + 2) + 2) ≤ (m + 1) * (T + 15) + 9
    have hcost : T + 13 + 2 = T + 15 := by omega
    rw [hcost]
    omega
  · exact status_min (by simpa only [hcur] using hstat)

/-- The least prime whose three actual collision counts satisfy the supplied thresholds.
Every candidate query is executed by `Query.program`; the hypotheses only constrain native
input values, layout and word fits. All instructions, including the scan after acceptance,
are charged. The final halt is excluded. -/
theorem exec {w : ℕ} (x : Data 64) (values : Fin 3 → ℕ → ℤ)
    (hfactor : 0 < x.regs factor)
    (hmod : GenericRAM.Signed.Fits w ((x.regs factor * x.regs limit : ℕ) : ℤ))
    (hfit : Fits (w + 2) (x.regs limit + 3))
    (haddr : Fits (w + 2) (x.regs primes + (x.regs limit + 1)))
    (hbefore : x.regs primes + (x.regs limit + 1) ≤ x.regs CountCall.scratch)
    (hbitmap : ∀ q ≤ x.regs limit, x.mem (x.regs primes + q) = if q.Prime then 1 else 0)
    (hvalues : ∀ j i, i < x.regs (CountCall.length j) → GenericRAM.Signed.Fits w (values j i))
    (hs : ∀ j, Fits (w + 2) (x.regs (CountCall.source j) + x.regs (CountCall.length j)))
    (hk : ∀ j, Fits (w + 2) (x.regs CountCall.scratch + x.regs (CountCall.length j)))
    (hd : Fits (w + 2) (x.regs CountCall.histogram + x.regs factor * x.regs limit))
    (ht : ∀ j, Fits (w + 2) (x.regs (CountCall.length j) * x.regs (CountCall.length j) +
      x.regs (CountCall.length j) + 1))
    (hproduct : ∀ j, Fits (w + 2) (x.regs (CountCall.length j) * x.regs (CountCall.length j) *
      x.regs CollisionTest.card))
    (hsk : ∀ j, x.regs (CountCall.source j) + x.regs (CountCall.length j) ≤
      x.regs CountCall.scratch)
    (hkd : ∀ j, x.regs CountCall.scratch + x.regs (CountCall.length j) ≤
      x.regs CountCall.histogram)
    (hinput : ∀ j i, i < x.regs (CountCall.length j) →
      x.mem (x.regs (CountCall.source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (CountCall.length j))) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y
        ((x.regs limit + 1) * (34 * (x.regs (CountCall.length 0) +
          x.regs (CountCall.length 1) + x.regs (CountCall.length 2)) +
          15 * (x.regs factor * x.regs limit) + 102) + 9) ∧
      (∀ i, ((28 ≤ i.val ∧ i.val ≤ 35) ∨ (40 ≤ i.val ∧ i.val ≤ 46)) →
        y.regs i = x.regs i) ∧
      (∀ a < x.regs CountCall.scratch, y.mem a = x.mem a) ∧
      y.regs answer = minOrOne {q ∈ Nat.primesLE (x.regs limit) | ∀ j : Fin 3,
        coll ((Finset.range (x.regs (CountCall.length j))).image (values j))
          (x.regs factor * q) * x.regs CollisionTest.card ≤
            x.regs (CollisionTest.threshold j)} := by
  let A (q : ℕ) : Prop := ∀ j : Fin 3,
    coll ((Finset.range (x.regs (CountCall.length j))).image (values j))
      (x.regs factor * q) * x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold j)
  let T := 34 * (x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
    x.regs (CountCall.length 2)) + 15 * (x.regs factor * x.regs limit) + 87
  have hquery (y : Data 64) (hy : Stable x y) (hiq : y.regs cursor ≤ x.regs limit)
      (ho : y.regs one = 1) (hz : y.regs zero = 0) (htwo : y.regs two = 2)
      (hp : (y.regs cursor).Prime) :
      ∃ z, ExecWithin (w + 2) query y z T ∧ Stable x z ∧
        z.regs good = (if A (y.regs cursor) then 1 else 0) ∧
        ∀ i, Control i → z.regs i = y.regs i := by
    let M := x.regs factor * y.regs cursor
    have hM : 0 < M := Nat.mul_pos hfactor hp.pos
    have hMle : M ≤ x.regs factor * x.regs limit := Nat.mul_le_mul_left _ hiq
    have hMf : GenericRAM.Signed.Fits w (M : ℤ) := by
      refine ⟨hmod.1, ?_, lt_of_le_of_lt (by exact_mod_cast hMle) hmod.2.2⟩
      have hnonneg : (0 : ℤ) ≤ M := Nat.cast_nonneg _
      have hpower : (0 : ℤ) ≤ 2 ^ (w - 1) := by positivity
      omega
    have henc : encode (M : ℤ) = 2 * M := by simp [encode]
    have hencoded : Fits (w + 2) (2 * M) := by
      rw [← henc]
      exact (encode_fits hMf).mono (by omega)
    have hraw : Fits (w + 2) M := hencoded.of_le (by omega)
    have hyf : y.regs factor = x.regs factor := hy.1 _ (by decide)
    let u := (y.set rawModulus M).set modulus (2 * M)
    have hprep : ExecWithin (w + 2)
        (ram[ rawModulus ← factor * cursor; modulus ← rawModulus * two ]) y u 2 := by
      ram_eval [u, M, hyf, htwo, hraw, hencoded, rawModulus, modulus, factor, cursor, two,
        CountCall.modulus, Fin.mk.injEq, Nat.mul_comm]
    have huc (i : Fin 64) (hi : Control i) : u.regs i = y.regs i := by
      have hr : i ≠ rawModulus := by intro h; subst i; norm_num [Control, rawModulus] at hi
      have hm : i ≠ modulus := by
        intro h; subst i; norm_num [Control, modulus, CountCall.modulus] at hi
      simp only [u, Data.set_regs, Function.update_of_ne hr, Function.update_of_ne hm]
    have huf (i : Fin 64) (hi : Fixed i) : u.regs i = x.regs i :=
      (huc i (by unfold Control Fixed at *; omega)).trans (hy.1 i hi)
    have hlen (j : Fin 3) : u.regs (CountCall.length j) = x.regs (CountCall.length j) :=
      huf _ (by dsimp [CountCall.length, Fixed]; omega)
    have hsrc (j : Fin 3) : u.regs (CountCall.source j) = x.regs (CountCall.source j) :=
      huf _ (by dsimp [CountCall.source, Fixed]; omega)
    have hscratch : u.regs CountCall.scratch = x.regs CountCall.scratch := huf _ (by decide)
    have hhist : u.regs CountCall.histogram = x.regs CountCall.histogram := huf _ (by decide)
    have hcard : u.regs CollisionTest.card = x.regs CollisionTest.card := huf _ (by decide)
    have hcut (j : Fin 3) : u.regs (CollisionTest.threshold j) =
        x.regs (CollisionTest.threshold j) :=
      huf _ (by dsimp [Fixed, CollisionTest.threshold]; omega)
    have hmodreg : u.regs CountCall.modulus = encode (M : ℤ) := by
      simpa only [henc] using (show u.regs modulus = 2 * M from by simp [u])
    have huinput : ∀ j i, i < u.regs (CountCall.length j) →
        u.mem (u.regs (CountCall.source j) + i) = encode (values j i) := by
      intro j i hi
      rw [hlen] at hi
      change y.mem (u.regs (CountCall.source j) + i) = _
      rw [hsrc, hy.2 _ (by have := hsk j; omega)]
      exact hinput j i hi
    obtain ⟨z, he, hgood, hreg, hmem⟩ := Query.exec u values hM hMf hmodreg
      (by simpa only [hlen] using hvalues) (by simpa only [hsrc, hlen] using hs)
      (by simpa only [hscratch, hlen] using hk)
      (by rw [hhist]; exact hd.of_le (Nat.add_le_add_left hMle _))
      (by simpa only [hlen] using ht) (by simpa only [hlen, hcard] using hproduct)
      ((huc zero (by decide)).trans hz)
      (by simpa only [hsrc, hlen, hscratch] using hsk)
      (by simpa only [hscratch, hlen, hhist] using hkd) huinput
      (by simpa only [hlen] using hinj)
    have hcontrol (i : Fin 64) (hi : Control i) : z.regs i = y.regs i := by
      have hscl : i ≠ CollisionTest.scaled := by
        intro h; subst i; norm_num [Control, CollisionTest.scaled] at hi
      have hg : i ≠ CollisionTest.good := by
        intro h; subst i; norm_num [Control, CollisionTest.good] at hi
      exact (hreg i (by unfold Control at hi; omega) hscl hg).trans (huc i hi)
    refine ⟨z, (hprep.seq he).mono ?_, ?_, ?_, hcontrol⟩
    · dsimp only [T]
      rw [hlen 0, hlen 1, hlen 2]
      have := Nat.mul_le_mul_left 15 hMle
      omega
    · refine ⟨fun i hi => (hcontrol i (by unfold Fixed Control at *; omega)).trans
          (hy.1 i hi), ?_⟩
      intro a ha
      rw [hmem a (by simpa only [hscratch] using ha)]
      exact hy.2 a ha
    · have hA : A (y.regs cursor) ↔
          coll ((Finset.range (x.regs (CountCall.length 0))).image (values 0)) M *
            x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 0) ∧
          coll ((Finset.range (x.regs (CountCall.length 1))).image (values 1)) M *
            x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 1) ∧
          coll ((Finset.range (x.regs (CountCall.length 2))).image (values 2)) M *
            x.regs CollisionTest.card ≤ x.regs (CollisionTest.threshold 2) := by
        constructor
        · intro h; exact ⟨h 0, h 1, h 2⟩
        · intro h j
          fin_cases j
          · exact h.1
          · exact h.2.1
          · exact h.2.2
      simpa only [hlen, hcard, hcut, ← hA] using hgood
  obtain ⟨y, he, hs, ha⟩ := exec_driver x A hfit haddr hbefore hbitmap hquery
  refine ⟨y, he.mono ?_, hs.1, hs.2, ha⟩
  dsimp only [T]
  have hcost : 34 * (x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
      x.regs (CountCall.length 2)) + 15 * (x.regs factor * x.regs limit) + 87 + 15 =
      34 * (x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
        x.regs (CountCall.length 2)) + 15 * (x.regs factor * x.regs limit) + 102 := by omega
  rw [hcost]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Search
