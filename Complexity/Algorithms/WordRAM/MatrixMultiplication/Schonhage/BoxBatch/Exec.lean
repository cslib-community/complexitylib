/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Program

/-!
# Correctness and charged execution of a native sparse-query batch

The original wanted codes lie below the retained table's end, and answers lie above
the query stack. Each query preserves both the original codes and all earlier answers.
The bound sums actual sparse query allowances and charges six further instructions per
wanted code, plus two for final loop exit. Empty lists execute only that exit.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Persistent ordinary arguments of the reused tile; no execution or resource fields. -/
structure Arguments (L t AA BB D V K : ℕ) (x : Data registers) : Prop where
  /-- Original encoding depth. -/
  levels : x.regs BoxTable.Reg.levels = L
  /-- Original sparse threshold. -/
  threshold : x.regs BoxTable.Reg.threshold = t
  /-- Actual encoding-array length. -/
  span : x.regs BoxTable.Reg.span = 10 ^ L
  /-- Actual left array base. -/
  arrayA : x.regs BoxTable.Reg.arrayA = AA
  /-- Actual right array base. -/
  arrayB : x.regs BoxTable.Reg.arrayB = BB
  /-- Shared directory base. -/
  directory : x.regs BoxTable.Reg.directory = D
  /-- Retained signed value-table base. -/
  values : x.regs BoxTable.Reg.values = V
  /-- Actual compact box count. -/
  count : x.regs BoxTable.Reg.count = K

/-- The actual native batch charge, including every load, store, cursor increment and loop test. -/
@[expose] def queryTime {L : ℕ} (m t : ℕ) (qs : List (OutStr L)) : ℕ :=
  (qs.map fun η => BoxQuery.queryTime m t η + 6).sum + 2

/-- Original addresses cover the reused kernel, batch cursors and their one-past-end values. -/
@[expose] def addressBound (L t AA BB D V K Q O N : ℕ) : ℕ :=
  BoxQuery.queryAddressBound L t AA BB D V K + Q + O + 2 * N + 1

private theorem exec_finish {w Q O Z : ℕ} (x : Data registers)
    (hQ : x.regs Reg.next = Q) (hO : x.regs Reg.output = O)
    (hZ : x.regs BoxQuery.Reg.answer = Z) (h1 : x.regs BoxTable.Reg.one = 1)
    (hfQ : Fits w (Q + 1)) (hfO : Fits w (O + 1)) :
    ∃ y, ExecWithin w finishQuery x y 3 ∧
      y.regs Reg.next = Q + 1 ∧ y.regs Reg.output = O + 1 ∧
      y.mem = Function.update x.mem O Z := by
  let y := ((x.write O Z).set Reg.next (Q + 1)).set Reg.output (O + 1)
  have he : ExecWithin w finishQuery x y 3 := by
    ram_eval [finishQuery, y, hQ, hO, hZ, h1, hfQ, hfO,
      Reg.next, Reg.output, BoxQuery.Reg.answer, BoxTable.Reg.one, Fin.mk.injEq]
  exact ⟨y, he, by simp [y, Reg.next, Reg.output], by simp [y], rfl⟩

/-- Execute all wanted codes against one actual retained table. The input list may be
empty or contain duplicates. The same final memory stores every answer in order and
preserves source/table readback and all words outside the stack and output intervals. -/
theorem exec_queryProgram {w L m t AA BB D V K A B Q O : ℕ}
    (qs : List (OutStr L)) (x : Data registers) (hx : Arguments L t AA BB D V K x)
    (hnext : x.regs Reg.next = Q) (hstop : x.regs Reg.stop = Q + qs.length)
    (hout : x.regs Reg.output = O)
    (a b : Leaf L → ℤ) (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hη : ∀ η ∈ qs, (innerSetO η).card = m)
    (hcodes : ∀ i : Fin qs.length, x.mem (Q + i.val) = (PrunedQuery.queryIndex (qs.get i)).val)
    (hK : K = (boxes L m t).card)
    (hAA : AA + 10 ^ L ≤ V + K) (hBB : BB + 10 ^ L ≤ V + K)
    (hDir : D + (m - t + 1) * 10 ^ L ≤ V + K)
    (hQ : Q + qs.length ≤ V + K)
    (hO : V + K + 5 * BoxQuery.stackCapacity L ≤ O)
    (hread : BoxQuery.Readback m t D V AA BB a b x.mem)
    (hfit : Fits (w + 2) (addressBound L t AA BB D V K Q O qs.length))
    (hmag : GenericRAM.Signed.Fits w (BoxQuery.magnitudeBound L A B : ℕ)) :
    ∃ y, ExecWithin (w + 2) queryProgram x y (queryTime m t qs) ∧
      Arguments L t AA BB D V K y ∧ y.regs Reg.next = Q + qs.length ∧
      y.regs Reg.stop = Q + qs.length ∧ y.regs Reg.output = O + qs.length ∧
      (∀ i : Fin qs.length, y.mem (O + i.val) =
        Signed.encode (BoxQuery.queryValue m t (qs.get i) a b)) ∧
      BoxQuery.Readback m t D V AA BB a b y.mem ∧
      (∀ p, ¬((V + K ≤ p ∧ p < V + K + 5 * BoxQuery.stackCapacity L) ∨
        (O ≤ p ∧ p < O + qs.length)) → y.mem p = x.mem p) := by
  induction qs generalizing x Q O with
  | nil =>
    refine ⟨x, ?_, hx, ?_, hstop, ?_, ?_, hread, ?_⟩
    · exact ExecWithin.loop_exit (by simp [Cond.Holds, hnext, hstop])
    · simpa using hnext
    · simpa using hout
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => rfl
  | cons η qs ih =>
    have hfQ : Fits (w + 2) (Q + 1) := hfit.of_le (by
      unfold addressBound
      simp only [List.length_cons]
      omega)
    have hfO : Fits (w + 2) (O + 1) := hfit.of_le (by unfold addressBound; omega)
    have hload : x.mem Q = (PrunedQuery.queryIndex η).val := by
      simpa using hcodes ⟨0, by simp⟩
    let u := x.set BoxQuery.Reg.query (PrunedQuery.queryIndex η).val
    have hu : ExecWithin (w + 2) loadQuery x u 1 := by
      ram_eval [loadQuery, u, hnext, hload]
    have ux : Arguments L t AA BB D V K u := by
      rcases hx with ⟨hL, ht, hT, hA, hB, hD, hV, hC⟩
      exact ⟨(hu.regs_eq (by decide)).trans hL, (hu.regs_eq (by decide)).trans ht,
        (hu.regs_eq (by decide)).trans hT, (hu.regs_eq (by decide)).trans hA,
        (hu.regs_eq (by decide)).trans hB, (hu.regs_eq (by decide)).trans hD,
        (hu.regs_eq (by decide)).trans hV, (hu.regs_eq (by decide)).trans hC⟩
    obtain ⟨v, hv, vp, _, va, vr, vf⟩ := BoxQuery.exec_queryProgram u η
      (hη η (by simp)) a b ha hb ux.levels ux.threshold ux.span
      (by simp [u]) ux.arrayA ux.arrayB ux.directory ux.values ux.count hK hAA hBB hDir
      hread (hfit.of_le (by unfold addressBound; omega)) hmag
    have vn : v.regs Reg.next = Q :=
      (hv.regs_eq query_preserves.1).trans ((hu.regs_eq (by decide)).trans hnext)
    have vo : v.regs Reg.output = O :=
      (hv.regs_eq query_preserves.2.2).trans ((hu.regs_eq (by decide)).trans hout)
    have vs : v.regs Reg.stop = Q + (η :: qs).length :=
      (hv.regs_eq query_preserves.2.1).trans ((hu.regs_eq (by decide)).trans hstop)
    obtain ⟨z, hz, zn, zo, zm⟩ := exec_finish v vn vo va vp.one hfQ hfO
    have zx : Arguments L t AA BB D V K z := by
      exact ⟨(hz.regs_eq (by decide)).trans vp.levels,
        (hz.regs_eq (by decide)).trans vp.threshold,
        (hz.regs_eq (by decide)).trans vp.span,
        (hz.regs_eq (by decide)).trans vp.arrayA,
        (hz.regs_eq (by decide)).trans vp.arrayB,
        (hz.regs_eq (by decide)).trans vp.directory,
        (hz.regs_eq (by decide)).trans vp.values,
        (hz.regs_eq (by decide)).trans vp.count⟩
    have zs : z.regs Reg.stop = (Q + 1) + qs.length := by
      rw [hz.regs_eq (by decide), vs]
      simp only [List.length_cons]
      omega
    have zframe (p : ℕ) (hp : ¬((V + K ≤ p ∧
        p < V + K + 5 * BoxQuery.stackCapacity L) ∨ p = O)) : z.mem p = x.mem p := by
      rw [zm, Function.update_of_ne (by omega : p ≠ O), vf p (by omega)]
      rfl
    have zr : BoxQuery.Readback m t D V AA BB a b z.mem :=
      vr.transport hAA hBB hDir (by rw [hK]) (fun p hp => by
        rw [zm, Function.update_of_ne (by omega : p ≠ O)])
    have zcodes (i : Fin qs.length) : z.mem (Q + 1 + i.val) =
        (PrunedQuery.queryIndex (qs.get i)).val := by
      rw [zframe _ (by have := i.isLt; simp only [List.length_cons] at hQ; omega)]
      simpa only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hcodes ⟨i.val + 1, by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using i.isLt⟩
    have zfit : Fits (w + 2) (addressBound L t AA BB D V K (Q + 1) (O + 1) qs.length) := by
      exact hfit.of_le (by unfold addressBound; simp only [List.length_cons]; omega)
    obtain ⟨y, hy, yx, yn, ys, yo, yanswers, yr, yf⟩ := ih z zx zn zs zo
      (by intro η h; exact hη η (by simp [h])) zcodes (by simp only [List.length_cons] at hQ; omega)
      (by omega) zr zfit
    refine ⟨y, ?_, yx, ?_, ?_, ?_, ?_, yr, ?_⟩
    · have hbdy : ExecWithin (w + 2) body x z (BoxQuery.queryTime m t η + 4) := by
        exact (hu.seq (hv.seq hz)).mono (by omega)
      have he := ExecWithin.loop_iter
        (show (Cond.lt Reg.next Reg.stop).Holds x from by
          simp only [Cond.Holds, hnext, hstop, List.length_cons]; omega) hbdy hy
      exact he.mono (by simp only [queryTime, List.map_cons, List.sum_cons]; omega)
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yn
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ys
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yo
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change y.mem (O + 0) = Signed.encode (BoxQuery.queryValue m t η a b)
        rw [Nat.add_zero, yf O (by omega), zm, Function.update_self]
      · simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yanswers j
    · intro p hp
      rw [yf p (by simp only [List.length_cons] at hp ⊢; omega),
        zframe p (by simp only [List.length_cons] at hp ⊢; omega)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
