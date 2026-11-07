/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Setup
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Readback
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Exec
import all Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Exec

/-!
# Pointer-gather product core

External matrix and interleaved-occurrence words are physically gathered into the computed
snapshot. The low matrix/query payload need not be initialized. Source continuation premises
come from the actual gather, and every native and translated phase is charged.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open CallableProduct

/-- Setup, source layout, native gather, and the remaining translated source instructions. -/
@[expose] def coreTime (m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) : ℕ :=
  517 * Nat.clog 2 (N + qs.length + 3) + 184 + 3 * PointerInput.prefixTime (21 * m) +
    gatherTime (N * D m) qs.length + 3 * BoxProduct.snapshotTimeBound (21 * m) m t qs

/-- Execute the genuine pointer front, including all source work after the removed copy. -/
theorem exec_core {W b m t N s r q : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 173)
    (hb : x.regs Reg.base = b) (hs : x.regs Reg.left = s)
    (hr : x.regs Reg.right = r) (hq : x.regs Reg.queries = q)
    (hheader : ∀ a < 5, x.mem (b + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a)
    (hthreshold : x.mem (b + QueriedProduct.inputEnd m N qs.length) = t)
    (hsb : s + N * D m ≤ b) (hrb : r + N * D m ≤ b) (hqb : q + 2 * qs.length ≤ b)
    (hleft : ∀ a < N * D m, x.mem (s + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem (5 + a))
    (hright : ∀ a < N * D m, x.mem (r + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
        (5 + N * D m + a))
    (hqueries : ∀ a < 2 * qs.length, x.mem (q + a) =
      (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
        (5 + 2 * (N * D m) + a))
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (ht : t ≤ m) (hN : D m ^ 18 ≤ N)
    (hfit : Fits W (2 * b + 4 * windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W core x y (coreTime m t qs) ∧
      y.regs Reg.base = b ∧
      y.regs (callableBank CallableProduct.Reg.modulus) = windowSize N qs.length ∧
      y.regs (sourceBank QueriedProduct.Reg.inputSize) = QueriedProduct.inputEnd m N qs.length ∧
      y.regs (sourceBank QueriedProduct.Reg.queryCount) = qs.length ∧
      y.regs (sourceBank QueriedProduct.Reg.output) =
        QueriedProduct.outputBase (21 * m) m N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (21 * m) m N qs.length + i.val)) %
          windowSize N qs.length = Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a < QueriedProduct.inputEnd m N qs.length + 1,
        y.mem (b + a) % windowSize N qs.length =
          (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a) ∧
      (∀ a, a < b ∨ b + windowSize N qs.length ≤ a → y.mem a = x.mem a) := by
  let original :=
    (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem
  have hsource (a : ℕ) (ha : 0 < a) (ha' : a < QueriedProduct.inputEnd m N qs.length) :
      original a =
        (State.init (QueriedProduct.input true (21 * m) X Y qs) : State 160).data.mem a :=
    BoxProduct.input_prefix true X Y qs a ha ha'
  have hXabs (i k) : |X i k| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hX i k).1]; exact (hX i k).2
  have hYabs (k j) : |Y k j| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hY k j).1]; exact (hY k j).2
  obtain ⟨hw, hmag, hbudget⟩ := CallableBoxProduct.source_admission (Q := qs.length) ht hN
  have htwo : sourceWidth N qs.length - 2 + 2 = sourceWidth N qs.length := by omega
  have hbudget' : Fits (sourceWidth N qs.length - 2 + 2)
      (BoxProduct.wordBudget (21 * m) m t N qs.length) := by simpa only [htwo] using hbudget
  have hi := BoxProduct.input_fits hw (show m ≤ 21 * m by omega) true X Y qs
    hXabs hYabs hmag hbudget'
  have hi' : (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.Bounded
      (sourceWidth N qs.length) := by
    simpa only [htwo, State.init] using (Data.Bounded.init (r := 160) hi)
  have head (a : ℕ) (ha : 0 < a) (ha5 : a < 5) :
      x.mem (b + a) = (State.init (QueriedProduct.input true (21 * m) X Y qs) :
        State 160).data.mem a :=
    (hheader a ha5).trans (hsource a ha (by unfold QueriedProduct.inputEnd; omega))
  obtain ⟨u, hu, up, ut, ub, uM, ubound, um, uf⟩ := exec_setupLayout x hb
    (by rw [head 1 (by decide) (by decide)]; rfl)
    (by rw [head 2 (by decide) (by decide)]; rfl)
    (by rw [head 3 (by decide) (by decide)]; rfl)
    (by rw [head 4 (by decide) (by decide)]; rfl)
    hthreshold ht hN (hfit.of_le (by omega))
  have hphysical : Fits W (b + 4 * windowSize N qs.length + 1024) := hfit.of_le (by omega)
  have hspan : QueriedProduct.snapshotBase (21 * m) m N qs.length +
      QueriedProduct.inputEnd m N qs.length < windowSize N qs.length := by
    have hsnap : QueriedProduct.snapshotBase (21 * m) m N qs.length +
        QueriedProduct.inputEnd m N qs.length ≤
          QueriedProduct.outputBase (21 * m) m N qs.length := by
      unfold QueriedProduct.outputBase QueriedProduct.groupedBase QueriedProduct.originalBase
        QueriedProduct.codeBase QueriedProduct.offsetBase
      omega
    have hspans := (CallableBoxProduct.spans_le_budget (21 * m) m t N qs.length).2
    exact (hsnap.trans (by omega)).trans_lt hbudget
  have hS : 5 ≤ QueriedProduct.snapshotBase (21 * m) m N qs.length := by
    unfold QueriedProduct.snapshotBase QueriedProduct.inputEnd; omega
  obtain ⟨g, hg, gm, gf⟩ := exec_gather u ub up.snapshot up.matrixWords up.queryCount
    up.two up.five ((uf _ (by decide)).trans hs) ((uf _ (by decide)).trans hr)
    ((uf _ (by decide)).trans hq) hS hsb hrb hqb (hfit.of_le (by
      unfold QueriedProduct.inputEnd at hspan; omega))
  have gb : g.regs Reg.base = b := (gf _ (by decide)).trans ub
  have gM : g.regs (callableBank CallableProduct.Reg.modulus) = windowSize N qs.length :=
    (gf _ (by decide)).trans uM
  have gvbound : (view (sourceWidth N qs.length) b g).Bounded (sourceWidth N qs.length) := by
    constructor
    · intro i
      change g.regs (sourceBank i) < _
      rw [gf _ (by change i.val < 166; omega)]
      exact ubound.1 i
    · intro a
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have gp : QueriedProduct.Parameters (21 * m) m N qs.length
      (view (sourceWidth N qs.length) b g) :=
    up.of_frame (fun i _ => gf (sourceBank i) (by change i.val < 166; omega))
  have gt : (view (sourceWidth N qs.length) b g).regs BoxProduct.Reg.threshold = t :=
    (gf _ (by decide)).trans ut
  have gframe (a : ℕ) (ha : a < b ∨ b + windowSize N qs.length ≤ a) : g.mem a = x.mem a := by
    rw [gm, gatherMemory_outside _ _ _ _ _ _ _ _ _ (by
      unfold QueriedProduct.inputEnd at hspan; omega), um]
  have gsnapshot (a : ℕ) (ha : a < QueriedProduct.inputEnd m N qs.length) :
      (view (sourceWidth N qs.length) b g).mem
        (QueriedProduct.snapshotBase (21 * m) m N qs.length + a) = original a := by
    change g.mem (b + (_ + a)) % _ = _
    rw [gm, ← Nat.add_assoc b]
    rw [gatherMemory_readback u.mem original b _ (N * D m) qs.length s r q hS hsb hrb hqb
      (by intro j hj; rw [um]; exact hheader j hj)
      (by intro j hj; rw [um]; exact hleft j hj)
      (by intro j hj; rw [um]; exact hright j hj)
      (by intro j hj; rw [um]; exact hqueries j hj) a ha,
      Nat.mod_eq_of_lt (hi'.2 a)]
  have gheader (a : ℕ) (ha : 0 < a) (ha5 : a < 5) :
      (view (sourceWidth N qs.length) b g).mem a =
        (State.init (QueriedProduct.input true (21 * m) X Y qs) : State 160).data.mem a := by
    change g.mem (b + a) % _ = _
    rw [gm, gatherMemory_outside _ _ _ _ _ _ _ _ _ (Or.inl (by omega)), um,
      hheader a ha5, Nat.mod_eq_of_lt (hi'.2 a)]
    exact hsource a ha (by unfold QueriedProduct.inputEnd; omega)
  obtain ⟨p, hp, pp, _, pv, pi, pt, _⟩ := BoxProduct.exec_fromSnapshot hw (show m ≤ 21 * m by omega)
    ht true X Y qs original (view (sourceWidth N qs.length) b g) hsource gp gt gheader gsnapshot
    hXabs hYabs (fun _ => ⟨fun i k => (hX i k).1, fun k j => (hY k j).1⟩) hmag hbudget'
  have hp' : ExecWithin (sourceWidth N qs.length) (BoxProduct.programFromSnapshot true)
      (view (sourceWidth N qs.length) b g) p (BoxProduct.snapshotTimeBound (21 * m) m t qs) := by
    simpa only [htwo] using hp
  obtain ⟨y, hy, ym, yf, _⟩ := exec_source hp' (by decide) gvbound g
    ⟨rfl, gb, gM⟩ (setup_fits hphysical).1
    (hfit.of_le (by change b + windowSize N qs.length ≤ _; omega))
  refine ⟨y, (hu.seq (hg.seq hy)).mono (by unfold coreTime; omega),
    ym.base_eq, ym.modulus_eq, ym.regs _ |>.trans pp.inputSize,
    ym.regs _ |>.trans pp.queryCount, ym.regs _ |>.trans pp.output, ?_, ?_, ?_⟩
  · intro i
    exact (ym.mem _).trans (pv i)
  · intro a ha
    have yread : y.mem (b + a) % windowSize N qs.length = p.mem a := ym.mem a
    rw [yread]
    by_cases hai : a < QueriedProduct.inputEnd m N qs.length
    · exact pi a hai
    · have heq : a = QueriedProduct.inputEnd m N qs.length := by omega
      subst a
      exact pt.trans (BoxProduct.input_threshold true X Y qs).symm
  · intro a ha
    exact (yf a ha).trans (gframe a ha)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct
