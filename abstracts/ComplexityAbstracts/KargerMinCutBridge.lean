/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import Complexity.Algorithms.WordRAM.KargerMinCut
import Complexity.Algorithms.WordRAM.KargerStein
import ComplexityAbstracts.RandomizedWordRAMBridge

/-!
# Bridge for Karger and Karger–Stein randomized global minimum cut formal abstract

`KargerMinCutAbstract.lean` states the randomized word-RAM model (`AluOp`, `Instr`, `Comp`, `State`,
`Cfg`, `stepRand`, `runRand`, `evalRand`, `HaltsWithin`, `RandCallsBounded`), weighted undirected
multigraphs and global minimum cuts (`IsMultigraph`, `IsNonTrivialCut`, `cutWeight`,
`totalDoubledWeight`, `minCut`, `flattenMatrix`), the three Karger (1993) endpoints
(`kargerSingleTrial`, `kargerAmplified`, `kargerHighProb`), and the two Karger–Stein (1996)
recursive `FastCut` endpoints (`kargerSteinFastCut`, `kargerSteinHighProb`) from scratch.

This bridge establishes two facts without duplicating the randomized word-RAM presentation
correspondence in `RandomizedWordRAMBridge`:

1. **Lifting `singleCode`, `amplifiedCode`, `highProbCode`, `fastCutCode`, and
   `fastCutHighProbCode` from `Basis.standard` to `Basis.exact`:**
   None of the five programs uses `.div` or `.mod`, and every reached `.sub` instruction satisfies
   `b ≤ a` (loop guards `val1 < rem` in `uScan`/`vScan`, degree bounds `2 * W u v ≤ totS` and
   `W u v ≤ rowDeg W` in `phaseADegrees`, active vertex count `1 ≤ m + 1` in `postRandStep` and
   `contractStep`, positive total weight `1 ≤ totS` before `rand`, `1 ≤ n` in `highProbSetup`,
   `1 ≤ k` in `thresholdPre`, and stack depth `1 ≤ b + 1` on frame pops in `basePost` and
   `combineAndPop`). Therefore `toExactCode` preserves the structured `ProbComp` execution tree `m`
   identically, and `runRand` over `Basis.exact` equals `runRand` over `Basis.standard`.
2. **Polymorphic transport across `RandomizedWordRAMBridge.Presentation`:**
   Reusing `RandomizedWordRAMBridge.Presentation.{programOf, evalRand_eq, haltsWithin_iff,
   randCallsBounded_iff}`, the five `Basis.exact` specifications transport directly to any
   self-contained presentation `S` satisfying `RandomizedWordRAMBridge.Laws S`.
-/

namespace ComplexityAbstracts.KargerMinCutBridge

open scoped ENNReal
open Cslib
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.Karger
open ComplexityAbstracts.RandomizedWordRAMBridge

/-! ## Row-major flattening equivalence -/

private theorem flatMap_finRange_length {n : ℕ} (W : Fin n → Fin n → ℕ) :
    ∀ us : List (Fin n),
      (us.flatMap fun u => (List.finRange n).map fun v => W u v).length = us.length * n
  | [] => by simp
  | u :: us => by
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_finRange,
      List.length_cons, flatMap_finRange_length W us]
    ring

private theorem flatMap_finRange_getElem {n : ℕ} (W : Fin n → Fin n → ℕ) :
    ∀ (us : List (Fin n)) (i : ℕ) (hi : i < us.length) (v : Fin n),
      (us.flatMap fun u => (List.finRange n).map fun b => W u b)[i * n + v.val]'(by
        rw [flatMap_finRange_length]
        nlinarith [v.isLt]) = W us[i] v
  | [], i, hi, _ => by simp at hi
  | a :: us, 0, _, v => by
    have hv : v.val < ((List.finRange n).map fun b => W a b).length := by simp [v.isLt]
    simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_append_left hv,
      List.getElem_map, List.getElem_finRange, List.getElem_cons_zero]
    exact congrArg (W a) (Fin.ext rfl)
  | a :: us, i + 1, hi, v => by
    have hi' : i < us.length := by simpa using hi
    have hge : ((List.finRange n).map fun b => W a b).length ≤ (i + 1) * n + v.val := by
      simp only [List.length_map, List.length_finRange]
      nlinarith
    have hsub : (i + 1) * n + v.val - n = i * n + v.val := by
      ring_nf
      omega
    simp only [List.flatMap_cons, List.getElem_append_right hge, List.length_map,
      List.length_finRange, List.getElem_cons_succ, hsub]
    exact flatMap_finRange_getElem W us i hi' v

/-- The `flatMap` row-major encoding in the abstract equals `Karger.flattenMatrix`. -/
theorem flatMap_finRange_eq_flattenMatrix {n : ℕ} (W : Fin n → Fin n → ℕ) :
    ((List.finRange n).flatMap fun u => (List.finRange n).map fun v => W u v) =
      flattenMatrix W := by
  refine List.ext_getElem ?_ fun idx h₁ h₂ => ?_
  · rw [flatMap_finRange_length, List.length_finRange, length_flattenMatrix]
  · rw [length_flattenMatrix] at h₂
    have hn : 0 < n := by
      by_contra h0
      have h0' : n = 0 := Nat.eq_zero_of_not_pos h0
      simp [h0'] at h₂
    let u : Fin n := ⟨idx / n, Nat.div_lt_of_lt_mul h₂⟩
    let v : Fin n := ⟨idx % n, Nat.mod_lt _ hn⟩
    have hidx : idx = u.val * n + v.val := by
      have hdm := Nat.div_add_mod idx n
      dsimp only [u, v]
      nlinarith
    have hu_lt : u.val < (List.finRange n).length := by simp [u.isLt]
    have h_lhs := flatMap_finRange_getElem W (List.finRange n) u.val hu_lt v
    have hu_eq : (List.finRange n)[u.val]'hu_lt = u := by
      simp only [List.getElem_finRange]
      exact Fin.ext rfl
    rw [hu_eq] at h_lhs
    have h_rhs := getElem_flattenMatrix W u v
    calc
      ((List.finRange n).flatMap fun a => (List.finRange n).map fun b => W a b)[idx]
        = ((List.finRange n).flatMap
            fun a => (List.finRange n).map fun b => W a b)[u.val * n + v.val]'(by
              rw [flatMap_finRange_length, List.length_finRange]
              nlinarith [u.isLt, v.isLt]) := by simp only [hidx]
      _ = W u v := h_lhs
      _ = (flattenMatrix W)[u.val * n + v.val]'(by
            rw [length_flattenMatrix]
            nlinarith [u.isLt, v.isLt]) := h_rhs.symm
      _ = (flattenMatrix W)[idx] := by simp only [hidx]

/-! ## General `Basis.standard` → `Basis.exact` lifting helpers -/

private theorem eval_toExactOp_of_noSubDivMod' {r w : ℕ} {o : Op .standard r} {x : Data r}
    (hno : noSubDivModOp o = true) :
    (toExactOp o).eval w x = o.eval w x := by
  cases o with
  | const d v | copy d s | load d a | store a s => rfl
  | alu f d args =>
    cases f with
    | width => rfl
    | bin g => cases g <;> first | contradiction | rfl

private theorem eval_toExactOp_sub {r w : ℕ} {d i j : Fin r} {x : Data r}
    (hle : x.regs j ≤ x.regs i) :
    (toExactOp (Op.bin .sub d i j)).eval w x = (Op.bin .sub d i j).eval w x := by
  change (Option.bind (BinOp.evalExact .sub (x.regs i) (x.regs j)) (x.put w d)) =
    x.put w d (BinOp.eval .sub (x.regs i) (x.regs j))
  simp [BinOp.evalExact, BinOp.eval, hle]

private theorem toExactOp_rename {r₁ r₂ : ℕ} (o : Op .standard r₁) (f : Fin r₁ → Fin r₂) :
    toExactOp (o.rename f) = (toExactOp o).rename f := by
  cases o <;> rfl

theorem toExactCode_rename {r₁ r₂ : ℕ} (c : Code .standard r₁) (f : Fin r₁ → Fin r₂) :
    toExactCode (c.rename f) = (toExactCode c).rename f := by
  induction c with
  | op o => exact congrArg Code.op (toExactOp_rename o f)
  | seq c₁ c₂ ih₁ ih₂ => simp only [Code.rename, toExactCode, ih₁, ih₂]
  | branch cond pos neg ih₁ ih₂ => simp only [Code.rename, toExactCode, ih₁, ih₂]
  | loop cond body ih => simp only [Code.rename, toExactCode, ih]
  | rand dst src => rfl

private abbrev exec_toExact_noSub := @RandomizedWordRAMBridge.Exec.toExact_of_noSubDivMod

private theorem set_regs_ne {r : ℕ} (x : Data r) (d reg : Fin r) (v : ℕ) (hne : reg ≠ d) :
    (x.set d v).regs reg = x.regs reg := by
  simp [Data.set, Function.update_of_ne hne]

private theorem exec_unique_std {r w : ℕ} {c : Code .standard r} {x y₁ y₂ : Data r} {n₁ n₂ : ℕ}
    (h₁ : Exec w c x y₁ n₁) (h₂ : Exec w c x y₂ n₂) : y₁ = y₂ ∧ n₁ = n₂ := by
  have heq : (pure (y₁, n₁) : ProbComp (Data r × ℕ)) = pure (y₂, n₂) :=
    h₁.execRand.unique h₂.execRand
  injection heq with hp
  exact Prod.ext_iff.mp hp

private def preservesReg {B : Basis} {r : ℕ} (reg : Fin r) : Code B r → Bool
  | .op (.const d _) | .op (.copy d _) | .op (.alu _ d _) | .op (.load d _) | .rand d _ =>
    d != reg
  | .op (.store _ _) => true
  | .seq c₁ c₂ | .branch _ c₁ c₂ => preservesReg reg c₁ && preservesReg reg c₂
  | .loop _ body => preservesReg reg body

private theorem op_regs_eq_of_ne {B : Basis} {r w : ℕ} {o : Op B r} {x y : Data r} {reg : Fin r}
    (ho : o.eval w x = some y) (hp : preservesReg reg (Code.op o) = true) :
    y.regs reg = x.regs reg := by
  cases o with
  | store a s => cases ho; rfl
  | copy d s | load d a =>
    have hne : d ≠ reg := by simpa [preservesReg] using hp
    cases ho
    simp [Data.set, Function.update_of_ne hne.symm]
  | const d v =>
    have hne : d ≠ reg := by simpa [preservesReg] using hp
    simp only [Op.eval, Data.put] at ho
    split_ifs at ho with hf
    cases ho
    simp [Data.set, Function.update_of_ne hne.symm]
  | alu f d args =>
    have hne : d ≠ reg := by simpa [preservesReg] using hp
    simp only [Op.eval] at ho
    cases hi : B.interp w f (x.regs ∘ args) with
    | none => simp [hi] at ho
    | some val =>
      rw [hi] at ho
      dsimp only [bind, Option.bind, Data.put] at ho
      split_ifs at ho with hf
      cases ho
      simp [Data.set, Function.update_of_ne hne.symm]

private theorem exec_regs_eq_of_preserves {B : Basis} {r w : ℕ} {c : Code B r} {x y : Data r}
    {n : ℕ} {reg : Fin r} (h : Exec w c x y n) (hp : preservesReg reg c = true) :
    y.regs reg = x.regs reg := by
  induction h with
  | op ho => exact op_regs_eq_of_ne ho hp
  | seq _ _ ih₁ ih₂ =>
    rw [preservesReg, Bool.and_eq_true] at hp
    exact (ih₂ hp.2).trans (ih₁ hp.1)
  | branch_pos _ _ ih =>
    rw [preservesReg, Bool.and_eq_true] at hp
    exact ih hp.1
  | branch_neg _ _ ih =>
    rw [preservesReg, Bool.and_eq_true] at hp
    exact ih hp.2
  | loop_exit _ => rfl
  | loop_iter _ _ _ ihb ihl => exact (ihl hp).trans (ihb hp)

private theorem op_eval_bin_eq {r w : ℕ} {g : BinOp} {d i j : Fin r} {x z : Data r}
    (ho : (Op.bin g d i j).eval w x = some z) :
    z = x.set d (BinOp.eval g (x.regs i) (x.regs j)) := by
  simp only [Op.eval_bin, Data.put] at ho
  split_ifs at ho
  cases ho
  rfl

private theorem op_eval_const_eq {r w : ℕ} {d : Fin r} {c : ℕ} {x z : Data r}
    (ho : (Op.const (B := .standard) d c).eval w x = some z) :
    z = x.set d c := by
  simp only [Op.eval, Data.put] at ho
  split_ifs at ho
  cases ho
  rfl

private theorem exec_op_sub_toExact {r w : ℕ} {d i j : Fin r} {x y : Data r} {n : ℕ}
    (hle : x.regs j ≤ x.regs i) (h : Exec w (.op (.bin .sub d i j)) x y n) :
    Exec w (toExactCode (.op (.bin .sub d i j))) x y n ∧ y = x.set d (x.regs i - x.regs j) := by
  cases h with
  | op ho =>
    exact ⟨.op (by rwa [eval_toExactOp_sub hle]), op_eval_bin_eq ho⟩

private theorem exec_seq_op_sub {r w : ℕ} {d i j : Fin r} {rest : Code .standard r}
    {x y : Data r} {n : ℕ} (hle : x.regs j ≤ x.regs i)
    (h : Exec w (.seq (.op (.bin .sub d i j)) rest) x y n)
    (hrest : ∀ m, Exec w rest (x.set d (x.regs i - x.regs j)) y m →
      Exec w (toExactCode rest) (x.set d (x.regs i - x.regs j)) y m) :
    Exec w (toExactCode (.seq (.op (.bin .sub d i j)) rest)) x y n := by
  cases h with
  | seq h₁ h₂ =>
    obtain ⟨h₁', rfl⟩ := exec_op_sub_toExact hle h₁
    exact .seq h₁' (hrest _ h₂)

private theorem exec_seq_op_noSub {r w : ℕ} {o : Op .standard r} {rest : Code .standard r}
    {x y : Data r} {n : ℕ} (hno : noSubDivModOp o = true)
    (h : Exec w (.seq (.op o) rest) x y n)
    (hrest : ∀ z m, o.eval w x = some z → Exec w rest z y m → Exec w (toExactCode rest) z y m) :
    Exec w (toExactCode (.seq (.op o) rest)) x y n := by
  cases h with
  | seq h₁ h₂ =>
    cases h₁ with
    | op ho =>
      exact .seq (.op (by rwa [eval_toExactOp_of_noSubDivMod' hno])) (hrest _ _ ho h₂)

private theorem loop_sub_first_toExact {r w : ℕ} {d i j : Fin r} {rest : Code .standard r}
    {x y : Data r} {n : ℕ} (hrest : noSubDivMod rest = true)
    (h : Exec w (.loop (.lt j i) (.seq (.op (.bin .sub d i j)) rest)) x y n) :
    Exec w (toExactCode (.loop (.lt j i) (.seq (.op (.bin .sub d i j)) rest))) x y n := by
  generalize hc_eq : Code.loop (.lt j i) (.seq (.op (.bin .sub d i j)) rest) = c at h
  induction h with
  | op _ | seq _ _ | branch_pos _ _ | branch_neg _ _ => cases hc_eq
  | loop_exit hc =>
    cases hc_eq
    exact .loop_exit hc
  | loop_iter hc hb _ _ ihl =>
    cases hc_eq
    have hlt : _ < _ := hc
    have hb_ex := exec_seq_op_sub (Nat.le_of_lt hlt) hb fun _ hr => exec_toExact_noSub hr hrest
    exact .loop_iter hc hb_ex (ihl rfl)

/-! ## Lifting `uScan`, `vScan`, `phaseADegrees`, `postRandStep`, and `contractDownTo` -/

section ContractLift

open Reg

private theorem uScan_toExact {w : ℕ} {x y : Data 16} {n : ℕ} (h : Exec w uScan x y n) :
    Exec w (toExactCode uScan) x y n := by
  unfold uScan uScanBody at h ⊢
  refine exec_seq_op_noSub rfl h fun z₁ _ _ h₁ => ?_
  refine exec_seq_op_noSub rfl h₁ fun z₂ _ _ h₂ => ?_
  refine exec_seq_op_noSub rfl h₂ fun z₃ _ _ h₃ => ?_
  refine exec_seq_op_noSub rfl h₃ fun z₄ _ _ h₄ => ?_
  exact loop_sub_first_toExact rfl h₄

private theorem vScan_toExact {w : ℕ} {x y : Data 16} {n : ℕ} (h : Exec w vScan x y n) :
    Exec w (toExactCode vScan) x y n := by
  unfold vScan vScanBody at h ⊢
  refine exec_seq_op_noSub rfl h fun z₁ _ _ h₁ => ?_
  refine exec_seq_op_noSub rfl h₁ fun z₂ _ _ h₂ => ?_
  refine exec_seq_op_noSub rfl h₂ fun z₃ _ _ h₃ => ?_
  refine exec_seq_op_noSub rfl h₃ fun z₄ _ _ h₄ => ?_
  refine exec_seq_op_noSub rfl h₄ fun z₅ _ _ h₅ => ?_
  exact loop_sub_first_toExact rfl h₅

private theorem phaseADegrees_toExact {w wb db str m : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x y : Data 16} {n : ℕ}
    (hW : IsMultigraph W) (huv : u ≠ v)
    (hdBase : x.regs dBase = db) (htotS : x.regs totS = totalDoubledWeight W)
    (huReg : x.regs uReg = u.val) (hvReg : x.regs vReg = v.val)
    (ha2 : x.regs addr2 = wb + u.val * str + v.val) (hv1 : x.regs val1 = W u v)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hdeg : ∀ i : Fin (m + 1), x.mem (db + i.val) = rowDeg W i)
    (h : Exec w phaseADegrees x y n) :
    Exec w (toExactCode phaseADegrees) x y n := by
  have h2w : 2 * W u v ≤ totalDoubledWeight W := by
    have hc := totalDoubledWeight_contractMatrix hW huv
    omega
  have hdu : W u v ≤ rowDeg W u := entry_le_rowDeg W u v
  have hdv : W u v ≤ rowDeg W v := hW.1 u v ▸ entry_le_rowDeg W v u
  unfold phaseADegrees at h ⊢
  refine exec_seq_op_sub (by rw [hv1, htotS]; omega) h fun _ h₁ => ?_
  set s₁ := x.set totS (x.regs totS - x.regs val1)
  have hs₁_v1 : s₁.regs val1 = W u v := (set_regs_ne _ _ _ _ (by decide)).trans hv1
  have hs₁_tot : s₁.regs totS = totalDoubledWeight W - W u v := by simp [s₁, htotS, hv1]
  refine exec_seq_op_sub (by rw [hs₁_v1, hs₁_tot]; omega) h₁ fun _ h₂ => ?_
  set s₂ := s₁.set totS (s₁.regs totS - s₁.regs val1)
  have hs₂_db : s₂.regs dBase = db :=
    (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans hdBase)
  have hs₂_u : s₂.regs uReg = u.val :=
    (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans huReg)
  have hs₂_v : s₂.regs vReg = v.val :=
    (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans hvReg)
  have hs₂_v1 : s₂.regs val1 = W u v := (set_regs_ne _ _ _ _ (by decide)).trans hs₁_v1
  refine exec_seq_op_noSub rfl h₂ fun s₃ _ ho₃ h₃ => ?_
  cases ho₃
  have hs₃_a2 : s₂.regs addr2 = wb + u.val * str + v.val :=
    (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans ha2)
  refine exec_seq_op_noSub rfl h₃ fun s₄ _ ho₄ h₄ => ?_
  obtain rfl := op_eval_bin_eq ho₄
  have hs₄_a2 : (s₂.write (s₂.regs addr2) (s₂.regs zero)).regs dBase +
      (s₂.write (s₂.regs addr2) (s₂.regs zero)).regs uReg = db + u.val := by
    change s₂.regs dBase + s₂.regs uReg = db + u.val
    omega
  refine exec_seq_op_noSub rfl h₄ fun s₅ _ ho₅ h₅ => ?_
  cases ho₅
  set s₄ := (s₂.write (s₂.regs addr2) (s₂.regs zero)).set addr2
    (BinOp.eval .add ((s₂.write (s₂.regs addr2) (s₂.regs zero)).regs dBase)
      ((s₂.write (s₂.regs addr2) (s₂.regs zero)).regs uReg))
  have hs₄_load : s₄.mem (s₄.regs addr2) = rowDeg W u := by
    have ha2' : s₄.regs addr2 = db + u.val := by simpa [s₄, BinOp.eval] using hs₄_a2
    rw [ha2']
    change (s₂.write (s₂.regs addr2) (s₂.regs zero)).mem (db + u.val) = rowDeg W u
    rw [Data.write_mem, hs₃_a2, Function.update_of_ne (matAddr_ne_degAddr hstr hdisj u v u).symm]
    exact hdeg u
  set s₅ := s₄.set val2 (s₄.mem (s₄.regs addr2))
  have hs₅_v1 : s₅.regs val1 = W u v :=
    (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans hs₂_v1)
  have hs₅_v2 : s₅.regs val2 = rowDeg W u := by simp [s₅, hs₄_load]
  refine exec_seq_op_sub (by rw [hs₅_v1, hs₅_v2]; exact hdu) h₅ fun _ h₆ => ?_
  set s₆ := s₅.set val2 (s₅.regs val2 - s₅.regs val1)
  refine exec_seq_op_noSub rfl h₆ fun s₇ _ ho₇ h₇ => ?_
  obtain rfl := op_eval_bin_eq ho₇
  have hs₇_a1 : s₆.regs dBase + s₆.regs vReg = db + v.val := by
    have hdb' : s₆.regs dBase = db :=
      (set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans hs₂_db))
    have hv' : s₆.regs vReg = v.val :=
      (set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans hs₂_v))
    omega
  refine exec_seq_op_noSub rfl h₇ fun s₈ _ ho₈ h₈ => ?_
  cases ho₈
  set s₇ := s₆.set addr1 (BinOp.eval .add (s₆.regs dBase) (s₆.regs vReg))
  have hs₇_load : s₇.mem (s₇.regs addr1) = rowDeg W v := by
    have ha1' : s₇.regs addr1 = db + v.val := by simpa [s₇, BinOp.eval] using hs₇_a1
    rw [ha1']
    change (s₂.write (s₂.regs addr2) (s₂.regs zero)).mem (db + v.val) = rowDeg W v
    rw [Data.write_mem, hs₃_a2, Function.update_of_ne (matAddr_ne_degAddr hstr hdisj u v v).symm]
    exact hdeg v
  set s₈ := s₇.set rem (s₇.mem (s₇.regs addr1))
  have hs₈_v1 : s₈.regs val1 = W u v :=
    (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
      ((set_regs_ne _ _ _ _ (by decide)).trans hs₅_v1))
  have hs₈_rem : s₈.regs rem = rowDeg W v := by simp [s₈, hs₇_load]
  refine exec_seq_op_sub (by rw [hs₈_v1, hs₈_rem]; exact hdv) h₈ fun _ h₉ => ?_
  exact exec_toExact_noSub h₉ rfl

private theorem postRandStep_toExact {w wb db str m r_val : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x y : Data 16} {n : ℕ}
    (hW : IsMultigraph W) (hsamp : IsSampledPair W r_val u v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = m + 1)
    (htotS : x.regs totS = totalDoubledWeight W) (hrem : x.regs rem = r_val)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1))) (hdEnd : Fits w (db + (m + 1)))
    (htot : Fits w (totalDoubledWeight W)) (hws : HoldsWorkspace x.mem wb db str W)
    (h : Exec w postRandStep x y n) :
    Exec w (toExactCode postRandStep) x y n := by
  have huv : u ≠ v := isSampledPair_ne hW hsamp
  obtain ⟨y1, ⟨_, _, e1_ref⟩, hm1, h1_0, h1_1, h1_wb, h1_db, h1_str, h1_k, _, h1_tot,
      h1_u, h1_rem⟩ :=
    uScan_exec hsamp h0 h1 hwBase hdBase hstride hactiveK htotS hrem hdEnd htot hws.2
  obtain ⟨y2, ⟨_, _, e2_ref⟩, hm2, _, h2_1, _, h2_db, _, h2_k, _, h2_tot, h2_u, h2_v,
      h2_a2, h2_v1⟩ :=
    vScan_exec hsamp h1_0 h1_1 h1_wb h1_db h1_str h1_k h1_tot h1_u h1_rem
      hstr hwEnd hdEnd htot (hm1 ▸ hws.1)
  unfold postRandStep at h ⊢
  cases h with
  | seq h_u h_r1 =>
    obtain ⟨rfl, _⟩ := exec_unique_std h_u e1_ref
    cases h_r1 with
    | seq h_v h_r2 =>
      obtain ⟨rfl, _⟩ := exec_unique_std h_v e2_ref
      cases h_r2 with
      | seq h_deg h_r3 =>
        cases h_r3 with
        | seq h_ptrs h_r4 =>
          cases h_r4 with
          | seq h_mloop h_r5 =>
            cases h_r5 with
            | seq h_sub h_if =>
              have hk_z5 : _ = m + 1 :=
                ((exec_regs_eq_of_preserves h_mloop rfl).trans
                  ((exec_regs_eq_of_preserves h_ptrs rfl).trans
                    (exec_regs_eq_of_preserves h_deg rfl))).trans h2_k
              have h1_z5 : _ = 1 :=
                ((exec_regs_eq_of_preserves h_mloop rfl).trans
                  ((exec_regs_eq_of_preserves h_ptrs rfl).trans
                    (exec_regs_eq_of_preserves h_deg rfl))).trans h2_1
              exact .seq (uScan_toExact h_u) (.seq (vScan_toExact h_v)
                (.seq (phaseADegrees_toExact hW huv h2_db h2_tot h2_u h2_v h2_a2 h2_v1
                  hstr hdisj (hm2.trans hm1 ▸ hws.2) h_deg)
                  (.seq (exec_toExact_noSub h_ptrs rfl)
                    (.seq (exec_toExact_noSub h_mloop rfl)
                      (.seq (exec_op_sub_toExact (by rw [h1_z5, hk_z5]; omega) h_sub).1
                        (exec_toExact_noSub h_if rfl))))))

/-- Shared-witness execution in both `Basis.standard` and `Basis.exact`. -/
def ExactExecRand {r : ℕ} (w : ℕ) (c : Code .standard r) (x : Data r)
    (m : ProbComp (Data r × ℕ)) : Prop :=
  ExecRand (B := .standard) w c x m ∧ ExecRand (B := .exact) w (toExactCode c) x m

private theorem ExactExecRand.toExact {r w : ℕ} {c : Code .standard r} {x : Data r}
    {m m' : ProbComp (Data r × ℕ)} (hex : ExactExecRand w c x m')
    (hm : ExecRand (B := .standard) w c x m) :
    ExecRand (B := .exact) w (toExactCode c) x m :=
  hm.unique hex.1 ▸ hex.2

private theorem ExactExecRand.seqExec {r w : ℕ} {c₁ c₂ : Code .standard r} {x y : Data r}
    {n₁ : ℕ} {m₂ : ProbComp (Data r × ℕ)}
    (h₁ : Exec (B := .standard) w c₁ x y n₁)
    (h₁_ex : Exec (B := .exact) w (toExactCode c₁) x y n₁)
    (h₂ : ExactExecRand w c₂ y m₂) :
    ExactExecRand w (.seq c₁ c₂) x ((fun z => (z.1, n₁ + z.2)) <$> m₂) :=
  ⟨h₁.seqRand h₂.1, h₁_ex.seqRand h₂.2⟩

private theorem ExactExecRand.seqExec_noSub {r w : ℕ} {c₁ c₂ : Code .standard r} {x y : Data r}
    {n₁ : ℕ} {m₂ : ProbComp (Data r × ℕ)} (hno : noSubDivMod c₁ = true)
    (h₁ : Exec (B := .standard) w c₁ x y n₁) (h₂ : ExactExecRand w c₂ y m₂) :
    ExactExecRand w (.seq c₁ c₂) x ((fun z => (z.1, n₁ + z.2)) <$> m₂) :=
  ExactExecRand.seqExec h₁ (exec_toExact_noSub h₁ hno) h₂

private theorem contractLoop_exact {w wb db str t steps : ℕ}
    {W : Fin (t + steps) → Fin (t + steps) → ℕ} {x : Data 16}
    (ht : 2 ≤ t) (hW : IsMultigraph W) (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hst : ContractState w wb db str (t + steps) t W x) :
    ∃ m, ExactExecRand w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] x m := by
  induction steps generalizing x with
  | zero =>
    have hnc : ¬ (Cond.lt targetT activeK).Holds x := by
      simp [hst.regs_targetT, hst.regs_activeK]
    exact ⟨pure (x, 2), .loop_exit hnc, .loop_exit hnc⟩
  | succ s ih =>
    let m_cur := t + s
    have hm_ge : 2 ≤ m_cur := by omega
    have hc_loop : (Cond.lt targetT activeK).Holds x := by
      simp only [Cond.holds_lt, hst.regs_targetT, hst.regs_activeK]
      omega
    by_cases hS0 : totalDoubledWeight W = 0
    · have hcond_z : (Cond.eq totS zero).Holds x := by simp [hst.regs_totS, hS0, h0]
      have hm_fit : Fits w m_cur := hst.fits_dEnd.of_le (by omega)
      let x_next := x.set activeK m_cur
      have hsub1 : (t + (s + 1)) - 1 = m_cur := by omega
      have hop_std : (Op.bin .sub activeK activeK one).eval w x = some x_next := by
        simp only [Op.eval_bin, BinOp.eval, hst.regs_activeK, h1, hsub1]
        exact Data.put_of_fits hm_fit
      have hop_ex : (toExactOp (Op.bin .sub activeK activeK one)).eval w x = some x_next := by
        rw [eval_toExactOp_sub (by rw [h1, hst.regs_activeK]; omega)]
        exact hop_std
      have hb_std : ExecRand (B := .standard) w contractStep x (pure (x_next, 2)) := by
        unfold contractStep
        simpa only [map_pure] using ExecRand.branch_pos hcond_z (ExecRand.op hop_std)
      have hb_ex : ExecRand (B := .exact) w (toExactCode contractStep) x (pure (x_next, 2)) := by
        unfold contractStep
        simpa only [toExactCode, map_pure] using ExecRand.branch_pos hcond_z (ExecRand.op hop_ex)
      let u₀ : Fin (m_cur + 1) := ⟨0, by omega⟩
      let v₀ : Fin (m_cur + 1) := Fin.last m_cur
      have hW_zero : ∀ a b : Fin (t + (s + 1)), W a b = 0 := fun a b => by
        have := entry_le_totalDoubledWeight W a b
        omega
      have hcm_zero : ∀ i j : Fin m_cur, contractMatrix W u₀ v₀ i j = 0 := fun i j => by
        unfold contractMatrix mergePair
        simp [hW_zero]
      have hdeg_cm_zero : ∀ i : Fin m_cur, rowDeg (contractMatrix W u₀ v₀) i = 0 := fun i => by
        unfold rowDeg
        simp [hcm_zero]
      have htot_cm_zero : totalDoubledWeight (contractMatrix W u₀ v₀) = 0 := by
        unfold totalDoubledWeight
        simp [hdeg_cm_zero]
      have hws_next : HoldsWorkspace x_next.mem wb db str (contractMatrix W u₀ v₀) := by
        refine ⟨fun i j => ?_, fun i => ?_⟩
        · have hi_lt : i.val < t + (s + 1) := by
            have hlt : i.val < t + s := i.isLt
            omega
          have hj_lt : j.val < t + (s + 1) := by
            have hlt : j.val < t + s := j.isLt
            omega
          change x.mem (wb + i.val * str + j.val) = _
          have hw_ij : x.mem (wb + i.val * str + j.val) = W ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩ :=
            hst.workspace.1 ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩
          rw [hw_ij, hW_zero, hcm_zero]
        · have hi_lt : i.val < t + (s + 1) := by
            have hlt : i.val < t + s := i.isLt
            omega
          change x.mem (db + i.val) = _
          have hd_i : x.mem (db + i.val) = rowDeg W ⟨i.val, hi_lt⟩ :=
            hst.workspace.2 ⟨i.val, hi_lt⟩
          rw [hd_i, hdeg_cm_zero]
          unfold rowDeg
          simp [hW_zero]
      have hmul_le : str * m_cur ≤ str * (t + (s + 1)) := Nat.mul_le_mul_left str (by omega)
      have hst_next : ContractState w wb db str m_cur t (contractMatrix W u₀ v₀) x_next := {
        regs_wBase := (set_regs_ne _ _ _ _ (by decide)).trans hst.regs_wBase
        regs_dBase := (set_regs_ne _ _ _ _ (by decide)).trans hst.regs_dBase
        regs_stride := (set_regs_ne _ _ _ _ (by decide)).trans hst.regs_stride
        regs_activeK := by simp [x_next]
        regs_targetT := (set_regs_ne _ _ _ _ (by decide)).trans hst.regs_targetT
        regs_totS := by
          rw [set_regs_ne _ _ _ _ (by decide), hst.regs_totS, hS0, htot_cm_zero]
        le_stride := by have := hst.le_stride; omega
        disjoint_blocks := by have := hst.disjoint_blocks; omega
        fits_wEnd := hst.fits_wEnd.of_le (by omega)
        fits_dEnd := hst.fits_dEnd.of_le (by omega)
        fits_totS := by rw [htot_cm_zero]; exact fits_zero w
        workspace := hws_next
      }
      obtain ⟨m_tail, htail_std, htail_ex⟩ := ih (isMultigraph_contractMatrix hW u₀ v₀)
        ((set_regs_ne _ _ _ _ (by decide)).trans h0)
        ((set_regs_ne _ _ _ _ (by decide)).trans h1) hst_next
      refine ⟨_, ExecRand.loop_iter hc_loop hb_std (ml := fun _ => m_tail) (fun z hz => by
          cases OracleComp.eq_of_mem_supportWith_pure hz; exact htail_std),
        ExecRand.loop_iter hc_loop hb_ex (ml := fun _ => m_tail) (fun z hz => by
          cases OracleComp.eq_of_mem_supportWith_pure hz; exact htail_ex)⟩
    · have hS_pos : 0 < totalDoubledWeight W := Nat.pos_of_ne_zero hS0
      have hcond_nz : ¬ (Cond.eq totS zero).Holds x := by
        simp only [Cond.holds_eq, hst.regs_totS, h0]
        omega
      let S := totalDoubledWeight W
      have hSm1_fit : Fits w (S - 1) := hst.fits_totS.of_le (by omega)
      let x_sub := x.set val1 (S - 1)
      have hop_std : (Op.bin .sub val1 totS one).eval w x = some x_sub := by
        simp only [Op.eval_bin, BinOp.eval, hst.regs_totS, h1]
        exact Data.put_of_fits hSm1_fit
      have hop_ex : (toExactOp (Op.bin .sub val1 totS one)).eval w x = some x_sub := by
        rw [eval_toExactOp_sub (by rw [h1, hst.regs_totS]; omega)]
        exact hop_std
      have hsub_v1_fit : Fits w (x_sub.regs val1) := by
        simpa only [x_sub, Data.set_regs, Function.update_self] using hSm1_fit
      have hper_sample : ∀ k_fin : Fin (x_sub.regs val1 + 1),
          ∃ (y_post : Data 16) (n_post : ℕ) (m_rec : ProbComp (Data 16 × ℕ)),
            Exec (B := .standard) w postRandStep (x_sub.set rem k_fin.val) y_post n_post ∧
            Exec (B := .exact) w (toExactCode postRandStep)
              (x_sub.set rem k_fin.val) y_post n_post ∧
            ExactExecRand w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] y_post m_rec := by
        intro k_fin
        have hk_lt : k_fin.val < S := by
          have := k_fin.isLt
          simp only [x_sub, Data.set_regs, Function.update_self] at this
          omega
        obtain ⟨u, v, hsamp⟩ := exists_isSampledPair W hk_lt
        let x_r := x_sub.set rem k_fin.val
        have hr0 : x_r.regs zero = 0 :=
          (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans h0)
        have hr1 : x_r.regs one = 1 :=
          (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans h1)
        have hr_wb : x_r.regs wBase = wb :=
          (set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_wBase)
        have hr_db : x_r.regs dBase = db :=
          (set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_dBase)
        have hr_str : x_r.regs stride = str :=
          (set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_stride)
        have hr_k : x_r.regs activeK = m_cur + 1 :=
          (set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_activeK)
        have hr_t : x_r.regs targetT = t :=
          (set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_targetT)
        have hr_tot : x_r.regs totS = S :=
          (set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_totS)
        have hr_rem : x_r.regs rem = k_fin.val := by simp [x_r]
        obtain ⟨y_post, ⟨n_post, _, e_post⟩, _, hst_post, hy0, hy1⟩ :=
          postRandStep_exec hm_ge hW hsamp hr0 hr1 hr_wb hr_db hr_str hr_k hr_t hr_tot hr_rem
            hst.le_stride hst.disjoint_blocks hst.fits_wEnd hst.fits_dEnd hst.fits_totS
            hst.workspace
        have e_post_ex :=
          postRandStep_toExact hW hsamp hr0 hr1 hr_wb hr_db hr_str hr_k hr_tot hr_rem
            hst.le_stride hst.disjoint_blocks hst.fits_wEnd hst.fits_dEnd hst.fits_totS
            hst.workspace e_post
        obtain ⟨m_rec, hm_rec⟩ := ih (isMultigraph_contractMatrix hW u v) hy0 hy1 hst_post
        exact ⟨y_post, n_post, m_rec, e_post, e_post_ex, hm_rec⟩
      let m_post (d : Data 16) := codeComp (B := .standard) w postRandStep d
      let m_loop_rec (d : Data 16) :=
        codeComp (B := .standard) w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] d
      have hrand_post_std : ExecRand (B := .standard) w ram[rem ← rand val1; ⟪postRandStep⟫]
          x_sub
          (do
            let z₁ ← (do
              let k ← ProbComp.unifFin (x_sub.regs val1)
              pure (x_sub.set rem k.val, 1))
            let z₂ ← m_post z₁.1
            pure (z₂.1, z₁.2 + z₂.2)) := by
        refine ExecRand.seq (ExecRand.rand hsub_v1_fit) fun z₁ hz₁ => ?_
        obtain ⟨k_fin, -, hk_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
        cases OracleComp.eq_of_mem_supportWith_pure hk_eq
        obtain ⟨y_post, n_post, _, e_post, _, _⟩ := hper_sample k_fin
        dsimp only [m_post]
        rw [e_post.execRand.codeComp_eq]
        exact e_post.execRand
      have hrand_post_ex : ExecRand (B := .exact) w
          (toExactCode ram[rem ← rand val1; ⟪postRandStep⟫]) x_sub
          (do
            let z₁ ← (do
              let k ← ProbComp.unifFin (x_sub.regs val1)
              pure (x_sub.set rem k.val, 1))
            let z₂ ← m_post z₁.1
            pure (z₂.1, z₁.2 + z₂.2)) := by
        refine ExecRand.seq (ExecRand.rand hsub_v1_fit) fun z₁ hz₁ => ?_
        obtain ⟨k_fin, -, hk_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
        cases OracleComp.eq_of_mem_supportWith_pure hk_eq
        obtain ⟨y_post, n_post, _, e_post, e_post_ex, _⟩ := hper_sample k_fin
        dsimp only [m_post]
        rw [e_post.execRand.codeComp_eq]
        exact e_post_ex.execRand
      have hb_std : ExecRand (B := .standard) w contractStep x _ :=
        ExecRand.branch_neg hcond_nz ((Exec.op hop_std).seqRand hrand_post_std)
      have hb_ex : ExecRand (B := .exact) w (toExactCode contractStep) x _ :=
        ExecRand.branch_neg hcond_nz ((Exec.op hop_ex).seqRand hrand_post_ex)
      refine ⟨_, ExecRand.loop_iter hc_loop hb_std (ml := m_loop_rec) ?_,
        ExecRand.loop_iter hc_loop hb_ex (ml := m_loop_rec) ?_⟩
      · intro z hz
        obtain ⟨z_in, hz_in, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
        obtain ⟨z_r, hz_r, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz_in
        obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz_r
        obtain ⟨k_fin, -, hk_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
        cases OracleComp.eq_of_mem_supportWith_pure hk_eq
        obtain ⟨y_post, n_post, m_rec, e_post, _, hm_rec⟩ := hper_sample k_fin
        dsimp only [m_post] at hrest
        rw [e_post.execRand.codeComp_eq] at hrest
        obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
        cases OracleComp.eq_of_mem_supportWith_pure hz₂
        cases OracleComp.eq_of_mem_supportWith_pure hfinal
        dsimp only [m_loop_rec]
        rw [hm_rec.1.codeComp_eq]
        exact hm_rec.1
      · intro z hz
        obtain ⟨z_in, hz_in, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
        obtain ⟨z_r, hz_r, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz_in
        obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz_r
        obtain ⟨k_fin, -, hk_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
        cases OracleComp.eq_of_mem_supportWith_pure hk_eq
        obtain ⟨y_post, n_post, m_rec, e_post, _, hm_rec⟩ := hper_sample k_fin
        dsimp only [m_post] at hrest
        rw [e_post.execRand.codeComp_eq] at hrest
        obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
        cases OracleComp.eq_of_mem_supportWith_pure hz₂
        cases OracleComp.eq_of_mem_supportWith_pure hfinal
        dsimp only [m_loop_rec]
        rw [hm_rec.1.codeComp_eq]
        exact hm_rec.2

/-- Any `ExecRand` of `contractDownTo` from a valid `ContractState` lifts with identical sampling
tree `m` to `Basis.exact`. -/
theorem contractDownTo_toExact {w wb db str k t : ℕ} {W : Fin k → Fin k → ℕ} {x : Data 16}
    {m : ProbComp (Data 16 × ℕ)} (ht : 2 ≤ t) (htk : t ≤ k) (hW : IsMultigraph W)
    (hst : ContractState w wb db str k t W x)
    (hm : ExecRand (B := .standard) w contractDownTo x m) :
    ExecRand (B := .exact) w (toExactCode contractDownTo) x m := by
  have hk_split : t + (k - t) = k := Nat.add_sub_of_le htk
  revert W hst hm
  rw [← hk_split]
  intro W hW hst hm
  have h1_fit : Fits w 1 := hst.fits_dEnd.of_le (by omega)
  let x₁ := (x.set zero 0).set one 1
  have e0 : Exec w (Code.op (.const zero 0)) x (x.set zero 0) 1 :=
    Exec.const (B := .standard) (d := zero) (x := x) (fits_zero w)
  have e1 : Exec w (Code.op (.const one 1)) (x.set zero 0) x₁ 1 :=
    Exec.const (B := .standard) (d := one) (x := x.set zero 0) h1_fit
  have hst₁ : ContractState w wb db str (t + (k - t)) t W x₁ := {
    regs_wBase := (set_regs_ne _ _ _ _ (by decide)).trans
      ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_wBase)
    regs_dBase := (set_regs_ne _ _ _ _ (by decide)).trans
      ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_dBase)
    regs_stride := (set_regs_ne _ _ _ _ (by decide)).trans
      ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_stride)
    regs_activeK := (set_regs_ne _ _ _ _ (by decide)).trans
      ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_activeK)
    regs_targetT := (set_regs_ne _ _ _ _ (by decide)).trans
      ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_targetT)
    regs_totS := (set_regs_ne _ _ _ _ (by decide)).trans
      ((set_regs_ne _ _ _ _ (by decide)).trans hst.regs_totS)
    le_stride := hst.le_stride
    disjoint_blocks := hst.disjoint_blocks
    fits_wEnd := hst.fits_wEnd
    fits_dEnd := hst.fits_dEnd
    fits_totS := hst.fits_totS
    workspace := hst.workspace
  }
  obtain ⟨m_loop, hm_loop⟩ :=
    contractLoop_exact ht hW (set_regs_ne _ _ _ _ (by decide)) (by simp [x₁]) hst₁
  have hex : ExactExecRand w contractDownTo x _ :=
    ExactExecRand.seqExec_noSub rfl e0 (ExactExecRand.seqExec_noSub rfl e1 hm_loop)
  exact hex.toExact hm

/-- Any `ExecRand` of `contractDownToAt hr` from a valid `ContractState` lifts with identical
sampling tree `m` to `Basis.exact`. -/
theorem contractDownToAt_toExact {r w wb db str k t : ℕ} (hr : 16 ≤ r)
    {W : Fin k → Fin k → ℕ} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (ht : 2 ≤ t) (htk : t ≤ k) (hW : IsMultigraph W)
    (hst : ContractState w wb db str k t W (x.comap (Fin.castLE hr)))
    (hm : ExecRand (B := .standard) w (contractDownToAt hr) x m) :
    ExecRand (B := .exact) w (toExactCode (contractDownToAt hr)) x m := by
  obtain ⟨m₀, hm₀, _, _, _⟩ := contractDownTo_spec ht htk (isContractionOf_id hW) hst
  have hm₀_ex := contractDownTo_toExact ht htk hW hst hm₀
  have hf := Fin.castLE_injective hr
  have hm_std : ExecRand (B := .standard) w (contractDownToAt hr) x
      ((fun z : Data 16 × ℕ => (z.1.extend (Fin.castLE hr) x, z.2)) <$> m₀) := hm₀.rename hf
  have hm_ex : ExecRand (B := .exact) w (toExactCode (contractDownToAt hr)) x
      ((fun z : Data 16 × ℕ => (z.1.extend (Fin.castLE hr) x, z.2)) <$> m₀) := by
    unfold contractDownToAt
    rw [toExactCode_rename]
    exact hm₀_ex.rename hf
  exact (hm.unique hm_std) ▸ hm_ex

end ContractLift

/-! ## Lifting `singleCode`, `ampCore`, `amplifiedCode`, and `highProbCode` -/

section EndpointLifts

private theorem noSubDivMod_rename {r₁ r₂ : ℕ} (c : Code .standard r₁) (f : Fin r₁ → Fin r₂) :
    noSubDivMod (c.rename f) = noSubDivMod c := by
  induction c with
  | op o =>
    cases o with
    | const _ _ | copy _ _ | load _ _ | store _ _ => rfl
    | alu g _ _ =>
      cases g with
      | width => rfl
      | bin b => cases b <;> rfl
  | seq _ _ ih₁ ih₂ | branch _ _ _ ih₁ ih₂ => simp only [Code.rename, noSubDivMod, ih₁, ih₂]
  | loop _ _ ih => simp only [Code.rename, noSubDivMod, ih]
  | rand _ _ => rfl

private theorem singleCode_toExact {n w : ℕ} {W : Fin n → Fin n → ℕ}
    {m : ProbComp (Data 16 × ℕ)} (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W))
    (hm : ExecRand (B := .standard) w singleCode (Data.init (n :: flattenMatrix W)) m) :
    ExecRand (B := .exact) w (toExactCode singleCode) (Data.init (n :: flattenMatrix W)) m := by
  have hws_fit := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws_fit.of_le (by omega)
  have hwEnd : Fits w (2 + n * n) := hws_fit.of_le (by omega)
  have hdEnd : Fits w (2 + n * n + n) := hws_fit.of_le (by omega)
  have hwb1 : Fits w (2 + 1) := hws_fit.of_le (by omega)
  obtain ⟨y_setup, e_setup, hmem_setup, hwb_s, hdb_s, hstr_s, hk_s, ht_s⟩ :=
    singleSetup_exec (W := W) hn hw
  obtain ⟨y_deg, ⟨n_deg, _, e_deg⟩, hws_deg, _, _, _,
      hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d⟩ :=
    computeDegreesAndTotal_exec (w := w) (W := W) (x := y_setup)
      hwb_s hdb_s hstr_s hk_s (le_refl n) (Or.inl (le_refl _)) h1 hwEnd hdEnd htot
      (hmem_setup ▸ holdsMatrix_init_single W)
  rw [ht_s] at ht_d
  have hst_deg : ContractState w 2 (2 + n * n) n n 2 W y_deg :=
    ⟨hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d, le_refl n, Or.inl (le_refl _),
      hwEnd, hdEnd, htot, hws_deg⟩
  obtain ⟨m_c, hm_c, _, hsup_c, _⟩ :=
    contractDownTo_spec (le_refl 2) hn (isContractionOf_id hW) hst_deg
  have hm_c_ex := contractDownTo_toExact (le_refl 2) hn hW hst_deg hm_c
  let m_post (d : Data 16) := codeComp (B := .standard) w singlePost d
  have hex_cp : ExactExecRand w (.seq contractDownTo singlePost) y_deg
      (do let z₁ ← m_c; let z₂ ← m_post z₁.1; pure (z₂.1, z₁.2 + z₂.2)) := by
    refine ⟨ExecRand.seq hm_c fun z hz => ?_, ExecRand.seq hm_c_ex fun z hz => ?_⟩
    · rcases hsup_c z hz with ⟨_, _, _, _, _, hst'⟩
      obtain ⟨_, e_p, _, _⟩ := singlePost_exec hst'.regs_wBase h1 hwb1
      dsimp only [m_post]
      rw [e_p.execRand.codeComp_eq]
      exact e_p.execRand
    · rcases hsup_c z hz with ⟨_, _, _, _, _, hst'⟩
      obtain ⟨_, e_p, _, _⟩ := singlePost_exec hst'.regs_wBase h1 hwb1
      dsimp only [m_post]
      rw [e_p.execRand.codeComp_eq]
      exact (exec_toExact_noSub e_p rfl).execRand
  have hex : ExactExecRand w singleCode (Data.init (n :: flattenMatrix W)) _ :=
    ExactExecRand.seqExec_noSub rfl e_setup (ExactExecRand.seqExec_noSub rfl e_deg hex_cp)
  exact hex.toExact hm

section AmpLift

open AmpReg

private theorem ampTrialBody_toExact {w sb n R i : ℕ} {W : Fin n → Fin n → ℕ}
    {mem₀ : ℕ → ℕ} {x : Data 22} {m : ProbComp (Data 22 × ℕ)}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hiR : i < R)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n)) (hR_fit : Fits w R)
    (htot : Fits w (totalDoubledWeight W))
    (hinv : AmpInv w sb n R i W mem₀ x)
    (hm : ExecRand (B := .standard) w ampTrialBody x m) :
    ExecRand (B := .exact) w (toExactCode ampTrialBody) x m := by
  let wb := sb + n * n
  let db := sb + 2 * (n * n)
  have hr22 : 16 ≤ 22 := by decide
  have hwEnd : Fits w (wb + n * n) := hdEnd.of_le (by omega)
  have hwb1_fit : Fits w (wb + 1) := hdEnd.of_le (by omega)
  have h2_fit : Fits w 2 := hdEnd.of_le (by omega)
  obtain ⟨y_cp, ⟨n_cp, _, e_cp⟩, hmat_cp, _, hwb_cp, hdb_cp, _, hn_cp_reg, _, _, hti_cp, _⟩ :=
    copyMatrixCode_exec hinv.regs_srcBase hinv.regs_wBase hinv.regs_matLen
      (le_refl _) h1 hwEnd hinv.src_matrix
  rw [hinv.regs_dBase] at hdb_cp
  rw [hinv.regs_nOrig] at hn_cp_reg
  rw [hinv.regs_trialIdx] at hti_cp
  let y_cfg := ((y_cp.set activeK n).set stride n).set targetT 2
  have ec1 : Exec (B := .standard) w ram[activeK ← nOrig] y_cp (y_cp.set activeK n) 1 := by
    simpa [hn_cp_reg] using
      Exec.copy (B := .standard) (w := w) (d := activeK) (s := nOrig) (x := y_cp)
  have ec2 : Exec (B := .standard) w ram[stride ← nOrig] (y_cp.set activeK n)
      ((y_cp.set activeK n).set stride n) 1 := by
    have hr : (y_cp.set activeK n).regs nOrig = n :=
      (set_regs_ne _ _ _ _ (by decide)).trans hn_cp_reg
    simpa [hr] using
      Exec.copy (B := .standard) (w := w) (d := stride) (s := nOrig) (x := y_cp.set activeK n)
  have ec3 : Exec (B := .standard) w ram[targetT ← #2]
      ((y_cp.set activeK n).set stride n) y_cfg 1 :=
    Exec.const h2_fit
  obtain ⟨y_deg, ⟨n_deg, _, e_deg⟩, hws_deg, _, hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d,
      hhi_d⟩ :=
    computeDegreesAndTotalAt_exec (w := w) (W := W) (x := y_cfg) hr22
      (by
        change y_cfg.regs wBase = wb
        exact (set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hwb_cp)))
      (by
        change y_cfg.regs dBase = db
        exact (set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hdb_cp)))
      (by
        change y_cfg.regs stride = n
        exact (set_regs_ne _ _ _ _ (by decide)).trans (by simp))
      (by
        change y_cfg.regs activeK = n
        exact (set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans (by simp)))
      (le_refl n) (Or.inl (by omega)) h1 hwEnd hdEnd htot hmat_cp
  have ht_d' : y_deg.regs (Fin.castLE hr22 Reg.targetT) = 2 := by
    rw [ht_d]
    change y_cfg.regs targetT = 2
    simp [y_cfg]
  have hti_deg : y_deg.regs trialIdx = i := by
    rw [hhi_d trialIdx (by decide)]
    exact (set_regs_ne _ _ _ _ (by decide)).trans
      ((set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans hti_cp))
  have hst_deg : ContractState w wb db n n 2 W (y_deg.comap (Fin.castLE hr22)) :=
    ⟨hwb_d, hdb_d, hstr_d, hk_d, ht_d', htot_d, le_refl n, Or.inl (by omega),
      hwEnd, hdEnd, htot, hws_deg⟩
  obtain ⟨m_c, hm_c, _, hsup_c, _⟩ :=
    contractDownToAt_spec hr22 (le_refl 2) hn (isContractionOf_id hW) hst_deg
  have hm_c_ex := contractDownToAt_toExact hr22 (le_refl 2) hn hW hst_deg hm_c
  let m_post (d : Data 22) := codeComp (B := .standard) w ampTrialPost d
  have hex_cp : ExactExecRand w (.seq (contractDownToAt hr22) ampTrialPost) y_deg
      (do let z₁ ← m_c; let z₂ ← m_post z₁.1; pure (z₂.1, z₁.2 + z₂.2)) := by
    refine ⟨ExecRand.seq hm_c fun z hz => ?_, ExecRand.seq hm_c_ex fun z hz => ?_⟩
    · rcases hsup_c z hz with ⟨_, _, hz_hi, _, _, _, hst'⟩
      have hz_wb : z.1.regs wBase = wb := hst'.regs_wBase
      have hz_ti : z.1.regs trialIdx = i := (hz_hi trialIdx (by decide)).trans hti_deg
      obtain ⟨_, ⟨_, _, e_p⟩, _⟩ := ampTrialPost_exec hz_wb hz_ti hiR h1 hwb1_fit hR_fit
      dsimp only [m_post]
      rw [e_p.execRand.codeComp_eq]
      exact e_p.execRand
    · rcases hsup_c z hz with ⟨_, _, hz_hi, _, _, _, hst'⟩
      have hz_wb : z.1.regs wBase = wb := hst'.regs_wBase
      have hz_ti : z.1.regs trialIdx = i := (hz_hi trialIdx (by decide)).trans hti_deg
      obtain ⟨_, ⟨_, _, e_p⟩, _⟩ := ampTrialPost_exec hz_wb hz_ti hiR h1 hwb1_fit hR_fit
      dsimp only [m_post]
      rw [e_p.execRand.codeComp_eq]
      exact (exec_toExact_noSub e_p rfl).execRand
  have hno_cp : noSubDivMod copyMatrixCode = true := by
    rw [copyMatrixCode, noSubDivMod_rename]
    rfl
  have hno_deg : noSubDivMod (computeDegreesAndTotalAt hr22) = true := by
    rw [computeDegreesAndTotalAt, noSubDivMod_rename]
    rfl
  have hex : ExactExecRand w ampTrialBody x _ :=
    ExactExecRand.seqExec_noSub hno_cp e_cp
      (ExactExecRand.seqExec_noSub rfl ec1
        (ExactExecRand.seqExec_noSub rfl ec2
          (ExactExecRand.seqExec_noSub rfl ec3
            (ExactExecRand.seqExec_noSub hno_deg e_deg hex_cp))))
  exact hex.toExact hm

private theorem ampLoop_exact {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (h1 : Fits w 1)
    (hdEnd : Fits w (sb + 2 * (n * n) + n)) (hR_fit : Fits w R)
    (htot : Fits w (totalDoubledWeight W)) :
    ∀ (remTrials i : ℕ) (x : Data 22),
      i + remTrials = R → AmpInv w sb n R i W mem₀ x →
      ∃ m : ProbComp (Data 22 × ℕ), ExactExecRand w ampLoop x m
  | 0, i, x, hsum, hinv => by
    have hi_eq : i = R := by omega
    have hnc : ¬ (Cond.lt trialIdx numTrials).Holds x := by
      simp [Cond.holds_lt, hinv.regs_trialIdx, hinv.regs_numTrials, hi_eq]
    exact ⟨pure (x, 2), .loop_exit hnc, .loop_exit hnc⟩
  | r + 1, i, x, hsum, hinv => by
    have hiR : i < R := by omega
    have hc : (Cond.lt trialIdx numTrials).Holds x := by
      simp [Cond.holds_lt, hinv.regs_trialIdx, hinv.regs_numTrials, hiR]
    obtain ⟨m_b, hm_b, _, hsup_b, _⟩ :=
      ampTrialBody_spec hn hW hiR h1 hdEnd hR_fit htot hinv
    have hm_b_ex := ampTrialBody_toExact hn hW hiR h1 hdEnd hR_fit htot hinv hm_b
    let ml (d : Data 22) := codeComp (B := .standard) w ampLoop d
    refine ⟨_, ExecRand.loop_iter hc hm_b (ml := ml) ?_,
      ExecRand.loop_iter hc hm_b_ex (ml := ml) ?_⟩
    · intro z hz
      obtain ⟨m_r, hm_r⟩ := ampLoop_exact hn hW h1 hdEnd hR_fit htot r (i + 1) z.1
        (by omega) (hsup_b z hz).2.1
      dsimp only [ml]
      rw [hm_r.1.codeComp_eq]
      exact hm_r.1
    · intro z hz
      obtain ⟨m_r, hm_r⟩ := ampLoop_exact hn hW h1 hdEnd hR_fit htot r (i + 1) z.1
        (by omega) (hsup_b z hz).2.1
      dsimp only [ml]
      rw [hm_r.1.codeComp_eq]
      exact hm_r.2

private theorem ampCore_exact {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 22}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hsb : x.regs srcBase = sb) (hnOrig : x.regs nOrig = n) (hnumT : x.regs numTrials = R)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hsrc_mat : HoldsMatrix x.mem sb n W) :
    ∃ m : ProbComp (Data 22 × ℕ), ExactExecRand w ampCore x m := by
  have hnn_fit : Fits w (n * n) := hdEnd.of_le (by omega)
  have hwb_fit : Fits w (sb + n * n) := hdEnd.of_le (by omega)
  have hdb_fit : Fits w (sb + 2 * (n * n)) := hdEnd.of_le (by omega)
  let s₁ := x.set val1 (n * n)
  let s₂ := s₁.set matLen (n * n)
  let s₃ := s₂.set wBase (sb + n * n)
  let s₄ := s₃.set dBase (sb + 2 * (n * n))
  let s₅ := s₄.set trialIdx 0
  let s₆ := s₅.set bestVal 0
  have e1 : Exec w ram[val1 ← nOrig * nOrig] x s₁ 1 := by
    simpa [s₁, BinOp.eval, hnOrig] using
      Exec.bin (w := w) (f := .mul) (d := val1) (i := nOrig) (j := nOrig) (x := x)
        (by simpa [BinOp.eval, hnOrig] using hnn_fit)
  have e2 : Exec (B := .standard) w ram[matLen ← val1] s₁ s₂ 1 := by
    have hv1 : s₁.regs val1 = n * n := by simp [s₁]
    simpa [s₂, hv1] using Exec.copy (B := .standard) (w := w) (d := matLen) (s := val1) (x := s₁)
  have e3 : Exec w ram[wBase ← srcBase + matLen] s₂ s₃ 1 := by
    have hs : s₂.regs srcBase = sb :=
      (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans hsb)
    have hml : s₂.regs matLen = n * n := by simp [s₂]
    simpa [s₃, BinOp.eval, hs, hml] using
      Exec.bin (w := w) (f := .add) (d := wBase) (i := srcBase) (j := matLen) (x := s₂)
        (by simpa [BinOp.eval, hs, hml] using hwb_fit)
  have e4 : Exec w ram[dBase ← wBase + matLen] s₃ s₄ 1 := by
    have hw' : s₃.regs wBase = sb + n * n := by simp [s₃]
    have hml : s₃.regs matLen = n * n := (set_regs_ne _ _ _ _ (by decide)).trans (by simp [s₂])
    have hadd : sb + n * n + n * n = sb + 2 * (n * n) := by omega
    simpa [s₄, BinOp.eval, hw', hml, hadd] using
      Exec.bin (w := w) (f := .add) (d := dBase) (i := wBase) (j := matLen) (x := s₃)
        (by simpa [BinOp.eval, hw', hml, hadd] using hdb_fit)
  have e5 : Exec (B := .standard) w ram[trialIdx ← #0] s₄ s₅ 1 := Exec.const (fits_zero w)
  have e6 : Exec (B := .standard) w ram[bestVal ← #0] s₅ s₆ 1 := Exec.const (fits_zero w)
  have hinv₀ : AmpInv w sb n R 0 W x.mem s₆ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hsrc_mat, Modifies.refl _ _, fun h0 => absurd h0 (by omega)⟩
    · exact (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans hsb)))))
    · exact (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans (by simp [s₃])))
    · exact (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
        (by simp [s₄]))
    · exact (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hnOrig)))))
    · exact (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans (by simp [s₂]))))
    · exact (set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans ((set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans
            ((set_regs_ne _ _ _ _ (by decide)).trans hnumT)))))
    · exact (set_regs_ne _ _ _ _ (by decide)).trans (by simp [s₅])
  obtain ⟨m_l, hm_l⟩ := ampLoop_exact hn hW h1 hdEnd hR_fit htot R 0 s₆ (Nat.zero_add R) hinv₀
  exact ⟨_, ExactExecRand.seqExec_noSub rfl e1
    (ExactExecRand.seqExec_noSub rfl e2
      (ExactExecRand.seqExec_noSub rfl e3
        (ExactExecRand.seqExec_noSub rfl e4
          (ExactExecRand.seqExec_noSub rfl e5
            (ExactExecRand.seqExec_noSub rfl e6 hm_l)))))⟩

private theorem amplifiedCode_toExact {R n w : ℕ} {W : Fin n → Fin n → ℕ}
    {m : ProbComp (Data 22 × ℕ)} (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hm : ExecRand (B := .standard) w amplifiedCode (Data.init (R :: n :: flattenMatrix W)) m) :
    ExecRand (B := .exact) w (toExactCode amplifiedCode)
      (Data.init (R :: n :: flattenMatrix W)) m := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s, hnt_s⟩ := amplifiedSetup_exec (R := R) (W := W) hn hw
  obtain ⟨_, hex_c⟩ := ampCore_exact hn hW hsb_s hn_s hnt_s h1 hws hR_fit htot
    (hm_s ▸ holdsMatrix_init_amplified W)
  exact (ExactExecRand.seqExec_noSub rfl e_s hex_c).toExact hm

private theorem highProbSetup_toExact {w n : ℕ} {W : Fin n → Fin n → ℕ} {y : Data 22} {k : ℕ}
    (hn : 2 ≤ n) (h : Exec w highProbSetup (Data.init (n :: flattenMatrix W)) y k) :
    Exec w (toExactCode highProbSetup) (Data.init (n :: flattenMatrix W)) y k := by
  let x₀ : Data 22 := Data.init (n :: flattenMatrix W)
  have hm1 : x₀.mem 1 = n := rfl
  unfold highProbSetup at h ⊢
  refine exec_seq_op_noSub rfl h fun s₁ _ ho₁ h₁ => ?_
  obtain rfl := op_eval_const_eq ho₁
  refine exec_seq_op_noSub rfl h₁ fun s₂ _ ho₂ h₂ => ?_
  cases ho₂
  refine exec_seq_op_noSub rfl h₂ fun s₃ _ ho₃ h₃ => ?_
  cases ho₃
  refine exec_seq_op_noSub rfl h₃ fun s₄ _ ho₄ h₄ => ?_
  obtain rfl := op_eval_const_eq ho₄
  cases h₄ with
  | seq h_loop h_rest =>
    set s₄ := (((x₀.set one 1).set nOrig (x₀.mem ((x₀.set one 1).regs one))).set rem
      (((x₀.set one 1).set nOrig (x₀.mem ((x₀.set one 1).regs one))).regs nOrig)).set idx 0
    have hs₄_one : s₄.regs one = 1 :=
      (set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans
          ((set_regs_ne _ _ _ _ (by decide)).trans (by simp)))
    have hs₄_n : s₄.regs nOrig = n :=
      (set_regs_ne _ _ _ _ (by decide)).trans
        ((set_regs_ne _ _ _ _ (by decide)).trans (by simp [hm1]))
    have h5_one := (exec_regs_eq_of_preserves h_loop (reg := one) rfl).trans hs₄_one
    have h5_n := (exec_regs_eq_of_preserves h_loop (reg := nOrig) rfl).trans hs₄_n
    refine .seq (exec_toExact_noSub h_loop rfl) ?_
    refine exec_seq_op_noSub rfl h_rest fun t₁ _ hot₁ ht₁ => ?_
    obtain rfl := op_eval_const_eq hot₁
    refine exec_seq_op_noSub rfl ht₁ fun t₂ _ hot₂ ht₂ => ?_
    obtain rfl := op_eval_bin_eq hot₂
    refine exec_seq_op_sub ?_ ht₂ fun _ ht₃ => exec_toExact_noSub ht₃ rfl
    rw [set_regs_ne _ _ _ _ (by decide), set_regs_ne _ _ _ _ (by decide),
      set_regs_ne _ _ _ _ (by decide), set_regs_ne _ _ _ _ (by decide), h5_one, h5_n]
    omega

private theorem highProbCode_toExact {n w : ℕ} {W : Fin n → Fin n → ℕ}
    {m : ProbComp (Data 22 × ℕ)} (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W))
    (hm : ExecRand (B := .standard) w highProbCode (Data.init (n :: flattenMatrix W)) m) :
    ExecRand (B := .exact) w (toExactCode highProbCode) (Data.init (n :: flattenMatrix W)) m := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  have hdEnd : Fits w (2 + 2 * (n * n) + n) := hws.of_le (by omega)
  have hhp_fit := fits_highProbTrials_of_logWidth_three hn hw
  obtain ⟨y_s, ⟨n_s, _, e_s⟩, hm_s, hsb_s, hn_s_r, hnt_s⟩ :=
    highProbSetup_exec (W := W) hn hw
  obtain ⟨_, hex_c⟩ := ampCore_exact hn hW hsb_s hn_s_r hnt_s h1 hdEnd hhp_fit htot
    (hm_s ▸ holdsMatrix_init_single W)
  exact (ExactExecRand.seqExec e_s (highProbSetup_toExact hn e_s) hex_c).toExact hm

end AmpLift

section KargerSteinLift

open KSReg

private def ExactLoopSegment {r : ℕ} (w : ℕ) (cond : Cond r) (body : Code .standard r)
    (x : Data r) (m : ProbComp (Data r × ℕ)) : Prop :=
  LoopSegment (B := .standard) w cond body x m ∧
  LoopSegment (B := .exact) w cond (toExactCode body) x m

private theorem ExactLoopSegment.single {r w : ℕ} {cond : Cond r} {body : Code .standard r}
    {x : Data r} {m : ProbComp (Data r × ℕ)}
    (hc : cond.Holds x) (hb : ExactExecRand w body x m) :
    ExactLoopSegment w cond body x ((fun z => (z.1, z.2 + 2)) <$> m) :=
  ⟨LoopSegment.single hc hb.1, LoopSegment.single hc hb.2⟩

private theorem ExactLoopSegment.detSingle {r w : ℕ} {cond : Cond r} {body : Code .standard r}
    {x y : Data r} {n : ℕ} (hc : cond.Holds x)
    (hb : Exec (B := .standard) w body x y n)
    (hb_ex : Exec (B := .exact) w (toExactCode body) x y n) :
    ExactLoopSegment w cond body x (pure (y, n + 2)) :=
  ⟨LoopSegment.detSingle hc hb, LoopSegment.detSingle hc hb_ex⟩

private theorem ExactLoopSegment.trans_exists {r w : ℕ} {cond : Cond r}
    {body : Code .standard r} {x : Data r} {m₁ : ProbComp (Data r × ℕ)}
    {Q : Data r → ProbComp (Data r × ℕ) → Prop}
    (h₁ : ExactLoopSegment w cond body x m₁)
    (h₂ : ∀ z ∈ m₁.support, ∃ m', ExactLoopSegment w cond body z.1 m' ∧ Q z.1 m') :
    ∃ m₂ : Data r → ProbComp (Data r × ℕ),
      ExactLoopSegment w cond body x (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2)) ∧
      ∀ z ∈ m₁.support, ExactLoopSegment w cond body z.1 (m₂ z.1) ∧ Q z.1 (m₂ z.1) := by
  classical
  let m₂ : Data r → ProbComp (Data r × ℕ) := fun d =>
    if h : ∃ m', ExactLoopSegment w cond body d m' ∧ Q d m' then h.choose else pure (d, 0)
  have hm₂ : ∀ z ∈ m₁.support, ExactLoopSegment w cond body z.1 (m₂ z.1) ∧ Q z.1 (m₂ z.1) := by
    intro z hz
    have hex := h₂ z hz
    simp only [m₂, hex, ↓reduceDIte]
    exact hex.choose_spec
  exact ⟨m₂,
    ⟨h₁.1.trans fun z hz => (hm₂ z hz).1.1, h₁.2.trans fun z hz => (hm₂ z hz).1.2⟩,
    hm₂⟩

private theorem ExactLoopSegment.finish {r w : ℕ} {cond : Cond r} {body : Code .standard r}
    {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExactLoopSegment w cond body x m)
    (hexit : ∀ z ∈ m.support, ¬cond.Holds z.1) :
    ExactExecRand w (.loop cond body) x ((fun z => (z.1, z.2 + 2)) <$> m) :=
  ⟨h.1.finish hexit, h.2.finish hexit⟩

private theorem thresholdCode_toExact {w k : ℕ} {x y : Data 24} {n : ℕ}
    (hk : 7 ≤ k) (hactiveK : x.regs activeK = k)
    (h : Exec w thresholdCode x y n) :
    Exec w (toExactCode thresholdCode) x y n := by
  unfold thresholdCode at h ⊢
  cases h with
  | seq h_pre h_loop =>
    refine .seq ?_ (exec_toExact_noSub h_loop rfl)
    unfold thresholdPre at h_pre ⊢
    refine exec_seq_op_noSub rfl h_pre fun s₁ _ ho₁ h₁ => ?_
    obtain rfl := op_eval_const_eq ho₁
    refine exec_seq_op_sub ?_ h₁ fun _ h₂ => exec_toExact_noSub h₂ rfl
    have h1_s : (x.set one 1).regs one = 1 := by simp
    have hk_s : (x.set one 1).regs activeK = k :=
      (set_regs_ne x one activeK 1 (by decide)).trans hactiveK
    omega

private theorem basePost_toExact {w b : ℕ} {x y : Data 24} {n : ℕ}
    (hsp : x.regs spReg = b + 1) (h : Exec w basePost x y n) :
    Exec w (toExactCode basePost) x y n := by
  unfold basePost at h ⊢
  refine exec_seq_op_noSub rfl h fun s₁ _ ho₁ h₁ => ?_
  have hs₁_sp : s₁.regs spReg = b + 1 := (op_regs_eq_of_ne ho₁ rfl).trans hsp
  refine exec_seq_op_noSub rfl h₁ fun s₂ _ ho₂ h₂ => ?_
  obtain rfl := op_eval_const_eq ho₂
  have hs₂_1 : (s₁.set one 1).regs one = 1 := by simp
  have hs₂_sp : (s₁.set one 1).regs spReg = b + 1 :=
    (set_regs_ne _ _ _ _ (by decide)).trans hs₁_sp
  refine exec_seq_op_noSub rfl h₂ fun s₃ _ ho₃ h₃ => ?_
  have hs₃_1 : s₃.regs one = 1 := (op_regs_eq_of_ne ho₃ rfl).trans hs₂_1
  have hs₃_sp : s₃.regs spReg = b + 1 := (op_regs_eq_of_ne ho₃ rfl).trans hs₂_sp
  refine exec_seq_op_noSub rfl h₃ fun s₄ _ ho₄ h₄ => ?_
  have hs₄_1 : s₄.regs one = 1 := (op_regs_eq_of_ne ho₄ rfl).trans hs₃_1
  have hs₄_sp : s₄.regs spReg = b + 1 := (op_regs_eq_of_ne ho₄ rfl).trans hs₃_sp
  refine exec_seq_op_noSub rfl h₄ fun s₅ _ ho₅ h₅ => ?_
  have hs₅_1 : s₅.regs one = 1 := (op_regs_eq_of_ne ho₅ rfl).trans hs₄_1
  have hs₅_sp : s₅.regs spReg = b + 1 := (op_regs_eq_of_ne ho₅ rfl).trans hs₄_sp
  exact (exec_op_sub_toExact (by rw [hs₅_1, hs₅_sp]; omega) h₅).1

private theorem combineAndPop_toExact {w b : ℕ} {x y : Data 24} {n : ℕ}
    (h1 : x.regs one = 1) (hsp : x.regs spReg = b + 1)
    (h : Exec w combineAndPop x y n) :
    Exec w (toExactCode combineAndPop) x y n := by
  unfold combineAndPop at h ⊢
  refine exec_seq_op_noSub rfl h fun s₁ _ ho₁ h₁ => ?_
  have hs₁_1 : s₁.regs one = 1 := (op_regs_eq_of_ne ho₁ rfl).trans h1
  have hs₁_sp : s₁.regs spReg = b + 1 := (op_regs_eq_of_ne ho₁ rfl).trans hsp
  refine exec_seq_op_noSub rfl h₁ fun s₂ _ ho₂ h₂ => ?_
  have hs₂_1 : s₂.regs one = 1 := (op_regs_eq_of_ne ho₂ rfl).trans hs₁_1
  have hs₂_sp : s₂.regs spReg = b + 1 := (op_regs_eq_of_ne ho₂ rfl).trans hs₁_sp
  cases h₂ with
  | seq h_br h₃ =>
    have hs₃_1 := (exec_regs_eq_of_preserves h_br (reg := one) rfl).trans hs₂_1
    have hs₃_sp := (exec_regs_eq_of_preserves h_br (reg := spReg) rfl).trans hs₂_sp
    refine .seq (exec_toExact_noSub h_br rfl) ?_
    refine exec_seq_op_noSub rfl h₃ fun s₄ _ ho₄ h₄ => ?_
    have hs₄_1 := (op_regs_eq_of_ne ho₄ rfl).trans hs₃_1
    have hs₄_sp := (op_regs_eq_of_ne ho₄ rfl).trans hs₃_sp
    exact (exec_op_sub_toExact (by rw [hs₄_1, hs₄_sp]; omega) h₄).1

private theorem basePost_halts {w wb b : ℕ} {x : Data 24}
    (hwb : x.regs wBase = wb) (hsp : x.regs spReg = b + 1)
    (h1 : Fits w 1) (hwb1_fit : Fits w (wb + 1)) (hsp_fit : Fits w b) :
    ∃ y : Data 24, Exec (B := .standard) w basePost x y 6 := by
  let q₁ := x.set zero 0
  let q₂ := q₁.set one 1
  let q₃ := q₂.set addr1 (wb + 1)
  let q₄ := q₃.set retVal (q₃.mem (wb + 1))
  let q₅ := q₄.set fpReg (q₄.mem (q₄.regs fpReg))
  let y := q₅.set spReg b
  have b1 : Exec (B := .standard) w ram[zero ← #0] x q₁ 1 := Exec.const (fits_zero w)
  have b2 : Exec (B := .standard) w ram[one ← #1] q₁ q₂ 1 := Exec.const h1
  have b3 : Exec w ram[addr1 ← wBase + one] q₂ q₃ 1 := by
    have hwb' : q₂.regs wBase = wb := by
      simpa +decide [q₂, q₁, Function.update_apply] using hwb
    have h1' : q₂.regs one = 1 := by simp [q₂]
    simpa [q₃, BinOp.eval, hwb', h1'] using
      Exec.bin (f := .add) (d := addr1) (i := wBase) (j := one) (x := q₂)
        (by simpa [BinOp.eval, hwb', h1'] using hwb1_fit)
  have b4 : Exec (B := .standard) w ram[retVal ← *addr1] q₃ q₄ 1 := by
    have ha1' : q₃.regs addr1 = wb + 1 := by simp [q₃]
    simpa [q₄, ha1'] using
      Exec.load (B := .standard) (w := w) (d := retVal) (a := addr1) (x := q₃)
  have b5 : Exec (B := .standard) w ram[fpReg ← *fpReg] q₄ q₅ 1 :=
    Exec.load (B := .standard) (w := w) (d := fpReg) (a := fpReg) (x := q₄)
  have b6 : Exec w ram[spReg ← spReg - one] q₅ y 1 := by
    have hsp' : q₅.regs spReg = b + 1 := by
      simpa +decide [q₅, q₄, q₃, q₂, q₁, Function.update_apply] using hsp
    have h1' : q₅.regs one = 1 := by simp +decide [q₅, q₄, q₃, q₂]
    have hsub : (b + 1) - 1 = b := by omega
    simpa [y, BinOp.eval, hsp', h1', hsub] using
      Exec.bin (f := .sub) (d := spReg) (i := spReg) (j := one) (x := q₅)
        (by simpa [BinOp.eval, hsp', h1', hsub] using hsp_fit)
  unfold basePost
  exact ⟨y, b1.seq (b2.seq (b3.seq (b4.seq (b5.seq b6))))⟩

private theorem baseCaseAndPop_toExact {n w fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    {m : ProbComp (Data 24 × ℕ)}
    (hk2 : 2 ≤ k) (hk_reg : x.regs activeK = k) (hrem_reg : x.regs rem = k * k)
    (ha1_reg : x.regs addr1 = fp + 2) (ha2_reg : x.regs addr2 = fp + 2 + k * k)
    (hsp : x.regs spReg = b + 1) (hmat : HoldsMatrix x.mem (fp + 2) k W_k)
    (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b)
    (htot : Fits w (totalDoubledWeight W₀))
    (hm : ExecRand (B := .standard) w baseCaseAndPop x m) :
    ExecRand (B := .exact) w (toExactCode baseCaseAndPop) x m := by
  let wb := fp + 4 + k * k
  let db := fp + 4 + 2 * (k * k)
  have hfs_eq : fp + frameSize k = db + k := by dsimp only [db]; unfold frameSize; omega
  have hkk_ge : 4 ≤ k * k := Nat.mul_le_mul hk2 hk2
  have h1 : Fits w 1 := hfit.of_le (by rw [hfs_eq]; dsimp only [db]; omega)
  have h2 : Fits w 2 := hfit.of_le (by rw [hfs_eq]; dsimp only [db]; omega)
  have hwb_fit : Fits w wb := hfit.of_le (by rw [hfs_eq]; dsimp only [wb, db]; omega)
  have hdb_fit : Fits w db := hfit.of_le (by rw [hfs_eq]; omega)
  have hdEnd_fit : Fits w (db + k) := hfs_eq ▸ hfit
  have hwb1_fit : Fits w (wb + 1) := hdEnd_fit.of_le (by dsimp only [wb, db]; omega)
  have hd_eq : wb + k * k = db := by dsimp only [wb, db]; omega
  have htot_k : Fits w (totalDoubledWeight W_k) :=
    htot.of_le (totalDoubledWeight_le_of_isContractionOf hC)
  let p₁ := x.set uReg (fp + 2)
  let p₂ := p₁.set val1 2
  let p₃ := p₂.set wBase wb
  let p₄ := p₃.set dBase db
  let p₅ := p₄.set stride k
  let x_pre := p₅.set targetT 2
  have hex_pre : Exec w basePre x x_pre 6 := by
    have s1 : Exec (B := .standard) w ram[uReg ← addr1] x p₁ 1 := by
      simpa [p₁, ha1_reg] using
        Exec.copy (B := .standard) (w := w) (d := uReg) (s := addr1) (x := x)
    have s2 : Exec (B := .standard) w ram[val1 ← #2] p₁ p₂ 1 := Exec.const h2
    have s3 : Exec w ram[wBase ← addr2 + val1] p₂ p₃ 1 := by
      have ha2' : p₂.regs addr2 = fp + 2 + k * k := by
        simpa +decide [p₂, p₁, Function.update_apply] using ha2_reg
      have hv1' : p₂.regs val1 = 2 := by simp [p₂]
      have heq : (fp + 2 + k * k) + 2 = wb := by dsimp only [wb]; omega
      simpa [p₃, BinOp.eval, ha2', hv1', heq] using
        Exec.bin (f := .add) (d := wBase) (i := addr2) (j := val1) (x := p₂)
          (by simpa [BinOp.eval, ha2', hv1', heq] using hwb_fit)
    have s4 : Exec w ram[dBase ← wBase + rem] p₃ p₄ 1 := by
      have hwb' : p₃.regs wBase = wb := by simp [p₃]
      have hr' : p₃.regs rem = k * k := by
        simpa +decide [p₃, p₂, p₁, Function.update_apply] using hrem_reg
      simpa [p₄, BinOp.eval, hwb', hr', hd_eq] using
        Exec.bin (f := .add) (d := dBase) (i := wBase) (j := rem) (x := p₃)
          (by simpa [BinOp.eval, hwb', hr', hd_eq] using hdb_fit)
    have s5 : Exec (B := .standard) w ram[stride ← activeK] p₄ p₅ 1 := by
      have hk' : p₄.regs activeK = k := by
        simpa +decide [p₄, p₃, p₂, p₁, Function.update_apply] using hk_reg
      simpa [p₅, hk'] using
        Exec.copy (B := .standard) (w := w) (d := stride) (s := activeK) (x := p₄)
    have s6 : Exec (B := .standard) w ram[targetT ← #2] p₅ x_pre 1 := Exec.const h2
    unfold basePre
    exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))
  obtain ⟨x_cp, ⟨_, _, hex_cp⟩, hmat_cp, _, _, hwb_cp, hdb_cp, hstr_cp, hk_cp, ht_cp, hhi_cp⟩ :=
    ksCopyCode_exec (x := x_pre) (sb := fp + 2) (db := wb) (k := k) (W := W_k)
      (by simp +decide [x_pre, p₅, p₄, p₃, p₂, p₁])
      (by simp +decide [x_pre, p₅, p₄, p₃])
      (by simpa +decide [x_pre, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using hrem_reg)
      (by dsimp only [wb]; omega) h1 (hd_eq ▸ hdb_fit) hmat
  have hdb_cp' : x_cp.regs dBase = db := by rw [hdb_cp]; simp +decide [x_pre, p₅, p₄]
  have hstr_cp' : x_cp.regs stride = k := by rw [hstr_cp]; simp +decide [x_pre, p₅]
  have hk_cp' : x_cp.regs activeK = k := by
    rw [hk_cp]; simpa +decide [x_pre, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using hk_reg
  have ht_cp' : x_cp.regs targetT = 2 := by rw [ht_cp]; simp [x_pre]
  have hr24 : 16 ≤ 24 := by decide
  obtain ⟨x_deg, ⟨_, _, hex_deg⟩, hws_deg, _, hwb_deg, hdb_deg, hstr_deg, hk_deg, ht_deg, htot_deg,
      hhi_deg⟩ :=
    computeDegreesAndTotalAt_exec hr24 (x := x_cp) (wb := wb) (db := db) (str := k) (k := k)
      (W := W_k) hwb_cp hdb_cp' hstr_cp' hk_cp' (le_refl k)
      (Or.inl (by dsimp only [wb, db]; omega)) h1 (hd_eq ▸ hdb_fit) hdEnd_fit htot_k hmat_cp
  have hsp_deg : x_deg.regs spReg = b + 1 := by
    rw [hhi_deg spReg (by decide), hhi_cp spReg (by decide)]
    simpa +decide [x_pre, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using hsp
  have hst_deg : ContractState w wb db k k 2 W_k (x_deg.comap (Fin.castLE hr24)) :=
    ⟨hwb_deg, hdb_deg, hstr_deg, hk_deg, ht_deg.trans ht_cp', htot_deg, le_refl k,
      Or.inl (by dsimp only [wb, db]; omega), hd_eq ▸ hdb_fit, hdEnd_fit, htot_k, hws_deg⟩
  obtain ⟨m_c, hm_c, _, hsup_c, _⟩ :=
    contractDownToAt_spec hr24 (le_refl 2) hk2 hC hst_deg
  have hm_c_ex := contractDownToAt_toExact hr24 (le_refl 2) hk2 hC.multigraph hst_deg hm_c
  let m_post (d : Data 24) := codeComp (B := .standard) w basePost d
  have hex_cp_post : ExactExecRand w (.seq (contractDownToAt hr24) basePost) x_deg
      (do let z₁ ← m_c; let z₂ ← m_post z₁.1; pure (z₂.1, z₁.2 + z₂.2)) := by
    refine ⟨ExecRand.seq hm_c fun z hz => ?_, ExecRand.seq hm_c_ex fun z hz => ?_⟩
    · rcases hsup_c z hz with ⟨_, _, hhi_c, _, _, _, hst_c⟩
      have hz_sp : z.1.regs spReg = b + 1 := (hhi_c spReg (by decide)).trans hsp_deg
      obtain ⟨_, e_p⟩ := basePost_halts hst_c.regs_wBase hz_sp h1 hwb1_fit hsp_fit
      dsimp only [m_post]
      rw [e_p.execRand.codeComp_eq]
      exact e_p.execRand
    · rcases hsup_c z hz with ⟨_, _, hhi_c, _, _, _, hst_c⟩
      have hz_sp : z.1.regs spReg = b + 1 := (hhi_c spReg (by decide)).trans hsp_deg
      obtain ⟨_, e_p⟩ := basePost_halts hst_c.regs_wBase hz_sp h1 hwb1_fit hsp_fit
      dsimp only [m_post]
      rw [e_p.execRand.codeComp_eq]
      exact (basePost_toExact hz_sp e_p).execRand
  have hno_cp : noSubDivMod ksCopyCode = true := by
    rw [ksCopyCode, noSubDivMod_rename]; rfl
  have hno_deg : noSubDivMod (computeDegreesAndTotalAt hr24) = true := by
    rw [computeDegreesAndTotalAt, noSubDivMod_rename]; rfl
  have hex : ExactExecRand w baseCaseAndPop x _ :=
    ExactExecRand.seqExec_noSub rfl hex_pre
      (ExactExecRand.seqExec_noSub hno_cp hex_cp
        (ExactExecRand.seqExec_noSub hno_deg hex_deg hex_cp_post))
  exact hex.toExact hm

private theorem branchContractAndPush_toExact {n w fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    {m : ProbComp (Data 24 × ℕ)}
    (hk7 : 7 ≤ k) (hk_reg : x.regs activeK = k)
    (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀))
    (hm : ExecRand (B := .standard) w branchContractAndPush x m) :
    ExecRand (B := .exact) w (toExactCode branchContractAndPush) x m := by
  let t := fastCutThreshold k
  let wb := fp + 4 + k * k
  let db := fp + 4 + 2 * (k * k)
  let childFp := fp + frameSize k
  have ht6 : 6 ≤ t := fastCutThreshold_ge_six hk7
  have htk : t < k := fastCutThreshold_lt (by omega)
  have hscr_eq : fp + fastCutScratch k = childFp + fastCutScratch t := by
    dsimp only [childFp, t]; rw [fastCutScratch_of_ge_seven hk7]; omega
  have hfs_t_le : frameSize t ≤ fastCutScratch t := frameSize_le_fastCutScratch t
  have hcfp_eq : fp + frameSize k = db + k := by dsimp only [db]; unfold frameSize; omega
  have hfit_child : Fits w (childFp + frameSize t) := hfit.of_le (by omega)
  have hfit_th : Fits w (2 * k * (k - 1)) := by
    have hle : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
    have h2 : 2 * k * (k - 1) = 2 * (k * (k - 1)) := by ring
    exact hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; dsimp only [db]; omega)
  have hkk_ge : 49 ≤ k * k := Nat.mul_le_mul hk7 hk7
  have h1 : Fits w 1 := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have h2 : Fits w 2 := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have h4 : Fits w 4 := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hfp2_fit : Fits w (fp + 2) := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hfp4_fit : Fits w (fp + 4) := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hkk_fit : Fits w (k * k) := hfit_child.of_le (by
    dsimp only [childFp]; rw [hcfp_eq]; dsimp only [db]; omega)
  have hwb_fit : Fits w wb := hfit_child.of_le (by
    dsimp only [childFp]; rw [hcfp_eq]; dsimp only [wb, db]; omega)
  have hdb_fit : Fits w db := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hdEnd_fit : Fits w (db + k) := hfit_child.of_le (by
    dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hd_eq : wb + k * k = db := by dsimp only [wb, db]; omega
  have htot_k : Fits w (totalDoubledWeight W_k) :=
    htot.of_le (totalDoubledWeight_le_of_isContractionOf hC)
  obtain ⟨x_th, ⟨_, _, hex_th⟩, hmem_th, _, hk_th, ht_th, _, _, _, hhi_th⟩ :=
    thresholdCode_exec hk7 hk_reg hfit_th
  have hex_th_ex := thresholdCode_toExact hk7 hk_reg hex_th
  have hfp_th : x_th.regs fpReg = fp := (hhi_th fpReg (by decide)).trans hfp
  have hsp_th : x_th.regs spReg = b + 1 := (hhi_th spReg (by decide)).trans hsp
  let s₁ := x_th.set val1 2
  let s₂ := s₁.set uReg (fp + 2)
  let s₃ := s₂.set rem (k * k)
  let s₄ := s₃.set val1 4
  let s₅ := s₄.set wBase (fp + 4)
  let s₆ := s₅.set wBase wb
  let s₇ := s₆.set dBase db
  let x_set := s₇.set stride k
  have hex_setup : Exec w branchSetup x_th x_set 8 := by
    have e1 : Exec (B := .standard) w ram[val1 ← #2] x_th s₁ 1 := Exec.const h2
    have e2 : Exec w ram[uReg ← fpReg + val1] s₁ s₂ 1 := by
      have hfp' : s₁.regs fpReg = fp := by simpa +decide [s₁, Function.update_apply] using hfp_th
      have hv1' : s₁.regs val1 = 2 := by simp [s₁]
      simpa [s₂, BinOp.eval, hfp', hv1'] using
        Exec.bin (f := .add) (d := uReg) (i := fpReg) (j := val1) (x := s₁)
          (by simpa [BinOp.eval, hfp', hv1'] using hfp2_fit)
    have e3 : Exec w ram[rem ← activeK * activeK] s₂ s₃ 1 := by
      have hk' : s₂.regs activeK = k := by
        simpa +decide [s₂, s₁, Function.update_apply] using hk_th
      simpa [s₃, BinOp.eval, hk'] using
        Exec.bin (f := .mul) (d := rem) (i := activeK) (j := activeK) (x := s₂)
          (by simpa [BinOp.eval, hk'] using hkk_fit)
    have e4 : Exec (B := .standard) w ram[val1 ← #4] s₃ s₄ 1 := Exec.const h4
    have e5 : Exec w ram[wBase ← fpReg + val1] s₄ s₅ 1 := by
      have hfp' : s₄.regs fpReg = fp := by
        simpa +decide [s₄, s₃, s₂, s₁, Function.update_apply] using hfp_th
      have hv1' : s₄.regs val1 = 4 := by simp [s₄]
      simpa [s₅, BinOp.eval, hfp', hv1'] using
        Exec.bin (f := .add) (d := wBase) (i := fpReg) (j := val1) (x := s₄)
          (by simpa [BinOp.eval, hfp', hv1'] using hfp4_fit)
    have e6 : Exec w ram[wBase ← wBase + rem] s₅ s₆ 1 := by
      have hwb' : s₅.regs wBase = fp + 4 := by simp [s₅]
      have hr' : s₅.regs rem = k * k := by simp +decide [s₅, s₄, s₃]
      have heq : (fp + 4) + k * k = wb := rfl
      simpa [s₆, BinOp.eval, hwb', hr', heq] using
        Exec.bin (f := .add) (d := wBase) (i := wBase) (j := rem) (x := s₅)
          (by simpa [BinOp.eval, hwb', hr', heq] using hwb_fit)
    have e7 : Exec w ram[dBase ← wBase + rem] s₆ s₇ 1 := by
      have hwb' : s₆.regs wBase = wb := by simp [s₆]
      have hr' : s₆.regs rem = k * k := by simp +decide [s₆, s₅, s₄, s₃]
      simpa [s₇, BinOp.eval, hwb', hr', hd_eq] using
        Exec.bin (f := .add) (d := dBase) (i := wBase) (j := rem) (x := s₆)
          (by simpa [BinOp.eval, hwb', hr', hd_eq] using hdb_fit)
    have e8 : Exec (B := .standard) w ram[stride ← activeK] s₇ x_set 1 := by
      have hk' : s₇.regs activeK = k := by
        simpa +decide [s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hk_th
      simpa [x_set, hk'] using
        Exec.copy (B := .standard) (w := w) (d := stride) (s := activeK) (x := s₇)
    unfold branchSetup
    exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  obtain ⟨x_cp, ⟨_, _, hex_cp⟩, hmat_cp, _, _, hwb_cp, hdb_cp, hstr_cp, hk_cp, ht_cp, hhi_cp⟩ :=
    ksCopyCode_exec (x := x_set) (sb := fp + 2) (db := wb) (k := k) (W := W_k)
      (by simp +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂])
      (by simp +decide [x_set, s₇, s₆])
      (by simp +decide [x_set, s₇, s₆, s₅, s₄, s₃])
      (by dsimp only [wb]; omega) h1 (hd_eq ▸ hdb_fit) (hmem_th ▸ hmat)
  have hdb_cp' : x_cp.regs dBase = db := by rw [hdb_cp]; simp +decide [x_set, s₇]
  have hstr_cp' : x_cp.regs stride = k := by rw [hstr_cp]; simp [x_set]
  have hk_cp' : x_cp.regs activeK = k := by
    rw [hk_cp]; simpa +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hk_th
  have ht_cp' : x_cp.regs targetT = t := by
    rw [ht_cp]; simpa +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using ht_th
  have hr24 : 16 ≤ 24 := by decide
  obtain ⟨x_deg, ⟨_, _, hex_deg⟩, hws_deg, _, hwb_deg, hdb_deg, hstr_deg, hk_deg, ht_deg, htot_deg,
      hhi_deg⟩ :=
    computeDegreesAndTotalAt_exec hr24 (x := x_cp) (wb := wb) (db := db) (str := k) (k := k)
      (W := W_k) hwb_cp hdb_cp' hstr_cp' hk_cp' (le_refl k)
      (Or.inl (by dsimp only [wb, db]; omega)) h1 (hd_eq ▸ hdb_fit) hdEnd_fit htot_k hmat_cp
  have hfp_deg : x_deg.regs fpReg = fp := by
    rw [hhi_deg fpReg (by decide), hhi_cp fpReg (by decide)]
    simpa +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hfp_th
  have hsp_deg : x_deg.regs spReg = b + 1 := by
    rw [hhi_deg spReg (by decide), hhi_cp spReg (by decide)]
    simpa +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hsp_th
  have hst_deg : ContractState w wb db k k t W_k (x_deg.comap (Fin.castLE hr24)) :=
    ⟨hwb_deg, hdb_deg, hstr_deg, hk_deg, ht_deg.trans ht_cp', htot_deg, le_refl k,
      Or.inl (by dsimp only [wb, db]; omega), hd_eq ▸ hdb_fit, hdEnd_fit, htot_k, hws_deg⟩
  obtain ⟨m_c, hm_c, _, hsup_c, _⟩ :=
    contractDownToAt_spec hr24 (by omega : 2 ≤ t) htk.le hC hst_deg
  have hm_c_ex := contractDownToAt_toExact hr24 (by omega : 2 ≤ t) htk.le hC.multigraph hst_deg hm_c
  let m_tail (d : Data 24) := codeComp (B := .standard) w branchTail d
  have hex_ct : ExactExecRand w (.seq (contractDownToAt hr24) branchTail) x_deg
      (do let z₁ ← m_c; let z₂ ← m_tail z₁.1; pure (z₂.1, z₁.2 + z₂.2)) := by
    refine ⟨ExecRand.seq hm_c fun z hz => ?_, ExecRand.seq hm_c_ex fun z hz => ?_⟩
    · rcases hsup_c z hz with ⟨_, _, hhi_c, _, _, _, hst_c⟩
      obtain ⟨_, ⟨_, _, e_t⟩, _⟩ :=
        branchTail_exec ht6 htk.le hst_c.regs_wBase hst_c.regs_dBase hst_c.regs_stride
          hst_c.regs_targetT ((hhi_c fpReg (by decide)).trans hfp_deg)
          ((hhi_c spReg (by decide)).trans hsp_deg) hfit_child hsp_fit
      dsimp only [m_tail]
      rw [e_t.execRand.codeComp_eq]
      exact e_t.execRand
    · rcases hsup_c z hz with ⟨_, _, hhi_c, _, _, _, hst_c⟩
      obtain ⟨_, ⟨_, _, e_t⟩, _⟩ :=
        branchTail_exec ht6 htk.le hst_c.regs_wBase hst_c.regs_dBase hst_c.regs_stride
          hst_c.regs_targetT ((hhi_c fpReg (by decide)).trans hfp_deg)
          ((hhi_c spReg (by decide)).trans hsp_deg) hfit_child hsp_fit
      dsimp only [m_tail]
      rw [e_t.execRand.codeComp_eq]
      exact (exec_toExact_noSub e_t rfl).execRand
  have hno_cp : noSubDivMod ksCopyCode = true := by
    rw [ksCopyCode, noSubDivMod_rename]; rfl
  have hno_deg : noSubDivMod (computeDegreesAndTotalAt hr24) = true := by
    rw [computeDegreesAndTotalAt, noSubDivMod_rename]; rfl
  have hex : ExactExecRand w branchContractAndPush x _ :=
    ExactExecRand.seqExec hex_th hex_th_ex
      (ExactExecRand.seqExec_noSub rfl hex_setup
        (ExactExecRand.seqExec_noSub hno_cp hex_cp
          (ExactExecRand.seqExec_noSub hno_deg hex_deg hex_ct)))
  exact hex.toExact hm

private theorem fastCutStep_base_exact {n w fp parentFp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk2 : 2 ≤ k) (hk6 : k ≤ 6)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_p : x.mem fp = parentFp) (hmem_k : x.mem (fp + 1) = k)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w b)
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExactLoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
      ∀ z ∈ m.support,
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = parentFp ∧
        z.1.regs spReg = b := by
  have hscr : fastCutScratch k = frameSize k := fastCutScratch_of_lt_seven (by omega)
  have hfit_fs : Fits w (fp + frameSize k) := hscr ▸ hfit
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  obtain ⟨y_h, hex_hdr, hm_h, _, _, hk_h, hrem_h, ha1_h, ha2_h, _, hv1_h, hhi_h⟩ :=
    stepHeader_exec hk2 hfp hmem_k rfl hfit_fs
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hc_lt : (Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]; omega
  obtain ⟨m_b, hm_b, _, hsup_b, _⟩ :=
    baseCaseAndPop_spec hk2 hk6 hk_h hrem_h ha1_h ha2_h hfp_h hsp_h
      (hm_h ▸ hmem_p) (hm_h ▸ hmat) hC hfit_fs hsp_fit htot
  have hm_b_ex :=
    baseCaseAndPop_toExact hk2 hk_h hrem_h ha1_h ha2_h hsp_h (hm_h ▸ hmat) hC hfit_fs hsp_fit htot
      hm_b
  have hstep : ExactExecRand w fastCutStep x _ :=
    ⟨hex_hdr.seqRand (ExecRand.branch_pos hc_lt hm_b),
      (exec_toExact_noSub hex_hdr rfl).seqRand (ExecRand.branch_pos hc_lt hm_b_ex)⟩
  refine ⟨_, ExactLoopSegment.single hc_loop hstep, fun z hz => ?_⟩
  simp only [Functor.map_map] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  rcases hsup_b z₀ hz₀ with ⟨_, hmod₀, hz0, hzfp, hzsp, _⟩
  exact ⟨hscr.symm ▸ (hm_h ▸ hmod₀), hz0, hzfp, hzsp⟩

private theorem fastCutStep_stage0_exact {n w fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_k : x.mem (fp + 1) = k) (hmem_stg : x.mem (fp + 2 + k * k) = 0)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    ∃ m : ProbComp (Data 24 × ℕ),
      ExactLoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
      ∀ z ∈ m.support,
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
        z.1.mem (fp + 2 + k * k) = 1 ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = childFp ∧
        z.1.regs spReg = b + 2 ∧
        z.1.mem childFp = fp ∧
        z.1.mem (childFp + 1) = t ∧
        z.1.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          HoldsMatrix z.1.mem (childFp + 2) t W' := by
  intro t childFp
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  have hfs_le : frameSize k ≤ fastCutScratch k := frameSize_le_fastCutScratch k
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg (hfit.of_le (by omega))
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]; omega
  have hc_eq0 : (Cond.eq val2 zero).Holds y_h := by simp [Cond.holds_eq, hv2_h, h0_h]
  let y_s := y_h.write (fp + 2 + k * k) 1
  have hex_s0 : Exec (B := .standard) w stageZeroSet y_h y_s 1 := by
    unfold stageZeroSet
    simpa [y_s, ha2_h, h1_h] using
      Exec.store (B := .standard) (w := w) (a := addr2) (s := one) (x := y_h)
  have hmat_s : HoldsMatrix y_s.mem (fp + 2) k W_k := by
    intro i j
    have hlt : fp + 2 + i.val * k + j.val < fp + 2 + k * k := matAddr_lt_end (le_refl k) i j
    change Function.update y_h.mem (fp + 2 + k * k) 1 (fp + 2 + i.val * k + j.val) = W_k i j
    rw [Function.update_of_ne (by omega), hm_h]
    exact hmat i j
  obtain ⟨m_c, hm_c, _, hsup_c, _⟩ :=
    branchContractAndPush_spec (x := y_s) hk7 hk_h hfp_h hsp_h hmat_s hC hfit hsp_fit htot
  have hm_c_ex :=
    branchContractAndPush_toExact (x := y_s) hk7 hk_h hfp_h hsp_h hmat_s hC hfit hsp_fit htot hm_c
  have hstep : ExactExecRand w fastCutStep x _ :=
    ⟨hex_hdr.seqRand (ExecRand.branch_neg hnc_lt (ExecRand.branch_pos hc_eq0
      (hex_s0.seqRand hm_c))),
    (exec_toExact_noSub hex_hdr rfl).seqRand (ExecRand.branch_neg hnc_lt
      (ExecRand.branch_pos hc_eq0 ((exec_toExact_noSub hex_s0 rfl).seqRand hm_c_ex)))⟩
  refine ⟨_, ExactLoopSegment.single hc_loop hstep, fun z hz => ?_⟩
  simp only [Functor.map_map] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  rcases hsup_c z₀ hz₀ with ⟨_, hmod₀, rest⟩
  have hmod_s : Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k))
      x.mem y_s.mem := by
    change Modifies _ x.mem (Function.update y_h.mem (fp + 2 + k * k) 1)
    rw [hm_h]
    intro a ha
    rw [Finset.mem_Ico] at ha
    exact Function.update_of_ne (by unfold frameSize at hfs_le; omega) _ _
  have hsub : Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k) ⊆
      Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
    intro a ha; rw [Finset.mem_Ico] at ha ⊢; omega
  have hstg_val : z₀.1.mem (fp + 2 + k * k) = 1 := by
    rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega)]
    exact Function.update_self _ _ _
  exact ⟨modifies_trans_subset hmod_s hmod₀ Finset.Subset.rfl hsub, hstg_val, rest⟩

private theorem fastCutStep_stage1_exact {n w fp b k v1 : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hret : x.regs retVal = v1)
    (hmem_k : x.mem (fp + 1) = k) (hmem_stg : x.mem (fp + 2 + k * k) = 1)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    ∃ m : ProbComp (Data 24 × ℕ),
      ExactLoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
      ∀ z ∈ m.support,
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
        z.1.mem (fp + 2 + k * k) = 2 ∧
        z.1.mem (fp + 3 + k * k) = v1 ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = childFp ∧
        z.1.regs spReg = b + 2 ∧
        z.1.mem childFp = fp ∧
        z.1.mem (childFp + 1) = t ∧
        z.1.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          HoldsMatrix z.1.mem (childFp + 2) t W' := by
  intro t childFp
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  have hfs_le : frameSize k ≤ fastCutScratch k := frameSize_le_fastCutScratch k
  have hfit_fs : Fits w (fp + frameSize k) := hfit.of_le (by omega)
  have h2_fit : Fits w 2 := hfit_fs.of_le (by unfold frameSize; omega)
  have ha1_fit : Fits w (fp + 3 + k * k) := hfit_fs.of_le (by unfold frameSize; omega)
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg hfit_fs
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hret_h : y_h.regs retVal = v1 := (hhi_h retVal (by decide)).trans hret
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]; omega
  have hnc_eq0 : ¬(Cond.eq val2 zero).Holds y_h := by simp [Cond.holds_eq, hv2_h, h0_h]
  have hc_eq1 : (Cond.eq val2 one).Holds y_h := by simp [Cond.holds_eq, hv2_h, h1_h]
  let q₁ := y_h.set val1 2
  let q₂ := q₁.write (fp + 2 + k * k) 2
  let q₃ := q₂.set addr1 (fp + 3 + k * k)
  let y_s := q₃.write (fp + 3 + k * k) v1
  have hex_s1 : Exec w stageOneSaveAndSet y_h y_s 4 := by
    have s1 : Exec (B := .standard) w ram[val1 ← #2] y_h q₁ 1 := Exec.const h2_fit
    have s2 : Exec (B := .standard) w ram[*addr2 ← val1] q₁ q₂ 1 := by
      have ha2' : q₁.regs addr2 = fp + 2 + k * k := by
        simpa +decide [q₁, Function.update_apply] using ha2_h
      have hv1' : q₁.regs val1 = 2 := by simp [q₁]
      simpa [q₂, ha2', hv1'] using
        Exec.store (B := .standard) (w := w) (a := addr2) (s := val1) (x := q₁)
    have s3 : Exec w ram[addr1 ← addr2 + one] q₂ q₃ 1 := by
      have ha2' : q₂.regs addr2 = fp + 2 + k * k := by
        simpa +decide [q₂, q₁, Function.update_apply] using ha2_h
      have h1' : q₂.regs one = 1 := by simpa +decide [q₂, q₁, Function.update_apply] using h1_h
      have heq : (fp + 2 + k * k) + 1 = fp + 3 + k * k := by omega
      simpa [q₃, BinOp.eval, ha2', h1', heq] using
        Exec.bin (f := .add) (d := addr1) (i := addr2) (j := one) (x := q₂)
          (by simpa [BinOp.eval, ha2', h1', heq] using ha1_fit)
    have s4 : Exec (B := .standard) w ram[*addr1 ← retVal] q₃ y_s 1 := by
      have ha1' : q₃.regs addr1 = fp + 3 + k * k := by simp [q₃]
      have hr' : q₃.regs retVal = v1 := by
        simpa +decide [q₃, q₂, q₁, Function.update_apply] using hret_h
      simpa [y_s, ha1', hr'] using
        Exec.store (B := .standard) (w := w) (a := addr1) (s := retVal) (x := q₃)
    unfold stageOneSaveAndSet
    exact s1.seq (s2.seq (s3.seq s4))
  have hys_mem : y_s.mem =
      Function.update (Function.update x.mem (fp + 2 + k * k) 2) (fp + 3 + k * k) v1 := by
    change Function.update (Function.update y_h.mem _ _) _ _ = _
    rw [hm_h]
  have hmat_s : HoldsMatrix y_s.mem (fp + 2) k W_k := by
    intro i j
    have hlt : fp + 2 + i.val * k + j.val < fp + 2 + k * k := matAddr_lt_end (le_refl k) i j
    rw [hys_mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hmat i j
  have hk_s : y_s.regs activeK = k := by
    simpa +decide [y_s, q₃, q₂, q₁, Function.update_apply] using hk_h
  have hfp_s : y_s.regs fpReg = fp := by
    simpa +decide [y_s, q₃, q₂, q₁, Function.update_apply] using hfp_h
  have hsp_s : y_s.regs spReg = b + 1 := by
    simpa +decide [y_s, q₃, q₂, q₁, Function.update_apply] using hsp_h
  obtain ⟨m_c, hm_c, _, hsup_c, _⟩ :=
    branchContractAndPush_spec (x := y_s) hk7 hk_s hfp_s hsp_s hmat_s hC hfit hsp_fit htot
  have hm_c_ex :=
    branchContractAndPush_toExact (x := y_s) hk7 hk_s hfp_s hsp_s hmat_s hC hfit hsp_fit htot hm_c
  have hstep : ExactExecRand w fastCutStep x _ :=
    ⟨hex_hdr.seqRand (ExecRand.branch_neg hnc_lt (ExecRand.branch_neg hnc_eq0
      (ExecRand.branch_pos hc_eq1 (hex_s1.seqRand hm_c)))),
    (exec_toExact_noSub hex_hdr rfl).seqRand (ExecRand.branch_neg hnc_lt
      (ExecRand.branch_neg hnc_eq0 (ExecRand.branch_pos hc_eq1
        ((exec_toExact_noSub hex_s1 rfl).seqRand hm_c_ex))))⟩
  refine ⟨_, ExactLoopSegment.single hc_loop hstep, fun z hz => ?_⟩
  simp only [Functor.map_map] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  rcases hsup_c z₀ hz₀ with ⟨_, hmod₀, rest⟩
  have hmod_s : Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k))
      x.mem y_s.mem := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    rw [hys_mem, Function.update_of_ne (by unfold frameSize at hfs_le; omega),
      Function.update_of_ne (by unfold frameSize at hfs_le; omega)]
  have hsub : Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k) ⊆
      Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
    intro a ha; rw [Finset.mem_Ico] at ha ⊢; omega
  have hstg_val : z₀.1.mem (fp + 2 + k * k) = 2 := by
    rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega), hys_mem,
      Function.update_of_ne (by omega), Function.update_self]
  have hv1_val : z₀.1.mem (fp + 3 + k * k) = v1 := by
    rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega), hys_mem, Function.update_self]
  exact ⟨modifies_trans_subset hmod_s hmod₀ Finset.Subset.rfl hsub, hstg_val, hv1_val, rest⟩

private theorem fastCutStep_stage2_exact {w fp parentFp b k v1 r2 : ℕ} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hr2 : x.regs retVal = r2)
    (hmem_p : x.mem fp = parentFp) (hmem_k : x.mem (fp + 1) = k)
    (hmem_stg : x.mem (fp + 2 + k * k) = 2) (hmem_v1 : x.mem (fp + 3 + k * k) = v1)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b) :
    ∃ (y : Data 24) (n_s2 : ℕ),
      ExactLoopSegment w (Cond.lt zero spReg) fastCutStep x (pure (y, n_s2)) ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = parentFp ∧
      y.regs spReg = b := by
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg hfit
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hr2_h : y_h.regs retVal = r2 := (hhi_h retVal (by decide)).trans hr2
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]; omega
  have hnc_eq0 : ¬(Cond.eq val2 zero).Holds y_h := by simp [Cond.holds_eq, hv2_h, h0_h]
  have hnc_eq1 : ¬(Cond.eq val2 one).Holds y_h := by simp [Cond.holds_eq, hv2_h, h1_h]
  obtain ⟨y_f, ⟨n_c, _, hex_c⟩, hm_f, h0_f, hfp_f, hsp_f, _⟩ :=
    combineAndPop_exec (by omega : 2 ≤ k) h0_h h1_h ha2_h hfp_h hsp_h hr2_h
      (hm_h ▸ hmem_p) (hm_h ▸ hmem_v1) hfit hsp_fit
  have hex_c_ex := combineAndPop_toExact h1_h hsp_h hex_c
  have hstep_std : Exec w fastCutStep x y_f (9 + (((n_c + 2) + 2) + 2)) :=
    hex_hdr.seq (.branch_neg hnc_lt (.branch_neg hnc_eq0 (.branch_neg hnc_eq1 hex_c)))
  have hstep_ex : Exec w (toExactCode fastCutStep) x y_f (9 + (((n_c + 2) + 2) + 2)) :=
    (exec_toExact_noSub hex_hdr rfl).seq
      (.branch_neg hnc_lt (.branch_neg hnc_eq0 (.branch_neg hnc_eq1 hex_c_ex)))
  exact ⟨y_f, _, ExactLoopSegment.detSingle hc_loop hstep_std hstep_ex,
    hm_f.trans hm_h, h0_f, hfp_f, hsp_f⟩

private theorem composeBranchExact {n w d' fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {P_frame : (ℕ → ℕ) → Prop} {d₀ : Data 24} {m_s : ProbComp (Data 24 × ℕ)}
    (hk7 : 7 ≤ k) (hd' : fastCutDepth (fastCutThreshold k) ≤ d')
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 1 + (d' + 1)))
    (hm_s : ExactLoopSegment w (Cond.lt zero spReg) fastCutStep d₀ m_s)
    (hsup_s : ∀ z ∈ m_s.support,
      let t := fastCutThreshold k
      let childFp := fp + frameSize k
      Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) d₀.mem z.1.mem ∧
      P_frame z.1.mem ∧
      z.1.regs zero = 0 ∧
      z.1.regs fpReg = childFp ∧
      z.1.regs spReg = b + 2 ∧
      z.1.mem childFp = fp ∧
      z.1.mem (childFp + 1) = t ∧
      z.1.mem (childFp + 2 + t * t) = 0 ∧
      ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
        IsContractionOf W₀ part' W' ∧
        HoldsMatrix z.1.mem (childFp + 2) t W')
    (hP_pres : ∀ m₁ m₂ : ℕ → ℕ,
      let t := fastCutThreshold k
      let childFp := fp + frameSize k
      Modifies (Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t)) m₁ m₂ →
      P_frame m₁ → P_frame m₂)
    (hih : ∀ {W_t : Fin (fastCutThreshold k) → Fin (fastCutThreshold k) → ℕ}
      {part_t : Fin n → Fin (fastCutThreshold k)} {x_c : Data 24},
      let t := fastCutThreshold k
      let childFp := fp + frameSize k
      2 ≤ t → fastCutDepth t ≤ d' →
      x_c.regs zero = 0 → x_c.regs fpReg = childFp → x_c.regs spReg = (b + 1) + 1 →
      x_c.mem childFp = fp → x_c.mem (childFp + 1) = t → x_c.mem (childFp + 2 + t * t) = 0 →
      HoldsMatrix x_c.mem (childFp + 2) t W_t → IsContractionOf W₀ part_t W_t →
      Fits w (childFp + fastCutScratch t) → Fits w ((b + 1) + 1 + d') →
      ∃ mc : ProbComp (Data 24 × ℕ),
        ExactLoopSegment w (Cond.lt zero spReg) fastCutStep x_c mc ∧
        ∀ zc ∈ mc.support,
          Modifies (Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t))
            x_c.mem zc.1.mem ∧
          zc.1.regs zero = 0 ∧
          zc.1.regs fpReg = fp ∧
          zc.1.regs spReg = b + 1) :
    ∃ m_br : ProbComp (Data 24 × ℕ),
      ExactLoopSegment w (Cond.lt zero spReg) fastCutStep d₀ m_br ∧
      ∀ z ∈ m_br.support,
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) d₀.mem z.1.mem ∧
        P_frame z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = fp ∧
        z.1.regs spReg = b + 1 := by
  let t := fastCutThreshold k
  let childFp := fp + frameSize k
  have ht2 : 2 ≤ t := fastCutThreshold_ge_two (by omega)
  have hscr_eq : fp + fastCutScratch k = childFp + fastCutScratch t := by
    dsimp only [childFp, t]; rw [fastCutScratch_of_ge_seven hk7]; omega
  have hfit_c : Fits w (childFp + fastCutScratch t) := hscr_eq ▸ hfit
  have hsp_c : Fits w ((b + 1) + 1 + d') := hsp_fit.of_le (by omega)
  let Q_c (dc : Data 24) (mc : ProbComp (Data 24 × ℕ)) : Prop :=
    ∀ zc ∈ mc.support,
      Modifies (Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t))
        dc.mem zc.1.mem ∧
      zc.1.regs zero = 0 ∧
      zc.1.regs fpReg = fp ∧
      zc.1.regs spReg = b + 1
  have hchild_ex : ∀ z₀ ∈ m_s.support,
      ∃ mc, ExactLoopSegment w (Cond.lt zero spReg) fastCutStep z₀.1 mc ∧ Q_c z₀.1 mc := by
    intro z₀ hz₀
    rcases hsup_s z₀ hz₀ with
      ⟨_, _, hz0, hzfp, hzsp, hm_cfp, hm_cfp1, hm_stg, W', part', hC', hmat'⟩
    exact hih ht2 hd' hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat' hC' hfit_c hsp_c
  obtain ⟨mc_fn, hseg_br, hmc_fn⟩ := hm_s.trans_exists hchild_ex
  refine ⟨_, hseg_br, fun z hz => ?_⟩
  obtain ⟨z₀, hz₀, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨zc, hzc, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  rcases hsup_s z₀ hz₀ with ⟨hmod₀, hP₀, _⟩
  rcases (hmc_fn z₀ hz₀).2 zc hzc with ⟨hmod_c, hz0, hzfp, hzsp⟩
  have hsub_c : Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t) ⊆
      Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
    intro a ha; rw [Finset.mem_Ico] at ha ⊢
    rw [hscr_eq]; dsimp only [childFp] at *; unfold frameSize at *; omega
  exact ⟨modifies_trans_subset hmod₀ hmod_c Finset.Subset.rfl hsub_c,
    hP_pres z₀.1.mem zc.1.mem hmod_c hP₀, hz0, hzfp, hzsp⟩

private theorem fastCutNode_exact {n w : ℕ} {W₀ : Fin n → Fin n → ℕ}
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∀ (d : ℕ) {fp parentFp b k : ℕ} {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k}
      {x : Data 24},
      2 ≤ k →
      fastCutDepth k ≤ d →
      x.regs zero = 0 →
      x.regs fpReg = fp →
      x.regs spReg = b + 1 →
      x.mem fp = parentFp →
      x.mem (fp + 1) = k →
      x.mem (fp + 2 + k * k) = 0 →
      HoldsMatrix x.mem (fp + 2) k W_k →
      IsContractionOf W₀ part W_k →
      Fits w (fp + fastCutScratch k) →
      Fits w (b + 1 + d) →
      ∃ m : ProbComp (Data 24 × ℕ),
        ExactLoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
        ∀ z ∈ m.support,
          Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
          z.1.regs zero = 0 ∧
          z.1.regs fpReg = parentFp ∧
          z.1.regs spReg = b := by
  intro d
  induction d with
  | zero =>
    intro fp parentFp b k W_k part x hk2 hd0 h0 hfp hsp hmem_p hmem_k _ hmat hC hfit hsp_fit
    have hk6 : k ≤ 6 := by
      by_contra hlt
      rw [fastCutDepth_of_ge_seven (by omega)] at hd0
      omega
    exact fastCutStep_base_exact hk2 hk6 h0 hfp hsp hmem_p hmem_k hmat hC hfit
      (hsp_fit.of_le (by omega)) htot
  | succ d' ih =>
    intro fp parentFp b k W_k part x hk2 hd h0 hfp hsp hmem_p hmem_k hmem_stg hmat hC hfit hsp_fit
    by_cases hk7 : 7 ≤ k
    · have hd' : fastCutDepth (fastCutThreshold k) ≤ d' := by
        rw [fastCutDepth_of_ge_seven hk7] at hd; omega
      have hfs_le : frameSize k ≤ fastCutScratch k := frameSize_le_fastCutScratch k
      have hsp_b2 : Fits w (b + 2) := hsp_fit.of_le (by omega)
      obtain ⟨m_s0, hm_s0, hsup_s0⟩ :=
        fastCutStep_stage0_exact hk7 h0 hfp hsp hmem_k hmem_stg hmat hC hfit hsp_b2 htot
      obtain ⟨m_b1, hseg_b1, hsup_b1⟩ :=
        composeBranchExact (P_frame := fun mem => mem (fp + 2 + k * k) = 1)
          hk7 hd' hfit hsp_fit hm_s0 hsup_s0
          (fun m₁ m₂ hmod h1 => by
            rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]; exact h1)
          (fun ht2 hd_c hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat_c hC_c hfit_c hsp_c =>
            ih ht2 hd_c hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat_c hC_c hfit_c hsp_c)
      let Q_b2 (d₁ : Data 24) (m₂ : ProbComp (Data 24 × ℕ)) : Prop :=
        ∀ zf ∈ m₂.support,
          Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) d₁.mem zf.1.mem ∧
          zf.1.regs zero = 0 ∧
          zf.1.regs fpReg = parentFp ∧
          zf.1.regs spReg = b
      have hb2_ex : ∀ z₁ ∈ m_b1.support,
          ∃ m₂, ExactLoopSegment w (Cond.lt zero spReg) fastCutStep z₁.1 m₂ ∧ Q_b2 z₁.1 m₂ := by
        intro z₁ hz₁
        rcases hsup_b1 z₁ hz₁ with ⟨hmod₁, hstg₁, hz1_0, hz1_fp, hz1_sp⟩
        let v₁ := z₁.1.regs retVal
        have hm1_p : z₁.1.mem fp = parentFp := by
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega)]; exact hmem_p
        have hm1_k : z₁.1.mem (fp + 1) = k := by
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega)]; exact hmem_k
        have hm1_mat : HoldsMatrix z₁.1.mem (fp + 2) k W_k := by
          intro i j
          have hlt : fp + 2 + i.val * k + j.val < fp + 2 + k * k :=
            matAddr_lt_end (le_refl k) i j
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega)]
          exact hmat i j
        obtain ⟨m_s1, hm_s1, hsup_s1⟩ :=
          fastCutStep_stage1_exact (v1 := v₁) hk7 hz1_0 hz1_fp hz1_sp rfl hm1_k hstg₁ hm1_mat
            hC hfit hsp_b2 htot
        obtain ⟨m_b2_pre, hseg_pre, hsup_pre⟩ :=
          composeBranchExact
            (P_frame := fun mem => mem (fp + 2 + k * k) = 2 ∧ mem (fp + 3 + k * k) = v₁)
            hk7 hd' hfit hsp_fit hm_s1
            (fun z hz => by
              rcases hsup_s1 z hz with ⟨hmod, hs2, hv, rest⟩
              exact ⟨hmod, ⟨hs2, hv⟩, rest⟩)
            (fun m₁ m₂ hmod ⟨hs2, hv⟩ => ⟨by
              rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]; exact hs2, by
              rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]; exact hv⟩)
            (fun ht2 hd_c hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat_c hC_c hfit_c hsp_c =>
              ih ht2 hd_c hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat_c hC_c hfit_c hsp_c)
        let Q_s2 (d₂ : Data 24) (ms2 : ProbComp (Data 24 × ℕ)) : Prop :=
          ∀ zf ∈ ms2.support,
            zf.1.mem = d₂.mem ∧
            zf.1.regs zero = 0 ∧
            zf.1.regs fpReg = parentFp ∧
            zf.1.regs spReg = b
        have hs2_ex : ∀ z₂ ∈ m_b2_pre.support,
            ∃ ms2, ExactLoopSegment w (Cond.lt zero spReg) fastCutStep z₂.1 ms2 ∧
              Q_s2 z₂.1 ms2 := by
          intro z₂ hz₂
          rcases hsup_pre z₂ hz₂ with ⟨hmod₂, ⟨hstg₂, hv1_₂⟩, hz2_0, hz2_fp, hz2_sp⟩
          have hm2_p : z₂.1.mem fp = parentFp := by
            rw [hmod₂ _ (by rw [Finset.mem_Ico]; omega)]; exact hm1_p
          have hm2_k : z₂.1.mem (fp + 1) = k := by
            rw [hmod₂ _ (by rw [Finset.mem_Ico]; omega)]; exact hm1_k
          obtain ⟨y_f, n_s2, hseg_f, hm_f, h0_f, hfp_f, hsp_f⟩ :=
            fastCutStep_stage2_exact hk7 hz2_0 hz2_fp hz2_sp rfl hm2_p hm2_k hstg₂ hv1_₂
              (hfit.of_le (by omega)) (hsp_fit.of_le (by omega))
          refine ⟨pure (y_f, n_s2), hseg_f, fun zf hzf => ?_⟩
          cases OracleComp.eq_of_mem_supportWith_pure hzf
          exact ⟨hm_f, h0_f, hfp_f, hsp_f⟩
        obtain ⟨ms2_fn, hseg_b2, hms2_fn⟩ := hseg_pre.trans_exists hs2_ex
        refine ⟨_, hseg_b2, fun zf hzf => ?_⟩
        obtain ⟨z₂, hz₂, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hzf
        obtain ⟨zs, hzs, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
        cases OracleComp.eq_of_mem_supportWith_pure hpure
        rcases hsup_pre z₂ hz₂ with ⟨hmod₂, _⟩
        rcases (hms2_fn z₂ hz₂).2 zs hzs with ⟨hm_s, h0_s, hfp_s, hsp_s⟩
        exact ⟨hm_s ▸ hmod₂, h0_s, hfp_s, hsp_s⟩
      obtain ⟨m₂_fn, hseg_tot, hm₂_fn⟩ := hseg_b1.trans_exists hb2_ex
      refine ⟨_, hseg_tot, fun z hz => ?_⟩
      obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
      obtain ⟨z₂, hz₂, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
      cases OracleComp.eq_of_mem_supportWith_pure hpure
      rcases hsup_b1 z₁ hz₁ with ⟨hmod₁, _⟩
      rcases (hm₂_fn z₁ hz₁).2 z₂ hz₂ with ⟨hmod₂, hz0, hzfp, hzsp⟩
      exact ⟨modifies_trans_subset hmod₁ hmod₂ Finset.Subset.rfl Finset.Subset.rfl,
        hz0, hzfp, hzsp⟩
    · exact fastCutStep_base_exact hk2 (by omega) h0 hfp hsp hmem_p hmem_k hmat hC hfit
        (hsp_fit.of_le (by omega)) htot

private theorem fastCutTree_toExact {n w sb : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 24}
    {m : ProbComp (Data 24 × ℕ)}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hsb : x.regs srcBase = sb) (hnOrig : x.regs nOrig = n)
    (hmat : HoldsMatrix x.mem sb n W)
    (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (htot : Fits w (totalDoubledWeight W))
    (hm : ExecRand (B := .standard) w fastCutTree x m) :
    ExecRand (B := .exact) w (toExactCode fastCutTree) x m := by
  let fp₀ := sb + n * n
  have hscr_le : fastCutScratch n ≤ 26 * (n * n) := fastCutScratch_le hn
  have hfs_le : frameSize n ≤ fastCutScratch n := frameSize_le_fastCutScratch n
  have hnn_ge : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have hfit_scr : Fits w (fp₀ + fastCutScratch n) := hws_fit.of_le (by dsimp only [fp₀]; omega)
  have hfit_fs : Fits w (fp₀ + frameSize n) := hfit_scr.of_le (by omega)
  have h0_fit : Fits w 0 := fits_zero w
  have h1_fit : Fits w 1 := hfit_fs.of_le (by unfold frameSize; omega)
  have hnn_fit : Fits w (n * n) := hfit_fs.of_le (by unfold frameSize; omega)
  have hfp_fit : Fits w fp₀ := hfit_fs.of_le (by omega)
  have hfp1_fit : Fits w (fp₀ + 1) := hfit_fs.of_le (by unfold frameSize; omega)
  have hfp2_fit : Fits w (fp₀ + 2) := hfit_fs.of_le (by unfold frameSize; omega)
  have hstg_fit : Fits w (fp₀ + 2 + n * n) := hfit_fs.of_le (by unfold frameSize; omega)
  let r₁ := x.set zero 0
  let r₂ := r₁.set one 1
  let r₃ := r₂.set rem (n * n)
  let r₄ := r₃.set fpReg fp₀
  let r₅ := r₄.write fp₀ 0
  let r₆ := r₅.set addr1 (fp₀ + 1)
  let r₇ := r₆.write (fp₀ + 1) n
  let r₈ := r₇.set uReg sb
  let x₁ := r₈.set wBase (fp₀ + 2)
  have hex_rset : Exec w fastCutRootSetup x x₁ 9 := by
    have s1 : Exec (B := .standard) w ram[zero ← #0] x r₁ 1 := Exec.const h0_fit
    have s2 : Exec (B := .standard) w ram[one ← #1] r₁ r₂ 1 := Exec.const h1_fit
    have s3 : Exec w ram[rem ← nOrig * nOrig] r₂ r₃ 1 := by
      have hn' : r₂.regs nOrig = n := by simpa +decide [r₂, r₁, Function.update_apply] using hnOrig
      simpa [r₃, BinOp.eval, hn'] using
        Exec.bin (f := .mul) (d := rem) (i := nOrig) (j := nOrig) (x := r₂)
          (by simpa [BinOp.eval, hn'] using hnn_fit)
    have s4 : Exec w ram[fpReg ← srcBase + rem] r₃ r₄ 1 := by
      have hsb' : r₃.regs srcBase = sb := by
        simpa +decide [r₃, r₂, r₁, Function.update_apply] using hsb
      have hr' : r₃.regs rem = n * n := by simp [r₃]
      simpa [r₄, BinOp.eval, hsb', hr', fp₀] using
        Exec.bin (f := .add) (d := fpReg) (i := srcBase) (j := rem) (x := r₃)
          (by simpa [BinOp.eval, hsb', hr', fp₀] using hfp_fit)
    have s5 : Exec (B := .standard) w ram[*fpReg ← zero] r₄ r₅ 1 := by
      have hfp' : r₄.regs fpReg = fp₀ := by simp [r₄]
      have hz' : r₄.regs zero = 0 := by simp +decide [r₄, r₃, r₂, r₁]
      simpa [r₅, hfp', hz'] using
        Exec.store (B := .standard) (w := w) (a := fpReg) (s := zero) (x := r₄)
    have s6 : Exec w ram[addr1 ← fpReg + one] r₅ r₆ 1 := by
      have hfp' : r₅.regs fpReg = fp₀ := by simp +decide [r₅, r₄]
      have h1' : r₅.regs one = 1 := by simp +decide [r₅, r₄, r₃, r₂]
      simpa [r₆, BinOp.eval, hfp', h1'] using
        Exec.bin (f := .add) (d := addr1) (i := fpReg) (j := one) (x := r₅)
          (by simpa [BinOp.eval, hfp', h1'] using hfp1_fit)
    have s7 : Exec (B := .standard) w ram[*addr1 ← nOrig] r₆ r₇ 1 := by
      have ha1 : r₆.regs addr1 = fp₀ + 1 := by simp [r₆]
      have hn' : r₆.regs nOrig = n := by
        simpa +decide [r₆, r₅, r₄, r₃, r₂, r₁, Function.update_apply] using hnOrig
      simpa [r₇, ha1, hn'] using
        Exec.store (B := .standard) (w := w) (a := addr1) (s := nOrig) (x := r₆)
    have s8 : Exec (B := .standard) w ram[uReg ← srcBase] r₇ r₈ 1 := by
      have hsb' : r₇.regs srcBase = sb := by
        simpa +decide [r₇, r₆, r₅, r₄, r₃, r₂, r₁, Function.update_apply] using hsb
      simpa [r₈, hsb'] using
        Exec.copy (B := .standard) (w := w) (d := uReg) (s := srcBase) (x := r₇)
    have s9 : Exec w ram[wBase ← addr1 + one] r₈ x₁ 1 := by
      have ha1 : r₈.regs addr1 = fp₀ + 1 := by simp +decide [r₈, r₇, r₆]
      have h1' : r₈.regs one = 1 := by simp +decide [r₈, r₇, r₆, r₅, r₄, r₃, r₂]
      have heq : (fp₀ + 1) + 1 = fp₀ + 2 := by omega
      simpa [x₁, BinOp.eval, ha1, h1', heq] using
        Exec.bin (f := .add) (d := wBase) (i := addr1) (j := one) (x := r₈)
          (by simpa [BinOp.eval, ha1, h1', heq] using hfp2_fit)
    unfold fastCutRootSetup
    exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq s9)))))))
  have hx₁_mem : x₁.mem = Function.update (Function.update x.mem fp₀ 0) (fp₀ + 1) n := rfl
  have hx₁_src : HoldsMatrix x₁.mem sb n W := by
    intro i j
    have hlt : sb + i.val * n + j.val < fp₀ := matAddr_lt_end (wb := sb) (le_refl n) i j
    rw [hx₁_mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hmat i j
  obtain ⟨x₂, ⟨_, _, hex_cp⟩, hmat_cp, hmod_cp, _, hwb₂, _, _, _, _, _⟩ :=
    ksCopyCode_exec (x := x₁) (sb := sb) (db := fp₀ + 2) (k := n) (W := W)
      (by simp +decide [x₁, r₈])
      (by simp [x₁])
      (by simp +decide [x₁, r₈, r₇, r₆, r₅, r₄, r₃])
      (by dsimp only [fp₀]; omega) h1_fit hstg_fit hx₁_src
  have hn_x₂ : x₂.regs nOrig = n :=
    (hex_cp.regs_eq (by decide)).trans (hex_rset.regs_eq (by decide) |>.trans hnOrig)
  have hfp_x₂ : x₂.regs fpReg = fp₀ := by
    rw [hex_cp.regs_eq (by decide)]
    simp +decide [x₁, r₈, r₇, r₆, r₅, r₄]
  let q₁ := x₂.set zero 0
  let q₂ := q₁.set one 1
  let q₃ := q₂.set rem (n * n)
  let q₄ := q₃.set addr2 (fp₀ + 2 + n * n)
  let q₅ := q₄.write (fp₀ + 2 + n * n) 0
  let x₃ := q₅.set spReg 1
  have hex_rfin : Exec w fastCutRootFinish x₂ x₃ 6 := by
    have s1 : Exec (B := .standard) w ram[zero ← #0] x₂ q₁ 1 := Exec.const h0_fit
    have s2 : Exec (B := .standard) w ram[one ← #1] q₁ q₂ 1 := Exec.const h1_fit
    have s3 : Exec w ram[rem ← nOrig * nOrig] q₂ q₃ 1 := by
      have hn' : q₂.regs nOrig = n := by
        simpa +decide [q₂, q₁, Function.update_apply] using hn_x₂
      simpa [q₃, BinOp.eval, hn'] using
        Exec.bin (f := .mul) (d := rem) (i := nOrig) (j := nOrig) (x := q₂)
          (by simpa [BinOp.eval, hn'] using hnn_fit)
    have s4 : Exec w ram[addr2 ← wBase + rem] q₃ q₄ 1 := by
      have hwb' : q₃.regs wBase = fp₀ + 2 := by
        simpa +decide [q₃, q₂, q₁, Function.update_apply] using hwb₂
      have hr' : q₃.regs rem = n * n := by simp [q₃]
      simpa [q₄, BinOp.eval, hwb', hr'] using
        Exec.bin (f := .add) (d := addr2) (i := wBase) (j := rem) (x := q₃)
          (by simpa [BinOp.eval, hwb', hr'] using hstg_fit)
    have s5 : Exec (B := .standard) w ram[*addr2 ← zero] q₄ q₅ 1 := by
      have ha2 : q₄.regs addr2 = fp₀ + 2 + n * n := by simp [q₄]
      have hz' : q₄.regs zero = 0 := by simp +decide [q₄, q₃, q₂, q₁]
      simpa [q₅, ha2, hz'] using
        Exec.store (B := .standard) (w := w) (a := addr2) (s := zero) (x := q₄)
    have s6 : Exec (B := .standard) w ram[spReg ← #1] q₅ x₃ 1 := Exec.const h1_fit
    unfold fastCutRootFinish
    exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))
  have hx₃_mem : x₃.mem = Function.update x₂.mem (fp₀ + 2 + n * n) 0 := rfl
  have hx₃_p : x₃.mem fp₀ = 0 := by
    rw [hx₃_mem, Function.update_of_ne (by omega), hmod_cp _ (by rw [Finset.mem_Ico]; omega),
      hx₁_mem, Function.update_of_ne (by omega), Function.update_self]
  have hx₃_k : x₃.mem (fp₀ + 1) = n := by
    rw [hx₃_mem, Function.update_of_ne (by omega), hmod_cp _ (by rw [Finset.mem_Ico]; omega),
      hx₁_mem, Function.update_self]
  have hx₃_stg : x₃.mem (fp₀ + 2 + n * n) = 0 := by rw [hx₃_mem, Function.update_self]
  have hx₃_mat : HoldsMatrix x₃.mem (fp₀ + 2) n W := by
    intro i j
    have hlt : fp₀ + 2 + i.val * n + j.val < fp₀ + 2 + n * n := matAddr_lt_end (le_refl n) i j
    rw [hx₃_mem, Function.update_of_ne (by omega)]
    exact hmat_cp i j
  obtain ⟨m_seg, hseg, hsup_seg⟩ :=
    fastCutNode_exact htot (2 * Nat.log 2 n) (b := 0) (parentFp := 0)
      hn (fastCutDepth_le_two_mul_log n)
      (by simp +decide [x₃, q₅, q₄, q₃, q₂, q₁])
      (by simpa +decide [x₃, q₅, q₄, q₃, q₂, q₁, Function.update_apply] using hfp_x₂)
      (by simp [x₃])
      hx₃_p hx₃_k hx₃_stg hx₃_mat (isContractionOf_id hW) hfit_scr
      (by simpa only [Nat.zero_add, Nat.add_comm 1] using hsp_fit)
  have hex_loop : ExactExecRand w fastCutLoop x₃ _ :=
    hseg.finish fun z hz => by
      rcases hsup_seg z hz with ⟨_, hz0, _, hzsp⟩
      simp [Cond.holds_lt, hz0, hzsp]
  have hno_cp : noSubDivMod ksCopyCode = true := by
    rw [ksCopyCode, noSubDivMod_rename]; rfl
  have hex : ExactExecRand w fastCutTree x _ :=
    ExactExecRand.seqExec_noSub rfl hex_rset
      (ExactExecRand.seqExec_noSub hno_cp hex_cp
        (ExactExecRand.seqExec_noSub rfl hex_rfin hex_loop))
  exact hex.toExact hm

private theorem fastCutCode_toExact {n w : ℕ} {W : Fin n → Fin n → ℕ}
    {m : ProbComp (Data 24 × ℕ)} (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W))
    (hm : ExecRand (B := .standard) w fastCutCode (Data.init (n :: flattenMatrix W)) m) :
    ExecRand (B := .exact) w (toExactCode fastCutCode) (Data.init (n :: flattenMatrix W)) m := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hsp : Fits w (2 * Nat.log 2 n + 1) := by
    have := Nat.log_lt_self 2 (by omega : n ≠ 0)
    have := Nat.le_mul_self n
    exact hws.of_le (by omega)
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s⟩ := fastCutSetup_exec (W := W) hn hw
  obtain ⟨m_t, hm_t, _, _, _⟩ :=
    fastCutTree_spec hn hW hsb_s hn_s (hm_s ▸ holdsMatrix_init_fastCut W) hws hsp htot
  have hm_t_ex :=
    fastCutTree_toExact hn hW hsb_s hn_s (hm_s ▸ holdsMatrix_init_fastCut W) hws hsp htot hm_t
  exact (ExactExecRand.seqExec_noSub rfl e_s ⟨hm_t, hm_t_ex⟩).toExact hm

private theorem fastCutAmpBody_toExact {w sb n R i : ℕ} {W : Fin n → Fin n → ℕ}
    {mem₀ : ℕ → ℕ} {x : Data 24} {m : ProbComp (Data 24 × ℕ)}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hiR : i < R)
    (h1 : Fits w 1) (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hinv : KSAmpInv sb n R i W mem₀ x)
    (hm : ExecRand (B := .standard) w fastCutAmpBody x m) :
    ExecRand (B := .exact) w (toExactCode fastCutAmpBody) x m := by
  obtain ⟨m_t, hm_t, _, hsup_t, _⟩ :=
    fastCutTree_spec hn hW hinv.regs_srcBase hinv.regs_nOrig hinv.src_matrix hws_fit hsp_fit htot
  have hm_t_ex :=
    fastCutTree_toExact hn hW hinv.regs_srcBase hinv.regs_nOrig hinv.src_matrix hws_fit hsp_fit htot
      hm_t
  let m_post (d : Data 24) := codeComp (B := .standard) w fastCutAmpPost d
  have hex : ExactExecRand w fastCutAmpBody x
      (do let z₁ ← m_t; let z₂ ← m_post z₁.1; pure (z₂.1, z₁.2 + z₂.2)) := by
    refine ⟨ExecRand.seq hm_t fun z hz => ?_, ExecRand.seq hm_t_ex fun z hz => ?_⟩
    · have hti : z.1.regs trialIdx = i := (hsup_t z hz).2.2.2.2.2.1.trans hinv.regs_trialIdx
      obtain ⟨_, ⟨_, _, e_p⟩, _⟩ := fastCutAmpPost_exec hti hiR h1 hR_fit
      dsimp only [m_post]
      rw [e_p.execRand.codeComp_eq]
      exact e_p.execRand
    · have hti : z.1.regs trialIdx = i := (hsup_t z hz).2.2.2.2.2.1.trans hinv.regs_trialIdx
      obtain ⟨_, ⟨_, _, e_p⟩, _⟩ := fastCutAmpPost_exec hti hiR h1 hR_fit
      dsimp only [m_post]
      rw [e_p.execRand.codeComp_eq]
      exact (exec_toExact_noSub e_p rfl).execRand
  exact hex.toExact hm

private theorem fastCutAmpLoop_exact {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (h1 : Fits w 1) (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ∀ (remTrials i : ℕ) (x : Data 24),
      i + remTrials = R → KSAmpInv sb n R i W mem₀ x →
      ∃ m : ProbComp (Data 24 × ℕ), ExactExecRand w fastCutAmpLoop x m
  | 0, i, x, hsum, hinv => by
    have hi_eq : i = R := by omega
    have hnc : ¬(Cond.lt trialIdx numTrials).Holds x := by
      simp [Cond.holds_lt, hinv.regs_trialIdx, hinv.regs_numTrials, hi_eq]
    exact ⟨pure (x, 2), .loop_exit hnc, .loop_exit hnc⟩
  | r + 1, i, x, hsum, hinv => by
    have hiR : i < R := by omega
    have hc : (Cond.lt trialIdx numTrials).Holds x := by
      simp [Cond.holds_lt, hinv.regs_trialIdx, hinv.regs_numTrials, hiR]
    obtain ⟨m_b, hm_b, _, hsup_b, _⟩ :=
      fastCutAmpBody_spec hn hW hiR h1 hws_fit hsp_fit hR_fit htot hinv
    have hm_b_ex := fastCutAmpBody_toExact hn hW hiR h1 hws_fit hsp_fit hR_fit htot hinv hm_b
    let ml (d : Data 24) := codeComp (B := .standard) w fastCutAmpLoop d
    refine ⟨_, ExecRand.loop_iter hc hm_b (ml := ml) ?_,
      ExecRand.loop_iter hc hm_b_ex (ml := ml) ?_⟩
    · intro z hz
      obtain ⟨m_r, hm_r⟩ := fastCutAmpLoop_exact hn hW h1 hws_fit hsp_fit hR_fit htot r (i + 1) z.1
        (by omega) (hsup_b z hz).2.1
      dsimp only [ml]
      rw [hm_r.1.codeComp_eq]
      exact hm_r.1
    · intro z hz
      obtain ⟨m_r, hm_r⟩ := fastCutAmpLoop_exact hn hW h1 hws_fit hsp_fit hR_fit htot r (i + 1) z.1
        (by omega) (hsup_b z hz).2.1
      dsimp only [ml]
      rw [hm_r.1.codeComp_eq]
      exact hm_r.2

private theorem fastCutHighProbCode_toExact {n w : ℕ} {W : Fin n → Fin n → ℕ}
    {m : ProbComp (Data 24 × ℕ)} (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W))
    (hm : ExecRand (B := .standard) w fastCutHighProbCode (Data.init (n :: flattenMatrix W)) m) :
    ExecRand (B := .exact) w (toExactCode fastCutHighProbCode)
      (Data.init (n :: flattenMatrix W)) m := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hsp : Fits w (2 * Nat.log 2 n + 1) := by
    have := Nat.log_lt_self 2 (by omega : n ≠ 0)
    have := Nat.le_mul_self n
    exact hws.of_le (by omega)
  have h1 : Fits w 1 := hws.of_le (by omega)
  have hhp_fit := fits_fastCutTrials_of_logWidth_four hn hw
  obtain ⟨y_s, ⟨_, _, e_s⟩, hm_s, hsb_s, hn_s_r, hnt_s, hti_s, _⟩ :=
    fastCutHighProbSetup_exec (W := W) hn hw
  have hinv₀ : KSAmpInv 2 n (fastCutTrials n) 0 W
      (Data.init (r := 24) (n :: flattenMatrix W)).mem y_s :=
    ⟨hsb_s, hn_s_r, hnt_s, hti_s, hm_s ▸ holdsMatrix_init_fastCut W,
      hm_s ▸ Modifies.refl _ _, fun h0 => absurd h0 (by omega)⟩
  obtain ⟨_, hex_l⟩ :=
    fastCutAmpLoop_exact hn hW h1 hws hsp hhp_fit htot (fastCutTrials n) 0 y_s
      (Nat.zero_add _) hinv₀
  exact (ExactExecRand.seqExec_noSub rfl e_s hex_l).toExact hm

end KargerSteinLift

end EndpointLifts

/-! ## Compiled `Basis.exact` programs and polymorphic `Presentation` transport -/

/-- Single-trial Karger contraction compiled over `Basis.exact`. -/
def singleExactProgram : Program .exact 16 :=
  (toExactCode singleCode).program Reg.val1

/-- `R`-trial amplified Karger compiled over `Basis.exact`. -/
def amplifiedExactProgram : Program .exact 22 :=
  (toExactCode amplifiedCode).program AmpReg.bestVal

/-- `O(n ^ 4 log n)` high-probability Karger compiled over `Basis.exact`. -/
def highProbExactProgram : Program .exact 22 :=
  (toExactCode highProbCode).program AmpReg.bestVal

private theorem singleExactProgram_runRand_eq {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hw : logWidth 3 n ≤ w)
    (htot : Fits w (totalDoubledWeight W)) :
    Cslib.WordRAM.runRand w singleExactProgram (singleTime n)
        (.running (.init (n :: flattenMatrix W))) =
      Cslib.WordRAM.runRand w singleProgram (singleTime n)
        (.running (.init (n :: flattenMatrix W))) := by
  obtain ⟨m, hm_std, _, hsup, _⟩ := singleCode_spec hn hW hw htot
  have hm_ex := singleCode_toExact hn hW hw htot hm_std
  exact (hm_ex.runRand_program Reg.val1 fun z hz => (hsup z hz).1).trans
    (hm_std.runRand_program Reg.val1 fun z hz => (hsup z hz).1).symm

private theorem amplifiedExactProgram_runRand_eq {R n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W) (hw : logWidth 3 n ≤ w)
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    Cslib.WordRAM.runRand w amplifiedExactProgram (amplifiedTime R n)
        (.running (.init (R :: n :: flattenMatrix W))) =
      Cslib.WordRAM.runRand w amplifiedProgram (amplifiedTime R n)
        (.running (.init (R :: n :: flattenMatrix W))) := by
  obtain ⟨m, hm_std, _, hsup, _⟩ := amplifiedCode_spec hR hn hW hw hR_fit htot
  have hm_ex := amplifiedCode_toExact hn hW hw hR_fit htot hm_std
  exact (hm_ex.runRand_program AmpReg.bestVal fun z hz => (hsup z hz).1).trans
    (hm_std.runRand_program AmpReg.bestVal fun z hz => (hsup z hz).1).symm

private theorem highProbExactProgram_runRand_eq {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hw : logWidth 3 n ≤ w)
    (htot : Fits w (totalDoubledWeight W)) :
    Cslib.WordRAM.runRand w highProbExactProgram (highProbTime n)
        (.running (.init (n :: flattenMatrix W))) =
      Cslib.WordRAM.runRand w highProbProgram (highProbTime n)
        (.running (.init (n :: flattenMatrix W))) := by
  obtain ⟨m, hm_std, _, hsup, _⟩ := highProbCode_spec hn hW hw htot
  have hm_ex := highProbCode_toExact hn hW hw htot hm_std
  exact (hm_ex.runRand_program AmpReg.bestVal fun z hz => (hsup z hz).1).trans
    (hm_std.runRand_program AmpReg.bestVal fun z hz => (hsup z hz).1).symm

private theorem init_mem_eq {r : ℕ} (input : List ℕ) :
    (Data.init (r := r) input).mem = Presentation.initMem input := by
  funext a
  rcases a with _ | a <;> simp [Presentation.initMem, Data.init]

/-- **Single-trial Karger contraction** transported to any presentation `S` satisfying `Laws S`. -/
theorem kargerSingleTrial (S : Presentation) (h : Laws S) :
    ∃ p : List (S.Instr 16),
      ∀ (n w : ℕ) (W : Fin n → Fin n → ℕ),
        2 ≤ n →
        IsMultigraph W →
        3 * (Nat.log 2 n + 1) ≤ w →
        (∑ u : Fin n, ∑ v : Fin n, W u v) < 2 ^ w →
        let input := n :: (List.finRange n).flatMap fun u => (List.finRange n).map fun v => W u v
        let T := 42 * n ^ 2 + 12 * n + 21
        S.HaltsWithin (r := 16) w p (S.init input) T ∧
        S.RandCallsBounded (r := 16) w p (S.init input) T (n - 2) ∧
        (∀ cfg ∈ (S.evalRand (r := 16) w p T (S.init input)).support,
          ∃ (reg : Fin 16 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = S.halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 2 ∨ 2 + n * n + n ≤ a → mem a = Presentation.initMem input a)) ∧
        (0 < minCut W →
          (2 : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal) ≤
            (S.evalRand (r := 16) w p T (S.init input)).toOuterMeasure
              {cfg | ∃ reg mem, cfg = S.halted (minCut W) reg mem}) := by
  refine ⟨S.programOf singleExactProgram, fun n w W hn hW hw htot => ?_⟩
  dsimp only
  rw [flatMap_finRange_eq_flattenMatrix]
  have hw' : logWidth 3 n ≤ w := hw
  have htot' : Fits w (totalDoubledWeight W) := htot
  obtain ⟨hHalts, hCalls, hPost, hProb⟩ := singleProgram_spec hn hW hw' htot'
  have hrun_eq := singleExactProgram_runRand_eq hn hW hw' htot'
  have heval_eq : Cslib.WordRAM.evalRand w singleExactProgram (singleTime n)
      (.init (n :: flattenMatrix W)) =
    Cslib.WordRAM.evalRand w singleProgram (singleTime n)
      (.init (n :: flattenMatrix W)) := by
    unfold Cslib.WordRAM.evalRand
    rw [hrun_eq]
  unfold singleTime at hHalts hCalls hPost hProb hrun_eq heval_eq
  have hinit := Presentation.init_state_eq (r := 16) (n :: flattenMatrix W)
  have hmem0 := init_mem_eq (r := 16) (n :: flattenMatrix W)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Presentation.init, S.haltsWithin_iff h, ← hinit]
    unfold Cslib.WordRAM.RandHaltsWithin
    rwa [hrun_eq]
  · rw [Presentation.init, S.randCallsBounded_iff h, ← hinit]
    unfold Cslib.WordRAM.RandCallsBounded
    rwa [hrun_eq]
  · intro cfg hcfg
    rw [Presentation.init, S.evalRand_eq h, ← hinit, PMF.mem_support_map_iff] at hcfg
    obtain ⟨cfg', hcfg', rfl⟩ := hcfg
    rw [Cslib.WordRAM.support_evalRand, hrun_eq] at hcfg'
    obtain ⟨y, C, rfl, hbnd, hC, hle, hmod⟩ := hPost cfg' hcfg'
    refine ⟨y.regs, y.mem, C, rfl, hbnd.1, hbnd.2, hC, hle, fun a ha => ?_⟩
    rw [← hmem0]
    exact hmod a (by rw [Finset.mem_Ico]; omega)
  · intro hpos
    rw [Presentation.init, S.evalRand_eq h, ← hinit, heval_eq, PMF.toOuterMeasure_map_apply]
    refine (hProb hpos).trans (PMF.toOuterMeasure_mono _ ?_)
    rintro cfg' ⟨⟨y, rfl⟩, -⟩
    exact ⟨y.regs, y.mem, rfl⟩

/-- **`R`-trial amplified Karger** transported to any presentation `S` satisfying `Laws S`. -/
theorem kargerAmplified (S : Presentation) (h : Laws S) :
    ∃ p : List (S.Instr 22),
      ∀ (R n w : ℕ) (W : Fin n → Fin n → ℕ),
        1 ≤ R →
        2 ≤ n →
        IsMultigraph W →
        3 * (Nat.log 2 n + 1) ≤ w →
        R < 2 ^ w →
        (∑ u : Fin n, ∑ v : Fin n, W u v) < 2 ^ w →
        let input :=
          R :: n :: (List.finRange n).flatMap fun u => (List.finRange n).map fun v => W u v
        let T := R * (50 * n ^ 2 + 12 * n + 30) + 16
        S.HaltsWithin (r := 22) w p (S.init input) T ∧
        S.RandCallsBounded (r := 22) w p (S.init input) T (R * (n - 2)) ∧
        (∀ cfg ∈ (S.evalRand (r := 22) w p T (S.init input)).support,
          ∃ (reg : Fin 22 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = S.halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 3 + n * n ∨ 3 + 2 * (n * n) + n ≤ a →
              mem a = Presentation.initMem input a)) ∧
        (0 < minCut W →
          (S.evalRand (r := 22) w p T (S.init input)).toOuterMeasure
              {cfg | ∀ reg mem, cfg ≠ S.halted (minCut W) reg mem} ≤
            ((1 : ENNReal) - (2 : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal)) ^ R) := by
  refine ⟨S.programOf amplifiedExactProgram, fun R n w W hR hn hW hw hRf htot => ?_⟩
  dsimp only
  rw [flatMap_finRange_eq_flattenMatrix]
  have hw' : logWidth 3 n ≤ w := hw
  have hR_fit : Fits w R := hRf
  have htot' : Fits w (totalDoubledWeight W) := htot
  obtain ⟨hHalts, hCalls, hPost, hFail⟩ := amplifiedProgram_spec hR hn hW hw' hR_fit htot'
  have hrun_eq := amplifiedExactProgram_runRand_eq hR hn hW hw' hR_fit htot'
  have heval_eq : Cslib.WordRAM.evalRand w amplifiedExactProgram (amplifiedTime R n)
      (.init (R :: n :: flattenMatrix W)) =
    Cslib.WordRAM.evalRand w amplifiedProgram (amplifiedTime R n)
      (.init (R :: n :: flattenMatrix W)) := by
    unfold Cslib.WordRAM.evalRand
    rw [hrun_eq]
  unfold amplifiedTime at hHalts hCalls hPost hFail hrun_eq heval_eq
  have hinit := Presentation.init_state_eq (r := 22) (R :: n :: flattenMatrix W)
  have hmem0 := init_mem_eq (r := 22) (R :: n :: flattenMatrix W)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Presentation.init, S.haltsWithin_iff h, ← hinit]
    unfold Cslib.WordRAM.RandHaltsWithin
    rwa [hrun_eq]
  · rw [Presentation.init, S.randCallsBounded_iff h, ← hinit]
    unfold Cslib.WordRAM.RandCallsBounded
    rwa [hrun_eq]
  · intro cfg hcfg
    rw [Presentation.init, S.evalRand_eq h, ← hinit, PMF.mem_support_map_iff] at hcfg
    obtain ⟨cfg', hcfg', rfl⟩ := hcfg
    rw [Cslib.WordRAM.support_evalRand, hrun_eq] at hcfg'
    obtain ⟨y, C, rfl, hbnd, hC, hle, hmod⟩ := hPost cfg' hcfg'
    refine ⟨y.regs, y.mem, C, rfl, hbnd.1, hbnd.2, hC, hle, fun a ha => ?_⟩
    rw [← hmem0]
    exact hmod a (by rw [Finset.mem_Ico]; omega)
  · intro hpos
    rw [Presentation.init, S.evalRand_eq h, ← hinit, heval_eq, PMF.toOuterMeasure_map_apply]
    refine (PMF.toOuterMeasure_mono _ ?_).trans (hFail hpos)
    rintro cfg' ⟨hnot, -⟩ y rfl
    exact hnot y.regs y.mem rfl

/-- **High-probability `O(n ^ 4 log n)` global minimum cut** transported to any presentation `S`
satisfying `Laws S`. -/
theorem kargerHighProb (S : Presentation) (h : Laws S) :
    ∃ p : List (S.Instr 22),
      ∀ (n w : ℕ) (W : Fin n → Fin n → ℕ),
        2 ≤ n →
        IsMultigraph W →
        3 * (Nat.log 2 n + 1) ≤ w →
        (∑ u : Fin n, ∑ v : Fin n, W u v) < 2 ^ w →
        let input := n :: (List.finRange n).flatMap fun u => (List.finRange n).map fun v => W u v
        let T := 33 * n ^ 4 * (Nat.log 2 n + 2)
        let R := (n * (n - 1) / 2) * (Nat.log 2 n + 2)
        S.HaltsWithin (r := 22) w p (S.init input) T ∧
        S.RandCallsBounded (r := 22) w p (S.init input) T (R * (n - 2)) ∧
        (∀ cfg ∈ (S.evalRand (r := 22) w p T (S.init input)).support,
          ∃ (reg : Fin 22 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = S.halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 2 + n * n ∨ 2 + 2 * (n * n) + n ≤ a →
              mem a = Presentation.initMem input a)) ∧
        (0 < minCut W →
          (S.evalRand (r := 22) w p T (S.init input)).toOuterMeasure
              {cfg | ∀ reg mem, cfg ≠ S.halted (minCut W) reg mem} ≤
            (1 : ENNReal) / ((2 * n : ℕ) : ENNReal)) := by
  refine ⟨S.programOf highProbExactProgram, fun n w W hn hW hw htot => ?_⟩
  dsimp only
  rw [flatMap_finRange_eq_flattenMatrix]
  have hw' : logWidth 3 n ≤ w := hw
  have htot' : Fits w (totalDoubledWeight W) := htot
  obtain ⟨hHalts, hCalls, hPost, hFail⟩ := highProbProgram_spec hn hW hw' htot'
  have hrun_eq := highProbExactProgram_runRand_eq hn hW hw' htot'
  have heval_eq : Cslib.WordRAM.evalRand w highProbExactProgram (highProbTime n)
      (.init (n :: flattenMatrix W)) =
    Cslib.WordRAM.evalRand w highProbProgram (highProbTime n)
      (.init (n :: flattenMatrix W)) := by
    unfold Cslib.WordRAM.evalRand
    rw [hrun_eq]
  unfold highProbTime at hHalts hCalls hPost hFail hrun_eq heval_eq
  unfold highProbTrials at hCalls
  have hinit := Presentation.init_state_eq (r := 22) (n :: flattenMatrix W)
  have hmem0 := init_mem_eq (r := 22) (n :: flattenMatrix W)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Presentation.init, S.haltsWithin_iff h, ← hinit]
    unfold Cslib.WordRAM.RandHaltsWithin
    rwa [hrun_eq]
  · rw [Presentation.init, S.randCallsBounded_iff h, ← hinit]
    unfold Cslib.WordRAM.RandCallsBounded
    rwa [hrun_eq]
  · intro cfg hcfg
    rw [Presentation.init, S.evalRand_eq h, ← hinit, PMF.mem_support_map_iff] at hcfg
    obtain ⟨cfg', hcfg', rfl⟩ := hcfg
    rw [Cslib.WordRAM.support_evalRand, hrun_eq] at hcfg'
    obtain ⟨y, C, rfl, hbnd, hC, hle, hmod⟩ := hPost cfg' hcfg'
    refine ⟨y.regs, y.mem, C, rfl, hbnd.1, hbnd.2, hC, hle, fun a ha => ?_⟩
    rw [← hmem0]
    exact hmod a (by rw [Finset.mem_Ico]; omega)
  · intro hpos
    rw [Presentation.init, S.evalRand_eq h, ← hinit, heval_eq, PMF.toOuterMeasure_map_apply]
    refine (PMF.toOuterMeasure_mono _ ?_).trans (hFail hpos)
    rintro cfg' ⟨hnot, -⟩ y rfl
    exact hnot y.regs y.mem rfl

/-- Single-tree `O(n ^ 2 log n)` Karger–Stein `FastCut` compiled over `Basis.exact`. -/
def fastCutExactProgram : Program .exact 24 :=
  (toExactCode fastCutCode).program KSReg.retVal

/-- `O(n ^ 2 log ^ 3 n)` high-probability Karger–Stein compiled over `Basis.exact`. -/
def fastCutHighProbExactProgram : Program .exact 24 :=
  (toExactCode fastCutHighProbCode).program KSReg.bestVal

private theorem fastCutExactProgram_runRand_eq {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hw : logWidth 4 n ≤ w)
    (htot : Fits w (totalDoubledWeight W)) :
    Cslib.WordRAM.runRand w fastCutExactProgram (fastCutTime n)
        (.running (.init (n :: flattenMatrix W))) =
      Cslib.WordRAM.runRand w fastCutProgram (fastCutTime n)
        (.running (.init (n :: flattenMatrix W))) := by
  obtain ⟨m, hm_std, _, hsup, _⟩ := fastCutCode_spec hn hW hw htot
  have hm_ex := fastCutCode_toExact hn hW hw htot hm_std
  exact (hm_ex.runRand_program KSReg.retVal fun z hz => (hsup z hz).1).trans
    (hm_std.runRand_program KSReg.retVal fun z hz => (hsup z hz).1).symm

private theorem fastCutHighProbExactProgram_runRand_eq {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hw : logWidth 4 n ≤ w)
    (htot : Fits w (totalDoubledWeight W)) :
    Cslib.WordRAM.runRand w fastCutHighProbExactProgram (fastCutHighProbTime n)
        (.running (.init (n :: flattenMatrix W))) =
      Cslib.WordRAM.runRand w fastCutHighProbProgram (fastCutHighProbTime n)
        (.running (.init (n :: flattenMatrix W))) := by
  obtain ⟨m, hm_std, _, hsup, _⟩ := fastCutHighProbCode_spec hn hW hw htot
  have hm_ex := fastCutHighProbCode_toExact hn hW hw htot hm_std
  exact (hm_ex.runRand_program KSReg.bestVal fun z hz => (hsup z hz).1).trans
    (hm_std.runRand_program KSReg.bestVal fun z hz => (hsup z hz).1).symm

/-- **Single-tree `O(n ^ 2 log n)` Karger–Stein `FastCut`** transported to any presentation `S`
satisfying `Laws S`. -/
theorem kargerSteinFastCut (S : Presentation) (h : Laws S) :
    ∃ p : List (S.Instr 24),
      ∀ (n w : ℕ) (W : Fin n → Fin n → ℕ),
        2 ≤ n →
        IsMultigraph W →
        4 * (Nat.log 2 n + 1) ≤ w →
        (∑ u : Fin n, ∑ v : Fin n, W u v) < 2 ^ w →
        let input := n :: (List.finRange n).flatMap fun u => (List.finRange n).map fun v => W u v
        let T := 2500 * n ^ 2 * (Nat.log 2 n + 2)
        S.HaltsWithin (r := 24) w p (S.init input) T ∧
        S.RandCallsBounded (r := 24) w p (S.init input) T (6 * (n * n)) ∧
        (∀ cfg ∈ (S.evalRand (r := 24) w p T (S.init input)).support,
          ∃ (reg : Fin 24 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = S.halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 2 + n * n ∨ 2 + 27 * (n * n) ≤ a →
              mem a = Presentation.initMem input a)) ∧
        (0 < minCut W →
          (1 : ENNReal) / ((Nat.log 2 n + 15 : ℕ) : ENNReal) ≤
            (S.evalRand (r := 24) w p T (S.init input)).toOuterMeasure
              {cfg | ∃ reg mem, cfg = S.halted (minCut W) reg mem}) := by
  refine ⟨S.programOf fastCutExactProgram, fun n w W hn hW hw htot => ?_⟩
  dsimp only
  rw [flatMap_finRange_eq_flattenMatrix]
  have hw' : logWidth 4 n ≤ w := hw
  have htot' : Fits w (totalDoubledWeight W) := htot
  obtain ⟨hHalts, hCalls, hPost, hProb⟩ := fastCutProgram_spec hn hW hw' htot'
  have hCalls' : Cslib.WordRAM.RandCallsBounded w fastCutProgram
      (.init (n :: flattenMatrix W)) (fastCutTime n) (6 * (n * n)) :=
    OracleComp.IsCostBounded.mono hCalls (fastCutNodeQueries_le hn)
  have hrun_eq := fastCutExactProgram_runRand_eq hn hW hw' htot'
  have heval_eq : Cslib.WordRAM.evalRand w fastCutExactProgram (fastCutTime n)
      (.init (n :: flattenMatrix W)) =
    Cslib.WordRAM.evalRand w fastCutProgram (fastCutTime n)
      (.init (n :: flattenMatrix W)) := by
    unfold Cslib.WordRAM.evalRand
    rw [hrun_eq]
  unfold fastCutTime at hHalts hCalls' hPost hProb hrun_eq heval_eq
  have hinit := Presentation.init_state_eq (r := 24) (n :: flattenMatrix W)
  have hmem0 := init_mem_eq (r := 24) (n :: flattenMatrix W)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Presentation.init, S.haltsWithin_iff h, ← hinit]
    unfold Cslib.WordRAM.RandHaltsWithin
    rwa [hrun_eq]
  · rw [Presentation.init, S.randCallsBounded_iff h, ← hinit]
    unfold Cslib.WordRAM.RandCallsBounded
    rwa [hrun_eq]
  · intro cfg hcfg
    rw [Presentation.init, S.evalRand_eq h, ← hinit, PMF.mem_support_map_iff] at hcfg
    obtain ⟨cfg', hcfg', rfl⟩ := hcfg
    rw [Cslib.WordRAM.support_evalRand, hrun_eq] at hcfg'
    obtain ⟨y, C, rfl, hbnd, hC, hle, hmod⟩ := hPost cfg' hcfg'
    refine ⟨y.regs, y.mem, C, rfl, hbnd.1, hbnd.2, hC, hle, fun a ha => ?_⟩
    rw [← hmem0]
    exact hmod a (by rw [Finset.mem_Ico]; omega)
  · intro hpos
    rw [Presentation.init, S.evalRand_eq h, ← hinit, heval_eq, PMF.toOuterMeasure_map_apply]
    refine (hProb hpos).trans (PMF.toOuterMeasure_mono _ ?_)
    rintro cfg' ⟨⟨y, rfl⟩, -⟩
    exact ⟨y.regs, y.mem, rfl⟩

/-- **High-probability `O(n ^ 2 log ^ 3 n)` Karger–Stein global minimum cut** transported to any
presentation `S` satisfying `Laws S`. -/
theorem kargerSteinHighProb (S : Presentation) (h : Laws S) :
    ∃ p : List (S.Instr 24),
      ∀ (n w : ℕ) (W : Fin n → Fin n → ℕ),
        2 ≤ n →
        IsMultigraph W →
        4 * (Nat.log 2 n + 1) ≤ w →
        (∑ u : Fin n, ∑ v : Fin n, W u v) < 2 ^ w →
        let input := n :: (List.finRange n).flatMap fun u => (List.finRange n).map fun v => W u v
        let T := 2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2
        let R := (Nat.log 2 n + 15) * (Nat.log 2 n + 2)
        S.HaltsWithin (r := 24) w p (S.init input) T ∧
        S.RandCallsBounded (r := 24) w p (S.init input) T (R * (6 * (n * n))) ∧
        (∀ cfg ∈ (S.evalRand (r := 24) w p T (S.init input)).support,
          ∃ (reg : Fin 24 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = S.halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 2 + n * n ∨ 2 + 27 * (n * n) ≤ a →
              mem a = Presentation.initMem input a)) ∧
        (0 < minCut W →
          (S.evalRand (r := 24) w p T (S.init input)).toOuterMeasure
              {cfg | ∀ reg mem, cfg ≠ S.halted (minCut W) reg mem} ≤
            (1 : ENNReal) / ((2 * n : ℕ) : ENNReal)) := by
  refine ⟨S.programOf fastCutHighProbExactProgram, fun n w W hn hW hw htot => ?_⟩
  dsimp only
  rw [flatMap_finRange_eq_flattenMatrix]
  have hw' : logWidth 4 n ≤ w := hw
  have htot' : Fits w (totalDoubledWeight W) := htot
  obtain ⟨hHalts, hCalls, hPost, hFail⟩ := fastCutHighProbProgram_spec hn hW hw' htot'
  have hrun_eq := fastCutHighProbExactProgram_runRand_eq hn hW hw' htot'
  have heval_eq : Cslib.WordRAM.evalRand w fastCutHighProbExactProgram (fastCutHighProbTime n)
      (.init (n :: flattenMatrix W)) =
    Cslib.WordRAM.evalRand w fastCutHighProbProgram (fastCutHighProbTime n)
      (.init (n :: flattenMatrix W)) := by
    unfold Cslib.WordRAM.evalRand
    rw [hrun_eq]
  unfold fastCutHighProbTime at hHalts hCalls hPost hFail hrun_eq heval_eq
  unfold fastCutTrials at hCalls
  have hinit := Presentation.init_state_eq (r := 24) (n :: flattenMatrix W)
  have hmem0 := init_mem_eq (r := 24) (n :: flattenMatrix W)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Presentation.init, S.haltsWithin_iff h, ← hinit]
    unfold Cslib.WordRAM.RandHaltsWithin
    rwa [hrun_eq]
  · rw [Presentation.init, S.randCallsBounded_iff h, ← hinit]
    unfold Cslib.WordRAM.RandCallsBounded
    rwa [hrun_eq]
  · intro cfg hcfg
    rw [Presentation.init, S.evalRand_eq h, ← hinit, PMF.mem_support_map_iff] at hcfg
    obtain ⟨cfg', hcfg', rfl⟩ := hcfg
    rw [Cslib.WordRAM.support_evalRand, hrun_eq] at hcfg'
    obtain ⟨y, C, rfl, hbnd, hC, hle, hmod⟩ := hPost cfg' hcfg'
    refine ⟨y.regs, y.mem, C, rfl, hbnd.1, hbnd.2, hC, hle, fun a ha => ?_⟩
    rw [← hmem0]
    exact hmod a (by rw [Finset.mem_Ico]; omega)
  · intro hpos
    rw [Presentation.init, S.evalRand_eq h, ← hinit, heval_eq, PMF.toOuterMeasure_map_apply]
    refine (PMF.toOuterMeasure_mono _ ?_).trans (hFail hpos)
    rintro cfg' ⟨hnot, -⟩ y rfl
    exact hnot y.regs y.mem rfl

end ComplexityAbstracts.KargerMinCutBridge
