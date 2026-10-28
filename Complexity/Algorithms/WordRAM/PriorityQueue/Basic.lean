/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.IndexedMinPQ
public import Complexity.Computability.WordRAM.ExactNotation
public import Complexity.Computability.WordRAM.Subroutine

/-!
# Word-RAM interface for indexed min-priority queues

This file packages uniform Word-RAM calling conventions (`PQCode`) and parametric specification /
resource certificates (`PQPackage`) for `Cslib.Algorithms.Lean.IndexedMinPQ.spec`.

A `PQPackage B r_pq` bundles a `SubroutineCode B r_pq 1` with:
* three 1-bit operation-tag registers (`tag2`, `tag1`, `tag0`) taking values only in `{0, 1}`, so
  encoded operation arguments fit in `w`-bit words even at small word sizes (`w ≥ 1`);
* standard argument registers (`argV`, `argK`) and result registers (`outFlag`, `outV`, `outK`);
* parametric `SubroutineDS` certificates over `(n, K_max, w, base)` supporting arbitrary concrete
  potentials `potential : Data r_pq → ℕ` (both worst-case `potential = 0` heaps such as
  `BinaryHeap` and amortized heaps such as `FibonacciHeap`).

It also provides basis-polymorphic inline caller helpers (`callIsEmpty`, `callGetKey`, `callInsert`,
`callDecreaseKey`, `callExtractMin`) built from `Op.copy` and `SubroutineDS.call_rename`.

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.PQCode`: `SubroutineCode B r_pq 1` equipped with standard
  priority-queue interface registers, `encode`, `argMatch`, `decode`, and inline caller blocks.
* `Cslib.Algorithms.WordRAM.PriorityQueue.PQPackage`: uniform code together with parametric
  `SubroutineDS` certificates and per-operation amortized charge bounds.

## Main results

* `PQCode.arguments_fit`, `PQCode.encode_matches`: generic proof that the standard priority-queue
  encoding fits in `w`-bit words and satisfies `argMatch`.
* `PQCode.callIsEmpty_exec`, `PQCode.callGetKey_exec`, `PQCode.callInsert_exec`,
  `PQCode.callDecreaseKey_exec`, `PQCode.callExtractMin_exec`: relocated inline operation calls with
  amortized potential accounting and bidirectional framing.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue

open Cslib.WordRAM
open Cslib.Algorithms.Lean

/-! ## `PQCode`: Uniform priority-queue subroutine code and calling convention -/

/-- Uniform machine code and register calling convention for an indexed min-priority queue over
basis `B` using `r_pq` local registers. -/
structure PQCode (B : Basis) (r_pq : ℕ) extends SubroutineCode B r_pq 1 where
  /-- Register holding the handle-universe size `n` at initialization (`initParams = ![nReg]`). -/
  nReg : Fin r_pq
  /-- High tag bit (`≠ 0` selects `extractMin`). -/
  tag2 : Fin r_pq
  /-- Middle tag bit (`≠ 0` selects `insert` / `decreaseKey` when `tag2 = 0`). -/
  tag1 : Fin r_pq
  /-- Low tag bit (`0` selects `isEmpty` / `insert`; `≠ 0` selects `getKey` / `decreaseKey`). -/
  tag0 : Fin r_pq
  /-- Handle argument register (`v.val` for `getKey`, `insert`, `decreaseKey`). -/
  argV : Fin r_pq
  /-- Key argument register (`k` for `insert`, `decreaseKey`). -/
  argK : Fin r_pq
  /-- Flag output register (`1`/`0` for `isEmpty`, `getKey`, `extractMin`). -/
  outFlag : Fin r_pq
  /-- Extracted handle output register (`u.val` for non-empty `extractMin`). -/
  outV : Fin r_pq
  /-- Key output register (`k` for present `getKey` and non-empty `extractMin`). -/
  outK : Fin r_pq
  /-- Initialization takes `n` in `nReg`. -/
  initParams_eq : initParams = ![nReg]
  /-- `nReg` is distinct from `frontierReg` so callers can pass `n` and `frontier` together. -/
  nReg_ne_frontier : nReg ≠ frontierReg
  /-- Tag and argument registers are pairwise distinct. -/
  args_nodup : [tag2, tag1, tag0, argV, argK].Nodup
  /-- `tag2` is a caller-overwritable input register. -/
  tag2_input : input tag2 = true
  /-- `tag1` is a caller-overwritable input register. -/
  tag1_input : input tag1 = true
  /-- `tag0` is a caller-overwritable input register. -/
  tag0_input : input tag0 = true
  /-- `argV` is a caller-overwritable input register. -/
  argV_input : input argV = true
  /-- `argK` is a caller-overwritable input register. -/
  argK_input : input argK = true
  /-- Primary halting output register is `outFlag`. -/
  output_eq : output = outFlag

namespace PQCode

variable {B B' : Basis} {r_pq r_caller : ℕ}

/-- Translate a `PQCode` bundle along a basis simulation. -/
def mapSimulates (φ : B.Simulates B') (P : PQCode B r_pq) : PQCode B' r_pq where
  toSubroutineCode := P.toSubroutineCode.mapSimulates φ
  nReg := P.nReg
  tag2 := P.tag2
  tag1 := P.tag1
  tag0 := P.tag0
  argV := P.argV
  argK := P.argK
  outFlag := P.outFlag
  outV := P.outV
  outK := P.outK
  initParams_eq := P.initParams_eq
  nReg_ne_frontier := P.nReg_ne_frontier
  args_nodup := P.args_nodup
  tag2_input := P.tag2_input
  tag1_input := P.tag1_input
  tag0_input := P.tag0_input
  argV_input := P.argV_input
  argK_input := P.argK_input
  output_eq := P.output_eq

/-- Lift an exact-basis `PQCode` to `Basis.standard`. -/
abbrev toStandard (P : PQCode .exact r_pq) : PQCode .standard r_pq :=
  P.mapSimulates .exactStandard

/-- Standard register encoding for `IndexedMinPQ.Op n` using 1-bit tags `(tag2, tag1, tag0)`. -/
def encode (P : PQCode B r_pq) {n : ℕ} : IndexedMinPQ.Op n → Fin r_pq → ℕ
  | .isEmpty => fun _ => 0
  | .getKey v => fun i => if i = P.tag0 then 1 else if i = P.argV then v.val else 0
  | .insert v k => fun i =>
      if i = P.tag1 then 1 else if i = P.argV then v.val else if i = P.argK then k else 0
  | .decreaseKey v k => fun i =>
      if i = P.tag1 then 1 else if i = P.tag0 then 1
      else if i = P.argV then v.val else if i = P.argK then k else 0
  | .extractMin => fun i => if i = P.tag2 then 1 else 0

/-- Partial argument-matching predicate for inline priority-queue calls. -/
def argMatch (P : PQCode B r_pq) {n : ℕ} : IndexedMinPQ.Op n → (Fin r_pq → ℕ) → Prop
  | .isEmpty => fun regs => regs P.tag2 = 0 ∧ regs P.tag1 = 0 ∧ regs P.tag0 = 0
  | .getKey v => fun regs =>
      regs P.tag2 = 0 ∧ regs P.tag1 = 0 ∧ regs P.tag0 ≠ 0 ∧ regs P.argV = v.val
  | .insert v k => fun regs =>
      regs P.tag2 = 0 ∧ regs P.tag1 ≠ 0 ∧ regs P.tag0 = 0 ∧ regs P.argV = v.val ∧ regs P.argK = k
  | .decreaseKey v k => fun regs =>
      regs P.tag2 = 0 ∧ regs P.tag1 ≠ 0 ∧ regs P.tag0 ≠ 0 ∧ regs P.argV = v.val ∧ regs P.argK = k
  | .extractMin => fun regs => regs P.tag2 ≠ 0

/-- Standard output decoder for `IndexedMinPQ.spec n K_max`. -/
def decode (P : PQCode B r_pq) {n K_max : ℕ} :
    (o : (IndexedMinPQ.spec n K_max).Op) → (Fin r_pq → ℕ) →
      Option ((IndexedMinPQ.spec n K_max).Result o)
  | .isEmpty, regs => some (decide (regs P.outFlag ≠ 0))
  | .getKey _, regs =>
      if regs P.outFlag = 0 then some none else some (some (regs P.outK))
  | .insert _ _, _ => some ()
  | .decreaseKey _ _, _ => some ()
  | .extractMin, regs =>
      if regs P.outFlag = 0 then some none
      else if h : regs P.outV < n then some (some (⟨regs P.outV, h⟩, regs P.outK))
      else none

private theorem nodup_dests (P : PQCode B r_pq) :
    P.tag2 ≠ P.tag1 ∧ P.tag2 ≠ P.tag0 ∧ P.tag2 ≠ P.argV ∧ P.tag2 ≠ P.argK ∧
    P.tag1 ≠ P.tag0 ∧ P.tag1 ≠ P.argV ∧ P.tag1 ≠ P.argK ∧
    P.tag0 ≠ P.argV ∧ P.tag0 ≠ P.argK ∧ P.argV ≠ P.argK := by
  obtain ⟨h2, h1, h0, hv, _⟩ :=
    (List.nodup_cons.mp P.args_nodup).imp_right fun h =>
      (List.nodup_cons.mp h).imp_right fun h =>
        (List.nodup_cons.mp h).imp_right List.nodup_cons.mp
  exact ⟨fun e => h2 (by simp [e]), fun e => h2 (by simp [e]),
    fun e => h2 (by simp [e]), fun e => h2 (by simp [e]),
    fun e => h1 (by simp [e]), fun e => h1 (by simp [e]), fun e => h1 (by simp [e]),
    fun e => h0 (by simp [e]), fun e => h0 (by simp [e]),
    fun e => hv (by simp [e])⟩

/-- Standard encoded arguments fit in `w`-bit words whenever `n + 1 ≤ space`,
`Fits w (base + space)`, and `Fits w K_max`. -/
theorem arguments_fit (P : PQCode B r_pq) {n K_max w base space : ℕ}
    (hsp : n + 1 ≤ space) (hS : Fits w (base + space)) (hK : Fits w K_max)
    {s : IndexedMinPQ.State n} (o : IndexedMinPQ.Op n)
    (hv : (IndexedMinPQ.spec n K_max).valid s o) (i : Fin r_pq) :
    Fits w (P.encode o i) := by
  have h0 : Fits w 0 := hS.of_le (Nat.zero_le _)
  have h1 : Fits w 1 := hS.of_le (by omega)
  cases o with
  | isEmpty => exact h0
  | getKey v =>
    simp only [encode]
    split_ifs
    · exact h1
    · exact hS.of_le (by have := v.isLt; omega)
    · exact h0
  | insert v k =>
    have hk : k ≤ K_max := hv.2
    simp only [encode]
    split_ifs
    · exact h1
    · exact hS.of_le (by have := v.isLt; omega)
    · exact hK.of_le hk
    · exact h0
  | decreaseKey v k =>
    have hk : k ≤ K_max := hv.2
    simp only [encode]
    split_ifs
    · exact h1
    · exact h1
    · exact hS.of_le (by have := v.isLt; omega)
    · exact hK.of_le hk
    · exact h0
  | extractMin =>
    simp only [encode]
    split_ifs
    · exact h1
    · exact h0

/-- Full standalone `prepare` register delivery satisfies `P.argMatch`. -/
theorem encode_matches (P : PQCode B r_pq) {n : ℕ} (o : IndexedMinPQ.Op n)
    (regs : Fin r_pq → ℕ) :
    P.argMatch o (fun i => if P.input i then P.encode o i else regs i) := by
  obtain ⟨h21, h20, h2v, h2k, h10, h1v, h1k, h0v, h0k, hvk⟩ := P.nodup_dests
  cases o with
  | isEmpty =>
    simp [argMatch, encode, P.tag2_input, P.tag1_input, P.tag0_input]
  | getKey v =>
    simp [argMatch, encode, P.tag2_input, P.tag1_input, P.tag0_input, P.argV_input,
      h20, h2v, h10, h1v, h0v.symm]
  | insert v k =>
    simp [argMatch, encode, P.tag2_input, P.tag1_input, P.tag0_input, P.argV_input, P.argK_input,
      h21, h2v, h2k, h10.symm, h0v, h0k, h1v.symm, h1k.symm, hvk.symm]
  | decreaseKey v k =>
    simp [argMatch, encode, P.tag2_input, P.tag1_input, P.tag0_input, P.argV_input, P.argK_input,
      h21, h20, h2v, h2k, h1v.symm, h0v.symm, h1k.symm, h0k.symm, hvk.symm]
  | extractMin =>
    simp [argMatch, encode, P.tag2_input]

/-! ### Basis-polymorphic inline caller blocks and execution lemmas -/

/-- Relocated inline call to `isEmpty`, copying `0` from `zeroReg_c`. -/
def callIsEmpty (P : PQCode B r_pq) (f : Fin r_pq → Fin r_caller) (zeroReg_c : Fin r_caller) :
    Code B r_caller :=
  .seq (.seq (.op (.copy (f P.tag2) zeroReg_c))
         (.seq (.op (.copy (f P.tag1) zeroReg_c)) (.op (.copy (f P.tag0) zeroReg_c))))
       (P.code.rename f)

/-- Relocated inline call to `extractMin`, copying `1` from `oneReg_c`. -/
def callExtractMin (P : PQCode B r_pq) (f : Fin r_pq → Fin r_caller) (oneReg_c : Fin r_caller) :
    Code B r_caller :=
  .seq (.op (.copy (f P.tag2) oneReg_c)) (P.code.rename f)

/-- Relocated inline call to `getKey`, copying `0`, `1`, and handle `vReg_c`. -/
def callGetKey (P : PQCode B r_pq) (f : Fin r_pq → Fin r_caller)
    (zeroReg_c oneReg_c vReg_c : Fin r_caller) : Code B r_caller :=
  .seq (.seq (.op (.copy (f P.tag2) zeroReg_c)) <|
        .seq (.op (.copy (f P.tag1) zeroReg_c)) <|
        .seq (.op (.copy (f P.tag0) oneReg_c)) <|
             (.op (.copy (f P.argV) vReg_c)))
       (P.code.rename f)

/-- Relocated inline call to `insert`, copying `0`, `1`, handle `vReg_c`, and key `kReg_c`. -/
def callInsert (P : PQCode B r_pq) (f : Fin r_pq → Fin r_caller)
    (zeroReg_c oneReg_c vReg_c kReg_c : Fin r_caller) : Code B r_caller :=
  .seq (.seq (.op (.copy (f P.tag2) zeroReg_c)) <|
        .seq (.op (.copy (f P.tag1) oneReg_c)) <|
        .seq (.op (.copy (f P.tag0) zeroReg_c)) <|
        .seq (.op (.copy (f P.argV) vReg_c)) <|
             (.op (.copy (f P.argK) kReg_c)))
       (P.code.rename f)

/-- Relocated inline call to `decreaseKey`, copying `0`, `1`, handle `vReg_c`, and key `kReg_c`. -/
def callDecreaseKey (P : PQCode B r_pq) (f : Fin r_pq → Fin r_caller)
    (zeroReg_c oneReg_c vReg_c kReg_c : Fin r_caller) : Code B r_caller :=
  .seq (.seq (.op (.copy (f P.tag2) zeroReg_c)) <|
        .seq (.op (.copy (f P.tag1) oneReg_c)) <|
        .seq (.op (.copy (f P.tag0) oneReg_c)) <|
        .seq (.op (.copy (f P.argV) vReg_c)) <|
             (.op (.copy (f P.argK) kReg_c)))
       (P.code.rename f)

private theorem comap_set_of_injective {r₁ r₂ : ℕ} {f : Fin r₁ → Fin r₂} (hf : f.Injective)
    (x : Data r₂) (d : Fin r₁) (v : ℕ) :
    (x.set (f d) v).comap f = (x.comap f).set d v := by
  ext i
  · simp only [Data.comap, Data.set_regs, Function.comp_apply, Function.update_apply, hf.eq_iff]
  · rfl

private theorem copy_from_val {B : Basis} {r w : ℕ} {x : Data r} {dst src : Fin r} {v : ℕ}
    (h : x.regs src = v) :
    ExecWithin (B := B) w (.op (.copy dst src)) x (x.set dst v) 1 := by
  rw [← h]
  exact ExecWithin.copy

private theorem set_regs_out {r₁ r₂ : ℕ} {f : Fin r₁ → Fin r₂} (x : Data r₂) (d : Fin r₁)
    (v : ℕ) {j : Fin r₂} (hj : j ∉ Set.range f) : (x.set (f d) v).regs j = x.regs j :=
  Function.update_of_ne (fun h => hj ⟨d, h.symm⟩) _ _

/-- Inline execution of `P.callIsEmpty`: preserves abstract state `s`, sets `z.regs (f P.outFlag)`
so `z.regs (f P.outFlag) = 0 ↔ IndexedMinPQ.dom s ≠ ∅`, and charges `3 + C.charge s .isEmpty`. -/
theorem callIsEmpty_exec {P : PQCode B r_pq} {n K_max w base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    (harg_eq : C.argMatch = P.argMatch) (hdec_eq : C.decode = P.decode)
    {f : Fin r_pq → Fin r_caller} (hf : f.Injective)
    {zeroReg_c : Fin r_caller} (hz_out : zeroReg_c ∉ Set.range f)
    {s : IndexedMinPQ.State n} {x : Data r_caller}
    (hr : C.rep s (x.comap f)) (hz0 : x.regs zeroReg_c = 0) :
    ∃ z t, ExecWithin w (P.callIsEmpty f zeroReg_c) x z t ∧
      (z.regs (f P.outFlag) = 0 ↔ IndexedMinPQ.dom s ≠ ∅) ∧
      C.rep s (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤ 3 + C.charge s .isEmpty + C.potential (x.comap f) := by
  obtain ⟨h21, h20, _, _, h10, _, _, _, _, _⟩ := P.nodup_dests
  let x₁ := x.set (f P.tag2) 0
  let x₂ := x₁.set (f P.tag1) 0
  let x₃ := x₂.set (f P.tag0) 0
  have hz1 : x₁.regs zeroReg_c = 0 := (set_regs_out x P.tag2 0 hz_out).trans hz0
  have hz2 : x₂.regs zeroReg_c = 0 := (set_regs_out x₁ P.tag1 0 hz_out).trans hz1
  have hprep : ExecWithin (B := B) w
      (.seq (.op (.copy (f P.tag2) zeroReg_c))
        (.seq (.op (.copy (f P.tag1) zeroReg_c)) (.op (.copy (f P.tag0) zeroReg_c)))) x x₃ 3 :=
    (copy_from_val hz0).seq ((copy_from_val hz1).seq (copy_from_val hz2))
  have hx_bnd := C.bounded hr
  have hfit0 : Fits w 0 := (hx_bnd.1 P.baseReg).of_le (Nat.zero_le _)
  have hcomap : x₃.comap f = (((x.comap f).set P.tag2 0).set P.tag1 0).set P.tag0 0 := by
    simp only [x₃, x₂, x₁, comap_set_of_injective hf]
  have hb3 : (x₃.comap f).Bounded w := by
    rw [hcomap]
    exact Data.Bounded.set (Data.Bounded.set (Data.Bounded.set hx_bnd hfit0) hfit0) hfit0
  have hreg : ∀ i, P.input i = false → x₃.regs (f i) = x.regs (f i) := by
    intro i hi
    change (x₃.comap f).regs i = (x.comap f).regs i
    rw [hcomap]
    have ni0 : i ≠ P.tag0 := fun h => by rw [h, P.tag0_input] at hi; cases hi
    have ni1 : i ≠ P.tag1 := fun h => by rw [h, P.tag1_input] at hi; cases hi
    have ni2 : i ≠ P.tag2 := fun h => by rw [h, P.tag2_input] at hi; cases hi
    simp only [Data.set_regs, Function.update_of_ne ni0, Function.update_of_ne ni1,
      Function.update_of_ne ni2]
  have harg : C.argMatch .isEmpty (x₃.comap f).regs := by
    rw [harg_eq, hcomap]
    simp only [argMatch, Data.set_regs, Function.update_self,
      Function.update_of_ne h20, Function.update_of_ne h21, Function.update_of_ne h10]
    trivial
  obtain ⟨z, t, he, hdec, hrep_z, hmod, hregs_z, hpot⟩ :=
    C.call_rename hf .isEmpty hr trivial hprep hb3 hreg (fun _ _ => rfl) harg
  have hx3_out : ∀ j ∉ Set.range f, x₃.regs j = x.regs j := fun j hj =>
    (set_regs_out x₂ P.tag0 0 hj).trans
      ((set_regs_out x₁ P.tag1 0 hj).trans (set_regs_out x P.tag2 0 hj))
  rw [hdec_eq] at hdec
  simp only [decode, IndexedMinPQ.spec, Option.some.injEq, decide_eq_decide] at hdec
  have hflag : z.regs (f P.outFlag) = 0 ↔ IndexedMinPQ.dom s ≠ ∅ := by
    change (z.comap f).regs P.outFlag = 0 ↔ IndexedMinPQ.dom s ≠ ∅
    exact ⟨fun h0 hd => absurd h0 (hdec.mpr hd),
      fun hd => Decidable.byContradiction fun hne => hd (hdec.mp hne)⟩
  exact ⟨z, t, he, hflag, hrep_z, hmod, fun j hj => (hregs_z j hj).trans (hx3_out j hj), hpot⟩

/-- Inline execution of `P.callExtractMin`: extracts `findMin s` and charges
`1 + C.charge s .extractMin`. -/
theorem callExtractMin_exec {P : PQCode B r_pq} {n K_max w base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    (hsp_pos : 1 ≤ C.space) (hS : Fits w (base + C.space))
    (harg_eq : C.argMatch = P.argMatch) (hdec_eq : C.decode = P.decode)
    {f : Fin r_pq → Fin r_caller} (hf : f.Injective)
    {oneReg_c : Fin r_caller}
    {s : IndexedMinPQ.State n} {x : Data r_caller}
    (hr : C.rep s (x.comap f)) (ho1 : x.regs oneReg_c = 1) :
    ∃ z t, ExecWithin w (P.callExtractMin f oneReg_c) x z t ∧
      P.decode (K_max := K_max) .extractMin (z.comap f).regs =
        some ((IndexedMinPQ.spec n K_max).step s .extractMin).2 ∧
      C.rep ((IndexedMinPQ.spec n K_max).step s .extractMin).1 (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤ 1 + C.charge s .extractMin + C.potential (x.comap f) := by
  let x₁ := x.set (f P.tag2) 1
  have hprep : ExecWithin (B := B) w (.op (.copy (f P.tag2) oneReg_c)) x x₁ 1 :=
    copy_from_val ho1
  have hx_bnd := C.bounded hr
  have hfit1 : Fits w 1 := hS.of_le (by omega)
  have hcomap : x₁.comap f = (x.comap f).set P.tag2 1 := comap_set_of_injective hf x P.tag2 1
  have hb1 : (x₁.comap f).Bounded w := by
    rw [hcomap]
    exact Data.Bounded.set hx_bnd hfit1
  have hreg : ∀ i, P.input i = false → x₁.regs (f i) = x.regs (f i) := by
    intro i hi
    change (x₁.comap f).regs i = (x.comap f).regs i
    rw [hcomap]
    have ni2 : i ≠ P.tag2 := fun h => by rw [h, P.tag2_input] at hi; cases hi
    simp only [Data.set_regs, Function.update_of_ne ni2]
  have harg : C.argMatch .extractMin (x₁.comap f).regs := by
    rw [harg_eq, hcomap]
    simp only [argMatch, Data.set_regs, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true]
  obtain ⟨z, t, he, hdec, hrep_z, hmod, hregs_z, hpot⟩ :=
    C.call_rename hf .extractMin hr trivial hprep hb1 hreg (fun _ _ => rfl) harg
  rw [hdec_eq] at hdec
  have hx1_out : ∀ j ∉ Set.range f, x₁.regs j = x.regs j :=
    fun j hj => set_regs_out x P.tag2 1 hj
  exact ⟨z, t, he, hdec, hrep_z, hmod, fun j hj => (hregs_z j hj).trans (hx1_out j hj), hpot⟩

/-- Inline execution of `P.callInsert`: inserts `(v, k)` and charges
`5 + C.charge s (.insert v k)`. -/
theorem callInsert_exec {P : PQCode B r_pq} {n K_max w base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    (hsp : n + 1 ≤ C.space) (hS : Fits w (base + C.space)) (hK : Fits w K_max)
    (harg_eq : C.argMatch = P.argMatch)
    {f : Fin r_pq → Fin r_caller} (hf : f.Injective)
    {zeroReg_c oneReg_c vReg_c kReg_c : Fin r_caller}
    (hz_out : zeroReg_c ∉ Set.range f) (ho_out : oneReg_c ∉ Set.range f)
    (hv_out : vReg_c ∉ Set.range f) (hk_out : kReg_c ∉ Set.range f)
    {s : IndexedMinPQ.State n} {x : Data r_caller} {v : Fin n} {k : ℕ}
    (hr : C.rep s (x.comap f)) (hval : s v = none ∧ k ≤ K_max)
    (hz0 : x.regs zeroReg_c = 0) (ho1 : x.regs oneReg_c = 1)
    (hvv : x.regs vReg_c = v.val) (hvk : x.regs kReg_c = k) :
    ∃ z t, ExecWithin w (P.callInsert f zeroReg_c oneReg_c vReg_c kReg_c) x z t ∧
      C.rep (Function.update s v (some k)) (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤ 5 + C.charge s (.insert v k) + C.potential (x.comap f) := by
  obtain ⟨h21, h20, h2v, h2k, h10, h1v, h1k, h0v, h0k, hvk_ne⟩ := P.nodup_dests
  let x₁ := x.set (f P.tag2) 0
  let x₂ := x₁.set (f P.tag1) 1
  let x₃ := x₂.set (f P.tag0) 0
  let x₄ := x₃.set (f P.argV) v.val
  let x₅ := x₄.set (f P.argK) k
  have hout1 : ∀ j ∉ Set.range f, x₁.regs j = x.regs j := fun _ hj => set_regs_out x _ _ hj
  have hout2 : ∀ j ∉ Set.range f, x₂.regs j = x.regs j := fun j hj =>
    (set_regs_out x₁ _ _ hj).trans (hout1 j hj)
  have hout3 : ∀ j ∉ Set.range f, x₃.regs j = x.regs j := fun j hj =>
    (set_regs_out x₂ _ _ hj).trans (hout2 j hj)
  have hout4 : ∀ j ∉ Set.range f, x₄.regs j = x.regs j := fun j hj =>
    (set_regs_out x₃ _ _ hj).trans (hout3 j hj)
  have hout5 : ∀ j ∉ Set.range f, x₅.regs j = x.regs j := fun j hj =>
    (set_regs_out x₄ _ _ hj).trans (hout4 j hj)
  have hprep : ExecWithin (B := B) w
      (.seq (.op (.copy (f P.tag2) zeroReg_c)) <|
       .seq (.op (.copy (f P.tag1) oneReg_c)) <|
       .seq (.op (.copy (f P.tag0) zeroReg_c)) <|
       .seq (.op (.copy (f P.argV) vReg_c)) <|
            (.op (.copy (f P.argK) kReg_c))) x x₅ 5 :=
    (copy_from_val hz0).seq <|
    (copy_from_val ((hout1 _ ho_out).trans ho1)).seq <|
    (copy_from_val ((hout2 _ hz_out).trans hz0)).seq <|
    (copy_from_val ((hout3 _ hv_out).trans hvv)).seq <|
    copy_from_val ((hout4 _ hk_out).trans hvk)
  have hx_bnd := C.bounded hr
  have hcomap : x₅.comap f =
      (((((x.comap f).set P.tag2 0).set P.tag1 1).set P.tag0 0).set P.argV v.val).set P.argK k := by
    simp only [x₅, x₄, x₃, x₂, x₁, comap_set_of_injective hf]
  have hb5 : (x₅.comap f).Bounded w := by
    rw [hcomap]
    exact Data.Bounded.set (Data.Bounded.set (Data.Bounded.set (Data.Bounded.set
      (Data.Bounded.set hx_bnd (hS.of_le (Nat.zero_le _)))
      (hS.of_le (by omega)))
      (hS.of_le (Nat.zero_le _)))
      (hS.of_le (by have := v.isLt; omega)))
      (hK.of_le hval.2)
  have hreg : ∀ i, P.input i = false → x₅.regs (f i) = x.regs (f i) := by
    intro i hi
    change (x₅.comap f).regs i = (x.comap f).regs i
    rw [hcomap]
    have niK : i ≠ P.argK := fun h => by rw [h, P.argK_input] at hi; cases hi
    have niV : i ≠ P.argV := fun h => by rw [h, P.argV_input] at hi; cases hi
    have ni0 : i ≠ P.tag0 := fun h => by rw [h, P.tag0_input] at hi; cases hi
    have ni1 : i ≠ P.tag1 := fun h => by rw [h, P.tag1_input] at hi; cases hi
    have ni2 : i ≠ P.tag2 := fun h => by rw [h, P.tag2_input] at hi; cases hi
    simp only [Data.set_regs, Function.update_of_ne niK, Function.update_of_ne niV,
      Function.update_of_ne ni0, Function.update_of_ne ni1, Function.update_of_ne ni2]
  have harg : C.argMatch (.insert v k) (x₅.comap f).regs := by
    rw [harg_eq, hcomap]
    simp only [argMatch, Data.set_regs, Function.update_self,
      Function.update_of_ne h2k, Function.update_of_ne h2v, Function.update_of_ne h20,
      Function.update_of_ne h21, Function.update_of_ne h1k, Function.update_of_ne h1v,
      Function.update_of_ne h10, Function.update_of_ne h0k, Function.update_of_ne h0v,
      Function.update_of_ne hvk_ne, ne_eq, one_ne_zero, not_false_eq_true]
    trivial
  obtain ⟨z, t, he, _, hrep_z, hmod, hregs_z, hpot⟩ :=
    C.call_rename hf (.insert v k) hr hval hprep hb5 hreg (fun _ _ => rfl) harg
  exact ⟨z, t, he, hrep_z, hmod, fun j hj => (hregs_z j hj).trans (hout5 j hj), hpot⟩

/-- Inline execution of `P.callDecreaseKey`: lowers `v`'s key to `k` and charges
`5 + C.charge s (.decreaseKey v k)`. -/
theorem callDecreaseKey_exec {P : PQCode B r_pq} {n K_max w base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    (hsp : n + 1 ≤ C.space) (hS : Fits w (base + C.space)) (hK : Fits w K_max)
    (harg_eq : C.argMatch = P.argMatch)
    {f : Fin r_pq → Fin r_caller} (hf : f.Injective)
    {zeroReg_c oneReg_c vReg_c kReg_c : Fin r_caller}
    (ho_out : oneReg_c ∉ Set.range f)
    (hv_out : vReg_c ∉ Set.range f) (hk_out : kReg_c ∉ Set.range f)
    {s : IndexedMinPQ.State n} {x : Data r_caller} {v : Fin n} {k : ℕ}
    (hr : C.rep s (x.comap f)) (hval : (∃ k₀, s v = some k₀ ∧ k ≤ k₀) ∧ k ≤ K_max)
    (hz0 : x.regs zeroReg_c = 0) (ho1 : x.regs oneReg_c = 1)
    (hvv : x.regs vReg_c = v.val) (hvk : x.regs kReg_c = k) :
    ∃ z t, ExecWithin w (P.callDecreaseKey f zeroReg_c oneReg_c vReg_c kReg_c) x z t ∧
      C.rep (Function.update s v (some k)) (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤
        5 + C.charge s (.decreaseKey v k) + C.potential (x.comap f) := by
  obtain ⟨h21, h20, h2v, h2k, h10, h1v, h1k, h0v, h0k, hvk_ne⟩ := P.nodup_dests
  let x₁ := x.set (f P.tag2) 0
  let x₂ := x₁.set (f P.tag1) 1
  let x₃ := x₂.set (f P.tag0) 1
  let x₄ := x₃.set (f P.argV) v.val
  let x₅ := x₄.set (f P.argK) k
  have hout1 : ∀ j ∉ Set.range f, x₁.regs j = x.regs j := fun _ hj => set_regs_out x _ _ hj
  have hout2 : ∀ j ∉ Set.range f, x₂.regs j = x.regs j := fun j hj =>
    (set_regs_out x₁ _ _ hj).trans (hout1 j hj)
  have hout3 : ∀ j ∉ Set.range f, x₃.regs j = x.regs j := fun j hj =>
    (set_regs_out x₂ _ _ hj).trans (hout2 j hj)
  have hout4 : ∀ j ∉ Set.range f, x₄.regs j = x.regs j := fun j hj =>
    (set_regs_out x₃ _ _ hj).trans (hout3 j hj)
  have hout5 : ∀ j ∉ Set.range f, x₅.regs j = x.regs j := fun j hj =>
    (set_regs_out x₄ _ _ hj).trans (hout4 j hj)
  have hprep : ExecWithin (B := B) w
      (.seq (.op (.copy (f P.tag2) zeroReg_c)) <|
       .seq (.op (.copy (f P.tag1) oneReg_c)) <|
       .seq (.op (.copy (f P.tag0) oneReg_c)) <|
       .seq (.op (.copy (f P.argV) vReg_c)) <|
            (.op (.copy (f P.argK) kReg_c))) x x₅ 5 :=
    (copy_from_val hz0).seq <|
    (copy_from_val ((hout1 _ ho_out).trans ho1)).seq <|
    (copy_from_val ((hout2 _ ho_out).trans ho1)).seq <|
    (copy_from_val ((hout3 _ hv_out).trans hvv)).seq <|
    copy_from_val ((hout4 _ hk_out).trans hvk)
  have hx_bnd := C.bounded hr
  have hcomap : x₅.comap f =
      (((((x.comap f).set P.tag2 0).set P.tag1 1).set P.tag0 1).set P.argV v.val).set P.argK k := by
    simp only [x₅, x₄, x₃, x₂, x₁, comap_set_of_injective hf]
  have hb5 : (x₅.comap f).Bounded w := by
    rw [hcomap]
    exact Data.Bounded.set (Data.Bounded.set (Data.Bounded.set (Data.Bounded.set
      (Data.Bounded.set hx_bnd (hS.of_le (Nat.zero_le _)))
      (hS.of_le (by omega)))
      (hS.of_le (by omega)))
      (hS.of_le (by have := v.isLt; omega)))
      (hK.of_le hval.2)
  have hreg : ∀ i, P.input i = false → x₅.regs (f i) = x.regs (f i) := by
    intro i hi
    change (x₅.comap f).regs i = (x.comap f).regs i
    rw [hcomap]
    have niK : i ≠ P.argK := fun h => by rw [h, P.argK_input] at hi; cases hi
    have niV : i ≠ P.argV := fun h => by rw [h, P.argV_input] at hi; cases hi
    have ni0 : i ≠ P.tag0 := fun h => by rw [h, P.tag0_input] at hi; cases hi
    have ni1 : i ≠ P.tag1 := fun h => by rw [h, P.tag1_input] at hi; cases hi
    have ni2 : i ≠ P.tag2 := fun h => by rw [h, P.tag2_input] at hi; cases hi
    simp only [Data.set_regs, Function.update_of_ne niK, Function.update_of_ne niV,
      Function.update_of_ne ni0, Function.update_of_ne ni1, Function.update_of_ne ni2]
  have harg : C.argMatch (.decreaseKey v k) (x₅.comap f).regs := by
    rw [harg_eq, hcomap]
    simp only [argMatch, Data.set_regs, Function.update_self,
      Function.update_of_ne h2k, Function.update_of_ne h2v, Function.update_of_ne h20,
      Function.update_of_ne h21, Function.update_of_ne h1k, Function.update_of_ne h1v,
      Function.update_of_ne h10, Function.update_of_ne h0k, Function.update_of_ne h0v,
      Function.update_of_ne hvk_ne, ne_eq, one_ne_zero, not_false_eq_true]
    trivial
  obtain ⟨z, t, he, _, hrep_z, hmod, hregs_z, hpot⟩ :=
    C.call_rename hf (.decreaseKey v k) hr hval hprep hb5 hreg (fun _ _ => rfl) harg
  exact ⟨z, t, he, hrep_z, hmod, fun j hj => (hregs_z j hj).trans (hout5 j hj), hpot⟩

/-- Inline execution of `P.callGetKey`: queries `s v` and charges `4 + C.charge s (.getKey v)`. -/
theorem callGetKey_exec {P : PQCode B r_pq} {n K_max w base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    (hsp : n + 1 ≤ C.space) (hS : Fits w (base + C.space))
    (harg_eq : C.argMatch = P.argMatch) (hdec_eq : C.decode = P.decode)
    {f : Fin r_pq → Fin r_caller} (hf : f.Injective)
    {zeroReg_c oneReg_c vReg_c : Fin r_caller}
    (hz_out : zeroReg_c ∉ Set.range f) (ho_out : oneReg_c ∉ Set.range f)
    (hv_out : vReg_c ∉ Set.range f)
    {s : IndexedMinPQ.State n} {x : Data r_caller} (v : Fin n)
    (hr : C.rep s (x.comap f)) (hz0 : x.regs zeroReg_c = 0) (ho1 : x.regs oneReg_c = 1)
    (hvv : x.regs vReg_c = v.val) :
    ∃ z t, ExecWithin w (P.callGetKey f zeroReg_c oneReg_c vReg_c) x z t ∧
      P.decode (K_max := K_max) (.getKey v) (z.comap f).regs = some (s v) ∧
      C.rep s (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤ 4 + C.charge s (.getKey v) + C.potential (x.comap f) := by
  obtain ⟨h21, h20, h2v, _, h10, h1v, _, h0v, _, _⟩ := P.nodup_dests
  let x₁ := x.set (f P.tag2) 0
  let x₂ := x₁.set (f P.tag1) 0
  let x₃ := x₂.set (f P.tag0) 1
  let x₄ := x₃.set (f P.argV) v.val
  have hout1 : ∀ j ∉ Set.range f, x₁.regs j = x.regs j := fun _ hj => set_regs_out x _ _ hj
  have hout2 : ∀ j ∉ Set.range f, x₂.regs j = x.regs j := fun j hj =>
    (set_regs_out x₁ _ _ hj).trans (hout1 j hj)
  have hout3 : ∀ j ∉ Set.range f, x₃.regs j = x.regs j := fun j hj =>
    (set_regs_out x₂ _ _ hj).trans (hout2 j hj)
  have hout4 : ∀ j ∉ Set.range f, x₄.regs j = x.regs j := fun j hj =>
    (set_regs_out x₃ _ _ hj).trans (hout3 j hj)
  have hprep : ExecWithin (B := B) w
      (.seq (.op (.copy (f P.tag2) zeroReg_c)) <|
       .seq (.op (.copy (f P.tag1) zeroReg_c)) <|
       .seq (.op (.copy (f P.tag0) oneReg_c)) <|
            (.op (.copy (f P.argV) vReg_c))) x x₄ 4 :=
    (copy_from_val hz0).seq <|
    (copy_from_val ((hout1 _ hz_out).trans hz0)).seq <|
    (copy_from_val ((hout2 _ ho_out).trans ho1)).seq <|
    copy_from_val ((hout3 _ hv_out).trans hvv)
  have hx_bnd := C.bounded hr
  have hcomap : x₄.comap f =
      ((((x.comap f).set P.tag2 0).set P.tag1 0).set P.tag0 1).set P.argV v.val := by
    simp only [x₄, x₃, x₂, x₁, comap_set_of_injective hf]
  have hb4 : (x₄.comap f).Bounded w := by
    rw [hcomap]
    exact Data.Bounded.set (Data.Bounded.set (Data.Bounded.set
      (Data.Bounded.set hx_bnd (hS.of_le (Nat.zero_le _)))
      (hS.of_le (Nat.zero_le _)))
      (hS.of_le (by omega)))
      (hS.of_le (by have := v.isLt; omega))
  have hreg : ∀ i, P.input i = false → x₄.regs (f i) = x.regs (f i) := by
    intro i hi
    change (x₄.comap f).regs i = (x.comap f).regs i
    rw [hcomap]
    have niV : i ≠ P.argV := fun h => by rw [h, P.argV_input] at hi; cases hi
    have ni0 : i ≠ P.tag0 := fun h => by rw [h, P.tag0_input] at hi; cases hi
    have ni1 : i ≠ P.tag1 := fun h => by rw [h, P.tag1_input] at hi; cases hi
    have ni2 : i ≠ P.tag2 := fun h => by rw [h, P.tag2_input] at hi; cases hi
    simp only [Data.set_regs, Function.update_of_ne niV, Function.update_of_ne ni0,
      Function.update_of_ne ni1, Function.update_of_ne ni2]
  have harg : C.argMatch (.getKey v) (x₄.comap f).regs := by
    rw [harg_eq, hcomap]
    simp only [argMatch, Data.set_regs, Function.update_self,
      Function.update_of_ne h2v, Function.update_of_ne h20, Function.update_of_ne h21,
      Function.update_of_ne h1v, Function.update_of_ne h10, Function.update_of_ne h0v,
      ne_eq, one_ne_zero, not_false_eq_true]
    trivial
  obtain ⟨z, t, he, hdec, hrep_z, hmod, hregs_z, hpot⟩ :=
    C.call_rename hf (.getKey v) hr trivial hprep hb4 hreg (fun _ _ => rfl) harg
  rw [hdec_eq] at hdec
  exact ⟨z, t, he, hdec, hrep_z, hmod, fun j hj => (hregs_z j hj).trans (hout4 j hj), hpot⟩

end PQCode

/-! ## `PQPackage`: Parametric priority-queue implementation bundle -/

/-- A priority-queue implementation over basis `B` with uniform `PQCode B r_pq`, memory footprint
`space n`, per-operation amortized instruction charges `*Time n`, and parametric `SubroutineDS`
certificates supporting arbitrary concrete potentials `potential : Data r_pq → ℕ`. -/
structure PQPackage (B : Basis) (r_pq : ℕ) where
  /-- Uniform priority-queue code and register convention. -/
  code : PQCode B r_pq
  /-- Memory footprint size on `n` handles (`[base, base + space n)`). -/
  space : ℕ → ℕ
  /-- Every priority queue on `n` handles reserves at least `n + 1` words (`n + 1 ≤ space n`), so
  handle arguments `v < n` fit in `w` bits via `Fits w (base + space n)` in `PQCode.arguments_fit`.
  -/
  space_lower : ∀ n, n + 1 ≤ space n
  /-- Fresh-initialization instruction bound (`initFresh`). -/
  initTime : ℕ → ℕ
  /-- Amortized instruction bound for `isEmpty`. -/
  emptyTime : ℕ → ℕ
  /-- Amortized instruction bound for `getKey`. -/
  getTime : ℕ → ℕ
  /-- Amortized instruction bound for `insert`. -/
  insertTime : ℕ → ℕ
  /-- Amortized instruction bound for `decreaseKey`. -/
  decreaseTime : ℕ → ℕ
  /-- Amortized instruction bound for `extractMin`. -/
  extractTime : ℕ → ℕ
  /-- Parametric `SubroutineDS` certificate whenever `base + space n` and `K_max` fit in `w` bits.
  -/
  cert : ∀ {n K_max w base : ℕ}, Fits w (base + space n) → Fits w K_max →
    SubroutineDS code.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n)
  /-- Certificate footprint agrees with `space n`. -/
  cert_space : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max),
    (cert hS hK).space = space n
  /-- Fresh initialization runs within `initTime n` instructions. -/
  cert_initTime : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max),
    (cert hS hK).initTime ≤ initTime n
  /-- Empty priority queue starts with `initPotential = 0`. -/
  cert_initPotential : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max),
    (cert hS hK).initPotential = 0
  /-- Certificate `argMatch` agrees with `code.argMatch`. -/
  cert_argMatch : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max),
    (cert hS hK).argMatch = code.argMatch
  /-- Certificate `decode` agrees with `code.decode`. -/
  cert_decode : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max),
    (cert hS hK).decode = code.decode
  /-- Amortized charge bound for `isEmpty`. -/
  charge_isEmpty : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max)
    (s : IndexedMinPQ.State n), (cert hS hK).charge s .isEmpty ≤ emptyTime n
  /-- Amortized charge bound for `getKey`. -/
  charge_getKey : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max)
    (s : IndexedMinPQ.State n) (v : Fin n), (cert hS hK).charge s (.getKey v) ≤ getTime n
  /-- Amortized charge bound for `insert`. -/
  charge_insert : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max)
    (s : IndexedMinPQ.State n) (v : Fin n) (k : ℕ),
    (cert hS hK).charge s (.insert v k) ≤ insertTime n
  /-- Amortized charge bound for `decreaseKey`. -/
  charge_decreaseKey : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max)
    (s : IndexedMinPQ.State n) (v : Fin n) (k : ℕ),
    (cert hS hK).charge s (.decreaseKey v k) ≤ decreaseTime n
  /-- Amortized charge bound for `extractMin`. -/
  charge_extractMin : ∀ {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max)
    (s : IndexedMinPQ.State n), (cert hS hK).charge s .extractMin ≤ extractTime n

namespace PQPackage

/-- Translate a `PQPackage` along any basis simulation. -/
def mapSimulates {B B' : Basis} {r_pq : ℕ} (φ : B.Simulates B') (pkg : PQPackage B r_pq) :
    PQPackage B' r_pq where
  code := pkg.code.mapSimulates φ
  space := pkg.space
  space_lower := pkg.space_lower
  initTime := pkg.initTime
  emptyTime := pkg.emptyTime
  getTime := pkg.getTime
  insertTime := pkg.insertTime
  decreaseTime := pkg.decreaseTime
  extractTime := pkg.extractTime
  cert hS hK := (pkg.cert hS hK).mapSimulates φ
  cert_space := pkg.cert_space
  cert_initTime := pkg.cert_initTime
  cert_initPotential := pkg.cert_initPotential
  cert_argMatch := pkg.cert_argMatch
  cert_decode := pkg.cert_decode
  charge_isEmpty := pkg.charge_isEmpty
  charge_getKey := pkg.charge_getKey
  charge_insert := pkg.charge_insert
  charge_decreaseKey := pkg.charge_decreaseKey
  charge_extractMin := pkg.charge_extractMin

/-- Lift an exact-basis `PQPackage` to `Basis.standard`. -/
abbrev toStandard {r_pq : ℕ} (pkg : PQPackage .exact r_pq) : PQPackage .standard r_pq :=
  pkg.mapSimulates .exactStandard

end PQPackage

end Cslib.Algorithms.WordRAM.PriorityQueue
