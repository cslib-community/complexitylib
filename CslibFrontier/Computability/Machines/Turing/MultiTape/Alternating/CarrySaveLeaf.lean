/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveStream
public import CslibFrontier.Computability.PolyTime.CountingLeaf.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
import Mathlib.Tactic.FinCases

/-!
# Preparing a native leaf query from persistent controller storage

Context, count, and width words are supplied on private tapes 6–8. The carry tape 9 starts blank
and is written by the actual finite control. The persistent path is rewound from its right blank;
the index already starts at zero. The remaining private tapes are blank evaluator scratch.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveLeaf

open MultiTapeTM Cslib.CountingLeaf

/-- The carry field is created on this private tape rather than assumed as prefilled input. -/
@[expose] def carryTape (k : ℕ) : Fin (k + 12) := ⟨9, by omega⟩

/-- Supplied context and size words, followed by blank carry and evaluator scratch tapes. -/
@[expose] def scratch (k : ℕ) (context count width : List Bool) :
    CarrySaveStream.Scratch (k + 6) :=
  ⟨fun i => if i.val = 6 then tapeOfList context else if i.val = 7 then tapeOfList count
    else if i.val = 8 then tapeOfList width else fun _ => none, fun _ => 0⟩

/-- Initial physical controller storage before preparing a selected leaf. -/
@[expose] def initial (k : ℕ) (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) : Cfg (k + 12) Bool Unit input :=
  CarrySaveStream.config height bits path unary frontier status (scratch k context count width)

/-- After preparation, the path head is zero and the fresh carry tape holds its singleton word. -/
@[expose] def prepared {k : ℕ} {input : List Bool} (cfg : Cfg (k + 12) Bool Unit input)
    (carry : Bool) : Cfg (k + 12) Bool Unit input :=
  { cfg with
    workTapes := Function.update cfg.workTapes (carryTape k) (tapeOfList [carry])
    workTapePos := Function.update cfg.workTapePos (CarrySaveStream.coreEmb (k + 6) 2) 0 }

private def writeCarry (k : ℕ) (carry : Bool) : MultiTapeTM (k + 12) Bool Unit :=
  ofTr () fun _ _ _ =>
    ⟨0, fun i => (if i = carryTape k then some (some carry) else none, 0), none, none⟩

/-- Write the selected carry component and rewind the persistent path, preserving other storage. -/
noncomputable def machine (k : ℕ) (carry : Bool) :=
  (writeCarry k carry).seq ((rewindWork Bool).extendTapes
    (tapeEmb (CarrySaveStream.coreEmb (k + 6) 2)))

/-- The actual raw query whose six fields become readable after preparation. -/
@[expose] def query (context count width path bits : List Bool) (carry : Bool) : RawInput :=
  ⟨context, count, width, path, carry, bits⟩

/-- Charged preparation includes writing the carry symbol and all path-rewind steps. -/
theorem runsBetween (k : ℕ) (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status carry : Bool) :
    let cfg := initial k input context count width height bits path unary frontier status
    RunsBetween (machine k carry) cfg (prepared cfg carry) (path.length + 3)
      ((k + 12) * (path.length + 5)) := by
  dsimp only
  let cfg := initial k input context count width height bits path unary frontier status
  let mid : Cfg (k + 12) Bool Unit input :=
    { cfg with workTapes := Function.update cfg.workTapes (carryTape k) (tapeOfList [carry]) }
  have hblank : cfg.workTapes (carryTape k) = fun _ => none := by
    simp [cfg, initial, CarrySaveStream.config_extra_tape, carryTape, scratch]
  have hcarry : cfg.workTapePos (carryTape k) = 0 := by
    simp [cfg, initial, CarrySaveStream.config_extra_head, carryTape, scratch]
  have hb : Function.update (fun _ : ℤ => (none : Option Bool)) 0 (some carry) =
      tapeOfList [carry] := by
    simpa using (tapeOfList_append_single ([] : List Bool) carry).symm
  have hwrite : RunsBetween (writeCarry k carry) cfg mid 1 ((k + 12) * 2) := by
    apply RunsBetween.of_runFrom
    rw [runFrom_one, step_of_state rfl]
    apply Cfg.ext
    · simp [writeCarry, tr_ofTr, Action.apply, mid, Cfg.withState]
    · simp [writeCarry, tr_ofTr, Action.apply, mid, Cfg.withState]
    · funext i
      by_cases hi : i = carryTape k
      · subst i
        simp [writeCarry, tr_ofTr, Action.apply, mid, Cfg.withState, hcarry, hblank, hb]
      · simp [writeCarry, tr_ofTr, Action.apply, mid, Cfg.withState, hi]
    · simp [writeCarry, tr_ofTr, Action.apply, mid, Cfg.withState]
    · simp [writeCarry, tr_ofTr, Action.apply, mid, Cfg.withState]
  have hpath : mid.workTapes (CarrySaveStream.coreEmb (k + 6) 2) = tapeOfList path := by
    have hn : CarrySaveStream.coreEmb (k + 6) 2 ≠ carryTape k := by
      intro h
      have hv := congrArg Fin.val h
      change (2 : ℕ) = 9 at hv
      omega
    simp [mid, hn, cfg, initial]
  have hhead : mid.workTapePos (CarrySaveStream.coreEmb (k + 6) 2) = path.length := by
    simp [mid, cfg, initial]
  have hr : RunsBetween ((rewindWork Bool).extendTapes
      (tapeEmb (CarrySaveStream.coreEmb (k + 6) 2))) mid (prepared cfg carry)
      (path.length + 2) ((k + 12) * (path.length + 3)) := by
    apply RunsBetween.of_runFrom
    simp only [runFrom_tapeEmb, oneTapeCfg, Cfg.withState, extendTapes_q₀]
    rw [hhead, runFrom_rewindWork_none _ _ _ hpath le_rfl, embed_tapeEmb]
    apply Cfg.ext <;> try rfl
    · funext i
      by_cases hi : i = CarrySaveStream.coreEmb (k + 6) 2
      · subst i
        simp only [Function.update_self, prepared]
        rfl
      · simp [prepared, mid, hi]
  convert hwrite.seq hr using 1 <;> (first | rfl | omega | ring)

/-- The six evaluator sources reuse controller path/index tapes and four private field tapes. -/
@[expose] def sourceTapes (k : ℕ) : Fin 6 ↪ Fin (k + 12) where
  toFun i := ⟨(![6, 7, 8, 2, 9, 1] : Fin 6 → ℕ) i,
    by fin_cases i <;> simp⟩
  inj' := by
    intro i j h
    have hv := congrArg Fin.val h
    fin_cases i <;> fin_cases j <;> simp_all

/-- Extend the six selected sources by the native evaluator's private scratch block. -/
@[expose] def nativeTapes (k : ℕ) : Fin (6 + (k + 2)) ↪ Fin (k + 12) where
  toFun := Fin.addCases (sourceTapes k) (fun j => ⟨10 + j.val, by have := j.isLt; omega⟩)
  inj' := by
    intro a b h
    cases a using Fin.addCases with
    | left a =>
      cases b using Fin.addCases with
      | left b =>
        exact congrArg (Fin.castAdd (k + 2)) ((sourceTapes k).injective (by simpa using h))
      | right b =>
        have hv := congrArg Fin.val h
        fin_cases a <;> simp [sourceTapes, Function.Embedding.coeFn_mk] at hv <;> omega
    | right a =>
      cases b using Fin.addCases with
      | left b =>
        have hv := congrArg Fin.val h
        fin_cases b <;> simp [sourceTapes, Function.Embedding.coeFn_mk] at hv <;> omega
      | right b =>
        have hv := congrArg Fin.val h
        apply congrArg (Fin.natAdd 6)
        apply Fin.ext
        simp only [Fin.addCases_right, Fin.val_mk] at hv
        omega

@[simp] private theorem nativeTapes_source (k : ℕ) (i : Fin 6) :
    nativeTapes k (Fin.castAdd (k + 2) i) = sourceTapes k i := by simp [nativeTapes]

@[simp] private theorem nativeTapes_extra (k : ℕ) (j : Fin (k + 2)) :
    nativeTapes k (Fin.natAdd 6 j) = ⟨10 + j.val, by have := j.isLt; omega⟩ := by
  simp [nativeTapes]

private theorem prepared_source_tape (k : ℕ)
    (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status carry : Bool) (i : Fin 6) :
    (prepared (initial k input context count width height bits path unary frontier status)
      carry).workTapes (sourceTapes k i) =
      tapeOfList (Serialize.fields
        (query context count width path bits carry) i) := by
  have hp := CarrySaveStream.config_path_tape (scratch := scratch k context count width)
    (input := input) height bits path unary frontier status
  have hb := CarrySaveStream.config_bits_tape (scratch := scratch k context count width)
    (input := input) height bits path unary frontier status
  change (CarrySaveStream.config height bits path unary frontier status
    (scratch k context count width)).workTapes (⟨2, by omega⟩ : Fin (k + 12)) = _ at hp
  change (CarrySaveStream.config height bits path unary frontier status
    (scratch k context count width)).workTapes (1 : Fin (k + 12)) = _ at hb
  dsimp only [scratch] at hp hb
  fin_cases i <;>
    simp [prepared, initial, sourceTapes, Function.Embedding.coeFn_mk, carryTape,
      CarrySaveStream.config_extra_tape, Serialize.fields, query, hp, hb, scratch]

private theorem prepared_source_head (k : ℕ)
    (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status carry : Bool) (i : Fin 6) :
    (prepared (initial k input context count width height bits path unary frontier status)
      carry).workTapePos (sourceTapes k i) = 0 := by
  have hb := CarrySaveStream.config_bits_head (scratch := scratch k context count width)
    (input := input) height bits path unary frontier status
  have hc : CarrySaveStream.coreEmb (k + 6) 2 = (⟨2, by omega⟩ : Fin (k + 12)) := rfl
  change (CarrySaveStream.config height bits path unary frontier status
    (scratch k context count width)).workTapePos (1 : Fin (k + 12)) = _ at hb
  dsimp only [scratch] at hb
  fin_cases i <;>
    simp [prepared, initial, sourceTapes, Function.Embedding.coeFn_mk, carryTape,
      CarrySaveStream.config_extra_head, hc, hb, scratch]

/-- The prepared physical view consists exactly of the six raw fields and blank evaluator tapes. -/
theorem view_prepared (k : ℕ) (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status carry : Bool) :
    viewCfg (nativeTapes k)
      (prepared (initial k input context count width height bits path unary frontier status)
      carry) =
      Native.initial k input (query context count width path bits carry) := by
  unfold Native.initial
  apply Cfg.ext
  · simp [viewCfg, prepared, initial]
  · simp [viewCfg, prepared, initial]
  · funext j
    cases j using Fin.addCases with
    | left j =>
      simpa only [viewCfg, nativeTapes_source, Fin.append_left] using
        prepared_source_tape k input context count width height bits path unary frontier
          status carry j
    | right j =>
      have h2 : (⟨10 + j.val, by have := j.isLt; omega⟩ : Fin (k + 12)) ≠ carryTape k := by
        intro h; have hv := congrArg Fin.val h; change 10 + j.val = 9 at hv; omega
      have h6 : 6 ≤ 10 + j.val := by omega
      have hne6 : 10 + j.val ≠ 6 := by omega
      have hne7 : 10 + j.val ≠ 7 := by omega
      have hne8 : 10 + j.val ≠ 8 := by omega
      simp [viewCfg, nativeTapes_extra, prepared, h2, initial,
        CarrySaveStream.config_extra_tape, h6, scratch, hne6, hne7, hne8]
  · funext j
    cases j using Fin.addCases with
    | left j =>
      simpa only [viewCfg, nativeTapes_source] using
        prepared_source_head k input context count width height bits path unary frontier
          status carry j
    | right j =>
      have h2 : (⟨10 + j.val, by have := j.isLt; omega⟩ : Fin (k + 12)) ≠
          CarrySaveStream.coreEmb (k + 6) 2 := by
        intro h; have hv := congrArg Fin.val h; change 10 + j.val = 2 at hv; omega
      have h6 : 6 ≤ 10 + j.val := by omega
      simp [viewCfg, nativeTapes_extra, prepared, h2, initial,
        CarrySaveStream.config_extra_head, h6, scratch]
  · simp [viewCfg, prepared, initial]

/-- Place the evaluator's final configuration back beside the protected controller tapes. -/
@[expose] def completed {k : ℕ} {input : List Bool} (cfg : Cfg (k + 12) Bool Unit input)
    (q : RawInput) (out : List Bool) : Cfg (k + 12) Bool Unit input :=
  embed (nativeTapes k) (Native.final k input q out) cfg.workTapes cfg.workTapePos

/-- The real leaf machine prepares fields before invoking the native evaluator. -/
noncomputable def leafMachine {k : ℕ} {S : Type}
    (tm : MultiTapeTM (6 + (k + 2)) Bool S) (carry : Bool) :=
  (machine k carry).seq (tm.extendTapes (nativeTapes k))

/-- Actual traversal storage reaches the native leaf answer with preparation fully charged. -/
theorem runFrom_leafMachine {k : ℕ} {S : Type}
    (tm : MultiTapeTM (6 + (k + 2)) Bool S)
    (input context count width height bits path unary : List Bool)
    (frontier : ℤ) (status carry answer : Bool) (time : ℕ)
    (hr : tm.runFrom
      ((Native.initial k input (query context count width path bits carry)).withState
        (some tm.q₀))
      time = (Native.final k input (query context count width path bits carry) [answer]).withState
        none) :
    let cfg := initial k input context count width height bits path unary frontier status
    (leafMachine tm carry).runFrom (cfg.withState (some (leafMachine tm carry).q₀))
      (path.length + 3 + time) =
      (completed (prepared cfg carry) (query context count width path bits carry)
        [answer]).withState none := by
  dsimp only
  let cfg := initial k input context count width height bits path unary frontier status
  have hp := (runsBetween k input context count width height bits path unary frontier
    status carry).1
  have hv : viewCfg (nativeTapes k) ((prepared cfg carry).withState (some tm.q₀)) =
      (Native.initial k input (query context count width path bits carry)).withState
        (some tm.q₀) := by
    change (viewCfg (nativeTapes k) (prepared cfg carry)).withState _ = _
    rw [view_prepared]
    rfl
  have hn : (tm.extendTapes (nativeTapes k)).runFrom
      ((prepared cfg carry).withState (some tm.q₀)) time =
      (completed (prepared cfg carry) (query context count width path bits carry)
        [answer]).withState none := by
    rw [runFrom_extendTapes, hv, hr]
    rfl
  exact ((RunsBetween.of_runFrom hp).seq (RunsBetween.of_runFrom hn)).1

/-- One fixed polynomial clock for every reachable path and padded counter within a size budget. -/
@[expose] def clock (c d : ℕ) (context count width : List Bool) (sizeBudget : ℕ) : ℕ :=
  sizeBudget + 3 + c * (context.length + count.length + width.length + sizeBudget + 2) ^ d

private theorem clock_le (c d : ℕ) (context count width path bits : List Bool)
    (carry : Bool) (sizeBudget : ℕ) (hb : path.length + bits.length ≤ sizeBudget) :
    path.length + 3 + c * (Native.size (query context count width path bits carry) + 1) ^ d ≤
      clock c d context count width sizeBudget := by
  have hn : Native.size (query context count width path bits carry) + 1 ≤
      context.length + count.length + width.length + sizeBudget + 2 := by
    simp only [Native.size, query]
    omega
  have hp := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hn d)
  unfold clock
  omega

/-- A native polynomial-time counting predicate runs from actual persistent stream storage.
The carry word is written by the machine; all preparation, serialization and evaluation costs
are included in one clock uniform over the bounded path and counter words. -/
theorem exists_counting (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (leaf : Bool → MultiTapeTM (k + 12) Bool S)
      (c d : ℕ), ∀ (input context count width height bits path unary : List Bool)
        (frontier : ℤ) (status carry : Bool) (sizeBudget : ℕ),
      path.length + bits.length ≤ sizeBudget →
      let cfg := initial k input context count width height bits path unary frontier status
      (leaf carry).runFrom (cfg.withState (some (leaf carry).q₀))
        (clock c d context count width sizeBudget) =
        (completed (prepared cfg carry) (query context count width path bits carry)
          [runRaw predicate (query context count width path bits carry)]).withState none := by
  obtain ⟨k, S, hS, tm, c, d, hr⟩ := Native.exists_counting predicate hp
  let := hS
  refine ⟨k, _, inferInstance, leafMachine tm, c, d, ?_⟩
  intro input context count width height bits path unary frontier status carry sizeBudget hb
  have h := runFrom_leafMachine tm input context count width height bits path unary frontier
    status carry _ _ (hr (query context count width path bits carry) input)
  dsimp only at h ⊢
  rw [runFrom_eq_of_halt _ _ (clock_le c d context count width path bits carry sizeBudget hb)
    (by rw [h]; rfl), h]

end Turing.MultiTapeATM.CarrySaveLeaf
