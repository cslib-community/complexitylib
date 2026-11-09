/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Branch
public import CslibFrontier.Computability.WordRAM.Realization.Loop
import CslibFrontier.DataStructure.Memory.Frame

/-!
# Measure-bounded memory-client while loops

The source is finite recursion in the existing `Memory.Prog`. Its cutoff depends only on the
explicit initial input. A reached-state measure proves that the guard becomes false before the
cutoff, so the native code can use a genuine `Code.loop` without computing or storing that cutoff.
The native guard is an existing `Cond` on the faithfully encoded environment and mutable state;
an arbitrary semantic predicate is not granted executable code by a body certificate.

Local work counts only executed iterations. Every native guard, body, register copy and control
instruction is charged, including the initial/final false guard and iterations without queries.
Rank and potential may inspect reached memory as proof data; they never secretly select the
source program or its initial cutoff from unencoded memory.

## Main definitions

* `boundedWhile`: an early-exit loop represented by an ordinary finite memory program.
* `whileSafe`, `whileWork`: reached body domains, nontruncation and local iteration charges.

## Main results

* `whileSafe_of_measure`: invariant and decreasing rank establish the nontruncating domain.
* `boundedWhile_stops`: the returned source value has a false guard.
* `while_charge_le_potential`: a potential pays memory and local work and retains exit credit.
* `Realizes.whileBounded`: one native emitter before every runtime input and width.
* `Realizes.whileMeasure`: semantic invariant/rank conditions discharge the native entry domain.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {δ σ : Type} {k l r : ℕ}

section Source

variable (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
  (body : δ × σ → Memory.Prog σ)

/-- Finite source representation of a while loop. `whileSafe` excludes cutoff truncation. -/
def boundedWhile (d : δ) : ℕ → σ → Memory.Prog σ
  | 0, a => pure a
  | n + 1, a => if guard d a then do
      let a' ← body (d, a)
      boundedWhile d n a'
    else pure a

/-- Only continuing states require the body domain. At the cutoff the guard must be false. -/
def whileSafe (safe : ℕ → (δ × σ) → Memory.State → Prop) (w : ℕ) (d : δ) :
    ℕ → σ → Memory.State → Prop
  | 0, a, _ => ¬guard d a
  | n + 1, a, s => if guard d a then safe w (d, a) s ∧ whileSafe safe w d n
      ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a)))
    else True

/-- Local body work and one control unit for each executed iteration. The final guard is paid
by the existing realization overhead, even when no body executes. -/
def whileWork (work : (δ × σ) → Memory.State → ℕ) (d : δ) :
    ℕ → σ → Memory.State → ℕ
  | 0, _, _ => 0
  | n + 1, a, s => if guard d a then work (d, a) s + whileWork work d n
      ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a))) + 1
    else 0

/-- An initially false guard does not execute the body, independently of the ghost cutoff. -/
theorem boundedWhile_of_not (d : δ) (n : ℕ) (a : σ) (hg : ¬guard d a) :
    boundedWhile guard body d n a = pure a := by
  cases n <;> simp [boundedWhile, hg]

/-- Every real continuation splits its exact memory cost and local control charge. -/
theorem while_charge_succ (work : (δ × σ) → Memory.State → ℕ)
    (d : δ) (n : ℕ) (a : σ) (s : Memory.State) (hg : guard d a) :
    memoryCost (boundedWhile guard body d (n + 1) a) s +
        whileWork guard body work d (n + 1) a s =
      memoryCost (body (d, a)) s + work (d, a) s +
        (memoryCost (boundedWhile guard body d n
          ((Memory.spec 0).clientResult s (body (d, a))))
          ((Memory.spec 0).clientState s (body (d, a))) +
        whileWork guard body work d n ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a)))) + 1 := by
  simp only [boundedWhile, hg, ↓reduceIte, ← PFunctor.FreeM.bind_eq_bind,
    memoryCost_bind, whileWork]
  omega

/-- An invariant supplies the genuine body domain and a strictly decreasing reached-state
rank. The source cutoff is sufficient when it initially bounds that rank. No rank is executed. -/
theorem whileSafe_of_measure
    (safe : ℕ → (δ × σ) → Memory.State → Prop) (w : ℕ) (d : δ)
    (I : σ → Memory.State → Prop) (rank : σ → Memory.State → ℕ)
    (hzero : ∀ a s, I a s → rank a s = 0 → ¬guard d a)
    (hstep : ∀ a s, I a s → guard d a →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) →
      safe w (d, a) s ∧
        I ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))) ∧
        rank ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))) < rank a s)
    {n : ℕ} {a : σ} {s : Memory.State} (hi : I a s) (hr : rank a s ≤ n)
    (hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard body d n a))) :
    whileSafe guard body safe w d n a s := by
  induction n generalizing a s with
  | zero => exact hzero a s hi (by omega)
  | succ n ih =>
    by_cases hg : guard d a
    · simp only [boundedWhile, hg, ↓reduceIte] at hv
      obtain ⟨hb, ht⟩ := (validHistory_bind w (body (d, a))
        (boundedWhile guard body d n) s).mp hv
      rw [clientResult_width w, clientState_width w] at ht
      obtain ⟨hsafe, hi', hr'⟩ := hstep a s hi hg hb
      change if guard d a then _ else True
      rw [ite_eq_left hg]
      exact ⟨hsafe, ih hi' (by omega) ht⟩
    · simp [whileSafe, hg]

/-- The reached-state domain guarantees a false guard at the actual returned source value,
not merely a value obtained by truncating an unfinished loop. -/
theorem boundedWhile_stops
    (safe : ℕ → (δ × σ) → Memory.State → Prop) (w : ℕ) (d : δ)
    {n : ℕ} {a : σ} {s : Memory.State} (hs : whileSafe guard body safe w d n a s)
    (hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard body d n a))) :
    ¬guard d ((Memory.spec 0).clientResult s (boundedWhile guard body d n a)) := by
  induction n generalizing a s with
  | zero => simpa only [boundedWhile, whileSafe, StateTransitionSpec.clientResult,
      StateTransitionSpec.runClient_pure'] using hs
  | succ n ih =>
    by_cases hg : guard d a
    · simp only [whileSafe, hg, ↓reduceIte] at hs
      simp only [boundedWhile, hg, ↓reduceIte] at hv
      have ht := ((validHistory_bind w (body (d, a)) (boundedWhile guard body d n) s).mp hv).2
      rw [clientResult_width w, clientState_width w] at ht
      simpa only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
        StateTransitionSpec.clientState, ← PFunctor.FreeM.bind_eq_bind,
        StateTransitionSpec.runClient_bind] using ih hs.2 ht
    · simpa only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
        StateTransitionSpec.runClient_pure'] using hg

/-- The charged source cost telescopes while preserving the remaining exit potential. This
can pay query-free iterations because local work and control are included in every step. -/
theorem while_charge_le_potential
    (work : (δ × σ) → Memory.State → ℕ) (w : ℕ) (d : δ)
    (I : σ → Memory.State → Prop) (potential : σ → Memory.State → ℕ)
    (hstep : ∀ a s, I a s → guard d a →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) →
      I ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))) ∧
        memoryCost (body (d, a)) s + work (d, a) s + 1 +
          potential ((Memory.spec 0).clientResult s (body (d, a)))
            ((Memory.spec 0).clientState s (body (d, a))) ≤ potential a s)
    {n : ℕ} {a : σ} {s : Memory.State} (hi : I a s)
    (hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard body d n a))) :
    memoryCost (boundedWhile guard body d n a) s + whileWork guard body work d n a s +
      potential ((Memory.spec 0).clientResult s (boundedWhile guard body d n a))
        ((Memory.spec 0).clientState s (boundedWhile guard body d n a)) ≤ potential a s := by
  induction n generalizing a s with
  | zero => simp [boundedWhile, whileWork, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState]
  | succ n ih =>
    by_cases hg : guard d a
    · have hv' := hv
      simp only [boundedWhile, hg, ↓reduceIte] at hv'
      obtain ⟨hb, ht⟩ := (validHistory_bind w (body (d, a))
        (boundedWhile guard body d n) s).mp hv'
      rw [clientResult_width w, clientState_width w] at ht
      obtain ⟨hi', hp⟩ := hstep a s hi hg hb
      have hrest := ih hi' ht
      rw [while_charge_succ guard body work d n a s hg]
      simp only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
        StateTransitionSpec.clientState, ← PFunctor.FreeM.bind_eq_bind,
        StateTransitionSpec.runClient_bind] at *
      omega
    · rw [boundedWhile_of_not guard body d (n + 1) a hg]
      simp [whileWork, hg, StateTransitionSpec.clientResult, StateTransitionSpec.clientState]

end Source

private def whileStateSlot {l n : ℕ} (i : Fin l) : Fin (l + (l + n + 1) + 1) :=
  ⟨i.val, by omega⟩

private def whileBodySlot {l n : ℕ} (i : Fin (l + n + 1)) : Fin (l + (l + n + 1) + 1) :=
  ⟨l + i.val, by omega⟩

private def whileBody {B : Basis} {n : ℕ}
    (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r)
    (frontier : Fin r) (src : Fin (k + l) → Fin r)
    (tmp : Fin (l + (l + n + 1) + 1) → Fin r) : Code B r :=
  .seq (emit frontier (Fin.append (fun i : Fin k => src (Fin.castAdd l i))
    (fun i => tmp (whileStateSlot i))) (fun i => tmp (whileBodySlot i)))
    (copyBank (fun i : Fin l => tmp (whileBodySlot (Fin.castAdd (n + 1) i)))
      (fun i => tmp (whileStateSlot i)) (tmp (Fin.last (l + (l + n + 1)))))

private def whileEmit {B : Basis} {n : ℕ} (cond : Cond (k + l))
    (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r)
    (frontier : Fin r) (src : Fin (k + l) → Fin r)
    (tmp : Fin (l + (l + n + 1) + 1) → Fin r) : Code B r :=
  .seq (copyBank (fun i : Fin l => src (Fin.natAdd k i))
    (fun i => tmp (whileStateSlot i)) (tmp (Fin.last (l + (l + n + 1)))))
    (.loop (cond.rename (Fin.append (fun i : Fin k => src (Fin.castAdd l i))
      (fun i => tmp (whileStateSlot i)))) (whileBody emit frontier src tmp))

namespace Realizes

/-- One native while emitter genuinely exits on the existing encoded condition. The pure source
cutoff depends only on explicit initial input and is not computed or stored by this emitter.
The domain excludes truncation; every executed guard/body/copy/control and final exit is charged. -/
theorem whileBounded {B : Basis} (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    (cond : Cond (k + l)) (cutoff : δ × σ → ℕ)
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Realizes B body (appendWords input output) output safe work) :
    Realizes B (fun (d, a) => boundedWhile
      (fun d a => test cond ((appendWords input output) (d, a))) body d (cutoff (d, a)) a)
      (appendWords input output) output
      (fun w (d, a) s => whileSafe
        (fun d a => test cond ((appendWords input output) (d, a))) body safe w d
        (cutoff (d, a)) a s)
      (fun (d, a) s => whileWork
        (fun d a => test cond ((appendWords input output) (d, a))) body work d
        (cutoff (d, a)) a s) := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨l + n + 1, C + 2 * l + 4, whileEmit cond emit, ?_⟩
  intro r frontier src tmp hi hd hf hs
  let st : Fin l → Fin r := fun i => tmp (whileStateSlot i)
  let bt : Fin (l + n + 1) → Fin r := fun i => tmp (whileBodySlot i)
  let env : Fin k → Fin r := fun i => src (Fin.castAdd l i)
  let bs := Fin.append env st
  let idle := tmp (Fin.last (l + (l + n + 1)))
  have hst : Function.Injective st := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val (hi hij)
    exact hh
  have hbt : Function.Injective bt := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val (hi hij)
    dsimp only [whileBodySlot] at hh
    omega
  have hbdis : ∀ i j, bs i ≠ bt j := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [bs, Fin.append_left] using hd (Fin.castAdd l i) (whileBodySlot j)
    · simp only [bs, Fin.append_right]
      intro hij
      have hh := congrArg Fin.val (hi hij)
      dsimp only [whileStateSlot, whileBodySlot] at hh
      omega
  have hbf : ∀ j, bt j ≠ frontier := fun j => hf _
  have hbs : ∀ i, bs i ≠ frontier := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [bs, Fin.append_left] using hs (Fin.castAdd l i)
    · simpa only [bs, Fin.append_right] using hf (whileStateSlot i)
  obtain ⟨hnw, hrun⟩ := he frontier bs bt hbt hbdis hbf hbs
  have houtdis : ∀ i j : Fin l, bt (Fin.castAdd (n + 1) i) ≠ st j := by
    intro i j hij
    have hh := congrArg Fin.val (hi hij)
    dsimp only [whileBodySlot, whileStateSlot] at hh
    omega
  refine ⟨?_, ?_⟩
  · simpa [whileEmit, whileBody, Code.ReadsWidth, copyBank_not_readsWidth] using hnw
  · rintro w ⟨d, a₀⟩ x hx hin hsafe hv
    let guard := fun d a => test cond ((appendWords input output) (d, a))
    let I : (σ × Memory.State) → Data r → Prop := fun q y =>
      y.Bounded w ∧ memoryState frontier y = q.2 ∧
      (∀ i, y.regs (env i) = input d i) ∧ (∀ i, y.regs (st i) = output q.1 i) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i
    have hcond (q : σ × Memory.State) (y : Data r) (hI : I q y) :
        (cond.rename bs).Holds y ↔ guard d q.1 := by
      have hb : y.regs ∘ bs = (appendWords input output) (d, q.1) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa [bs, appendWords, Fin.appendEquiv] using hI.2.2.1 i
        · simpa [bs, appendWords, Fin.appendEquiv] using hI.2.2.2.1 i
      cases cond <;> simp only [Cond.rename, Cond.Holds, guard, test] <;>
        simp only [← hb, Function.comp_apply]
    have step (q : σ × Memory.State) (y : Data r) (hI : I q y)
        (hdom : safe w (d, q.1) q.2)
        (hvalid : (Memory.spec w).ValidHistory q.2
          ((Memory.spec w).clientHistory q.2 (body (d, q.1)))) :
        ∃ z, ExecWithin w (whileBody emit frontier src tmp) y z
            (C * (memoryCost (body (d, q.1)) q.2 + work (d, q.1) q.2 + 1) + (l + 1)) ∧
          I (iterationStep body d q) z := by
      obtain ⟨hyb, hym, hye, hys, hyframe⟩ := hI
      have hinput : y.regs ∘ bs = (appendWords input output) (d, q.1) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa [bs, appendWords, Fin.appendEquiv] using hye i
        · simpa [bs, appendWords, Fin.appendEquiv] using hys i
      obtain ⟨u, hu, hum, huo, huf⟩ := hrun w (d, q.1) y hyb hinput
        (hym ▸ hdom) (hym ▸ hvalid)
      rw [hym] at hu hum huo
      rw [clientState_width] at hum
      simp only [clientResult_width] at huo
      obtain ⟨z, hz, hzm, hzs, hzf⟩ := copyBank_exec (B := B)
        (fun i : Fin l => bt (Fin.castAdd (n + 1) i)) st idle hst houtdis w u
      refine ⟨z, hu.seq hz, (hu.seq hz).bounded hyb, ?_, ?_, ?_, ?_⟩
      · apply Memory.State.ext
        · exact hzm.trans (congrArg Memory.State.mem hum)
        · change z.regs frontier = _
          rw [show z.regs frontier = u.regs frontier from hzf frontier (fun i => hf _)]
          exact congrArg Memory.State.frontier hum
      · intro i
        rw [hzf _ (fun _ => (hd _ _).symm), huf _ (hs _) (fun _ => (hd _ _).symm)]
        exact hye i
      · intro i
        rw [hzs, huo]
        rfl
      · intro i hif htmp
        rw [hzf _ (fun _ => htmp _), huf _ hif (fun _ => htmp _)]
        exact hyframe i hif htmp
    have aux : ∀ fuel q y, I q y → whileSafe guard body safe w d fuel q.1 q.2 →
        (Memory.spec w).ValidHistory q.2
          ((Memory.spec w).clientHistory q.2 (boundedWhile guard body d fuel q.1)) →
        ∃ z, ExecWithin w (.loop (cond.rename bs) (whileBody emit frontier src tmp)) y z
            ((C + l + 3) * (memoryCost (boundedWhile guard body d fuel q.1) q.2 +
              whileWork guard body work d fuel q.1 q.2 + 1)) ∧
          I ((Memory.spec 0).clientResult q.2 (boundedWhile guard body d fuel q.1),
            (Memory.spec 0).clientState q.2 (boundedWhile guard body d fuel q.1)) z := by
      intro fuel
      induction fuel with
      | zero =>
        intro q y hI hdom hvalid
        refine ⟨y, (ExecWithin.loop_exit (by exact (hcond q y hI).not.mpr hdom)).mono ?_, ?_⟩
        · change 2 ≤ (C + l + 3) * (0 + 0 + 1)
          omega
        · simpa only [boundedWhile, StateTransitionSpec.clientResult,
            StateTransitionSpec.clientState, StateTransitionSpec.runClient_pure'] using hI
      | succ fuel ih =>
        intro q y hI hdom hvalid
        by_cases hg : guard d q.1
        · simp only [whileSafe, hg, ↓reduceIte] at hdom
          simp only [boundedWhile, hg, ↓reduceIte] at hvalid
          obtain ⟨hb, ht⟩ := (validHistory_bind w (body (d, q.1))
            (boundedWhile guard body d fuel) q.2).mp hvalid
          rw [clientResult_width w, clientState_width w] at ht
          obtain ⟨u, hu, hIu⟩ := step q y hI hdom.1 hb
          obtain ⟨z, hz, hIz⟩ := ih (iterationStep body d q) u hIu hdom.2 ht
          refine ⟨z, (ExecWithin.loop_iter ((hcond q y hI).mpr hg) hu hz).mono ?_, ?_⟩
          · rw [while_charge_succ guard body work d fuel q.1 q.2 hg]
            dsimp only [iterationStep] at hz ⊢
            nlinarith
          · simpa only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
              StateTransitionSpec.clientState, ← PFunctor.FreeM.bind_eq_bind,
              StateTransitionSpec.runClient_bind, iterationStep] using hIz
        · refine ⟨y, (ExecWithin.loop_exit ((hcond q y hI).not.mpr hg)).mono ?_, ?_⟩
          · rw [boundedWhile_of_not guard body d (fuel + 1) q.1 hg]
            simp only [memoryCost_pure, whileWork, hg, ↓reduceIte]
            omega
          · simpa only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
              StateTransitionSpec.clientState, StateTransitionSpec.runClient_pure'] using hI
    obtain ⟨a, ha, ham, has, haf⟩ := copyBank_exec (B := B)
      (fun i : Fin l => src (Fin.natAdd k i)) st idle hst (fun _ _ => hd _ _) w x
    have hIa : I (a₀, memoryState frontier x) a := by
      refine ⟨ha.bounded hx, ?_, ?_, ?_, ?_⟩
      · apply Memory.State.ext
        · exact ham
        · exact haf frontier (fun i => hf _)
      · intro i
        rw [haf _ (fun _ => (hd _ _).symm)]
        simpa [env, appendWords, Fin.appendEquiv] using congrFun hin (Fin.castAdd l i)
      · intro i
        rw [has]
        simpa [appendWords, Fin.appendEquiv] using congrFun hin (Fin.natAdd k i)
      · intro i _ htmp
        exact haf i (fun _ => htmp _)
    obtain ⟨y, hy, hyb, hym, _, hys, hyf⟩ :=
      aux (cutoff (d, a₀)) (a₀, memoryState frontier x) a hIa hsafe hv
    refine ⟨y, (ha.seq hy).mono ?_, ?_, ?_, hyf⟩
    · nlinarith
    · rw [clientState_width w]
      exact hym
    · intro i
      rw [clientResult_width w]
      exact hys i

/-- Semantic invariants and a decreasing rank establish the native while's complete reached-state
domain. The rank/cutoff comparison is proof data; the emitted code still tests only `cond`. -/
theorem whileMeasure {B : Basis} (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    (cond : Cond (k + l)) (cutoff : δ × σ → ℕ)
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Realizes B body (appendWords input output) output safe work)
    (I : ℕ → δ → σ → Memory.State → Prop) (rank : δ → σ → Memory.State → ℕ)
    (hzero : ∀ w d a s, I w d a s → rank d a s = 0 →
      ¬test cond ((appendWords input output) (d, a)))
    (hstep : ∀ w d a s, I w d a s → test cond ((appendWords input output) (d, a)) →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) →
      safe w (d, a) s ∧
        I w d ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))) ∧
        rank d ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))) < rank d a s) :
    Realizes B (fun (d, a) => boundedWhile
      (fun d a => test cond ((appendWords input output) (d, a))) body d (cutoff (d, a)) a)
      (appendWords input output) output
      (fun w (d, a) s => I w d a s ∧ rank d a s ≤ cutoff (d, a))
      (fun (d, a) s => whileWork
        (fun d a => test cond ((appendWords input output) (d, a))) body work d
        (cutoff (d, a)) a s) := by
  obtain ⟨n, C, emit, he⟩ := whileBounded input output cond cutoff h
  refine ⟨n, C, emit, ?_⟩
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨hnw, ?_⟩
  rintro w ⟨d, a⟩ x hx hin ⟨hI, hr⟩ hv
  exact hrun w (d, a) x hx hin
    (whileSafe_of_measure _ body safe w d (I w d) (rank d)
      (hzero w d) (hstep w d) hI hr hv) hv

end Realizes

namespace RealizesBounded

/-- Frontier-bounded native while realization. -/
theorem whileBounded {B : Basis} (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    (cond : Cond (k + l)) (cutoff : δ × σ → ℕ)
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : RealizesBounded B body (appendWords input output) output safe work) :
    RealizesBounded B (fun (d, a) => boundedWhile
      (fun d a => test cond ((appendWords input output) (d, a))) body d (cutoff (d, a)) a)
      (appendWords input output) output
      (fun w (d, a) s => whileSafe
        (fun d a => test cond ((appendWords input output) (d, a))) body safe w d
        (cutoff (d, a)) a s)
      (fun (d, a) s => whileWork
        (fun d a => test cond ((appendWords input output) (d, a))) body work d
        (cutoff (d, a)) a s) := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨l + n + 1, C + 2 * l + 4, whileEmit cond emit, ?_⟩
  intro r frontier src tmp hi hd hf hs
  let st : Fin l → Fin r := fun i => tmp (whileStateSlot i)
  let bt : Fin (l + n + 1) → Fin r := fun i => tmp (whileBodySlot i)
  let env : Fin k → Fin r := fun i => src (Fin.castAdd l i)
  let bs := Fin.append env st
  let idle := tmp (Fin.last (l + (l + n + 1)))
  have hst : Function.Injective st := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val (hi hij)
    exact hh
  have hbt : Function.Injective bt := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val (hi hij)
    dsimp only [whileBodySlot] at hh
    omega
  have hbdis : ∀ i j, bs i ≠ bt j := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [bs, Fin.append_left] using hd (Fin.castAdd l i) (whileBodySlot j)
    · simp only [bs, Fin.append_right]
      intro hij
      have hh := congrArg Fin.val (hi hij)
      dsimp only [whileStateSlot, whileBodySlot] at hh
      omega
  have hbf : ∀ j, bt j ≠ frontier := fun j => hf _
  have hbs : ∀ i, bs i ≠ frontier := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [bs, Fin.append_left] using hs (Fin.castAdd l i)
    · simpa only [bs, Fin.append_right] using hf (whileStateSlot i)
  obtain ⟨hnw, hrun⟩ := he frontier bs bt hbt hbdis hbf hbs
  have houtdis : ∀ i j : Fin l, bt (Fin.castAdd (n + 1) i) ≠ st j := by
    intro i j hij
    have hh := congrArg Fin.val (hi hij)
    dsimp only [whileBodySlot, whileStateSlot] at hh
    omega
  refine ⟨by simpa [whileEmit, whileBody, Code.ReadsWidth, copyBank_not_readsWidth] using hnw, ?_⟩
  rintro w ⟨d, a₀⟩ x hx hin hsafe hv
  let guard := fun d a => test cond ((appendWords input output) (d, a))
  let I : (σ × Memory.State) → Data r → Prop := fun q y =>
    y.Bounded w ∧ memoryState frontier y = q.2 ∧
    (∀ i, y.regs (env i) = input d i) ∧ (∀ i, y.regs (st i) = output q.1 i) ∧
    ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i
  have hcond (q : σ × Memory.State) (y : Data r) (hI : I q y) :
      (cond.rename bs).Holds y ↔ guard d q.1 := by
    have hb : y.regs ∘ bs = (appendWords input output) (d, q.1) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa [bs, appendWords, Fin.appendEquiv] using hI.2.2.1 i
      · simpa [bs, appendWords, Fin.appendEquiv] using hI.2.2.2.1 i
    cases cond <;> simp only [Cond.rename, Cond.Holds, guard, test] <;>
      simp only [← hb, Function.comp_apply]
  have step (q : σ × Memory.State) (y : Data r) (hI : I q y)
      (hdom : safe w (d, q.1) q.2)
      (hvalid : (Memory.spec w).ValidHistory q.2
        ((Memory.spec w).clientHistory q.2 (body (d, q.1)))) :
      ∃ z, ExecBounded w (z.regs frontier) (whileBody emit frontier src tmp) y z
          (C * (memoryCost (body (d, q.1)) q.2 + work (d, q.1) q.2 + 1) + (l + 1)) ∧
        I (iterationStep body d q) z := by
    obtain ⟨hyb, hym, hye, hys, hyframe⟩ := hI
    have hinput : y.regs ∘ bs = (appendWords input output) (d, q.1) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa [bs, appendWords, Fin.appendEquiv] using hye i
      · simpa [bs, appendWords, Fin.appendEquiv] using hys i
    obtain ⟨u, hu, hum, huo, huf⟩ := hrun w (d, q.1) y hyb hinput
      (hym ▸ hdom) (hym ▸ hvalid)
    rw [hym] at hu hum huo
    rw [clientState_width] at hum
    simp only [clientResult_width] at huo
    obtain ⟨z, hz, hzm, hzs, hzf⟩ := copyBank_execBounded (B := B)
      (fun i : Fin l => bt (Fin.castAdd (n + 1) i)) st idle hst houtdis w (u.regs frontier) u
    have hzu_fr : z.regs frontier = u.regs frontier := hzf frontier (fun i => hf _)
    have hseq := hu.seq hz
    rw [← hzu_fr] at hseq
    refine ⟨z, hseq, hseq.bounded hyb, ?_, ?_, ?_, ?_⟩
    · apply Memory.State.ext
      · exact hzm.trans (congrArg Memory.State.mem hum)
      · change z.regs frontier = _
        rw [hzu_fr]
        exact congrArg Memory.State.frontier hum
    · intro i
      rw [hzf _ (fun _ => (hd _ _).symm), huf _ (hs _) (fun _ => (hd _ _).symm)]
      exact hye i
    · intro i
      rw [hzs, huo]
      rfl
    · intro i hif htmp
      rw [hzf _ (fun _ => htmp _), huf _ hif (fun _ => htmp _)]
      exact hyframe i hif htmp
  have aux : ∀ fuel q y, I q y → whileSafe guard body safe w d fuel q.1 q.2 →
      (Memory.spec w).ValidHistory q.2
        ((Memory.spec w).clientHistory q.2 (boundedWhile guard body d fuel q.1)) →
      ∃ z, ExecBounded w (z.regs frontier)
          (.loop (cond.rename bs) (whileBody emit frontier src tmp)) y z
          ((C + l + 3) * (memoryCost (boundedWhile guard body d fuel q.1) q.2 +
            whileWork guard body work d fuel q.1 q.2 + 1)) ∧
        I ((Memory.spec 0).clientResult q.2 (boundedWhile guard body d fuel q.1),
          (Memory.spec 0).clientState q.2 (boundedWhile guard body d fuel q.1)) z := by
    intro fuel
    induction fuel with
    | zero =>
      intro q y hI hdom _
      refine ⟨y, (ExecBounded.loop_exit ((hcond q y hI).not.mpr hdom)).mono ?_, ?_⟩
      · change 2 ≤ (C + l + 3) * (0 + 0 + 1)
        omega
      · simpa only [boundedWhile, StateTransitionSpec.clientResult,
          StateTransitionSpec.clientState, StateTransitionSpec.runClient_pure'] using hI
    | succ fuel ih =>
      intro q y hI hdom hvalid
      by_cases hg : guard d q.1
      · simp only [whileSafe, hg, ↓reduceIte] at hdom
        simp only [boundedWhile, hg, ↓reduceIte] at hvalid
        obtain ⟨hb, ht⟩ := (validHistory_bind w (body (d, q.1))
          (boundedWhile guard body d fuel) q.2).mp hvalid
        rw [clientResult_width w, clientState_width w] at ht
        obtain ⟨u, hu, hIu⟩ := step q y hI hdom.1 hb
        obtain ⟨z, hz, hIz⟩ := ih (iterationStep body d q) u hIu hdom.2 ht
        have hu_le : u.regs frontier ≤ z.regs frontier := by
          have hu_fr := congrArg Memory.State.frontier hIu.2.1
          have hz_fr := congrArg Memory.State.frontier hIz.2.1
          change u.regs frontier = (iterationStep body d q).2.frontier at hu_fr
          change z.regs frontier = ((Memory.spec 0).clientState (iterationStep body d q).2
            (boundedWhile guard body d fuel (iterationStep body d q).1)).frontier at hz_fr
          rw [hu_fr, hz_fr]
          exact Memory.frontier_le_clientState (w := 0) _ _
        refine ⟨z, (ExecBounded.loop_iter ((hcond q y hI).mpr hg) (hu.mono_bound hu_le) hz).mono ?_,
          ?_⟩
        · rw [while_charge_succ guard body work d fuel q.1 q.2 hg]
          dsimp only [iterationStep] at hz ⊢
          nlinarith
        · simpa only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
            StateTransitionSpec.clientState, ← PFunctor.FreeM.bind_eq_bind,
            StateTransitionSpec.runClient_bind, iterationStep] using hIz
      · refine ⟨y, (ExecBounded.loop_exit ((hcond q y hI).not.mpr hg)).mono ?_, ?_⟩
        · rw [boundedWhile_of_not guard body d (fuel + 1) q.1 hg]
          simp only [memoryCost_pure, whileWork, hg, ↓reduceIte]
          omega
        · simpa only [boundedWhile, hg, ↓reduceIte, StateTransitionSpec.clientResult,
            StateTransitionSpec.clientState, StateTransitionSpec.runClient_pure'] using hI
  obtain ⟨a, ha, ham, has, haf⟩ := copyBank_execBounded (B := B)
    (fun i : Fin l => src (Fin.natAdd k i)) st idle hst (fun _ _ => hd _ _) w 0 x
  have hIa : I (a₀, memoryState frontier x) a := by
    refine ⟨ha.bounded hx, ?_, ?_, ?_, ?_⟩
    · apply Memory.State.ext
      · exact ham
      · exact haf frontier (fun i => hf _)
    · intro i
      rw [haf _ (fun _ => (hd _ _).symm)]
      simpa [env, appendWords, Fin.appendEquiv] using congrFun hin (Fin.castAdd l i)
    · intro i
      rw [has]
      simpa [appendWords, Fin.appendEquiv] using congrFun hin (Fin.natAdd k i)
    · intro i _ htmp
      exact haf i (fun _ => htmp _)
  obtain ⟨y, hy, _, hym, _, hys, hyf⟩ :=
    aux (cutoff (d, a₀)) (a₀, memoryState frontier x) a hIa hsafe hv
  refine ⟨y, ((ha.mono_bound (Nat.zero_le _)).seq hy).mono ?_, ?_, ?_, hyf⟩
  · nlinarith
  · rw [clientState_width w]
    exact hym
  · intro i
    rw [clientResult_width w]
    exact hys i

/-- Measure-bounded frontier-bounded while realization. -/
theorem whileMeasure {B : Basis} (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    (cond : Cond (k + l)) (cutoff : δ × σ → ℕ)
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : RealizesBounded B body (appendWords input output) output safe work)
    (I : ℕ → δ → σ → Memory.State → Prop) (rank : δ → σ → Memory.State → ℕ)
    (hzero : ∀ w d a s, I w d a s → rank d a s = 0 →
      ¬test cond ((appendWords input output) (d, a)))
    (hstep : ∀ w d a s, I w d a s → test cond ((appendWords input output) (d, a)) →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) →
      safe w (d, a) s ∧
        I w d ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))) ∧
        rank d ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))) < rank d a s) :
    RealizesBounded B (fun (d, a) => boundedWhile
      (fun d a => test cond ((appendWords input output) (d, a))) body d (cutoff (d, a)) a)
      (appendWords input output) output
      (fun w (d, a) s => I w d a s ∧ rank d a s ≤ cutoff (d, a))
      (fun (d, a) s => whileWork
        (fun d a => test cond ((appendWords input output) (d, a))) body work d
        (cutoff (d, a)) a s) := by
  obtain ⟨n, C, emit, he⟩ := whileBounded input output cond cutoff h
  refine ⟨n, C, emit, fun frontier src tmp hi hd hf hs => ?_⟩
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨hnw, ?_⟩
  rintro w ⟨d, a⟩ x hx hin ⟨hI, hr⟩ hv
  exact hrun w (d, a) x hx hin
    (whileSafe_of_measure _ body safe w d (I w d) (rank d)
      (hzero w d) (hstep w d) hI hr hv) hv

end RealizesBounded

end Cslib.WordRAM.Realization
