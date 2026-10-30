/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WordMoves
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
import Mathlib.Tactic.FinCases

/-!
# The stack-loop machine: tape layout and phases

The machine of `Turing.MultiTapeTM.ComputableInO.stackLoop` has the `kk` work tapes shared by the
machines it runs, followed by six named tapes: a flag tape for `Turing.MultiTapeTM.onWords`, the
current value `C`, the halting flag `F`, the round input or output `R`, the pushed frames `P` and
the stack `S`. The stack is kept as the framed words of its frames, top first, ending just before
cell `0` of `S`, so that pushing writes to the left and popping erases from the left.

This file describes the configurations of the machine (`StackLoopKernel.cfgS`) and the runs of its
phases between them.
-/

@[expose] public section

namespace Turing.MultiTapeTM.StackLoopKernel

variable {kk : ℕ} {input : List Bool}

/-! ### Tape layout -/

/-- The named tape `j`: `0` flag, `1` current value, `2` halting flag, `3` round word, `4` pushed
frames, `5` stack. -/
abbrev nm (j : Fin 6) : Fin (kk + 6) := Fin.natAdd kk j

/-- The words on the tapes: the shared work tapes and the flag tape are blank. -/
def tapeWords (c f r p s : List Bool) : Fin (kk + 6) → List Bool :=
  Fin.append (fun _ => []) ![[], c, f, r, p, s]

/-- The offsets of the words: only the current value and the stack may be shifted. -/
def tapeOffs (oc os : ℤ) : Fin (kk + 6) → ℤ := Fin.append (fun _ => 0) ![0, oc, 0, 0, 0, os]

/-- The heads: on the first cells of the words, except possibly on the round word and the pushed
frames. -/
def tapeHeads (oc os hr hp : ℤ) : Fin (kk + 6) → ℤ :=
  Fin.append (fun _ => 0) ![0, oc, 0, hr, hp, os]

/-- A configuration of the stack-loop machine. -/
def cfgS (input : List Bool) (c f r p s : List Bool) (oc os hr hp : ℤ) (out : List Bool) :
    Cfg (kk + 6) Bool Unit input :=
  tapesCfg input (tapeWords c f r p s) (tapeOffs oc os) (tapeHeads oc os hr hp) out

lemma tapeHeads_zero (oc os : ℤ) : tapeHeads (kk := kk) oc os 0 0 = tapeOffs oc os := rfl

@[simp] lemma tapeWords_castAdd (c f r p s : List Bool) (i : Fin kk) :
    tapeWords c f r p s (Fin.castAdd 6 i) = [] := Fin.append_left _ _ _
@[simp] lemma tapeWords_nm (c f r p s : List Bool) (j : Fin 6) :
    tapeWords (kk := kk) c f r p s (nm j) = ![[], c, f, r, p, s] j := Fin.append_right _ _ _
@[simp] lemma tapeOffs_castAdd (oc os : ℤ) (i : Fin kk) :
    tapeOffs oc os (Fin.castAdd 6 i) = 0 := Fin.append_left _ _ _
@[simp] lemma tapeOffs_nm (oc os : ℤ) (j : Fin 6) :
    tapeOffs (kk := kk) oc os (nm j) = ![0, oc, 0, 0, 0, os] j := Fin.append_right _ _ _
@[simp] lemma tapeHeads_castAdd (oc os hr hp : ℤ) (i : Fin kk) :
    tapeHeads oc os hr hp (Fin.castAdd 6 i) = 0 := Fin.append_left _ _ _
@[simp] lemma tapeHeads_nm (oc os hr hp : ℤ) (j : Fin 6) :
    tapeHeads (kk := kk) oc os hr hp (nm j) = ![0, oc, 0, hr, hp, os] j := Fin.append_right _ _ _

/-- Two families on the tapes agree if they agree on the shared and the named tapes. -/
lemma fun_ext_tapes {α : Type*} {f g : Fin (kk + 6) → α} (h₁ : ∀ i, f (Fin.castAdd 6 i) =
    g (Fin.castAdd 6 i)) (h₂ : ∀ j, f (nm j) = g (nm j)) : f = g := by
  funext l
  induction l using Fin.addCases with
  | left i => exact h₁ i
  | right j => exact h₂ j

/-! ### Embeddings of the phases -/

/-- The tapes of `Turing.MultiTapeTM.onWords` with `kk` work tapes: the shared tapes, the output
tape `nm o`, the input tape `nm v` and the flag tape `nm 0`. -/
def owEmb (v o : Fin 6) (hv : v.val ≠ 0) (ho : o.val ≠ 0) (hvo : v.val ≠ o.val) :
    Fin (kk + 1 + 2) ↪ Fin (kk + 6) :=
  ⟨fun j => if h : j.val < kk then Fin.castAdd 6 ⟨j.val, h⟩
    else if j.val = kk then nm o else if j.val = kk + 1 then nm v else nm 0, by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    simp only at hab
    split_ifs at hab <;> simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hab <;>
      omega⟩

section OwEmb

variable {v o : Fin 6} {hv : v.val ≠ 0} {ho : o.val ≠ 0} {hvo : v.val ≠ o.val}

@[simp] lemma owEmb_work (i : Fin kk) :
    owEmb v o hv ho hvo ((Fin.castSucc i).castAdd 2) = Fin.castAdd 6 i := by
  unfold owEmb
  simp only [Function.Embedding.coeFn_mk]
  rw [dite_eq_left (by simp)]
  rfl

@[simp] lemma owEmb_out : owEmb v o hv ho hvo ((Fin.last kk).castAdd 2) = nm o := by
  simp [owEmb]

@[simp] lemma owEmb_in : owEmb v o hv ho hvo (Fin.natAdd (kk + 1) 0) = nm v := by
  simp [owEmb]

@[simp] lemma owEmb_flag : owEmb v o hv ho hvo (Fin.natAdd (kk + 1) 1) = nm 0 := by
  unfold owEmb
  simp only [Function.Embedding.coeFn_mk, Fin.val_natAdd, Fin.val_one]
  rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

end OwEmb

/-- The tapes of `Turing.MultiTapeTM.outputToWord` with `kk` work tapes: the shared tapes and the
current value. -/
def initEmb : Fin (kk + 1) ↪ Fin (kk + 6) :=
  ⟨fun j => if h : j.val < kk then Fin.castAdd 6 ⟨j.val, h⟩ else nm 1, by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    simp only at hab
    split_ifs at hab <;> simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hab <;>
      omega⟩

@[simp] lemma initEmb_work (i : Fin kk) : initEmb (Fin.castSucc i) = Fin.castAdd 6 i := by
  unfold initEmb
  simp only [Function.Embedding.coeFn_mk]
  rw [dite_eq_left (by simp)]
  rfl

@[simp] lemma initEmb_last : initEmb (Fin.last kk) = nm 1 := by
  simp [initEmb]

/-- Two named tapes, for a two-tape machine. -/
def pairEmb (a b : Fin 6) (h : a ≠ b) : Fin 2 ↪ Fin (kk + 6) :=
  ⟨![nm a, nm b], by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [Fin.natAdd_inj]⟩

/-- The tapes of `Turing.MultiTapeTM.copyWord`: from the round word to the current value. -/
def copyEmb : Fin (0 + 1 + 2) ↪ Fin (kk + 6) :=
  ⟨![nm 1, nm 3, nm 0], by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [Fin.natAdd_inj]⟩

/-- The tapes of `Turing.MultiTapeTM.emitWord`: the current value. -/
def emitEmb : Fin (0 + 2) ↪ Fin (kk + 6) :=
  ⟨![nm 1, nm 0], by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [Fin.natAdd_inj]⟩

/-! ### Specifications on embedded tapes -/

/-- **`onWords` on embedded tapes**, with every other tape arbitrary: the input on the tape
selected for the input of `onWords`, its other tapes blank. -/
theorem transformsTapes_onWords_embed {k K : ℕ} {Symbol S : Type*} {tm : MultiTapeTM k Symbol S}
    {x y : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace x y t s) (mark : Symbol)
    (e : Fin (k + 1 + 2) ↪ Fin K) :
    TransformsTapes ((tm.onWords mark).extendTapes e)
      (fun _ ws => ws (e (Fin.natAdd (k + 1) 0)) = x ∧
        ∀ j ≠ Fin.natAdd (k + 1) 0, ws (e j) = [])
      (fun _ ws ws' em => ws' = Function.update ws (e ((Fin.last k).castAdd 2)) y ∧ em = [])
      (t + y.length + 6) (s + 2 * x.length + 2 * y.length + 3 * k + 18 + (K - (k + 1 + 2))) := by
  refine ((h.onWords mark).extendTapes e).imp (fun _ ws ⟨hx, hb⟩ => ?_)
    (fun _ ws ws' _ _ ⟨⟨hv, hy⟩, hx⟩ => ⟨?_, hy⟩) le_rfl le_rfl
  · funext j
    by_cases hj : j = Fin.natAdd (k + 1) 0
    · subst hj
      simp [hx]
    · rw [Function.update_of_ne hj]
      exact hb j hj
  · funext l
    by_cases hl : l ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hl
      have : ws' (e j) = Function.update (fun j => ws (e j)) ((Fin.last k).castAdd 2) y j :=
        congrFun hv j
      rw [this]
      by_cases hj : j = (Fin.last k).castAdd 2
      · subst hj
        simp
      · rw [Function.update_of_ne hj, Function.update_of_ne (e.injective.ne hj)]
    · rw [hx l hl, Function.update_of_ne fun h => hl ⟨_, h.symm⟩]

/-! ### Runs of the phases -/

/-- A specification on the words, read on configurations of the stack-loop machine with every head
on the first cell of its word. -/
lemma runs_of_spec {S : Type*} {M : MultiTapeTM (kk + 6) Bool S}
    {P : (input : List Bool) → (Fin (kk + 6) → List Bool) → Prop}
    {Q : (input : List Bool) → (Fin (kk + 6) → List Bool) → (Fin (kk + 6) → List Bool) →
      List Bool → Prop} {t s : ℕ} (h : TransformsTapes M P Q t s)
    {c f r p st c' f' r' p' st' : List Bool} {oc os : ℤ} {e out out' : List Bool}
    (hP : P input (tapeWords c f r p st))
    (hQ : ∀ ws e', Q input (tapeWords c f r p st) ws e' →
      ws = tapeWords c' f' r' p' st' ∧ e' = e) (hout : out' = out ++ e) :
    RunsBetween M (cfgS input c f r p st oc os 0 0 out)
      (cfgS input c' f' r' p' st' oc os 0 0 out') t s := by
  obtain ⟨ws, e', hQ', hrun⟩ := RunsBetween.of_transformsTapes h hP (tapeOffs oc os) out
  obtain ⟨rfl, rfl⟩ := hQ ws e' hQ'
  subst hout
  exact hrun

/-- A run of a machine on embedded tapes. -/
lemma runs_lift {m : ℕ} {S : Type*} {tm : MultiTapeTM m Bool S} (e : Fin m ↪ Fin (kk + 6))
    {c c' : Cfg (kk + 6) Bool Unit input} {d₀ d : Cfg m Bool Unit input} {t s : ℕ}
    (hd₀ : viewCfg e c = d₀) (h : RunsBetween tm d₀ d t s)
    (hc : embed e d c.workTapes c.workTapePos = c') :
    RunsBetween (tm.extendTapes e) c c' t (s + (kk + 6 - m)) := by
  subst hd₀ hc
  exact h.extendTapes e

lemma update_tapeWords (c f r p st : List Bool) (j : Fin 6) (x : List Bool) :
    Function.update (tapeWords (kk := kk) c f r p st) (nm j) x =
      Fin.append (fun _ => []) (Function.update ![[], c, f, r, p, st] j x) :=
  (Fin.append_update_right _ _ _ _).symm

/-- The machine clearing the named tape `j`. -/
noncomputable def clearM (j : Fin 6) :=
  (clearWork Bool).extendTapes (tapeEmb (nm (kk := kk) j))

lemma runs_clearC (c f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (clearM (kk := kk) 1) (cfgS input c f r p st oc os 0 0 out)
      (cfgS input [] f r p st oc os 0 0 out) (3 * (c.length + 1)) (c.length + 1 + (kk + 6)) := by
  refine runs_of_spec (e := []) (transformsTapes_clearWork_tapeEmb (Symbol := Bool) (nm 1) c)
    (by simp) (by
      rintro _ _ ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [update_tapeWords]
      unfold tapeWords
      congr 1
      funext i
      fin_cases i <;> rfl) (List.append_nil out).symm

lemma runs_clearF (c f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (clearM (kk := kk) 2) (cfgS input c f r p st oc os 0 0 out)
      (cfgS input c [] r p st oc os 0 0 out) (3 * (f.length + 1)) (f.length + 1 + (kk + 6)) := by
  refine runs_of_spec (e := []) (transformsTapes_clearWork_tapeEmb (Symbol := Bool) (nm 2) f)
    (by simp) (by
      rintro _ _ ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [update_tapeWords]
      unfold tapeWords
      congr 1
      funext i
      fin_cases i <;> rfl) (List.append_nil out).symm

lemma runs_clearR (c f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (clearM (kk := kk) 3) (cfgS input c f r p st oc os 0 0 out)
      (cfgS input c f [] p st oc os 0 0 out) (3 * (r.length + 1)) (r.length + 1 + (kk + 6)) := by
  refine runs_of_spec (e := []) (transformsTapes_clearWork_tapeEmb (Symbol := Bool) (nm 3) r)
    (by simp) (by
      rintro _ _ ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [update_tapeWords]
      unfold tapeWords
      congr 1
      funext i
      fin_cases i <;> rfl) (List.append_nil out).symm

/-- Copying the round word to the blank current-value tape. -/
noncomputable def copyM := copyWord (copyEmb (kk := kk)) true

lemma runs_copy (f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (copyM (kk := kk)) (cfgS input [] f r p st oc os 0 0 out)
      (cfgS input r f r p st oc os 0 0 out) (3 * r.length + 10)
      (4 * r.length + (kk + 6) + 15) := by
  refine runs_of_spec (e := []) (transformsTapes_copyWord (copyEmb (kk := kk)) true r)
    (by simp [copyEmb]) (by
      rintro _ _ ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [show copyEmb (kk := kk) 0 = nm 1 from rfl, update_tapeWords]
      unfold tapeWords
      congr 1
      funext i
      fin_cases i <;> rfl) (List.append_nil out).symm

/-- Emitting the current value. -/
noncomputable def emitM := emitWord (emitEmb (kk := kk)) true

lemma runs_emit (c f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (emitM (kk := kk)) (cfgS input c f r p st oc os 0 0 out)
      (cfgS input c f r p st oc os 0 0 (out ++ c)) (2 * c.length + 8)
      (2 * c.length + (kk + 6) + 10) :=
  runs_of_spec (transformsTapes_emitWord (emitEmb (kk := kk)) true c) (by simp [emitEmb])
    (by rintro _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) rfl

/-- Running a machine with `kk` work tapes on words, from the named tape `v` to the named tape
`o`. -/
noncomputable def wordsM {S : Type*} (tm : MultiTapeTM kk Bool S) (v o : Fin 6) (hv : v.val ≠ 0)
    (ho : o.val ≠ 0) (hvo : v.val ≠ o.val) :=
  (tm.onWords true).extendTapes (owEmb v o hv ho hvo)

lemma tapeWords_owEmb_eq_nil {v o : Fin 6} {hv : v.val ≠ 0} {ho : o.val ≠ 0}
    {hvo : v.val ≠ o.val} {c f r p st : List Bool} (hnil : ![[], c, f, r, p, st] o = [])
    (j : Fin (kk + 1 + 2)) (hj : j ≠ Fin.natAdd (kk + 1) 0) :
    tapeWords c f r p st (owEmb v o hv ho hvo j) = [] := by
  induction j using Fin.addCases with
  | left j =>
    induction j using Fin.lastCases with
    | last => simpa using hnil
    | cast i => simp
  | right j =>
    fin_cases j
    · exact absurd rfl hj
    · simp

/-- The halting test: from the current value to the halting flag. -/
lemma runs_halt {S : Type*} {tm : MultiTapeTM kk Bool S} {c y : List Bool} {t s' : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace c y t s') (r p st : List Bool) (oc os : ℤ)
    (out : List Bool) :
    RunsBetween (wordsM tm 1 2 (by decide) (by decide) (by decide))
      (cfgS input c [] r p st oc os 0 0 out) (cfgS input c y r p st oc os 0 0 out)
      (t + y.length + 6) (s' + 2 * c.length + 2 * y.length + 3 * kk + 18 + 3) := by
  have := runs_of_spec (input := input) (e := []) (oc := oc) (os := os) (out := out) (out' := out)
    (transformsTapes_onWords_embed h true (owEmb (kk := kk) 1 2 (by decide) (by decide)
      (by decide))) (c := c) (f := []) (r := r) (p := p) (st := st) (c' := c) (f' := y)
    (r' := r) (p' := p) (st' := st)
    ⟨by simp, tapeWords_owEmb_eq_nil (by rfl)⟩ (by
      rintro _ _ ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [owEmb_out, update_tapeWords]
      unfold tapeWords
      congr 1
      funext i
      fin_cases i <;> rfl) (List.append_nil out).symm
  simpa [wordsM, show kk + 6 - (kk + 1 + 2) = 3 by omega] using this

/-- A round machine, from the current value to the pushed frames. -/
lemma runs_push {S : Type*} {tm : MultiTapeTM kk Bool S} {c y : List Bool} {t s' : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace c y t s') (f r st : List Bool) (oc os : ℤ)
    (out : List Bool) :
    RunsBetween (wordsM tm 1 4 (by decide) (by decide) (by decide))
      (cfgS input c f r [] st oc os 0 0 out) (cfgS input c f r y st oc os 0 0 out)
      (t + y.length + 6) (s' + 2 * c.length + 2 * y.length + 3 * kk + 18 + 3) := by
  have := runs_of_spec (input := input) (e := []) (oc := oc) (os := os) (out := out) (out' := out)
    (transformsTapes_onWords_embed h true (owEmb (kk := kk) 1 4 (by decide) (by decide)
      (by decide))) (c := c) (f := f) (r := r) (p := []) (st := st) (c' := c) (f' := f)
    (r' := r) (p' := y) (st' := st)
    ⟨by simp, tapeWords_owEmb_eq_nil (by rfl)⟩ (by
      rintro _ _ ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [owEmb_out, update_tapeWords]
      unfold tapeWords
      congr 1
      funext i
      fin_cases i <;> rfl) (List.append_nil out).symm
  simpa [wordsM, show kk + 6 - (kk + 1 + 2) = 3 by omega] using this

/-- A round machine, from the current value to the round word. -/
lemma runs_next {S : Type*} {tm : MultiTapeTM kk Bool S} {c y : List Bool} {t s' : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace c y t s') (f p st : List Bool) (oc os : ℤ)
    (out : List Bool) :
    RunsBetween (wordsM tm 1 3 (by decide) (by decide) (by decide))
      (cfgS input c f [] p st oc os 0 0 out) (cfgS input c f y p st oc os 0 0 out)
      (t + y.length + 6) (s' + 2 * c.length + 2 * y.length + 3 * kk + 18 + 3) := by
  have := runs_of_spec (input := input) (e := []) (oc := oc) (os := os) (out := out) (out' := out)
    (transformsTapes_onWords_embed h true (owEmb (kk := kk) 1 3 (by decide) (by decide)
      (by decide))) (c := c) (f := f) (r := []) (p := p) (st := st) (c' := c) (f' := f)
    (r' := y) (p' := p) (st' := st)
    ⟨by simp, tapeWords_owEmb_eq_nil (by rfl)⟩ (by
      rintro _ _ ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [owEmb_out, update_tapeWords]
      unfold tapeWords
      congr 1
      funext i
      fin_cases i <;> rfl) (List.append_nil out).symm
  simpa [wordsM, show kk + 6 - (kk + 1 + 2) = 3 by omega] using this

/-- The initialization: the machine reads the input and writes its output to the current-value
tape. -/
noncomputable def initM {S : Type*} (tm : MultiTapeTM kk Bool S) :=
  tm.outputToWord.extendTapes (initEmb (kk := kk))

lemma runs_init {S : Type*} {tm : MultiTapeTM kk Bool S} {y : List Bool} {t s' : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input y t s') (out : List Bool) :
    RunsBetween (initM tm) (cfgS input [] [] [] [] [] 0 0 0 0 out)
      (cfgS input y [] [] [] [] 0 0 0 0 out)
      (t + y.length + 2) (s' + 2 * y.length + kk + 4 + 5) := by
  have := runs_of_spec (input := input) (e := []) (oc := 0) (os := 0) (out := out) (out' := out)
    (h.outputToWord_extendTapes (initEmb (kk := kk))) (c := []) (f := []) (r := []) (p := [])
    (st := []) (c' := y) (f' := []) (r' := []) (p' := []) (st' := [])
    ⟨rfl, fun j => by
      induction j using Fin.lastCases with
      | last => simp
      | cast i => simp⟩ (by
      rintro _ _ ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [initEmb_last, update_tapeWords]
      unfold tapeWords
      congr 1
      funext i
      fin_cases i <;> rfl) (List.append_nil out).symm
  simpa [initM, show kk + 6 - (kk + 1) = 5 by omega] using this

/-! ### Native phases -/

lemma append_apply_eq {α : Type*} {z : α} {u v : Fin 6 → α} {l : Fin (kk + 6)}
    (h : ∀ j, l = nm j → u j = v j) :
    Fin.append (fun _ : Fin kk => z) u l = Fin.append (fun _ : Fin kk => z) v l := by
  induction l using Fin.addCases with
  | left i => simp only [Fin.append_left]
  | right j => simp only [Fin.append_right]; exact h j rfl

/-- A two-tape machine on the named tapes `a` and `b`. -/
lemma runs_pair {S : Type*} {tm : MultiTapeTM 2 Bool S} (a b : Fin 6) (hab : a ≠ b)
    {w w' : Fin 6 → List Bool} {o o' h h' : Fin 6 → ℤ} {t s : ℕ} {out : List Bool}
    (hrun : RunsBetween tm (tapesCfg input ![w a, w b] ![o a, o b] ![h a, h b] out)
      (tapesCfg input ![w' a, w' b] ![o' a, o' b] ![h' a, h' b] out) t s)
    (hw : ∀ j, j ≠ a → j ≠ b → w' j = w j ∧ o' j = o j ∧ h' j = h j) :
    RunsBetween (tm.extendTapes (pairEmb (kk := kk) a b hab))
      (tapesCfg input (Fin.append (fun _ => []) w) (Fin.append (fun _ => 0) o)
        (Fin.append (fun _ => 0) h) out)
      (tapesCfg input (Fin.append (fun _ => []) w') (Fin.append (fun _ => 0) o')
        (Fin.append (fun _ => 0) h') out) t (s + (kk + 6 - 2)) := by
  refine runs_lift _ ?_ hrun (embed_tapesCfg _ (fun j => ?_) fun l hl => ?_)
  · rw [viewCfg_tapesCfg]
    congr 1 <;> funext j <;> fin_cases j <;> simp [pairEmb]
  · fin_cases j <;> simp [pairEmb]
  · have hne : ∀ j, l = nm j → j ≠ a ∧ j ≠ b := by
      rintro j rfl
      exact ⟨fun h => hl ⟨0, by subst h; rfl⟩, fun h => hl ⟨1, by subst h; rfl⟩⟩
    exact ⟨append_apply_eq fun j hj => (hw j (hne j hj).1 (hne j hj).2).1,
      append_apply_eq fun j hj => (hw j (hne j hj).1 (hne j hj).2).2.1,
      append_apply_eq fun j hj => (hw j (hne j hj).1 (hne j hj).2).2.2⟩

/-- A one-tape machine on the named tape `a`. -/
lemma runs_one {S : Type*} {tm : MultiTapeTM 1 Bool S} (a : Fin 6)
    {w w' : Fin 6 → List Bool} {o o' h h' : Fin 6 → ℤ} {t s : ℕ} {out : List Bool}
    (hrun : RunsBetween tm (tapesCfg input (fun _ => w a) (fun _ => o a) (fun _ => h a) out)
      (tapesCfg input (fun _ => w' a) (fun _ => o' a) (fun _ => h' a) out) t s)
    (hw : ∀ j, j ≠ a → w' j = w j ∧ o' j = o j ∧ h' j = h j) :
    RunsBetween (tm.extendTapes (tapeEmb (nm (kk := kk) a)))
      (tapesCfg input (Fin.append (fun _ => []) w) (Fin.append (fun _ => 0) o)
        (Fin.append (fun _ => 0) h) out)
      (tapesCfg input (Fin.append (fun _ => []) w') (Fin.append (fun _ => 0) o')
        (Fin.append (fun _ => 0) h') out) t (s + (kk + 6 - 1)) := by
  refine runs_lift _ ?_ hrun (embed_tapesCfg _ (fun j => ?_) fun l hl => ?_)
  · rw [viewCfg_tapesCfg]
    simp only [tapeEmb_apply, nm, Fin.append_right]
  · simp only [tapeEmb_apply, nm, Fin.append_right, and_self]
  · have hne : ∀ j, l = nm j → j ≠ a := by
      rintro j rfl h
      exact hl ⟨0, by subst h; rfl⟩
    exact ⟨append_apply_eq fun j hj => (hw j (hne j hj)).1,
      append_apply_eq fun j hj => (hw j (hne j hj)).2.1,
      append_apply_eq fun j hj => (hw j (hne j hj)).2.2⟩

/-- Popping the stack to the round word. -/
noncomputable def popM := popFrame.extendTapes (pairEmb (kk := kk) 5 3 (by decide))

lemma runs_pop_nil (c f p : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (popM (kk := kk)) (cfgS input c f [] p [] oc os 0 0 out)
      (cfgS input c f [false] p [] oc os 1 0 out) 1 (2 * (1 + 1) + (kk + 6 - 2)) :=
  runs_pair 5 3 _ (by simpa using runsBetween_popFrame_nil (input := input) os 0 out)
    (fun j h5 h3 => by fin_cases j <;> simp_all)

lemma runs_pop_frame (c f p u rest : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (popM (kk := kk)) (cfgS input c f [] p (frame u ++ rest) oc os 0 0 out)
      (cfgS input c f (frame (true :: u)) p rest oc (os + (frame u).length)
        (frame (true :: u)).length 0 out) (2 * u.length + 3)
      (2 * (2 * u.length + 3 + 1) + (kk + 6 - 2)) :=
  runs_pair 5 3 _ (by simpa using runsBetween_popFrame_frame (input := input) u rest os 0 out)
    (fun j h5 h3 => by fin_cases j <;> simp_all)

/-- Moving the round word to the front of the current value. -/
noncomputable def backRC := (copyBack Bool).extendTapes (pairEmb (kk := kk) 3 1 (by decide))

lemma runs_backRC (c f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (backRC (kk := kk)) (cfgS input c f r p st oc os r.length 0 out)
      (cfgS input (r ++ c) f [] p st (oc - r.length) os 0 0 out) (r.length + 2)
      (2 * (r.length + 2 + 1) + (kk + 6 - 2)) :=
  runs_pair 3 1 _ (by simpa using runsBetween_copyBack (input := input) r c 0 oc out)
    (fun j h3 h1 => by fin_cases j <;> simp_all)

/-- Moving the pushed frames to the front of the stack. -/
noncomputable def backPS := (copyBack Bool).extendTapes (pairEmb (kk := kk) 4 5 (by decide))

lemma runs_backPS (c f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (backPS (kk := kk)) (cfgS input c f r p st oc os 0 p.length out)
      (cfgS input c f r [] (p ++ st) oc (os - p.length) 0 0 out) (p.length + 2)
      (2 * (p.length + 2 + 1) + (kk + 6 - 2)) :=
  runs_pair 4 5 _ (by simpa using runsBetween_copyBack (input := input) p st 0 os out)
    (fun j h4 h5 => by fin_cases j <;> simp_all)

/-- Erasing the popped frame at the front of the current value. -/
noncomputable def eraseM := eraseFrame.extendTapes (tapeEmb (nm (kk := kk) 1))

lemma runs_erase (u rest f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (eraseM (kk := kk)) (cfgS input (frame u ++ rest) f r p st oc os 0 0 out)
      (cfgS input rest f r p st (oc + (frame u).length) os 0 0 out) (2 * u.length + 1)
      (1 * (2 * u.length + 1 + 1) + (kk + 6 - 1)) :=
  runs_one 1 (by simpa using runsBetween_eraseFrame (input := input) u rest oc out)
    (fun j h1 => by fin_cases j <;> simp_all)

/-- Moving the head of the pushed frames to their end. -/
noncomputable def seekM := (seekEnd Bool).extendTapes (tapeEmb (nm (kk := kk) 4))

lemma runs_seek (c f r p st : List Bool) (oc os : ℤ) (out : List Bool) :
    RunsBetween (seekM (kk := kk)) (cfgS input c f r p st oc os 0 0 out)
      (cfgS input c f r p st oc os 0 p.length out) (p.length + 1)
      (1 * (p.length + 1 + 1) + (kk + 6 - 1)) :=
  runs_one 4 (by simpa using runsBetween_seekEnd (input := input) p 0 out)
    (fun j h4 => by fin_cases j <;> simp_all)

end Turing.MultiTapeTM.StackLoopKernel
