/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Structured
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange

/-!
# Explicit-budget certificates for register-word glue

This module certifies finite, memory-independent glue in the existing `WordRAM.Code` language.
An emitter takes possibly repeated input registers and a disjoint fresh scratch bank. Its code
and instruction budget are chosen before the input values and word width. This follows the
emit-and-frame pattern of `Multiword.Circuit`, specialized to physical words; it does not use
that compiler's standard-basis wide-arithmetic semantics for exact-basis operations.

The admissible-input predicate and one envelope for executed values remain explicit. In
particular, increasing the width does not justify exact subtraction below zero or a zero
divisor. Selection runs only its chosen alternative. Width reads, memory instructions, loops
and random sampling are excluded. This is the word-glue component of realization, not a
compiler for memory clients or algorithms. The certificate asserts successful execution on its
stated domain; it does not assert a converse about executions outside that domain.

Inputs are already in the supplied registers. Their installation, scratch reservation and a
final halt are not charged here; the surrounding realization must charge them. Constants,
copies, ALU instructions and branch overhead inside the emitted code are charged normally.
The interface and closure results are original; the underlying model is `WordRAM.Structured`.

## Main definitions

* `Code.IsGlue`: the memory-independent, width-independent finite fragment of existing code.
* `GlueComputes`: a framed scalar computation with an explicit uniform instruction budget.
* `GlueComputable`: the same contract with only the instruction budget existentially hidden.
* `GlueComputes.Witness`: retain specified scalar scratch and code under that same contract.

## Main results

* `GlueComputes.proj`, `GlueComputes.const`: register projections and constants.
* `GlueComputes.binary`, `GlueComputes.comp_many`, `GlueComputes.select`: compositional emission.
* `GlueComputes.realize`: instantiate the emitter with a concrete finite register layout.
* `GlueComputes.mono`: explicit weakening of the value envelope and instruction budget.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {k r : ℕ}

/-- The register-only finite fragment of `Code`. Conditions may select a branch, but no loop,
memory access, random choice or word-width read is permitted. This is a predicate on the
existing language, not a second program syntax. -/
@[expose] def Code.IsGlue : Code B r → Prop
  | .op (.const _ _) | .op (.copy _ _) => True
  | .op (.alu f _ _) => ¬B.ReadsWidth f
  | .seq a b | .branch _ a b => a.IsGlue ∧ b.IsGlue
  | _ => False

/-- Register glue does not read the word width, so existing execution monotonicity applies. -/
theorem Code.IsGlue.not_readsWidth {c : Code B r} (h : c.IsGlue) : ¬c.ReadsWidth := by
  induction c with
  | op o => cases o <;> simp_all [Code.IsGlue, Code.ReadsWidth, Op.ReadsWidth]
  | seq a b ha hb | branch cond a b ha hb =>
    exact fun hc => hc.elim (ha h.1) (hb h.2)
  | loop | rand => exact h.elim

/-- The uniform native contract shared by existential and retained scalar certificates.
Inputs may alias; only the scratch bank is fresh and injective. No whole-state boundedness
premise is added to the scalar interface. -/
@[expose] def GlueComputes.Spec (B : Basis) (P : (Fin k → ℕ) → Prop)
    (f bound : (Fin k → ℕ) → ℕ) (time n : ℕ)
    (emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (n + 1) → Fin r) → Code B r) : Prop :=
  ∀ {r : ℕ} (src : Fin k → Fin r) (tmp : Fin (n + 1) → Fin r),
    Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
    (emit src tmp).IsGlue ∧
    ∀ (w : ℕ) (x : Data r), P (x.regs ∘ src) → Fits w (bound (x.regs ∘ src)) →
      ∃ y, ExecWithin w (emit src tmp) x y time ∧
        y.regs (tmp 0) = f (x.regs ∘ src) ∧ y.mem = x.mem ∧
        ∀ i, (∀ j, tmp j ≠ i) → y.regs i = x.regs i

/-- A scalar register function has a fixed emitter and instruction budget. `bound` is one
top-level value envelope, and `P` is the fixed admissibility predicate. The scratch bank is
fresh and injectively placed; input registers may repeat. Output is in scratch slot zero,
memory is unchanged, and registers outside scratch retain their initial contents. Neither the
emitter nor the budget may depend on run-time values or the word width. -/
@[expose] def GlueComputes (B : Basis) (P : (Fin k → ℕ) → Prop)
    (f bound : (Fin k → ℕ) → ℕ)
    (time : ℕ) : Prop :=
  (∀ v, P v → f v ≤ bound v) ∧
  ∃ n, ∃ emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (n + 1) → Fin r) → Code B r,
    GlueComputes.Spec B P f bound time n emit

/-- Syntax-directed automation hides only the uniform budget and emitter witness. The basis,
admissibility predicate, scalar function and value envelope remain visible parameters. -/
@[expose, fun_prop]
def GlueComputable (B : Basis) (f : (Fin k → ℕ) → ℕ) (P : (Fin k → ℕ) → Prop)
    (bound : (Fin k → ℕ) → ℕ) : Prop :=
  ∃ time, GlueComputes B P f bound time

namespace GlueComputes

variable {P : (Fin k → ℕ) → Prop} {f bound bound' : (Fin k → ℕ) → ℕ} {time time' : ℕ}

/-- A specified scalar emitter with the same contract as `GlueComputes`. The envelope,
scratch and code are retained as data before every runtime value, width and register layout. -/
structure Witness (B : Basis) (P : (Fin k → ℕ) → Prop)
    (f bound : (Fin k → ℕ) → ℕ) (time : ℕ) where
  /-- Auxiliary slots, in addition to the scalar result slot. -/
  scratchSize : ℕ
  /-- The uniform scalar emitter. -/
  code : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (scratchSize + 1) → Fin r) → Code B r
  /-- The original visible value envelope. -/
  bound_spec : ∀ v, P v → f v ≤ bound v
  /-- The original native execution and memory/register-frame contract. -/
  code_spec : Spec B P f bound time scratchSize code

/-- Forget the specified code and scratch without changing the scalar contract. -/
theorem Witness.toGlueComputes (h : Witness B P f bound time) : GlueComputes B P f bound time :=
  ⟨h.bound_spec, h.scratchSize, h.code, h.code_spec⟩

/-- Existential-only fallback. The selected scratch and code need not equal those of any
particular derivation; use a supplied `Witness` when their identities matter. -/
noncomputable def Witness.ofGlueComputes (h : GlueComputes B P f bound time) :
    Witness B P f bound time where
  scratchSize := h.2.choose
  code := h.2.choose_spec.choose
  bound_spec := h.1
  code_spec := h.2.choose_spec.choose_spec

/-- A checked explicit budget supplies the automation facade. -/
theorem computable (h : GlueComputes B P f bound time) : GlueComputable B f P bound :=
  ⟨time, h⟩

/-- A canonical finite register layout puts inputs first and fresh scratch after them. The
same code and register count work for every valid input and width, and every initial memory
is framed. The budget excludes a final halt; a later flat-program export must charge it. -/
theorem realize (h : GlueComputes B P f bound time) :
    ∃ n, ∃ code : Code B (k + (n + 1)), code.IsGlue ∧
      ∀ (w : ℕ) (v : Fin k → ℕ) (mem : ℕ → ℕ), P v → Fits w (bound v) →
        ∃ y, ExecWithin w code ⟨Fin.addCases v (fun _ => 0), mem⟩ y time ∧
          y.regs (Fin.natAdd k 0) = f v ∧ y.mem = mem ∧
          ∀ i, y.regs (Fin.castAdd (n + 1) i) = v i := by
  obtain ⟨_, n, emit, he⟩ := h
  have hd (i : Fin k) (j : Fin (n + 1)) : Fin.castAdd (n + 1) i ≠ Fin.natAdd k j := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  obtain ⟨hg, hrun⟩ := he (Fin.castAdd (n + 1)) (Fin.natAdd k) (Fin.natAdd_injective (n + 1) k) hd
  refine ⟨n, emit (Fin.castAdd (n + 1)) (Fin.natAdd k), hg, ?_⟩
  intro w v mem hv hw
  let x : Data (k + (n + 1)) := ⟨Fin.addCases v (fun _ => 0), mem⟩
  have hxs : x.regs ∘ Fin.castAdd (n + 1) = v := by
    funext i
    change Fin.addCases v (fun _ : Fin (n + 1) => 0) (Fin.castAdd (n + 1) i) = v i
    exact Fin.addCases_left i
  obtain ⟨y, hy, hyo, hym, hyf⟩ := hrun w x (hxs.symm ▸ hv) (hxs.symm ▸ hw)
  refine ⟨y, hy, hxs ▸ hyo, hym, ?_⟩
  intro i
  exact (hyf _ (fun j => (hd i j).symm)).trans (congrFun hxs i)

/-- Weaken the envelope and instruction budget explicitly, outside syntax-directed search. -/
theorem mono (h : GlueComputes B P f bound time)
    (hb : ∀ v, P v → bound v ≤ bound' v) (ht : time ≤ time') :
    GlueComputes B P f bound' time' := by
  obtain ⟨hf, n, emit, he⟩ := h
  refine ⟨fun v hv => (hf v hv).trans (hb v hv), n, emit, ?_⟩
  intro r src tmp hi hd
  obtain ⟨hg, hrun⟩ := he src tmp hi hd
  refine ⟨hg, ?_⟩
  intro w x hx hw
  obtain ⟨y, hy, ho, hm, hf⟩ := hrun w x hx (hw.of_le (hb _ hx))
  exact ⟨y, hy.mono ht, ho, hm, hf⟩

/-- Copy one input register. Its bound is checked against the common visible envelope. -/
@[expose] def Witness.proj (i : Fin k) (hb : ∀ v, P v → v i ≤ bound v) :
    Witness B P (fun v => v i) bound 1 := by
  refine ⟨0, fun src tmp => .op (.copy (tmp 0) (src i)), hb, ?_⟩
  intro r src tmp hi hd
  refine ⟨trivial, ?_⟩
  intro w x hx hw
  refine ⟨x.set (tmp 0) (x.regs (src i)), ExecWithin.copy, ?_, rfl, ?_⟩
  · simp [Data.set]
  · intro j hj
    exact Function.update_of_ne (hj 0).symm _ _

/-- Erase the retained projection certificate. -/
theorem proj (i : Fin k) (hb : ∀ v, P v → v i ≤ bound v) :
    GlueComputes B P (fun v => v i) bound 1 :=
  (Witness.proj i hb).toGlueComputes

/-- Write a fitting constant. -/
@[expose] def Witness.const (z : ℕ) (hb : ∀ v, P v → z ≤ bound v) :
    Witness B P (fun _ => z) bound 1 := by
  refine ⟨0, fun _ tmp => .op (.const (tmp 0) z), hb, ?_⟩
  intro r src tmp hi hd
  refine ⟨trivial, ?_⟩
  intro w x hx hw
  refine ⟨x.set (tmp 0) z, ExecWithin.const (hw.of_le (hb _ hx)), ?_, rfl, ?_⟩
  · simp [Data.set]
  · intro j hj
    exact Function.update_of_ne (hj 0).symm _ _

/-- Erase the retained constant certificate. -/
theorem const (z : ℕ) (hb : ∀ v, P v → z ≤ bound v) :
    GlueComputes B P (fun _ => z) bound 1 :=
  (Witness.const z hb).toGlueComputes

private def left {a b : ℕ} (j : Fin (a + 1)) : Fin (a + b + 3) :=
  ⟨j.val + 1, by omega⟩

private def right {a b : ℕ} (j : Fin (b + 1)) : Fin (a + b + 3) :=
  ⟨j.val + a + 2, by omega⟩

private theorem left_injective {a b : ℕ} : Function.Injective (@left a b) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [left] at this
  omega

private theorem right_injective {a b : ℕ} : Function.Injective (@right a b) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [right] at this
  omega

private theorem left_ne_right {a b : ℕ} (i : Fin (a + 1)) (j : Fin (b + 1)) :
    left i ≠ right j := by
  intro h
  have := congrArg Fin.val h
  simp only [left, right] at this
  omega

/-- Apply a basis operation to two computed words. The operation may repeat or ignore either
word in its argument vector. Its interpretation and domain are checked explicitly, at every
width; no totalization of a partial basis operation is used. Intermediate executions share the
same envelope, and their instruction costs are added without bound search. -/
def Witness.binary {f g h : (Fin k → ℕ) → ℕ} {tf tg : ℕ}
    (hf : Witness B P f bound tf) (hg : Witness B P g bound tg)
    (op : B.Op) (args : Fin (B.Arity op) → Fin 2) (hop : ¬B.ReadsWidth op)
    (heval : ∀ v, P v → ∀ w, B.interp w op (fun i => ![f v, g v] (args i)) = some (h v))
    (hb : ∀ v, P v → h v ≤ bound v) :
    Witness B P h bound (tf + tg + 1) := by
  obtain ⟨a, ea, _, ha⟩ := hf
  obtain ⟨b, eb, _, hg⟩ := hg
  let emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (a + b + 2 + 1) → Fin r) → Code B r :=
    fun src tmp => .seq (ea src (tmp ∘ left))
      (.seq (eb src (tmp ∘ right))
        (.op (.alu op (tmp 0) (fun i => if args i = 0 then tmp (left 0) else tmp (right 0)))))
  refine ⟨a + b + 2, emit, hb, ?_⟩
  intro r src tmp hi hd
  obtain ⟨hga, hra⟩ := ha src (tmp ∘ left) (hi.comp left_injective)
    (fun i j => hd i (left j))
  obtain ⟨hgb, hrb⟩ := hg src (tmp ∘ right) (hi.comp right_injective)
    (fun i j => hd i (right j))
  refine ⟨⟨hga, hgb, hop⟩, ?_⟩
  intro w x hx hw
  obtain ⟨y, hy, hyo, hym, hyf⟩ := hra w x hx hw
  have hys : y.regs ∘ src = x.regs ∘ src := by
    funext i
    exact hyf (src i) (fun j => (hd i (left j)).symm)
  obtain ⟨z, hz, hzo, hzm, hzf⟩ := hrb w y (hys.symm ▸ hx) (hys.symm ▸ hw)
  have hleft : z.regs (tmp (left 0)) = f (x.regs ∘ src) :=
    (hzf _ (fun j h => left_ne_right (0 : Fin (a + 1)) j (hi h).symm)).trans hyo
  have hright : z.regs (tmp (right 0)) = g (x.regs ∘ src) := by
    change z.regs (tmp (right 0)) = g (y.regs ∘ src) at hzo
    exact hys ▸ hzo
  have hargs : (z.regs ∘ (fun i => if args i = 0 then tmp (left 0) else tmp (right 0))) =
      (fun i => ![f (x.regs ∘ src), g (x.regs ∘ src)] (args i)) := by
    funext i
    by_cases h : args i = 0
    · simp [h, hleft]
    · have h' : args i = 1 := by apply Fin.ext; have := (args i).isLt; omega
      simp [h', hright]
  have he : ExecWithin w (.op (.alu op (tmp 0)
      (fun i => if args i = 0 then tmp (left 0) else tmp (right 0)))) z
      (z.set (tmp 0) (h (x.regs ∘ src))) 1 := by
    apply ExecWithin.alu _ (hw.of_le (hb _ hx))
    rw [hargs]
    exact heval _ hx w
  refine ⟨z.set (tmp 0) (h (x.regs ∘ src)), hy.seq (hz.seq he), ?_, hzm.trans hym, ?_⟩
  · simp [Data.set]
  · intro i hne
    change Function.update z.regs (tmp 0) (h (x.regs ∘ src)) i = x.regs i
    rw [Function.update_of_ne (hne 0).symm]
    exact (hzf i (fun j => hne (right j))).trans (hyf i (fun j => hne (left j)))

/-- Binary composition retains the two disjoint operand banks and one result slot. -/
@[simp] theorem Witness.binary_scratchSize {f g h : (Fin k → ℕ) → ℕ} {tf tg : ℕ}
    (hf : Witness B P f bound tf) (hg : Witness B P g bound tg)
    (op : B.Op) (args : Fin (B.Arity op) → Fin 2) (hop : ¬B.ReadsWidth op)
    (heval : ∀ v, P v → ∀ w, B.interp w op (fun i => ![f v, g v] (args i)) = some (h v))
    (hb : ∀ v, P v → h v ≤ bound v) :
    (hf.binary hg op args hop heval hb).scratchSize = hf.scratchSize + hg.scratchSize + 2 := by
  cases hf
  cases hg
  rfl

/-- Compose existential certificates using their choice-selected scalar witnesses. For
specified scratch and code, use `Witness.binary` directly. -/
theorem binary {f g h : (Fin k → ℕ) → ℕ} {tf tg : ℕ}
    (hf : GlueComputes B P f bound tf) (hg : GlueComputes B P g bound tg)
    (op : B.Op) (args : Fin (B.Arity op) → Fin 2) (hop : ¬B.ReadsWidth op)
    (heval : ∀ v, P v → ∀ w, B.interp w op (fun i => ![f v, g v] (args i)) = some (h v))
    (hb : ∀ v, P v → h v ≤ bound v) :
    GlueComputes B P h bound (tf + tg + 1) :=
  (Witness.binary (Witness.ofGlueComputes hf) (Witness.ofGlueComputes hg)
    op args hop heval hb).toGlueComputes

/-- Substitute a register map, including a map with repeated inputs. The emitter accepts
arbitrary input layouts, so this substitution needs no staging copies or injectivity premise. -/
theorem reindex {m : ℕ} {Q : (Fin m → ℕ) → Prop} {b : (Fin m → ℕ) → ℕ}
    (h : GlueComputes B P f bound time) (ρ : Fin k → Fin m)
    (hP : ∀ v, Q v → P (v ∘ ρ)) (hb : ∀ v, Q v → bound (v ∘ ρ) ≤ b v) :
    GlueComputes B Q (fun v => f (v ∘ ρ)) b time := by
  obtain ⟨hf, n, emit, he⟩ := h
  refine ⟨fun v hv => (hf _ (hP v hv)).trans (hb v hv), n,
    fun src tmp => emit (src ∘ ρ) tmp, ?_⟩
  intro r src tmp hi hd
  obtain ⟨hg, hrun⟩ := he (src ∘ ρ) tmp hi (fun i j => hd (ρ i) j)
  refine ⟨hg, ?_⟩
  intro w x hx hw
  exact hrun w x (hP _ hx) (hw.of_le (hb _ hx))

/-- Substitute any finite vector of computed arguments into a routine. All component emitters,
scratch banks and budgets are fixed before runtime inputs or widths. The forest runs in index
order, preserving inputs and earlier results, and then runs the outer routine in its own bank.
The one common envelope covers all components and dominates the outer envelope. -/
theorem comp_many {m : ℕ} {Q : (Fin m → ℕ) → Prop} {h b : (Fin m → ℕ) → ℕ}
    {g : (Fin k → ℕ) → Fin m → ℕ} {tf : ℕ} {t : Fin m → ℕ}
    (hf : GlueComputes B Q h b tf)
    (hg : ∀ i, GlueComputes B P (fun v => g v i) bound (t i))
    (hQ : ∀ v, P v → Q (g v)) (hb : ∀ v, P v → b (g v) ≤ bound v) :
    GlueComputes B P (fun v => h (g v)) bound ((List.ofFn t).sum + tf) := by
  classical
  obtain ⟨hfo, a, ef, hef⟩ := hf
  choose ns es hes using fun i => (hg i).2
  let S := (i : Fin m) × Fin (ns i + 1)
  let N := Fintype.card S
  let idx : S ≃ Fin N := Fintype.equivFin S
  let inner (i : Fin m) (j : Fin (ns i + 1)) : Fin (N + a + 1) :=
    ⟨a + 1 + (idx ⟨i, j⟩).val, by have := (idx ⟨i, j⟩).isLt; omega⟩
  let outer (j : Fin (a + 1)) : Fin (N + a + 1) := ⟨j.val, by omega⟩
  have hindex {i j : Fin m} {p : Fin (ns i + 1)} {q : Fin (ns j + 1)}
      (he : inner i p = inner j q) : (⟨i, p⟩ : S) = ⟨j, q⟩ := by
    apply idx.injective
    apply Fin.ext
    have := congrArg Fin.val he
    dsimp only [inner] at this
    omega
  have hinj (i : Fin m) : Function.Injective (inner i) := by
    intro p q he
    exact Fin.ext (congrArg (fun s : S => s.2.val) (hindex he))
  have hsep (i j : Fin m) (p : Fin (ns i + 1)) (q : Fin (ns j + 1))
      (he : inner i p = inner j q) : i = j := congrArg Sigma.fst (hindex he)
  have hout : Function.Injective outer := by
    intro p q he
    apply Fin.ext
    have hv := congrArg (fun j : Fin (N + a + 1) => j.val) he
    exact hv
  have hio (i : Fin m) (p : Fin (ns i + 1)) (q : Fin (a + 1)) :
      inner i p ≠ outer q := by
    intro he
    have := congrArg Fin.val he
    dsimp only [inner, outer] at this
    omega
  let emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (N + a + 1) → Fin r) → Code B r :=
    fun src tmp => (List.finRange m).foldr
      (fun i rest => .seq (es i src (tmp ∘ inner i)) rest)
      (ef (fun i => tmp (inner i 0)) (tmp ∘ outer))
  refine ⟨fun v hv => (hfo _ (hQ v hv)).trans (hb v hv), N + a, emit, ?_⟩
  intro r src tmp hi hd
  have hc (i : Fin m) := hes i src (tmp ∘ inner i) (hi.comp (hinj i))
    (fun j q => hd j (inner i q))
  obtain ⟨hfg, hfrun⟩ := hef (fun i => tmp (inner i 0)) (tmp ∘ outer)
    (hi.comp hout) (fun i q he => hio i 0 q (hi he))
  refine ⟨?_, ?_⟩
  · dsimp only [emit]
    generalize List.finRange m = L
    induction L with
    | nil => exact hfg
    | cons i L ih => exact ⟨(hc i).1, ih⟩
  intro w x hx hw
  let v := x.regs ∘ src
  have run (L : List (Fin m)) (z : Data r) (hz : z.regs ∘ src = v)
      (hvals : ∀ i, i ∉ L → z.regs (tmp (inner i 0)) = g v i) :
      ∃ y, ExecWithin w
        (L.foldr (fun i rest => .seq (es i src (tmp ∘ inner i)) rest)
          (ef (fun i => tmp (inner i 0)) (tmp ∘ outer))) z y ((L.map t).sum + tf) ∧
        y.regs (tmp 0) = h (g v) ∧ y.mem = z.mem ∧
        ∀ j, (∀ q, tmp q ≠ j) → y.regs j = z.regs j := by
    induction L generalizing z with
    | nil =>
      have hargs : z.regs ∘ (fun i => tmp (inner i 0)) = g v := by
        funext i
        exact hvals i (by simp)
      obtain ⟨y, hy, ho, hm, hf⟩ := hfrun w z (hargs.symm ▸ hQ v hx)
        (hargs.symm ▸ hw.of_le (hb v hx))
      refine ⟨y, ?_, ?_, hm, ?_⟩
      · simpa only [List.foldr_nil, List.map_nil, List.sum_nil, Nat.zero_add] using hy
      · change y.regs (tmp 0) = h (z.regs ∘ (fun i => tmp (inner i 0))) at ho
        exact hargs ▸ ho
      · intro j hj
        exact hf j (fun q => hj (outer q))
    | cons i L ih =>
      obtain ⟨z', he, ho, hm, hframe⟩ := (hc i).2 w z (hz.symm ▸ hx) (hz.symm ▸ hw)
      have hz' : z'.regs ∘ src = v := by
        funext j
        exact (hframe (src j) (fun q => (hd j (inner i q)).symm)).trans (congrFun hz j)
      have hvals' (j : Fin m) (hj : j ∉ L) : z'.regs (tmp (inner j 0)) = g v j := by
        by_cases hji : j = i
        · subst j
          change z'.regs (tmp (inner i 0)) = g (z.regs ∘ src) i at ho
          exact hz ▸ ho
        · have hreg := hframe (tmp (inner j 0))
            (fun q heq => hji (hsep i j q 0 (hi heq)).symm)
          exact hreg.trans (hvals j (by simpa only [List.mem_cons, not_or] using And.intro hji hj))
      obtain ⟨y, hy, hyo, hym, hyf⟩ := ih z' hz' hvals'
      refine ⟨y, ?_, hyo, hym.trans hm, ?_⟩
      · simpa only [List.foldr_cons, List.map_cons, List.sum_cons, Nat.add_assoc] using he.seq hy
      · intro j hj
        exact (hyf j hj).trans (hframe j (fun q => hj (inner i q)))
  obtain ⟨y, hy, ho, hm, hf⟩ := run (List.finRange m) x rfl
    (fun i hi => False.elim (hi (by simp)))
  refine ⟨y, ?_, ho, hm, hf⟩
  simpa only [List.ofFn_eq_map] using hy

/-- Compose two scalar computations, passing the first result as the second computation's
single input. Each stage keeps its own explicit domain and envelope; the caller proves the
domain implication and envelope domination once. -/
theorem comp {g b : (Fin 1 → ℕ) → ℕ} {Q : (Fin 1 → ℕ) → Prop} {tf tg : ℕ}
    (hf : GlueComputes B P f bound tf) (hg : GlueComputes B Q g b tg)
    (hQ : ∀ v, P v → Q (fun _ => f v))
    (hb : ∀ v, P v → b (fun _ => f v) ≤ bound v) :
    GlueComputes B P (fun v => g (fun _ => f v)) bound (tf + tg + 1) := by
  have hc := hg.comp_many (g := fun v _ => f v) (t := fun _ : Fin 1 => tf)
    (fun _ => hf) hQ hb
  have hc' : GlueComputes B P (fun v => g (fun _ => f v)) bound (tf + tg) := by
    simpa [List.ofFn_succ] using hc
  exact hc'.mono (fun _ _ => le_rfl) (by omega)

/-- Select between two computations by an existing register condition. Only the selected
branch must satisfy its domain; the inactive branch may fault if executed. -/
theorem select (cond : Cond k) {f g : (Fin k → ℕ) → ℕ} {tf tg : ℕ}
    (hf : GlueComputes B (fun v => P v ∧ cond.Holds ⟨v, fun _ => 0⟩) f bound tf)
    (hg : GlueComputes B (fun v => P v ∧ ¬cond.Holds ⟨v, fun _ => 0⟩) g bound tg) :
    GlueComputes B P (fun v => if cond.Holds ⟨v, fun _ => 0⟩ then f v else g v)
      bound (max tf tg + 3) := by
  obtain ⟨hfo, a, ea, ha⟩ := hf
  obtain ⟨hgo, b, eb, hg⟩ := hg
  let emit : ∀ {r : ℕ}, (Fin k → Fin r) → (Fin (a + b + 2 + 1) → Fin r) → Code B r :=
    fun src tmp => .branch (cond.rename src)
      (.seq (ea src (tmp ∘ left)) (.op (.copy (tmp 0) (tmp (left 0)))))
      (.seq (eb src (tmp ∘ right)) (.op (.copy (tmp 0) (tmp (right 0)))))
  refine ⟨?_, a + b + 2, emit, ?_⟩
  · intro v hv
    dsimp only
    split
    · exact hfo v ⟨hv, by assumption⟩
    · exact hgo v ⟨hv, by assumption⟩
  intro r src tmp hi hd
  obtain ⟨hga, hra⟩ := ha src (tmp ∘ left) (hi.comp left_injective)
    (fun i j => hd i (left j))
  obtain ⟨hgb, hrb⟩ := hg src (tmp ∘ right) (hi.comp right_injective)
    (fun i j => hd i (right j))
  refine ⟨⟨⟨hga, trivial⟩, hgb, trivial⟩, ?_⟩
  intro w x hx hw
  have hc : (cond.rename src).Holds x ↔ cond.Holds ⟨x.regs ∘ src, fun _ => 0⟩ := by
    cases cond <;> rfl
  by_cases h : cond.Holds ⟨x.regs ∘ src, fun _ => 0⟩
  · obtain ⟨y, hy, hyo, hym, hyf⟩ := hra w x ⟨hx, h⟩ hw
    refine ⟨y.set (tmp 0) (y.regs (tmp (left 0))),
      ((hy.seq ExecWithin.copy).branch_pos (hc.mpr h)).mono (by omega), ?_, hym, ?_⟩
    · simpa [Data.set, h] using hyo
    · intro i hne
      change Function.update y.regs (tmp 0) _ i = x.regs i
      rw [Function.update_of_ne (hne 0).symm]
      exact hyf i (fun j => hne (left j))
  · obtain ⟨y, hy, hyo, hym, hyf⟩ := hrb w x ⟨hx, h⟩ hw
    refine ⟨y.set (tmp 0) (y.regs (tmp (right 0))),
      ((hy.seq ExecWithin.copy).branch_neg (fun h' => h (hc.mp h'))).mono (by omega),
      ?_, hym, ?_⟩
    · simpa [Data.set, h] using hyo
    · intro i hne
      change Function.update y.regs (tmp 0) _ i = x.regs i
      rw [Function.update_of_ne (hne 0).symm]
      exact hyf i (fun j => hne (right j))

/-- Standard binary operations use the basis's documented total natural-number semantics. -/
theorem bin_standard {f g : (Fin k → ℕ) → ℕ} {tf tg : ℕ}
    (hf : GlueComputes .standard P f bound tf) (hg : GlueComputes .standard P g bound tg)
    (op : BinOp) (hb : ∀ v, P v → op.eval (f v) (g v) ≤ bound v) :
    GlueComputes .standard P (fun v => op.eval (f v) (g v)) bound (tf + tg + 1) :=
  binary hf hg (.bin op) id (by simp) (fun _ _ _ => rfl) hb

/-- Retain exact binary code and scratch. Definedness of the partial operation on the fixed
domain is still required separately from output fit. -/
@[expose] def Witness.binExact {f g : (Fin k → ℕ) → ℕ} {tf tg : ℕ}
    (hf : Witness .exact P f bound tf) (hg : Witness .exact P g bound tg)
    (op : BinOp) (hv : ∀ v, P v → op.evalExact (f v) (g v) = some (op.eval (f v) (g v)))
    (hb : ∀ v, P v → op.eval (f v) (g v) ≤ bound v) :
    Witness .exact P (fun v => op.eval (f v) (g v)) bound (tf + tg + 1) :=
  Witness.binary hf hg (.bin op) id (by simp) (fun v hp _ => hv v hp) hb

/-- Exact binary witnesses retain the original operand-bank accounting without requiring
clients to unfold the basis-dependent emitter. -/
@[simp] theorem Witness.binExact_scratchSize {f g : (Fin k → ℕ) → ℕ} {tf tg : ℕ}
    (hf : Witness .exact P f bound tf) (hg : Witness .exact P g bound tg)
    (op : BinOp) (hv : ∀ v, P v → op.evalExact (f v) (g v) = some (op.eval (f v) (g v)))
    (hb : ∀ v, P v → op.eval (f v) (g v) ≤ bound v) :
    (hf.binExact hg op hv hb).scratchSize = hf.scratchSize + hg.scratchSize + 2 := by
  cases hf
  cases hg
  rfl

/-- Exact binary operations require their interpretation to be defined on the fixed domain.
Output fit alone cannot discharge underflow or a zero divisor. -/
theorem bin_exact {f g : (Fin k → ℕ) → ℕ} {tf tg : ℕ}
    (hf : GlueComputes .exact P f bound tf) (hg : GlueComputes .exact P g bound tg)
    (op : BinOp) (hv : ∀ v, P v → op.evalExact (f v) (g v) = some (op.eval (f v) (g v)))
    (hb : ∀ v, P v → op.eval (f v) (g v) ≤ bound v) :
    GlueComputes .exact P (fun v => op.eval (f v) (g v)) bound (tf + tg + 1) :=
  binary hf hg (.bin op) id (by simp) (fun v hp _ => hv v hp) hb

end GlueComputes

end Cslib.WordRAM
