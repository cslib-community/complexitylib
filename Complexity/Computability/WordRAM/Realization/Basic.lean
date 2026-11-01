/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Controller
public import Complexity.Computability.WordRAM.MapOp
public import Complexity.DataStructure.Memory.Spec

/-!
# Graded realization of memory-oracle clients

`Realization.Realizes` certifies one uniform native emitter for an existing `Memory.Prog`
family. Arguments and results have explicit faithful finite-register encodings. Its memory
abstraction is the entire memory function together with one frontier register; scratch consists
only of fresh registers. The entry predicate and local-work charge are visible parameters.

The charged currency adds certified local computation and control work to `Memory.charge`.
In particular, a query-free loop cannot acquire a constant instruction bound merely because its
memory history is empty. The emitter, scratch size and exchange constant precede every runtime
argument, word width and initial memory. `Refines` is a semantic projection of this certificate,
not a competing execution semantics or a second client language.

## Main definitions

* `memoryState`: the functional whole-memory/frontier abstraction.
* `memoryCost`: the memory-level charge of the client's actual deterministic history.
* `Realizes`: uniform native realization with a combined instruction currency and register frame.

## Main results

* `Realizes.exists_refines`: forget the fresh-register frame to the existing `Refines` API.

The realization certificate and its grading are original infrastructure. The memory interface,
free-monad interpreter and native execution rules are reused unchanged.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {B : Basis} {r k l : ℕ} {δ α : Type}

/-- The abstraction retains every cell, including unallocated and inaccessible cells. -/
def memoryState (frontier : Fin r) (x : Data r) : Memory.State :=
  ⟨x.mem, x.regs frontier⟩

/-- Bounded native data supplies the memory invariant, independently of any scratch layout. -/
theorem wellFormed_memoryState {w : ℕ} {frontier : Fin r} {x : Data r} (hx : x.Bounded w) :
    Memory.WellFormed w (memoryState frontier x) :=
  ⟨hx.1 frontier, hx.2⟩

/-- The memory-level instruction currency uses the existing deterministic interpreter. Its
transition function does not depend on the word width; admissibility is a separate premise. -/
def memoryCost (p : Memory.Prog α) (s : Memory.State) : ℕ :=
  (Memory.spec 0).totalCost Memory.charge s ((Memory.spec 0).clientHistory s p)

/-- Uniformity of the mathematical interpreter across widths: only `valid` depends on `w`. -/
theorem runClient_width (w : ℕ) (p : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).runClient s p = (Memory.spec 0).runClient s p := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o cont ih =>
    exact congrArg (fun t : α × Memory.State × List Memory.Op => (t.1, t.2.1, o :: t.2.2))
      (ih (Memory.step s o).2 (Memory.step s o).1)

/-- A semantic return issues no memory operation. Its native glue is charged separately. -/
@[simp] theorem memoryCost_pure (a : α) (s : Memory.State) :
    memoryCost (.pure a) s = 0 := rfl

/-- Memory charges add at the actual intermediate state; the local bind charge is separate. -/
theorem memoryCost_bind {β : Type} (p : Memory.Prog α) (q : α → Memory.Prog β)
    (s : Memory.State) :
    memoryCost (p.bind q) s = memoryCost p s +
      memoryCost (q ((Memory.spec 0).clientResult s p)) ((Memory.spec 0).clientState s p) := by
  unfold memoryCost
  simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_bind]
  rw [StateTransitionSpec.totalCost_append, StateTransitionSpec.run_runClient]

/-- Existing `Memory.Prog` clients have a fixed emitter and a combined charge. The explicit
`safe` predicate may contain glue domains and fit envelopes; it is never existentially chosen.
The existing valid-history premise supplies memory admissibility. The extra one pays uniform
entry/exit overhead, so the native bound is `C * charged + C` with one fixed `C`.

Input registers may alias each other. The injective scratch bank is disjoint from all inputs and
the frontier; its first `l` registers hold the faithfully encoded result. Every other register,
except the frontier, is framed. All native registers and memory are bounded at entry, separately
from the functional representation. -/
def Realizes (B : Basis) (p : δ → Memory.Prog α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (work : δ → Memory.State → ℕ) : Prop :=
  ∃ n C : ℕ,
    ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
        (Fin (l + n + 1) → Fin r) → Code B r,
      ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
        (tmp : Fin (l + n + 1) → Fin r),
        Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
        (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
        ¬(emit frontier src tmp).ReadsWidth ∧
        ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
          safe w d (memoryState frontier x) →
          (Memory.spec w).ValidHistory (memoryState frontier x)
            ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
          ∃ y, ExecWithin w (emit frontier src tmp) x y
              (C * (memoryCost (p d) (memoryState frontier x) +
                work d (memoryState frontier x) + 1)) ∧
            memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (p d) ∧
            (∀ i : Fin l, y.regs (tmp (Fin.castAdd (n + 1) i)) =
              output ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i) ∧
            ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i

namespace Realizes

variable {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
  {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
  {work : δ → Memory.State → ℕ}

/-- Strengthen the visible entry domain or enlarge the local-work charge. The entry word and
memory bounds may discharge fit conditions; no executable code or domain is hidden by this rule. -/
theorem consequence {safe' : ℕ → δ → Memory.State → Prop} {work' : δ → Memory.State → ℕ}
    (h : Realizes B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → safe w d s)
    (hwork : ∀ d s, work d s ≤ work' d s) : Realizes B p input output safe' work' := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, emit, ?_⟩
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨hnw, ?_⟩
  intro w d x hx hin hsafe' hv
  have hwords (i : Fin k) : Fits w (input d i) := congrFun hin i ▸ hx.1 (src i)
  obtain ⟨y, hy, hm, hout, hframe⟩ :=
    hrun w d x hx hin (hsafe w d _ hwords (wellFormed_memoryState hx) hsafe') hv
  exact ⟨y, hy.mono (Nat.mul_le_mul_left C (by have := hwork d (memoryState frontier x); omega)),
    hm, hout, hframe⟩

/-- Existing defined-evaluation basis simulation preserves the complete realization certificate. -/
theorem mapSimulates {B' : Basis} (h : Realizes B p input output safe work)
    (φ : B.Simulates B') : Realizes B' p input output safe work := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, fun frontier src tmp => (emit frontier src tmp).mapSimulates φ, ?_⟩
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨fun h => hnw (Code.readsWidth_of_mapSimulates φ h), ?_⟩
  intro w d x hx hin hsafe hv
  obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x hx hin hsafe hv
  exact ⟨y, hy.mapSimulates φ, hm, hout, hframe⟩

/-- The same witness derives the existing semantic `Refines` judgment. The intermediate
representation is fixed by the functional memory abstraction and argument/result registers. -/
theorem exists_refines (h : Realizes B p input output safe work) :
    ∃ n C : ℕ,
      ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
          (Fin (l + n + 1) → Fin r) → Code B r,
        ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
          (tmp : Fin (l + n + 1) → Fin r),
          Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
          (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
          ∀ (w : ℕ) (d : δ),
          Refines (D := Memory.spec w) w
            (fun s x => s = memoryState frontier x ∧ x.Bounded w ∧ x.regs ∘ src = input d ∧
              safe w d s ∧ (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)))
            (p d)
            (fun a s y => memoryState frontier y = s ∧
              ∀ i : Fin l, y.regs (tmp (Fin.castAdd (n + 1) i)) = output a i)
            (fun s _ => C * (memoryCost (p d) s + work d s + 1)) (emit frontier src tmp) := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, emit, fun frontier src tmp hi hd hf hs w d => ?_⟩
  apply Refines.ofFn
  rintro s x ⟨rfl, hx, hin, hsafe, hv⟩
  obtain ⟨y, hy, hm, hout, _⟩ := (he frontier src tmp hi hd hf hs).2 w d x hx hin hsafe hv
  exact ⟨hv, y, hy, hm, hout⟩

end Realizes

end Cslib.WordRAM.Realization
