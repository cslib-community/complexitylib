/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.BoundedExec
public import CslibFrontier.Computability.WordRAM.Controller
public import CslibFrontier.Computability.WordRAM.MapOp
public import CslibFrontier.DataStructure.Memory.Spec

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
* `Realizes.SpecWith`, `Realizes.With`: judgment-parametric realization contract and existential
  certificate over an arbitrary execution predicate `exec`.
* `Realizes.Spec`, `Realizes`: uniform native realization over `ExecWithin`.
* `Realizes.SpecBounded`, `RealizesBounded`: frontier-bounded instance over `ExecBounded w
  (y.regs frontier)` for lifting to the Resizable Word RAM.

## Main results

* `Realizes.SpecWith.weaken`, `Realizes.With.weaken`: transport a realization certificate along
  an execution-judgment implication.
* `Realizes.SpecWith.consequence`, `Realizes.With.consequence`, `Realizes.Spec.consequence`,
  `Realizes.consequence`: strengthen the domain or enlarge work.
* `Realizes.exists_refines`: forget the fresh-register frame to the existing `Refines` API.
* `RealizesBounded.toRealizes`: erase the frontier-access bound back to `Realizes`.

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

/-- The result of the memory interpreter is independent of the admissibility width. -/
theorem clientResult_width (w : ℕ) (p : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).clientResult s p = (Memory.spec 0).clientResult s p :=
  congrArg Prod.fst (runClient_width w p s)

/-- The final memory/frontier state is independent of the admissibility width. -/
theorem clientState_width (w : ℕ) (p : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).clientState s p = (Memory.spec 0).clientState s p :=
  congrArg (fun t => t.2.1) (runClient_width w p s)

/-- Admissible sequential histories split at the actual returned value and memory state. -/
theorem validHistory_bind (w : ℕ) {α β : Type} (p : Memory.Prog α)
    (q : α → Memory.Prog β) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q)) ↔
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
      (Memory.spec w).ValidHistory ((Memory.spec w).clientState s p)
        ((Memory.spec w).clientHistory ((Memory.spec w).clientState s p)
          (q ((Memory.spec w).clientResult s p))) := by
  simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_bind]
  rw [StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient]

/-- Faithfully append a returned word vector to the original input environment.
This is static register wiring; it performs no native computation or copies. -/
def appendWords (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ)) :
    δ × α ↪ (Fin (k + l) → ℕ) :=
  (input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding

/-- A semantic return issues no memory operation. Its native glue is charged separately. -/
@[simp, client_simps] theorem memoryCost_pure (a : α) (s : Memory.State) :
    memoryCost (pure a) s = 0 := rfl

/-- Memory charges add at the actual intermediate state; the local bind charge is separate. -/
theorem memoryCost_bind {β : Type} (p : Memory.Prog α) (q : α → Memory.Prog β)
    (s : Memory.State) :
    memoryCost (p.bind q) s = memoryCost p s +
      memoryCost (q ((Memory.spec 0).clientResult s p)) ((Memory.spec 0).clientState s p) := by
  unfold memoryCost
  simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_bind]
  rw [StateTransitionSpec.totalCost_append, StateTransitionSpec.run_runClient]

/-- `memoryCost_bind` stated with `>>=`, the form `do` blocks elaborate to. -/
@[client_simps] theorem memoryCost_bind' {β : Type} (p : Memory.Prog α) (q : α → Memory.Prog β)
    (s : Memory.State) :
    memoryCost (p >>= q) s = memoryCost p s +
      memoryCost (q ((Memory.spec 0).clientResult s p)) ((Memory.spec 0).clientState s p) :=
  memoryCost_bind p q s

/-- Parameterless-bound `ExecWithin` adapter for `Realizes.SpecWith` and `Realizes.With`. -/
abbrev Realizes.execWithin (B : Basis) {r : ℕ} (w : ℕ) (_ : Fin r) (c : Code B r)
    (x y : Data r) (T : ℕ) : Prop :=
  ExecWithin w c x y T

/-- Frontier-bounded `ExecBounded` adapter for `Realizes.SpecWith` and `Realizes.With`. -/
abbrev Realizes.execBounded (B : Basis) {r : ℕ} (w : ℕ) (frontier : Fin r) (c : Code B r)
    (x y : Data r) (T : ℕ) : Prop :=
  ExecBounded w (y.regs frontier) c x y T

/-- Judgment-parametric execution contract for specified scratch, exchange factor and emitter.
Both `Realizes.Spec` (over `ExecWithin`) and `Realizes.SpecBounded` (over
`ExecBounded w (y.regs frontier)`) are instances of this contract. -/
def Realizes.SpecWith (B : Basis)
    (exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop)
    (p : δ → Memory.Prog α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (work : δ → Memory.State → ℕ) (n C : ℕ)
    (emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r) : Prop :=
  ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
    (tmp : Fin (l + n + 1) → Fin r),
    Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
    (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
    ¬(emit frontier src tmp).ReadsWidth ∧
    ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
      safe w d (memoryState frontier x) →
      (Memory.spec w).ValidHistory (memoryState frontier x)
        ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
      ∃ y, exec w frontier (emit frontier src tmp) x y
          (C * (memoryCost (p d) (memoryState frontier x) +
            work d (memoryState frontier x) + 1)) ∧
        memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (p d) ∧
        (∀ i : Fin l, y.regs (tmp (Fin.castAdd (n + 1) i)) =
          output ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i) ∧
        ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i

/-- The execution contract for specified scratch, exchange factor and emitter. Both the
existential judgment and data witnesses use this same contract. -/
def Realizes.Spec (B : Basis) (p : δ → Memory.Prog α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (work : δ → Memory.State → ℕ) (n C : ℕ)
    (emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r) : Prop :=
  Realizes.SpecWith B (Realizes.execWithin B) p input output safe work n C emit

/-- Judgment-parametric uniform realization for an existing `Memory.Prog` family over `exec`. -/
def Realizes.With (B : Basis)
    (exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop)
    (p : δ → Memory.Prog α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (work : δ → Memory.State → ℕ) : Prop :=
  ∃ n C : ℕ,
    ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
        (Fin (l + n + 1) → Fin r) → Code B r,
      Realizes.SpecWith B exec p input output safe work n C emit

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
  Realizes.With B (Realizes.execWithin B) p input output safe work

namespace Realizes

variable {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
  {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
  {work : δ → Memory.State → ℕ}

/-- General domain, work-bound, exchange-factor and execution-judgment transport for `SpecWith`.
Entry word fits, well-formed memory and admissible client history are available both to discharge
the entry predicate and to transport the resulting execution judgment. -/
theorem SpecWith.consequence_of
    {exec₁ exec₂ : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {safe' : ℕ → δ → Memory.State → Prop} {work' : δ → Memory.State → ℕ} {n C C' : ℕ}
    {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : SpecWith B exec₁ p input output safe work n C emit)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s)
    (htransport : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r}
      {d : δ},
      (∀ i, Fits w (input d i)) → Memory.WellFormed w (memoryState frontier x) →
      (Memory.spec w).ValidHistory (memoryState frontier x)
        ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
      safe' w d (memoryState frontier x) →
      exec₁ w frontier c x y (C * (memoryCost (p d) (memoryState frontier x) +
        work d (memoryState frontier x) + 1)) →
      exec₂ w frontier c x y (C' * (memoryCost (p d) (memoryState frontier x) +
        work' d (memoryState frontier x) + 1))) :
    SpecWith B exec₂ p input output safe' work' n C' emit := by
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨hnw, fun w d x hx hin hsafe' hv => ?_⟩
  have hwords (i : Fin k) : Fits w (input d i) := congrFun hin i ▸ hx.1 (src i)
  have hmem := wellFormed_memoryState (frontier := frontier) hx
  obtain ⟨y, hy, hm, hout, hframe⟩ :=
    hrun w d x hx hin (hsafe w d _ hwords hmem hv hsafe') hv
  exact ⟨y, htransport hwords hmem hv hsafe' hy, hm, hout, hframe⟩

/-- Transport a `SpecWith` contract along an implication between execution judgments. -/
theorem SpecWith.weaken
    {exec₁ exec₂ : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {n C : ℕ} {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : SpecWith B exec₁ p input output safe work n C emit)
    (hweaken : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T : ℕ},
      exec₁ w frontier c x y T → exec₂ w frontier c x y T) :
    SpecWith B exec₂ p input output safe work n C emit :=
  he.consequence_of (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ hy => hweaken hy)

/-- Transport an existential `With` certificate along an implication between execution judgments. -/
theorem With.weaken
    {exec₁ exec₂ : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    (h : With B exec₁ p input output safe work)
    (hweaken : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T : ℕ},
      exec₁ w frontier c x y T → exec₂ w frontier c x y T) :
    With B exec₂ p input output safe work :=
  let ⟨n, C, emit, he⟩ := h
  ⟨n, C, emit, he.weaken hweaken⟩

/-- Strengthen the entry domain of a `SpecWith` contract using the client's valid history. -/
theorem SpecWith.consequence_valid
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {safe' : ℕ → δ → Memory.State → Prop} {n C : ℕ}
    {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : SpecWith B exec p input output safe work n C emit)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s) :
    SpecWith B exec p input output safe' work n C emit :=
  he.consequence_of hsafe (fun _ _ _ _ hy => hy)

/-- Strengthen the entry domain of a `With` certificate under the client's valid history. -/
theorem With.consequence_valid
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {safe' : ℕ → δ → Memory.State → Prop}
    (h : With B exec p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s) :
    With B exec p input output safe' work :=
  let ⟨n, C, emit, he⟩ := h
  ⟨n, C, emit, he.consequence_valid hsafe⟩

/-- Strengthen the visible entry domain or enlarge the local-work charge for `SpecWith`. -/
theorem SpecWith.consequence
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {safe' : ℕ → δ → Memory.State → Prop} {work' : δ → Memory.State → ℕ} {n C : ℕ}
    {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : SpecWith B exec p input output safe work n C emit)
    (hmono : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T₁ T₂ : ℕ},
      T₁ ≤ T₂ → exec w frontier c x y T₁ → exec w frontier c x y T₂)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → safe w d s)
    (hwork : ∀ d s, work d s ≤ work' d s) :
    SpecWith B exec p input output safe' work' n C emit :=
  he.consequence_of (fun w d s hwords hmem _ hs' => hsafe w d s hwords hmem hs')
    (fun {_ _ frontier _ x _ d} _ _ _ _ hy =>
      hmono (Nat.mul_le_mul_left C (by have := hwork d (memoryState frontier x); omega)) hy)

/-- Strengthen the visible entry domain or enlarge the local-work charge for `With`. -/
theorem With.consequence
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {safe' : ℕ → δ → Memory.State → Prop} {work' : δ → Memory.State → ℕ}
    (h : With B exec p input output safe work)
    (hmono : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T₁ T₂ : ℕ},
      T₁ ≤ T₂ → exec w frontier c x y T₁ → exec w frontier c x y T₂)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → safe w d s)
    (hwork : ∀ d s, work d s ≤ work' d s) :
    With B exec p input output safe' work' :=
  let ⟨n, C, emit, he⟩ := h
  ⟨n, C, emit, he.consequence hmono hsafe hwork⟩

/-- Transport a `SpecWith` contract along a basis simulation. -/
theorem SpecWith.mapSimulates {B' : Basis}
    {exec₁ : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {exec₂ : ∀ {r : ℕ}, ℕ → Fin r → Code B' r → Data r → Data r → ℕ → Prop}
    {n C : ℕ} {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : SpecWith B exec₁ p input output safe work n C emit) (φ : B.Simulates B')
    (hsim : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T : ℕ},
      exec₁ w frontier c x y T → exec₂ w frontier (c.mapSimulates φ) x y T) :
    SpecWith B' exec₂ p input output safe work n C
      (fun frontier src tmp => (emit frontier src tmp).mapSimulates φ) := by
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨fun h => hnw (Code.readsWidth_of_mapSimulates φ h), ?_⟩
  intro w d x hx hin hsafe hv
  obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x hx hin hsafe hv
  exact ⟨y, hsim hy, hm, hout, hframe⟩

/-- Transport a `With` certificate along a basis simulation. -/
theorem With.mapSimulates {B' : Basis}
    {exec₁ : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {exec₂ : ∀ {r : ℕ}, ℕ → Fin r → Code B' r → Data r → Data r → ℕ → Prop}
    (h : With B exec₁ p input output safe work) (φ : B.Simulates B')
    (hsim : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T : ℕ},
      exec₁ w frontier c x y T → exec₂ w frontier (c.mapSimulates φ) x y T) :
    With B' exec₂ p input output safe work :=
  let ⟨n, C, emit, he⟩ := h
  ⟨n, C, fun frontier src tmp => (emit frontier src tmp).mapSimulates φ, he.mapSimulates φ hsim⟩

/-- Strengthen the visible entry domain or enlarge the local-work charge for a specified
scratch size, exchange factor and emitter, all of which are unchanged. -/
theorem Spec.consequence {safe' : ℕ → δ → Memory.State → Prop}
    {work' : δ → Memory.State → ℕ} {n C : ℕ}
    {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : Spec B p input output safe work n C emit)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → safe w d s)
    (hwork : ∀ d s, work d s ≤ work' d s) : Spec B p input output safe' work' n C emit :=
  SpecWith.consequence he (fun hT h => h.mono hT) hsafe hwork

/-- Strengthen the visible entry domain or enlarge the local-work charge. The entry word and
memory bounds may discharge fit conditions; no executable code or domain is hidden by this rule. -/
theorem consequence {safe' : ℕ → δ → Memory.State → Prop} {work' : δ → Memory.State → ℕ}
    (h : Realizes B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → safe w d s)
    (hwork : ∀ d s, work d s ≤ work' d s) : Realizes B p input output safe' work' :=
  With.consequence h (fun hT h => h.mono hT) hsafe hwork

/-- Existing defined-evaluation basis simulation preserves the complete realization certificate. -/
theorem mapSimulates {B' : Basis} (h : Realizes B p input output safe work)
    (φ : B.Simulates B') : Realizes B' p input output safe work :=
  With.mapSimulates h φ (fun h => h.mapSimulates φ)

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

/-- Frontier-bounded execution contract strengthening `Realizes.Spec` with
`ExecBounded w (y.regs frontier)`. -/
def SpecBounded (B : Basis) (p : δ → Memory.Prog α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (work : δ → Memory.State → ℕ) (n C : ℕ)
    (emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r) : Prop :=
  SpecWith B (Realizes.execBounded B) p input output safe work n C emit

/-- Erase the frontier-access bound from `SpecBounded` back to `Spec`. -/
theorem SpecBounded.toSpec {n C : ℕ}
    {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : SpecBounded B p input output safe work n C emit) :
    Spec B p input output safe work n C emit :=
  SpecWith.weaken he fun h => h.toExecWithin

/-- Strengthen the visible entry domain or enlarge the local-work charge for `SpecBounded`. -/
theorem SpecBounded.consequence {safe' : ℕ → δ → Memory.State → Prop}
    {work' : δ → Memory.State → ℕ} {n C : ℕ}
    {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : SpecBounded B p input output safe work n C emit)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → safe w d s)
    (hwork : ∀ d s, work d s ≤ work' d s) :
    SpecBounded B p input output safe' work' n C emit :=
  SpecWith.consequence he (fun hT h => h.mono hT) hsafe hwork

end Realizes

/-- Uniform frontier-bounded realization of a `Memory.Prog` family, certifying that every native
`load` and `store` accesses an address strictly below `y.regs frontier`. -/
def RealizesBounded (B : Basis) (p : δ → Memory.Prog α)
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ))
    (safe : ℕ → δ → Memory.State → Prop) (work : δ → Memory.State → ℕ) : Prop :=
  Realizes.With B (Realizes.execBounded B) p input output safe work

namespace RealizesBounded

section CoreBinders

variable {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
  {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
  {work : δ → Memory.State → ℕ}

/-- Erase the frontier-access bound back to `Realizes`. -/
theorem toRealizes (h : RealizesBounded B p input output safe work) :
    Realizes B p input output safe work :=
  Realizes.With.weaken h fun h => h.toExecWithin

/-- Strengthen the visible entry domain or enlarge the local-work charge. -/
theorem consequence {safe' : ℕ → δ → Memory.State → Prop} {work' : δ → Memory.State → ℕ}
    (h : RealizesBounded B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → safe w d s)
    (hwork : ∀ d s, work d s ≤ work' d s) : RealizesBounded B p input output safe' work' :=
  Realizes.With.consequence h (fun hT h => h.mono hT) hsafe hwork

/-- Transport a frontier-bounded realization certificate along a basis simulation. -/
theorem mapSimulates {B' : Basis} (h : RealizesBounded B p input output safe work)
    (φ : B.Simulates B') : RealizesBounded B' p input output safe work :=
  Realizes.With.mapSimulates h φ fun h => h.mapSimulates φ

end CoreBinders

end RealizesBounded

end Cslib.WordRAM.Realization

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

section ReindexBinders

variable {B : Basis} {ε δ α : Type} {k m l : ℕ}

/-- Rewire a `SpecWith` emitter's inputs by a fixed index map. -/
theorem Realizes.SpecWith.reindex
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
    {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
    {work : δ → Memory.State → ℕ} {n C : ℕ}
    {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : Realizes.SpecWith B exec p input output safe work n C emit)
    (f : ε → δ) (env : ε ↪ (Fin m → ℕ)) (ix : Fin k → Fin m)
    (hw : ∀ e i, input (f e) i = env e (ix i)) :
    Realizes.SpecWith B exec (fun e => p (f e)) env output
      (fun w e s => safe w (f e) s) (fun e s => work (f e) s) n C
      (fun frontier src tmp => emit frontier (src ∘ ix) tmp) := by
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := he frontier (src ∘ ix) tmp hi
    (fun i j => hd (ix i) j) hf (fun i => hs (ix i))
  refine ⟨hnw, fun w e x hx hin hsafe hv => ?_⟩
  have hin' : x.regs ∘ (src ∘ ix) = input (f e) := by
    funext i
    exact (congrFun hin (ix i)).trans (hw e i).symm
  exact hrun w (f e) x hx hin' hsafe hv

/-- Pull a `Realizes.With` certificate back along a fixed register-index map. -/
theorem Realizes.With.reindex
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
    {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
    {work : δ → Memory.State → ℕ} (h : Realizes.With B exec p input output safe work)
    (f : ε → δ) (env : ε ↪ (Fin m → ℕ)) (ix : Fin k → Fin m)
    (hw : ∀ e i, input (f e) i = env e (ix i)) :
    Realizes.With B exec (fun e => p (f e)) env output
      (fun w e s => safe w (f e) s) (fun e s => work (f e) s) :=
  let ⟨n, C, emit, he⟩ := h
  ⟨n, C, fun frontier src tmp => emit frontier (src ∘ ix) tmp, he.reindex f env ix hw⟩

/-- Rewire a `SpecBounded` emitter's inputs by a fixed index map. -/
theorem Realizes.SpecBounded.reindex {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
    {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
    {work : δ → Memory.State → ℕ} {n C : ℕ}
    {emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code B r}
    (he : Realizes.SpecBounded B p input output safe work n C emit)
    (f : ε → δ) (env : ε ↪ (Fin m → ℕ)) (ix : Fin k → Fin m)
    (hw : ∀ e i, input (f e) i = env e (ix i)) :
    Realizes.SpecBounded B (fun e => p (f e)) env output
      (fun w e s => safe w (f e) s) (fun e s => work (f e) s) n C
      (fun frontier src tmp => emit frontier (src ∘ ix) tmp) :=
  Realizes.SpecWith.reindex he f env ix hw

/-- Pull a `RealizesBounded` certificate back along a fixed register-index map. -/
theorem RealizesBounded.reindex {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
    {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
    {work : δ → Memory.State → ℕ} (h : RealizesBounded B p input output safe work)
    (f : ε → δ) (env : ε ↪ (Fin m → ℕ)) (ix : Fin k → Fin m)
    (hw : ∀ e i, input (f e) i = env e (ix i)) :
    RealizesBounded B (fun e => p (f e)) env output
      (fun w e s => safe w (f e) s) (fun e s => work (f e) s) :=
  Realizes.With.reindex h f env ix hw

end ReindexBinders

section AbsorbBinders

variable {B : Basis} {δ α : Type} {k l : ℕ}
  {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work work' : δ → Memory.State → ℕ}

/-- Absorb local work dominated by a constant multiple of the memory charge plus another grading
on any monotonic `Realizes.With` judgment. -/
theorem Realizes.With.mono_mul
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    (h : Realizes.With B exec p input output safe work)
    (hmono : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T₁ T₂ : ℕ},
      T₁ ≤ T₂ → exec w frontier c x y T₁ → exec w frontier c x y T₂)
    (K : ℕ)
    (hwork : ∀ d s, work d s ≤ K * (memoryCost (p d) s + work' d s + 1)) :
    Realizes.With B exec p input output safe work' := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C * (K + 1), emit, he.consequence_of (fun _ _ _ _ _ _ h => h) ?_⟩
  intro _ _ frontier _ x _ d _ _ _ _ hy
  have hw := hwork d (memoryState frontier x)
  exact hmono (by rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left; nlinarith) hy

/-- Pointwise equal programs have the same `Realizes.With` certificates. -/
theorem Realizes.With.congr
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {p' : δ → Memory.Prog α}
    (h : Realizes.With B exec p input output safe work)
    (hp : ∀ d, p d = p' d) : Realizes.With B exec p' input output safe work :=
  funext hp ▸ h

/-- Absorb local work dominated by a constant multiple of the memory charge plus another grading. -/
theorem RealizesBounded.mono_mul (h : RealizesBounded B p input output safe work) (K : ℕ)
    (hwork : ∀ d s, work d s ≤ K * (memoryCost (p d) s + work' d s + 1)) :
    RealizesBounded B p input output safe work' :=
  Realizes.With.mono_mul h (fun hT h => h.mono hT) K hwork

/-- Pointwise equal programs have the same frontier-bounded certificates. -/
theorem RealizesBounded.congr {p' : δ → Memory.Prog α}
    (h : RealizesBounded B p input output safe work)
    (hp : ∀ d, p d = p' d) : RealizesBounded B p' input output safe work :=
  Realizes.With.congr h hp

/-- Strengthen the visible domain under the client's own valid history. -/
theorem RealizesBounded.consequence_valid {safe' : ℕ → δ → Memory.State → Prop}
    (h : RealizesBounded B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s) : RealizesBounded B p input output safe' work :=
  Realizes.With.consequence_valid h hsafe

end AbsorbBinders

end Cslib.WordRAM.Realization
