/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Loop

/-!
# Fixed-environment transport for bounded memory-client loops

Equal body programs at two fixed environments give equal bounded iterations. Pointwise equal
body-work charges and equivalent body domains likewise transport the iteration's work and safety
conditions along its actual reached memory states. These are semantic laws of the existing free
programs: they need no fit, history or resource assumptions.

## Main results

* `iterate_comap`: pull a loop body back along a map of its environment.
* `iterate_congr`: equal bodies at fixed environments give equal iterations.
* `iterationSafe_congr`: transport iteration domains between agreeing bodies and environments.
* `iterationWork_congr`: transport local work between agreeing bodies and environments.
* `validHistory_bind'`: factored valid-history rule across program binds under word-size
  zero state transitions.
* `iterate_spec`: bounded iteration invariant induction bounding safety, valid history,
  memory cost, and frame preservation.

The transport rules are original infrastructure over the existing memory-client loops.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {δ σ : Type}

/-- A loop may receive any function of its environment: it is the loop over the whole
environment whose body applies that function. -/
theorem iterate_comap {ε σ : Type} (g : ε → δ) (body : δ × σ → Memory.Prog σ) (e : ε) (n : ℕ)
    (a : σ) : iterate body (g e) n a = iterate (fun x : ε × σ => body (g x.1, x.2)) e n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact congrArg (fun k => (body (g e, a)).bind k) (funext ih)

/-- Equal body programs at fixed environments give equal bounded iterations, including their
complete memory histories. -/
theorem iterate_congr {δ' : Type}
    {body : δ × σ → Memory.Prog σ} {body' : δ' × σ → Memory.Prog σ}
    {d : δ} {d' : δ'} (hbody : ∀ a, body (d, a) = body' (d', a)) (n : ℕ) (a : σ) :
    iterate body d n a = iterate body' d' n a := by
  calc
    _ = iterate (fun x : Unit × σ => body (d, x.2)) () n a :=
      iterate_comap (fun _ : Unit => d) body () n a
    _ = iterate (fun x : Unit × σ => body' (d', x.2)) () n a :=
      congrArg (fun b : Unit × σ → Memory.Prog σ => iterate b () n a)
        (funext fun x => hbody x.2)
    _ = _ := (iterate_comap (fun _ : Unit => d') body' () n a).symm

/-- Iteration domains agree when the bodies and their domains agree at fixed environments. -/
theorem iterationSafe_congr {δ' : Type}
    {body : δ × σ → Memory.Prog σ} {body' : δ' × σ → Memory.Prog σ}
    {safe : ℕ → δ × σ → Memory.State → Prop} {safe' : ℕ → δ' × σ → Memory.State → Prop}
    {w : ℕ} {d : δ} {d' : δ'} (hbody : ∀ a, body (d, a) = body' (d', a))
    (hsafe : ∀ a s, safe w (d, a) s ↔ safe' w (d', a) s) (n : ℕ) (a : σ) (s : Memory.State) :
    iterationSafe body safe w d n a s ↔ iterationSafe body' safe' w d' n a s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih => simp only [iterationSafe, hsafe, ← hbody, ih]

/-- Transport safety along agreeing bodies and sub-domains at fixed environments. -/
theorem iterationSafe_imp {δ' σ : Type} {body' : δ' × σ → Memory.Prog σ}
    {safe' : ℕ → δ' × σ → Memory.State → Prop} {δ : Type}
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → δ × σ → Memory.State → Prop}
    {w : ℕ} {d' : δ'} {d : δ} {n : ℕ} {a : σ} {s : Memory.State}
    (h : iterationSafe body safe w d n a s)
    (hb : ∀ a, body' (d', a) = body (d, a))
    (hs : ∀ a s, safe w (d, a) s → safe' w (d', a) s) :
    iterationSafe body' safe' w d' n a s := by
  induction n generalizing a s with
  | zero => trivial
  | succ n ih => refine ⟨hs a s h.1, ?_⟩; rw [hb]; exact ih h.2

/-- The local work is invariant under agreeing bodies and body charges at their environments. -/
theorem iterationWork_congr {δ' : Type}
    {body : δ × σ → Memory.Prog σ} {body' : δ' × σ → Memory.Prog σ}
    {work : δ × σ → Memory.State → ℕ} {work' : δ' × σ → Memory.State → ℕ}
    {d : δ} {d' : δ'} (hbody : ∀ a, body (d, a) = body' (d', a))
    (hwork : ∀ a s, work (d, a) s = work' (d', a) s) (n : ℕ) (a : σ) (s : Memory.State) :
    iterationWork body work d n a s = iterationWork body' work' d' n a s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih => simp only [iterationWork, hwork, ← hbody, ih]

/-- Sequential validity decomposes across monadic bind in `Memory.spec w`. -/
theorem validHistory_bind' {α β : Type} (w : ℕ) (p : Memory.Prog α)
    (q : α → Memory.Prog β) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) ↔
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
      (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
        ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
          (q ((Memory.spec 0).clientResult s p))) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q)) ↔ _
  rw [validHistory_bind, clientResult_width, clientState_width]

/-- Bounded iteration invariant induction for `Memory.Prog`. -/
theorem iterate_spec {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → δ × σ → Memory.State → Prop) (w : ℕ) (d : δ) (B n : ℕ)
    (inv : ℕ → σ → Memory.State → Prop) (mod : ℕ → Prop)
    (hstep : ∀ k < n, ∀ a s, inv k a s → safe w (d, a) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a))) ∧
      memoryCost (body (d, a)) s ≤ B ∧
      let s' := (Memory.spec 0).clientState s (body (d, a))
      s'.frontier = s.frontier ∧ (∀ x, ¬mod x → s'.mem x = s.mem x) ∧
      inv (k + 1) ((Memory.spec 0).clientResult s (body (d, a))) s')
    (a₀ : σ) (s₀ : Memory.State) (h₀ : inv 0 a₀ s₀) :
    let prog := iterate body d n a₀; let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe body safe w d n a₀ s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ B * n ∧ s'.frontier = s₀.frontier ∧
    (∀ x, ¬mod x → s'.mem x = s₀.mem x) ∧ inv n ((Memory.spec 0).clientResult s₀ prog) s' := by
  induction n generalizing inv a₀ s₀ with
  | zero => exact ⟨trivial, trivial, Nat.zero_le _, rfl, fun _ _ => rfl, h₀⟩
  | succ n ih =>
    obtain ⟨hs₀, hv₀, hc₀, hfr₀, hmod₀, hinv₁⟩ := hstep 0 (Nat.succ_pos n) a₀ s₀ h₀
    set a₁ := (Memory.spec 0).clientResult s₀ (body (d, a₀))
    set s₁ := (Memory.spec 0).clientState s₀ (body (d, a₀))
    obtain ⟨hsn, hvn, hcn, hfrn, hmodn, hinvn⟩ :=
      ih (fun k => inv (k + 1)) (fun k hk => hstep (k + 1) (Nat.succ_lt_succ hk)) a₁ s₁ hinv₁
    refine ⟨⟨hs₀, by rw [clientResult_width, clientState_width]; exact hsn⟩, ?_, ?_, ?_,
      fun x hx => ?_, ?_⟩
    · rw [iterate, validHistory_bind']; exact ⟨hv₀, hvn⟩
    · rw [iterate, memoryCost_bind']
      exact (Nat.add_le_add hc₀ hcn).trans_eq (by ring)
    · rw [iterate, StateTransitionSpec.clientState_bind]; exact hfrn.trans hfr₀
    · rw [iterate, StateTransitionSpec.clientState_bind]; exact (hmodn x hx).trans (hmod₀ x hx)
    · rw [iterate, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      exact hinvn

end Cslib.WordRAM.Realization
