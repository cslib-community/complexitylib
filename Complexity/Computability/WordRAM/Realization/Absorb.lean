/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Bind
public import Complexity.Computability.WordRAM.Realization.Branch
public import Complexity.Computability.WordRAM.Realization.GlueVector
public import Complexity.Computability.WordRAM.Realization.Primitive

/-!
# Realization rules with absorbed constant local work

`Realizes` bounds native instructions by `C * (memory charge + local work + 1)` with one
existential exchange factor `C`. Local work bounded by a constant multiple of another grading can
therefore be traded for a larger factor (`Realizes.mono_mul`). In particular, a loop-free
composition of glue, binds and branches has the same certificate with local work `0`: its native
cost is `O(memory charge + 1)`. Loop work grows with the iteration count, so loops keep their
graded charge.

The rules below are the C2 rules `bind`, `branch` and `glueVector` with that absorption applied.
They are the target shapes of the `realize` tactic. Scalar and finite-vector glue takes
`GlueComputable` certificates, whose instruction budgets stay hidden.

## Main definitions

* `WordEncoding`: the word encoding `realize` uses for an intermediate answer type.

## Main results

* `Realizes.mono_mul`: absorb a local-work grading dominated by a constant multiple.
* `Realizes.congr`: transport a certificate along pointwise equal programs.
* `Realizes.bind₀`, `Realizes.branch₀`: sequencing and branching with absorbed control work.
* `Realizes.pure₀`: finite-result glue from `GlueComputable` coordinates, with a visible domain
  and an explicit word-fit obligation.

These are derived rules over the existing realization kernel; no execution semantics or
certificate is added.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-- The faithful word encoding `realize` uses when a bind passes an answer of type `α` to its
continuation. Instances cover words, unit, optional words and Booleans. -/
class WordEncoding (α : Type) where
  /-- The number of words. -/
  width : ℕ
  /-- The faithful encoding. -/
  encode : α ↪ (Fin width → ℕ)

instance : WordEncoding ℕ := ⟨1, (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding⟩

instance : WordEncoding Unit := ⟨0, (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding⟩

instance : WordEncoding (Option ℕ) := ⟨2, optionWords⟩

instance : WordEncoding Bool := ⟨2, boolWords⟩

variable {B : Basis} {δ α β : Type} {k l m : ℕ}

namespace Realizes

variable {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work work' : δ → Memory.State → ℕ}

/-- A local-work grading within a constant multiple of another is absorbed by the exchange
factor. The new factor is `C * (K + 1)`; the emitter and scratch are unchanged. -/
theorem mono_mul (h : Realizes B p input output safe work) (K : ℕ)
    (hwork : ∀ d s, work d s ≤ K * (work' d s + 1)) :
    Realizes B p input output safe work' := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C * (K + 1), emit, fun frontier src tmp hi hd hf hs => ?_⟩
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  refine ⟨hnw, fun w d x hx hin hsafe hv => ?_⟩
  obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x hx hin hsafe hv
  refine ⟨y, hy.mono ?_, hm, hout, hframe⟩
  have hw := hwork d (memoryState frontier x)
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have hexpand : (K + 1) * (memoryCost (p d) (memoryState frontier x) +
      work' d (memoryState frontier x) + 1) =
      K * (work' d (memoryState frontier x) + 1) +
        K * memoryCost (p d) (memoryState frontier x) +
        (memoryCost (p d) (memoryState frontier x) + work' d (memoryState frontier x) + 1) := by
    ring
  omega

/-- Pointwise equal programs have the same certificates. -/
theorem congr {p' : δ → Memory.Prog α} (h : Realizes B p input output safe work)
    (hp : ∀ d, p d = p' d) : Realizes B p' input output safe work :=
  funext hp ▸ h

variable {q : δ × α → Memory.Prog β} {answer : α ↪ (Fin l → ℕ)} {output' : β ↪ (Fin m → ℕ)}
  {safeP : ℕ → δ → Memory.State → Prop} {safeQ : ℕ → δ × α → Memory.State → Prop}

/-- Sequencing with the bind's control unit absorbed. -/
theorem bind₀ (hP : Realizes B p input answer safeP (fun _ _ => 0))
    (hQ : Realizes B q ((input.prodMap answer).trans (Fin.appendEquiv k l).toEmbedding) output'
      safeQ (fun _ _ => 0)) :
    Realizes B (fun d => (p d).bind (fun a => q (d, a))) input output'
      (fun w d s => safeP w d s ∧
        safeQ w (d, (Memory.spec 0).clientResult s (p d)) ((Memory.spec 0).clientState s (p d)))
      (fun _ _ => 0) :=
  (hP.bind hQ).mono_mul 1 (fun _ _ => le_refl _)

/-- Branching with the test and jump absorbed. Only the selected alternative's domain is
required. -/
theorem branch₀ {pos neg : δ → Memory.Prog α} {safePos safeNeg : ℕ → δ → Memory.State → Prop}
    (c : Cond k) (hp : Realizes B pos input output safePos (fun _ _ => 0))
    (hn : Realizes B neg input output safeNeg (fun _ _ => 0)) :
    Realizes B (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s) (fun _ _ => 0) :=
  (branch c hp hn).mono_mul 2 (fun _ _ => by split <;> simp)

/-- Return a computed finite result. Each coordinate has a `GlueComputable` certificate over the
live words with a common domain `P` and value envelope `bound`; `need` is any condition that,
together with the live words' fit and `P`, makes the envelope fit. Native glue cost is absorbed. -/
theorem pure₀ (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ)) (f : δ → α)
    (g : Fin l → (Fin k → ℕ) → ℕ) {P : (Fin k → ℕ) → Prop} {bound : (Fin k → ℕ) → ℕ}
    (need : ℕ → (Fin k → ℕ) → Prop)
    (hresult : ∀ d i, output (f d) i = g i (input d))
    (hcoord : ∀ i, GlueComputable B (g i) P bound)
    (hneed : ∀ w v, (∀ i, Fits w (v i)) → P v → need w v → Fits w (bound v)) :
    Realizes B (fun d => pure (f d)) input output
      (fun w d _ => P (input d) ∧ need w (input d)) (fun _ _ => 0) := by
  choose time htime using hcoord
  refine ((glueVector input output f g (fun _ => bound) time hresult htime).consequence
    (fun w d _ hwords _ h => ⟨h.1, fun _ => hneed w _ hwords h.1 h.2⟩)
    (fun _ _ => le_rfl)).mono_mul ((∑ i, time i) + l) (fun _ _ => ?_)
  simp

end Realizes

end Cslib.WordRAM.Realization
