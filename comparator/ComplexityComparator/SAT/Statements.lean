/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger, OpenAI.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, OpenAI

Independent statement surface for a comparator audit of complexitylib.
The encoding proofs are adapted from Christian Reitwiessner's pure framed-word
and encoding definitions, with no imports from Complexity or ComplexityAbstracts.
-/

module
-- upstream: local-only (independent comparator statements)

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Bitwise

/-!
# Independently stated SAT and counting contracts

The definitions below spell out CNF evaluation, model counting, bit encodings and resource
bounds. They import only pinned upstream CSLib machine semantics and Mathlib, not complexitylib's
CNF, complexity-class, encoding or algorithm modules. The encoding definitions retain their
original source credit; the two proposition definitions at the end specify the checked endpoints.
-/

@[expose] public section

namespace ComplexityComparator.SAT

/- Binary serialization: tag each bit with true and terminate its frame with false. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

def unframe : List Bool → List Bool
  | true :: b :: v => b :: unframe v
  | _ => []

def dropFrame : List Bool → List Bool
  | true :: _ :: v => dropFrame v
  | false :: v => v
  | _ => []

@[simp] theorem frame_nil : frame [] = [false] := rfl
@[simp] theorem frame_cons (b : Bool) (w : List Bool) :
    frame (b :: w) = true :: b :: frame w := rfl
@[simp] theorem frame_ne_nil (w : List Bool) : frame w ≠ [] := by simp [frame]

@[simp] theorem unframe_frame_append (w u : List Bool) : unframe (frame w ++ u) = w := by
  induction w <;> simp [unframe, *]

@[simp] theorem dropFrame_frame_append (w u : List Bool) : dropFrame (frame w ++ u) = u := by
  induction w <;> simp [dropFrame, *]

theorem frame_append_inj {w w' u u' : List Bool} (h : frame w ++ u = frame w' ++ u') :
    w = w' ∧ u = u' :=
  ⟨by simpa using congrArg unframe h, by simpa using congrArg dropFrame h⟩

def encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨fun p => frame (a p.1) ++ b p.2, fun _ _ h =>
    Prod.ext (a.injective (frame_append_inj h).1) (b.injective (frame_append_inj h).2)⟩

def encList {α : Type} (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨fun l => l.flatMap (frame ∘ enc), fun l l' h => by
    induction l generalizing l' with
    | nil => cases l' <;> simp_all
    | cons a l ih =>
      cases l' with
      | nil => simp at h
      | cons a' l' => rw [enc.injective (frame_append_inj h).1, ih _ (frame_append_inj h).2]⟩

def encNat : ℕ ↪ List Bool :=
  ⟨Nat.bits, fun m n h => Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_eq_inth, h]⟩

def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/- CNF semantics use finite sets of the occurring variables, independent of their labels. -/
abbrev Literal := ℕ × Bool
abbrev Clause := List Literal
abbrev Formula := List Clause

def eval (φ : Formula) (σ : ℕ → Bool) : Bool :=
  φ.all fun clause => clause.any fun literal => σ literal.1 == literal.2

def Satisfiable (φ : Formula) : Prop := ∃ σ : ℕ → Bool, eval φ σ = true
def vars (φ : Formula) : Finset ℕ := (φ.flatten.map Prod.fst).toFinset
def numVars (φ : Formula) : ℕ := (vars φ).card

def modelCount (φ : Formula) : ℕ :=
  (Finset.univ.filter fun σ : vars φ → Bool =>
    eval φ (fun v => if h : v ∈ vars φ then σ ⟨v, h⟩ else false) = true).card

def HasWidth (k : ℕ) (φ : Formula) : Prop := ∀ clause ∈ φ, clause.length ≤ k

def encCNF : Formula ↪ List Bool := encList (encList (encPair encNat encBool))

/- One upstream deterministic binary multitape TM is fixed before all inputs. -/
def ComputableInO {α β : Type} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (T S : α → ℕ) : Prop :=
  ∃ c, Turing.MultiTapeTM.ComputableInTimeAndSpace f encIn encOut
      (fun x => c * (T x + 1)) (fun x => c * (S x + 1)) ∧
    ∀ x, (encOut (f x)).length ≤ c * (S x + 1)

def DecidableInTimeO {α : Type} (A : Set α) (enc : α ↪ List Bool) (T : α → ℝ) : Prop :=
  ∃ c : ℕ, ∃ t s : α → ℕ, (∀ x, (t x : ℝ) ≤ c * T x + c) ∧
    Turing.MultiTapeTM.DecidableInTimeAndSpace A enc t s

def DecidableInExpTime {α : Type} (A : Set α) (enc : α ↪ List Bool)
    (μ : α → ℕ) (δ : ℝ) : Prop :=
  ∃ e : ℕ, DecidableInTimeO A enc fun x => 2 ^ (δ * μ x) * ((enc x).length + 1) ^ e

def KSAT (k : ℕ) : Set Formula :=
  {φ | (∀ clause ∈ φ, clause.length ≤ k) ∧ Satisfiable φ}

def ETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ¬DecidableInExpTime (KSAT 3) encCNF numVars δ

noncomputable def interpolationScale (n : ℕ) : ℝ :=
  n * Real.log (Real.log ((n : ℝ) + 16)) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16))

/-- One counter per fixed width counts all satisfying assignments within the interpolation-scale
bound and polynomial work space, including the encoded output charge. -/
def ExactCount : Prop :=
  ∀ k : Nat, ∃ (count : Formula → Nat) (A e b : Nat),
    (∀ φ, HasWidth k φ → count φ = modelCount φ) ∧
    ComputableInO count encCNF encNat
      (fun φ => ⌈(2 : ℝ) ^ (A * interpolationScale (numVars φ))⌉₊ *
        ((encCNF φ).length + 1) ^ e)
      (fun φ => ((encCNF φ).length + 1) ^ b)

/-- No positive exponential rate lower-bounds every deterministic 3SAT decider. -/
def NotETH : Prop := ¬ETH

end ComplexityComparator.SAT
