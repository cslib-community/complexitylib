/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.PCP.Encoded.Composition
public import CslibFrontier.Computability.PCP.Encoded.SelectedComposition
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.List.OfFn

/-! Explicit finite numberings reused by executable PCP composition and amplification tests. -/

@[expose] public section

namespace ComplexityTests.PCPNumbering

open Cslib Cslib.PCP.HadamardTester Cslib.PCP.Encoded

-- These numberings compose explicit equivalences, never a chosen Fintype.equivFin.
abbrev Numbering (α : Type) := Σ n, α ≃ Fin n

def numberProd {α β : Type} (left : Numbering α) (right : Numbering β) :
    Numbering (α × β) :=
  ⟨left.1 * right.1, (Equiv.prodCongr left.2 right.2).trans finProdFinEquiv⟩

def numberSum {α β : Type} (left : Numbering α) (right : Numbering β) :
    Numbering (α ⊕ β) :=
  ⟨left.1 + right.1, (Equiv.sumCongr left.2 right.2).trans finSumFinEquiv⟩

def numberBits {α : Type} (alphabet : Numbering α) : Numbering (α → Bool) :=
  ⟨2 ^ alphabet.1,
    (Equiv.arrowCongr alphabet.2 (Equiv.refl Bool)).trans (BitString.equivFin alphabet.1)⟩

def numberCoins {α : Type} (alphabet : Numbering α) : Numbering (Rand α) :=
  let indices := numberProd ⟨2, Equiv.refl _⟩ alphabet
  let linear := numberBits indices
  let quadratic := numberBits (numberProd indices indices)
  let equations := numberBits (numberSum (numberProd indices indices) ⟨2, Equiv.refl _⟩)
  numberProd (numberProd linear linear) <|
    numberProd (numberProd quadratic quadratic) <|
    numberProd (numberProd linear (numberProd linear (numberProd linear (numberProd linear
      quadratic)))) <|
    numberProd (numberProd equations quadratic) <|
    numberProd ⟨2, Equiv.refl _⟩ (numberProd (numberBits alphabet) linear)

def numberSlots {α : Type} (alphabet : Numbering α) : Numbering (Graph.ComposeSlot α) :=
  let indices := numberProd ⟨2, Equiv.refl _⟩ alphabet
  numberSum (numberBits alphabet) <|
    numberSum (numberSum (numberBits indices) (numberBits (numberProd indices indices)))
      (numberCoins alphabet)

-- Parallel explicit numberings for the six-query selected composition. The conjunction helpers
-- above remain unchanged for clients that still use the seventeen-query tester.
def numberSelectedCoins {α : Type} (alphabet : Numbering α) :
    Numbering (Fin 5 × Rand α) :=
  numberProd ⟨5, Equiv.refl _⟩ (numberCoins alphabet)

def numberSelectedSlots {α : Type} (alphabet : Numbering α) :
    Numbering (Graph.SelectedComposeSlot α) :=
  let indices := numberProd ⟨2, Equiv.refl _⟩ alphabet
  numberSum (numberBits alphabet) <|
    numberSum (numberSum (numberBits indices) (numberBits (numberProd indices indices)))
      (numberSelectedCoins alphabet)

def numberSelectedQueries : Numbering (Fin 6) := ⟨6, Equiv.refl _⟩

def selectedQueries : List (Fin 6) := List.ofFn numberSelectedQueries.2.symm

def selectedCoins {α : Type} (alphabet : Numbering α) : List (Fin 5 × Rand α) :=
  List.ofFn (numberSelectedCoins alphabet).2.symm

theorem nodup_selectedCoins {α : Type} (alphabet : Numbering α) :
    (selectedCoins alphabet).Nodup :=
  List.nodup_ofFn.mpr (numberSelectedCoins alphabet).2.symm.injective

theorem mem_selectedCoins {α : Type} (alphabet : Numbering α) (ω : Fin 5 × Rand α) :
    ω ∈ selectedCoins alphabet :=
  List.mem_ofFn.mpr ⟨(numberSelectedCoins alphabet).2 ω,
    (numberSelectedCoins alphabet).2.symm_apply_apply ω⟩

theorem nodup_selectedQueries : selectedQueries.Nodup :=
  List.nodup_ofFn.mpr numberSelectedQueries.2.symm.injective

theorem mem_selectedQueries (i : Fin 6) : i ∈ selectedQueries :=
  List.mem_ofFn.mpr ⟨numberSelectedQueries.2 i, numberSelectedQueries.2.symm_apply_apply i⟩

def numberQueries : Numbering Query :=
  numberSum ⟨3, Equiv.refl _⟩ <| numberSum ⟨3, Equiv.refl _⟩ <|
    numberSum ⟨6, Equiv.refl _⟩ <| numberSum ⟨2, Equiv.refl _⟩ ⟨3, Equiv.refl _⟩

def queries : List Query := List.ofFn numberQueries.2.symm

theorem nodup_coins {α : Type} (alphabet : Numbering α) :
    (List.ofFn (numberCoins alphabet).2.symm).Nodup :=
  List.nodup_ofFn.mpr (numberCoins alphabet).2.symm.injective

theorem mem_coins {α : Type} (alphabet : Numbering α) (ω : Rand α) :
    ω ∈ List.ofFn (numberCoins alphabet).2.symm :=
  List.mem_ofFn.mpr ⟨(numberCoins alphabet).2 ω, (numberCoins alphabet).2.symm_apply_apply ω⟩

theorem nodup_queries : queries.Nodup :=
  List.nodup_ofFn.mpr numberQueries.2.symm.injective

theorem mem_queries (i : Query) : i ∈ queries :=
  List.mem_ofFn.mpr ⟨numberQueries.2 i, numberQueries.2.symm_apply_apply i⟩

end ComplexityTests.PCPNumbering
