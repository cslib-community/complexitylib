/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Automata.NA.Basic
public import Mathlib.Computability.Language

/-!
# Relabelling nondeterministic automata along a letter map

Given a letter map `f : Symbol → Symbol'` and a nondeterministic automaton `na` over `Symbol`,
`na.map f` is the automaton over `Symbol'` with the same states, start and accepting states, which
can step from `s` to `t` on `b` whenever `na` can step from `s` to `t` on some letter `a` with
`f a = b`. It accepts exactly the image `Language.map f (language na)`: this is the projection
step of the translation of monadic second-order logic into automata
[Thomas, Section 3][Thomas1997].

Unlike `NA.FinAcc.preimage`, which pulls an automaton back along a language homomorphism, `map`
pushes it forward along a letter-to-letter map, so it needs nondeterminism even when `na` is
deterministic.

## Main definitions

* `Cslib.Automata.NA.FinAcc.map`: relabel the transitions of an automaton along a letter map.

## Main results

* `Cslib.Automata.NA.FinAcc.map_mTr`: the multistep transitions of `na.map f` are the images of
  those of `na`.
* `Cslib.Automata.NA.FinAcc.map_language_eq`: `na.map f` accepts `Language.map f (language na)`.

## References

* [W. Thomas, *Languages, automata, and logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Automata.NA.FinAcc

open Acceptor

variable {State Symbol Symbol' : Type*}

/-- Relabel the transitions of an automaton along a letter map `f`: `na.map f` steps from `s` to
`t` on `b` when `na` steps from `s` to `t` on some letter `a` with `f a = b`. -/
def map (f : Symbol → Symbol') (na : FinAcc State Symbol) : FinAcc State Symbol' where
  Tr s b t := ∃ a, f a = b ∧ na.Tr s a t
  start := na.start
  accept := na.accept

@[simp]
theorem map_start (f : Symbol → Symbol') (na : FinAcc State Symbol) :
    (na.map f).start = na.start := rfl

@[simp]
theorem map_accept (f : Symbol → Symbol') (na : FinAcc State Symbol) :
    (na.map f).accept = na.accept := rfl

/-- `na.map f` has a run from `s` to `t` on `ys` iff `na` has one on some word that `f` maps
to `ys`. -/
theorem map_mTr (f : Symbol → Symbol') (na : FinAcc State Symbol) {s t : State}
    {ys : List Symbol'} :
    (na.map f).MTr s ys t ↔ ∃ xs, xs.map f = ys ∧ na.MTr s xs t := by
  induction ys generalizing s with
  | nil =>
    simp only [LTS.MTr.nil_iff, List.map_eq_nil_iff, exists_eq_left]
  | cons b ys ih =>
    rw [LTS.MTr.cons_iff]
    constructor
    · rintro ⟨u, ⟨a, rfl, ha⟩, hu⟩
      obtain ⟨xs, rfl, hxs⟩ := ih.1 hu
      exact ⟨a :: xs, rfl, LTS.MTr.stepL ha hxs⟩
    · rintro ⟨_ | ⟨a, xs⟩, hxs, h⟩
      · exact absurd hxs (List.cons_ne_nil b ys).symm
      · rw [List.map_cons, List.cons.injEq] at hxs
        obtain ⟨rfl, rfl⟩ := hxs
        obtain ⟨u, hu, hrest⟩ := LTS.MTr.cons_iff.1 h
        exact ⟨u, ⟨a, rfl, hu⟩, ih.2 ⟨xs, rfl, hrest⟩⟩

/-- `na.map f` accepts the image under `f` of the language of `na`. -/
theorem map_language_eq (f : Symbol → Symbol') (na : FinAcc State Symbol) :
    language (na.map f) = Language.map f (language na) := by
  ext ys
  simp only [mem_language, Accepts]
  change _ ↔ ys ∈ List.map f '' _
  constructor
  · rintro ⟨s, hs, t, ht, h⟩
    obtain ⟨xs, rfl, hxs⟩ := (map_mTr f na).1 h
    exact ⟨xs, ⟨s, hs, t, ht, hxs⟩, rfl⟩
  · rintro ⟨xs, ⟨s, hs, t, ht, hxs⟩, rfl⟩
    exact ⟨s, hs, t, ht, (map_mTr f na).2 ⟨xs, rfl, hxs⟩⟩

end Cslib.Automata.NA.FinAcc
