/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PostCorrespondence.Basic

/-!
# From the modified correspondence problem to PCP

Sipser's reduction [Sipser2013, proof of Theorem 5.15] turns an MPCP instance into a PCP instance
over the alphabet `α` extended by markers. Writing `⋆u` for `⋆u₁⋆u₂⋯⋆uₙ` and `u⋆` for
`u₁⋆u₂⋆⋯uₙ⋆`, the domino `t / b` becomes `⋆t / b⋆`, the start domino `t / b` becomes
`⋆t / ⋆b⋆`, and the end domino `⋆◇ / ◇` is added. A match must then begin with the start domino,
whose top and bottom alone begin with the same letter.

As stated, the construction can be unsound when a domino of the instance has an empty bottom,
since `⋆t / ε` may then come first. For the start domino `a / ba` and the single domino `b / ε`, the
MPCP instance has no match (its top begins with `a` and its bottom with `b`), but
`⋆b / ε`, `⋆a / ⋆b⋆a⋆`, `⋆◇ / ◇` is a match of the PCP instance (checked in the test module
`ComplexityTests.PostCorrespondence`). The reduction here therefore prefixes the start
domino with a start marker `▷`, which occurs in no other domino. A match then contains the start
domino, the part before its first occurrence matches on its own, and the part after it gives an
MPCP match. The domino `ε / ε`, which would be a PCP match by itself, is dropped.

Sipser's machine instances contain no domino with an empty bottom, so his proof is unaffected. The
instances of `Complexity.Computability.PostCorrespondence.OfTM0` do: the rule `OfTM0.Rule.finish`
erases the final word `⊢ halt ⊣`. So Sipser's argument does not apply to them as written, while
the marked reduction needs no instance-specific argument. Empty tops are harmless.

## Main definitions

* `Cslib.PostCorrespondence.Marked`: the alphabet `α` with the markers `⋆`, `◇` and `▷`.
* `Cslib.PostCorrespondence.toPCP`: the reduction.

## Main results

* `Cslib.PostCorrespondence.solvable_toPCP_iff`: `toPCP I` is solvable iff `I` is.
* `Cslib.PostCorrespondence.mSolvable_manyOneReducible`: MPCP many-one reduces to PCP.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.PostCorrespondence

variable {α : Type*}

-- Exposed so that `decide` can evaluate the derived `DecidableEq` instance in client modules.
@[expose] public section MarkedDef

/-- The alphabet of Sipser's reduction from MPCP to PCP: the letters of `α` and three markers. -/
inductive Marked (α : Type*) where
  /-- A letter of the original alphabet. -/
  | letter : α → Marked α
  /-- The separator `⋆`. -/
  | sep : Marked α
  /-- The end marker `◇`. -/
  | stop : Marked α
  /-- The start marker `▷`, which forces every match to begin with the start domino. -/
  | start : Marked α
deriving DecidableEq

end MarkedDef

namespace Marked

/-- `Marked α` as `α ⊕ Fin 3`. -/
def equivSum : Marked α ≃ α ⊕ Fin 3 where
  toFun
    | letter a => .inl a
    | sep => .inr 0
    | stop => .inr 1
    | start => .inr 2
  invFun
    | .inl a => letter a
    | .inr 0 => sep
    | .inr 1 => stop
    | .inr 2 => start
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with a | ⟨_ | _ | _ | n, h⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · omega

instance [Primcodable α] : Primcodable (Marked α) := Primcodable.ofEquiv _ equivSum

theorem primrec_letter [Primcodable α] : Primrec (letter : α → Marked α) :=
  (Primrec.of_equiv_symm.comp Primrec.sumInl).of_eq fun _ => rfl

end Marked

open Marked

/-- `⋆a₁⋆a₂⋯⋆aₙ`: a separator before every letter. -/
def starBefore (w : List α) : List (Marked α) := w.flatMap fun a => [sep, letter a]

/-- `a₁⋆a₂⋆⋯aₙ⋆`: a separator after every letter. -/
def starAfter (w : List α) : List (Marked α) := w.flatMap fun a => [letter a, sep]

@[simp] theorem starBefore_nil : starBefore ([] : List α) = [] := List.flatMap_nil
@[simp] theorem starAfter_nil : starAfter ([] : List α) = [] := List.flatMap_nil
@[simp] theorem starBefore_cons (a : α) (w : List α) :
    starBefore (a :: w) = sep :: letter a :: starBefore w := List.flatMap_cons
@[simp] theorem starAfter_cons (a : α) (w : List α) :
    starAfter (a :: w) = letter a :: sep :: starAfter w := List.flatMap_cons
@[simp] theorem starBefore_append (u v : List α) :
    starBefore (u ++ v) = starBefore u ++ starBefore v := List.flatMap_append
@[simp] theorem starAfter_append (u v : List α) :
    starAfter (u ++ v) = starAfter u ++ starAfter v := List.flatMap_append

/-- `⋆ (a₁⋆⋯aₙ⋆) = (⋆a₁⋯⋆aₙ) ⋆`. -/
theorem sep_cons_starAfter (w : List α) : sep :: starAfter w = starBefore w ++ [sep] := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [starAfter_cons, starBefore_cons, ih]; rfl

theorem sep_cons_starAfter_append (w : List α) (l : List (Marked α)) :
    sep :: (starAfter w ++ l) = starBefore w ++ sep :: l := by
  rw [← List.cons_append, sep_cons_starAfter, List.append_assoc, List.singleton_append]

theorem length_starBefore (w : List α) : (starBefore w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [starBefore_cons, List.length_cons, ih]; omega

theorem starBefore_injective : Function.Injective (starBefore : List α → List (Marked α)) := by
  intro u
  induction u with
  | nil =>
    rintro (_ | ⟨b, v⟩) h
    · rfl
    · simp at h
  | cons a u ih =>
    rintro (_ | ⟨b, v⟩) h
    · simp at h
    · simp only [starBefore_cons, List.cons.injEq, letter.injEq, true_and] at h
      rw [h.1, ih h.2]

theorem start_notMem_starBefore (w : List α) : start ∉ starBefore w := by
  simp [starBefore]

theorem start_notMem_starAfter (w : List α) : start ∉ starAfter w := by
  simp [starAfter]

theorem stop_notMem_starBefore (w : List α) : stop ∉ starBefore w := by
  simp [starBefore]

theorem head?_starBefore (w : List α) : ∀ x ∈ (starBefore w).head?, x = sep := by
  cases w <;> simp

theorem head?_starAfter (w : List α) : ∀ x ∈ (starAfter w).head?, x ≠ sep := by
  cases w <;> simp

/-- The start domino of the PCP instance: `▷⋆t₁⋯⋆tₖ` over `▷⋆b₁⋆⋯bₗ⋆`. -/
def startPiece (s : Domino α) : Domino (Marked α) :=
  ⟨start :: starBefore s.top, start :: sep :: starAfter s.bottom⟩

/-- The end domino of the PCP instance: `⋆◇` over `◇`. -/
def stopPiece : Domino (Marked α) := ⟨[sep, stop], [stop]⟩

/-- The domino `⋆t₁⋯⋆tₖ` over `b₁⋆⋯bₗ⋆` of a domino `t` over `b`. -/
def markPiece (d : Domino α) : Domino (Marked α) := ⟨starBefore d.top, starAfter d.bottom⟩

/-- Sipser's reduction from MPCP to PCP [Sipser2013, proof of Theorem 5.15], with a start marker
`▷`: the start domino, the end domino, and the marked dominoes of the instance other than the empty
one. -/
def toPCP (I : MInstance α) : List (Domino (Marked α)) :=
  startPiece I.start :: stopPiece ::
    (I.dominoes.filter fun d => 0 < d.top.length + d.bottom.length).map markPiece

theorem tops_map_markPiece (ds : List (Domino α)) :
    tops (ds.map markPiece) = starBefore (tops ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.map_cons, tops_cons, tops_cons, ih, starBefore_append]; rfl

theorem bottoms_map_markPiece (ds : List (Domino α)) :
    bottoms (ds.map markPiece) = starAfter (bottoms ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.map_cons, bottoms_cons, bottoms_cons, ih, starAfter_append]; rfl

private theorem tops_filter (ds : List (Domino α)) :
    tops (ds.filter fun d => 0 < d.top.length + d.bottom.length) = tops ds ∧
      bottoms (ds.filter fun d => 0 < d.top.length + d.bottom.length) = bottoms ds := by
  induction ds with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
    rcases d with ⟨t, b⟩
    by_cases h : 0 < t.length + b.length
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp only [tops_cons, bottoms_cons, ih.1, ih.2, and_self]
    · rw [List.filter_cons_of_neg (by simpa using h)]
      have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hb : b = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst ht hb
      exact ih

/-- The marked pieces after the start domino: if their tops follow `⋆T` and their bottoms follow
`⋆B⋆`, then a sequence of dominoes of the instance completes `T` over `B`. -/
private theorem complete_of_marked (I : MInstance α) :
    ∀ (ρ : List (Domino (Marked α))) (T B : List α), (∀ d ∈ ρ, d ∈ toPCP I) →
      starBefore T ++ tops ρ = starBefore B ++ sep :: bottoms ρ →
      ∃ ds : List (Domino α), (∀ d ∈ ds, d ∈ I.dominoes) ∧ T ++ tops ds = B ++ bottoms ds
  | [], T, B, _, h => by
    have := congrArg List.length h
    simp only [tops_nil, List.append_nil, bottoms_nil, List.length_append, length_starBefore,
      List.length_cons, List.length_nil] at this
    omega
  | d :: ρ, T, B, hρ, h => by
    have hd := hρ d List.mem_cons_self
    have hρ' : ∀ d ∈ ρ, d ∈ toPCP I := fun e he => hρ e (List.mem_cons_of_mem d he)
    simp only [toPCP, List.mem_cons, List.mem_map, List.mem_filter] at hd
    rcases hd with rfl | rfl | ⟨e, ⟨he, -⟩, rfl⟩
    · -- the start domino again: impossible, by the parity of the prefix
      have h' : starBefore T ++ start :: (starBefore I.start.top ++ tops ρ) =
          (starBefore B ++ [sep]) ++ start :: (sep :: starAfter I.start.bottom ++ bottoms ρ) := by
        simpa [startPiece] using h
      obtain ⟨h'', -⟩ := (append_cons_inj_of_notMem_prefix (start_notMem_starBefore T)
        (by simp [start_notMem_starBefore])).mp h'
      have := congrArg List.length h''
      simp only [List.length_append, length_starBefore, List.length_singleton] at this
      omega
    · -- the end domino: then `T = B`
      have h' : (starBefore T ++ [sep]) ++ stop :: tops ρ =
          (starBefore B ++ [sep]) ++ stop :: bottoms ρ := by
        simpa [stopPiece] using h
      obtain ⟨h'', -⟩ := (append_cons_inj_of_notMem_prefix (by simp [stop_notMem_starBefore])
        (by simp [stop_notMem_starBefore])).mp h'
      have hTB : T = B := starBefore_injective (List.append_cancel_right h'')
      exact ⟨[], fun _ h => absurd h List.not_mem_nil, by rw [hTB, tops_nil, bottoms_nil]⟩
    · -- a marked domino of the instance
      have key : starBefore B ++ sep :: (starAfter e.bottom ++ bottoms ρ) =
          starBefore (B ++ e.bottom) ++ sep :: bottoms ρ := by
        rw [sep_cons_starAfter_append, starBefore_append, List.append_assoc]
      simp only [tops_cons, bottoms_cons, markPiece] at h
      obtain ⟨ds, hds, heq⟩ := complete_of_marked I ρ (T ++ e.top) (B ++ e.bottom) hρ' (by
        rw [starBefore_append, List.append_assoc, h, key])
      refine ⟨e :: ds, ?_, by simpa using heq⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact he
      · exact hds d hd

/-- The heads of the concatenation of words whose heads satisfy `p`. -/
private theorem head?_flatMap {β : Type*} {p : α → Prop} {f : β → List α} :
    ∀ {l : List β}, (∀ b ∈ l, ∀ x ∈ (f b).head?, p x) → ∀ x ∈ (l.flatMap f).head?, p x
  | [], _ => by simp
  | b :: l, h => by
    rw [List.flatMap_cons]
    intro x hx
    cases hfb : f b with
    | nil =>
      rw [hfb, List.nil_append] at hx
      exact head?_flatMap (fun c hc => h c (List.mem_cons_of_mem b hc)) x hx
    | cons y w =>
      rw [hfb, List.cons_append, List.head?_cons, Option.mem_some_iff] at hx
      exact h b List.mem_cons_self x (by rw [hfb, ← hx]; rfl)

/-- **Sipser's reduction is correct.** An MPCP instance is solvable exactly when the PCP instance
`toPCP I` is. -/
theorem solvable_toPCP_iff (I : MInstance α) : Solvable (toPCP I) ↔ I.Solvable := by
  constructor
  · rintro ⟨ρ, hne, hρ, heq⟩
    by_cases hs : startPiece I.start ∈ ρ
    · obtain ⟨ρ₁, _, ρ₂, rfl, rfl, hρ₁⟩ :=
        exists_eq_append_cons_of_exists_mem (p := (· = startPiece I.start)) ⟨_, hs, rfl⟩
      -- no domino before the start domino contains `▷`
      have hnot : ∀ d ∈ ρ₁, start ∉ d.top ∧ start ∉ d.bottom := by
        intro d hd
        have hd' := hρ d (List.mem_append_left _ hd)
        simp only [toPCP, List.mem_cons, List.mem_map, List.mem_filter] at hd'
        rcases hd' with rfl | rfl | ⟨e, -, rfl⟩
        · exact absurd rfl (hρ₁ _ hd)
        · simp [stopPiece]
        · exact ⟨start_notMem_starBefore _, start_notMem_starAfter _⟩
      have ht : start ∉ tops ρ₁ := by
        simp only [tops, List.mem_flatMap, not_exists, not_and]
        exact fun d hd => (hnot d hd).1
      have hb : start ∉ bottoms ρ₁ := by
        simp only [bottoms, List.mem_flatMap, not_exists, not_and]
        exact fun d hd => (hnot d hd).2
      simp only [tops_append, tops_cons, startPiece, bottoms_append, bottoms_cons,
        List.cons_append] at heq
      obtain ⟨-, heq⟩ := (append_cons_inj_of_notMem_prefix ht hb).mp heq
      have hρ₂ : ∀ d ∈ ρ₂, d ∈ toPCP I := fun d hd =>
        hρ d (List.mem_append_right _ (List.mem_cons_of_mem _ hd))
      exact complete_of_marked I ρ₂ I.start.top I.start.bottom hρ₂ (by
        rw [heq, sep_cons_starAfter_append])
    · -- without the start domino, tops begin with `⋆` and bottoms do not
      exfalso
      have hρ' : ∀ d ∈ ρ, d = stopPiece ∨ ∃ e ∈ I.dominoes, 0 < e.top.length + e.bottom.length ∧
          d = markPiece e := by
        intro d hd
        have hd' := hρ d hd
        simp only [toPCP, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq] at hd'
        rcases hd' with rfl | rfl | ⟨e, ⟨he, hpos⟩, rfl⟩
        · exact absurd hd hs
        · exact Or.inl rfl
        · exact Or.inr ⟨e, he, hpos, rfl⟩
      have htop : ∀ x ∈ (tops ρ).head?, x = sep := head?_flatMap fun d hd => by
        rcases hρ' d hd with rfl | ⟨e, -, -, rfl⟩
        · simp [stopPiece]
        · exact head?_starBefore e.top
      have hbot : ∀ x ∈ (bottoms ρ).head?, x ≠ sep := head?_flatMap fun d hd => by
        rcases hρ' d hd with rfl | ⟨e, -, -, rfl⟩
        · simp [stopPiece]
        · exact head?_starAfter e.bottom
      have hnil : tops ρ = [] := by
        cases h : tops ρ with
        | nil => rfl
        | cons x w =>
          have hx := htop x (by rw [h]; rfl)
          rw [heq] at h
          exact absurd hx (hbot x (by rw [h]; rfl))
      obtain ⟨d, ρ', rfl⟩ := List.exists_cons_of_ne_nil hne
      have hdt : d.top = [] := List.append_eq_nil_iff.mp (by simpa using hnil) |>.1
      have hdb : d.bottom = [] := by
        rw [heq] at hnil
        exact (List.append_eq_nil_iff.mp (by simpa using hnil)).1
      rcases hρ' d List.mem_cons_self with rfl | ⟨e, -, hpos, rfl⟩
      · simp [stopPiece] at hdt
      · have h1 : e.top = [] := by
          have := congrArg List.length hdt
          simp only [markPiece, length_starBefore, List.length_nil] at this
          exact List.eq_nil_of_length_eq_zero (by omega)
        have h2 : e.bottom = [] := by
          cases hb : e.bottom with
          | nil => rfl
          | cons y w => simp [markPiece, hb] at hdb
        rw [h1, h2] at hpos
        simp at hpos
  · rintro ⟨ds, hds, heq⟩
    obtain ⟨ht, hb⟩ := tops_filter ds
    refine ⟨startPiece I.start ::
        ((ds.filter fun d => 0 < d.top.length + d.bottom.length).map markPiece ++ [stopPiece]),
      List.cons_ne_nil _ _, fun d hd => ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hd
      simp only [toPCP, List.mem_cons, List.mem_map]
      rcases hd with rfl | ⟨e, he, rfl⟩ | rfl
      · exact Or.inl rfl
      · rw [List.mem_filter] at he
        exact Or.inr (Or.inr ⟨e, List.mem_filter.mpr ⟨hds e he.1, he.2⟩, rfl⟩)
      · exact Or.inr (Or.inl rfl)
    · simp only [tops_cons, tops_append, tops_map_markPiece, startPiece, bottoms_cons,
        bottoms_append, bottoms_map_markPiece, stopPiece, ht, hb, tops_nil, bottoms_nil,
        List.append_nil, List.cons_append, List.cons.injEq, true_and]
      rw [← List.append_assoc, ← starBefore_append, heq, ← List.append_assoc (starAfter _),
        ← starAfter_append, sep_cons_starAfter_append]

theorem primrec_starBefore [Primcodable α] : Primrec (starBefore : List α → List (Marked α)) :=
  Primrec.list_flatMap Primrec.id
    (Primrec.list_cons.comp (Primrec.const sep)
      (Primrec.list_cons.comp (Marked.primrec_letter.comp Primrec.snd)
        (Primrec.const []))).to₂

theorem primrec_starAfter [Primcodable α] : Primrec (starAfter : List α → List (Marked α)) :=
  Primrec.list_flatMap Primrec.id
    (Primrec.list_cons.comp (Marked.primrec_letter.comp Primrec.snd)
      (Primrec.const [sep])).to₂

theorem primrec_toPCP [Primcodable α] :
    Primrec (toPCP : MInstance α → List (Domino (Marked α))) := by
  have hstart : Primrec (startPiece : Domino α → Domino (Marked α)) :=
    Domino.primrec₂_mk.comp
      (Primrec.list_cons.comp (Primrec.const start) (primrec_starBefore.comp Domino.primrec_top))
      (Primrec.list_cons.comp (Primrec.const start)
        (Primrec.list_cons.comp (Primrec.const sep)
          (primrec_starAfter.comp Domino.primrec_bottom)))
  have hmark : Primrec (markPiece : Domino α → Domino (Marked α)) :=
    Domino.primrec₂_mk.comp (primrec_starBefore.comp Domino.primrec_top)
      (primrec_starAfter.comp Domino.primrec_bottom)
  have hpos : PrimrecPred fun d : Domino α => 0 < d.top.length + d.bottom.length :=
    Primrec.nat_lt.comp (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.list_length.comp Domino.primrec_top)
        (Primrec.list_length.comp Domino.primrec_bottom))
  have hfilter : Primrec fun I : MInstance α =>
      I.dominoes.filter fun d => 0 < d.top.length + d.bottom.length :=
    (Primrec.listFilter hpos).comp MInstance.primrec_dominoes
  exact Primrec.list_cons.comp (hstart.comp MInstance.primrec_start)
    (Primrec.list_cons.comp (Primrec.const stopPiece)
      (Primrec.list_map hfilter (hmark.comp Primrec.snd).to₂))

/-- MPCP reduces to PCP by a computable many-one reduction. -/
theorem mSolvable_manyOneReducible [Primcodable α] :
    (MInstance.Solvable : MInstance α → Prop) ≤₀ (Solvable : List (Domino (Marked α)) → Prop) :=
  ⟨toPCP, primrec_toPCP.to_comp, fun I => (solvable_toPCP_iff I).symm⟩

end Cslib.PostCorrespondence
