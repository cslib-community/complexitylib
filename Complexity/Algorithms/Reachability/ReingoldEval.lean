/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Reingold

/-!
# Evaluating Reingold's rotation maps in place

The rotation map of the `ℓ`-th graph `G_ℓ` of Reingold's transformation can be evaluated with
a constant number of labels of extra memory per level, as in the proof of
[Reingold, Lemma 3.4][Reingold2008]. Reingold's step takes the eighth power of `G ⓩ H` and keeps
sixteen labels of `H` in a label of `G_ℓ`; the step here takes the square and keeps four. A
vertex of `G_m` is a vertex `v` of `G` followed by `m` labels `r₀, …, r_{m-1}`
(`Cslib.IteratedProd.toList`), and its rotation along a label `a` changes these
registers in place: a step of `G_m = ((G_{m-1} ⓩ H) ^ 2).relabel e.symm` is a step of `H` from the
label `r_{m-1}`, a recursive rotation of `G_{m-1}`, and a step of `H`, twice, and the four labels of
`H` it uses and produces are stored in `a` itself, which a fixed permutation of these four labels
finally turns into the label at the far end (`reingoldStep_rot`).

`Cslib.RotationMap.reingoldEvalStep` runs this recursion with an explicit stack. A state holds the
vertex `v` of `G`, the labels `r_{m-1}, …, r₀` below the current level, and a stack of frames, one
per level being evaluated, each with a program counter (`Cslib.RotationMap.ReingoldPc`) and its
own label; the level of the top frame is the number of labels below it. Every step is a step of
`H` on two labels, a push or a pop, or a step of `G` on the vertex and the lowest label, so the
memory is the vertex of `G` and `O(1)` labels and a program counter for each of the `ℓ` levels.
From a frame for level `m` at the top, the evaluation reaches the rotated registers and the label
at the far end, the frame popped (`exists_iterate_reingoldEvalStep`).

## Main definitions

* `Cslib.IteratedProd.toList`: the vertex of `G` and the labels of a vertex of
  `G_m`.
* `Cslib.RotationMap.reingoldHStep`, `Cslib.RotationMap.reingoldFinish`: the steps of `H` and
  the final permutation of a step of the transformation, on the labels.
* `Cslib.RotationMap.ReingoldPc`, `Cslib.RotationMap.ReingoldEvalState`,
  `Cslib.RotationMap.reingoldEvalStep`: the evaluation with an explicit stack.
* `Cslib.RotationMap.ReingoldEvalState.mapVertex`: renaming the vertex of the original graph in
  a state of the evaluation.
* `Cslib.RotationMap.ReingoldEvalState.atRoot`: whether the next step is a step of the original
  graph.

## Main results

* `Cslib.RotationMap.reingoldStep_rot`: a step of the transformation on the registers.
* `Cslib.RotationMap.exists_iterate_reingoldEvalStep`: the evaluation computes the rotation map
  of `G_m`.
* `Cslib.RotationMap.reingoldEvalStep_congr`, `Cslib.RotationMap.reingoldEvalStep_mapVertex`:
  a step uses the rotation map of the original graph only at a step of the original graph, and
  commutes with renaming the vertices of the original graph.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
-/

@[expose] public section

namespace Cslib.RotationMap

universe u


variable {B : Type u} {E : Type*} (H : RotationMap B E) (e : B ≃ (Fin 2 → E × E))

/-- The program counter of a frame: the four steps of `H` (`zig₀`, `zag₀`, `zig₁`, `zag₁`), the
two recursive rotations between them (`call₀`, `call₁`) and the final permutation (`finish`). -/
inductive ReingoldPc where
  /-- The first step of `H`, before the first rotation of the level below. -/
  | zig₀
  /-- The first rotation of the level below. -/
  | call₀
  /-- The second step of `H`, after the first rotation of the level below. -/
  | zag₀
  /-- The third step of `H`, before the second rotation of the level below. -/
  | zig₁
  /-- The second rotation of the level below. -/
  | call₁
  /-- The fourth step of `H`, after the second rotation of the level below. -/
  | zag₁
  /-- The final permutation of the labels of `H`. -/
  | finish
  deriving DecidableEq

/-- There are finitely many program counters. -/
instance : Fintype ReingoldPc where
  elems := {.zig₀, .call₀, .zag₀, .zig₁, .call₁, .zag₁, .finish}
  complete x := by cases x <;> simp

/-- **The steps of `H`** on the label `b` below a frame and the label `a` of the frame, which
packs the four labels `e a = ![(i₀, j₀), (i₁, j₁)]` of `H` used by a step of the transformation:
each takes the step of `H` from `b` along one of them and stores the label at the far end in its
place. Other program counters leave the labels unchanged. -/
def reingoldHStep : ReingoldPc → B × B → B × B
  | .zig₀, (b, a) =>
    ((H.rot (b, (e a 0).1)).1, e.symm ![((H.rot (b, (e a 0).1)).2, (e a 0).2), e a 1])
  | .zag₀, (b, a) =>
    ((H.rot (b, (e a 0).2)).1, e.symm ![((e a 0).1, (H.rot (b, (e a 0).2)).2), e a 1])
  | .zig₁, (b, a) =>
    ((H.rot (b, (e a 1).1)).1, e.symm ![e a 0, ((H.rot (b, (e a 1).1)).2, (e a 1).2)])
  | .zag₁, (b, a) =>
    ((H.rot (b, (e a 1).2)).1, e.symm ![e a 0, ((e a 1).1, (H.rot (b, (e a 1).2)).2)])
  | _, p => p

/-- **The final permutation**: the labels `![(i₀', j₀'), (i₁', j₁')]` produced by the steps of `H`
become the label `![(j₁', i₁'), (j₀', i₀')]` at the far end of the step of the transformation. -/
def reingoldFinish (a : B) : B :=
  e.symm ![((e a 1).2, (e a 1).1), ((e a 0).2, (e a 0).1)]

/-- **A step of the transformation on the registers**, as in the proof of
[Reingold, Lemma 3.4][Reingold2008] (with the square instead of the eighth power): the
rotation of `((G ⓩ H) ^ 2).relabel e.symm` at the vertex `(y, c)` along the label `a` is a step of
`H` from `c`, a rotation of `G` at `y`, two steps of `H`, a rotation of `G` and a step of `H`, with
the labels of `H` kept in `a`, followed by the final permutation of `a`. -/
theorem reingoldStep_rot {V : Type*} (G : RotationMap V B) (y : V) (c a : B) :
    (reingoldStep H e G).rot ((y, c), a) =
      let s₁ := reingoldHStep H e .zig₀ (c, a)
      let r₁ := G.rot (y, s₁.1)
      let s₂ := reingoldHStep H e .zag₀ (r₁.2, s₁.2)
      let s₃ := reingoldHStep H e .zig₁ (s₂.1, s₂.2)
      let r₂ := G.rot (r₁.1, s₃.1)
      let s₄ := reingoldHStep H e .zag₁ (r₂.2, s₃.2)
      ((r₂.1, s₄.1), reingoldFinish e s₄.2) := by
  simp only [reingoldStep, rot_relabel, reingoldHStep, reingoldFinish, Equiv.apply_symm_apply]
  change Prod.map id e.symm (powRot (G.zigzag H).rot 2 ((y, c), e.symm.symm a)) = _
  simp only [powRot, Equiv.symm_symm, zigzagRot, Fin.tail, Prod.map_apply, id_eq]
  refine Prod.ext rfl (congrArg e.symm (funext fun i ↦ ?_))
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.snoc]

/-- The memory of the evaluation: the vertex of the original graph, the labels below the current
level, the innermost first, and the stack of frames, the innermost first, each with its program
counter and its label. -/
structure ReingoldEvalState (V B : Type*) where
  /-- The vertex of the original graph. -/
  vertex : V
  /-- The labels below the current level, the innermost first. -/
  lower : List B
  /-- The frames of the levels being evaluated, the innermost first. -/
  frames : List (ReingoldPc × B)

/-- **A step of the evaluation** of the rotation maps of the transformation, with `rotG` the
rotation map of the original graph. The level of the top frame is the number of labels below it,
and the label `b` just below it is its last coordinate. A step of `H` acts on `b` and the label of
the frame; a rotation of the level below is a step of `rotG` on the vertex and `b` at level `1`,
and otherwise pushes a frame for the level below with the label `b`; the final permutation pops the
frame and puts its label below the frame of the level above. -/
def reingoldEvalStep {V : Type*} (rotG : V × B → V × B) :
    ReingoldEvalState V B → ReingoldEvalState V B
  | ⟨v, b :: l, (pc, a) :: rest⟩ =>
    match pc with
    | .call₀ =>
      if l = [] then ⟨(rotG (v, b)).1, [(rotG (v, b)).2], (.zag₀, a) :: rest⟩
      else ⟨v, l, (.zig₀, b) :: (.zag₀, a) :: rest⟩
    | .call₁ =>
      if l = [] then ⟨(rotG (v, b)).1, [(rotG (v, b)).2], (.zag₁, a) :: rest⟩
      else ⟨v, l, (.zig₀, b) :: (.zag₁, a) :: rest⟩
    | .finish => ⟨v, reingoldFinish e a :: b :: l, rest⟩
    | .zig₀ => ⟨v, (reingoldHStep H e .zig₀ (b, a)).1 :: l,
        (.call₀, (reingoldHStep H e .zig₀ (b, a)).2) :: rest⟩
    | .zag₀ => ⟨v, (reingoldHStep H e .zag₀ (b, a)).1 :: l,
        (.zig₁, (reingoldHStep H e .zag₀ (b, a)).2) :: rest⟩
    | .zig₁ => ⟨v, (reingoldHStep H e .zig₁ (b, a)).1 :: l,
        (.call₁, (reingoldHStep H e .zig₁ (b, a)).2) :: rest⟩
    | .zag₁ => ⟨v, (reingoldHStep H e .zag₁ (b, a)).1 :: l,
        (.finish, (reingoldHStep H e .zag₁ (b, a)).2) :: rest⟩
  | s => s

namespace ReingoldEvalState

variable {V W : Type*}

/-- Rename the vertex of the original graph. -/
def mapVertex (φ : V → W) (s : ReingoldEvalState V B) : ReingoldEvalState W B :=
  ⟨φ s.vertex, s.lower, s.frames⟩

/-- Whether the next step of the evaluation is a step of the original graph: a rotation of the
level below at level `1`. -/
def atRoot (s : ReingoldEvalState V B) : Bool :=
  match s.lower, s.frames with
  | [_], (.call₀, _) :: _ => true
  | [_], (.call₁, _) :: _ => true
  | _, _ => false

end ReingoldEvalState

/-- A step of the evaluation depends on the rotation map of the original graph only at a step of
the original graph, and there only at the vertex and the label below the frame. -/
theorem reingoldEvalStep_congr {V : Type*} {rotG rotG' : V × B → V × B}
    {s : ReingoldEvalState V B}
    (h : s.atRoot = true → ∀ b, s.lower = [b] → rotG (s.vertex, b) = rotG' (s.vertex, b)) :
    reingoldEvalStep H e rotG s = reingoldEvalStep H e rotG' s := by
  obtain ⟨v, _ | ⟨b, _ | ⟨b', l⟩⟩, _ | ⟨⟨pc, a⟩, rest⟩⟩ := s
  all_goals first
    | rfl
    | (cases pc <;> simp_all [reingoldEvalStep, ReingoldEvalState.atRoot])

/-- **Renaming the vertices** commutes with the evaluation, when the rotation maps agree through the
renaming. -/
theorem reingoldEvalStep_mapVertex {V W : Type*} (φ : V → W) {rotG : V × B → V × B}
    {rotG' : W × B → W × B} (h : ∀ v b, rotG' (φ v, b) = Prod.map φ id (rotG (v, b)))
    (s : ReingoldEvalState V B) :
    reingoldEvalStep H e rotG' (s.mapVertex φ) = (reingoldEvalStep H e rotG s).mapVertex φ := by
  obtain ⟨v, _ | ⟨b, l⟩, _ | ⟨⟨pc, a⟩, rest⟩⟩ := s
  all_goals try rfl
  cases pc <;> by_cases hl : l = [] <;>
    simp [reingoldEvalStep, ReingoldEvalState.mapVertex, h, hl]

/-- Renaming the vertices commutes with runs of the evaluation. -/
theorem iterate_reingoldEvalStep_mapVertex {V W : Type*} (φ : V → W) {rotG : V × B → V × B}
    {rotG' : W × B → W × B} (h : ∀ v b, rotG' (φ v, b) = Prod.map φ id (rotG (v, b)))
    (N : ℕ) (s : ReingoldEvalState V B) :
    (reingoldEvalStep H e rotG')^[N] (s.mapVertex φ) =
      ((reingoldEvalStep H e rotG)^[N] s).mapVertex φ := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      reingoldEvalStep_mapVertex H e φ h, ih]

/-- A step of the evaluation keeps the total number of labels below and in the frames. -/
theorem length_lower_add_length_frames_reingoldEvalStep {V : Type*} (rotG : V × B → V × B)
    (s : ReingoldEvalState V B) :
    (reingoldEvalStep H e rotG s).lower.length + (reingoldEvalStep H e rotG s).frames.length =
      s.lower.length + s.frames.length := by
  obtain ⟨v, _ | ⟨b, l⟩, _ | ⟨⟨pc, a⟩, rest⟩⟩ := s
  all_goals try rfl
  cases pc <;> by_cases hl : l = [] <;>
    simp only [reingoldEvalStep, hl, ↓reduceIte, List.length_cons, List.length_nil] <;> omega

/-- A step of the evaluation keeps a property of the vertex that the steps of the original graph
keep. -/
theorem reingoldEvalStep_vertex {V : Type*} {rotG : V × B → V × B} {P : V → Prop}
    (hP : ∀ v b, P v → P (rotG (v, b)).1) {s : ReingoldEvalState V B} (hs : P s.vertex) :
    P (reingoldEvalStep H e rotG s).vertex := by
  obtain ⟨v, _ | ⟨b, l⟩, _ | ⟨⟨pc, a⟩, rest⟩⟩ := s
  all_goals try exact hs
  cases pc <;> by_cases hl : l = [] <;>
    simp only [reingoldEvalStep, hl, ite_true, ite_false] <;>
    first | exact hs | exact hP _ _ hs

section Correct

variable {V : Type u} (G : RotationMap V B)

/-- The evaluation of level `k + 1` from the rotations of level `k`. -/
private theorem exists_iterate_zig₀_of_call (k : ℕ)
    (hcall₀ : ∀ (y : IteratedProd V B k) (c a : B) (rest : List (ReingoldPc × B)),
      ∃ N, (reingoldEvalStep H e G.rot)^[N]
          ⟨(y.toList).1, c :: (y.toList).2, (.call₀, a) :: rest⟩ =
        ⟨(((reingold H e G k).rot (y, c)).1.toList).1,
          ((reingold H e G k).rot (y, c)).2 :: (((reingold H e G k).rot (y, c)).1.toList).2,
          (.zag₀, a) :: rest⟩)
    (hcall₁ : ∀ (y : IteratedProd V B k) (c a : B) (rest : List (ReingoldPc × B)),
      ∃ N, (reingoldEvalStep H e G.rot)^[N]
          ⟨(y.toList).1, c :: (y.toList).2, (.call₁, a) :: rest⟩ =
        ⟨(((reingold H e G k).rot (y, c)).1.toList).1,
          ((reingold H e G k).rot (y, c)).2 :: (((reingold H e G k).rot (y, c)).1.toList).2,
          (.zag₁, a) :: rest⟩)
    (x : IteratedProd V B (k + 1)) (a : B) (rest : List (ReingoldPc × B)) :
    ∃ N, (reingoldEvalStep H e G.rot)^[N]
        ⟨(x.toList).1, (x.toList).2, (.zig₀, a) :: rest⟩ =
      ⟨(((reingold H e G (k + 1)).rot (x, a)).1.toList).1,
        ((reingold H e G (k + 1)).rot (x, a)).2 ::
          (((reingold H e G (k + 1)).rot (x, a)).1.toList).2, rest⟩ := by
  obtain ⟨y, c⟩ := x
  set s₁ := reingoldHStep H e .zig₀ (c, a)
  set r₁ := (reingold H e G k).rot (y, s₁.1)
  set s₂ := reingoldHStep H e .zag₀ (r₁.2, s₁.2)
  set s₃ := reingoldHStep H e .zig₁ (s₂.1, s₂.2)
  set r₂ := (reingold H e G k).rot (r₁.1, s₃.1)
  set s₄ := reingoldHStep H e .zag₁ (r₂.2, s₃.2)
  obtain ⟨N₁, hN₁⟩ := hcall₀ y s₁.1 s₁.2 rest
  obtain ⟨N₂, hN₂⟩ := hcall₁ r₁.1 s₃.1 s₃.2 rest
  have e₁ : reingoldEvalStep H e G.rot ⟨(y.toList).1, c :: (y.toList).2, (.zig₀, a) :: rest⟩ =
      ⟨(y.toList).1, s₁.1 :: (y.toList).2, (.call₀, s₁.2) :: rest⟩ := rfl
  have e₂ : reingoldEvalStep H e G.rot
      ⟨(r₁.1.toList).1, r₁.2 :: (r₁.1.toList).2, (.zag₀, s₁.2) :: rest⟩ =
      ⟨(r₁.1.toList).1, s₂.1 :: (r₁.1.toList).2, (.zig₁, s₂.2) :: rest⟩ := rfl
  have e₃ : reingoldEvalStep H e G.rot
      ⟨(r₁.1.toList).1, s₂.1 :: (r₁.1.toList).2, (.zig₁, s₂.2) :: rest⟩ =
      ⟨(r₁.1.toList).1, s₃.1 :: (r₁.1.toList).2, (.call₁, s₃.2) :: rest⟩ := rfl
  have e₄ : reingoldEvalStep H e G.rot
      ⟨(r₂.1.toList).1, r₂.2 :: (r₂.1.toList).2, (.zag₁, s₃.2) :: rest⟩ =
      ⟨(r₂.1.toList).1, s₄.1 :: (r₂.1.toList).2, (.finish, s₄.2) :: rest⟩ := rfl
  have e₅ : reingoldEvalStep H e G.rot
      ⟨(r₂.1.toList).1, s₄.1 :: (r₂.1.toList).2, (.finish, s₄.2) :: rest⟩ =
      ⟨(r₂.1.toList).1, reingoldFinish e s₄.2 :: s₄.1 :: (r₂.1.toList).2, rest⟩ := rfl
  have hrot : (reingold H e G (k + 1)).rot ((y, c), a) = ((r₂.1, s₄.1), reingoldFinish e s₄.2) :=
    reingoldStep_rot H e (reingold H e G k) y c a
  refine ⟨1 + 1 + N₂ + 1 + 1 + N₁ + 1, ?_⟩
  simp only [Function.iterate_add_apply, Function.iterate_one, IteratedProd.toList_succ]
  rw [e₁, hN₁, e₂, e₃, hN₂, e₄, e₅, hrot]
  rfl

/-- A rotation of level `k + 1` pushes a frame for level `k + 1` and evaluates that level. -/
private theorem exists_iterate_call_succ (k : ℕ)
    (heval : ∀ (x : IteratedProd V B (k + 1)) (a : B) (rest : List (ReingoldPc × B)),
      ∃ N, (reingoldEvalStep H e G.rot)^[N]
          ⟨(x.toList).1, (x.toList).2, (.zig₀, a) :: rest⟩ =
        ⟨(((reingold H e G (k + 1)).rot (x, a)).1.toList).1,
          ((reingold H e G (k + 1)).rot (x, a)).2 ::
            (((reingold H e G (k + 1)).rot (x, a)).1.toList).2, rest⟩)
    (pc next : ReingoldPc) (hpc : pc = .call₀ ∧ next = .zag₀ ∨ pc = .call₁ ∧ next = .zag₁)
    (y : IteratedProd V B (k + 1)) (c a : B) (rest : List (ReingoldPc × B)) :
    ∃ N, (reingoldEvalStep H e G.rot)^[N]
        ⟨(y.toList).1, c :: (y.toList).2, (pc, a) :: rest⟩ =
      ⟨(((reingold H e G (k + 1)).rot (y, c)).1.toList).1,
        ((reingold H e G (k + 1)).rot (y, c)).2 ::
          (((reingold H e G (k + 1)).rot (y, c)).1.toList).2, (next, a) :: rest⟩ := by
  obtain ⟨N, hN⟩ := heval y c ((next, a) :: rest)
  refine ⟨N + 1, ?_⟩
  rw [Function.iterate_succ_apply]
  have hne : (y.toList).2 ≠ [] := by
    rw [ne_eq, ← List.length_eq_zero_iff, IteratedProd.length_toList]
    exact Nat.succ_ne_zero k
  have hpush : reingoldEvalStep H e G.rot ⟨(y.toList).1, c :: (y.toList).2, (pc, a) :: rest⟩ =
      ⟨(y.toList).1, (y.toList).2, (.zig₀, c) :: (next, a) :: rest⟩ := by
    rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [reingoldEvalStep, hne]
  rw [hpush, hN]

/-- **The rotations of the level below and the evaluation of a level.** For every `k`: a frame at
a rotation of level `k` (program counter `call₀` or `call₁`), above the registers of a vertex `y` of
`G_k` and the label `c`, reaches the registers of the rotation of `G_k` at `(y, c)`, with the frame
moved to the next step; and a frame for level `k + 1`, freshly pushed with the label `a` above the
registers of a vertex `x`, reaches the registers of the rotation of `G_{k+1}` at `(x, a)` with the
label at the far end below the frames, the frame popped. -/
private theorem exists_iterate_call (k : ℕ) :
    (∀ (y : IteratedProd V B k) (c a : B) (rest : List (ReingoldPc × B)),
      ∃ N, (reingoldEvalStep H e G.rot)^[N]
          ⟨(y.toList).1, c :: (y.toList).2, (.call₀, a) :: rest⟩ =
        ⟨(((reingold H e G k).rot (y, c)).1.toList).1,
          ((reingold H e G k).rot (y, c)).2 :: (((reingold H e G k).rot (y, c)).1.toList).2,
          (.zag₀, a) :: rest⟩) ∧
    (∀ (y : IteratedProd V B k) (c a : B) (rest : List (ReingoldPc × B)),
      ∃ N, (reingoldEvalStep H e G.rot)^[N]
          ⟨(y.toList).1, c :: (y.toList).2, (.call₁, a) :: rest⟩ =
        ⟨(((reingold H e G k).rot (y, c)).1.toList).1,
          ((reingold H e G k).rot (y, c)).2 :: (((reingold H e G k).rot (y, c)).1.toList).2,
          (.zag₁, a) :: rest⟩) ∧
    (∀ (x : IteratedProd V B (k + 1)) (a : B) (rest : List (ReingoldPc × B)),
      ∃ N, (reingoldEvalStep H e G.rot)^[N]
          ⟨(x.toList).1, (x.toList).2, (.zig₀, a) :: rest⟩ =
        ⟨(((reingold H e G (k + 1)).rot (x, a)).1.toList).1,
          ((reingold H e G (k + 1)).rot (x, a)).2 ::
            (((reingold H e G (k + 1)).rot (x, a)).1.toList).2, rest⟩) := by
  induction k with
  | zero =>
    -- a rotation of level `0` is one step of `G`
    refine ⟨fun _ _ _ _ ↦ ⟨1, rfl⟩, fun _ _ _ _ ↦ ⟨1, rfl⟩, ?_⟩
    exact exists_iterate_zig₀_of_call H e G 0
      (fun _ _ _ _ ↦ ⟨1, rfl⟩) (fun _ _ _ _ ↦ ⟨1, rfl⟩)
  | succ k ih =>
    -- a rotation of level `k + 1` pushes a frame and evaluates the level
    have hcall₀ := exists_iterate_call_succ H e G k ih.2.2 .call₀ .zag₀ (.inl ⟨rfl, rfl⟩)
    have hcall₁ := exists_iterate_call_succ H e G k ih.2.2 .call₁ .zag₁ (.inr ⟨rfl, rfl⟩)
    exact ⟨hcall₀, hcall₁, exists_iterate_zig₀_of_call H e G (k + 1) hcall₀ hcall₁⟩

/-- **The evaluation computes the rotation map**, as in the proof of
[Reingold, Lemma 3.4][Reingold2008]: from a frame for level `m ≥ 1`, freshly pushed with the label
`a` above the registers of a vertex `x` of `G_m`, the evaluation reaches the registers of the
rotation `(x', a')` of `G_m` at `(x, a)`, with the label `a'` at the far end below the frames, and
the frame popped. -/
theorem exists_iterate_reingoldEvalStep {m : ℕ} (hm : m ≠ 0) (x : IteratedProd V B m) (a : B)
    (rest : List (ReingoldPc × B)) :
    ∃ N, (reingoldEvalStep H e G.rot)^[N] ⟨(x.toList).1, (x.toList).2, (.zig₀, a) :: rest⟩ =
      ⟨(((reingold H e G m).rot (x, a)).1.toList).1,
        ((reingold H e G m).rot (x, a)).2 :: (((reingold H e G m).rot (x, a)).1.toList).2,
        rest⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  exact (exists_iterate_call H e G k).2.2 x a rest

end Correct

end Cslib.RotationMap
