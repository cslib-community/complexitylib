/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.LabelCover
public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Words
import CslibFrontier.Computability.PCP.Encoded.Size

/-!
# Polynomial-time membership for satisfiable unique games

For each fixed finite alphabet `Fin L`, label propagation
(`Cslib.Complexity.UniqueGames.Propagation.solve`) runs in polynomial time on the multi-tape Turing
machine model under the graph encoding `Graph.encoding (encPi (encFinEnum (Fin L)))` of
`Cslib.Complexity.UniqueGamesConjecture`.

To avoid building closures of type `ℕ → Fin L` at runtime, we evaluate a table-reading check
directly on `(Propagation.run (List.finRange L) g).table`, show it agrees pointwise with
`(Propagation.solve (List.finRange L) g).isSome`, and combine it with
`Propagation.solvedBy_gapUniqueGames_one` and `Propagation.solve_isSome_iff`.

For `L = 0`, `Fin 0` is empty, so no labelling `ℕ → Fin 0` exists: every unique game vacuously
has `unsatVal = 0` and is a yes-instance of `GapUniqueGames (Fin 0) 1 s` (with no no-instances),
while `{g : Graph (Fin 0 → Fin 0) | IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable}`
is empty. Both belong to `PromiseP` / `P`.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.computableInPolyTime_isSome_solve`: for every
  `[NeZero L]`, `(solve (List.finRange L) ·).isSome` is computable in polynomial time under
  `Graph.encoding (encPi (encFinEnum (Fin L)))`.
* `Cslib.Complexity.gapUniqueGames_one_mem_PromiseP_of_pos`: for `0 < L` and every `s : ℝ`,
  `GapUniqueGames (Fin L) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin L))))`.
* `Cslib.Complexity.gapUniqueGames_zero_mem_PromiseP`: explicit characterization and `PromiseP`
  membership for `L = 0`.
* `Cslib.Complexity.gapUniqueGames_one_mem_PromiseP`: unconditional `PromiseP` membership for all
  `L : ℕ` and `s : ℝ`.
* `Cslib.Complexity.isUniqueGame_mem_P`, `Cslib.Complexity.satisfiable_uniqueGame_mem_P`: `P`
  membership for recognizing unique games and deciding their satisfiability.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

section PolyTime

open ComputableTidilyInPolyTime

private noncomputable def encUGFn (L : ℕ) : (Fin L → Fin L) ↪ List Bool :=
  encPi (encFinEnum (Fin L))

private noncomputable abbrev encUGGraph (L : ℕ) : Graph (Fin L → Fin L) ↪ List Bool :=
  Graph.encoding (encUGFn L)

private noncomputable abbrev encUGEdge (L : ℕ) : Edge (Fin L → Fin L) ↪ List Bool :=
  Edge.encoding (encUGFn L)

private noncomputable abbrev encUGTable (L : ℕ) : List (Option (Fin L → Fin L)) ↪ List Bool :=
  encList (encOption (encUGFn L))

private noncomputable def encUGCand (L : ℕ) : (Fin L → Bool) ↪ List Bool :=
  encPi encBool

private abbrev encUGVerts : List ℕ ↪ List Bool :=
  encList encUnary

private noncomputable def encUGState (L : ℕ) : State (Fin L) ↪ List Bool :=
  (⟨fun S => ((S.table, S.cand), (S.stack, S.comp)), fun S₁ S₂ h => by
    cases S₁; cases S₂; simp_all⟩ : State (Fin L) ↪ _).trans
    (encPair (encPair (encUGTable L) (encUGCand L)) (encPair encUGVerts encUGVerts))

private theorem encUGState_apply (L : ℕ) (S : State (Fin L)) :
    encUGState L S =
      encPair (encPair (encUGTable L) (encUGCand L)) (encPair encUGVerts encUGVerts)
        ((S.table, S.cand), (S.stack, S.comp)) :=
  rfl

private theorem poly_state_unpack (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun S : State (Fin L) => ((S.table, S.cand), (S.stack, S.comp)))
      (encUGState L)
      (encPair (encPair (encUGTable L) (encUGCand L)) (encPair encUGVerts encUGVerts)) :=
  .of_eq fun _ => rfl

private theorem poly_state_table (L : ℕ) :
    ComputableTidilyInPolyTime (fun S : State (Fin L) => S.table) (encUGState L) (encUGTable L) :=
  (poly_state_unpack L).fst'.fst'

private theorem poly_state_cand (L : ℕ) :
    ComputableTidilyInPolyTime (fun S : State (Fin L) => S.cand) (encUGState L) (encUGCand L) :=
  (poly_state_unpack L).fst'.snd'

private theorem poly_state_stack (L : ℕ) :
    ComputableTidilyInPolyTime (fun S : State (Fin L) => S.stack) (encUGState L) encUGVerts :=
  (poly_state_unpack L).snd'.fst'

private theorem poly_state_comp (L : ℕ) :
    ComputableTidilyInPolyTime (fun S : State (Fin L) => S.comp) (encUGState L) encUGVerts :=
  (poly_state_unpack L).snd'.snd'

private theorem poly_state_mk {L : ℕ} {γ : Type} {encIn : γ ↪ List Bool}
    {table : γ → List (Option (Fin L → Fin L))} {cand : γ → Fin L → Bool}
    {stack comp : γ → List ℕ}
    (htable : ComputableTidilyInPolyTime table encIn (encUGTable L))
    (hcand : ComputableTidilyInPolyTime cand encIn (encUGCand L))
    (hstack : ComputableTidilyInPolyTime stack encIn encUGVerts)
    (hcomp : ComputableTidilyInPolyTime comp encIn encUGVerts) :
    ComputableTidilyInPolyTime (fun x => State.mk (table x) (cand x) (stack x) (comp x))
      encIn (encUGState L) :=
  ((htable.prod hcand).prod (hstack.prod hcomp)).of_enc_eq fun _ => rfl

private theorem poly_graph_vertices (L : ℕ) :
    ComputableTidilyInPolyTime (fun g : Graph (Fin L → Fin L) => g.vertices)
      (encUGGraph L) encUnary :=
  (Graph.isPolyTime_vertices (.id' (encIn := encUGGraph L))).tidy

private theorem poly_graph_edges (L : ℕ) :
    ComputableTidilyInPolyTime (fun g : Graph (Fin L → Fin L) => g.edges)
      (encUGGraph L) (encList (encUGEdge L)) :=
  (Graph.isPolyTime_edges (.id' (encIn := encUGGraph L))).tidy

private theorem poly_edge_src (L : ℕ) :
    ComputableTidilyInPolyTime (fun e : Edge (Fin L → Fin L) => e.src) (encUGEdge L) encUnary :=
  (Edge.isPolyTime_src (.id' (encIn := encUGEdge L))).tidy

private theorem poly_edge_dst (L : ℕ) :
    ComputableTidilyInPolyTime (fun e : Edge (Fin L → Fin L) => e.dst) (encUGEdge L) encUnary :=
  (Edge.isPolyTime_dst (.id' (encIn := encUGEdge L))).tidy

private theorem poly_edge_constraint (L : ℕ) :
    ComputableTidilyInPolyTime (fun e : Edge (Fin L → Fin L) => e.constraint)
      (encUGEdge L) (encUGFn L) :=
  (Edge.isPolyTime_constraint (.id' (encIn := encUGEdge L))).tidy

private theorem poly_listSet {γ α : Type} {encIn : γ ↪ List Bool} (encA : α ↪ List Bool)
    {list : γ → List α} {idx : γ → ℕ} {val : γ → α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hidx : ComputableTidilyInPolyTime idx encIn encUnary)
    (hval : ComputableTidilyInPolyTime val encIn encA) :
    ComputableTidilyInPolyTime (fun x => (list x).set (idx x) (val x)) encIn (encList encA) := by
  simp_rw [List.set_eq_take_append_cons_drop]
  exact ite_decide
    (unary_lt' hidx ((length_list encA).comp hlist))
    (listAppend'
      (listTakeWithInput hlist hidx)
      (cons' hval (listDropWithInput hlist (unary_add.comp (hidx.prod (const 1))))))
    hlist

private lemma optBound_spec (L : ℕ) (o : Option (Fin L → Fin L)) :
    (encOption (encUGFn L) o).length ≤ L * (2 * L + 1) + 1 := by
  cases o with
  | none => simp [encOption_none]
  | some f =>
    have hpi : (encUGFn L f).length ≤ Fintype.card (Fin L) * (2 * L + 1) :=
      length_encPi_le (encFinEnum (Fin L)) f fun i =>
        (length_encFinEnum_lt (f i)).le.trans (by simp)
    simp only [Fintype.card_fin] at hpi
    simp only [encUGFn, encOption_some, List.length_cons] at hpi ⊢
    omega

private lemma candBound_spec (L : ℕ) (c : Fin L → Bool) :
    (encUGCand L c).length ≤ 3 * L := by
  have hpi : (encUGCand L c).length ≤ Fintype.card (Fin L) * (2 * 1 + 1) :=
    length_encPi_le encBool c fun i => by simp [encBool_apply]
  simp only [Fintype.card_fin, encUGCand] at hpi ⊢
  omega

private lemma length_encList_replicate_none {α : Type} (n : ℕ) (enc : α ↪ List Bool) :
    (encList (encOption enc) (List.replicate n none)).length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, encList_cons, encOption_none, List.length_append,
      length_frame, List.length_nil, ih]
    omega

private lemma length_encUGState_eq (L : ℕ) (S : State (Fin L)) :
    (encUGState L S).length =
      4 * (encUGTable L S.table).length + 2 * (encUGCand L S.cand).length +
        2 * (encUGVerts S.stack).length + (encUGVerts S.comp).length + 4 := by
  simp only [encUGState_apply, length_encPair]
  omega

private lemma length_encUGTable_le_mul (L : ℕ) (t : List (Option (Fin L → Fin L))) :
    (encUGTable L t).length ≤ t.length * (2 * (L * (2 * L + 1) + 1) + 1) :=
  length_encList_le (encOption (encUGFn L)) t fun o _ => optBound_spec L o

private theorem poly_slots (L : ℕ) :
    ComputableTidilyInPolyTime (slots (C := Fin L → Fin L)) (encUGGraph L) encUnary := by
  unfold slots
  refine foldlWith_of_bounded_growth
    (encP := encBool) (encB := encUnary) (encA := encUGEdge L)
    (par := fun _ => true) (list := fun g => g.edges) (init := fun g => g.vertices)
    (step := fun _ n e => max n (max e.src e.dst + 1))
    (const true) (poly_graph_edges L) (poly_graph_vertices L)
    ?_ (growth := fun g => (encUGGraph L g).length) (.self) fun g n e he => ?_
  · have hn : ComputableTidilyInPolyTime
        (fun q : (Bool × ℕ) × Edge (Fin L → Fin L) => q.1.2)
        (encFoldStep encBool encUnary (encUGEdge L)) encUnary :=
      (fst _ _).snd'
    have he : ComputableTidilyInPolyTime
        (fun q : (Bool × ℕ) × Edge (Fin L → Fin L) => q.2)
        (encFoldStep encBool encUnary (encUGEdge L)) (encUGEdge L) :=
      snd _ _
    exact unary_max.comp
      (hn.prod (unary_add.comp
        ((unary_max.comp (((poly_edge_src L).comp he).prod ((poly_edge_dst L).comp he))).prod
          (const 1))))
  · have hmem := SizedListEncoding.length_elem_le (encA := encUGEdge L)
      (encL := encList (encUGEdge L)) g.edges e he
    have hle : (encList (encUGEdge L) g.edges).length ≤ (encUGGraph L g).length := by
      change _ ≤ (encPair encUnary (encList (encUGEdge L)) (g.vertices, g.edges)).length
      rw [length_encPair]
      dsimp only
      omega
    have hlen' : (encUGEdge L e).length =
        (encPair encUnary (encPair encUnary (encUGFn L)) (e.src, e.dst, e.constraint)).length :=
      rfl
    have hend : e.src + 1 ≤ (encUGEdge L e).length ∧ e.dst + 1 ≤ (encUGEdge L e).length := by
      rw [hlen', length_encPair, length_encPair]
      dsimp only
      simp only [encUnary_apply, List.length_replicate]
      omega
    have hmax : max e.src e.dst + 1 ≤ (encUGGraph L g).length := by omega
    simp only [encUnary_apply, List.length_replicate]
    exact max_le (Nat.le_add_right _ _) (hmax.trans (Nat.le_add_left _ _))

private theorem poly_init (L : ℕ) :
    ComputableTidilyInPolyTime (init (α := Fin L)) (encUGGraph L) (encUGState L) := by
  unfold init
  have htab : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) => List.replicate (slots g) (none : Option (Fin L → Fin L)))
      (encUGGraph L) (encUGTable L) :=
    replicate (poly_slots L) (const (none : Option (Fin L → Fin L)))
  exact poly_state_mk htab (const (fun _ => true)) (const []) (const [])

private theorem poly_start (L : ℕ) :
    ComputableTidilyInPolyTime (fun p : State (Fin L) × ℕ => start p.1 p.2)
      (encPair (encUGState L) encUnary) (encUGState L) := by
  unfold start
  have hS : ComputableTidilyInPolyTime (fun p : State (Fin L) × ℕ => p.1)
      (encPair (encUGState L) encUnary) (encUGState L) := fst _ _
  have hs : ComputableTidilyInPolyTime (fun p : State (Fin L) × ℕ => p.2)
      (encPair (encUGState L) encUnary) encUnary := snd _ _
  exact poly_state_mk
    (poly_listSet (encOption (encUGFn L)) ((poly_state_table L).comp hS) hs (const (some id)))
    (const (fun _ => true))
    (cons' hs (const []))
    (const [])

private theorem poly_push (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : (State (Fin L) × ℕ) × (Fin L → Fin L) => push p.1.1 p.1.2 p.2)
      (encPair (encPair (encUGState L) encUnary) (encUGFn L)) (encUGState L) := by
  unfold push
  have hS : ComputableTidilyInPolyTime
      (fun p : (State (Fin L) × ℕ) × (Fin L → Fin L) => p.1.1)
      (encPair (encPair (encUGState L) encUnary) (encUGFn L)) (encUGState L) :=
    (fst _ _).fst'
  have hw : ComputableTidilyInPolyTime
      (fun p : (State (Fin L) × ℕ) × (Fin L → Fin L) => p.1.2)
      (encPair (encPair (encUGState L) encUnary) (encUGFn L)) encUnary :=
    (fst _ _).snd'
  have hf : ComputableTidilyInPolyTime
      (fun p : (State (Fin L) × ℕ) × (Fin L → Fin L) => p.2)
      (encPair (encPair (encUGState L) encUnary) (encUGFn L)) (encUGFn L) :=
    snd _ _
  exact poly_state_mk
    (poly_listSet (encOption (encUGFn L)) ((poly_state_table L).comp hS) hw
      ((optionSome (encUGFn L)).comp hf))
    ((poly_state_cand L).comp hS)
    (cons' hw ((poly_state_stack L).comp hS))
    ((poly_state_comp L).comp hS)

private theorem poly_get (L : ℕ) :
    ComputableTidilyInPolyTime (fun p : State (Fin L) × ℕ => p.1.get p.2)
      (encPair (encUGState L) encUnary) (encOption (encUGFn L)) := by
  unfold State.get
  exact (listGetD (encA := encOption (encUGFn L)) (encL := encUGTable L) none).comp
    (((poly_state_table L).comp (fst _ _)).prod (snd _ _))

private theorem extend_eq_elim (L : ℕ) (S : State (Fin L)) (e : Edge (Fin L → Fin L)) :
    extend (List.finRange L) S e =
      (S.get e.src).elim
        ((S.get e.dst).elim S fun h => push S e.src (preimage (List.finRange L) e.constraint ∘ h))
        (fun f => (S.get e.dst).elim (push S e.dst (e.constraint ∘ f)) fun _ => S) := by
  unfold extend
  cases S.get e.src <;> cases S.get e.dst <;> rfl

private theorem prune_eq_elim (L : ℕ) (S : State (Fin L)) (e : Edge (Fin L → Fin L)) :
    prune S e =
      (S.get e.src).elim S fun f =>
        (S.get e.dst).elim S fun h =>
          State.mk S.table (fun a => S.cand a && decide (e.constraint (f a) = h a))
            S.stack S.comp := by
  unfold prune
  cases S.get e.src <;> cases S.get e.dst <;> rfl

private theorem scan_eq_elim {α : Type} [DecidableEq α] (labels : List α)
    (g : Graph (α → α)) (S : State α) :
    scan labels g S =
      S.stack.head?.elim S fun u =>
        (adj g u).foldl (visit labels)
          (State.mk S.table S.cand (S.stack.drop 1) (u :: S.comp)) := by
  unfold scan
  cases S.stack <;> rfl

private theorem step_eq_elim {α : Type} [DecidableEq α] [Inhabited α] (labels : List α)
    (g : Graph (α → α)) (S : State α) (e : Edge (α → α)) :
    step labels g S e =
      (S.get e.src).elim
        (settle labels ((scan labels g)^[slots g] (start S e.src)))
        (fun _ => S) := by
  unfold step
  cases S.get e.src <;> rfl

private theorem poly_se_state (L : ℕ) :
    ComputableTidilyInPolyTime (fun p : State (Fin L) × Edge (Fin L → Fin L) => p.1)
      (encPair (encUGState L) (encUGEdge L)) (encUGState L) := fst _ _

private theorem poly_se_edge (L : ℕ) :
    ComputableTidilyInPolyTime (fun p : State (Fin L) × Edge (Fin L → Fin L) => p.2)
      (encPair (encUGState L) (encUGEdge L)) (encUGEdge L) := snd _ _

private theorem poly_se_get {L : ℕ} (endp : Edge (Fin L → Fin L) → ℕ)
    (hendp : ComputableTidilyInPolyTime endp (encUGEdge L) encUnary) :
    ComputableTidilyInPolyTime (fun p : State (Fin L) × Edge (Fin L → Fin L) => p.1.get (endp p.2))
      (encPair (encUGState L) (encUGEdge L)) (encOption (encUGFn L)) := by
  simpa only [Function.comp_def] using
    (poly_get L).comp ((poly_se_state L).prod (hendp.comp (poly_se_edge L)))

private theorem poly_se1_state (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun q : (State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L) => q.1.1)
      (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGState L) := by
  simpa only [Function.comp_def] using (poly_se_state L).comp (fst _ _)

private theorem poly_se1_edge (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun q : (State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L) => q.1.2)
      (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGEdge L) := by
  simpa only [Function.comp_def] using (poly_se_edge L).comp (fst _ _)

private theorem poly_se1_getDst (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun q : (State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L) => q.1.1.get q.1.2.dst)
      (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encOption (encUGFn L)) := by
  simpa only [Function.comp_def] using
    (poly_se_get Edge.dst (poly_edge_dst L)).comp (fst _ _)

private theorem poly_se1_push_op {L : ℕ} (endp : Edge (Fin L → Fin L) → ℕ)
    (hendp : ComputableTidilyInPolyTime endp (encUGEdge L) encUnary)
    (op : (Fin L → Fin L) → (Fin L → Fin L) → (Fin L → Fin L)) :
    ComputableTidilyInPolyTime
      (fun q : (State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L) =>
        push q.1.1 (endp q.1.2) (op q.1.2.constraint q.2))
      (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGState L) := by
  have hop : ComputableTidilyInPolyTime
      (fun q : (State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L) =>
        op q.1.2.constraint q.2)
      (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGFn L) := by
    simpa only [Function.comp_def] using
      (of_finite (fun r : (Fin L → Fin L) × (Fin L → Fin L) => op r.1 r.2)).comp
        (((poly_edge_constraint L).comp (poly_se1_edge L)).prod (snd _ _))
  simpa only [Function.comp_def] using
    (poly_push L).comp (((poly_se1_state L).prod (hendp.comp (poly_se1_edge L))).prod hop)

private theorem poly_extend_none (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : State (Fin L) × Edge (Fin L → Fin L) =>
        (p.1.get p.2.dst).elim p.1 fun h =>
          push p.1 p.2.src (preimage (List.finRange L) p.2.constraint ∘ h))
      (encPair (encUGState L) (encUGEdge L)) (encUGState L) :=
  optionElimWithInput (poly_se_get Edge.dst (poly_edge_dst L)) (poly_se_state L)
    (poly_se1_push_op Edge.src (poly_edge_src L) fun π h => preimage (List.finRange L) π ∘ h)

private theorem poly_extend_some (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun q : (State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L) =>
        (q.1.1.get q.1.2.dst).elim (push q.1.1 q.1.2.dst (q.1.2.constraint ∘ q.2)) fun _ => q.1.1)
      (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGState L) := by
  have hbody : ComputableTidilyInPolyTime
      (fun r : ((State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L)) × (Fin L → Fin L) =>
        r.1.1.1)
      (encPair (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGFn L))
      (encUGState L) := by
    simpa only [Function.comp_def] using (poly_se1_state L).comp (fst _ _)
  exact optionElimWithInput (poly_se1_getDst L)
    (poly_se1_push_op Edge.dst (poly_edge_dst L) fun π f => π ∘ f) hbody

private theorem poly_extend (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : State (Fin L) × Edge (Fin L → Fin L) => extend (List.finRange L) p.1 p.2)
      (encPair (encUGState L) (encUGEdge L)) (encUGState L) := by
  have heq : (fun p : State (Fin L) × Edge (Fin L → Fin L) => extend (List.finRange L) p.1 p.2) =
      fun p => (p.1.get p.2.src).elim
        ((p.1.get p.2.dst).elim p.1 fun h =>
          push p.1 p.2.src (preimage (List.finRange L) p.2.constraint ∘ h))
        (fun f => (p.1.get p.2.dst).elim (push p.1 p.2.dst (p.2.constraint ∘ f)) fun _ => p.1) := by
    funext p
    exact extend_eq_elim L p.1 p.2
  rw [heq]
  exact optionElimWithInput (poly_se_get Edge.src (poly_edge_src L))
    (poly_extend_none L) (poly_extend_some L)

private theorem poly_state_setCand {γ : Type} {encIn : γ ↪ List Bool} (L : ℕ)
    {s : γ → State (Fin L)} {c : γ → (Fin L → Bool)}
    (hs : ComputableTidilyInPolyTime s encIn (encUGState L))
    (hc : ComputableTidilyInPolyTime c encIn (encUGCand L)) :
    ComputableTidilyInPolyTime
      (fun x => State.mk (s x).table (c x) (s x).stack (s x).comp)
      encIn (encUGState L) :=
  poly_state_mk
    (by simpa only [Function.comp_def] using (poly_state_table L).comp hs)
    hc
    (by simpa only [Function.comp_def] using (poly_state_stack L).comp hs)
    (by simpa only [Function.comp_def] using (poly_state_comp L).comp hs)

private theorem poly_prune_some (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun q : (State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L) =>
        (q.1.1.get q.1.2.dst).elim q.1.1 fun h =>
          State.mk q.1.1.table
            (fun a => q.1.1.cand a && decide (q.1.2.constraint (q.2 a) = h a))
            q.1.1.stack q.1.1.comp)
      (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGState L) := by
  have hbase : ComputableTidilyInPolyTime
      (fun q : ((State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L)) × (Fin L → Fin L) =>
        q.1)
      (encPair (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGFn L))
      (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) :=
    fst _ _
  have hS2 : ComputableTidilyInPolyTime
      (fun q : ((State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L)) × (Fin L → Fin L) =>
        q.1.1.1)
      (encPair (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGFn L))
      (encUGState L) := by
    simpa only [Function.comp_def] using (poly_se1_state L).comp hbase
  have he2 : ComputableTidilyInPolyTime
      (fun q : ((State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L)) × (Fin L → Fin L) =>
        q.1.1.2)
      (encPair (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGFn L))
      (encUGEdge L) := by
    simpa only [Function.comp_def] using (poly_se1_edge L).comp hbase
  have hf2 : ComputableTidilyInPolyTime
      (fun q : ((State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L)) × (Fin L → Fin L) =>
        q.1.2)
      (encPair (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGFn L))
      (encUGFn L) := by
    simpa only [Function.comp_def] using (snd _ _).comp hbase
  have hh2 : ComputableTidilyInPolyTime
      (fun q : ((State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L)) × (Fin L → Fin L) =>
        q.2)
      (encPair (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGFn L))
      (encUGFn L) :=
    snd _ _
  have hcandFin : ComputableTidilyInPolyTime
      (fun r : ((Fin L → Bool) × (Fin L → Fin L)) × ((Fin L → Fin L) × (Fin L → Fin L)) =>
        fun a => r.1.1 a && decide (r.2.1 (r.1.2 a) = r.2.2 a))
      (encPair (encPair (encUGCand L) (encUGFn L)) (encPair (encUGFn L) (encUGFn L)))
      (encUGCand L) :=
    of_finite _
  have hcand : ComputableTidilyInPolyTime
      (fun q : ((State (Fin L) × Edge (Fin L → Fin L)) × (Fin L → Fin L)) × (Fin L → Fin L) =>
        fun a => q.1.1.1.cand a && decide (q.1.1.2.constraint (q.1.2 a) = q.2 a))
      (encPair (encPair (encPair (encUGState L) (encUGEdge L)) (encUGFn L)) (encUGFn L))
      (encUGCand L) := by
    simpa only [Function.comp_def] using
      hcandFin.comp ((((poly_state_cand L).comp hS2).prod hf2).prod
        (((poly_edge_constraint L).comp he2).prod hh2))
  exact optionElimWithInput (poly_se1_getDst L) (poly_se1_state L)
    (poly_state_setCand L hS2 hcand)

private theorem poly_prune (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : State (Fin L) × Edge (Fin L → Fin L) => prune p.1 p.2)
      (encPair (encUGState L) (encUGEdge L)) (encUGState L) := by
  have heq : (fun p : State (Fin L) × Edge (Fin L → Fin L) => prune p.1 p.2) =
      fun p => (p.1.get p.2.src).elim p.1 fun f =>
        (p.1.get p.2.dst).elim p.1 fun h =>
          State.mk p.1.table (fun a => p.1.cand a && decide (p.2.constraint (f a) = h a))
            p.1.stack p.1.comp := by
    funext p
    exact prune_eq_elim L p.1 p.2
  rw [heq]
  exact optionElimWithInput (poly_se_get Edge.src (poly_edge_src L))
    (poly_se_state L) (poly_prune_some L)

private theorem poly_visit (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : State (Fin L) × Edge (Fin L → Fin L) => visit (List.finRange L) p.1 p.2)
      (encPair (encUGState L) (encUGEdge L)) (encUGState L) := by
  unfold visit
  simpa only [Function.comp_def] using
    (poly_prune L).comp ((poly_extend L).prod (snd _ _))

private theorem poly_adj (L : ℕ) :
    ComputableTidilyInPolyTime (fun p : Graph (Fin L → Fin L) × ℕ => adj p.1 p.2)
      (encPair (encUGGraph L) encUnary) (encList (encUGEdge L)) := by
  unfold adj incident
  have hg : ComputableTidilyInPolyTime (fun p : Graph (Fin L → Fin L) × ℕ => p.1)
      (encPair (encUGGraph L) encUnary) (encUGGraph L) := fst _ _
  have hv : ComputableTidilyInPolyTime (fun p : Graph (Fin L → Fin L) × ℕ => p.2)
      (encPair (encUGGraph L) encUnary) encUnary := snd _ _
  refine filterWithInput ((poly_graph_edges L).comp hg) ?_
  have hp : ComputableTidilyInPolyTime
      (fun q : (Graph (Fin L → Fin L) × ℕ) × Edge (Fin L → Fin L) => q.1.2)
      (encPair (encPair (encUGGraph L) encUnary) (encUGEdge L)) encUnary :=
    hv.comp (fst _ _)
  have he : ComputableTidilyInPolyTime
      (fun q : (Graph (Fin L → Fin L) × ℕ) × Edge (Fin L → Fin L) => q.2)
      (encPair (encPair (encUGGraph L) encUnary) (encUGEdge L)) (encUGEdge L) :=
    snd _ _
  exact bool_or.comp
    ((unary_beq ((poly_edge_src L).comp he) hp).prod
      (unary_beq ((poly_edge_dst L).comp he) hp))

private def visitGrowth (L : ℕ) (n : ℕ) : ℕ :=
  4 * (2 * (L * (2 * L + 1) + 1) + 1) + 2 * (2 * n + 1) + 6 * L

private lemma length_encUGState_push_le (L : ℕ) (S : State (Fin L)) (w : ℕ) (f : Fin L → Fin L) :
    (encUGState L (push S w f)).length ≤
      (encUGState L S).length + 4 * (2 * (L * (2 * L + 1) + 1) + 1) + 2 * (2 * w + 1) := by
  have htab : (encUGTable L (S.table.set w (some f))).length ≤
      (encUGTable L S.table).length + 2 * (encOption (encUGFn L) (some f)).length + 1 :=
    length_encList_set_le (encOption (encUGFn L)) S.table w (some f)
  have hopt := optBound_spec L (some f)
  have hst : (encUGVerts (w :: S.stack)).length = 2 * w + 1 + (encUGVerts S.stack).length := by
    simp [encUGVerts, encList_cons, length_frame, encUnary_apply]
  rw [length_encUGState_eq, length_encUGState_eq]
  simp only [push]
  omega

private lemma length_encUGState_prune_le (L : ℕ) (S : State (Fin L)) (e : Edge (Fin L → Fin L)) :
    (encUGState L (prune S e)).length ≤ (encUGState L S).length + 6 * L := by
  unfold prune
  split
  · rename_i f h _ _
    have hcand := candBound_spec L (fun a => S.cand a && decide (e.constraint (f a) = h a))
    rw [length_encUGState_eq, length_encUGState_eq]
    dsimp only
    omega
  · exact Nat.le_add_right _ _

private lemma length_encUGState_visit_le (L : ℕ) (labels : List (Fin L)) (S : State (Fin L))
    (e : Edge (Fin L → Fin L)) (n : ℕ) (hsrc : e.src < n) (hdst : e.dst < n) :
    (encUGState L (visit labels S e)).length ≤
      (encUGState L S).length + visitGrowth L n := by
  unfold visit visitGrowth
  have hp := length_encUGState_prune_le L (extend labels S e) e
  have he : (encUGState L (extend labels S e)).length ≤
      (encUGState L S).length + 4 * (2 * (L * (2 * L + 1) + 1) + 1) + 2 * (2 * n + 1) := by
    unfold extend
    rcases hs : S.get e.src with _ | f <;> rcases hd : S.get e.dst with _ | h <;> dsimp only
    · omega
    · have hpush := length_encUGState_push_le L S e.src (preimage labels e.constraint ∘ h)
      omega
    · have hpush := length_encUGState_push_le L S e.dst (e.constraint ∘ f)
      omega
    · omega
  omega

private theorem poly_visitGrowth_comp {γ : Type} {encIn : γ ↪ List Bool} (L : ℕ)
    {n : γ → ℕ} (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => visitGrowth L (n x)) encIn encUnary := by
  have h2n : ComputableTidilyInPolyTime (fun x => 2 * n x) encIn encUnary := by
    simpa only [Function.comp_def] using unary_mul.comp ((const 2).prod hn)
  have h2n1 : ComputableTidilyInPolyTime (fun x => 2 * n x + 1) encIn encUnary := by
    simpa only [Function.comp_def] using unary_add.comp (h2n.prod (const 1))
  have hmul : ComputableTidilyInPolyTime (fun x => 2 * (2 * n x + 1)) encIn encUnary := by
    simpa only [Function.comp_def] using unary_mul.comp ((const 2).prod h2n1)
  have hadd : ComputableTidilyInPolyTime
      (fun x => 4 * (2 * (L * (2 * L + 1) + 1) + 1) + 2 * (2 * n x + 1)) encIn encUnary := by
    simpa only [Function.comp_def] using
      unary_add.comp ((const (4 * (2 * (L * (2 * L + 1) + 1) + 1))).prod hmul)
  simpa only [visitGrowth, Function.comp_def] using unary_add.comp (hadd.prod (const (6 * L)))

private theorem poly_scan (L : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : Graph (Fin L → Fin L) × State (Fin L) => scan (List.finRange L) p.1 p.2)
      (encPair (encUGGraph L) (encUGState L)) (encUGState L) := by
  have heq :
      (fun p : Graph (Fin L → Fin L) × State (Fin L) => scan (List.finRange L) p.1 p.2) =
        fun p => p.2.stack.head?.elim p.2 fun u =>
          (adj p.1 u).foldl (visit (List.finRange L))
            (State.mk p.2.table p.2.cand (p.2.stack.drop 1) (u :: p.2.comp)) := by
    funext p
    exact scan_eq_elim (List.finRange L) p.1 p.2
  rw [heq]
  have hstack : ComputableTidilyInPolyTime
      (fun p : Graph (Fin L → Fin L) × State (Fin L) => p.2.stack)
      (encPair (encUGGraph L) (encUGState L)) encUGVerts := by
    simpa only [Function.comp_def] using (poly_state_stack L).comp (snd _ _)
  have hg : ComputableTidilyInPolyTime
      (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.1.1)
      (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) (encUGGraph L) :=
    (fst _ _).fst'
  have hS : ComputableTidilyInPolyTime
      (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.1.2)
      (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) (encUGState L) :=
    (fst _ _).snd'
  have hu : ComputableTidilyInPolyTime
      (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.2)
      (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) encUnary :=
    snd _ _
  have hstep : ComputableTidilyInPolyTime
      (fun r : (Bool × State (Fin L)) × Edge (Fin L → Fin L) =>
        visit (List.finRange L) r.1.2 r.2)
      (encFoldStep encBool (encUGState L) (encUGEdge L)) (encUGState L) := by
    simpa only [Function.comp_def] using (poly_visit L).comp ((fst _ _).snd'.prod (snd _ _))
  have hbody : ComputableTidilyInPolyTime
      (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ =>
        (adj q.1.1 q.2).foldl (visit (List.finRange L))
          (State.mk q.1.2.table q.1.2.cand (q.1.2.stack.drop 1) (q.2 :: q.1.2.comp)))
      (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) (encUGState L) := by
    have hadj : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => adj q.1.1 q.2)
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) (encList (encUGEdge L)) := by
      simpa only [Function.comp_def] using (poly_adj L).comp (hg.prod hu)
    have htab : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.1.2.table)
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) (encUGTable L) := by
      simpa only [Function.comp_def] using (poly_state_table L).comp hS
    have hcand : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.1.2.cand)
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) (encUGCand L) := by
      simpa only [Function.comp_def] using (poly_state_cand L).comp hS
    have hst : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.1.2.stack)
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) encUGVerts := by
      simpa only [Function.comp_def] using (poly_state_stack L).comp hS
    have hdrop : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.1.2.stack.drop 1)
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) encUGVerts := by
      simpa only [Function.comp_def] using listDropWithInput hst (const 1)
    have hco : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.1.2.comp)
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) encUGVerts := by
      simpa only [Function.comp_def] using (poly_state_comp L).comp hS
    have hcons : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => q.2 :: q.1.2.comp)
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) encUGVerts := by
      simpa only [Function.comp_def] using cons' hu hco
    have hinit : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ =>
          State.mk q.1.2.table q.1.2.cand (q.1.2.stack.drop 1) (q.2 :: q.1.2.comp))
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) (encUGState L) :=
      poly_state_mk htab hcand hdrop hcons
    have hgr : ComputableTidilyInPolyTime
        (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => visitGrowth L (slots q.1.1))
        (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) encUnary := by
      have hsl : ComputableTidilyInPolyTime
          (fun q : (Graph (Fin L → Fin L) × State (Fin L)) × ℕ => slots q.1.1)
          (encPair (encPair (encUGGraph L) (encUGState L)) encUnary) encUnary := by
        simpa only [Function.comp_def] using (poly_slots L).comp hg
      exact poly_visitGrowth_comp L hsl
    have hfold := foldlWith_of_bounded_growth
      (encP := encBool) (encB := encUGState L) (encA := encUGEdge L)
      (encL := encList (encUGEdge L))
      (encIn := encPair (encPair (encUGGraph L) (encUGState L)) encUnary)
      (par := fun _ => true)
      (list := fun q => adj q.1.1 q.2)
      (init := fun q => State.mk q.1.2.table q.1.2.cand (q.1.2.stack.drop 1) (q.2 :: q.1.2.comp))
      (step := fun (_ : Bool) => visit (List.finRange L))
      (const true) hadj hinit hstep (growth := fun q => visitGrowth L (slots q.1.1))
      hgr.polyBounded fun q acc e he =>
        length_encUGState_visit_le L (List.finRange L) acc e (slots q.1.1)
          (src_lt_slots (List.mem_filter.mp he).1) (dst_lt_slots (List.mem_filter.mp he).1)
    exact hfold
  have hopt : ComputableTidilyInPolyTime
      (fun p : Graph (Fin L → Fin L) × State (Fin L) => p.2.stack.head?)
      (encPair (encUGGraph L) (encUGState L)) (encOption encUnary) := by
    simpa only [Function.comp_def] using (head? encUnary).comp hstack
  exact optionElimWithInput hopt (snd _ _) hbody

private theorem poly_settle (L : ℕ) [NeZero L] :
    ComputableTidilyInPolyTime (settle (List.finRange L)) (encUGState L) (encUGState L) := by
  unfold settle
  have hcandPick : ComputableTidilyInPolyTime
      (fun S : State (Fin L) => ((List.finRange L).find? S.cand).getD default)
      (encUGState L) (encFinEnum (Fin L)) := by
    simpa only [Function.comp_def] using
      (of_finite (fun c : Fin L → Bool => ((List.finRange L).find? c).getD default)).comp
        (poly_state_cand L)
  have htable : ComputableTidilyInPolyTime
      (fun S : State (Fin L) => S.comp.foldl
        (fun t v =>
          t.set v (freeze (((List.finRange L).find? S.cand).getD default) (t.getD v none)))
        S.table)
      (encUGState L) (encUGTable L) := by
    refine foldlWith_of_bounded_growth
      (encP := encFinEnum (Fin L)) (encB := encUGTable L) (encA := encUnary)
      (par := fun S : State (Fin L) => ((List.finRange L).find? S.cand).getD default)
      (list := fun S : State (Fin L) => S.comp) (init := fun S : State (Fin L) => S.table)
      (step := fun c t v => t.set v (freeze c (t.getD v none)))
      hcandPick (poly_state_comp L) (poly_state_table L)
      ?_ (growth := fun _ => 2 * (L * (2 * L + 1) + 1) + 1)
      (PolyBounded.const _) fun S t v _ => ?_
    · have hfreeze : ComputableTidilyInPolyTime
          (fun p : Fin L × Option (Fin L → Fin L) => freeze p.1 p.2)
          (encPair (encFinEnum (Fin L)) (encOption (encUGFn L)))
          (encOption (encUGFn L)) := of_finite _
      have hc : ComputableTidilyInPolyTime
          (fun q : (Fin L × List (Option (Fin L → Fin L))) × ℕ => q.1.1)
          (encFoldStep (encFinEnum (Fin L)) (encUGTable L) encUnary)
          (encFinEnum (Fin L)) :=
        (fst _ _).fst'
      have ht : ComputableTidilyInPolyTime
          (fun q : (Fin L × List (Option (Fin L → Fin L))) × ℕ => q.1.2)
          (encFoldStep (encFinEnum (Fin L)) (encUGTable L) encUnary)
          (encUGTable L) :=
        (fst _ _).snd'
      have hv : ComputableTidilyInPolyTime
          (fun q : (Fin L × List (Option (Fin L → Fin L))) × ℕ => q.2)
          (encFoldStep (encFinEnum (Fin L)) (encUGTable L) encUnary)
          encUnary :=
        snd _ _
      have hget : ComputableTidilyInPolyTime
          (fun q : (Fin L × List (Option (Fin L → Fin L))) × ℕ => q.1.2.getD q.2 none)
          (encFoldStep (encFinEnum (Fin L)) (encUGTable L) encUnary)
          (encOption (encUGFn L)) := by
        simpa only [Function.comp_def] using
          (listGetD (encA := encOption (encUGFn L)) (encL := encUGTable L) none).comp (ht.prod hv)
      have hval : ComputableTidilyInPolyTime
          (fun q : (Fin L × List (Option (Fin L → Fin L))) × ℕ =>
            freeze q.1.1 (q.1.2.getD q.2 none))
          (encFoldStep (encFinEnum (Fin L)) (encUGTable L) encUnary)
          (encOption (encUGFn L)) := by
        simpa only [Function.comp_def] using hfreeze.comp (hc.prod hget)
      exact poly_listSet (encOption (encUGFn L)) ht hv hval
    · have hle := length_encList_set_le (encOption (encUGFn L)) t v
        (freeze (((List.finRange L).find? S.cand).getD default) (t.getD v none))
      have hopt := optBound_spec L
        (freeze (((List.finRange L).find? S.cand).getD default) (t.getD v none))
      change (encList (encOption (encUGFn L)) _).length ≤
        (encList (encOption (encUGFn L)) t).length + (2 * (L * (2 * L + 1) + 1) + 1)
      omega
  exact poly_state_mk htable (poly_state_cand L) (poly_state_stack L) (const [])

private lemma length_encUGState_scan_le (L : ℕ) (labels : List (Fin L))
    (g : Graph (Fin L → Fin L)) (S : State (Fin L)) :
    (encUGState L (scan labels g S)).length ≤
      (encUGState L S).length + g.edges.length * visitGrowth L (slots g) := by
  unfold scan
  cases hs : S.stack with
  | nil => exact Nat.le_add_right _ _
  | cons u rest =>
    dsimp only
    let S₀ : State (Fin L) :=
      { table := S.table, cand := S.cand, stack := rest, comp := u :: S.comp }
    have hS₀ : (encUGState L S₀).length ≤ (encUGState L S).length := by
      have hst : (encUGVerts (u :: rest)).length =
          (frame (encUnary u)).length + (encUGVerts rest).length := by
        simp [encUGVerts, encList_cons]
      have hco : (encUGVerts (u :: S.comp)).length =
          (frame (encUnary u)).length + (encUGVerts S.comp).length := by
        simp [encUGVerts, encList_cons]
      rw [length_encUGState_eq, length_encUGState_eq]
      dsimp only [S₀]
      rw [hs, hst, hco]
      omega
    have hfold : ∀ (l : List (Edge (Fin L → Fin L))) (acc : State (Fin L)),
        (∀ e ∈ l, e ∈ g.edges) →
        (encUGState L (l.foldl (visit labels) acc)).length ≤
          (encUGState L acc).length + l.length * visitGrowth L (slots g) := by
      intro l acc hl
      induction l generalizing acc with
      | nil => simp
      | cons e l ih =>
        have he := hl e (List.mem_cons_self ..)
        have hv := length_encUGState_visit_le L labels acc e (slots g)
          (src_lt_slots he) (dst_lt_slots he)
        have hih := ih (visit labels acc e) fun e' he' => hl e' (List.mem_cons_of_mem _ he')
        simp only [List.foldl_cons, List.length_cons] at hih hv ⊢
        rw [Nat.succ_mul]
        omega
    have hadj := hfold (adj g u) S₀ fun e he => (List.mem_filter.mp he).1
    have hlen : (adj g u).length ≤ g.edges.length := List.length_filter_le _ _
    have hmul : (adj g u).length * visitGrowth L (slots g) ≤
        g.edges.length * visitGrowth L (slots g) :=
      Nat.mul_le_mul_right (visitGrowth L (slots g)) hlen
    exact hadj.trans (Nat.add_le_add hS₀ hmul)

private lemma length_encUGState_iterate_scan_le (L : ℕ) (labels : List (Fin L))
    (g : Graph (Fin L → Fin L)) (S : State (Fin L)) (k : ℕ) :
    (encUGState L ((scan labels g)^[k] S)).length ≤
      (encUGState L S).length + k * (g.edges.length * visitGrowth L (slots g)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := length_encUGState_scan_le L labels g ((scan labels g)^[k] S)
    rw [Nat.succ_mul]
    omega

private lemma length_encUGState_settle_le (L : ℕ) [NeZero L] (labels : List (Fin L))
    (S : State (Fin L)) :
    (encUGState L (settle labels S)).length ≤
      4 * (S.table.length * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
        2 * (encUGVerts S.stack).length + 4 := by
  have htab := (length_encUGTable_le_mul L (settle labels S).table).trans
    (by rw [settle_length])
  have hcand := candBound_spec L (settle labels S).cand
  have hcomp : (settle labels S).comp = [] := rfl
  have hstack : (settle labels S).stack = S.stack := rfl
  rw [length_encUGState_eq]
  rw [hstack, hcomp]
  simp only [encUGVerts, encList_nil, List.length_nil]
  omega

private theorem poly_step (L : ℕ) [NeZero L] :
    ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
        step (List.finRange L) p.1.1 p.1.2 p.2)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGState L) := by
  have heq :
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
          step (List.finRange L) p.1.1 p.1.2 p.2) =
        fun p => (p.1.2.get p.2.src).elim
          (settle (List.finRange L) ((scan (List.finRange L) p.1.1)^[slots p.1.1]
            (start p.1.2 p.2.src)))
          fun _ => p.1.2 := by
    funext p
    exact step_eq_elim (List.finRange L) p.1.1 p.1.2 p.2
  rw [heq]
  have hg : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) => p.1.1)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGGraph L) :=
    (fst _ _).fst'
  have hS : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) => p.1.2)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGState L) :=
    (fst _ _).snd'
  have he : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) => p.2)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGEdge L) :=
    snd _ _
  have hsrc : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) => p.2.src)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) encUnary := by
    simpa only [Function.comp_def] using (poly_edge_src L).comp he
  have hget : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) => p.1.2.get p.2.src)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L))
      (encOption (encUGFn L)) := by
    simpa only [Function.comp_def] using (poly_get L).comp (hS.prod hsrc)
  have hsl : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) => slots p.1.1)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) encUnary := by
    simpa only [Function.comp_def] using (poly_slots L).comp hg
  have hed : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
        p.1.1.edges.length)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) encUnary := by
    simpa only [Function.comp_def] using
      (length_list (encUGEdge L)).comp ((poly_graph_edges L).comp hg)
  have hgrowth : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
        p.1.1.edges.length * visitGrowth L (slots p.1.1))
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) encUnary := by
    simpa only [Function.comp_def] using
      unary_mul.comp (hed.prod (poly_visitGrowth_comp L hsl))
  have hstart : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
        start p.1.2 p.2.src)
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGState L) := by
    simpa only [Function.comp_def] using (poly_start L).comp (hS.prod hsrc)
  have hiter : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
        (scan (List.finRange L) p.1.1)^[slots p.1.1] (start p.1.2 p.2.src))
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGState L) := by
    have hit := iterateWith_of_bounded_growth
      (encIn := encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L))
      (encPar := encUGGraph L) (encState := encUGState L)
      (par := fun p => p.1.1) (count := fun p => slots p.1.1)
      (init := fun p => start p.1.2 p.2.src) (step := scan (List.finRange L))
      hg hsl hstart (poly_scan L)
      (growth := fun p => p.1.1.edges.length * visitGrowth L (slots p.1.1))
      hgrowth.polyBounded fun p acc => length_encUGState_scan_le L (List.finRange L) p.1.1 acc
    exact hit
  have hfallback : ComputableTidilyInPolyTime
      (fun p : (Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L) =>
        settle (List.finRange L)
          ((scan (List.finRange L) p.1.1)^[slots p.1.1] (start p.1.2 p.2.src)))
      (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGState L) := by
    simpa only [Function.comp_def] using (poly_settle L).comp hiter
  have hbody : ComputableTidilyInPolyTime
      (fun q : ((Graph (Fin L → Fin L) × State (Fin L)) × Edge (Fin L → Fin L)) ×
          (Fin L → Fin L) => q.1.1.2)
      (encPair (encPair (encPair (encUGGraph L) (encUGState L)) (encUGEdge L)) (encUGFn L))
      (encUGState L) := by
    simpa only [Function.comp_def] using hS.comp (fst _ _)
  exact optionElimWithInput hget hfallback hbody

private def runBound (L : ℕ) (g : Graph (Fin L → Fin L)) : ℕ :=
  4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
    2 * (4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
      2 * (2 * slots g + 1) + 4 + slots g * (g.edges.length * visitGrowth L (slots g))) + 4

private theorem poly_runBound (L : ℕ) :
    ComputableTidilyInPolyTime (runBound L) (encUGGraph L) encUnary := by
  have hsl := poly_slots L
  have hed : ComputableTidilyInPolyTime (fun g : Graph (Fin L → Fin L) => g.edges.length)
      (encUGGraph L) encUnary :=
    (length_list (encUGEdge L)).comp (poly_graph_edges L)
  have htab : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) => slots g * (2 * (L * (2 * L + 1) + 1) + 1))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using
      unary_mul.comp (hsl.prod (const (2 * (L * (2 * L + 1) + 1) + 1)))
  have h4tab : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) => 4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_mul.comp ((const 4).prod htab)
  have hpre : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) =>
        4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_add.comp (h4tab.prod (const (2 * (3 * L))))
  have hst : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) => 2 * slots g + 1) (encUGGraph L) encUnary := by
    have h2s : ComputableTidilyInPolyTime
        (fun g : Graph (Fin L → Fin L) => 2 * slots g) (encUGGraph L) encUnary := by
      simpa only [Function.comp_def] using unary_mul.comp ((const 2).prod hsl)
    simpa only [Function.comp_def] using unary_add.comp (h2s.prod (const 1))
  have h2st : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) => 2 * (2 * slots g + 1)) (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_mul.comp ((const 2).prod hst)
  have hvg := poly_visitGrowth_comp L hsl
  have hedvg : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) => g.edges.length * visitGrowth L (slots g))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_mul.comp (hed.prod hvg)
  have hscan : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) => slots g * (g.edges.length * visitGrowth L (slots g)))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_mul.comp (hsl.prod hedvg)
  have hinner1 : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) =>
        4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) + 2 * (2 * slots g + 1))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_add.comp (hpre.prod h2st)
  have hinner2 : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) =>
        4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
          2 * (2 * slots g + 1) + 4)
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_add.comp (hinner1.prod (const 4))
  have hinner : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) =>
        4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
          2 * (2 * slots g + 1) + 4 + slots g * (g.edges.length * visitGrowth L (slots g)))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_add.comp (hinner2.prod hscan)
  have h2inner : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) =>
        2 * (4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
          2 * (2 * slots g + 1) + 4 + slots g * (g.edges.length * visitGrowth L (slots g))))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_mul.comp ((const 2).prod hinner)
  have houter : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) =>
        4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
          2 * (4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
            2 * (2 * slots g + 1) + 4 + slots g * (g.edges.length * visitGrowth L (slots g))))
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_add.comp (hpre.prod h2inner)
  have hres : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) =>
        4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
          2 * (4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
            2 * (2 * slots g + 1) + 4 + slots g * (g.edges.length * visitGrowth L (slots g))) + 4)
      (encUGGraph L) encUnary := by
    simpa only [Function.comp_def] using unary_add.comp (houter.prod (const 4))
  exact hres

private theorem poly_run (L : ℕ) [NeZero L] :
    ComputableTidilyInPolyTime (run (List.finRange L)) (encUGGraph L) (encUGState L) := by
  unfold run
  refine foldlWith
    (encP := encUGGraph L) (encB := encUGState L) (encA := encUGEdge L)
    (par := id) (list := fun g => g.edges) (init := init) (step := step (List.finRange L))
    id' (poly_graph_edges L) (poly_init L) (poly_step L)
    (B := runBound L) (poly_runBound L).polyBounded fun g i hi => ?_
  suffices ∀ j ≤ g.edges.length,
      (List.foldl (step (List.finRange L) g) (init g) (g.edges.take j)).table.length =
        slots g ∧
      (encUGState L (List.foldl (step (List.finRange L) g) (init g) (g.edges.take j))).length ≤
        runBound L g from (this i hi).2
  intro j hj
  induction j with
  | zero =>
    simp only [List.take_zero, List.foldl_nil, init, List.length_replicate, true_and]
    have htab : (encUGTable L (List.replicate (slots g) none)).length = slots g :=
      length_encList_replicate_none (slots g) (encUGFn L)
    have hcand := candBound_spec L (fun _ : Fin L => true)
    rw [length_encUGState_eq]
    simp only [htab, encUGVerts, encList_nil, List.length_nil, runBound]
    omega
  | succ j ih =>
    obtain ⟨hlen, hbound⟩ := ih (Nat.le_of_succ_le hj)
    have htake : g.edges.take (j + 1) = g.edges.take j ++ [g.edges[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := List.foldl (step (List.finRange L) g) (init g) (g.edges.take j)
    refine ⟨(length_step _ g acc g.edges[j]).trans hlen, ?_⟩
    unfold step
    rcases hget : acc.get g.edges[j].src with _ | _
    · dsimp only
      set e := g.edges[j]
      have hedge : e ∈ g.edges := List.getElem_mem hj
      have hsrc : e.src < slots g := src_lt_slots hedge
      have hstartLen : (start acc e.src).table.length = slots g := by
        simpa [start, List.length_set] using hlen
      have hS₀ : (encUGState L (start acc e.src)).length ≤
          4 * (slots g * (2 * (L * (2 * L + 1) + 1) + 1)) + 2 * (3 * L) +
            2 * (2 * slots g + 1) + 4 := by
        have htab := length_encUGTable_le_mul L (start acc e.src).table
        rw [hstartLen] at htab
        have hcand := candBound_spec L (fun _ : Fin L => true)
        have hst : (encUGVerts [e.src]).length = 2 * e.src + 1 := by
          simp [encUGVerts, encList_cons, encList_nil, length_frame, encUnary_apply]
        rw [length_encUGState_eq]
        dsimp only [start] at htab ⊢
        rw [hst]
        simp only [encList_nil, List.length_nil]
        omega
      have hiter := length_encUGState_iterate_scan_le L (List.finRange L) g
        (start acc e.src) (slots g)
      have hstack : (encUGVerts ((scan (List.finRange L) g)^[slots g]
          (start acc e.src)).stack).length ≤
          (encUGState L ((scan (List.finRange L) g)^[slots g] (start acc e.src))).length := by
        rw [length_encUGState_eq]
        omega
      have hset := length_encUGState_settle_le L (List.finRange L)
        ((scan (List.finRange L) g)^[slots g] (start acc e.src))
      rw [length_iterate_scan, hstartLen] at hset
      unfold runBound
      omega
    · exact hbound

private def checkTable {α : Type} [DecidableEq α] [Inhabited α]
    (table : List (Option (α → α))) (g : Graph (α → α)) : Bool :=
  g.edges.all fun e =>
    let l : ℕ → α := fun v => (table.getD v none).elim default fun f => f default
    decide (e.constraint (l e.src) = l e.dst)

private theorem checkTable_run_eq_isSome_solve {α : Type} [DecidableEq α] [Inhabited α]
    (labels : List α) (g : Graph (α → α)) :
    checkTable (run labels g).table g = (solve labels g).isSome := by
  have hcheck : checkTable (run labels g).table g = check g (labelling labels g) := rfl
  rw [hcheck]
  unfold solve
  split_ifs with h <;> simp [h]

private def tableVal {L : ℕ} [NeZero L] (o : Option (Fin L → Fin L)) : Fin L :=
  o.elim default fun f => f default

private theorem poly_checkTable (L : ℕ) [NeZero L] :
    ComputableTidilyInPolyTime
      (fun p : List (Option (Fin L → Fin L)) × Graph (Fin L → Fin L) =>
        checkTable p.1 p.2)
      (encPair (encUGTable L) (encUGGraph L)) encBool := by
  have heq : (fun p : List (Option (Fin L → Fin L)) × Graph (Fin L → Fin L) =>
        checkTable p.1 p.2) =
      fun p => p.2.edges.all fun e =>
        decide (e.constraint (tableVal (p.1.getD e.src none)) = tableVal (p.1.getD e.dst none)) :=
    rfl
  rw [heq]
  refine allWithInput ((poly_graph_edges L).comp (snd _ _)) ?_
  have hp : ComputableTidilyInPolyTime
      (fun q : (List (Option (Fin L → Fin L)) × Graph (Fin L → Fin L)) × Edge (Fin L → Fin L) =>
        q.1.1)
      (encPair (encPair (encUGTable L) (encUGGraph L)) (encUGEdge L)) (encUGTable L) :=
    (fst _ _).fst'
  have he : ComputableTidilyInPolyTime
      (fun q : (List (Option (Fin L → Fin L)) × Graph (Fin L → Fin L)) × Edge (Fin L → Fin L) =>
        q.2)
      (encPair (encPair (encUGTable L) (encUGGraph L)) (encUGEdge L)) (encUGEdge L) :=
    snd _ _
  have hvalPoly : ComputableTidilyInPolyTime (tableVal (L := L))
      (encOption (encUGFn L)) (encFinEnum (Fin L)) := of_finite _
  have hlsrc := hvalPoly.comp ((listGetD
    (encA := encOption (encUGFn L)) (encL := encUGTable L) none).comp
    (hp.prod ((poly_edge_src L).comp he)))
  have hldst := hvalPoly.comp ((listGetD
    (encA := encOption (encUGFn L)) (encL := encUGTable L) none).comp
    (hp.prod ((poly_edge_dst L).comp he)))
  have hcheckFin : ComputableTidilyInPolyTime
      (fun r : (Fin L → Fin L) × (Fin L × Fin L) => decide (r.1 r.2.1 = r.2.2))
      (encPair (encUGFn L) (encPair (encFinEnum (Fin L)) (encFinEnum (Fin L)))) encBool :=
    of_finite _
  exact hcheckFin.comp (((poly_edge_constraint L).comp he).prod (hlsrc.prod hldst))

end PolyTime

/-- Label propagation over `List.finRange L` is polynomial-time computable in the multi-tape
Turing machine model under the `UniqueGamesConjecture` graph encoding. -/
theorem computableInPolyTime_isSome_solve (L : ℕ) [NeZero L] :
    ComputableInPolyTime (fun g : Graph (Fin L → Fin L) => (solve (List.finRange L) g).isSome)
      (Graph.encoding (encPi (encFinEnum (Fin L)))) encBool := by
  have h : ComputableTidilyInPolyTime
      (fun g : Graph (Fin L → Fin L) => checkTable (run (List.finRange L) g).table g)
      (encUGGraph L) encBool :=
    (poly_checkTable L).comp
      (((poly_state_table L).comp (poly_run L)).prod ComputableTidilyInPolyTime.id')
  have h' : ComputableInPolyTime
      (fun g : Graph (Fin L → Fin L) => checkTable (run (List.finRange L) g).table g)
      (Graph.encoding (encPi (encFinEnum (Fin L)))) encBool :=
    ComputableInPolyTime.of_tidy h
  simpa only [checkTable_run_eq_isSome_solve] using h'

end Cslib.Complexity.UniqueGames.Propagation

namespace Cslib.Complexity

open Cslib.Complexity.UniqueGames.Propagation Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- For `0 < L`, `GapUniqueGames (Fin L) 1 s` is in `PromiseP` under the encoding of
`UniqueGamesConjecture`, via label propagation over `List.finRange L`. -/
theorem gapUniqueGames_one_mem_PromiseP_of_pos {L : ℕ} (hL : 0 < L) (s : ℝ) :
    GapUniqueGames (Fin L) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin L)))) := by
  have : NeZero L := ⟨hL.ne'⟩
  exact mem_PromiseP_iff.2 ⟨_, computableInPolyTime_isSome_solve L,
    solvedBy_gapUniqueGames_one (fun a => List.mem_finRange a) s⟩

/-- Over `Fin 0`, no labelling `ℕ → Fin 0` exists, so no graph is satisfiable. -/
theorem not_satisfiable_fin_zero (g : Graph (Fin 0 → Fin 0)) :
    ¬ (g.toGraph permutationEval).Satisfiable := by
  rintro ⟨σ, _⟩
  exact Fin.elim0 (σ 0)

/-- Over `Fin 0`, the empty infimum gives `unsatVal = 0`, so every unique game is a yes-instance
of `GapUniqueGames (Fin 0) 1 s`. -/
theorem gapUniqueGames_zero_yes (s : ℝ) :
    (GapUniqueGames (Fin 0) 1 s).yes = {g : Graph (Fin 0 → Fin 0) | IsUniqueGame g} := by
  ext g
  simp [GapUniqueGames, PromiseProblem.restrict, ConstraintGraph.unsatVal]

/-- Over `Fin 0`, `GapUniqueGames (Fin 0) 1 s` has no no-instances: every unique game has value
`1`, which cannot simultaneously satisfy `1 ≤ s` and `s < 1`. -/
theorem gapUniqueGames_zero_no (s : ℝ) :
    (GapUniqueGames (Fin 0) 1 s).no = ∅ := by
  ext g
  simp only [GapUniqueGames, PromiseProblem.restrict, PromiseProblem.gapMax,
    ConstraintGraph.unsatVal, Real.iInf_of_isEmpty, sub_zero, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, _⟩
  exact h1.not_gt h2

/-- `GapUniqueGames (Fin 0) 1 s ∈ PromiseP`: every unique game is a yes-instance and there are
no no-instances, so the constant-`true` decider solves the promise problem. -/
theorem gapUniqueGames_zero_mem_PromiseP (s : ℝ) :
    GapUniqueGames (Fin 0) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin 0)))) := by
  refine mem_PromiseP_iff.2 ⟨fun _ => true, .const true, fun g _ => rfl, fun g hg => ?_⟩
  rw [gapUniqueGames_zero_no] at hg
  exact hg.elim

/-- For every alphabet size `L : ℕ` and soundness threshold `s : ℝ`, `GapUniqueGames (Fin L) 1 s`
belongs to `PromiseP` under the encoding used by `UniqueGamesConjecture`. -/
theorem gapUniqueGames_one_mem_PromiseP (L : ℕ) (s : ℝ) :
    GapUniqueGames (Fin L) 1 s ∈ PromiseP (Graph.encoding (encPi (encFinEnum (Fin L)))) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact gapUniqueGames_zero_mem_PromiseP s
  · exact gapUniqueGames_one_mem_PromiseP_of_pos hL s

private def isUniqueGameBool (L : ℕ) (g : Graph (Fin L → Fin L)) : Bool :=
  g.edges.all fun e => decide (Function.Bijective e.constraint)

private theorem isUniqueGameBool_eq_true (L : ℕ) (g : Graph (Fin L → Fin L)) :
    isUniqueGameBool L g = true ↔ IsUniqueGame g := by
  simp [isUniqueGameBool, IsUniqueGame]

private theorem computableInPolyTime_isUniqueGameBool (L : ℕ) :
    ComputableInPolyTime (isUniqueGameBool L)
      (Graph.encoding (encPi (encFinEnum (Fin L)))) encBool := by
  have h : ComputableTidilyInPolyTime (isUniqueGameBool L) (encUGGraph L) encBool := by
    refine ComputableTidilyInPolyTime.allWithInput (poly_graph_edges L) ?_
    exact (ComputableTidilyInPolyTime.of_finite
      (fun f : Fin L → Fin L => decide (Function.Bijective f))).comp
      ((poly_edge_constraint L).comp (ComputableTidilyInPolyTime.snd _ _))
  exact ComputableInPolyTime.of_tidy h

/-- Checking `IsUniqueGame` belongs to `P` for every fixed alphabet size `L`. -/
theorem isUniqueGame_mem_P (L : ℕ) :
    {g : Graph (Fin L → Fin L) | IsUniqueGame g} ∈
      P (Graph.encoding (encPi (encFinEnum (Fin L)))) :=
  ⟨isUniqueGameBool L, computableInPolyTime_isUniqueGameBool L,
    fun g => (isUniqueGameBool_eq_true L g).symm⟩

/-- Deciding satisfiability of unique games belongs to `P` for every fixed alphabet size `L`. -/
theorem satisfiable_uniqueGame_mem_P (L : ℕ) :
    {g : Graph (Fin L → Fin L) | IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable} ∈
      P (Graph.encoding (encPi (encFinEnum (Fin L)))) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have heq :
        {g : Graph (Fin 0 → Fin 0) | IsUniqueGame g ∧ (g.toGraph permutationEval).Satisfiable} =
          ∅ := by
      ext g
      simp [not_satisfiable_fin_zero g]
    rw [heq]
    exact empty_mem_P
  · have : NeZero L := ⟨hL.ne'⟩
    refine ⟨fun g => isUniqueGameBool L g && (solve (List.finRange L) g).isSome, ?_, fun g => ?_⟩
    · exact ComputableInPolyTime.bool_and.comp
        ((computableInPolyTime_isUniqueGameBool L).prod (computableInPolyTime_isSome_solve L))
    · simp only [Set.mem_ofPred_eq, Bool.and_eq_true, isUniqueGameBool_eq_true,
        and_congr_right_iff]
      intro hg
      exact (solve_isSome_iff (fun a => List.mem_finRange a) hg).symm

end Cslib.Complexity
