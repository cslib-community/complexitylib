/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.Interpret
public import CslibFrontier.Logics.FirstOrder.Raw.Sentence
public import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Set.Finite.List

/-!
# Interpreting a relational structure in a graph

A formula whose atoms all use the symbol `0` (at positive arities) is translated into a formula
over a single binary relation `E` (the symbol `0` at arity `2`), preserving finite satisfiability
(`Cslib.Logic.FO.RawFormula.finSat_toGraph`). The translation is a relativized interpretation
(`Cslib.Logic.FO.RawFormula.interpret`):

* the domain is the set of loops `E(x, x)`;
* an atom `R(x_0, …, x_{L-1})` becomes the **tuple gadget**
  `Cslib.Logic.FO.RawFormula.tupleGadget`: there are non-loops `u_0, …, u_{L-1}` with chain edges
  `u_{i+1} → u_i` and coordinate edges `u_i → x_i`, such that `u_0` has no edge to a non-loop and
  no non-loop has an edge to `u_{L-1}`.

Conversely, a finite structure `I` (the relation `I 0` on `M`) gives the finite **tuple graph**
`Cslib.Logic.FO.RawFormula.tupleGraph` on `M ⊕ TupleVertex I K`: a loop at each element of `M`,
and for each tuple `l ∈ I 0` of length at most `K` a chain of non-loops `(l, j)`, `j < |l|`, with
edges `(l, j + 1) → (l, j)` and `(l, j) → l[j]`. A tuple gadget holds in the tuple graph exactly
for the tuples of `I 0` (`Cslib.Logic.FO.RawFormula.isTupleGadget_tupleGraph_iff`): the two
boundary conditions force a witnessing chain to be a whole gadget chain of the right length.

This is a standard interpretation of a relational structure in a graph (used to sharpen
Trakhtenbrot's theorem to one binary relation, cf. [Libkin2004], Theorem 9.2). The atom helpers
`edgeAtom`, `loopAtom` and `listRel` live in the namespace `Cslib.Logic.FO.RawFormula.Graph`.

## Main definitions

* `Cslib.Logic.FO.RawFormula.tupleGadget`, `Cslib.Logic.FO.RawFormula.IsTupleGadget`: the tuple
  gadget, as a formula and semantically.
* `Cslib.Logic.FO.RawFormula.tupleGraph`: the tuple graph of a structure.
* `Cslib.Logic.FO.RawFormula.toGraph`: the graph translation.

## Main results

* `Cslib.Logic.FO.RawFormula.realize_tupleGadget`: semantics of the gadget formula.
* `Cslib.Logic.FO.RawFormula.isTupleGadget_tupleGraph_iff`: the gadgets of the tuple graph.
* `Cslib.Logic.FO.RawFormula.finSat_toGraph`: the translation preserves finite satisfiability.
* `Cslib.Logic.FO.RawFormula.primrec₂_toGraph`: the translation is primitive recursive.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

/-! ### The tuple gadget -/

namespace Graph

/-- The edge atom `E(x, y)` of the single binary relation `0`. -/
def edgeAtom (x y : ℕ) : RawFormula := rel 0 [x, y]

/-- The loop atom `E(x, x)`, defining the domain. -/
def loopAtom (x : ℕ) : RawFormula := edgeAtom x x

/-- Binary relations as list relations. -/
def listRel {G : Type*} (E : G → G → Prop) : List G → Prop
  | [a, b] => E a b
  | _ => False

end Graph

open Graph

/-- The body of the tuple gadget for `args` (of length `L`), with chain variables
`u_i = x_{B+i}` and a scratch variable `x_{B+L}`: the `u_i` are non-loops, `u_{i+1} → u_i`, `u_0`
has no edge to a non-loop, no non-loop has an edge to `u_{L-1}`, and `u_i → args[i]`. -/
def tupleGadgetBody (B : ℕ) (args : List ℕ) : RawFormula :=
  bigConj ((List.range args.length).map (fun i => neg (loopAtom (B + i))) ++
    (List.range (args.length - 1)).map (fun i => edgeAtom (B + i + 1) (B + i)) ++
    [all (B + args.length) (imp (neg (loopAtom (B + args.length)))
      (neg (edgeAtom B (B + args.length)))),
     all (B + args.length) (imp (neg (loopAtom (B + args.length)))
      (neg (edgeAtom (B + args.length) (B + args.length - 1))))] ++
    (List.range args.length).map (fun i => edgeAtom (B + i) (args.getD i 0)))

/-- The tuple gadget: `∃ u_0 … u_{L-1}`, the gadget body. -/
def tupleGadget (B : ℕ) (args : List ℕ) : RawFormula :=
  exRange B args.length (tupleGadgetBody B args)

theorem atoms_tupleGadget (B : ℕ) (args : List ℕ) :
    ∀ a ∈ (tupleGadget B args).atoms, a = (0, 2) := by
  intro a h
  rw [tupleGadget, atoms_exRange, tupleGadgetBody] at h
  obtain ⟨φ, hφ, h⟩ := atoms_bigConj h
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hφ
  rcases hφ with ((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | rfl | rfl) | ⟨i, -, rfl⟩ <;>
    simpa [loopAtom, edgeAtom, neg, atoms] using h

/-- The semantic tuple gadget in a graph `E`: the witnesses `u_i` of the gadget formula. -/
def IsTupleGadget {G : Type*} (E : G → G → Prop) (xs : List G) : Prop :=
  ∃ u : ℕ → G, (∀ i < xs.length, ¬E (u i) (u i)) ∧
    (∀ i, i + 1 < xs.length → E (u (i + 1)) (u i)) ∧
    (∀ m, ¬E m m → ¬E (u 0) m) ∧ (∀ m, ¬E m m → ¬E m (u (xs.length - 1))) ∧
    ∀ i (h : i < xs.length), E (u i) xs[i]

theorem realize_tupleGadgetBody {G : Type*} {E : G → G → Prop} {B : ℕ} {args : List ℕ}
    (hL : 0 < args.length) (w : ℕ → G) :
    (tupleGadgetBody B args).Realize (fun _ => listRel E) w ↔
      (∀ i < args.length, ¬E (w (B + i)) (w (B + i))) ∧
      (∀ i < args.length - 1, E (w (B + i + 1)) (w (B + i))) ∧
      (∀ m, ¬E m m → ¬E (w B) m) ∧
      (∀ m, ¬E m m → ¬E m (w (B + args.length - 1))) ∧
      (∀ i < args.length, E (w (B + i)) (w (args.getD i 0))) := by
  have h1 : B ≠ B + args.length := by omega
  have h2 : B + args.length - 1 ≠ B + args.length := by omega
  simp [tupleGadgetBody, loopAtom, edgeAtom, listRel, or_imp, forall_and, Function.update_of_ne h1,
    Function.update_of_ne h2]

theorem realize_tupleGadget {G : Type*} {E : G → G → Prop} {B : ℕ} {args : List ℕ}
    (hL : 0 < args.length) (hB : ∀ x ∈ args, x < B) (w : ℕ → G) :
    (tupleGadget B args).Realize (fun _ => listRel E) w ↔ IsTupleGadget E (args.map w) := by
  rw [tupleGadget, realize_exRange]
  simp only [IsTupleGadget, List.length_map]
  constructor
  · rintro ⟨w', hw', hb⟩
    rw [realize_tupleGadgetBody hL] at hb
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb
    refine ⟨fun i => w' (B + i), b1, fun i hi => b2 i (by omega), b3, fun m hm => ?_,
      fun i hi => ?_⟩
    · have := b4 m hm
      rwa [show B + args.length - 1 = B + (args.length - 1) by omega] at this
    have hx : args[i] < B := hB _ (List.getElem_mem hi)
    have := b5 i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      hw' args[i] (by omega)] at this
    simpa using this
  · rintro ⟨u, g1, g2, g3, g4, g5⟩
    classical
    let w' : ℕ → G := fun y => if B ≤ y ∧ y < B + args.length then u (y - B) else w y
    refine ⟨w', fun y hy => ite_eq_right hy, ?_⟩
    have hw'u : ∀ i < args.length, w' (B + i) = u i := by
      intro i hi
      simp only [w']
      rw [ite_eq_left (by omega), Nat.add_sub_cancel_left]
    rw [realize_tupleGadgetBody hL]
    refine ⟨fun i hi => by rw [hw'u i hi]; exact g1 i hi,
      fun i hi => by
        rw [show B + i + 1 = B + (i + 1) by omega, hw'u i (by omega), hw'u (i + 1) (by omega)]
        exact g2 i (by omega),
      fun m hm => by rw [show B = B + 0 by rfl, hw'u 0 hL]; exact g3 m hm,
      fun m hm => by
        rw [show B + args.length - 1 = B + (args.length - 1) by omega,
          hw'u _ (by omega)]
        exact g4 m hm,
      fun i hi => ?_⟩
    have hx : args[i] < B := hB _ (List.getElem_mem hi)
    rw [hw'u i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    have hw : w' args[i] = w args[i] := by simp only [w']; rw [ite_eq_right (by omega)]
    rw [hw]
    simpa using g5 i (by simpa using hi)

/-! ### The canonical tuple graph -/

section Canonical

variable {M : Type*} (I : ℕ → List M → Prop) (K : ℕ)

/-- The gadget vertices of the tuple graph: positions `j` in a tuple `l ∈ I 0` of length at most
`K`. (Exposed because the code generator needs the representation of this type in other
modules.) -/
@[expose] def TupleVertex : Type _ :=
  {q : List M × ℕ // q.1.length ≤ K ∧ q.2 < q.1.length ∧ I 0 q.1}

instance instFiniteTupleVertex [Finite M] : Finite (TupleVertex I K) := by
  have : Finite {l : List M // l.length ≤ K} := (List.finite_length_le M K).to_subtype
  refine Finite.of_injective (β := {l : List M // l.length ≤ K} × Fin (K + 1))
    (fun q => (⟨q.1.1, q.2.1⟩, ⟨q.1.2, by have := q.2.1; have := q.2.2.1; omega⟩)) ?_
  rintro ⟨⟨l, j⟩, h⟩ ⟨⟨l', j'⟩, h'⟩ he
  simp only [Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rfl

/-- The tuple graph on `M ⊕ TupleVertex I K`: loops on `M`, chain edges
`(l, j + 1) → (l, j)`, and coordinate edges `(l, j) → l[j]`. -/
def tupleGraph : M ⊕ TupleVertex I K → M ⊕ TupleVertex I K → Prop
  | .inl a, .inl b => a = b
  | .inl _, .inr _ => False
  | .inr q, .inr q' => q.1.1 = q'.1.1 ∧ q.1.2 = q'.1.2 + 1
  | .inr q, .inl a => q.1.1[q.1.2]? = some a

/-- **The tuple gadgets of the tuple graph are the tuples of `I 0`**, of length between `1`
and `K`. -/
theorem isTupleGadget_tupleGraph_iff {bs : List M} (h0 : 0 < bs.length) (hK : bs.length ≤ K) :
    IsTupleGadget (tupleGraph I K) (bs.map Sum.inl) ↔ I 0 bs := by
  simp only [IsTupleGadget, List.length_map, List.getElem_map]
  constructor
  · rintro ⟨u, g1, g2, g3, g4, g5⟩
    have hinr : ∀ i < bs.length, ∃ q, u i = .inr q := by
      intro i hi
      rcases h : u i with a | q
      · exact (g1 i hi (by rw [h]; exact rfl)).elim
      · exact ⟨q, rfl⟩
    obtain ⟨q0, hq0⟩ := hinr 0 h0
    have hj0 : q0.1.2 = 0 := by
      by_contra hne
      have hv : q0.1.2 - 1 < q0.1.1.length := by have := q0.2.2.1; omega
      refine g3 (.inr ⟨(q0.1.1, q0.1.2 - 1), q0.2.1, hv, q0.2.2.2⟩) (fun h => ?_) ?_
      · simp only [tupleGraph] at h; omega
      · rw [hq0]; exact ⟨rfl, by simp only; omega⟩
    have hchain : ∀ i < bs.length,
        ∃ q : TupleVertex I K, u i = .inr q ∧ q.1.1 = q0.1.1 ∧ q.1.2 = i := by
      intro i hi
      induction i with
      | zero => exact ⟨q0, hq0, rfl, hj0⟩
      | succ i ih =>
        obtain ⟨q, hq, hl, hj⟩ := ih (by omega)
        obtain ⟨q', hq'⟩ := hinr (i + 1) hi
        have := g2 i hi
        rw [hq, hq'] at this
        exact ⟨q', hq', this.1.trans hl, by have := this.2; omega⟩
    have hlen : q0.1.1.length = bs.length := by
      obtain ⟨q, hq, hl, hj⟩ := hchain (bs.length - 1) (by omega)
      have h1 : bs.length ≤ q0.1.1.length := by have := q.2.2.1; rw [hl] at this; omega
      by_contra hne
      have hv : bs.length < q0.1.1.length := by omega
      refine g4 (.inr ⟨(q0.1.1, bs.length), q0.2.1, hv, q0.2.2.2⟩) (fun h => ?_) ?_
      · simp only [tupleGraph] at h; omega
      · rw [hq]; exact ⟨hl.symm, by simp only; omega⟩
    have hl : q0.1.1 = bs := by
      apply List.ext_getElem hlen
      intro i h1 h2
      obtain ⟨q, hq, hql, hqj⟩ := hchain i h2
      have := g5 i h2
      rw [hq] at this
      change q.1.1[q.1.2]? = some bs[i] at this
      rw [hql, hqj, List.getElem?_eq_getElem h1] at this
      exact Option.some_injective _ this
    rw [← hl]; exact q0.2.2.2
  · intro hI
    let vt : ℕ → TupleVertex I K := fun i =>
      ⟨(bs, min i (bs.length - 1)), hK, by simp only; omega, hI⟩
    refine ⟨fun i => .inr (vt i), fun i _ h => ?_, fun i hi => ?_, fun m hm h => ?_,
      fun m hm h => ?_, fun i hi => ?_⟩
    · change bs = bs ∧ min i (bs.length - 1) = min i (bs.length - 1) + 1 at h; omega
    · exact ⟨rfl, by simp only [vt]; omega⟩
    · rcases m with a | q
      · exact hm rfl
      · change bs = q.1.1 ∧ min 0 (bs.length - 1) = q.1.2 + 1 at h; omega
    · rcases m with a | q
      · exact hm rfl
      · change q.1.1 = bs ∧ q.1.2 = min (bs.length - 1) (bs.length - 1) + 1 at h
        have := q.2.2.1
        rw [h.1] at this
        omega
    · change bs[min i (bs.length - 1)]? = some bs[i]
      rw [show min i (bs.length - 1) = i by omega]
      exact List.getElem?_eq_getElem hi

/-- The loops of the tuple graph are the elements of `M`. -/
def tupleGraphLoopEquiv : M ≃ {g : M ⊕ TupleVertex I K // tupleGraph I K g g} where
  toFun a := ⟨.inl a, rfl⟩
  invFun g := match g with
    | ⟨.inl a, _⟩ => a
    | ⟨.inr q, h⟩ => absurd h (by simp [tupleGraph])
  left_inv _ := rfl
  right_inv g := by
    rcases g with ⟨a | q, h⟩
    · rfl
    · exact absurd h (by simp [tupleGraph])

private theorem coe_tupleGraphLoopEquiv_symm (g : {g : M ⊕ TupleVertex I K // tupleGraph I K g g}) :
    (g : M ⊕ TupleVertex I K) = .inl ((tupleGraphLoopEquiv I K).symm g) := by
  conv_lhs => rw [← (tupleGraphLoopEquiv I K).apply_symm_apply g]
  rfl

end Canonical

/-! ### The graph translation -/

/-- The graph translation with free variables below `B`: they are loops, and the formula is
interpreted with the loops as domain and the tuple gadgets as atoms. -/
def toGraph (B : ℕ) (ψ : RawFormula) : RawFormula :=
  conj (bigConj ((List.range (B + 1)).map loopAtom)) (interpret loopAtom (fun _ => tupleGadget B) ψ)

theorem atoms_toGraph (B : ℕ) (ψ : RawFormula) : ∀ a ∈ (toGraph B ψ).atoms, a = (0, 2) := by
  intro a h
  simp only [toGraph, conj, neg, atoms, List.append_nil, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨φ, hφ, h⟩ := atoms_bigConj h
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hφ
    simpa [loopAtom, edgeAtom, atoms] using h
  · exact atoms_interpret (Q := (· = (0, 2)))
      (fun x a h => by simpa [loopAtom, edgeAtom, atoms] using h)
      (fun _ args => atoms_tupleGadget B args) ψ a h

private theorem listRel_iff {G : Type*} {J : ℕ → List G → Prop} {as : List G} (h : as.length = 2) :
    J 0 as ↔ listRel (fun a b => J 0 [a, b]) as := by
  rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, as⟩⟩⟩
  · simp at h
  · simp at h
  · exact Iff.rfl
  · simp at h

private theorem realize_listRel_of_atoms {G : Type*} {J : ℕ → List G → Prop} {φ : RawFormula}
    (hφ : ∀ a ∈ φ.atoms, a = (0, 2)) (w : ℕ → G) :
    φ.Realize J w ↔ φ.Realize (fun _ => listRel fun a b => J 0 [a, b]) w := by
  refine realize_congr_rel φ w fun r as h => ?_
  obtain ⟨hr, hl⟩ := Prod.mk.inj (hφ _ h)
  subst hr
  exact listRel_iff hl

/-- The largest arity of an atom of `φ`. -/
private def arityBound (φ : RawFormula) : ℕ := (φ.atoms.map Prod.snd).foldr max 0

private theorem le_arityBound {φ : RawFormula} {a : ℕ × ℕ} (h : a ∈ φ.atoms) :
    a.2 ≤ arityBound φ := by
  unfold arityBound
  generalize φ.atoms = l at h ⊢
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem finSat_toGraph {ψ : RawFormula} (hψ : ∀ a ∈ ψ.atoms, a.1 = 0 ∧ 0 < a.2) :
    FinSat (toGraph ψ.varBound ψ) ↔ FinSat ψ := by
  constructor
  · rintro ⟨G, hf, -, J, w, h⟩
    rw [realize_listRel_of_atoms (atoms_toGraph _ ψ), toGraph, realize_conj, realize_bigConj] at h
    obtain ⟨hloop, h⟩ := h
    have hP : ∀ x ≤ ψ.varBound, J 0 [w x, w x] := fun x hx =>
      hloop (loopAtom x) (List.mem_map.2 ⟨x, List.mem_range.2 (by omega), rfl⟩)
    let P : G → Prop := fun g => J 0 [g, g]
    have hne : Nonempty (Subtype P) := ⟨⟨w 0, hP 0 (Nat.zero_le _)⟩⟩
    classical
    let u : ℕ → Subtype P := fun y =>
      if hy : P (w y) then ⟨w y, hy⟩ else Classical.arbitrary _
    have hwu : ∀ x < ψ.varBound, w x = u x := fun x hx => by
      simp only [u]
      split
      · rfl
      · exact absurd (hP x hx.le) ‹_›
    refine ⟨Subtype P, inferInstance, hne,
      fun _ bs => IsTupleGadget (fun a b => J 0 [a, b]) (bs.map Subtype.val), u, ?_⟩
    refine (realize_interpret (Q := fun a => a.1 = 0 ∧ 0 < a.2) (B := ψ.varBound)
      (fun x w => Iff.rfl) ?_ ψ hψ le_rfl w u hwu).1 h
    intro r args w' u' hargs hwu' hQ
    rw [realize_tupleGadget hQ.2 hargs, List.map_map,
      List.map_congr_left (g := Subtype.val ∘ u') fun x hx => hwu' x (hargs x hx)]
  · rintro ⟨M, _, _, I, v, h⟩
    let K := arityBound ψ
    have := instFiniteTupleVertex I K
    refine ⟨M ⊕ TupleVertex I K, inferInstance, inferInstance, fun _ => listRel (tupleGraph I K),
      Sum.inl ∘ v, ?_⟩
    rw [toGraph, realize_conj, realize_bigConj]
    refine ⟨fun φ hφ => ?_, ?_⟩
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hφ
      exact rfl
    · let e := tupleGraphLoopEquiv I K
      refine (realize_interpret (Q := fun a => a.1 = 0 ∧ 0 < a.2 ∧ a.2 ≤ K) (B := ψ.varBound)
        (R := fun r bs => I r (bs.map e.symm)) (fun x w => Iff.rfl) ?_ ψ
        (fun a ha => ⟨(hψ a ha).1, (hψ a ha).2, le_arityBound ha⟩) le_rfl
        (Sum.inl ∘ v) (e ∘ v) (fun x _ => rfl)).2 ((realize_equiv e I ψ v).2 h)
      intro r args w' u' hargs hwu' hQ
      have hr : r = 0 := hQ.1
      subst hr
      have hmap : args.map w' = (args.map (e.symm ∘ u')).map Sum.inl := by
        rw [List.map_map]
        exact List.map_congr_left fun x hx =>
          (hwu' x (hargs x hx)).trans (coe_tupleGraphLoopEquiv_symm I K _)
      rw [realize_tupleGadget hQ.2.1 hargs, hmap,
        isTupleGadget_tupleGraph_iff I K (by simpa using hQ.2.1) (by simpa using hQ.2.2),
        List.map_map]

/-! ### Primitive recursiveness -/

section Primrec

open Primrec

variable {α : Type*} [Primcodable α]

theorem Graph.primrec_edgeAtom {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => edgeAtom (f a) (g a) :=
  primrec_rel (const 0) (list_cons.comp hf (list_cons.comp hg (const [])))

theorem Graph.primrec_loopAtom : Primrec loopAtom := primrec_edgeAtom Primrec.id Primrec.id

theorem primrec₂_tupleGadgetBody : Primrec₂ tupleGadgetBody := by
  have hB : Primrec fun p : ℕ × List ℕ => p.1 := fst
  have hL : Primrec fun p : ℕ × List ℕ => p.2.length := list_length.comp snd
  have l1 : Primrec fun p : ℕ × List ℕ =>
      (List.range p.2.length).map fun i => neg (loopAtom (p.1 + i)) :=
    list_map (list_range.comp hL)
      (primrec_neg (primrec_loopAtom.comp (nat_add.comp (hB.comp fst) snd))).to₂
  have l2 : Primrec fun p : ℕ × List ℕ =>
      (List.range (p.2.length - 1)).map fun i => edgeAtom (p.1 + i + 1) (p.1 + i) :=
    list_map (list_range.comp (nat_sub.comp hL (const 1)))
      (primrec_edgeAtom (succ.comp (nat_add.comp (hB.comp fst) snd))
        (nat_add.comp (hB.comp fst) snd)).to₂
  have hBL : Primrec fun p : ℕ × List ℕ => p.1 + p.2.length := nat_add.comp hB hL
  have l3 : Primrec fun p : ℕ × List ℕ =>
      [all (p.1 + p.2.length) (imp (neg (loopAtom (p.1 + p.2.length)))
        (neg (edgeAtom p.1 (p.1 + p.2.length)))),
       all (p.1 + p.2.length) (imp (neg (loopAtom (p.1 + p.2.length)))
        (neg (edgeAtom (p.1 + p.2.length) (p.1 + p.2.length - 1))))] :=
    list_cons.comp (primrec_all hBL (primrec_imp (primrec_neg (primrec_loopAtom.comp hBL))
        (primrec_neg (primrec_edgeAtom hB hBL))))
      (list_cons.comp (primrec_all hBL (primrec_imp (primrec_neg (primrec_loopAtom.comp hBL))
        (primrec_neg (primrec_edgeAtom hBL (nat_sub.comp hBL (const 1)))))) (const []))
  have l4 : Primrec fun p : ℕ × List ℕ =>
      (List.range p.2.length).map fun i => edgeAtom (p.1 + i) (p.2.getD i 0) :=
    list_map (list_range.comp hL)
      (primrec_edgeAtom (nat_add.comp (hB.comp fst) snd)
        ((list_getD 0).comp (snd.comp fst) snd)).to₂
  exact (primrec_bigConj.comp (list_append.comp (list_append.comp (list_append.comp l1 l2) l3)
    l4)).to₂

theorem primrec₂_tupleGadget : Primrec₂ tupleGadget :=
  (primrec_exRange fst (list_length.comp snd) primrec₂_tupleGadgetBody).to₂

theorem primrec₂_toGraph : Primrec₂ toGraph :=
  (primrec_conj (primrec_bigConj.comp (list_map (list_range.comp (succ.comp fst))
    (primrec_loopAtom.comp snd).to₂))
    (primrec₂_interpret (D := fun _ => loopAtom) (θ := fun B _ => tupleGadget B)
      (primrec_loopAtom.comp snd).to₂ (primrec₂_tupleGadget.comp fst (snd.comp snd)).to₂)).to₂

end Primrec

end RawFormula

end Cslib.Logic.FO
