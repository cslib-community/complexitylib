/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter
import all CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

/-!
# The refuter's final search finds a counterexample

`findCounterexample C f d S` enumerates `2^d` points of `Φ(Z(P))` built from the free parameters
of `S`. When `S` is a valid terminal state for the function of `C` (no refuter step applies) with
`d < S.a`, the output of `S` is constant on the enumerated `d`-dimensional affine subspace, so a
`d`-affine disperser `f` disagrees with `C` at one of the enumerated points.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.findCounterexample_spec`: every returned point is a
  counterexample.
* `Cslib.Circuits.Boolean.AffineDisperser4n.findCounterexample_isSome`: on a valid terminal state
  with `d < S.a`, the search returns a point.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperserCore.State
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString

/-! ### List utilities -/

private theorem mem_allAssignments : ∀ {d : ℕ} {A : List Bool}, A.length = d → A ∈ allAssignments d
  | 0, A, h => by simp [allAssignments, List.eq_nil_of_length_eq_zero h]
  | d + 1, [], h => by simp at h
  | d + 1, b :: A, h => by
    have hA : A ∈ allAssignments d := mem_allAssignments (by simpa using h)
    cases b <;> simp [allAssignments, hA]

/-! ### `findPair` and `terminalVal` -/

variable {n : ℕ}

/-- A pair found by `findPair S x` is a pair of `S` containing `x`. -/
theorem findPair_spec {S : State n} {x : ℕ} {pr : ZeroPair} (h : findPair S x = some pr) :
    pr ∈ S.pairs ∧ (pr.fst = x ∨ pr.snd = x) := by
  obtain ⟨r, -, hr⟩ := List.exists_of_findSome?_eq_some h
  have hmem := List.mem_of_find?_eq_some hr
  have hp := List.find?_some hr
  refine ⟨by simpa using hp, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- On a valid state, `findPair S x` finds a pair whenever `x` belongs to one. -/
theorem findPair_isSome {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {pr : ZeroPair}
    (hpr : pr ∈ S.pairs) {x : ℕ} (hx : pr.Contains x) : (findPair S x).isSome := by
  have hmem := hS.pair_mem pr hpr
  obtain ⟨fst, b₁, snd, b₂⟩ := pr
  rcases hx with hx | hx <;> simp only at hx <;> subst hx
  · refine List.findSome?_isSome_iff.2 ⟨snd, (Finset.mem_sort _).2 hmem.2.1, ?_⟩
    exact List.find?_isSome.2 ⟨⟨fst, b₁, snd, b₂⟩, by cases b₁ <;> cases b₂ <;> simp,
      by simpa using hpr⟩
  · refine List.findSome?_isSome_iff.2 ⟨fst, (Finset.mem_sort _).2 hmem.1, ?_⟩
    exact List.find?_isSome.2 ⟨⟨fst, b₁, snd, b₂⟩, by cases b₁ <;> cases b₂ <;> simp,
      by simpa using hpr⟩

private theorem eq_of_findPair_eq_some {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {x : ℕ}
    {pr pr' : ZeroPair} (h : findPair S x = some pr') (hpr : pr ∈ S.pairs) (hx : pr.fst = x) :
    pr' = pr := by
  obtain ⟨hpr', hx'⟩ := findPair_spec h
  by_contra hne
  have := hS.pairs_disjoint pr' hpr' pr hpr hne
  rcases hx' with h' | h' <;> simp only at this <;> omega

private theorem isFstOfAnyPair_eq_true_iff {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {x : ℕ} : isFstOfAnyPair S x = true ↔ ∃ pr ∈ S.pairs, pr.fst = x := by
  constructor
  · unfold isFstOfAnyPair
    split
    · rename_i pr h
      intro hx
      exact ⟨pr, (findPair_spec h).1, by simpa using hx⟩
    · simp
  · rintro ⟨pr, hpr, hx⟩
    obtain ⟨pr', h'⟩ := Option.isSome_iff_exists.1 (findPair_isSome hS hpr (Or.inl hx))
    have := eq_of_findPair_eq_some hS h' hpr hx
    subst this
    unfold isFstOfAnyPair
    rw [h']
    simpa using hx

private theorem terminalVal_fst {f : BooleanFunction n} {S : State n} (hS : S.Valid f) (L : List ℕ)
    (A : List Bool) {pr : ZeroPair} (hpr : pr ∈ S.pairs) :
    terminalVal S L A pr.fst = pr.fstBias := by
  obtain ⟨pr', h'⟩ := Option.isSome_iff_exists.1 (findPair_isSome hS hpr (Or.inl rfl))
  have := eq_of_findPair_eq_some hS h' hpr rfl
  subst this
  unfold terminalVal
  rw [h']
  simp

private theorem findIdx?_eq_some_of_nodup {L : List ℕ} (hL : L.Nodup) {j : ℕ} (hj : j < L.length) :
    L.findIdx? (· = L[j]) = some j := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hj, by simp, fun k hk => ?_⟩
  have := (hL.getElem_inj_iff (i := k) (j := j) (hi := by omega) (hj := hj)).not.2 (by omega)
  simpa using this

private theorem terminalVal_of_getElem {S : State n} {L : List ℕ} (hL : L.Nodup) (A : List Bool)
    {j : ℕ} (hj : j < L.length) (hfst : isFstOfAnyPair S L[j] = false) :
    terminalVal S L A L[j] = A.getD j false := by
  unfold terminalVal
  rw [findIdx?_eq_some_of_nodup hL hj]
  unfold isFstOfAnyPair at hfst
  split
  · rename_i pr h
    rw [h] at hfst
    have : pr.fst ≠ L[j] := by simpa using hfst
    simp [this]
  · rfl

private theorem isAffine_getD_ofFn {d : ℕ} (i : ℕ) :
    IsAffine fun u : BitString d => (List.ofFn u).getD i false := by
  intro a b c
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hi : i < d
  · simp [hi]
  · simp only [hi, ↓reduceDIte, Option.getD_none]
    rfl

private theorem isAffine_terminalVal {d : ℕ} (S : State n) (L : List ℕ) (x : ℕ) :
    IsAffine fun u : BitString d => terminalVal S L (List.ofFn u) x := by
  unfold terminalVal
  rcases findPair S x with _ | pr
  · rcases L.findIdx? (· = x) with _ | i
    · exact Cslib.BitString.isAffine_const (fun b => Bool.xor_self b) false
    · exact isAffine_getD_ofFn i
  · by_cases h : pr.fst = x
    · simpa [h] using Cslib.BitString.isAffine_const (fun b => Bool.xor_self b) pr.fstBias
    · simp only [h, ite_false]
      rcases L.findIdx? (· = x) with _ | i
      · exact Cslib.BitString.isAffine_const (fun b => Bool.xor_self b) false
      · exact isAffine_getD_ofFn i

/-! ### The free parameters -/

/-- The free parameters scanned by `findCounterexample`. -/
private abbrev freeParams (S : State n) : List ℕ :=
  (S.params.sort (· ≤ ·)).filter (fun x => !(isFstOfAnyPair S x))

private theorem nodup_freeParams (S : State n) : (freeParams S).Nodup :=
  (Finset.sort_nodup _ _).filter _

private theorem mem_freeParams {S : State n} {x : ℕ} :
    x ∈ freeParams S ↔ x ∈ S.params ∧ isFstOfAnyPair S x = false := by
  simp [freeParams]

private theorem length_freeParams {f : BooleanFunction n} {S : State n} (hS : S.Valid f) :
    (freeParams S).length = S.a := by
  rw [← List.toFinset_card_of_nodup (nodup_freeParams S),
    ← hS.card_sdiff_image ZeroPair.fst (fun _ _ => Or.inl rfl)]
  congr 1
  ext x
  rw [List.mem_toFinset, mem_freeParams, Finset.mem_sdiff, Finset.mem_image]
  refine and_congr_right fun _ => ?_
  rw [← Bool.not_eq_true, isFstOfAnyPair_eq_true_iff hS]

/-! ### The generic search -/

private theorem inj_of_coords {d : ℕ} {S : State n} (σ : List Bool → ℕ → Bool) {L : List ℕ}
    (hLp : ∀ x ∈ L, x ∈ S.params) (hlen : L.length = d)
    (hcoord : ∀ A j (hj : j < L.length), σ A L[j] = A.getD j false) :
    ∀ u v : BitString d, (∀ j ∈ S.params, σ (List.ofFn u) j = σ (List.ofFn v) j) → u = v := by
  intro u v h
  funext ⟨j, hj⟩
  have hj' : j < L.length := hlen ▸ hj
  have := h L[j] (hLp _ (List.getElem_mem hj'))
  rw [hcoord _ _ hj', hcoord _ _ hj'] at this
  simpa [List.getD_eq_getElem?_getD, hj] using this

private theorem findSome_isSome_of_family {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d) {S : State n}
    (hS : S.Valid (fun x => C.eval fullInterpretation x 0)) (σ : List Bool → ℕ → Bool)
    (hσ : ∀ x, IsAffine fun u : BitString d => σ (List.ofFn u) x)
    {L : List ℕ} (hLp : ∀ x ∈ L, x ∈ S.params) (hlen : L.length = d)
    (hcoord : ∀ A j (hj : j < L.length), σ A L[j] = A.getD j false)
    (hlocus : ∀ A, ∀ pr ∈ S.pairs, σ A pr.fst = pr.fstBias) (b : Bool)
    (hout : ∀ A val, S.Consistent val → (∀ j ∈ S.params, val j = σ A j) → S.out.eval val = b) :
    ((allAssignments d).findSome? fun A =>
      let x_vec : BitString n := S.phi fun y =>
        if decide (y ∈ S.params) then σ A y else evaluateAux S y (σ A)
      if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none).isSome := by
  set g : BitString d → BitString n := fun u => S.phi (σ (List.ofFn u)) with hg_def
  have hgaff : IsAffine g := by
    have : IsAffine fun u : BitString d => σ (List.ofFn u) :=
      fun x y z => funext fun i => hσ i x y z
    exact hS.phi_affine.comp this
  have hginj : Function.Injective g := fun u v h =>
    inj_of_coords σ hLp hlen hcoord u v (hS.phi_injective _ _ h)
  have hval : ∀ w, C.eval fullInterpretation (g w) 0 = b := by
    intro w
    obtain ⟨val, hv, hcons⟩ := hS.wf.exists_consistent (σ (List.ofFn w))
    have hlv : S.Locus val := fun pr hpr =>
      ZeroPair.holds_of_eq_bias (x := pr.fst) (Or.inl rfl) (by
        rw [hv _ (hS.pair_mem pr hpr).1, hlocus _ pr hpr]
        simp [ZeroPair.bias])
    have := hS.computes val hcons hlv
    rw [hout _ val hcons hv, hS.phi_congr val _ hv] at this
    exact this.symm
  obtain ⟨u, v, huv⟩ := hf g hgaff hginj
  have hx : ∀ w, (S.phi fun y => if decide (y ∈ S.params) then σ (List.ofFn w) y else
      evaluateAux S y (σ (List.ofFn w))) = g w :=
    fun w => hS.phi_congr _ _ fun j hj => by simp [hj]
  have key : ∃ w, C.eval fullInterpretation (g w) 0 ≠ f (g w) := by
    by_cases hu : C.eval fullInterpretation (g u) 0 = f (g u)
    · exact ⟨v, fun hv => huv (by rw [← hu, ← hv, hval, hval])⟩
    · exact ⟨u, hu⟩
  obtain ⟨w, hw⟩ := key
  refine List.findSome?_isSome_iff.2
    ⟨List.ofFn w, mem_allAssignments (A := List.ofFn w) (by simp), ?_⟩
  simp only [hx w]
  simp [hw]

private theorem terminalVal_coord {S : State n} {L : List ℕ} (hLn : L.Nodup)
    (hLF : ∀ x ∈ L, x ∈ freeParams S) (A : List Bool) (j : ℕ) (hj : j < L.length) :
    terminalVal S L A L[j] = A.getD j false :=
  terminalVal_of_getElem hLn A hj (mem_freeParams.1 (hLF _ (List.getElem_mem hj))).2

private theorem take_props {S : State n} {L₀ : List ℕ} (hn : L₀.Nodup)
    (hF : ∀ x ∈ L₀, x ∈ freeParams S)
    {d : ℕ} (hd : d ≤ L₀.length) :
    (L₀.take d).Nodup ∧ (∀ x ∈ L₀.take d, x ∈ freeParams S) ∧ (L₀.take d).length = d :=
  ⟨hn.sublist (List.take_sublist _ _), fun x hx => hF x (List.mem_of_mem_take hx),
    by rw [List.length_take]; omega⟩

private theorem fst_ne_of_mem_freeParams {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {p : ℕ} (hp : p ∈ freeParams S) {pr : ZeroPair} (hpr : pr ∈ S.pairs) : pr.fst ≠ p := by
  rintro rfl
  have := (mem_freeParams.1 hp).2
  rw [← Bool.not_eq_true, isFstOfAnyPair_eq_true_iff hS] at this
  exact this ⟨pr, hpr, rfl⟩

/-- The search over the free parameters `L` with `terminalVal` succeeds when the output is
constant on the corresponding consistent assignments. -/
private theorem findSome_isSome_terminalVal {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d) {S : State n}
    (hS : S.Valid (fun x => C.eval fullInterpretation x 0)) {L : List ℕ}
    (hL : L.Nodup ∧ (∀ x ∈ L, x ∈ freeParams S) ∧ L.length = d) (b : Bool)
    (hout : ∀ A val, S.Consistent val → (∀ j ∈ S.params, val j = terminalVal S L A j) →
      S.out.eval val = b) :
    ((allAssignments d).findSome? fun A =>
      let x_vec : BitString n := S.phi fun y =>
        if decide (y ∈ S.params) then terminalVal S L A y else evaluateAux S y (terminalVal S L A)
      if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none).isSome :=
  findSome_isSome_of_family C f hf hS (fun A => terminalVal S L A) (isAffine_terminalVal S L)
    (fun x hx => (mem_freeParams.1 (hL.2.1 x hx)).1) hL.2.2 (terminalVal_coord hL.1 hL.2.1)
    (fun A _ hpr => terminalVal_fst hS L A hpr) b hout

private theorem foldl_xor_eq_sum (g : ℕ → Bool) (T : Finset ℕ) :
    (T.sort (· ≤ ·)).foldl (fun acc y => acc ^^ g y) false = ∑ y ∈ T, g y := by
  change (T.sort (· ≤ ·)).foldl (fun acc y => acc + g y) 0 = ∑ y ∈ T, g y
  rw [← List.foldl_map, ← List.sum_eq_foldl, ← List.sum_toFinset _ (Finset.sort_nodup _ _)]
  rw [Finset.sort_toFinset]

private theorem filter_ne_take_props {f : BooleanFunction n} {S : State n} (hS : S.Valid f) {p : ℕ}
    (hp : p ∈ freeParams S) {d : ℕ} (hd : d < S.a) :
    ((((freeParams S).filter (fun x => decide (x ≠ p))).take d).Nodup ∧
      (∀ x ∈ ((freeParams S).filter (fun x => decide (x ≠ p))).take d, x ∈ freeParams S) ∧
      (((freeParams S).filter (fun x => decide (x ≠ p))).take d).length = d) ∧
      ∀ x ∈ ((freeParams S).filter (fun x => decide (x ≠ p))).take d, x ≠ p := by
  refine ⟨?_, fun x hx => by simpa using (List.mem_filter.1 (List.mem_of_mem_take hx)).2⟩
  refine take_props ((nodup_freeParams S).filter _) (fun x hx => (List.mem_filter.1 hx).1) ?_
  have hfe : (freeParams S).filter (fun x => decide (x ≠ p)) = (freeParams S).erase p := by
    rw [(nodup_freeParams S).erase_eq_filter]
    congr 1
  rw [hfe, List.length_erase_of_mem hp, length_freeParams hS]
  omega

private theorem op_const_of_not_isAffineOp :
    ∀ op : Bool → Bool → Bool, ¬ IsAffineOp op →
      op (decide ((op true false == op true true) = true)) false =
        op (decide ((op true false == op true true) = true)) true := by
  intro op h
  simp only [beq_iff_eq]
  rw [and_form_spec h (decide (op true false = op true true)) false,
    and_form_spec h (decide (op true false = op true true)) true]
  cases decide (op true false = op true true) <;>
    cases decide (op false true = op true true) <;> rfl

private theorem terminal_gate {S : State n} {u : ℕ} (hterm : chooseStep? S = none)
    (hu : S.out.arg = .node u) (hup : u ∉ S.params) (hne : S.gates.Nonempty) :
    findD1 S = none ∧ findMovable S = none ∧ findAndOnPair S = none ∧
      S.auxIn (S.gates.min' hne) = 0 ∧ u = S.gates.min' hne := by
  unfold chooseStep? at hterm
  rw [hu] at hterm
  simp only [hup, ite_false] at hterm
  repeat' split at hterm
  all_goals try (simp at hterm; done)
  all_goals first
    | exact absurd hne ‹¬S.gates.Nonempty›
    | exact ⟨Option.eq_none_iff_forall_ne_some.2 fun p hp =>
          ‹∀ p, findD1 S = some p → False› p hp,
        Option.eq_none_iff_forall_ne_some.2 fun p hp =>
          ‹∀ p, findMovable S = some p → False› p hp,
        Option.eq_none_iff_forall_ne_some.2 fun p hp =>
          ‹∀ G p, findAndOnPair S = some (G, p) → False› p.1 p.2 hp,
        Nat.eq_zero_of_not_pos ‹_›, ‹u = S.gates.min' _›⟩

private theorem terminal_gate_shape {f : BooleanFunction n} {S : State n} (hS : S.Valid f) {u : ℕ}
    (hterm : chooseStep? S = none) (hu : S.out.arg = .node u) (hup : u ∉ S.params)
    (hne : S.gates.Nonempty) :
    ∃ t₁ t₂, (S.gate (S.gates.min' hne)).left = .node t₁ ∧
      (S.gate (S.gates.min' hne)).right = .node t₂ ∧ t₁ ∈ S.params ∧ ¬ S.Paired t₁ ∧
      ¬ IsAffineOp (S.gate (S.gates.min' hne)).op ∧ u = S.gates.min' hne := by
  obtain ⟨h1, hm, hA, haux, huG⟩ := terminal_gate hterm hu hup hne
  set G := S.gates.min' hne with hG_def
  have hG : G ∈ S.gates := Finset.min'_mem _ _
  have hGs : G ∈ S.gates.sort (· ≤ ·) := (Finset.mem_sort _).2 hG
  have hargs : ∃ t₁ t₂, (S.gate G).left = .node t₁ ∧ (S.gate G).right = .node t₂ ∧ t₁ ≠ t₂ := by
    have hdeg := List.find?_eq_none.1 h1 G hGs
    unfold isDegenerate at hdeg
    rcases hl : (S.gate G).left with b₁ | t₁ <;> rcases hr : (S.gate G).right with b₂ | t₂ <;>
      simp only [hl, hr, not_true_eq_false, decide_eq_true_eq] at hdeg
    exact ⟨t₁, t₂, rfl, rfl, hdeg⟩
  obtain ⟨t₁, t₂, hl, hr, h12⟩ := hargs
  have hnotgate : ∀ t, (S.gate G).Reads t → t ∉ S.gates := fun t ht htg =>
    absurd (hS.wf.reads_lt G hG t htg ht) (not_lt.2 (Finset.min'_le _ _ htg))
  have hparam : ∀ t, (S.gate G).Reads t → t ∉ S.aux → t ∈ S.params := fun t ht hta => by
    have := hS.wf.reads_live G hG t ht
    simp only [live, Finset.mem_union] at this
    tauto
  have ht₁a : t₁ ∉ S.aux := fun h => by
    unfold State.auxIn State.auxArg at haux
    rw [hl] at haux
    simp [h] at haux
  have ht₂a : t₂ ∉ S.aux := fun h => by
    unfold State.auxIn State.auxArg at haux
    rw [hr] at haux
    simp [h] at haux
  have ht₁p := hparam t₁ (Or.inl hl) ht₁a
  have ht₂p := hparam t₂ (Or.inr hr) ht₂a
  have hnaff : ¬ IsAffineOp (S.gate G).op := by
    have := List.find?_eq_none.1 hm G hGs
    simpa [hl, hr, isGate, hnotgate t₁ (Or.inl hl), hnotgate t₂ (Or.inr hr)] using this
  have hpaired : ¬ S.Paired t₁ := by
    have := List.findSome?_eq_none_iff.1 hA G hGs
    simp only [hl, hr] at this
    simp only [hnaff, ht₁p, ht₂p] at this
    intro hp
    simp only [not_false_eq_true, ↓reduceIte, ne_eq, and_self, and_true, hp, ite_not,
      ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not] at this
    exact h12 this
  exact ⟨t₁, t₂, hl, hr, ht₁p, hpaired, hnaff, huG⟩

/-- On a valid terminal state of the refuter for the function of `C` with `d < S.a`, the final
search of `findCounterexample` succeeds. -/
theorem findCounterexample_isSome {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d) {S : State n}
    (hS : S.Valid (fun x => C.eval fullInterpretation x 0)) (hterm : chooseStep? S = none)
    (ha : d < S.a)
    (hrep : ∀ u ∈ S.aux, S.AffineIn u (findAffineRep S u).1 (findAffineRep S u).2) :
    (findCounterexample C f d S).isSome := by
  unfold findCounterexample
  split
  · rename_i b hb
    refine findSome_isSome_terminalVal C f hf hS
      (take_props (nodup_freeParams S) (fun _ h => h) (by rw [length_freeParams hS]; omega))
      (b ^^ S.out.neg) fun A val _ _ => ?_
    simp [Lit.eval, hb, Arg.eval]
  · rename_i u hu
    split
    · rename_i hcase
      split
      rename_i c_out T_out hpair
      have hAff : S.AffineIn u c_out T_out := by
        by_cases hup : u ∈ S.params
        · simp only [hup, decide_true, ite_true, Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          exact affineIn_param hup
        · simp only [hup, decide_false, Bool.false_eq_true, ite_false] at hpair
          have hg : S.gates = ∅ := by simpa [hup] using hcase
          have hu_aux : u ∈ S.aux := by
            have := hS.wf.out_live u hu
            simpa [live, hup, hg] using this
          have := hrep u hu_aux
          rw [hpair] at this
          exact this
      dsimp only
      split
      · rename_i pivot hpiv
        have hpF : pivot ∈ freeParams S := List.mem_of_find?_eq_some hpiv
        have hpT : pivot ∈ T_out := by simpa using List.find?_some hpiv
        set L := ((freeParams S).filter (fun x => decide (x ≠ pivot))).take d with hL_def
        obtain ⟨hLp, hLne⟩ := filter_ne_take_props hS hpF ha
        refine findSome_isSome_of_family C f hf hS
          (fun A y => if y = pivot then (c_out ^^ S.out.neg ^^
            List.foldl (fun acc y => acc ^^ terminalVal S L A y) false
              ({x ∈ T_out | x ≠ pivot}.sort (· ≤ ·))) else terminalVal S L A y)
          ?_ (fun x hx => (mem_freeParams.1 (hLp.2.1 x hx)).1) hLp.2.2 ?_ ?_ false ?_
        · intro x
          by_cases hx : x = pivot
          · simp only [hx, ite_true, foldl_xor_eq_sum]
            have := isAffine_const_add_sum
              (σ := fun u : BitString d => fun y => terminalVal S L (List.ofFn u) y)
              (fun a b c => funext fun y => isAffine_terminalVal S L y a b c)
              (c_out ^^ S.out.neg) {x ∈ T_out | x ≠ pivot}
            exact this
          · simpa [hx] using isAffine_terminalVal S L x
        · intro A j hj
          rw [ite_eq_right (hLne _ (List.getElem_mem hj))]
          exact terminalVal_coord hLp.1 hLp.2.1 A j hj
        · intro A pr hpr
          rw [ite_eq_right (fst_ne_of_mem_freeParams hS hpF hpr)]
          exact terminalVal_fst hS L A hpr
        · intro A val hcons hval
          have h1 := hAff.2 val hcons.1
          simp only [Lit.eval, hu, Arg.eval, h1]
          rw [← Finset.add_sum_erase _ _ hpT, hval pivot (hAff.1 hpT), ite_eq_left rfl,
            foldl_xor_eq_sum, Finset.filter_ne',
            Finset.sum_congr rfl fun y hy => (hval y (hAff.1 (Finset.mem_of_mem_erase hy))).trans
              (ite_eq_right (Finset.ne_of_mem_erase hy))]
          generalize ∑ y ∈ T_out.erase pivot, terminalVal S L A y = X
          cases c_out <;> cases S.out.neg <;> cases X <;> rfl
      · rename_i hpiv
        have hnot : ∀ v ∈ freeParams S, v ∉ T_out := fun v hv => by
          simpa using List.find?_eq_none.1 hpiv v hv
        refine findSome_isSome_terminalVal C f hf hS
          (take_props (nodup_freeParams S) (fun _ h => h) (by rw [length_freeParams hS]; omega))
          ((c_out + ∑ y ∈ T_out, terminalVal S ((freeParams S).take d) [] y) ^^ S.out.neg)
          fun A val hcons hval => ?_
        have hsum : ∑ y ∈ T_out, val y =
            ∑ y ∈ T_out, terminalVal S ((freeParams S).take d) [] y := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hyp := hAff.1 hy
          have hfst : isFstOfAnyPair S y = true := by
            by_contra h
            exact hnot y (mem_freeParams.2 ⟨hyp, by simpa using h⟩) hy
          obtain ⟨pr, hpr, rfl⟩ := (isFstOfAnyPair_eq_true_iff hS).1 hfst
          rw [hval _ hyp, terminalVal_fst hS _ _ hpr, terminalVal_fst hS _ _ hpr]
        simp only [Lit.eval, hu, Arg.eval, hAff.2 val hcons.1, hsum]
    · rename_i hcase
      split
      · rename_i hne
        have hup : u ∉ S.params := fun h => by simp [h] at hcase
        obtain ⟨t₁, t₂, hl, hr, ht₁p, ht₁u, hnaff, huG⟩ :=
          terminal_gate_shape hS hterm hu hup hne
        have ht₁F : t₁ ∈ freeParams S := mem_freeParams.2 ⟨ht₁p, by
          rw [← Bool.not_eq_true, isFstOfAnyPair_eq_true_iff hS]
          rintro ⟨pr, hpr, rfl⟩
          exact ht₁u ⟨pr, hpr, Or.inl rfl⟩⟩
        dsimp only
        simp only [hl]
        set L := ((freeParams S).filter (fun x => decide (x ≠ t₁))).take d with hL_def
        obtain ⟨hLp, hLne⟩ := filter_ne_take_props hS ht₁F ha
        set op := (S.gate (S.gates.min' hne)).op with hop
        refine findSome_isSome_of_family C f hf hS
          (fun A y => if y = t₁ then decide ((op true false == op true true) = true)
            else terminalVal S L A y)
          ?_ (fun x hx => (mem_freeParams.1 (hLp.2.1 x hx)).1) hLp.2.2 ?_ ?_
          (op (decide ((op true false == op true true) = true)) false ^^ S.out.neg) ?_
        · intro x
          by_cases hx : x = t₁
          · simpa [hx] using
              Cslib.BitString.isAffine_const (fun b => Bool.xor_self b)
                (decide ((op true false == op true true) = true))
          · simpa [hx] using isAffine_terminalVal S L x
        · intro A j hj
          rw [ite_eq_right (hLne _ (List.getElem_mem hj))]
          exact terminalVal_coord hLp.1 hLp.2.1 A j hj
        · intro A pr hpr
          rw [ite_eq_right (fun h => ht₁u ⟨pr, hpr, Or.inl h⟩)]
          exact terminalVal_fst hS L A hpr
        · intro A val hcons hval
          have hG := hcons.2 _ (Finset.min'_mem _ hne)
          have h1 : val t₁ = decide ((op true false == op true true) = true) := by
            rw [hval _ ht₁p, ite_eq_left rfl]
          simp only [Lit.eval, hu, Arg.eval, huG, hG, Gate.eval, hl, hr, h1]
          rw [← hop]
          congr 1
          cases val t₂
          · rfl
          · exact (op_const_of_not_isAffineOp op hnaff).symm
      · rename_i hne
        exfalso
        have hcard : S.gates.card ≠ 0 := fun h => by simp [h] at hcase
        exact hne (Finset.card_pos.1 (Nat.pos_of_ne_zero hcard))

private theorem findSome_neq {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool)
    {g : List Bool → BitString n} {x : BitString n}
    (h : (allAssignments d).findSome? (fun A =>
      if C.eval fullInterpretation (g A) 0 != f (g A) then some (g A) else none) = some x) :
    C.eval fullInterpretation x 0 ≠ f x := by
  obtain ⟨A, -, hA⟩ := List.exists_of_findSome?_eq_some h
  split at hA
  · rename_i hne
    cases hA
    simpa using hne
  · cases hA

/-- Every input returned by `findCounterexample` is a counterexample. -/
theorem findCounterexample_spec {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (S : State n) {x : BitString n}
    (h : findCounterexample C f d S = some x) : C.eval fullInterpretation x 0 ≠ f x := by
  unfold findCounterexample at h
  repeat' (first | (dsimp only at h; split at h) | split at h)
  all_goals first | exact findSome_neq C f h | cases h

end Cslib.Circuits.Boolean.AffineDisperser4n
