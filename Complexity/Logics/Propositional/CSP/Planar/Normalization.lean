/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.CyclicDifference.Boundary
public import Complexity.Foundations.Data.BitString.DeltaMatroid.Operations
public import Complexity.Logics.Propositional.CSP.Planar.Crossover
public import Complexity.Logics.Propositional.CSP.PrimitivePositive.Operations
import Mathlib.Tactic.IntervalCases

/-!
# Ordered normalization of a cyclic exchange obstruction

This is an original reconstruction of the combinatorial argument missing from
[DvorakKupec2015], §4, printed p. 440, Lemma 6 (ICALP 2015 version,
DOI 10.1007/978-3-662-47672-7_35). That version supplies the statement only.
The source's ordered difference convention is `cyclicDifference`; its standardized endpoint
is the existing `IsStandardizedInconsistent`. Nonemptiness is explicit, so an empty relation
cannot supply a spurious failed exchange.

The finite program records only cyclic rotation, adjacent equality identification and the
specific two-difference cap. Its execution changes actual CSP scopes, starting with one literal
of the input relation and one or two disequality spokes per port. There are no Boolean constants.
This module does not declare a planar expressibility relation or prove a geometric realization,
planar substitution, hardness reduction, or running-time bound. Realizing each recorded operation
in the existing geometric model remains separate work.

## Main definitions

* `Cslib.BitString.CyclicExchangeObstruction`: feasible failed-exchange invariant.
* `Cslib.Logic.PL.CSP.Normalization.Program`: typed finite ordered boundary operations.
* `Cslib.Logic.PL.CSP.Normalization.Construction`: the twist, rotation and completed recipe.

## Main results

* `Cslib.Logic.PL.CSP.Normalization.exists_construction`: arbitrary-arity normalization.
* `Cslib.Logic.PL.CSP.Normalization.Construction.gadget`: the actual finite conjunction.
* `Cslib.Logic.PL.CSP.Normalization.Construction.numAux_bound`: at most `3n-4` auxiliaries.
-/

public section

namespace Cslib.Logic.PL.CSP.Normalization

open Cslib.BitString

/-- The two symbols used by normalization: one input relation and binary disequality. -/
inductive Symbol where
  /-- The original relation, of arbitrary arity. -/
  | relation
  /-- Boolean disequality, of arity two. -/
  | disequality
  deriving DecidableEq

/-- Reconstruct a normalization symbol from its constructor index. -/
add_decl_doc Symbol.ofNat_ctorIdx

/-- Declared widths of normalization constraints. -/
@[expose] def arity (n : ℕ) : Symbol → ℕ
  | .relation => n
  | .disequality => 2

/-- Width-guarded interpretation of the original relation and disequality.
The classical membership decision is fixed-language preprocessing, with no runtime claim. -/
@[expose] noncomputable def sem {n : ℕ} (R : Set (Fin n → Bool)) :
    Symbol → List Bool → Bool := by
  classical
  exact fun r xs => match r with
  | .relation => if h : xs.length = n then
      decide ((fun i : Fin n => xs[i.val]'(by omega)) ∈ R) else false
  | .disequality => match xs with
      | [a, b] => decide (a ≠ b)
      | _ => false

/-- The input symbol evaluates its tuple in exactly the original port order. -/
@[simp] theorem sem_relation {n : ℕ} (R : Set (Fin n → Bool)) (x : Fin n → Bool) :
    sem R .relation (List.ofFn x) = true ↔ x ∈ R := by
  classical
  simp [sem]

/-- Binary disequality has exactly its ordinary Boolean semantics. -/
@[simp] theorem sem_disequality {n : ℕ} (R : Set (Fin n → Bool)) (a b : Bool) :
    sem R .disequality [a, b] = true ↔ a ≠ b := by
  classical
  simp [sem]

/-- The initial twist relation: translate all original ports by a fixed feasible tuple. -/
@[expose] def twist {n : ℕ} (R : Set (Fin n → Bool)) (a : Fin n → Bool) :
    Set (Fin n → Bool) := {x | x + a ∈ R}

/-- A single original constraint and radial disequality chains. The first `n` auxiliaries
are the inner ports; the next `n` are the middle ports for the two-edge chains. A flipped port
uses one disequality; an unchanged port uses two. Free and inner labels remain distinct. -/
@[expose] def twistBody {n : ℕ} (a : Fin n → Bool) :
    CSP Symbol (Fin n ⊕ Fin (n + n)) :=
  (.relation, List.ofFn (fun i : Fin n => Sum.inr (i.castAdd n))) ::
    (List.finRange n).flatMap (fun i =>
      if a i then [(.disequality, [.inr (i.castAdd n), .inl i])]
      else [(.disequality, [.inr (i.castAdd n), .inr (i.natAdd n)]),
        (.disequality, [.inr (i.natAdd n), .inl i])])

/-- The initial conjunction uses at most `1+2n` constraints and total scope width `5n`. -/
theorem twistBody_size {n : ℕ} (a : Fin n → Bool) :
    (twistBody a).length ≤ 1 + 2 * n ∧ (twistBody a).vars.length ≤ 5 * n := by
  let f : Fin n → CSP Symbol (Fin n ⊕ Fin (n + n)) := fun i =>
    if a i then [(.disequality, [.inr (i.castAdd n), .inl i])]
    else [(.disequality, [.inr (i.castAdd n), .inr (i.natAdd n)]),
      (.disequality, [.inr (i.natAdd n), .inl i])]
  have hl (L : List (Fin n)) : (L.flatMap f).length ≤ 2 * L.length := by
    induction L with
    | nil => simp
    | cons i L ih => cases ha : a i <;> simp [f, ha] at * <;> omega
  have hw (L : List (Fin n)) : ((L.flatMap f).flatMap Prod.snd).length ≤ 4 * L.length := by
    induction L with
    | nil => simp
    | cons i L ih => cases ha : a i <;> simp [f, ha] at * <;> omega
  have hc := hl (List.finRange n)
  have hv := hw (List.finRange n)
  simp only [List.length_finRange] at hc hv
  constructor
  · change ((List.finRange n).flatMap f).length + 1 ≤ 1 + 2 * n
    omega
  · change (List.ofFn (fun i : Fin n => Sum.inr (i.castAdd n)) ++
      (((List.finRange n).flatMap f).flatMap Prod.snd)).length ≤ 5 * n
    rw [List.length_append, List.length_ofFn]
    omega

/-- Exact scope widths of the initial conjunction, including arities zero and one. -/
theorem wellFormed_twistBody {n : ℕ} (a : Fin n → Bool) :
    WellFormed (arity n) (twistBody a) := by
  intro c hc
  simp only [twistBody, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨i, _, hc⟩
  · simp [arity]
  · split_ifs at hc
    · simp only [List.mem_singleton] at hc
      subst c
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl

/-- The existential witnesses of the initial twist are exactly the spoke equations and
one original relation test. Unused middle ports on flipped spokes are unrestricted. -/
theorem eval_twistBody_iff {n : ℕ} (R : Set (Fin n → Bool)) (a x : Fin n → Bool)
    (b : Fin (n + n) → Bool) :
    (twistBody a).eval (sem R) (Sum.elim x b) = true ↔
      (fun i => b (i.castAdd n)) ∈ R ∧
      ∀ i, if a i then b (i.castAdd n) ≠ x i
        else b (i.castAdd n) ≠ b (i.natAdd n) ∧ b (i.natAdd n) ≠ x i := by
  classical
  unfold twistBody eval
  rw [List.all_cons, List.all_flatMap]
  simp only [Bool.and_eq_true, Constraint.eval, List.map_ofFn,
    sem_relation, Function.comp_def, Sum.elim_inr]
  apply and_congr Iff.rfl
  rw [List.all_eq_true]
  simp only [List.mem_finRange, forall_true_left]
  apply forall_congr'
  intro i
  cases ha : a i <;> simp [Constraint.eval]

/-- The actual twist gadget; it uses one original literal and at most two disequalities
per port, with `2n` auxiliary labels. -/
@[expose] noncomputable def twistGadget {n : ℕ} (R : Set (Fin n → Bool))
    (a : Fin n → Bool) : PPGadget (arity n) (sem R) (twist R a) where
  numAux := n + n
  body := twistBody a
  wellFormed := wellFormed_twistBody a
  correct x := by
    simp only [eval_twistBody_iff]
    constructor
    · intro hx
      refine ⟨Fin.addCases (x + a) (fun i => !x i), ?_, ?_⟩
      · change x + a ∈ R at hx
        simpa only [Fin.addCases_left] using hx
      · intro i
        simp only [Fin.addCases_left, Fin.addCases_right, Pi.add_apply, Bool.add_eq_xor]
        cases ha : a i <;> cases hx : x i <;> simp
    · rintro ⟨b, hb, hs⟩
      have he : (fun i => b (i.castAdd n)) = x + a := by
        funext i
        have hi := hs i
        cases ha : a i <;> cases hx : x i <;> cases hu : b (i.castAdd n) <;>
          cases hz : b (i.natAdd n) <;> simp_all [Bool.add_eq_xor]
      change x + a ∈ R
      rwa [← he]

/-- A cyclic change of starting port, with orientation preserved. -/
@[expose] def rotate {n : ℕ} (e : Fin n) (P : Set (Fin n → Bool)) :
    Set (Fin n → Bool) := {y | y ∘ (finCycle e).symm ∈ P}

instance {n : ℕ} (e : Fin n) (P : Set (Fin n → Bool)) [DecidablePred (· ∈ P)] :
    DecidablePred (· ∈ rotate e P) := fun y =>
  inferInstanceAs (Decidable (y ∘ (finCycle e).symm ∈ P))

/-- A finite typed sequence of the permitted ordered boundary operations. It is executable
program data; its constructors are coordinate maps, not planar closure assumptions. -/
inductive Program : ℕ → ℕ → Type where
  /-- Keep the current ordered boundary. -/
  | done (n : ℕ) : Program n n
  /-- Change only the cyclic starting port. -/
  | rotate {n m : ℕ} (e : Fin n) (rest : Program n m) : Program n m
  /-- Identify adjacent ports and delete the redundant port, with the explicit wraparound map. -/
  | zero {n m : ℕ} (i : Fin (n + 2)) (rest : Program (n + 1) m) : Program (n + 2) m
  /-- Identify old ports 1 and 3 and hide old port 2; retain free order `0,1,4,…`.
The lower bound excludes degenerate short boundaries in the intended geometric realization. -/
  | cap {n m : ℕ} (large : 2 ≤ n) (rest : Program (n + 2) m) : Program (n + 4) m

/-- Execute the recorded coordinate maps on boundary relations. -/
@[expose] def Program.eval {n m : ℕ} (p : Program n m) (P : Set (Fin n → Bool)) :
    Set (Fin m → Bool) := match p with
  | .done _ => P
  | .rotate e rest => rest.eval (Normalization.rotate e P)
  | .zero i rest => rest.eval (zeroRestriction i P)
  | .cap _ rest => rest.eval (capRelation P)

/-- Compile the recorded operations by relabeling the actual conjunction. The cap adds exactly
one fresh auxiliary; rotation and zero deletion add none. No original constraints are replaced. -/
@[expose] def Program.gadget {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool} :
    {n m : ℕ} → (p : Program n m) → {P : Set (Fin n → Bool)} →
      (g : PPGadget ar s P) → PPGadget ar s (p.eval P)
  | _, _, .done _, _, g => g
  | _, _, .rotate e rest, _, g => rest.gadget (g.relabelFree (finCycle e).symm)
  | _, _, .zero i rest, _, g => rest.gadget (g.relabelFree (zeroPort i))
  | _, _, .cap _ rest, _, g => rest.gadget (g.substitute capPort)

end Cslib.Logic.PL.CSP.Normalization

namespace Cslib.BitString

/-- A failed-exchange witness with distinguished difference literally at coordinate 0.
The witness may have proper support before zero deletion. Feasibility of both the witness and
the zero tuple prevents empty intermediate relations. -/
structure CyclicExchangeObstruction {n : ℕ} (P : Set (Fin (n + 1) → Bool))
    (d : Fin (n + 1) → Bool) : Prop where
  /-- Complementing all ports preserves membership. -/
  selfComplementary : IsSelfComplementary P
  /-- The all-false original tuple is feasible. -/
  zero_mem : (fun _ => false) ∈ P
  /-- The nonzero difference witness is feasible. -/
  feasible : d ∈ cyclicDifferenceRelation P
  /-- The distinguished difference is coordinate 0. -/
  first : d 0 = true
  /-- Every two-coordinate exchange involving 0 within the witness support fails. -/
  forbidden : ∀ j, j ≠ 0 → d j = true → flipOn {0, j} (fun _ => false) ∉ cyclicDifferenceRelation P

/-- Zero-conditioned deletion preserves the failed-exchange witness and its distinguished edge. -/
theorem CyclicExchangeObstruction.zero {n : ℕ} {P : Set (Fin (n + 2) → Bool)}
    {d : Fin (n + 2) → Bool} (h : CyclicExchangeObstruction P d) (i : Fin (n + 2))
    (hi : d i = false) :
    CyclicExchangeObstruction (zeroRestriction i P) (d ∘ differencePort i) := by
  have hi0 : i ≠ 0 := by rintro rfl; rw [h.first] at hi; contradiction
  refine ⟨?_, h.zero_mem, ?_, ?_, ?_⟩
  · intro y
    exact h.selfComplementary (y ∘ zeroPort i)
  · exact (mem_cyclicDifferenceRelation_zeroRestriction i P _).mpr
      ⟨d, h.feasible, hi, rfl⟩
  · simpa only [Function.comp_apply, differencePort_zero i hi0] using h.first
  · intro j hj hd hp
    obtain ⟨s, hs, hsi, hsd⟩ :=
      (mem_cyclicDifferenceRelation_zeroRestriction i P _).mp hp
    have he := eq_pair_of_zero_restriction i hi0 j s hsi hsd
    have hj0 : differencePort i j ≠ 0 := by
      rw [← differencePort_zero i hi0, differencePort_eq_succAbove]
      exact fun he => hj (Fin.succAbove_right_injective he)
    exact h.forbidden _ hj0 hd (he ▸ hs)

/-- No failed-exchange witness fits on fewer than four cyclic difference coordinates. -/
theorem CyclicExchangeObstruction.four_le {n : ℕ} {P : Set (Fin (n + 1) → Bool)}
    {d : Fin (n + 1) → Bool} (h : CyclicExchangeObstruction P d) : 4 ≤ n + 1 := by
  have hp := parityOn_mem_cyclicDifferenceRelation h.feasible
  by_contra hn
  have hn3 : n ≤ 2 := by omega
  interval_cases n
  · have he : ∀ d : Fin 1 → Bool, parityOn Finset.univ d = false → d 0 ≠ true := by decide
    exact he d hp h.first
  · have he : ∀ d : Fin 2 → Bool, parityOn Finset.univ d = false → d 0 = true →
        ∃ j, j ≠ 0 ∧ d j = true ∧ d = flipOn {0, j} (fun _ => false) := by
      decide
    obtain ⟨j, hj, hd, he⟩ := he d hp h.first
    exact h.forbidden j hj hd (he ▸ h.feasible)
  · have he : ∀ d : Fin 3 → Bool, parityOn Finset.univ d = false → d 0 = true →
        ∃ j, j ≠ 0 ∧ d j = true ∧ d = flipOn {0, j} (fun _ => false) := by
      decide
    obtain ⟨j, hj, hd, he⟩ := he d hp h.first
    exact h.forbidden j hj hd (he ▸ h.feasible)

/-- The witnessed failed exchange rules out the even delta-matroid axiom. -/
theorem CyclicExchangeObstruction.not_isEvenDeltaMatroid {n : ℕ}
    {P : Set (Fin (n + 1) → Bool)} {d : Fin (n + 1) → Bool}
    (h : CyclicExchangeObstruction P d) : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation P) := by
  intro hd
  have hz : (fun _ => false) ∈ cyclicDifferenceRelation P :=
    ⟨_, h.zero_mem, cyclicDifference_const _ false⟩
  obtain ⟨j, hj, hjd, hf⟩ := hd.exchange hz h.feasible (i := 0) (by rw [h.first]; decide)
  apply h.forbidden j hj _ hf
  cases hb : d j
  · exact (hjd hb.symm).elim
  · rfl

/-- At arity four, the witness must be the full set of differences. -/
theorem CyclicExchangeObstruction.eq_full {P : Set (Fin 4 → Bool)} {d : Fin 4 → Bool}
    (h : CyclicExchangeObstruction P d) : d = fun _ => true := by
  have he : ∀ d : Fin 4 → Bool, parityOn Finset.univ d = false → d 0 = true →
      d = (fun _ => true) ∨ ∃ j, j ≠ 0 ∧ d j = true ∧ d = flipOn {0, j} (fun _ => false) := by
    decide
  rcases he d (parityOn_mem_cyclicDifferenceRelation h.feasible) h.first with
    he | ⟨j, hj, hd, he⟩
  · exact he
  · exact (h.forbidden j hj hd (he ▸ h.feasible)).elim

/-- The terminal relation is standardized in precisely the recorded cyclic port order. -/
theorem CyclicExchangeObstruction.standardized {P : Set (Fin 4 → Bool)} {d : Fin 4 → Bool}
    (h : CyclicExchangeObstruction P d) : IsStandardizedInconsistent P := by
  have hfull : (fun _ => true) ∈ cyclicDifferenceRelation P := h.eq_full ▸ h.feasible
  have hz : (fun _ => false) ∈ cyclicDifferenceRelation P :=
    ⟨_, h.zero_mem, cyclicDifference_const 4 false⟩
  refine ⟨h.selfComplementary, ?_, ?_⟩
  · intro x hx
    have hc : ∀ x : Fin 4 → Bool, x ∈ cross →
        cyclicDifference x = (fun _ => false) ∨ cyclicDifference x = (fun _ => true) := by decide
    apply (mem_cyclicDifferenceRelation_iff h.selfComplementary x).mp
    rcases hc x hx with he | he
    · rwa [he]
    · rwa [he]
  · intro x hx
    by_cases he : x 0 = x 1
    · exact Or.inl he
    have hfirst : cyclicDifference x 0 = true := by
      change (x 0 ^^ x 1) = true
      cases ha : x 0 <;> cases hb : x 1 <;> simp_all
    have hc : ∀ d : Fin 4 → Bool, parityOn Finset.univ d = false → d 0 = true →
        d = (fun _ => true) ∨ ∃ j, j ≠ 0 ∧ d = flipOn {0, j} (fun _ => false) := by
      decide
    rcases hc (cyclicDifference x) (parityOn_cyclicDifference x) hfirst with hf | ⟨j, hj, hjd⟩
    · right
      have ht : ∀ x : Fin 4 → Bool, cyclicDifference x = (fun _ => true) →
          x 0 = x 2 ∧ x 0 ≠ x 1 ∧ x 1 = x 3 := by decide
      exact ht x hf
    · exact (h.forbidden j hj (by rw [h.eq_full]) (hjd ▸ ⟨x, hx, rfl⟩)).elim

/-- When all candidate quartets fail, the cap preserves the full-support obstruction.
Every putative new pair has exactly the two lifts ruled out by the hypotheses. -/
theorem CyclicExchangeObstruction.cap {n : ℕ} {P : Set (Fin (n + 4) → Bool)}
    (h : CyclicExchangeObstruction P (fun _ => true))
    (hq : ∀ k : Fin (n + 4), 3 ≤ k.val →
      flipOn {0, 1, 2, k} (fun _ => false) ∉ cyclicDifferenceRelation P) :
    CyclicExchangeObstruction (capRelation P) (fun _ => true) := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · intro y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨fun i => !z i, ?_⟩
      rw [capPort_not]
      exact (h.selfComplementary _).mp hz
    · rintro ⟨z, hz⟩
      refine ⟨fun i => !z i, ?_⟩
      have hc := (h.selfComplementary _).mp hz
      convert hc using 1
      funext i
      simp only [Function.comp_apply]
      cases capPort i <;> simp
  · refine ⟨fun _ => false, ?_⟩
    convert h.zero_mem using 1
    funext i
    simp only [Function.comp_apply]
    cases capPort i <;> rfl
  · exact (mem_cyclicDifferenceRelation_capRelation P _).mpr
      ⟨_, h.feasible, rfl, rfl⟩
  · intro j hj hd hp
    obtain ⟨s, hs, h12, hsd⟩ := (mem_cyclicDifferenceRelation_capRelation P _).mp hp
    have hk : 3 ≤ (capDifferencePort j).val := by
      have hjv : j.val ≠ 0 := fun he => hj (Fin.ext he)
      simp only [capDifferencePort, hjv, ite_false]
      change 3 ≤ j.val + 2
      omega
    rcases eq_pair_or_quartet_of_cap j hj s h12 hsd with he | he
    · have hk0 : capDifferencePort j ≠ 0 := by
        intro he
        have hv := congrArg Fin.val he
        change (capDifferencePort j).val = 0 at hv
        omega
      exact h.forbidden _ hk0 rfl (he ▸ hs)
    · exact hq _ hk (he ▸ hs)

/-- Any feasible quartet gives a fresh obstruction witness in the same relation.
It is this quartet, not the previous full tuple, that survives the finishing zero restrictions. -/
theorem CyclicExchangeObstruction.quartet {n : ℕ} {P : Set (Fin (n + 4) → Bool)}
    (h : CyclicExchangeObstruction P (fun _ => true)) (k : Fin (n + 4))
    (hk : flipOn {0, 1, 2, k} (fun _ => false) ∈ cyclicDifferenceRelation P) :
    CyclicExchangeObstruction P (flipOn {0, 1, 2, k} (fun _ => false)) := by
  refine ⟨h.selfComplementary, h.zero_mem, hk, ?_, ?_⟩
  · simp [flipOn]
  · intro j hj hd
    exact h.forbidden j hj rfl

private theorem exists_zero_quartet {n : ℕ} (hn : 1 ≤ n) (k : Fin (n + 4)) :
    ∃ i : Fin (n + 4), flipOn {0, 1, 2, k} (fun _ => false) i = false := by
  classical
  have hc : ({0, 1, 2, k} : Finset (Fin (n + 4))).card <
      (Finset.univ : Finset (Fin (n + 4))).card := by
    have hb : ({0, 1, 2, k} : Finset (Fin (n + 4))).card ≤ 4 := by
      exact (Finset.card_insert_le _ _).trans (by
        have := Finset.card_insert_le (1 : Fin (n + 4)) {2, k}
        have := Finset.card_insert_le (2 : Fin (n + 4)) {k}
        simp only [Finset.card_singleton] at *
        omega)
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨i, by simp [flipOn, hi]⟩

end Cslib.BitString

namespace Cslib.Logic.PL.CSP.Normalization

open Cslib.BitString

/-- Normalize an arbitrary-arity obstruction by a finite sequence of the recorded maps.
Zero differences are deleted at their greatest remaining index, so a run of zero deletions
proceeds in descending order. Each recursive call strictly decreases the actual arity. -/
theorem exists_program_of_obstruction (n : ℕ) (P : Set (Fin (n + 1) → Bool))
    (d : Fin (n + 1) → Bool) (h : CyclicExchangeObstruction P d) :
    ∃ p : Program (n + 1) 4, IsStandardizedInconsistent (p.eval P) := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hn := h.four_le
    by_cases hfour : n = 3
    · subst n
      exact ⟨.done 4, h.standardized⟩
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 4 := ⟨n - 4, by omega⟩
    have shrink (d' : Fin (r + 5) → Bool) (hd' : CyclicExchangeObstruction P d')
        (hz : ∃ i, d' i = false) :
        ∃ p : Program (r + 5) 4, IsStandardizedInconsistent (p.eval P) := by
      let Z := Finset.univ.filter (fun i => d' i = false)
      have hZ : Z.Nonempty := by simpa only [Z, Finset.nonempty_def,
        Finset.mem_filter, Finset.mem_univ, true_and] using hz
      let i := Z.max' hZ
      have hi : d' i = false := (Finset.mem_filter.mp (Finset.max'_mem Z hZ)).2
      obtain ⟨p, hp⟩ := ih (r + 3) (by omega) (zeroRestriction i P)
        (d' ∘ differencePort i) (hd'.zero i hi)
      exact ⟨.zero i p, hp⟩
    by_cases hz : ∃ i, d i = false
    · exact shrink d h hz
    have hdfull : d = fun _ => true := by
      funext i
      cases he : d i
      · exact (hz ⟨i, he⟩).elim
      · rfl
    subst d
    have hr : 1 ≤ r := by
      by_contra hr
      have he : r = 0 := by omega
      subst r
      have hp := parityOn_mem_cyclicDifferenceRelation h.feasible
      exact (by decide : parityOn Finset.univ (fun _ : Fin 5 => true) ≠ false) hp
    by_cases hq : ∃ k : Fin (r + 5), 3 ≤ k.val ∧
        flipOn {0, 1, 2, k} (fun _ => false) ∈ cyclicDifferenceRelation P
    · obtain ⟨k, _, hk⟩ := hq
      exact shrink _ (h.quartet k hk) (exists_zero_quartet (by omega) k)
    have hq' : ∀ k : Fin (r + 5), 3 ≤ k.val →
        flipOn {0, 1, 2, k} (fun _ => false) ∉ cyclicDifferenceRelation P := by
      intro k hk hf
      exact hq ⟨k, hk, hf⟩
    obtain ⟨p, hp⟩ := ih (r + 2) (by omega) (capRelation P)
      (fun _ => true) (h.cap hq')
    refine ⟨@Program.cap (r + 1) 4 (by omega) p, ?_⟩
    simpa only [Program.eval] using hp

/-- Twisting preserves simultaneous complementation of all original ports. -/
theorem isSelfComplementary_twist {n : ℕ} {R : Set (Fin n → Bool)}
    (hR : IsSelfComplementary R) (a : Fin n → Bool) : IsSelfComplementary (twist R a) := by
  intro x
  change x + a ∈ R ↔ (fun i => !x i) + a ∈ R
  have he : (fun i => !x i) + a = fun i => !(x + a) i := by
    funext i
    simp only [Pi.add_apply, Bool.add_eq_xor]
    cases x i <;> cases a i <;> rfl
  rw [he]
  exact hR _

/-- A cyclic change of starting port preserves self-complementarity. -/
theorem isSelfComplementary_rotate {n : ℕ} {P : Set (Fin n → Bool)}
    (hP : IsSelfComplementary P) (e : Fin n) : IsSelfComplementary (rotate e P) := by
  intro y
  exact hP (y ∘ (finCycle e).symm)

/-- The actual twist and initial cyclic rotation normalize a genuine failed exchange.
The tuple `a` is feasible in the original relation, and every exchange along the difference
support of `a` and `b` is ruled out by `hf`. -/
theorem obstruction_twist_rotate {n : ℕ} {R : Set (Fin (n + 1) → Bool)}
    (hR : IsSelfComplementary R) (a b : Fin (n + 1) → Bool) (ha : a ∈ R) (hb : b ∈ R)
    (e : Fin (n + 1)) (he : cyclicDifference a e ≠ cyclicDifference b e)
    (hf : ∀ j, cyclicDifference a j ≠ cyclicDifference b j →
      flipOn {e, j} (cyclicDifference a) ∉ cyclicDifferenceRelation R) :
    CyclicExchangeObstruction (rotate e (twist R a))
      ((cyclicDifference b + cyclicDifference a) ∘ finCycle e) := by
  have hcycle : finCycle e 0 = e := by simp
  refine ⟨isSelfComplementary_rotate (isSelfComplementary_twist hR a) e, ?_, ?_, ?_, ?_⟩
  · change (fun _ => false) + a ∈ R
    have hz : (fun _ => false) + a = a := by
      funext i
      simp only [Pi.add_apply, Bool.add_eq_xor, Bool.false_xor]
    rwa [hz]
  · refine ⟨(b + a) ∘ finCycle e, ?_, ?_⟩
    · change (((b + a) ∘ finCycle e) ∘ (finCycle e).symm) + a ∈ R
      have hc : ((b + a) ∘ finCycle e) ∘ (finCycle e).symm = b + a := by
        funext i
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
      rw [hc]
      have heq : (b + a) + a = b := by
        funext i
        simp only [Pi.add_apply, Bool.add_eq_xor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      rwa [heq]
    · rw [cyclicDifference_comp_finCycle, cyclicDifference_add]
  · simp only [Function.comp_apply, hcycle, Pi.add_apply, Bool.add_eq_xor]
    cases ha : cyclicDifference a e <;> cases hb : cyclicDifference b e <;> simp_all
  · intro j hj hd hp
    obtain ⟨x, hx, hdx⟩ := hp
    have hjd : cyclicDifference a (finCycle e j) ≠ cyclicDifference b (finCycle e j) := by
      change (cyclicDifference b (finCycle e j) + cyclicDifference a (finCycle e j)) = true at hd
      cases ha : cyclicDifference a (finCycle e j) <;>
        cases hb : cyclicDifference b (finCycle e j) <;> simp_all [Bool.add_eq_xor]
    apply hf (finCycle e j) hjd
    refine ⟨(x ∘ (finCycle e).symm) + a, hx, ?_⟩
    rw [cyclicDifference_add, cyclicDifference_comp_finCycle_symm, hdx]
    funext k
    have hk0 : (finCycle e).symm k = 0 ↔ k = e := by
      rw [Equiv.symm_apply_eq]
      rw [hcycle]
    have hkj : (finCycle e).symm k = j ↔ k = finCycle e j := Equiv.symm_apply_eq _
    simp only [Pi.add_apply, Function.comp_apply, flipOn, Finset.mem_insert,
      Finset.mem_singleton, hk0, hkj]
    split_ifs <;> cases cyclicDifference a k <;> rfl

/-- A nonempty cyclic-difference relation that is not an even delta-matroid has a genuine
failed exchange. Even parity is automatic, so neither parity nor emptiness causes the failure. -/
theorem exists_failed_exchange {n : ℕ} {R : Set (Fin n → Bool)} (hne : R.Nonempty)
    (hn : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation R)) :
    ∃ a ∈ R, ∃ b ∈ R, ∃ e, cyclicDifference a e ≠ cyclicDifference b e ∧
      ∀ j, cyclicDifference a j ≠ cyclicDifference b j →
        flipOn {e, j} (cyclicDifference a) ∉ cyclicDifferenceRelation R := by
  classical
  have hd : ¬IsDeltaMatroid (cyclicDifferenceRelation R) := by
    intro h
    apply hn
    refine ⟨h, ?_⟩
    intro x y hx hy
    rw [parityOn_mem_cyclicDifferenceRelation hx, parityOn_mem_cyclicDifferenceRelation hy]
  have hw : ∃ x ∈ cyclicDifferenceRelation R, ∃ y ∈ cyclicDifferenceRelation R,
      ∃ e, x e ≠ y e ∧ ∀ j, x j ≠ y j → flipOn {e, j} x ∉ cyclicDifferenceRelation R := by
    by_contra h
    push Not at h
    apply hd
    refine ⟨(cyclicDifferenceRelation_nonempty_iff R).mpr hne, ?_⟩
    intro x y hx hy e he
    exact h x hx y hy e he
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, e, he, hf⟩ := hw
  exact ⟨a, ha, b, hb, e, he, hf⟩

/-- A completed finite normalization recipe. Its starting tuple is feasible in the input,
and the first operation is the specified cyclic rotation of the twisted literal. -/
structure Construction {n : ℕ} (R : Set (Fin n → Bool)) where
  /-- Feasible tuple used by the disequality spokes. -/
  tuple : Fin n → Bool
  /-- The twist is chosen at a feasible original tuple. -/
  tuple_mem : tuple ∈ R
  /-- Original difference moved to boundary coordinate 0. -/
  start : Fin n
  /-- Finite ordered boundary operations after the initial rotation. -/
  reduction : Program n 4
  /-- The executed relation is standardized in the resulting free-port order. -/
  standardized : IsStandardizedInconsistent (reduction.eval (rotate start (twist R tuple)))

/-- The four-ary relation defined by the recorded normalization recipe. -/
@[expose] def Construction.target {n : ℕ} {R : Set (Fin n → Bool)}
    (c : Construction R) : Set (Fin 4 → Bool) :=
  c.reduction.eval (rotate c.start (twist R c.tuple))

/-- The executed actual finite gadget for the normalized relation, starting with one original
literal and its twist spokes. Its correctness follows at every step from exact scope relabeling. -/
@[expose] noncomputable def Construction.gadget {n : ℕ} {R : Set (Fin n → Bool)}
    (c : Construction R) : PPGadget (arity n) (sem R) c.target :=
  (Program.rotate c.start c.reduction).gadget (twistGadget R c.tuple)

/-- Arbitrary-arity ordered combinatorial normalization, with no expressibility, solver,
classification or reduction premise. The result contains an executable finite operation trace
and an actual equality-free `{R,N}` gadget for a standardized four-ary relation.
Geometric realization of the recorded operations and the full planar hardness theorem remain
separate obligations; this does not assert the planar expressibility conclusion of Lemma 6. -/
theorem exists_construction {n : ℕ} (R : Set (Fin n → Bool)) (hne : R.Nonempty)
    (hR : IsSelfComplementary R) (hn : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation R)) :
    4 ≤ n ∧ Nonempty (Construction R) := by
  obtain ⟨a, ha, b, hb, e, he, hf⟩ := exists_failed_exchange hne hn
  cases n with
  | zero => exact e.elim0
  | succ n =>
    have ho := obstruction_twist_rotate hR a b ha hb e he hf
    obtain ⟨p, hp⟩ := exists_program_of_obstruction n _ _ ho
    exact ⟨ho.four_le, ⟨a, ha, e, p, hp⟩⟩

/-- Number of caps, each introducing exactly one hidden port. -/
@[expose] def Program.caps {n m : ℕ} (p : Program n m) : ℕ := match p with
  | .done _ => 0
  | .rotate _ rest => rest.caps
  | .zero _ rest => rest.caps
  | .cap _ rest => rest.caps + 1

/-- Number of boundary reductions; the initial cyclic rotation is not counted. -/
@[expose] def Program.reductions {n m : ℕ} (p : Program n m) : ℕ := match p with
  | .done _ => 0
  | .rotate _ rest => rest.reductions
  | .zero _ rest => rest.reductions + 1
  | .cap _ rest => rest.reductions + 1

/-- Every cap removes two boundary ports. -/
theorem Program.caps_bound {n m : ℕ} (p : Program n m) : 2 * p.caps + m ≤ n := by
  induction p <;> simp_all only [caps] <;> omega

/-- Every nonrotation operation removes at least one boundary port. -/
theorem Program.reductions_bound {n m : ℕ} (p : Program n m) : p.reductions + m ≤ n := by
  induction p <;> simp_all only [reductions] <;> omega

/-- Execution keeps exactly the original ordered sequence of relation symbols.
Only variable labels in their scopes change. -/
theorem Program.gadget_symbols {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}
    {n m : ℕ} (p : Program n m) {P : Set (Fin n → Bool)} (g : PPGadget ar s P) :
    (p.gadget g).body.map Prod.fst = g.body.map Prod.fst := by
  induction p with
  | done => rfl
  | rotate e rest ih =>
    change (rest.gadget (g.relabelFree (finCycle e).symm)).body.map Prod.fst = _
    exact (ih _).trans (by
      simp [PPGadget.relabelFree, relabel, Constraint.relabel, List.map_map])
  | zero i rest ih =>
    change (rest.gadget (g.relabelFree (zeroPort i))).body.map Prod.fst = _
    exact (ih _).trans (by
      simp [PPGadget.relabelFree, relabel, Constraint.relabel, List.map_map])
  | cap large rest ih =>
    change (rest.gadget (g.substitute capPort)).body.map Prod.fst = _
    exact (ih _).trans (by
      simp [PPGadget.substitute, relabel, Constraint.relabel, List.map_map])

/-- Scope relabeling keeps the exact total number of variable occurrences. -/
theorem Program.gadget_width {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}
    {n m : ℕ} (p : Program n m) {P : Set (Fin n → Bool)} (g : PPGadget ar s P) :
    (p.gadget g).body.vars.length = g.body.vars.length := by
  induction p with
  | done => rfl
  | rotate e rest ih =>
    change (rest.gadget (g.relabelFree (finCycle e).symm)).body.vars.length = _
    exact (ih _).trans (by simp [PPGadget.relabelFree])
  | zero i rest ih =>
    change (rest.gadget (g.relabelFree (zeroPort i))).body.vars.length = _
    exact (ih _).trans (by simp [PPGadget.relabelFree])
  | cap large rest ih =>
    change (rest.gadget (g.substitute capPort)).body.vars.length = _
    exact (ih _).trans (by simp [PPGadget.substitute])

/-- The cap adds precisely one fresh auxiliary label; all old auxiliaries survive. -/
theorem Program.gadget_numAux {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}
    {n m : ℕ} (p : Program n m) {P : Set (Fin n → Bool)} (g : PPGadget ar s P) :
    (p.gadget g).numAux = g.numAux + p.caps := by
  induction p with
  | done => simp [gadget, caps]
  | rotate e rest ih =>
    change (rest.gadget (g.relabelFree (finCycle e).symm)).numAux = _
    simpa only [caps, PPGadget.relabelFree] using ih (g.relabelFree (finCycle e).symm)
  | zero i rest ih =>
    change (rest.gadget (g.relabelFree (zeroPort i))).numAux = _
    simpa only [caps, PPGadget.relabelFree] using ih (g.relabelFree (zeroPort i))
  | cap large rest ih =>
    change (rest.gadget (g.substitute capPort)).numAux = _
    rw [ih]
    simp only [PPGadget.substitute, caps]
    omega

/-- The final gadget has at most `3n-4` auxiliaries, counting the redundant twist labels. -/
theorem Construction.numAux_bound {n : ℕ} {R : Set (Fin n → Bool)}
    (c : Construction R) : c.gadget.numAux ≤ 3 * n - 4 := by
  have hb := (Program.rotate c.start c.reduction).caps_bound
  rw [Construction.gadget, Program.gadget_numAux]
  change n + n + (Program.rotate c.start c.reduction).caps ≤ 3 * n - 4
  omega

/-- The final body retains the initial constraint and scope-width bounds. -/
theorem Construction.body_bounds {n : ℕ} {R : Set (Fin n → Bool)}
    (c : Construction R) : c.gadget.body.length ≤ 1 + 2 * n ∧
      c.gadget.body.vars.length ≤ 5 * n := by
  have hs := (Program.rotate c.start c.reduction).gadget_symbols (twistGadget R c.tuple)
  have hl := congrArg List.length hs
  simp only [List.length_map] at hl
  have hw := (Program.rotate c.start c.reduction).gadget_width (twistGadget R c.tuple)
  change c.gadget.body.length = (twistBody c.tuple).length at hl
  change c.gadget.body.vars.length = (twistBody c.tuple).vars.length at hw
  rw [hl, hw]
  exact twistBody_size c.tuple

end Cslib.Logic.PL.CSP.Normalization
