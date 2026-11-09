/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.CanonicalTree
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment.Counting

/-!
# The switching lemma

**Håstad's switching lemma**: if every term of a formula `F` in disjunctive normal form has at most
`k` literals and reads each variable once, then few restrictions (partial assignments,
`BitString.PartialAssignment`) leaving `ℓ` variables free make the canonical decision tree of `F`
deep. Precisely, at most `#R(ℓ - s) (4k)^s` of them leave a query path of length at least `s`
(`DNF.card_filter_pathLength_le`), and so at most that many leave `F` with decision tree
complexity at least `s` (`DNF.card_switching_le`), where `R(m)` is the set of restrictions of the
`n` variables `ι` leaving `m` of them free. Since `#R(ℓ - s) / #R(ℓ)` is about `(2ℓ / n) ^ s`, a
random restriction leaving `ℓ ≪ n / k` variables free turns `F` into a function of decision tree
complexity less than `s`, except with probability exponentially small in `s` [Hastad1986]. Both
statements hold more generally among the extensions of any fixed restriction, which is the form
used to restrict a formula in several stages.

We follow Razborov's proof by encoding [Razborov1995], [Jukna, Chapter 12][Jukna2012]. A
restriction `ρ` with a query path of length at least `s` on the input `x` is encoded by an extension
of `ρ` with `s` fewer free variables, which fixes each of the first `s` queried variables to the
value that satisfies the term it was queried for, together with a word of `s` letters from an
alphabet of size `4k`: the position of each queried variable in its term, its value in `x`, and
whether it ends its stage (`DNF.encode`). Since the terms queried in the encoding are again the
first terms not falsified, the decoder can replay the path (`DNF.decode`, `DNF.decode_encode`).

## Main definitions

* `Cslib.Logic.PL.DNF.encode`, `Cslib.Logic.PL.DNF.decode`: Razborov's encoding of a restriction
  with a long query path.

## Main results

* `Cslib.Logic.PL.DNF.decode_encode`: the encoding is invertible.
* `Cslib.Logic.PL.DNF.card_filter_pathLength_le`: few restrictions leave long query paths.
* `Cslib.Logic.PL.DNF.card_switching_le`: the switching lemma, counting version.

## References

* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [A. A. Razborov, *Bounded arithmetic and lower bounds in Boolean complexity*][Razborov1995]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.BitString Cslib.DecisionTree Finset

variable {ι : Type*}

namespace Term

/-- A restriction falsifies more terms than any restriction it extends. -/
theorem FalsifiedBy.mono {t : Term ι} {ρ θ : PartialAssignment ι} (ht : t.FalsifiedBy ρ)
    (h : θ.Extends ρ) : t.FalsifiedBy θ :=
  let ⟨l, hl, hρ⟩ := ht
  ⟨l, hl, h _ _ hρ⟩

variable [DecidableEq ι]

/-- The values of the variables making the literals of `t` true. -/
def satisfying (t : Term ι) : ι → Bool :=
  fun v => (t.lookup v).getD false

/-- The code of one stage of the canonical path: for each queried variable, its position in the
term, its value in `x`, and whether it ends the stage. -/
def stageCode (t : Term ι) (x : ι → Bool) : List ι → List (ℕ × Bool × Bool)
  | [] => []
  | v :: W => ((t.map Prod.fst).idxOf v, x v, W.isEmpty) :: stageCode t x W

variable {t : Term ι}

private theorem satisfying_of_mem (ht : (t.map Prod.fst).Nodup) {l : Literal ι} (hl : l ∈ t) :
    t.satisfying l.1 = l.2 := by
  induction t with
  | nil => simp at hl
  | cons a t ih =>
    obtain ⟨w, c⟩ := a
    obtain ⟨hat, ht⟩ := List.nodup_cons.1 ht
    rcases List.mem_cons.1 hl with rfl | hl'
    · simp [satisfying]
    · have hne : (l.1 == w) = false := by
        rw [beq_eq_false_iff_ne]
        rintro rfl
        exact hat (List.mem_map.2 ⟨l, hl', rfl⟩)
      simpa [satisfying, List.lookup_cons, hne] using ih ht hl'

@[simp] theorem length_stageCode (x : ι → Bool) (W : List ι) :
    (t.stageCode x W).length = W.length := by
  induction W <;> simp_all [stageCode]

private theorem stageCode_eq_nil_iff {x : ι → Bool} {W : List ι} :
    t.stageCode x W = [] ↔ W = [] := by
  cases W <;> simp [stageCode]

private theorem fst_lt_of_mem_stageCode {x : ι → Bool} {W : List ι}
    (hW : ∀ v ∈ W, v ∈ t.map Prod.fst) {e : ℕ × Bool × Bool} (he : e ∈ t.stageCode x W) :
    e.1 < t.length := by
  induction W with
  | nil => simp [stageCode] at he
  | cons v W ih =>
    rcases List.mem_cons.1 he with rfl | he
    · simpa using List.idxOf_lt_length_iff.2 (hW v (by simp))
    · exact ih (fun w hw => hW w (by simp [hw])) he

end Term

namespace DNF

variable {F : DNF ι} {ρ θ : PartialAssignment ι} {t : Term ι}

private theorem queried_eq_freeVars (ht : F.firstTerm ρ = some t) : F.queried ρ = t.freeVars ρ := by
  simp [queried, ht]

private theorem exists_firstTerm_of_queried_ne_nil (h : F.queried ρ ≠ []) :
    ∃ t, F.firstTerm ρ = some t := by
  cases ht : F.firstTerm ρ with
  | none => simp [queried, ht] at h
  | some t => exact ⟨t, rfl⟩

private theorem mem_of_firstTerm_eq_some (ht : F.firstTerm ρ = some t) : t ∈ F :=
  List.mem_of_find?_eq_some ht

private theorem not_falsifiedBy_of_firstTerm_eq_some (ht : F.firstTerm ρ = some t) :
    ¬ t.FalsifiedBy ρ := by
  simpa using List.find?_some ht

private theorem nodup_queried (hF : ∀ t ∈ F, (t.map Prod.fst).Nodup) : (F.queried ρ).Nodup := by
  unfold queried
  cases ht : F.firstTerm ρ with
  | none => simp
  | some t =>
    simpa [Term.freeVars] using
      ((List.filter_sublist (l := t)).map Prod.fst).nodup (hF t (mem_of_firstTerm_eq_some ht))

private theorem mem_map_fst_of_mem_queried (ht : F.firstTerm ρ = some t) {v : ι}
    (hv : v ∈ F.queried ρ) : v ∈ t.map Prod.fst := by
  rw [queried_eq_freeVars ht] at hv
  obtain ⟨b, hb, -⟩ := Term.mem_freeVars.1 hv
  exact List.mem_map.2 ⟨_, hb, rfl⟩

/-- Extending a restriction keeps its first term not falsified, as long as that term stays
unfalsified. -/
private theorem firstTerm_eq_of_extends (ht : F.firstTerm ρ = some t) (h : θ.Extends ρ)
    (hθ : ¬ t.FalsifiedBy θ) :
    F.firstTerm θ = some t := by
  rw [firstTerm, List.find?_eq_some_iff_append] at ht ⊢
  obtain ⟨-, as, bs, rfl, has⟩ := ht
  refine ⟨by simp [hθ], as, bs, rfl, fun a ha => ?_⟩
  simpa using (show a.FalsifiedBy ρ by simpa using has a ha).mono h

variable [DecidableEq ι]

/-- Fixing some queried variables to the values satisfying the first term keeps it first, in any
extension leaving the other queried variables free. -/
private theorem firstTerm_assign_satisfying (hF : ∀ t ∈ F, (t.map Prod.fst).Nodup)
    (ht : F.firstTerm ρ = some t) (h : θ.Extends ρ) {W : List ι}
    (hWq : ∀ v ∈ W, v ∈ F.queried ρ) (hW : ∀ v ∈ F.queried ρ, v ∉ W → θ v = none) :
    F.firstTerm (θ.assign W.toFinset t.satisfying) = some t := by
  have hfree : ∀ v ∈ W, ρ v = none := fun v hv => free_of_mem_queried (hWq v hv)
  refine firstTerm_eq_of_extends ht (fun i b hi => ?_) ?_
  · have : i ∉ W := fun hiW => by simp [hfree i hiW] at hi
    simpa [this] using h i b hi
  · have hρ := not_falsifiedBy_of_firstTerm_eq_some ht
    rintro ⟨l, hl, hθ⟩
    by_cases hlW : l.1 ∈ W
    · simp [hlW, Term.satisfying_of_mem (hF t (mem_of_firstTerm_eq_some ht)) hl] at hθ
    · rw [PartialAssignment.assign_of_notMem (by simpa using hlW)] at hθ
      cases hρl : ρ l.1 with
      | none =>
        have hq : l.1 ∈ F.queried ρ := by
          rw [queried_eq_freeVars ht]
          exact Term.mem_freeVars.2 ⟨l.2, hl, hρl⟩
        simp [hW _ hq hlW] at hθ
      | some c =>
        rw [h _ _ hρl] at hθ
        exact hρ ⟨l, hl, hθ ▸ hρl⟩

variable (F)

/-- Replay the canonical path from the code: `cur` is the term of the current stage, if the stage
has started, `θ` the restriction so far, and `Q` the variables replayed so far. -/
def decodeAux : Option (Term ι) → PartialAssignment ι → Finset ι →
    List (ℕ × Bool × Bool) → PartialAssignment ι
  | _, θ, Q, [] => θ.unassign Q
  | cur, θ, Q, (j, b, e) :: c =>
    match ((cur.getD ((F.firstTerm θ).getD [])).map Prod.fst)[j]? with
    | none => θ
    | some v => decodeAux (if e then none else some (cur.getD ((F.firstTerm θ).getD [])))
        (Function.update θ v (some b)) (insert v Q) c

/-- Razborov's decoding: recover the restriction from its encoding. -/
def decode (θ : PartialAssignment ι) (c : List (ℕ × Bool × Bool)) :
    PartialAssignment ι :=
  F.decodeAux none θ ∅ c

variable {F}

/-- One step of the decoder: set the variable at position `j` of the current term to `b`. -/
private theorem decodeAux_cons {cur : Option (Term ι)} {θ : PartialAssignment ι}
    {t : Term ι} (ht : cur.getD ((F.firstTerm θ).getD []) = t) {j : ℕ} {v : ι}
    (hv : (t.map Prod.fst)[j]? = some v) (Q : Finset ι) (b e : Bool)
    (c : List (ℕ × Bool × Bool)) :
    F.decodeAux cur θ Q ((j, b, e) :: c) =
      F.decodeAux (if e then none else some t) (Function.update θ v (some b)) (insert v Q) c := by
  subst ht
  simp only [decodeAux, hv]

/-- Replaying a stage from its term. -/
private theorem decodeAux_stageCode {t : Term ι} {W : List ι}
    (hW : ∀ v ∈ W, v ∈ t.map Prod.fst) (hne : W ≠ []) (x : ι → Bool)
    (θ : PartialAssignment ι) (Q : Finset ι) (c : List (ℕ × Bool × Bool)) :
    F.decodeAux (some t) θ Q (t.stageCode x W ++ c) =
      F.decodeAux none (θ.assign W.toFinset x) (Q ∪ W.toFinset) c := by
  induction W generalizing θ Q with
  | nil => exact absurd rfl hne
  | cons v W ih =>
    rw [Term.stageCode, List.cons_append,
      decodeAux_cons (cur := some t) (θ := θ) (t := t) rfl
        (List.getElem?_idxOf (hW v List.mem_cons_self))]
    cases W with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append, Term.stageCode]
      congr 1
      · funext i
        by_cases hi : i = v <;> simp [hi]
      · ext i
        simp
    | cons w W =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [ih (fun u hu => hW u (List.mem_cons_of_mem _ hu)) (List.cons_ne_nil _ _)]
      congr 1
      · funext i
        have hv : v ∈ (v :: w :: W).toFinset := by simp
        by_cases hi' : i ∈ (w :: W).toFinset
        · rw [PartialAssignment.assign_of_mem hi', PartialAssignment.assign_of_mem
            (List.mem_toFinset.2 (List.mem_cons_of_mem _ (List.mem_toFinset.1 hi')))]
        · rw [PartialAssignment.assign_of_notMem hi']
          by_cases hi : i = v
          · subst hi
            rw [PartialAssignment.assign_of_mem hv, Function.update_self]
          · rw [Function.update_of_ne hi, PartialAssignment.assign_of_notMem (by simp_all)]
      · ext i
        simp only [mem_union, mem_insert, List.mem_toFinset, List.mem_cons]
        tauto

/-- At the start of a stage, the decoder reads the first term not falsified. -/
private theorem decodeAux_none {c : List (ℕ × Bool × Bool)} (hc : c ≠ []) (θ : PartialAssignment ι)
    (Q : Finset ι) :
    F.decodeAux none θ Q c = F.decodeAux ((F.firstTerm θ).getD []) θ Q c := by
  obtain ⟨⟨j, b, e⟩, c, rfl⟩ := List.exists_cons_of_ne_nil hc
  simp only [decodeAux, Option.getD_none, Option.getD_some]

variable [Fintype ι] (F)

/-- Razborov's encoding of the first `s` queries of the canonical path of `x` from `ρ`: the
restriction fixing the queried variables to the values satisfying their terms, and the code of
the path. -/
def encode (s : ℕ) (ρ : PartialAssignment ι) (x : ι → Bool) :
    PartialAssignment ι × List (ℕ × Bool × Bool) :=
  if h : F.queried ρ = [] then (ρ, [])
  else if s ≤ (F.queried ρ).length then
    (ρ.assign ((F.queried ρ).take s).toFinset ((F.firstTerm ρ).getD []).satisfying,
      ((F.firstTerm ρ).getD []).stageCode x ((F.queried ρ).take s))
  else
    have := card_free_assign_lt h x
    ((encode (s - (F.queried ρ).length) (ρ.assign (F.queried ρ).toFinset x) x).1.assign
        (F.queried ρ).toFinset ((F.firstTerm ρ).getD []).satisfying,
      ((F.firstTerm ρ).getD []).stageCode x (F.queried ρ) ++
        (encode (s - (F.queried ρ).length) (ρ.assign (F.queried ρ).toFinset x) x).2)
termination_by #ρ.free
decreasing_by exact this

variable {F}

private theorem encode_of_queried_eq_nil (h : F.queried ρ = []) (s : ℕ) (x : ι → Bool) :
    F.encode s ρ x = (ρ, []) := by
  rw [encode, dite_eq_left h]

private theorem encode_of_le (h : F.queried ρ ≠ []) {s : ℕ} (hs : s ≤ (F.queried ρ).length)
    (x : ι → Bool) :
    F.encode s ρ x = (ρ.assign ((F.queried ρ).take s).toFinset ((F.firstTerm ρ).getD []).satisfying,
      ((F.firstTerm ρ).getD []).stageCode x ((F.queried ρ).take s)) := by
  rw [encode, dite_eq_right h, ite_eq_left hs]

private theorem encode_of_lt (h : F.queried ρ ≠ []) {s : ℕ} (hs : (F.queried ρ).length < s)
    (x : ι → Bool) :
    F.encode s ρ x =
      ((F.encode (s - (F.queried ρ).length) (ρ.assign (F.queried ρ).toFinset x) x).1.assign
        (F.queried ρ).toFinset ((F.firstTerm ρ).getD []).satisfying,
      ((F.firstTerm ρ).getD []).stageCode x (F.queried ρ) ++
        (F.encode (s - (F.queried ρ).length) (ρ.assign (F.queried ρ).toFinset x) x).2) := by
  rw [encode, dite_eq_right h, ite_eq_right (by omega)]

/-- The encoding extends the restriction it encodes. -/
private theorem encode_extends (s : ℕ) (ρ : PartialAssignment ι) (x : ι → Bool) :
    (F.encode s ρ x).1.Extends ρ := by
  intro i b hi
  have hiV : i ∉ (F.queried ρ).toFinset := fun hiV => by
    simp [free_of_mem_queried (List.mem_toFinset.1 hiV)] at hi
  by_cases h : F.queried ρ = []
  · rw [encode_of_queried_eq_nil h]
    exact hi
  by_cases hs : s ≤ (F.queried ρ).length
  · rw [encode_of_le h hs]
    dsimp only
    rw [PartialAssignment.assign_of_notMem
      fun hiW => hiV (List.mem_toFinset.2 (List.mem_of_mem_take (List.mem_toFinset.1 hiW))), hi]
  · rw [encode_of_lt h (by omega)]
    dsimp only
    rw [PartialAssignment.assign_of_notMem hiV,
      encode_extends _ (ρ.assign (F.queried ρ).toFinset x) x i b (by simp [hiV, hi])]
termination_by #ρ.free
decreasing_by exact card_free_assign_lt h x

/-- The variables an encoding stage assigns are free. -/
private theorem toFinset_take_queried_subset_free (s : ℕ) :
    ((F.queried ρ).take s).toFinset ⊆ ρ.free := fun _ hv =>
  toFinset_queried_subset_free (List.mem_toFinset.2 (List.mem_of_mem_take (List.mem_toFinset.1 hv)))

/-- After the first stage, the encoding has fixed the queried variables to the values of `x`. -/
private theorem encode_assign_eq (s : ℕ) (x : ι → Bool) {i : ι}
    (hi : i ∈ (F.queried ρ).toFinset) :
    (F.encode s (ρ.assign (F.queried ρ).toFinset x) x).1 i = some (x i) :=
  encode_extends _ _ _ _ _ (by simp [hi])

/-- Decoding the encoding of a restriction with a query path of length at least `s` gives the
restriction back, freeing the accumulated variables `Q`. -/
private theorem decodeAux_encode (hF : ∀ t ∈ F, (t.map Prod.fst).Nodup) {ρ : PartialAssignment ι}
    {s : ℕ} {x : ι → Bool} (hs : s ≤ F.pathLength ρ x) (Q : Finset ι) :
    F.decodeAux none (F.encode s ρ x).1 Q (F.encode s ρ x).2 = ρ.unassign Q := by
  by_cases h : F.queried ρ = []
  · rw [encode_of_queried_eq_nil h]
    rfl
  obtain ⟨t, ht⟩ := exists_firstTerm_of_queried_ne_nil h
  have htV : ∀ v ∈ F.queried ρ, v ∈ t.map Prod.fst := fun v hv => mem_map_fst_of_mem_queried ht hv
  by_cases hsV : s ≤ (F.queried ρ).length
  · rw [encode_of_le h hsV, ht, Option.getD_some]
    dsimp only
    by_cases hs0 : s = 0
    · subst hs0
      simp only [List.take_zero, List.toFinset_nil, Term.stageCode, decodeAux]
      exact congrArg (PartialAssignment.unassign · Q) (PartialAssignment.assign_eq_self (by simp))
    have hW : (F.queried ρ).take s ≠ [] := by simp [List.take_eq_nil_iff, hs0, h]
    rw [decodeAux_none (Term.stageCode_eq_nil_iff.not.2 hW),
      firstTerm_assign_satisfying hF ht (PartialAssignment.Extends.refl ρ)
        (fun _ hv => List.mem_of_mem_take hv)
        (fun v hv _ => free_of_mem_queried hv),
      Option.getD_some, ← List.append_nil (Term.stageCode _ _ _),
      decodeAux_stageCode (fun v hv => htV v (List.mem_of_mem_take hv)) hW]
    simp only [decodeAux, PartialAssignment.assign_assign]
    exact PartialAssignment.unassign_union_assign (toFinset_take_queried_subset_free s) x
  · have hlt : (F.queried ρ).length < s := by omega
    rw [encode_of_lt h hlt, ht, Option.getD_some]
    dsimp only
    rw [decodeAux_none (List.append_ne_nil_of_left_ne_nil (Term.stageCode_eq_nil_iff.not.2 h) _),
      firstTerm_assign_satisfying hF ht ((encode_extends _ _ _).trans
          (PartialAssignment.extends_assign toFinset_queried_subset_free x))
        (fun _ hv => hv) (fun _ hv hv' => absurd hv hv'),
      Option.getD_some, decodeAux_stageCode htV h, PartialAssignment.assign_assign,
      PartialAssignment.assign_eq_self fun i hi => encode_assign_eq _ x hi,
      decodeAux_encode hF (ρ := ρ.assign (F.queried ρ).toFinset x) (by
        rw [pathLength_of_queried_ne_nil h] at hs
        omega)]
    exact PartialAssignment.unassign_union_assign toFinset_queried_subset_free x
termination_by #ρ.free
decreasing_by exact card_free_assign_lt h x

/-- **Razborov's decoding.** The encoding of a restriction with a query path of length at least
`s` determines the restriction. -/
theorem decode_encode (hF : ∀ t ∈ F, (t.map Prod.fst).Nodup) {s : ℕ} {x : ι → Bool}
    (hs : s ≤ F.pathLength ρ x) : F.decode (F.encode s ρ x).1 (F.encode s ρ x).2 = ρ := by
  rw [decode, decodeAux_encode hF hs, PartialAssignment.unassign_empty]

/-- The encoding fixes `s` more variables. -/
private theorem card_free_encode (hF : ∀ t ∈ F, (t.map Prod.fst).Nodup) {ρ : PartialAssignment ι}
    {s : ℕ} {x : ι → Bool} (hs : s ≤ F.pathLength ρ x) :
    #(F.encode s ρ x).1.free = #ρ.free - s := by
  by_cases h : F.queried ρ = []
  · rw [pathLength_of_queried_eq_nil h] at hs
    rw [encode_of_queried_eq_nil h, Nat.le_zero.1 hs, Nat.sub_zero]
  have hnd := nodup_queried (ρ := ρ) hF
  by_cases hsV : s ≤ (F.queried ρ).length
  · rw [encode_of_le h hsV]
    dsimp only
    rw [PartialAssignment.free_assign, card_sdiff_of_subset (toFinset_take_queried_subset_free s),
      List.toFinset_card_of_nodup ((List.take_sublist _ _).nodup hnd), List.length_take,
      min_eq_left hsV]
  · rw [encode_of_lt h (by omega)]
    dsimp only
    have hlen := (List.toFinset_card_of_nodup hnd).symm.trans_le
      (card_le_card (toFinset_queried_subset_free (ρ := ρ)))
    rw [PartialAssignment.free_assign, sdiff_eq_self_of_disjoint (disjoint_left.2 fun i hi hiV => by
        simp [PartialAssignment.mem_free, encode_assign_eq _ x hiV] at hi),
      card_free_encode hF (ρ := ρ.assign (F.queried ρ).toFinset x) (by
        rw [pathLength_of_queried_ne_nil h] at hs
        omega),
      PartialAssignment.free_assign, card_sdiff_of_subset toFinset_queried_subset_free,
      List.toFinset_card_of_nodup hnd]
    omega
termination_by #ρ.free
decreasing_by exact card_free_assign_lt h x

/-- The code of a query path of length at least `s` has length `s`. -/
private theorem length_encode {ρ : PartialAssignment ι} {s : ℕ} {x : ι → Bool}
    (hs : s ≤ F.pathLength ρ x) : (F.encode s ρ x).2.length = s := by
  by_cases h : F.queried ρ = []
  · rw [pathLength_of_queried_eq_nil h] at hs
    rw [encode_of_queried_eq_nil h, Nat.le_zero.1 hs]
    rfl
  by_cases hsV : s ≤ (F.queried ρ).length
  · rw [encode_of_le h hsV]
    simp [hsV]
  · rw [encode_of_lt h (by omega)]
    dsimp only
    rw [List.length_append, Term.length_stageCode,
      length_encode (ρ := ρ.assign (F.queried ρ).toFinset x) (by
        rw [pathLength_of_queried_ne_nil h] at hs
        omega)]
    omega
termination_by #ρ.free
decreasing_by exact card_free_assign_lt h x

/-- The positions recorded in a code are positions in terms of at most `k` literals. -/
private theorem fst_lt_of_mem_encode {k : ℕ} (hF : ∀ t ∈ F, t.length ≤ k) (s : ℕ)
    (ρ : PartialAssignment ι) (x : ι → Bool) {e : ℕ × Bool × Bool}
    (he : e ∈ (F.encode s ρ x).2) : e.1 < k := by
  by_cases h : F.queried ρ = []
  · rw [encode_of_queried_eq_nil h] at he
    simp at he
  obtain ⟨t, ht⟩ := exists_firstTerm_of_queried_ne_nil h
  have htk := hF t (mem_of_firstTerm_eq_some ht)
  have htV : ∀ v ∈ F.queried ρ, v ∈ t.map Prod.fst := fun v hv => mem_map_fst_of_mem_queried ht hv
  by_cases hsV : s ≤ (F.queried ρ).length
  · rw [encode_of_le h hsV, ht, Option.getD_some] at he
    exact (Term.fst_lt_of_mem_stageCode (fun v hv => htV v (List.mem_of_mem_take hv)) he).trans_le
      htk
  · rw [encode_of_lt h (by omega), ht, Option.getD_some] at he
    rcases List.mem_append.1 he with he | he
    · exact (Term.fst_lt_of_mem_stageCode htV he).trans_le htk
    · exact fst_lt_of_mem_encode hF _ (ρ.assign (F.queried ρ).toFinset x) x he
termination_by #ρ.free
decreasing_by exact card_free_assign_lt h x

/-- The codes of length `s` over positions below `k`. -/
private theorem mem_image_ofFn {k s : ℕ} {c : List (ℕ × Bool × Bool)} (hc : c.length = s)
    (hk : ∀ e ∈ c, e.1 < k) :
    c ∈ (Fintype.piFinset fun _ : Fin s => range k ×ˢ (univ : Finset (Bool × Bool))).image
      List.ofFn := by
  subst hc
  refine mem_image.2 ⟨fun i => c[i], Fintype.mem_piFinset.2 fun i => ?_, List.ofFn_getElem⟩
  simpa using hk _ (List.getElem_mem _)

/-- **Counting bad extensions.** Among the extensions of `ρ₀` leaving `ℓ` variables free, at most
`#E(ℓ - s) (4k)^s` have a canonical query path of length at least `s`, where `E(m)` are the
extensions of `ρ₀` leaving `m` variables free, if every term of `F` has at most `k` literals and
reads each variable once. -/
theorem card_filter_pathLength_le {k : ℕ} (hk : ∀ t ∈ F, t.length ≤ k)
    (hnd : ∀ t ∈ F, (t.map Prod.fst).Nodup) (ρ₀ : PartialAssignment ι) (ℓ s : ℕ) :
    #((ρ₀.extensions ℓ).filter fun ρ => ∃ x, s ≤ F.pathLength ρ x) ≤
      #(ρ₀.extensions (ℓ - s)) * (4 * k) ^ s := by
  set C := (Fintype.piFinset fun _ : Fin s => range k ×ˢ (univ : Finset (Bool × Bool))).image
    List.ofFn
  have hC : #C ≤ (4 * k) ^ s := card_image_le.trans (by simp [mul_comm])
  calc _ ≤ #((ρ₀.extensions (ℓ - s) ×ˢ C).image fun p => F.decode p.1 p.2) :=
        card_le_card fun ρ hρ => by
          obtain ⟨hρ, x, hx⟩ := mem_filter.1 hρ
          obtain ⟨hext, hcard⟩ := PartialAssignment.mem_extensions.1 hρ
          refine mem_image.2 ⟨F.encode s ρ x, mem_product.2 ⟨?_, ?_⟩, decode_encode hnd hx⟩
          · refine PartialAssignment.mem_extensions.2 ⟨(encode_extends s ρ x).trans hext, ?_⟩
            rw [card_free_encode hnd hx, hcard]
          · exact mem_image_ofFn (length_encode hx) fun e he => fst_lt_of_mem_encode hk s ρ x he
    _ ≤ #(ρ₀.extensions (ℓ - s) ×ˢ C) := card_image_le
    _ ≤ _ := by
      rw [card_product]
      exact Nat.mul_le_mul_left _ hC

/-- **Håstad's switching lemma**, counting version. If every term of `F` has at most `k` literals
and reads each variable once, then at most `#E(ℓ - s) (4k)^s` of the extensions of `ρ₀` leaving `ℓ`
variables free leave `F` with decision tree complexity at least `s`, where `E(m)` are the
extensions of `ρ₀` leaving `m` variables free. For `ρ₀` fixing nothing, these are all restrictions
(`PartialAssignment.withFree`). -/
theorem card_switching_le {k : ℕ} (hk : ∀ t ∈ F, t.length ≤ k)
    (hnd : ∀ t ∈ F, (t.map Prod.fst).Nodup) (ρ₀ : PartialAssignment ι) (ℓ s : ℕ) :
    #((ρ₀.extensions ℓ).filter fun ρ => s ≤ complexity fun x => DNF.eval (ρ.fill x) F) ≤
      #(ρ₀.extensions (ℓ - s)) * (4 * k) ^ s := by
  refine (card_le_card fun ρ hρ => ?_).trans (card_filter_pathLength_le hk hnd ρ₀ ℓ s)
  obtain ⟨hρ, hs⟩ := mem_filter.1 hρ
  refine mem_filter.2 ⟨hρ, ?_⟩
  by_contra! h
  exact absurd hs (not_le.2 (complexity_lt_of_forall_pathLength_lt h))

end DNF

end Cslib.Logic.PL
