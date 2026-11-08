/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Table.DeltaMatroid
public import Complexity.Foundations.Data.BitString.Enumeration
public import Complexity.Foundations.Data.BitString.ListParity
import Mathlib.Data.List.GetD

/-!
# Explicit parity chains

The chain replaces an EVEN constraint by tables of width at most three. It has `k - 2`
constraints and `k - 3` fresh variables when `k ≥ 4`; smaller scopes retain one table.
Fresh names begin at the supplied offset. Construction traverses the actual scope, never
an unchecked binary arity. The chain is an original implementation detail for the difference
reduction of [DvorakKupec2015], Section 3, Lemma 5, Corollary 4 and Theorem 2,
printed pp. 439–440. No geometric realization of the expansion is asserted or needed.

## Main definitions

* `Cslib.Logic.PL.CSP.Table.evenTable`: explicit even-parity rows.
* `Cslib.Logic.PL.CSP.Table.parityChain`: the actual width-three expansion.
-/

public section

namespace Cslib.Logic.PL.CSP.Table

open Cslib.BitString

/-- Explicit even-parity table. Only widths zero through three are generated at runtime by
`parityChain`; larger tables are a mathematical API, with no uniform polynomial claim. -/
@[expose] def evenTable (width : ℕ) : Table :=
  ⟨width, (enumList width).filter fun row => !wordParity row⟩

@[simp] theorem arity_evenTable (width : ℕ) : (evenTable width).arity = width := rfl

/-- Every row has exactly the declared width, including the nullary row. -/
theorem wellFormed_evenTable (width : ℕ) : (evenTable width).wellFormed = true := by
  apply wellFormed_eq_true.mpr
  intro row hrow
  exact length_of_mem_enumList (List.mem_filter.mp hrow).1

/-- The table includes the exact-arity guard even for malformed supplied rows. -/
theorem sem_evenTable (width : ℕ) (row : List Bool) :
    (evenTable width).sem row = true ↔ row.length = width ∧ wordParity row = false := by
  rw [sem_eq_true]
  constructor
  · rintro ⟨_, hrow⟩
    exact ⟨length_of_mem_enumList (List.mem_filter.mp hrow).1,
      (by simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hrow).2)⟩
  · rintro ⟨hlen, hp⟩
    exact ⟨wellFormed_evenTable width,
      List.mem_filter.mpr ⟨mem_enumList.mpr hlen, (by simpa only [Bool.not_eq_true'] using hp)⟩⟩

/-- Explicit tables denote the existing parity relation, without a second Boolean model. -/
theorem booleanRelation_evenTable (width : ℕ) :
    booleanRelation arity sem (evenTable width) =
      {x : Fin width → Bool | parityOn Finset.univ x = false} := by
  ext x
  change Fin width → Bool at x
  change (evenTable width).sem (List.ofFn x) = true ↔ parityOn Finset.univ x = false
  rw [sem_evenTable]
  simp only [List.length_ofFn, wordParity_ofFn, true_and]

/-- All parity tables used by a chain are nonempty even delta-matroids. -/
theorem isEvenDeltaMatroid_evenTable (width : ℕ) :
    IsEvenDeltaMatroid (booleanRelation arity sem (evenTable width)) := by
  rw [booleanRelation_evenTable]
  apply isEvenDeltaMatroid_parityOn_fiber
  exact ⟨fun _ => false, by
    rw [parityOn_eq_sum]
    change (∑ _ : Fin width, (0 : Bool)) = 0
    exact Finset.sum_const_zero⟩

/-- Chain tail with the accumulated parity variable first. Each recursive step consumes one
actual boundary entry and allocates one fresh binary name. -/
@[expose] def parityChainTail (fresh first : ℕ) : List ℕ → CSP Table ℕ
  | [] => [(evenTable 1, [first])]
  | [b] => [(evenTable 2, [first, b])]
  | [b, c] => [(evenTable 3, [first, b, c])]
  | b :: c :: d :: rest =>
    (evenTable 3, [first, b, fresh]) :: parityChainTail (fresh + 1) fresh (c :: d :: rest)

/-- Width-three expansion, retaining the original boundary order. Names below `fresh` are
reserved for the caller; an empty boundary is the true nullary parity table. -/
@[expose] def parityChain (fresh : ℕ) (scope : List ℕ) : CSP Table ℕ :=
  match scope with
  | [] => [(evenTable 0, [])]
  | first :: rest => parityChainTail fresh first rest

/-- Exactly the requested number of chain constraints. -/
theorem length_parityChainTail (fresh first : ℕ) (rest : List ℕ) :
    (parityChainTail fresh first rest).length = max 1 (rest.length - 1) := by
  induction rest using List.twoStepInduction generalizing fresh first with
  | nil => rfl
  | singleton b => rfl
  | cons_cons b c rest _ ih =>
    cases rest with
    | nil => rfl
    | cons d rest =>
      simp only [parityChainTail, List.length_cons]
      rw [ih c]
      simp only [List.length_cons]
      omega

/-- Linear constraint count, including empty and short boundaries. -/
theorem length_parityChain (fresh : ℕ) (scope : List ℕ) :
    (parityChain fresh scope).length = max 1 (scope.length - 2) := by
  cases scope with
  | nil => rfl
  | cons first rest => simpa [parityChain] using length_parityChainTail fresh first rest

/-- Every output table and scope has matching width at most three. -/
theorem parityChainTail_width (fresh first : ℕ) (rest : List ℕ)
    (c : Constraint Table ℕ) (hc : c ∈ parityChainTail fresh first rest) :
    c.1.arity = c.2.length ∧ c.2.length ≤ 3 ∧
      ∃ n ≤ 3, c.1 = evenTable n := by
  induction rest using List.twoStepInduction generalizing fresh first with
  | nil =>
    have he : c = (evenTable 1, [first]) := by
      simpa only [parityChainTail, List.mem_singleton] using hc
    subst c
    exact ⟨rfl, by change 1 ≤ 3; omega, 1, by omega, rfl⟩
  | singleton b =>
    have he : c = (evenTable 2, [first, b]) := by
      simpa only [parityChainTail, List.mem_singleton] using hc
    subst c
    exact ⟨rfl, by change 2 ≤ 3; omega, 2, by omega, rfl⟩
  | cons_cons b d rest _ ih =>
    cases rest with
    | nil =>
      have he : c = (evenTable 3, [first, b, d]) := by
        simpa only [parityChainTail, List.mem_singleton] using hc
      subst c
      exact ⟨rfl, by change 3 ≤ 3; omega, 3, by omega, rfl⟩
    | cons e rest =>
      simp only [parityChainTail, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨rfl, by change 3 ≤ 3; omega, 3, by omega, rfl⟩
      · exact ih d (fresh + 1) fresh hc

/-- The actual expansion uses only nonempty even delta-matroid relations. -/
theorem parityChain_tables (fresh : ℕ) (scope : List ℕ)
    (c : Constraint Table ℕ) (hc : c ∈ parityChain fresh scope) :
    c.1.arity = c.2.length ∧ c.2.length ≤ 3 ∧
      IsEvenDeltaMatroid (booleanRelation arity sem c.1) := by
  cases scope with
  | nil =>
    have he : c = (evenTable 0, []) := by simpa [parityChain] using hc
    subst c
    exact ⟨rfl, by decide, isEvenDeltaMatroid_evenTable 0⟩
  | cons first rest =>
    obtain ⟨hw, hb, n, _, hn⟩ := parityChainTail_width fresh first rest c hc
    exact ⟨hw, hb, by rw [hn]; exact isEvenDeltaMatroid_evenTable n⟩

/-- Every satisfying chain assignment has even boundary parity. This direction needs no
freshness or distinctness assumption, so repeated boundary names cause no semantic shortcut. -/
theorem parityChainTail_sound (fresh first : ℕ) (rest : List ℕ) (σ : ℕ → Bool)
    (h : (parityChainTail fresh first rest).eval sem σ = true) :
    wordParity ((first :: rest).map σ) = false := by
  induction rest using List.twoStepInduction generalizing fresh first with
  | nil =>
    exact (sem_evenTable 1 _).mp (by simpa only [parityChainTail, CSP.eval,
      List.all_cons, List.all_nil, Bool.and_true, Constraint.eval] using h) |>.2
  | singleton b =>
    exact (sem_evenTable 2 _).mp (by simpa only [parityChainTail, CSP.eval,
      List.all_cons, List.all_nil, Bool.and_true, Constraint.eval] using h) |>.2
  | cons_cons b c rest _ ih =>
    cases rest with
    | nil =>
      exact (sem_evenTable 3 _).mp (by simpa only [parityChainTail, CSP.eval,
        List.all_cons, List.all_nil, Bool.and_true, Constraint.eval] using h) |>.2
    | cons d rest =>
      have hh : (evenTable 3).sem ([first, b, fresh].map σ) = true ∧
          (parityChainTail (fresh + 1) fresh (c :: d :: rest)).eval sem σ = true := by
        simpa only [parityChainTail, CSP.eval, List.all_cons, Bool.and_eq_true,
          Constraint.eval] using h
      have hp := (sem_evenTable 3 _).mp hh.1 |>.2
      have ht := ih c (fresh + 1) fresh hh.2
      simp only [List.map_cons, List.map_nil, wordParity_cons, wordParity_nil,
        Bool.xor_false] at hp
      have he : σ fresh = wordParity ((c :: d :: rest).map σ) := by
        change (σ fresh ^^ wordParity ((c :: d :: rest).map σ)) = false at ht
        simpa using ht
      change (σ first ^^ (σ b ^^ wordParity ((c :: d :: rest).map σ))) = false
      rwa [← he]

/-- A satisfying expansion enforces even parity on its original boundary, including zero
and one ports. -/
theorem parityChain_sound (fresh : ℕ) (scope : List ℕ) (σ : ℕ → Bool)
    (h : (parityChain fresh scope).eval sem σ = true) : wordParity (scope.map σ) = false := by
  cases scope with
  | nil => rfl
  | cons first rest => exact parityChainTail_sound fresh first rest σ h

/-- Extend any even boundary assignment using only the consecutive allocated auxiliary block.
Names outside that block are preserved, including arbitrary large binary names. -/
theorem parityChainTail_complete (fresh first : ℕ) (rest : List ℕ) (σ : ℕ → Bool)
    (hbound : ∀ v ∈ first :: rest, v < fresh)
    (hparity : wordParity ((first :: rest).map σ) = false) :
    ∃ τ : ℕ → Bool,
      (∀ v, v < fresh ∨ fresh + (rest.length - 2) ≤ v → τ v = σ v) ∧
      (parityChainTail fresh first rest).eval sem τ = true := by
  induction rest using List.twoStepInduction generalizing fresh first σ with
  | nil =>
    refine ⟨σ, fun _ _ => rfl, ?_⟩
    simp only [parityChainTail, CSP.eval, List.all_cons, List.all_nil, Bool.and_true,
      Constraint.eval]
    exact (sem_evenTable 1 _).mpr ⟨rfl, hparity⟩
  | singleton b =>
    refine ⟨σ, fun _ _ => rfl, ?_⟩
    simp only [parityChainTail, CSP.eval, List.all_cons, List.all_nil, Bool.and_true,
      Constraint.eval]
    exact (sem_evenTable 2 _).mpr ⟨rfl, hparity⟩
  | cons_cons b c rest _ ih =>
    cases rest with
    | nil =>
      refine ⟨σ, fun _ _ => rfl, ?_⟩
      simp only [parityChainTail, CSP.eval, List.all_cons, List.all_nil, Bool.and_true,
        Constraint.eval]
      exact (sem_evenTable 3 _).mpr ⟨rfl, hparity⟩
    | cons d rest =>
      let σ' := Function.update σ fresh (σ first ^^ σ b)
      have hfirst := hbound first (by simp)
      have hb := hbound b (by simp)
      have hread (v : ℕ) (hv : v < fresh) : σ' v = σ v := by
        exact Function.update_of_ne (by omega) _ _
      have hnext : ∀ v ∈ fresh :: c :: d :: rest, v < fresh + 1 := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · omega
        · exact (hbound v (List.mem_cons_of_mem first (List.mem_cons_of_mem b hv))).trans
            (Nat.lt_succ_self fresh)
      have hparity' : wordParity ((fresh :: c :: d :: rest).map σ') = false := by
        have he : (c :: d :: rest).map σ' = (c :: d :: rest).map σ := by
          apply List.map_congr_left
          intro v hv
          exact hread v (hbound v (List.mem_cons_of_mem first (List.mem_cons_of_mem b hv)))
        change (σ' fresh ^^ wordParity ((c :: d :: rest).map σ')) = false
        rw [he]
        rw [show σ' fresh = (σ first ^^ σ b) from Function.update_self _ _ _]
        rw [Bool.xor_assoc]
        exact hparity
      obtain ⟨τ, hτ, heval⟩ := ih c (fresh + 1) fresh σ' hnext hparity'
      refine ⟨τ, ?_, ?_⟩
      · intro v hv
        have hv' : v < fresh + 1 ∨ fresh + 1 + ((c :: d :: rest).length - 2) ≤ v := by
          simp only [List.length_cons] at hv ⊢
          omega
        rw [hτ v hv']
        exact Function.update_of_ne (by simp only [List.length_cons] at hv; omega) _ _
      · have htfirst : τ first = σ first := (hτ first (.inl (by omega))).trans
          (hread first hfirst)
        have htb : τ b = σ b := (hτ b (.inl (by omega))).trans (hread b hb)
        have htfresh : τ fresh = (σ first ^^ σ b) := by
          rw [hτ fresh (.inl (by omega))]
          exact Function.update_self _ _ _
        simp only [parityChainTail, CSP.eval, List.all_cons, Bool.and_eq_true,
          Constraint.eval]
        refine ⟨(sem_evenTable 3 _).mpr ⟨rfl, ?_⟩, heval⟩
        simp only [List.map_cons, List.map_nil, wordParity_cons, wordParity_nil,
          Bool.xor_false, htfirst, htb, htfresh]
        cases σ first <;> cases σ b <;> rfl

/-- Exact existential semantics of the actual chain with its allocated names. -/
theorem parityChain_complete (fresh : ℕ) (scope : List ℕ) (σ : ℕ → Bool)
    (hbound : ∀ v ∈ scope, v < fresh) (hparity : wordParity (scope.map σ) = false) :
    ∃ τ : ℕ → Bool,
      (∀ v, v < fresh ∨ fresh + (scope.length - 3) ≤ v → τ v = σ v) ∧
      (parityChain fresh scope).eval sem τ = true := by
  cases scope with
  | nil =>
    refine ⟨σ, fun _ _ => rfl, ?_⟩
    change (evenTable 0).sem [] && true = true
    decide
  | cons first rest =>
    have hlen : (first :: rest).length - 3 = rest.length - 2 := by
      simp only [List.length_cons]; omega
    simpa only [parityChain, hlen] using
      parityChainTail_complete fresh first rest σ hbound hparity

/-- Exactly two occurrences of each allocated auxiliary, and the original multiplicity of
all boundary names. This equality does not assume that the caller chose fresh names. -/
theorem count_vars_parityChainTail (fresh first : ℕ) (rest : List ℕ) (v : ℕ) :
    (parityChainTail fresh first rest).vars.count v = (first :: rest).count v +
      if fresh ≤ v ∧ v < fresh + (rest.length - 2) then 2 else 0 := by
  induction rest using List.twoStepInduction generalizing fresh first with
  | nil => simp [parityChainTail, CSP.vars]
  | singleton b => simp [parityChainTail, CSP.vars]
  | cons_cons b c rest _ ih =>
    cases rest with
    | nil => simp [parityChainTail, CSP.vars]
    | cons d rest =>
      change ([first, b, fresh] ++ (parityChainTail (fresh + 1) fresh
        (c :: d :: rest)).vars).count v = _
      rw [List.count_append, ih c]
      simp only [List.count_cons, List.count_nil, List.length_cons]
      split_ifs <;> simp_all only [beq_iff_eq] <;> omega

/-- Every old boundary occurrence is retained once, and every new auxiliary occurs twice. -/
theorem count_vars_parityChain (fresh : ℕ) (scope : List ℕ) (v : ℕ) :
    (parityChain fresh scope).vars.count v = scope.count v +
      if fresh ≤ v ∧ v < fresh + (scope.length - 3) then 2 else 0 := by
  cases scope with
  | nil => simp [parityChain, CSP.vars]
  | cons first rest =>
    have hlen : (first :: rest).length - 3 = rest.length - 2 := by
      simp only [List.length_cons]; omega
    simpa only [parityChain, hlen] using count_vars_parityChainTail fresh first rest v

/-- Output names are boundary names or precisely the allocated consecutive auxiliary interval. -/
theorem mem_vars_parityChain (fresh : ℕ) (scope : List ℕ) (v : ℕ) :
    v ∈ (parityChain fresh scope).vars ↔
      v ∈ scope ∨ fresh ≤ v ∧ v < fresh + (scope.length - 3) := by
  rw [← List.count_pos_iff, count_vars_parityChain, ← List.count_pos_iff]
  split_ifs <;> omega

/-- The entire output lies below the first unused name when all boundary names are reserved. -/
theorem parityChain_names_lt (fresh : ℕ) (scope : List ℕ)
    (hbound : ∀ v ∈ scope, v < fresh) (v : ℕ)
    (hv : v ∈ (parityChain fresh scope).vars) : v < fresh + (scope.length - 3) := by
  rcases (mem_vars_parityChain fresh scope v).mp hv with hb | ha
  · exact (hbound v hb).trans_le (Nat.le_add_right _ _)
  · exact ha.2

/-- No scope repeats a name when the original boundary is distinct and auxiliaries are fresh. -/
theorem parityChainTail_scopes_nodup (fresh first : ℕ) (rest : List ℕ)
    (hnd : (first :: rest).Nodup) (hbound : ∀ v ∈ first :: rest, v < fresh)
    (constraint : Constraint Table ℕ) (hc : constraint ∈ parityChainTail fresh first rest) :
    constraint.2.Nodup := by
  induction rest using List.twoStepInduction generalizing fresh first with
  | nil =>
    have he : constraint = (evenTable 1, [first]) := by simpa [parityChainTail] using hc
    subst constraint
    exact hnd
  | singleton b =>
    have he : constraint = (evenTable 2, [first, b]) := by simpa [parityChainTail] using hc
    subst constraint
    exact hnd
  | cons_cons b c rest _ ih =>
    cases rest with
    | nil =>
      have he : constraint = (evenTable 3, [first, b, c]) := by
        simpa [parityChainTail] using hc
      subst constraint
      exact hnd
    | cons d rest =>
      simp only [parityChainTail, List.mem_cons] at hc
      rcases hc with rfl | hc
      · have hfirst := hbound first (by simp)
        have hb := hbound b (by simp)
        have hne : first ≠ b := fun he => hnd.notMem (by simp [he])
        simp only [List.nodup_cons, List.mem_cons,
          not_or, List.not_mem_nil, not_false_eq_true, and_true]
        exact ⟨⟨hne, by omega⟩, by omega, trivial, List.nodup_nil⟩
      · apply ih c (fresh + 1) fresh ?_ ?_ hc
        · apply List.nodup_cons.mpr
          refine ⟨?_, hnd.tail.tail⟩
          intro hf
          have := hbound fresh (List.mem_cons_of_mem first (List.mem_cons_of_mem b hf))
          omega
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · omega
          · exact (hbound v (List.mem_cons_of_mem first
              (List.mem_cons_of_mem b hv))).trans (Nat.lt_succ_self fresh)

/-- Fresh parity expansion satisfies the target's no-repeat-within-one-scope convention. -/
theorem parityChain_scopes_nodup (fresh : ℕ) (scope : List ℕ) (hnd : scope.Nodup)
    (hbound : ∀ v ∈ scope, v < fresh)
    (constraint : Constraint Table ℕ) (hc : constraint ∈ parityChain fresh scope) :
    constraint.2.Nodup := by
  cases scope with
  | nil =>
    have he : constraint = (evenTable 0, []) := by simpa [parityChain] using hc
    subst constraint
    exact List.nodup_nil
  | cons first rest => exact parityChainTail_scopes_nodup fresh first rest hnd hbound constraint hc

end Cslib.Logic.PL.CSP.Table
