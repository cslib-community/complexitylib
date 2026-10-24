/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Scheduler.Phase
public import Complexity.Computability.Circuit.Boolean.BatchOr
public import Complexity.Computability.Circuit.Boolean.DuplicateFlags
import Complexity.Computability.Circuit.Boolean.Synthesis

/-!
# A circuit for one scheduler phase

The phase function `next` is synthesized stage by stage, each stage reading wires built by the
earlier ones:

1. candidate bits: the target bits plus fixed offsets, one negation per set offset bit;
2. occupancy: one shared OR lookup of all candidates among the accepted line points
   (`batchOrCircuit`);
3. duplicates: for each menu entry, duplicate flags among its candidates
   (`duplicateFlagsCircuit`), with padding records marked by a tag bit;
4. clean flags, a disjunction over the scalars per request;
5. success: the clean flags of each entry, sorted, read at position `⌈2 ^ p / 2⌉ - 1`;
6. the first successful entry, from shared prefix disjunctions;
7. the chosen clean flags and candidate lines, disjunctions over the entries;
8. the enriched pending records, sorted with clean records first.

`phaseCost` is the exact sum of the stage budgets; it counts every gate, including constants. The
construction is existential and does not certify the running time of any constructor.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Scheduler.phaseCost`: the phase gate budget.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.Scheduler.exists_next_circuit`: a circuit computing
  `next` within `phaseCost` gates.

## References

* Adapted from MassProduction/Nonuniform/BufferedPhaseCost.lean,
  MassProduction/Nonuniform/BufferOccupancy.lean,
  MassProduction/Nonuniform/CandidateSelection.lean,
  MassProduction/Nonuniform/ConstantTranslations.lean and
  MassProduction/Nonuniform/MaskedOr.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
  using the sorting network of
  [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Scheduler

open Finset BitString BitonicSort

variable {K : Type*} [Field K] {ℓ b s D p a r : ℕ}
  (hk : a + arity p = 2 ^ D) (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
  (menu : Fin r → Fin (arity p) → Fin ℓ → K)
  {src : Set (BooleanFunction (2 ^ D * width D (ℓ * b) s))}

private theorem add_false (x : Bool) : x + false = x := by cases x <;> rfl

private theorem add_true (x : Bool) : x + true = !x := by cases x <;> rfl

/-- Stage 1: each candidate bit is an input bit or its negation. -/
private theorem synthesis_candidate (hin : inputs _ ⊆ src) :
    Synthesis interpretation src
      (Set.range fun q : Fin r × Fin (arity p) × Fin s × Fin (ℓ * b) =>
        fun x => candidate hk bits scalar menu x q.1 q.2.1 q.2.2.1 q.2.2.2)
      (r * arity p * s * (ℓ * b)) := by
  refine (Synthesis.family _ (fun _ => 1) fun q => ?_).mono Set.Subset.rfl Set.Subset.rfl
    (le_of_eq ?_)
  · obtain ⟨e, i, c, β⟩ := q
    let w := finProdFinEquiv (pending hk i, targetBit (D := D) (s := s) β)
    have hw : (fun x : BitString (2 ^ D * width D (ℓ * b) s) => x w) ∈ src := hin ⟨w, rfl⟩
    cases hb : pointBits bits ((scalar c : K) • menu e i) β
    · have : (fun x => candidate hk bits scalar menu x e i c β) = fun x => x w := by
        funext x
        simp only [candidate, Pi.add_apply, hb, add_false]
        rfl
      simpa only [this] using (Synthesis.of_mem hw).mono Set.Subset.rfl Set.Subset.rfl
        (Nat.zero_le 1)
    · have : (fun x => candidate hk bits scalar menu x e i c β) = fun x => !x w := by
        funext x
        simp only [candidate, Pi.add_apply, hb, add_true]
        rfl
      simpa only [this] using (Synthesis.of_mem hw).not
  · simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, mul_one,
      Nat.mul_assoc]

/-- Stage 2: occupancy by one shared OR lookup among the accepted line points. -/
private theorem synthesis_occupied (hin : inputs _ ⊆ src)
    (hcand : (Set.range fun q : Fin r × Fin (arity p) × Fin s × Fin (ℓ * b) =>
      fun x => candidate hk bits scalar menu x q.1 q.2.1 q.2.2.1 q.2.2.2) ⊆ src) :
    Synthesis interpretation src
      (Set.range fun q : Fin r × Fin (arity p) × Fin s =>
        fun x => occupied hk bits scalar menu x q.1 q.2.1 q.2.2)
      (48 * (r * arity p * s + a * s + 1) * (Nat.clog 2 (r * arity p * s + a * s) + 1) ^ 2 *
        (ℓ * b + 1 + 1)) := by
  classical
  let ι := (Fin a × Fin s × Fin (ℓ * b)) ⊕ (Fin r × Fin (arity p) × Fin s × Fin (ℓ * b))
  let eι := Fintype.equivFin ι
  let eS := Fintype.equivFin (Fin a × Fin s)
  let eQ := Fintype.equivFin (Fin r × Fin (arity p) × Fin s)
  let g : Fin (Fintype.card ι) → BooleanFunction (2 ^ D * width D (ℓ * b) s) := fun w =>
    Sum.elim (fun q x => x (finProdFinEquiv (accepted hk q.1, lineBit q.2.1 q.2.2)))
      (fun q x => candidate hk bits scalar menu x q.1 q.2.1 q.2.2.1 q.2.2.2) (eι.symm w)
  have hg : ∀ w, g w ∈ src := by
    intro w
    rcases h : eι.symm w with q | q
    · simp only [g, h, Sum.elim_inl]
      exact hin ⟨_, rfl⟩
    · simp only [g, h, Sum.elim_inr]
      exact hcand ⟨q, rfl⟩
  let sourceKeys : Fin (Fintype.card (Fin a × Fin s)) → Fin (ℓ * b) →
      Fin (Fintype.card ι) ⊕ Bool :=
    fun q β => .inl (eι (.inl ((eS.symm q).1, (eS.symm q).2, β)))
  let sourceValues : Fin (Fintype.card (Fin a × Fin s)) → Fin 1 →
      Fin (Fintype.card ι) ⊕ Bool := fun _ _ => .inr true
  let queryKeys : Fin (Fintype.card (Fin r × Fin (arity p) × Fin s)) → Fin (ℓ * b) →
      Fin (Fintype.card ι) ⊕ Bool :=
    fun q β => .inl (eι (.inr ((eQ.symm q).1, (eQ.symm q).2.1, (eQ.symm q).2.2, β)))
  refine (Synthesis.circuit (batchOrCircuit sourceKeys sourceValues queryKeys) g hg).mono
    Set.Subset.rfl ?_ ?_
  · rintro _ ⟨⟨e, i, c⟩, rfl⟩
    refine ⟨finProdFinEquiv (eQ (e, i, c), 0), funext fun x => Bool.eq_iff_iff.mpr ?_⟩
    beta_reduce
    have hsk (q : Fin (Fintype.card (Fin a × Fin s))) :
        substitute (sourceKeys q) (fun w => g w x) =
          line x (accepted hk (eS.symm q).1) (eS.symm q).2 := by
      funext β
      simp only [substitute, sourceKeys, g, Sum.elim_inl, Equiv.symm_apply_apply, line]
    have hqk : substitute (queryKeys (eQ (e, i, c))) (fun w => g w x) =
        candidate hk bits scalar menu x e i c := by
      funext β
      simp only [substitute, queryKeys, g, Sum.elim_inr, Sum.elim_inl, Equiv.symm_apply_apply]
    have hsv (q : Fin (Fintype.card (Fin a × Fin s))) :
        substitute (sourceValues q) (fun w => g w x) 0 = true := rfl
    rw [eval_batchOrCircuit_iff, occupied, decide_eq_true_iff]
    simp only [hsk, hqk, hsv, and_true]
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨(eS.symm q).1, (eS.symm q).2, hq⟩
    · rintro ⟨m, c', hm⟩
      exact ⟨eS (m, c'), by simpa only [Equiv.symm_apply_apply] using hm⟩
  · refine (size_batchOrCircuit_le sourceKeys sourceValues queryKeys).trans (le_of_eq ?_)
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc]

/-- Stage 3: for each menu entry, duplicate flags among its candidates. Padding records carry a
true tag bit, so they never repeat a candidate. -/
private theorem synthesis_duplicate
    (hcand : (Set.range fun q : Fin r × Fin (arity p) × Fin s × Fin (ℓ * b) =>
      fun x => candidate hk bits scalar menu x q.1 q.2.1 q.2.2.1 q.2.2.2) ⊆ src) :
    Synthesis interpretation src
      (Set.range fun q : Fin r × Fin (arity p) × Fin s =>
        fun x => duplicate hk bits scalar menu x q.1 q.2.1 q.2.2)
      (r * ((duplicateFlagsCircuit (id : Fin (ℓ * b + 1) → Fin (ℓ * b + 1))
        (Nat.clog 2 (arity p * s))).size + 2)) := by
  classical
  let d := Nat.clog 2 (arity p * s)
  let pad := arity d - arity p * s
  have hpad : arity p * s + pad = arity d := by
    have : arity p * s ≤ arity d := by
      rw [arity_eq_two_pow d]
      exact Nat.le_pow_clog (by decide : 1 < 2) _
    lia
  let ι := Fin (arity p) × Fin s × Fin (ℓ * b)
  let eι := Fintype.equivFin ι
  let slot : Fin (arity p) × Fin s → Fin (arity d) :=
    fun ic => Fin.cast hpad (Fin.castAdd pad (finProdFinEquiv ic))
  let ρ : Fin (arity d * (ℓ * b + 1)) → Fin (Fintype.card ι) ⊕ Bool := fun q =>
    Fin.addCases (motive := fun _ => Fin (Fintype.card ι) ⊕ Bool)
      (fun j => Fin.cases (.inr false) (fun β => .inl (eι ((finProdFinEquiv.symm j).1,
        (finProdFinEquiv.symm j).2, β))) (finProdFinEquiv.symm q).2)
      (fun _ => Fin.cases (.inr true) (fun _ => .inr false) (finProdFinEquiv.symm q).2)
      (Fin.cast hpad.symm (finProdFinEquiv.symm q).1)
  let circuit := (duplicateFlagsCircuit (id : Fin (ℓ * b + 1) → Fin (ℓ * b + 1)) d).comp
    (substituteCircuit ρ)
  have hentry (e : Fin r) : Synthesis interpretation src
      (Set.range fun q : Fin (arity p) × Fin s =>
        fun x => duplicate hk bits scalar menu x e q.1 q.2)
      ((duplicateFlagsCircuit (id : Fin (ℓ * b + 1) → Fin (ℓ * b + 1)) d).size + 2) := by
    let g : Fin (Fintype.card ι) → BooleanFunction (2 ^ D * width D (ℓ * b) s) := fun w x =>
      candidate hk bits scalar menu x e (eι.symm w).1 (eι.symm w).2.1 (eι.symm w).2.2
    refine (Synthesis.circuit circuit g fun w => hcand ⟨(e, eι.symm w), rfl⟩).mono
      Set.Subset.rfl ?_ (by simp only [circuit, Circuit.size_comp, size_substituteCircuit]; lia)
    rintro _ ⟨⟨i, c⟩, rfl⟩
    refine ⟨slot (i, c), funext fun x => Bool.eq_iff_iff.mpr ?_⟩
    let y : BitString (Fintype.card ι) := fun w => g w x
    -- The records seen by the duplicate circuit.
    let row := directProductInput (substitute ρ y)
    have hreal (i' : Fin (arity p)) (c' : Fin s) :
        row (slot (i', c')) = Fin.cons false (candidate hk bits scalar menu x e i' c') := by
      funext f
      simp only [row, directProductInput, substitute, ρ, slot, Equiv.symm_apply_apply,
        Fin.cast_cast, Fin.cast_eq_self, Fin.addCases_left]
      refine Fin.cases ?_ (fun β => ?_) f
      · simp only [Fin.cases_zero, Fin.cons_zero, Sum.elim_inr, id]
      · simp only [Fin.cases_succ, Fin.cons_succ, Sum.elim_inl, y, g, Equiv.symm_apply_apply]
    have hpadRow (j : Fin pad) : row (Fin.cast hpad (Fin.natAdd _ j)) 0 = true := by
      simp only [row, directProductInput, substitute, ρ, Equiv.symm_apply_apply,
        Fin.cast_cast, Fin.cast_eq_self, Fin.addCases_right, Fin.cases_zero, Sum.elim_inr, id]
    simp only [circuit, Circuit.eval_comp, eval_substituteCircuit]
    rw [eval_duplicateFlagsCircuit_iff, duplicate, decide_eq_true_iff]
    simp only [Function.comp_id]
    change (∃ j, j ≠ slot (i, c) ∧ row j = row (slot (i, c))) ↔ _
    constructor
    · rintro ⟨j, hne, heq⟩
      obtain ⟨j, rfl⟩ := (finCongr hpad).surjective j
      induction j using Fin.addCases with
      | left j =>
        obtain ⟨⟨i', c'⟩, rfl⟩ := finProdFinEquiv.surjective j
        change slot (i', c') ≠ slot (i, c) at hne
        change row (slot (i', c')) = row (slot (i, c)) at heq
        rw [hreal, hreal] at heq
        exact ⟨i', c', fun h => hne (congrArg slot h), funext fun β => congrFun heq β.succ⟩
      | right j =>
        have := congrFun heq 0
        rw [show (finCongr hpad) (Fin.natAdd _ j) = Fin.cast hpad (Fin.natAdd _ j) from rfl,
          hpadRow, hreal] at this
        exact absurd this (by simp)
    · rintro ⟨i', c', hne, heq⟩
      refine ⟨slot (i', c'), fun h => hne ?_, by rw [hreal, hreal, heq]⟩
      exact finProdFinEquiv.injective (Fin.castAdd_injective _ _ (Fin.cast_injective hpad h))
  refine (Synthesis.iUnion _ _ hentry).mono Set.Subset.rfl ?_ (le_of_eq ?_)
  · rintro _ ⟨⟨e, i, c⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨e, ⟨(i, c), rfl⟩⟩
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rfl

/-- Stage 4: a request is clean when no candidate is occupied or a duplicate. -/
private theorem synthesis_clean
    (hocc : (Set.range fun q : Fin r × Fin (arity p) × Fin s =>
      fun x => occupied hk bits scalar menu x q.1 q.2.1 q.2.2) ⊆ src)
    (hdup : (Set.range fun q : Fin r × Fin (arity p) × Fin s =>
      fun x => duplicate hk bits scalar menu x q.1 q.2.1 q.2.2) ⊆ src) :
    Synthesis interpretation src
      (Set.range fun q : Fin r × Fin (arity p) => fun x => clean hk bits scalar menu x q.1 q.2)
      (r * arity p * (2 * s + 2)) := by
  refine (Synthesis.family _ (fun _ => 2 * s + 2) fun q => ?_).mono Set.Subset.rfl
    Set.Subset.rfl (le_of_eq ?_)
  · obtain ⟨e, i⟩ := q
    have h := (Synthesis.exists_mem (s := src) univ
      (fun c x => occupied hk bits scalar menu x e i c || duplicate hk bits scalar menu x e i c)
      (fun _ => 1) fun c _ => (Synthesis.of_mem (hocc ⟨(e, i, c), rfl⟩)).or
        (Synthesis.of_mem (hdup ⟨(e, i, c), rfl⟩))).not
    refine (Synthesis.congr_iff h fun x => ?_).mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)
    · rw [clean, decide_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not]
      simp only [mem_univ, true_and, Bool.or_eq_true, not_exists, not_or, Bool.not_eq_true]
    · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      lia
  · simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]

/-- Stage 5: an entry succeeds when its sorted clean flags are true at position
`⌈2 ^ p / 2⌉ - 1`. -/
private theorem synthesis_success
    (hclean : (Set.range fun q : Fin r × Fin (arity p) =>
      fun x => clean hk bits scalar menu x q.1 q.2) ⊆ src) :
    Synthesis interpretation src
      (Set.range fun e : Fin r => fun x => success hk bits scalar menu x e)
      (r * (bitonicSortCircuit (id : Fin 1 → Fin 1) p false).size) := by
  have hpos : 0 < arity p := by
    rw [arity_eq_two_pow]
    exact Nat.two_pow_pos p
  let j₀ : Fin (arity p) := ⟨(arity p + 1) / 2 - 1, by lia⟩
  have hentry (e : Fin r) : Synthesis interpretation src
      (Set.range fun _ : Unit => fun x => success hk bits scalar menu x e)
      (bitonicSortCircuit (id : Fin 1 → Fin 1) p false).size := by
    let g : Fin (arity p * 1) → BooleanFunction (2 ^ D * width D (ℓ * b) s) :=
      fun q x => clean hk bits scalar menu x e (finProdFinEquiv.symm q).1
    refine (Synthesis.circuit (bitonicSortCircuit id p false) g
      fun q => hclean ⟨(e, _), rfl⟩).mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨-, rfl⟩
    refine ⟨finProdFinEquiv (j₀, 0), funext fun x => ?_⟩
    have h := congrFun (congrFun
      (eval_bitonicSortCircuit (id : Fin 1 → Fin 1) p false (fun q => g q x)) j₀) 0
    have hin : directProductInput (fun q => g q x) =
        fun i _ => clean hk bits scalar menu x e i := by
      funext i f
      simp only [directProductInput, g, Equiv.symm_apply_apply]
    rw [hin] at h
    have hflag := sort_flag_eq_true_iff (fun r : BitString 1 => r ∘ id) p
      (fun i _ => clean hk bits scalar menu x e i) j₀
    change (bitonicSortCircuit id p false).eval interpretation (fun q => g q x)
      (finProdFinEquiv (j₀, 0)) = success hk bits scalar menu x e
    rw [show (bitonicSortCircuit id p false).eval interpretation (fun q => g q x)
      (finProdFinEquiv (j₀, 0)) = _ from h, Bool.eq_iff_iff, success, decide_eq_true_iff]
    refine hflag.trans ?_
    simp only [Function.comp_id, j₀]
    lia
  refine (Synthesis.iUnion _ _ hentry).mono Set.Subset.rfl ?_ (le_of_eq ?_)
  · rintro _ ⟨e, rfl⟩
    exact Set.mem_iUnion.mpr ⟨e, ⟨(), rfl⟩⟩
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- Stage 6: the first successful entry, from shared prefix disjunctions. -/
private theorem synthesis_chosen
    (hsucc : (Set.range fun e : Fin r => fun x => success hk bits scalar menu x e) ⊆ src) :
    Synthesis interpretation src
      (Set.range fun e : Fin r => fun x => chosen hk bits scalar menu x e) (3 * r) := by
  let F : Fin r → BooleanFunction (2 ^ D * width D (ℓ * b) s) :=
    fun e x => success hk bits scalar menu x e
  have hpre := Synthesis.prefixOr F fun e => hsucc ⟨e, rfl⟩
  refine (hpre.trans (Synthesis.family _ (fun _ => 2) fun e => ?_)).mono Set.Subset.rfl
    Set.Subset.rfl (le_of_eq ?_)
  · have hF : F e ∈ src ∪ Set.range fun e : Fin r => Boolean.prefixOr F e.val :=
      Or.inl (hsucc ⟨e, rfl⟩)
    rcases he : e.val with _ | j
    · have : (fun x => chosen hk bits scalar menu x e) = F e := by
        funext x
        rw [Bool.eq_iff_iff, chosen, decide_eq_true_iff]
        refine ⟨And.left, fun h => ⟨h, fun e' he' => ?_⟩⟩
        have := Fin.lt_def.mp he'
        lia
      rw [this]
      exact (Synthesis.of_mem hF).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le 2)
    · have hj : j < r := by have := e.isLt; lia
      have hP : Boolean.prefixOr F j ∈
          src ∪ Set.range fun e : Fin r => Boolean.prefixOr F e.val :=
        Or.inr ⟨⟨j, hj⟩, rfl⟩
      have : (fun x => chosen hk bits scalar menu x e) =
          fun x => F e x && !Boolean.prefixOr F j x := by
        funext x
        rw [Bool.eq_iff_iff, chosen, decide_eq_true_iff, Bool.and_eq_true, Bool.not_eq_true',
          Boolean.prefixOr, decide_eq_false_iff_not]
        simp only [not_exists, not_and, Bool.not_eq_true, F]
        refine and_congr Iff.rfl ⟨fun h e' he' => h e' (Fin.lt_def.mpr (by lia)),
          fun h e' he' => h e' (by have := Fin.lt_def.mp he'; lia)⟩
      rw [this]
      exact (Synthesis.of_mem hF).and (Synthesis.of_mem hP).not
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    lia

/-- Stage 7: the clean flag of each request for the chosen entry. -/
private theorem synthesis_flag
    (hchosen : (Set.range fun e : Fin r => fun x => chosen hk bits scalar menu x e) ⊆ src)
    (hclean : (Set.range fun q : Fin r × Fin (arity p) =>
      fun x => clean hk bits scalar menu x q.1 q.2) ⊆ src) :
    Synthesis interpretation src
      (Set.range fun i : Fin (arity p) => fun x => flag hk bits scalar menu x i)
      (arity p * (2 * r + 1)) := by
  refine (Synthesis.family _ (fun _ => 2 * r + 1) fun i => ?_).mono Set.Subset.rfl
    Set.Subset.rfl (le_of_eq ?_)
  · have h := Synthesis.exists_mem (s := src) univ
      (fun e x => chosen hk bits scalar menu x e && clean hk bits scalar menu x e i)
      (fun _ => 1) fun e _ => (Synthesis.of_mem (hchosen ⟨e, rfl⟩)).and
        (Synthesis.of_mem (hclean ⟨(e, i), rfl⟩))
    refine (Synthesis.congr_iff h fun x => ?_).mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)
    · simp only [flag, decide_eq_true_iff, mem_univ, true_and, Bool.and_eq_true]
    · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      lia
  · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- Stage 7: the candidate line of each request for the chosen entry. -/
private theorem synthesis_newLine
    (hchosen : (Set.range fun e : Fin r => fun x => chosen hk bits scalar menu x e) ⊆ src)
    (hcand : (Set.range fun q : Fin r × Fin (arity p) × Fin s × Fin (ℓ * b) =>
      fun x => candidate hk bits scalar menu x q.1 q.2.1 q.2.2.1 q.2.2.2) ⊆ src) :
    Synthesis interpretation src
      (Set.range fun q : Fin (arity p) × Fin s × Fin (ℓ * b) =>
        fun x => newLine hk bits scalar menu x q.1 q.2.1 q.2.2)
      (arity p * s * (ℓ * b) * (2 * r + 1)) := by
  refine (Synthesis.family _ (fun _ => 2 * r + 1) fun q => ?_).mono Set.Subset.rfl
    Set.Subset.rfl (le_of_eq ?_)
  · obtain ⟨i, c, β⟩ := q
    have h := Synthesis.exists_mem (s := src) univ
      (fun e x => chosen hk bits scalar menu x e && candidate hk bits scalar menu x e i c β)
      (fun _ => 1) fun e _ => (Synthesis.of_mem (hchosen ⟨e, rfl⟩)).and
        (Synthesis.of_mem (hcand ⟨(e, i, c, β), rfl⟩))
    refine (Synthesis.congr_iff h fun x => ?_).mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)
    · simp only [newLine, decide_eq_true_iff, mem_univ, true_and, Bool.and_eq_true]
    · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      lia
  · simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
      Nat.mul_assoc]

/-- Stage 8: the enriched pending records, sorted with clean records first. -/
private theorem synthesis_sortedPending (hin : inputs _ ⊆ src)
    (hflag : (Set.range fun i : Fin (arity p) => fun x => flag hk bits scalar menu x i) ⊆ src)
    (hnew : (Set.range fun q : Fin (arity p) × Fin s × Fin (ℓ * b) =>
      fun x => newLine hk bits scalar menu x q.1 q.2.1 q.2.2) ⊆ src) :
    Synthesis interpretation src
      (Set.range fun q : Fin (arity p) × Fin (1 + width D (ℓ * b) s) =>
        fun x => sortedPending hk bits scalar menu x q.1 q.2)
      (bitonicSortCircuit (flagKey (D := D) (ℓ := ℓ) (b := b) (s := s)) p false).size := by
  let g : Fin (arity p * (1 + width D (ℓ * b) s)) →
      BooleanFunction (2 ^ D * width D (ℓ * b) s) := fun w x =>
    enriched hk bits scalar menu x (finProdFinEquiv.symm w).1 (finProdFinEquiv.symm w).2
  have hg (w) : g w ∈ src := by
    obtain ⟨⟨i, f⟩, rfl⟩ := finProdFinEquiv.surjective w
    simp only [g, Equiv.symm_apply_apply]
    induction f using Fin.addCases with
    | left f =>
      simp only [enriched, Fin.append_left]
      exact hflag ⟨i, rfl⟩
    | right f =>
      induction f using Fin.addCases with
      | left j =>
        simp only [enriched, Fin.append_right, Fin.append_left, label]
        exact hin ⟨_, rfl⟩
      | right f =>
        induction f using Fin.addCases with
        | left β =>
          simp only [enriched, Fin.append_right, Fin.append_left, target]
          exact hin ⟨_, rfl⟩
        | right q =>
          simp only [enriched, Fin.append_right]
          exact hnew ⟨(i, (finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2), rfl⟩
  refine (Synthesis.circuit (bitonicSortCircuit flagKey p false) g hg).mono Set.Subset.rfl ?_
    le_rfl
  rintro _ ⟨⟨j, f⟩, rfl⟩
  refine ⟨finProdFinEquiv (j, f), funext fun x => ?_⟩
  have h := congrFun (congrFun
    (eval_bitonicSortCircuit flagKey p false (fun w => g w x)) j) f
  have hin : directProductInput (fun w => g w x) = enriched hk bits scalar menu x := by
    funext i f
    simp only [directProductInput, g, Equiv.symm_apply_apply]
  rw [hin] at h
  exact h

/-- The phase output is available once the sorted pending records are. -/
theorem next_mem (hin : inputs _ ⊆ src)
    (hsort : (Set.range fun q : Fin (arity p) × Fin (1 + width D (ℓ * b) s) =>
      fun x => sortedPending hk bits scalar menu x q.1 q.2) ⊆ src)
    (q : Fin (2 ^ D * width D (ℓ * b) s)) : (fun x => next hk bits scalar menu x q) ∈ src := by
  obtain ⟨⟨m, f⟩, rfl⟩ := finProdFinEquiv.surjective q
  rcases accepted_or_pending (hk := hk) m with ⟨m', rfl⟩ | ⟨j, rfl⟩
  · simp only [next_accepted]
    exact hin ⟨_, rfl⟩
  · simp only [next_pending]
    exact hsort ⟨(j, Fin.natAdd 1 f), rfl⟩

/-- The gate budget of one phase with `2 ^ p` pending and `a` accepted records and a menu of `r`
entries: the sum of the eight stage budgets. It counts every gate, including constants. -/
def phaseCost (D L s p a r : ℕ) : ℕ :=
  r * arity p * s * L +
  48 * (r * arity p * s + a * s + 1) * (Nat.clog 2 (r * arity p * s + a * s) + 1) ^ 2 *
    (L + 1 + 1) +
  r * ((duplicateFlagsCircuit (id : Fin (L + 1) → Fin (L + 1))
    (Nat.clog 2 (arity p * s))).size + 2) +
  r * arity p * (2 * s + 2) +
  r * (bitonicSortCircuit (id : Fin 1 → Fin 1) p false).size +
  3 * r +
  arity p * (2 * r + 1) +
  arity p * s * L * (2 * r + 1) +
  (bitonicSortCircuit (Fin.castAdd (width D L s) : Fin 1 → Fin (1 + width D L s)) p false).size

/-- **One scheduler phase.** Some circuit computes `next` exactly, on every input, within
`phaseCost` gates; the size counts every gate, including constants. -/
theorem exists_next_circuit :
    ∃ c : Circuit signature (2 ^ D * width D (ℓ * b) s) (2 ^ D * width D (ℓ * b) s),
      c.Computes interpretation (next hk bits scalar menu) ∧
        c.size ≤ phaseCost D (ℓ * b) s p a r := by
  have h1 := synthesis_candidate hk bits scalar menu
    (src := inputs (2 ^ D * width D (ℓ * b) s)) Set.Subset.rfl
  have h2 := h1.comp (synthesis_occupied hk bits scalar menu Set.subset_union_left
    Set.subset_union_right)
  have h3 := h2.comp (synthesis_duplicate hk bits scalar menu
    (by intro _ h; simp only [Set.mem_union]; tauto))
  have h4 := h3.comp (synthesis_clean hk bits scalar menu
    (by intro _ h; simp only [Set.mem_union]; tauto)
    (by intro _ h; simp only [Set.mem_union]; tauto))
  have h5 := h4.comp (synthesis_success hk bits scalar menu
    (by intro _ h; simp only [Set.mem_union]; tauto))
  have h6 := h5.comp (synthesis_chosen hk bits scalar menu
    (by intro _ h; simp only [Set.mem_union]; tauto))
  have h7 := h6.comp (synthesis_flag hk bits scalar menu
    (by intro _ h; simp only [Set.mem_union]; tauto)
    (by intro _ h; simp only [Set.mem_union]; tauto))
  have h8 := h7.comp (synthesis_newLine hk bits scalar menu
    (by intro _ h; simp only [Set.mem_union]; tauto)
    (by intro _ h; simp only [Set.mem_union]; tauto))
  have h9 := h8.comp (synthesis_sortedPending hk bits scalar menu
    (by intro _ h; simp only [Set.mem_union]; tauto)
    (by intro _ h; simp only [Set.mem_union]; tauto)
    (by intro _ h; simp only [Set.mem_union]; tauto))
  have h10 := h9.trans (Synthesis.of_subset (t := Set.range fun q x =>
    next hk bits scalar menu x q) (by
      rintro _ ⟨q, rfl⟩
      exact next_mem hk bits scalar menu (fun _ h => Or.inl h)
        (by intro _ h; simp only [Set.mem_union]; tauto) q))
  obtain ⟨c, hc, hsize⟩ := Synthesis.exists_circuit_outputs h10
  exact ⟨c, hc, hsize.trans (le_of_eq (by rw [Nat.add_zero]; rfl))⟩

end Cslib.Circuits.Boolean.MassProduction.Scheduler
