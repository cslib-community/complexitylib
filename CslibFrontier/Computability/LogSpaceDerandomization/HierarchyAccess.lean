/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.SignedResidualBins

/-!
# Stochastic calls in the global hierarchy order

These are the actual normalized-bin calls of [OpenAI2026LogSpace, Sections 7.1–7.2,
(7.1)–(7.3)], revision `7ef5c0cc`. Calls specify whole functions, never a retained source
vertex or endpoint. The negative correction uses its own scale-`f` endpoint rank channel;
the product-right child resets the entire source tuple. Copy traversal prepends both fixed
symbols before inherited suffixes and calls a routed residual bin, rather than expanding a
second copy hierarchy. Preparation and normalized-bin constructors belong to `HierarchyTask`.

The evaluator substitutes arbitrary completed child functions before products or averaging.
It has no supplied rank, mean or error certificate. Zero correction iterations read zero;
positive iterations read their actual earlier normalized constructor with a finite index.
The scalar parameters, including normalization margins, retain the contracts of the existing
bounded recipes. These are noncomputable finite functions, with no native complexity claim.

Finite-accuracy pre-incoming classes/caps and port/address enumeration are separate open work.
A complete mean-prefix theorem still needs estimated direct/product/negative, routed-copy,
second-channel, detector/maximum and reward comparisons, including source release, the full
cutoff/gate root and complement regularity ladder, and summable omitted-bin payments. The
true-atom means alone do not provide those comparisons. Paired raw differences, full-coordinate
walks and summed noise, compression, statistical-budget induction and native workspace/class
equality remain open. No selected abstract or catalogue claim changes.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams.HierarchyTask

open CorrectionRowTask

/-- Raw constructor whose stochastic first channel is assembled from bins. -/
inductive RawTask (k : ℕ) where
  | pilotInput (i : Fin k)
  | input (i : Fin k)
  | residual
  deriving DecidableEq

/-- The existing global constructor served by a raw sample. -/
@[expose] def RawTask.task {k : ℕ} (l : ℕ) : RawTask k → HierarchyTask k
  | .pilotInput i => .row l (.pilotInput i)
  | .input i => .row l (.input i)
  | .residual => .residual l

/-- A zero correction is a literal zero constructor; a positive correction reads the
normalized child of its preceding finite iteration. -/
@[expose] def correctionAtomTask {k : ℕ} (l : ℕ) (pilot : Bool)
    (i : Fin (k + 1)) : HierarchyTask k :=
  Fin.cases (.row l (if pilot then .pilotCorrection 0 else .correction 0))
    (fun j => .row l (if pilot then .pilotNormalized j else .normalized j)) i

/-- The final positive correction dispatches to the last normalized child, whose
zero-based index is the preceding iterate. This structural index is not a precision. -/
@[simp] theorem correctionAtomTask_last_succ (h l : ℕ) :
    correctionAtomTask (k := h + 1) l false (Fin.last (h + 1)) =
      .row l (.normalized (Fin.last h)) := by
  unfold correctionAtomTask
  rw [show Fin.last (h + 1) = (Fin.last h).succ from rfl, Fin.cases_succ]
  rfl

/-- Positive structural size selects its own last normalized index. -/
theorem correctionAtomTask_last {q : ℕ} (hq : 0 < q) (l : ℕ) :
    correctionAtomTask (k := q) l false (Fin.last q) =
      .row l (.normalized ⟨q - 1, Nat.sub_lt hq (by decide)⟩) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  exact correctionAtomTask_last_succ h l

/-- Four distinct whole-function requests; the negative term is present only for residuals. -/
structure RawRequests (k : ℕ) (Role Symbol : Type*) where
  /-- Direct normalized base bin. -/
  direct : Request k Role Symbol
  /-- Left normalized correction on the midpoint role. -/
  left : Request k Role Symbol
  /-- Right normalized base bin with midpoint source reset. -/
  right : Request k Role Symbol
  /-- Negative endpoint correction on its own scale-f rank channel. -/
  negative : Option (Request k Role Symbol)

/-- All called functions, retaining distinct requests even when their constructors agree. -/
@[expose] def RawRequests.calls {k : ℕ} {Role Symbol : Type*}
    (R : RawRequests k Role Symbol) : List (Request k Role Symbol) :=
  [R.direct, R.left, R.right] ++ R.negative.toList

/-- Bin and usage are different endpoint channels: their rates are `b` and `min(a,b)`.
The negative channel has rank rate `f`, independently of `b`. -/
@[expose] def rawRequests {k : ℕ} {Role Symbol : Type*} (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ) :
    RawRequests k Role Symbol :=
  let iter := match t with
    | .pilotInput i | .input i => i.castSucc
    | .residual => Fin.last k
  let correction := correctionAtomTask l (match t with | .pilotInput _ => true | _ => false) iter
  { direct := ⟨.baseNormalized l bin, source, { endpoint with rate := b },
      { endpoint with rate := min endpoint.rate b }⟩
    left := ⟨correction, source, midpoint, midpoint⟩
    right := ⟨.baseNormalized l bin, midpoint, { endpoint with rate := b },
      { endpoint with rate := min endpoint.rate b }⟩
    negative := match t with
      | .residual => some ⟨correction, source, { endpoint with rate := midpoint.rate },
          { endpoint with rate := min endpoint.rate midpoint.rate }⟩
      | _ => none }

/-- The normalized correction really precedes its target raw input, including iteration zero. -/
theorem correctionAtomTask_rank_lt {k : ℕ} (l : ℕ) (t : RawTask k) :
    (correctionAtomTask l (match t with | .pilotInput _ => true | _ => false)
      (match t with | .pilotInput i | .input i => i.castSucc | .residual => Fin.last k)).rank <
        (t.task l).rank := by
  cases t with
  | pilotInput i | input i =>
    cases k with
    | zero => exact Fin.elim0 i
    | succ k => refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [correctionAtomTask, RawTask.task, Fin.castSucc_zero, Fin.cases_zero,
        Fin.castSucc_succ, Fin.cases_succ, Bool.false_eq_true, ↓reduceIte, rank,
        CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank, Fin.val_zero,
        Fin.val_succ, Fin.val_castSucc] <;> omega
  | residual =>
    have h := BoundedRowTask.rank_le (k := k)
    unfold correctionAtomTask
    generalize hi : Fin.last k = i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero, Bool.false_eq_true, ↓reduceIte, RawTask.task, rank,
        CorrectionRowTask.rank, Fin.val_zero]
      omega
    · have := h (BoundedRowTask.normalized j)
      simp only [Fin.cases_succ, Bool.false_eq_true, ↓reduceIte, RawTask.task, rank]
      omega

/-- Every stochastic first-channel request decreases the same global constructor rank. -/
theorem rawRequests_rank_lt {k : ℕ} {Role Symbol : Type*} (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ)
    (r : Request k Role Symbol) (hr : r ∈ (rawRequests l bin t source midpoint endpoint b).calls) :
    r.task.rank < (t.task l).rank := by
  have hc := correctionAtomTask_rank_lt l t
  have hb : (baseNormalized (k := k) l bin).rank < (t.task l).rank := by
    cases t with
    | pilotInput i => exact rank_lt_of_binDependency (.basePilotInput l bin i)
    | input i => exact rank_lt_of_binDependency (.baseInput l bin i)
    | residual =>
      simp only [rank, RawTask.task]
      omega
  cases t <;>
    simp only [rawRequests, RawRequests.calls, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, Option.toList_none, Option.toList_some] at hr <;>
    first
    | (rcases hr with (rfl | rfl | rfl) | rfl <;> first | exact hb | exact hc)
    | (rcases hr with rfl | rfl | rfl <;> first | exact hb | exact hc)

/-- Actual copy access uses the earlier routed normalized residual and broad-source weight.
Routing is part of the bin's scalar recipe, and is evaluated before averaging. -/
@[expose] def routedCopyRequests {k : ℕ} {Role Symbol : Type*} (l bin : ℕ)
    (source endpoint : Channel Role (List Symbol)) (f b : ℝ) (i j : Symbol) :
    List (Request k Role Symbol) :=
  [⟨.row l .weights, { source.throughCopy i with rate := f },
      endpoint.throughCopy j, endpoint.throughCopy j⟩,
   ⟨.residualNormalized l bin, source.throughCopy i,
      { endpoint.throughCopy j with rate := b },
      { endpoint.throughCopy j with rate := min endpoint.rate b }⟩]

/-- Copy access follows residual normalization and stays before the next stage's base. -/
theorem routedCopyRequests_rank_lt {k : ℕ} {Role Symbol : Type*} (l bin : ℕ)
    (source endpoint : Channel Role (List Symbol)) (f b : ℝ) (i j : Symbol)
    (r : Request k Role Symbol) (hr : r ∈ routedCopyRequests l bin source endpoint f b i j) :
    r.task.rank < (nextMatrix (k := k) l).rank := by
  simp only [routedCopyRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact row_rank_lt_nextMatrix _ _
  · exact rank_lt_of_binDependency (.copy l bin)

section Evaluation

variable {k : ℕ} {Role Symbol V Ω : Type*} [Fintype V] [Fintype Ω]
  (channels : Role → ℝ → List Symbol → Ω → V → Prop)
  [∀ role rate suffix σ v, Decidable (channels role rate suffix σ v)]

/-- Endpoint importance uses the parent's conditioning slice and the child's actual usage. -/
@[expose] noncomputable def usageRatio (endpoint : Channel Role (List Symbol))
    (r : Request k Role Symbol) (y : V) : ℝ :=
  (dens {σ | endpoint.retains channels σ y} : ℝ) /
    dens {σ | r.usage.retains channels σ y}

/-- Positive direct and shared-midpoint product contribution of one raw bin. Keeping
this separate lets bin assembly include the special negative correction only once. -/
@[expose] noncomputable def rawPositiveSample (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ)
    (child : Request k Role Symbol → Matrix V V ℝ) (x y : V) : ℝ :=
  let R := rawRequests l bin t source midpoint endpoint b
  b * usageRatio channels endpoint R.direct y * child R.direct x y +
    b * usageRatio channels endpoint R.right y *
      (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ)) *
      ∑ z, child R.left x z * child R.right z y

/-- Special endpoint correction at scale f. It is absent for non-residual raw tasks;
residual bin assembly subtracts this contribution once, separately from positive bins. -/
@[expose] noncomputable def rawNegativeSample (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ)
    (child : Request k Role Symbol → Matrix V V ℝ) (x y : V) : ℝ :=
  match (rawRequests l bin t source midpoint endpoint b).negative with
  | none => 0
  | some r => midpoint.rate * usageRatio channels endpoint r y * child r x y

/-- Equations (7.1)–(7.2), with a distinct special negative term for residuals.
The child oracle returns arbitrary completed whole matrices on this draw. Midpoints are
function arguments and not parameters stored by the right child. -/
@[expose] noncomputable def rawSample (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ)
    (child : Request k Role Symbol → Matrix V V ℝ) (x y : V) : ℝ :=
  rawPositiveSample channels l bin t source midpoint endpoint b child x y -
    rawNegativeSample channels l bin t source midpoint endpoint b child x y

/-- Equation (7.3) on a fixed copy-symbol part. The routing fraction is already included
in the supplied residual bin, rather than applied to its conditional mean. -/
@[expose] noncomputable def routedCopySample (l bin : ℕ)
    (source endpoint : Channel Role (List Symbol)) (b : ℝ) (i j : Symbol)
    (weight : V → ℝ) (child : Request k Role Symbol → Matrix V V ℝ) (x y : V) : ℝ :=
  let r : Request k Role Symbol := ⟨.residualNormalized l bin, source.throughCopy i,
    { endpoint.throughCopy j with rate := b },
    { endpoint.throughCopy j with rate := min endpoint.rate b }⟩
  weight x * b * usageRatio channels (endpoint.throughCopy j) r y * child r x y

end Evaluation
end Matrix.HierarchyParams.HierarchyTask
