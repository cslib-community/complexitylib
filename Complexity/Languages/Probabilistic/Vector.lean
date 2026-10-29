/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Repeat

/-!
# Collecting runs in finite tuples and vectors

`OracleComp.pi` collects successive runs of a dependent family of oracle computations indexed by
`Fin m`, in index order, and `OracleComp.piRestrict` runs only the coordinates belonging to a
subset `I : Finset (Fin m)`. `OracleComp.replicateFin` is the homogeneous specialization of
`OracleComp.pi` to a single repeated program. Listing its coordinates gives the existing
list-valued repetition program `OracleComp.replicate`; closed `ProbComp` runs draw independent
values with the product distribution `PMF.pi`.

## Main definitions

* `Cslib.OracleComp.pi`: collect successive runs of a dependent family over `Fin m`.
* `Cslib.OracleComp.piRestrict`: run only the coordinates in a subset `I : Finset (Fin m)`.
* `Cslib.OracleComp.replicateFin`: collect successive runs of one program in a length-indexed
  vector (`pi (fun _ => program)`).

## Main results

* `Cslib.OracleComp.replicateFin_eq_pi`: `replicateFin` is the constant-family specialization of
  `pi`.
* `Cslib.OracleComp.map_ofFn_replicateFin`: agreement with list-valued repetition.
* `Cslib.ProbComp.mem_support_pi_iff`, `Cslib.ProbComp.mem_support_replicateFin_iff`: support is
  coordinatewise, even for infinite types.
* `Cslib.ProbComp.eval_pi`, `Cslib.ProbComp.eval_replicateFin`: independent finite coordinates have
  the product law `PMF.pi`.
* `Cslib.ProbComp.eval_pi_map`, `Cslib.ProbComp.eval_replicateFin_map_coords`: coordinatewise maps
  commute with `pi` and `replicateFin`.
* `Cslib.ProbComp.eval_bind_restrict_pi`, `Cslib.ProbComp.eval_map_restrict_pi`: restricting
  `eval (pi programs)` to `I : Finset (Fin m)` runs only the programs in `I`.
* `Cslib.ProbComp.eval_replicateFin_map`: list-valued encodings preserve the joint law.
* `Cslib.ProbComp.eval_replicateFin_of_uniformList`: a flat fair-bit seed supplies every run.

## References

This is the finite-tuple interface to `OracleComp.replicate` and its product-distribution laws.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v

variable {Query : Type u} {spec : OracleSpec.{u, v} Query} {α : Type v}

/-- Collect successive runs of a dependent family of oracle computations over `Fin m`, in
execution order (`0, 1, …, m - 1`). -/
def pi : {m : ℕ} → {α : Fin m → Type v} →
    ((i : Fin m) → OracleComp spec (α i)) → OracleComp spec ((i : Fin m) → α i)
  | 0, _, _ => pure (fun i => i.elim0)
  | m + 1, _, programs =>
    programs 0 >>= fun first => Fin.cons first <$> pi (fun i : Fin m => programs i.succ)

@[simp] theorem pi_zero {α : Fin 0 → Type v}
    (programs : (i : Fin 0) → OracleComp spec (α i)) :
    pi programs = pure (fun i => i.elim0) := rfl

theorem pi_succ {m : ℕ} {α : Fin (m + 1) → Type v}
    (programs : (i : Fin (m + 1)) → OracleComp spec (α i)) :
    pi programs =
      (programs 0 >>= fun first => Fin.cons first <$> pi (fun i : Fin m => programs i.succ)) := rfl

/-- Run the programs in a subset `I : Finset (Fin m)` in index order, returning a dependent tuple
on `I` without running programs outside `I`. -/
def piRestrict : {m : ℕ} → {α : Fin m → Type v} → (I : Finset (Fin m)) →
    ((i : I) → OracleComp spec (α i.1)) → OracleComp spec ((i : I) → α i.1)
  | 0, _, _, _ => pure (fun i => i.1.elim0)
  | m + 1, α, I, programs =>
    let I' : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.succ ∈ I)
    let restProg : (j : I') → OracleComp spec (α j.1.succ) :=
      fun j => programs ⟨j.1.succ, (Finset.mem_filter.mp j.2).2⟩
    if h0 : (0 : Fin (m + 1)) ∈ I then
      programs ⟨0, h0⟩ >>= fun first =>
        (fun (rest : (j : I') → α j.1.succ) (i : I) =>
          Fin.cases
            (motive := fun k => k ∈ I → α k)
            (fun _ => first)
            (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
            i.1 i.2) <$> piRestrict (α := fun k => α k.succ) I' restProg
    else
      (fun (rest : (j : I') → α j.1.succ) (i : I) =>
        Fin.cases
          (motive := fun k => k ∈ I → α k)
          (fun hk => (h0 hk).elim)
          (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
          i.1 i.2) <$> piRestrict (α := fun k => α k.succ) I' restProg

/-- Collect successive runs as a length-indexed vector, in execution order. -/
def replicateFin (count : ℕ) (program : OracleComp spec α) : OracleComp spec (Fin count → α) :=
  pi (fun _ : Fin count => program)

/-- `replicateFin` is the constant-family specialization of `pi`. -/
theorem replicateFin_eq_pi (count : ℕ) (program : OracleComp spec α) :
    replicateFin count program = pi (fun _ : Fin count => program) := rfl

@[simp] theorem replicateFin_zero (program : OracleComp spec α) :
    replicateFin 0 program = pure Fin.elim0 := rfl

theorem replicateFin_succ (count : ℕ) (program : OracleComp spec α) :
    replicateFin (count + 1) program =
      (program >>= fun first => Fin.cons first <$> replicateFin count program) := rfl

/-- Listing the coordinates gives exactly the existing repeated-run program. -/
@[simp] theorem map_ofFn_replicateFin (count : ℕ) (program : OracleComp spec α) :
    List.ofFn <$> replicateFin count program = replicate count program := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp [replicateFin_succ, replicate_succ, map_bind, Functor.map_map, List.ofFn_succ, ← ih]

end OracleComp

namespace ProbComp

open Probability

variable {α : Type}

/-- A tuple is in the support of `pi programs` if and only if each coordinate is in the support of
its coordinate program. -/
theorem mem_support_pi_iff {m : ℕ} {α : Fin m → Type}
    (programs : (i : Fin m) → ProbComp (α i)) (r : (i : Fin m) → α i) :
    r ∈ (eval (OracleComp.pi programs)).support ↔ ∀ i, r i ∈ (eval (programs i)).support := by
  induction m with
  | zero =>
    have hr : r = fun i => i.elim0 := funext fun i => i.elim0
    subst hr
    simp
  | succ m ih =>
    simp only [OracleComp.pi_succ, eval_bind, eval_map, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff, ih]
    constructor
    · rintro ⟨first, hfirst, rest, hrest, rfl⟩ i
      refine Fin.cases ?_ ?_ i
      · simpa using hfirst
      · intro j
        simpa using hrest j
    · intro h
      refine ⟨r 0, h 0, fun j => r j.succ, fun j => h j.succ, ?_⟩
      ext i
      exact Fin.cases rfl (fun _ => rfl) i

/-- Evaluating `pi programs` depends only on the distributions of the individual programs. -/
theorem eval_pi_congr {m : ℕ} {α : Fin m → Type}
    {p q : (i : Fin m) → ProbComp (α i)} (h : ∀ i, eval (p i) = eval (q i)) :
    eval (OracleComp.pi p) = eval (OracleComp.pi q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [OracleComp.pi_succ, eval_bind, eval_map, h 0, ih (fun i => h i.succ)]

/-- Mapping each coordinate program commutes with `pi`. -/
theorem eval_pi_map {m : ℕ} {α β : Fin m → Type}
    (programs : (i : Fin m) → ProbComp (α i)) (f : (i : Fin m) → α i → β i) :
    eval (OracleComp.pi (fun i => f i <$> programs i)) =
      (eval (OracleComp.pi programs)).map (fun r i => f i (r i)) := by
  induction m with
  | zero =>
    simp only [OracleComp.pi_zero, eval_pure, PMF.pure_map]
    congr 1
    ext i
    exact i.elim0
  | succ m ih =>
    simp only [OracleComp.pi_succ, eval_bind, eval_map, ih, PMF.bind_map, PMF.map_bind,
      PMF.map_comp]
    refine congrArg _ (funext fun first => congrArg (PMF.map · _) (funext fun rest => ?_))
    ext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Evaluating `pi` on pure coordinate programs yields `PMF.pure`. -/
@[simp] theorem eval_pi_pure {m : ℕ} {α : Fin m → Type} (x : (i : Fin m) → α i) :
    eval (OracleComp.pi (fun i => (pure (x i) : ProbComp (α i)))) = PMF.pure x := by
  induction m with
  | zero =>
    simp only [OracleComp.pi_zero, eval_pure]
    exact congrArg PMF.pure (funext fun i => i.elim0)
  | succ m ih =>
    simp only [OracleComp.pi_succ, eval_bind, eval_map, eval_pure,
      ih (fun i => x i.succ), PMF.pure_bind, PMF.pure_map]
    exact congrArg PMF.pure (funext fun i => Fin.cases rfl (fun _ => rfl) i)

/-- Coordinatewise monadic bind distributes over `eval (OracleComp.pi ...)`. -/
theorem eval_pi_bind {m : ℕ} {α β : Fin m → Type}
    (p : (i : Fin m) → ProbComp (α i)) (q : (i : Fin m) → α i → ProbComp (β i)) :
    eval (OracleComp.pi (fun i => p i >>= q i)) =
      (eval (OracleComp.pi p)).bind fun a =>
        eval (OracleComp.pi (fun i => q i (a i))) := by
  induction m with
  | zero =>
    simp only [OracleComp.pi_zero, eval_pure, PMF.pure_bind]
  | succ m ih =>
    simp only [OracleComp.pi_succ, eval_bind, eval_map, ih,
      PMF.bind_bind, PMF.bind_map, PMF.map_bind]
    refine congrArg (eval (p 0)).bind (funext fun a0 => ?_)
    rw [PMF.bind_comm]
    refine congrArg (eval (OracleComp.pi fun i => p i.succ)).bind (funext fun a_rest => ?_)
    refine congrArg (eval (q 0 a0)).bind (funext fun b0 => ?_)
    rfl

/-- Pairing independent coordinate programs in `OracleComp.pi` is equivalent to binding two
independent `OracleComp.pi` runs. -/
theorem eval_pi_pair {m : ℕ} {α β : Fin m → Type}
    (p : (i : Fin m) → ProbComp (α i)) (q : (i : Fin m) → ProbComp (β i)) :
    eval (OracleComp.pi (fun i => do
      let a ← p i
      let b ← q i
      return (a, b))) =
      (eval (OracleComp.pi p)).bind fun a =>
        (eval (OracleComp.pi q)).map fun b i => (a i, b i) := by
  simp only [bind_pure_comp]
  rw [eval_pi_bind]
  refine congrArg (eval (OracleComp.pi p)).bind (funext fun a => ?_)
  exact eval_pi_map q (fun i b => (a i, b))

/-- Swapping `Fin m` and `Fin k` in a nested `OracleComp.pi` preserves the evaluated `PMF`. -/
theorem eval_pi_comm {m k : ℕ} {α : Fin m → Fin k → Type}
    (p : (i : Fin m) → (s : Fin k) → ProbComp (α i s)) :
    eval (OracleComp.pi (fun i => OracleComp.pi (fun s => p i s))) =
      (eval (OracleComp.pi (fun s => OracleComp.pi (fun i => p i s)))).map
        (fun f i s => f s i) := by
  induction k with
  | zero =>
    simp only [OracleComp.pi_zero, eval_pi_pure, eval_pure, PMF.pure_map]
    exact congrArg PMF.pure (funext fun _ => funext fun s => s.elim0)
  | succ k ih =>
    simp only [OracleComp.pi_succ (m := k)]
    rw [eval_pi_bind]
    simp only [eval_pi_map, ih (fun i s => p i s.succ),
      eval_bind, eval_map, PMF.map_bind, PMF.map_comp]
    refine congrArg (eval (OracleComp.pi fun i => p i 0)).bind (funext fun first => ?_)
    refine congrArg (PMF.map · _) (funext fun rest => ?_)
    ext i s
    exact Fin.cases rfl (fun _ => rfl) s

/-- When each coordinate type is finite, `eval (pi programs)` is the independent product
distribution `PMF.pi`. -/
theorem eval_pi {m : ℕ} {α : Fin m → Type} [∀ i, Finite (α i)]
    (programs : (i : Fin m) → ProbComp (α i)) :
    eval (OracleComp.pi programs) = PMF.pi (fun i => eval (programs i)) := by
  induction m with
  | zero =>
    ext r
    have hr : r = fun i => i.elim0 := funext fun i => i.elim0
    subst hr
    simp
  | succ m ih =>
    rw [OracleComp.pi_succ, eval_bind]
    ext r
    simp only [eval_map, ih, PMF.bind_apply, PMF.map_apply, PMF.pi_apply]
    rw [Fin.prod_univ_succ, tsum_eq_single (r 0)]
    · congr 1
      rw [tsum_eq_single (fun i : Fin m => r i.succ)]
      · rw [ite_eq_left]
        ext i
        exact Fin.cases rfl (fun _ => rfl) i
      · intro b hb
        rw [ite_eq_right]
        intro hEq
        apply hb
        funext i
        simpa using (congrFun hEq (Fin.succ i)).symm
    · intro a ha
      simp only [mul_eq_zero, ENNReal.tsum_eq_zero]
      right
      intro b
      rw [ite_eq_right]
      intro hEq
      exact ha (by simpa using (congrFun hEq 0).symm)

/-- Binding `eval (pi programs)` to a continuation that depends only on `I.restrict r` is
equivalent to running only the programs in `I` via `piRestrict`. No finiteness assumption on `α`
is needed. -/
theorem eval_bind_restrict_pi {m : ℕ} {α : Fin m → Type} {β : Type}
    (I : Finset (Fin m)) (programs : (i : Fin m) → ProbComp (α i))
    (k : ((i : I) → α i.1) → PMF β) :
    (eval (OracleComp.pi programs)).bind (fun r => k (I.restrict r)) =
      (eval (OracleComp.piRestrict I (I.restrict programs))).bind k := by
  induction m with
  | zero =>
    simp only [OracleComp.pi_zero, OracleComp.piRestrict, eval_pure, PMF.pure_bind]
    exact congrArg k (funext fun i => i.1.elim0)
  | succ m ih =>
    let I' : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.succ ∈ I)
    simp only [OracleComp.pi_succ, OracleComp.piRestrict, eval_bind, eval_map, PMF.bind_bind,
      PMF.bind_map]
    by_cases h0 : (0 : Fin (m + 1)) ∈ I
    · simp only [dite_eq_left h0, eval_bind, eval_map, PMF.bind_bind, PMF.bind_map,
        Function.comp_def]
      refine congrArg _ (funext fun first => ?_)
      have hih := ih (α := fun j => α j.succ) I' (fun j => programs j.succ) (fun rest =>
        k (fun i =>
          Fin.cases (motive := fun idx => idx ∈ I → α idx)
            (fun _ => first)
            (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
            i.1 i.2))
      refine (congrArg (eval _).bind (funext fun rest => ?_)).trans hih
      exact congrArg k (funext fun ⟨i, hi⟩ =>
        Fin.cases (motive := fun idx => ∀ h : idx ∈ I, Fin.cons first rest idx =
          Fin.cases (motive := fun idx => idx ∈ I → α idx) (fun _ => first)
            (fun j hj => I'.restrict rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩) idx h)
          (fun _ => rfl) (fun _ _ => rfl) i hi)
    · simp only [dite_eq_right h0, eval_map, PMF.bind_map, Function.comp_def]
      have hconst : ∀ first : α 0,
          (eval (OracleComp.pi fun i : Fin m => programs i.succ)).bind
            (fun x => k (I.restrict (Fin.cons first x))) =
          (eval (OracleComp.piRestrict (α := fun j => α j.succ) I'
            (fun j => programs j.1.succ))).bind
            (fun rest =>
              k (fun i =>
                Fin.cases (motive := fun idx => idx ∈ I → α idx)
                  (fun hk => (h0 hk).elim)
                  (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
                  i.1 i.2)) := by
        intro first
        have hih := ih (α := fun j => α j.succ) I' (fun j => programs j.succ) (fun rest =>
          k (fun i =>
            Fin.cases (motive := fun idx => idx ∈ I → α idx)
              (fun hk => (h0 hk).elim)
              (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
              i.1 i.2))
        refine (congrArg (eval _).bind (funext fun rest => ?_)).trans hih
        exact congrArg k (funext fun ⟨i, hi⟩ =>
          Fin.cases (motive := fun idx => ∀ h : idx ∈ I, Fin.cons first rest idx =
            Fin.cases (motive := fun idx => idx ∈ I → α idx) (fun hk => (h0 hk).elim)
              (fun j hj => I'.restrict rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
                idx h)
            (fun h => (h0 h).elim) (fun _ _ => rfl) i hi)
      rw [congrArg (eval (programs 0)).bind (funext hconst), PMF.bind_const]
      rfl

/-- Restricting `eval (pi programs)` to a subset `I : Finset (Fin m)` has the same law as
`piRestrict I (I.restrict programs)`. -/
theorem eval_map_restrict_pi {m : ℕ} {α : Fin m → Type}
    (I : Finset (Fin m)) (programs : (i : Fin m) → ProbComp (α i)) :
    (eval (OracleComp.pi programs)).map I.restrict =
      eval (OracleComp.piRestrict I (I.restrict programs)) := by
  simpa only [PMF.map, Function.comp_def, PMF.bind_pure] using
    eval_bind_restrict_pi I programs PMF.pure

/-- The vector support consists exactly of the tuples of individually supported values. -/
theorem mem_support_replicateFin_iff (count : ℕ) (program : ProbComp α)
    (values : Fin count → α) :
    values ∈ (eval (OracleComp.replicateFin count program)).support ↔
      ∀ i, values i ∈ (eval program).support :=
  mem_support_pi_iff (fun _ : Fin count => program) values

/-- Finite coordinate distributions give the independent product law. -/
theorem eval_replicateFin [Finite α] (count : ℕ) (program : ProbComp α) :
    eval (OracleComp.replicateFin count program) =
      Probability.PMF.pi (fun _ : Fin count => eval program) :=
  eval_pi (fun _ : Fin count => program)

/-- Repeating a representation of each sampled value gives the represented vector law. -/
theorem eval_replicateFin_map {β : Type} {source : ProbComp α} {encoded : ProbComp β}
    {encode : α → β} (h : eval encoded = (eval source).map encode) (count : ℕ) :
    eval (OracleComp.replicate count encoded) =
      (eval (OracleComp.replicateFin count source)).map
        (fun values => List.ofFn (fun i => encode (values i))) := by
  rw [eval_replicate_map h, ← OracleComp.map_ofFn_replicateFin, eval_map, PMF.map_comp]
  simp only [Function.comp_def, List.map_ofFn]

/-- Mapping each coordinate after independent runs agrees with mapping each run's outcome.
Neither outcome type needs to be finite. -/
theorem eval_replicateFin_map_coords {β : Type} (count : ℕ) (program : ProbComp α)
    (f : α → β) :
    eval (OracleComp.replicateFin count (f <$> program)) =
      (eval (OracleComp.replicateFin count program)).map (fun values i => f (values i)) :=
  eval_pi_map (fun _ : Fin count => program) (fun _ => f)

/-- Disjoint blocks of one uniform tape realize a vector of independently sampled values.
The output type may be infinite, and either the count or the block width may be zero. -/
theorem eval_replicateFin_of_uniformList (count width : ℕ) (program : ProbComp α)
    (evaluate : List Bool → α)
    (hlaw : eval program = (BitString.uniformList width).map evaluate) :
    eval (OracleComp.replicateFin count program) =
      (BitString.uniformList (count * width)).map (fun tape i =>
        evaluate (List.ofFn (BitString.block (BitString.ofList (count * width) tape) i))) := by
  apply PMF.map_injective List.ofFn_injective
  rw [← eval_map, OracleComp.map_ofFn_replicateFin,
    eval_replicate_of_uniformList count width program evaluate hlaw, PMF.map_comp]
  simp only [Function.comp_def, BitString.listRows_eq_ofFn, List.map_ofFn]

end ProbComp

end Cslib
