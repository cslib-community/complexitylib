/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Primitives.Garbling.Switch.Basic
public import Complexity.Languages.Probabilistic.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.ZMod.Defs

/-!
# Garbled switch systems

Heath's garbling of switch systems [Heath2024] with arithmetic free-XOR labels. Labels live in an
`R`-module `L`. The garbler samples a global offset `Δ : L` whose colour `col Δ` is `1`, for an
additive colour map `col : L →+ ZMod 2`, and gives each wire `w` a zero label `K w`; the label of
value `v` on `w` is `K w + v • Δ` (`wireLabel`). For labels in `(ℤ_{2^k})^λ` the colour is the
low bit of a fixed coordinate. A tweakable hash `H : L → ℕ → L` is tweaked by the position of
the gate in the list.

The garbler visits the gates in order (`garbleGate`):

* an affine gate `out := ∑ c • w + b` sets `K out := ∑ c • K w - b • Δ` and has no
  material, so the evaluator computes the output label as `∑ c • (label of w)`;
* a switch `(src, out, ctrl)` at position `i` sets `K out := K src + H (K ctrl) i` and publishes
  the colour `col (K ctrl)` of the control's zero label;
* a join `(left, right)` publishes the difference `K right - K left`.

The evaluator propagates labels exactly as `SwitchSystem.sweep` propagates values
(`evalGate`). It uses a switch, in either direction, when the colour of the control label plus the
published colour is `0`, that is, when the control carries `0`; its key `H (K ctrl) i` is then
the hash of the control label itself. An open switch has control label `K ctrl + Δ`, and its key
stays hidden under circular correlation robustness (`Garbling.Switch.Oblivious`). A join is used
in either direction with the published difference.

**Correctness** (`evaluate_garbleWith`): for a well-formed system and every assignment `σ` that
satisfies it on the input `x`, the garbled evaluation, run from the input labels, knows exactly
the wires that propagation `SwitchSystem.solve` knows, and the label it finds on each is the label
of that wire's value. Decoding an output wire whose value is a bit `0` or `1` adds the published
colour of its zero label and gives that bit (`Garbled.run_garbleWith`). This holds for every hash,
offset of colour `1` and choice of input zero labels.

Heath's construction attaches hashed output tags to the output wires so that output labels can
also be authenticated; here output decoding is by colour only.

## Main definitions

* `Cslib.Crypto.Garbling.Switch.Material`: the material of one gate.
* `Cslib.Crypto.Garbling.Switch.garbleGates`, `Cslib.Crypto.Garbling.Switch.garbleWith`,
  `Cslib.Crypto.Garbling.Switch.garble`: garbling with given and with uniform randomness.
* `Cslib.Crypto.Garbling.Switch.evalGates`, `Cslib.Crypto.Garbling.Switch.evaluate`: the
  evaluator.

## Main results

* `Cslib.Crypto.Garbling.Switch.allConsistent_garbleGates`: the garbler's material satisfies
  the gate equations for the final zero labels.
* `Cslib.Crypto.Garbling.Switch.evaluate_garbleWith`: garbled evaluation tracks propagation.
* `Cslib.Crypto.Garbling.Switch.Garbled.run_garbleWith`: correctness of decoding.

## References

* [D. Heath, *Efficient Arithmetic in Garbled Circuits*][Heath2024]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling.Switch

open SwitchGate

variable {n m N : ℕ} {R L : Type} [CommRing R] [AddCommGroup L] [Module R L]

/-- The label of value `v` on a wire with zero label `K0`, for the global offset `Δ`. -/
def wireLabel (Δ K0 : L) (v : R) : L := K0 + v • Δ

/-- The material of one garbled gate. -/
inductive Material (L : Type) where
  /-- Affine gates have no material. -/
  | none
  /-- A switch publishes the colour of its control's zero label. -/
  | colour (bit : ZMod 2)
  /-- A join publishes the difference of its wires' zero labels. -/
  | shift (d : L)

/-- Garble the gate at position `i`, given the zero labels so far: its material and the updated
zero labels. -/
def garbleGate (H : L → ℕ → L) (col : L →+ ZMod 2) (Δ : L) (i : ℕ)
    (K : Fin n ⊕ Fin N → L) : SwitchGate n N R → Material L × (Fin n ⊕ Fin N → L)
  | affine terms b y => (.none, Function.update K (.inr y) (termSum K terms - b • Δ))
  | switch x y c => (.colour (col (K c)), Function.update K (.inr y) (K x + H (K c) i))
  | join x y => (.shift (K y - K x), K)

/-- Garble the gates `gs`, the first at position `i`: their material and the final zero
labels. -/
def garbleGates (H : L → ℕ → L) (col : L →+ ZMod 2) (Δ : L) :
    ℕ → List (SwitchGate n N R) → (Fin n ⊕ Fin N → L) →
      List (Material L) × (Fin n ⊕ Fin N → L)
  | _, [], K => ([], K)
  | i, g :: gs, K =>
    let p := garbleGate H col Δ i K g
    let q := garbleGates H col Δ (i + 1) gs p.2
    (p.1 :: q.1, q.2)

/-- A garbled switch system: the gate material, the input encoding (the zero labels of the
input wires and the offset) and the output decoding colours. -/
structure Garbled (L : Type) (n m : ℕ) where
  /-- The material of each gate, in order. -/
  material : List (Material L)
  /-- The zero label of each input wire. -/
  zero : Fin n → L
  /-- The global offset. -/
  delta : L
  /-- The colour of each output wire's zero label. -/
  decoding : Fin m → ZMod 2

/-- The zero labels of all wires after garbling `S` with offset `Δ` and input zero labels
`K`. -/
def zeroLabels (S : SwitchSystem n m N R) (H : L → ℕ → L) (col : L →+ ZMod 2) (Δ : L)
    (K : Fin n → L) : Fin n ⊕ Fin N → L :=
  (garbleGates H col Δ 0 S.gates (Sum.elim K 0)).2

/-- Garble `S` with offset `Δ` and input zero labels `K`. -/
def garbleWith (S : SwitchSystem n m N R) (H : L → ℕ → L) (col : L →+ ZMod 2) (Δ : L)
    (K : Fin n → L) : Garbled L n m where
  material := (garbleGates H col Δ 0 S.gates (Sum.elim K 0)).1
  zero := K
  delta := Δ
  decoding o := col (zeroLabels S H col Δ K (S.output o))

/-- Garble `S` with a uniform offset of colour `1` and uniform input zero labels. -/
noncomputable def garble (S : SwitchSystem n m N R) (H : L → ℕ → L) (col : L →+ ZMod 2)
    [Fintype L] [Nonempty {Δ : L // col Δ = 1}] : ProbComp (Garbled L n m) :=
  do
    let Δ ← ProbComp.uniform {Δ : L // col Δ = 1}
    let K ← ProbComp.uniform (Fin n → L)
    return garbleWith S H col Δ K

/-- The input labels of input `x`. -/
def Garbled.encode (G : Garbled L n m) (x : Fin n → R) : Fin n → L :=
  fun i => wireLabel G.delta (G.zero i) (x i)

/-- One evaluation step through the gate at position `i` with material `μ`: fill in a label the
gate determines from known labels. -/
def evalGate (H : L → ℕ → L) (col : L →+ ZMod 2) (i : ℕ)
    (st : Fin n ⊕ Fin N → Option L) :
    SwitchGate n N R → Material L → Fin n ⊕ Fin N → Option L
  | affine terms _ y, _ => match st (.inr y), knownSum st terms with
    | none, some s => Function.update st (.inr y) (some s)
    | _, _ => st
  | switch x y c, .colour p => match st c with
    | some k => if col k + p = 0 then
        match st x, st (.inr y) with
        | some a, none => Function.update st (.inr y) (some (a + H k i))
        | none, some a => Function.update st x (some (a - H k i))
        | _, _ => st
      else st
    | none => st
  | join x y, .shift d => match st x, st y with
    | some a, none => Function.update st y (some (a + d))
    | none, some a => Function.update st x (some (a - d))
    | _, _ => st
  | _, _ => st

/-- Evaluate through the gates `gs` with their material, the first at position `i`. -/
def evalGates (H : L → ℕ → L) (col : L →+ ZMod 2) :
    ℕ → List (SwitchGate n N R) → List (Material L) →
      (Fin n ⊕ Fin N → Option L) → Fin n ⊕ Fin N → Option L
  | i, g :: gs, μ :: μs, st => evalGates H col (i + 1) gs μs (evalGate H col i st g μ)
  | _, _, _, st => st

/-- Evaluate a garbled system from input labels `X`: one sweep through the gates per wire. -/
def evaluate (S : SwitchSystem n m N R) (H : L → ℕ → L) (col : L →+ ZMod 2)
    (material : List (Material L)) (X : Fin n → L) : Fin n ⊕ Fin N → Option L :=
  (evalGates H col 0 S.gates material)^[n + N] (Sum.elim (fun i => some (X i)) fun _ => none)

/-- Evaluate a garbled system on input `x` and decode each output wire whose label is found. -/
def Garbled.run (G : Garbled L n m) (S : SwitchSystem n m N R) (H : L → ℕ → L)
    (col : L →+ ZMod 2) (x : Fin n → R) : Fin m → Option (ZMod 2) :=
  fun o => (evaluate S H col G.material (G.encode x) (S.output o)).map fun Y => col Y + G.decoding o

/-! ### The garbler's equations -/

/-- The gate at position `i` with material `μ` satisfies the garbler's equations for the zero
labels `K`. -/
def Consistent (H : L → ℕ → L) (col : L →+ ZMod 2) (Δ : L) (K : Fin n ⊕ Fin N → L)
    (i : ℕ) : SwitchGate n N R → Material L → Prop
  | affine terms b y, μ => μ = .none ∧ K (.inr y) = termSum K terms - b • Δ
  | switch x y c, μ => μ = .colour (col (K c)) ∧ K (.inr y) = K x + H (K c) i
  | join x y, μ => μ = .shift (K y - K x)

/-- Every gate of `gs`, the first at position `i`, satisfies the garbler's equations with its
material. -/
def AllConsistent (H : L → ℕ → L) (col : L →+ ZMod 2) (Δ : L) (K : Fin n ⊕ Fin N → L) :
    ℕ → List (SwitchGate n N R) → List (Material L) → Prop
  | _, [], [] => True
  | i, g :: gs, μ :: μs =>
    Consistent H col Δ K i g μ ∧ AllConsistent H col Δ K (i + 1) gs μs
  | _, _, _ => False

private theorem termSum_congr {K K' : Fin n ⊕ Fin N → L} (terms : List ((Fin n ⊕ Fin N) × R))
    (h : ∀ p ∈ terms, K p.1 = K' p.1) : termSum K terms = termSum K' terms := by
  simp only [termSum]
  congr 1
  exact List.map_congr_left fun p hp => by rw [h p hp]

private theorem garbleGate_eq_on (H : L → ℕ → L) (col : L →+ ZMod 2) (Δ : L) (i : ℕ)
    (K : Fin n ⊕ Fin N → L) {D : Set (Fin n ⊕ Fin N)} {g : SwitchGate n N R}
    (hg : g.WellPlaced D) : ∀ w ∈ D, (garbleGate H col Δ i K g).2 w = K w := by
  intro w hw
  cases g with
  | affine terms b y =>
    exact Function.update_of_ne (fun (h : w = .inr y) => hg.2 (h ▸ hw)) _ _
  | switch x y c =>
    exact Function.update_of_ne (fun (h : w = .inr y) => hg.2.2 (h ▸ hw)) _ _
  | join x y => rfl

/-- The garbler's equations hold for its final zero labels, which agree with the starting ones
on the wires defined before the gates. -/
theorem allConsistent_garbleGates (H : L → ℕ → L) (col : L →+ ZMod 2) (Δ : L) :
    ∀ (gs : List (SwitchGate n N R)) (D : Set (Fin n ⊕ Fin N)) (i : ℕ)
      (K : Fin n ⊕ Fin N → L), SwitchSystem.WellFormedFrom D gs →
      AllConsistent H col Δ (garbleGates H col Δ i gs K).2 i gs
          (garbleGates H col Δ i gs K).1 ∧
        ∀ w ∈ D, (garbleGates H col Δ i gs K).2 w = K w
  | [], _, _, _, _ => ⟨trivial, fun _ _ => rfl⟩
  | g :: gs, D, i, K, ⟨hg, hgs⟩ => by
    obtain ⟨hcons, heq⟩ := allConsistent_garbleGates H col Δ gs (g.define D) (i + 1)
      (garbleGate H col Δ i K g).2 hgs
    have hD := garbleGate_eq_on H col Δ i K hg
    -- The final labels agree with the starting ones on the wires defined before `g`.
    have hfin :
        ∀ w ∈ D, (garbleGates H col Δ (i + 1) gs (garbleGate H col Δ i K g).2).2 w = K w :=
      fun w hw => (heq w (g.mem_define_of_mem hw)).trans (hD w hw)
    refine ⟨⟨?_, hcons⟩, hfin⟩
    change Consistent H col Δ (garbleGates H col Δ (i + 1) gs (garbleGate H col Δ i K g).2).2 i g
      (garbleGate H col Δ i K g).1
    cases g with
    | affine terms b y =>
      have hy := heq (.inr y) (Set.mem_insert _ _)
      refine ⟨rfl, ?_⟩
      rw [hy, termSum_congr terms fun p hp => hfin p.1 (hg.1 p hp)]
      exact Function.update_self _ _ _
    | switch x y c =>
      have hy := heq (.inr y) (Set.mem_insert _ _)
      have hx := hfin x hg.1
      have hc := hfin c hg.2.1
      refine ⟨by rw [hc]; rfl, ?_⟩
      rw [hy, hx, hc]
      exact Function.update_self _ _ _
    | join x y =>
      change Material.shift (K y - K x) = Material.shift (_ - _)
      rw [hfin x hg.1, hfin y hg.2]

/-! ### Correctness -/

private theorem knownSum_map (Δ : L) (K : Fin n ⊕ Fin N → L)
    (pst : Fin n ⊕ Fin N → Option R) :
    ∀ ts : List ((Fin n ⊕ Fin N) × R),
      knownSum (fun w => (pst w).map (wireLabel Δ (K w))) ts =
        (knownSum pst ts).map fun s => termSum K ts + s • Δ
  | [] => by simp [knownSum, termSum]
  | (w, c) :: ts => by
    have ih := knownSum_map Δ K pst ts
    simp only [knownSum, ih]
    cases pst w with
    | none => rfl
    | some a =>
      cases knownSum pst ts with
      | none => rfl
      | some s =>
        simp only [Option.map_some, termSum, List.map_cons, List.sum_cons, wireLabel,
          Option.some.injEq]
        rw [smul_eq_mul, add_smul, mul_smul, smul_add]
        abel

/-- An offset of colour `1` makes `1 ≠ 0` in `R`. -/
private theorem one_ne_zero_of_col {col : L →+ ZMod 2} {Δ : L} (hΔ : col Δ = 1) :
    (1 : R) ≠ 0 := by
  intro h
  have h0 : Δ = 0 := by rw [← one_smul R Δ, h, zero_smul]
  rw [h0, map_zero] at hΔ
  exact absurd hΔ (by decide)

/-- The colour of a label shifted by `v • Δ`, for a bit `v` and an offset of colour `1`. -/
private theorem col_wireLabel_add [DecidableEq R] {col : L →+ ZMod 2} {Δ : L} (hΔ : col Δ = 1)
    (K0 : L) {v : R} (hv : v = 0 ∨ v = 1) :
    col (wireLabel Δ K0 v) + col K0 = if v = 0 then 0 else 1 := by
  rcases hv with rfl | rfl
  · rw [ite_eq_left rfl, wireLabel, zero_smul, add_zero]
    exact CharTwo.add_self_eq_zero _
  · rw [ite_eq_right (one_ne_zero_of_col hΔ), wireLabel, one_smul, map_add, hΔ,
      add_comm (col K0) 1, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The lockstep relation between propagation and garbled evaluation for zero labels `K`. -/
private def Lockstep (Δ : L) (K : Fin n ⊕ Fin N → L) (σ : Fin n ⊕ Fin N → R)
    (pst : Fin n ⊕ Fin N → Option R) (gst : Fin n ⊕ Fin N → Option L) : Prop :=
  (∀ w, gst w = (pst w).map (wireLabel Δ (K w))) ∧ ∀ w v, pst w = some v → v = σ w

private theorem lockstep_update {Δ : L} {K : Fin n ⊕ Fin N → L}
    {pst : Fin n ⊕ Fin N → Option R} {gst : Fin n ⊕ Fin N → Option L}
    (h : ∀ w, gst w = (pst w).map (wireLabel Δ (K w))) (w : Fin n ⊕ Fin N) (v : R) (a : L)
    (ha : a = wireLabel Δ (K w) v) (u : Fin n ⊕ Fin N) :
    Function.update gst w (some a) u = (Function.update pst w (some v) u).map
      (wireLabel Δ (K u)) := by
  by_cases hu : u = w
  · subst hu
    simp [ha]
  · simp only [Function.update_of_ne hu]
    exact h u

private theorem lockstep_evalGate [DecidableEq R] {H : L → ℕ → L} {col : L →+ ZMod 2}
    {Δ : L} (hΔ : col Δ = 1) {K : Fin n ⊕ Fin N → L} {σ : Fin n ⊕ Fin N → R} {i : ℕ}
    {g : SwitchGate n N R} {μ : Material L} (hcons : Consistent H col Δ K i g μ)
    (hg : g.Holds σ) {pst : Fin n ⊕ Fin N → Option R} {gst : Fin n ⊕ Fin N → Option L}
    (h : Lockstep Δ K σ pst gst) :
    Lockstep Δ K σ (g.propagate pst) (evalGate H col i gst g μ) := by
  obtain ⟨hmap, hsound⟩ := h
  refine ⟨?_, g.propagate_sound hsound hg⟩
  cases g with
  | affine terms b y =>
    obtain ⟨rfl, hy⟩ := hcons
    have hsum := knownSum_map Δ K pst terms
    have hgs :
        knownSum gst terms = (knownSum pst terms).map fun s => termSum K terms + s • Δ := by
      rw [← hsum]
      exact congrArg (knownSum · terms) (funext hmap)
    simp only [propagate, evalGate, hmap (.inr y), hgs]
    cases pst (.inr y) with
    | some v => cases knownSum pst terms <;> exact hmap
    | none =>
      cases knownSum pst terms with
      | none => exact hmap
      | some s =>
        refine lockstep_update hmap _ _ _ ?_
        simp only [wireLabel, hy, add_smul]
        abel
  | switch x y c =>
    obtain ⟨rfl, hy⟩ := hcons
    simp only [propagate, evalGate, hmap c]
    cases hpc : pst c with
    | none => simp only [Option.map_none, reduceCtorEq, ite_false]; exact hmap
    | some v =>
      have hv : v = σ c := hsound c v hpc
      have hbit : v = 0 ∨ v = 1 := hv ▸ hg.1
      simp only [Option.map_some, col_wireLabel_add hΔ (K c) hbit, Option.some.injEq]
      by_cases hv0 : v = 0
      · subst hv0
        have hk : wireLabel Δ (K c) (0 : R) = K c := by simp [wireLabel]
        simp only [ite_true, hk, hmap x, hmap (.inr y)]
        cases pst x with
        | none =>
          cases pst (.inr y) with
          | none => exact hmap
          | some a =>
            refine lockstep_update hmap _ _ _ ?_
            simp only [wireLabel, hy]
            abel
        | some a =>
          cases pst (.inr y) with
          | none =>
            refine lockstep_update hmap _ _ _ ?_
            simp only [wireLabel, hy]
            abel
          | some _ => exact hmap
      · simp only [hv0, ite_false]
        exact hmap
  | join x y =>
    change μ = _ at hcons
    subst hcons
    simp only [propagate, evalGate, hmap x, hmap y]
    cases pst x with
    | none =>
      cases pst y with
      | none => exact hmap
      | some a =>
        refine lockstep_update hmap _ _ _ ?_
        simp only [wireLabel]
        abel
    | some a =>
      cases pst y with
      | none =>
        refine lockstep_update hmap _ _ _ ?_
        simp only [wireLabel]
        abel
      | some _ => exact hmap

private theorem lockstep_evalGates [DecidableEq R] {H : L → ℕ → L} {col : L →+ ZMod 2}
    {Δ : L} (hΔ : col Δ = 1) {K : Fin n ⊕ Fin N → L} {σ : Fin n ⊕ Fin N → R} :
    ∀ (i : ℕ) (gs : List (SwitchGate n N R)) (μs : List (Material L)),
      AllConsistent H col Δ K i gs μs → (∀ g ∈ gs, g.Holds σ) →
      ∀ pst gst, Lockstep Δ K σ pst gst →
        Lockstep Δ K σ (SwitchSystem.sweepGates gs pst) (evalGates H col i gs μs gst)
  | _, [], [], _, _, _, _, h => h
  | i, g :: gs, _ :: μs, ⟨hc, hcs⟩, hgs, _, _, h =>
    lockstep_evalGates hΔ (i + 1) gs μs hcs (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      _ _ (lockstep_evalGate hΔ hc (hgs g List.mem_cons_self) h)
  | _, [], _ :: _, hc, _, _, _, _ => hc.elim
  | _, _ :: _, [], hc, _, _, _, _ => hc.elim

/-- **Garbled evaluation tracks propagation.** For a well-formed system, an assignment `σ`
satisfying it on input `x`, every hash `H`, offset `Δ` of colour `1` and input zero labels `K`,
the evaluator run from the input labels of `x` finds a label on exactly the wires on which
propagation finds a value, and that label is the wire's label for the value. -/
theorem evaluate_garbleWith [DecidableEq R] {S : SwitchSystem n m N R} (hS : S.WellFormed)
    {x : Fin n → R} {σ : Fin n ⊕ Fin N → R} (hσ : S.Satisfies x σ) (H : L → ℕ → L)
    (col : L →+ ZMod 2) {Δ : L} (hΔ : col Δ = 1) (K : Fin n → L) (w : Fin n ⊕ Fin N) :
    evaluate S H col (garbleWith S H col Δ K).material ((garbleWith S H col Δ K).encode x) w =
      (S.solve x w).map (wireLabel Δ (zeroLabels S H col Δ K w)) := by
  obtain ⟨hcons, hinp⟩ :=
    allConsistent_garbleGates H col Δ S.gates _ 0 (Sum.elim K 0) hS
  have hinit : Lockstep Δ (zeroLabels S H col Δ K) σ (SwitchSystem.initState x)
      (Sum.elim (fun i => some ((garbleWith S H col Δ K).encode x i)) fun _ => none) := by
    refine ⟨?_, ?_⟩
    · rintro (i | j)
      · simp only [Sum.elim_inl, SwitchSystem.initState, Option.map_some, Garbled.encode,
          garbleWith, zeroLabels]
        rw [hinp (.inl i) ⟨i, rfl⟩]
        rfl
      · rfl
    · rintro (i | j) a ha
      · simp only [SwitchSystem.initState, Sum.elim_inl, Option.some.injEq] at ha
        rw [← ha, hσ.1 i]
      · simp [SwitchSystem.initState] at ha
  have key : ∀ t, Lockstep Δ (zeroLabels S H col Δ K) σ
      (S.sweep^[t] (SwitchSystem.initState x))
      ((evalGates H col 0 S.gates (garbleWith S H col Δ K).material)^[t]
        (Sum.elim (fun i => some ((garbleWith S H col Δ K).encode x i)) fun _ => none)) := by
    intro t
    induction t with
    | zero => exact hinit
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact lockstep_evalGates hΔ 0 S.gates _ hcons hσ.2 _ _ ih
  exact (key (n + N)).1 w

/-- **Correctness.** For a well-formed system and an assignment `σ` satisfying it on input `x`,
every output wire on which propagation finds a bit `v` decodes to `v`, for every hash, offset of
colour `1` and input zero labels. -/
theorem Garbled.run_garbleWith [DecidableEq R] {S : SwitchSystem n m N R} (hS : S.WellFormed)
    {x : Fin n → R} {σ : Fin n ⊕ Fin N → R} (hσ : S.Satisfies x σ) (H : L → ℕ → L)
    (col : L →+ ZMod 2) {Δ : L} (hΔ : col Δ = 1) (K : Fin n → L) (o : Fin m) {v : R}
    (ho : S.solve x (S.output o) = some v) (hv : v = 0 ∨ v = 1) :
    (garbleWith S H col Δ K).run S H col x o = some (if v = 0 then 0 else 1) := by
  simp only [Garbled.run, evaluate_garbleWith hS hσ H col hΔ K, ho, Option.map_some,
    Option.some.injEq]
  exact col_wireLabel_add hΔ _ hv

end Cslib.Crypto.Garbling.Switch
