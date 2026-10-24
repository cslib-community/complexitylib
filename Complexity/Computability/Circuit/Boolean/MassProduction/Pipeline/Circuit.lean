/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.BatchLookup
public import Complexity.Computability.Circuit.Boolean.MassProduction.Pipeline.Packing
public import Complexity.Computability.Circuit.Boolean.MassProduction.Schedule
public import Complexity.Computability.Circuit.Replication
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The scheduled recovery circuit

One circuit answers `t` requests `Fin.append a z` to a packed function (see
`MassProduction.Pipeline.Packing`), keeping every request in its input position:

1. a shared table maps every prefix `a` to its target point, copy and bit position
   (`lookupStage`, by `batchLookupCircuit`);
2. a scheduler lists the points of pairwise disjoint punctured lines through the targets
   (`scheduleStage`);
3. every incidence of a request with a point of its line sends the request's suffix to the slot
   of its copy and point (`scatterCircuit`); since the lines are disjoint, a slot receives the
   suffix of at most one request, and unused slots receive zeros;
4. every slot evaluates every resource of its copy and point on its suffix once
   (`bankCircuit`), from caller-supplied resource circuits;
5. every incidence reads back the resource bit of its request (`gatherCircuit`);
6. every request sums its gathered bits (`lineSums`, at four gates per bit by
   `complexity_lineSums_le`).

The sum of a request is the requested value (`lineSums_eval_recoveryCircuit`). Requests may
repeat. Scatter and gather are shared OR lookups (`batchOrCircuit`) on keys made of a copy index,
point bits and, for the gather, a bit index.

Sizes count every gate, constants included (`size_recoveryCircuit`); they do not certify the
running time of the circuit constructors.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Pipeline.slotEquiv`,
  `Cslib.Circuits.Boolean.MassProduction.Pipeline.slotKey`: slot numbering and lookup keys.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.metaWidth`,
  `Cslib.Circuits.Boolean.MassProduction.Pipeline.stateWidth`,
  `Cslib.Circuits.Boolean.MassProduction.Pipeline.metadata`,
  `Cslib.Circuits.Boolean.MassProduction.Pipeline.prefixWires`,
  `Cslib.Circuits.Boolean.MassProduction.Pipeline.incidenceKey`: wire widths, prefix metadata, and
  incidence lookup keys.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.recoveryCircuit`: stages one to five.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.lineSums`: stage six, as a function.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.slotResource`: the resource of a slot.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.Pipeline.lineSums_eval_recoveryCircuit`: correctness.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.size_recoveryCircuit`: the exact gate count.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.complexity_lineSums_le`: the cost of the sums.

## References

* Adapted from MassProduction/HighRate/{ResourceLayout,PrefixMetadata}.lean and
  MassProduction/Nonuniform/{IncidenceEvaluation,MaskedScatter,ResourceBank,ResourceGather,
  ScheduledRecovery}.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Pipeline

open Finset BitString LineCode

/-! ### Shared OR lookup with one matching value -/

/-- If some source matches a query and every matching source carries the value `V`, the shared
OR lookup returns `V` to that query. -/
theorem directProductInput_eval_batchOrCircuit {input sources requests k v : ℕ}
    (sourceKeys : Fin sources → Fin k → Fin input ⊕ Bool)
    (sourceValues : Fin sources → Fin v → Fin input ⊕ Bool)
    (queryKeys : Fin requests → Fin k → Fin input ⊕ Bool) (x : BitString input)
    (request : Fin requests) {V : BitString v}
    (hex : ∃ source, substitute (sourceKeys source) x = substitute (queryKeys request) x)
    (hall : ∀ source, substitute (sourceKeys source) x = substitute (queryKeys request) x →
      substitute (sourceValues source) x = V) :
    directProductInput ((batchOrCircuit sourceKeys sourceValues queryKeys).eval interpretation x)
      request = V := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  change (batchOrCircuit sourceKeys sourceValues queryKeys).eval interpretation x
    (finProdFinEquiv (request, bit)) = true ↔ _
  rw [eval_batchOrCircuit_iff]
  constructor
  · rintro ⟨source, hkey, hvalue⟩
    rwa [hall source hkey] at hvalue
  · intro hV
    obtain ⟨source, hkey⟩ := hex
    exact ⟨source, hkey, by rwa [hall source hkey]⟩

/-! ### Encodings -/

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {t p w ℓ b s copies : ℕ}

/-- Slots are numbered by a copy and the bits of a point. -/
def slotEquiv : Fin copies × BitString (ℓ * b) ≃ Fin (copies * 2 ^ (ℓ * b)) :=
  (Equiv.prodCongr (Equiv.refl _) (BitString.equivFin _)).trans finProdFinEquiv

/-- The key of a slot: its copy index followed by its point bits. -/
def slotKey (q : Fin (copies * 2 ^ (ℓ * b))) : BitString (Nat.clog 2 copies + ℓ * b) :=
  Fin.append (indexBits (slotEquiv.symm q).1) (slotEquiv.symm q).2

/-- The key of `slotEquiv (c, y)` is the binary index of `c` followed by `y`. -/
theorem slotKey_slotEquiv (c : Fin copies) (y : BitString (ℓ * b)) :
    slotKey (slotEquiv (c, y)) = Fin.append (indexBits c) y := by
  simp only [slotKey, Equiv.symm_apply_apply]

/-- The width of the metadata of a request: its target point, copy and bit position. -/
abbrev metaWidth (ℓ b copies : ℕ) : ℕ := ℓ * b + (Nat.clog 2 copies + Nat.clog 2 b)

/-- The width of the circuit state after scheduling: listed lines, metadata and the input. -/
abbrev stateWidth (t p w ℓ b s copies : ℕ) : ℕ :=
  t * (s * (ℓ * b)) + (t * metaWidth ℓ b copies + t * (p + w))

private theorem append_eq_append_iff {α : Type*} {m n : ℕ} {u u' : Fin m → α} {v v' : Fin n → α} :
    Fin.append u v = Fin.append u' v' ↔ u = u' ∧ v = v' := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa only [Fin.append_left] using congrFun h (Fin.castAdd n i)
    · simpa only [Fin.append_right] using congrFun h (Fin.natAdd m i)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Distinct slots have distinct lookup keys. -/
theorem slotKey_injective : Function.Injective (slotKey (copies := copies) (ℓ := ℓ) (b := b)) := by
  intro q q' h
  rw [slotKey, slotKey, append_eq_append_iff] at h
  apply slotEquiv.symm.injective
  exact Prod.ext (indexBits_injective h.1) h.2

/-! ### The stages -/

variable (bits : K ≃+ BitString b) (C : LineCode K ℓ)
  (place : BitString p ↪ Fin copies × C.info × Fin b)

/-- The metadata of a prefix: the bits of its information point, its copy and its bit index. -/
def metadata (a : BitString p) : BitString (metaWidth ℓ b copies) :=
  Fin.append (pointBits bits ((place a).2.1 : Fin ℓ → K))
    (Fin.append (indexBits (place a).1) (indexBits (place a).2.2))

variable (t p w) in
/-- The input wires of the prefixes of the requests, as `t` consecutive blocks. -/
def prefixWires (y : Fin (t * p)) : Fin (t * (p + w)) :=
  finProdFinEquiv ((finProdFinEquiv.symm y).1, Fin.castAdd w (finProdFinEquiv.symm y).2)

/-- Stage one: look up the metadata of every prefix in one shared table, keeping the input. -/
def lookupStage (t w : ℕ) :
    Circuit signature (t * (p + w)) (t * metaWidth ℓ b copies + t * (p + w)) :=
  ((batchLookupCircuit (metadata bits C place) t).comp
      (Circuit.wiring signature (prefixWires t p w))).append (Circuit.id signature _)

variable {bits C place}

/-- Stage two: list the lines of the scheduler through the target points, keeping the state. -/
def scheduleStage (sched : Circuit signature (t * (ℓ * b)) (t * (s * (ℓ * b))))
    (p w copies : ℕ) :
    Circuit signature (t * metaWidth ℓ b copies + t * (p + w)) (stateWidth t p w ℓ b s copies) :=
  (sched.comp (Circuit.wiring signature fun y => Fin.castAdd (t * (p + w))
      (finProdFinEquiv ((finProdFinEquiv.symm y).1,
        Fin.castAdd (Nat.clog 2 copies + Nat.clog 2 b) (finProdFinEquiv.symm y).2)))).append
    (Circuit.id signature _)

variable (t p w ℓ b s copies) in
/-- The state wires of the key of incidence `(i, j)`: the copy index of request `i`, then
point `j` of its line. -/
def incidenceKey (y : Fin (t * s)) :
    Fin (Nat.clog 2 copies + ℓ * b) → Fin (stateWidth t p w ℓ b s copies) :=
  Fin.append
    (fun k => Fin.natAdd (t * (s * (ℓ * b))) (Fin.castAdd (t * (p + w))
      (finProdFinEquiv ((finProdFinEquiv.symm y).1,
        Fin.natAdd (ℓ * b) (Fin.castAdd (Nat.clog 2 b) k)))))
    (fun k => Fin.castAdd (t * metaWidth ℓ b copies + t * (p + w))
      (finProdFinEquiv ((finProdFinEquiv.symm y).1,
        finProdFinEquiv ((finProdFinEquiv.symm y).2, k))))

variable (t p w ℓ b s copies) in
/-- Stage three: every incidence sends the suffix of its request to the slot of its key. -/
def scatterCircuit :
    Circuit signature (stateWidth t p w ℓ b s copies) (copies * 2 ^ (ℓ * b) * w) :=
  batchOrCircuit (fun y => Sum.inl ∘ incidenceKey t p w ℓ b s copies y)
    (fun y k => .inl (Fin.natAdd (t * (s * (ℓ * b))) (Fin.natAdd (t * metaWidth ℓ b copies)
      (finProdFinEquiv ((finProdFinEquiv.symm y).1, Fin.natAdd p k)))))
    (fun q => Sum.inr ∘ slotKey q)

/-- Stage four: every slot runs one circuit per bit position on its suffix. -/
def bankCircuit (members : Fin (copies * 2 ^ (ℓ * b)) → Fin b → Circuit signature w 1) :
    Circuit signature (copies * 2 ^ (ℓ * b) * w) (copies * 2 ^ (ℓ * b) * b) :=
  Circuit.parallelFamily fun q => Circuit.pi (members q)

variable (t p w ℓ b s copies) in
/-- Stage five: every incidence reads the bank output at the slot of its key and the bit
position of its request. -/
def gatherCircuit :
    Circuit signature (copies * 2 ^ (ℓ * b) * b + stateWidth t p w ℓ b s copies) (t * s * 1) :=
  batchOrCircuit
    (fun y => Sum.inr ∘ Fin.append (slotKey (finProdFinEquiv.symm y).1)
      (indexBits (finProdFinEquiv.symm y).2))
    (fun y _ => .inl (Fin.castAdd _ y))
    (fun y => Sum.inl ∘ Fin.append (Fin.natAdd _ ∘ incidenceKey t p w ℓ b s copies y)
      (fun k => Fin.natAdd (copies * 2 ^ (ℓ * b) * b) (Fin.natAdd (t * (s * (ℓ * b)))
        (Fin.castAdd (t * (p + w)) (finProdFinEquiv ((finProdFinEquiv.symm y).1,
          Fin.natAdd (ℓ * b) (Fin.natAdd (Nat.clog 2 copies) k)))))))

variable (bits C place) in
/-- The scheduled recovery circuit. Output `(i, j)` is the resource bit of request `i` at point
`j` of its line. -/
def recoveryCircuit (sched : Circuit signature (t * (ℓ * b)) (t * (s * (ℓ * b))))
    (members : Fin (copies * 2 ^ (ℓ * b)) → Fin b → Circuit signature w 1) :
    Circuit signature (t * (p + w)) (t * s * 1) :=
  (gatherCircuit t p w ℓ b s copies).comp
    ((((bankCircuit members).comp (scatterCircuit t p w ℓ b s copies)).append
        (Circuit.id signature _)).comp
      ((scheduleStage sched p w copies).comp (lookupStage bits C place t w)))

/-- Every gate is counted, including the constants of the lookups. -/
theorem size_recoveryCircuit (sched : Circuit signature (t * (ℓ * b)) (t * (s * (ℓ * b))))
    (members : Fin (copies * 2 ^ (ℓ * b)) → Fin b → Circuit signature w 1) :
    (recoveryCircuit bits C place sched members).size =
      (batchLookupCircuit (metadata bits C place) t).size + sched.size +
        (scatterCircuit t p w ℓ b s copies).size + (∑ q, ∑ r, (members q r).size) +
        (gatherCircuit t p w ℓ b s copies).size := by
  simp only [recoveryCircuit, lookupStage, scheduleStage, bankCircuit, Circuit.size_comp,
    Circuit.size_append, Circuit.size_wiring, Circuit.size_parallelFamily, Circuit.size_pi]
  ring

variable (t s) in
/-- Stage six, as a function: request `i` sums its `s` gathered bits. -/
def lineSums (y : BitString (t * s * 1)) (i : Fin t) : Bool :=
  ∑ j : Fin s, y (finProdFinEquiv (finProdFinEquiv (i, j), 0))

/-- Summing the gathered bits costs four gates per bit and one constant per request. -/
theorem complexity_lineSums_le : complexity interpretation (lineSums t s) ≤ t * (4 * s + 1) := by
  have h : Synthesis interpretation (inputs (t * s * 1))
      (Set.range fun i y => lineSums t s y i) (∑ _i : Fin t, ((∑ _j : Fin s, (0 + 4)) + 1)) :=
    Synthesis.family _ _ fun i => Synthesis.sum univ _ (fun _ => 0) fun j _ =>
      Synthesis.of_mem ⟨finProdFinEquiv (finProdFinEquiv (i, j), 0), rfl⟩
  obtain ⟨c, hc, hsize⟩ := h.exists_circuit_outputs
  refine (complexity_le_of_computes c hc).trans (hsize.trans_eq ?_)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-! ### Correctness -/

variable (bits C place) in
/-- The resource of slot `q` and bit position `r`. -/
def slotResource (f : BooleanFunction (p + w)) (q : Fin (copies * 2 ^ (ℓ * b))) (r : Fin b) :
    BooleanFunction w :=
  resource bits C place f (slotEquiv.symm q).1 ((pointEquiv bits).symm (slotEquiv.symm q).2) r

/-- **Correctness of scheduled recovery.** Given a scheduler and circuits for the slot resources,
the outputs of every request along its line sum to `f` at its input block. -/
theorem lineSums_eval_recoveryCircuit (scalar : Fin s ≃ {c : K // c ≠ 0})
    {sched : Circuit signature (t * (ℓ * b)) (t * (s * (ℓ * b)))}
    (hsched : IsScheduler bits scalar sched) {f : BooleanFunction (p + w)}
    {members : Fin (copies * 2 ^ (ℓ * b)) → Fin b → Circuit signature w 1}
    (hmembers : ∀ q r,
      (members q r).Computes interpretation (single (slotResource bits C place f q r)))
    (x : BitString (t * (p + w))) :
    lineSums t s ((recoveryCircuit bits C place sched members).eval interpretation x) =
      directProduct f t x := by
  funext i
  -- The requests, their targets and the scheduled lines.
  set a : Fin t → BitString p := fun i k => directProductInput x i (Fin.castAdd w k) with ha
  set z : Fin t → BitString w := fun i k => directProductInput x i (Fin.natAdd p k) with hz
  set targets : Fin t → Fin ℓ → K := fun i => ((place (a i)).2.1 : Fin ℓ → K) with htargets
  obtain ⟨dirs, hdirs, hdisj, hlines⟩ := hsched targets
  set point : Fin t → Fin s → Fin ℓ → K := fun i j => targets i + (scalar j : K) • dirs i
    with hpoint
  have hmem (i : Fin t) (j : Fin s) : point i j ∈ puncturedLine (targets i) (dirs i) :=
    mem_image_of_mem _ (mem_erase.mpr ⟨(scalar j).2, mem_univ _⟩)
  -- Stage one.
  set M := blockMap (metadata bits C place) t (x ∘ prefixWires t p w) with hM
  have hMapply (i : Fin t) (k : Fin (metaWidth ℓ b copies)) :
      M (finProdFinEquiv (i, k)) = metadata bits C place (a i) k := by
    rw [hM, blockMap_apply]
    congr 1
    funext k
    simp only [directProductInput, prefixWires, Function.comp_apply, Equiv.symm_apply_apply, ha]
  have h1 : (lookupStage bits C place t w).eval interpretation x = Fin.append M x := by
    simp only [lookupStage, Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring,
      eval_batchLookupCircuit]
    rfl
  -- Stage two.
  set L := lineBits bits (fun j => (scalar j : K)) targets dirs with hL
  set W := Fin.append L (Fin.append M x) with hW
  have h2 : (scheduleStage sched p w copies).eval interpretation (Fin.append M x) = W := by
    simp only [scheduleStage, Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring]
    rw [hW, ← hlines]
    congr 2
    funext y
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective y
    simp only [Function.comp_apply, Fin.append_left, hMapply, metadata,
      targetBits, blocksEquiv_symm_apply, Equiv.symm_apply_apply, htargets]
  have hLapply (i : Fin t) (j : Fin s) (k : Fin (ℓ * b)) :
      L (finProdFinEquiv (i, finProdFinEquiv (j, k))) = pointBits bits (point i j) k := by
    simp only [hL, lineBits, blocksEquiv_symm_apply, Equiv.symm_apply_apply, hpoint]
  -- Stage three.
  have hkey (i : Fin t) (j : Fin s) :
      substitute (Sum.inl ∘ incidenceKey t p w ℓ b s copies (finProdFinEquiv (i, j))) W =
        Fin.append (indexBits (place (a i)).1) (pointBits bits (point i j)) := by
    funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [substitute, incidenceKey, Function.comp_apply, Sum.elim_inl, hW,
        Fin.append_left, Fin.append_right, Equiv.symm_apply_apply, hMapply, metadata]
    · simp only [substitute, incidenceKey, Function.comp_apply, Sum.elim_inl, hW,
        Fin.append_left, Fin.append_right, Equiv.symm_apply_apply, hLapply]
  have hslot (q : Fin (copies * 2 ^ (ℓ * b))) :
      substitute (Sum.inr ∘ slotKey q) W = slotKey q := rfl
  set S := (scatterCircuit t p w ℓ b s copies).eval interpretation W with hS
  have hscatter (i : Fin t) (j : Fin s) :
      directProductInput S (slotEquiv ((place (a i)).1, pointBits bits (point i j))) = z i := by
    apply directProductInput_eval_batchOrCircuit
    · exact ⟨finProdFinEquiv (i, j), by rw [hkey, hslot, slotKey_slotEquiv]⟩
    · intro y hy
      obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective y
      rw [hkey, hslot, slotKey_slotEquiv, append_eq_append_iff] at hy
      have hpt : point i' j' = point i j := (pointEquiv bits).injective hy.2
      obtain rfl : i' = i := by
        by_contra hne
        exact disjoint_left.mp (hdisj i' i hne) (hmem i' j') (hpt ▸ hmem i j)
      funext k
      simp only [substitute, Sum.elim_inl, Equiv.symm_apply_apply, hW, Fin.append_right, hz]
      rfl
  -- Stage four.
  set B := (bankCircuit members).eval interpretation S with hB
  have hbank (q : Fin (copies * 2 ^ (ℓ * b))) (r : Fin b) :
      B (finProdFinEquiv (q, r)) = slotResource bits C place f q r (directProductInput S q) := by
    rw [hB, bankCircuit, Circuit.eval_parallelFamily_apply, Circuit.eval_pi]
    exact congrFun (hmembers q r _) 0
  have h3 : (((bankCircuit members).comp (scatterCircuit t p w ℓ b s copies)).append
      (Circuit.id signature _)).eval interpretation W = Fin.append B W := by
    simp only [Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring, hB, hS]
    rfl
  -- Stage five.
  have hquery (i : Fin t) (j : Fin s) :
      substitute (Sum.inl ∘ Fin.append
        (Fin.natAdd _ ∘ incidenceKey t p w ℓ b s copies (finProdFinEquiv (i, j)))
        (fun k => Fin.natAdd (copies * 2 ^ (ℓ * b) * b) (Fin.natAdd (t * (s * (ℓ * b)))
          (Fin.castAdd (t * (p + w)) (finProdFinEquiv ((finProdFinEquiv.symm
            (finProdFinEquiv (i, j))).1, Fin.natAdd (ℓ * b) (Fin.natAdd (Nat.clog 2 copies) k)))))))
        (Fin.append B W) =
      Fin.append (Fin.append (indexBits (place (a i)).1) (pointBits bits (point i j)))
        (indexBits (place (a i)).2.2) := by
    funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [← hkey i j]
      simp only [substitute, Function.comp_apply, Sum.elim_inl, Fin.append_left,
        Fin.append_right]
    · simp only [substitute, Function.comp_apply, Sum.elim_inl, Fin.append_right, hW,
        Fin.append_left, Equiv.symm_apply_apply, hMapply, metadata]
  have hgather (i : Fin t) (j : Fin s) :
      directProductInput ((gatherCircuit t p w ℓ b s copies).eval interpretation (Fin.append B W))
        (finProdFinEquiv (i, j)) =
      fun _ => resource bits C place f (place (a i)).1 (point i j) (place (a i)).2.2 (z i) := by
    apply directProductInput_eval_batchOrCircuit
    · refine ⟨finProdFinEquiv (slotEquiv ((place (a i)).1, pointBits bits (point i j)),
        (place (a i)).2.2), ?_⟩
      rw [hquery]
      simp only [Equiv.symm_apply_apply, slotKey_slotEquiv]
      rfl
    · intro y hy
      obtain ⟨⟨q, r⟩, rfl⟩ := finProdFinEquiv.surjective y
      rw [hquery] at hy
      change Fin.append (slotKey (finProdFinEquiv.symm (finProdFinEquiv (q, r))).1)
        (indexBits (finProdFinEquiv.symm (finProdFinEquiv (q, r))).2) = _ at hy
      rw [Equiv.symm_apply_apply, append_eq_append_iff, ← slotKey_slotEquiv] at hy
      obtain rfl := slotKey_injective hy.1
      obtain rfl := indexBits_injective hy.2
      funext _
      simp only [substitute, Sum.elim_inl, Fin.append_left, hbank, hscatter, slotResource,
        Equiv.symm_apply_apply]
      rw [← pointEquiv_apply, Equiv.symm_apply_apply]
  rw [lineSums, recoveryCircuit, Circuit.eval_comp, Circuit.eval_comp, Circuit.eval_comp, h1, h2,
    h3]
  have hsum := sum_resource bits scalar (C := C) (place := place) (f := f) (a i) (z i) (hdirs i)
  rw [Fin.append_castAdd_natAdd] at hsum
  rw [directProduct, ← hsum]
  exact Finset.sum_congr rfl fun j _ => congrFun (hgather i j) 0

end Cslib.Circuits.Boolean.MassProduction.Pipeline
