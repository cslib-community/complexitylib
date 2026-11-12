/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CountingLeaf.Serialize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate

/-!
# Native counting-leaf evaluation from six physical fields

The first six tapes hold context, count digits, width digits, path, singleton carry selector and
index digits. All begin at cell zero. A physical serializer builds the encoded query, and a
native predicate runner evaluates it on fresh private tapes. Both phases, including destination
rewind, marker cleanup and host-input positioning, are charged. No serialized query is assumed.
-/

public section

namespace Cslib.CountingLeaf.Native

open Turing Turing.MultiTapeTM

/-- Physical length of the six source fields, including the carry selector. -/
@[expose] def size (q : RawInput) : ℕ :=
  q.context.length + q.count.length + q.width.length + q.path.length + 1 + q.bit.length

/-- Put the serializer's six sources first and its destination on the runner's virtual input. -/
def serializerTapes (k : ℕ) : Fin 7 ↪ Fin (6 + (k + 2)) where
  toFun := Fin.lastCases (Fin.natAdd 6 (Fin.natAdd k 0)) (Fin.castAdd (k + 2))
  inj' := by
    intro a b h
    cases a using Fin.lastCases with
    | last =>
      cases b using Fin.lastCases with
      | last => rfl
      | cast b =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
        exact False.elim (Fin.castAdd_ne_natAdd b (Fin.natAdd k 0) h.symm)
    | cast a =>
      cases b using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
        exact False.elim (Fin.castAdd_ne_natAdd a (Fin.natAdd k 0) h)
      | cast b =>
        simp only [Fin.lastCases_castSucc, Fin.castAdd_inj] at h
        exact congrArg Fin.castSucc h

/-- Source tapes keep their indices in the first block. -/
@[simp] theorem serializerTapes_source (k : ℕ) (i : Fin 6) :
    serializerTapes k i.castSucc = Fin.castAdd (k + 2) i := by
  change Fin.lastCases (motive := fun _ : Fin 7 => Fin (6 + (k + 2)))
    (Fin.natAdd 6 (Fin.natAdd k 0)) (Fin.castAdd (k + 2)) i.castSucc = _
  exact Fin.lastCases_castSucc i

/-- The serialized destination is the native runner's virtual input. -/
@[simp] theorem serializerTapes_query (k : ℕ) :
    serializerTapes k (Fin.last 6) = Fin.natAdd 6 (Fin.natAdd k 0) := by
  change Fin.lastCases (motive := fun _ : Fin 7 => Fin (6 + (k + 2)))
    (Fin.natAdd 6 (Fin.natAdd k 0)) (Fin.castAdd (k + 2))
    (Fin.last 6) = _
  exact Fin.lastCases_last

/-- Six source words at zero, followed by blank predicate scratch, query and marker tapes. -/
@[expose] def initial (k : ℕ) (input : List Bool) (q : RawInput) :
    Cfg (6 + (k + 2)) Bool Unit input :=
  ⟨none, 0, Fin.append (fun i => tapeOfList (Serialize.fields q i)) (fun _ _ => none),
    fun _ => 0, []⟩

/-- The sources are preserved at their right ends. The query remains serialized at its origin,
predicate scratch and marker are blank, and the result is emitted on the real output. -/
@[expose] def final (k : ℕ) (input : List Bool) (q : RawInput) (out : List Bool) :
    Cfg (6 + (k + 2)) Bool Unit input :=
  ⟨none, 0, Fin.append (fun i => tapeOfList (Serialize.fields q i))
      (fun i => tapeOfList (Function.update (fun _ => []) (Fin.natAdd k 0) (encRawInput q) i)),
    Fin.append (fun i => ((Serialize.fields q i).length : ℤ)) (fun _ => 0), out⟩

private theorem not_mem_serializerTapes {k : ℕ} (j : Fin (k + 2))
    (hj : j ≠ Fin.natAdd k 0) : Fin.natAdd 6 j ∉ Set.range (serializerTapes k) := by
  rintro ⟨i, hi⟩
  cases i using Fin.lastCases with
  | last =>
    change serializerTapes k (Fin.last 6) = Fin.natAdd 6 j at hi
    rw [serializerTapes_query] at hi
    apply hj
    apply Fin.ext
    have hv := congrArg (fun i : Fin (6 + (k + 2)) => i.val) hi
    change 6 + k = 6 + j.val at hv
    change j.val = k
    omega
  | cast i =>
    have he : Fin.castAdd (k + 2) i = Fin.natAdd 6 j := by simpa using hi
    exact Fin.castAdd_ne_natAdd i j he

private theorem serializer_initial (k : ℕ) (input : List Bool) (q : RawInput) :
    embed (serializerTapes k) (Serialize.initial input q) (fun _ _ => none) (fun _ => 0) =
      initial k input q := by
  apply Cfg.ext <;> try rfl
  · funext j x
    cases j using Fin.addCases with
    | left j =>
      have hp : partialInv (serializerTapes k) (Fin.castAdd (k + 2) j) = some j.castSucc :=
        by simpa only [serializerTapes_source] using
          partialInv_embed (serializerTapes k) j.castSucc
      simp [embed, hp, Serialize.initial, Serialize.stage, Serialize.prefixWord, tapesCfg, initial]
    | right j =>
      by_cases hj : j = Fin.natAdd k 0
      · subst j
        have hp := partialInv_embed (serializerTapes k) (Fin.last 6)
        rw [serializerTapes_query] at hp
        simp only [embed, hp, Serialize.initial, Serialize.stage, Serialize.prefixWord,
          tapesCfg, initial, Fin.lastCases_last]
        simp
      · simp [embed, partialInv_eq_none _ (not_mem_serializerTapes j hj), initial]
  · funext j
    cases hp : partialInv (serializerTapes k) j with
    | none => simp [embed, hp, initial]
    | some i =>
      cases i using Fin.lastCases with
      | last =>
        simp only [embed, hp, Serialize.initial, Serialize.stage, Serialize.prefixWord,
          tapesCfg, initial, Fin.lastCases_last]
        simp
      | cast i => simp [embed, hp, Serialize.initial, Serialize.stage, tapesCfg, initial]

private theorem serializer_final (k : ℕ) (input : List Bool) (q : RawInput) :
    embed (serializerTapes k) (Serialize.final input q) (fun _ _ => none) (fun _ => 0) =
      final k input q [] := by
  apply Cfg.ext <;> try rfl
  all_goals
    funext j
    cases j using Fin.addCases with
    | left j =>
      have hp : partialInv (serializerTapes k) (Fin.castAdd (k + 2) j) = some j.castSucc :=
        by simpa only [serializerTapes_source] using
          partialInv_embed (serializerTapes k) j.castSucc
      simp [embed, hp, Serialize.final, Serialize.finished, tapesCfg, final]
    | right j =>
      by_cases hj : j = Fin.natAdd k 0
      · subst j
        have hp := partialInv_embed (serializerTapes k) (Fin.last 6)
        rw [serializerTapes_query] at hp
        simp only [embed, hp, Serialize.final, Serialize.finished, tapesCfg, final,
          Fin.lastCases_last]
        simp
      · simp [embed, partialInv_eq_none _ (not_mem_serializerTapes j hj), final, hj]

/-- The runner reads only its private block; the six source fields lie outside its view. -/
theorem view_final (k : ℕ) (input : List Bool) (q : RawInput) (out : List Bool) :
    viewCfg (Fin.natAddEmb 6) (final k input q out) =
      WorkTapePredicate.config input (encRawInput q) out := by
  apply Cfg.ext <;> try rfl
  all_goals funext i; simp [viewCfg, final, WorkTapePredicate.config, tapesCfg]

/-- Physical serialization followed by the supplied native work-tape predicate runner. -/
noncomputable def machine {k : ℕ} {S : Type} (runner : MultiTapeTM (k + 2) Bool S) :=
  (Serialize.machine.extendTapes (serializerTapes k)).seq (runner.extendTapes (Fin.natAddEmb 6))

/-- Serialization and native evaluation compose on physical storage. This charges construction
of the framed query as well as the supplied runner's complete clock. -/
theorem runFrom_machine {k : ℕ} {S : Type} (runner : MultiTapeTM (k + 2) Bool S)
    (q : RawInput) (input : List Bool) (answer : Bool) (t : ℕ)
    (hr : runner.runFrom
      ((WorkTapePredicate.config input (encRawInput q)).withState (some runner.q₀)) t =
        (WorkTapePredicate.config input (encRawInput q) [answer]).withState none) :
    (machine runner).runFrom ((initial k input q).withState (some (machine runner).q₀))
      (2 * (encRawInput q).length + 5 + t) = (final k input q [answer]).withState none := by
  have hs := runFrom_map
    (embedHom Serialize.machine (serializerTapes k) (fun _ _ => none) (fun _ => 0))
    ((Serialize.initial input q).withState (some Serialize.machine.q₀))
    (2 * (encRawInput q).length + 5)
  rw [(Serialize.runsBetween input q []).1] at hs
  change (Serialize.machine.extendTapes (serializerTapes k)).runFrom
      ((embed (serializerTapes k) (Serialize.initial input q) (fun _ _ => none)
        (fun _ => 0)).withState (some Serialize.machine.q₀)) _ =
      (embed (serializerTapes k) (Serialize.final input q) (fun _ _ => none)
        (fun _ => 0)).withState none at hs
  rw [serializer_initial, serializer_final] at hs
  have hv : viewCfg (Fin.natAddEmb 6)
      ((final k input q []).withState (some runner.q₀)) =
      (WorkTapePredicate.config input (encRawInput q)).withState (some runner.q₀) := by
    change (viewCfg (Fin.natAddEmb 6) (final k input q [])).withState _ = _
    rw [view_final]
    rfl
  have hrun : (runner.extendTapes (Fin.natAddEmb 6)).runFrom
      ((final k input q []).withState (some runner.q₀)) t =
        (final k input q [answer]).withState none := by
    rw [runFrom_extendTapes, hv, hr]
    have he := embed_viewCfg (Fin.natAddEmb 6) (final k input q [answer])
    rw [view_final] at he
    exact congrArg (fun c => c.withState (none : Option S)) he
  exact ((RunsBetween.of_runFrom hs).seq (RunsBetween.of_runFrom hrun)).1

/-- Framing the physical source words has polynomial, in fact linear, encoded length. -/
theorem encodedLength_polyBounded : PolyBounded size (fun q => (encRawInput q).length) := by
  apply PolyBounded.of_forall_le 7 1
  intro q
  rw [length_encRawInput]
  simp only [pow_one, size]
  omega

/-- Every native polynomial-time predicate on raw queries runs from the six unencoded physical
fields on one finite machine. The clock is polynomial in their total length, including framing,
copying, rewinding and native evaluation. -/
theorem exists_of_polyTime {f : RawInput → Bool}
    (hf : ComputableInPolyTime f encRawInput encBool) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (6 + (k + 2)) Bool S)
      (c d : ℕ), ∀ (q : RawInput) (input : List Bool),
        tm.runFrom ((initial k input q).withState (some tm.q₀)) (c * (size q + 1) ^ d) =
          (final k input q [f q]).withState none := by
  obtain ⟨k, S, hS, runner, c, d, hr⟩ := WorkTapePredicate.exists_of_polyTime hf
  have ht : PolyBounded size
      (fun q => 2 * (encRawInput q).length + 5 + c * ((encRawInput q).length + 1) ^ d) :=
    (((PolyBounded.const 2).mul encodedLength_polyBounded).add (PolyBounded.const 5)).add
      ((PolyBounded.const c).mul
        ((encodedLength_polyBounded.add (PolyBounded.const 1)).pow d))
  obtain ⟨C, D, hbound⟩ := ht.exists_le
  refine ⟨k, _, inferInstance, machine runner, C, D, ?_⟩
  intro q input
  have hrun := runFrom_machine runner q input (f q) (c * ((encRawInput q).length + 1) ^ d)
    (hr q input)
  rw [runFrom_eq_of_halt _ _ (hbound q) (by rw [hrun]; rfl), hrun]

/-- Native counting-leaf evaluation from physical context, raw counters and path words. -/
theorem exists_counting (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (6 + (k + 2)) Bool S)
      (c d : ℕ), ∀ (q : RawInput) (input : List Bool),
        tm.runFrom ((initial k input q).withState (some tm.q₀)) (c * (size q + 1) ^ d) =
          (final k input q [runRaw predicate q]).withState none :=
  exists_of_polyTime (computableInPolyTime_runRaw predicate hp)

end Cslib.CountingLeaf.Native
