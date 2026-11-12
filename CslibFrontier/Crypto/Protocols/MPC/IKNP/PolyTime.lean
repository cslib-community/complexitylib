/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.IKNP
public import CslibFrontier.Crypto.Primitives.CorrelationRobust.Asymptotic
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Tactic.PPT
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Languages.Probabilistic.Oracle.Norm

/-!
# Polynomial-Time IKNP OT Extension

Word-level probabilistic polynomial-time realization of IKNP OT extension (`iknpProtocol`)
against a single batched base-OT oracle (`WordOracleComp Unit`), together with asymptotic
semi-honest privacy from a `CorrelationRobustHash`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.iknpWordOracle`, `iknpWordRun`: oracle-PPT and closed base-OT
  word-level realizations of IKNP OT extension.
* `Cslib.Crypto.Protocols.MPC.iknpSenderSimWord`, `iknpReceiverSimWord`: PPT word-level
  simulators matching `iknpSenderSim` and `iknpReceiverSim`.
* `Cslib.Crypto.Protocols.MPC.iknpWordReduction`: PPT correlation-robustness adversary induced
  by a word-level receiver distinguisher.

## Main results

* `Cslib.Crypto.Protocols.MPC.isOraclePPTOn_iknpWordOracle`, `isPPTOn_iknpWordRun`:
  uniform strict polynomial-time certificates.
* `Cslib.Crypto.Protocols.MPC.iknpWordRun_correctness`: every supported output matches the
  `batchOTAnswer` functionality.
* `Cslib.Crypto.Protocols.MPC.iknpWord_sender_advantage_zero`,
  `iknpWord_asymptotic_sender_private`: unconditional zero-advantage sender privacy.
* `Cslib.Crypto.Protocols.MPC.iknpWord_receiver_advantage_eq`,
  `iknpWord_asymptotic_receiver_private`: negligible receiver distinguishing advantage under
  `CorrelationRobustHash.IsCorrelationRobust`.

## References

* [Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*][IshaiKilianNissimPetrank2003]
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.BitString
open Cslib.Crypto
open Cslib.Crypto.CorrelationRobust
open Cslib.Probability
open Turing.MultiTapeTM

/-! ### Bit-string encodings and word-to-finite bridges -/

/-- Bit-string embedding of sender message pairs `[(m₀, m₁), ...]`. -/
@[expose] def encIKNPSenderPairs : List (List Bool × List Bool) ↪ List Bool :=
  encList (encPair encBits encBits)

/-- Bit-string embedding of a word-level IKNP input `(XWords, rWord)`. -/
@[expose] def encIKNPWordPair : (List (List Bool × List Bool) × List Bool) ↪ List Bool :=
  encPair encIKNPSenderPairs encBits

/-- Bit-string embedding of `(n, (XWords, rWord))`. -/
@[expose] def encIKNPWordInput : (ℕ × List (List Bool × List Bool) × List Bool) ↪ List Bool :=
  encPair encUnary encIKNPWordPair

/-- Raw word-level encoding of a sender view `(XWords, sWord, QWords)`. -/
@[expose] def encIKNPSenderViewRaw :
    (List (List Bool × List Bool) × List Bool × List (List Bool)) ↪ List Bool :=
  encPair encIKNPSenderPairs (encPair encBits (encList encBits))

/-- Raw word-level encoding of a receiver view `(rWord, TWords, YWords)`. -/
@[expose] def encIKNPReceiverViewRaw :
    (List Bool × List (List Bool) × List (List Bool × List Bool)) ↪ List Bool :=
  encPair encBits (encPair (encList encBits) encIKNPSenderPairs)

/-- Bit-string embedding of `(senderView_w, receiverView_w, out_w)`. -/
@[expose] def encIKNPRunOut : (List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

/-- Decode a sender message list into `Fin m → Bool → BitString ℓ`. -/
@[expose] def decodeIKNPSender (m ℓ : ℕ) (XWords : List (List Bool × List Bool)) :
    Fin m → Bool → BitString ℓ :=
  fun j b =>
    BitString.ofList ℓ (if b then (XWords.getD j ([], [])).2 else (XWords.getD j ([], [])).1)

/-- Decode word inputs `(XWords, rWord)` into a two-party query to `batchOTSpec m (BitString ℓ)`. -/
@[expose] def decodeIKNPInput (m ℓ : ℕ) (XWords : List (List Bool × List Bool))
    (rWord : List Bool) :
    (i : Fin 2) → (batchOTSpec m (BitString ℓ)).Query () i :=
  Fin.cases (decodeIKNPSender m ℓ XWords) (fun _ => BitString.ofList m rWord)

/-- Encode a finite table `X : Fin m → Bool → BitString ℓ` into a list of bit-string pairs. -/
@[expose] def encodeIKNPSender {m ℓ : ℕ} (X : Fin m → Bool → BitString ℓ) :
    List (List Bool × List Bool) :=
  List.ofFn fun j => (List.ofFn (X j false), List.ofFn (X j true))

/-- Encode finite sender-view components `(X, s, Q)` into a bit string. -/
@[expose] def encodeIKNPSenderViewWord {m κ ℓ : ℕ} (X : Fin m → Bool → BitString ℓ)
    (s : BitString κ) (Q : Fin κ → BitString m) : List Bool :=
  encIKNPSenderViewRaw
    (encodeIKNPSender X, List.ofFn s, List.ofFn fun i => List.ofFn (Q i))

/-- Encode finite receiver-view components `(r, T, Y)` into a bit string. -/
@[expose] def encodeIKNPReceiverViewWord {m κ ℓ : ℕ} (r : BitString m)
    (T : Fin m → BitString κ) (Y : Fin m → Bool → BitString ℓ) : List Bool :=
  encIKNPReceiverViewRaw
    (List.ofFn r, List.ofFn fun j => List.ofFn (T j), encodeIKNPSender Y)

/-- Encode finite receiver outputs `z : Fin m → BitString ℓ` into a bit string. -/
@[expose] def encodeIKNPOutputsWord {m ℓ : ℕ} (z : Fin m → BitString ℓ) : List Bool :=
  encList encBits (List.ofFn fun j => List.ofFn (z j))

private theorem encodeIKNPSender_injective {m ℓ : ℕ} :
    Function.Injective (encodeIKNPSender (m := m) (ℓ := ℓ)) := by
  intro X₁ X₂ h
  funext j b
  have hrow := congrArg (fun l => l[j.val]?) h
  simp only [encodeIKNPSender, List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.some.injEq,
    Prod.mk.injEq] at hrow
  cases b
  · exact List.ofFn_injective hrow.1
  · exact List.ofFn_injective hrow.2

/-- Word encoding of finite IKNP sender views is injective. -/
theorem encodeIKNPSenderViewWord_injective {m κ ℓ : ℕ} :
    Function.Injective (fun p :
      (Fin m → Bool → BitString ℓ) × BitString κ × (Fin κ → BitString m) =>
        let (X, s, Q) := p
        encodeIKNPSenderViewWord X s Q) := by
  rintro ⟨X₁, s₁, Q₁⟩ ⟨X₂, s₂, Q₂⟩ h
  have hraw := encIKNPSenderViewRaw.injective h
  simp only [Prod.mk.injEq] at hraw
  rcases hraw with ⟨hX, hs, hQ⟩
  refine Prod.ext (encodeIKNPSender_injective hX) (Prod.ext (List.ofFn_injective hs) ?_)
  funext i
  have hrow := congrArg (fun l => l[i.val]?) hQ
  simp only [List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.some.injEq] at hrow
  exact List.ofFn_injective hrow

/-- Word encoding of finite IKNP receiver views is injective. -/
theorem encodeIKNPReceiverViewWord_injective {m κ ℓ : ℕ} :
    Function.Injective (fun p :
      BitString m × (Fin m → BitString κ) × (Fin m → Bool → BitString ℓ) =>
        let (r, T, Y) := p
        encodeIKNPReceiverViewWord r T Y) := by
  rintro ⟨r₁, T₁, Y₁⟩ ⟨r₂, T₂, Y₂⟩ h
  have hraw := encIKNPReceiverViewRaw.injective h
  simp only [Prod.mk.injEq] at hraw
  rcases hraw with ⟨hr, hT, hY⟩
  refine Prod.ext (List.ofFn_injective hr) (Prod.ext ?_ (encodeIKNPSender_injective hY))
  funext j
  have hrow := congrArg (fun l => l[j.val]?) hT
  simp only [List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.some.injEq] at hrow
  exact List.ofFn_injective hrow

/-- Word encoding of finite IKNP receiver outputs is injective. -/
theorem encodeIKNPOutputsWord_injective {m ℓ : ℕ} :
    Function.Injective (encodeIKNPOutputsWord (m := m) (ℓ := ℓ)) := by
  intro z₁ z₂ h
  have hlist := (encList encBits).injective h
  funext j
  have hrow := congrArg (fun l => l[j.val]?) hlist
  simp only [List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.some.injEq] at hrow
  exact List.ofFn_injective hrow

/-- Pad/truncate sender message pairs to `m` pairs of width `ℓ`. -/
@[expose] def normalizeIKNPSenderPairs (m ℓ : ℕ) (XWords : List (List Bool × List Bool)) :
    List (List Bool × List Bool) :=
  (List.range m).map fun j =>
    let p := XWords.getD j ([], [])
    (BitString.listRow ℓ 0 p.1, BitString.listRow ℓ 0 p.2)

/-- Pad/truncate a receiver choice word to width `m`. -/
@[expose] def normalizeIKNPReceiverBits (m : ℕ) (rWord : List Bool) : List Bool :=
  BitString.listRow m 0 rWord

/-- Canonical dimension invariant on word-level IKNP inputs at security parameter `n`. -/
@[expose] def ValidIKNPInput (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) : Prop :=
  XWords.length = H.queries n ∧
  (∀ p ∈ XWords, p.1.length = H.outLength n ∧ p.2.length = H.outLength n) ∧
  rWord.length = H.queries n

theorem normalizeIKNPSenderPairs_eq_encode (m ℓ : ℕ) (XWords : List (List Bool × List Bool)) :
    normalizeIKNPSenderPairs m ℓ XWords = encodeIKNPSender (decodeIKNPSender m ℓ XWords) := by
  apply List.ext_getElem (by simp [normalizeIKNPSenderPairs, encodeIKNPSender])
  intro j hj hj'
  simp only [normalizeIKNPSenderPairs, List.length_map, List.length_range] at hj
  simp only [normalizeIKNPSenderPairs, encodeIKNPSender, decodeIKNPSender,
    List.getElem_map, List.getElem_range, List.getElem_ofFn,
    BitString.listRow_zero, Bool.false_eq_true, ↓reduceIte]

theorem normalizeIKNPReceiverBits_eq_ofFn (m : ℕ) (rWord : List Bool) :
    normalizeIKNPReceiverBits m rWord = List.ofFn (BitString.ofList m rWord) :=
  BitString.listRow_zero m rWord

theorem normalizeIKNPSenderPairs_of_valid {H : CorrelationRobustHash} {n : ℕ}
    {XWords : List (List Bool × List Bool)} {rWord : List Bool}
    (hvalid : ValidIKNPInput H n XWords rWord) :
    normalizeIKNPSenderPairs (H.queries n) (H.outLength n) XWords = XWords := by
  rcases hvalid with ⟨hlen, hmem, _⟩
  apply List.ext_getElem (by simp [normalizeIKNPSenderPairs, hlen])
  intro j hj hj'
  simp only [normalizeIKNPSenderPairs, List.length_map, List.length_range] at hj
  have hget : XWords.getD j ([], []) = XWords[j]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < XWords.length)]
  have hmemj := hmem (XWords[j]'(by omega)) (List.getElem_mem (by omega))
  simp only [normalizeIKNPSenderPairs, List.getElem_map, List.getElem_range, hget,
    BitString.listRow_zero, BitString.ofFn_ofList hmemj.1, BitString.ofFn_ofList hmemj.2]

theorem normalizeIKNPReceiverBits_of_valid {H : CorrelationRobustHash} {n : ℕ}
    {XWords : List (List Bool × List Bool)} {rWord : List Bool}
    (hvalid : ValidIKNPInput H n XWords rWord) :
    normalizeIKNPReceiverBits (H.queries n) rWord = rWord := by
  rcases hvalid with ⟨_, _, hr⟩
  simp only [normalizeIKNPReceiverBits, BitString.listRow_zero, BitString.ofFn_ofList hr]

/-! ### Base-OT oracle word encoding and closed handler -/

/-- Column `i` of `T` (as `m` rows of width `κ`), XORed with `r` when `b = true`. -/
@[expose] def iknpColumnWord (m κ : ℕ) (rWord TFlat : List Bool) (i : ℕ) (b : Bool) :
    List Bool :=
  (List.range m).map fun j => TFlat.getD (j * κ + i) false ^^ (b && rWord.getD j false)

@[simp] theorem length_iknpColumnWord (m κ : ℕ) (rWord TFlat : List Bool) (i : ℕ) (b : Bool) :
    (iknpColumnWord m κ rWord TFlat i b).length = m := by
  simp [iknpColumnWord]

/-- Encoded batched base-OT query `(m, (sWord, (t0Flat, t1Flat)))`. -/
@[expose] def batchOTWordQuery (m κ : ℕ) (rWord TFlat sWord : List Bool) : List Bool :=
  encPair encUnary (encPair encBits (encPair encBits encBits))
    (m, sWord,
      (List.range κ).flatMap (fun i => iknpColumnWord m κ rWord TFlat i false),
      (List.range κ).flatMap (fun i => iknpColumnWord m κ rWord TFlat i true))

/-- Deterministic word evaluation of a batched `m`-bit OT query. -/
@[expose] def batchOTWordEval (q : List Bool) : List Bool :=
  let m := (unframe q).length
  let rest := dropFrame q
  let s := unframe rest
  let t0 := unframe (dropFrame rest)
  let t1 := dropFrame (dropFrame rest)
  (List.range s.length).flatMap fun i =>
    if s.getD i false then BitString.listRow m i t1 else BitString.listRow m i t0

/-- Ideal memoryless batched base-OT word oracle handler. -/
@[expose] noncomputable def batchOTWordHandler (q : Unit × List Bool) : ProbComp (List Bool) :=
  pure (batchOTWordEval q.2)

private theorem computably_encode_encIKNPSenderPairs :
    ComputableInPolyTime (fun x => encIKNPSenderPairs x) encIKNPSenderPairs encBits :=
  ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.encode encIKNPSenderPairs)

@[fun_prop]
private theorem computably_encode_encIKNPSenderPairs_comp {α : Type} {input : α ↪ List Bool}
    {f : α → List (List Bool × List Bool)}
    (hf : ComputableInPolyTime f input encIKNPSenderPairs) :
    ComputableInPolyTime (fun a => encIKNPSenderPairs (f a)) input encBits :=
  computably_encode_encIKNPSenderPairs.comp hf

@[fun_prop]
private theorem computably_encode_encIKNPSenderViewRaw {α : Type} {input : α ↪ List Bool}
    {f : α → List (List Bool × List Bool) × List Bool × List (List Bool)}
    (hf : ComputableInPolyTime f input encIKNPSenderViewRaw) :
    ComputableInPolyTime (fun a => encIKNPSenderViewRaw (f a)) input encBits :=
  (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.encode encIKNPSenderViewRaw)).comp hf

@[fun_prop]
private theorem computably_encode_encIKNPReceiverViewRaw {α : Type} {input : α ↪ List Bool}
    {f : α → List Bool × List (List Bool) × List (List Bool × List Bool)}
    (hf : ComputableInPolyTime f input encIKNPReceiverViewRaw) :
    ComputableInPolyTime (fun a => encIKNPReceiverViewRaw (f a)) input encBits :=
  (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.encode encIKNPReceiverViewRaw)).comp
    hf

@[fun_prop]
private theorem computably_encode_encListBits {α : Type} {input : α ↪ List Bool}
    {f : α → List (List Bool)}
    (hf : ComputableInPolyTime f input (encList encBits)) :
    ComputableInPolyTime (fun a => encList encBits (f a)) input encBits :=
  (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.encode (encList encBits))).comp hf

@[fun_prop]
private theorem computably_encode_batchOTQuery {α : Type} {input : α ↪ List Bool}
    {f : α → ℕ × List Bool × List Bool × List Bool}
    (hf : ComputableInPolyTime f input
      (encPair encUnary (encPair encBits (encPair encBits encBits)))) :
    ComputableInPolyTime
      (fun a => encPair encUnary (encPair encBits (encPair encBits encBits)) (f a))
      input encBits :=
  (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.encode
      (encPair encUnary (encPair encBits (encPair encBits encBits))))).comp hf

@[fun_prop]
private theorem computably_iknpColumnWord {α : Type} {input : α ↪ List Bool}
    {m κ : α → ℕ} {rWord TFlat : α → List Bool} {i : α → ℕ} {b : α → Bool}
    (hm : ComputableInPolyTime m input encUnary)
    (hκ : ComputableInPolyTime κ input encUnary)
    (hr : ComputableInPolyTime rWord input encBits)
    (hT : ComputableInPolyTime TFlat input encBits)
    (hi : ComputableInPolyTime i input encUnary)
    (hb : ComputableInPolyTime b input encBool) :
    ComputableInPolyTime
      (fun a => iknpColumnWord (m a) (κ a) (rWord a) (TFlat a) (i a) (b a))
      input encBits := by
  unfold iknpColumnWord
  fun_prop

@[fun_prop]
private theorem computably_normalizeIKNPSenderPairs {α : Type} {input : α ↪ List Bool}
    {m ℓ : α → ℕ} {XWords : α → List (List Bool × List Bool)}
    (hm : ComputableInPolyTime m input encUnary)
    (hℓ : ComputableInPolyTime ℓ input encUnary)
    (hX : ComputableInPolyTime XWords input encIKNPSenderPairs) :
    ComputableInPolyTime (fun a => normalizeIKNPSenderPairs (m a) (ℓ a) (XWords a))
      input encIKNPSenderPairs := by
  unfold normalizeIKNPSenderPairs encIKNPSenderPairs
  fun_prop

@[fun_prop]
private theorem computably_normalizeIKNPReceiverBits {α : Type} {input : α ↪ List Bool}
    {m : α → ℕ} {rWord : α → List Bool}
    (hm : ComputableInPolyTime m input encUnary)
    (hr : ComputableInPolyTime rWord input encBits) :
    ComputableInPolyTime (fun a => normalizeIKNPReceiverBits (m a) (rWord a)) input encBits := by
  unfold normalizeIKNPReceiverBits
  fun_prop

private theorem iknpColumnWord_eq_ofFn {m κ : ℕ} (r : BitString m)
    (T : Fin m → BitString κ) (rWord TFlat : List Bool)
    (hr : r = BitString.ofList m rWord)
    (hT : T = BitString.block (BitString.ofList (m * κ) TFlat))
    (i : Fin κ) (b : Bool) :
    iknpColumnWord m κ rWord TFlat i.val b = List.ofFn (iknpColumns r T i b) := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp only [length_iknpColumnWord] at hj
  have hTji : T ⟨j, hj⟩ i = TFlat.getD (j * κ + i.val) false := by
    have h1 : BitString.listRow κ j TFlat = List.ofFn (T ⟨j, hj⟩) := by
      simpa [hT] using BitString.listRow_eq_ofFn κ ⟨j, hj⟩ TFlat
    have h2 := BitString.getD_listRow (width := κ) (row := j) (word := TFlat) i.isLt
    have h3 := congrArg (fun l : List Bool => l.getD i.val false) h1
    simpa [List.getD_eq_getElem?_getD, i.isLt] using h3.symm.trans h2
  have hrj : r ⟨j, hj⟩ = rWord.getD j false := by
    simp [hr, BitString.ofList, List.getD_eq_getElem?_getD]
  simp only [iknpColumnWord, List.getElem_map, List.getElem_range, List.getElem_ofFn,
    iknpColumns, Bool.add_eq_xor, hTji, hrj]

private theorem batchOTWordEval_query {m κ : ℕ} (rWord TFlat sWord : List Bool)
    (hs : sWord.length = κ) :
    batchOTWordEval (batchOTWordQuery m κ rWord TFlat sWord) =
      (List.range κ).flatMap fun i =>
        iknpColumnWord m κ rWord TFlat i (sWord.getD i false) := by
  simp only [batchOTWordEval, batchOTWordQuery, encPair_apply, unframe_frame_append,
    dropFrame_frame_append, encUnary_apply, encBits_apply, List.length_replicate, hs]
  refine List.flatMap_congr fun i hi => ?_
  have hik : i < κ := List.mem_range.mp hi
  have hside (b : Bool) :
      BitString.listRow m i ((List.range κ).flatMap fun r =>
          iknpColumnWord m κ rWord TFlat r b) =
        iknpColumnWord m κ rWord TFlat i b := by
    have hrow := BitString.listRow_flatMap_append
      (width := m)
      (fun r => iknpColumnWord m κ rWord TFlat r b)
      (List.range κ)
      (fun r _ => length_iknpColumnWord m κ rWord TFlat r b)
      [] i (by simp only [List.length_range, hik])
    simpa only [List.append_nil, List.getElem_range] using hrow
  cases hsi : sWord.getD i false
  · simpa using hside false
  · simpa using hside true

private theorem length_batchOTWordEval_query {m κ : ℕ} (rWord TFlat sWord : List Bool)
    (hs : sWord.length = κ) :
    (batchOTWordEval (batchOTWordQuery m κ rWord TFlat sWord)).length = κ * m := by
  rw [batchOTWordEval_query rWord TFlat sWord hs, List.length_flatMap]
  simp only [length_iknpColumnWord, List.map_const', List.length_range, List.sum_replicate,
    smul_eq_mul]

private theorem batchOTAnswer_decodeIKNPInput (m ℓ : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) (j : Fin m) :
    batchOTAnswer (decodeIKNPInput m ℓ XWords rWord) 1 j =
      decodeIKNPSender m ℓ XWords j (BitString.ofList m rWord j) := by
  have hb : batchOTAnswer (decodeIKNPInput m ℓ XWords rWord) 1 =
      fun j => decodeIKNPInput m ℓ XWords rWord 0 j
        (decodeIKNPInput m ℓ XWords rWord 1 j) :=
    Fin.cases_succ (motive := fun i => (batchOTSpec m (BitString ℓ)).Answer () i) 0
  have hd0 : decodeIKNPInput m ℓ XWords rWord 0 = decodeIKNPSender m ℓ XWords :=
    Fin.cases_zero
  have hd1 : decodeIKNPInput m ℓ XWords rWord 1 = BitString.ofList m rWord :=
    Fin.cases_succ (motive := fun i => (batchOTSpec m (BitString ℓ)).Query () i) 0
  rw [congrFun hb j, hd0, hd1]

@[fun_prop]
private theorem computably_batchOTWordQuery {α : Type} {input : α ↪ List Bool}
    {m κ : α → ℕ} {rWord TFlat sWord : α → List Bool}
    (hm : ComputableInPolyTime m input encUnary)
    (hκ : ComputableInPolyTime κ input encUnary)
    (hr : ComputableInPolyTime rWord input encBits)
    (hT : ComputableInPolyTime TFlat input encBits)
    (hs : ComputableInPolyTime sWord input encBits) :
    ComputableInPolyTime
      (fun a => batchOTWordQuery (m a) (κ a) (rWord a) (TFlat a) (sWord a)) input encBits := by
  unfold batchOTWordQuery
  have h0 : ComputableInPolyTime
      (fun a => (List.range (κ a)).flatMap fun i =>
        iknpColumnWord (m a) (κ a) (rWord a) (TFlat a) i false) input encBits :=
    ComputableInPolyTime.flatMapToBitsWithInput (ComputableInPolyTime.range.comp hκ)
      (by fun_prop)
  have h1 : ComputableInPolyTime
      (fun a => (List.range (κ a)).flatMap fun i =>
        iknpColumnWord (m a) (κ a) (rWord a) (TFlat a) i true) input encBits :=
    ComputableInPolyTime.flatMapToBitsWithInput (ComputableInPolyTime.range.comp hκ)
      (by fun_prop)
  exact computably_encode_batchOTQuery (hm.prod (hs.prod (h0.prod h1)))

@[fun_prop]
private theorem computably_unframe {α : Type} {input : α ↪ List Bool}
    {w : α → List Bool} (hw : ComputableInPolyTime w input encBits) :
    ComputableInPolyTime (fun a => Turing.MultiTapeTM.unframe (w a)) input encBits :=
  (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unframe).comp hw

@[fun_prop]
private theorem computably_dropFrame {α : Type} {input : α ↪ List Bool}
    {w : α → List Bool} (hw : ComputableInPolyTime w input encBits) :
    ComputableInPolyTime (fun a => Turing.MultiTapeTM.dropFrame (w a)) input encBits :=
  (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.dropFrame).comp hw

@[fun_prop]
private theorem computably_batchOTWordEval :
    ComputableInPolyTime batchOTWordEval encBits encBits := by
  unfold batchOTWordEval
  exact ComputableInPolyTime.flatMapToBitsWithInput
    (ComputableInPolyTime.range.comp (by fun_prop)) (by fun_prop)

/-! ### Oracle and closed word-level IKNP execution -/

/-- Shared deterministic postprocessing mapping `(n, XWords, rWord, sWord, tFlat, qFlat)` to the
encoded IKNP `(senderView, receiverView, output)` triple. -/
def iknpWordPost (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord sWord tFlat qFlat : List Bool) :
    List Bool × List Bool × List Bool :=
  let κ := H.keyLength n
  let m := H.queries n
  let ℓ := H.outLength n
  let qRows := BitString.listRows κ m qFlat
  let tRows := BitString.listRows m κ tFlat
  let yWords := (List.range m).map fun j =>
    let qRow := (List.range κ).map fun i => (qRows.getD i []).getD j false
    let p := XWords.getD j ([], [])
    (BitString.listXor ℓ [BitString.listRow ℓ 0 p.1, H.eval n j qRow],
      BitString.listXor ℓ [BitString.listRow ℓ 0 p.2,
        H.eval n j (BitString.listXor κ [qRow, sWord])])
  let zWords := (List.range m).map fun j =>
    let y := yWords.getD j ([], [])
    let ySel := if rWord.getD j false then y.2 else y.1
    BitString.listXor ℓ [ySel, H.eval n j (tRows.getD j [])]
  let sv := encIKNPSenderViewRaw (normalizeIKNPSenderPairs m ℓ XWords, sWord, qRows)
  let rv := encIKNPReceiverViewRaw (normalizeIKNPReceiverBits m rWord, tRows, yWords)
  let ov := encList encBits zWords
  (sv, rv, ov)

@[fun_prop]
private theorem computably_iknpWordPost (H : CorrelationRobustHash) {α : Type}
    {input : α ↪ List Bool} {n : α → ℕ} {XWords : α → List (List Bool × List Bool)}
    {rWord sWord tFlat qFlat : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hX : ComputableInPolyTime XWords input encIKNPSenderPairs)
    (hr : ComputableInPolyTime rWord input encBits)
    (hs : ComputableInPolyTime sWord input encBits)
    (ht : ComputableInPolyTime tFlat input encBits)
    (hq : ComputableInPolyTime qFlat input encBits) :
    ComputableInPolyTime
      (fun a => iknpWordPost H (n a) (XWords a) (rWord a) (sWord a) (tFlat a) (qFlat a))
      input encIKNPRunOut := by
  unfold iknpWordPost encIKNPRunOut
  fun_prop

/-- Oracle-PPT word-level IKNP OT extension calling one batched `batchOT` base-OT oracle. -/
noncomputable def iknpWordOracle (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    WordOracleComp Unit (List Bool × List Bool × List Bool) := do
  let κ := H.keyLength n
  let m := H.queries n
  let sWord ← ProbOracleComp.sample (BitString.sampleList κ)
  let tFlat ← ProbOracleComp.sample (BitString.sampleList (m * κ))
  let qFlat ← List.take (κ * m) <$>
    ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), batchOTWordQuery m κ rWord tFlat sWord)
  return iknpWordPost H n XWords rWord sWord tFlat qFlat

/-- `iknpWordOracle` runs in uniform strict oracle probabilistic polynomial time. -/
theorem isOraclePPTOn_iknpWordOracle (H : CorrelationRobustHash) :
    IsOraclePPTOn encIKNPWordInput encIKNPRunOut
      (fun p => let q := p.2; iknpWordOracle H p.1 q.1 q.2) := by
  have hsSample : IsOraclePPTOn (Operation := Unit) encIKNPWordInput encBits
      (fun p => ProbOracleComp.sample (BitString.sampleList (H.keyLength p.1))) :=
    (ComputableInPolyTime.sampleList
      (by unfold encIKNPWordInput; fun_prop)).isOraclePPTOn
  have htSample : IsOraclePPTOn (Operation := Unit) (encPair encIKNPWordInput encBits) encBits
      (fun p => ProbOracleComp.sample
        (BitString.sampleList (H.queries p.1.1 * H.keyLength p.1.1))) :=
    (ComputableInPolyTime.sampleList
      (by unfold encIKNPWordInput; fun_prop)).isOraclePPTOn
  have hqQuery : IsOraclePPTOn (Operation := Unit)
      (encPair (encPair encIKNPWordInput encBits) encBits) encBits
      (fun p => List.take (H.keyLength p.1.1.1 * H.queries p.1.1.1) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), batchOTWordQuery (H.queries p.1.1.1) (H.keyLength p.1.1.1)
            p.1.1.2.2 p.2 p.1.2)) :=
    IsOraclePPTOn.query_take' ()
      (by unfold encIKNPWordInput encIKNPWordPair; fun_prop)
      (by unfold encIKNPWordInput encIKNPWordPair; fun_prop)
  have htail : IsOraclePPTOn (Operation := Unit)
      (encPair (encPair encIKNPWordInput encBits) encBits) encIKNPRunOut
      (fun p => do
        let qFlat ← List.take (H.keyLength p.1.1.1 * H.queries p.1.1.1) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), batchOTWordQuery (H.queries p.1.1.1) (H.keyLength p.1.1.1)
              p.1.1.2.2 p.2 p.1.2)
        return iknpWordPost H p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2 qFlat) := by
    simpa only [bind_pure_comp] using hqQuery.map_with'
      (f := fun p qFlat => iknpWordPost H p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2 qFlat)
      (by unfold encIKNPWordInput encIKNPWordPair; fun_prop)
  exact hsSample.bind_with (htSample.bind_with htail)

/-- Closed `ProbComp` realization of word-level IKNP using `batchOTWordEval`. -/
noncomputable def iknpWordClosed (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp (List Bool × List Bool × List Bool) := do
  let κ := H.keyLength n
  let m := H.queries n
  let sWord ← BitString.sampleList κ
  let tFlat ← BitString.sampleList (m * κ)
  let qFlat := batchOTWordEval (batchOTWordQuery m κ rWord tFlat sWord)
  return iknpWordPost H n XWords rWord sWord tFlat qFlat

/-- Closed word-level IKNP protocol obtained by instantiating the base-OT oracle with
`batchOTWordHandler`. -/
noncomputable def iknpWordRun (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp (List Bool × List Bool × List Bool) :=
  OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin batchOTWordHandler)
    (iknpWordOracle H n XWords rWord)

theorem eval_iknpWordRun_eq_closed (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp.eval (iknpWordRun H n XWords rWord) =
      ProbComp.eval (iknpWordClosed H n XWords rWord) := by
  rw [iknpWordRun, ProbOracleComp.eval_interpret_eq_evalWith]
  simp only [iknpWordOracle, iknpWordClosed, batchOTWordHandler,
    OracleComp.evalWith_bind, OracleComp.evalWith_map, OracleComp.evalWith_pure,
    ProbOracleComp.evalWith_sumHandler_unifOracle_sample,
    ProbOracleComp.evalWith_sumHandler_query,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_map, PMF.pure_bind]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun sWord hsWord => ?_
  have hsLen : sWord.length = H.keyLength n :=
    BitString.length_of_mem_support_uniformList (by simpa [BitString.eval_sampleList] using hsWord)
  refine congrArg (PMF.bind _) (funext fun tFlat => ?_)
  have htake :
      List.take (H.keyLength n * H.queries n)
          (batchOTWordEval (batchOTWordQuery (H.queries n) (H.keyLength n) rWord tFlat sWord)) =
        batchOTWordEval (batchOTWordQuery (H.queries n) (H.keyLength n) rWord tFlat sWord) :=
    List.take_of_length_le (length_batchOTWordEval_query rWord tFlat sWord hsLen).le
  rw [htake]

/-- `iknpWordRun` runs in uniform strict probabilistic polynomial time. -/
theorem isPPTOn_iknpWordRun (H : CorrelationRobustHash) :
    IsPPTOn encIKNPWordInput encIKNPRunOut (fun p => iknpWordRun H p.1 p.2.1 p.2.2) := by
  have hsSample : IsPPTOn encIKNPWordInput encBits
      (fun p => BitString.sampleList (H.keyLength p.1)) :=
    ComputableInPolyTime.sampleList (by unfold encIKNPWordInput; fun_prop)
  have htSample : IsPPTOn (encPair encIKNPWordInput encBits) encBits
      (fun p => BitString.sampleList (H.queries p.1.1 * H.keyLength p.1.1)) :=
    ComputableInPolyTime.sampleList (by unfold encIKNPWordInput; fun_prop)
  have hpostComp : ComputableInPolyTime
      (fun pair : ((ℕ × List (List Bool × List Bool) × List Bool) × List Bool) × List Bool =>
        iknpWordPost H pair.1.1.1 pair.1.1.2.1 pair.1.1.2.2 pair.1.2 pair.2
          (batchOTWordEval (batchOTWordQuery (H.queries pair.1.1.1) (H.keyLength pair.1.1.1)
            pair.1.1.2.2 pair.2 pair.1.2)))
      (encPair (encPair encIKNPWordInput encBits) encBits) encIKNPRunOut := by
    unfold encIKNPWordInput encIKNPWordPair
    fun_prop
  have hclosed : IsPPTOn encIKNPWordInput encIKNPRunOut
      (fun p => iknpWordClosed H p.1 p.2.1 p.2.2) :=
    hsSample.bind_with (htSample.bind_with hpostComp.tidy.isPPTOn)
  exact hclosed.congr fun p => (eval_iknpWordRun_eq_closed H p.1 p.2.1 p.2.2).symm

private theorem iknpWordClosed_body_eq (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool)
    {sWord tFlat : List Bool} (hsLen : sWord.length = H.keyLength n) :
    let κ := H.keyLength n
    let m := H.queries n
    let ℓ := H.outLength n
    let qFlat := batchOTWordEval (batchOTWordQuery m κ rWord tFlat sWord)
    let qRows := BitString.listRows κ m qFlat
    let tRows := BitString.listRows m κ tFlat
    let yWords := (List.range m).map fun j =>
      let qRow := (List.range κ).map fun i => (qRows.getD i []).getD j false
      let p := XWords.getD j ([], [])
      (BitString.listXor ℓ [BitString.listRow ℓ 0 p.1, H.eval n j qRow],
        BitString.listXor ℓ [BitString.listRow ℓ 0 p.2,
          H.eval n j (BitString.listXor κ [qRow, sWord])])
    let zWords := (List.range m).map fun j =>
      let y := yWords.getD j ([], [])
      let ySel := if rWord.getD j false then y.2 else y.1
      BitString.listXor ℓ [ySel, H.eval n j (tRows.getD j [])]
    let sv := encIKNPSenderViewRaw (normalizeIKNPSenderPairs m ℓ XWords, sWord, qRows)
    let rv := encIKNPReceiverViewRaw (normalizeIKNPReceiverBits m rWord, tRows, yWords)
    let ov := encList encBits zWords
    (sv, rv, ov) =
      let s := BitString.ofList κ sWord
      let T := BitString.block (BitString.ofList (m * κ) tFlat)
      let X := decodeIKNPSender m ℓ XWords
      let r := BitString.ofList m rWord
      let Q := fun i => iknpColumns r T i (s i)
      (encodeIKNPSenderViewWord X s Q,
        encodeIKNPReceiverViewWord r T (iknpMasked (H.toFinite n) X s Q),
        encodeIKNPOutputsWord (batchOTAnswer (decodeIKNPInput m ℓ XWords rWord) 1)) := by
  intro κ m ℓ qFlat qRows tRows yWords zWords sv rv ov
  set s := BitString.ofList κ sWord
  set T := BitString.block (BitString.ofList (m * κ) tFlat)
  set X := decodeIKNPSender m ℓ XWords
  set r := BitString.ofList m rWord
  set Q := fun i : Fin κ => iknpColumns r T i (s i)
  have hqFlat :
      qFlat = (List.range κ).flatMap fun i =>
        iknpColumnWord m κ rWord tFlat i (sWord.getD i false) :=
    batchOTWordEval_query rWord tFlat sWord hsLen
  have hqRows : qRows = List.ofFn fun i : Fin κ => List.ofFn (Q i) := by
    apply List.ext_getElem (by simp [qRows])
    intro i hi hi'
    simp only [qRows, BitString.length_listRows] at hi
    simp only [qRows, BitString.listRows, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hrow := BitString.listRow_flatMap_append
      (width := m)
      (fun u => iknpColumnWord m κ rWord tFlat u (sWord.getD u false))
      (List.range κ)
      (fun u _ => length_iknpColumnWord m κ rWord tFlat u (sWord.getD u false))
      [] i (by simpa using hi)
    have hqRowEq : BitString.listRow m i qFlat =
        iknpColumnWord m κ rWord tFlat i (sWord.getD i false) := by
      simpa [hqFlat] using hrow
    have hsi : sWord.getD i false = s ⟨i, hi⟩ := by
      simp [s, BitString.ofList, List.getD_eq_getElem?_getD]
    rw [hqRowEq, hsi]
    exact iknpColumnWord_eq_ofFn r T rWord tFlat rfl rfl ⟨i, hi⟩ (s ⟨i, hi⟩)
  have hqRow_fn (j : Fin m) :
      ((List.range κ).map fun i => (qRows.getD i []).getD j.val false) =
        List.ofFn (iknpRows Q j) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, iknpRows, hqRows,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some,
      j.isLt]
  have hyWords : yWords = encodeIKNPSender (iknpMasked (H.toFinite n) X s Q) := by
    apply List.ext_getElem (by simp [yWords, encodeIKNPSender, m])
    intro j hj hj'
    simp only [yWords, List.length_map, List.length_range] at hj
    simp only [yWords, encodeIKNPSender, List.getElem_map, List.getElem_range, List.getElem_ofFn,
      Prod.mk.injEq, hqRow_fn ⟨j, hj⟩, iknpMasked, Bool.false_eq_true, ↓reduceIte]
    have hmask (b : Bool) :
        BitString.listXor ℓ
            [BitString.listRow ℓ 0
              (if b then (XWords.getD j ([], [])).2 else (XWords.getD j ([], [])).1),
              H.eval n j
                (if b then BitString.listXor κ [List.ofFn (iknpRows Q ⟨j, hj⟩), sWord]
                  else List.ofFn (iknpRows Q ⟨j, hj⟩))] =
          List.ofFn (X ⟨j, hj⟩ b +
            H.toFinite n ⟨j, hj⟩ (if b then iknpRows Q ⟨j, hj⟩ + s else iknpRows Q ⟨j, hj⟩)) := by
      have hx :
          BitString.listRow ℓ 0
              (if b then (XWords.getD j ([], [])).2 else (XWords.getD j ([], [])).1) =
            List.ofFn (X ⟨j, hj⟩ b) := by
        simpa [X, decodeIKNPSender] using BitString.listRow_zero ℓ
          (if b then (XWords.getD j ([], [])).2 else (XWords.getD j ([], [])).1)
      have harg :
          (if b then BitString.listXor κ [List.ofFn (iknpRows Q ⟨j, hj⟩), sWord]
            else List.ofFn (iknpRows Q ⟨j, hj⟩)) =
            List.ofFn (if b then iknpRows Q ⟨j, hj⟩ + s else iknpRows Q ⟨j, hj⟩) := by
        cases b
        · rfl
        · simp [BitString.listXor_pair, s, BitString.ofList_ofFn]
      have hargLen :
          (if b then BitString.listXor κ [List.ofFn (iknpRows Q ⟨j, hj⟩), sWord]
            else List.ofFn (iknpRows Q ⟨j, hj⟩)).length = κ := by
        rw [harg, List.length_ofFn]
      have hhash :
          H.eval n j
              (if b then BitString.listXor κ [List.ofFn (iknpRows Q ⟨j, hj⟩), sWord]
                else List.ofFn (iknpRows Q ⟨j, hj⟩)) =
            List.ofFn (H.toFinite n ⟨j, hj⟩
              (if b then iknpRows Q ⟨j, hj⟩ + s else iknpRows Q ⟨j, hj⟩)) := by
        rw [harg]
        simpa [CorrelationRobustHash.toFinite] using
          (BitString.ofFn_ofList (H.eval_length n j _ hj (by rw [← harg]; exact hargLen))).symm
      rw [hx, hhash, BitString.listXor_pair, BitString.ofList_ofFn, BitString.ofList_ofFn]
    exact ⟨by simpa using hmask false, by simpa using hmask true⟩
  have htRows : tRows = List.ofFn fun j : Fin m => List.ofFn (T j) := by
    simp [tRows, T, BitString.listRows_eq_ofFn]
  have hzWords :
      zWords = List.ofFn fun j : Fin m =>
        List.ofFn (batchOTAnswer (decodeIKNPInput m ℓ XWords rWord) 1 j) := by
    apply List.ext_getElem (by simp [zWords])
    intro j hj hj'
    simp only [zWords, List.length_map, List.length_range] at hj
    simp only [zWords, List.getElem_map, List.getElem_range, List.getElem_ofFn,
      batchOTAnswer_decodeIKNPInput]
    have hrj : rWord.getD j false = r ⟨j, hj⟩ := by
      simp [r, BitString.ofList, List.getD_eq_getElem?_getD]
    have hjm : j < H.queries n := hj
    have hyj :
        yWords.getD j ([], []) =
          (List.ofFn (iknpMasked (H.toFinite n) X s Q ⟨j, hjm⟩ false),
           List.ofFn (iknpMasked (H.toFinite n) X s Q ⟨j, hjm⟩ true)) := by
      simp only [hyWords, encodeIKNPSender, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hjm, ↓reduceDIte, Option.getD_some]
    have htj : tRows.getD j [] = List.ofFn (T ⟨j, hj⟩) := by
      simp only [htRows, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, ↓reduceDIte,
        Option.getD_some]
    have hhash :
        H.eval n j (tRows.getD j []) = List.ofFn (H.toFinite n ⟨j, hj⟩ (T ⟨j, hj⟩)) := by
      rw [htj]
      simpa [CorrelationRobustHash.toFinite] using
        (BitString.ofFn_ofList (H.eval_length n j (List.ofFn (T ⟨j, hj⟩)) hj (by simp [κ]))).symm
    have hsel :
        (if rWord.getD j false then (yWords.getD j ([], [])).2
          else (yWords.getD j ([], [])).1) =
          List.ofFn (iknpMasked (H.toFinite n) X s Q ⟨j, hj⟩ (r ⟨j, hj⟩)) := by
      rw [hrj, hyj]
      cases r ⟨j, hj⟩ <;> rfl
    rw [hsel, hhash, BitString.listXor_pair, BitString.ofList_ofFn, BitString.ofList_ofFn]
    refine congrArg List.ofFn ?_
    simp only [iknpMasked, Q]
    rw [iknp_mask_input]
    simp [X, r]
  have hsv : sv = encodeIKNPSenderViewWord X s Q := by
    have hsWordEq : sWord = List.ofFn s := (BitString.ofFn_ofList (n := κ) hsLen).symm
    simp only [sv, encodeIKNPSenderViewWord, normalizeIKNPSenderPairs_eq_encode, X,
      hsWordEq, hqRows]
  have hrv : rv = encodeIKNPReceiverViewWord r T (iknpMasked (H.toFinite n) X s Q) := by
    simp [rv, encodeIKNPReceiverViewWord, normalizeIKNPReceiverBits_eq_ofFn, r, htRows, hyWords]
  have hov : ov = encodeIKNPOutputsWord (batchOTAnswer (decodeIKNPInput m ℓ XWords rWord) 1) := by
    simp [ov, encodeIKNPOutputsWord, hzWords]
  exact Prod.ext hsv (Prod.ext hrv hov)

/-- Exact PMF description of `iknpWordRun` matching `sampleIKNPCoins` and `IKNP.lean` views. -/
theorem eval_iknpWordRun (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp.eval (iknpWordRun H n XWords rWord) =
      (ProbComp.eval (sampleIKNPCoins (H.keyLength n) (H.queries n))).map fun c =>
        let m := H.queries n
        let ℓ := H.outLength n
        let X := decodeIKNPSender m ℓ XWords
        let r := BitString.ofList m rWord
        let Q := fun i => iknpColumns r c.2 i (c.1 i)
        (encodeIKNPSenderViewWord X c.1 Q,
          encodeIKNPReceiverViewWord r c.2 (iknpMasked (H.toFinite n) X c.1 Q),
          encodeIKNPOutputsWord
            (batchOTAnswer (decodeIKNPInput m ℓ XWords rWord) 1)) := by
  rw [eval_iknpWordRun_eq_closed]
  set κ := H.keyLength n
  set m := H.queries n
  set ℓ := H.outLength n
  have hL :
      ProbComp.eval (iknpWordClosed H n XWords rWord) =
        (BitString.uniformList κ).bind fun sWord =>
          (BitString.uniformList (m * κ)).bind fun tFlat =>
            PMF.pure
              (encodeIKNPSenderViewWord (decodeIKNPSender m ℓ XWords) (BitString.ofList κ sWord)
                  (fun i => iknpColumns (BitString.ofList m rWord)
                    (BitString.block (BitString.ofList (m * κ) tFlat)) i
                    (BitString.ofList κ sWord i)),
                encodeIKNPReceiverViewWord (BitString.ofList m rWord)
                  (BitString.block (BitString.ofList (m * κ) tFlat))
                  (iknpMasked (H.toFinite n) (decodeIKNPSender m ℓ XWords)
                    (BitString.ofList κ sWord)
                    (fun i => iknpColumns (BitString.ofList m rWord)
                      (BitString.block (BitString.ofList (m * κ) tFlat)) i
                      (BitString.ofList κ sWord i))),
                encodeIKNPOutputsWord (batchOTAnswer (decodeIKNPInput m ℓ XWords rWord) 1)) := by
    simp only [iknpWordClosed, iknpWordPost, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun sWord hsWord => ?_
    have hsLen : sWord.length = κ := BitString.length_of_mem_support_uniformList hsWord
    refine congrArg (PMF.bind _) (funext fun tFlat => ?_)
    exact congrArg PMF.pure (iknpWordClosed_body_eq H n XWords rWord hsLen)
  rw [hL]
  symm
  have hs := BitString.uniformList_ofList κ
  have hT := BitString.uniformList_blocks m κ
  simp only [sampleIKNPCoins, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind, ← PMF.bind_pure_comp, Function.comp_def]
  rw [← hs, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun sWord => ?_)
  dsimp only [Function.comp_def]
  rw [← hT, PMF.bind_map]
  rfl

/-- **Correctness**: every supported output of `iknpWordRun` equals the `batchOTAnswer`
functionality output. -/
theorem iknpWordRun_correctness (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool)
    {sv rv ov : List Bool}
    (hsupp : (sv, rv, ov) ∈ (ProbComp.eval (iknpWordRun H n XWords rWord)).support) :
    ov = encodeIKNPOutputsWord
      (batchOTAnswer (decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord) 1) := by
  rw [eval_iknpWordRun, PMF.mem_support_map_iff] at hsupp
  obtain ⟨c, _, hc⟩ := hsupp
  exact (Prod.mk.inj (Prod.mk.inj hc).2).2.symm

/-- Exact distributional agreement between `iknpWordRun`'s sender marginal `(sv, ov)` and
`(iknpProtocol (H.toFinite n)).realJoint` for coalition `{0}`. -/
theorem iknpWordRun_eq_realJoint_sender (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp.eval (do let (sv, _, ov) ← iknpWordRun H n XWords rWord; return (sv, ov)) =
      ((iknpProtocol (H.toFinite n)).realJoint
          (batchOTWorld (H.keyLength n) (BitString (H.queries n))) {0}
          (decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord)).map fun (v, y) =>
        (encodeIKNPSenderViewWord (v ⟨0, Finset.mem_singleton_self 0⟩).input
            (v ⟨0, Finset.mem_singleton_self 0⟩).coins
            ((v ⟨0, Finset.mem_singleton_self 0⟩).received.1 1 rfl),
          encodeIKNPOutputsWord (y 1)) := by
  rw [ProbComp.eval_bind, eval_iknpWordRun, realJoint_iknp_sender, PMF.map_comp,
    ← PMF.bind_pure_comp]
  simp only [ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, Function.comp_def, singletonView,
    iknpSenderView, decodeIKNPInput, Fin.cases_zero]
  refine congrArg (PMF.bind _) (funext fun c => ?_)
  rfl

/-- Masked-message table received by party `1` in round `1` of an IKNP receiver view. -/
abbrev iknpReceiverMsg {κ m : ℕ} {L : Type}
    (v : PartyView ((batchOTSpec m L).Query ()) (IKNPCoins κ m) (iknpSchedule κ m L) 1) :
    Fin m → Bool → L :=
  let (_, msg, _) := v.received
  msg rfl

/-- Exact distributional agreement between `iknpWordRun`'s receiver marginal `(rv, ov)` and
`(iknpProtocol (H.toFinite n)).realJoint` for coalition `{1}`. -/
theorem iknpWordRun_eq_realJoint_receiver (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp.eval (do let (_, rv, ov) ← iknpWordRun H n XWords rWord; return (rv, ov)) =
      ((iknpProtocol (H.toFinite n)).realJoint
          (batchOTWorld (H.keyLength n) (BitString (H.queries n))) {1}
          (decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord)).map fun (v, y) =>
        (encodeIKNPReceiverViewWord (v ⟨1, Finset.mem_singleton_self 1⟩).input
            (v ⟨1, Finset.mem_singleton_self 1⟩).coins
            (iknpReceiverMsg (v ⟨1, Finset.mem_singleton_self 1⟩)),
          encodeIKNPOutputsWord (y 1)) := by
  have hd0 :
      decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord 0 =
        decodeIKNPSender (H.queries n) (H.outLength n) XWords :=
    Fin.cases_zero
  have hd1 :
      decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord 1 =
        BitString.ofList (H.queries n) rWord :=
    Fin.cases_succ (motive := fun i =>
        (batchOTSpec (H.queries n) (BitString (H.outLength n))).Query () i) 0
  rw [ProbComp.eval_bind, eval_iknpWordRun, realJoint_iknp_receiver, PMF.map_comp,
    ← PMF.bind_pure_comp]
  simp only [ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, Function.comp_def, singletonView,
    iknpReceiverView, iknpReceiverMsg, hd0, hd1]
  refine congrArg (PMF.bind _) (funext fun c => congrArg PMF.pure ?_)
  refine Prod.ext (congrArg
    (encodeIKNPReceiverViewWord (BitString.ofList (H.queries n) rWord) c.2) ?_) rfl
  funext j b
  simp only [iknpMasked]
  rw [iknp_mask_input, apply_ite (H.toFinite n j)]

/-! ### Sender simulator and unconditional sender privacy -/

/-- PPT word-level sender simulator matching `iknpSenderSim`. -/
noncomputable def iknpSenderSimWord (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) : ProbComp (List Bool) := do
  let κ := H.keyLength n
  let m := H.queries n
  let ℓ := H.outLength n
  let sWord ← BitString.sampleList κ
  let qFlat ← BitString.sampleList (κ * m)
  let qRows := BitString.listRows κ m qFlat
  return encIKNPSenderViewRaw (normalizeIKNPSenderPairs m ℓ XWords, sWord, qRows)

/-- `iknpSenderSimWord` runs in uniform strict probabilistic polynomial time. -/
theorem isPPTOn_iknpSenderSimWord (H : CorrelationRobustHash) :
    IsPPTOn (encPair encUnary encIKNPSenderPairs) encBits
      (fun p => iknpSenderSimWord H p.1 p.2) := by
  have hsSample : IsPPTOn (encPair encUnary encIKNPSenderPairs) encBits
      (fun p => BitString.sampleList (H.keyLength p.1)) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have hqSample : IsPPTOn (encPair (encPair encUnary encIKNPSenderPairs) encBits) encBits
      (fun p => BitString.sampleList (H.keyLength p.1.1 * H.queries p.1.1)) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have hpost : ComputableInPolyTime
      (fun p : ((ℕ × List (List Bool × List Bool)) × List Bool) × List Bool =>
        encIKNPSenderViewRaw
          (normalizeIKNPSenderPairs (H.queries p.1.1.1) (H.outLength p.1.1.1) p.1.1.2,
            p.1.2, BitString.listRows (H.keyLength p.1.1.1) (H.queries p.1.1.1) p.2))
      (encPair (encPair (encPair encUnary encIKNPSenderPairs) encBits) encBits) encBits := by
    fun_prop
  exact hsSample.bind_with (hqSample.bind_with hpost.tidy.isPPTOn)

/-- Ideal word-level sender experiment pairing `iknpSenderSimWord` with honest output. -/
noncomputable def iknpWordSenderIdealSample (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp (List Bool × List Bool) := do
  let sv ← iknpSenderSimWord H n XWords
  let ov := encodeIKNPOutputsWord
    (batchOTAnswer (decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord) 1)
  return (sv, ov)

/-- Exact PMF equality between real and ideal word-level sender joint `(view, output)` runs. -/
theorem iknpWord_sender_eval_eq (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp.eval (do let (sv, _, ov) ← iknpWordRun H n XWords rWord; return (sv, ov)) =
      ProbComp.eval (iknpWordSenderIdealSample H n XWords rWord) := by
  let x := decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord
  have hreal := iknpWordRun_eq_realJoint_sender H n XWords rWord
  rw [← idealJoint_iknp_sender (H.toFinite n) x] at hreal
  rw [hreal]
  symm
  have hs := BitString.uniformList_ofList (H.keyLength n)
  have hQ := BitString.uniformList_blocks (H.keyLength n) (H.queries n)
  have hx0 :
      ({0} : Finset (Fin 2)).restrict x ⟨0, Finset.mem_singleton_self 0⟩ =
        decodeIKNPSender (H.queries n) (H.outLength n) XWords := by
    dsimp only [Finset.restrict, Set.domRestrict, x, decodeIKNPInput]
    exact Fin.cases_zero
  simp only [iknpWordSenderIdealSample, iknpSenderSimWord, idealJoint, batchOTFunctionality,
    Functionality.ofDeterministic, iknpSenderSim, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind,
    ← PMF.bind_pure_comp, Function.comp_def, singletonView, iknpSenderView]
  rw [← hs, PMF.bind_map]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun sWord hsWord => ?_
  have hsLen : sWord.length = H.keyLength n :=
    BitString.length_of_mem_support_uniformList hsWord
  dsimp only [Function.comp_def]
  rw [← hQ, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun qFlat => ?_)
  dsimp only [Function.comp_def]
  rw [hx0]
  simp only [encodeIKNPSenderViewWord, normalizeIKNPSenderPairs_eq_encode,
    BitString.listRows_eq_ofFn, BitString.ofFn_ofList hsLen]
  rfl

/-- **Unconditional sender privacy**: real and ideal word-level sender runs have distinguishing
advantage `0` against every distinguisher. -/
theorem iknpWord_sender_advantage_zero (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool)
    (D : List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval (do let (sv, _, ov) ← iknpWordRun H n XWords rWord; D (sv, ov)))
      (ProbComp.eval (do let pair ← iknpWordSenderIdealSample H n XWords rWord; D pair)) = 0 := by
  have heq :
      ProbComp.eval (do let (sv, _, ov) ← iknpWordRun H n XWords rWord; D (sv, ov)) =
        ProbComp.eval (do let pair ← iknpWordSenderIdealSample H n XWords rWord; D pair) := by
    have hbind := congrArg
      (fun p : PMF (List Bool × List Bool) => p.bind fun q => ProbComp.eval (D q))
      (iknpWord_sender_eval_eq H n XWords rWord)
    simpa [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, Function.comp_def] using hbind
  rw [heq, Game.advantage_self]

/-- **Asymptotic sender privacy**: for any polynomial-time inputs `(X, r)`, the encoded real
and ideal sender joint `(view, output)` distributions are computationally indistinguishable (in
fact identical). -/
theorem iknpWord_asymptotic_sender_private (H : CorrelationRobustHash)
    (X : ℕ → List (List Bool × List Bool)) (r : ℕ → List Bool) :
    ComputationallyIndistinguishable
      (fun n =>
        (ProbComp.eval (do let (sv, _, ov) ← iknpWordRun H n (X n) (r n); return (sv, ov))).map
          (encPair encBits encBits))
      (fun n =>
        (ProbComp.eval (iknpWordSenderIdealSample H n (X n) (r n))).map
          (encPair encBits encBits)) := by
  intro D hD
  have hzero (n : ℕ) :
      Game.advantage
        (distinguishingGame
          ((ProbComp.eval (do let (sv, _, ov) ← iknpWordRun H n (X n) (r n); return (sv, ov))).map
            (encPair encBits encBits)) (D n))
        (distinguishingGame
          ((ProbComp.eval (iknpWordSenderIdealSample H n (X n) (r n))).map
            (encPair encBits encBits)) (D n)) = 0 := by
    simp only [iknpWord_sender_eval_eq, Game.advantage_self]
  simpa only [hzero] using negligible_zero

/-! ### Receiver simulator, reduction, and asymptotic receiver privacy -/

/-- Word-level receiver simulator matching `iknpReceiverSim`. -/
noncomputable def iknpReceiverSimWord (H : CorrelationRobustHash) (n : ℕ)
    (rWord : List Bool) (zWords : List (List Bool)) : ProbComp (List Bool) := do
  let κ := H.keyLength n
  let m := H.queries n
  let ℓ := H.outLength n
  let tFlat ← BitString.sampleList (m * κ)
  let uFlat ← BitString.sampleList (m * ℓ)
  let tRows := BitString.listRows m κ tFlat
  let uRows := BitString.listRows m ℓ uFlat
  let rn := normalizeIKNPReceiverBits m rWord
  let yWords := (List.range m).map fun j =>
    let maskedZ := BitString.listXor ℓ
      [BitString.listRow ℓ 0 (zWords.getD j []), H.eval n j (tRows.getD j [])]
    let uj := uRows.getD j []
    if rn.getD j false then (uj, maskedZ) else (maskedZ, uj)
  return encIKNPReceiverViewRaw (rn, tRows, yWords)

/-- `iknpReceiverSimWord` runs in uniform strict probabilistic polynomial time. -/
theorem isPPTOn_iknpReceiverSimWord (H : CorrelationRobustHash) :
    IsPPTOn (encPair encUnary (encPair encBits (encList encBits))) encBits
      (fun p => iknpReceiverSimWord H p.1 p.2.1 p.2.2) := by
  have htSample : IsPPTOn (encPair encUnary (encPair encBits (encList encBits))) encBits
      (fun p => BitString.sampleList (H.queries p.1 * H.keyLength p.1)) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have huSample : IsPPTOn
      (encPair (encPair encUnary (encPair encBits (encList encBits))) encBits) encBits
      (fun p => BitString.sampleList (H.queries p.1.1 * H.outLength p.1.1)) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have hpost : ComputableInPolyTime
      (fun p : ((ℕ × List Bool × List (List Bool)) × List Bool) × List Bool =>
        let n := p.1.1.1
        let rWord := p.1.1.2.1
        let zWords := p.1.1.2.2
        let tFlat := p.1.2
        let uFlat := p.2
        let κ := H.keyLength n
        let m := H.queries n
        let ℓ := H.outLength n
        let tRows := BitString.listRows m κ tFlat
        let uRows := BitString.listRows m ℓ uFlat
        let rn := normalizeIKNPReceiverBits m rWord
        let yWords := (List.range m).map fun j =>
          let maskedZ := BitString.listXor ℓ
            [BitString.listRow ℓ 0 (zWords.getD j []), H.eval n j (tRows.getD j [])]
          let uj := uRows.getD j []
          if rn.getD j false then (uj, maskedZ) else (maskedZ, uj)
        encIKNPReceiverViewRaw (rn, tRows, yWords))
      (encPair (encPair (encPair encUnary (encPair encBits (encList encBits))) encBits) encBits)
      encBits := by
    fun_prop
  exact htSample.bind_with (huSample.bind_with hpost.tidy.isPPTOn)

/-- Ideal word-level receiver experiment pairing `iknpReceiverSimWord` with honest output. -/
noncomputable def iknpWordReceiverIdealSample (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp (List Bool × List Bool) := do
  let m := H.queries n
  let ℓ := H.outLength n
  let zWords := (List.range m).map fun j =>
    let p := XWords.getD j ([], [])
    BitString.listRow ℓ 0 (if rWord.getD j false then p.2 else p.1)
  let rv ← iknpReceiverSimWord H n rWord zWords
  return (rv, encList encBits zWords)

/-- Exact PMF equality between `iknpWordReceiverIdealSample` and encoded `idealJoint ...
(iknpReceiverSim (H.toFinite n))`. -/
theorem iknpWordReceiverIdealSample_eval_eq (H : CorrelationRobustHash) (n : ℕ)
    (XWords : List (List Bool × List Bool)) (rWord : List Bool) :
    ProbComp.eval (iknpWordReceiverIdealSample H n XWords rWord) =
      (ProbComp.eval (idealJoint (batchOTFunctionality (H.queries n) (BitString (H.outLength n)))
          {1} (iknpReceiverSim (H.toFinite n))
          (decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord))).map fun (v, y) =>
        (encodeIKNPReceiverViewWord (v ⟨1, Finset.mem_singleton_self 1⟩).input
            (v ⟨1, Finset.mem_singleton_self 1⟩).coins
            (iknpReceiverMsg (v ⟨1, Finset.mem_singleton_self 1⟩)),
          encodeIKNPOutputsWord (y 1)) := by
  symm
  have hx1 :
      ({1} : Finset (Fin 2)).restrict
          (decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord)
          ⟨1, Finset.mem_singleton_self 1⟩ =
        BitString.ofList (H.queries n) rWord := by
    dsimp only [Finset.restrict, Set.domRestrict, decodeIKNPInput]
    exact Fin.cases_succ (motive := fun i =>
        (batchOTSpec (H.queries n) (BitString (H.outLength n))).Query () i) 0
  have hy1 :
      ({1} : Finset (Fin 2)).restrict
          (batchOTAnswer (decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord))
          ⟨1, Finset.mem_singleton_self 1⟩ =
        fun j => decodeIKNPSender (H.queries n) (H.outLength n) XWords j
          (BitString.ofList (H.queries n) rWord j) := by
    funext j
    exact batchOTAnswer_decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord j
  have hzWords :
      ((List.range (H.queries n)).map fun j =>
          let p := XWords.getD j ([], [])
          BitString.listRow (H.outLength n) 0 (if rWord.getD j false then p.2 else p.1)) =
        List.ofFn fun j : Fin (H.queries n) =>
          List.ofFn (batchOTAnswer
            (decodeIKNPInput (H.queries n) (H.outLength n) XWords rWord) 1 j) := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      batchOTAnswer_decodeIKNPInput, decodeIKNPSender]
    have hrj : rWord.getD j false = BitString.ofList (H.queries n) rWord ⟨j, hj⟩ := by
      simp [BitString.ofList, List.getD_eq_getElem?_getD]
    rw [hrj]
    cases BitString.ofList (H.queries n) rWord ⟨j, hj⟩ <;> simp [BitString.listRow_zero]
  have hT := BitString.uniformList_blocks (H.queries n) (H.keyLength n)
  have hU := BitString.uniformList_blocks (H.queries n) (H.outLength n)
  simp only [idealJoint, batchOTFunctionality, Functionality.ofDeterministic, iknpReceiverSim,
    iknpWordReceiverIdealSample, iknpReceiverSimWord, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind,
    ← PMF.bind_pure_comp, Function.comp_def, singletonView, iknpReceiverView,
    iknpReceiverMsg]
  rw [← hT, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun tFlat => ?_)
  dsimp only [Function.comp_def]
  rw [← hU, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun uFlat => congrArg PMF.pure ?_)
  dsimp only [Function.comp_def]
  rw [hx1, hy1]
  refine Prod.ext ?_ (congrArg (encList encBits) hzWords.symm)
  simp only [encodeIKNPReceiverViewWord, BitString.listRows_eq_ofFn,
    normalizeIKNPReceiverBits_eq_ofFn]
  refine congrArg encIKNPReceiverViewRaw (Prod.ext rfl (Prod.ext rfl ?_))
  dsimp only [encodeIKNPSender]
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp only [List.length_map, List.length_range, List.length_ofFn] at hj hj'
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, List.getElem?_ofFn,
    hj, ↓reduceDIte, Option.map_some, Option.getD_some, BitString.listRow_zero]
  have hrj : rWord[j]?.getD false = BitString.ofList (H.queries n) rWord ⟨j, hj⟩ := by
    simp [BitString.ofList, List.getD_eq_getElem?_getD]
  have hzJ :
      BitString.listRow (H.outLength n) 0
          (if BitString.ofList (H.queries n) rWord ⟨j, hj⟩ then
            (XWords.getD j ([], [])).2
          else (XWords.getD j ([], [])).1) =
        List.ofFn (decodeIKNPSender (H.queries n) (H.outLength n) XWords ⟨j, hj⟩
          (BitString.ofList (H.queries n) rWord ⟨j, hj⟩)) := by
    rw [decodeIKNPSender]
    cases BitString.ofList (H.queries n) rWord ⟨j, hj⟩ <;> simp [BitString.listRow_zero]
  have htj :
      H.eval n j (List.ofFn
          (BitString.block (BitString.ofList (H.queries n * H.keyLength n) tFlat) ⟨j, hj⟩)) =
        List.ofFn (H.toFinite n ⟨j, hj⟩
          (BitString.block (BitString.ofList (H.queries n * H.keyLength n) tFlat) ⟨j, hj⟩)) := by
    simpa [CorrelationRobustHash.toFinite] using
      (BitString.ofFn_ofList (H.eval_length n j _ hj (by simp))).symm
  have hmaskZ :
      BitString.listXor (H.outLength n)
          [BitString.listRow (H.outLength n) 0
              (if BitString.ofList (H.queries n) rWord ⟨j, hj⟩ then
                (XWords.getD j ([], [])).2
              else (XWords.getD j ([], [])).1),
            H.eval n j (List.ofFn
              (BitString.block (BitString.ofList (H.queries n * H.keyLength n) tFlat)
                ⟨j, hj⟩))] =
        List.ofFn (decodeIKNPSender (H.queries n) (H.outLength n) XWords ⟨j, hj⟩
            (BitString.ofList (H.queries n) rWord ⟨j, hj⟩) +
          H.toFinite n ⟨j, hj⟩
            (BitString.block (BitString.ofList (H.queries n * H.keyLength n) tFlat) ⟨j, hj⟩)) := by
    rw [hzJ, htj, BitString.listXor_pair, BitString.ofList_ofFn, BitString.ofList_ofFn]
  rw [hrj]
  cases hrv : BitString.ofList (H.queries n) rWord ⟨j, hj⟩
  · have hmaskF := by simpa [hrv, BitString.listRow_zero] using hmaskZ
    simp [hmaskF]
  · have hmaskT := by simpa [hrv, BitString.listRow_zero] using hmaskZ
    simp [hmaskT]

/-- Word-level correlation-robustness adversary induced by a receiver distinguisher `D` on
inputs `(X, r)`. -/
noncomputable def iknpWordReduction (H : CorrelationRobustHash)
    (X : ℕ → List (List Bool × List Bool)) (r : ℕ → List Bool)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    CorrelationRobust.WordAdversary :=
  fun n pair =>
    let m := H.queries n
    let κ := H.keyLength n
    let ℓ := H.outLength n
    let Xn := normalizeIKNPSenderPairs m ℓ (X n)
    let rn := normalizeIKNPReceiverBits m (r n)
    let tWords := (List.range m).map fun j => BitString.listRow κ 0 (pair.1.getD j [])
    let maskedPairs := (List.range m).map fun j =>
      let p := Xn.getD j ([], [])
      let tj := tWords.getD j []
      let yj := BitString.listRow ℓ 0 (pair.2.getD j [])
      let rj := rn.getD j false
      let mask0 := if rj then yj else H.eval n j tj
      let mask1 := if rj then H.eval n j tj else yj
      (BitString.listXor ℓ [p.1, mask0], BitString.listXor ℓ [p.2, mask1])
    let zWords := (List.range m).map fun j =>
      let p := Xn.getD j ([], [])
      if rn.getD j false then p.2 else p.1
    let rv := encIKNPReceiverViewRaw (rn, tWords, maskedPairs)
    let ov := encList encBits zWords
    D n (rv, ov)

/-- `iknpWordReduction` is a strict PPT correlation-robustness word adversary whenever `X`, `r`,
and `D` are polynomial-time. -/
theorem isPPTOn_iknpWordReduction (H : CorrelationRobustHash)
    {X : ℕ → List (List Bool × List Bool)} {r : ℕ → List Bool}
    {D : ℕ → List Bool × List Bool → ProbComp Bool}
    (hX : ComputableInPolyTime X encUnary encIKNPSenderPairs)
    (hr : ComputableInPolyTime r encUnary encBits)
    (hD : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool (fun p => D p.1 p.2)) :
    CorrelationRobust.WordAdversary.IsPPT (iknpWordReduction H X r D) := by
  have hX' : ComputableInPolyTime (fun p : ℕ × List (List Bool) × List (List Bool) => X p.1)
      encWordAdvInput encIKNPSenderPairs :=
    hX.comp (by unfold encWordAdvInput; fun_prop)
  have hr' : ComputableInPolyTime (fun p : ℕ × List (List Bool) × List (List Bool) => r p.1)
      encWordAdvInput encBits :=
    hr.comp (by unfold encWordAdvInput; fun_prop)
  have hprep : ComputableInPolyTime
      (fun p : ℕ × List (List Bool) × List (List Bool) =>
        let n := p.1
        let m := H.queries n
        let κ := H.keyLength n
        let ℓ := H.outLength n
        let Xn := normalizeIKNPSenderPairs m ℓ (X n)
        let rn := normalizeIKNPReceiverBits m (r n)
        let tWords := (List.range m).map fun j => BitString.listRow κ 0 (p.2.1.getD j [])
        let maskedPairs := (List.range m).map fun j =>
          let q := Xn.getD j ([], [])
          let tj := tWords.getD j []
          let yj := BitString.listRow ℓ 0 (p.2.2.getD j [])
          let rj := rn.getD j false
          let mask0 := if rj then yj else H.eval n j tj
          let mask1 := if rj then H.eval n j tj else yj
          (BitString.listXor ℓ [q.1, mask0], BitString.listXor ℓ [q.2, mask1])
        let zWords := (List.range m).map fun j =>
          let q := Xn.getD j ([], [])
          if rn.getD j false then q.2 else q.1
        (n, encIKNPReceiverViewRaw (rn, tWords, maskedPairs), encList encBits zWords))
      encWordAdvInput (encPair encUnary (encPair encBits encBits)) := by
    unfold encWordAdvInput encWordTuple
    fun_prop
  simpa [CorrelationRobust.WordAdversary.IsPPT, iknpWordReduction] using
    IsPPTOn.preprocess hD hprep

/-- **Exact receiver reduction identity**: word-level receiver distinguishing advantage equals
the correlation-robustness advantage of `iknpWordReduction` at `n`. -/
theorem iknpWord_receiver_advantage_eq (H : CorrelationRobustHash)
    (X : ℕ → List (List Bool × List Bool)) (r : ℕ → List Bool)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) (n : ℕ) :
    Game.advantage
        (ProbComp.eval (do let (_, rv, ov) ← iknpWordRun H n (X n) (r n); D n (rv, ov)))
        (ProbComp.eval (do
          let pair ← iknpWordReceiverIdealSample H n (X n) (r n)
          D n pair)) =
      Game.advantage
        (CorrelationRobust.wordRealGame H (iknpWordReduction H X r D) n)
        (CorrelationRobust.wordIdealGame H (iknpWordReduction H X r D) n) := by
  let x := decodeIKNPInput (H.queries n) (H.outLength n) (X n) (r n)
  let DFin :
      ((i : ({1} : Finset (Fin 2))) →
          PartyView ((batchOTSpec (H.queries n) (BitString (H.outLength n))).Query ())
            (IKNPCoins (H.keyLength n) (H.queries n))
            (iknpSchedule (H.keyLength n) (H.queries n) (BitString (H.outLength n))) i) ×
        ((i : Fin 2) → (batchOTSpec (H.queries n) (BitString (H.outLength n))).Answer () i) →
      ProbComp Bool :=
    fun p =>
      let v := p.1 ⟨1, Finset.mem_singleton_self 1⟩
      D n (encodeIKNPReceiverViewWord v.input v.coins (iknpReceiverMsg v),
        encodeIKNPOutputsWord (p.2 1))
  have hred :
      CorrelationRobust.Adversary.ofWord (iknpWordReduction H X r D) n
          (H.queries n) (H.keyLength n) (H.outLength n) =
        iknpReduction (H.toFinite n) x DFin := by
    funext ⟨t, y⟩
    have hx0 : x 0 = decodeIKNPSender (H.queries n) (H.outLength n) (X n) :=
      Fin.cases_zero
    have hx1 : x 1 = BitString.ofList (H.queries n) (r n) :=
      Fin.cases_succ (motive := fun i =>
          (batchOTSpec (H.queries n) (BitString (H.outLength n))).Query () i) 0
    simp only [CorrelationRobust.Adversary.ofWord, CorrelationRobust.encodePair,
      iknpWordReduction, iknpReduction, DFin, singletonView, iknpReceiverView,
      iknpReceiverMsg, encodeIKNPReceiverViewWord, encodeIKNPOutputsWord]
    refine congrArg (D n) (Prod.ext (congrArg encIKNPReceiverViewRaw ?_)
      (congrArg (encList encBits) ?_))
    · have htWords :
          ((List.range (H.queries n)).map fun j => BitString.listRow (H.keyLength n) 0
              ((List.ofFn fun j => List.ofFn (t j)).getD j [])) =
            List.ofFn fun j : Fin (H.queries n) => List.ofFn (t j) := by
        apply List.ext_getElem (by simp)
        intro j hj hj'
        simp only [List.length_map, List.length_range] at hj
        simp [List.getD_eq_getElem?_getD, hj, BitString.listRow_zero, BitString.ofList_ofFn]
      rw [hx0, hx1]
      refine Prod.ext (normalizeIKNPReceiverBits_eq_ofFn (H.queries n) (r n)) (Prod.ext htWords ?_)
      simp only [htWords]
      apply List.ext_getElem (by simp [encodeIKNPSender])
      intro j hj hj'
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range, encodeIKNPSender, List.getElem_ofFn,
        normalizeIKNPSenderPairs_eq_encode, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        hj, ↓reduceDIte, Option.getD_some, BitString.listRow_zero,
        BitString.ofList_ofFn, normalizeIKNPReceiverBits_eq_ofFn, Prod.mk.injEq]
      have hht :
          H.eval n j (List.ofFn (t ⟨j, hj⟩)) =
            List.ofFn (H.toFinite n ⟨j, hj⟩ (t ⟨j, hj⟩)) := by
        simpa [CorrelationRobustHash.toFinite] using
          (BitString.ofFn_ofList (H.eval_length n j _ hj (by simp))).symm
      cases BitString.ofList (H.queries n) (r n) ⟨j, hj⟩ <;>
        simp [decodeIKNPSender, hht, BitString.listXor_pair, BitString.ofList_ofFn]
    · apply List.ext_getElem (by simp)
      intro j hj hj'
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
        normalizeIKNPSenderPairs_eq_encode, encodeIKNPSender, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some, normalizeIKNPReceiverBits_eq_ofFn]
      rw [batchOTAnswer_decodeIKNPInput]
      cases BitString.ofList (H.queries n) (r n) ⟨j, hj⟩ <;> simp [decodeIKNPSender]
  have hreal :
      ProbComp.eval (do let (_, rv, ov) ← iknpWordRun H n (X n) (r n); D n (rv, ov)) =
        ((iknpProtocol (H.toFinite n)).realJoint
            (batchOTWorld (H.keyLength n) (BitString (H.queries n))) {1} x).bind
          (fun pair => ProbComp.eval (DFin pair)) := by
    have hbind := congrArg
      (fun p : PMF (List Bool × List Bool) => p.bind fun q => ProbComp.eval (D n q))
      (iknpWordRun_eq_realJoint_receiver H n (X n) (r n))
    simpa [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, DFin] using hbind
  have hideal :
      ProbComp.eval (do let pair ← iknpWordReceiverIdealSample H n (X n) (r n); D n pair) =
        ProbComp.eval (idealJoint
            (batchOTFunctionality (H.queries n) (BitString (H.outLength n))) {1}
            (iknpReceiverSim (H.toFinite n)) x >>= DFin) := by
    have hbind := congrArg
      (fun p : PMF (List Bool × List Bool) => p.bind fun q => ProbComp.eval (D n q))
      (iknpWordReceiverIdealSample_eval_eq H n (X n) (r n))
    simpa [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, DFin] using hbind
  rw [hreal, hideal, Game.advantage_comm]
  change semiHonestAdvantage (iknpProtocol (H.toFinite n))
      (batchOTWorld (H.keyLength n) (BitString (H.queries n)))
      (batchOTFunctionality (H.queries n) (BitString (H.outLength n))) {1}
      (iknpReceiverSim (H.toFinite n)) x DFin = _
  rw [semiHonestAdvantage_iknp_receiver (H.toFinite n) x DFin, ← hred]
  exact (CorrelationRobust.wordAdvantage_eq_finite H (iknpWordReduction H X r D) n).symm

/-- **Asymptotic receiver privacy**: if `H` is correlation-robust, then for any polynomial-time
inputs `(X, r)`, real and ideal receiver joint `(view, output)` distributions are
computationally indistinguishable. -/
theorem iknpWord_asymptotic_receiver_private {H : CorrelationRobustHash}
    (hH : H.IsCorrelationRobust)
    {X : ℕ → List (List Bool × List Bool)} {r : ℕ → List Bool}
    (hX : ComputableInPolyTime X encUnary encIKNPSenderPairs)
    (hr : ComputableInPolyTime r encUnary encBits) :
    ComputationallyIndistinguishable
      (fun n =>
        (ProbComp.eval (do let (_, rv, ov) ← iknpWordRun H n (X n) (r n); return (rv, ov))).map
          (encPair encBits encBits))
      (fun n =>
        (ProbComp.eval (iknpWordReceiverIdealSample H n (X n) (r n))).map
          (encPair encBits encBits)) := by
  intro D hD
  let DPair : ℕ → List Bool × List Bool → ProbComp Bool :=
    fun n pair => D n (encPair encBits encBits pair)
  have hprep : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (p.1, encPair encBits encBits p.2))
      (encPair encUnary (encPair encBits encBits)) (encPair encUnary encBits) := by
    have hfst : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => p.1)
        (encPair encUnary (encPair encBits encBits)) encUnary := by fun_prop
    have hsnd : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => encPair encBits encBits p.2)
        (encPair encUnary (encPair encBits encBits)) encBits :=
      (ComputableInPolyTime.of_tidy
        (ComputableTidilyInPolyTime.encode (encPair encBits encBits))).comp
        (by fun_prop)
    exact hfst.prod hsnd
  have hDPair : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
      (fun p => DPair p.1 p.2) :=
    IsPPTOn.preprocess hD hprep
  have hneg := hH (iknpWordReduction H X r DPair) (isPPTOn_iknpWordReduction H hX hr hDPair)
  refine hneg.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hadv := (iknpWord_receiver_advantage_eq H X r DPair n).symm
  simpa only [distinguishingGame, ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, DPair] using hadv

end Cslib.Crypto.Protocols.MPC
