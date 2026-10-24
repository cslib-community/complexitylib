/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.Selection
public import Complexity.Computability.Circuit.Boolean.Sorting

/-!
# Records for detecting checkpoint hits and repeats

The fixed-power circuit sorts one array of records. Stored records carry a checkpoint state and
a payload, queries carry a state of the orbit prefix and its time, and padding fills the array.
Records are sorted by a padding flag followed by their state, so that padding comes last. Both
a checkpoint hit and a repeated state appear as two different records with equal keys, and
sorting makes such a pair adjacent; a linear scan finds one (`detect`). The detected pair
certifies one of the two situations exactly (`detect_sorted_witness`), even when complete
records repeat. Sorting uses the native Batcher circuit `bitonicSortCircuit`.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.Record`,
  `Cslib.Circuits.Boolean.Iteration.Record.width`,
  `Cslib.Circuits.Boolean.Iteration.Record.key`,
  `Cslib.Circuits.Boolean.Iteration.Record.keyBits`,
  `Cslib.Circuits.Boolean.Iteration.Record.encode`,
  `Cslib.Circuits.Boolean.Iteration.Record.decode`: a complete record, its sort key, and its bit
  encoding.
* `Cslib.Circuits.Boolean.Iteration.Record.query`,
  `Cslib.Circuits.Boolean.Iteration.Record.stored`,
  `Cslib.Circuits.Boolean.Iteration.Record.pad`,
  `Cslib.Circuits.Boolean.Iteration.Record.collision`,
  `Cslib.Circuits.Boolean.Iteration.Record.initial`,
  `Cslib.Circuits.Boolean.Iteration.Record.Valid`: query, checkpoint, and padding records,
  collision test, initial array, and validity predicate.
* `Cslib.Circuits.Boolean.Iteration.Record.Witness`: what a detected collision certifies.
* `Cslib.Circuits.Boolean.Iteration.Record.pack`,
  `Cslib.Circuits.Boolean.Iteration.Record.sorted`,
  `Cslib.Circuits.Boolean.Iteration.Record.adjacentPair`,
  `Cslib.Circuits.Boolean.Iteration.Record.detect`: array packing, sorting, and adjacent-collision
  scan.

## Main results

* `Cslib.Circuits.Boolean.Iteration.Record.detect_sorted_witness`: if the orbit prefix reaches a
  checkpoint or repeats, the detected pair is a witness.

## References

* Adapted from lean/Proofs/{Records,Detector}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n w : ℕ}

/-- A complete record carried through the sorting network. -/
@[ext] structure Record (n w : ℕ) where
  /-- Padding records sort after all others and never collide. -/
  padding : Bool
  /-- The state compared by the sort. -/
  state : BitString n
  /-- Whether this is a stored checkpoint rather than a query. -/
  checkpoint : Bool
  /-- The time of a query in the orbit prefix. -/
  index : BitVec w
  /-- The shifted state stored with a checkpoint. -/
  payload : BitString n
  deriving DecidableEq

namespace Record

/-- The number of bits of a record: its key, then its remaining fields. -/
def width (n w : ℕ) : ℕ := (n + 1) + (w + n + 1)

/-- The sort key: the padding flag, then the state. -/
def key (r : Record n w) : Lex (Fin (n + 1) → Bool) := toLex (Fin.cons r.padding r.state)

/-- The key coordinates of an encoded record. -/
def keyBits : Fin (n + 1) → Fin (width n w) := Fin.castAdd (w + n + 1)

/-- The bits of a record: padding flag and state, then checkpoint flag, index and payload. -/
def encode (r : Record n w) : BitString (width n w) :=
  Fin.append (Fin.cons r.padding r.state)
    (Fin.cons r.checkpoint (Fin.append (fun i => r.index.getLsbD i.val) r.payload))

/-- The record with the given bits; inverse to `encode`. -/
def decode (bits : BitString (width n w)) : Record n w where
  padding := bits (Fin.castAdd (w + n + 1) 0)
  state i := bits (Fin.castAdd (w + n + 1) i.succ)
  checkpoint := bits (Fin.natAdd (n + 1) 0)
  index := word fun i => bits (Fin.natAdd (n + 1) (Fin.castAdd n i).succ)
  payload i := bits (Fin.natAdd (n + 1) (Fin.natAdd w i).succ)

/-- Decoding the bit encoding of a record recovers the record. -/
@[simp] theorem decode_encode (r : Record n w) : decode (encode r) = r := by
  ext <;> simp [decode, encode, Fin.cons]

/-- Encoding the decoded record of a bit string recovers the bit string. -/
@[simp] theorem encode_decode (bits : BitString (width n w)) : encode (decode bits) = bits := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.cases with
    | zero => simp [encode, decode]
    | succ i => simp [encode, decode]
  | right i =>
    induction i using Fin.cases with
    | zero => simp [encode, decode]
    | succ i =>
      induction i using Fin.addCases with
      | left i => simp [encode, decode]
      | right i => simp [encode, decode]

/-- Record bit encoding `encode` is injective. -/
theorem encode_injective : Function.Injective (encode : Record n w → BitString (width n w)) :=
  Function.LeftInverse.injective decode_encode

/-- The sort key of a decoded record is read from its key coordinates. -/
private theorem key_decode (bits : BitString (width n w)) :
    (decode bits).key = toLex (bits ∘ keyBits) := by
  apply congrArg toLex
  funext i
  induction i using Fin.cases <;> rfl

/-- Two records have equal sort keys iff they have the same padding flag and state. -/
theorem key_eq_iff (a b : Record n w) :
    a.key = b.key ↔ a.padding = b.padding ∧ a.state = b.state := by
  constructor
  · intro h
    exact ⟨congrFun h 0, funext fun i => congrFun h i.succ⟩
  · rintro ⟨hpad, hstate⟩
    simp [key, hpad, hstate]

/-- A query for the state at time `index` of the orbit prefix. -/
def query (state : BitString n) (index : ℕ) : Record n w :=
  ⟨false, state, false, BitVec.ofNat w index, fun _ => false⟩

/-- A stored checkpoint with its payload. -/
def stored (state payload : BitString n) : Record n w :=
  ⟨false, state, true, 0, payload⟩

/-- A padding record. -/
def pad : Record n w := ⟨true, fun _ => false, false, 0, fun _ => false⟩

/-- Two records collide when neither is padding, their states agree, and they differ. -/
def collision (a b : Record n w) : Bool :=
  !a.padding && !b.padding && decide (a.state = b.state) && decide (a ≠ b)

/-- `collision a b` holds iff neither record is padding, their states are equal, and the records
are distinct. -/
theorem collision_iff (a b : Record n w) :
    collision a b = true ↔ a.padding = false ∧ b.padding = false ∧
      a.state = b.state ∧ a ≠ b := by
  simp [collision, and_assoc]

variable {M R : ℕ}

/-- The initial array: stored checkpoints, then the orbit prefix up to time `K`, then padding.
Checkpoint `h` stores the state `T - K` steps later. -/
def initial (f : BitString n → BitString n) (T K : ℕ) (checkpoints : Fin M → BitString n)
    (x : BitString n) (j : Fin R) : Record n w :=
  if h : j.val < M then stored (checkpoints ⟨j.val, h⟩) (f^[T - K] (checkpoints ⟨j.val, h⟩))
  else if j.val - M ≤ K then query (f^[j.val - M] x) (j.val - M)
  else pad

private theorem initial_stored (f : BitString n → BitString n) (T K : ℕ)
    (checkpoints : Fin M → BitString n) (x : BitString n) (hR : M + (K + 1) ≤ R) (j : Fin M) :
    initial (R := R) (w := w) f T K checkpoints x ⟨j.val, by have := j.isLt; omega⟩ =
      stored (checkpoints j) (f^[T - K] (checkpoints j)) := by
  simp [initial, j.isLt]

private theorem initial_query (f : BitString n → BitString n) (T K : ℕ)
    (checkpoints : Fin M → BitString n) (x : BitString n) (hR : M + (K + 1) ≤ R)
    (j : Fin (K + 1)) :
    initial (R := R) (w := w) f T K checkpoints x ⟨M + j.val, by have := j.isLt; omega⟩ =
      query (f^[j.val] x) j.val := by
  simp [initial, Nat.le_of_lt_succ j.isLt]

/-- A record that is padding, a stored checkpoint, or a query of the orbit prefix. -/
def Valid (f : BitString n → BitString n) (T K : ℕ) (checkpoints : Fin M → BitString n)
    (x : BitString n) (r : Record n w) : Prop :=
  r = pad ∨ (∃ h : Fin M, r = stored (checkpoints h) (f^[T - K] (checkpoints h))) ∨
    ∃ d ≤ K, r = query (f^[d] x) d

private theorem valid_initial (f : BitString n → BitString n) (T K : ℕ)
    (checkpoints : Fin M → BitString n) (x : BitString n) (j : Fin R) :
    Valid f T K checkpoints x (initial (w := w) f T K checkpoints x j) := by
  unfold initial
  split_ifs with h1 h2
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, h2, rfl⟩)
  · exact Or.inl rfl

/-- What a collision certifies: the prefix reaches a checkpoint, or it repeats. -/
inductive Witness (f : BitString n → BitString n) (T K : ℕ) (checkpoints : Fin M → BitString n)
    (x : BitString n) : Record n w → Record n w → Prop
  /-- A stored checkpoint followed by the prefix state at time `d` that equals it. -/
  | hitLeft (h : Fin M) (d : ℕ) (hd : d ≤ K) (heq : f^[d] x = checkpoints h) :
      Witness f T K checkpoints x
        (stored (checkpoints h) (f^[T - K] (checkpoints h))) (query (f^[d] x) d)
  /-- The prefix state at time `d` followed by the checkpoint it equals. -/
  | hitRight (h : Fin M) (d : ℕ) (hd : d ≤ K) (heq : f^[d] x = checkpoints h) :
      Witness f T K checkpoints x (query (f^[d] x) d)
        (stored (checkpoints h) (f^[T - K] (checkpoints h)))
  /-- Two different times of the prefix with equal states. -/
  | repeated (i j : ℕ) (hi : i ≤ K) (hj : j ≤ K) (hne : i ≠ j) (heq : f^[i] x = f^[j] x) :
      Witness f T K checkpoints x (query (f^[i] x) i) (query (f^[j] x) j)

/-- A collision between valid records is a witness, without requiring unique records. -/
private theorem collision_witness (f : BitString n → BitString n) (T K : ℕ)
    (checkpoints : Fin M → BitString n) (x : BitString n) (a b : Record n w)
    (ha : Valid f T K checkpoints x a) (hb : Valid f T K checkpoints x b)
    (hc : collision a b = true) : Witness f T K checkpoints x a b := by
  obtain ⟨hpa, hpb, hstate, hne⟩ := (collision_iff a b).mp hc
  rcases ha with rfl | ⟨h, rfl⟩ | ⟨i, hi, rfl⟩
  · simp [pad] at hpa
  · rcases hb with rfl | ⟨h', rfl⟩ | ⟨j, hj, rfl⟩
    · simp [pad] at hpb
    · have he : checkpoints h = checkpoints h' := hstate
      exact (hne (by rw [he])).elim
    · exact Witness.hitLeft h j hj hstate.symm
  · rcases hb with rfl | ⟨h', rfl⟩ | ⟨j, hj, rfl⟩
    · simp [pad] at hpb
    · exact Witness.hitRight h' i hi hstate
    · exact Witness.repeated i j hi hj (by rintro rfl; exact hne rfl) hstate

/-! ### Sorting and detection -/

/-- Records stored in consecutive blocks of bits. -/
def pack (records : Fin R → Record n w) : BitString (R * width n w) :=
  fun bit => encode (records (finProdFinEquiv.symm bit).1) (finProdFinEquiv.symm bit).2

/-- Extracting the `j`-th block of `pack records` gives `encode (records j)`. -/
@[simp] theorem directProductInput_pack (records : Fin R → Record n w) (j : Fin R) :
    directProductInput (pack records) j = encode (records j) := by
  funext bit
  simp [directProductInput, pack]

/-- Sort records by padding flag and state with the native Batcher circuit. -/
def sorted (d : ℕ) (records : Fin (BitonicSort.arity d) → Record n w) :
    Fin (BitonicSort.arity d) → Record n w :=
  fun j => decode (directProductInput
    ((bitonicSortCircuit keyBits d true).eval interpretation (pack records)) j)

private theorem sorted_perm (d : ℕ) (records : Fin (BitonicSort.arity d) → Record n w) :
    (List.ofFn (sorted d records)).Perm (List.ofFn records) := by
  have h := (bitonicSortCircuit_perm (keyBits (n := n) (w := w)) d true (pack records)).map decode
  unfold sorted
  simpa only [List.map_ofFn, Function.comp_def, directProductInput_pack, decode_encode] using h

private theorem monotone_key_sorted (d : ℕ) (records : Fin (BitonicSort.arity d) → Record n w) :
    Monotone (key ∘ sorted d records) := by
  have h := monotone_bitonicSortCircuit (keyBits (n := n) (w := w)) d (pack records)
  simpa only [Function.comp_def, sorted, key_decode] using h

/-- Two adjacent records of an array. -/
def adjacentPair (records : Fin R → Record n w) (j : Fin (R - 1)) : Record n w × Record n w :=
  (records ⟨j.val, by have := j.isLt; omega⟩, records ⟨j.val + 1, by have := j.isLt; omega⟩)

/-- The last colliding adjacent pair, or two padding records if there is none. -/
def detect (records : Fin R → Record n w) : Record n w × Record n w :=
  chooseRecord (fun j => collision (adjacentPair records j).1 (adjacentPair records j).2)
    (adjacentPair records) (pad, pad) (R - 1)

/-- A checkpoint hit or a repeat of the prefix gives two different initial records with equal
keys, the first of which is not padding. -/
private theorem initial_collision (f : BitString n → BitString n) (T K : ℕ)
    (checkpoints : Fin M → BitString n) (x : BitString n) (hR : M + (K + 1) ≤ R) (hK : K < 2 ^ w)
    (hcover : (∃ d ≤ K, ∃ h : Fin M, f^[d] x = checkpoints h) ∨
      ∃ i j, i < j ∧ j ≤ K ∧ f^[i] x = f^[j] x) :
    ∃ a b : Fin R,
      initial (w := w) f T K checkpoints x a ≠ initial (w := w) f T K checkpoints x b ∧
      (initial (w := w) f T K checkpoints x a).key =
        (initial (w := w) f T K checkpoints x b).key ∧
      (initial (w := w) f T K checkpoints x a).padding = false := by
  rcases hcover with ⟨d, hd, h, heq⟩ | ⟨i, j, hij, hj, heq⟩
  · refine ⟨⟨h.val, by have := h.isLt; omega⟩, ⟨M + d, by omega⟩, ?_⟩
    rw [initial_stored f T K checkpoints x hR h,
      initial_query f T K checkpoints x hR ⟨d, by omega⟩]
    refine ⟨fun hbad => ?_, by simp [key, stored, query, heq], rfl⟩
    simpa [stored, query] using congrArg checkpoint hbad
  · refine ⟨⟨M + i, by omega⟩, ⟨M + j, by omega⟩, ?_⟩
    rw [initial_query f T K checkpoints x hR ⟨i, by omega⟩,
      initial_query f T K checkpoints x hR ⟨j, by omega⟩]
    refine ⟨fun hbad => ?_, by simp [key, query, heq], rfl⟩
    have hidx := congrArg (fun r : Record n w => r.index.toNat) hbad
    simp only [query, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((by omega : i ≤ K).trans_lt hK),
      Nat.mod_eq_of_lt (hj.trans_lt hK)] at hidx
    omega

/-- Sorting turns such a pair into a flagged adjacent pair. -/
private theorem sorted_has_collision (d : ℕ) (records : Fin (BitonicSort.arity d) → Record n w)
    (hex : ∃ a b, records a ≠ records b ∧ (records a).key = (records b).key ∧
      (records a).padding = false) :
    ∃ j : Fin (BitonicSort.arity d - 1),
      collision (adjacentPair (sorted d records) j).1 (adjacentPair (sorted d records) j).2 =
        true := by
  obtain ⟨a, b, hne, heq, hpad⟩ := hex
  obtain ⟨p, hp, hdiff, hkey, horig⟩ := adjacent_distinct_collision records (sorted d records)
    key (sorted_perm d records) (monotone_key_sorted d records) a b hne heq
  refine ⟨⟨p, by omega⟩, (collision_iff _ _).mpr ?_⟩
  obtain ⟨hpad', hstate⟩ := (key_eq_iff _ _).mp hkey
  have hfirst := (key_eq_iff _ _).mp horig
  exact ⟨hfirst.1.trans hpad, hpad'.symm.trans (hfirst.1.trans hpad), hstate, hdiff⟩

/-- If the prefix up to time `K` reaches a checkpoint or repeats, the detected pair of the
sorted initial array is a witness. -/
theorem detect_sorted_witness (f : BitString n → BitString n) (T K d : ℕ)
    (checkpoints : Fin M → BitString n) (x : BitString n)
    (hR : M + (K + 1) ≤ BitonicSort.arity d) (hK : K < 2 ^ w)
    (hcover : (∃ t ≤ K, ∃ h : Fin M, f^[t] x = checkpoints h) ∨
      ∃ i j, i < j ∧ j ≤ K ∧ f^[i] x = f^[j] x) :
    let pair := detect (sorted d (initial (w := w) f T K checkpoints x))
    Witness f T K checkpoints x pair.1 pair.2 := by
  let records := initial (R := BitonicSort.arity d) (w := w) f T K checkpoints x
  obtain ⟨j, hj⟩ := sorted_has_collision d records
    (initial_collision f T K checkpoints x hR hK hcover)
  obtain ⟨j, _, hj, hchosen⟩ := chooseRecord_spec
    (fun j => collision (adjacentPair (sorted d records) j).1
      (adjacentPair (sorted d records) j).2)
    (adjacentPair (sorted d records)) (pad, pad) (BitonicSort.arity d - 1) ⟨j, j.isLt, hj⟩
  change Witness f T K checkpoints x (detect (sorted d records)).1 (detect (sorted d records)).2
  change detect (sorted d records) = _ at hchosen
  have hvalid (i : Fin (BitonicSort.arity d)) :
      Valid f T K checkpoints x (sorted d records i) := by
    obtain ⟨source, heq⟩ :=
      ((sorted_perm d records).exists_ofFn_iff (· = sorted d records i)).mp ⟨i, rfl⟩
    exact heq ▸ valid_initial f T K checkpoints x source
  rw [hchosen]
  exact collision_witness f T K checkpoints x _ _ (hvalid _) (hvalid _) hj

end Record

end Cslib.Circuits.Boolean.Iteration
