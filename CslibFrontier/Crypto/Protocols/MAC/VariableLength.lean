/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MAC
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.SuppCases

/-!
# Variable-length MACs from fixed-length MACs

This file extends a fixed-length MAC to messages of varying length with the blockwise
construction of [KatzLindell2020], Construction 4.7. Write `L = M.msgLen n` and `w = L / 4`.
A message with `0 < |m| < 2 ^ w` is cut into `w`-bit blocks (the last one padded with zeros).
The signer samples a uniform `w`-bit identifier `r` and applies `M` to one `L`-bit input per
block, made of `r`, the message length, the block index and the block itself.

## Main definitions

* `BlockwiseMAC.blockInputs`: the fixed-length inputs that a block encoder assigns to a message.
* `BlockwiseMAC.fullEncoder`: the encoder of the construction; `noIdentifierEncoder`,
  `noLengthEncoder` and `noIndexEncoder` are insecure variants that each omit one field.
* `MACScheme.blockwiseSign`, `MACScheme.blockwiseVerify`: the variable-length scheme.
* `MACScheme.blockwiseGame`: its fresh-message EUF-CMA experiment, and
  `MACScheme.blockwiseRepeatGame`: the event that two signing queries share an identifier.
* `MACScheme.blockwiseReduction`: the fixed-length adversary built from a blockwise adversary.

## Main results

* `MACScheme.blockwiseGame_le_add_repeat`: the blockwise advantage is at most the advantage of
  `blockwiseReduction` against `M` plus the probability of a repeated identifier.
* `MACScheme.blockwiseRepeatGame_le`: with at most `Q` signing queries, a repeated identifier has
  probability at most `(∑ i ∈ range Q, i) / 2 ^ w`.
* `MACScheme.blockwiseGame_le`: the combined concrete bound ([KatzLindell2020], Theorem 4.8).
* `MACScheme.blockwiseGame_noIndex`, `MACScheme.blockwiseGame_noLength`,
  `MACScheme.blockwiseGame_noIdentifier`: separations. Each insecure variant admits an explicit
  adversary with at most two signing queries that wins with probability one when `w ≥ 3`.

## Implementation notes

The encoder is a parameter, so the construction and its three variants share one definition.
Messages outside the domain have no block inputs and never verify. The repeated-identifier bound
adds up, query by query, the chance that a new identifier equals an earlier one, which gives
`Q (Q - 1) / 2 ^ (w + 1)`. A uniform PPT corollary is left for later work.

## References

* [J. Katz and Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped ENNReal

namespace BlockwiseMAC

/-- The width `L / 4` of each field of an `L`-bit block input. -/
def fieldWidth (L : ℕ) : ℕ := L / 4

/-- The number of `w`-bit blocks, rounded up, in a `len`-bit message. -/
def blockCount (w len : ℕ) : ℕ := (len + w - 1) / w

/-- Block `i` (counting from `0`) of `m`, padded with zeros to exactly `w` bits. -/
def messageBlock (w : ℕ) (m : List Bool) (i : ℕ) : List Bool :=
  (m.drop (i * w) ++ List.replicate w false).take w

/-- A block encoder takes a field width, an input length, an identifier, a message length, a
block index and a block, and returns an input for the fixed-length MAC. -/
abbrev Encoder : Type := ℕ → ℕ → List Bool → ℕ → ℕ → List Bool → List Bool

/-- The encoder of the construction: identifier, length, index, block, then zero padding. -/
def fullEncoder (w L : ℕ) (r : List Bool) (len idx : ℕ) (block : List Bool) : List Bool :=
  r ++ BitString.lowBits w len ++ BitString.lowBits w idx ++ block ++
    List.replicate (L - 4 * w) false

/-- Insecure variant that omits the identifier. -/
def noIdentifierEncoder (w L : ℕ) (_r : List Bool) (len idx : ℕ) (block : List Bool) :
    List Bool :=
  BitString.lowBits w len ++ BitString.lowBits w idx ++ block ++ List.replicate (L - 3 * w) false

/-- Insecure variant that omits the message length. -/
def noLengthEncoder (w L : ℕ) (r : List Bool) (_len idx : ℕ) (block : List Bool) : List Bool :=
  r ++ BitString.lowBits w idx ++ block ++ List.replicate (L - 3 * w) false

/-- Insecure variant that omits the block index. -/
def noIndexEncoder (w L : ℕ) (r : List Bool) (len _idx : ℕ) (block : List Bool) : List Bool :=
  r ++ BitString.lowBits w len ++ block ++ List.replicate (L - 3 * w) false

/-- The fixed-length inputs that encoder `E` assigns to `m` under identifier `r`, one per block,
with indices starting at `1`. The list is empty unless `0 < |m| < 2 ^ w`. -/
def blockInputs (E : Encoder) (L : ℕ) (r m : List Bool) : List (List Bool) :=
  if 0 < m.length ∧ m.length < 2 ^ fieldWidth L then
    (List.range (blockCount (fieldWidth L) m.length)).map fun i =>
      E (fieldWidth L) L r m.length (i + 1) (messageBlock (fieldWidth L) m i)
  else []

/-- A blockwise tag: the identifier together with one fixed-length tag per block. -/
abbrev Tag : Type := List Bool × List (List Bool)

/-- The fixed-length inputs covered by a log of blockwise signing queries (newest first), listed
in the order in which the fixed-length signing oracle logs them. -/
def authenticatedInputs (E : Encoder) (L : ℕ) (log : List (List Bool × Tag)) :
    List (List Bool) :=
  log.flatMap fun (m, (r, _)) => (blockInputs E L r m).reverse

/-- The first block input of `msg`, paired with its tag, that the logged queries do not cover,
or `([], [])` if every block input is covered. -/
def freshBlockPair (E : Encoder) (L : ℕ) (log : List (List Bool × Tag)) (msg : List Bool)
    (tag : Tag) : List Bool × List Bool :=
  (((blockInputs E L tag.1 msg).zip tag.2).find? fun p =>
    !(authenticatedInputs E L log).contains p.1).getD ([], [])

theorem four_mul_fieldWidth_le (L : ℕ) : 4 * fieldWidth L ≤ L := Nat.mul_div_le L 4

@[simp] theorem length_messageBlock (w : ℕ) (m : List Bool) (i : ℕ) :
    (messageBlock w m i).length = w := by
  simp only [messageBlock, List.length_take, List.length_append, List.length_replicate,
    List.length_drop]
  omega

private theorem getElem?_messageBlock {w k i : ℕ} {m : List Bool} (hk : k < w)
    (hlen : i * w + k < m.length) : (messageBlock w m i)[k]? = m[i * w + k]? := by
  have hd : k < (m.drop (i * w)).length := by rw [List.length_drop]; omega
  rw [messageBlock, List.getElem?_take_of_lt hk, List.getElem?_append_left hd,
    List.getElem?_drop]

/-- Two messages of the same length with the same blocks are equal. -/
theorem eq_of_messageBlock_eq {w : ℕ} {m m' : List Bool} (hw : 0 < w)
    (hlen : m.length = m'.length)
    (hblock : ∀ i < blockCount w m.length, messageBlock w m i = messageBlock w m' i) :
    m = m' := by
  refine List.ext_getElem? fun j => ?_
  obtain ⟨i, k, hk, rfl⟩ : ∃ i k, k < w ∧ j = i * w + k :=
    ⟨j / w, j % w, Nat.mod_lt j hw, (Nat.div_add_mod' j w).symm⟩
  by_cases hj : i * w + k < m.length
  · have hi : i < blockCount w m.length := by
      have : (i + 1) * w ≤ m.length + w - 1 := by rw [Nat.add_mul, Nat.one_mul]; omega
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) ((Nat.le_div_iff_mul_le hw).2 this)
    have hj' : i * w + k < m'.length := by omega
    rw [← getElem?_messageBlock hk hj, ← getElem?_messageBlock hk hj', hblock i hi]
  · have h1 : m.length ≤ i * w + k := by omega
    have h2 : m'.length ≤ i * w + k := by omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

private theorem fieldWidth_pos {L len : ℕ} (h1 : 0 < len) (h2 : len < 2 ^ fieldWidth L) :
    0 < fieldWidth L :=
  Nat.pos_of_ne_zero fun h0 => by rw [h0, pow_zero] at h2; omega

private theorem blockCount_le {w len : ℕ} (hw : 0 < w) (hlen : 0 < len) :
    blockCount w len ≤ len := by
  obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
  have h1 : k ≤ w * k := Nat.le_mul_of_pos_left k hw
  have h2 : w * (k + 1) = w * k + w := by ring
  exact Nat.div_le_of_le_mul (by omega)

private theorem blockCount_pos {w len : ℕ} (hw : 0 < w) (hlen : 0 < len) :
    0 < blockCount w len :=
  Nat.div_pos (by omega) hw

private theorem mem_blockInputs_of_lt {E : Encoder} {L i : ℕ} {r m : List Bool}
    (hm : 0 < m.length ∧ m.length < 2 ^ fieldWidth L)
    (hi : i < blockCount (fieldWidth L) m.length) :
    E (fieldWidth L) L r m.length (i + 1) (messageBlock (fieldWidth L) m i) ∈
      blockInputs E L r m := by
  rw [blockInputs, ite_eq_left hm]
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

private theorem fullEncoder_inj {w L len idx len' idx' : ℕ} {r r' b b' : List Bool}
    (hb : b.length = w) (hb' : b'.length = w)
    (h : fullEncoder w L r len idx b = fullEncoder w L r' len' idx' b') :
    r = r' ∧ BitString.lowBits w len = BitString.lowBits w len' ∧
      BitString.lowBits w idx = BitString.lowBits w idx' ∧ b = b' := by
  simp only [fullEncoder] at h
  obtain ⟨h, -⟩ := List.append_inj' h rfl
  obtain ⟨h, hbb⟩ := List.append_inj' h (hb.trans hb'.symm)
  obtain ⟨h, hidx⟩ := List.append_inj' h (by simp)
  obtain ⟨hr, hlen⟩ := List.append_inj' h (by simp)
  exact ⟨hr, hlen, hidx, hbb⟩

/-- A block input of the construction determines the identifier, the message length, the block
index and the block. -/
private theorem eq_of_mem_blockInputs_full {L len idx : ℕ} {r r' m block : List Bool}
    (hlen : len < 2 ^ fieldWidth L) (hidx : idx < 2 ^ fieldWidth L)
    (hblock : block.length = fieldWidth L)
    (h : fullEncoder (fieldWidth L) L r len idx block ∈ blockInputs fullEncoder L r' m) :
    r' = r ∧ m.length = len ∧ ∃ i < blockCount (fieldWidth L) m.length,
      i + 1 = idx ∧ messageBlock (fieldWidth L) m i = block := by
  rw [blockInputs] at h
  split_ifs at h with hm
  · obtain ⟨i, hi, heq⟩ := List.mem_map.1 h
    have hi' := List.mem_range.1 hi
    have hw := fieldWidth_pos hm.1 hm.2
    have hcount := blockCount_le hw hm.1
    have hm2 := hm.2
    obtain ⟨hr, hl, hx, hb⟩ := fullEncoder_inj (length_messageBlock _ _ _) hblock heq
    exact ⟨hr, BitString.lowBits_injective_of_lt hm.2 hlen hl, i, hi',
      BitString.lowBits_injective_of_lt (by omega) hidx hx, hb⟩
  · simp at h

private theorem source_of_mem_authenticatedInputs {E : Encoder} {L : ℕ}
    {log : List (List Bool × Tag)} {x : List Bool} (hx : x ∈ authenticatedInputs E L log) :
    ∃ entry ∈ log, x ∈ blockInputs E L entry.2.1 entry.1 := by
  simpa [authenticatedInputs] using hx

/-- If the logged identifiers are distinct and every block input of `msg` under `r` is covered by
the log, then `msg` itself was queried. -/
private theorem mem_of_forall_mem_authenticatedInputs {L : ℕ} {log : List (List Bool × Tag)}
    {r msg : List Bool} (hnodup : (log.map fun entry => entry.2.1).Nodup)
    (hm : 0 < msg.length ∧ msg.length < 2 ^ fieldWidth L)
    (hall : ∀ x ∈ blockInputs fullEncoder L r msg, x ∈ authenticatedInputs fullEncoder L log) :
    msg ∈ log.map Prod.fst := by
  obtain ⟨hm1, hm2⟩ := hm
  have hw := fieldWidth_pos hm1 hm2
  have hcount := blockCount_le hw hm1
  have key : ∀ i < blockCount (fieldWidth L) msg.length, ∃ entry ∈ log, entry.2.1 = r ∧
      entry.1.length = msg.length ∧
      messageBlock (fieldWidth L) entry.1 i = messageBlock (fieldWidth L) msg i := by
    intro i hi
    obtain ⟨entry, hentry, hx⟩ :=
      source_of_mem_authenticatedInputs (hall _ (mem_blockInputs_of_lt ⟨hm1, hm2⟩ hi))
    obtain ⟨hr, hl, j, -, hj, hb⟩ :=
      eq_of_mem_blockInputs_full hm2 (by omega) (length_messageBlock _ _ _) hx
    obtain rfl : j = i := by omega
    exact ⟨entry, hentry, hr, hl, hb⟩
  obtain ⟨entry, hentry, hr, hl, -⟩ := key 0 (blockCount_pos hw hm1)
  refine List.mem_map.2 ⟨entry, hentry, eq_of_messageBlock_eq hw hl fun i hi => ?_⟩
  obtain ⟨entry', hentry', hr', -, hb'⟩ := key i (by rwa [← hl])
  obtain rfl : entry' = entry := List.inj_on_of_nodup_map hnodup hentry' hentry (hr'.trans hr.symm)
  exact hb'

private theorem length_of_mem_blockInputs {E : Encoder} {L : ℕ} {r m x : List Bool}
    (hE : ∀ len idx b, b.length = fieldWidth L → (E (fieldWidth L) L r len idx b).length = L)
    (hx : x ∈ blockInputs E L r m) : x.length = L := by
  rw [blockInputs] at hx
  split_ifs at hx
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hE _ _ _ (length_messageBlock _ _ _)
  · simp at hx

private theorem length_fullEncoder {L len idx : ℕ} {r b : List Bool}
    (hr : r.length = fieldWidth L) (hb : b.length = fieldWidth L) :
    (fullEncoder (fieldWidth L) L r len idx b).length = L := by
  have := four_mul_fieldWidth_le L
  simp only [fullEncoder, List.length_append, BitString.length_lowBits,
    List.length_replicate, hr, hb]
  omega

private theorem length_noIdentifierEncoder {L len idx : ℕ} {r b : List Bool}
    (hb : b.length = fieldWidth L) :
    (noIdentifierEncoder (fieldWidth L) L r len idx b).length = L := by
  have := four_mul_fieldWidth_le L
  simp only [noIdentifierEncoder, List.length_append, BitString.length_lowBits,
    List.length_replicate, hb]
  omega

private theorem length_noLengthEncoder {L len idx : ℕ} {r b : List Bool}
    (hr : r.length = fieldWidth L) (hb : b.length = fieldWidth L) :
    (noLengthEncoder (fieldWidth L) L r len idx b).length = L := by
  have := four_mul_fieldWidth_le L
  simp only [noLengthEncoder, List.length_append, BitString.length_lowBits,
    List.length_replicate, hr, hb]
  omega

private theorem length_noIndexEncoder {L len idx : ℕ} {r b : List Bool}
    (hr : r.length = fieldWidth L) (hb : b.length = fieldWidth L) :
    (noIndexEncoder (fieldWidth L) L r len idx b).length = L := by
  have := four_mul_fieldWidth_le L
  simp only [noIndexEncoder, List.length_append, BitString.length_lowBits,
    List.length_replicate, hr, hb]
  omega

private theorem messageBlock_zero {w : ℕ} {u v : List Bool} (hu : u.length = w) :
    messageBlock w (u ++ v) 0 = u := by
  rw [messageBlock, Nat.zero_mul, List.drop_zero, List.append_assoc, List.take_left' hu]

private theorem messageBlock_one {w : ℕ} {u v : List Bool} (hu : u.length = w)
    (hv : v.length = w) : messageBlock w (u ++ v) 1 = v := by
  rw [messageBlock, Nat.one_mul, List.drop_left' hu, List.take_left' hv]

private theorem messageBlock_single {w : ℕ} {u : List Bool} (hu : u.length = w) :
    messageBlock w u 0 = u := by
  rw [messageBlock, Nat.zero_mul, List.drop_zero, List.take_left' hu]

/-- The block inputs of a two-block message `u ++ v`. -/
private theorem blockInputs_two_blocks {E : Encoder} {L : ℕ} (hw : 3 ≤ fieldWidth L)
    {r u v : List Bool} (hu : u.length = fieldWidth L) (hv : v.length = fieldWidth L) :
    blockInputs E L r (u ++ v) =
      [E (fieldWidth L) L r (2 * fieldWidth L) 1 u,
        E (fieldWidth L) L r (2 * fieldWidth L) 2 v] := by
  have hlen : (u ++ v).length = 2 * fieldWidth L := by rw [List.length_append, hu, hv]; omega
  have hcount : blockCount (fieldWidth L) (2 * fieldWidth L) = 2 := by
    unfold blockCount; exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [blockInputs, hlen, ite_eq_left
    (show 0 < 2 * fieldWidth L ∧ 2 * fieldWidth L < 2 ^ fieldWidth L from
      ⟨by omega, Nat.two_mul_lt_two_pow hw⟩), hcount]
  simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, zero_add,
    messageBlock_zero hu, messageBlock_one hu hv]

private theorem blockInputs_replicate_append {E : Encoder} {L : ℕ} (hw : 3 ≤ fieldWidth L)
    (r : List Bool) (a b : Bool) :
    blockInputs E L r (List.replicate (fieldWidth L) a ++ List.replicate (fieldWidth L) b) =
      [E (fieldWidth L) L r (2 * fieldWidth L) 1 (List.replicate (fieldWidth L) a),
        E (fieldWidth L) L r (2 * fieldWidth L) 2 (List.replicate (fieldWidth L) b)] :=
  blockInputs_two_blocks hw (by simp) (by simp)

private theorem blockInputs_replicate {E : Encoder} {L : ℕ} (hw : 3 ≤ fieldWidth L)
    (r : List Bool) (a : Bool) :
    blockInputs E L r (List.replicate (fieldWidth L) a) =
      [E (fieldWidth L) L r (fieldWidth L) 1 (List.replicate (fieldWidth L) a)] := by
  have hlt : fieldWidth L < 2 ^ fieldWidth L := by have := Nat.two_mul_lt_two_pow hw; omega
  have hcount : blockCount (fieldWidth L) (fieldWidth L) = 1 := by
    unfold blockCount; exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [blockInputs, List.length_replicate, ite_eq_left (show 0 < fieldWidth L ∧
    fieldWidth L < 2 ^ fieldWidth L from ⟨by omega, hlt⟩), hcount]
  simp only [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, zero_add,
    messageBlock_single (List.length_replicate ..)]

private theorem eq_of_replicate_eq {w : ℕ} {a b : Bool} (hw : 0 < w)
    (h : List.replicate w a = List.replicate w b) : a = b := by
  have ha : a ∈ List.replicate w b := h ▸ List.mem_replicate.2 ⟨by omega, rfl⟩
  exact (List.mem_replicate.1 ha).2

private theorem replicate_append_ne {w : ℕ} {a b c d : Bool} (hw : 0 < w) (h : a ≠ c ∨ b ≠ d) :
    List.replicate w a ++ List.replicate w b ≠ List.replicate w c ++ List.replicate w d := by
  intro heq
  obtain ⟨h1, h2⟩ := List.append_inj heq (by simp)
  exact h.elim (· (eq_of_replicate_eq hw h1)) (· (eq_of_replicate_eq hw h2))

private theorem forall₂_pair {α β : Type} {R : α → β → Prop} {a b : α} {ys : List β}
    (h : List.Forall₂ R [a, b] ys) : ∃ s t, ys = [s, t] ∧ R a s ∧ R b t := by
  obtain ⟨s, l, hs, h', rfl⟩ := List.forall₂_cons_left_iff.1 h
  obtain ⟨t, l', ht, h'', rfl⟩ := List.forall₂_cons_left_iff.1 h'
  rw [List.forall₂_nil_left_iff] at h''
  subst h''
  exact ⟨s, t, rfl, hs, ht⟩

end BlockwiseMAC

/-- An adaptive adversary against a variable-length MAC: on security parameter `n` it queries a
blockwise signing oracle and outputs a candidate message/tag pair. -/
abbrev BlockwiseMACAdversary : Type :=
  ℕ → ProbOracleComp (fun _ : List Bool => BlockwiseMAC.Tag) (List Bool × BlockwiseMAC.Tag)

namespace MACScheme

open BlockwiseMAC

variable (M : MACScheme) (E : Encoder)

/-- Blockwise signing: sample a `w`-bit identifier `r`, then tag every block input with `M`. -/
noncomputable def blockwiseSign (n : ℕ) (sk m : List Bool) : ProbComp Tag := do
  let r ← BitString.sampleList (fieldWidth (M.msgLen n))
  let tags ← (blockInputs E (M.msgLen n) r m).mapM (M.sign sk)
  return (r, tags)

/-- Blockwise verification: the message is in the domain, the identifier has `w` bits, there is
one tag per block, and `M` accepts every block input with its tag. -/
def blockwiseVerify (n : ℕ) (sk m : List Bool) (tag : Tag) : Bool :=
  decide (0 < m.length ∧ m.length < 2 ^ fieldWidth (M.msgLen n)) &&
    tag.1.length == fieldWidth (M.msgLen n) &&
    tag.2.length == (blockInputs E (M.msgLen n) tag.1 m).length &&
    ((blockInputs E (M.msgLen n) tag.1 m).zip tag.2).all fun p => M.verify sk p.1 p.2

/-- The blockwise signing oracle; its state logs each query with the returned tag, newest
first. -/
noncomputable def blockwiseSigningOracle (n : ℕ) (sk m : List Bool) :
    StateT (List (List Bool × Tag)) ProbComp Tag :=
  fun log => do
    let tag ← M.blockwiseSign E n sk m
    return (tag, (m, tag) :: log)

/-- The fresh-message EUF-CMA experiment for the blockwise scheme: the adversary wins when it
outputs a message it never queried together with a tag that `blockwiseVerify` accepts. -/
noncomputable def blockwiseGame (A : BlockwiseMACAdversary) (n : ℕ) : ProbComp Bool := do
  let sk ← M.keyGen n
  let ((msg, tag), log) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.blockwiseSigningOracle E n sk)) (A n)).run []
  return !(log.map Prod.fst).contains msg && M.blockwiseVerify E n sk msg tag

/-- The same experiment, reporting instead whether two signing queries received the same
identifier. -/
noncomputable def blockwiseRepeatGame (A : BlockwiseMACAdversary) (n : ℕ) : ProbComp Bool := do
  let sk ← M.keyGen n
  let (_, log) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.blockwiseSigningOracle E n sk)) (A n)).run []
  return !decide (log.map fun (_, (r, _)) => r).Nodup

/-- Answers a blockwise signing query with fixed-length signing queries, one per block input,
and logs the query. -/
noncomputable def blockwiseSimulator (n : ℕ) (m : List Bool) :
    StateT (List (List Bool × Tag)) (WordOracleComp Unit) Tag :=
  fun log => do
    let r ← ProbOracleComp.sample (BitString.sampleList (fieldWidth (M.msgLen n)))
    let tags ← (blockInputs E (M.msgLen n) r m).mapM fun x =>
      (ProbOracleComp.query ((), x) : WordOracleComp Unit (List Bool))
    return ((r, tags), (m, (r, tags)) :: log)

/-- The fixed-length adversary of the reduction: run the blockwise adversary against
`blockwiseSimulator`, then output the first block input of its message that no simulated query
covered, with the matching block tag. -/
noncomputable def blockwiseReduction (A : BlockwiseMACAdversary) : Forger := fun n _ => do
  let ((msg, tag), log) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (M.blockwiseSimulator E n)) (A n)).run []
  return freshBlockPair E (M.msgLen n) log msg tag

/-- Output distribution of the blockwise adversary together with the final log. -/
private noncomputable def blockwiseRun (A : BlockwiseMACAdversary) (n : ℕ) (sk : List Bool) :
    PMF ((List Bool × Tag) × List (List Bool × Tag)) :=
  ProbOracleComp.runWith (fun q s => ProbComp.eval (M.blockwiseSigningOracle E n sk q s)) (A n) []

/-- Success predicate of the fixed-length experiment. -/
private def reductionWins (n : ℕ) (sk : List Bool) (pair : List Bool × List Bool)
    (queried : List (List Bool)) : Bool :=
  (pair.1.length == M.msgLen n) && !queried.contains pair.1 && M.verify sk pair.1 pair.2

private theorem eval_blockwiseGame (A : BlockwiseMACAdversary) (n : ℕ) :
    ProbComp.eval (M.blockwiseGame E A n) = (ProbComp.eval (M.keyGen n)).bind fun sk =>
      (M.blockwiseRun E A n sk).bind fun out => PMF.pure
        (!(out.2.map Prod.fst).contains out.1.1 && M.blockwiseVerify E n sk out.1.1 out.1.2) := by
  simp only [blockwiseGame, blockwiseRun, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret_eq_runWith]

private theorem eval_blockwiseRepeatGame (A : BlockwiseMACAdversary) (n : ℕ) :
    ProbComp.eval (M.blockwiseRepeatGame E A n) = (ProbComp.eval (M.keyGen n)).bind fun sk =>
      (M.blockwiseRun E A n sk).bind fun out =>
        PMF.pure (!decide (out.2.map fun entry => entry.2.1).Nodup) := by
  simp only [blockwiseRepeatGame, blockwiseRun, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret_eq_runWith]

private theorem eval_blockwiseSigningOracle (n : ℕ) (sk m : List Bool)
    (log : List (List Bool × Tag)) :
    ProbComp.eval (M.blockwiseSigningOracle E n sk m log) =
      (BitString.uniformList (fieldWidth (M.msgLen n))).bind fun r =>
        (ProbComp.eval ((blockInputs E (M.msgLen n) r m).mapM (M.sign sk))).bind fun tags =>
          PMF.pure ((r, tags), (m, (r, tags)) :: log) := by
  simp only [blockwiseSigningOracle, blockwiseSign, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]

private theorem mem_support_blockwiseSigningOracle {n : ℕ} {sk m r : List Bool}
    {tags : List (List Bool)} {log log' : List (List Bool × Tag)}
    (h : ((r, tags), log') ∈ (ProbComp.eval (M.blockwiseSigningOracle E n sk m log)).support) :
    log' = (m, (r, tags)) :: log ∧ r.length = fieldWidth (M.msgLen n) ∧
      tags ∈ (ProbComp.eval ((blockInputs E (M.msgLen n) r m).mapM (M.sign sk))).support := by
  supp_cases h [eval_blockwiseSigningOracle] with ⟨r', hr', tags', htags', ⟨rfl, rfl⟩, rfl⟩
  exact ⟨rfl, BitString.length_of_mem_support_uniformList hr', htags'⟩

private theorem forall₂_of_mem_support_mapM {n : ℕ} {sk : List Bool}
    (hsk : sk ∈ (ProbComp.eval (M.keyGen n)).support) (xs : List (List Bool))
    (hxs : ∀ x ∈ xs, x.length = M.msgLen n) {tags : List (List Bool)}
    (htags : tags ∈ (ProbComp.eval (xs.mapM (M.sign sk))).support) :
    List.Forall₂ (fun x t => M.verify sk x t = true) xs tags := by
  induction xs generalizing tags with
  | nil =>
    supp_cases htags [List.mapM_nil]
    exact .nil
  | cons x xs ih =>
    supp_cases htags [List.mapM_cons] with ⟨t, ht, ts, hts, rfl⟩
    exact .cons (M.verify_sign n sk hsk x (hxs x (by simp)) t ht)
      (ih (fun y hy => hxs y (by simp [hy])) hts)

private theorem blockwiseVerify_of_forall₂ {n : ℕ} {sk m : List Bool} {tag : Tag}
    (hm : 0 < m.length ∧ m.length < 2 ^ fieldWidth (M.msgLen n))
    (hr : tag.1.length = fieldWidth (M.msgLen n))
    (htags : List.Forall₂ (fun x t => M.verify sk x t = true)
      (blockInputs E (M.msgLen n) tag.1 m) tag.2) :
    M.blockwiseVerify E n sk m tag = true := by
  simp only [blockwiseVerify, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨hm, hr⟩, htags.length_eq.symm⟩, fun p hp => ?_⟩
  exact (List.forall₂_iff_zip.1 htags).2 hp

private theorem reductionWins_of_blockwiseWins {n : ℕ} {sk : List Bool}
    {log : List (List Bool × Tag)} {msg : List Bool} {tag : Tag}
    (hnodup : (log.map fun entry => entry.2.1).Nodup)
    (hwin : (!(log.map Prod.fst).contains msg && M.blockwiseVerify fullEncoder n sk msg tag) =
      true) :
    M.reductionWins n sk (freshBlockPair fullEncoder (M.msgLen n) log msg tag)
      (authenticatedInputs fullEncoder (M.msgLen n) log) = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hwin
  obtain ⟨hnew, hver⟩ := hwin
  simp only [blockwiseVerify, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true] at hver
  obtain ⟨⟨⟨hm, hr⟩, hlen⟩, hall⟩ := hver
  cases hfind : ((blockInputs fullEncoder (M.msgLen n) tag.1 msg).zip tag.2).find?
      (fun p => !(authenticatedInputs fullEncoder (M.msgLen n) log).contains p.1) with
  | none =>
    refine absurd (mem_of_forall_mem_authenticatedInputs (r := tag.1) hnodup hm fun x hx => ?_) hnew
    have hx' : x ∈ ((blockInputs fullEncoder (M.msgLen n) tag.1 msg).zip tag.2).map Prod.fst := by
      rw [List.map_fst_zip (le_of_eq hlen.symm)]
      exact hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx'
    simpa using List.find?_eq_none.1 hfind p hp
  | some p =>
    have hp := List.mem_of_find?_eq_some hfind
    have hpred := List.find?_some hfind
    simp only [freshBlockPair, hfind, Option.getD_some, reductionWins, Bool.and_eq_true,
      beq_iff_eq]
    exact ⟨⟨length_of_mem_blockInputs (fun _ _ _ hb => length_fullEncoder hr hb)
      (List.of_mem_zip hp).1, hpred⟩, hall p hp⟩

private theorem runWith_mapM_query (sk : List Bool) (xs : List (List Bool))
    (log : List (List Bool)) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (M.signingOracle sk q s))
      (xs.mapM fun x => (ProbOracleComp.query ((), x) : WordOracleComp Unit (List Bool))) log =
      (ProbComp.eval (xs.mapM (M.sign sk))).map fun tags => (tags, xs.reverse ++ log) := by
  induction xs generalizing log with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, ih]
    simp only [signingOracle, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind, PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem runWith_blockwiseSimulator (A : BlockwiseMACAdversary) (n : ℕ)
    (sk : List Bool) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (M.signingOracle sk q s))
      ((OracleComp.interpret (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (M.blockwiseSimulator E n)) (A n)).run []) [] =
      (M.blockwiseRun E A n sk).map fun out => (out, authenticatedInputs E (M.msgLen n) out.2) := by
  rw [ProbOracleComp.runWith_run_interpret]
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun q s => ProbComp.eval (M.blockwiseSigningOracle E n sk q s))
    (oracle' := fun q (state : List (List Bool × Tag) × List (List Bool)) =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (M.signingOracle sk q s))
        ((M.blockwiseSimulator E n q).run state.1) state.2).map fun x => (x.1.1, x.1.2, x.2))
    (represent := fun log => (log, authenticatedInputs E (M.msgLen n) log))
    (step := by
      intro m log
      simp only [eval_blockwiseSigningOracle, StateT.run, blockwiseSimulator,
        ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure,
        runWith_mapM_query, BitString.eval_sampleList, PMF.map_bind, PMF.bind_map, PMF.pure_map,
        Function.comp_def, authenticatedInputs, List.flatMap_cons])
    (A n) []
  exact (congrArg (PMF.map _) hsim.symm).trans (by rw [PMF.map_comp]; rfl)

private theorem eval_eufCmaGame_blockwiseReduction (A : BlockwiseMACAdversary) (n : ℕ) :
    ProbComp.eval (M.eufCmaGame (M.blockwiseReduction E A) n) =
      (ProbComp.eval (M.keyGen n)).bind fun sk => (M.blockwiseRun E A n sk).bind fun out =>
        PMF.pure (M.reductionWins n sk (freshBlockPair E (M.msgLen n) out.2 out.1.1 out.1.2)
          (authenticatedInputs E (M.msgLen n) out.2)) := by
  simp only [eufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk _ => ?_
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  simp only [blockwiseReduction, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure]
  rw [runWith_blockwiseSimulator, PMF.bind_map, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun out _ => ?_
  simp only [Function.comp_apply, PMF.pure_bind]
  rfl

/-- The blockwise success probability is at most the EUF-CMA success of `blockwiseReduction`
against `M` plus the probability that two signing queries share an identifier. -/
theorem blockwiseGame_le_add_repeat (A : BlockwiseMACAdversary) (n : ℕ) :
    ProbComp.eval (M.blockwiseGame fullEncoder A n) true ≤
      ProbComp.eval (M.eufCmaGame (M.blockwiseReduction fullEncoder A) n) true +
        ProbComp.eval (M.blockwiseRepeatGame fullEncoder A n) true := by
  rw [eval_blockwiseGame, eval_eufCmaGame_blockwiseReduction, eval_blockwiseRepeatGame]
  refine PMF.bind_apply_le_add_on_support _ _ fun sk _ => ?_
  refine PMF.bind_apply_le_add_on_support _ _ fun out _ => ?_
  by_cases hnodup : (out.2.map fun entry => entry.2.1).Nodup
  · by_cases hwin : (!(out.2.map Prod.fst).contains out.1.1 &&
        M.blockwiseVerify fullEncoder n sk out.1.1 out.1.2) = true
    · rw [hwin, M.reductionWins_of_blockwiseWins hnodup hwin, PMF.pure_apply, ite_eq_left rfl]
      exact le_self_add
    · rw [Bool.eq_false_iff.2 hwin]
      simp
  · have h3 : (!decide (out.2.map fun entry => entry.2.1).Nodup) = true := by simp [hnodup]
    rw [h3, PMF.pure_apply true true, ite_eq_left rfl]
    exact le_add_left (PMF.coe_le_one _ _)

/-- Correctness of the blockwise scheme: an honest tag on a message in the domain verifies. -/
theorem blockwiseVerify_blockwiseSign {n : ℕ} {sk : List Bool}
    (hsk : sk ∈ (ProbComp.eval (M.keyGen n)).support) {m : List Bool}
    (hm : 0 < m.length ∧ m.length < 2 ^ fieldWidth (M.msgLen n)) {tag : Tag}
    (htag : tag ∈ (ProbComp.eval (M.blockwiseSign fullEncoder n sk m)).support) :
    M.blockwiseVerify fullEncoder n sk m tag = true := by
  supp_cases htag [blockwiseSign, BitString.eval_sampleList] with ⟨r, hr, tags, htags, rfl⟩
  have hrlen := BitString.length_of_mem_support_uniformList hr
  exact M.blockwiseVerify_of_forall₂ fullEncoder hm hrlen (M.forall₂_of_mem_support_mapM hsk _
    (fun x hx => length_of_mem_blockInputs (fun _ _ _ hb => length_fullEncoder hrlen hb) hx)
    htags)

private theorem repeat_arith {c len k w : ℕ} (x : ℝ≥0∞) (hc : c ≤ len) :
    (c : ℝ≥0∞) * (1 / 2 ^ w) +
        (x + (((len + 1) * k + ∑ i ∈ Finset.range k, i : ℕ) : ℝ≥0∞) / 2 ^ w) ≤
      x + ((len * (k + 1) + ∑ i ∈ Finset.range (k + 1), i : ℕ) : ℝ≥0∞) / 2 ^ w := by
  rw [mul_one_div, add_left_comm, ← ENNReal.add_div, ← Nat.cast_add]
  refine add_le_add le_rfl (ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _)
  rw [Finset.sum_range_succ]
  have : len * (k + 1) = len * k + len := by ring
  have : (len + 1) * k = len * k + k := by ring
  omega

private theorem repeat_cons_le (r : List Bool) (ids : List (List Bool)) :
    PMF.pure (!decide (r :: ids).Nodup) true ≤
      (if r ∈ ids.toFinset then 1 else 0) + PMF.pure (!decide ids.Nodup) true := by
  by_cases hr : r ∈ ids <;> by_cases hn : ids.Nodup <;> simp [hr, hn, PMF.pure_apply]

private theorem runWith_inl_bind {β : Type} (o : List Bool → List (List Bool × Tag) →
      PMF (Tag × List (List Bool × Tag))) (k : ℕ)
    (cont : Fin (k + 1) → ProbOracleComp (fun _ : List Bool => Tag) β)
    (log : List (List Bool × Tag)) :
    ProbOracleComp.runWith o (OracleComp.query (Sum.inl k) >>= cont) log =
      (ProbComp.unifOracle k).bind fun x => ProbOracleComp.runWith o (cont x) log := by
  rw [ProbOracleComp.runWith_bind, show ProbOracleComp.runWith o (OracleComp.query (Sum.inl k))
    log = (ProbComp.unifOracle k).map (·, log) from OracleComp.runWith_query _ _ _, PMF.bind_map]
  rfl

private theorem runWith_inr_bind {β : Type} (o : List Bool → List (List Bool × Tag) →
      PMF (Tag × List (List Bool × Tag))) (m : List Bool)
    (cont : Tag → ProbOracleComp (fun _ : List Bool => Tag) β) (log : List (List Bool × Tag)) :
    ProbOracleComp.runWith o (OracleComp.query (Sum.inr m) >>= cont) log =
      (o m log).bind fun x => ProbOracleComp.runWith o (cont x.1) x.2 := by
  rw [ProbOracleComp.runWith_bind, show ProbOracleComp.runWith o (OracleComp.query (Sum.inr m))
    log = o m log from OracleComp.runWith_query _ _ _]

private theorem runWith_repeat_le (n : ℕ) (sk : List Bool) {α : Type}
    {p : ProbOracleComp (fun _ : List Bool => Tag) α} {Q : ℕ}
    (hp : ProbOracleComp.IsQueryBounded p Q) (log : List (List Bool × Tag)) :
    ((ProbOracleComp.runWith (fun q s => ProbComp.eval (M.blockwiseSigningOracle E n sk q s))
      p log).bind fun out => PMF.pure (!decide (out.2.map fun entry => entry.2.1).Nodup)) true ≤
      PMF.pure (!decide (log.map fun entry => entry.2.1).Nodup) true +
        ((log.length * Q + ∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / 2 ^ fieldWidth (M.msgLen n) := by
  induction hp generalizing log with
  | pure a k =>
    rw [ProbOracleComp.runWith_pure, PMF.pure_bind]
    exact le_self_add
  | liftBind q cont k _ ih =>
    cases q with
    | inl j =>
      simp only [Sum.elim_inl, add_zero]
      rw [runWith_inl_bind, PMF.bind_bind]
      exact PMF.bind_apply_le_on_support _ fun x _ => ih x log
    | inr m =>
      simp only [Sum.elim_inr]
      rw [runWith_inr_bind, eval_blockwiseSigningOracle]
      simp only [PMF.bind_bind, PMF.pure_bind]
      rw [PMF.bind_apply]
      refine le_trans (PMF.tsum_mul_le_card_mul_add _
        (BitString.uniformList_apply_le (fieldWidth (M.msgLen n)))
        (log.map fun entry => entry.2.1).toFinset
        (B := PMF.pure (!decide (log.map fun entry => entry.2.1).Nodup) true +
          (((log.length + 1) * k + ∑ i ∈ Finset.range k, i : ℕ) : ℝ≥0∞) /
            2 ^ fieldWidth (M.msgLen n)) fun r => ?_) ?_
      · refine PMF.bind_apply_le_on_support _ fun tags _ => (ih (r, tags) _).trans ?_
        rw [List.length_cons, List.map_cons, ← add_assoc]
        exact add_le_add (repeat_cons_le r _) le_rfl
      · exact repeat_arith _ ((List.toFinset_card_le _).trans (List.length_map _).le)

/-- If the adversary makes at most `Q` signing queries, two queries share an identifier with
probability at most `(∑ i ∈ range Q, i) / 2 ^ w`. -/
theorem blockwiseRepeatGame_le (A : BlockwiseMACAdversary) (n Q : ℕ)
    (hA : ProbOracleComp.IsQueryBounded (A n) Q) :
    ProbComp.eval (M.blockwiseRepeatGame E A n) true ≤
      ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / 2 ^ fieldWidth (M.msgLen n) := by
  rw [eval_blockwiseRepeatGame]
  refine PMF.bind_apply_le_on_support _ fun sk _ => ?_
  have h := M.runWith_repeat_le E n sk hA []
  simp only [List.map_nil, List.nodup_nil, decide_true, Bool.not_true, List.length_nil,
    zero_mul, zero_add, PMF.pure_apply, Bool.true_eq_false, ite_false] at h
  exact h

/-- Concrete security of the blockwise construction against an adversary with at most `Q`
signing queries: this is the concrete inequality behind [KatzLindell2020], Theorem 4.8. No query
or time budget is stated yet for `blockwiseReduction`, so the asymptotic statement (a secure
fixed-length scheme gives a secure variable-length scheme) does not follow from it yet. -/
theorem blockwiseGame_le (A : BlockwiseMACAdversary) (n Q : ℕ)
    (hA : ProbOracleComp.IsQueryBounded (A n) Q) :
    ProbComp.eval (M.blockwiseGame fullEncoder A n) true ≤
      ProbComp.eval (M.eufCmaGame (M.blockwiseReduction fullEncoder A) n) true +
        ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / 2 ^ fieldWidth (M.msgLen n) :=
  (M.blockwiseGame_le_add_repeat A n).trans
    (add_le_add le_rfl (M.blockwiseRepeatGame_le fullEncoder A n Q hA))

/-- Separation witness for `noIndexEncoder`: one query on `0^w ‖ 1^w`, then the output
`1^w ‖ 0^w` with the two block tags in the opposite order. -/
def swapBlocksAdversary : BlockwiseMACAdversary := fun n => do
  let tag ← ProbOracleComp.query (spec := fun _ : List Bool => Tag)
    (List.replicate (fieldWidth (M.msgLen n)) false ++
      List.replicate (fieldWidth (M.msgLen n)) true)
  return (List.replicate (fieldWidth (M.msgLen n)) true ++
    List.replicate (fieldWidth (M.msgLen n)) false, (tag.1, tag.2.reverse))

/-- Separation witness for `noLengthEncoder`: one query on `0^w ‖ 1^w`, then the output `0^w`
with the first block tag. -/
def truncateAdversary : BlockwiseMACAdversary := fun n => do
  let tag ← ProbOracleComp.query (spec := fun _ : List Bool => Tag)
    (List.replicate (fieldWidth (M.msgLen n)) false ++
      List.replicate (fieldWidth (M.msgLen n)) true)
  return (List.replicate (fieldWidth (M.msgLen n)) false, (tag.1, tag.2.take 1))

/-- Separation witness for `noIdentifierEncoder`: queries on `0^w ‖ 0^w` and `1^w ‖ 1^w`, then
the output `0^w ‖ 1^w` with the first block tag of the first answer and the second block tag of
the second answer. -/
def mixBlocksAdversary : BlockwiseMACAdversary := fun n => do
  let tag ← ProbOracleComp.query (spec := fun _ : List Bool => Tag)
    (List.replicate (fieldWidth (M.msgLen n)) false ++
      List.replicate (fieldWidth (M.msgLen n)) false)
  let tag' ← ProbOracleComp.query (spec := fun _ : List Bool => Tag)
    (List.replicate (fieldWidth (M.msgLen n)) true ++
      List.replicate (fieldWidth (M.msgLen n)) true)
  return (List.replicate (fieldWidth (M.msgLen n)) false ++
    List.replicate (fieldWidth (M.msgLen n)) true, (tag.1, tag.2.take 1 ++ tag'.2.drop 1))

private theorem blockwiseGame_eq_one {A : BlockwiseMACAdversary} {n : ℕ}
    (h : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ out ∈ (M.blockwiseRun E A n sk).support,
      (!(out.2.map Prod.fst).contains out.1.1 && M.blockwiseVerify E n sk out.1.1 out.1.2) =
        true) :
    ProbComp.eval (M.blockwiseGame E A n) true = 1 := by
  rw [eval_blockwiseGame]
  refine le_antisymm (PMF.coe_le_one _ _) ?_
  refine PMF.le_bind_apply_on_support _ fun sk hsk => ?_
  refine PMF.le_bind_apply_on_support _ fun out hout => ?_
  rw [h sk hsk out hout, PMF.pure_apply, ite_eq_left rfl]

private theorem wins_of_forall₂ {n : ℕ} {sk : List Bool} {log : List (List Bool × Tag)}
    {msg : List Bool} {tag : Tag} (hnew : msg ∉ log.map Prod.fst)
    (hm : 0 < msg.length ∧ msg.length < 2 ^ fieldWidth (M.msgLen n))
    (hr : tag.1.length = fieldWidth (M.msgLen n))
    (htags : List.Forall₂ (fun x t => M.verify sk x t = true)
      (blockInputs E (M.msgLen n) tag.1 msg) tag.2) :
    (!(log.map Prod.fst).contains msg && M.blockwiseVerify E n sk msg tag) = true := by
  have hc : (log.map Prod.fst).contains msg = false := by simpa using hnew
  simp only [hc, M.blockwiseVerify_of_forall₂ E hm hr htags, Bool.not_false, Bool.and_true]

/-- Without the block index the construction is not EUF-CMA: `swapBlocksAdversary` wins with
probability one. -/
theorem blockwiseGame_noIndex (n : ℕ) (hw : 3 ≤ fieldWidth (M.msgLen n)) :
    ProbComp.eval (M.blockwiseGame noIndexEncoder M.swapBlocksAdversary n) true = 1 := by
  refine M.blockwiseGame_eq_one noIndexEncoder fun sk hsk out hout => ?_
  supp_cases hout [blockwiseRun, swapBlocksAdversary, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure] with ⟨⟨⟨r, tags⟩, log⟩, hq, rfl⟩
  obtain ⟨rfl, hr, htags⟩ := M.mem_support_blockwiseSigningOracle noIndexEncoder hq
  have h2 := M.forall₂_of_mem_support_mapM hsk _ (fun x hx => length_of_mem_blockInputs
    (fun _ _ _ hb => length_noIndexEncoder hr hb) hx) htags
  rw [blockInputs_replicate_append hw] at h2
  obtain ⟨t1, t2, rfl, h1, h2'⟩ := forall₂_pair h2
  refine M.wins_of_forall₂ noIndexEncoder ?_ ?_ hr ?_
  · simp only [List.map_cons, List.map_nil, List.mem_singleton]
    exact replicate_append_ne (by omega) (by decide)
  · simp only [List.length_append, List.length_replicate]
    exact ⟨by omega, by have := Nat.two_mul_lt_two_pow hw; omega⟩
  · rw [blockInputs_replicate_append hw]
    exact .cons h2' (.cons h1 .nil)

/-- Without the message length the construction is not EUF-CMA: `truncateAdversary` wins with
probability one. -/
theorem blockwiseGame_noLength (n : ℕ) (hw : 3 ≤ fieldWidth (M.msgLen n)) :
    ProbComp.eval (M.blockwiseGame noLengthEncoder M.truncateAdversary n) true = 1 := by
  refine M.blockwiseGame_eq_one noLengthEncoder fun sk hsk out hout => ?_
  supp_cases hout [blockwiseRun, truncateAdversary, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure] with ⟨⟨⟨r, tags⟩, log⟩, hq, rfl⟩
  obtain ⟨rfl, hr, htags⟩ := M.mem_support_blockwiseSigningOracle noLengthEncoder hq
  have h2 := M.forall₂_of_mem_support_mapM hsk _ (fun x hx => length_of_mem_blockInputs
    (fun _ _ _ hb => length_noLengthEncoder hr hb) hx) htags
  rw [blockInputs_replicate_append hw] at h2
  obtain ⟨t1, t2, rfl, h1, -⟩ := forall₂_pair h2
  refine M.wins_of_forall₂ noLengthEncoder ?_ ?_ hr ?_
  · simp only [List.map_cons, List.map_nil, List.mem_singleton]
    intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_replicate] at this
    omega
  · simp only [List.length_replicate]
    exact ⟨by omega, by have := Nat.two_mul_lt_two_pow hw; omega⟩
  · rw [blockInputs_replicate hw]
    exact .cons h1 .nil

/-- Without the identifier the construction is not EUF-CMA: `mixBlocksAdversary` wins with
probability one. -/
theorem blockwiseGame_noIdentifier (n : ℕ) (hw : 3 ≤ fieldWidth (M.msgLen n)) :
    ProbComp.eval (M.blockwiseGame noIdentifierEncoder M.mixBlocksAdversary n) true = 1 := by
  refine M.blockwiseGame_eq_one noIdentifierEncoder fun sk hsk out hout => ?_
  supp_cases hout [blockwiseRun, mixBlocksAdversary, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure]
    with ⟨⟨⟨r, tags⟩, log⟩, hq, ⟨⟨r', tags'⟩, log'⟩, hq', rfl⟩
  obtain ⟨rfl, hr, htags⟩ := M.mem_support_blockwiseSigningOracle noIdentifierEncoder hq
  obtain ⟨rfl, -, htags'⟩ := M.mem_support_blockwiseSigningOracle noIdentifierEncoder hq'
  have h2 := M.forall₂_of_mem_support_mapM hsk _ (fun x hx => length_of_mem_blockInputs
    (fun _ _ _ hb => length_noIdentifierEncoder hb) hx) htags
  have h2' := M.forall₂_of_mem_support_mapM hsk _ (fun x hx => length_of_mem_blockInputs
    (fun _ _ _ hb => length_noIdentifierEncoder hb) hx) htags'
  rw [blockInputs_replicate_append hw] at h2 h2'
  obtain ⟨t1, t2, rfl, h1, -⟩ := forall₂_pair h2
  obtain ⟨s1, s2, rfl, -, hs2⟩ := forall₂_pair h2'
  refine M.wins_of_forall₂ noIdentifierEncoder ?_ ?_ hr ?_
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    exact ⟨replicate_append_ne (by omega) (by decide),
      replicate_append_ne (by omega) (by decide)⟩
  · simp only [List.length_append, List.length_replicate]
    exact ⟨by omega, by have := Nat.two_mul_lt_two_pow hw; omega⟩
  · rw [blockInputs_replicate_append hw]
    exact .cons h1 (.cons hs2 .nil)

end MACScheme

end Cslib.Crypto
