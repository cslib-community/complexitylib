/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Crypto.Computational.MAC
public import CslibFrontier.Crypto.Negligible.Dyadic
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime.Init
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
* `BlockwiseMAC.IsPolyTimeEncoder`: polynomial-time predicate for block encoders.
* `BlockwiseMACForger`: uniform word-oracle blockwise MAC forger
  (`WordOracleAdv Unit (List Bool × Tag)`).
* `MACScheme.blockwiseSign`, `MACScheme.blockwiseVerify`: the variable-length scheme.
* `MACScheme.blockwiseGame`: its fresh-message EUF-CMA experiment, and
  `MACScheme.blockwiseRepeatGame`: the event that two signing queries share an identifier.
* `MACScheme.blockwiseReduction`: the fixed-length adversary built from a blockwise adversary.
* `MACScheme.blockwiseBoundedReduction`: the uniform strict oracle-PPT fixed-length forger built
  from a `BlockwiseMACForger` by truncating fixed-length oracle replies to a polynomial bound.
* `MACScheme.BlockwiseEUFCMA`: uniform asymptotic EUF-CMA security against strict oracle-PPT
  `BlockwiseMACForger`s.

## Main results

* `MACScheme.isPPTOn_blockwiseSign`, `MACScheme.computableInPolyTime_blockwiseVerify`,
  `MACScheme.isPPTOn_blockwiseSigningOracle`, `MACScheme.isPPT_blockwiseGame`: strict PPT and
  plain polynomial-time certificates for the honest algorithms, signing oracle, and experiment.
* `MACScheme.isOraclePPT_blockwiseBoundedReduction`: `blockwiseBoundedReduction` is uniformly
  strict oracle PPT.
* `MACScheme.blockwiseGame_le_add_repeat`: the blockwise advantage is at most the advantage of
  `blockwiseReduction` against `M` plus the probability of a repeated identifier.
* `MACScheme.blockwiseRepeatGame_le`: with at most `Q` signing queries, a repeated identifier has
  probability at most `(∑ i ∈ range Q, i) / 2 ^ w`.
* `MACScheme.blockwiseGame_le`: the combined concrete bound ([KatzLindell2020], Theorem 4.8).
* `MACScheme.EUFCMA.blockwiseEUFCMA`: uniform asymptotic security (`M.EUFCMA →
  M.BlockwiseEUFCMA fullEncoder` when `PolynomiallyLowerBounded M.msgLen`).
* `MACScheme.blockwiseGame_noIndex`, `MACScheme.blockwiseGame_noLength`,
  `MACScheme.blockwiseGame_noIdentifier`, and `MACScheme.not_blockwiseEUFCMA_noIndexEncoder`,
  `MACScheme.not_blockwiseEUFCMA_noLengthEncoder`,
  `MACScheme.not_blockwiseEUFCMA_noIdentifierEncoder`: concrete and uniform oracle-PPT
  separations. Each insecure variant admits an explicit strict oracle-PPT forger with at most two
  signing queries that wins with probability one when `w ≥ 3`.

## Implementation notes

The encoder is a parameter, so the construction and its three variants share one definition.
Messages outside the domain have no block inputs and never verify. The repeated-identifier bound
adds up, query by query, the chance that a new identifier equals an earlier one, which gives
`Q (Q - 1) / 2 ^ (w + 1)`. To obtain a uniform strict oracle-PPT reduction without changing the
concrete experiment `blockwiseReduction`, `blockwiseBoundedSimulator` truncates each fixed-length
oracle reply to `tagBound n` bits; when `tagBound` covers all honest tags of `M.sign`, this agrees
identically with `blockwiseSimulator`.

## References

* [J. Katz and Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace BlockwiseMAC

/-- The width `L / 4` of each field of an `L`-bit block input. -/
@[expose] def fieldWidth (L : ℕ) : ℕ := L / 4

/-- The number of `w`-bit blocks, rounded up, in a `len`-bit message. -/
@[expose] def blockCount (w len : ℕ) : ℕ := (len + w - 1) / w

/-- Block `i` (counting from `0`) of `m`, padded with zeros to exactly `w` bits. -/
@[expose] def messageBlock (w : ℕ) (m : List Bool) (i : ℕ) : List Bool :=
  (m.drop (i * w) ++ List.replicate w false).take w

/-- A block encoder takes a field width, an input length, an identifier, a message length, a
block index and a block, and returns an input for the fixed-length MAC. -/
abbrev Encoder : Type := ℕ → ℕ → List Bool → ℕ → ℕ → List Bool → List Bool

/-- The encoder of the construction: identifier, length, index, block, then zero padding. -/
@[expose] def fullEncoder (w L : ℕ) (r : List Bool) (len idx : ℕ) (block : List Bool) : List Bool :=
  r ++ BitString.lowBits w len ++ BitString.lowBits w idx ++ block ++
    List.replicate (L - 4 * w) false

/-- Insecure variant that omits the identifier. -/
@[expose] def noIdentifierEncoder (w L : ℕ) (_r : List Bool) (len idx : ℕ) (block : List Bool) :
    List Bool :=
  BitString.lowBits w len ++ BitString.lowBits w idx ++ block ++ List.replicate (L - 3 * w) false

/-- Insecure variant that omits the message length. -/
@[expose] def noLengthEncoder (w L : ℕ) (r : List Bool) (_len idx : ℕ) (block : List Bool) :
    List Bool :=
  r ++ BitString.lowBits w idx ++ block ++ List.replicate (L - 3 * w) false

/-- Insecure variant that omits the block index. -/
@[expose] def noIndexEncoder (w L : ℕ) (r : List Bool) (len _idx : ℕ) (block : List Bool) :
    List Bool :=
  r ++ BitString.lowBits w len ++ block ++ List.replicate (L - 3 * w) false

/-- The fixed-length inputs that encoder `E` assigns to `m` under identifier `r`, one per block,
with indices starting at `1`. The list is empty unless `0 < |m| < 2 ^ w`. -/
@[expose] def blockInputs (E : Encoder) (L : ℕ) (r m : List Bool) : List (List Bool) :=
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

/-- The number of block inputs of a message `m` is at most `m.length`. -/
theorem length_blockInputs_le (E : Encoder) (L : ℕ) (r m : List Bool) :
    (blockInputs E L r m).length ≤ m.length := by
  rw [blockInputs]
  split_ifs with hm
  · rw [List.length_map, List.length_range]
    exact blockCount_le (fieldWidth_pos hm.1 hm.2) hm.1
  · simp

/-! ### Encodings and polynomial-time certificates -/

/-- Binary encoding of a blockwise tag `(r, tags)`. -/
abbrev encTag : Tag ↪ List Bool :=
  encPair encBits (encList encBits)

/-- Total polynomial-time decoder for `encTag`. -/
def tagDecoder : Decoder encTag :=
  Decoder.pair Decoder.bits (Decoder.list Decoder.bits)

/-- Binary encoding of a candidate message/tag forgery `(msg, tag)`. -/
abbrev encForgerOutput : List Bool × Tag ↪ List Bool :=
  encPair encBits encTag

/-- Binary encoding of a blockwise signing log `List (List Bool × Tag)`. -/
abbrev encLog : List (List Bool × Tag) ↪ List Bool :=
  encList encForgerOutput

/-- Binary encoding of the inputs `(n, sk, m)` to `MACScheme.blockwiseSign`. -/
abbrev encSignInput : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Binary encoding of the inputs `(n, sk, m, tag)` to `MACScheme.blockwiseVerify`. -/
abbrev encVerifyInput : ℕ × List Bool × List Bool × Tag ↪ List Bool :=
  encPair encUnary (encPair encBits encForgerOutput)

/-- Binary encoding of the six arguments `(w, L, r, len, idx, block)` to a block `Encoder`. -/
abbrev encEncoderInput : ℕ × ℕ × List Bool × ℕ × ℕ × List Bool ↪ List Bool :=
  encPair encUnary
    (encPair encUnary
      (encPair encBits (encPair encUnary (encPair encUnary encBits))))

/-- Binary encoding of the arguments `(L, log, msg, tag)` to `freshBlockPair`. -/
abbrev encFreshBlockInput :
    ℕ × List (List Bool × Tag) × List Bool × Tag ↪ List Bool :=
  encPair encUnary (encPair encLog encForgerOutput)

/-- `tagDecoder.decode` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_tagDecoder_decode :
    ComputableInPolyTime tagDecoder.decode encBits encTag :=
  tagDecoder.computableInPolyTime

/-- Composition rule for `tagDecoder.decode`. -/
@[fun_prop]
theorem computableInPolyTime_tagDecoder_decode_comp {γ : Type} {encIn : γ ↪ List Bool}
    {w : γ → List Bool} (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun a => tagDecoder.decode (w a)) encIn encTag :=
  tagDecoder.computableInPolyTime.comp hw

/-- `fieldWidth` is computable in polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_fieldWidth :
    ComputableInPolyTime fieldWidth encUnary encUnary := by
  unfold fieldWidth
  fun_prop

/-- Composition rule for `fieldWidth`. -/
@[fun_prop]
theorem computableInPolyTime_fieldWidth_comp {γ : Type} {encIn : γ ↪ List Bool}
    {L : γ → ℕ} (hL : ComputableInPolyTime L encIn encUnary) :
    ComputableInPolyTime (fun a => fieldWidth (L a)) encIn encUnary :=
  computableInPolyTime_fieldWidth.comp hL

/-- `blockCount` is computable in polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_blockCount :
    ComputableInPolyTime (fun p : ℕ × ℕ => blockCount p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  unfold blockCount
  fun_prop

/-- Composition rule for `blockCount`. -/
@[fun_prop]
theorem computableInPolyTime_blockCount_comp {γ : Type} {encIn : γ ↪ List Bool}
    {w len : γ → ℕ} (hw : ComputableInPolyTime w encIn encUnary)
    (hlen : ComputableInPolyTime len encIn encUnary) :
    ComputableInPolyTime (fun a => blockCount (w a) (len a)) encIn encUnary :=
  computableInPolyTime_blockCount.comp (hw.prod hlen)

/-- `messageBlock` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_messageBlock :
    ComputableInPolyTime (fun p : ℕ × List Bool × ℕ => messageBlock p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encUnary)) encBits := by
  unfold messageBlock
  fun_prop

/-- Composition rule for `messageBlock`. -/
@[fun_prop]
theorem computableInPolyTime_messageBlock_comp {γ : Type} {encIn : γ ↪ List Bool}
    {w i : γ → ℕ} {m : γ → List Bool}
    (hw : ComputableInPolyTime w encIn encUnary)
    (hm : ComputableInPolyTime m encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun a => messageBlock (w a) (m a) (i a)) encIn encBits :=
  computableInPolyTime_messageBlock.comp (hw.prod (hm.prod hi))

/-- A block `Encoder` is polynomial-time when it is computable in polynomial time with unary
widths/lengths/indices and bit-string identifier/block inputs. -/
@[expose] def IsPolyTimeEncoder (E : Encoder) : Prop :=
  ComputableInPolyTime
    (fun p : ℕ × ℕ × List Bool × ℕ × ℕ × List Bool =>
      E p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    encEncoderInput encBits

/-- Unfolded characterization of `IsPolyTimeEncoder`. -/
theorem isPolyTimeEncoder_iff (E : Encoder) :
    IsPolyTimeEncoder E ↔
      ComputableInPolyTime
        (fun p : ℕ × ℕ × List Bool × ℕ × ℕ × List Bool =>
          E p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
        encEncoderInput encBits :=
  Iff.rfl

/-- Construct `IsPolyTimeEncoder` from a `ComputableInPolyTime` certificate on `encEncoderInput`. -/
theorem IsPolyTimeEncoder.of_computableInPolyTime {E : Encoder}
    (hE : ComputableInPolyTime
      (fun p : ℕ × ℕ × List Bool × ℕ × ℕ × List Bool =>
        E p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      encEncoderInput encBits) :
    IsPolyTimeEncoder E :=
  hE

/-- Composition rule for a polynomial-time block `Encoder`. -/
theorem IsPolyTimeEncoder.comp {E : Encoder} (hE : IsPolyTimeEncoder E)
    {γ : Type} {encIn : γ ↪ List Bool}
    {w L len idx : γ → ℕ} {r block : γ → List Bool}
    (hw : ComputableInPolyTime w encIn encUnary)
    (hL : ComputableInPolyTime L encIn encUnary)
    (hr : ComputableInPolyTime r encIn encBits)
    (hlen : ComputableInPolyTime len encIn encUnary)
    (hidx : ComputableInPolyTime idx encIn encUnary)
    (hblock : ComputableInPolyTime block encIn encBits) :
    ComputableInPolyTime (fun a => E (w a) (L a) (r a) (len a) (idx a) (block a))
      encIn encBits :=
  ComputableInPolyTime.comp hE (hw.prod (hL.prod (hr.prod (hlen.prod (hidx.prod hblock)))))

/-- `fullEncoder` is polynomial-time. -/
theorem isPolyTimeEncoder_fullEncoder : IsPolyTimeEncoder fullEncoder := by
  unfold IsPolyTimeEncoder fullEncoder
  fun_prop

/-- `noIdentifierEncoder` is polynomial-time. -/
theorem isPolyTimeEncoder_noIdentifierEncoder : IsPolyTimeEncoder noIdentifierEncoder := by
  unfold IsPolyTimeEncoder noIdentifierEncoder
  fun_prop

/-- `noLengthEncoder` is polynomial-time. -/
theorem isPolyTimeEncoder_noLengthEncoder : IsPolyTimeEncoder noLengthEncoder := by
  unfold IsPolyTimeEncoder noLengthEncoder
  fun_prop

/-- `noIndexEncoder` is polynomial-time. -/
theorem isPolyTimeEncoder_noIndexEncoder : IsPolyTimeEncoder noIndexEncoder := by
  unfold IsPolyTimeEncoder noIndexEncoder
  fun_prop

/-- `blockInputs E` is computable in polynomial time whenever `E` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_blockInputs {E : Encoder} (hE : IsPolyTimeEncoder E) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => blockInputs E p.1 p.2.1 p.2.2)
      encSignInput (encList encBits) := by
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List Bool × List Bool) × ℕ =>
        E (fieldWidth q.1.1) q.1.1 q.1.2.1 q.1.2.2.length (q.2 + 1)
          (messageBlock (fieldWidth q.1.1) q.1.2.2 q.2))
      (encPair encSignInput encUnary) encBits :=
    hE.comp (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold blockInputs
  exact ComputableInPolyTime.ite_decide (by fun_prop)
    (ComputableInPolyTime.mapWithInput (by fun_prop) hstep)
    (by fun_prop)

/-- Composition rule for `blockInputs E`. -/
@[fun_prop]
theorem computableInPolyTime_blockInputs_comp {E : Encoder} (hE : IsPolyTimeEncoder E)
    {γ : Type} {encIn : γ ↪ List Bool}
    {L : γ → ℕ} {r m : γ → List Bool}
    (hL : ComputableInPolyTime L encIn encUnary)
    (hr : ComputableInPolyTime r encIn encBits)
    (hm : ComputableInPolyTime m encIn encBits) :
    ComputableInPolyTime (fun a => blockInputs E (L a) (r a) (m a))
      encIn (encList encBits) :=
  (computableInPolyTime_blockInputs hE).comp (hL.prod (hr.prod hm))

/-- `authenticatedInputs E` is computable in polynomial time whenever `E` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_authenticatedInputs {E : Encoder} (hE : IsPolyTimeEncoder E) :
    ComputableInPolyTime
      (fun p : ℕ × List (List Bool × Tag) => authenticatedInputs E p.1 p.2)
      (encPair encUnary encLog) (encList encBits) := by
  have heq : (fun p : ℕ × List (List Bool × Tag) => authenticatedInputs E p.1 p.2) =
      fun p => p.2.flatMap fun entry => (blockInputs E p.1 entry.2.1 entry.1).reverse := by
    funext p
    rfl
  rw [heq]
  fun_prop

/-- Composition rule for `authenticatedInputs E`. -/
@[fun_prop]
theorem computableInPolyTime_authenticatedInputs_comp {E : Encoder} (hE : IsPolyTimeEncoder E)
    {γ : Type} {encIn : γ ↪ List Bool}
    {L : γ → ℕ} {log : γ → List (List Bool × Tag)}
    (hL : ComputableInPolyTime L encIn encUnary)
    (hlog : ComputableInPolyTime log encIn encLog) :
    ComputableInPolyTime (fun a => authenticatedInputs E (L a) (log a))
      encIn (encList encBits) :=
  (computableInPolyTime_authenticatedInputs hE).comp (hL.prod hlog)

/-- `freshBlockPair E` is computable in polynomial time whenever `E` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_freshBlockPair {E : Encoder} (hE : IsPolyTimeEncoder E) :
    ComputableInPolyTime
      (fun p : ℕ × List (List Bool × Tag) × List Bool × Tag =>
        freshBlockPair E p.1 p.2.1 p.2.2.1 p.2.2.2)
      encFreshBlockInput (encPair encBits encBits) := by
  unfold freshBlockPair
  simp only [List.contains_eq_mem]
  exact ComputableInPolyTime.optionGetDWithInput
    (ComputableInPolyTime.findWithInput (by fun_prop) (by fun_prop))
    (by fun_prop)

/-- Composition rule for `freshBlockPair E`. -/
@[fun_prop]
theorem computableInPolyTime_freshBlockPair_comp {E : Encoder} (hE : IsPolyTimeEncoder E)
    {γ : Type} {encIn : γ ↪ List Bool}
    {L : γ → ℕ} {log : γ → List (List Bool × Tag)}
    {msg : γ → List Bool} {tag : γ → Tag}
    (hL : ComputableInPolyTime L encIn encUnary)
    (hlog : ComputableInPolyTime log encIn encLog)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (htag : ComputableInPolyTime tag encIn encTag) :
    ComputableInPolyTime (fun a => freshBlockPair E (L a) (log a) (msg a) (tag a))
      encIn (encPair encBits encBits) :=
  ComputableInPolyTime.comp (g := fun a => (L a, log a, msg a, tag a))
    (computableInPolyTime_freshBlockPair hE) (hL.prod (hlog.prod (hmsg.prod htag)))

end BlockwiseMAC

/-- An adaptive adversary against a variable-length MAC: on security parameter `n` it queries a
blockwise signing oracle and outputs a candidate message/tag pair. -/
abbrev BlockwiseMACAdversary : Type :=
  ℕ → ProbOracleComp (fun _ : List Bool => BlockwiseMAC.Tag) (List Bool × BlockwiseMAC.Tag)

/-- A uniform adaptive word-oracle forger against a variable-length MAC: on security parameter `n`
and auxiliary word `aux`, it queries the single-channel word oracle on messages `m : List Bool`
(receiving encoded blockwise tags `BlockwiseMAC.encTag tag : List Bool`) and outputs a candidate
forgery `(msg, tag)`. -/
abbrev BlockwiseMACForger : Type :=
  ℕ → List Bool → WordOracleComp Unit (List Bool × BlockwiseMAC.Tag)

/-- Embed a uniform word-oracle forger as a `BlockwiseMACAdversary` by running it on empty
auxiliary input `[]` and encoding each returned `BlockwiseMAC.Tag` with `BlockwiseMAC.encTag`. -/
def BlockwiseMACForger.toAdversary (F : BlockwiseMACForger) : BlockwiseMACAdversary :=
  fun n =>
    ProbOracleComp.simulate
      (fun request : Unit × List Bool => do
        let tag ← ProbOracleComp.query (spec := fun _ : List Bool => BlockwiseMAC.Tag) request.2
        return BlockwiseMAC.encTag tag)
      (F n [])

/-- Embedding a `BlockwiseMACForger` as a `BlockwiseMACAdversary` preserves query budgets. -/
theorem BlockwiseMACForger.isQueryBounded_toAdversary (F : BlockwiseMACForger) (n Q : ℕ)
    (hQ : ProbOracleComp.IsQueryBounded (F n []) Q) :
    ProbOracleComp.IsQueryBounded (F.toAdversary n) Q := by
  unfold BlockwiseMACForger.toAdversary
  refine ProbOracleComp.IsQueryBounded.simulate (fun request => ?_) hQ
  exact (ProbOracleComp.IsQueryBounded.query
    (spec := fun _ : List Bool => BlockwiseMAC.Tag) request.2).bind
    fun tag => .pure (BlockwiseMAC.encTag tag) 0

/-- Convert a `BlockwiseMACAdversary` into a `BlockwiseMACForger` by answering each signing query
`m` with `BlockwiseMAC.tagDecoder.decode` of the first `replyBound n m.length` bits of the external
word-oracle reply. -/
def BlockwiseMACAdversary.toForger (replyBound : ℕ → ℕ → ℕ) (A : BlockwiseMACAdversary) :
    BlockwiseMACForger :=
  fun n _ =>
    ProbOracleComp.simulate
      (fun m : List Bool => do
        let raw ← (ProbOracleComp.query ((), m) : WordOracleComp Unit (List Bool))
        return BlockwiseMAC.tagDecoder.decode (raw.take (replyBound n m.length)))
      (A n)

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
signing queries: this is the concrete inequality behind [KatzLindell2020], Theorem 4.8. Because
`blockwiseReduction` forwards arbitrary fixed-length oracle replies without a length bound, the
unbounded reduction itself has no uniform oracle-PPT certificate; see `blockwiseBoundedReduction`,
`blockwiseGame_le_blockwiseBoundedReduction`, and `EUFCMA.blockwiseEUFCMA` for the truncated
oracle-PPT reduction and the resulting uniform asymptotic security theorem. -/
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

/-! ### Efficiency of the honest algorithms, game, and reduction -/

variable {E}

/-- `blockwiseSign E` is strict PPT whenever `E` is a polynomial-time encoder. -/
@[program_certificate]
theorem isPPTOn_blockwiseSign (hE : IsPolyTimeEncoder E) :
    IsPPTOn encSignInput encTag
      (fun p : ℕ × List Bool × List Bool => M.blockwiseSign E p.1 p.2.1 p.2.2) := by
  have hmsgLen := M.msgLen_polyTime
  have hsample : IsPPTOn encSignInput encBits
      (fun p : ℕ × List Bool × List Bool =>
        BitString.sampleList (fieldWidth (M.msgLen p.1))) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have hsign : IsPPTOn (encPair (encPair encSignInput encBits) encBits) encBits
      (fun q : ((ℕ × List Bool × List Bool) × List Bool) × List Bool =>
        M.sign q.1.1.2.1 q.2) :=
    M.sign_ppt.preprocess
      (input := encPair (encPair encSignInput encBits) encBits)
      (prepare := fun q : ((ℕ × List Bool × List Bool) × List Bool) × List Bool =>
        (q.1.1.2.1, q.2))
      (by fun_prop)
  have htags : IsPPTOn (encPair encSignInput encBits) (encList encBits)
      (fun q : (ℕ × List Bool × List Bool) × List Bool =>
        (blockInputs E (M.msgLen q.1.1) q.2 q.1.2.2).mapM (M.sign q.1.2.1)) :=
    IsPPTOn.mapMWith hsign (by fun_prop)
  unfold blockwiseSign
  simpa only [bind_pure_comp] using
    hsample.bind_with (htags.map_with (f := fun q tags => (q.2, tags)) (by fun_prop))

/-- `blockwiseVerify E` is computable in polynomial time whenever `E` is a polynomial-time
encoder. -/
@[fun_prop]
theorem computableInPolyTime_blockwiseVerify (hE : IsPolyTimeEncoder E) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × Tag =>
        M.blockwiseVerify E p.1 p.2.1 p.2.2.1 p.2.2.2)
      encVerifyInput encBool := by
  have hmsgLen := M.msgLen_polyTime
  have hverify := M.verify_polyTime
  have hall : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × Tag =>
        ((blockInputs E (M.msgLen p.1) p.2.2.2.1 p.2.2.1).zip p.2.2.2.2).all
          fun q => M.verify p.2.1 q.1 q.2)
      encVerifyInput encBool :=
    ComputableInPolyTime.allWithEncoding
      (par := fun p : ℕ × List Bool × List Bool × Tag => p.2.1)
      (test := fun q : List Bool × List Bool × List Bool => M.verify q.1 q.2.1 q.2.2)
      hverify (by fun_prop) (by fun_prop)
  unfold blockwiseVerify
  fun_prop

/-- Composition rule for `blockwiseVerify E`. -/
@[fun_prop]
theorem computableInPolyTime_blockwiseVerify_comp (hE : IsPolyTimeEncoder E)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {sk m : γ → List Bool} {tag : γ → Tag}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hm : ComputableInPolyTime m encIn encBits)
    (htag : ComputableInPolyTime tag encIn encTag) :
    ComputableInPolyTime (fun a => M.blockwiseVerify E (n a) (sk a) (m a) (tag a))
      encIn encBool :=
  (M.computableInPolyTime_blockwiseVerify hE).comp (hn.prod (hsk.prod (hm.prod htag)))

/-- `blockwiseSigningOracle E` is strict PPT in `(n, sk, m)` and the signing log `log`. -/
@[program_certificate]
theorem isPPTOn_blockwiseSigningOracle (hE : IsPolyTimeEncoder E) :
    IsPPTOn (encPair encSignInput encLog) (encPair encTag encLog)
      (fun p : (ℕ × List Bool × List Bool) × List (List Bool × Tag) =>
        M.blockwiseSigningOracle E p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hsign := (M.isPPTOn_blockwiseSign hE).preprocess
    (input := encPair encSignInput encLog)
    (prepare := fun p : (ℕ × List Bool × List Bool) × List (List Bool × Tag) => p.1)
    (by fun_prop)
  unfold blockwiseSigningOracle
  simpa only [bind_pure_comp] using
    hsign.map_with (f := fun p tag => (tag, (p.1.2.2, tag) :: p.2)) (by fun_prop)

/-- Every `MACScheme` and polynomial-time `Encoder` admits a plain polynomial-time bound
`replyBound n ℓ` on the encoded length `(encTag tag).length` of every blockwise tag produced on an
`ℓ`-bit message at security parameter `n`. -/
theorem exists_blockwiseSign_length_bound (hE : IsPolyTimeEncoder E) :
    ∃ replyBound : ℕ → ℕ → ℕ,
      ComputableInPolyTime (fun p : ℕ × ℕ => replyBound p.1 p.2)
        (encPair encUnary encUnary) encUnary ∧
      ∀ n, ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ m,
        ∀ tag ∈ (ProbComp.eval (M.blockwiseSign E n sk m)).support,
          (encTag tag).length ≤ replyBound n m.length := by
  obtain ⟨ck, dk, hlenk⟩ := M.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := (M.isPPTOn_blockwiseSign hE).length_le
  refine ⟨fun n ℓ => cs * (2 * n + 2 * (2 * (ck * (n + 1) ^ dk) + ℓ + 1) + 4) ^ ds,
    by fun_prop, fun n sk hsk m tag htag => ?_⟩
  have hkeyLen := hlenk n sk hsk
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkeyLen
  have htagLen := hlens (n, sk, m) tag htag
  have hlenInput : (encSignInput (n, sk, m)).length = 2 * n + 2 * sk.length + m.length + 2 := by
    simp only [encSignInput, length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
    omega
  exact htagLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by omega) ds))

variable (E) in
/-- Word-oracle wrapper around `blockwiseSigningOracle`: tags `request.2` using `blockwiseSign`,
replies with the word `encTag tag`, and logs `(request.2, tag)`. -/
noncomputable def blockwiseWordSigningOracle (n : ℕ) (sk : List Bool)
    (request : Unit × List Bool) :
    StateT (List (List Bool × Tag)) ProbComp (List Bool) :=
  fun log => do
    let tag ← M.blockwiseSign E n sk request.2
    return (encTag tag, (request.2, tag) :: log)

/-- `blockwiseWordSigningOracle E` is strict PPT on handler calls with caller `(n, sk)`. -/
@[program_certificate]
theorem isPPTOn_blockwiseWordSigningOracle (hE : IsPolyTimeEncoder E) :
    IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) encLog))
      (encPair encBits encLog)
      (fun call : (ℕ × List Bool) × (Unit × List Bool) × List (List Bool × Tag) =>
        M.blockwiseWordSigningOracle E call.1.1 call.1.2 call.2.1 call.2.2) := by
  have hsign := (M.isPPTOn_blockwiseSign hE).preprocess
    (input := encPair (encPair encUnary encBits)
      (encPair (encPair (encFinEnum Unit) encBits) encLog))
    (prepare := fun call : (ℕ × List Bool) × (Unit × List Bool) × List (List Bool × Tag) =>
      (call.1.1, call.1.2, call.2.1.2))
    (by fun_prop)
  unfold blockwiseWordSigningOracle
  simpa only [bind_pure_comp] using
    hsign.map_with (f := fun call tag => (encTag tag, (call.2.1.2, tag) :: call.2.2)) (by fun_prop)

private theorem run_interpret_blockwiseSigningOracle_toAdversary (F : BlockwiseMACForger)
    (n : ℕ) (sk : List Bool) (log : List (List Bool × Tag)) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.blockwiseSigningOracle E n sk)) (F.toAdversary n)).run log =
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.blockwiseWordSigningOracle E n sk)) (F n [])).run log := by
  rw [BlockwiseMACForger.toAdversary, ProbOracleComp.interpret_simulate]
  congr 3
  funext request log'
  change (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.blockwiseSigningOracle E n sk))
      (do
        let tag ← ProbOracleComp.query (spec := fun _ : List Bool => Tag) request.2
        return encTag tag)).run log' =
    (M.blockwiseWordSigningOracle E n sk request).run log'
  simp only [OracleComp.interpret_bind, ProbOracleComp.interpret_query, OracleComp.interpret_pure,
    StateT.run_bind, StateT.run_pure]
  simp only [blockwiseSigningOracle, blockwiseWordSigningOracle, StateT.run, bind_assoc, pure_bind]

/-- `blockwiseGame E F.toAdversary` is strict PPT on the security parameter `n` whenever `E` is
a polynomial-time encoder and `F` is a strict oracle-PPT blockwise forger. -/
@[program_certificate]
theorem isPPTOn_blockwiseGame (hE : IsPolyTimeEncoder E) {F : BlockwiseMACForger}
    (hF : IsOraclePPT encForgerOutput F) :
    IsPPTOn encUnary encBool (M.blockwiseGame E F.toAdversary) := by
  obtain ⟨cs, ds, hlens⟩ := (M.isPPTOn_blockwiseSign hE).length_le
  have hrun : IsPPTOn (encPair encUnary encBits) (encPair encForgerOutput encLog)
      (fun c : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.blockwiseWordSigningOracle E c.1 c.2)) (F c.1 [])).run []) := by
    refine hF.run_interpret_preprocess'
      (input := encPair encUnary encBits)
      (prepare := fun c : ℕ × List Bool => (c.1, ([] : List Bool)))
      (initial := fun _ : ℕ × List Bool => ([] : List (List Bool × Tag)))
      (resources := fun c w =>
        2 * (2 * w.length + cs * ((encSignInput (c.1, c.2, w)).length + 1) ^ ds + 1) + 2)
      (by fun_prop) (M.isPPTOn_blockwiseWordSigningOracle hE) (by fun_prop)
      (fun _ _ => True) (fun _ => trivial) (by fun_prop) ?_
    intro c request log _ result hresult
    simp only [blockwiseWordSigningOracle, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨tag, htag, rfl⟩ := hresult
    have htagLen := hlens (c.1, c.2, request.2) tag htag
    have hlogLen : (encLog ((request.2, tag) :: log)).length =
        2 * (2 * request.2.length + (encTag tag).length + 1) + 1 + (encLog log).length := by
      simp only [encLog, encForgerOutput, encList_cons, List.length_append, length_frame,
        length_encPair, encBits_apply]
      omega
    refine ⟨trivial, ?_, ?_⟩
    · dsimp only
      omega
    · dsimp only
      omega
  have hgame : M.blockwiseGame E F.toAdversary = fun n =>
      M.keyGen n >>= fun sk =>
      (fun out : (List Bool × Tag) × List (List Bool × Tag) =>
        !decide (out.1.1 ∈ out.2.map Prod.fst) && M.blockwiseVerify E n sk out.1.1 out.1.2) <$>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.blockwiseWordSigningOracle E n sk)) (F n [])).run [] := by
    funext n
    simp only [blockwiseGame, run_interpret_blockwiseSigningOracle_toAdversary,
      List.contains_eq_mem, bind_pure_comp]
  rw [hgame]
  exact M.keyGen_ppt.bind_with (hrun.map_with (by fun_prop))

/-- `blockwiseGame E F.toAdversary` is strict PPT whenever `E` is a polynomial-time encoder and
`F` is a strict oracle-PPT blockwise forger. -/
theorem isPPT_blockwiseGame (hE : IsPolyTimeEncoder E) {F : BlockwiseMACForger}
    (hF : IsOraclePPT encForgerOutput F) :
    IsPPT encBool (fun n _ => M.blockwiseGame E F.toAdversary n) :=
  ((M.isPPTOn_blockwiseGame hE hF).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-! ### Truncated oracle-PPT simulator and reduction -/

private def mapQueryTakeStep (limit : ℕ) (state : List (List Bool) × List (List Bool)) :
    WordOracleComp Unit (List (List Bool) × List (List Bool)) :=
  (fun tag => (state.1.tail, state.2 ++ [tag])) <$>
    (List.take limit <$>
      (ProbOracleComp.query ((), state.1.headD []) : WordOracleComp Unit (List Bool)))

private theorem iterate_mapQueryTakeStep (limit : ℕ) (xs acc : List (List Bool)) :
    Prod.snd <$> OracleComp.iterate xs.length (mapQueryTakeStep limit) (xs, acc) =
      (acc ++ ·) <$> xs.mapM (fun x =>
        List.take limit <$>
          (ProbOracleComp.query ((), x) : WordOracleComp Unit (List Bool))) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, OracleComp.iterate_succ_bind, mapQueryTakeStep,
      List.headD_cons, List.tail_cons, List.mapM_cons, map_bind, bind_map_left, ih,
      List.append_assoc, List.singleton_append]
    simp only [map_pure, bind_pure_comp]

private theorem isOraclePPTOn_mapM_query_take {α : Type} {input : α ↪ List Bool}
    {list : α → List (List Bool)} {limit : α → ℕ}
    (hlist : ComputableInPolyTime list input (encList encBits))
    (hlimit : ComputableInPolyTime limit input encUnary) :
    IsOraclePPTOn input (encList encBits) (fun a =>
      (list a).mapM fun x =>
        List.take (limit a) <$>
          (ProbOracleComp.query ((), x) : WordOracleComp Unit (List Bool))) := by
  let stateEncoding : List (List Bool) × List (List Bool) ↪ List Bool :=
    encPair (encList encBits) (encList encBits)
  have hcount : ComputableInPolyTime (fun a => (list a).length) input encUnary :=
    (ComputableInPolyTime.length_list encBits).comp hlist
  have hinitial : ComputableInPolyTime (fun a => (list a, ([] : List (List Bool))))
      input stateEncoding :=
    hlist.prod (ComputableInPolyTime.const [])
  have htail : ComputableInPolyTime
      (fun p : α × List (List Bool) × List (List Bool) => p.2.1.tail)
      (encPair input stateEncoding) (encList encBits) := by fun_prop
  have hstep : IsOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun p : α × List (List Bool) × List (List Bool) => mapQueryTakeStep (limit p.1) p.2) := by
    unfold mapQueryTakeStep
    exact (IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)).map_with'
      (f := fun (p : α × List (List Bool) × List (List Bool)) tag =>
        (p.2.1.tail, p.2.2 ++ [tag]))
      (by fun_prop)
  have hpoly : PolyBounded (fun a => (input a).length) (fun a => 2 * limit a + 2) := by
    have h1 : ComputableInPolyTime (fun a => 2 * limit a + 2) input encUnary := by fun_prop
    simpa only [encUnary_apply, List.length_replicate] using h1.polyBounded_length
  have hloop : IsOraclePPTOn input stateEncoding
      (fun a => OracleComp.iterate (list a).length (mapQueryTakeStep (limit a)) (list a, [])) := by
    refine IsOraclePPTOn.iterateWith_of_bounded_growth' hcount hinitial hstep hpoly ?_
    intro a state next hnext
    unfold mapQueryTakeStep at hnext
    obtain ⟨tag, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
    have htailLen : (encList encBits state.1.tail).length ≤ (encList encBits state.1).length :=
      ((List.tail_sublist state.1).flatMap (frame ∘ encBits)).length_le
    have htake : (raw.take (limit a)).length ≤ limit a := List.length_take_le _ _
    simp only [stateEncoding, length_encPair, encList_append, encList_cons, encList_nil,
      List.append_nil, List.length_append, length_frame, encBits_apply]
    omega
  simpa only [iterate_mapQueryTakeStep, List.nil_append, id_map'] using
    hloop.map' (ComputableInPolyTime.snd (encList encBits) (encList encBits))

private theorem length_encList_of_mem_support_mapM_query_take (k : ℕ) (xs : List (List Bool))
    {tags : List (List Bool)}
    (htags : tags ∈ OracleComp.support
      (xs.mapM fun x =>
        List.take k <$> (ProbOracleComp.query ((), x) : WordOracleComp Unit (List Bool)))) :
    (encList encBits tags).length ≤ xs.length * (2 * k + 2) := by
  have hrel := (OracleComp.mem_supportWith_mapM_iff _ _ xs tags).mp htags
  have htagLen : ∀ tag ∈ tags, (encBits tag).length ≤ k := by
    intro tag htag
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp htag
    obtain ⟨raw, -, hraw⟩ :=
      OracleComp.mem_supportWith_map_iff.mp (hrel.get (hrel.length_eq.symm ▸ i.2) i.2)
    simpa only [encBits_apply, ← hraw] using List.length_take_le k raw
  refine (Turing.MultiTapeTM.length_encList_le encBits tags htagLen).trans ?_
  rw [← hrel.length_eq]
  exact Nat.mul_le_mul_left xs.length (by omega)

variable (E) in
/-- Answers a word-oracle blockwise signing query `((), m)` with fixed-length signing queries, one
per block input in `blockInputs E (M.msgLen n) r m`, truncating each reply to `tagBound n` bits,
encoding the resulting blockwise tag `(r, tags)` with `encTag`, and logging `(m, (r, tags))`. -/
noncomputable def blockwiseBoundedSimulator (tagBound : ℕ → ℕ) (n : ℕ)
    (request : Unit × List Bool) :
    StateT (List (List Bool × Tag)) (WordOracleComp Unit) (List Bool) :=
  fun log => do
    let r ← ProbOracleComp.sample (BitString.sampleList (fieldWidth (M.msgLen n)))
    let tags ← (blockInputs E (M.msgLen n) r request.2).mapM fun x =>
      List.take (tagBound n) <$>
        (ProbOracleComp.query ((), x) : WordOracleComp Unit (List Bool))
    return (encTag (r, tags), (request.2, (r, tags)) :: log)

variable (E) in
/-- The uniform strict oracle-PPT fixed-length forger built from a word-oracle blockwise forger
`F`: run `F n []` against `blockwiseBoundedSimulator E tagBound n`, then output the first block
input of its message that no simulated query covered, with the matching block tag. -/
noncomputable def blockwiseBoundedReduction (tagBound : ℕ → ℕ) (F : BlockwiseMACForger) :
    Forger := fun n _ => do
  let ((msg, tag), log) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (M.blockwiseBoundedSimulator E tagBound n)) (F n [])).run []
  return freshBlockPair E (M.msgLen n) log msg tag

/-- `blockwiseBoundedSimulator E tagBound` is strict oracle PPT in the caller `(n, aux)`, the
request and the signing log `log`, for every polynomial-time `E` and `tagBound`. -/
theorem isOraclePPTOn_blockwiseBoundedSimulator (hE : IsPolyTimeEncoder E)
    {tagBound : ℕ → ℕ} (htagBound : ComputableInPolyTime tagBound encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) encLog))
      (encPair encBits encLog)
      (fun call : (ℕ × List Bool) × (Unit × List Bool) × List (List Bool × Tag) =>
        M.blockwiseBoundedSimulator E tagBound call.1.1 call.2.1 call.2.2) := by
  let encCall :=
    encPair (encPair encUnary encBits) (encPair (encPair (encFinEnum Unit) encBits) encLog)
  have hmsgLen := M.msgLen_polyTime
  have hsample : IsOraclePPTOn encCall encBits
      (fun call : (ℕ × List Bool) × (Unit × List Bool) × List (List Bool × Tag) =>
        ProbOracleComp.sample (BitString.sampleList (fieldWidth (M.msgLen call.1.1)))) :=
    (ComputableInPolyTime.sampleList (by fun_prop)).isOraclePPTOn (Operation := Unit)
  have htags : IsOraclePPTOn (encPair encCall encBits) (encList encBits)
      (fun p : ((ℕ × List Bool) × (Unit × List Bool) × List (List Bool × Tag)) × List Bool =>
        (blockInputs E (M.msgLen p.1.1.1) p.2 p.1.2.1.2).mapM fun x =>
          List.take (tagBound p.1.1.1) <$>
            (ProbOracleComp.query ((), x) : WordOracleComp Unit (List Bool))) :=
    isOraclePPTOn_mapM_query_take (by fun_prop) (by fun_prop)
  unfold blockwiseBoundedSimulator
  simpa only [bind_pure_comp] using
    hsample.bind_with
      (htags.map_with'
        (f := fun p tags => (encTag (p.2, tags), (p.1.2.1.2, (p.2, tags)) :: p.1.2.2))
        (by fun_prop))

private theorem blockwiseBoundedSimulator_bound {tagBound : ℕ → ℕ}
    (c : ℕ × List Bool) (request : Unit × List Bool) (log : List (List Bool × Tag))
    {result : List Bool × List (List Bool × Tag)}
    (hresult : result ∈ OracleComp.support
      (M.blockwiseBoundedSimulator E tagBound c.1 request log)) :
    let tagLen := 2 * fieldWidth (M.msgLen c.1) + request.2.length * (2 * tagBound c.1 + 2) + 1
    result.1.length ≤ 2 * (2 * request.2.length + tagLen + 1) + 2 ∧
      (encLog result.2).length ≤
        (encLog log).length + (2 * (2 * request.2.length + tagLen + 1) + 2) := by
  simp only [blockwiseBoundedSimulator, OracleComp.mem_supportWith_bind_iff,
    ProbOracleComp.support_sample, BitString.eval_sampleList, OracleComp.supportWith_pure,
    Set.mem_singleton_iff] at hresult
  obtain ⟨r, hr, tags, htags, rfl⟩ := hresult
  have hrlen := BitString.length_of_mem_support_uniformList hr
  have htagsLen := (length_encList_of_mem_support_mapM_query_take (tagBound c.1) _ htags).trans
    (Nat.mul_le_mul_right _ (length_blockInputs_le E (M.msgLen c.1) r request.2))
  have hencTag : (encTag (r, tags)).length ≤
      2 * fieldWidth (M.msgLen c.1) + request.2.length * (2 * tagBound c.1 + 2) + 1 := by
    simp only [encTag, length_encPair, encBits_apply, hrlen]
    omega
  have hlogLen : (encLog ((request.2, (r, tags)) :: log)).length =
      2 * (2 * request.2.length + (encTag (r, tags)).length + 1) + 1 + (encLog log).length := by
    simp only [encLog, encForgerOutput, encList_cons, List.length_append, length_frame,
      length_encPair, encBits_apply]
    omega
  refine ⟨?_, ?_⟩
  · dsimp only
    omega
  · dsimp only
    omega

/-- `blockwiseBoundedReduction E tagBound F` is uniformly strict oracle PPT whenever `E` is a
polynomial-time encoder, `tagBound` is polynomial-time, and `F` is a strict oracle-PPT blockwise
forger. -/
theorem isOraclePPT_blockwiseBoundedReduction (hE : IsPolyTimeEncoder E)
    {tagBound : ℕ → ℕ} (htagBound : ComputableInPolyTime tagBound encUnary encUnary)
    {F : BlockwiseMACForger} (hF : IsOraclePPT encForgerOutput F) :
    IsOraclePPT (encPair encBits encBits) (M.blockwiseBoundedReduction E tagBound F) := by
  have hmsgLen := M.msgLen_polyTime
  have heq : M.blockwiseBoundedReduction E tagBound F = fun n _ =>
      (fun out : (List Bool × Tag) × List (List Bool × Tag) =>
        freshBlockPair E (M.msgLen n) out.2 out.1.1 out.1.2) <$>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (M.blockwiseBoundedSimulator E tagBound n)) (F n [])).run [] := by
    funext n aux
    simp only [blockwiseBoundedReduction, bind_pure_comp]
  rw [heq]
  refine ((hF.run_interpret_preprocess_open'
      (input := encPair encUnary encBits)
      (prepare := fun c : ℕ × List Bool => (c.1, ([] : List Bool)))
      (initial := fun _ : ℕ × List Bool => ([] : List (List Bool × Tag)))
      (resources := fun c w =>
        2 * (2 * w.length +
          (2 * fieldWidth (M.msgLen c.1) + w.length * (2 * tagBound c.1 + 2) + 1) + 1) + 2)
      (by fun_prop) (M.isOraclePPTOn_blockwiseBoundedSimulator hE htagBound) (by fun_prop)
      (fun _ _ => True) (fun _ => trivial) (by fun_prop)
      (fun c request log _ result hresult =>
        ⟨trivial, M.blockwiseBoundedSimulator_bound c request log hresult⟩)).map_with'
    (by fun_prop)).isOraclePPT

private theorem runWith_mapM_query_take {n : ℕ} {sk : List Bool} {tagBound : ℕ → ℕ}
    (htagBound : ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n)
    (xs : List (List Bool)) (hxs : ∀ x ∈ xs, x.length = M.msgLen n) (log : List (List Bool)) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (M.signingOracle sk q s))
      (xs.mapM fun x =>
        List.take (tagBound n) <$>
          (ProbOracleComp.query ((), x) : WordOracleComp Unit (List Bool))) log =
      (ProbComp.eval (xs.mapM (M.sign sk))).map fun tags => (tags, xs.reverse ++ log) := by
  induction xs generalizing log with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have hxs' : ∀ y ∈ xs, y.length = M.msgLen n := fun y hy => hxs y (by simp [hy])
    simp only [List.mapM_cons, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, ih hxs']
    simp only [signingOracle, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind, PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def,
      Prod.map_apply, id_eq, List.reverse_cons, List.append_assoc, List.singleton_append]
    refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
    rw [List.take_of_length_le (htagBound x hx tag htag)]

private theorem runWith_blockwiseBoundedSimulator (F : BlockwiseMACForger) (tagBound : ℕ → ℕ)
    (n : ℕ) (sk : List Bool)
    (htagBound : ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n)
    (hElen : ∀ len idx r b, r.length = fieldWidth (M.msgLen n) →
      b.length = fieldWidth (M.msgLen n) →
        (E (fieldWidth (M.msgLen n)) (M.msgLen n) r len idx b).length = M.msgLen n) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (M.signingOracle sk q s))
      ((OracleComp.interpret (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (M.blockwiseBoundedSimulator E tagBound n)) (F n [])).run []) [] =
      ProbOracleComp.runWith (fun q s => ProbComp.eval (M.signingOracle sk q s))
        ((OracleComp.interpret (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (M.blockwiseSimulator E n)) (F.toAdversary n)).run []) [] := by
  rw [BlockwiseMACForger.toAdversary, ProbOracleComp.interpret_simulate,
    ProbOracleComp.runWith_run_interpret, ProbOracleComp.runWith_run_interpret]
  refine congrArg (PMF.map _) (congrArg (fun o => ProbOracleComp.runWith o (F n []) ([], []))
    (funext fun request => funext fun state => congrArg (PMF.map _) ?_))
  simp only [OracleComp.interpret_bind, ProbOracleComp.interpret_query, OracleComp.interpret_pure,
    StateT.run_bind, StateT.run_pure]
  simp only [blockwiseBoundedSimulator, blockwiseSimulator, StateT.run,
    bind_assoc, pure_bind, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    ProbOracleComp.runWith_pure, BitString.eval_sampleList, PMF.bind_map, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun r hr => ?_
  have hrlen := BitString.length_of_mem_support_uniformList hr
  rw [M.runWith_mapM_query_take htagBound _
      (fun x hx => length_of_mem_blockInputs (fun len idx b hb => hElen len idx r b hrlen hb) hx),
    M.runWith_mapM_query]

/-- When `tagBound n` bounds all honest tags of `M.sign sk` on `M.msgLen n`-bit messages, running
`blockwiseBoundedReduction fullEncoder tagBound F` in `M.eufCmaGame` has the exact same output
distribution as running `blockwiseReduction fullEncoder F.toAdversary`. -/
theorem eval_eufCmaGame_blockwiseBoundedReduction (F : BlockwiseMACForger) (tagBound : ℕ → ℕ)
    (n : ℕ)
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.eufCmaGame (M.blockwiseBoundedReduction fullEncoder tagBound F) n) =
      ProbComp.eval (M.eufCmaGame (M.blockwiseReduction fullEncoder F.toAdversary) n) := by
  simp only [eufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith]
  simp only [blockwiseBoundedReduction, blockwiseReduction, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_pure]
  rw [M.runWith_blockwiseBoundedSimulator F tagBound n sk (htagBound sk hsk)
    (fun _ _ _ _ hr hb => length_fullEncoder hr hb)]

/-- Concrete security of the blockwise construction with `blockwiseBoundedReduction`: for any
word-oracle forger `F` making at most `Q` signing queries and any `tagBound` covering honest tags,
the blockwise forgery probability is at most the EUF-CMA success of
`blockwiseBoundedReduction fullEncoder tagBound F` plus `(∑ i ∈ range Q, i) / 2 ^ w`. -/
theorem blockwiseGame_le_blockwiseBoundedReduction (F : BlockwiseMACForger) (tagBound : ℕ → ℕ)
    (n Q : ℕ) (hF : ProbOracleComp.IsQueryBounded (F n []) Q)
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.blockwiseGame fullEncoder F.toAdversary n) true ≤
      ProbComp.eval (M.eufCmaGame (M.blockwiseBoundedReduction fullEncoder tagBound F) n) true +
        ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / 2 ^ fieldWidth (M.msgLen n) := by
  rw [M.eval_eufCmaGame_blockwiseBoundedReduction F tagBound n htagBound]
  exact M.blockwiseGame_le F.toAdversary n Q (F.isQueryBounded_toAdversary n Q hF)

/-- `Game.succProbability` form of `blockwiseGame_le_blockwiseBoundedReduction` in `ℝ≥0`. -/
theorem succProbability_blockwiseGame_le (F : BlockwiseMACForger) (tagBound : ℕ → ℕ)
    (n Q : ℕ) (hF : ProbOracleComp.IsQueryBounded (F n []) Q)
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n) :
    Game.succProbability (ProbComp.eval (M.blockwiseGame fullEncoder F.toAdversary n)) ≤
      Game.succProbability
        (ProbComp.eval (M.eufCmaGame (M.blockwiseBoundedReduction fullEncoder tagBound F) n)) +
        ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0) / 2 ^ fieldWidth (M.msgLen n) := by
  let err : ℝ≥0 := ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0) / 2 ^ fieldWidth (M.msgLen n)
  have herr : (err : ℝ≥0∞) =
      ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / 2 ^ fieldWidth (M.msgLen n) := by
    simp [err, ENNReal.coe_div (pow_ne_zero _ two_ne_zero)]
  have hle := M.blockwiseGame_le_blockwiseBoundedReduction F tagBound n Q hF htagBound
  rw [← herr] at hle
  have hmono := ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.coe_ne_top⟩) hle
  rwa [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top,
    ENNReal.toNNReal_coe] at hmono

/-! ### Uniform asymptotic security and separations -/

variable (E) in
/-- Existential unforgeability of the blockwise variable-length MAC with block encoder `E` under
adaptive chosen-message attack ([KatzLindell2020], Construction 4.7 and Theorem 4.8) against
uniform strict oracle-PPT word-oracle forgers (`BlockwiseMACForger`). -/
@[expose] def BlockwiseEUFCMA : Prop :=
  Game.Indistinguishable
    (fun (F : BlockwiseMACForger) n => ProbComp.eval (M.blockwiseGame E F.toAdversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encForgerOutput)

variable {M}

/-- Blockwise EUF-CMA security gives negligible forging probability for every oracle-PPT
blockwise forger. -/
theorem BlockwiseEUFCMA.negligible (h : M.BlockwiseEUFCMA E) (F : BlockwiseMACForger)
    (hF : IsOraclePPT encForgerOutput F) :
    Negligible (fun n =>
      Game.succProbability (ProbComp.eval (M.blockwiseGame E F.toAdversary n))) := by
  unfold BlockwiseEUFCMA at h
  exact Game.Indistinguishable.negligible_succProbability h F hF

/-- **Uniform security of the blockwise variable-length MAC** ([KatzLindell2020], Theorem 4.8):
if `M` is an `EUFCMA`-secure fixed-length MAC whose message-length schedule `M.msgLen` is
polynomially lower-bounded (which holds automatically when `M.msgLen = id`), then the blockwise
variable-length MAC with `fullEncoder` is `BlockwiseEUFCMA`-secure. -/
theorem EUFCMA.blockwiseEUFCMA (h : M.EUFCMA)
    (hmsgLen : PolynomiallyLowerBounded M.msgLen := by fun_prop) :
    M.BlockwiseEUFCMA fullEncoder := by
  obtain ⟨tagBound, htagBoundPoly, htagBound⟩ := M.exists_tag_length_bound_of_length_eq
  apply Game.Indistinguishable.of_negligible_succProbability
  intro F hF
  obtain ⟨c, d, hFbounds⟩ := hF.query_bounds
  let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hQpoly : PolynomiallyBounded Q := by
    dsimp only [Q]
    fun_prop
  have hw : PolynomiallyLowerBounded (fun n => fieldWidth (M.msgLen n)) :=
    hmsgLen.div_const (by decide)
  have hpow : Negligible (fun n => ((2 : ℝ≥0) ^ fieldWidth (M.msgLen n))⁻¹) :=
    negligible_inv_two_pow.comp_polynomiallyLowerBounded hw
  have hcol : Negligible (fun n =>
      ((∑ i ∈ Finset.range (Q n), i : ℕ) : ℝ≥0) / 2 ^ fieldWidth (M.msgLen n)) := by
    refine negligible_of_le (Negligible.polynomiallyBounded_div (hQpoly.mul hQpoly) hpow)
      fun n => ?_
    refine div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (by positivity)
    calc
      ∑ i ∈ Finset.range (Q n), i ≤ ∑ _i ∈ Finset.range (Q n), Q n :=
        Finset.sum_le_sum fun i hi => (Finset.mem_range.mp hi).le
      _ = Q n * Q n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hred := h.negligible (M.blockwiseBoundedReduction fullEncoder tagBound F)
    (M.isOraclePPT_blockwiseBoundedReduction isPolyTimeEncoder_fullEncoder htagBoundPoly hF)
  refine negligible_of_le (hred.add hcol) fun n => ?_
  have hFn : ProbOracleComp.IsQueryBounded (F n []) (Q n) := by
    simpa [Q, Nat.add_assoc] using (hFbounds n []).1
  exact M.succProbability_blockwiseGame_le F tagBound n (Q n) hFn (htagBound n)

variable (M E) in
/-- When `replyBound n m.length` covers the encoded length of every honest blockwise tag on `m`,
converting a `BlockwiseMACAdversary` to a `BlockwiseMACForger` and back preserves the game
distribution. -/
theorem eval_blockwiseGame_toForger (A : BlockwiseMACAdversary) (replyBound : ℕ → ℕ → ℕ) (n : ℕ)
    (hbound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ m,
      ∀ tag ∈ (ProbComp.eval (M.blockwiseSign E n sk m)).support,
        (encTag tag).length ≤ replyBound n m.length) :
    ProbComp.eval (M.blockwiseGame E (A.toForger replyBound).toAdversary n) =
      ProbComp.eval (M.blockwiseGame E A n) := by
  simp only [blockwiseGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith]
  congr 1
  rw [BlockwiseMACForger.toAdversary, BlockwiseMACAdversary.toForger,
    ProbOracleComp.simulate_simulate, ProbOracleComp.runWith_simulate]
  congr 1
  funext m log
  simp only [ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query,
    ProbOracleComp.simulate_pure, bind_assoc, pure_bind, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, blockwiseSigningOracle,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
  rw [List.take_of_length_le (hbound sk hsk m tag htag), tagDecoder.decode_enc]

variable (M) in
/-- `M.swapBlocksAdversary.toForger replyBound` is strict oracle PPT for any polynomial-time
`replyBound`. -/
theorem isOraclePPT_toForger_swapBlocksAdversary {replyBound : ℕ → ℕ → ℕ}
    (hbound : ComputableInPolyTime (fun p : ℕ × ℕ => replyBound p.1 p.2)
      (encPair encUnary encUnary) encUnary) :
    IsOraclePPT encForgerOutput (M.swapBlocksAdversary.toForger replyBound) := by
  have hmsgLen := M.msgLen_polyTime
  have heq : M.swapBlocksAdversary.toForger replyBound = fun n _ =>
      (fun raw : List Bool =>
        let tag := tagDecoder.decode raw
        (List.replicate (fieldWidth (M.msgLen n)) true ++
          List.replicate (fieldWidth (M.msgLen n)) false, (tag.1, tag.2.reverse))) <$>
        (List.take
          (replyBound n
            (List.replicate (fieldWidth (M.msgLen n)) false ++
              List.replicate (fieldWidth (M.msgLen n)) true).length) <$>
          ProbOracleComp.query
            ((), List.replicate (fieldWidth (M.msgLen n)) false ++
              List.replicate (fieldWidth (M.msgLen n)) true)) := by
    funext n aux
    simp only [BlockwiseMACAdversary.toForger, swapBlocksAdversary, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_def]
  rw [heq]
  exact ((IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)).map_with'
    (by fun_prop)).isOraclePPT

variable (M) in
/-- `M.truncateAdversary.toForger replyBound` is strict oracle PPT for any polynomial-time
`replyBound`. -/
theorem isOraclePPT_toForger_truncateAdversary {replyBound : ℕ → ℕ → ℕ}
    (hbound : ComputableInPolyTime (fun p : ℕ × ℕ => replyBound p.1 p.2)
      (encPair encUnary encUnary) encUnary) :
    IsOraclePPT encForgerOutput (M.truncateAdversary.toForger replyBound) := by
  have hmsgLen := M.msgLen_polyTime
  have heq : M.truncateAdversary.toForger replyBound = fun n _ =>
      (fun raw : List Bool =>
        let tag := tagDecoder.decode raw
        (List.replicate (fieldWidth (M.msgLen n)) false, (tag.1, tag.2.take 1))) <$>
        (List.take
          (replyBound n
            (List.replicate (fieldWidth (M.msgLen n)) false ++
              List.replicate (fieldWidth (M.msgLen n)) true).length) <$>
          ProbOracleComp.query
            ((), List.replicate (fieldWidth (M.msgLen n)) false ++
              List.replicate (fieldWidth (M.msgLen n)) true)) := by
    funext n aux
    simp only [BlockwiseMACAdversary.toForger, truncateAdversary, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_def]
  rw [heq]
  exact ((IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)).map_with'
    (by fun_prop)).isOraclePPT

variable (M) in
/-- `M.mixBlocksAdversary.toForger replyBound` is strict oracle PPT for any polynomial-time
`replyBound`. -/
theorem isOraclePPT_toForger_mixBlocksAdversary {replyBound : ℕ → ℕ → ℕ}
    (hbound : ComputableInPolyTime (fun p : ℕ × ℕ => replyBound p.1 p.2)
      (encPair encUnary encUnary) encUnary) :
    IsOraclePPT encForgerOutput (M.mixBlocksAdversary.toForger replyBound) := by
  have hmsgLen := M.msgLen_polyTime
  have heq : M.mixBlocksAdversary.toForger replyBound = fun n _ =>
      (List.take
        (replyBound n
          (List.replicate (fieldWidth (M.msgLen n)) false ++
            List.replicate (fieldWidth (M.msgLen n)) false).length) <$>
        ProbOracleComp.query
          ((), List.replicate (fieldWidth (M.msgLen n)) false ++
            List.replicate (fieldWidth (M.msgLen n)) false)) >>= fun raw =>
      (fun raw' : List Bool =>
        (List.replicate (fieldWidth (M.msgLen n)) false ++
          List.replicate (fieldWidth (M.msgLen n)) true,
          ((tagDecoder.decode raw).1,
            (tagDecoder.decode raw).2.take 1 ++ (tagDecoder.decode raw').2.drop 1))) <$>
        (List.take
          (replyBound n
            (List.replicate (fieldWidth (M.msgLen n)) true ++
              List.replicate (fieldWidth (M.msgLen n)) true).length) <$>
          ProbOracleComp.query
            ((), List.replicate (fieldWidth (M.msgLen n)) true ++
              List.replicate (fieldWidth (M.msgLen n)) true)) := by
    funext n aux
    simp only [BlockwiseMACAdversary.toForger, mixBlocksAdversary, ProbOracleComp.simulate_bind,
      ProbOracleComp.simulate_query, ProbOracleComp.simulate_pure, bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_def]
  rw [heq]
  have hq1 : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        List.take
          (replyBound p.1
            (List.replicate (fieldWidth (M.msgLen p.1)) false ++
              List.replicate (fieldWidth (M.msgLen p.1)) false).length) <$>
          ProbOracleComp.query
            ((), List.replicate (fieldWidth (M.msgLen p.1)) false ++
              List.replicate (fieldWidth (M.msgLen p.1)) false)) :=
    IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)
  have hq2 : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun q : (ℕ × List Bool) × List Bool =>
        List.take
          (replyBound q.1.1
            (List.replicate (fieldWidth (M.msgLen q.1.1)) true ++
              List.replicate (fieldWidth (M.msgLen q.1.1)) true).length) <$>
          ProbOracleComp.query
            ((), List.replicate (fieldWidth (M.msgLen q.1.1)) true ++
              List.replicate (fieldWidth (M.msgLen q.1.1)) true)) :=
    IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)
  exact (hq1.bind_with (hq2.map_with' (by fun_prop))).isOraclePPT

private theorem not_negligible_of_eventually_eq_one {f : ℕ → ℝ≥0}
    (hf : ∀ᶠ n in Filter.atTop, f n = 1) : ¬ Negligible f := fun hneg =>
  not_negligible_const one_ne_zero
    (negligible_of_eventually_le hneg (hf.mono fun _ hn => hn.symm.le))

/-- Without the block index (`noIndexEncoder`), the blockwise construction is not
`BlockwiseEUFCMA`-secure whenever `3 ≤ fieldWidth (M.msgLen n)` eventually. -/
theorem not_blockwiseEUFCMA_noIndexEncoder
    (hw : ∀ᶠ n in Filter.atTop, 3 ≤ fieldWidth (M.msgLen n)) :
    ¬ M.BlockwiseEUFCMA noIndexEncoder := by
  intro hsec
  obtain ⟨replyBound, hboundPoly, hbound⟩ :=
    M.exists_blockwiseSign_length_bound isPolyTimeEncoder_noIndexEncoder
  have hneg := hsec.negligible (M.swapBlocksAdversary.toForger replyBound)
    (M.isOraclePPT_toForger_swapBlocksAdversary hboundPoly)
  refine not_negligible_of_eventually_eq_one ?_ hneg
  filter_upwards [hw] with n hn
  rw [M.eval_blockwiseGame_toForger noIndexEncoder M.swapBlocksAdversary replyBound n (hbound n),
    Game.succProbability, M.blockwiseGame_noIndex n hn, ENNReal.toNNReal_one]

/-- Without the message length (`noLengthEncoder`), the blockwise construction is not
`BlockwiseEUFCMA`-secure whenever `3 ≤ fieldWidth (M.msgLen n)` eventually. -/
theorem not_blockwiseEUFCMA_noLengthEncoder
    (hw : ∀ᶠ n in Filter.atTop, 3 ≤ fieldWidth (M.msgLen n)) :
    ¬ M.BlockwiseEUFCMA noLengthEncoder := by
  intro hsec
  obtain ⟨replyBound, hboundPoly, hbound⟩ :=
    M.exists_blockwiseSign_length_bound isPolyTimeEncoder_noLengthEncoder
  have hneg := hsec.negligible (M.truncateAdversary.toForger replyBound)
    (M.isOraclePPT_toForger_truncateAdversary hboundPoly)
  refine not_negligible_of_eventually_eq_one ?_ hneg
  filter_upwards [hw] with n hn
  rw [M.eval_blockwiseGame_toForger noLengthEncoder M.truncateAdversary replyBound n (hbound n),
    Game.succProbability, M.blockwiseGame_noLength n hn, ENNReal.toNNReal_one]

/-- Without the identifier (`noIdentifierEncoder`), the blockwise construction is not
`BlockwiseEUFCMA`-secure whenever `3 ≤ fieldWidth (M.msgLen n)` eventually. -/
theorem not_blockwiseEUFCMA_noIdentifierEncoder
    (hw : ∀ᶠ n in Filter.atTop, 3 ≤ fieldWidth (M.msgLen n)) :
    ¬ M.BlockwiseEUFCMA noIdentifierEncoder := by
  intro hsec
  obtain ⟨replyBound, hboundPoly, hbound⟩ :=
    M.exists_blockwiseSign_length_bound isPolyTimeEncoder_noIdentifierEncoder
  have hneg := hsec.negligible (M.mixBlocksAdversary.toForger replyBound)
    (M.isOraclePPT_toForger_mixBlocksAdversary hboundPoly)
  refine not_negligible_of_eventually_eq_one ?_ hneg
  filter_upwards [hw] with n hn
  rw [M.eval_blockwiseGame_toForger noIdentifierEncoder M.mixBlocksAdversary replyBound n
      (hbound n),
    Game.succProbability, M.blockwiseGame_noIdentifier n hn, ENNReal.toNNReal_one]

end MACScheme

end Cslib.Crypto
