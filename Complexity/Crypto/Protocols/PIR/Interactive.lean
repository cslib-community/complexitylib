/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Languages.Probabilistic.Basic
public import Complexity.Computability.Communication.Rectangle
import Complexity.Probability.PMF.Map

/-!
# Interactive single-server private information retrieval

With one server, even interaction does not help: a perfectly private and perfectly correct
protocol must exchange `n` bits [Chor, Goldreich, Kushilevitz and Sudan,
Section 5.1][ChorGoldreichKushilevitzSudan1998]. `PIR.SingleServer` proves the one-round case; this
file proves the interactive one.

An interactive scheme `P : PIR.InteractiveScheme ι C D` is a deterministic two-party protocol
`P.protocol` (`Cslib.Communication.Protocol`) between the server, holding the database
`x : ι → Bool` and its coins `d : D`, and the user, holding the index `i : ι` and its coins `c : C`.
The protocol may use any number of rounds, and the coins are drawn by the probabilistic programs
`P.serverCoins` and `P.userCoins i` (the latter may depend on `i`). The *transcript*
`P.transcript x i` is the leaf the protocol reaches. It determines every bit sent, so it is
everything the server sees besides its own input. The user's output `P.run x i` is the label of
that leaf applied to the user's view `(i, c)`.

**The user's output depends on its view, not only on the transcript.** Perfect privacy
(`InteractiveScheme.IsPrivate`) says that for every database, the transcript has the same
distribution for all indices. If the output were a function of the transcript alone, it would
therefore have the same distribution for all indices, and no scheme could be correct for a
database with two different bits. So leaves are labelled by functions `ι × C → Bool`, and the user's
output may depend on its private coins as well as on the communication. In this generality, the
source's step "on the same communication C, the user must output the same bit" is replaced by the
rectangle property of protocols (`Communication.Protocol.leaf_eq_iff`). Suppose that a leaf is
reached on `(x, d₁)` with user view `(j, c₁)`, and on `(y, d₂)` with user view `(j, c₂)`. Then it is
also reached on `(y, d₂)` with user view `(j, c₁)`. On that one view, correctness forces the label
to output both `x j` and `y j`.

With that step, the source's counting argument goes through (`InteractiveScheme.injective_leaf`):
for fixed coins, the transcript determines the database. So every index has at least `2 ^ n`
possible transcripts (`InteractiveScheme.two_pow_card_le_ncard_transcripts`), the protocol tree
has at least `2 ^ n` leaves, and the protocol sends at least `n` bits on some input
(`InteractiveScheme.card_le_depth`). The privacy hypothesis is weaker than the source's, which
covers the whole view of the server; the server's own coins are independent of `i` anyway. The
server sending the database attains the bound (`InteractiveScheme.download`), so a scheme sending
at most `c` bits exists exactly when `n ≤ c` (`InteractiveScheme.exists_iff`).

The server is Alice and the user is Bob in `Communication.Protocol`.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.InteractiveScheme`: interactive single-server schemes.
* `Cslib.Crypto.Protocols.PIR.InteractiveScheme.transcript`,
  `Cslib.Crypto.Protocols.PIR.InteractiveScheme.run`: the transcript and the user's output.
* `Cslib.Crypto.Protocols.PIR.InteractiveScheme.IsCorrect`,
  `Cslib.Crypto.Protocols.PIR.InteractiveScheme.IsPrivate`: perfect correctness and privacy.
* `Cslib.Crypto.Protocols.PIR.InteractiveScheme.transcripts`: the possible transcripts for an
  index.
* `Cslib.Crypto.Protocols.PIR.InteractiveScheme.download`: the server sends the database.

## Main results

* `Cslib.Crypto.Protocols.PIR.InteractiveScheme.injective_leaf`: for fixed coins, the transcript
  determines the database.
* `Cslib.Crypto.Protocols.PIR.InteractiveScheme.two_pow_card_le_ncard_transcripts`: at least
  `2 ^ n` possible transcripts for each index.
* `Cslib.Crypto.Protocols.PIR.InteractiveScheme.two_pow_card_le_leafCount`,
  `Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_le_depth`: at least `2 ^ n` leaves and `n`
  bits.
* `Cslib.Crypto.Protocols.PIR.InteractiveScheme.exists_iff`: one server needs exactly `n` bits,
  with or without interaction.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Section 5.1; numbering of the authors' journal
  version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability Communication

/-- An interactive single-server private information retrieval scheme for databases
`x : ι → Bool`, with user coins `C` and server coins `D`
[CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]. The server (Alice) holds the database and
its coins, and the user (Bob) holds the index and its coins. Each leaf of the protocol is labelled
by the user's output as a function of its view. -/
structure InteractiveScheme (ι C D : Type) where
  /-- The user's coins for the index `i`. -/
  userCoins : ι → ProbComp C
  /-- The server's coins. -/
  serverCoins : ProbComp D
  /-- The protocol; its leaves are labelled by the user's output as a function of its view. -/
  protocol : Protocol ((ι → Bool) × D) (ι × C) (ι × C → Bool)

namespace InteractiveScheme

variable {ι C D : Type}

section Defs

variable (P : InteractiveScheme ι C D)

/-- The coins of the user, for the index `i`, and of the server, drawn independently. -/
def coins (i : ι) : ProbComp (C × D) := do
  let c ← P.userCoins i
  let d ← P.serverCoins
  pure (c, d)

/-- The transcript of the protocol on the database `x` and the index `i`: the leaf it reaches. The
leaf determines every bit sent, in order. -/
def transcript (x : ι → Bool) (i : ι) : ProbComp (Fin P.protocol.leafCount) :=
  (fun cd => P.protocol.leaf (x, cd.2) (i, cd.1)) <$> P.coins i

/-- The user's output on the database `x` and the index `i`: the label of the leaf reached,
applied to the user's view. -/
def run (x : ι → Bool) (i : ι) : ProbComp Bool :=
  (fun cd => P.protocol.leafOutput (P.protocol.leaf (x, cd.2) (i, cd.1)) (i, cd.1)) <$> P.coins i

/-- Perfect correctness: on every database, the user outputs the bit it asks for with probability
one. -/
def IsCorrect : Prop :=
  ∀ x i, ProbComp.eval (P.run x i) = PMF.pure (x i)

/-- Perfect privacy: for every database, the transcript has the same distribution for all indices.
-/
def IsPrivate : Prop :=
  ∀ x i i', ProbComp.eval (P.transcript x i) = ProbComp.eval (P.transcript x i')

/-- The possible transcripts for the index `i`: the leaves reached with positive probability on
some database. -/
noncomputable def transcripts (i : ι) : Set (Fin P.protocol.leafCount) :=
  ⋃ x, (ProbComp.eval (P.transcript x i)).support

theorem mem_support_coins_iff {i : ι} {cd : C × D} :
    cd ∈ (ProbComp.eval (P.coins i)).support ↔
      cd.1 ∈ (ProbComp.eval (P.userCoins i)).support ∧
        cd.2 ∈ (ProbComp.eval P.serverCoins).support := by
  simp only [coins, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff]
  constructor
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨hc, hd⟩
  · rintro ⟨hc, hd⟩
    exact ⟨cd.1, hc, cd.2, hd, rfl⟩

theorem mem_support_transcript_iff {x : ι → Bool} {i : ι} {t : Fin P.protocol.leafCount} :
    t ∈ (ProbComp.eval (P.transcript x i)).support ↔
      ∃ c ∈ (ProbComp.eval (P.userCoins i)).support, ∃ d ∈ (ProbComp.eval P.serverCoins).support,
        P.protocol.leaf (x, d) (i, c) = t := by
  rw [transcript, ProbComp.eval_map, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨cd, hcd, rfl⟩
    obtain ⟨hc, hd⟩ := P.mem_support_coins_iff.mp hcd
    exact ⟨cd.1, hc, cd.2, hd, rfl⟩
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨(c, d), P.mem_support_coins_iff.mpr ⟨hc, hd⟩, rfl⟩

/-- Perfect correctness holds exactly when the user outputs the right bit on all coins that can be
drawn. -/
theorem isCorrect_iff : P.IsCorrect ↔ ∀ x i, ∀ c ∈ (ProbComp.eval (P.userCoins i)).support,
    ∀ d ∈ (ProbComp.eval P.serverCoins).support,
      P.protocol.leafOutput (P.protocol.leaf (x, d) (i, c)) (i, c) = x i := by
  refine forall_congr' fun x => forall_congr' fun i => ?_
  rw [run, ProbComp.eval_map]
  constructor
  · intro h c hc d hd
    have hmem : P.protocol.leafOutput (P.protocol.leaf (x, d) (i, c)) (i, c) ∈
        ((ProbComp.eval (P.coins i)).map fun cd =>
          P.protocol.leafOutput (P.protocol.leaf (x, cd.2) (i, cd.1)) (i, cd.1)).support :=
      (PMF.mem_support_map_iff _ _ _).2 ⟨(c, d), P.mem_support_coins_iff.mpr ⟨hc, hd⟩, rfl⟩
    rwa [h, PMF.support_pure, Set.mem_singleton_iff] at hmem
  · intro h
    rw [Cslib.Probability.PMF.map_congr_on_support _ _ (Function.const _ (x i))
      fun cd hcd => h cd.1 (P.mem_support_coins_iff.mp hcd).1 cd.2
        (P.mem_support_coins_iff.mp hcd).2, PMF.map_const]

theorem isPrivate_iff : P.IsPrivate ↔
    ∀ x i i', ProbComp.eval (P.transcript x i) = ProbComp.eval (P.transcript x i') := by
  rw [IsPrivate]

end Defs

variable {P : InteractiveScheme ι C D}

/-- A correct scheme outputs the right bit on all coins that can be drawn. -/
theorem IsCorrect.leafOutput_eq (h : P.IsCorrect) (x : ι → Bool) {i : ι} {c : C} {d : D}
    (hc : c ∈ (ProbComp.eval (P.userCoins i)).support)
    (hd : d ∈ (ProbComp.eval P.serverCoins).support) :
    P.protocol.leafOutput (P.protocol.leaf (x, d) (i, c)) (i, c) = x i :=
  P.isCorrect_iff.mp h x i c hc d hd

/-- **For fixed coins, the transcript determines the database**
[CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]. If two databases `x ≠ y` reached the same
leaf, then by privacy that leaf would also be reached for an index `j` with `x j ≠ y j`, on both
databases. By the rectangle property, it is then reached on `y` with the user's view from the run
on `x`, and on that view the user would have to output both `x j` and `y j`. -/
theorem injective_leaf (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) {i : ι} {c : C} {d : D}
    (hc : c ∈ (ProbComp.eval (P.userCoins i)).support)
    (hd : d ∈ (ProbComp.eval P.serverCoins).support) :
    Function.Injective fun x : ι → Bool => P.protocol.leaf (x, d) (i, c) := by
  intro x y hxy
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  -- The leaf `t` is possible for `(x, i)` and `(y, i)`, so by privacy for `(x, j)` and `(y, j)`.
  set t := P.protocol.leaf (x, d) (i, c) with ht
  have hpossible (z : ι → Bool) (hz : P.protocol.leaf (z, d) (i, c) = t) :
      t ∈ (ProbComp.eval (P.transcript z j)).support := by
    rw [hprivate z j i]
    exact P.mem_support_transcript_iff.mpr ⟨c, hc, d, hd, hz⟩
  obtain ⟨c₁, hc₁, d₁, hd₁, h₁⟩ := P.mem_support_transcript_iff.mp (hpossible x rfl)
  obtain ⟨c₂, hc₂, d₂, hd₂, h₂⟩ := P.mem_support_transcript_iff.mp (hpossible y hxy.symm)
  -- By the rectangle property, `t` is also reached on `(y, d₂)` with the user's view `(j, c₁)`.
  have h₃ : P.protocol.leaf (y, d₂) (j, c₁) = t :=
    Protocol.leaf_eq_iff.mpr ⟨(Protocol.leaf_eq_iff.mp h₂).1, (Protocol.leaf_eq_iff.mp h₁).2⟩
  have hx := hcorrect.leafOutput_eq x hc₁ hd₁
  have hy := hcorrect.leafOutput_eq y hc₁ hd₂
  rw [h₁] at hx
  rw [h₃] at hy
  exact hj (hx.symm.trans hy)

/-- **Every index has at least `2 ^ n` possible transcripts**
[CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]. -/
theorem two_pow_card_le_ncard_transcripts [Fintype ι] (hcorrect : P.IsCorrect)
    (hprivate : P.IsPrivate) (i : ι) : 2 ^ Fintype.card ι ≤ (P.transcripts i).ncard := by
  classical
  obtain ⟨c, hc⟩ := (ProbComp.eval (P.userCoins i)).support_nonempty
  obtain ⟨d, hd⟩ := (ProbComp.eval P.serverCoins).support_nonempty
  have hsub : Set.range (fun x : ι → Bool => P.protocol.leaf (x, d) (i, c)) ⊆ P.transcripts i := by
    rintro _ ⟨x, rfl⟩
    exact Set.mem_iUnion.mpr ⟨x, P.mem_support_transcript_iff.mpr ⟨c, hc, d, hd, rfl⟩⟩
  have h := Set.ncard_le_ncard hsub
  rwa [Set.ncard_range_of_injective (injective_leaf hcorrect hprivate hc hd),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool] at h

/-- **A perfectly correct and perfectly private interactive scheme for `n`-bit databases has at
least `2 ^ n` transcripts.** -/
theorem two_pow_card_le_leafCount [Fintype ι] (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    2 ^ Fintype.card ι ≤ P.protocol.leafCount := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · rw [Fintype.card_eq_zero, pow_zero]
    exact P.protocol.leafCount_pos
  · refine (two_pow_card_le_ncard_transcripts hcorrect hprivate i).trans ?_
    exact (Set.ncard_le_card _).trans_eq (Nat.card_eq_fintype_card.trans (Fintype.card_fin _))

/-- **A perfectly correct and perfectly private single-server scheme for `n`-bit databases sends at
least `n` bits on some input, even with interaction**
[CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]. -/
theorem card_le_depth [Fintype ι] (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    Fintype.card ι ≤ P.protocol.depth :=
  (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    ((two_pow_card_le_leafCount hcorrect hprivate).trans P.protocol.leafCount_le_two_pow_depth)

/-! ### The trivial scheme -/

/-- The server sends its database, with no coins on either side, and the user reads the bit it
wants. -/
def download (n : ℕ) : InteractiveScheme (Fin n) Unit Unit where
  userCoins _ := pure ()
  serverCoins := pure ()
  protocol := Protocol.aliceSend n (fun xd => xd.1) fun x => Protocol.output fun ic => x ic.1

/-- In a protocol in which only Alice sends, the leaf does not depend on Bob's input. -/
private theorem leaf_aliceSend_output {X Y Z : Type} (n : ℕ) (msg : X → BitString n)
    (out : BitString n → Z) (x : X) (y y' : Y) :
    (Protocol.aliceSend n msg fun m => Protocol.output (out m)).leaf x y =
      (Protocol.aliceSend n msg fun m => Protocol.output (out m)).leaf x y' := by
  induction n generalizing Z with
  | zero => rfl
  | succ n ih =>
    simp only [Protocol.aliceSend, Protocol.leaf_alice]
    rw [ih (fun x => Fin.tail (msg x)) fun m => out (Fin.cons false m),
      ih (fun x => Fin.tail (msg x)) fun m => out (Fin.cons true m)]

theorem isCorrect_download (n : ℕ) : (download n).IsCorrect :=
  (download n).isCorrect_iff.mpr fun x i _ _ _ _ => by
    rw [← Protocol.run_eq_leafOutput_leaf]
    simp only [download, Protocol.run_aliceSend, Protocol.run_output]

theorem isPrivate_download (n : ℕ) : (download n).IsPrivate :=
  (download n).isPrivate_iff.mpr fun x i i' => by
    simp only [transcript, coins, download, ProbComp.eval_map, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map]
    exact congrArg PMF.pure
      (leaf_aliceSend_output n _ (fun (x : BitString n) (ic : Fin n × Unit) => x ic.1) _ _ _)

theorem depth_download (n : ℕ) : (download n).protocol.depth = n :=
  le_antisymm (Protocol.depth_aliceSend_le (d := 0) fun _ => le_rfl)
    ((Fintype.card_fin n).symm.trans_le
      (card_le_depth (isCorrect_download n) (isPrivate_download n)))

/-- **One server needs exactly `n` bits, with or without interaction**: a perfectly correct and
perfectly private interactive scheme for `n`-bit databases that sends at most `c` bits on every
input exists exactly when `n ≤ c` [CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]. -/
theorem exists_iff (n c : ℕ) :
    (∃ (C D : Type) (P : InteractiveScheme (Fin n) C D),
      P.IsCorrect ∧ P.IsPrivate ∧ P.protocol.depth ≤ c) ↔ n ≤ c := by
  constructor
  · rintro ⟨C, D, P, hcorrect, hprivate, hc⟩
    exact ((Fintype.card_fin n).symm.trans_le (card_le_depth hcorrect hprivate)).trans hc
  · intro h
    exact ⟨Unit, Unit, download n, isCorrect_download n, isPrivate_download n,
      (depth_download n).trans_le h⟩

end InteractiveScheme

end Cslib.Crypto.Protocols.PIR
