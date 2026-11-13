/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Interactive

/-!
# Multi-server interactive private information retrieval and full-coalition lower bounds

`PIR.Interactive` formalizes arbitrary-round single-server private information retrieval
([Chor, Goldreich, Kushilevitz and Sudan, Section 5.1][ChorGoldreichKushilevitzSudan1998]), while
`PIR.Collusion` extends `t`-privacy and the `n`-bit full-coalition lower bound (`|S| ≤ t`) to
one-round `k`-server schemes.

This module models **adaptive multi-round `k`-server PIR** (`PIR.MultiInteractiveScheme`) where the
`k` servers do not observe one another's channels:

* **Channel-isolated interaction tree (`PIR.ChannelMsg`, `PIR.MultiRoundTree`).** At each internal
  node the user either sends one bit to a chosen server `s : S` (`sendTo s`, logged on `s`'s channel
  as `ChannelMsg.fromUser b`) or receives one bit from `s` (`recvFrom s`, logged on `s`'s channel as
  `ChannelMsg.fromServer b`), while server `s`'s response strategy `serverBit s x (d s) (hist s)`
  depends *only* on the database `x`, server `s`'s own randomness `d s`, and the directional channel
  history `hist s : List ChannelMsg` of bits previously exchanged on server `s`'s channel (allowing
  a server to emit multi-bit replies across consecutive `recvFrom s` steps without dummy user bits).
* **Coalition privacy (`MultiInteractiveScheme.IsTPrivate`).** A coalition `T : Finset S` observes
  the sub-trace `coalitionTranscript T x i` of all directional channel events `(s, msg)` exchanged
  with servers `s ∈ T`. `IsTPrivate t` asks this sub-trace distribution to be independent of `i`
  whenever `T.card ≤ t` (with `1`-privacy hiding each individual server's channel transcript). As in
  `PIR.Interactive`, comparing communication sub-trace laws rather than `(serverCoins, sub-trace)`
  views is equivalent for deterministic servers
  ([CGKS, Section 2.2, p. 5][ChorGoldreichKushilevitzSudan1998]) and weaker — hence yielding a
  stronger lower bound — when servers draw private coins.
* **Full-coalition compilation to `PIR.InteractiveScheme` (`toInteractiveScheme`).** Compiling a
  `MultiInteractiveScheme` into a two-party `Communication.Protocol` between the combined server
  coalition (Alice) and the user (Bob) preserves `depth` (`depth_compile`) and `run`
  (`run_toInteractiveScheme`), and recovers the reached protocol leaf from the full trace
  `coalitionTranscript Finset.univ` (`isPrivate_toInteractiveScheme_of_card_le`). Consequently,
  whenever all servers may collude (`|S| ≤ t`), `PIR.InteractiveScheme.card_le_depth` and
  `PIR.InteractiveScheme.card_mul_le_depth` immediately force protocol depth at least `|ι|` bits on
  Boolean databases (`card_le_depth_of_card_le`) and `|ι| · |κ|` bits on `(κ → Bool)` block
  databases (`card_mul_le_depth_of_card_le`), without re-proving rectangle injectivity.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.ChannelMsg`: directional 1-bit event (`fromUser` or `fromServer`) on a
  server's channel.
* `Cslib.Crypto.Protocols.PIR.MultiRoundTree`: adaptive user-driven interaction trees over servers
  `S`.
* `Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme`: channel-isolated multi-round `k`-server PIR
  schemes.
* `Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.coalitionTranscript`,
  `Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.IsTPrivate`: coalition transcript laws and
  `t`-privacy.
* `Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.toInteractiveScheme`: compilation to a
  two-party `InteractiveScheme` between the combined server family and the user.

## Main results

* `Cslib.Crypto.Protocols.PIR.MultiRoundTree.depth_compile`: compilation preserves worst-case bit
  depth.
* `Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.isPrivate_toInteractiveScheme_of_card_le`:
  full-coalition `t`-privacy (`|S| ≤ t`) implies two-party `InteractiveScheme.IsPrivate`.
* `Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.card_le_depth_of_card_le`,
  `Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.card_mul_le_depth_of_card_le`: even with
  arbitrary multi-round interaction, `|S| ≤ t` forces at least `|ι|` bits (`|ι| · |κ|` bits for
  blocks).

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Sections 2.2, 4 and 5.1; numbering of the
  authors' journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability Communication

@[expose] public section

/-- A single directional bit event on a server's channel: either sent by the user (`fromUser`) or
sent by the server (`fromServer`). -/
inductive ChannelMsg where
  /-- One bit sent from the user to the server. -/
  | fromUser (b : Bool)
  /-- One bit sent from the server to the user. -/
  | fromServer (b : Bool)
  deriving DecidableEq, Repr

end

/-- Extract the underlying payload bit from a `ChannelMsg`. -/
@[expose] def ChannelMsg.bit : ChannelMsg → Bool
  | .fromUser b => b
  | .fromServer b => b

/-- An adaptive multi-round interaction tree between a user (holding `y : Y`) and servers `s : S`,
producing an output in `Z`. Server replies are supplied separately by channel-isolated server
strategies so no server's reply can depend on another server's messages. -/
inductive MultiRoundTree (S Y Z : Type) where
  /-- Terminate with leaf label `z`. -/
  | output (z : Z)
  /-- The user sends `bit y` to server `s`, branching on the bit sent. -/
  | sendTo (s : S) (bit : Y → Bool) (ifFalse ifTrue : MultiRoundTree S Y Z)
  /-- The user receives one bit from server `s`, branching on the bit received. -/
  | recvFrom (s : S) (ifFalse ifTrue : MultiRoundTree S Y Z)

namespace MultiRoundTree

variable {S X Y Z : Type} {D : S → Type}

/-- Worst-case number of bits exchanged along any branch of the interaction tree. -/
@[expose] def depth : MultiRoundTree S Y Z → ℕ
  | output _ => 0
  | sendTo _ _ p₀ p₁ => max p₀.depth p₁.depth + 1
  | recvFrom _ p₀ p₁ => max p₀.depth p₁.depth + 1

/-- Compile a `MultiRoundTree` together with channel-isolated server strategies `serverBit` and
current per-server directional channel histories `hist` into a two-party `Communication.Protocol`
between the combined server family (Alice) and the user (Bob). -/
@[expose] def compile [DecidableEq S] (serverBit : (s : S) → X → D s → List ChannelMsg → Bool)
    (hist : S → List ChannelMsg) :
    MultiRoundTree S Y Z → Protocol (X × ((s : S) → D s)) Y Z
  | output out => Protocol.output out
  | sendTo s bit p₀ p₁ =>
    Protocol.bob bit
      (compile serverBit (Function.update hist s (hist s ++ [.fromUser false])) p₀)
      (compile serverBit (Function.update hist s (hist s ++ [.fromUser true])) p₁)
  | recvFrom s p₀ p₁ =>
    Protocol.alice (fun xd => serverBit s xd.1 (xd.2 s) (hist s))
      (compile serverBit (Function.update hist s (hist s ++ [.fromServer false])) p₀)
      (compile serverBit (Function.update hist s (hist s ++ [.fromServer true])) p₁)

@[simp] theorem depth_compile [DecidableEq S]
    (serverBit : (s : S) → X → D s → List ChannelMsg → Bool) (hist : S → List ChannelMsg)
    (tree : MultiRoundTree S Y Z) : (compile serverBit hist tree).depth = tree.depth := by
  induction tree generalizing hist with
  | output _ => rfl
  | sendTo _ _ p₀ p₁ ih₀ ih₁ =>
    simp only [compile, Protocol.depth, depth, ih₀, ih₁]
  | recvFrom _ p₀ p₁ ih₀ ih₁ =>
    simp only [compile, Protocol.depth, depth, ih₀, ih₁]

/-- Ordered trace of `(server, directional message)` channel events produced on inputs `(x, d)` and
`y`. -/
@[expose] def execTrace [DecidableEq S] (serverBit : (s : S) → X → D s → List ChannelMsg → Bool)
    (hist : S → List ChannelMsg) :
    MultiRoundTree S Y Z → X → ((s : S) → D s) → Y → List (S × ChannelMsg)
  | output _, _, _, _ => []
  | sendTo s bit p₀ p₁, x, d, y =>
    cond (bit y)
      ((s, .fromUser true) ::
        execTrace serverBit (Function.update hist s (hist s ++ [.fromUser true])) p₁ x d y)
      ((s, .fromUser false) ::
        execTrace serverBit (Function.update hist s (hist s ++ [.fromUser false])) p₀ x d y)
  | recvFrom s p₀ p₁, x, d, y =>
    cond (serverBit s x (d s) (hist s))
      ((s, .fromServer true) ::
        execTrace serverBit (Function.update hist s (hist s ++ [.fromServer true])) p₁ x d y)
      ((s, .fromServer false) ::
        execTrace serverBit (Function.update hist s (hist s ++ [.fromServer false])) p₀ x d y)

/-- Follow a sequence of branch bits down a `Communication.Protocol` tree to a leaf. -/
private def leafOfBits {A B : Type} : (p : Protocol A B Z) → List Bool → Fin p.leafCount
  | Protocol.output _, _ => ⟨0, Nat.zero_lt_one⟩
  | Protocol.alice _ p₀ p₁, [] => Fin.castAdd p₁.leafCount (leafOfBits p₀ [])
  | Protocol.alice _ p₀ p₁, b :: bs =>
    cond b (Fin.natAdd p₀.leafCount (leafOfBits p₁ bs))
      (Fin.castAdd p₁.leafCount (leafOfBits p₀ bs))
  | Protocol.bob _ p₀ p₁, [] => Fin.castAdd p₁.leafCount (leafOfBits p₀ [])
  | Protocol.bob _ p₀ p₁, b :: bs =>
    cond b (Fin.natAdd p₀.leafCount (leafOfBits p₁ bs))
      (Fin.castAdd p₁.leafCount (leafOfBits p₀ bs))

private theorem leafOfBits_map_bit_execTrace [DecidableEq S]
    (serverBit : (s : S) → X → D s → List ChannelMsg → Bool) (hist : S → List ChannelMsg)
    (tree : MultiRoundTree S Y Z) (x : X) (d : (s : S) → D s) (y : Y) :
    leafOfBits (compile serverBit hist tree)
        ((execTrace serverBit hist tree x d y).map (ChannelMsg.bit ∘ Prod.snd)) =
      (compile serverBit hist tree).leaf (x, d) y := by
  induction tree generalizing hist with
  | output _ => rfl
  | sendTo s bit p₀ p₁ ih₀ ih₁ =>
    cases h : bit y <;> simp [execTrace, compile, leafOfBits, ChannelMsg.bit, h, ih₀, ih₁]
  | recvFrom s p₀ p₁ ih₀ ih₁ =>
    cases h : serverBit s x (d s) (hist s) <;>
      simp [execTrace, compile, leafOfBits, ChannelMsg.bit, h, ih₀, ih₁]

end MultiRoundTree

/-- A channel-isolated multi-round `k`-server PIR scheme for databases `x : ι → β` (by default
`β = Bool`) with user coins `C` and per-server coins `D : S → Type`. -/
structure MultiInteractiveScheme (ι S C : Type) (D : S → Type) (β : Type := Bool) where
  /-- The user's private coins for index `i`. -/
  userCoins : ι → ProbComp C
  /-- Joint draw of server coins (for independent servers, `OracleComp.pi`). -/
  serverCoins : ProbComp ((s : S) → D s)
  /-- Deterministic bit-response function of server `s`, depending only on the database, server
  `s`'s coins, and the directional history of bits previously exchanged on `s`'s channel. -/
  serverBit : (s : S) → (ι → β) → D s → List ChannelMsg → Bool
  /-- Adaptive interaction tree controller, with leaves labelled by the user's output from `(i, c)`.
  -/
  tree : MultiRoundTree S (ι × C) (ι × C → β)

namespace MultiInteractiveScheme

variable {ι S C β : Type} {D : S → Type} [DecidableEq S]

section Defs

variable (P : MultiInteractiveScheme ι S C D β)

/-- Compile `P` into the two-party `InteractiveScheme` between the combined server coalition and the
user. -/
def toInteractiveScheme : InteractiveScheme ι C ((s : S) → D s) β where
  userCoins := P.userCoins
  serverCoins := P.serverCoins
  protocol := P.tree.compile P.serverBit fun _ => []

@[simp] theorem toInteractiveScheme_userCoins :
    P.toInteractiveScheme.userCoins = P.userCoins := by
  rfl

@[simp] theorem toInteractiveScheme_serverCoins :
    P.toInteractiveScheme.serverCoins = P.serverCoins := by
  rfl

@[simp] theorem toInteractiveScheme_protocol :
    P.toInteractiveScheme.protocol = P.tree.compile P.serverBit fun _ => [] := by
  rfl

theorem depth_toInteractiveScheme :
    P.toInteractiveScheme.protocol.depth = P.tree.depth :=
  MultiRoundTree.depth_compile P.serverBit (fun _ => []) P.tree

/-- The user's output distribution on database `x` and index `i`. -/
def run (x : ι → β) (i : ι) : ProbComp β :=
  P.toInteractiveScheme.run x i

@[simp] theorem run_toInteractiveScheme (x : ι → β) (i : ι) :
    P.toInteractiveScheme.run x i = P.run x i := by
  rfl

/-- Sub-trace of directional channel events `(s, msg)` observed by a server coalition
`T : Finset S`. -/
def coalitionTranscript (T : Finset S) (x : ι → β) (i : ι) : ProbComp (List (S × ChannelMsg)) :=
  (fun cd => (P.tree.execTrace P.serverBit (fun _ => []) x cd.2 (i, cd.1)).filter
    fun sm => sm.1 ∈ T) <$> P.toInteractiveScheme.coins i

/-- Single-server directional channel transcript exchanged with server `s`. -/
def serverTranscript (s : S) (x : ι → β) (i : ι) : ProbComp (List ChannelMsg) :=
  (List.map Prod.snd) <$> P.coalitionTranscript {s} x i

/-- Perfect correctness: on every database and index, `P.run x i` outputs `x i` with probability 1.
-/
def IsCorrect : Prop :=
  P.toInteractiveScheme.IsCorrect

/-- Perfect single-server privacy: each individual server's directional channel transcript has an
index-independent distribution on every database. -/
def IsPrivate : Prop :=
  ∀ s x i i', ProbComp.eval (P.serverTranscript s x i) = ProbComp.eval (P.serverTranscript s x i')

/-- Perfect `t`-privacy: every coalition `T` of at most `t` servers sees an index-independent
directional communication sub-trace on every database. -/
def IsTPrivate (t : ℕ) : Prop :=
  ∀ T : Finset S, T.card ≤ t → ∀ x i i',
    ProbComp.eval (P.coalitionTranscript T x i) = ProbComp.eval (P.coalitionTranscript T x i')

theorem eval_coalitionTranscript (T : Finset S) (x : ι → β) (i : ι) :
    ProbComp.eval (P.coalitionTranscript T x i) =
      (ProbComp.eval (P.toInteractiveScheme.coins i)).map fun cd =>
        (P.tree.execTrace P.serverBit (fun _ => []) x cd.2 (i, cd.1)).filter
          fun sm => decide (sm.1 ∈ T) := by
  rw [coalitionTranscript, ProbComp.eval_map]

theorem eval_serverTranscript (s : S) (x : ι → β) (i : ι) :
    ProbComp.eval (P.serverTranscript s x i) =
      (ProbComp.eval (P.toInteractiveScheme.coins i)).map fun cd =>
        ((P.tree.execTrace P.serverBit (fun _ => []) x cd.2 (i, cd.1)).filter
          fun sm => decide (sm.1 = s)).map Prod.snd := by
  simp only [serverTranscript, coalitionTranscript, ProbComp.eval_map, PMF.map_comp,
    Finset.mem_singleton]
  rfl

theorem isCorrect_iff : P.IsCorrect ↔ ∀ x i, ∀ c ∈ (ProbComp.eval (P.userCoins i)).support,
    ∀ d ∈ (ProbComp.eval P.serverCoins).support,
      (P.tree.compile P.serverBit (fun _ => [])).leafOutput
        ((P.tree.compile P.serverBit (fun _ => [])).leaf (x, d) (i, c)) (i, c) = x i :=
  P.toInteractiveScheme.isCorrect_iff

theorem isPrivate_iff : P.IsPrivate ↔
    ∀ s x i i',
      ProbComp.eval (P.serverTranscript s x i) = ProbComp.eval (P.serverTranscript s x i') :=
  Iff.rfl

theorem isTPrivate_iff (t : ℕ) : P.IsTPrivate t ↔
    ∀ T : Finset S, T.card ≤ t → ∀ x i i',
      ProbComp.eval (P.coalitionTranscript T x i) = ProbComp.eval (P.coalitionTranscript T x i') :=
  Iff.rfl

theorem IsTPrivate.mono {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) (h : P.IsTPrivate t₂) : P.IsTPrivate t₁ :=
  fun T hT => h T (hT.trans hle)

theorem isTPrivate_one_iff : P.IsTPrivate 1 ↔ P.IsPrivate := by
  constructor
  · intro h s x i i'
    have hsing := h {s} (by simp) x i i'
    simp only [serverTranscript, ProbComp.eval_map, hsing]
  · intro h T hT x i i'
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with h0 | h1
    · have hEmpty : T = ∅ := Finset.card_eq_zero.mp h0
      subst hEmpty
      have hnil (idx : ι) : ProbComp.eval (P.coalitionTranscript ∅ x idx) = PMF.pure [] := by
        rw [coalitionTranscript, ProbComp.eval_map]
        have hfn : (fun cd : C × ((s : S) → D s) =>
            (P.tree.execTrace P.serverBit (fun _ => []) x cd.2 (idx, cd.1)).filter
              fun sm => decide (sm.1 ∈ (∅ : Finset S))) = Function.const _ [] := by
          funext cd
          exact List.filter_eq_nil_iff.mpr fun _ _ => by simp
        rw [hfn, PMF.map_const]
      rw [hnil i, hnil i']
    · obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp h1
      have hrec (idx : ι) : ProbComp.eval (P.coalitionTranscript {s} x idx) =
          (ProbComp.eval (P.serverTranscript s x idx)).map (List.map fun msg => (s, msg)) := by
        simp only [serverTranscript, coalitionTranscript, ProbComp.eval_map, PMF.map_comp]
        congr 1
        funext cd
        simp only [Function.comp_apply, List.map_map]
        induction (P.tree.execTrace P.serverBit (fun _ => []) x cd.2 (idx, cd.1)) with
        | nil => rfl
        | cons hd tl ih =>
          rcases hd with ⟨s', msg⟩
          by_cases hs : s' = s
          · subst hs
            rw [List.filter_cons_of_pos (by simp), List.map_cons, Function.comp_apply, ← ih]
          · rw [List.filter_cons_of_neg (by simp [hs])]
            exact ih
      rw [hrec i, hrec i', h s x i i']

end Defs

variable {P : MultiInteractiveScheme ι S C D β}

/-- When all servers collude (`|S| ≤ t`), `t`-privacy gives two-party `InteractiveScheme.IsPrivate`
on `P.toInteractiveScheme`, because the full trace `coalitionTranscript Finset.univ` determines the
reached protocol leaf. -/
theorem isPrivate_toInteractiveScheme_of_card_le [Fintype S] {t : ℕ}
    (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    P.toInteractiveScheme.IsPrivate := by
  rw [InteractiveScheme.isPrivate_iff]
  intro x i i'
  have huniv : (Finset.univ : Finset S).card ≤ t := by simpa using hcard
  have hleaf (idx : ι) : ProbComp.eval (P.toInteractiveScheme.transcript x idx) =
      (ProbComp.eval (P.coalitionTranscript Finset.univ x idx)).map
        (fun tr => MultiRoundTree.leafOfBits P.toInteractiveScheme.protocol
          (tr.map (ChannelMsg.bit ∘ Prod.snd))) := by
    rw [InteractiveScheme.eval_transcript, coalitionTranscript, ProbComp.eval_map, PMF.map_comp]
    congr 1
    funext cd
    simp only [Function.comp_apply, toInteractiveScheme, Finset.mem_univ, decide_true,
      List.filter_true]
    exact (MultiRoundTree.leafOfBits_map_bit_execTrace P.serverBit (fun _ => []) P.tree
      x cd.2 (idx, cd.1)).symm
  rw [hleaf i, hleaf i', hprivate Finset.univ huniv x i i']

/-- **Full-coalition multi-round lower bound (`|S| ≤ t`)**
[CGKS, Sections 2.2 and 5.1][ChorGoldreichKushilevitzSudan1998]: if all `k` servers may collude,
even arbitrary adaptive multi-round interaction requires at least `|ι|` bits of total communication.
-/
theorem card_le_depth_of_card_le [Fintype S] [Fintype ι]
    {P : MultiInteractiveScheme ι S C D} {t : ℕ} (hcorrect : P.IsCorrect)
    (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    Fintype.card ι ≤ P.tree.depth := by
  rw [← P.depth_toInteractiveScheme]
  exact InteractiveScheme.card_le_depth hcorrect
    (isPrivate_toInteractiveScheme_of_card_le hprivate hcard)

/-- **Full-coalition multi-round block lower bound (`|S| ≤ t`)**
[CGKS, Sections 2.2, 4 and 5.1][ChorGoldreichKushilevitzSudan1998]: on `(κ → Bool)` block databases,
full-coalition `t`-privacy (`|S| ≤ t`) forces at least `|ι| · |κ|` bits across all rounds. -/
theorem card_mul_le_depth_of_card_le {κ : Type} [Fintype S] [Fintype ι] [Fintype κ]
    {P : MultiInteractiveScheme ι S C D (κ → Bool)} {t : ℕ} (hcorrect : P.IsCorrect)
    (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    Fintype.card ι * Fintype.card κ ≤ P.tree.depth := by
  rw [← P.depth_toInteractiveScheme]
  exact InteractiveScheme.card_mul_le_depth hcorrect
    (isPrivate_toInteractiveScheme_of_card_le hprivate hcard)

end MultiInteractiveScheme

end Cslib.Crypto.Protocols.PIR
