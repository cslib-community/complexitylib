/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Protocol
public import Complexity.Foundations.Data.BitString.Basic

/-!
# Exchanging the players, relabelling outputs, and trivial upper bounds

Exchanging the roles of Alice and Bob in a protocol (`Protocol.swapPlayers`) computes the
function with its arguments exchanged, and relabelling the leaves by `g` (`Protocol.map`) computes
`g` of the function; neither changes the depth. So the communication complexity of a function is
invariant under exchanging the arguments (`Protocol.ecomplexityFun_swap`), does not increase under
relabelling the outputs or transforming the inputs (`Protocol.ecomplexityFun_map_le`,
`Protocol.ecomplexityFun_comap_le`), and is unchanged by an injective (left-invertible) relabelling
such as negation (`Protocol.ecomplexityFun_map_of_leftInverse`, `Protocol.ecomplexityFun_not`). All
of these follow from `Protocol.ecomplexityFun_le_of_forall`: a function is no harder than another if
every protocol for the latter yields one of no greater depth for the former.

Protocols can also be run one after another: `Protocol.bind` replaces each leaf of a protocol by a
protocol chosen by its output, sending at most the bits of both (`Protocol.depth_bind_le`), and
`Protocol.runAll` runs a tuple of protocols in turn and combines their outputs
(`Protocol.run_runAll`, `Protocol.depth_runAll_le`). Relabelling is a special case of sequencing
(`Protocol.map_eq_bind`).

Together with the trivial protocol `Protocol.ecomplexityFun_le_succ`, in which Alice sends her `n`
bits and Bob announces the value, this gives the other trivial upper bounds
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]: `n + 1` bits when Bob holds `n` bits
(`Protocol.ecomplexityFun_le_succ_right`), `min n m + 1` bits for inputs of `n` and `m` bits
(`Protocol.ecomplexityFun_le_min_succ`), and `⌈log₂ |X|⌉ + 1` bits when Alice's input ranges over
a finite type `X`, which she encodes in `⌈log₂ |X|⌉` bits
(`Protocol.ecomplexityFun_le_clog_card_succ`, and `Protocol.ecomplexityFun_le_clog_card_succ_right`
for Bob). More generally, if Bob's answer depends on Alice's input only through a value in a finite
set `s`, she sends that value in `⌈log₂ |s|⌉` bits
(`Protocol.ecomplexityFun_le_clog_card_finset_succ`). A protocol computing the indicator of a
predicate decides it (`Protocol.ecomplexity_decides_le`).

## Main definitions

* `Cslib.Communication.Protocol.swapPlayers`: exchanging the roles of Alice and Bob.
* `Cslib.Communication.Protocol.map`: relabelling the outputs of a protocol.
* `Cslib.Communication.Protocol.bind`, `Cslib.Communication.Protocol.runAll`: running protocols
  one after another.

## Main results

* `Cslib.Communication.Protocol.ecomplexityFun_le_of_forall`: comparing communication complexities
  through a transformation of protocols.
* `Cslib.Communication.Protocol.ecomplexityFun_swap`: exchanging the arguments.
* `Cslib.Communication.Protocol.ecomplexityFun_map_le`,
  `Cslib.Communication.Protocol.ecomplexityFun_map_of_leftInverse`,
  `Cslib.Communication.Protocol.ecomplexityFun_not`: relabelling the outputs.
* `Cslib.Communication.Protocol.ecomplexityFun_comap_le`: transforming the inputs.
* `Cslib.Communication.Protocol.ecomplexityFun_le_succ_right`,
  `Cslib.Communication.Protocol.ecomplexityFun_le_min_succ`,
  `Cslib.Communication.Protocol.ecomplexityFun_le_clog_card_succ`,
  `Cslib.Communication.Protocol.ecomplexityFun_le_clog_card_succ_right`,
  `Cslib.Communication.Protocol.ecomplexityFun_le_clog_card_finset_succ`: trivial upper bounds.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

namespace Protocol

variable {X Y Z Z' X' Y' : Type*}

/-! ### Exchanging the players -/

/-- The protocol `p` with the roles of Alice and Bob exchanged: Bob sends the bits Alice sent in
`p`, and conversely. -/
def swapPlayers : Protocol X Y Z → Protocol Y X Z
  | output z => output z
  | alice send p₀ p₁ => bob send p₀.swapPlayers p₁.swapPlayers
  | bob send p₀ p₁ => alice send p₀.swapPlayers p₁.swapPlayers

/-- The protocol with the players exchanged computes the function with its arguments exchanged. -/
@[simp] theorem run_swapPlayers (p : Protocol X Y Z) (y : Y) (x : X) :
    p.swapPlayers.run y x = p.run x y := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [swapPlayers, ih₀, ih₁]

/-- Exchanging the players does not change the depth. -/
@[simp] theorem depth_swapPlayers (p : Protocol X Y Z) : p.swapPlayers.depth = p.depth := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [swapPlayers, ih₀, ih₁]

/-- Exchanging the players does not change the number of leaves. -/
@[simp] theorem leafCount_swapPlayers (p : Protocol X Y Z) :
    p.swapPlayers.leafCount = p.leafCount := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [swapPlayers, ih₀, ih₁]

/-- Exchanging the players twice gives back the protocol. -/
@[simp] theorem swapPlayers_swapPlayers (p : Protocol X Y Z) : p.swapPlayers.swapPlayers = p := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [swapPlayers, ih₀, ih₁]

/-! ### Relabelling the outputs -/

/-- The protocol `p` with every leaf label `z` replaced by `g z`. -/
def map (g : Z → Z') : Protocol X Y Z → Protocol X Y Z'
  | output z => output (g z)
  | alice send p₀ p₁ => alice send (p₀.map g) (p₁.map g)
  | bob send p₀ p₁ => bob send (p₀.map g) (p₁.map g)

/-- The relabelled protocol outputs the relabelled value. -/
@[simp] theorem run_map (g : Z → Z') (p : Protocol X Y Z) (x : X) (y : Y) :
    (p.map g).run x y = g (p.run x y) := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ =>
    simp only [map, run_alice, ih₀, ih₁]
    cases send x <;> rfl
  | bob send p₀ p₁ ih₀ ih₁ =>
    simp only [map, run_bob, ih₀, ih₁]
    cases send y <;> rfl

/-- Relabelling the outputs does not change the depth. -/
@[simp] theorem depth_map (g : Z → Z') (p : Protocol X Y Z) : (p.map g).depth = p.depth := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [map, ih₀, ih₁]

/-- Relabelling the outputs does not change the number of leaves. -/
@[simp] theorem leafCount_map (g : Z → Z') (p : Protocol X Y Z) :
    (p.map g).leafCount = p.leafCount := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp [map, ih₀, ih₁]

/-! ### Sequencing protocols -/

/-- Run `p`, then the protocol `q z` for the output `z` of `p`: each leaf of `p` labelled `z` is
replaced by `q z`. -/
def bind : Protocol X Y Z → (Z → Protocol X Y Z') → Protocol X Y Z'
  | output z, q => q z
  | alice send p₀ p₁, q => alice send (p₀.bind q) (p₁.bind q)
  | bob send p₀ p₁, q => bob send (p₀.bind q) (p₁.bind q)

/-- Sequencing outputs the value of the second protocol, chosen by the output of the first. -/
@[simp] theorem run_bind (p : Protocol X Y Z) (q : Z → Protocol X Y Z') (x : X) (y : Y) :
    (p.bind q).run x y = (q (p.run x y)).run x y := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ => cases h : send x <;> simp [bind, h, ih₀, ih₁]
  | bob send p₀ p₁ ih₀ ih₁ => cases h : send y <;> simp [bind, h, ih₀, ih₁]

/-- Sequencing sends at most the bits of the first protocol and then those of the second. -/
theorem depth_bind_le {p : Protocol X Y Z} {q : Z → Protocol X Y Z'} {d : ℕ}
    (hq : ∀ z, (q z).depth ≤ d) : (p.bind q).depth ≤ p.depth + d := by
  induction p with
  | output z => simpa [bind] using hq z
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ =>
    simp only [bind, depth_alice, depth_bob]
    omega

/-- Relabelling the outputs is sequencing with protocols that only output. -/
theorem map_eq_bind (g : Z → Z') (p : Protocol X Y Z) : p.map g = p.bind fun z => output (g z) := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ => simp only [map, bind, ih₀, ih₁]

/-- Run the protocols `ps 0`, …, `ps (k - 1)` one after another and output `g` of their
outputs. -/
def runAll : {k : ℕ} → (Fin k → Protocol X Y Z) → ((Fin k → Z) → Z') → Protocol X Y Z'
  | 0, _, g => output (g Fin.elim0)
  | _ + 1, ps, g => (ps 0).bind fun z => runAll (Fin.tail ps) fun v => g (Fin.cons z v)

/-- Running the protocols one after another outputs `g` of their outputs. -/
@[simp] theorem run_runAll {k : ℕ} (ps : Fin k → Protocol X Y Z) (g : (Fin k → Z) → Z') (x : X)
    (y : Y) : (runAll ps g).run x y = g fun i => (ps i).run x y := by
  induction k generalizing Z' with
  | zero =>
    simp only [runAll, run_output]
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    rw [runAll, run_bind, ih]
    congr 1
    funext i
    induction i using Fin.cases <;> rfl

/-- Running `k` protocols of depth at most `d` one after another sends at most `k d` bits. -/
theorem depth_runAll_le {k : ℕ} {ps : Fin k → Protocol X Y Z} {g : (Fin k → Z) → Z'} {d : ℕ}
    (hps : ∀ i, (ps i).depth ≤ d) : (runAll ps g).depth ≤ k * d := by
  induction k generalizing Z' with
  | zero => simp [runAll]
  | succ k ih =>
    rw [runAll]
    refine (depth_bind_le fun z => ih (fun i => hps i.succ)).trans ?_
    have := hps 0
    rw [Nat.succ_mul]
    omega

/-! ### Communication complexity under these operations -/

/-- If every protocol computing `f` yields one of no greater depth computing `f'`, then `f'` is
no harder than `f`. -/
theorem ecomplexityFun_le_of_forall {f : X → Y → Z} {f' : X' → Y' → Z'}
    (h : ∀ p : Protocol X Y Z, p.run = f →
      ∃ q : Protocol X' Y' Z', q.run = f' ∧ q.depth ≤ p.depth) :
    ecomplexityFun f' ≤ ecomplexityFun f :=
  le_ecomplexityFun_iff.mpr fun p hp =>
    let ⟨_, hq, hd⟩ := h p hp
    (ecomplexityFun_le_depth hq).trans (by exact_mod_cast hd)

/-- Transforming the inputs does not make a function harder to compute: run a protocol for `f`
on the transformed inputs (`Protocol.comap`). -/
theorem ecomplexityFun_comap_le (f : X → Y → Z) (a : X' → X) (b : Y' → Y) :
    ecomplexityFun (fun x y => f (a x) (b y)) ≤ ecomplexityFun f :=
  ecomplexityFun_le_of_forall fun p hp => ⟨p.comap a b, by funext x y; simp [hp], by simp⟩

/-- Relabelling the outputs does not make a function harder to compute. -/
theorem ecomplexityFun_map_le (g : Z → Z') (f : X → Y → Z) :
    ecomplexityFun (fun x y => g (f x y)) ≤ ecomplexityFun f :=
  ecomplexityFun_le_of_forall fun p hp => ⟨p.map g, by funext x y; simp [hp], by simp⟩

/-- An injective relabelling `g` of the outputs, given with a left inverse `g'`, does not change
the communication complexity. -/
theorem ecomplexityFun_map_of_leftInverse {g : Z → Z'} {g' : Z' → Z}
    (hg : Function.LeftInverse g' g) (f : X → Y → Z) :
    ecomplexityFun (fun x y => g (f x y)) = ecomplexityFun f := by
  refine le_antisymm (ecomplexityFun_map_le g f) ?_
  simpa only [hg _] using ecomplexityFun_map_le g' fun x y => g (f x y)

/-- Negating the output does not change the communication complexity. -/
@[simp] theorem ecomplexityFun_not (f : X → Y → Bool) :
    ecomplexityFun (fun x y => !f x y) = ecomplexityFun f :=
  ecomplexityFun_map_of_leftInverse Bool.not_not f

private theorem ecomplexityFun_swap_le (f : X → Y → Z) :
    ecomplexityFun (fun y x => f x y) ≤ ecomplexityFun f :=
  ecomplexityFun_le_of_forall fun p hp => ⟨p.swapPlayers, by funext y x; simp [hp], by simp⟩

/-- Exchanging the arguments, and so the roles of Alice and Bob, does not change the
communication complexity. -/
theorem ecomplexityFun_swap (f : X → Y → Z) :
    ecomplexityFun (fun y x => f x y) = ecomplexityFun f :=
  le_antisymm (ecomplexityFun_swap_le f) (ecomplexityFun_swap_le fun y x => f x y)

/-! ### Trivial upper bounds -/

/-- **The trivial protocol for Bob.** Every Boolean function of Alice's input and Bob's `n` bits
has a protocol with `n + 1` bits: Bob sends his input and Alice announces the value. -/
theorem ecomplexityFun_le_succ_right {n : ℕ} (f : X → BitString n → Bool) :
    ecomplexityFun f ≤ n + 1 :=
  (ecomplexityFun_swap f).symm.trans_le (ecomplexityFun_le_succ _)

/-- Every Boolean function of Alice's `n` bits and Bob's `m` bits has a protocol with
`min n m + 1` bits: the player with the shorter input sends it. -/
theorem ecomplexityFun_le_min_succ {n m : ℕ} (f : BitString n → BitString m → Bool) :
    ecomplexityFun f ≤ min n m + 1 := by
  rcases le_total n m with h | h
  · simpa [min_eq_left h] using ecomplexityFun_le_succ f
  · simpa [min_eq_right h] using ecomplexityFun_le_succ_right f

/-- **The trivial protocol for a finite input type.** If Alice's input ranges over a finite type
`X`, every Boolean function has a protocol with `⌈log₂ |X|⌉ + 1` bits: Alice sends an encoding of
her input in `⌈log₂ |X|⌉` bits and Bob announces the value. -/
theorem ecomplexityFun_le_clog_card_succ [Fintype X] (f : X → Y → Bool) :
    ecomplexityFun f ≤ Nat.clog 2 (Fintype.card X) + 1 := by
  obtain ⟨e⟩ : Nonempty (X ↪ BitString (Nat.clog 2 (Fintype.card X))) :=
    Function.Embedding.nonempty_of_card_le (BitString.card ▸ Nat.le_pow_clog one_lt_two _)
  have hf : f = fun x y => Function.extend e f (fun _ _ => false) (e x) (id y) := by
    funext x y
    rw [e.injective.extend_apply, id]
  rw [hf]
  exact (ecomplexityFun_comap_le _ e id).trans (ecomplexityFun_le_succ _)

/-- If Bob's input ranges over a finite type `Y`, every Boolean function has a protocol with
`⌈log₂ |Y|⌉ + 1` bits. -/
theorem ecomplexityFun_le_clog_card_succ_right [Fintype Y] (f : X → Y → Bool) :
    ecomplexityFun f ≤ Nat.clog 2 (Fintype.card Y) + 1 :=
  (ecomplexityFun_swap f).symm.trans_le (ecomplexityFun_le_clog_card_succ _)

/-- **Sending a value from a finite set.** If Bob's answer depends on Alice's input `x` only through
a value `m x` in a finite set `s`, there is a protocol with `⌈log₂ |s|⌉ + 1` bits: Alice sends an
encoding of `m x` and Bob announces the value. -/
theorem ecomplexityFun_le_clog_card_finset_succ {α : Type*} (s : Finset α) (m : X → α)
    (hm : ∀ x, m x ∈ s) (g : α → Y → Bool) :
    ecomplexityFun (fun x y => g (m x) y) ≤ Nat.clog 2 s.card + 1 := by
  have h := ecomplexityFun_comap_le (fun (w : s) y => g w y) (fun x => ⟨m x, hm x⟩) id
  refine h.trans ((ecomplexityFun_le_clog_card_succ _).trans ?_)
  simp

/-- A protocol computing the indicator of a predicate `P` decides `P`: its Boolean output is
`true` exactly when `P` holds. -/
theorem ecomplexity_decides_le {P : X → Y → Prop} [∀ x y, Decidable (P x y)] {A : Set X}
    {B : Set Y} :
    ecomplexity (fun x y (z : Bool) => z = true ↔ P x y) A B ≤
      ecomplexityFun (fun x y => decide (P x y)) := by
  refine (ecomplexity_mono (Set.subset_univ _) (Set.subset_univ _)).trans ?_
  refine le_iInf fun p => iInf_le_of_le ⟨p.1, fun x _ y _ => ?_⟩ le_rfl
  rw [← p.2 x trivial y trivial]
  exact decide_eq_true_iff

end Protocol

end Cslib.Communication
