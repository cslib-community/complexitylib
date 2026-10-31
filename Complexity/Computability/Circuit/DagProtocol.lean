/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.DagProtocol
public import Complexity.Computability.Communication.KarchmerWigderson
public import Complexity.Computability.Circuit.Monotone.Synthesis
public import Cslib.Computability.Circuit.Boolean.Synthesis
import Complexity.Computability.Communication.Rectangle

/-!
# Circuits from dag-like protocols

A dag-like protocol for the Karchmer–Wigderson game on `U × V` (`Cslib.Communication.DagProtocol`
solving `Cslib.Communication.DiffersAt`) with `k` inner nodes and communication complexity `t`
gives a De Morgan circuit with at most `(k · 2 ^ t + 1) · 2 ^ (t + 1)` gates that is true on `U`
and false on `V` (`Cslib.Communication.DagProtocol.Solves.exists_circuit`). A monotone protocol,
one solving `Cslib.Communication.ExceedsAt`, gives a monotone circuit with as many gates
(`Cslib.Communication.DagProtocol.Solves.exists_monotone_circuit`). This is
[Krajíček, Theorem 2.3][Krajicek1997], with the explicit constant `2 ^ (2 t + 1)` for the factor
`2 ^ O(t)`. Krajíček credits the theorem to Razborov and proves it by citing Theorem 3.1 of
[Razborov1995b]; that locator is Krajíček's and was not checked against Razborov's paper. The proof
here is direct.

The tree protocol at an inner node `j` partitions the inputs into at most `2 ^ t` rectangles
(`Cslib.Communication.Protocol.leafAlice`, `Cslib.Communication.Protocol.leafBob`). For each leaf
`ℓ` of it that names an inner node `i`, the circuit has a gate that is true on the inputs of `U`
and false on those of `V` in the rectangle of `ℓ`. That gate is the Karchmer–Wigderson formula of
the tree protocol at `i` restricted to this rectangle, as in
`Cslib.Communication.Protocol.kwFormula`: an OR at each of Alice's nodes and an AND at each of
Bob's. At a leaf of the tree protocol at `i` the formula takes the gate of that leaf if it names an
inner node, a literal if it names an answer, and a constant if it answers `none`: on the inputs of
the rectangle the node `i` is consistent, so the part of a `none` leaf inside it has an empty
side. Each such formula has at most `2 ^ (t + 1)` gates, and there are at most `k · 2 ^ t` of them,
built from the last inner node to the first; one more formula, at the source, separates `U` from
`V`.

## Main results

* `Cslib.Communication.DagProtocol.Solves.exists_circuit`: a dag-like protocol for the
  Karchmer–Wigderson game gives a separating De Morgan circuit.
* `Cslib.Communication.DagProtocol.Solves.exists_monotone_circuit`: a dag-like protocol for the
  monotone Karchmer–Wigderson game gives a separating monotone circuit.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
* [A. A. Razborov, *Unprovability of lower bounds on the circuit size in certain fragments of
  bounded arithmetic*][Razborov1995b]
-/

public section

namespace Cslib.Communication.DagProtocol

open Cslib.Circuits

variable {n k : ℕ}

/-! ### Separating rectangles -/

/-- `f` is true on `A` and false on `B`. -/
private def Sep (f : BitString n → Bool) (A B : Set (BitString n)) : Prop :=
  (∀ x ∈ A, f x = true) ∧ ∀ y ∈ B, f y = false

private theorem Sep.mono {f : BitString n → Bool} {A B A' B' : Set (BitString n)}
    (h : Sep f A B) (hA : A' ⊆ A) (hB : B' ⊆ B) : Sep f A' B' :=
  ⟨fun x hx => h.1 x (hA hx), fun y hy => h.2 y (hB hy)⟩

section Core

variable {σ : Signature} {I : Interpretation σ Bool}

/-- A rectangle containing no pair of inputs is separated by a constant. -/
private theorem exists_sep_const {S : Set (BitString n → Bool)}
    (hconst : ∀ b, Synthesis I S {fun _ => b} 1) {A B : Set (BitString n)}
    (h : ∀ x ∈ A, ∀ y ∈ B, False) : ∃ f, Sep f A B ∧ Synthesis I S {f} 1 := by
  by_cases hA : A.Nonempty
  · obtain ⟨x, hx⟩ := hA
    exact ⟨fun _ => true, ⟨fun _ _ => rfl, fun y hy => (h x hx y hy).elim⟩, hconst true⟩
  · exact ⟨fun _ => false, ⟨fun x hx => (hA ⟨x, hx⟩).elim, fun _ _ => rfl⟩, hconst false⟩

variable {S : Set (BitString n → Bool)}

/-- **Separating through a tree protocol.** If every leaf rectangle of `p`, cut down to `A × B`,
is separated by a function synthesized from `S` with one gate, then `A` is separated from `B` by a
function synthesized with `2 · leaves - 1` gates: an OR at each of Alice's nodes and an AND at
each of Bob's. -/
private theorem exists_sep_of_leaves
    (hor : ∀ {f g : BitString n → Bool} {a b : ℕ}, Synthesis I S {f} a → Synthesis I S {g} b →
      Synthesis I S {fun x => f x || g x} (a + b + 1))
    (hand : ∀ {f g : BitString n → Bool} {a b : ℕ}, Synthesis I S {f} a → Synthesis I S {g} b →
      Synthesis I S {fun x => f x && g x} (a + b + 1))
    {Z : Type*} (p : Protocol (BitString n) (BitString n) Z) {A B : Set (BitString n)}
    (hleaf : ∀ ℓ, ∃ f, Sep f (A ∩ p.leafAlice ℓ) (B ∩ p.leafBob ℓ) ∧ Synthesis I S {f} 1) :
    ∃ f, Sep f A B ∧ Synthesis I S {f} (2 * p.leafCount - 1) := by
  induction p generalizing A B with
  | output z =>
    obtain ⟨f, hf, hs⟩ := hleaf ⟨0, Nat.zero_lt_one⟩
    exact ⟨f, hf.mono (fun x hx => ⟨hx, Set.mem_univ x⟩) fun y hy => ⟨hy, Set.mem_univ y⟩, hs⟩
  | alice send p₀ p₁ ih₀ ih₁ =>
    obtain ⟨f₀, hf₀, hs₀⟩ := ih₀ (A := {x ∈ A | send x = false}) (B := B) fun ℓ => by
      obtain ⟨f, hf, hs⟩ := hleaf (Fin.castAdd _ ℓ)
      refine ⟨f, hf.mono ?_ ?_, hs⟩
      · rintro x ⟨⟨hx, hsx⟩, hℓ⟩
        simp [hx, hsx, hℓ]
      · simp
    obtain ⟨f₁, hf₁, hs₁⟩ := ih₁ (A := {x ∈ A | send x = true}) (B := B) fun ℓ => by
      obtain ⟨f, hf, hs⟩ := hleaf (Fin.natAdd _ ℓ)
      refine ⟨f, hf.mono ?_ ?_, hs⟩
      · rintro x ⟨⟨hx, hsx⟩, hℓ⟩
        simp [hx, hsx, hℓ]
      · simp
    refine ⟨fun x => f₀ x || f₁ x, ⟨fun x hx => ?_, fun y hy => ?_⟩,
      (hor hs₀ hs₁).mono Set.Subset.rfl Set.Subset.rfl ?_⟩
    · cases h : send x
      · simp [hf₀.1 x ⟨hx, h⟩]
      · simp [hf₁.1 x ⟨hx, h⟩]
    · simp [hf₀.2 y hy, hf₁.2 y hy]
    · have := p₀.leafCount_pos
      have := p₁.leafCount_pos
      simp only [Protocol.leafCount_alice]
      omega
  | bob send p₀ p₁ ih₀ ih₁ =>
    obtain ⟨f₀, hf₀, hs₀⟩ := ih₀ (A := A) (B := {y ∈ B | send y = false}) fun ℓ => by
      obtain ⟨f, hf, hs⟩ := hleaf (Fin.castAdd _ ℓ)
      refine ⟨f, hf.mono ?_ ?_, hs⟩
      · simp
      · rintro y ⟨⟨hy, hsy⟩, hℓ⟩
        simp [hy, hsy, hℓ]
    obtain ⟨f₁, hf₁, hs₁⟩ := ih₁ (A := A) (B := {y ∈ B | send y = true}) fun ℓ => by
      obtain ⟨f, hf, hs⟩ := hleaf (Fin.natAdd _ ℓ)
      refine ⟨f, hf.mono ?_ ?_, hs⟩
      · simp
      · rintro y ⟨⟨hy, hsy⟩, hℓ⟩
        simp [hy, hsy, hℓ]
    refine ⟨fun x => f₀ x && f₁ x, ⟨fun x hx => ?_, fun y hy => ?_⟩,
      (hand hs₀ hs₁).mono Set.Subset.rfl Set.Subset.rfl ?_⟩
    · simp [hf₀.1 x hx, hf₁.1 x hx]
    · cases h : send y
      · simp [hf₀.2 y ⟨hy, h⟩]
      · simp [hf₁.2 y ⟨hy, h⟩]
    · have := p₀.leafCount_pos
      have := p₁.leafCount_pos
      simp only [Protocol.leafCount_bob]
      omega

end Core

/-! ### Building the circuit -/

section Build

variable {σ : Signature} {I : Interpretation σ Bool}
  (P : DagProtocol (BitString n) (BitString n) (Fin n) k)
  (R : BitString n → BitString n → Fin n → Prop) (U V : Set (BitString n))

/-- Every leaf of the tree protocol at inner node `j` that names an inner node has a function in
`T` that is true on the inputs of `U` and false on those of `V` in its rectangle. -/
private def Gated (T : Set (BitString n → Bool)) (j : Fin k) : Prop :=
  ∀ ℓ (i : Fin j), (P.step j).leafOutput ℓ = some (.inl i) →
    ∃ f ∈ T, Sep f (U ∩ (P.step j).leafAlice ℓ) (V ∩ (P.step j).leafBob ℓ)

variable {P R U V}

/-- The gate rules used to build the circuit: constants, a one-gate separator of every rectangle
on which an answer is valid, disjunction and conjunction. -/
private structure Rules (I : Interpretation σ Bool) (R : BitString n → BitString n → Fin n → Prop) :
    Prop where
  const : ∀ b, Synthesis I (inputs n) {fun _ => b} 1
  rect : ∀ (A B : Set (BitString n)) (o : Fin n), (∀ x ∈ A, ∀ y ∈ B, R x y o) →
    ∃ f, Sep f A B ∧ Synthesis I (inputs n) {f} 1
  or : ∀ {S : Set (BitString n → Bool)} {f g : BitString n → Bool} {a b : ℕ},
    Synthesis I S {f} a → Synthesis I S {g} b → Synthesis I S {fun x => f x || g x} (a + b + 1)
  and : ∀ {S : Set (BitString n → Bool)} {f g : BitString n → Bool} {a b : ℕ},
    Synthesis I S {f} a → Synthesis I S {g} b → Synthesis I S {fun x => f x && g x} (a + b + 1)

/-- **The formula at an inner node.** If the leaves of the tree protocol at `j` naming inner nodes
have gates in `T`, then any rectangle `A × B` inside `U × V` on which `j` is consistent is
separated by a function synthesized from the inputs and `T` with `2 · leaves - 1` gates. -/
private theorem exists_sep_node (hP : P.Solves R U V) (rules : Rules I R)
    {T : Set (BitString n → Bool)} {j : Fin k} (hT : Gated P U V T j) {A B : Set (BitString n)}
    (hA : A ⊆ U) (hB : B ⊆ V) (hcons : ∀ x ∈ A, ∀ y ∈ B, (P.step j).run x y ≠ none) :
    ∃ f, Sep f A B ∧ Synthesis I (inputs n ∪ T) {f} (2 * (P.step j).leafCount - 1) := by
  refine exists_sep_of_leaves rules.or rules.and (P.step j) fun ℓ => ?_
  have hrun : ∀ x ∈ A ∩ (P.step j).leafAlice ℓ, ∀ y ∈ B ∩ (P.step j).leafBob ℓ,
      (P.step j).run x y = (P.step j).leafOutput ℓ := fun x hx y hy =>
    Protocol.run_eq_leafOutput hx.2 hy.2
  rcases hout : (P.step j).leafOutput ℓ with _ | i | o
  · exact exists_sep_const (A := A ∩ (P.step j).leafAlice ℓ) (B := B ∩ (P.step j).leafBob ℓ)
      (fun b => (rules.const b).mono Set.subset_union_left Set.Subset.rfl le_rfl)
      fun x hx y hy => hcons x hx.1 y hy.1 ((hrun x hx y hy).trans hout)
  · obtain ⟨f, hfT, hf⟩ := hT ℓ i hout
    exact ⟨f, hf.mono (Set.inter_subset_inter_left _ hA) (Set.inter_subset_inter_left _ hB),
      (Synthesis.of_mem (Set.mem_union_right _ hfT)).mono Set.Subset.rfl Set.Subset.rfl
        (Nat.zero_le 1)⟩
  · obtain ⟨f, hf, hs⟩ := rules.rect (A ∩ (P.step j).leafAlice ℓ) (B ∩ (P.step j).leafBob ℓ) o
      fun x hx y hy => by
        have := hP.2 j x (hA hx.1) y (hB hy.1) (.inr o) ((hrun x hx y hy).trans hout)
        simpa using this
    exact ⟨f, hf, hs.mono Set.subset_union_left Set.Subset.rfl le_rfl⟩

/-- A tree protocol at an inner node, of depth at most that of the dag-like protocol, gives a
formula with at most `2 ^ (P.depth + 1)` gates. -/
private theorem two_mul_leafCount_sub_one_le (j : Fin k) :
    2 * (P.step j).leafCount - 1 ≤ 2 ^ (P.depth + 1) := by
  have h₁ := (P.step j).leafCount_le_two_pow_depth
  have h₂ := Nat.pow_le_pow_right (by decide : 0 < 2) (P.depth_step_le j)
  rw [pow_succ]
  omega

/-- **The gates of the circuit**, for the leaves of the tree protocols at the inner nodes below
`m`, with at most `2 ^ P.depth` leaves per node and `2 ^ (P.depth + 1)` gates per leaf. -/
private theorem exists_gates (hP : P.Solves R U V) (rules : Rules I R) :
    ∀ m ≤ k, ∃ T, Synthesis I (inputs n) T (m * (2 ^ P.depth * 2 ^ (P.depth + 1))) ∧
      ∀ j : Fin k, j.val < m → Gated P U V T j := by
  intro m
  induction m with
  | zero =>
    exact fun _ => ⟨∅, (Synthesis.of_subset (I := I) (Set.empty_subset _)).mono Set.Subset.rfl
      Set.Subset.rfl (Nat.zero_le _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨T, hT, hgated⟩ := ih (by omega)
    obtain ⟨j, hj⟩ : ∃ j : Fin k, j.val = m := ⟨⟨m, hm⟩, rfl⟩
    have hleaf : ∀ ℓ : Fin (P.step j).leafCount, ∃ f,
        (∀ i : Fin j, (P.step j).leafOutput ℓ = some (.inl i) →
          Sep f (U ∩ (P.step j).leafAlice ℓ) (V ∩ (P.step j).leafBob ℓ)) ∧
        Synthesis I (inputs n ∪ T) {f} (2 ^ (P.depth + 1)) := by
      intro ℓ
      have hconst : Synthesis I (inputs n ∪ T) {fun _ => false} (2 ^ (P.depth + 1)) :=
        (rules.const false).mono Set.subset_union_left Set.Subset.rfl Nat.one_le_two_pow
      rcases hout : (P.step j).leafOutput ℓ with _ | i | o
      · exact ⟨fun _ => false, by simp, hconst⟩
      · obtain ⟨f, hf, hs⟩ := exists_sep_node hP rules (j := Fin.castLE j.isLt.le i)
          (hgated _ (by simpa [hj] using i.isLt)) Set.inter_subset_left Set.inter_subset_left
          fun x hx y hy => by
            have := hP.2 j x hx.1 y hy.1 (.inl i)
              ((Protocol.run_eq_leafOutput hx.2 hy.2).trans hout)
            simpa using this
        refine ⟨f, fun i' hi' => hf, hs.mono Set.Subset.rfl Set.Subset.rfl ?_⟩
        exact two_mul_leafCount_sub_one_le _
      · exact ⟨fun _ => false, by simp, hconst⟩
    choose g hg using hleaf
    refine ⟨T ∪ Set.range g, ?_, fun j' hj' => ?_⟩
    · refine (hT.comp (Synthesis.family g (fun _ => 2 ^ (P.depth + 1)) fun ℓ => (hg ℓ).2)).mono
        Set.Subset.rfl Set.Subset.rfl ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have h₁ := (P.step j).leafCount_le_two_pow_depth
      have h₂ := Nat.pow_le_pow_right (by decide : 0 < 2) (P.depth_step_le j)
      have h₃ := Nat.mul_le_mul_right (2 ^ (P.depth + 1)) (h₁.trans h₂)
      rw [Nat.succ_mul]
      omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hlt | heq
      · intro ℓ i h
        obtain ⟨f, hf, hsep⟩ := hgated j' hlt ℓ i h
        exact ⟨f, Or.inl hf, hsep⟩
      · obtain rfl : j' = j := Fin.ext (heq.trans hj.symm)
        intro ℓ i h
        exact ⟨g ℓ, Or.inr ⟨ℓ, rfl⟩, (hg ℓ).1 i h⟩

/-- **The separator.** A dag-like protocol solving `R` on `U × V` gives a function that is true on
`U` and false on `V`, synthesized with at most `(k · 2 ^ t + 1) · 2 ^ (t + 1)` gates, where `t` is
the communication complexity. -/
private theorem exists_sep (hP : P.Solves R U V) (rules : Rules I R) :
    ∃ f, Sep f U V ∧
      Synthesis I (inputs n) {f} ((k * 2 ^ P.depth + 1) * 2 ^ (P.depth + 1)) := by
  obtain ⟨T, hT, hgated⟩ := exists_gates hP rules k le_rfl
  have hroot := hP.1
  rcases hr : P.root with j | o
  · obtain ⟨f, hf, hs⟩ := exists_sep_node hP rules (hgated j j.isLt) Set.Subset.rfl
      Set.Subset.rfl fun x hx y hy => by simpa [hr] using hroot x hx y hy
    refine ⟨f, hf, (hT.trans hs).mono Set.Subset.rfl Set.Subset.rfl ?_⟩
    have := two_mul_leafCount_sub_one_le (P := P) j
    rw [Nat.add_mul, one_mul, Nat.mul_assoc]
    omega
  · obtain ⟨f, hf, hs⟩ := rules.rect U V o fun x hx y hy => by simpa [hr] using hroot x hx y hy
    exact ⟨f, hf, hs.mono Set.Subset.rfl Set.Subset.rfl
      (Nat.mul_pos (Nat.succ_pos _) (Nat.two_pow_pos _))⟩

end Build

/-! ### The De Morgan and monotone circuits -/

/-- A rectangle on which every pair of inputs differs at `i` is separated by a constant, the
literal `xᵢ` or the literal `¬xᵢ`. -/
private theorem exists_sep_differsAt (A B : Set (BitString n)) (i : Fin n)
    (h : ∀ x ∈ A, ∀ y ∈ B, DiffersAt x y i) :
    ∃ f, Sep f A B ∧ Synthesis Boolean.interpretation (inputs n) {f} 1 := by
  by_cases hA : A.Nonempty
  swap
  · exact ⟨fun _ => false, ⟨fun x hx => (hA ⟨x, hx⟩).elim, fun _ _ => rfl⟩, Synthesis.const false⟩
  by_cases hB : B.Nonempty
  swap
  · exact ⟨fun _ => true, ⟨fun _ _ => rfl, fun y hy => (hB ⟨y, hy⟩).elim⟩, Synthesis.const true⟩
  obtain ⟨x₀, hx₀⟩ := hA
  obtain ⟨y₀, hy₀⟩ := hB
  have hinput : Synthesis Boolean.interpretation (inputs n) {fun x => x i} 0 :=
    Synthesis.of_mem ⟨i, rfl⟩
  cases hxi : x₀ i
  · have hyi : y₀ i = true := by simpa [hxi] using (h x₀ hx₀ y₀ hy₀).symm
    refine ⟨fun x => !x i, ⟨fun x hx => ?_, fun y hy => ?_⟩, hinput.not⟩
    · simpa [hyi] using h x hx y₀ hy₀
    · simpa [hxi] using (h x₀ hx₀ y hy).symm
  · have hyi : y₀ i = false := by simpa [hxi] using (h x₀ hx₀ y₀ hy₀).symm
    refine ⟨fun x => x i, ⟨fun x hx => ?_, fun y hy => ?_⟩,
      hinput.mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le 1)⟩
    · simpa [hyi] using h x hx y₀ hy₀
    · simpa [hxi] using (h x₀ hx₀ y hy).symm

/-- A rectangle on which every pair of inputs has `xᵢ = 1` and `yᵢ = 0` is separated by a
constant or the literal `xᵢ`. -/
private theorem exists_sep_exceedsAt (A B : Set (BitString n)) (i : Fin n)
    (h : ∀ x ∈ A, ∀ y ∈ B, ExceedsAt x y i) :
    ∃ f, Sep f A B ∧ Synthesis Monotone.interpretation (inputs n) {f} 1 := by
  by_cases hA : A.Nonempty
  swap
  · exact ⟨fun _ => false, ⟨fun x hx => (hA ⟨x, hx⟩).elim, fun _ _ => rfl⟩,
      Synthesis.monotone_const false⟩
  by_cases hB : B.Nonempty
  swap
  · exact ⟨fun _ => true, ⟨fun _ _ => rfl, fun y hy => (hB ⟨y, hy⟩).elim⟩,
      Synthesis.monotone_const true⟩
  obtain ⟨x₀, hx₀⟩ := hA
  obtain ⟨y₀, hy₀⟩ := hB
  have hinput : Synthesis Monotone.interpretation (inputs n) {fun x => x i} 0 :=
    Synthesis.of_mem ⟨i, rfl⟩
  exact ⟨fun x => x i, ⟨fun x hx => (h x hx y₀ hy₀).1, fun y hy => (h x₀ hx₀ y hy).2⟩,
    hinput.mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le 1)⟩

variable {P : DagProtocol (BitString n) (BitString n) (Fin n) k} {U V : Set (BitString n)}

/-- **Circuits from dag-like protocols** [Krajíček, Theorem 2.3][Krajicek1997], which Krajíček
credits to Razborov [Razborov1995b]. A dag-like protocol for the Karchmer–Wigderson game on
`U × V` with `k` inner nodes and communication complexity `t` gives a De Morgan circuit with at
most `(k · 2 ^ t + 1) · 2 ^ (t + 1)` gates that is true on `U` and false on `V`. -/
theorem Solves.exists_circuit (hP : P.Solves DiffersAt U V) :
    ∃ C : Circuit Boolean.signature n 1,
      C.size ≤ (k * 2 ^ P.depth + 1) * 2 ^ (P.depth + 1) ∧
      (∀ u ∈ U, C.eval Boolean.interpretation u 0 = true) ∧
      ∀ v ∈ V, C.eval Boolean.interpretation v 0 = false := by
  obtain ⟨f, hf, hs⟩ := exists_sep hP
    ⟨Synthesis.const, exists_sep_differsAt, Synthesis.or, Synthesis.and⟩
  obtain ⟨C, hC, hsize⟩ := hs.exists_circuit
  exact ⟨C, hsize, fun u hu => (congrFun (hC u) 0).trans (hf.1 u hu),
    fun v hv => (congrFun (hC v) 0).trans (hf.2 v hv)⟩

/-- **Monotone circuits from monotone dag-like protocols** [Krajíček, Theorem 2.3][Krajicek1997],
which Krajíček credits to Razborov [Razborov1995b]. A dag-like protocol for the monotone
Karchmer–Wigderson game on `U × V` with `k` inner nodes and communication complexity `t` gives a
monotone circuit with at most `(k · 2 ^ t + 1) · 2 ^ (t + 1)` gates that is true on `U` and false
on `V`. -/
theorem Solves.exists_monotone_circuit (hP : P.Solves ExceedsAt U V) :
    ∃ C : Circuit Monotone.signature n 1,
      C.size ≤ (k * 2 ^ P.depth + 1) * 2 ^ (P.depth + 1) ∧
      (∀ u ∈ U, C.eval Monotone.interpretation u 0 = true) ∧
      ∀ v ∈ V, C.eval Monotone.interpretation v 0 = false := by
  obtain ⟨f, hf, hs⟩ := exists_sep hP
    ⟨Synthesis.monotone_const, exists_sep_exceedsAt, Synthesis.monotone_or,
      Synthesis.monotone_and⟩
  obtain ⟨C, hC, hsize⟩ := hs.exists_circuit
  exact ⟨C, hsize, fun u hu => (congrFun (hC u) 0).trans (hf.1 u hu),
    fun v hv => (congrFun (hC v) 0).trans (hf.2 v hv)⟩

end Cslib.Communication.DagProtocol
