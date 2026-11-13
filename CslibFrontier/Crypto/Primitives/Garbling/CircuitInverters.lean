/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Foundations
public import Mathlib.Data.Fintype.Pi

/-!
# Conventional circuits and side-information inverters

For circuit garbling schemes in the sense of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012], Sections 2.3 and 4.1, function descriptions are well-formed
conventional Boolean circuits `f = (n, m, q, A, B, G)` with `n ≥ 2` inputs, `m ≥ 1` outputs,
`q ≥ 1` binary gates (`m ≤ q`), 1-indexed wire numbers `1` to `n + q`, and gate inputs satisfying
`1 ≤ A(g) < B(g) < g` and `B(g) ≤ n + q - m` so that output wires are disjoint from input wires
and are never fed into subsequent gates. Unlike `Cslib.Circuits.Circuit`, where input and output
arities are type parameters and output wires may alias arbitrary wires, `ConventionalCircuit`
packages `(n, m, q)` as data inside a single type `ValidCircuit` of function descriptions (so an
adversary can query circuits of chosen sizes) and enforces the BHR12 output-wire convention
needed for total side-information inversion.

Three standard side-information functions (`SideInfo`) on `ValidCircuit` are defined:

* `phiTopo`, revealing the circuit topology `(n, m, q, A, B)` (`ValidTopo`);
* `phiSize`, revealing only the shape `(n, m, q)` (`ValidShape`);
* `phiCirc`, revealing the full circuit.

Following [BellareHoangRogaway2012], Section 4.1, Proposition 1, we construct explicit
deterministic `(Φ, ev)`-inverters `mTopo` and `mSize` and `Φ`-inverters `mTopoInv` and `mSizeInv`.
Given a valid topology `t` and target output `y ∈ {0, 1}^m`, `mTopo` leaves the wiring unchanged,
sets every non-output gate to the constant `false` table and every output gate `g` to the constant
table returning the corresponding bit of `y`, and pairs this circuit with `0^n`. Given a valid
shape `(n, m, q)` and `y`, `mSize` wires every gate to the first two input wires `A(g) = 1`,
`B(g) = 2` (which is well-formed because `2 ≤ n` and `m ≤ q` for every valid circuit) and applies
`mTopo`. Combining these inverters with the reductions of
`CslibFrontier.Crypto.Primitives.Garbling.Foundations` yields Corollaries 1 and 2 of
[BellareHoangRogaway2012], Sections 4.2 and 4.3, relating `prv.ind` to `prv.sim` and `obv.ind` to
`obv.sim` for `phiTopo`, `phiSize` and `phiCirc`.

## Main definitions

* `Cslib.Crypto.Garbling.Topo`, `Cslib.Crypto.Garbling.ConventionalCircuit`,
  `Cslib.Crypto.Garbling.ValidCircuit`: BHR12 conventional circuits and their topologies.
* `Cslib.Crypto.Garbling.Topo.IsValid`, `Cslib.Crypto.Garbling.ConventionalCircuit.IsValid`:
  well-formedness, a property of the topology alone.
* `Cslib.Crypto.Garbling.ValidTopo`, `Cslib.Crypto.Garbling.ValidShape`: valid topologies and
  valid shapes `(n, m, q)`.
* `Cslib.Crypto.Garbling.Scheme.IsCircuitScheme`: schemes over `ValidCircuit` whose length readers
  and semantics agree with `(n, m, q)` and `ConventionalCircuit.evalCirc`.
* `Cslib.Crypto.Garbling.phiTopo`, `Cslib.Crypto.Garbling.phiSize`,
  `Cslib.Crypto.Garbling.phiCirc`: the topology, size and full-circuit side-information functions.
* `Cslib.Crypto.Garbling.mTopo`, `Cslib.Crypto.Garbling.mSize`,
  `Cslib.Crypto.Garbling.mTopoInv`, `Cslib.Crypto.Garbling.mSizeInv`: the explicit `(Φ, ev)`- and
  `Φ`-inverters of [BellareHoangRogaway2012], Section 4.1, Proposition 1.

## Main results

* `Cslib.Crypto.Garbling.phiTopo_isEvInverter`, `Cslib.Crypto.Garbling.phiSize_isEvInverter`,
  `Cslib.Crypto.Garbling.phiTopo_isInverter`, `Cslib.Crypto.Garbling.phiSize_isInverter`,
  `Cslib.Crypto.Garbling.phiCirc_isInverter`: Proposition 1 of [BellareHoangRogaway2012].
* `Cslib.Crypto.Garbling.prvSimAdvantage_phiTopo_mTopo_eq`,
  `Cslib.Crypto.Garbling.prvSimAdvantage_phiSize_mSize_eq`: Corollary 1 of
  [BellareHoangRogaway2012], Section 4.2.
* `Cslib.Crypto.Garbling.obvSimAdvantage_phiTopo_mTopoInv_eq`,
  `Cslib.Crypto.Garbling.obvSimAdvantage_phiSize_mSizeInv_eq`,
  `Cslib.Crypto.Garbling.obvSimAdvantage_phiCirc_id_eq`: Corollary 2 of
  [BellareHoangRogaway2012], Section 4.3.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open scoped NNReal

/-! ## Conventional circuits and topologies -/

/-- The topology `(n, m, q, A, B)` of a conventional Boolean circuit
([BellareHoangRogaway2012], Section 2.3): `n` input wires, `m` output wires, `q` binary gates,
and first/second input-wire maps `A, B : Fin q → ℕ` (with 1-indexed wire numbers). -/
structure Topo where
  /-- The number of input wires `n`. -/
  n : ℕ
  /-- The number of output wires `m`. -/
  m : ℕ
  /-- The number of gates `q`. -/
  q : ℕ
  /-- The first input wire `A(g)` of each gate (1-indexed). -/
  A : Fin q → ℕ
  /-- The second input wire `B(g)` of each gate (1-indexed). -/
  B : Fin q → ℕ
  deriving DecidableEq

/-- Well-formedness of a topology ([BellareHoangRogaway2012], Section 2.3): `2 ≤ n`, `1 ≤ m`,
`1 ≤ q`, `m ≤ q` (output wires are disjoint from input wires), and for every gate `g = n + 1 + i`,
`1 ≤ A(g) < B(g) < g` and `B(g) ≤ n + q - m` (output wires are not fed into any gate). -/
structure Topo.IsValid (t : Topo) : Prop where
  /-- At least two input wires. -/
  two_le_n : 2 ≤ t.n
  /-- At least one output wire. -/
  one_le_m : 1 ≤ t.m
  /-- At least one gate. -/
  one_le_q : 1 ≤ t.q
  /-- The output wires are gate wires, disjoint from the input wires. -/
  m_le_q : t.m ≤ t.q
  /-- Wire numbers start at `1`. -/
  one_le_A : ∀ i, 1 ≤ t.A i
  /-- The first input wire of a gate precedes its second input wire. -/
  A_lt_B : ∀ i, t.A i < t.B i
  /-- A gate reads only earlier wires. -/
  B_lt_gate : ∀ i : Fin t.q, t.B i < t.n + 1 + i.val
  /-- No gate reads an output wire. -/
  B_le_n_add_q_sub_m : ∀ i, t.B i ≤ t.n + t.q - t.m

theorem Topo.isValid_iff (t : Topo) :
    t.IsValid ↔ 2 ≤ t.n ∧ 1 ≤ t.m ∧ 1 ≤ t.q ∧ t.m ≤ t.q ∧ (∀ i, 1 ≤ t.A i) ∧
      (∀ i, t.A i < t.B i) ∧ (∀ i : Fin t.q, t.B i < t.n + 1 + i.val) ∧
      ∀ i, t.B i ≤ t.n + t.q - t.m :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩⟩

instance (t : Topo) : Decidable t.IsValid := decidable_of_iff _ t.isValid_iff.symm

/-- A conventional Boolean circuit `f = (n, m, q, A, B, G)` following
[BellareHoangRogaway2012], Section 2.3: wires are numbered `1` to `n + q`, with inputs `1` to `n`,
gate `i : Fin q` on wire `n + 1 + i.val`, and outputs on the last `m` wires
`n + q - m + 1` to `n + q`. -/
structure ConventionalCircuit where
  /-- The number of input wires `n`. -/
  n : ℕ
  /-- The number of output wires `m`. -/
  m : ℕ
  /-- The number of gates `q`. -/
  q : ℕ
  /-- The first input wire `A(g)` of each gate (1-indexed). -/
  A : Fin q → ℕ
  /-- The second input wire `B(g)` of each gate (1-indexed). -/
  B : Fin q → ℕ
  /-- The truth table `G(g)` of each binary gate. -/
  G : Fin q → Bool → Bool → Bool
  deriving DecidableEq

namespace ConventionalCircuit

/-- The topology of a conventional circuit, forgetting the gate truth tables `G`. -/
def topo (f : ConventionalCircuit) : Topo := ⟨f.n, f.m, f.q, f.A, f.B⟩

/-- Well-formedness of a conventional circuit ([BellareHoangRogaway2012], Section 2.3): its
topology is valid (`Topo.IsValid`). It does not depend on the gate truth tables. -/
abbrev IsValid (f : ConventionalCircuit) : Prop := f.topo.IsValid

/-- Read the 1-indexed wire `w` from a list of wire values, defaulting to `false`. -/
def wireVal (ws : List Bool) (w : ℕ) : Bool := ws[w - 1]?.getD false

/-- The values on the first `n + s` wires (`n` input wires followed by the first `s` gate wires)
when evaluating `f` on `x`. Inputs shorter than `n` are padded with `false`; longer inputs are
truncated to `n` bits. -/
def wires (f : ConventionalCircuit) (x : List Bool) : ℕ → List Bool
  | 0 => x.take f.n ++ List.replicate (f.n - x.length) false
  | s + 1 =>
    if h : s < f.q then
      let ws := f.wires x s
      ws ++ [f.G ⟨s, h⟩ (wireVal ws (f.A ⟨s, h⟩)) (wireVal ws (f.B ⟨s, h⟩))]
    else
      f.wires x s

theorem length_wires (f : ConventionalCircuit) (x : List Bool) {s : ℕ} (hs : s ≤ f.q) :
    (f.wires x s).length = f.n + s := by
  induction s with
  | zero =>
    simp [wires]
    omega
  | succ s ih =>
    have hsq : s < f.q := Nat.lt_of_succ_le hs
    rw [wires, dite_eq_left hsq, List.length_append, ih (Nat.le_of_lt hsq)]
    simp [Nat.add_assoc]

/-- Plaintext evaluation `ev_circ(f, x)` of a conventional circuit ([BellareHoangRogaway2012],
Section 2.3): evaluate all `q` gates and return the values on the final `m` output wires. -/
def evalCirc (f : ConventionalCircuit) (x : List Bool) : List Bool :=
  (f.wires x f.q).drop (f.n + f.q - f.m)

theorem length_evalCirc (f : ConventionalCircuit) (x : List Bool) (hm : f.m ≤ f.q) :
    (f.evalCirc x).length = f.m := by
  simp only [evalCirc, List.length_drop, f.length_wires x le_rfl]
  omega

end ConventionalCircuit

/-- Valid conventional circuits: the function descriptions of circuit garbling. -/
abbrev ValidCircuit := {f : ConventionalCircuit // f.IsValid}

/-- A garbling scheme `G` over `ValidCircuit` is a circuit garbling scheme when its length readers
return `(n, m, q)` and its semantics `ev` is `ConventionalCircuit.evalCirc`
([BellareHoangRogaway2012], Section 3.1). -/
def Scheme.IsCircuitScheme (G : Scheme ValidCircuit) : Prop :=
  (∀ f : ValidCircuit, G.inLen f = f.1.n ∧ G.outLen f = f.1.m ∧ G.size f = f.1.q) ∧
    ∀ (f : ValidCircuit) (x : List Bool), G.ev f x = f.1.evalCirc x

/-- Assemble a conventional circuit from a topology `t` and gate truth tables `G`. -/
def ofTopo (t : Topo) (G : Fin t.q → Bool → Bool → Bool) : ConventionalCircuit :=
  ⟨t.n, t.m, t.q, t.A, t.B, G⟩

@[simp] theorem topo_ofTopo (t : Topo) (G : Fin t.q → Bool → Bool → Bool) :
    (ofTopo t G).topo = t := rfl

/-- Topologies of valid conventional circuits. -/
abbrev ValidTopo := {t : Topo // t.IsValid}

/-- Valid circuit shapes `(n, m, q)`: `2 ≤ n`, `1 ≤ m`, `1 ≤ q` and `m ≤ q`, the shape conditions
of `Topo.IsValid`. -/
structure ValidShape where
  /-- The number of input wires `n`. -/
  n : ℕ
  /-- The number of output wires `m`. -/
  m : ℕ
  /-- The number of gates `q`. -/
  q : ℕ
  /-- At least two input wires. -/
  two_le_n : 2 ≤ n
  /-- At least one output wire. -/
  one_le_m : 1 ≤ m
  /-- At least one gate. -/
  one_le_q : 1 ≤ q
  /-- The output wires are gate wires. -/
  m_le_q : m ≤ q
  deriving DecidableEq

/-! ## Standard side-information functions -/

/-- `Φ_topo(f) = (n, m, q, A, B)`: side information revealing the circuit topology
([BellareHoangRogaway2012], Section 3.3). -/
def phiTopo : SideInfo ValidCircuit ValidTopo where
  phi f := ⟨f.1.topo, f.2⟩
  inLen t := t.1.n
  outLen t := t.1.m
  size t := t.1.q

/-- `Φ_size(f) = (n, m, q)`: side information revealing only the input count, output count and
gate count ([BellareHoangRogaway2012], Section 3.3). -/
def phiSize : SideInfo ValidCircuit ValidShape where
  phi f := ⟨f.1.n, f.1.m, f.1.q, f.2.two_le_n, f.2.one_le_m, f.2.one_le_q, f.2.m_le_q⟩
  inLen s := s.n
  outLen s := s.m
  size s := s.q

/-- `Φ_circ(f) = f`: side information revealing the entire valid circuit
([BellareHoangRogaway2012], Section 3.3). -/
def phiCirc : SideInfo ValidCircuit ValidCircuit where
  phi := id
  inLen f := f.1.n
  outLen f := f.1.m
  size f := f.1.q

theorem phiTopo_compatible {G : Scheme ValidCircuit} (hG : G.IsCircuitScheme) :
    phiTopo.Compatible G := fun f => by
  obtain ⟨h1, h2, h3⟩ := hG.1 f
  exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem phiSize_compatible {G : Scheme ValidCircuit} (hG : G.IsCircuitScheme) :
    phiSize.Compatible G := fun f => by
  obtain ⟨h1, h2, h3⟩ := hG.1 f
  exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem phiCirc_compatible {G : Scheme ValidCircuit} (hG : G.IsCircuitScheme) :
    phiCirc.Compatible G := fun f => by
  obtain ⟨h1, h2, h3⟩ := hG.1 f
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-! ## Explicit side-information inverters -/

/-- Gate tables for `mTopo` ([BellareHoangRogaway2012], Section 4.1, Proposition 1): non-output
gates are constant `false`, while output gate `g = n + 1 + i` is the constant gate returning bit
`g - (n + q - m) - 1` of `y`. -/
def mTopoGates (t : Topo) (y : List Bool) : Fin t.q → Bool → Bool → Bool :=
  fun i _ _ =>
    let g := t.n + 1 + i.val
    if g ≤ t.n + t.q - t.m then false else y[g - (t.n + t.q - t.m) - 1]?.getD false

/-- The `(Φ_topo, ev)`-inverter `M_topo` ([BellareHoangRogaway2012], Section 4.1, Proposition 1):
from a valid topology `t` and output string `y`, build the circuit with topology `t` and constant
gates `mTopoGates t y` paired with the all-zero input `0^n`. -/
def mTopo (t : ValidTopo) (y : List Bool) : Query ValidCircuit :=
  ⟨⟨ofTopo t.1 (mTopoGates t.1 y), t.2⟩, List.replicate t.1.n false⟩

/-- The canonical wiring for a shape `(n, m, q)` ([BellareHoangRogaway2012], Section 4.1,
Proposition 1): every gate takes wires `A(g) = 1` and `B(g) = 2`. -/
def sizeTopo (s : ValidShape) : Topo := ⟨s.n, s.m, s.q, fun _ => 1, fun _ => 2⟩

theorem sizeTopo_isValid (s : ValidShape) : (sizeTopo s).IsValid where
  two_le_n := s.two_le_n
  one_le_m := s.one_le_m
  one_le_q := s.one_le_q
  m_le_q := s.m_le_q
  one_le_A _ := le_rfl
  A_lt_B _ := Nat.one_lt_two
  B_lt_gate _ := by have := s.two_le_n; simp only [sizeTopo]; omega
  B_le_n_add_q_sub_m _ := by have := s.two_le_n; have := s.m_le_q; simp only [sizeTopo]; omega

/-- The `(Φ_size, ev)`-inverter `M_size` ([BellareHoangRogaway2012], Section 4.1, Proposition 1):
extend the shape `s = (n, m, q)` with the canonical wiring `A(g) = 1, B(g) = 2` and apply
`mTopo`. -/
def mSize (s : ValidShape) (y : List Bool) : Query ValidCircuit :=
  mTopo ⟨sizeTopo s, sizeTopo_isValid s⟩ y

/-- The `Φ_topo`-inverter built from `mTopo` by setting `y = 0^m`. -/
def mTopoInv (t : ValidTopo) : ValidCircuit := (mTopo t (List.replicate t.1.m false)).fn

/-- The `Φ_size`-inverter built from `mSize` by setting `y = 0^m`. -/
def mSizeInv (s : ValidShape) : ValidCircuit := (mSize s (List.replicate s.m false)).fn

@[simp] theorem phiTopo_mTopo (t : ValidTopo) (y : List Bool) :
    phiTopo.phi (mTopo t y).fn = t := rfl

@[simp] theorem phiSize_mSize (s : ValidShape) (y : List Bool) :
    phiSize.phi (mSize s y).fn = s := rfl

/-- `mTopoInv` is a `Φ_topo`-inverter ([BellareHoangRogaway2012], Section 4.1, Proposition 1). -/
theorem phiTopo_isInverter : phiTopo.IsInverter mTopoInv := fun _ => rfl

/-- `mSizeInv` is a `Φ_size`-inverter ([BellareHoangRogaway2012], Section 4.1, Proposition 1). -/
theorem phiSize_isInverter : phiSize.IsInverter mSizeInv := fun _ => rfl

/-- The identity is a `Φ_circ`-inverter ([BellareHoangRogaway2012], Section 4.1, Proposition 1). -/
theorem phiCirc_isInverter : phiCirc.IsInverter id := fun _ => rfl

/-- Wire evaluation for any circuit whose gate tables `fun i _ _ => c i` depend only on the gate
index `i`. -/
theorem wires_ofTopo_const (t : Topo) (c : Fin t.q → Bool) (x : List Bool) (hx : x.length = t.n)
    (s : ℕ) (hs : s ≤ t.q) :
    (ofTopo t (fun i _ _ => c i)).wires x s =
      x ++ List.ofFn (fun i : Fin s => c ⟨i.val, Nat.lt_of_lt_of_le i.isLt hs⟩) := by
  induction s with
  | zero =>
    simp [ConventionalCircuit.wires, ofTopo, hx, List.take_of_length_le (le_of_eq hx)]
  | succ s ih =>
    have hsq : s < (ofTopo t (fun i _ _ => c i)).q := Nat.lt_of_succ_le hs
    rw [ConventionalCircuit.wires, dite_eq_left hsq, ih (Nat.le_of_lt hsq)]
    rw [List.append_assoc, List.ofFn_succ' (f := fun i : Fin (s + 1) =>
      c ⟨i.val, Nat.lt_of_lt_of_le i.isLt hs⟩)]
    simp [List.concat_eq_append, ofTopo]

/-- Because `mTopoGates t y` ignores gate wire inputs, `(ofTopo t (mTopoGates t y)).evalCirc x = y`
for every `t.n`-bit input `x` whenever `t.m ≤ t.q` and `y.length = t.m`. -/
theorem evalCirc_ofTopo_mTopoGates_any (t : Topo) (hm : t.m ≤ t.q) (y x : List Bool)
    (hy : y.length = t.m) (hx : x.length = t.n) :
    (ofTopo t (mTopoGates t y)).evalCirc x = y := by
  unfold ConventionalCircuit.evalCirc
  have hw := wires_ofTopo_const t (fun i => mTopoGates t y i false false) x hx t.q le_rfl
  change ((ofTopo t (fun i _ _ => mTopoGates t y i false false)).wires x t.q).drop
    (t.n + t.q - t.m) = y
  rw [hw]
  apply List.ext_getElem
  · simp [hy, hx]
    omega
  · intro j h1 h2
    rw [List.getElem_drop, List.getElem_append_right (by simp [hx]; omega)]
    simp only [hx, List.getElem_ofFn, mTopoGates]
    have hgt : ¬ (t.n + 1 + (t.n + t.q - t.m + j - t.n) ≤ t.n + t.q - t.m) := by omega
    have hidx : t.n + 1 + (t.n + t.q - t.m + j - t.n) - (t.n + t.q - t.m) - 1 = j := by omega
    simp only [hgt, ↓reduceIte, hidx, List.getElem?_eq_getElem h2, Option.getD_some]

/-- Evaluating `ofTopo t (mTopoGates t y)` on `0^n` returns `y` whenever `t.m ≤ t.q` and
`y.length = t.m`. -/
theorem evalCirc_ofTopo_mTopoGates (t : Topo) (hm : t.m ≤ t.q) (y : List Bool)
    (hy : y.length = t.m) :
    (ofTopo t (mTopoGates t y)).evalCirc (List.replicate t.n false) = y :=
  evalCirc_ofTopo_mTopoGates_any t hm y (List.replicate t.n false) hy List.length_replicate

/-- `mTopo` is a `(Φ_topo, ev)`-inverter for every circuit garbling scheme
([BellareHoangRogaway2012], Section 4.1, Proposition 1). -/
theorem phiTopo_isEvInverter {G : Scheme ValidCircuit} (hG : G.IsCircuitScheme) :
    phiTopo.IsEvInverter G mTopo := by
  intro f x _
  refine ⟨rfl, ?_, ?_⟩
  · rw [(hG.1 _).1]
    exact List.length_replicate
  · rw [hG.2, hG.2]
    exact evalCirc_ofTopo_mTopoGates f.1.topo f.2.m_le_q (f.1.evalCirc x)
      (f.1.length_evalCirc x f.2.m_le_q)

/-- `mSize` is a `(Φ_size, ev)`-inverter for every circuit garbling scheme
([BellareHoangRogaway2012], Section 4.1, Proposition 1). -/
theorem phiSize_isEvInverter {G : Scheme ValidCircuit} (hG : G.IsCircuitScheme) :
    phiSize.IsEvInverter G mSize := by
  intro f x _
  refine ⟨rfl, ?_, ?_⟩
  · rw [(hG.1 _).1]
    exact List.length_replicate
  · rw [hG.2, hG.2]
    exact evalCirc_ofTopo_mTopoGates (sizeTopo (phiSize.phi f)) f.2.m_le_q (f.1.evalCirc x)
      (f.1.length_evalCirc x f.2.m_le_q)

/-! ## Equivalence of indistinguishability and simulation for circuit side information -/

section Corollaries

variable {σ : Type} {G : Scheme ValidCircuit} (hG : G.IsCircuitScheme)
include hG

/-- Corollary 1 of [BellareHoangRogaway2012], Section 4.2 (`Φ_topo`, simulation to
indistinguishability): for any circuit garbling scheme, the `prv.ind` advantage under `phiTopo` is
twice the `prv.sim` advantage of `prvIndToSim` against any simulator. -/
theorem prvIndAdvantage_phiTopo_eq_two_mul_prvSimAdvantage (k : ℕ) (S : PrvSimulator ValidTopo)
    (A : PrvIndAdversary ValidCircuit σ) :
    prvIndAdvantage G phiTopo k A = 2 * prvSimAdvantage G phiTopo k S (prvIndToSim G phiTopo A) :=
  prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G phiTopo (phiTopo_compatible hG) k S A

/-- Corollary 1 of [BellareHoangRogaway2012], Section 4.2 (`Φ_topo`, indistinguishability to
simulation): for any circuit garbling scheme, the `prv.sim` advantage against the `mTopo` inverter
simulator equals the `prv.ind` advantage of `prvSimToInd`. -/
theorem prvSimAdvantage_phiTopo_mTopo_eq (k : ℕ) (B : PrvSimAdversary ValidCircuit σ) :
    prvSimAdvantage G phiTopo k (prvSimFromInverter G k mTopo) B =
      prvIndAdvantage G phiTopo k (prvSimToInd G phiTopo mTopo B) :=
  prvSimAdvantage_prvSimFromInverter_eq G phiTopo (phiTopo_compatible hG)
    (phiTopo_isEvInverter hG) k B

/-- Corollary 1 of [BellareHoangRogaway2012], Section 4.2 (`Φ_size`, simulation to
indistinguishability): for any circuit garbling scheme, the `prv.ind` advantage under `phiSize` is
twice the `prv.sim` advantage of `prvIndToSim` against any simulator. -/
theorem prvIndAdvantage_phiSize_eq_two_mul_prvSimAdvantage (k : ℕ) (S : PrvSimulator ValidShape)
    (A : PrvIndAdversary ValidCircuit σ) :
    prvIndAdvantage G phiSize k A = 2 * prvSimAdvantage G phiSize k S (prvIndToSim G phiSize A) :=
  prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G phiSize (phiSize_compatible hG) k S A

/-- Corollary 1 of [BellareHoangRogaway2012], Section 4.2 (`Φ_size`, indistinguishability to
simulation): for any circuit garbling scheme, the `prv.sim` advantage against the `mSize` inverter
simulator equals the `prv.ind` advantage of `prvSimToInd`. -/
theorem prvSimAdvantage_phiSize_mSize_eq (k : ℕ) (B : PrvSimAdversary ValidCircuit σ) :
    prvSimAdvantage G phiSize k (prvSimFromInverter G k mSize) B =
      prvIndAdvantage G phiSize k (prvSimToInd G phiSize mSize B) :=
  prvSimAdvantage_prvSimFromInverter_eq G phiSize (phiSize_compatible hG)
    (phiSize_isEvInverter hG) k B

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_topo`, simulation to
indistinguishability): for any circuit garbling scheme, the `obv.ind` advantage under `phiTopo` is
twice the `obv.sim` advantage of `obvIndToSim` against any simulator. -/
theorem obvIndAdvantage_phiTopo_eq_two_mul_obvSimAdvantage (k : ℕ) (S : ObvSimulator ValidTopo)
    (A : ObvIndAdversary ValidCircuit σ) :
    obvIndAdvantage G phiTopo k A = 2 * obvSimAdvantage G phiTopo k S (obvIndToSim G phiTopo A) :=
  obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G phiTopo (phiTopo_compatible hG) k S A

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_topo`, indistinguishability to
simulation): for any circuit garbling scheme, the `obv.sim` advantage against the `mTopoInv`
inverter simulator equals the `obv.ind` advantage of `obvSimToInd`. -/
theorem obvSimAdvantage_phiTopo_mTopoInv_eq (k : ℕ) (B : ObvSimAdversary ValidCircuit σ) :
    obvSimAdvantage G phiTopo k (obvSimFromInverter G k mTopoInv) B =
      obvIndAdvantage G phiTopo k (obvSimToInd G phiTopo mTopoInv B) :=
  obvSimAdvantage_obvSimFromInverter_eq G phiTopo (phiTopo_compatible hG) phiTopo_isInverter k B

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_size`, simulation to
indistinguishability): for any circuit garbling scheme, the `obv.ind` advantage under `phiSize` is
twice the `obv.sim` advantage of `obvIndToSim` against any simulator. -/
theorem obvIndAdvantage_phiSize_eq_two_mul_obvSimAdvantage (k : ℕ) (S : ObvSimulator ValidShape)
    (A : ObvIndAdversary ValidCircuit σ) :
    obvIndAdvantage G phiSize k A = 2 * obvSimAdvantage G phiSize k S (obvIndToSim G phiSize A) :=
  obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G phiSize (phiSize_compatible hG) k S A

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_size`, indistinguishability to
simulation): for any circuit garbling scheme, the `obv.sim` advantage against the `mSizeInv`
inverter simulator equals the `obv.ind` advantage of `obvSimToInd`. -/
theorem obvSimAdvantage_phiSize_mSizeInv_eq (k : ℕ) (B : ObvSimAdversary ValidCircuit σ) :
    obvSimAdvantage G phiSize k (obvSimFromInverter G k mSizeInv) B =
      obvIndAdvantage G phiSize k (obvSimToInd G phiSize mSizeInv B) :=
  obvSimAdvantage_obvSimFromInverter_eq G phiSize (phiSize_compatible hG) phiSize_isInverter k B

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_circ`, simulation to
indistinguishability): for any circuit garbling scheme, the `obv.ind` advantage under `phiCirc` is
twice the `obv.sim` advantage of `obvIndToSim` against any simulator. -/
theorem obvIndAdvantage_phiCirc_eq_two_mul_obvSimAdvantage (k : ℕ) (S : ObvSimulator ValidCircuit)
    (A : ObvIndAdversary ValidCircuit σ) :
    obvIndAdvantage G phiCirc k A = 2 * obvSimAdvantage G phiCirc k S (obvIndToSim G phiCirc A) :=
  obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G phiCirc (phiCirc_compatible hG) k S A

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_circ`, indistinguishability to
simulation): for any circuit garbling scheme, the `obv.sim` advantage against the identity
inverter simulator equals the `obv.ind` advantage of `obvSimToInd`. -/
theorem obvSimAdvantage_phiCirc_id_eq (k : ℕ) (B : ObvSimAdversary ValidCircuit σ) :
    obvSimAdvantage G phiCirc k (obvSimFromInverter G k id) B =
      obvIndAdvantage G phiCirc k (obvSimToInd G phiCirc id B) :=
  obvSimAdvantage_obvSimFromInverter_eq G phiCirc (phiCirc_compatible hG) phiCirc_isInverter k B

end Corollaries

end Cslib.Crypto.Garbling
