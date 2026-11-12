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
`B(g) = 2` (which is well-formed because `2 ≤ n` and `m + 2 ≤ n + q` for every valid circuit)
and applies `mTopo`. Combining these inverters with the reductions of
`CslibFrontier.Crypto.Primitives.Garbling.Foundations` yields Corollaries 1 and 2 of
[BellareHoangRogaway2012], Sections 4.2 and 4.3, relating `prv.ind` to `prv.sim` and `obv.ind` to
`obv.sim` for `phiTopo`, `phiSize` and `phiCirc`.

## Main definitions

* `Cslib.Crypto.Garbling.Topo`, `Cslib.Crypto.Garbling.ConventionalCircuit`,
  `Cslib.Crypto.Garbling.ValidCircuit`: BHR12 conventional circuits and their topologies.
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

/-- Well-formedness of a conventional circuit ([BellareHoangRogaway2012], Section 2.3):
`2 ≤ n`, `1 ≤ m`, `1 ≤ q`, `m ≤ q` (output wires are disjoint from input wires), and for every
gate `g = n + 1 + i`, `1 ≤ A(g) < B(g) < g` and `B(g) ≤ n + q - m` (output wires are not fed into
any gate). -/
def IsValid (f : ConventionalCircuit) : Prop :=
  2 ≤ f.n ∧ 1 ≤ f.m ∧ 1 ≤ f.q ∧ f.m ≤ f.q ∧
    ∀ i : Fin f.q,
      1 ≤ f.A i ∧ f.A i < f.B i ∧ f.B i < f.n + 1 + i.val ∧ f.B i ≤ f.n + f.q - f.m

instance (f : ConventionalCircuit) : Decidable f.IsValid := by
  unfold IsValid
  infer_instance

theorem IsValid.m_le {f : ConventionalCircuit} (h : f.IsValid) : f.m ≤ f.q := h.2.2.2.1

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

/-- Circuit well-formedness depends only on the topology. -/
theorem isValid_ofTopo_iff (t : Topo) (G G' : Fin t.q → Bool → Bool → Bool) :
    (ofTopo t G).IsValid ↔ (ofTopo t G').IsValid := Iff.rfl

/-- Topologies of valid conventional circuits. -/
abbrev ValidTopo := {t : Topo // (ofTopo t fun _ _ _ => false).IsValid}

/-- Valid circuit shapes `(n, m, q)` satisfying `2 ≤ n`, `1 ≤ m`, `1 ≤ q`, `m ≤ q` and
`m + 2 ≤ n + q`. The predicate reads the triple by position because it defines the layout;
elsewhere use the components `ValidShape.n`, `ValidShape.m` and `ValidShape.q`. -/
abbrev ValidShape :=
  {s : ℕ × ℕ × ℕ // 2 ≤ s.1 ∧ 1 ≤ s.2.1 ∧ 1 ≤ s.2.2 ∧ s.2.1 ≤ s.2.2 ∧ s.2.1 + 2 ≤ s.1 + s.2.2}

/-- The input count `n` of a shape. -/
abbrev ValidShape.n (s : ValidShape) : ℕ := s.1.1

/-- The output count `m` of a shape. -/
abbrev ValidShape.m (s : ValidShape) : ℕ := s.1.2.1

/-- The gate count `q` of a shape. -/
abbrev ValidShape.q (s : ValidShape) : ℕ := s.1.2.2

/-- The shape `(n, m, q)` of any valid conventional circuit is a `ValidShape`. -/
theorem shape_of_isValid {f : ConventionalCircuit} (h : f.IsValid) :
    2 ≤ f.n ∧ 1 ≤ f.m ∧ 1 ≤ f.q ∧ f.m ≤ f.q ∧ f.m + 2 ≤ f.n + f.q := by
  obtain ⟨hn, hm, hq, hmq, hg⟩ := h
  obtain ⟨h1, h2, _, h4⟩ := hg ⟨0, hq⟩
  have h2le : 2 ≤ f.n + f.q - f.m := Nat.le_trans (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt h1 h2)) h4
  have hmlenq : f.m ≤ f.n + f.q := Nat.le_trans hmq (Nat.le_add_left f.q f.n)
  exact ⟨hn, hm, hq, hmq, Nat.add_comm f.m 2 ▸ (Nat.le_sub_iff_add_le hmlenq).mp h2le⟩

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
  phi f := ⟨(f.1.n, f.1.m, f.1.q), shape_of_isValid f.2⟩
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
def mTopo (t : ValidTopo) (y : List Bool) : ValidCircuit × List Bool :=
  (⟨ofTopo t.1 (mTopoGates t.1 y), t.2⟩, List.replicate t.1.n false)

/-- The canonical wiring for a shape `(n, m, q)` ([BellareHoangRogaway2012], Section 4.1,
Proposition 1): every gate takes wires `A(g) = 1` and `B(g) = 2`. -/
def sizeTopo : ℕ × ℕ × ℕ → Topo
  | (n, m, q) => ⟨n, m, q, fun _ => 1, fun _ => 2⟩

theorem sizeTopo_valid (s : ValidShape) :
    (ofTopo (sizeTopo s.1) fun _ _ _ => false).IsValid := by
  obtain ⟨⟨n, m, q⟩, h⟩ := s
  change 2 ≤ n ∧ 1 ≤ m ∧ 1 ≤ q ∧ m ≤ q ∧ m + 2 ≤ n + q at h
  obtain ⟨hn, hm, hq, hmq, hs⟩ := h
  refine ⟨hn, hm, hq, hmq, fun i => ⟨Nat.le_refl 1, Nat.lt_succ_self 1,
    Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hn) (Nat.le_add_right _ _),
    Nat.le_sub_of_add_le' hs⟩⟩

/-- The `(Φ_size, ev)`-inverter `M_size` ([BellareHoangRogaway2012], Section 4.1, Proposition 1):
extend the shape `s = (n, m, q)` with the canonical wiring `A(g) = 1, B(g) = 2` and apply
`mTopo`. -/
def mSize (s : ValidShape) (y : List Bool) : ValidCircuit × List Bool :=
  mTopo ⟨sizeTopo s.1, sizeTopo_valid s⟩ y

/-- The `Φ_topo`-inverter built from `mTopo` by setting `y = 0^m`. -/
def mTopoInv (t : ValidTopo) : ValidCircuit := (mTopo t (List.replicate t.1.m false)).1

/-- The `Φ_size`-inverter built from `mSize` by setting `y = 0^m`. -/
def mSizeInv (s : ValidShape) : ValidCircuit := (mSize s (List.replicate s.m false)).1

@[simp] theorem phiTopo_mTopo (t : ValidTopo) (y : List Bool) :
    phiTopo.phi (mTopo t y).1 = t := rfl

@[simp] theorem phiSize_mSize (s : ValidShape) (y : List Bool) :
    phiSize.phi (mSize s y).1 = s := rfl

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
  intro f x _ f' x' hM
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hM.symm
  refine ⟨rfl, ?_, ?_⟩
  · rw [(hG.1 _).1]
    exact List.length_replicate
  · rw [hG.2, hG.2]
    exact evalCirc_ofTopo_mTopoGates f.1.topo f.2.m_le (f.1.evalCirc x)
      (f.1.length_evalCirc x f.2.m_le)

/-- `mSize` is a `(Φ_size, ev)`-inverter for every circuit garbling scheme
([BellareHoangRogaway2012], Section 4.1, Proposition 1). -/
theorem phiSize_isEvInverter {G : Scheme ValidCircuit} (hG : G.IsCircuitScheme) :
    phiSize.IsEvInverter G mSize := by
  intro f x _ f' x' hM
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hM.symm
  refine ⟨rfl, ?_, ?_⟩
  · rw [(hG.1 _).1]
    exact List.length_replicate
  · rw [hG.2, hG.2]
    exact evalCirc_ofTopo_mTopoGates (sizeTopo (phiSize.phi f).1) f.2.m_le (f.1.evalCirc x)
      (f.1.length_evalCirc x f.2.m_le)

/-! ## Equivalence of indistinguishability and simulation for circuit side information -/

section Corollaries

variable {σ : Type} {G : Scheme ValidCircuit} (hG : G.IsCircuitScheme)
include hG

/-- Corollary 1 of [BellareHoangRogaway2012], Section 4.2 (`Φ_topo`, simulation to
indistinguishability): for any circuit garbling scheme, the `prv.ind` advantage under `phiTopo` is
twice the `prv.sim` advantage of `prvIndToSim` against any simulator. -/
theorem prvIndAdvantage_phiTopo_eq_two_mul_prvSimAdvantage (A : PrvIndAdversary ValidCircuit σ)
    (S : PrvSimulator ValidTopo) (k : ℕ) :
    prvIndAdvantage G phiTopo A k =
      2 * prvSimAdvantage G phiTopo S (prvIndToSim G phiTopo A) k :=
  prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G phiTopo (phiTopo_compatible hG) A S k

/-- Corollary 1 of [BellareHoangRogaway2012], Section 4.2 (`Φ_topo`, indistinguishability to
simulation): for any circuit garbling scheme, the `prv.sim` advantage against the `mTopo` inverter
simulator equals the `prv.ind` advantage of `prvSimToInd`. -/
theorem prvSimAdvantage_phiTopo_mTopo_eq (B : PrvSimAdversary ValidCircuit σ) (k : ℕ) :
    prvSimAdvantage G phiTopo (prvSimFromInverter G mTopo) B k =
      prvIndAdvantage G phiTopo (prvSimToInd G phiTopo mTopo B) k :=
  prvSimAdvantage_prvSimFromInverter_eq G phiTopo (phiTopo_compatible hG)
    (phiTopo_isEvInverter hG) B k

/-- Corollary 1 of [BellareHoangRogaway2012], Section 4.2 (`Φ_size`, simulation to
indistinguishability): for any circuit garbling scheme, the `prv.ind` advantage under `phiSize` is
twice the `prv.sim` advantage of `prvIndToSim` against any simulator. -/
theorem prvIndAdvantage_phiSize_eq_two_mul_prvSimAdvantage (A : PrvIndAdversary ValidCircuit σ)
    (S : PrvSimulator ValidShape) (k : ℕ) :
    prvIndAdvantage G phiSize A k =
      2 * prvSimAdvantage G phiSize S (prvIndToSim G phiSize A) k :=
  prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G phiSize (phiSize_compatible hG) A S k

/-- Corollary 1 of [BellareHoangRogaway2012], Section 4.2 (`Φ_size`, indistinguishability to
simulation): for any circuit garbling scheme, the `prv.sim` advantage against the `mSize` inverter
simulator equals the `prv.ind` advantage of `prvSimToInd`. -/
theorem prvSimAdvantage_phiSize_mSize_eq (B : PrvSimAdversary ValidCircuit σ) (k : ℕ) :
    prvSimAdvantage G phiSize (prvSimFromInverter G mSize) B k =
      prvIndAdvantage G phiSize (prvSimToInd G phiSize mSize B) k :=
  prvSimAdvantage_prvSimFromInverter_eq G phiSize (phiSize_compatible hG)
    (phiSize_isEvInverter hG) B k

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_topo`, simulation to
indistinguishability): for any circuit garbling scheme, the `obv.ind` advantage under `phiTopo` is
twice the `obv.sim` advantage of `obvIndToSim` against any simulator. -/
theorem obvIndAdvantage_phiTopo_eq_two_mul_obvSimAdvantage (A : ObvIndAdversary ValidCircuit σ)
    (S : ObvSimulator ValidTopo) (k : ℕ) :
    obvIndAdvantage G phiTopo A k =
      2 * obvSimAdvantage G phiTopo S (obvIndToSim G phiTopo A) k :=
  obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G phiTopo (phiTopo_compatible hG) A S k

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_topo`, indistinguishability to
simulation): for any circuit garbling scheme, the `obv.sim` advantage against the `mTopoInv`
inverter simulator equals the `obv.ind` advantage of `obvSimToInd`. -/
theorem obvSimAdvantage_phiTopo_mTopoInv_eq (B : ObvSimAdversary ValidCircuit σ) (k : ℕ) :
    obvSimAdvantage G phiTopo (obvSimFromInverter G mTopoInv) B k =
      obvIndAdvantage G phiTopo (obvSimToInd G phiTopo mTopoInv B) k :=
  obvSimAdvantage_obvSimFromInverter_eq G phiTopo (phiTopo_compatible hG) phiTopo_isInverter B k

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_size`, simulation to
indistinguishability): for any circuit garbling scheme, the `obv.ind` advantage under `phiSize` is
twice the `obv.sim` advantage of `obvIndToSim` against any simulator. -/
theorem obvIndAdvantage_phiSize_eq_two_mul_obvSimAdvantage (A : ObvIndAdversary ValidCircuit σ)
    (S : ObvSimulator ValidShape) (k : ℕ) :
    obvIndAdvantage G phiSize A k =
      2 * obvSimAdvantage G phiSize S (obvIndToSim G phiSize A) k :=
  obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G phiSize (phiSize_compatible hG) A S k

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_size`, indistinguishability to
simulation): for any circuit garbling scheme, the `obv.sim` advantage against the `mSizeInv`
inverter simulator equals the `obv.ind` advantage of `obvSimToInd`. -/
theorem obvSimAdvantage_phiSize_mSizeInv_eq (B : ObvSimAdversary ValidCircuit σ) (k : ℕ) :
    obvSimAdvantage G phiSize (obvSimFromInverter G mSizeInv) B k =
      obvIndAdvantage G phiSize (obvSimToInd G phiSize mSizeInv B) k :=
  obvSimAdvantage_obvSimFromInverter_eq G phiSize (phiSize_compatible hG) phiSize_isInverter B k

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_circ`, simulation to
indistinguishability): for any circuit garbling scheme, the `obv.ind` advantage under `phiCirc` is
twice the `obv.sim` advantage of `obvIndToSim` against any simulator. -/
theorem obvIndAdvantage_phiCirc_eq_two_mul_obvSimAdvantage (A : ObvIndAdversary ValidCircuit σ)
    (S : ObvSimulator ValidCircuit) (k : ℕ) :
    obvIndAdvantage G phiCirc A k =
      2 * obvSimAdvantage G phiCirc S (obvIndToSim G phiCirc A) k :=
  obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G phiCirc (phiCirc_compatible hG) A S k

/-- Corollary 2 of [BellareHoangRogaway2012], Section 4.3 (`Φ_circ`, indistinguishability to
simulation): for any circuit garbling scheme, the `obv.sim` advantage against the identity
inverter simulator equals the `obv.ind` advantage of `obvSimToInd`. -/
theorem obvSimAdvantage_phiCirc_id_eq (B : ObvSimAdversary ValidCircuit σ) (k : ℕ) :
    obvSimAdvantage G phiCirc (obvSimFromInverter G id) B k =
      obvIndAdvantage G phiCirc (obvSimToInd G phiCirc id B) k :=
  obvSimAdvantage_obvSimFromInverter_eq G phiCirc (phiCirc_compatible hG) phiCirc_isInverter B k

end Corollaries

end Cslib.Crypto.Garbling
