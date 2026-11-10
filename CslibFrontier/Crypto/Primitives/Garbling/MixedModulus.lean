/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.QueriesWith
public import Mathlib.Data.ZMod.Defs

/-!
# Mixed-modulus circuits and mixed-modulus circular correlation robustness

Ball, Malkin and Rosulek [BallMalkinRosulek2016] garble *mixed-modulus* arithmetic circuits:
every wire carries a residue modulo its own modulus, addition and multiplication by a constant
act within one modulus, and a projection gate applies an arbitrary function
`φ : ℤ_m → ℤ_n` between moduli. Wire sorts are drawn from a finite type `ι`; sort `i` has modulus
`μ i` and wire labels of sort `i` are vectors of `ℤ_{μ i}^{ℓ i + 1}`, split as a key in
`ℤ_{μ i}^{ℓ i}` and a colour, the last coordinate. In [BallMalkinRosulek2016] the key length is
`λ_m = ⌈λ / log₂ m⌉` for security parameter `λ`.

A circuit is a typed straight-line program: `MixedModulusCircuit μ P Γ Θ` reads input wires of
the sorts listed in `Γ`, appends one wire per gate, and outputs wires of the sorts listed in
`Θ`. A wire is referred to by a typed de Bruijn reference `Ref Γ i`, so every gate reads only
earlier wires of the right sorts and no well-formedness side condition is needed. The parameter
`P i j` is the payload of a projection gate from sort `i` to sort `j`: for an actual circuit it is
the function `ℤ_{μ i} → ℤ_{μ j}` (`Projection`); a garbling simulator is polymorphic in `P`, so it
cannot read the projection functions, which are exactly what a garbled circuit hides.

The security of the garbling scheme rests on *mixed-modulus circular correlation robustness*
of a tweakable hash `H` [BallMalkinRosulek2016, Definition 1]. A secret offset `Δ_i = (δ_i, 1)` is
drawn for each sort, with uniform key part and colour `1`. The real oracle answers a query
`(g, i, j, X, a, b)` of source sort `i` and target sort `j` with `H(g, X + a Δ_i) + b Δ_j`; the
ideal oracle is a uniformly random function.

Definition 1 of [BallMalkinRosulek2016] quantifies over adversaries "that query their oracle on
distinct `g` values and `a ≠ 0`". A simulation proof for a projection gate from modulus `m` makes
`m - 1` queries under the tweak of that gate, which this condition forbids, so we use a relaxed
legality condition: along every run, no query uses `a = 0`, and two queries that agree on the
tweak, the source sort, `X` and `a` are equal (`CCRAdversary.IsLegal`). Every adversary legal for
Definition 1 is legal here, so `MixedModulusCCR` is a *stronger* assumption than Definition 1 as
literally stated. A run answers every call, private coin or oracle query, independently with an
arbitrary reply (`IsRun`).

## Main definitions

* `Cslib.Crypto.Garbling.MixedModulus.Ref`, `Cslib.Crypto.Garbling.MixedModulus.Env`: typed wire
  references and assignments of values to the wires of a context.
* `Cslib.Crypto.Garbling.MixedModulus.MixedModulusCircuit`, `.eval`: mixed-modulus circuits with
  `Add_m`, `Mult_c` and `Proj_φ` gates and their evaluation.
* `Cslib.Crypto.Garbling.MixedModulus.CCRInput`: a CCR query without its tweak, read through
  `source`, `target`, `label`, `a` and `b`.
* `Cslib.Crypto.Garbling.MixedModulus.ccrOracle`, `.ccrRealGame`, `.ccrIdealGame`, `.ccrAdvantage`:
  the mixed-modulus circular correlation robustness experiments.
* `Cslib.Crypto.Garbling.MixedModulus.IsRun`: the runs of an oracle program.
* `Cslib.Crypto.Garbling.MixedModulus.CCRAdversary.IsLegal`,
  `Cslib.Crypto.Garbling.MixedModulus.MixedModulusCCR`: legal adversaries and the assumption.

## References

* [M. Ball, T. Malkin, M. Rosulek, *Garbling Gadgets for Boolean and Arithmetic
  Circuits*][BallMalkinRosulek2016]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling.MixedModulus

open scoped NNReal

variable {ι : Type}

/-! ### Typed contexts -/

/-- A reference to a wire of sort `i` in a context `Γ` of wire sorts, newest wire first. -/
inductive Ref : List ι → ι → Type
  /-- The newest wire. -/
  | here {Γ : List ι} {i : ι} : Ref (i :: Γ) i
  /-- A wire before the newest one. -/
  | there {Γ : List ι} {i j : ι} : Ref Γ i → Ref (j :: Γ) i

/-- An element of `X i` for each wire of sort `i` of a context, newest wire first. -/
def Env (X : ι → Type) : List ι → Type
  | [] => PUnit
  | i :: Γ => X i × Env X Γ

namespace Env

variable {X Y Z : ι → Type}

/-- Extend an assignment by a value for a new wire. -/
def cons {Γ : List ι} {i : ι} (x : X i) (e : Env X Γ) : Env X (i :: Γ) := (x, e)

/-- The value of a wire. -/
def get : {Γ : List ι} → {i : ι} → Env X Γ → Ref Γ i → X i
  | _ :: _, _, e, .here => e.1
  | _ :: _, _, e, .there r => get e.2 r

/-- The values of a list of wires. -/
def gather {Γ : List ι} (e : Env X Γ) : {Θ : List ι} → Env (Ref Γ) Θ → Env X Θ
  | [], _ => PUnit.unit
  | _ :: _, rs => (e.get rs.1, e.gather rs.2)

/-- Apply a function to every entry. -/
def map (f : ∀ i, X i → Y i) : {Γ : List ι} → Env X Γ → Env Y Γ
  | [], _ => PUnit.unit
  | _ :: _, e => (f _ e.1, map f e.2)

/-- Combine two assignments entrywise. -/
def map₂ (f : ∀ i, X i → Y i → Z i) : {Γ : List ι} → Env X Γ → Env Y Γ → Env Z Γ
  | [], _, _ => PUnit.unit
  | _ :: _, e, e' => (f _ e.1 e'.1, map₂ f e.2 e'.2)

@[simp] theorem get_cons_here {Γ : List ι} {i : ι} (x : X i) (e : Env X Γ) :
    (cons x e).get .here = x := rfl

@[simp] theorem get_cons_there {Γ : List ι} {i j : ι} (x : X j) (e : Env X Γ) (r : Ref Γ i) :
    (cons x e).get (.there r) = e.get r := rfl

theorem get_map₂ (f : ∀ i, X i → Y i → Z i) {Γ : List ι} (e : Env X Γ) (e' : Env Y Γ) {i : ι}
    (r : Ref Γ i) : (map₂ f e e').get r = f i (e.get r) (e'.get r) := by
  induction r with
  | here => rfl
  | there r ih => exact ih e.2 e'.2

theorem gather_map₂ (f : ∀ i, X i → Y i → Z i) {Γ : List ι} (e : Env X Γ) (e' : Env Y Γ) :
    {Θ : List ι} → (rs : Env (Ref Γ) Θ) →
      (map₂ f e e').gather rs = map₂ f (e.gather rs) (e'.gather rs)
  | [], _ => rfl
  | _ :: _, rs => by
    change ((map₂ f e e').get rs.1, (map₂ f e e').gather rs.2) =
      (f _ (e.get rs.1) (e'.get rs.1), map₂ f (e.gather rs.2) (e'.gather rs.2))
    rw [get_map₂, gather_map₂ f e e' rs.2]

instance instFintype [∀ i, Fintype (X i)] : (Γ : List ι) → Fintype (Env X Γ)
  | [] => inferInstanceAs (Fintype PUnit)
  | i :: Γ => @instFintypeProd (X i) (Env X Γ) _ (instFintype Γ)

instance instNonempty [∀ i, Nonempty (X i)] : (Γ : List ι) → Nonempty (Env X Γ)
  | [] => inferInstanceAs (Nonempty PUnit)
  | i :: Γ => @instNonemptyProd (X i) (Env X Γ) _ (instNonempty Γ)

end Env

/-! ### Mixed-modulus circuits -/

/-- A residue of sort `i`: a wire value in `ℤ_{μ i}`. -/
abbrev Residue (μ : ι → ℕ) (i : ι) : Type := ZMod (μ i)

/-- A wire label of sort `i`: a key in `ℤ_{μ i}^{ℓ i}` and a colour in `ℤ_{μ i}`, that is, a
vector of `ℤ_{μ i}^{ℓ i + 1}` whose last coordinate is the colour. -/
abbrev Label (μ ℓ : ι → ℕ) (i : ι) : Type := (Fin (ℓ i) → ZMod (μ i)) × ZMod (μ i)

/-- The offset `Δ_i = (δ_i, 1)` of sort `i`: key part `δ_i` and colour `1`. -/
def offset {μ ℓ : ι → ℕ} (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) (i : ι) : Label μ ℓ i := (δ i, 1)

/-- The payload of an actual projection gate from sort `i` to sort `j`: a function
`ℤ_{μ i} → ℤ_{μ j}`. -/
abbrev Projection (μ : ι → ℕ) (i j : ι) : Type := ZMod (μ i) → ZMod (μ j)

/-- A mixed-modulus circuit [BallMalkinRosulek2016] with inputs of the sorts in `Γ` and
outputs of the sorts in `Θ`, as a straight-line program: each gate reads earlier wires and appends
a new wire. `P i j` is the payload of a projection gate from sort `i` to sort `j`. -/
inductive MixedModulusCircuit (μ : ι → ℕ) (P : ι → ι → Type) : List ι → List ι → Type
  /-- Output the listed wires. -/
  | output {Γ Θ : List ι} (outs : Env (Ref Γ) Θ) : MixedModulusCircuit μ P Γ Θ
  /-- `Add_m`: the sum modulo `μ i` of the listed wires of sort `i`. -/
  | add {Γ Θ : List ι} {i : ι} (args : List (Ref Γ i)) (next : MixedModulusCircuit μ P (i :: Γ) Θ) :
      MixedModulusCircuit μ P Γ Θ
  /-- `Mult_c`: the product of a wire of sort `i` by the constant `c ∈ ℤ_{μ i}`. -/
  | mul {Γ Θ : List ι} {i : ι} (c : ZMod (μ i)) (arg : Ref Γ i)
      (next : MixedModulusCircuit μ P (i :: Γ) Θ) : MixedModulusCircuit μ P Γ Θ
  /-- `Proj_φ`: a projection from a wire of sort `i` to a new wire of sort `j`. -/
  | proj {Γ Θ : List ι} {i j : ι} (arg : Ref Γ i) (φ : P i j)
      (next : MixedModulusCircuit μ P (j :: Γ) Θ) : MixedModulusCircuit μ P Γ Θ

namespace MixedModulusCircuit

variable {μ : ι → ℕ} {P : ι → ι → Type}

/-- The number of gates. -/
def size : {Γ Θ : List ι} → MixedModulusCircuit μ P Γ Θ → ℕ
  | _, _, .output _ => 0
  | _, _, .add _ next => next.size + 1
  | _, _, .mul _ _ next => next.size + 1
  | _, _, .proj _ _ next => next.size + 1

/-- Evaluate a circuit on the residues of its input wires. -/
def eval : {Γ Θ : List ι} → MixedModulusCircuit μ (Projection μ) Γ Θ → Env (Residue μ) Γ →
    Env (Residue μ) Θ
  | _, _, .output outs, V => V.gather outs
  | _, _, .add args next, V => eval next (Env.cons (args.map V.get).sum V)
  | _, _, .mul c a next, V => eval next (Env.cons (c * V.get a) V)
  | _, _, .proj a φ next, V => eval next (Env.cons (φ (V.get a)) V)

end MixedModulusCircuit

/-! ### Runs of oracle programs -/

/-- A run of an oracle program: the requests it makes, in order, and its result, when each call
is answered independently by an arbitrary reply. Two calls with the same request may get different
replies along one run. -/
def IsRun {Q : Type} {spec : OracleSpec Q} {α : Type} :
    OracleComp spec α → List Q → α → Prop
  | .pure x, requests, a => requests = [] ∧ a = x
  | .liftBind q next, requests, a => ∃ r rest, requests = q :: rest ∧ IsRun (next r) rest a

/-- A run of a sequence splits into a run of its first part and a run of the continuation
selected by the first result. -/
theorem IsRun.bind {Q : Type} {spec : OracleSpec Q} {α β : Type} {p : OracleComp spec α}
    {k : α → OracleComp spec β} {requests : List Q} {b : β} (h : IsRun (p >>= k) requests b) :
    ∃ r₁ a r₂, IsRun p r₁ a ∧ IsRun (k a) r₂ b ∧ requests = r₁ ++ r₂ := by
  induction p using PFunctor.FreeM.induction generalizing requests with
  | pure x => exact ⟨[], x, requests, ⟨rfl, rfl⟩, h, rfl⟩
  | lift_bind q cont ih =>
    obtain ⟨r, rest, rfl, h'⟩ := h
    obtain ⟨r₁, a, r₂, h₁, h₂, rfl⟩ := ih r h'
    exact ⟨q :: r₁, a, r₂, ⟨r, r₁, rfl, h₁⟩, h₂, rfl⟩

/-! ### Mixed-modulus circular correlation robustness -/

variable (T : Type) (μ ℓ : ι → ℕ)

/-- A query `(g, X, a, b)` of the mixed-modulus CCR oracle without its tweak `g`: the source sort
`i`, the target sort `j`, the label `X` of sort `i`, and the multipliers `a ∈ ℤ_{μ i}` and
`b ∈ ℤ_{μ j}`. -/
abbrev CCRInput : Type := Σ i j : ι, Label μ ℓ i × ZMod (μ i) × ZMod (μ j)

namespace CCRInput

variable {μ ℓ}

/-- The source sort `i`. -/
abbrev source (r : CCRInput μ ℓ) : ι := r.1

/-- The target sort `j`. -/
abbrev target (r : CCRInput μ ℓ) : ι := r.2.1

/-- The label `X` of the source sort. -/
abbrev label (r : CCRInput μ ℓ) : Label μ ℓ r.source := r.2.2.1

/-- The multiplier `a ∈ ℤ_{μ i}` of the source offset. -/
abbrev a (r : CCRInput μ ℓ) : ZMod (μ r.source) := r.2.2.2.1

/-- The multiplier `b ∈ ℤ_{μ j}` of the target offset. -/
abbrev b (r : CCRInput μ ℓ) : ZMod (μ r.target) := r.2.2.2.2

end CCRInput

/-- The oracle interface: a query with tweak in `T` is answered by a label of its target sort. -/
abbrev ccrSpec : T × CCRInput μ ℓ → Type := fun q => Label μ ℓ q.2.target

/-- A tweakable mixed-modulus hash `H(g, X)`: a tweak, a label of a source sort and a target
sort give a label of the target sort. -/
abbrev MixedModulusHash : Type := T → (i : ι) → Label μ ℓ i → (j : ι) → Label μ ℓ j

/-- An adversary against mixed-modulus CCR: private coins and adaptive oracle queries. -/
abbrev CCRAdversary : Type := ProbOracleComp (ccrSpec T μ ℓ) Bool

variable {T μ ℓ}

/-- The real mixed-modulus CCR oracle `𝒪_Δ(g, X, a, b) = H(g, X + a Δ_i) + b Δ_j`, for offsets
`Δ_i = (δ_i, 1)`. -/
def ccrOracle (H : MixedModulusHash T μ ℓ) (δ : ∀ i, Fin (ℓ i) → ZMod (μ i))
    (q : T × CCRInput μ ℓ) : Label μ ℓ q.2.target :=
  H q.1 q.2.source (q.2.label + q.2.a • offset δ q.2.source) q.2.target +
    q.2.b • offset δ q.2.target

/-- The part of a query that must determine the whole query in a legal run: the tweak, the source
sort, the label `X` and the multiplier `a`. -/
def ccrKey (q : T × CCRInput μ ℓ) : T × Σ i : ι, Label μ ℓ i × ZMod (μ i) :=
  (q.1, ⟨q.2.source, q.2.label, q.2.a⟩)

/-- A legal list of queries: no query has `a = 0`, and two queries with the same tweak, source
sort, label and multiplier `a` are equal. -/
def CCRLegal (qs : List (T × CCRInput μ ℓ)) : Prop :=
  (∀ q ∈ qs, q.2.a ≠ 0) ∧ ∀ q ∈ qs, ∀ q' ∈ qs, ccrKey q = ccrKey q' → q = q'

/-- A legal adversary makes a legal list of oracle queries along every run, whatever its private
coins and the oracle's replies: the oracle queries are the right components of the requests. -/
def CCRAdversary.IsLegal (B : CCRAdversary T μ ℓ) : Prop :=
  ∀ requests b, IsRun B requests b → CCRLegal (requests.filterMap Sum.getRight?)

variable [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)]

/-- The real experiment: sample the offsets and answer every query with the real oracle. -/
noncomputable def ccrRealGame (H : MixedModulusHash T μ ℓ) (B : CCRAdversary T μ ℓ) : Game :=
  ProbComp.eval do
    let δ ← ProbComp.uniform (∀ i, Fin (ℓ i) → ZMod (μ i))
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun q => pure (ccrOracle H δ q)) B

variable (T μ ℓ) in
/-- A reply for each query with a fixed tweak. -/
abbrev CCRTable : Type := (r : CCRInput μ ℓ) → Label μ ℓ r.target

variable [Fintype T] [DecidableEq T]

/-- Instance search does not find this product of finite function types on its own. -/
instance instFintypeCCRFunction : Fintype (T → CCRTable μ ℓ) :=
  @Pi.instFintype _ _ _ _ fun _ => inferInstance

/-- The ideal experiment: sample a uniformly random function and answer every query with it. -/
noncomputable def ccrIdealGame (B : CCRAdversary T μ ℓ) : Game :=
  ProbComp.eval do
    let f ← ProbComp.uniform (T → CCRTable μ ℓ)
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin
      fun q : T × CCRInput μ ℓ => pure (f q.1 q.2)) B

/-- The mixed-modulus CCR advantage of `B` against `H`. -/
noncomputable abbrev ccrAdvantage (H : MixedModulusHash T μ ℓ) (B : CCRAdversary T μ ℓ) : ℝ≥0 :=
  Game.advantage (ccrRealGame H B) (ccrIdealGame B)

/-- **Mixed-modulus circular correlation robustness** [BallMalkinRosulek2016, Definition 1], with
the relaxed legality condition `CCRAdversary.IsLegal`: every legal adversary in the class `𝒟` has
advantage at most `ε` against `H`. -/
def MixedModulusCCR (H : MixedModulusHash T μ ℓ) (𝒟 : Set (CCRAdversary T μ ℓ)) (ε : ℝ≥0) : Prop :=
  ∀ B ∈ 𝒟, B.IsLegal → ccrAdvantage H B ≤ ε

/-- Every hash is mixed-modulus CCR with bound `1`. -/
theorem MixedModulusCCR.one (H : MixedModulusHash T μ ℓ) (𝒟 : Set (CCRAdversary T μ ℓ)) :
    MixedModulusCCR H 𝒟 1 :=
  fun _ _ _ => Game.advantage_le_one _ _

end Cslib.Crypto.Garbling.MixedModulus
