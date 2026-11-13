/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.MixedModulus
import CslibFrontier.Probability.Product
import CslibFrontier.Probability.Product.Split
import CslibFrontier.Probability.Uniform

/-!
# The BMR16 garbling scheme for mixed-modulus circuits

The garbling scheme of Ball, Malkin and Rosulek [BallMalkinRosulek2016, Figure 1]
for mixed-modulus circuits (`MixedModulus.MixedModulusCircuit`). Each sort `i` has a secret offset
`Δ_i = (δ_i, 1)` and each wire `w` of sort `i` a zero label `W_w^0`; the label of value
`x ∈ ℤ_{μ i}` is `W_w^x = W_w^0 + x Δ_i`, whose colour is the colour of `W_w^0` plus `x`.

* `Add_m` and `Mult_c` gates are free: the output zero label is the sum of the input zero labels,
  or `c` times the input zero label, and no ciphertext is sent.
* A projection gate `g` from a wire `a` of sort `i` to sort `j` sends one ciphertext for each
  non-zero colour of its input. With `τ` the colour of `W_a^0`, the row of colour `τ + x` encrypts
  `W_g^{φ x}` as `H(g, W_a^x) + W_g^{φ x}`; the output zero label
  `W_g^0 = -H(g, W_a^{-τ}) - φ(-τ) Δ_j` is chosen so that the row of colour `0` is zero and need not
  be sent (row reduction, `reduceRows`). The evaluator holding `W_a` reads the row `c` named by
  its colour, taken to be zero for `c = 0`, and subtracts `H(g, W_a)`.

The input encoding is `(W^0, Δ)`, mapping `x` to `W^0 + x Δ`; the decoding information is the
colour of the zero label of each output wire, so an output label decodes to its colour minus
that colour. [BallMalkinRosulek2016] also sends output hashes, which add authenticity; they play no
role in privacy and are not modelled here. `Mult_c` is allowed for every `c`, not only for `c`
coprime to the modulus.

Correctness (`Garbled.run_ofKeys`) holds for every hash, tweak assignment, offsets and zero labels.

Privacy is simulation-based with the circuit's shape as side information: the simulator
(`simulate`) samples one uniform label per input wire and uniform ciphertexts, and sets the
decoding information so that the evaluated output labels decode to the output. It is polymorphic
in the projection payload, so it cannot read the projection functions (a parametricity argument
about its definition, not a theorem stated here), and it does not take the input. The main
theorem `advantage_realGame_simGame` shows that the advantage of any distinguisher `D` between
the real and the simulated view is *equal* to the mixed-modulus CCR advantage
(`MixedModulus.ccrAdvantage`) of an explicit reduction `reduction`, provided the tweaks of the
gates are distinct. The reduction samples the active labels of the input wires, evaluates the
circuit gate by gate, and asks the oracle, at projection gate `g` reading a wire of value `v` and
active label `A`, the query `(g, A, x - v, φ x - φ v)` for each `x ≠ v`: against the real oracle
the answer is `H(g, W^x) + (φ x - φ v) Δ_j`, which yields the real ciphertexts and active labels,
and against a random function the ciphertexts are uniform. The reduction is legal in the sense of
`MixedModulus.CCRAdversary.IsLegal` (`reduction_isLegal`): along every run it never uses
multiplier `0`, and its queries are determined by their tweak and multiplier. It asks several
queries under one tweak, so it is not legal for the literal Definition 1 of
[BallMalkinRosulek2016]; see `MixedModulus`. Running time is not tracked: there are no cost
bounds for garbling, evaluation, the simulator or the reduction.

## Main definitions

* `Cslib.Crypto.Garbling.BMR16.garbleWith`, `.Garbled`, `.garble`: garbling.
* `Cslib.Crypto.Garbling.BMR16.evaluate`, `.decode`, `.Garbled.run`: evaluation and decoding.
* `Cslib.Crypto.Garbling.BMR16.simulateWith`, `.simulate`, `.realGame`, `.simGame`: the simulator
  and the privacy experiments.
* `Cslib.Crypto.Garbling.BMR16.reduction`: the mixed-modulus CCR adversary.

## Main results

* `Cslib.Crypto.Garbling.BMR16.Garbled.run_ofKeys`, `.Garbled.run_of_mem_support`: correctness.
* `Cslib.Crypto.Garbling.BMR16.View.run_simulateWith`: simulated views decode to the output.
* `Cslib.Crypto.Garbling.BMR16.reduction_isLegal`: the reduction is a legal adversary.
* `Cslib.Crypto.Garbling.BMR16.advantage_realGame_simGame`: privacy, as an equality with the
  mixed-modulus CCR advantage of the reduction.
* `Cslib.Crypto.Garbling.BMR16.advantage_realGame_simGame_le`: privacy from `MixedModulusCCR`.

## References

* [M. Ball, T. Malkin, M. Rosulek, *Garbling Gadgets for Boolean and Arithmetic
  Circuits*][BallMalkinRosulek2016]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling.BMR16

open MixedModulus Probability

variable {ι T : Type} {μ ℓ : ι → ℕ} {P : ι → ι → Type}

/-! ### Garbled tables and row reduction -/

variable (ℓ) in
/-- The garbled tables of a circuit: for a projection gate from sort `i` to sort `j`, one label of
sort `j` for each non-zero colour of its input; addition and multiplication gates have none. -/
def Tables : {Γ Θ : List ι} → MixedModulusCircuit μ P Γ Θ → Type
  | _, _, .output _ => PUnit
  | _, _, .add _ next => Tables next
  | _, _, .mul _ _ next => Tables next
  | _, _, @MixedModulusCircuit.proj _ _ _ _ _ i j _ _ next =>
    ({c : ZMod (μ i) // c ≠ 0} → Label μ ℓ j) × Tables next

instance Tables.instFintype [∀ i, NeZero (μ i)] :
    {Γ Θ : List ι} → (C : MixedModulusCircuit μ P Γ Θ) → Fintype (Tables ℓ C)
  | _, _, .output _ => inferInstanceAs (Fintype PUnit)
  | _, _, .add _ next => instFintype next
  | _, _, .mul _ _ next => instFintype next
  | _, _, .proj _ _ next => @instFintypeProd _ _ _ (instFintype next)

instance Tables.instNonempty :
    {Γ Θ : List ι} → (C : MixedModulusCircuit μ P Γ Θ) → Nonempty (Tables ℓ C)
  | _, _, .output _ => inferInstanceAs (Nonempty PUnit)
  | _, _, .add _ next => instNonempty next
  | _, _, .mul _ _ next => instNonempty next
  | _, _, .proj _ _ next => @instNonemptyProd _ _ _ (instNonempty next)

/-- The row of colour `c` of a projection table; the row of colour `0` is zero. -/
def row {m : ℕ} {L : Type} [Zero L] (R : {c : ZMod m // c ≠ 0} → L) (c : ZMod m) : L :=
  if h : c = 0 then 0 else R ⟨c, h⟩

/-- Row reduction. Given the value `u x` to be sent in the row of input value `x`, relative to a
zero label of colour `τ`, the rows `u (c - τ) - u (-τ)` of the non-zero colours `c` and the label
`-u (-τ)` added to every row, which makes the row of colour `0` zero. -/
def reduceRows {m : ℕ} {L : Type} [AddCommGroup L] (u : ZMod m → L) (τ : ZMod m) :
    ({c : ZMod m // c ≠ 0} → L) × L :=
  (fun c => u (c.1 - τ) - u (-τ), -u (-τ))

/-- Reading the row of the colour of the label of value `v` and subtracting the part `h` of
`u v` gives the reduced label plus the rest of `u v`. -/
theorem row_reduceRows {m : ℕ} {L : Type} [AddCommGroup L] (u : ZMod m → L) (τ v : ZMod m)
    (h w : L) (huv : u v = h + w) :
    row (reduceRows u τ).1 (τ + v) - h = (reduceRows u τ).2 + w := by
  unfold row reduceRows
  dsimp only
  split_ifs with hc
  · have hv : v = -τ := by rw [eq_neg_iff_add_eq_zero, add_comm, hc]
    subst hv
    rw [huv, zero_sub, neg_add, neg_add_cancel_right]
  · rw [add_sub_cancel_left, huv]
    abel

/-- Shifting every value by a constant `z` keeps the rows and shifts the reduced label by `z`. -/
theorem reduceRows_sub_const {m : ℕ} {L : Type} [AddCommGroup L] (u : ZMod m → L) (z : L)
    (τ : ZMod m) :
    reduceRows (fun x => u x - z) τ = ((reduceRows u τ).1, (reduceRows u τ).2 + z) := by
  simp only [reduceRows, sub_sub_sub_cancel_right, neg_sub, Prod.mk.injEq, true_and]
  abel

/-! ### Garbling, evaluation and decoding -/

/-- Garble a circuit, from its gate number `k` on, given the hash `H`, the tweak `tw k` of gate
`k`, the offsets `δ` and the zero labels `E` of the wires so far: the garbled tables and the zero
labels of the output wires. -/
def garbleWith (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) :
    {Γ Θ : List ι} → ℕ → (C : MixedModulusCircuit μ (Projection μ) Γ Θ) → Env (Label μ ℓ) Γ →
      Tables ℓ C × Env (Label μ ℓ) Θ
  | _, _, _, .output outs, E => (PUnit.unit, E.gather outs)
  | _, _, k, .add args next, E => garbleWith H tw δ (k + 1) next (Env.cons (args.map E.get).sum E)
  | _, _, k, .mul c a next, E => garbleWith H tw δ (k + 1) next (Env.cons (c • E.get a) E)
  | _, _, k, @MixedModulusCircuit.proj _ _ _ _ _ i j a φ next, E =>
    let G := reduceRows (fun x => H (tw k) i (E.get a + x • offset δ i) j + φ x • offset δ j)
      (E.get a).2
    let N := garbleWith H tw δ (k + 1) next (Env.cons G.2 E)
    ((G.1, N.1), N.2)

/-- Evaluate garbled tables, from gate number `k` on, given the active labels `A` of the wires so
far: the active labels of the output wires. -/
def evaluate (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) :
    {Γ Θ : List ι} → ℕ → (C : MixedModulusCircuit μ P Γ Θ) → Tables ℓ C → Env (Label μ ℓ) Γ →
      Env (Label μ ℓ) Θ
  | _, _, _, .output outs, _, A => A.gather outs
  | _, _, k, .add args next, R, A => evaluate H tw (k + 1) next R (Env.cons (args.map A.get).sum A)
  | _, _, k, .mul c a next, R, A => evaluate H tw (k + 1) next R (Env.cons (c • A.get a) A)
  | _, _, k, @MixedModulusCircuit.proj _ _ _ _ _ i j a _ next, R, A =>
    evaluate H tw (k + 1) next R.2 (Env.cons (row R.1 (A.get a).2 - H (tw k) i (A.get a) j) A)

/-- Encode residues `V` with zero labels `E` and offsets `δ`: `E + V Δ`. -/
def encode (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) {Γ : List ι} (E : Env (Label μ ℓ) Γ)
    (V : Env (Residue μ) Γ) : Env (Label μ ℓ) Γ :=
  Env.map₂ (fun i W x => W + x • offset δ i) E V

/-- Decode output labels `Y` with decoding information `d`: each colour minus its entry of `d`.
With `d` the colours of the output zero labels this recovers the output values. -/
def decode {Θ : List ι} (d : Env (Residue μ) Θ) (Y : Env (Label μ ℓ) Θ) : Env (Residue μ) Θ :=
  Env.map₂ (fun _ W c => W.2 - c) Y d

/-- The colours of a list of labels. -/
def colours {Θ : List ι} (Y : Env (Label μ ℓ) Θ) : Env (Residue μ) Θ :=
  Env.map (fun _ W => W.2) Y

variable {Γ Θ : List ι}

variable (ℓ) in
/-- A garbled circuit: its tables, its input encoding information (zero labels and offsets), and
its decoding information. -/
structure Garbled (C : MixedModulusCircuit μ P Γ Θ) where
  /-- The garbled tables. -/
  tables : Tables ℓ C
  /-- The zero label of each input wire. -/
  zeroLabels : Env (Label μ ℓ) Γ
  /-- The key parts of the offsets. -/
  offsets : ∀ i, Fin (ℓ i) → ZMod (μ i)
  /-- The colour of the zero label of each output wire. -/
  decoding : Env (Residue μ) Θ

/-- The garbled circuit with offsets `δ` and input zero labels `E`. -/
def Garbled.ofKeys (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) (δ : ∀ i, Fin (ℓ i) → ZMod (μ i))
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (E : Env (Label μ ℓ) Γ) : Garbled ℓ C where
  tables := (garbleWith H tw δ 0 C E).1
  zeroLabels := E
  offsets := δ
  decoding := colours (garbleWith H tw δ 0 C E).2

/-- Encode an input with a garbled circuit's encoding information. -/
def Garbled.encode {C : MixedModulusCircuit μ P Γ Θ} (G : Garbled ℓ C) (x : Env (Residue μ) Γ) :
    Env (Label μ ℓ) Γ :=
  BMR16.encode G.offsets G.zeroLabels x

/-- Evaluate a garbled circuit on an encoded input and decode the result. -/
def Garbled.run (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) {C : MixedModulusCircuit μ P Γ Θ}
    (G : Garbled ℓ C) (x : Env (Residue μ) Γ) : Env (Residue μ) Θ :=
  decode G.decoding (evaluate H tw 0 C G.tables (G.encode x))

/-- Garble a circuit with uniform offsets and input zero labels. -/
noncomputable def garble [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)]
    (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) (C : MixedModulusCircuit μ (Projection μ) Γ Θ) :
    ProbComp (Garbled ℓ C) := do
  let δ ← ProbComp.uniform (∀ i, Fin (ℓ i) → ZMod (μ i))
  let E ← ProbComp.uniform (Env (Label μ ℓ) Γ)
  return Garbled.ofKeys H tw δ C E

/-! ### Correctness -/

theorem get_encode (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) (E : Env (Label μ ℓ) Γ)
    (V : Env (Residue μ) Γ) {i : ι} (r : Ref Γ i) :
    (encode δ E V).get r = E.get r + V.get r • offset δ i :=
  Env.get_map₂ _ E V r

theorem encode_cons (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) {i : ι} (W : Label μ ℓ i)
    (E : Env (Label μ ℓ) Γ) (x : ZMod (μ i)) (V : Env (Residue μ) Γ) :
    encode δ (Env.cons W E) (Env.cons x V) = Env.cons (W + x • offset δ i) (encode δ E V) := rfl

theorem gather_encode (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) (E : Env (Label μ ℓ) Γ)
    (V : Env (Residue μ) Γ) (outs : Env (Ref Γ) Θ) :
    (encode δ E V).gather outs = encode δ (E.gather outs) (V.gather outs) :=
  Env.gather_map₂ _ E V outs

/-- The colour of `W + x Δ_i` is the colour of `W` plus `x`. -/
theorem snd_add_smul_offset (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) {i : ι} (W : Label μ ℓ i)
    (x : ZMod (μ i)) : (W + x • offset δ i).2 = W.2 + x := by
  simp [offset]

/-- Decoding encoded output labels with the colours of their zero labels gives the values. -/
theorem decode_colours_encode (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) :
    {Θ : List ι} → (Z : Env (Label μ ℓ) Θ) → (y : Env (Residue μ) Θ) →
      decode (colours Z) (encode δ Z y) = y
  | [], _, _ => rfl
  | _ :: _, Z, y => by
    change ((Z.1 + y.1 • offset δ _).2 - Z.1.2, decode (colours Z.2) (encode δ Z.2 y.2)) =
      (y.1, y.2)
    rw [snd_add_smul_offset, decode_colours_encode δ Z.2 y.2, add_sub_cancel_left]

/-- Decoding output labels `Y` with information `decode y Y` gives `y`. -/
theorem decode_decode : {Θ : List ι} → (y : Env (Residue μ) Θ) → (Y : Env (Label μ ℓ) Θ) →
    decode (decode y Y) Y = y
  | [], _, _ => rfl
  | _ :: _, y, Y => by
    change (Y.1.2 - (Y.1.2 - y.1), decode (decode y.2 Y.2) Y.2) = (y.1, y.2)
    rw [decode_decode y.2 Y.2, sub_sub_cancel]

/-- Evaluation follows the labels of the actual wire values: with zero labels `E`, the active
labels `E + V Δ` evaluate to the encoded output values. -/
theorem evaluate_garbleWith (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) {Γ Θ : List ι} (k : ℕ)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (E : Env (Label μ ℓ) Γ)
    (V : Env (Residue μ) Γ) :
    evaluate H tw k C (garbleWith H tw δ k C E).1 (encode δ E V) =
      encode δ (garbleWith H tw δ k C E).2 (C.eval V) := by
  induction C generalizing k with
  | output outs => exact gather_encode δ E V outs
  | @add _ _ i args next ih =>
    have hsum : (args.map fun r => (encode δ E V).get r).sum =
        (args.map fun r => E.get r).sum + (args.map fun r => V.get r).sum • offset δ i := by
      simp only [get_encode, List.sum_map_add, List.sum_smul, List.map_map, Function.comp_def]
    simp only [evaluate, garbleWith, MixedModulusCircuit.eval, hsum, ← encode_cons, ih]
  | @mul _ _ i c a next ih =>
    have hmul : c • (encode δ E V).get a = c • E.get a + (c * V.get a) • offset δ i := by
      rw [get_encode, smul_add, mul_smul]
    simp only [evaluate, garbleWith, MixedModulusCircuit.eval, hmul, ← encode_cons, ih]
  | @proj _ _ i j a φ next ih =>
    have hrow := row_reduceRows
      (fun x => H (tw k) i (E.get a + x • offset δ i) j + φ x • offset δ j) (E.get a).2 (V.get a)
      (H (tw k) i ((encode δ E V).get a) j) (φ (V.get a) • offset δ j) (by rw [get_encode])
    simp only [evaluate, garbleWith, MixedModulusCircuit.eval, get_encode, snd_add_smul_offset]
    rw [← get_encode, hrow, ← encode_cons, ih]

/-- **Correctness**: evaluating a garbled circuit on an encoded input and decoding gives the
circuit's output, for every hash, tweak assignment, offsets and zero labels. -/
theorem Garbled.run_ofKeys (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) (C : MixedModulusCircuit μ (Projection μ) Γ Θ)
    (E : Env (Label μ ℓ) Γ) (x : Env (Residue μ) Γ) :
    (Garbled.ofKeys H tw δ C E).run H tw x = C.eval x := by
  simp only [Garbled.run, Garbled.ofKeys, Garbled.encode]
  rw [evaluate_garbleWith, decode_colours_encode]

/-- **Correctness** of the randomized garbling: every garbled circuit it can output evaluates
correctly on every input. -/
theorem Garbled.run_of_mem_support [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)]
    (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) (C : MixedModulusCircuit μ (Projection μ) Γ Θ)
    {G : Garbled ℓ C} (hG : G ∈ (ProbComp.eval (garble H tw C)).support)
    (x : Env (Residue μ) Γ) : G.run H tw x = C.eval x := by
  simp only [garble, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hG
  obtain ⟨δ, -, E, -, rfl⟩ := hG
  exact Garbled.run_ofKeys H tw δ C E x

/-! ### The privacy experiments -/

variable (ℓ) in
/-- What the evaluator of a garbled circuit sees: the garbled tables, one label per input wire and
the decoding information. The circuit's shape is public, as an index of the type. -/
@[ext] structure View (C : MixedModulusCircuit μ P Γ Θ) where
  /-- The garbled tables. -/
  tables : Tables ℓ C
  /-- The label of each input wire. -/
  input : Env (Label μ ℓ) Γ
  /-- The decoding information. -/
  decoding : Env (Residue μ) Θ

/-- The view of a garbled circuit on an input. -/
def Garbled.view {C : MixedModulusCircuit μ P Γ Θ} (G : Garbled ℓ C) (x : Env (Residue μ) Γ) :
    View ℓ C :=
  ⟨G.tables, G.encode x, G.decoding⟩

/-- Evaluate a view and decode the result. -/
def View.run (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) {C : MixedModulusCircuit μ P Γ Θ}
    (V : View ℓ C) : Env (Residue μ) Θ :=
  decode V.decoding (evaluate H tw 0 C V.tables V.input)

/-- Running the view of a garbled circuit on `x` is running the garbled circuit on `x`. -/
theorem Garbled.run_view (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    {C : MixedModulusCircuit μ P Γ Θ} (G : Garbled ℓ C) (x : Env (Residue μ) Γ) :
    (G.view x).run H tw = G.run H tw x := rfl

/-- The simulated view with input labels `A` and tables `R`: the decoding information makes the
evaluated output labels decode to `y`. -/
def simulateWith (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) (C : MixedModulusCircuit μ P Γ Θ)
    (y : Env (Residue μ) Θ) (A : Env (Label μ ℓ) Γ) (R : Tables ℓ C) : View ℓ C :=
  ⟨R, A, decode y (evaluate H tw 0 C R A)⟩

/-- **Simulator correctness**: every simulated view decodes to `y`. -/
theorem View.run_simulateWith (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (C : MixedModulusCircuit μ P Γ Θ) (y : Env (Residue μ) Θ) (A : Env (Label μ ℓ) Γ)
    (R : Tables ℓ C) : (simulateWith H tw C y A R).run H tw = y :=
  decode_decode y _

/-! ### The reduction -/


/-- Against a fixed oracle `f`, the value the reduction encrypts in the row of input value `x` of
a projection gate with tweak `t` reading a wire with active label `W` and value `v`: `H(t, W)`
for `x = v`, and otherwise the reply to the query `(t, W, x - v, φ x - φ v)`. -/
def rowsWith (f : (q : T × CCRInput μ ℓ) → Label μ ℓ q.2.target) (H : MixedModulusHash T μ ℓ)
    (t : T) {i j : ι} (W : Label μ ℓ i) (v : ZMod (μ i)) (φ : Projection μ i j) (x : ZMod (μ i)) :
    Label μ ℓ j :=
  if x = v then H t i W j else f (t, ⟨i, j, W, x - v, φ x - φ v⟩)

/-- The reduction's run against a fixed oracle `f`, from gate number `k` on, given the active
labels `A` and values `V` of the wires so far: the tables and the active labels of the output
wires that it builds. -/
def reduceWith (f : (q : T × CCRInput μ ℓ) → Label μ ℓ q.2.target) (H : MixedModulusHash T μ ℓ)
    (tw : ℕ → T) : {Γ Θ : List ι} → ℕ → (C : MixedModulusCircuit μ (Projection μ) Γ Θ) →
      Env (Label μ ℓ) Γ → Env (Residue μ) Γ → Tables ℓ C × Env (Label μ ℓ) Θ
  | _, _, _, .output outs, A, _ => (PUnit.unit, A.gather outs)
  | _, _, k, .add args next, A, V => reduceWith f H tw (k + 1) next
      (Env.cons (args.map A.get).sum A) (Env.cons (args.map V.get).sum V)
  | _, _, k, .mul c a next, A, V => reduceWith f H tw (k + 1) next
      (Env.cons (c • A.get a) A) (Env.cons (c * V.get a) V)
  | _, _, k, .proj a φ next, A, V =>
    let G := reduceRows (rowsWith f H (tw k) (A.get a) (V.get a) φ) ((A.get a).2 - V.get a)
    let N := reduceWith f H tw (k + 1) next (Env.cons G.2 A) (Env.cons (φ (V.get a)) V)
    ((G.1, N.1), N.2)

/-- The oracle queries of a projection gate, for the input values in `xs`: the table of the values
`rowsWith` encrypts, read from the oracle. -/
def queryRows (H : MixedModulusHash T μ ℓ) (t : T) {i j : ι} (W : Label μ ℓ i) (v : ZMod (μ i))
    (φ : Projection μ i j) : List (ZMod (μ i)) →
      ProbOracleComp (ccrSpec T μ ℓ) (ZMod (μ i) → Label μ ℓ j)
  | [] => pure 0
  | x :: xs => do
    let a ← if x = v then pure (H t i W j)
      else ProbOracleComp.query (spec := ccrSpec T μ ℓ) (t, ⟨i, j, W, x - v, φ x - φ v⟩)
    let u ← queryRows H t W v φ xs
    return Function.update u x a

variable [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)]

/-- The simulator: uniform input labels and uniform tables. It sees the shape of the circuit, the
public hash and tweaks, and the output; being polymorphic in the projection payload `P`, it cannot
read the projection functions. -/
noncomputable def simulate (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (C : MixedModulusCircuit μ P Γ Θ) (y : Env (Residue μ) Θ) : ProbComp (View ℓ C) := do
  let A ← ProbComp.uniform (Env (Label μ ℓ) Γ)
  let R ← ProbComp.uniform (Tables ℓ C)
  return simulateWith H tw C y A R

/-- The real privacy experiment: garble `C` and run `D` on the view of the garbled circuit on
`x`. -/
noncomputable def realGame (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (x : Env (Residue μ) Γ)
    (D : View ℓ C → ProbComp Bool) : Game :=
  ProbComp.eval do
    let G ← garble H tw C
    D (G.view x)

/-- The simulated privacy experiment: run `D` on a view simulated from the shape of `C` and its
output on `x`. -/
noncomputable def simGame (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (x : Env (Residue μ) Γ)
    (D : View ℓ C → ProbComp Bool) : Game :=
  ProbComp.eval do
    let V ← simulate H tw C (C.eval x)
    D V

/-- The reduction's adaptive run, from gate number `k` on: `reduceWith` with oracle queries. -/
noncomputable def reduceM (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) :
    {Γ Θ : List ι} → ℕ → (C : MixedModulusCircuit μ (Projection μ) Γ Θ) → Env (Label μ ℓ) Γ →
      Env (Residue μ) Γ → ProbOracleComp (ccrSpec T μ ℓ) (Tables ℓ C × Env (Label μ ℓ) Θ)
  | _, _, _, .output outs, A, _ => pure (PUnit.unit, A.gather outs)
  | _, _, k, .add args next, A, V => reduceM H tw (k + 1) next
      (Env.cons (args.map A.get).sum A) (Env.cons (args.map V.get).sum V)
  | _, _, k, .mul c a next, A, V => reduceM H tw (k + 1) next
      (Env.cons (c • A.get a) A) (Env.cons (c * V.get a) V)
  | _, _, k, @MixedModulusCircuit.proj _ _ _ _ _ i _ a φ next, A, V => do
    let u ← queryRows H (tw k) (A.get a) (V.get a) φ (Finset.univ : Finset (ZMod (μ i))).toList
    let G := reduceRows u ((A.get a).2 - V.get a)
    let N ← reduceM H tw (k + 1) next (Env.cons G.2 A) (Env.cons (φ (V.get a)) V)
    return ((G.1, N.1), N.2)


/-- The mixed-modulus CCR adversary built from a distinguisher `D` for the circuit `C` on input
`x`: sample active input labels, run the circuit gate by gate with oracle queries at the
projection gates, set the decoding information from the output, and run `D`. -/
noncomputable def reduction (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (x : Env (Residue μ) Γ)
    (D : View ℓ C → ProbComp Bool) : CCRAdversary T μ ℓ := do
  let A ← ProbOracleComp.sample (ProbComp.uniform (Env (Label μ ℓ) Γ))
  let N ← reduceM H tw 0 C A x
  ProbOracleComp.sample (D ⟨N.1, A, decode (C.eval x) N.2⟩)

/-! ### The reduction against the real oracle -/

omit [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)] in
/-- Against the real oracle, the reduction builds the real tables and active output labels. -/
theorem reduceWith_ccrOracle (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) {Γ Θ : List ι} (k : ℕ)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (E : Env (Label μ ℓ) Γ)
    (V : Env (Residue μ) Γ) :
    reduceWith (ccrOracle H δ) H tw k C (encode δ E V) V =
      ((garbleWith H tw δ k C E).1, encode δ (garbleWith H tw δ k C E).2 (C.eval V)) := by
  induction C generalizing k with
  | output outs =>
    simp only [reduceWith, garbleWith, MixedModulusCircuit.eval, gather_encode]
  | @add _ _ i args next ih =>
    have hsum : (args.map fun r => (encode δ E V).get r).sum =
        (args.map fun r => E.get r).sum + (args.map fun r => V.get r).sum • offset δ i := by
      simp only [get_encode, List.sum_map_add, List.sum_smul, List.map_map, Function.comp_def]
    simp only [reduceWith, garbleWith, MixedModulusCircuit.eval, hsum, ← encode_cons, ih]
    rfl
  | @mul _ _ i c a next ih =>
    have hmul : c • (encode δ E V).get a = c • E.get a + (c * V.get a) • offset δ i := by
      rw [get_encode, smul_add, mul_smul]
    simp only [reduceWith, garbleWith, MixedModulusCircuit.eval, hmul, ← encode_cons, ih]
    rfl
  | @proj _ _ i j a φ next ih =>
    have hrows : rowsWith (ccrOracle H δ) H (tw k) ((encode δ E V).get a) (V.get a) φ =
        fun x => (H (tw k) i (E.get a + x • offset δ i) j + φ x • offset δ j) -
          φ (V.get a) • offset δ j := by
      funext x
      simp only [rowsWith, get_encode]
      split_ifs with hx
      · rw [hx, add_sub_cancel_right]
      · have hx' : V.get a • offset δ i + (x - V.get a) • offset δ i = x • offset δ i := by
          rw [← add_smul, add_sub_cancel]
        simp only [ccrOracle, CCRInput.source, CCRInput.target, CCRInput.label, CCRInput.a,
          CCRInput.b, get_encode]
        rw [add_assoc, hx', sub_smul, add_sub_assoc]
    have hτ : ((encode δ E V).get a).2 - V.get a = (E.get a).2 := by
      rw [get_encode, snd_add_smul_offset, add_sub_cancel_right]
    simp only [reduceWith, garbleWith, MixedModulusCircuit.eval, hrows, hτ, reduceRows_sub_const]
    rw [← encode_cons, ih]

omit [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)] in
/-- Decoding encoded output values with the outputs gives the colours of the zero labels. -/
theorem decode_encode (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) :
    {Θ : List ι} → (Z : Env (Label μ ℓ) Θ) → (y : Env (Residue μ) Θ) →
      decode y (encode δ Z y) = colours Z
  | [], _, _ => rfl
  | _ :: _, Z, y => by
    change ((Z.1 + y.1 • offset δ _).2 - y.1, decode y.2 (encode δ Z.2 y.2)) =
      (Z.1.2, colours Z.2)
    rw [snd_add_smul_offset, decode_encode δ Z.2 y.2, add_sub_cancel_right]

omit [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)] in
private theorem encode_unencode (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) :
    {Γ : List ι} → (A : Env (Label μ ℓ) Γ) → (V : Env (Residue μ) Γ) →
      encode δ (Env.map₂ (fun i W x => W - x • offset δ i) A V) V = A
  | [], _, _ => rfl
  | _ :: _, A, V => by
    change (A.1 - V.1 • offset δ _ + V.1 • offset δ _,
      encode δ (Env.map₂ (fun i W x => W - x • offset δ i) A.2 V.2) V.2) = (A.1, A.2)
    rw [sub_add_cancel, encode_unencode δ A.2 V.2]

omit [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)] in
private theorem unencode_encode (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) :
    {Γ : List ι} → (E : Env (Label μ ℓ) Γ) → (V : Env (Residue μ) Γ) →
      Env.map₂ (fun i W x => W - x • offset δ i) (encode δ E V) V = E
  | [], _, _ => rfl
  | _ :: _, E, V => by
    change (E.1 + V.1 • offset δ _ - V.1 • offset δ _,
      Env.map₂ (fun i W x => W - x • offset δ i) (encode δ E.2 V.2) V.2) = (E.1, E.2)
    rw [add_sub_cancel_right, unencode_encode δ E.2 V.2]

omit [Fintype ι] [DecidableEq ι] in
/-- Encoding uniform zero labels gives uniform active labels. -/
theorem map_encode_uniformOfFintype (δ : ∀ i, Fin (ℓ i) → ZMod (μ i)) (V : Env (Residue μ) Γ) :
    (PMF.uniformOfFintype (Env (Label μ ℓ) Γ)).map (fun E => encode δ E V) =
      PMF.uniformOfFintype (Env (Label μ ℓ) Γ) :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv
    ⟨fun E => encode δ E V, fun A => Env.map₂ (fun i W x => W - x • offset δ i) A V,
      fun E => unencode_encode δ E V, fun A => encode_unencode δ A V⟩

/-! ### The reduction against a random function -/

omit [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)] in
/-- Interpreting the queries of a projection gate against a fixed oracle `f` reads `rowsWith f`
on the listed values. -/
theorem interpret_queryRows (f : (q : T × CCRInput μ ℓ) → Label μ ℓ q.2.target)
    (H : MixedModulusHash T μ ℓ) (t : T) {i j : ι} (W : Label μ ℓ i) (v : ZMod (μ i))
    (φ : Projection μ i j) (xs : List (ZMod (μ i))) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun q => (pure (f q) : ProbComp _))
        (queryRows H t W v φ xs) =
      pure (fun x => if x ∈ xs then rowsWith f H t W v φ x else 0) := by
  induction xs with
  | nil => simp only [queryRows, OracleComp.interpret_pure, List.not_mem_nil, ite_false]; rfl
  | cons x xs ih =>
    simp only [queryRows]
    split_ifs with hxv
    · simp only [OracleComp.interpret_bind, ih, pure_bind, OracleComp.interpret_pure]
      congr 1
      funext x'
      by_cases h : x' = x
      · subst h
        simp [rowsWith, hxv]
      · simp [h]
    · simp only [OracleComp.interpret_bind, ProbOracleComp.interpret_query, ih, pure_bind,
        OracleComp.interpret_pure]
      congr 1
      funext x'
      by_cases h : x' = x
      · subst h
        simp [rowsWith, hxv]
      · simp [h]

omit [Fintype ι] [DecidableEq ι] in
/-- Interpreting the adaptive reduction against a fixed oracle `f` is its run `reduceWith f`. -/
theorem interpret_reduceM (f : (q : T × CCRInput μ ℓ) → Label μ ℓ q.2.target)
    (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) {Γ Θ : List ι} (k : ℕ)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (A : Env (Label μ ℓ) Γ)
    (V : Env (Residue μ) Γ) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun q => (pure (f q) : ProbComp _))
        (reduceM H tw k C A V) =
      pure (reduceWith f H tw k C A V) := by
  induction C generalizing k with
  | output outs => exact OracleComp.interpret_pure _ _
  | add args next ih => exact ih _ _ _
  | mul c a next ih => exact ih _ _ _
  | proj a φ next ih =>
    simp only [reduceM, reduceWith, OracleComp.interpret_bind, interpret_queryRows,
      Finset.mem_toList, Finset.mem_univ, ite_true, pure_bind, ih, OracleComp.interpret_pure]

omit [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)] in
/-- **Locality**: the reduction's run from gate `k` on reads the oracle only at the tweaks of the
remaining gates. -/
theorem reduceWith_congr {f g : (q : T × CCRInput μ ℓ) → Label μ ℓ q.2.target}
    (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) {Γ Θ : List ι} (k : ℕ)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (A : Env (Label μ ℓ) Γ)
    (V : Env (Residue μ) Γ)
    (hfg : ∀ n, k ≤ n → n < k + C.size → ∀ r, f (tw n, r) = g (tw n, r)) :
    reduceWith f H tw k C A V = reduceWith g H tw k C A V := by
  induction C generalizing k with
  | output outs => rfl
  | add args next ih =>
    refine ih (k + 1) _ _ fun n h₁ h₂ r => hfg n (by omega) ?_ r
    simp only [MixedModulusCircuit.size]
    omega
  | mul c a next ih =>
    refine ih (k + 1) _ _ fun n h₁ h₂ r => hfg n (by omega) ?_ r
    simp only [MixedModulusCircuit.size]
    omega
  | proj a φ next ih =>
    have hrows : rowsWith f H (tw k) (A.get a) (V.get a) φ =
        rowsWith g H (tw k) (A.get a) (V.get a) φ := by
      funext x
      unfold rowsWith
      split_ifs
      · rfl
      · exact hfg k le_rfl (by simp only [MixedModulusCircuit.size]; omega) _
    simp only [reduceWith, hrows]
    rw [ih (k + 1) _ _ fun n h₁ h₂ r => hfg n (by omega) (by
      simp only [MixedModulusCircuit.size]; omega) r]

omit [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)] in
/-- The rows of a projection gate are uniform when the values of all input values but the active
one are uniform. -/
private theorem map_reduceRows_uniformOfFintype {m : ℕ} [NeZero m] {L : Type} [AddCommGroup L]
    [Fintype L] [Nonempty L] (v τ : ZMod m) (h : L) :
    (PMF.uniformOfFintype ({x : ZMod m // x ≠ v} → L)).map
        (fun o => (reduceRows (fun x => if hx : x = v then h else o ⟨x, hx⟩) τ).1) =
      PMF.uniformOfFintype ({c : ZMod m // c ≠ 0} → L) := by
  apply Cslib.Probability.PMF.uniformOfFintype_map_of_shift
  intro c
  let w : ZMod m → L := fun x => row c (x + τ) - row c (v + τ)
  refine ⟨Equiv.addRight fun x : {x : ZMod m // x ≠ v} => w x.1, fun o => funext fun c' => ?_⟩
  have hext : ∀ y,
      (if hy : y = v then h else (o + fun x : {x : ZMod m // x ≠ v} => w x.1) ⟨y, hy⟩) =
      (if hy : y = v then h else o ⟨y, hy⟩) + w y := by
    intro y
    by_cases hy : y = v
    · subst hy
      simp [w]
    · simp [hy]
  have hc' : row c c'.1 = c c' := by simp [row, c'.2]
  have h0 : row c 0 = 0 := by simp [row]
  change (reduceRows (fun y => if hy : y = v then h
      else (o + fun x : {x : ZMod m // x ≠ v} => w x.1) ⟨y, hy⟩) τ).1 c' =
    (reduceRows (fun y => if hy : y = v then h else o ⟨y, hy⟩) τ).1 c' + c c'
  rw [funext hext]
  simp only [reduceRows, w, sub_add_cancel, neg_add_cancel, hc', h0]
  abel

/-- **The ideal step**: against a uniformly random function, the tables the reduction builds are
uniform, and its active output labels are the evaluation of those tables, provided the remaining
gates have distinct tweaks. -/
theorem bind_reduceWith_uniformOfFintype [Fintype T] [DecidableEq T] {β : Type}
    (H : MixedModulusHash T μ ℓ) (tw : ℕ → T) {Γ Θ : List ι} (k : ℕ)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (A : Env (Label μ ℓ) Γ)
    (V : Env (Residue μ) Γ) (htw : Set.InjOn tw (Set.Ico k (k + C.size)))
    (κ : Tables ℓ C × Env (Label μ ℓ) Θ → PMF β) :
    (PMF.uniformOfFintype (T → CCRTable μ ℓ)).bind
        (fun f => κ (reduceWith (fun q => f q.1 q.2) H tw k C A V)) =
      (PMF.uniformOfFintype (Tables ℓ C)).bind fun R => κ (R, evaluate H tw k C R A) := by
  induction C generalizing k with
  | output outs =>
    simp only [reduceWith, evaluate, PMF.bind_const]
    exact (PMF.bind_const _ _).symm
  | add args next ih =>
    refine ih (k + 1) _ _ (htw.mono fun n hn => ?_) κ
    simp only [Set.mem_Ico, MixedModulusCircuit.size] at hn ⊢
    omega
  | mul c a next ih =>
    refine ih (k + 1) _ _ (htw.mono fun n hn => ?_) κ
    simp only [Set.mem_Ico, MixedModulusCircuit.size] at hn ⊢
    omega
  | @proj _ _ i j a φ next ih =>
    let t := tw k
    let W := A.get a
    let v := V.get a
    let pt : {x : ZMod (μ i) // x ≠ v} → CCRInput μ ℓ := fun x => ⟨i, j, W, x.1 - v, φ x.1 - φ v⟩
    let G : CCRTable μ ℓ → ({c : ZMod (μ i) // c ≠ 0} → Label μ ℓ j) × Label μ ℓ j :=
      fun s => reduceRows (rowsWith (fun q => s q.2) H t W v φ) (W.2 - v)
    let Φ : ({c : ZMod (μ i) // c ≠ 0} → Label μ ℓ j) → PMF β := fun R =>
      (PMF.uniformOfFintype (Tables ℓ next)).bind fun R' =>
        κ ((R, R'), evaluate H tw (k + 1) next R' (Env.cons (row R W.2 - H t i W j) A))
    have hnext : Set.InjOn tw (Set.Ico (k + 1) (k + 1 + next.size)) := htw.mono fun n hn => by
      simp only [Set.mem_Ico, MixedModulusCircuit.size] at hn ⊢
      omega
    -- The rows read only the replies at tweak `t`; the rest of the run never reads them.
    have hupdate : ∀ (g : T → CCRTable μ ℓ) (s : CCRTable μ ℓ),
        reduceWith (fun q => Function.update g t s q.1 q.2) H tw k (.proj a φ next) A V =
          (((G s).1, (reduceWith (fun q => g q.1 q.2) H tw (k + 1) next (Env.cons (G s).2 A)
            (Env.cons (φ v) V)).1), (reduceWith (fun q => g q.1 q.2) H tw (k + 1) next
              (Env.cons (G s).2 A) (Env.cons (φ v) V)).2) := by
      intro g s
      have hrows : rowsWith (fun q => Function.update g t s q.1 q.2) H t W v φ =
          rowsWith (fun q => s q.2) H t W v φ := by
        funext x
        unfold rowsWith
        split_ifs
        · rfl
        · simp only [Function.update_self]
      simp only [reduceWith]
      rw [hrows, reduceWith_congr H tw (k + 1) next _ _ fun n h₁ h₂ r => ?_]
      · rfl
      · have hne : tw n ≠ t := fun hn => by
          have := htw (by simp only [Set.mem_Ico, MixedModulusCircuit.size] at h₂ ⊢; omega)
            (by simp only [Set.mem_Ico, MixedModulusCircuit.size]; omega) hn
          omega
        simp only [Function.update_of_ne hne]
    have hG2 : ∀ s, (G s).2 = row (G s).1 W.2 - H t i W j := fun s => by
      have h := row_reduceRows (rowsWith (fun q => s q.2) H t W v φ) (W.2 - v) v (H t i W j) 0
        (by simp [rowsWith])
      rw [sub_add_cancel, add_zero] at h
      exact h.symm
    have hmap : (PMF.uniformOfFintype (CCRTable μ ℓ)).map (fun s => (G s).1) =
        PMF.uniformOfFintype ({c : ZMod (μ i) // c ≠ 0} → Label μ ℓ j) := by
      have hpt : Function.Injective pt := fun x x' hx => by
        simp only [pt, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, true_and] at hx
        exact Subtype.ext (sub_left_injective hx.1)
      have hG : (fun s => (G s).1) = (fun o : {x : ZMod (μ i) // x ≠ v} → Label μ ℓ j =>
          (reduceRows (fun x => if hx : x = v then H t i W j else o ⟨x, hx⟩) (W.2 - v)).1) ∘
            fun s x => s (pt x) := by
        funext s
        simp only [G, Function.comp_apply, pt, dite_eq_ite]
        rfl
      rw [hG, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_comp_dep hpt]
      exact map_reduceRows_uniformOfFintype v (W.2 - v) (H t i W j)
    calc (PMF.uniformOfFintype (T → CCRTable μ ℓ)).bind
          (fun f => κ (reduceWith (fun q => f q.1 q.2) H tw k (.proj a φ next) A V))
        = (PMF.uniformOfFintype (CCRTable μ ℓ)).bind fun s =>
            (PMF.uniformOfFintype (T → CCRTable μ ℓ)).bind fun g =>
              κ (reduceWith (fun q => Function.update g t s q.1 q.2) H tw k (.proj a φ next)
                A V) :=
          Cslib.Probability.PMF.bind_uniformOfFintype_update t _
      _ = (PMF.uniformOfFintype (CCRTable μ ℓ)).bind fun s => Φ (G s).1 := by
          refine congrArg (PMF.bind _) (funext fun s => ?_)
          simp only [hupdate]
          exact (ih (k + 1) _ _ hnext fun N => κ (((G s).1, N.1), N.2)).trans
            (by simp only [Φ, hG2 s])
      _ = (PMF.uniformOfFintype ({c : ZMod (μ i) // c ≠ 0} → Label μ ℓ j)).bind Φ := by
          rw [← hmap, PMF.bind_map]
          rfl
      _ = (PMF.uniformOfFintype (({c : ZMod (μ i) // c ≠ 0} → Label μ ℓ j) × Tables ℓ next)).bind
            fun RR => κ (RR, evaluate H tw (k + 1) next RR.2
              (Env.cons (row RR.1 W.2 - H t i W j) A)) := by
          rw [← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.bind_bind]
          simp only [Φ, PMF.bind_map]
          rfl
      _ = _ := rfl

/-! ### Privacy -/

/-- Against the real oracle, the reduction plays the real privacy experiment. -/
theorem realGame_eq_ccrRealGame (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (x : Env (Residue μ) Γ)
    (D : View ℓ C → ProbComp Bool) :
    realGame H tw C x D = ccrRealGame H (reduction H tw C x D) := by
  have hself : ∀ {α : Type} (p : ProbComp α), OracleComp.interpret ProbComp.unifFin p = p :=
    fun p => OracleComp.interpret_query_eq_self p
  simp only [realGame, ccrRealGame, reduction, garble, OracleComp.interpret_bind,
    ProbOracleComp.interpret_sample, hself, interpret_reduceM, pure_bind, bind_assoc,
    ProbComp.eval_bind, ProbComp.eval_uniform]
  refine congrArg (PMF.bind _) (funext fun δ => ?_)
  conv_rhs => rw [← map_encode_uniformOfFintype δ x]
  rw [PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun E => ?_)
  simp only [Function.comp_apply, reduceWith_ccrOracle, decode_encode]
  rfl

/-- Against a random function, the reduction plays the simulated privacy experiment, provided
the gates have distinct tweaks. -/
theorem simGame_eq_ccrIdealGame [Fintype T] [DecidableEq T] (H : MixedModulusHash T μ ℓ)
    (tw : ℕ → T) (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (x : Env (Residue μ) Γ)
    (D : View ℓ C → ProbComp Bool) (htw : Set.InjOn tw (Set.Iio C.size)) :
    simGame H tw C x D = ccrIdealGame (reduction H tw C x D) := by
  have hself : ∀ {α : Type} (p : ProbComp α), OracleComp.interpret ProbComp.unifFin p = p :=
    fun p => OracleComp.interpret_query_eq_self p
  simp only [simGame, ccrIdealGame, simulate, reduction, OracleComp.interpret_bind,
    ProbOracleComp.interpret_sample, hself, interpret_reduceM, pure_bind, bind_assoc,
    ProbComp.eval_bind, ProbComp.eval_uniform]
  conv_rhs => rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun A => ?_)
  rw [bind_reduceWith_uniformOfFintype H tw 0 C A x (htw.mono fun n hn => by
    simp only [Set.mem_Ico, Set.mem_Iio] at hn ⊢; omega)
    fun N => ProbComp.eval (D ⟨N.1, A, decode (C.eval x) N.2⟩)]
  rfl

/-- **Simulation privacy of BMR16.** For every mixed-modulus circuit `C`, input `x` and
distinguisher `D`, if the gates have distinct tweaks, the advantage of `D` between the real and
the simulated view equals the mixed-modulus CCR advantage of the reduction against `H`. -/
theorem advantage_realGame_simGame [Fintype T] [DecidableEq T] (H : MixedModulusHash T μ ℓ)
    (tw : ℕ → T) (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (x : Env (Residue μ) Γ)
    (D : View ℓ C → ProbComp Bool) (htw : Set.InjOn tw (Set.Iio C.size)) :
    Game.advantage (realGame H tw C x D) (simGame H tw C x D) =
      ccrAdvantage H (reduction H tw C x D) := by
  rw [realGame_eq_ccrRealGame, simGame_eq_ccrIdealGame H tw C x D htw]

/-! ### Legality of the reduction -/

section Legality

omit [Fintype ι] [DecidableEq ι] [∀ i, NeZero (μ i)]

/-- A run of a program followed by `pure` is a run of the program. -/
private theorem isRun_bind_pure {α β : Type} {p : ProbOracleComp (ccrSpec T μ ℓ) α} {f : α → β}
    {requests : List (ℕ ⊕ (T × CCRInput μ ℓ))} {b : β}
    (h : IsRun (p >>= fun a => pure (f a)) requests b) : ∃ a, IsRun p requests a := by
  obtain ⟨r₁, a, r₂, h₁, h₂, rfl⟩ := h.bind
  obtain ⟨rfl, -⟩ := h₂
  exact ⟨a, by rw [List.append_nil]; exact h₁⟩

/-- Private sampling makes no oracle query. -/
private theorem filterMap_getRight_of_isRun_sample {α : Type} (p : ProbComp α)
    {requests : List (ℕ ⊕ (T × CCRInput μ ℓ))} {a : α}
    (h : IsRun (ProbOracleComp.sample (spec := ccrSpec T μ ℓ) p) requests a) :
    requests.filterMap Sum.getRight? = [] := by
  induction p using PFunctor.FreeM.induction generalizing requests with
  | pure x => obtain ⟨rfl, -⟩ := h; rfl
  | lift_bind q cont ih =>
    obtain ⟨r, rest, rfl, h'⟩ := h
    change rest.filterMap Sum.getRight? = []
    exact ih r h'

/-- The queries of a projection gate with tweak `t` reading a wire with active label `W` and value
`v` are `(t, W, x - v, φ x - φ v)` for values `x ≠ v`. -/
private theorem mem_filterMap_getRight_queryRows (H : MixedModulusHash T μ ℓ) (t : T) {i j : ι}
    (W : Label μ ℓ i) (v : ZMod (μ i)) (φ : Projection μ i j) (xs : List (ZMod (μ i)))
    {requests : List (ℕ ⊕ (T × CCRInput μ ℓ))} {u : ZMod (μ i) → Label μ ℓ j}
    (h : IsRun (queryRows H t W v φ xs) requests u) {q : T × CCRInput μ ℓ}
    (hq : q ∈ requests.filterMap Sum.getRight?) :
    ∃ x, x ≠ v ∧ q = (t, ⟨i, j, W, x - v, φ x - φ v⟩) := by
  induction xs generalizing requests u with
  | nil =>
    obtain ⟨rfl, -⟩ := h
    simp at hq
  | cons x xs ih =>
    simp only [queryRows] at h
    split_ifs at h with hxv
    · obtain ⟨r₁, a, r₂, h₁, h₂, rfl⟩ := h.bind
      obtain ⟨rfl, -⟩ := h₁
      obtain ⟨u', h₂⟩ := isRun_bind_pure h₂
      exact ih h₂ hq
    · obtain ⟨r, rest, rfl, h'⟩ := h
      obtain ⟨u', h'⟩ := isRun_bind_pure h'
      simp only [List.filterMap_cons, Sum.getRight?_inr, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨x, hxv, rfl⟩
      · exact ih h' hq

/-- The query lists produced from gate `k` on, over `n` gates: no multiplier `a` is zero, every
tweak is the tweak of one of these gates, and a query is determined by its tweak, source sort,
label and multiplier `a`. -/
private def GoodQueries (tw : ℕ → T) (k n : ℕ) (qs : List (T × CCRInput μ ℓ)) : Prop :=
  (∀ q ∈ qs, q.2.a ≠ 0 ∧ ∃ m, k ≤ m ∧ m < k + n ∧ q.1 = tw m) ∧
    ∀ q ∈ qs, ∀ q' ∈ qs, ccrKey q = ccrKey q' → q = q'

private theorem goodQueries_append (tw : ℕ → T) (k n : ℕ) {i j : ι} (W : Label μ ℓ i)
    (v : ZMod (μ i)) (φ : Projection μ i j) {L₁ L₂ : List (T × CCRInput μ ℓ)}
    (h₁ : ∀ q ∈ L₁, ∃ x, x ≠ v ∧ q = (tw k, ⟨i, j, W, x - v, φ x - φ v⟩))
    (h₂ : GoodQueries tw (k + 1) n L₂) (htw : Set.InjOn tw (Set.Ico k (k + (n + 1)))) :
    GoodQueries tw k (n + 1) (L₁ ++ L₂) := by
  have hsep : ∀ q ∈ L₁, ∀ q' ∈ L₂, q.1 ≠ q'.1 := by
    intro q hq q' hq' heq
    obtain ⟨x, -, rfl⟩ := h₁ q hq
    obtain ⟨-, m, hm₁, hm₂, hm⟩ := h₂.1 q' hq'
    have := htw (by simp only [Set.mem_Ico]; omega) (by simp only [Set.mem_Ico]; omega)
      (heq.trans hm)
    omega
  refine ⟨fun q hq => ?_, fun q hq q' hq' hkey => ?_⟩
  · rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨x, hx, rfl⟩ := h₁ q hq
      exact ⟨sub_ne_zero.mpr hx, k, le_rfl, by omega, rfl⟩
    · obtain ⟨ha, m, hm₁, hm₂, hm⟩ := h₂.1 q hq
      exact ⟨ha, m, by omega, by omega, hm⟩
  · have h1 : q.1 = q'.1 :=
      congrArg (f := fun p : T × Σ i : ι, Label μ ℓ i × ZMod (μ i) => p.1) hkey
    rcases List.mem_append.mp hq with hq | hq <;> rcases List.mem_append.mp hq' with hq' | hq'
    · obtain ⟨x, -, rfl⟩ := h₁ q hq
      obtain ⟨x', -, rfl⟩ := h₁ q' hq'
      simp only [ccrKey, Prod.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at hkey
      obtain rfl : x = x' := sub_left_injective hkey
      rfl
    · exact absurd h1 (hsep q hq q' hq')
    · exact absurd h1.symm (hsep q' hq' q hq)
    · exact h₂.2 q hq q' hq' hkey

private theorem goodQueries_reduceM [∀ i, NeZero (μ i)] (H : MixedModulusHash T μ ℓ)
    (tw : ℕ → T) {Γ Θ : List ι} (k : ℕ) (C : MixedModulusCircuit μ (Projection μ) Γ Θ)
    (A : Env (Label μ ℓ) Γ) (V : Env (Residue μ) Γ) (htw : Set.InjOn tw (Set.Ico k (k + C.size)))
    {requests : List (ℕ ⊕ (T × CCRInput μ ℓ))} {N : Tables ℓ C × Env (Label μ ℓ) Θ}
    (h : IsRun (reduceM H tw k C A V) requests N) :
    GoodQueries tw k C.size (requests.filterMap Sum.getRight?) := by
  induction C generalizing k requests with
  | output outs =>
    obtain ⟨rfl, -⟩ := h
    simp [GoodQueries]
  | add args next ih =>
    obtain ⟨h₁, h₂⟩ := ih (k + 1) _ _ (htw.mono fun n hn => by
      simp only [Set.mem_Ico, MixedModulusCircuit.size] at hn ⊢; omega) h
    refine ⟨fun q hq => ?_, h₂⟩
    obtain ⟨ha, m, hm₁, hm₂, hm⟩ := h₁ q hq
    exact ⟨ha, m, by omega, by simp only [MixedModulusCircuit.size]; omega, hm⟩
  | mul c a next ih =>
    obtain ⟨h₁, h₂⟩ := ih (k + 1) _ _ (htw.mono fun n hn => by
      simp only [Set.mem_Ico, MixedModulusCircuit.size] at hn ⊢; omega) h
    refine ⟨fun q hq => ?_, h₂⟩
    obtain ⟨ha, m, hm₁, hm₂, hm⟩ := h₁ q hq
    exact ⟨ha, m, by omega, by simp only [MixedModulusCircuit.size]; omega, hm⟩
  | proj a φ next ih =>
    simp only [reduceM] at h
    obtain ⟨r₁, u, r₂, h₁, h₂, rfl⟩ := h.bind
    obtain ⟨N', h₂⟩ := isRun_bind_pure h₂
    rw [List.filterMap_append]
    exact goodQueries_append tw k next.size _ _ φ
      (fun q hq => mem_filterMap_getRight_queryRows H _ _ _ φ _ h₁ hq)
      (ih (k + 1) _ _ (htw.mono fun n hn => by
        simp only [Set.mem_Ico, MixedModulusCircuit.size] at hn ⊢; omega) h₂) htw

/-- **The reduction is legal**: along every run, whatever its private coins and the oracle's
replies, it never uses multiplier `0`, and its queries are determined by their tweak, source sort,
label and multiplier, provided the gates have distinct tweaks. -/
theorem reduction_isLegal [∀ i, NeZero (μ i)] (H : MixedModulusHash T μ ℓ) (tw : ℕ → T)
    (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (x : Env (Residue μ) Γ)
    (D : View ℓ C → ProbComp Bool) (htw : Set.InjOn tw (Set.Iio C.size)) :
    (reduction H tw C x D).IsLegal := by
  intro requests b h
  obtain ⟨r₁, A, r₂, h₁, h₂, rfl⟩ := IsRun.bind h
  obtain ⟨r₃, N, r₄, h₃, h₄, rfl⟩ := h₂.bind
  have hq : (r₁ ++ (r₃ ++ r₄)).filterMap Sum.getRight? = r₃.filterMap Sum.getRight? := by
    rw [List.filterMap_append, List.filterMap_append,
      filterMap_getRight_of_isRun_sample _ h₁, filterMap_getRight_of_isRun_sample _ h₄,
      List.nil_append, List.append_nil]
  obtain ⟨h₅, h₆⟩ := goodQueries_reduceM H tw 0 C A x
    (htw.mono fun n hn => by simp only [Set.mem_Ico, Set.mem_Iio] at hn ⊢; omega) h₃
  change CCRLegal ((r₁ ++ (r₃ ++ r₄)).filterMap Sum.getRight?)
  rw [hq]
  exact ⟨fun q hq => (h₅ q hq).1, h₆⟩

end Legality

/-- **Simulation privacy of BMR16 from mixed-modulus CCR.** If `H` is mixed-modulus CCR with bound
`ε` against a class of adversaries containing the reduction, every distinguisher has advantage at
most `ε` between the real and the simulated view. -/
theorem advantage_realGame_simGame_le [Fintype T] [DecidableEq T] (H : MixedModulusHash T μ ℓ)
    (tw : ℕ → T) (C : MixedModulusCircuit μ (Projection μ) Γ Θ) (x : Env (Residue μ) Γ)
    (D : View ℓ C → ProbComp Bool) (htw : Set.InjOn tw (Set.Iio C.size))
    {𝒟 : Set (CCRAdversary T μ ℓ)} {ε : NNReal} (hH : MixedModulusCCR H 𝒟 ε)
    (hD : reduction H tw C x D ∈ 𝒟) :
    Game.advantage (realGame H tw C x D) (simGame H tw C x D) ≤ ε := by
  rw [advantage_realGame_simGame H tw C x D htw]
  exact hH _ hD (reduction_isLegal H tw C x D htw)

end Cslib.Crypto.Garbling.BMR16
