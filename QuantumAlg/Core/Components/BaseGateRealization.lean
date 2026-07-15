/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.BaseGates
public import QuantumAlg.Util.FinPow
public import QuantumAlg.Util.ResidueEncoding

/-!
# Encoded same-Circuit realizations by base-gate programs

This module bridges semantic data labels to wire-addressed Toffoli/CNOT/X
programs.  A realization supplies a faithful encoding into `Qubits n` basis
labels and a `BaseGateProgram n` whose classical label action implements the
semantic update.  The folded `Circuit` from that same program is then the
shared object for encoded-basis correctness and resource accounting.
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

/-- Faithful encoding of semantic data labels as computational-basis labels of
a binary qubit register. -/
structure BinaryLabelEncoding (Data : Type) where
  /-- Number of qubits in the encoded register. -/
  width : Nat
  /-- Encoding of a semantic data label as a computational-basis label. -/
  encode : Data -> Fin (2 ^ width)
  /-- Semantic labels are not collapsed by the basis-label encoding. -/
  encode_injective : Function.Injective encode

namespace BinaryLabelEncoding

/-- Faithful one-qubit encoding of Boolean labels. -/
def bool : BinaryLabelEncoding Bool where
  width := 1
  encode := fun b => if b then 1 else 0
  encode_injective := by
    intro x y h
    cases x <;> cases y <;> simp at h <;> rfl

/-- Faithful encoding induced by an equivalence with the computational-basis
labels of an `n`-qubit register. -/
def ofEquiv {Data : Type} {n : Nat} (layout : Data ≃ Fin (2 ^ n)) :
    BinaryLabelEncoding Data where
  width := n
  encode := layout
  encode_injective := layout.injective

/-- Relabel the semantic domain of a faithful encoding by an explicit
equivalence. -/
def relabel {Data Other : Type} (encoding : BinaryLabelEncoding Data)
    (layout : Other ≃ Data) : BinaryLabelEncoding Other where
  width := encoding.width
  encode := fun x => encoding.encode (layout x)
  encode_injective := by
    intro x y h
    apply layout.injective
    exact encoding.encode_injective h

/-- Identity encoding for raw computational-basis labels. -/
def finIdentity (n : Nat) : BinaryLabelEncoding (Fin (2 ^ n)) :=
  ofEquiv (Equiv.refl (Fin (2 ^ n)))

/-- Faithful encoding of residues through a canonical binary residue register. -/
def ofResidueEncoding {N n : Nat} (E : BinaryResidueEncoding N n) :
    BinaryLabelEncoding (ZMod N) where
  width := n
  encode := E.encode
  encode_injective := by
    intro x y h
    have hdecode := congrArg E.decode h
    simpa using hdecode

/-- Faithful encoding of unit residues through their underlying canonical
binary residue labels. -/
def ofUnitResidueEncoding {N n : Nat} (E : BinaryResidueEncoding N n) :
    BinaryLabelEncoding ((ZMod N)ˣ) where
  width := n
  encode := fun u => E.encode (u : ZMod N)
  encode_injective := by
    intro x y h
    apply Units.ext
    have hdecode := congrArg E.decode h
    simpa using hdecode

/-- Big-endian product encoding of two semantic fields.  The left field occupies
the more significant slice of the packed computational-basis label. -/
def prod {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) : BinaryLabelEncoding (Left × Right) where
  width := left.width + right.width
  encode := fun x =>
    prodEquiv (m := left.width) (n := right.width)
      (left.encode x.1, right.encode x.2)
  encode_injective := by
    intro x y h
    have hpair :
        (left.encode x.1, right.encode x.2) =
          (left.encode y.1, right.encode y.2) :=
      (prodEquiv (m := left.width) (n := right.width)).injective h
    apply Prod.ext
    · exact left.encode_injective (congrArg Prod.fst hpair)
    · exact right.encode_injective (congrArg Prod.snd hpair)

/-- Faithful encoding of any finite semantic label type into a sufficiently
large binary register.  This is intentionally injective rather than surjective:
most arithmetic state spaces do not have cardinality exactly `2^n`. -/
def ofFintypeCardLe (Data : Type) [Fintype Data] (width : Nat)
    (hcard : Fintype.card Data <= 2 ^ width) : BinaryLabelEncoding Data where
  width := width
  encode := fun x =>
    ⟨(Fintype.equivFin Data x).val,
      Nat.lt_of_lt_of_le (Fintype.equivFin Data x).isLt hcard⟩
  encode_injective := by
    intro x y h
    apply (Fintype.equivFin Data).injective
    apply Fin.ext
    have hval := congrArg Fin.val h
    simpa using hval

@[simp] theorem ofEquiv_width {Data : Type} {n : Nat}
    (layout : Data ≃ Fin (2 ^ n)) :
    (ofEquiv layout).width = n :=
  rfl

@[simp] theorem ofEquiv_encode {Data : Type} {n : Nat}
    (layout : Data ≃ Fin (2 ^ n)) (x : Data) :
    (ofEquiv layout).encode x = layout x :=
  rfl

@[simp] theorem relabel_width {Data Other : Type}
    (encoding : BinaryLabelEncoding Data) (layout : Other ≃ Data) :
    (encoding.relabel layout).width = encoding.width :=
  rfl

@[simp] theorem relabel_encode {Data Other : Type}
    (encoding : BinaryLabelEncoding Data) (layout : Other ≃ Data) (x : Other) :
    (encoding.relabel layout).encode x = encoding.encode (layout x) :=
  rfl

@[simp] theorem finIdentity_width (n : Nat) :
    (finIdentity n).width = n :=
  rfl

@[simp] theorem finIdentity_encode (n : Nat) (x : Fin (2 ^ n)) :
    (finIdentity n).encode x = x :=
  rfl

@[simp] theorem bool_width : bool.width = 1 :=
  rfl

@[simp] theorem bool_encode_false : bool.encode false = 0 :=
  rfl

@[simp] theorem bool_encode_true : bool.encode true = 1 :=
  rfl

@[simp] theorem ofResidueEncoding_width {N n : Nat}
    (E : BinaryResidueEncoding N n) :
    (ofResidueEncoding E).width = n :=
  rfl

@[simp] theorem ofResidueEncoding_encode {N n : Nat}
    (E : BinaryResidueEncoding N n) (z : ZMod N) :
    (ofResidueEncoding E).encode z = E.encode z :=
  rfl

@[simp] theorem ofUnitResidueEncoding_width {N n : Nat}
    (E : BinaryResidueEncoding N n) :
    (ofUnitResidueEncoding E).width = n :=
  rfl

@[simp] theorem ofUnitResidueEncoding_encode {N n : Nat}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ) :
    (ofUnitResidueEncoding E).encode u = E.encode (u : ZMod N) :=
  rfl

@[simp] theorem prod_width {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right) :
    (prod left right).width = left.width + right.width :=
  rfl

@[simp] theorem prod_encode {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (x : Left × Right) :
    (prod left right).encode x =
      prodEquiv (m := left.width) (n := right.width)
        (left.encode x.1, right.encode x.2) :=
  rfl

@[simp] theorem ofFintypeCardLe_width (Data : Type) [Fintype Data]
    (width : Nat) (hcard : Fintype.card Data <= 2 ^ width) :
    (ofFintypeCardLe Data width hcard).width = width :=
  rfl

@[simp] theorem ofFintypeCardLe_encode_val (Data : Type) [Fintype Data]
    (width : Nat) (hcard : Fintype.card Data <= 2 ^ width) (x : Data) :
    ((ofFintypeCardLe Data width hcard).encode x).val =
      (Fintype.equivFin Data x).val :=
  rfl

/-- Equality of encoded labels reflects equality of semantic labels. -/
theorem encode_inj {Data : Type} (encoding : BinaryLabelEncoding Data)
    {x y : Data} (h : encoding.encode x = encoding.encode y) :
    x = y :=
  encoding.encode_injective h

end BinaryLabelEncoding

namespace BaseGateProgram

/-- A base-gate program realizes a semantic update on encoded basis labels. -/
structure Realizes {Data : Type} (encoding : BinaryLabelEncoding Data)
    (program : BaseGateProgram encoding.width) (step : Data -> Data) : Prop where
  /-- The program's classical basis-label action agrees with the semantic
  update after encoding. -/
  applyLabel_eq :
    ∀ x : Data, BaseGateProgram.applyLabel program (encoding.encode x) =
      encoding.encode (step x)

/-- Append a list of base-gate programs in list execution order. -/
def appendList {n : Nat} : List (BaseGateProgram n) -> BaseGateProgram n
  | [] => []
  | program :: rest => BaseGateProgram.append program (appendList rest)

namespace Realizes

/-- The empty program realizes the identity semantic update. -/
theorem id {Data : Type} (encoding : BinaryLabelEncoding Data) :
    Realizes encoding ([] : BaseGateProgram encoding.width) id where
  applyLabel_eq := by
    intro x
    rfl

/-- Sequentially composed programs realize the corresponding semantic
composition in list execution order. -/
theorem append {Data : Type} {encoding : BinaryLabelEncoding Data}
    {first second : BaseGateProgram encoding.width}
    {firstStep secondStep : Data -> Data}
    (hfirst : Realizes encoding first firstStep)
    (hsecond : Realizes encoding second secondStep) :
    Realizes encoding (BaseGateProgram.append first second)
      (fun x => secondStep (firstStep x)) where
  applyLabel_eq := by
    intro x
    rw [BaseGateProgram.applyLabel_append]
    rw [hfirst.applyLabel_eq x]
    rw [hsecond.applyLabel_eq (firstStep x)]

/-- Fold a list of semantic updates in the same execution order as
`BaseGateProgram.appendList`. -/
def stepList {Data : Type} : List (Data -> Data) -> Data -> Data
  | [] => _root_.id
  | step :: rest => fun x => stepList rest (step x)

/-- Splitting a semantic update list composes the two folded updates in
execution order. -/
theorem stepList_append {Data : Type}
    (first second : List (Data -> Data)) (x : Data) :
    stepList (first ++ second) x =
      stepList second (stepList first x) := by
  induction first generalizing x with
  | nil =>
      rfl
  | cons step rest ih =>
      simp [stepList, ih]

/-- Extending a semantic prefix by one step applies the selected next step
after the shorter prefix. -/
theorem stepList_take_succ {Data : Type}
    (steps : List (Data -> Data)) (i : Nat) (h : i < steps.length)
    (x : Data) :
    stepList (steps.take (i + 1)) x =
      steps.get ⟨i, h⟩ (stepList (steps.take i) x) := by
  rw [← List.take_concat_get' steps i h]
  rw [stepList_append]
  rfl

/-- A list of realized base-gate programs realizes the corresponding folded
semantic update in list execution order. -/
theorem appendList {Data : Type} (encoding : BinaryLabelEncoding Data) :
    ∀ (programs : List (BaseGateProgram encoding.width))
      (steps : List (Data -> Data)),
      List.Forall₂ (fun program step => Realizes encoding program step)
        programs steps ->
      Realizes encoding (BaseGateProgram.appendList programs) (stepList steps)
  | [], [], _ => by
      simpa [BaseGateProgram.appendList, stepList] using Realizes.id encoding
  | _ :: _, [], h => by
      cases h
  | [], _ :: _, h => by
      cases h
  | program :: programs, step :: steps, h => by
      cases h with
      | cons hhead htail =>
          simpa [BaseGateProgram.appendList, stepList] using
            Realizes.append hhead
              (appendList encoding programs steps htail)

/-- If a realized semantic update has a right inverse, the reversed base-gate
program realizes that inverse update on encoded labels. -/
theorem inverse_of_rightInverse {Data : Type} {encoding : BinaryLabelEncoding Data}
    {program : BaseGateProgram encoding.width} {step stepInv : Data -> Data}
    (h : Realizes encoding program step)
    (hright : ∀ x : Data, step (stepInv x) = x) :
    Realizes encoding (BaseGateProgram.inverse program) stepInv where
  applyLabel_eq := by
    intro x
    have hforward :
        BaseGateProgram.applyLabel program (encoding.encode (stepInv x)) =
          encoding.encode x := by
      simpa [hright x] using h.applyLabel_eq (stepInv x)
    calc
      BaseGateProgram.applyLabel (BaseGateProgram.inverse program)
          (encoding.encode x)
          =
        BaseGateProgram.applyLabel (BaseGateProgram.inverse program)
          (BaseGateProgram.applyLabel program (encoding.encode (stepInv x))) := by
            rw [hforward]
      _ = encoding.encode (stepInv x) :=
        BaseGateProgram.applyLabel_inverse_applyLabel program
          (encoding.encode (stepInv x))

/-- A semantic update realized by a reversible base-gate program is injective.

The proof uses the program inverse on encoded labels, so this lemma lets higher
layers derive a semantic inverse only from the same gate object that supplies
correctness and resource accounting. -/
theorem injective {Data : Type} {encoding : BinaryLabelEncoding Data}
    {program : BaseGateProgram encoding.width} {step : Data -> Data}
    (h : Realizes encoding program step) :
    Function.Injective step := by
  intro x y hxy
  apply encoding.encode_injective
  calc
    encoding.encode x =
        BaseGateProgram.applyLabel (BaseGateProgram.inverse program)
          (BaseGateProgram.applyLabel program (encoding.encode x)) := by
            symm
            exact
              BaseGateProgram.applyLabel_inverse_applyLabel program
                (encoding.encode x)
    _ =
        BaseGateProgram.applyLabel (BaseGateProgram.inverse program)
          (encoding.encode (step x)) := by
            rw [h.applyLabel_eq x]
    _ =
        BaseGateProgram.applyLabel (BaseGateProgram.inverse program)
          (encoding.encode (step y)) := by
            rw [hxy]
    _ =
        BaseGateProgram.applyLabel (BaseGateProgram.inverse program)
          (BaseGateProgram.applyLabel program (encoding.encode y)) := by
            rw [h.applyLabel_eq y]
    _ = encoding.encode y :=
        BaseGateProgram.applyLabel_inverse_applyLabel program
          (encoding.encode y)

/-- A concrete base-gate program realizes the semantic action induced by an
explicit equivalence-based register layout. -/
theorem ofEquivProgram {Data : Type} {n : Nat}
    (layout : Data ≃ Fin (2 ^ n)) (program : BaseGateProgram n) :
    Realizes (BinaryLabelEncoding.ofEquiv layout) program
      (fun x : Data => layout.symm (BaseGateProgram.applyLabel program (layout x))) where
  applyLabel_eq := by
    intro x
    simp [BinaryLabelEncoding.ofEquiv]

/-- A concrete base-gate program realizes its raw basis-label action under the
identity label encoding. -/
theorem finIdentityProgram {n : Nat} (program : BaseGateProgram n) :
    Realizes (BinaryLabelEncoding.finIdentity n) program
      (BaseGateProgram.applyLabel program) where
  applyLabel_eq := by
    intro x
    rfl

end Realizes

/-- Encoded-basis correctness for a realized base-gate program. -/
theorem toCircuit_apply_encoded_ket {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    {program : BaseGateProgram encoding.width} {step : Data -> Data}
    (h : Realizes encoding program step) (x : Data) :
    Circuit.apply (BaseGateProgram.toCircuit program).circuit
        ((PureState.ket (R := Qubits encoding.width) (encoding.encode x) :
          PureState (Qubits encoding.width)) :
          StateVector (Qubits encoding.width)) =
      (PureState.ket (R := Qubits encoding.width) (encoding.encode (step x)) :
        StateVector (Qubits encoding.width)) := by
  rw [BaseGateProgram.toCircuit_apply_ket]
  rw [h.applyLabel_eq x]

end BaseGateProgram

/-- A same-Circuit witness for a semantic update, carried by one folded
Toffoli/CNOT/X base-gate program. -/
structure BaseGateSameCircuitWitness (Data : Type) (step : Data -> Data) where
  /-- Encoding from semantic labels into binary basis labels. -/
  encoding : BinaryLabelEncoding Data
  /-- Wire-addressed base-gate program. -/
  program : BaseGateProgram encoding.width
  /-- Proof that the program implements the semantic update on encoded labels. -/
  realizes : BaseGateProgram.Realizes encoding program step

namespace BaseGateSameCircuitWitness

variable {Data : Type} {step : Data -> Data}

/-- Empty same-Circuit witness for the identity semantic update under a fixed
encoding. -/
def identity (encoding : BinaryLabelEncoding Data) :
    BaseGateSameCircuitWitness Data id where
  encoding := encoding
  program := []
  realizes := BaseGateProgram.Realizes.id encoding

/-- Bundle the sequential composition of two programs that have already been
proved under the same explicit encoding.  The bundled circuit and resource
profile are obtained by folding the appended base-gate program, so correctness
and accounting remain tied to the same wire-addressed object. -/
def sequentialOfPrograms (encoding : BinaryLabelEncoding Data)
    {first second : BaseGateProgram encoding.width}
    {firstStep secondStep : Data -> Data}
    (hfirst : BaseGateProgram.Realizes encoding first firstStep)
    (hsecond : BaseGateProgram.Realizes encoding second secondStep) :
    BaseGateSameCircuitWitness Data (fun x => secondStep (firstStep x)) where
  encoding := encoding
  program := BaseGateProgram.append first second
  realizes := BaseGateProgram.Realizes.append hfirst hsecond

/-- Bundle the sequential composition of a list of programs already proved
under the same explicit encoding. -/
def sequentialListOfPrograms (encoding : BinaryLabelEncoding Data)
    (programs : List (BaseGateProgram encoding.width))
    (steps : List (Data -> Data))
    (h :
      List.Forall₂ (fun program step =>
        BaseGateProgram.Realizes encoding program step) programs steps) :
    BaseGateSameCircuitWitness Data
      (BaseGateProgram.Realizes.stepList steps) where
  encoding := encoding
  program := BaseGateProgram.appendList programs
  realizes := BaseGateProgram.Realizes.appendList encoding programs steps h

/-- Reverse a same-Circuit witness when the semantic update has a right
inverse.  Since every accepted base-gate atom is self-inverse, reversing the
same folded program implements the inverse semantic update. -/
def inverse (w : BaseGateSameCircuitWitness Data step)
    {stepInv : Data -> Data} (hright : ∀ x : Data, step (stepInv x) = x) :
    BaseGateSameCircuitWitness Data stepInv where
  encoding := w.encoding
  program := BaseGateProgram.inverse w.program
  realizes := BaseGateProgram.Realizes.inverse_of_rightInverse w.realizes hright

/-- Relabel a same-Circuit witness along an equivalence of semantic label
types, reusing exactly the same wire-addressed program. -/
def relabel {Other : Type} (w : BaseGateSameCircuitWitness Data step)
    (layout : Other ≃ Data) :
    BaseGateSameCircuitWitness Other (fun x => layout.symm (step (layout x))) where
  encoding := w.encoding.relabel layout
  program := w.program
  realizes := by
    exact
      { applyLabel_eq := by
          intro x
          simpa [BinaryLabelEncoding.relabel] using w.realizes.applyLabel_eq (layout x) }

/-- Restate a same-Circuit witness under a pointwise equal semantic step,
without changing the encoding or wire-addressed program. -/
def congrStep (w : BaseGateSameCircuitWitness Data step)
    {step' : Data -> Data} (hstep : ∀ x : Data, step x = step' x) :
    BaseGateSameCircuitWitness Data step' where
  encoding := w.encoding
  program := w.program
  realizes := by
    exact
      { applyLabel_eq := by
          intro x
          rw [w.realizes.applyLabel_eq x, hstep x] }

/-- Build a same-Circuit witness from a concrete base-gate program and an
explicit equivalence-based register layout. -/
def ofEquivProgram {Data : Type} {n : Nat}
    (layout : Data ≃ Fin (2 ^ n)) (program : BaseGateProgram n) :
    BaseGateSameCircuitWitness Data
      (fun x : Data => layout.symm (BaseGateProgram.applyLabel program (layout x))) where
  encoding := BinaryLabelEncoding.ofEquiv layout
  program := program
  realizes := BaseGateProgram.Realizes.ofEquivProgram layout program

/-- Build a same-Circuit witness for a raw basis-label program under the
identity encoding. -/
def finIdentityProgram {n : Nat} (program : BaseGateProgram n) :
    BaseGateSameCircuitWitness (Fin (2 ^ n)) (BaseGateProgram.applyLabel program) where
  encoding := BinaryLabelEncoding.finIdentity n
  program := program
  realizes := BaseGateProgram.Realizes.finIdentityProgram program

/-- Bundled base-gate circuit obtained by folding the witness program. -/
def baseCircuit (w : BaseGateSameCircuitWitness Data step) :
    BaseGateCircuit (Qubits w.encoding.width) :=
  BaseGateProgram.toCircuit w.program

/-- The typed circuit shared by correctness and resource accounting. -/
def circuit (w : BaseGateSameCircuitWitness Data step) : Circuit (Qubits w.encoding.width) :=
  w.baseCircuit.circuit

/-- Resource profile projected from the same folded program. -/
def profile (w : BaseGateSameCircuitWitness Data step) :
    ModularArithmeticResourceProfile :=
  w.baseCircuit.profile

/-- The folded circuit history contains only X/CNOT/Toffoli leaves. -/
theorem structured (w : BaseGateSameCircuitWitness Data step) :
    w.circuit.history.IsBaseGateStructured :=
  w.baseCircuit.structured

/-- Encoded-basis correctness for the witness circuit. -/
theorem apply_encoded_ket (w : BaseGateSameCircuitWitness Data step) (x : Data) :
    Circuit.apply w.circuit
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode (step x)) :
        StateVector (Qubits w.encoding.width)) :=
  BaseGateProgram.toCircuit_apply_encoded_ket w.realizes x

/-- Resource counters are projected from the same folded program. -/
theorem resources_eq (w : BaseGateSameCircuitWitness Data step) :
    w.circuit.resources = w.profile.toResourceProfile :=
  w.baseCircuit.resources_eq

/-- Circuit depth is projected from the same folded program. -/
theorem depth_eq (w : BaseGateSameCircuitWitness Data step) :
    w.circuit.depth = w.profile.circuitDepth :=
  w.baseCircuit.depth_eq

/-- Query depth is projected from the same folded program. -/
theorem queryDepth_eq (w : BaseGateSameCircuitWitness Data step) :
    w.circuit.queryDepth = w.profile.oracleQueries :=
  w.baseCircuit.queryDepth_eq

/-- Resource-correct witness for an encoded same-Circuit realization. -/
def resourceCorrectWitness (w : BaseGateSameCircuitWitness Data step) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ x : Data,
        Circuit.apply w.circuit
          ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (step x)) :
            StateVector (Qubits w.encoding.width)))
      (w.circuit.resources = w.profile.toResourceProfile ∧
        w.circuit.depth = w.profile.circuitDepth ∧
        w.circuit.queryDepth = w.profile.oracleQueries) where
  circuit := w.circuit
  correctness := w.apply_encoded_ket
  resources := ⟨w.resources_eq, w.depth_eq, w.queryDepth_eq⟩

end BaseGateSameCircuitWitness

end

end QuantumAlg
