/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Semantic realization by actual circuits

This module states encoded computational-basis behavior directly about a Core
`UnitaryCircuit`.  `UnitaryCircuit.Realizes` is proof-only: it neither wraps a circuit nor
classifies the leaves of arbitrary circuits as belonging to a gate language.
-/

section

namespace QuantumAlg

noncomputable section

namespace UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel}

/-- Compose two exact normalized-state endpoints through a sequential
circuit without requiring clients to rewrite inside a specialized register
type. -/
theorem applyNormalized_seq_of_eq {count : Nat} {layout : QuantumLayout count}
    {first second : UnitaryCircuit gates oracles layout}
    {input middle output : NormalizedVector layout.register}
    (hfirst : first.applyNormalized input = middle)
    (hsecond : second.applyNormalized middle = output) :
    (UnitaryCircuit.seq first second).applyNormalized input = output := by
  rw [UnitaryCircuit.applyNormalized_seq, hfirst]
  exact hsecond

/-- An actual circuit realizes one semantic update under a faithful binary
encoding.  The obligation observes the circuit's real unitary action rather
than any resource label attached to its leaves. -/
structure Realizes {Data : Type} (encoding : BinaryLabelEncoding Data)
    {layout : QubitLayout encoding.width}
    (circuit : UnitaryCircuit gates oracles layout.toQuantum) (step : Data → Data) : Prop where
  /-- Actual circuit action agrees with the encoded semantic update. -/
  apply_encoded_ket :
    ∀ x, circuit.applyNormalized
      (NormalizedVector.ket (layout.basisEquiv.symm (encoding.encode x))) =
      NormalizedVector.ket (layout.basisEquiv.symm (encoding.encode (step x)))

namespace Realizes

/-- Compose semantic updates in list execution order. -/
def stepList {Data : Type} : List (Data → Data) → Data → Data
  | [] => _root_.id
  | step :: rest => fun x => stepList rest (step x)

/-- Splitting a semantic schedule at list append preserves execution order. -/
theorem stepList_append {Data : Type} (first second : List (Data → Data))
    (x : Data) :
    stepList (first ++ second) x = stepList second (stepList first x) := by
  induction first generalizing x with
  | nil => rfl
  | cons step rest ih =>
      simpa [stepList] using ih (step x)

/-- A prefix extended by its next in-bounds step executes that step last. -/
theorem stepList_take_succ {Data : Type} (steps : List (Data → Data))
    (index : Nat) (hindex : index < steps.length) (x : Data) :
    stepList (steps.take (index + 1)) x =
      steps.get ⟨index, hindex⟩ (stepList (steps.take index) x) := by
  rw [← List.take_concat_get' steps index hindex, stepList_append]
  rfl

/-- Identity executes on exactly the addressed qubits of the encoding. -/
theorem identityAt (gates : GateModel) (oracles : OracleModel) {Data : Type}
    (encoding : BinaryLabelEncoding Data) (layout : QubitLayout encoding.width) :
    Realizes encoding (UnitaryCircuit.identity gates oracles layout.toQuantum) _root_.id where
  apply_encoded_ket := by
    intro x
    apply NormalizedVector.ext
    intro i
    change (1 : UnitaryOperator layout.toQuantum.register).applyVec
      (NormalizedVector.ket (layout.basisEquiv.symm (encoding.encode x))) i = _
    rw [UnitaryOperator.one_applyVec]
    rfl

/-- The zero-event identity retains the full canonical physical word, including width zero. -/
theorem identity (gates : GateModel) (oracles : OracleModel) {Data : Type}
    (encoding : BinaryLabelEncoding Data) :
    Realizes encoding (UnitaryCircuit.identity gates oracles
      (QubitLayout.toQuantum ⟨Fin.val, Fin.val_injective⟩)) _root_.id :=
  identityAt gates oracles encoding ⟨Fin.val, Fin.val_injective⟩

/-- Sequential composition preserves direct semantic realization. -/
theorem seq {Data : Type} {encoding : BinaryLabelEncoding Data}
    {layout : QubitLayout encoding.width}
    {first second : UnitaryCircuit gates oracles layout.toQuantum}
    {firstStep secondStep : Data → Data}
    (hfirst : Realizes encoding first firstStep)
    (hsecond : Realizes encoding second secondStep) :
    Realizes encoding (UnitaryCircuit.seq first second)
      (fun x => secondStep (firstStep x)) where
  apply_encoded_ket := by
    intro x
    rw [UnitaryCircuit.applyNormalized_seq, hfirst.apply_encoded_ket,
      hsecond.apply_encoded_ket]

/-- Right-folded list composition preserves direct semantic realization. -/
theorem appendList {Data : Type} (encoding : BinaryLabelEncoding Data)
    (layout : QubitLayout encoding.width) :
    ∀ (circuits : List (UnitaryCircuit gates oracles layout.toQuantum))
      (steps : List (Data → Data)),
      List.Forall₂ (fun circuit step => Realizes encoding circuit step)
        circuits steps →
      Realizes encoding
        (circuits.foldr UnitaryCircuit.seq
          (UnitaryCircuit.identity gates oracles layout.toQuantum))
        (stepList steps)
  | [], [], _ => by
      simpa [stepList] using identityAt gates oracles encoding layout
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | circuit :: circuits, step :: steps, h => by
      cases h with
      | cons hhead htail =>
          simpa [stepList] using
            seq hhead (appendList encoding layout circuits steps htail)

/-- Pointwise-equal semantic updates may share the same actual realization
proof without changing the circuit or its resource provenance. -/
theorem congrStep {Data : Type} {encoding : BinaryLabelEncoding Data}
    {layout : QubitLayout encoding.width}
    {circuit : UnitaryCircuit gates oracles layout.toQuantum} {first second : Data → Data}
    (h : Realizes encoding circuit first)
    (hstep : ∀ x, first x = second x) :
    Realizes encoding circuit second where
  apply_encoded_ket := by
    intro x
    rw [← hstep x]
    exact h.apply_encoded_ket x

private theorem operator_cancel {R : Register} (operator : UnitaryOperator R)
    (state : NormalizedVector R) : (operator⁻¹).apply (operator.apply state) = state := by
  apply NormalizedVector.ext
  intro i
  change (operator⁻¹).applyVec (operator.applyVec state) i = _
  rw [← UnitaryOperator.mul_applyVec, inv_mul_cancel, UnitaryOperator.one_applyVec]

/-- An actual implementation of the inverse restores every normalized state. -/
theorem dagger_applyNormalized_applyNormalized {count : Nat} {layout : QuantumLayout count}
    (circuit inverse : UnitaryCircuit gates oracles layout)
    (inverse_eq : inverse.matrix = circuit.matrix⁻¹) (state : NormalizedVector layout.register) :
    inverse.applyNormalized (circuit.applyNormalized state) = state := by
  change inverse.matrix.apply (circuit.matrix.apply state) = state
  rw [inverse_eq]
  exact operator_cancel circuit.matrix state

/-- An available circuit implementing the inverse realizes the semantic right inverse. -/
theorem dagger_of_rightInverse {Data : Type} {encoding : BinaryLabelEncoding Data}
    {layout : QubitLayout encoding.width}
    {circuit inverse : UnitaryCircuit gates oracles layout.toQuantum} {step stepInv : Data → Data}
    (h : Realizes encoding circuit step) (inverse_eq : inverse.matrix = circuit.matrix⁻¹)
    (hright : ∀ x, step (stepInv x) = x) :
    Realizes encoding inverse stepInv where
  apply_encoded_ket := by
    intro x
    have hforward := h.apply_encoded_ket (stepInv x)
    rw [hright x] at hforward
    rw [← hforward]
    exact dagger_applyNormalized_applyNormalized circuit inverse inverse_eq _

/-- Every semantic update realized by an actual unitary circuit is injective. -/
theorem injective {Data : Type} {encoding : BinaryLabelEncoding Data}
    {layout : QubitLayout encoding.width}
    {circuit : UnitaryCircuit gates oracles layout.toQuantum} {step : Data → Data}
    (h : Realizes encoding circuit step) : Function.Injective step := by
  intro x y hxy
  have images : circuit.applyNormalized
      (NormalizedVector.ket (layout.basisEquiv.symm (encoding.encode x))) =
      circuit.applyNormalized
        (NormalizedVector.ket (layout.basisEquiv.symm (encoding.encode y))) := by
    rw [h.apply_encoded_ket, h.apply_encoded_ket, hxy]
  have restored := congrArg (fun state => (circuit.matrix⁻¹).apply state) images
  change (circuit.matrix⁻¹).apply (circuit.matrix.apply _) =
    (circuit.matrix⁻¹).apply (circuit.matrix.apply _) at restored
  rw [operator_cancel, operator_cancel] at restored
  exact encoding.encode_injective
    (layout.basisEquiv.symm.injective (NormalizedVector.ket_injective restored))

end Realizes

end UnitaryCircuit

end

end QuantumAlg

end
