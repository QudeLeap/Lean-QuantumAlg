/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.BinaryLabelEncoding
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

/-- Compose two exact normalized-state endpoints through a sequential
circuit without requiring clients to rewrite inside a specialized register
type. -/
theorem applyNormalized_seq_of_eq {R : Register}
    {first second : UnitaryCircuit R} {input middle output : NormalizedVector R}
    (hfirst : first.applyNormalized input = middle)
    (hsecond : second.applyNormalized middle = output) :
    (UnitaryCircuit.seq first second).applyNormalized input = output := by
  rw [UnitaryCircuit.applyNormalized_seq, hfirst]
  exact hsecond

/-- An actual circuit realizes one semantic update under a faithful binary
encoding.  The obligation observes the circuit's real unitary action rather
than any resource label attached to its leaves. -/
structure Realizes {Data : Type} (encoding : BinaryLabelEncoding Data)
    (circuit : UnitaryCircuit (Qubits encoding.width)) (step : Data → Data) : Prop where
  /-- Actual circuit action agrees with the encoded semantic update. -/
  apply_encoded_ket :
    ∀ x, circuit.applyNormalized (NormalizedVector.ket (encoding.encode x)) =
      NormalizedVector.ket (encoding.encode (step x))

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

/-- An actual identity circuit realizes the identity update regardless of the
duplicate-free physical footprint recorded for layout accounting. -/
theorem identityAt {Data : Type} (encoding : BinaryLabelEncoding Data)
    (physicalIdx : List Nat) (hnodup : physicalIdx.Nodup) :
    Realizes encoding
      (UnitaryCircuit.identity (Qubits encoding.width) physicalIdx hnodup)
      _root_.id where
  apply_encoded_ket := by
    intro x
    apply NormalizedVector.ext
    intro i
    change (1 : UnitaryOperator (Qubits encoding.width)).applyVec
        ((NormalizedVector.ket (R := Qubits encoding.width)
          (encoding.encode x) : NormalizedVector (Qubits encoding.width)) :
            HilbertVector (Qubits encoding.width)) i = _
    rw [UnitaryOperator.one_applyVec]
    rfl

/-- The empty actual circuit realizes the identity update. -/
theorem identity {Data : Type} (encoding : BinaryLabelEncoding Data) :
    Realizes encoding (UnitaryCircuit.identity (Qubits encoding.width) [] (by simp))
      _root_.id :=
  identityAt encoding [] (by simp)

/-- Sequential composition preserves direct semantic realization. -/
theorem seq {Data : Type} {encoding : BinaryLabelEncoding Data}
    {first second : UnitaryCircuit (Qubits encoding.width)}
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
theorem appendList {Data : Type} (encoding : BinaryLabelEncoding Data) :
    ∀ (circuits : List (UnitaryCircuit (Qubits encoding.width)))
      (steps : List (Data → Data)),
      List.Forall₂ (fun circuit step => Realizes encoding circuit step)
        circuits steps →
      Realizes encoding
        (circuits.foldr UnitaryCircuit.seq
          (UnitaryCircuit.identity (Qubits encoding.width) [] (by simp)))
        (stepList steps)
  | [], [], _ => by
      simpa [stepList] using identity encoding
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | circuit :: circuits, step :: steps, h => by
      cases h with
      | cons hhead htail =>
          simpa [stepList] using
            seq hhead (appendList encoding circuits steps htail)

/-- Pointwise-equal semantic updates may share the same actual realization
proof without changing the circuit or its resource provenance. -/
theorem congrStep {Data : Type} {encoding : BinaryLabelEncoding Data}
    {circuit : UnitaryCircuit (Qubits encoding.width)} {first second : Data → Data}
    (h : Realizes encoding circuit first)
    (hstep : ∀ x, first x = second x) :
    Realizes encoding circuit second where
  apply_encoded_ket := by
    intro x
    rw [← hstep x]
    exact h.apply_encoded_ket x

/-- Applying a circuit adjoint after that circuit restores every normalized
state. -/
theorem dagger_applyNormalized_applyNormalized {R : Register}
    (circuit : UnitaryCircuit R) (state : NormalizedVector R) :
    circuit.dagger.applyNormalized (circuit.applyNormalized state) = state := by
  apply NormalizedVector.ext
  intro i
  change (circuit.matrix⁻¹).applyVec (circuit.matrix.applyVec state) i = _
  rw [← UnitaryOperator.mul_applyVec, inv_mul_cancel,
    UnitaryOperator.one_applyVec]

/-- The adjoint realizes a supplied semantic right inverse. -/
theorem dagger_of_rightInverse {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    {circuit : UnitaryCircuit (Qubits encoding.width)} {step stepInv : Data → Data}
    (h : Realizes encoding circuit step)
    (hright : ∀ x, step (stepInv x) = x) :
    Realizes encoding circuit.dagger stepInv where
  apply_encoded_ket := by
    intro x
    have hforward := h.apply_encoded_ket (stepInv x)
    rw [hright x] at hforward
    rw [← hforward]
    exact dagger_applyNormalized_applyNormalized circuit
      (NormalizedVector.ket (encoding.encode (stepInv x)))

/-- Every semantic update realized by an actual unitary circuit is injective. -/
theorem injective {Data : Type} {encoding : BinaryLabelEncoding Data}
    {circuit : UnitaryCircuit (Qubits encoding.width)} {step : Data → Data}
    (h : Realizes encoding circuit step) : Function.Injective step := by
  intro x y hxy
  have hket :
      NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode x) =
        NormalizedVector.ket (encoding.encode y) := by
    calc
      NormalizedVector.ket (encoding.encode x) =
          circuit.dagger.applyNormalized
            (circuit.applyNormalized
              (NormalizedVector.ket (encoding.encode x))) :=
        (dagger_applyNormalized_applyNormalized circuit _).symm
      _ = circuit.dagger.applyNormalized
            (NormalizedVector.ket (encoding.encode (step x))) := by
        rw [h.apply_encoded_ket]
      _ = circuit.dagger.applyNormalized
            (NormalizedVector.ket (encoding.encode (step y))) := by
        rw [hxy]
      _ = circuit.dagger.applyNormalized
            (circuit.applyNormalized
              (NormalizedVector.ket (encoding.encode y))) := by
        rw [h.apply_encoded_ket]
      _ = NormalizedVector.ket (encoding.encode y) :=
        dagger_applyNormalized_applyNormalized circuit _
  exact encoding.encode_injective (NormalizedVector.ket_injective hket)

end Realizes

end UnitaryCircuit

end

end QuantumAlg

end
