/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Product
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Product
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Linear vector action of the actual model-indexed circuit

These equations project the circuit's own matrix. They neither replace its
native word nor grant access to an undeclared inverse or oracle.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
  {count width : Nat} {layout : QuantumLayout count}

/-- The zero-event circuit fixes every raw vector in the physical register basis. -/
public theorem applyVec_identity (vector : HilbertVector layout.register) :
    (identity gates oracles layout).applyVec vector = vector := by
  unfold applyVec
  rw [identity_matrix, UnitaryOperator.one_applyVec]

/-- Sequential physical-register vector action follows circuit execution order. -/
public theorem applyVec_seq (first second : UnitaryCircuit gates oracles layout)
    (vector : HilbertVector layout.register) :
    (first.seq second).applyVec vector = second.applyVec (first.applyVec vector) :=
  UnitaryOperator.mul_applyVec second.matrix first.matrix vector

/-- The physical-register operator preserves addition. -/
public theorem applyVec_add (circuit : UnitaryCircuit gates oracles layout)
    (left right : HilbertVector layout.register) :
    circuit.applyVec (left + right) = circuit.applyVec left + circuit.applyVec right :=
  UnitaryOperator.applyVec_add circuit.matrix left right

/-- The physical-register operator preserves scalar multiplication. -/
public theorem applyVec_smul (circuit : UnitaryCircuit gates oracles layout)
    (scalar : ℂ) (vector : HilbertVector layout.register) :
    circuit.applyVec (scalar • vector) = scalar • circuit.applyVec vector :=
  UnitaryOperator.applyVec_smul circuit.matrix scalar vector

/-- Apply the actual canonical-qubit circuit in its big-endian integer basis. -/
public abbrev applyBinaryVec
    (circuit : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (vector : HilbertVector (Qubits width)) : HilbertVector (Qubits width) :=
  circuit.binaryMatrix.applyVec vector

/-- The zero-event circuit fixes every raw vector. -/
public theorem applyBinaryVec_identity (vector : HilbertVector (Qubits width)) :
    (identity gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout).applyBinaryVec
        vector = vector := by
  unfold applyBinaryVec
  rw [unitaryCircuit_binaryMatrix_identity, UnitaryOperator.one_applyVec]

/-- Sequential vector action follows the same execution order as normalized states. -/
public theorem applyBinaryVec_seq
    (first second : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (vector : HilbertVector (Qubits width)) :
    (first.seq second).applyBinaryVec vector =
      second.applyBinaryVec (first.applyBinaryVec vector) := by
  unfold applyBinaryVec
  rw [unitaryCircuit_binaryMatrix_seq, UnitaryOperator.mul_applyVec]

/-- The actual operator preserves addition on the complete ambient vector. -/
public theorem applyBinaryVec_add
    (circuit : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (left right : HilbertVector (Qubits width)) :
    circuit.applyBinaryVec (left + right) =
      circuit.applyBinaryVec left + circuit.applyBinaryVec right := by
  unfold applyBinaryVec
  exact
  UnitaryOperator.applyVec_add circuit.binaryMatrix left right

/-- Scalar multiplication retains exact phase in the full ambient state. -/
public theorem applyBinaryVec_smul
    (circuit : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (scalar : ℂ) (vector : HilbertVector (Qubits width)) :
    circuit.applyBinaryVec (scalar • vector) =
      scalar • circuit.applyBinaryVec vector := by
  unfold applyBinaryVec
  exact
  UnitaryOperator.applyVec_smul circuit.binaryMatrix scalar vector

/-- An indexed product acts in increasing index order after its stored
initial circuit. -/
public theorem applyBinaryVec_indexedProduct (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (step : Fin steps → UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (vector : HilbertVector (Qubits width)) :
    (indexedProduct label steps start step).applyBinaryVec vector =
      (List.ofFn step).foldl
        (fun accumulated next => next.applyBinaryVec accumulated)
        (start.applyBinaryVec vector) := by
  unfold applyBinaryVec
  have foldAction : ∀ (circuits : List (UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout))
      (initial : UnitaryOperator (Qubits width)),
      ((circuits.map fun circuit => circuit.binaryMatrix).foldl
          (fun accumulated next => next * accumulated) initial).applyVec vector =
        circuits.foldl
          (fun accumulated next => next.binaryMatrix.applyVec accumulated)
          (initial.applyVec vector) := by
    intro circuits initial
    induction circuits generalizing initial with
    | nil => rfl
    | cons circuit rest induction =>
        simp only [List.map_cons, List.foldl_cons]
        rw [induction, UnitaryOperator.mul_applyVec]
  rw [unitaryCircuit_binaryMatrix_indexedProduct]
  have matrixList :
      List.ofFn (fun index : Fin steps => (step index).binaryMatrix) =
        (List.ofFn step).map fun circuit => circuit.binaryMatrix :=
    List.ofFn_comp' step fun circuit => circuit.binaryMatrix
  rw [matrixList]
  exact foldAction (List.ofFn step) start.binaryMatrix

/-- An indexed product fixes a raw vector when its start and every indexed
member fix that vector. -/
public theorem applyBinaryVec_indexedProduct_eq_self_of_each
    (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (step : Fin steps → UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (vector : HilbertVector (Qubits width))
    (startFixes : start.applyBinaryVec vector = vector)
    (eachFixes : ∀ index, (step index).applyBinaryVec vector = vector) :
    (indexedProduct label steps start step).applyBinaryVec vector = vector := by
  rw [applyBinaryVec_indexedProduct, startFixes]
  have foldFixes : ∀ circuits : List (UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout),
      (∀ circuit ∈ circuits, circuit.applyBinaryVec vector = vector) →
        circuits.foldl
          (fun accumulated circuit => circuit.applyBinaryVec accumulated)
          vector = vector := by
    intro circuits
    induction circuits with
    | nil => simp
    | cons circuit circuits induction =>
        intro fixes
        rw [List.foldl_cons, fixes circuit (by simp)]
        apply induction
        intro later member
        exact fixes later (by simp [member])
  apply foldFixes (List.ofFn step)
  intro circuit member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact eachFixes index

end

end QuantumAlg.UnitaryCircuit
