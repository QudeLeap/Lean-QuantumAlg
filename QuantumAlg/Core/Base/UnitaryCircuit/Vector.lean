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
public lemma applyVec_identity (vector : HilbertVector layout.register) (environment :
  oracles.Interpretation) :
    ((identity gates oracles layout).applyVec environment) vector = vector := by
  unfold applyVec
  rw [identity_matrix, UnitaryOperator.one_applyVec]

/-- Sequential physical-register vector action follows circuit execution order. -/
public lemma applyVec_seq (first second : UnitaryCircuit gates oracles layout)
    (vector : HilbertVector layout.register) (environment : oracles.Interpretation) :
    ((first.seq second).applyVec environment) vector = (second.applyVec environment)
      ((first.applyVec environment) vector) :=
  UnitaryOperator.mul_applyVec (second.matrix environment) (first.matrix environment) vector

/-- The physical-register operator preserves addition. -/
public lemma applyVec_add (circuit : UnitaryCircuit gates oracles layout)
    (left right : HilbertVector layout.register) (environment : oracles.Interpretation) :
    (circuit.applyVec environment) (left + right) = (circuit.applyVec environment) left +
      (circuit.applyVec environment) right :=
  UnitaryOperator.applyVec_add (circuit.matrix environment) left right

/-- The physical-register operator preserves scalar multiplication. -/
public lemma applyVec_smul (circuit : UnitaryCircuit gates oracles layout)
    (scalar : ℂ) (vector : HilbertVector layout.register) (environment : oracles.Interpretation) :
    (circuit.applyVec environment) (scalar • vector) = scalar • (circuit.applyVec environment)
      vector :=
  UnitaryOperator.applyVec_smul (circuit.matrix environment) scalar vector

/-- Apply the actual canonical-qubit circuit in its big-endian integer basis. -/
public abbrev applyBinaryVec
    (circuit : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (environment : oracles.Interpretation)
    (vector : HilbertVector (Qubits width)) : HilbertVector (Qubits width) :=
  (circuit.binaryMatrix environment).applyVec vector

/-- The zero-event circuit fixes every raw vector. -/
public lemma applyBinaryVec_identity (vector : HilbertVector (Qubits width)) (environment :
  oracles.Interpretation) :
    ((identity gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout).applyBinaryVec environment)
        vector = vector := by
  unfold applyBinaryVec
  rw [unitaryCircuit_binaryMatrix_identity, UnitaryOperator.one_applyVec]

/-- Sequential vector action follows the same execution order as normalized states. -/
public lemma applyBinaryVec_seq
    (first second : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (vector : HilbertVector (Qubits width)) (environment : oracles.Interpretation) :
    ((first.seq second).applyBinaryVec environment) vector =
      (second.applyBinaryVec environment) ((first.applyBinaryVec environment) vector) := by
  unfold applyBinaryVec
  rw [unitaryCircuit_binaryMatrix_seq, UnitaryOperator.mul_applyVec]

/-- The actual operator preserves addition on the complete ambient vector. -/
public lemma applyBinaryVec_add
    (circuit : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (left right : HilbertVector (Qubits width)) (environment : oracles.Interpretation) :
    (circuit.applyBinaryVec environment) (left + right) =
      (circuit.applyBinaryVec environment) left + (circuit.applyBinaryVec environment) right := by
  unfold applyBinaryVec
  exact
  UnitaryOperator.applyVec_add (circuit.binaryMatrix environment) left right

/-- Scalar multiplication retains exact phase in the full ambient state. -/
public lemma applyBinaryVec_smul
    (circuit : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (scalar : ℂ) (vector : HilbertVector (Qubits width)) (environment : oracles.Interpretation) :
    (circuit.applyBinaryVec environment) (scalar • vector) =
      scalar • (circuit.applyBinaryVec environment) vector := by
  unfold applyBinaryVec
  exact
  UnitaryOperator.applyVec_smul (circuit.binaryMatrix environment) scalar vector

/-- An indexed product acts in increasing index order after its stored
initial circuit. -/
public lemma applyBinaryVec_indexedProduct (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (step : Fin steps → UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (vector : HilbertVector (Qubits width)) (environment : oracles.Interpretation) :
    ((indexedProduct label steps start step).applyBinaryVec environment) vector =
      (List.ofFn step).foldl
        (fun accumulated next => (next.applyBinaryVec environment) accumulated)
        ((start.applyBinaryVec environment) vector) := by
  unfold applyBinaryVec
  have foldAction : ∀ (circuits : List (UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout))
      (initial : UnitaryOperator (Qubits width)),
      ((circuits.map fun circuit => (circuit.binaryMatrix environment)).foldl
          (fun accumulated next => next * accumulated) initial).applyVec vector =
        circuits.foldl
          (fun accumulated next => (next.binaryMatrix environment).applyVec accumulated)
          (initial.applyVec vector) := by
    intro circuits initial
    induction circuits generalizing initial with
    | nil => rfl
    | cons circuit rest induction =>
        simp only [List.map_cons, List.foldl_cons]
        rw [induction, UnitaryOperator.mul_applyVec]
  rw [unitaryCircuit_binaryMatrix_indexedProduct]
  have matrixList :
      List.ofFn (fun index : Fin steps => ((step index).binaryMatrix environment)) =
        (List.ofFn step).map fun circuit => (circuit.binaryMatrix environment) :=
    List.ofFn_comp' step fun circuit => (circuit.binaryMatrix environment)
  rw [matrixList]
  exact foldAction (List.ofFn step) (start.binaryMatrix environment)

/-- An indexed product fixes a raw vector when its start and every indexed
member fix that vector. -/
public lemma applyBinaryVec_indexedProduct_eq_self_of_each
    (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (step : Fin steps → UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (vector : HilbertVector (Qubits width))
    (environment : oracles.Interpretation)
    (startFixes : (start.applyBinaryVec environment) vector = vector)
    (eachFixes : ∀ index, ((step index).applyBinaryVec environment) vector = vector) :
    ((indexedProduct label steps start step).applyBinaryVec environment) vector = vector := by
  rw [applyBinaryVec_indexedProduct, startFixes]
  have foldFixes : ∀ circuits : List (UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout),
      (∀ circuit ∈ circuits, (circuit.applyBinaryVec environment) vector = vector) →
        circuits.foldl
          (fun accumulated circuit => (circuit.applyBinaryVec environment) accumulated)
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
