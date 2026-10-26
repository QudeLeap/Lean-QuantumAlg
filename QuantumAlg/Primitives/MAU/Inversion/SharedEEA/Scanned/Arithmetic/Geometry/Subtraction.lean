/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Readout
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Actual full-carry metadata subtraction on the same pool

The inverse is the native adjoint of the actual placed unitary adder.
Its complete source registers and both padding bits remain present.
All finite labels, including dirty padding, satisfy the same modular
word equation [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Reverse the actual native arithmetic body, including its real parallel schedule. -/
def subtractProgram (width : Nat) (positive : 1 ≤ width) (field : Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (program width positive field).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

/-- The complete inverse word action retains its original physical complement. -/
def subtractStep (width : Nat) (positive : 1 ≤ width) (field : Field) : Data width → Data width :=
  ((placement width positive field).subsystem.full
    (Addition.TTK.WordPlacement.source_onto) (encoding_surjective width)).step
      (fun pair => (Addition.TTK.subtractionOutput pair.1, pair.2))

/-- The full original geometry addition cancels the native inverse on every finite label. -/
lemma step_subtractStep (width : Nat) (positive : 1 ≤ width) (field : Field)
    (state : Data width) :
    step width positive field (subtractStep width positive field state) = state := by
  unfold step Addition.TTK.WordPlacement.step subtractStep FullPlacement.step
  simp only [Equiv.apply_symm_apply, Addition.TTK.lowOutput_subtractionOutput,
    Prod.eta, Equiv.symm_apply_apply]

/-- The actual native inverse has the full coherent source action, with no clean-padding premise. -/
lemma subtractProgram_realizes (width : Nat) (positive : 1 ≤ width) (field : Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (subtractProgram width positive field) environment
      (subtractStep width positive field) := by
  apply UnitaryCircuit.Realizes.dagger_of_rightInverse
    (program_realizes width positive field environment)
  · rw [subtractProgram, UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]
    exact Unitary.star_eq_inv _
  · exact step_subtractStep width positive field

/-- Every original source register survives the actual native subtraction. -/
lemma subtractStep_source (width : Nat) (positive : 1 ≤ width) (field : Field)
    (state : Data width) :
    (subtractStep width positive field state).1 = state.1 := by
  have retained := step_source width positive field (subtractStep width positive field state)
  rw [step_subtractStep] at retained
  exact retained.symm

/-- The entire prefix, including both real high padding positions, survives subtraction. -/
lemma subtractStep_prefix (width : Nat) (positive : 1 ≤ width) (field : Field)
    (state : Data width) :
    (subtractStep width positive field state).2.2.1 = state.2.2.1 := by
  have retained := step_prefix width positive field (subtractStep width positive field state)
  rw [step_subtractStep] at retained
  exact retained.symm

private lemma subtractStep_sourceValue (width : Nat) (positive : 1 ≤ width) (field : Field)
    (state : Data width) :
    sourceValue width positive field (subtractStep width positive field state) =
      sourceValue width positive field state := by
  unfold sourceValue
  simp only [prefixBit_get, subtractStep_prefix, fieldValue, subtractStep_source]

/-- No high metadata carry is dropped from the actual modular difference. -/
lemma subtractStep_targetValue (width : Nat) (positive : 1 ≤ width) (field : Field)
    (state : Data width) :
    targetValue width (subtractStep width positive field state) =
      targetValue width state - sourceValue width positive field state := by
  have addition := step_targetValue width positive field
    (subtractStep width positive field state)
  rw [step_subtractStep, subtractStep_sourceValue] at addition
  apply BitVec.eq_sub_iff_add_eq.mpr
  rw [BitVec.add_comm]
  exact addition.symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
