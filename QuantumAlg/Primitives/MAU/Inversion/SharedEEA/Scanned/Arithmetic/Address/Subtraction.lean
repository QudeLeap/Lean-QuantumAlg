/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Frame
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Actual inverse address arithmetic with the original separate conjunction

The adjoint of the emitted native address adder subtracts the complete
metadata operand. Its real padding, original payload and separate
conjunction retain their values, including on inactive finite labels.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Reverse exactly the actual placed native body and its parallel schedule. -/
def subtractProgram (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (program width positive field).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

/-- The inverse finite operand action retains the entire actual complementary frame. -/
def subtractStep (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field) :
    Data width → Data width :=
  ((placement width positive field).subsystem.full
    Addition.TTK.WordPlacement.source_onto (encoding_surjective width)).step
      (fun pair => (Addition.TTK.subtractionOutput pair.1, pair.2))

/-- The actual finite inverse cancels the native address addition on every label. -/
lemma step_subtractStep (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (state : Data width) :
    step width positive field (subtractStep width positive field state) = state := by
  unfold step Addition.TTK.WordPlacement.step subtractStep FullPlacement.step
  simp only [Equiv.apply_symm_apply, Addition.TTK.lowOutput_subtractionOutput,
    Prod.eta, Equiv.symm_apply_apply]

/-- The actual unitary adjoint implements the same full-frame inverse without padding premises. -/
lemma subtractProgram_realizes (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (subtractProgram width positive field) environment
      (subtractStep width positive field) := by
  apply UnitaryCircuit.Realizes.dagger_of_rightInverse
    (program_realizes width positive field environment)
  · rw [subtractProgram, UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]
    exact Unitary.star_eq_inv _
  · exact step_subtractStep width positive field

/-- Complete original payload, metadata, phase, Sign and arbitrary Iter survive subtraction. -/
lemma subtractStep_source (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) (state : Data width) :
    (subtractStep width positive field state).1 = state.1 := by
  have retained := step_source width positive field (subtractStep width positive field state)
  rw [step_subtractStep] at retained
  exact retained.symm

/-- Every prefix and the separate conjunction retain their original physical values. -/
lemma subtractStep_workspace (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) (state : Data width) :
    (subtractStep width positive field state).2.2 = state.2.2 := by
  have retained := step_workspace width positive field (subtractStep width positive field state)
  rw [step_subtractStep] at retained
  exact retained.symm

private lemma subtractStep_sourceValue (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) (state : Data width) :
    sourceValue width positive field (subtractStep width positive field state) =
      sourceValue width positive field state := by
  unfold sourceValue
  simp only [prefixBit_get, ArithmeticGeometry.fieldValue, subtractStep_source,
    congrArg Prod.fst (subtractStep_workspace width positive field state)]

/-- The actual address receives the full modular difference while conjunction stays separate. -/
lemma subtractStep_address (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) (state : Data width) :
    (subtractStep width positive field state).2.1 =
      state.2.1 - sourceValue width positive field state := by
  have addition := step_address width positive field (subtractStep width positive field state)
  rw [step_subtractStep, subtractStep_sourceValue] at addition
  apply BitVec.eq_sub_iff_add_eq.mpr
  rw [BitVec.add_comm]
  exact addition.symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
