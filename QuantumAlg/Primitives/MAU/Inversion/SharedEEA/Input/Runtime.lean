/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Input.Runtime.Placement
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Execute fixed shared-EEA input loading and native preprocessing

The source's fixed auxiliary bits are loaded with actual X gates after zero
allocation. The native fold and length writer then run at the identical
physical identities in the live context [LYL+26, sec_EEA/sub_4phase.tex:104-117].
The complete quantum/reference matrix retains the real preparation and
unitary conjugations [dW19, qcnotes.tex:5381,5405,8071].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InputRuntime

noncomputable section

open Execution InputPreparation

/-- Native preprocessing placed at its exact live physical identities. -/
def program (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (after modulus.size).quantumLayout :=
  InputRuntimePlacement.program modulus.size (InitialFrame.program modulus)

/-- The post-preprocessing runtime basis matches the actual native full-frame result. -/
def outputBasis (modulus : Nat) (old : (before modulus.size).register.Index) :
    (after modulus.size).register.Index :=
  (InputAssembly.basisEquiv modulus.size).symm
    ((encoding modulus.size).encode
      (InitialFrame.result modulus (inputBasisEquiv modulus.size old)))

/-- Actual preparation followed by the placed native word has the exact source-result action. -/
theorem program_prepared_input (modulus : Nat)
    (old : (before modulus.size).register.Index) :
    (program modulus).applyNormalized
        (NormalizedVector.ket
          (InputAssembly.assembly modulus.size ((preparation modulus).value, old))) =
      NormalizedVector.ket (outputBasis modulus old) := by
  have actual := InitialFrame.program_initial modulus (inputBasisEquiv modulus.size old)
  apply InputRuntimePlacement.program_apply_ket modulus.size
    (InitialFrame.program modulus) _ _ actual
  · rw [InputRuntimePlacement.selectedBasis_eq_basisEquiv]
    exact congrArg (QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
      (InputPreparedFrame.basisEquiv_prepared_initial modulus old)
  · rw [InputRuntimePlacement.selectedBasis_eq_basisEquiv, outputBasis]
    exact congrArg (QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
      ((InputAssembly.basisEquiv modulus.size).apply_symm_apply _)

/-- One selected-model unitary instruction runs native preprocessing. -/
def body (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (after modulus.size) (after modulus.size) :=
  .unitary (program modulus)

/-- Load the fixed seed, fold the input, and write the resulting divisor length. -/
def code (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size) (after modulus.size) :=
  (InputPreparation.circuit modulus).seq (body modulus)

theorem program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace = (InitialFrame.program modulus).eventTrace :=
  InputRuntimePlacement.program_eventTrace modulus.size (InitialFrame.program modulus)

/-- The physical runtime placement retains every actual native event multiplicity. -/
theorem program_eventCost (modulus : Nat) :
    (program modulus).eventCost = (InitialFrame.program modulus).eventCost :=
  InputRuntimePlacement.program_eventCost modulus.size (InitialFrame.program modulus)

/-- The trace charges zero allocation, fixed-seed X gates, fold and length writing. -/
theorem code_eventTrace (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).eventTrace path =
      (ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (auxiliaryLayout modulus.size) ++ (loadProgram modulus).eventTrace) ++
      ((FoldSourceProgram.program modulus).eventTrace ++
        (InitialLengthWrite.program modulus.size).eventTrace) := by
  change (InputPreparation.circuit modulus).eventTrace path.1 ++
    (program modulus).eventTrace = _
  rw [InputPreparation.circuit_eventTrace, program_eventTrace,
    InitialFrame.program_eventTrace]

variable {Reference : Register} {H : Type} [Fintype H]

/-- Every classical/hidden-state block evolves under the same joint operator. -/
theorem body_block_matrix (modulus : Nat)
    (state : State (after modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (store : Store (after modulus.size))
    (hidden : ClassicalOracleModel.empty.HiddenState) (history : H) :
    (((body modulus).execute Reference state).block
      (store, (hidden, (history, ())))).matrix =
      let operator := UnitaryOperator.prodTensor (program modulus).matrix
        (1 : UnitaryOperator Reference)
      (operator : HilbertOperator ((after modulus.size).register.prod Reference)) *
        (state.block (store, (hidden, history))).matrix *
          (operator : HilbertOperator
            ((after modulus.size).register.prod Reference)).conjTranspose :=
  Circuit.execute_unitary_block_matrix state (program modulus) store hidden history

/-- The full input/reference density includes both actual execution stages. -/
theorem code_quantumMarginal (modulus : Nat)
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((code modulus).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program modulus).matrix
          (1 : UnitaryOperator Reference))
        (((InputPreparation.circuit modulus).execute Reference state).quantumMarginal) := by
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal, body,
    Circuit.unitary_jointDensity]

/-- Both execution stages preserve the complete external-reference matrix. -/
theorem code_reference_entry (modulus : Nat)
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (left right : Reference.Index) :
    (∑ basis : (after modulus.size).register.Index,
      ((code modulus).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before modulus.size).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) := by
  rw [code_quantumMarginal]
  exact (DensityOperator.localUnitary_reference_entry (program modulus).matrix
    (((InputPreparation.circuit modulus).execute Reference state).quantumMarginal)
      left right).trans (InputPreparation.execute_reference_entry modulus state left right)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InputRuntime
