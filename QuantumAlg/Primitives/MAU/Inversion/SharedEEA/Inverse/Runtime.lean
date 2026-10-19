/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Runtime.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Inverse.Gates
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Execute the complete native XOR inverse on its physically prepared frame

The fixed auxiliary bits are loaded with actual gates. The native forward,
actual XOR copy, and generated adjoint then run on the same physical systems
[LYL+26, sec_EEA/sub_4phase.tex:104-128]. The input and every prepared field
are restored; the arbitrary target receives the independent mathematical
inverse by XOR. The complete reference matrix is retained
[dW19, qcnotes.tex:5381,5405].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseRuntime

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

variable {runtimeEnvironment :
  (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution InversePreparation

/-- The actual native inverse, or the full-frame identity at modulus one. -/
def nativeProgram (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum :=
  if nontrivial : 1 < modulus then NativeInverse.nativeProgram modulus nontrivial
  else UnitaryCircuit.identity AlgorithmGate.model .empty
    (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum

/-- The complete native inverse on the exact live two-word runtime layout. -/
def program (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (after modulus.size).quantumLayout :=
  InverseRuntimeFrame.program modulus.size (nativeProgram modulus)

/-- The modulus-one branch fixes every complete prepared-frame basis label. -/
lemma program_trivial_ket (modulus : Nat) (trivial : ¬1 < modulus)
    (basis : (after modulus.size).register.Index) :
    (program modulus).applyNormalized environment (NormalizedVector.ket basis) =
      NormalizedVector.ket basis := by
  let native := UnitaryCircuit.identity AlgorithmGate.model .empty
    (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum
  let sourceBasis := (QubitLayout.canonical
    (OutputCopy.encoding modulus.size).width).basisEquiv.symm
      (InverseAssembly.basisEquiv modulus.size basis)
  have actual : native.applyNormalized environment (NormalizedVector.ket sourceBasis) =
      NormalizedVector.ket sourceBasis := by
    change (native.matrix environment).apply (NormalizedVector.ket sourceBasis) = _
    rw [UnitaryCircuit.identity_matrix, UnitaryOperator.one_apply]
  have selected : UnitaryCircuit.selectedInput
      (InverseRuntimeFrame.source modulus.size) (after modulus.size).quantumLayout
      (InverseRuntimeFrame.position modulus.size)
      (InverseRuntimeFrame.position_dimensions modulus.size) basis = sourceBasis :=
    InverseRuntimeFrame.selectedBasis_eq_basisEquiv modulus.size basis
  have placed := InverseRuntimeFrame.program_apply_ket modulus.size native
    sourceBasis sourceBasis actual basis basis selected selected
  simpa only [program, nativeProgram, dif_neg trivial, native] using placed

/-- Only the target word changes, by XOR with the mathematical modular inverse. -/
def outputOld (modulus : Nat) (old : (before modulus.size).register.Index)
    (positive : 0 < (inputBasisEquiv modulus.size old).1.val)
    (bounded : (inputBasisEquiv modulus.size old).1.val < modulus) :
    (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).symm
    ((inputBasisEquiv modulus.size old).1,
      NativeInverse.output modulus (inputBasisEquiv modulus.size old).1.val positive bounded
        (inputBasisEquiv modulus.size old).2)

/-- The native result retains the same actual prepared values and original input. -/
def outputBasis (modulus : Nat) (old : (before modulus.size).register.Index)
    (positive : 0 < (inputBasisEquiv modulus.size old).1.val)
    (bounded : (inputBasisEquiv modulus.size old).1.val < modulus) :
    (after modulus.size).register.Index :=
  InversePreparation.assembly modulus.size ((InputPreparation.preparation modulus).value,
    outputOld modulus old positive bounded)

/-- Exact arbitrary-target XOR action of the physically placed complete inverse. -/
lemma program_prepared_input (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index)
    (coprime : Nat.Coprime (inputBasisEquiv modulus.size old).1.val modulus)
    (positive : 0 < (inputBasisEquiv modulus.size old).1.val)
    (bounded : (inputBasisEquiv modulus.size old).1.val < modulus) :
    (program modulus).applyNormalized environment
        (NormalizedVector.ket
          (InversePreparation.assembly modulus.size
            ((InputPreparation.preparation modulus).value, old))) =
      NormalizedVector.ket (outputBasis modulus old positive bounded) := by
  have actual := NativeInverse.nativeInverse_nativeProgram_initial
      (environment := environment) modulus nontrivial
    (inputBasisEquiv modulus.size old).1 (inputBasisEquiv modulus.size old).2
    coprime positive bounded
  have placed := InverseRuntimeFrame.program_apply_ket modulus.size
    (NativeInverse.nativeProgram modulus nontrivial) _ _ actual
    (InversePreparation.assembly modulus.size
      ((InputPreparation.preparation modulus).value, old))
    (outputBasis modulus old positive bounded)
  have initial :
      UnitaryCircuit.selectedInput
        (InverseRuntimeFrame.source modulus.size)
        (after modulus.size).quantumLayout (InverseRuntimeFrame.position modulus.size)
        (InverseRuntimeFrame.position_dimensions modulus.size)
        (InversePreparation.assembly modulus.size
          ((InputPreparation.preparation modulus).value, old)) =
        (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
          ((OutputCopy.encoding modulus.size).encode
            (InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
              (inputBasisEquiv modulus.size old).2)) := by
    rw [InverseRuntimeFrame.selectedBasis_eq_basisEquiv]
    exact congrArg
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
      (InverseAssembly.prepared_initial modulus old)
  have final :
      UnitaryCircuit.selectedInput
        (InverseRuntimeFrame.source modulus.size)
        (after modulus.size).quantumLayout (InverseRuntimeFrame.position modulus.size)
        (InverseRuntimeFrame.position_dimensions modulus.size)
        (outputBasis modulus old positive bounded) =
        (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
          ((OutputCopy.encoding modulus.size).encode
            (InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
              NativeInverse.output modulus (inputBasisEquiv modulus.size old).1.val
                positive bounded (inputBasisEquiv modulus.size old).2)) := by
    rw [InverseRuntimeFrame.selectedBasis_eq_basisEquiv]
    have prepared := InverseAssembly.prepared_initial modulus
      (outputOld modulus old positive bounded)
    have word : InverseAssembly.basisEquiv modulus.size
        (outputBasis modulus old positive bounded) =
          (OutputCopy.encoding modulus.size).encode
            (InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
              NativeInverse.output modulus (inputBasisEquiv modulus.size old).1.val
                positive bounded (inputBasisEquiv modulus.size old).2) := by
      simpa only [outputBasis, outputOld, Equiv.apply_symm_apply] using prepared
    change (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm
        (InverseAssembly.basisEquiv modulus.size
          (outputBasis modulus old positive bounded)) =
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm _
    exact congrArg
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).basisEquiv.symm word
  have done := placed initial final
  simpa only [program, nativeProgram, dif_pos nontrivial] using done

/-- One selected-model unitary instruction runs the complete inverse. -/
def body (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (after modulus.size) (after modulus.size) :=
  .unitary (program modulus)

/-- Load fixed auxiliaries and execute compute-copy-uncompute. -/
def code (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size) (after modulus.size) :=
  (InversePreparation.circuit modulus).seq (body modulus)

lemma program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace = (nativeProgram modulus).eventTrace :=
  InverseRuntimeFrame.program_eventTrace modulus.size (nativeProgram modulus)

lemma program_eventCost (modulus : Nat) :
    (program modulus).eventCost = (nativeProgram modulus).eventCost :=
  InverseRuntimeFrame.program_eventCost modulus.size (nativeProgram modulus)

/-- The trace charges allocation, seed X gates, and every native inverse event. -/
lemma code_eventTrace (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).eventTrace path =
      (ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
        (InversePreparation.loadProgram modulus).eventTrace) ++
      (nativeProgram modulus).eventTrace := by
  change (InversePreparation.circuit modulus).eventTrace path.1 ++
    (program modulus).eventTrace = _
  rw [InversePreparation.circuit_eventTrace, program_eventTrace]

variable {Reference : Register} {H : Type} [Fintype H]

/-- The full quantum/reference density includes both actual execution stages. -/
lemma code_quantumMarginal (modulus : Nat)
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((code modulus).execute runtimeEnvironment Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor ((program modulus).matrix runtimeEnvironment.quantum)
          (1 : UnitaryOperator Reference))
        (((InversePreparation.circuit modulus).execute runtimeEnvironment
          Reference state).quantumMarginal) := by
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal, body,
    Circuit.unitary_jointDensity]

/-- Both stages preserve every external-reference matrix entry. -/
lemma code_reference_entry (modulus : Nat)
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (left right : Reference.Index) :
    (∑ basis : (after modulus.size).register.Index,
      ((code modulus).execute runtimeEnvironment Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before modulus.size).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) := by
  rw [code_quantumMarginal]
  exact (DensityOperator.localUnitary_reference_entry ((program modulus).matrix
    runtimeEnvironment.quantum)
    (((InversePreparation.circuit modulus).execute runtimeEnvironment
      Reference state).quantumMarginal)
      left right).trans
        (InversePreparation.execute_reference_entry modulus state left right)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseRuntime
