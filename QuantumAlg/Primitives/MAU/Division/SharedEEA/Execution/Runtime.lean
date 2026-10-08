/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Execution.Layout
import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Correctness
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Payload.Runtime

/-!
# Actual prepared division accumulation with the original live flag

One fixed source auxiliary preparation precedes the native arithmetic.
For every nontrivial modulus, the complete corrected EEA forward, actual
VariableGidney product accumulation, and identical EEA dagger act beside
the original flag. Modulus one uses full-frame identity after that same
real preparation. The domain includes even and composite positive moduli;
this project extension does not substitute the source's prime assumption
[LYL+26, sec_EEA/sub_4phase.tex:104-128]. All physical systems remain live.
-/

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionRuntime

noncomputable section

open Execution ExecutionLayout Inversion.SharedEEA

/-- The arithmetic acts beside the original supplied flag in the same physical order. -/
def flagProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (nativeEncoding modulus.size).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix 1
    (QuantumAlg.MAU.Division.SharedEEA.program modulus nontrivial)

/-- Reassociate only the binary width of the retained physical carrier. -/
def nontrivialProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size (payloadWidth modulus.size)) :=
  (flagProgram modulus nontrivial).castCanonicalQubitWidth
    (divisionPayload_width modulus.size)

/-- Select full arithmetic or full-frame identity after the same preparation. -/
def nativeProgram (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size (payloadWidth modulus.size)) :=
  if nontrivial : 1 < modulus then nontrivialProgram modulus nontrivial
  else UnitaryCircuit.identity AlgorithmGate.model .empty
    (PayloadRuntimeFrame.source modulus.size (payloadWidth modulus.size))

/-- Run the native matrix on the actual prepared context. -/
def program (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (after modulus.size).quantumLayout :=
  PayloadRuntime.program modulus.size (payloadWidth modulus.size) (nativeProgram modulus)

/-- Modulus one fixes every full prepared-frame basis column. -/
theorem divisionExecution_program_trivial_ket (modulus : Nat) (trivial : ¬1 < modulus)
    (basis : (after modulus.size).register.Index) :
    (program modulus).applyNormalized (NormalizedVector.ket basis) =
      NormalizedVector.ket basis := by
  have native : (nativeProgram modulus).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical
          (PayloadPreparation.frameEncoding modulus.size
            (payloadWidth modulus.size)).width).basisEquiv.symm
          (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size) basis))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
          (PayloadPreparation.frameEncoding modulus.size
            (payloadWidth modulus.size)).width).basisEquiv.symm
          (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size) basis)) := by
    rw [nativeProgram, dif_neg trivial]
    change (1 : UnitaryOperator (PayloadRuntimeFrame.source modulus.size
      (payloadWidth modulus.size)).register).apply _ = _
    exact UnitaryOperator.one_apply _
  have selected := PayloadRuntimeFrame.selectedBasis_eq_basisEquiv modulus.size
    (payloadWidth modulus.size) basis
  exact PayloadRuntime.payloadRuntime_program_apply_ket modulus.size
    (payloadWidth modulus.size) (nativeProgram modulus) _ _ native basis basis selected selected

/-- Source and flag are retained while the arbitrary modular target receives quotient addition. -/
def outputOld (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) : (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).symm
    ((inputBasisEquiv modulus.size old).1,
      (((inputBasisEquiv modulus.size old).2.1.1,
        output modulus modulusPositive (inputBasisEquiv modulus.size old).1.val
          (inputBasisEquiv modulus.size old).2.1.1 (inputBasisEquiv modulus.size old).2.1.2),
        (inputBasisEquiv modulus.size old).2.2))

/-- Every original fixed auxiliary value is retained alongside the updated complete data payload. -/
def outputBasis (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) : (after modulus.size).register.Index :=
  PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
    ((InputPreparation.preparation modulus).value, outputOld modulus modulusPositive old)

private theorem cast_native_action {source target : Nat} (same : source = target)
    (body : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical source).toQuantum)
    (input output : Fin (2 ^ source))
    (action : body.applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical source).basisEquiv.symm input)) =
        NormalizedVector.ket ((QubitLayout.canonical source).basisEquiv.symm output)) :
    (body.castCanonicalQubitWidth same).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical target).basisEquiv.symm
          (UnitaryCircuit.castQubitWidthIndex same input))) =
      NormalizedVector.ket
        ((QubitLayout.canonical target).basisEquiv.symm
          (UnitaryCircuit.castQubitWidthIndex same output)) := by
  cases same
  exact action

/-- Full native division and the retained flag have their exact prepared action. -/
theorem divisionExecution_nontrivial_ket (modulus : Nat) (nontrivial : 1 < modulus)
    (denominator numerator target : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime denominator.val modulus) (positive : 0 < denominator.val)
    (bounded : denominator.val < modulus) (targetBounded : target.val < modulus) (flag : Bool) :
    (nontrivialProgram modulus nontrivial).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (PayloadPreparation.frameEncoding modulus.size
            (payloadWidth modulus.size)).width).basisEquiv.symm
            (nativeLabelEquiv modulus.size
              ((nativeEncoding modulus.size).encode
                ((InitialFrame.initial modulus denominator, numerator, target), flag))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
          (PayloadPreparation.frameEncoding modulus.size
            (payloadWidth modulus.size)).width).basisEquiv.symm
          (nativeLabelEquiv modulus.size
            ((nativeEncoding modulus.size).encode
              ((InitialFrame.initial modulus denominator, numerator,
                output modulus (by omega) denominator.val numerator target), flag)))) := by
  have native := divisionProgram_reference BinaryLabelEncoding.bool modulus nontrivial
    denominator numerator target coprime positive bounded targetBounded flag
  change (flagProgram modulus nontrivial).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical (nativeEncoding modulus.size).width).basisEquiv.symm
          ((nativeEncoding modulus.size).encode
            ((InitialFrame.initial modulus denominator, numerator, target), flag)))) =
    NormalizedVector.ket
      ((QubitLayout.canonical (nativeEncoding modulus.size).width).basisEquiv.symm
        ((nativeEncoding modulus.size).encode
          ((InitialFrame.initial modulus denominator, numerator,
            output modulus (by omega) denominator.val numerator target), flag))) at native
  exact cast_native_action (divisionPayload_width modulus.size)
    (flagProgram modulus nontrivial)
    ((nativeEncoding modulus.size).encode
      ((InitialFrame.initial modulus denominator, numerator, target), flag))
    ((nativeEncoding modulus.size).encode
      ((InitialFrame.initial modulus denominator, numerator,
        output modulus (by omega) denominator.val numerator target), flag)) native

/-- The chosen native branch maps prepared source and payload to the independent output. -/
private theorem nativeProgram_prepared (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index) (allowed : admissible modulus old) :
    (nativeProgram modulus).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (PayloadPreparation.frameEncoding modulus.size
            (payloadWidth modulus.size)).width).basisEquiv.symm
            (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size)
              (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
                ((InputPreparation.preparation modulus).value, old))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
          (PayloadPreparation.frameEncoding modulus.size
            (payloadWidth modulus.size)).width).basisEquiv.symm
          (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size)
            (outputBasis modulus (by omega) old))) := by
  have positive := ExecutionSpecification.divisionSpecification_positive modulus nontrivial
    (inputBasisEquiv modulus.size old) allowed
  rw [nativeProgram, dif_pos nontrivial, outputBasis,
    divisionPayload_prepared_initial, divisionPayload_prepared_initial]
  simp only [outputOld, Equiv.apply_symm_apply]
  exact divisionExecution_nontrivial_ket modulus nontrivial
    (inputBasisEquiv modulus.size old).1 (inputBasisEquiv modulus.size old).2.1.1
    (inputBasisEquiv modulus.size old).2.1.2 allowed.2.1 positive allowed.1 allowed.2.2.2
    (inputBasisEquiv modulus.size old).2.2

/-- Exact runtime ket action restores the EEA frame and unchanged supplied fields. -/
theorem divisionExecution_program_prepared (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index) (allowed : admissible modulus old) :
    (program modulus).applyNormalized
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
            ((InputPreparation.preparation modulus).value, old))) =
      NormalizedVector.ket (R := (after modulus.size).register)
        (outputBasis modulus (by omega) old) := by
  exact PayloadRuntime.payloadRuntime_program_apply_ket modulus.size
    (payloadWidth modulus.size) (nativeProgram modulus) _ _
    (nativeProgram_prepared modulus nontrivial old allowed)
    (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
      ((InputPreparation.preparation modulus).value, old))
    (outputBasis modulus (by omega) old)
    (PayloadRuntimeFrame.selectedBasis_eq_basisEquiv modulus.size (payloadWidth modulus.size) _)
    (PayloadRuntimeFrame.selectedBasis_eq_basisEquiv modulus.size (payloadWidth modulus.size) _)

/-- Execute zero allocation, fixed loading gates, and the complete arithmetic branch. -/
def code (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (before modulus.size) (after modulus.size) :=
  PayloadRuntime.code modulus (payloadWidth modulus.size) (nativeProgram modulus)

/-- Every event trace contains preparation and the same selected native program. -/
theorem divisionExecution_code_eventTrace (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).eventTrace path =
      (ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
        (PayloadPreparation.loadProgram modulus (payloadWidth modulus.size)).eventTrace) ++
        (nativeProgram modulus).eventTrace :=
  PayloadRuntime.payloadRuntime_code_eventTrace modulus (payloadWidth modulus.size)
    (nativeProgram modulus) path

/-- Fixed preparation and selected native body determine the actual joint density. -/
theorem divisionExecution_code_quantumMarginal (modulus : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((code modulus).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program modulus).matrix (1 : UnitaryOperator Reference))
        ((PayloadPreparation.circuit modulus (payloadWidth modulus.size)).execute
          Reference state).quantumMarginal :=
  PayloadRuntime.payloadRuntime_code_quantumMarginal modulus (payloadWidth modulus.size)
    (nativeProgram modulus) state

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionRuntime
