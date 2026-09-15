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

/-- The actual native arithmetic acts beside the original supplied flag qubit. -/
def flagProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit (Qubits (nativeEncoding modulus.size).width) :=
  UnitaryCircuit.prodLeft (n := BinaryLabelEncoding.bool.width)
    (QuantumAlg.MAU.Division.SharedEEA.program modulus nontrivial)

private theorem flagProgram_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (flagProgram modulus nontrivial).physical_idx ⊆
      List.range (nativeEncoding modulus.size).width := by
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  intro wire present
  exact List.mem_range.mpr ((divisionProgram_physical modulus nontrivial wire).mp present)

/-- Only representation association changes; the supplied body's physical identities remain. -/
def nontrivialProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit
      (Qubits (PayloadPreparation.frameEncoding modulus.size (payloadWidth modulus.size)).width) :=
  UnitaryCircuit.reindex (nativeLabelEquiv modulus.size) (flagProgram modulus nontrivial)

private theorem nontrivialProgram_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (nontrivialProgram modulus nontrivial).physical_idx ⊆
      List.range (PayloadPreparation.frameEncoding modulus.size (payloadWidth
        modulus.size)).width := by
  intro wire present
  have actual := List.mem_range.mp (flagProgram_within modulus nontrivial present)
  apply List.mem_range.mpr
  rw [← divisionPayload_width]
  exact actual

/-- Choose the full native arithmetic or a full-frame identity after the same fixed preparation. -/
def nativeProgram (modulus : Nat) :
    UnitaryCircuit
      (Qubits (PayloadPreparation.frameEncoding modulus.size (payloadWidth modulus.size)).width) :=
  if nontrivial : 1 < modulus then nontrivialProgram modulus nontrivial
  else UnitaryCircuit.identity
    (Qubits (PayloadPreparation.frameEncoding modulus.size (payloadWidth modulus.size)).width)
    (List.range (PayloadPreparation.frameEncoding modulus.size (payloadWidth modulus.size)).width)
    List.nodup_range

/-- Every native branch uses only the full actual frame and supplied payload coordinates. -/
theorem divisionExecution_native_within (modulus : Nat) :
    (nativeProgram modulus).physical_idx ⊆
      List.range (PayloadPreparation.frameEncoding modulus.size (payloadWidth
        modulus.size)).width := by
  by_cases nontrivial : 1 < modulus
  · simpa only [nativeProgram, dif_pos nontrivial] using
      nontrivialProgram_within modulus nontrivial
  · simp only [nativeProgram, dif_neg nontrivial]
    exact List.Subset.refl _

/-- The same native body runs on the exact actual prepared runtime context. -/
def program (modulus : Nat) : UnitaryCircuit (after modulus.size).register :=
  PayloadRuntime.program modulus.size (payloadWidth modulus.size) (nativeProgram modulus)

/-- All actual supplied and prepared identities occur in the final physical footprint. -/
theorem divisionExecution_program_physical (modulus : Nat) :
    (program modulus).physical_idx = (after modulus.size).physicalIdx :=
  PayloadRuntime.payloadRuntime_program_physical modulus.size (payloadWidth modulus.size)
    (nativeProgram modulus) (divisionExecution_native_within modulus)

/-- The trivial branch fixes every complete prepared-frame column, beyond valid input support. -/
theorem divisionExecution_program_trivial_ket (modulus : Nat) (trivial : ¬1 < modulus)
    (basis : (after modulus.size).register.Index) :
    (program modulus).applyNormalized (NormalizedVector.ket basis) =
      NormalizedVector.ket basis := by
  let identity := UnitaryCircuit.identity
    (Qubits (PayloadPreparation.frameEncoding modulus.size (payloadWidth modulus.size)).width)
    (List.range (PayloadPreparation.frameEncoding modulus.size (payloadWidth modulus.size)).width)
    List.nodup_range
  have actual := PayloadRuntime.payloadRuntime_program_apply_ket modulus.size
    (payloadWidth modulus.size) identity
    (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size) basis) _
    (UnitaryCircuit.applyNormalized_identity _ _ _
      (NormalizedVector.ket
        (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size) basis)))
  simpa only [program, nativeProgram, dif_neg trivial, Equiv.symm_apply_apply] using actual

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

/-- Exact native action after value-preserving binary reassociation, retaining the original flag. -/
theorem divisionExecution_nontrivial_ket (modulus : Nat) (nontrivial : 1 < modulus)
    (denominator numerator target : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime denominator.val modulus) (positive : 0 < denominator.val)
    (bounded : denominator.val < modulus) (targetBounded : target.val < modulus) (flag : Bool) :
    (nontrivialProgram modulus nontrivial).applyNormalized
        (NormalizedVector.ket (nativeLabelEquiv modulus.size
          ((nativeEncoding modulus.size).encode
            ((InitialFrame.initial modulus denominator, numerator, target), flag)))) =
      NormalizedVector.ket (nativeLabelEquiv modulus.size
        ((nativeEncoding modulus.size).encode
          ((InitialFrame.initial modulus denominator, numerator,
            output modulus (by omega) denominator.val numerator target), flag))) :=
  UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (nativeLabelEquiv modulus.size) (flagProgram modulus nontrivial) _ _
    (divisionProgram_reference BinaryLabelEncoding.bool modulus nontrivial
      denominator numerator target coprime positive bounded targetBounded flag)

private theorem initialBasis (modulus : Nat) (old : (before modulus.size).register.Index) :
    (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size)).symm
        (nativeLabelEquiv modulus.size
          ((nativeEncoding modulus.size).encode
            ((InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
              (inputBasisEquiv modulus.size old).2.1.1,
              (inputBasisEquiv modulus.size old).2.1.2),
              (inputBasisEquiv modulus.size old).2.2))) =
      PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
        ((InputPreparation.preparation modulus).value, old) := by
  have actual := congrArg
    (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size)).symm
    (divisionPayload_prepared_initial modulus old)
  simpa only [Equiv.symm_apply_apply] using actual.symm

private theorem finalBasis (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) :
    (PayloadAssembly.basisEquiv modulus.size (payloadWidth modulus.size)).symm
        (nativeLabelEquiv modulus.size
          ((nativeEncoding modulus.size).encode
            ((InitialFrame.initial modulus (inputBasisEquiv modulus.size old).1,
              (inputBasisEquiv modulus.size old).2.1.1,
              output modulus modulusPositive (inputBasisEquiv modulus.size old).1.val
                (inputBasisEquiv modulus.size old).2.1.1
                (inputBasisEquiv modulus.size old).2.1.2),
              (inputBasisEquiv modulus.size old).2.2))) =
      outputBasis modulus modulusPositive old := by
  simpa only [outputBasis, outputOld, Equiv.apply_symm_apply] using
    initialBasis modulus (outputOld modulus modulusPositive old)

/-- Exact runtime ket action restores the full initial EEA frame and all unchanged data fields. -/
theorem divisionExecution_program_prepared (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : admissible modulus old) :
    (program modulus).applyNormalized
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (payloadWidth modulus.size)
            ((InputPreparation.preparation modulus).value, old))) =
      NormalizedVector.ket (R := (after modulus.size).register)
        (outputBasis modulus (by omega) old) := by
  have positive := ExecutionSpecification.divisionSpecification_positive modulus nontrivial
    (inputBasisEquiv modulus.size old) allowed
  have actual := divisionExecution_nontrivial_ket modulus nontrivial
    (inputBasisEquiv modulus.size old).1 (inputBasisEquiv modulus.size old).2.1.1
    (inputBasisEquiv modulus.size old).2.1.2 allowed.2.1 positive allowed.1 allowed.2.2.2
    (inputBasisEquiv modulus.size old).2.2
  have placed := PayloadRuntime.payloadRuntime_program_apply_ket modulus.size
    (payloadWidth modulus.size) (nontrivialProgram modulus nontrivial) _ _ actual
  have inputKet := congrArg (NormalizedVector.ket (R := (after modulus.size).register))
    (initialBasis modulus old)
  have outputKet := congrArg (NormalizedVector.ket (R := (after modulus.size).register))
    (finalBasis modulus (by omega) old)
  have exactRun := (congrArg
    (PayloadRuntime.program modulus.size (payloadWidth modulus.size)
      (nontrivialProgram modulus nontrivial)).applyNormalized inputKet.symm).trans
        (placed.trans outputKet)
  simpa only [program, nativeProgram, dif_pos nontrivial] using exactRun

/-- Execute the one actual fixed preparation and the complete chosen arithmetic branch. -/
def code (modulus : Nat) : Circuit (before modulus.size) (after modulus.size) :=
  PayloadRuntime.code modulus (payloadWidth modulus.size) (nativeProgram modulus)
    (divisionExecution_native_within modulus)

/-- Exactly one preparation event precedes every event of the same chosen native body. -/
theorem divisionExecution_code_eventTrace (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).eventTrace path =
      (InputPreparation.preparation modulus).event :: (nativeProgram modulus).eventTrace :=
  PayloadRuntime.payloadRuntime_code_eventTrace modulus (payloadWidth modulus.size)
    (nativeProgram modulus) (divisionExecution_native_within modulus) path

/-- Fixed preparation and the selected complete native body determine the actual joint density. -/
theorem divisionExecution_code_quantumMarginal (modulus : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference H) :
    ((code modulus).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program modulus).matrix (1 : UnitaryOperator Reference))
        ((PayloadPreparation.circuit modulus (payloadWidth modulus.size)).execute
          Reference state).quantumMarginal :=
  PayloadRuntime.payloadRuntime_code_quantumMarginal modulus (payloadWidth modulus.size)
    (nativeProgram modulus) (divisionExecution_native_within modulus) state

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionRuntime
