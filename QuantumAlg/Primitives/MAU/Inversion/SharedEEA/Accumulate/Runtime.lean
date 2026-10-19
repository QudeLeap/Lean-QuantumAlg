/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Runtime.Layout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Correctness
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Payload.Runtime

/-!
# Actual prepared modular-add inversion with the original supplied flag

The nontrivial branch executes the complete native inverse accumulation
beside the unchanged flag. Modulus one selects full-frame identity after
the same fixed auxiliary preparation. Both branches retain all supplied
and prepared systems, and the same code determines their actual resources.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AccumulateRuntime

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution

/-- Extend the actual arithmetic by the live flag and preserve the numerical binary association. -/
def extendedProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size (modulus.size + 1)) :=
  (UnitaryCircuit.onBinaryPrefix 1 (Accumulate.program modulus nontrivial)).castCanonicalQubitWidth
    (accumulatePayload_width modulus.size)

/-- The only numerical branch chooses the actual nontrivial program or complete-frame identity. -/
def nativeProgram (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size (modulus.size + 1)) :=
  if nontrivial : 1 < modulus then extendedProgram modulus nontrivial
  else UnitaryCircuit.identity AlgorithmGate.model .empty
    (PayloadRuntimeFrame.source modulus.size (modulus.size + 1))

/-- The complete native matrix acts on the actual live context with the same physical identities. -/
def program (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (after modulus.size).quantumLayout :=
  PayloadRuntime.program modulus.size (modulus.size + 1) (nativeProgram modulus)

/-- The trivial branch preserves every full basis column, including arbitrary auxiliary values. -/
lemma accumulateRuntime_trivial_ket (modulus : Nat) (trivial : ¬1 < modulus)
    (basis : (after modulus.size).register.Index) :
    (program modulus).applyNormalized environment (NormalizedVector.ket basis) =
      NormalizedVector.ket basis := by
  have native : (nativeProgram modulus).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical
          (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width).basisEquiv.symm
          (PayloadAssembly.basisEquiv modulus.size (modulus.size + 1) basis))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
          (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width).basisEquiv.symm
          (PayloadAssembly.basisEquiv modulus.size (modulus.size + 1) basis)) := by
    rw [nativeProgram, dif_neg trivial]
    change (1 : UnitaryOperator (PayloadRuntimeFrame.source modulus.size
      (modulus.size + 1)).register).apply _ = _
    exact UnitaryOperator.one_apply _
  have selected := PayloadRuntimeFrame.selectedBasis_eq_basisEquiv modulus.size
    (modulus.size + 1) basis
  have actual := PayloadRuntime.payloadRuntime_program_apply_ket
      (environment := environment) modulus.size
    (modulus.size + 1) (nativeProgram modulus) _ _ native basis basis selected selected
  exact actual

/-- Independently add the mathematical inverse while preserving the original input and flag. -/
def outputOld (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) : (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).symm
    ((inputBasisEquiv modulus.size old).1,
      Accumulate.output modulus modulusPositive (inputBasisEquiv modulus.size old).1.val
        (inputBasisEquiv modulus.size old).2.1,
      (inputBasisEquiv modulus.size old).2.2)

private lemma cast_native_action {source target : Nat} (same : source = target)
    (body : UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical source).toQuantum)
    (input output : Fin (2 ^ source))
    (action : body.applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical source).basisEquiv.symm input)) =
        NormalizedVector.ket ((QubitLayout.canonical source).basisEquiv.symm output)) :
    (body.castCanonicalQubitWidth same).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical target).basisEquiv.symm
          (UnitaryCircuit.castQubitWidthIndex same input))) =
      NormalizedVector.ket
        ((QubitLayout.canonical target).basisEquiv.symm
          (UnitaryCircuit.castQubitWidthIndex same output)) := by
  cases same
  exact action

private lemma extendedProgram_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input target : Fin (2 ^ modulus.size)) (flag : Bool)
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (targetBounded : target.val < modulus) :
    (extendedProgram modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (PayloadPreparation.frameEncoding modulus.size
              (modulus.size + 1)).width).basisEquiv.symm
            (nativeLabelEquiv modulus.size
              ((nativeEncoding modulus.size).encode
                ((InitialFrame.initial modulus input, target), flag))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
          (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width).basisEquiv.symm
          (nativeLabelEquiv modulus.size
            ((nativeEncoding modulus.size).encode
              ((InitialFrame.initial modulus input,
                Accumulate.output modulus (by omega) input.val target), flag)))) := by
  have native := Accumulate.accumulateProgram_reference (environment := environment)
    BinaryLabelEncoding.bool modulus nontrivial
    input target coprime positive bounded targetBounded flag
  change (UnitaryCircuit.onBinaryPrefix 1
      (Accumulate.program modulus nontrivial)).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (nativeEncoding modulus.size).width).basisEquiv.symm
            ((nativeEncoding modulus.size).encode
              ((InitialFrame.initial modulus input, target), flag)))) =
    NormalizedVector.ket
      ((QubitLayout.canonical (nativeEncoding modulus.size).width).basisEquiv.symm
        ((nativeEncoding modulus.size).encode
          ((InitialFrame.initial modulus input,
            Accumulate.output modulus (by omega) input.val target), flag))) at native
  exact cast_native_action (accumulatePayload_width modulus.size)
    (UnitaryCircuit.onBinaryPrefix 1 (Accumulate.program modulus nontrivial))
    ((nativeEncoding modulus.size).encode
      ((InitialFrame.initial modulus input, target), flag))
    ((nativeEncoding modulus.size).encode
      ((InitialFrame.initial modulus input,
        Accumulate.output modulus (by omega) input.val target), flag)) native

private lemma nativeProgram_prepared (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size old)) :
    (nativeProgram modulus).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (PayloadPreparation.frameEncoding modulus.size
              (modulus.size + 1)).width).basisEquiv.symm
            (PayloadAssembly.basisEquiv modulus.size (modulus.size + 1)
              (PayloadPreparation.assembly modulus.size (modulus.size + 1)
                ((InputPreparation.preparation modulus).value, old))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
          (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width).basisEquiv.symm
          (PayloadAssembly.basisEquiv modulus.size (modulus.size + 1)
            (PayloadPreparation.assembly modulus.size (modulus.size + 1)
              ((InputPreparation.preparation modulus).value,
                outputOld modulus (by omega) old)))) := by
  have positive := AccumulateSpecification.accumulateSpecification_positive modulus nontrivial
    (inputBasisEquiv modulus.size old) allowed
  rw [nativeProgram, dif_pos nontrivial, accumulatePayload_prepared_initial,
    accumulatePayload_prepared_initial]
  simp only [outputOld, Equiv.apply_symm_apply]
  exact extendedProgram_initial modulus nontrivial (inputBasisEquiv modulus.size old).1
    (inputBasisEquiv modulus.size old).2.1 (inputBasisEquiv modulus.size old).2.2
    allowed.2.1 positive allowed.1 allowed.2.2

/-- The complete native branch restores prepared fields and preserves the supplied flag. -/
lemma accumulateRuntime_prepared_ket (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size old)) :
    (program modulus).applyNormalized environment
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (modulus.size + 1)
            ((InputPreparation.preparation modulus).value, old))) =
      NormalizedVector.ket (R := (after modulus.size).register)
        (PayloadPreparation.assembly modulus.size (modulus.size + 1)
          ((InputPreparation.preparation modulus).value, outputOld modulus (by omega) old)) := by
  have actual := PayloadRuntime.payloadRuntime_program_apply_ket
      (environment := environment) modulus.size (modulus.size + 1)
    (nativeProgram modulus) _ _ (nativeProgram_prepared modulus nontrivial old allowed)
    (PayloadPreparation.assembly modulus.size (modulus.size + 1)
      ((InputPreparation.preparation modulus).value, old))
    (PayloadPreparation.assembly modulus.size (modulus.size + 1)
      ((InputPreparation.preparation modulus).value, outputOld modulus (by omega) old))
    (PayloadRuntimeFrame.selectedBasis_eq_basisEquiv modulus.size (modulus.size + 1) _)
    (PayloadRuntimeFrame.selectedBasis_eq_basisEquiv modulus.size (modulus.size + 1) _)
  exact actual

/-- One actual fixed preparation precedes the selected complete native arithmetic program. -/
def code (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (before modulus.size) (after modulus.size) :=
  PayloadRuntime.code modulus (modulus.size + 1) (nativeProgram modulus)

/-- Every actual trace includes preparation and all occurrences of the same selected native body. -/
lemma accumulateRuntime_code_eventTrace (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).eventTrace path =
      (ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
        (PayloadPreparation.loadProgram modulus (modulus.size + 1)).eventTrace) ++
        (nativeProgram modulus).eventTrace :=
  PayloadRuntime.payloadRuntime_code_eventTrace modulus (modulus.size + 1)
    (nativeProgram modulus) path

end

end QuantumAlg.MAU.Inversion.SharedEEA.AccumulateRuntime
