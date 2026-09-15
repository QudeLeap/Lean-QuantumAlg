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

open Execution

/-- Extend the actual arithmetic by the live flag and preserve the numerical binary association. -/
def extendedProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit
      (Qubits (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width) :=
  .reindex (nativeLabelEquiv modulus.size)
    (UnitaryCircuit.prodLeft (n := 1) (Accumulate.program modulus nontrivial))

private theorem extendedProgram_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (extendedProgram modulus nontrivial).physical_idx ⊆
      List.range (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width := by
  have within : (Accumulate.program modulus nontrivial).physical_idx ⊆
      List.range (Accumulate.frameEncoding modulus.size).width := by
    intro wire present
    exact List.mem_range.mpr ((Accumulate.accumulateProgram_physical modulus nontrivial wire).1
      present)
  have extended := UnitaryCircuit.prodLeft_physical_idx_subset_range
    (n := 1) (Accumulate.program modulus nontrivial) within
  change (extendedProgram modulus nontrivial).physical_idx ⊆
    List.range (nativeEncoding modulus.size).width at extended
  rw [accumulatePayload_width] at extended
  exact extended

/-- The only numerical branch chooses the actual nontrivial program or complete-frame identity. -/
def nativeProgram (modulus : Nat) :
    UnitaryCircuit
      (Qubits (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width) :=
  if nontrivial : 1 < modulus then extendedProgram modulus nontrivial
  else UnitaryCircuit.identity
    (Qubits (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width)
    (List.range (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width)
    List.nodup_range

private theorem nativeProgram_within (modulus : Nat) :
    (nativeProgram modulus).physical_idx ⊆
      List.range (PayloadPreparation.frameEncoding modulus.size (modulus.size + 1)).width := by
  unfold nativeProgram
  split
  · exact extendedProgram_within modulus _
  · exact List.Subset.refl _

/-- The complete native matrix acts on the actual live context with the same physical identities. -/
def program (modulus : Nat) : UnitaryCircuit (after modulus.size).register :=
  PayloadRuntime.program modulus.size (modulus.size + 1) (nativeProgram modulus)

/-- Every supplied and prepared wire is present in the complete actual runtime footprint. -/
theorem accumulateRuntime_program_physical (modulus : Nat) :
    (program modulus).physical_idx = (after modulus.size).physicalIdx :=
  PayloadRuntime.payloadRuntime_program_physical modulus.size (modulus.size + 1)
    (nativeProgram modulus) (nativeProgram_within modulus)

/-- The trivial branch preserves every full basis column, including arbitrary auxiliary values. -/
theorem accumulateRuntime_trivial_ket (modulus : Nat) (trivial : ¬1 < modulus)
    (basis : (after modulus.size).register.Index) :
    (program modulus).applyNormalized (NormalizedVector.ket basis) =
      NormalizedVector.ket basis := by
  have native : (nativeProgram modulus).applyNormalized
      (NormalizedVector.ket
        (PayloadAssembly.basisEquiv modulus.size (modulus.size + 1) basis)) =
      NormalizedVector.ket
        (PayloadAssembly.basisEquiv modulus.size (modulus.size + 1) basis) := by
    rw [nativeProgram, dif_neg trivial]
    exact UnitaryCircuit.applyNormalized_identity _ _ _ _
  have actual := PayloadRuntime.payloadRuntime_program_apply_ket modulus.size (modulus.size + 1)
    (nativeProgram modulus) _ _ native
  simpa only [program, Equiv.symm_apply_apply] using actual

/-- Independently add the mathematical inverse while preserving the original input and flag. -/
def outputOld (modulus : Nat) (modulusPositive : 0 < modulus)
    (old : (before modulus.size).register.Index) : (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).symm
    ((inputBasisEquiv modulus.size old).1,
      Accumulate.output modulus modulusPositive (inputBasisEquiv modulus.size old).1.val
        (inputBasisEquiv modulus.size old).2.1,
      (inputBasisEquiv modulus.size old).2.2)

private theorem extendedProgram_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input target : Fin (2 ^ modulus.size)) (flag : Bool)
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (targetBounded : target.val < modulus) :
    (extendedProgram modulus nontrivial).applyNormalized
        (NormalizedVector.ket
          (nativeLabelEquiv modulus.size
            ((nativeEncoding modulus.size).encode
              ((InitialFrame.initial modulus input, target), flag)))) =
      NormalizedVector.ket
        (nativeLabelEquiv modulus.size
          ((nativeEncoding modulus.size).encode
            ((InitialFrame.initial modulus input,
              Accumulate.output modulus (by omega) input.val target), flag))) := by
  have native := Accumulate.accumulateProgram_reference BinaryLabelEncoding.bool modulus nontrivial
    input target coprime positive bounded targetBounded flag
  exact UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (nativeLabelEquiv modulus.size)
    (UnitaryCircuit.prodLeft (n := 1) (Accumulate.program modulus nontrivial)) _ _ native

private theorem nativeProgram_prepared (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size old)) :
    (nativeProgram modulus).applyNormalized
        (NormalizedVector.ket
          (PayloadAssembly.basisEquiv modulus.size (modulus.size + 1)
            (PayloadPreparation.assembly modulus.size (modulus.size + 1)
              ((InputPreparation.preparation modulus).value, old)))) =
      NormalizedVector.ket
        (PayloadAssembly.basisEquiv modulus.size (modulus.size + 1)
          (PayloadPreparation.assembly modulus.size (modulus.size + 1)
            ((InputPreparation.preparation modulus).value, outputOld modulus (by omega) old))) := by
  have positive := AccumulateSpecification.accumulateSpecification_positive modulus nontrivial
    (inputBasisEquiv modulus.size old) allowed
  rw [nativeProgram, dif_pos nontrivial, accumulatePayload_prepared_initial,
    accumulatePayload_prepared_initial]
  simp only [outputOld, Equiv.apply_symm_apply]
  exact extendedProgram_initial modulus nontrivial (inputBasisEquiv modulus.size old).1
    (inputBasisEquiv modulus.size old).2.1 (inputBasisEquiv modulus.size old).2.2
    allowed.2.1 positive allowed.1 allowed.2.2

/-- The complete native branch restores prepared fields and preserves the supplied flag. -/
theorem accumulateRuntime_prepared_ket (modulus : Nat) (nontrivial : 1 < modulus)
    (old : (before modulus.size).register.Index)
    (allowed : AccumulateSpecification.admissible modulus (inputBasisEquiv modulus.size old)) :
    (program modulus).applyNormalized
        (NormalizedVector.ket (R := (after modulus.size).register)
          (PayloadPreparation.assembly modulus.size (modulus.size + 1)
            ((InputPreparation.preparation modulus).value, old))) =
      NormalizedVector.ket (R := (after modulus.size).register)
        (PayloadPreparation.assembly modulus.size (modulus.size + 1)
          ((InputPreparation.preparation modulus).value, outputOld modulus (by omega) old)) := by
  have actual := PayloadRuntime.payloadRuntime_program_apply_ket modulus.size (modulus.size + 1)
    (nativeProgram modulus) _ _ (nativeProgram_prepared modulus nontrivial old allowed)
  simpa only [program, Equiv.symm_apply_apply] using actual

/-- One actual fixed preparation precedes the selected complete native arithmetic program. -/
def code (modulus : Nat) : Circuit (before modulus.size) (after modulus.size) :=
  PayloadRuntime.code modulus (modulus.size + 1) (nativeProgram modulus)
    (nativeProgram_within modulus)

/-- Every actual trace includes preparation and all occurrences of the same selected native body. -/
theorem accumulateRuntime_code_eventTrace (modulus : Nat) (path : (code modulus).Path) :
    (code modulus).eventTrace path =
      (InputPreparation.preparation modulus).event :: (nativeProgram modulus).eventTrace :=
  PayloadRuntime.payloadRuntime_code_eventTrace modulus (modulus.size + 1)
    (nativeProgram modulus) (nativeProgram_within modulus) path

end

end QuantumAlg.MAU.Inversion.SharedEEA.AccumulateRuntime
