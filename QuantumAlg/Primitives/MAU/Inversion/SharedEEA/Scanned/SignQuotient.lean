/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Correctness
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Original
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.SignQuotient

/-!
# Paid scanned Sign exchange followed by the actual original quotient update

The exchange reads the old complete finite length sum with the corrected
phase offset. Only after it returns the entire shared pool does the
original native quotient update execute, retaining original dirty Work1
and Iter. The control premise is the original source contract.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SignQuotient

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The unchanged actual quotient primitive word occupies only the original source prefix. -/
def quotientProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (PhaseQuotient.nativeProgram width)

private lemma quotientProgram_realizes (width : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (quotientProgram width) environment
      (ArithmeticAddress.liftSource width PhaseQuotient.step) :=
  (PhaseQuotient.phaseQuotient_nativeProgram_realizes
    (environment := environment) width).onBinaryPrefix

/-- Actual paid complete scan, its cleanup, then the actual original quotient word. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (PreparedSelection.program width).seq (quotientProgram width)

/-- The same complete source Sign/quotient result returns the original entire shared pool. -/
lemma program_apply_source (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Data width)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (prefixZero : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (control : state.1.control = false) :
    (program width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (SharedEEA.SignQuotient.sourceStep width state.1, state.2))) := by
  let selected : Data width := (SelectionSchedule.sourceStep width state.1, state.2)
  have selectedControl : selected.1.control = false :=
    (SharedEEA.SignQuotient.source_control width state.1).trans control
  have firstActual := PreparedSelection.program_apply_sourceStep width environment state
    addressZero prefixZero
  rw [SelectionSpecification.sourceStep_eq_original width state.1 control] at firstActual
  have lastActual := (quotientProgram_realizes width environment).apply_encoded_ket selected
  change (quotientProgram width).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode selected))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode (PhaseQuotient.step selected.1, state.2))) at lastActual
  rw [PhaseQuotient.step_eq_sourceStep selected.1 selectedControl] at lastActual
  rw [program, UnitaryCircuit.applyNormalized_seq, firstActual, lastActual]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SignQuotient
