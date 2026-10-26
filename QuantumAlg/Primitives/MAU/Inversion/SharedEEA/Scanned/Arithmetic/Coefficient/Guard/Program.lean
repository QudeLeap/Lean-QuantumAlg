/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Guard.Body
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Guard.Action

/-!
# Actual coefficient source guard, addressed arithmetic and complete cleanup

Both full source-guard executions and the addressed arithmetic are
actual native programs. Original Ctrl starts false, as in the original
source instruction contract. All other original finite metadata and
Iter remain arbitrary. Every physical address/prefix/conjunction bit
returns to its original zero value after this same fixed program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientGuard

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Two actual complete source guards surround the actual addressed coefficient arithmetic. -/
def program (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (ArithmeticGuard.coefficientToggleProgram width positive signed).seq
    ((bodyProgram width positive signed).seq
      (ArithmeticGuard.coefficientToggleProgram width positive signed))

/-- The complete emitted native instruction has the independent full original source action. -/
lemma program_apply_encoded_ket (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (disabled : state.1.control = false) :
    (program width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (step width signed state))) := by
  have targetZero : ArithmeticGeometry.targetValue width state =
      0#(ArithmeticGeometry.fullWidth width) := by
    rw [ArithmeticGeometry.targetValue, zero, addressZero]
    exact BitVec.false_cons_zero
  have firstActual := ArithmeticGuard.coefficientToggleProgram_apply_encoded_ket
    width positive signed environment state clean targetZero
  by_cases active : ArithmeticGuard.coefficientEnabled width signed state = true
  · have accepted := enabled_admitted width signed state active
    let selected := CoefficientCoordinates.window width
      (CoefficientAddress.wordLength width state.1)
      (CoefficientAddress.wordLength_fits width state.1 accepted)
    let before := (ArithmeticGuard.flag width 4).flip state
    let after := ArithmeticAddress.liftSource width
      (CoefficientWindowProgram.step selected (operation signed)) before
    have beforeEnabled : before.1.control = true := by
      change (!state.1.control) = true
      rw [disabled]
      rfl
    have beforeAccepted : CoefficientAddress.admitted width before.1 := accepted
    have middleActual := bodyProgram_apply_enabled width positive signed environment before
      clean zero addressZero beforeEnabled beforeAccepted
    change (bodyProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode before))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode after)) at middleActual
    have lastActual := ArithmeticGuard.coefficientToggleProgram_apply_encoded_ket
      width positive signed environment after clean targetZero
    have finalStep := toggle_body_toggle width signed selected state active
    rw [toggle_active width signed state active] at finalStep
    have finalEq : ArithmeticGuard.coefficientToggleStep width signed after =
        step width signed state := by
      rw [step, dif_pos active]
      exact finalStep
    rw [toggle_active width signed state active] at firstActual
    rw [program, UnitaryCircuit.applyNormalized_seq, firstActual,
      UnitaryCircuit.applyNormalized_seq, middleActual, lastActual, finalEq]
  · rw [toggle_inactive width signed state active] at firstActual
    have middleActual := bodyProgram_apply_disabled
      width positive signed environment state clean zero disabled
    rw [program, UnitaryCircuit.applyNormalized_seq, firstActual,
      UnitaryCircuit.applyNormalized_seq, middleActual, firstActual, step, dif_neg active]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientGuard
