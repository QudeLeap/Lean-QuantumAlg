/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Conjunction
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Coefficient.Runtime.Readout
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute

/-!
# Paid complete coefficient-window control with restored high carry

Actual original Phase2 controls the emitted length preparation. The
full geometry validity and phase predicate then toggle original Ctrl,
and the same actual preparation adjoint returns the complete temporary
target and prefix. All finite metadata values are retained
[LYL+26, sec_EEA/sub_regshare.tex:291-300].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Independent untruncated positive length and original source-phase condition. -/
def coefficientEnabled (width : Nat) (signed : Bool) (state : Data width) : Bool :=
  decide (if state.1.flags.second then
    state.1.divisorLength.toNat + state.1.shift.toNat < width + 3
  else state.1.coefficientLength.toNat + 1 ≤ width + 3) && condition width signed true state

/-- The independent semantic result changes only original Ctrl. -/
def coefficientToggleStep (width : Nat) (signed : Bool) : Data width → Data width :=
  predicateFlip (flag width 4) (coefficientEnabled width signed)

/-- Actual paid coherent preparation, native predicate copying, and the complete native adjoint. -/
def coefficientToggleProgram (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  PredicateCompute.program (ArithmeticGeometry.runtimeCoefficientProgram width positive)
    (conjunctionProgram width signed true)

/-- All finite source fields and arbitrary incoming Ctrl/Iter have their exact restored action. -/
lemma coefficientToggleProgram_apply_encoded_ket (width : Nat) (positive : 1 ≤ width)
    (signed : Bool) (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : ArithmeticGeometry.targetValue width state = 0#(ArithmeticGeometry.fullWidth width)) :
    (coefficientToggleProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (coefficientToggleStep width signed state))) := by
  let prepared := ArithmeticGeometry.runtimeCoefficientStep width positive state
  have preparedClean : prepared.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (ArithmeticGeometry.runtimeCoefficientStep_prefix width positive state).trans clean
  have validity : valid width prepared = decide (if state.1.flags.second then
      state.1.divisorLength.toNat + state.1.shift.toNat < width + 3
    else state.1.coefficientLength.toNat + 1 ≤ width + 3) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [valid, decide_eq_true_eq] using
      ArithmeticGeometry.runtimeCoefficientStep_target_positive_iff width positive state clean zero
  have phase : condition width signed true prepared = condition width signed true state :=
    congrArg (fun source : Registers width => condition width signed true (source, prepared.2))
      (ArithmeticGeometry.runtimeCoefficientStep_source width positive state)
  have selected : (valid width prepared && condition width signed true prepared) =
      coefficientEnabled width signed state := by
    rw [validity, phase]
    rfl
  have middle :=
    conjunctionProgram_apply_encoded_ket width signed true environment prepared preparedClean
  simp only [conjunctionStep, predicateFlip, selected] at middle
  have complete := PredicateCompute.program_apply_encoded_ket
    (ArithmeticGeometry.runtimeCoefficientProgram width positive)
    (conjunctionProgram width signed true)
    (ArithmeticGeometry.runtimeCoefficientStep width positive) (flag width 4)
    (coefficientEnabled width signed) environment
    (ArithmeticGeometry.runtimeCoefficientProgram_realizes width positive environment) state middle
    (ArithmeticGeometry.runtimeCoefficientStep_control_flip width positive state)
  exact complete

/-- The same actual guard restores all shared temporary bits, including the high geometry carry. -/
lemma coefficientToggleStep_pool (width : Nat) (signed : Bool) (state : Data width) :
    (coefficientToggleStep width signed state).2 = state.2 := by
  unfold coefficientToggleStep predicateFlip
  split <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
