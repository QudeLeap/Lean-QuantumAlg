/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Conjunction
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Remainder.Natural

/-!
# Paid full finite remainder-window control with actual target restoration

The actual full-carry metadata arithmetic prepares the physical length.
The actual conjunction toggles original Ctrl, and the actual unitary
adjoint then restores the entire temporary target. The retained
predicate reads complete natural metadata; no high carry is dropped
and no input value constructs a classical circuit parameter.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The independent positive-window and actual phase condition uses all source metadata bits. -/
def remainderEnabled (width : Nat) (signed : Bool) (state : Data width) : Bool :=
  decide (state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1 +
    state.1.shift.toNat < width + 3) && condition width signed false state

/-- Original Ctrl is toggled by that source condition and every other actual field is retained. -/
def remainderToggleStep (width : Nat) (signed : Bool) : Data width → Data width :=
  predicateFlip (flag width 4) (remainderEnabled width signed)

/-- Actual arithmetic preparation, actual finite predicate, and the same actual native adjoint. -/
def remainderToggleProgram (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (ArithmeticGeometry.remainderProgram width positive).seq
    ((conjunctionProgram width signed false).seq
      ((ArithmeticGeometry.remainderProgram width positive).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)))

private lemma restore_prepared (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) (state : Data width) :
    ((ArithmeticGeometry.remainderProgram width positive).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (ArithmeticGeometry.remainderStep width positive state)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  have forward :=
    (ArithmeticGeometry.remainderProgram_realizes width positive environment).apply_encoded_ket
      state
  rw [← forward]
  apply UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
  rw [UnitaryCircuit.dagger_matrix,
    Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
      environment]
  exact Unitary.star_eq_inv _

/-- Arbitrary original Ctrl and Iter follow the exact untruncated source predicate and cleanup. -/
lemma remainderToggleProgram_apply_encoded_ket (width : Nat) (positive : 1 ≤ width)
    (signed : Bool) (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : ArithmeticGeometry.targetValue width state = 0#(ArithmeticGeometry.fullWidth width)) :
    (remainderToggleProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (remainderToggleStep width signed state))) := by
  let prepared := ArithmeticGeometry.remainderStep width positive state
  have preparedClean : prepared.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (ArithmeticGeometry.remainderStep_prefix width positive state).trans clean
  have validity : valid width prepared =
      decide (state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1 +
        state.1.shift.toNat < width + 3) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [valid, decide_eq_true_eq] using
      ArithmeticGeometry.remainderStep_target_positive_iff width positive state clean zero
  have sameCondition : condition width signed false prepared = condition width signed false state :=
    congrArg (fun source : Registers width => condition width signed false (source, prepared.2))
      (ArithmeticGeometry.remainderStep_source width positive state)
  have selected : (valid width prepared && condition width signed false prepared) =
      remainderEnabled width signed state := by
    rw [validity, sameCondition]
    rfl
  have firstActual :=
    (ArithmeticGeometry.remainderProgram_realizes width positive environment).apply_encoded_ket
      state
  have middleActual :=
    conjunctionProgram_apply_encoded_ket width signed false environment prepared preparedClean
  rw [remainderToggleProgram, UnitaryCircuit.applyNormalized_seq, firstActual,
    UnitaryCircuit.applyNormalized_seq, middleActual]
  simp only [conjunctionStep, predicateFlip, selected]
  simp only [remainderToggleStep, predicateFlip]
  by_cases enabled : remainderEnabled width signed state = true
  · rw [if_pos enabled, if_pos enabled]
    have commute := ArithmeticGeometry.remainderStep_control_flip width positive state
    change ArithmeticGeometry.remainderStep width positive ((flag width 4).flip state) =
      (flag width 4).flip prepared at commute
    rw [← commute]
    exact restore_prepared width positive environment ((flag width 4).flip state)
  · rw [if_neg enabled, if_neg enabled]
    exact restore_prepared width positive environment state

/-- The complete physical pool is restored after the same actual paid predicate. -/
lemma remainderToggleStep_pool (width : Nat) (signed : Bool) (state : Data width) :
    (remainderToggleStep width signed state).2 = state.2 := by
  unfold remainderToggleStep predicateFlip
  split <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
