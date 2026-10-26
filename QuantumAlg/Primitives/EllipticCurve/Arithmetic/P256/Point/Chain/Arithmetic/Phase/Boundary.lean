/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Phase.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State

/-!
# Paid phase correction from actual full physical readouts

The original reset target and three selected arithmetic flags suffice.
Every other history, padding, pool, F/N/C/W and complementary value remains
inside the exact original state. Only an active source needs to be canonical.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Phase

noncomputable section

open scoped BigOperators

/-- Convert actual whole-frame readouts to the same proved paid phase action. -/
lemma program_applyVec_of_flags (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (state : Frame.Raw) (outcome : Word)
    (reset : assignment.target.value state = Horner.zeroWord)
    (flags : ((Placement.layout assignment).grouping state).1.1.2 = false ∧
      ((Placement.layout assignment).grouping state).1.2.1 = false ∧
        ((Placement.layout assignment).grouping state).1.2.2 = false)
    (admitted : (physicalSelector selection).get state = true →
      Canonical (assignment.source.value state)) :
    (program assignment selection outcome).applyVec environment (Native.ket state).vec =
      WalshHadamard.walshSign outcome
        (Save.savedWord (assignment.source.value state) (assignment.multiplier.value state)
          ((physicalSelector selection).get state)) • (Native.ket state).vec := by
  let retained := ((Placement.layout assignment).grouping state).2.2
  let represented := Native.arithmeticState assignment (assignment.source.value state)
    Horner.zeroWord (assignment.multiplier.value state) retained
  have representation : state = represented :=
    (Native.state_eq_arithmeticState_of_flags assignment state flags).trans
      (congrArg (fun target => Native.arithmeticState assignment (assignment.source.value state)
        target (assignment.multiplier.value state) retained) reset)
  have selected : (selectorBit assignment selection).get retained =
      (physicalSelector selection).get state :=
    (selector_get assignment selection state).symm
  have column := program_applyVec assignment selection environment (assignment.source.value state)
    (assignment.multiplier.value state) outcome retained (fun active =>
      admitted (selected.symm.trans active))
  have coefficient := congrArg
    (fun value => WalshHadamard.walshSign outcome
      (Save.savedWord (assignment.source.value state) (assignment.multiplier.value state) value))
    selected
  calc
    (program assignment selection outcome).applyVec environment (Native.ket state).vec =
        (program assignment selection outcome).applyVec environment
          (Native.ket represented).vec := congrArg
      (fun original => (program assignment selection outcome).applyVec environment
        (Native.ket original).vec) representation
    _ = _ := column
    _ = _ := congrArg (fun value : ℂ => value • (Native.ket represented).vec) coefficient
    _ = _ := congrArg
      (fun original => WalshHadamard.walshSign outcome
        (Save.savedWord (assignment.source.value state) (assignment.multiplier.value state)
          ((physicalSelector selection).get state)) • (Native.ket original).vec)
      representation.symm

/-- Arbitrary original and Reference coherence follows from the same complete-label action. -/
lemma program_reference_of_flags (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (outcome : Word)
    {Reference : Register} {Index : Type} [Fintype Index] (states : Index → Frame.Raw)
    (reset : ∀ index, assignment.target.value (states index) = Horner.zeroWord)
    (flags : ∀ index, ((Placement.layout assignment).grouping (states index)).1.1.2 = false ∧
      ((Placement.layout assignment).grouping (states index)).1.2.1 = false ∧
        ((Placement.layout assignment).grouping (states index)).1.2.2 = false)
    (admitted : ∀ index, (physicalSelector selection).get (states index) = true →
      Canonical (assignment.source.value (states index)))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (Native.referenceOperator (program assignment selection outcome) environment Reference)
      (Native.referenceVector states reference amplitude) =
      Native.referenceVector states reference (fun index => amplitude index *
        WalshHadamard.walshSign outcome
          (Save.savedWord (assignment.source.value (states index))
            (assignment.multiplier.value (states index))
            ((physicalSelector selection).get (states index)))) := by
  unfold Native.referenceVector
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  have action := reference_ket (program assignment selection outcome) environment _ _
    (program_applyVec_of_flags assignment selection environment (states index) outcome
      (reset index) (flags index) (admitted index)) (reference index)
  exact (congrArg (fun vector => amplitude index • vector) action).trans (smul_smul _ _ _)

end

end Arithmetic.Phase

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
