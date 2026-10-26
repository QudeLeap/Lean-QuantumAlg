/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Save
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State

/-!
# Product saving from complete physical point states

Only the existing target word and three actual arithmetic flags are clean.
The entire original complement, including the remaining pool and metadata,
is retained. The inactive source and multiplier are arbitrary binary words.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Save

noncomputable section

/-- The complete saved state keeps the same physical source, multiplier and complement. -/
def savedState (assignment : PortAssignment) (selection : Selector) (state : Frame.Raw) :
    Frame.Raw :=
  let retained := ((Placement.layout assignment).grouping state).2.2
  Native.arithmeticState assignment (assignment.source.value state)
    (savedWord (assignment.source.value state) (assignment.multiplier.value state)
      ((selectorBit assignment selection).get retained))
    (assignment.multiplier.value state) retained

/-- The actual save program applies to any full state with its real clean target and flags. -/
lemma program_apply_of_flags (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (state : Frame.Raw)
    (targetZero : assignment.target.value state = Horner.zeroWord)
    (flags : ((Placement.layout assignment).grouping state).1.1.2 = false ∧
      ((Placement.layout assignment).grouping state).1.2.1 = false ∧
        ((Placement.layout assignment).grouping state).1.2.2 = false)
    (admitted : (selectorBit assignment selection).get
      ((Placement.layout assignment).grouping state).2.2 = true →
        Canonical (assignment.source.value state)) :
    (program assignment selection).applyNormalized environment (Native.ket state) =
      Native.ket (savedState assignment selection state) := by
  let retained := ((Placement.layout assignment).grouping state).2.2
  have representation : state = Native.arithmeticState assignment
      (assignment.source.value state) Horner.zeroWord (assignment.multiplier.value state)
      retained :=
    (Native.state_eq_arithmeticState_of_flags assignment state flags).trans
      (congrArg (fun target => Native.arithmeticState assignment (assignment.source.value state)
        target (assignment.multiplier.value state) retained) targetZero)
  exact (congrArg (fun original => (program assignment selection).applyNormalized environment
    (Native.ket original)) representation).trans
    (program_apply assignment selection environment (assignment.source.value state)
      (assignment.multiplier.value state) retained admitted)

lemma savedState_source (assignment : PortAssignment) (selection : Selector) (state : Frame.Raw) :
    assignment.source.value (savedState assignment selection state) =
      assignment.source.value state :=
  Native.arithmeticState_source assignment _ _ _ _

lemma savedState_multiplier (assignment : PortAssignment) (selection : Selector)
    (state : Frame.Raw) :
    assignment.multiplier.value (savedState assignment selection state) =
      assignment.multiplier.value state :=
  Native.arithmeticState_multiplier assignment _ _ _ _

lemma savedState_target (assignment : PortAssignment) (selection : Selector) (state : Frame.Raw) :
    assignment.target.value (savedState assignment selection state) =
      savedWord (assignment.source.value state) (assignment.multiplier.value state)
        ((selectorBit assignment selection).get
          ((Placement.layout assignment).grouping state).2.2) :=
  Native.arithmeticState_target assignment _ _ _ _

/-- No original complementary bit is inferred merely from the arithmetic word values. -/
lemma savedState_complement (assignment : PortAssignment) (selection : Selector)
    (observed : EncodedBit Frame.encoding)
    (outside : observed.wire ∉ Set.range (Placement.subsystem assignment).wires)
    (state : Frame.Raw) :
    observed.get (savedState assignment selection state) = observed.get state :=
  (Native.arithmeticState_restBit assignment observed outside _ _ _ _).trans
    (Placement.restBit_get assignment observed outside state)

/-- The same actual circuit retains arbitrary coherence between enabled and disabled labels. -/
lemma program_reference_of_flags (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (states : Index → Frame.Raw)
    (targetZero : ∀ index, assignment.target.value (states index) = Horner.zeroWord)
    (flags : ∀ index, ((Placement.layout assignment).grouping (states index)).1.1.2 = false ∧
      ((Placement.layout assignment).grouping (states index)).1.2.1 = false ∧
        ((Placement.layout assignment).grouping (states index)).1.2.2 = false)
    (admitted : ∀ index, (selectorBit assignment selection).get
      ((Placement.layout assignment).grouping (states index)).2.2 = true →
        Canonical (assignment.source.value (states index)))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (Native.referenceOperator (program assignment selection)
      environment Reference) (Native.referenceVector states reference amplitude) =
      Native.referenceVector (fun index => savedState assignment selection (states index))
        reference amplitude :=
  Native.coherent_of_basis _ environment _ _ (fun index =>
    program_apply_of_flags assignment selection environment (states index)
      (targetZero index) (flags index) (admitted index)) reference amplitude

end

end Arithmetic.Save

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
