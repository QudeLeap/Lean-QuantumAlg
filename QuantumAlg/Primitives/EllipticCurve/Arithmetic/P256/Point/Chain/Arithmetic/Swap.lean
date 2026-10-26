/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Swap.Parallel
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Unlookup
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Reference
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Actual numerical A/Y swap in three physical CNOT layers

The numerical bit i of A uses physical position i, whereas the same bit of Y
uses position 580+255-i. This circuit exchanges those numerical bits, even on
the inactive branch, and retains all padding, history, pool, controls and
window address systems. It is separate from the static EEA workspace grouping.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Swap

noncomputable section

open scoped BigOperators

/-- The two original numerical words have certified disjoint complete supports. -/
def frame : EncodedBit.Word.ParallelSwap.Frame Window.encoding 256 where
  left := Window.resultWord .work1
  right := Window.resultWord .numerator
  leftDistinct := Window.resultWord_distinct .work1
  rightDistinct := Window.resultWord_distinct .numerator
  cross first second := by
    intro same
    have positions := congrArg Fin.val same
    rw [Window.resultWord_wire, Window.resultWord_wire] at positions
    have bound := first.isLt
    change first.val = 580 + (255 - second.val) at positions
    omega

def step : Window.Raw → Window.Raw := frame.step

def program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical Window.encoding.width).toQuantum :=
  frame.program (QubitLayout.canonical _) .empty

def ket (state : Window.Raw) :
    NormalizedVector (QubitLayout.canonical Window.encoding.width).toQuantum.register :=
  NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (Window.encoding.encode state))

attribute [local irreducible] EncodedBit.Word.ParallelSwap.Frame.step
  EncodedBit.Word.ParallelSwap.Frame.forward

/-- Every original label, including both coherent selector branches, has this exact action. -/
lemma program_apply (environment : OracleModel.empty.Interpretation) (state : Window.Raw) :
    program.applyNormalized environment (ket state) = ket (step state) :=
  frame.program_apply (QubitLayout.canonical _) .empty environment state

lemma step_work1 (state : Window.Raw) :
    Frame.work1 (step state).1 = Frame.numerator state.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have actual := frame.step_left index state
  change (Window.pointBit (WordPort.bit .work1 index)).get (step state) =
    (Window.pointBit (WordPort.bit .numerator index)).get state at actual
  simpa only [Window.pointBit_get, WordPort.bit_get, WordPort.value] using actual

lemma step_numerator (state : Window.Raw) :
    Frame.numerator (step state).1 = Frame.work1 state.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have actual := frame.step_right index state
  change (Window.pointBit (WordPort.bit .numerator index)).get (step state) =
    (Window.pointBit (WordPort.bit .work1 index)).get state at actual
  simpa only [Window.pointBit_get, WordPort.bit_get, WordPort.value] using actual

/-- All physical positions outside the two numerical payloads are retained without premises. -/
lemma step_other (observed : EncodedBit Window.encoding)
    (outsideA : ∀ index, ((Window.resultWord .work1).bit index).wire ≠ observed.wire)
    (outsideY : ∀ index, ((Window.resultWord .numerator).bit index).wire ≠ observed.wire)
    (state : Window.Raw) : observed.get (step state) = observed.get state :=
  frame.step_other observed outsideA outsideY state

/-- Every original padding/history/pool position, C/N/W and address position is retained. -/
lemma step_outside (observed : EncodedBit Window.encoding)
    (outside : (256 ≤ observed.wire.val ∧ observed.wire.val < 580) ∨
      836 ≤ observed.wire.val) (state : Window.Raw) :
    observed.get (step state) = observed.get state := by
  apply step_other observed
  · intro index same
    have positions := congrArg Fin.val same
    rw [Window.resultWord_wire] at positions
    have bound := index.isLt
    change index.val = observed.wire.val at positions
    omega
  · intro index same
    have positions := congrArg Fin.val same
    rw [Window.resultWord_wire] at positions
    have bound := index.isLt
    change 580 + (255 - index.val) = observed.wire.val at positions
    omega

lemma step_address (index : Fin 15) (state : Window.Raw) :
    (Window.addressBit index).get (step state) = (Window.addressBit index).get state := by
  apply step_outside
  right
  rw [Window.addressBit_wire]
  omega

lemma program_eventTrace :
    program.eventTrace = List.replicate 768 (.gate .cnot) :=
  frame.program_eventTrace (QubitLayout.canonical _) .empty

lemma program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      program.eventCost = 768 :=
  frame.program_cnot_count (QubitLayout.canonical _) .empty

lemma program_quantumTime :
    program.evaluatedEventDepth Resource.Event.quantumDuration = 3 :=
  frame.program_quantumTime (QubitLayout.canonical _) .empty

/-- The actual three-layer frame program keeps arbitrary original and external correlations. -/
lemma program_reference (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (states : Index → Window.Raw)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (UnitaryOperator.prodTensor
      ((frame.program (QubitLayout.canonical _) .empty).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
      (∑ index, amplitude index • (NormalizedVector.ket
        (R := (QubitLayout.canonical Window.encoding.width).toQuantum.register.prod Reference)
        ((QubitLayout.canonical _).basisEquiv.symm (Window.encoding.encode (states index)),
          reference index)).vec) =
      ∑ index, amplitude index • (NormalizedVector.ket
        (R := (QubitLayout.canonical Window.encoding.width).toQuantum.register.prod Reference)
        ((QubitLayout.canonical _).basisEquiv.symm
          (Window.encoding.encode (frame.step (states index))), reference index)).vec :=
  frame.program_reference (QubitLayout.canonical _) .empty environment states reference amplitude

end

end Arithmetic.Swap

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
