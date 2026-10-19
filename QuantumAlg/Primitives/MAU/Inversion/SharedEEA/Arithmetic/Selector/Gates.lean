/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Selector
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# Literal native instructions of a fixed arithmetic selector

The original equality computation surrounds the existing dirty-controlled TTK
list at its original remainder or coefficient placement. Every predicate mask,
borrowed-Iter cleanup gate and inverse predicate occurs in its original order.
The full input action includes arbitrary incoming Ctrl and arbitrary Iter.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelector

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit GateSpec ArithmeticWindowRegisters ArithmeticWindowProgram
open ArithmeticWindowPreservation ArithmeticSelectionKey

private def bodyGates {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) : List (GateSpec (encoding width)) :=
  if coefficient then
    (ArithmeticWindowControl.gates window operation).map
      (CoefficientWindowProgram.placement window).placeGate
  else
    (ArithmeticWindowControl.gates window operation).map
      (ArithmeticWindowPlacement.placement window).placeGate

private lemma bodyGates_step {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (state : Registers width) :
    stepList (bodyGates window operation coefficient) state =
      controlledBodyStep window operation coefficient state := by
  cases coefficient with
  | false =>
      exact ((ArithmeticWindowPlacement.placement window).placeGates_step
        (ArithmeticWindowControl.gates window operation) state).trans
          (congrArg (ArithmeticWindowPlacement.placement window).grouping.symm
            (ArithmeticWindowControl.gates_step window operation
              ((ArithmeticWindowPlacement.placement window).grouping state)))
  | true =>
      exact ((CoefficientWindowProgram.placement window).placeGates_step
        (ArithmeticWindowControl.gates window operation) state).trans
          (congrArg (CoefficientWindowProgram.placement window).grouping.symm
            (ArithmeticWindowControl.gates_step window operation
              ((CoefficientWindowProgram.placement window).grouping state)))

private lemma bodyGates_trace {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) :
    (bodyGates window operation coefficient).map (event .empty) =
      (ArithmeticWindowControl.gates window operation).map (event .empty) := by
  cases coefficient with
  | false =>
      exact (programList_eventTrace (QubitLayout.canonical _) .empty
        (bodyGates window operation false)).symm.trans
          ((ArithmeticWindowPlacement.placement window).placeGates_eventTrace
            (QubitLayout.canonical _) .empty (ArithmeticWindowControl.gates window operation))
  | true =>
      exact (programList_eventTrace (QubitLayout.canonical _) .empty
        (bodyGates window operation true)).symm.trans
          ((CoefficientWindowProgram.placement window).placeGates_eventTrace
            (QubitLayout.canonical _) .empty (ArithmeticWindowControl.gates window operation))

/-- The original equality, actual selected arithmetic, and inverse equality instructions. -/
def gates {width : Nat} (window : Window width) (operation : Operation) (coefficient : Bool)
    (selected : Key width (readsSign operation)) : List (GateSpec (encoding width)) :=
  ArithmeticSelectionPredicate.gates width (readsSign operation) selected ++
    bodyGates window operation coefficient ++
      (ArithmeticSelectionPredicate.gates width (readsSign operation) selected).reverse

/-- Exact full-frame selector action restores arbitrary Ctrl and borrowed Iter. -/
lemma arithmeticSelector_gates_step {width : Nat} (window : Window width)
    (operation : Operation) (coefficient : Bool)
    (selected : Key width (readsSign operation)) (state : Registers width) :
    stepList (gates window operation coefficient selected) state =
      step window operation coefficient selected state := by
  rw [gates, stepList_append, stepList_append,
    ArithmeticSelectionPredicate.gates_step, bodyGates_step,
    ArithmeticSelectionPredicate.reverse_step]
  exact cleanup window operation coefficient selected state

/-- The actual emitted word has the same complete coherent action on any supplied layout. -/
lemma arithmeticSelector_gates_realizes {width : Nat} (window : Window width)
    (operation : Operation) (coefficient : Bool)
    (selected : Key width (readsSign operation)) (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (gates window operation coefficient selected)) environment
      (step window operation coefficient selected) :=
  realizesList_congrStep layout .empty _
    (arithmeticSelector_gates_step window operation coefficient selected) environment

/-- Every emitted predicate and arithmetic event retains its exact original position. -/
lemma arithmeticSelector_gates_trace {width : Nat} (window : Window width)
    (operation : Operation) (coefficient : Bool) (selected : Key width (readsSign operation)) :
    (gates window operation coefficient selected).map (event .empty) =
      (program window operation coefficient selected).eventTrace := by
  rw [gates, List.map_append, List.map_append, bodyGates_trace, program_eventTrace]

/-- All native event multiplicities are inherited from the original actual selector. -/
lemma arithmeticSelector_gates_eventCost {width : Nat} (window : Window width)
    (operation : Operation) (coefficient : Bool) (selected : Key width (readsSign operation)) :
    ResourcePool.ofList ((gates window operation coefficient selected).map (event .empty)) =
      (program window operation coefficient selected).eventCost := by
  rw [arithmeticSelector_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Both full predicates and every actual dirty-control arithmetic instruction are counted. -/
lemma arithmeticSelector_gates_length {width : Nat} (window : Window width)
    (operation : Operation) (coefficient : Bool) (selected : Key width (readsSign operation)) :
    (gates window operation coefficient selected).length =
      2 * (ArithmeticSelectionPredicate.gates width (readsSign operation) selected).length +
        (ArithmeticWindowControl.gates window operation).length := by
  have count := congrArg List.length
    (arithmeticSelector_gates_trace window operation coefficient selected)
  rw [program_eventTrace] at count
  simp only [List.length_map, List.length_append, List.length_reverse] at count
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelector
