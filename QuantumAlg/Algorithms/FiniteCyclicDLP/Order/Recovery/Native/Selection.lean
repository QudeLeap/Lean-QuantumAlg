/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt
public import QuantumAlg.Components.Classical.FirstAccepted.Circuit
public import QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# First verified candidate from an actual sample batch

Every retained sample executes complete raw recovery and abstract group
verification.  The selector stores the first accepted candidate while later
attempts still execute and remain fully accounted.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {oracles : OracleModel}
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- Selector cells in the order expected by the existing first-accepted machine. -/
public def selectorShapes (width : Nat) : List CShape :=
  [.bit, .bit, .unsignedWord width, .bit]

/-- Name the actual first-accepted selector cells. -/
public def selectorRefs {width : Nat} (cells : Cells ctx (selectorShapes width)) :
    FirstAccepted.Refs ctx width where
  accepted := cells.tail.tail.tail.head.ref
  selected := cells.tail.tail.head.ref
  available := cells.tail.head.ref
  take := cells.head.ref

/-- Preserve selector destinations through one attempt scope. -/
public def liftSelector {width : Nat} {inner : RuntimeCtx .quantum}
    (refs : FirstAccepted.Refs ctx width) (transport : Transport ctx inner) :
    FirstAccepted.Refs inner width where
  accepted := transport.liftWrite refs.accepted
  selected := transport.liftWrite refs.selected
  available := transport.liftWrite refs.available
  take := transport.liftWrite refs.take

/-- Recover and verify one sample before updating the first-success selector. -/
@[expose] public def selectAttempt
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P)) :
    Circuit (recoveryModel P oracles) ctx ctx :=
  withAttempt (oracles := oracles) P spec input fun candidate accepted transport =>
    FirstAccepted.circuit ⟨accepted, candidate⟩ (liftSelector refs transport)

/-- Process every retained sample in chronological order. -/
@[expose] public def selectionLoop
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P)) :
    Circuit (recoveryModel P oracles) ctx ctx :=
  Circuit.forRange count fun index => selectAttempt (oracles := oracles) P spec (samples index) refs

/-- Pack the selector's final flag and word into the retained optional output. -/
public def selectionPack {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width))) :
    ClassicalOp (.product .bit (.unsignedWord width))
      (.option (.unsignedWord width)) ctx ctx :=
  .packOption ctx
    (.product (FirstAccepted.cellRead refs.accepted)
      (FirstAccepted.cellRead refs.selected))
    output

/-- Complete selection followed by one actual optional-result pack. -/
@[expose] public def recoveryBody
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (output : CWriteRef ctx (.option (.unsignedWord (OrderPreparation.width P)))) :
    Circuit (recoveryModel P oracles) ctx ctx :=
  .seq (selectionLoop (oracles := oracles) P spec count samples refs)
    (BitWord.instruction (execution := recoveryModel P oracles) (selectionPack refs output))

/-- Allocate one selector around the complete recovery of an existing sample batch. -/
@[expose] public def recoveryInto
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (output : CWriteRef ctx (.option (.unsignedWord (OrderPreparation.width P)))) :
    Circuit (recoveryModel P oracles) ctx ctx :=
  withCells (model := recoveryModel P oracles) ctx
      (selectorShapes (OrderPreparation.width P)) fun cells _ transport _ =>
    recoveryBody (oracles := oracles) P spec count (fun index => transport.liftInput (samples
      index))
      (selectorRefs cells) (transport.liftWrite output)

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
