/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine
import all QuantumAlg.Components.Classical.NumberTheory.Representation
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Original five-instruction public XGCD result packing

One shared public-width raw word is reused for the two coefficient resizes.
Each coefficient is packed into its own actual signed cell before the final
right-nested result pack. The original three lexical scratch cells enclose
exactly these five operations; no decoded result is substituted for execution.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original raw narrowing word and two distinct signed coefficient cells. -/
def packingShapes (width : Nat) : List CShape :=
  [.unsignedWord (coefficientWidth width),
    SignedShape (coefficientWidth width), SignedShape (coefficientWidth width)]

/-- The original five actual instructions, including both signed nominal boundaries. -/
def packingBody (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) : Circuit ctx ctx :=
  .seq (.classical (.wordResize (PureXGCD.executionCoefficientWidth width)
    (coefficientWidth width) ctx (GCD.cellRead outputs.leftCoefficient) raw))
    (.seq (.classical (.packBoundedSignedWord (coefficientWidth width) ctx
      (GCD.cellRead raw) left))
      (.seq (.classical (.wordResize (PureXGCD.executionCoefficientWidth width)
        (coefficientWidth width) ctx (GCD.cellRead outputs.rightCoefficient) raw))
        (.seq (.classical (.packBoundedSignedWord (coefficientWidth width) ctx
          (GCD.cellRead raw) right))
          (.classical (.packProduct ctx
            (.product (GCD.cellRead outputs.gcd)
              (.product (GCD.cellRead left) (GCD.cellRead right))) result)))))

/-- The literal actual five-operation store transformation. -/
def packingBodyStore (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (store : Store ctx) : Store ctx :=
  ((((store.applyOp (.wordResize (PureXGCD.executionCoefficientWidth width)
    (coefficientWidth width) ctx (GCD.cellRead outputs.leftCoefficient) raw)).applyOp
      (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) left)).applyOp
      (.wordResize (PureXGCD.executionCoefficientWidth width)
        (coefficientWidth width) ctx (GCD.cellRead outputs.rightCoefficient) raw)).applyOp
      (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) right)).applyOp
      (.packProduct ctx (.product (GCD.cellRead outputs.gcd)
        (.product (GCD.cellRead left) (GCD.cellRead right))) result)

/-- Every full quantum-reference block retains the actual store and all five instruction paths. -/
theorem xgcdNativePackingBody_execute (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (packingBody outputs raw left right result).execute Reference state =
      state.mapClassical (fun entry =>
        (packingBodyStore outputs raw left right result entry.1,
          (entry.2, ((), ((), ((), ((), ()))))))) := by
  simp only [packingBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Allocate the original three packing cells and return the actual public result destination. -/
def packRawOutputs (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width)) : Circuit ctx ctx :=
  withCells ctx (packingShapes width) fun cells _ transport _ =>
    packingBody (outputs.transport transport) cells.head.ref cells.tail.head.ref
      cells.tail.tail.head.ref (transport.liftWrite result)

/-- The original two resizes, two signed packs and one right-nested product pack. -/
def packingEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation
      (.wordResize (PureXGCD.executionCoefficientWidth width) (coefficientWidth width)),
    .classicalOperation (.nominalEncoding (.packBoundedSignedWord (coefficientWidth width))),
    .classicalOperation
      (.wordResize (PureXGCD.executionCoefficientWidth width) (coefficientWidth width)),
    .classicalOperation (.nominalEncoding (.packBoundedSignedWord (coefficientWidth width))),
    .classicalOperation (.nominalEncoding
      (.packProduct width (coefficientWidth width + coefficientWidth width)))]

/-- Original actual event list before the scratch scopes are released. -/
theorem xgcdNativePackingBody_eventTrace (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packingBody outputs raw left right result).Path) :
    (packingBody outputs raw left right result).eventTrace path = packingEvents kind width := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
