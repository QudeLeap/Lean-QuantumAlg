/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent protocols for complete quantum cycles

The caller specifies its intended completed computations before choosing an
implementation. A single cycle can contain measurement, feedback and reset.
Only an explicitly sequential plan authorizes reporting separate cycles.
These specifications contain no candidate circuit or execution witness.
-/

namespace QuantumAlg

namespace Problem

/-- Both the local caller domain and the joint service initialization must hold. -/
public def Admits {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {shape : CShape} (problem : Problem model pre post shape) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) : Prop :=
  problem.valid input.caller.localState ∧ problem.initialization input.localState

end Problem

/-- The caller's independent cycle protocols, including standalone classical work. -/
public inductive CyclePlan (model : ExecutionModel) :
    (pre post : RuntimeCtx model.kind) → CShape → Type 1 where
  /-- One complete computation, including all of its internal feedback and cleanup. -/
  | cycle {pre post : RuntimeCtx model.kind} {shape : CShape}
      (protocol : Problem model pre post shape) : CyclePlan model pre post shape
  /-- A separately specified section that performs only classical work. -/
  | classical {pre post : RuntimeCtx model.kind} {shape : CShape}
      (protocol : Problem model pre post shape) : CyclePlan model pre post shape
  /-- The caller explicitly requests consecutive completed sections. -/
  | seq {pre mid post : RuntimeCtx model.kind} {leftShape shape : CShape}
      (left : CyclePlan model pre mid leftShape)
      (right : CyclePlan model mid post shape) : CyclePlan model pre post shape

namespace CyclePlan

/-- Entry admissibility is fixed by the first independently stated protocol. -/
@[expose] public def Admits {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (plan : CyclePlan model pre post shape) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) : Prop :=
  match plan with
  | .cycle protocol => protocol.Admits input
  | .classical protocol => protocol.Admits input
  | .seq left _ => left.Admits input

end CyclePlan

/-- The caller owns both the final outcome contract and its intended cycle plan.
An implementation must satisfy both fields of this fixed specification. -/
public structure CycleProblem (model : ExecutionModel)
    (pre post : RuntimeCtx model.kind) (shape : CShape) : Type 1 where
  /-- The independently stated complete algorithm problem. -/
  outcome : Problem model pre post shape
  /-- Its independently stated decomposition into completed computations. -/
  plan : CyclePlan model pre post shape

end QuantumAlg
