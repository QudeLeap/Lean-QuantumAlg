/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Finite sequences of actual single-wire Z measurements

Each item names one physical wire and an existing classical cell of exactly
that wire's finite dimension. The sequence is built only from the existing
measurement, sequential composition and identity instructions. Its execution,
finite paths, events and live contexts are those of the single interpreter.

The empty list performs no measurement. Repeated wires or output cells are
allowed at this construction layer; their actual order determines later
stored values. Projective outcomes retain all quantum systems and their
conditional state [dW19, qcnotes.tex:5409,5420].
-/

namespace QuantumAlg

/-- One actual wire and the live cell that receives its finite Z outcome. -/
structure ZReadout (ctx : RuntimeCtx .quantum) where
  wire : Fin ctx.systemCount
  output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)

namespace Circuit

variable {ctx : RuntimeCtx .quantum}

/-- Execute the named single-wire measurements in their stated order. -/
@[implicit_reducible]
def measurementSequence : List (ZReadout ctx) → Circuit ctx ctx
  | [] => .id ctx
  | head :: tail => .seq (.measureZ head.wire head.output) (measurementSequence tail)

/-- The actual finite path read from one complete physical basis label. -/
def measurementBasisPath : (readouts : List (ZReadout ctx)) →
    ctx.register.Index → (measurementSequence readouts).Path
  | [], _basis => ()
  | head :: tail, basis => (basis head.wire, measurementBasisPath tail basis)

/-- The classical writes made by the outcomes on an actual measurement path. -/
def writeMeasurementPath : (readouts : List (ZReadout ctx)) → Execution.Store ctx →
    (measurementSequence readouts).Path → Execution.Store ctx
  | [], store, _path => store
  | head :: tail, store, path =>
      writeMeasurementPath tail (store.write head.output (.finite path.1)) path.2

/-- The empty measurement sequence emits no native operation. -/
theorem measurementSequence_nil_eventTrace
    (path : (measurementSequence ([] : List (ZReadout ctx))).Path) :
    (measurementSequence []).eventTrace path = [] := rfl

/-- Every list item emits exactly its native dimension-indexed Z coordinate. -/
theorem measurementSequence_eventTrace (readouts : List (ZReadout ctx))
    (path : (measurementSequence readouts).Path) :
    (measurementSequence readouts).eventTrace path =
      readouts.map (fun item => zEvent (ctx.quantumLayout.wire item.wire).dimension) := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change [zEvent (ctx.quantumLayout.wire head.wire).dimension] ++
        (measurementSequence tail).eventTrace path.2 = _
      rw [ih]
      rfl

/-- The native pool is the multiplicity projection of those same measured wires. -/
theorem measurementSequence_resourcePool (readouts : List (ZReadout ctx))
    (path : (measurementSequence readouts).Path) :
    (measurementSequence readouts).resourcePool path =
      ResourcePool.ofList
        (readouts.map (fun item => zEvent (ctx.quantumLayout.wire item.wire).dimension)) := by
  unfold resourcePool
  rw [measurementSequence_eventTrace]

/-- Measuring a list of dimension-two wires costs exactly one Z event per item. -/
theorem measurementSequence_qubit_resourcePool (readouts : List (ZReadout ctx))
    (qubits : ∀ item ∈ readouts, (ctx.quantumLayout.wire item.wire).dimension = 2)
    (path : (measurementSequence readouts).Path) :
    (measurementSequence readouts).resourcePool path =
      readouts.length • ResourcePool.singleton (zEvent 2) := by
  rw [measurementSequence_resourcePool]
  have same : readouts.map (fun item => zEvent (ctx.quantumLayout.wire item.wire).dimension) =
      List.replicate readouts.length (zEvent 2) := by
    induction readouts with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.length_cons, List.replicate_succ]
        rw [qubits head (.head _),
          ih (fun item present => qubits item (.tail head present)) path.2]
  rw [same, ResourcePool.ofList_replicate, ResourcePool.scale]

/-- Every instruction, including the final identity, keeps the same live context. -/
theorem measurementSequence_visitedContexts (readouts : List (ZReadout ctx))
    (path : (measurementSequence readouts).Path) :
    (measurementSequence readouts).visitedContexts path =
      List.replicate (readouts.length + 1) ctx := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change [ctx] ++ (measurementSequence tail).visitedContexts path.2 = _
      rw [ih]
      rfl

/-- Sequential measurement depth is the sum of the actual single-wire event durations. -/
theorem measurementSequence_depth (readouts : List (ZReadout ctx))
    (duration : Resource.Event .quantum → Nat) (path : (measurementSequence readouts).Path) :
    (measurementSequence readouts).depth duration path =
      (readouts.map
        (fun item => duration (zEvent (ctx.quantumLayout.wire item.wire).dimension))).sum := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change duration (zEvent (ctx.quantumLayout.wire head.wire).dimension) +
        (measurementSequence tail).depth duration path.2 = _
      rw [ih]
      rfl

/-- Unit duration charges every sequentially executed measurement, including the empty case. -/
theorem measurementSequence_unitDepth (readouts : List (ZReadout ctx))
    (path : (measurementSequence readouts).Path) :
    (measurementSequence readouts).depth (fun _ => 1) path = readouts.length := by
  rw [measurementSequence_depth]
  simp

end Circuit

end QuantumAlg
