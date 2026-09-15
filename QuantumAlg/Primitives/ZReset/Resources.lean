/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Circuit
public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Base.UnitaryCircuit.Leaf
public import Mathlib.Data.Finset.Lattice.Fold
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Components.QuditShift
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr
import Mathlib.Data.List.Perm.Subperm

/-!
# Exact path resources of measurement followed by stored-value correction

Every path of the same reset circuit contains two native events: its Z
measurement and the declared cyclic shift selected by the recorded classical
read. The finite dispatch is part of the circuit syntax, rather than a separate
`ClassicalOp`. The resulting two-atom depth expression preserves the dependency
from measurement to correction. This convention makes no claim about a physical
controller's latency.

The actual classical result cell and every physical system remain in the live
context. Both resident and auxiliary space therefore equal their input values.
The declared shift is present for every selected value, including zero.

The exact path ledger contains one selected shift. The separate uniform envelope
contains every possible shift coordinate once; it bounds alternatives and does
not describe their joint execution. Its dimension and native duration inputs
are independent of the run being checked.

The state operations underlying these native events are projective measurement
[dW19, qcnotes.tex:5409] and unitary conjugation [dW19, qcnotes.tex:5405]. Their
resource equalities below are derived from this circuit's actual syntax.
-/

namespace QuantumAlg.ZReset

noncomputable section

/-- The finite value recorded by the actual classical branch read. Syntax paths
also record the preceding measurement; execution enforces their consistency. -/
public def readOutcome {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) : Fin (ctx.quantumLayout.wire wire).dimension := by
  change Fin (ctx.quantumLayout.wire wire).dimension ×
    ((value : CShape.Value (.finite (ctx.quantumLayout.wire wire).dimension)) × Unit) at path
  exact path.2.1.toFin

/-- The circuit path recording one measurement result and the same stored-value read. -/
public def pathFor {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) : (circuit wire output).Path :=
  (outcome, ⟨.finite outcome, ()⟩)

/-- A consistent measurement-and-read record selects its recorded outcome. -/
public theorem zReset_readOutcome_pathFor {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) :
    readOutcome wire output (pathFor wire output outcome) = outcome := by
  rfl

/-- Exact ordered native events, indexed by the branch's recorded classical read. -/
public theorem zReset_eventTrace {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    (circuit wire output).eventTrace path =
      [.measurement
          { family := "builtin"
            name := "z"
            parameters := [(ctx.quantumLayout.wire wire).dimension] },
        .gate (.builtin "qudit-cyclic-shift"
          [(ctx.quantumLayout.wire wire).dimension, (-(readOutcome wire output path)).val])] := by
  change [Circuit.zEvent (ctx.quantumLayout.wire wire).dimension] ++
    (QuditShift.program ctx.quantumLayout wire (-(readOutcome wire output path))).eventTrace = _
  rw [QuditShift.program_eventTrace]
  rfl

/-- The actual ledger contains exactly the two events of the actual ordered trace. -/
public theorem zReset_resourcePool {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    (circuit wire output).resourcePool path =
      (([.measurement
            { family := "builtin"
              name := "z"
              parameters := [(ctx.quantumLayout.wire wire).dimension] },
          .gate (.builtin "qudit-cyclic-shift"
            [(ctx.quantumLayout.wire wire).dimension, (-(readOutcome wire output path)).val])] :
        List (Resource.Event .quantum)) : ResourcePool .quantum) := by
  exact congrArg ResourcePool.ofList (zReset_eventTrace wire output path)

/-- Every path executes two native events, including the zero-outcome correction. -/
public theorem zReset_eventTrace_length {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    ((circuit wire output).eventTrace path).length = 2 := by
  rw [zReset_eventTrace]
  rfl

/-- Measurement and correction each visit the unchanged complete live context. -/
public theorem zReset_visitedContexts {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    (circuit wire output).visitedContexts path = [ctx, ctx] := by
  rfl

/-- Resident peak includes the existing result cell and every existing physical system. -/
public theorem zReset_peakResidentSpace {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    (circuit wire output).peakResidentSpace path = ctx.residentSpace := by
  unfold Circuit.peakResidentSpace
  rw [zReset_visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, SpacePool.max_zero, SpacePool.max_self]

/-- Auxiliary peak follows the unchanged roles of those same live entries. -/
public theorem zReset_peakAuxiliarySpace {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    (circuit wire output).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  unfold Circuit.peakAuxiliarySpace
  rw [zReset_visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, SpacePool.max_zero, SpacePool.max_self]

/-- The exact native dependency is measurement followed by the selected declared shift. -/
public theorem zReset_eventDepth {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    (circuit wire output).eventDepth path =
      .seq (.atom (.measurement
          { family := "builtin"
            name := "z"
            parameters := [(ctx.quantumLayout.wire wire).dimension] }))
        (.atom (.gate (.builtin "qudit-cyclic-shift"
          [(ctx.quantumLayout.wire wire).dimension, (-(readOutcome wire output path)).val]))) := by
  change DepthExpr.seq (.atom (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension))
    (QuditShift.program ctx.quantumLayout wire (-(readOutcome wire output path))).eventDepth = _
  rw [QuditShift.program_eventDepth]
  rfl

/-- Durations add along the actual measurement-to-correction dependency. -/
public theorem zReset_depth {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (duration : Resource.Event .quantum → Nat) (path : (circuit wire output).Path) :
    (circuit wire output).depth duration path =
      duration (.measurement
          { family := "builtin"
            name := "z"
            parameters := [(ctx.quantumLayout.wire wire).dimension] }) +
        duration (.gate (.builtin "qudit-cyclic-shift"
          [(ctx.quantumLayout.wire wire).dimension, (-(readOutcome wire output path)).val])) := by
  unfold Circuit.depth
  rw [zReset_eventDepth]
  rfl

/-- Unit durations give depth two on every path, including the declared zero shift. -/
public theorem zReset_unitDepth {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    (circuit wire output).depth (fun _ => 1) path = 2 := by
  rw [zReset_depth]

/-- A dimension-only event budget: one Z event and one copy of every possible
correction coordinate. A single path uses only one of those alternatives. -/
public def eventEnvelope (dimension : ℕ+) : ResourcePool .quantum :=
  ((.measurement { family := "builtin", name := "z", parameters := [dimension] } ::
    List.ofFn (fun outcome : Fin dimension =>
      Resource.Event.gate (.builtin "qudit-cyclic-shift" [dimension, (-outcome).val]))) :
    List (Resource.Event .quantum))

/-- Every actual path is bounded by the independent dimension-indexed event envelope. -/
public theorem zReset_resourcePool_le_envelope {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (circuit wire output).Path) :
    (circuit wire output).resourcePool path ≤
      eventEnvelope (ctx.quantumLayout.wire wire).dimension := by
  rw [zReset_resourcePool]
  unfold eventEnvelope
  apply Multiset.coe_le.mpr
  apply List.Sublist.subperm
  apply List.Sublist.cons_cons
  apply List.singleton_sublist.mpr
  exact List.mem_ofFn.mpr ⟨readOutcome wire output path, rfl⟩

/-- A dimension-only depth budget using the largest possible declared shift duration. -/
public def depthEnvelope (dimension : ℕ+) (duration : Resource.Event .quantum → Nat) : Nat :=
  duration (.measurement { family := "builtin", name := "z", parameters := [dimension] }) +
    Finset.univ.sup (fun outcome : Fin dimension =>
      duration (.gate (.builtin "qudit-cyclic-shift" [dimension, (-outcome).val])))

/-- Each actual path has at most the maximum duration of its possible correction. -/
public theorem zReset_depth_le_envelope {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (duration : Resource.Event .quantum → Nat) (path : (circuit wire output).Path) :
    (circuit wire output).depth duration path ≤
      depthEnvelope (ctx.quantumLayout.wire wire).dimension duration := by
  rw [zReset_depth]
  unfold depthEnvelope
  apply Nat.add_le_add_left
  exact Finset.le_sup
    (f := fun outcome : Fin (ctx.quantumLayout.wire wire).dimension =>
      duration (.gate (.builtin "qudit-cyclic-shift"
        [(ctx.quantumLayout.wire wire).dimension, (-outcome).val])))
    (Finset.mem_univ (readOutcome wire output path))

end

end QuantumAlg.ZReset
