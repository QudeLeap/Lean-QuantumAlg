/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
/-!
# Circuit-derived VBE modular-addition resources

This module is a read-only resource view of the concrete fixed-layout programs
in `MAU.Addition.VBECircuit`.  Every value below is projected from the same
circuit object used by the clean semantic endpoint; callers cannot provide a
separate cost or depth package.

The retired Lean policy used a conservative block estimate of five plain-adder
passes, `2 * n` conditional register rewrites, two overflow copies, and `2 * n`
controlled-load operations.  That policy was not an exact gate list.  The v2
results instead count the canonical `(n+1)`-bit adder programs, both concrete
three-CNOT source swaps, the X/CNOT flag stages, and only the set bits actually
present in `N` and in the controlled constant `a`.  Thus ordinary ADD resources
depend on both `n` and `N`, while controlled-ADD resources also depend on `a`.

The registered VBE source supports the route and asymptotic scaling, but not an
exact gate-level constant package.  These exact values are implementation
results derived by Lean, not numerical quotations attributed to the paper.
-/

section

namespace QuantumAlg
namespace MAU.Addition
namespace VBECounting

open VBECircuit

/-! ### General modular ADD -/

/-- The exact circuit whose clean semantics is proved in `VBECircuit`. -/
def addCircuit (n N : Nat) :=
  VBECircuit.modularAddCircuit n N

/-- Strict event pool of the exact ADD circuit. -/
def addEventCost (n N : Nat) : ResourcePool .quantum :=
  (addCircuit n N).eventCost

/-- Strict symbolic event critical path of the exact ADD circuit. -/
def addEventDepth (n N : Nat) : DepthExpr (Resource.Event .quantum) :=
  (addCircuit n N).eventDepth

/-- Exact multiplicity of one literal gate coordinate in the ADD circuit. -/
def addEventGateCount (n N : Nat) (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) (addCircuit n N).eventCost

/-- Exact X-event count in the ADD circuit. -/
def addXEventCount (n N : Nat) : Nat :=
  addEventGateCount n N (.builtin "x")

/-- Exact CNOT-event count in the ADD circuit. -/
def addCNOTEventCount (n N : Nat) : Nat :=
  addEventGateCount n N (.builtin "cnot")

/-- Exact Toffoli-event count in the ADD circuit. -/
def addToffoliEventCount (n N : Nat) : Nat :=
  addEventGateCount n N (.builtin "toffoli")

/-- Exact ADD critical path under literal strict-event durations. -/
def addEvaluatedEventDepth (n N : Nat)
    (assign : Resource.Event .quantum → Nat) : Nat :=
  (addCircuit n N).evaluatedEventDepth assign

/-- Exact ADD depth selected by one literal event coordinate. -/
def addEventQueryDepth (n N : Nat)
    (focus : Resource.Event .quantum) : Nat :=
  (addCircuit n N).eventQueryDepth focus

/-- Critical-path depth of one literal gate coordinate in the ADD circuit. -/
def addEventGateDepth (n N : Nat) (label : Resource.GateLabel) : Nat :=
  addEventQueryDepth n N (.gate label)

/-- Literal Toffoli-event depth of the ADD circuit. -/
def addToffoliEventDepth (n N : Nat) : Nat :=
  addEventGateDepth n N (.builtin "toffoli")

/-- Linearizing ADD event depth recovers the same exact event pool. -/
theorem addResourcesFromEventDepth_eqEventCost (n N : Nat) :
    (addCircuit n N).resourcesFromEventDepth = addEventCost n N :=
  VBECircuit.modularAddCircuit_resourcesFromEventDepth_eq_eventCost n N























/-- Exact fixed-layout footprint, read from the circuit's semantic encoding.
The modulus remains explicit to match the sibling resource projections, while
the fixed encoding makes the result depend only on `n`. -/
@[nolint unusedArguments]
def addQubitCount (n _N : Nat) : Nat :=
  (VBECircuit.encoding n).width

@[simp] theorem addQubitCount_eq (n N : Nat) :
    addQubitCount n N = 4 * n + 4 := by
  change (VBECircuit.encoding n).width = 4 * n + 4
  exact VBECircuit.encoding_width n



/-! ### Doubly controlled modular ADD -/

/-- Exact load/add/unload circuit for the actual constant `a`. -/
def controlledAddCircuit (n N : Nat) (a : PlainAdder.Word n) :=
  VBECircuit.controlledAddCircuit n N a

/-- Strict event pool of the exact controlled-ADD circuit. -/
def controlledAddEventCost (n N : Nat) (a : PlainAdder.Word n) :
    ResourcePool .quantum :=
  (controlledAddCircuit n N a).eventCost

/-- Strict event critical path of the exact controlled-ADD circuit. -/
def controlledAddEventDepth (n N : Nat) (a : PlainAdder.Word n) :
    DepthExpr (Resource.Event .quantum) :=
  (controlledAddCircuit n N a).eventDepth

/-- Exact multiplicity of one literal gate coordinate in controlled ADD. -/
def controlledAddEventGateCount (n N : Nat) (a : PlainAdder.Word n)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) (controlledAddCircuit n N a).eventCost

/-- Exact X-event count in the controlled-ADD circuit. -/
def controlledAddXEventCount (n N : Nat) (a : PlainAdder.Word n) : Nat :=
  controlledAddEventGateCount n N a (.builtin "x")

/-- Exact CNOT-event count in the controlled-ADD circuit. -/
def controlledAddCNOTEventCount (n N : Nat) (a : PlainAdder.Word n) : Nat :=
  controlledAddEventGateCount n N a (.builtin "cnot")

/-- Exact Toffoli-event count in the controlled-ADD circuit. -/
def controlledAddToffoliEventCount (n N : Nat) (a : PlainAdder.Word n) : Nat :=
  controlledAddEventGateCount n N a (.builtin "toffoli")

/-- Evaluated controlled-ADD depth under literal strict-event durations. -/
def controlledAddEvaluatedEventDepth (n N : Nat) (a : PlainAdder.Word n)
    (assign : Resource.Event .quantum → Nat) : Nat :=
  (controlledAddCircuit n N a).evaluatedEventDepth assign

/-- Controlled-ADD depth selected by one literal event coordinate. -/
def controlledAddEventQueryDepth (n N : Nat) (a : PlainAdder.Word n)
    (focus : Resource.Event .quantum) : Nat :=
  (controlledAddCircuit n N a).eventQueryDepth focus

/-- Literal Toffoli-event depth of the controlled-ADD circuit. -/
def controlledAddToffoliEventDepth (n N : Nat)
    (a : PlainAdder.Word n) : Nat :=
  controlledAddEventQueryDepth n N a (.gate (.builtin "toffoli"))

/-- Linearizing controlled-ADD event depth recovers its exact event pool. -/
theorem controlledAddResourcesFromEventDepth_eqEventCost
    (n N : Nat) (a : PlainAdder.Word n) :
    (controlledAddCircuit n N a).resourcesFromEventDepth =
      controlledAddEventCost n N a :=
  VBECircuit.controlledAddCircuit_resourcesFromEventDepth_eq_eventCost n N a























/-- The controlled layout is exactly the arithmetic layout plus two controls.
The modulus and addend remain explicit to match the sibling resource
projections, while the fixed encoding makes the result depend only on `n`. -/
@[nolint unusedArguments]
def controlledAddQubitCount (n _N : Nat) (_a : PlainAdder.Word n) : Nat :=
  (VBECircuit.controlledEncoding n).width

@[simp] theorem controlledAddQubitCount_eq (n N : Nat)
    (a : PlainAdder.Word n) :
    controlledAddQubitCount n N a = 4 * n + 6 := by
  simp [controlledAddQubitCount]



end VBECounting
end MAU.Addition
end QuantumAlg

end
