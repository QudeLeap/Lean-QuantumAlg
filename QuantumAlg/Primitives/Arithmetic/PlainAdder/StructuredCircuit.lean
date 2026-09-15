/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Primitives.Arithmetic.PlainAdder

/-!
# Encoded base-gate plain-adder witnesses

This module records the actual-Circuit interface for a future concrete
X/CNOT/Toffoli plain-adder schedule.  The semantic endpoint in
`QuantumAlg.Primitives.Arithmetic.PlainAdder` already states addition over
`ZMod (2^n)`; a closing structured witness must additionally provide a concrete
`UnitaryCircuit` and a `Realizes` proof for the same encoded object.  The
with-work variant records the clean temporary-register contract used by full
adder networks.  The carry-schedule invariant is intentionally outside this
file and follows the VBE carry/sum/uncompute route with temporary carry work
[VBE95, 9511018.tex:237-264,591-618].
-/

section

namespace QuantumAlg
namespace PlainAdder

noncomputable section

/-- A gate-structured plain-adder witness over an explicit faithful binary
encoding.  The same actual circuit is used for correctness and resource
projection. -/
structure StructuredWitness (n : Nat) where
  /-- Faithful encoding of plain-adder labels. -/
  encoding : BinaryLabelEncoding (Data n)
  /-- Program adding the left word into the right word. -/
  program : UnitaryCircuit (Qubits encoding.width)
  /-- Correctness of the program on encoded plain-adder labels. -/
  realizes :
    UnitaryCircuit.Realizes encoding program Data.addIntoRight

namespace StructuredWitness

variable {n : Nat}

/-- Encoded-basis correctness for all plain-adder labels, intrinsically
preserving normalization. -/
theorem applyNormalized_ket (w : StructuredWitness n) (x : Data n) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x)) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (Data.addIntoRight x)) :=
  w.realizes.apply_encoded_ket x

/-- Ordered strict events derived from the folded adder program. -/
def eventTrace (w : StructuredWitness n) : List (Resource.Event .quantum) :=
  w.program.eventTrace

/-- Strict event pool derived from the folded adder program. -/
def eventCost (w : StructuredWitness n) : ResourcePool .quantum :=
  w.program.eventCost

/-- Strict symbolic event critical path of the folded adder program. -/
def eventDepth (w : StructuredWitness n) :
    DepthExpr (Resource.Event .quantum) :=
  w.program.eventDepth

/-- Literal depth of one strict event coordinate in the adder program. -/
def eventQueryDepth (w : StructuredWitness n)
    (focus : Resource.Event .quantum) : Nat :=
  w.program.eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the adder event pool. -/
def eventGateCount (w : StructuredWitness n)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) w.program.eventCost

/-- Linearizing folded adder event depth recovers its exact strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost (w : StructuredWitness n) :
    w.program.resourcesFromEventDepth = w.program.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.program











end StructuredWitness

/-- A gate-structured plain-adder witness with an explicit clean work register.
The same actual circuit is used for the folded full-register action and for
resource projection; the endpoint theorem is required only on inputs satisfying
the clean-work and clean-carry convention. -/
structure StructuredWithWorkWitness (n : Nat) (Work : Type) where
  /-- Faithful encoding of data plus work labels. -/
  encoding : BinaryLabelEncoding (Data n × Work)
  /-- Distinguished clean work value expected at input and restored at output. -/
  cleanWork : Work
  /-- Folded full-register semantic action of the base-gate program. -/
  step : Data n × Work -> Data n × Work
  /-- Program acting on the encoded data/work layout. -/
  program : UnitaryCircuit (Qubits encoding.width)
  /-- Correctness of the program on encoded data/work labels. -/
  realizes : UnitaryCircuit.Realizes encoding program step
  /-- On clean work and clean carry inputs, the folded action is the plain
  in-place adder and restores the clean work value. -/
  cleanEndpoint :
    ∀ x : Data n, x.CarryClean ->
      step (x, cleanWork) = (Data.addIntoRight x, cleanWork)

namespace StructuredWithWorkWitness

variable {n : Nat} {Work : Type}

/-- Encoded-basis correctness on clean work and clean carry inputs,
intrinsically preserving normalization. -/
theorem applyNormalized_clean_ket (w : StructuredWithWorkWitness n Work) (x : Data n)
    (hcarry : x.CarryClean) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (x, w.cleanWork))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (Data.addIntoRight x, w.cleanWork)) := by
  have h := w.realizes.apply_encoded_ket (x, w.cleanWork)
  simpa [w.cleanEndpoint x hcarry] using h

/-- Ordered strict events derived from the folded data/work adder program. -/
def eventTrace (w : StructuredWithWorkWitness n Work) :
    List (Resource.Event .quantum) :=
  w.program.eventTrace

/-- Strict event pool derived from the folded data/work adder program. -/
def eventCost (w : StructuredWithWorkWitness n Work) : ResourcePool .quantum :=
  w.program.eventCost

/-- Strict symbolic event critical path of the data/work adder program. -/
def eventDepth (w : StructuredWithWorkWitness n Work) :
    DepthExpr (Resource.Event .quantum) :=
  w.program.eventDepth

/-- Literal depth of one strict event coordinate in the data/work program. -/
def eventQueryDepth (w : StructuredWithWorkWitness n Work)
    (focus : Resource.Event .quantum) : Nat :=
  w.program.eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the data/work event pool. -/
def eventGateCount (w : StructuredWithWorkWitness n Work)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) w.program.eventCost

/-- Linearizing data/work event depth recovers its exact strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost
    (w : StructuredWithWorkWitness n Work) :
    w.program.resourcesFromEventDepth = w.program.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.program











end StructuredWithWorkWitness

end

end PlainAdder
end QuantumAlg

end
