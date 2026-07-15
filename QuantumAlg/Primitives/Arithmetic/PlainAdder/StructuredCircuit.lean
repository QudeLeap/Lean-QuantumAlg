/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.BaseGateRealization
public import QuantumAlg.Primitives.Arithmetic.PlainAdder

/-!
# Encoded base-gate plain-adder witnesses

This module records the same-Circuit interface for a future concrete
X/CNOT/Toffoli plain-adder schedule.  The semantic endpoint in
`QuantumAlg.Primitives.Arithmetic.PlainAdder` already states addition over
`ZMod (2^n)`; a closing structured witness must additionally provide a concrete
`BaseGateProgram` and a `Realizes` proof for the same encoded object.  The
with-work variant records the clean temporary-register contract used by full
adder networks.  The carry-schedule invariant is intentionally outside this
file and follows the VBE carry/sum/uncompute route with temporary carry work
[VBE95, 9511018.tex:237-264,591-618].
-/

@[expose] public section

namespace QuantumAlg
namespace PlainAdder

noncomputable section

/-- A gate-structured plain-adder witness over an explicit faithful binary
encoding.  The same `BaseGateProgram` is used for correctness and resource
projection. -/
structure StructuredWitness (n : Nat) where
  /-- Faithful encoding of plain-adder labels. -/
  encoding : BinaryLabelEncoding (Data n)
  /-- Program adding the left word into the right word. -/
  program : BaseGateProgram encoding.width
  /-- Correctness of the program on encoded plain-adder labels. -/
  realizes :
    BaseGateProgram.Realizes encoding program Data.addIntoRight

namespace StructuredWitness

variable {n : Nat}

/-- Same-Circuit witness induced by the structured plain-adder program. -/
def sameCircuit (w : StructuredWitness n) :
    BaseGateSameCircuitWitness (Data n) Data.addIntoRight where
  encoding := w.encoding
  program := w.program
  realizes := w.realizes

/-- The folded plain-adder circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : StructuredWitness n) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.sameCircuit

/-- Encoded-basis correctness for all plain-adder labels. -/
theorem apply_ket (w : StructuredWitness n) (x : Data n) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (Data.addIntoRight x)) :
        StateVector (Qubits w.encoding.width)) :=
  BaseGateSameCircuitWitness.apply_encoded_ket w.sameCircuit x

/-- Resource counters are projected from the same folded base-gate program. -/
theorem resources_eq (w : StructuredWitness n) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.sameCircuit

/-- Circuit depth is projected from the same folded base-gate program. -/
theorem depth_eq (w : StructuredWitness n) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.sameCircuit

/-- Query depth is projected from the same folded base-gate program. -/
theorem queryDepth_eq (w : StructuredWitness n) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.sameCircuit

end StructuredWitness

/-- A gate-structured plain-adder witness with an explicit clean work register.
The same `BaseGateProgram` is used for the folded full-register action and for
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
  program : BaseGateProgram encoding.width
  /-- Correctness of the program on encoded data/work labels. -/
  realizes : BaseGateProgram.Realizes encoding program step
  /-- On clean work and clean carry inputs, the folded action is the plain
  in-place adder and restores the clean work value. -/
  cleanEndpoint :
    ∀ x : Data n, x.CarryClean ->
      step (x, cleanWork) = (Data.addIntoRight x, cleanWork)

namespace StructuredWithWorkWitness

variable {n : Nat} {Work : Type}

/-- Same-Circuit witness induced by the structured data/work program. -/
def sameCircuit (w : StructuredWithWorkWitness n Work) :
    BaseGateSameCircuitWitness (Data n × Work) w.step where
  encoding := w.encoding
  program := w.program
  realizes := w.realizes

/-- The folded data/work circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : StructuredWithWorkWitness n Work) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.sameCircuit

/-- Encoded-basis correctness on clean work and clean carry inputs. -/
theorem apply_clean_ket (w : StructuredWithWorkWitness n Work) (x : Data n)
    (hcarry : x.CarryClean) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.sameCircuit)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (x, w.cleanWork)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (Data.addIntoRight x, w.cleanWork)) :
        StateVector (Qubits w.encoding.width)) := by
  have h :=
    BaseGateSameCircuitWitness.apply_encoded_ket w.sameCircuit (x, w.cleanWork)
  simpa [sameCircuit, w.cleanEndpoint x hcarry] using h

/-- Resource counters are projected from the same folded data/work program. -/
theorem resources_eq (w : StructuredWithWorkWitness n Work) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).resources =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.sameCircuit

/-- Circuit depth is projected from the same folded data/work program. -/
theorem depth_eq (w : StructuredWithWorkWitness n Work) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).depth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.sameCircuit

/-- Query depth is projected from the same folded data/work program. -/
theorem queryDepth_eq (w : StructuredWithWorkWitness n Work) :
    (BaseGateSameCircuitWitness.circuit w.sameCircuit).queryDepth =
      (BaseGateSameCircuitWitness.profile w.sameCircuit).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.sameCircuit

end StructuredWithWorkWitness

end

end PlainAdder
end QuantumAlg
