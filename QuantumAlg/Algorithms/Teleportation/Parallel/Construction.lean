/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
public import QuantumAlg.Algorithms.Teleportation.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Algorithms.Teleportation.Construction
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Output

/-!
# Native parallel teleportation with actual measured feedback

Alice's CNOT/H words act on disjoint triples. The interpreter then measures
the original two Alice systems of every triple into distinct live cells.
One structural branch reads those cells and selects the disjoint X/Z words
on Bob's original systems [dW19, qcnotes.tex:790,802,804]. Parallel scheduling
occurs only between the native words on disjoint systems; the premeasurement
word and the selected correction remain sequential dependencies.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open Execution

/-- The same native model as the one-block measured protocol. -/
public abbrev model : ExecutionModel := Block.model

/-- Alice's original native words placed on consecutive independent physical triples. -/
public def aliceWord : (count : Nat) →
    UnitaryCircuit AlgorithmGate.model .empty (layout count)
  | 0 => .identity AlgorithmGate.model .empty (layout 0)
  | count + 1 => UnitaryCircuit.parallelBinary Block.aliceWord (aliceWord count)

/-- Bob's selected native corrections on all original final positions of the triples. -/
public def correctionWord : (count : Nat) → (Fin count → Bool × Bool) →
    UnitaryCircuit AlgorithmGate.model .empty (layout count)
  | 0, _ => .identity AlgorithmGate.model .empty (layout 0)
  | count + 1, bits =>
      UnitaryCircuit.parallelBinary (Block.correctionWord (bits 0).1 (bits 0).2)
        (correctionWord count (fun index => bits index.succ))

/-- The branch derives each correction selector from its actual finite stored value. -/
def storedBits {count : Nat} (value : CShape.Value (resultShape count)) :
    Fin count → Bool × Bool := fun index =>
  (decide ((value.get index).first.toFin.val = 1),
    decide ((value.get index).second.toFin.val = 1))

/-- The full native word uses exactly the supplied live quantum layout. -/
def onContext (count : Nat)
    (word : UnitaryCircuit AlgorithmGate.model .empty (layout count)) :
    UnitaryCircuit AlgorithmGate.model .empty (context count).quantumLayout :=
  unitaryOfEqualWires _ _ (context_wires count) word

/-- The selected word reads all real measurement cells before applying Bob's gates. -/
public def selectedCorrection (count : Nat) (value : CShape.Value (resultShape count)) :
    UnitaryCircuit AlgorithmGate.model .empty (context count).quantumLayout :=
  onContext count (correctionWord count (storedBits value))

/-- Actual native gates, actual Z writes, and actual classical feedback in one interpreter. -/
public def code (count : Nat) : Circuit model (context count) (context count) false :=
  .seq (.unitary (onContext count (aliceWord count)))
    (.seq (Circuit.measurementSequence (readouts count))
      (.branch (resultInput count) (fun value => .unitary (selectedCorrection count value))))

/-- Complete output retains every measured system, Bob system, and actual written result. -/
public def algorithm (count : Nat) :
    Algorithm model (context count) (context count) (resultShape count) false where
  run := { code := code count, output := Output.all (context count) (.read (resultInput count)) }

end

end QuantumAlg.QuantumTeleportation.Parallel
