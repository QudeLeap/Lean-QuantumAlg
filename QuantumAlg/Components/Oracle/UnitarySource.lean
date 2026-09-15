/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf

/-!
# Access to a supplied unitary

The declaration owns one opaque unitary-query coordinate and its supplied
certified operator. Structural control derives the controlled coordinate
from the same query. This is the access model used by the Hadamard test
[AJL06, qf2.tex:625-645]; it does not attach synthesized gate counts to an
arbitrary matrix.
-/

namespace QuantumAlg.UnitarySource

noncomputable section

/-- Declaration-owned source-query label, parameterized by its system width. -/
public def label (width : Nat) : Resource.SubroutineLabel :=
  { family := "unitary-source", name := "unitary", parameters := [width] }

/-- Native coordinate of one source query. -/
public def event (width : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (label width).quantum

/-- Native coordinate obtained by adding an actual dimension-two control. -/
public def controlledEvent (width : Nat) : Resource.Event .quantum :=
  (event width).controlForDimension 2

/-- One source-unitary declaration at caller-supplied physical systems. -/
def leafAt {width : Nat} (unitary : UnitaryOperator (Qubits width)) (systems : List Nat) :
    UnitaryLeaf (Qubits width) :=
  UnitaryLeaf.subroutine (label width) systems unitary

/-- The source query on its complete canonical physical input word. -/
def program {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    UnitaryCircuit (Qubits width) :=
  UnitaryCircuit.ofLeaf (leafAt unitary (List.range width)) List.nodup_range

theorem program_matrix {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (program unitary).matrix = unitary := rfl

theorem program_physicalIdx {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (program unitary).physical_idx = List.range width := rfl

theorem program_eventTrace {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (program unitary).eventTrace = [event width] := rfl

theorem program_eventCost {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (program unitary).eventCost = ResourcePool.singleton (event width) := rfl

end

end QuantumAlg.UnitarySource
