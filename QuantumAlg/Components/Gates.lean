/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Operator
public import QuantumAlg.Components.Kets.Decomposition
public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.Gates.SingleQubit.Entries
public import QuantumAlg.Components.Gates.PhaseOperator
public import QuantumAlg.Components.Gates.ControlledPhase.Operator
public import QuantumAlg.Components.Gates.ControlledPhase.Physical
public import QuantumAlg.Components.Gates.Swap.Operator
public import QuantumAlg.Components.Gates.Swap.Physical
public import QuantumAlg.Components.Gates.Hadamard.Operator
public import QuantumAlg.Components.Gates.StatePreparation
public import QuantumAlg.Components.Gates.Rotation.Operator
public import QuantumAlg.Components.Gates.Signal.Operator
public import QuantumAlg.Components.Gates.Swap.Register

/-!
# Named operators and actual native gate constructions

Mathematical operators carry no execution capability. The default physical
constructors use the declared Toffoli, CNOT and arbitrary single-qubit model;
controlled phases and SWAPs retain their actual native decompositions.
Other native alphabets require their own explicit model and implementations.
-/
