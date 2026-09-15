/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Layout.Qubit
public import QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Qubit placement within finite-dimensional layouts

A qubit placement describes exactly the same physical systems when viewed as
a layout whose dimensions are all two. Its old binary labels and the new
coordinate labels agree through the explicit big-endian equivalence below.
This bridge changes the representation of labels, not the state or its space.
-/

namespace QuantumAlg.QubitLayout

/-- Keep every actual identity and assign dimension two to each qubit. -/
@[expose] public def toQuantumLayout {width : Nat} (layout : QubitLayout width) :
    QuantumLayout width :=
  QuantumLayout.uniform width 2 layout.physical_idx layout.physical_idx_injective

/-- Converting the layout neither renames nor adds a physical system. -/
theorem toQuantumLayout_identities {width : Nat} (layout : QubitLayout width) :
    layout.toQuantumLayout.identities = layout.systemIdx := rfl

/-- Converted qubits contribute only to the dimension-two system count. -/
theorem toQuantumLayout_dimensionCount {width : Nat} (layout : QubitLayout width)
    (dimension : ℕ+) :
    layout.toQuantumLayout.dimensionCount dimension =
      if (2 : ℕ+) = dimension then width else 0 :=
  QuantumLayout.dimensionCount_uniform width 2 dimension
    layout.physical_idx layout.physical_idx_injective

/-- The old qubit label is the explicit big-endian encoding of the same wires. -/
def binaryIndexEquiv {width : Nat} (layout : QubitLayout width) :
    layout.toQuantumLayout.register.Index ≃ (Qubits width).Index :=
  BinaryBasis.bigEndianEquiv width

/-- Index transport preserves the value of each selected logical wire. -/
theorem binaryIndexEquiv_bit {width : Nat} (layout : QubitLayout width)
    (basis : layout.toQuantumLayout.register.Index) (index : Fin width) :
    (layout.binaryIndexEquiv basis).val.testBit index.rev.val = finTwoEquiv (basis index) :=
  BinaryBasis.bigEndianEquiv_bit width basis index

end QuantumAlg.QubitLayout
