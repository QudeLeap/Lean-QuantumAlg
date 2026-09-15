/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Actual positions of the owned and borrowed qubit words

The correspondence follows equality of ordered wire records. Membership in
the borrowed selection is exactly membership in the supplied suffix; no
Hilbert-space cardinality is used to choose a physical correspondence.
-/

namespace QuantumAlg.Execution.OwnedBorrowedQubits

noncomputable section

def positionEquiv (owned borrowed : Nat) :
    Fin (owned + borrowed) ≃ Fin (context owned borrowed).systemCount :=
  Execution.positionsOfEqualWires (wordLayout (owned + borrowed)).toQuantumLayout
    (context owned borrowed).quantumLayout (context_wires owned borrowed)

/-- Each corresponding wire keeps its exact physical identity and binary dimension. -/
theorem position_wire (owned borrowed : Nat) (index : Fin (owned + borrowed)) :
    (context owned borrowed).quantumLayout.wire (positionEquiv owned borrowed index) =
      ({ identity := index.val, dimension := 2 } : QuantumWire) :=
  Execution.wireAtCorrespondingPosition
    (wordLayout (owned + borrowed)).toQuantumLayout
    (context owned borrowed).quantumLayout (context_wires owned borrowed) index

/-- The actual borrowed selection is precisely the supplied suffix of the full word. -/
theorem borrowed_position_iff (owned borrowed : Nat) (index : Fin (owned + borrowed)) :
    positionEquiv owned borrowed index ∈ (context owned borrowed).borrowedSelection ↔
      owned ≤ index.val := by
  rw [RuntimeCtx.mem_borrowedSelection, position_wire, context_borrowedWires]
  change ({ identity := index.val, dimension := 2 } : QuantumWire) ∈
    List.ofFn (fun item : Fin borrowed =>
      ({ identity := owned + item.val, dimension := 2 } : QuantumWire)) ↔ _
  constructor
  · intro member
    obtain ⟨item, same⟩ := List.mem_ofFn.mp member
    have identities := congrArg QuantumWire.identity same
    change owned + item.val = index.val at identities
    omega
  · intro afterOwned
    apply List.mem_ofFn.mpr
    refine ⟨⟨index.val - owned, by omega⟩, ?_⟩
    simp only [Nat.add_sub_of_le afterOwned]

/-- The actual complementary selection is exactly the supplied owned prefix. -/
theorem owned_position_iff (owned borrowed : Nat) (index : Fin (owned + borrowed)) :
    positionEquiv owned borrowed index ∈ (context owned borrowed).borrowedSelectionᶜ ↔
      index.val < owned := by
  rw [Finset.mem_compl, borrowed_position_iff, Nat.not_le]

end

end QuantumAlg.Execution.OwnedBorrowedQubits
