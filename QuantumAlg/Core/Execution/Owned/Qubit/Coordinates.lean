/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.Qubits

/-!
# Actual finite wire coordinates of a supplied owned qubit word

The existing owned-word basis map follows equality of the actual ordered
wire records. These equations expose each corresponding physical identity,
dimension and basis value for single-wire operations such as Z measurement.
No extra system or new input condition is introduced.
-/

namespace QuantumAlg.Execution.OwnedQubits

noncomputable section

/-- Each supplied physical word position corresponds to its actual live context position. -/
def wireEquiv (width : Nat) : Fin width ≃ Fin (context width).systemCount :=
  positionsOfEqualWires (layout width) (context width).quantumLayout (layout_wires width)

/-- The corresponding context wire has precisely the original identity and dimension two. -/
theorem ownedQubits_wire (width : Nat) (index : Fin width) :
    (context width).quantumLayout.wire (wireEquiv width index) =
      ({ identity := index.val, dimension := 2 } : QuantumWire) :=
  wireAtCorrespondingPosition (layout width) (context width).quantumLayout
    (layout_wires width) index

theorem ownedQubits_wire_identity (width : Nat) (index : Fin width) :
    ((context width).quantumLayout.wire (wireEquiv width index)).identity = index.val :=
  congrArg QuantumWire.identity (ownedQubits_wire width index)

theorem ownedQubits_wire_dimension (width : Nat) (index : Fin width) :
    ((context width).quantumLayout.wire (wireEquiv width index)).dimension = 2 :=
  congrArg QuantumWire.dimension (ownedQubits_wire width index)

/-- The complete binary label reads the same finite value as its actual corresponding wire. -/
theorem ownedQubits_basis_value (width : Nat) (state : (context width).register.Index)
    (index : Fin width) :
    (state (wireEquiv width index)).val =
      (finTwoEquiv.symm ((basisEquiv width state).val.testBit index.rev.val)).val := by
  let raw := (basisOfEqualWires (layout width) (context width).quantumLayout
    (layout_wires width)).symm state
  have stored := basisOfEqualWires_value (layout width) (context width).quantumLayout
    (layout_wires width) raw index
  change ((basisOfEqualWires (layout width) (context width).quantumLayout (layout_wires width))
    ((basisOfEqualWires (layout width) (context width).quantumLayout (layout_wires width)).symm
      state) (wireEquiv width index)).val = (raw index).val at stored
  rw [Equiv.apply_symm_apply] at stored
  have bit : (basisEquiv width state).val.testBit index.rev.val = finTwoEquiv (raw index) :=
    (qubitLayout width).binaryIndexEquiv_bit raw index
  rw [bit]
  exact stored.trans (congrArg (fun value : Fin 2 => value.val)
    (finTwoEquiv.symm_apply_apply (raw index))).symm

end

end QuantumAlg.Execution.OwnedQubits
