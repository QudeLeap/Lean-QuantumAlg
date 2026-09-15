/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement

/-!
# Exact placed basis actions on an admitted input

A native circuit may have an arithmetic specification only on its
original valid input domain. Transport its proved basis equation through
the existing full placement without requiring that specification on
unreachable labels or discarding any complementary physical coordinate.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Target : Type}
variable {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}

/-- Transport an exact admitted-input native equation through the same full physical placement. -/
theorem place_ket_of_eq (layout : FullPlacement source target)
    (body : UnitaryCircuit (Qubits source.width))
    (within : body.physical_idx ⊆ List.range source.width)
    (initial final : Source)
    (actual : body.applyNormalized
      (NormalizedVector.ket (R := Qubits source.width) (source.encode initial)) =
        NormalizedVector.ket (R := Qubits source.width) (source.encode final)) :
    (layout.place body within).applyNormalized
      (NormalizedVector.ket (R := Qubits target.width)
        (target.encode (layout.grouping.symm initial))) =
      NormalizedVector.ket (R := Qubits target.width)
        (target.encode (layout.grouping.symm final)) := by
  have transported := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (R := Qubits source.width) (S := Qubits target.width) layout.basis body _ _ actual
  have inputEncoding : layout.basis (source.encode initial) =
      target.encode (layout.grouping.symm initial) := by
    simpa only [Equiv.apply_symm_apply] using layout.basis_encode (layout.grouping.symm initial)
  have outputEncoding : layout.basis (source.encode final) =
      target.encode (layout.grouping.symm final) := by
    simpa only [Equiv.apply_symm_apply] using layout.basis_encode (layout.grouping.symm final)
  rw [inputEncoding, outputEncoding] at transported
  rw [place, UnitaryCircuit.applyNormalized_seq, UnitaryCircuit.applyNormalized_identity,
    addressed, UnitaryCircuit.Realizes.applyNormalized_relabel]
  exact transported

end

end QuantumAlg.EncodedBit.FullPlacement
