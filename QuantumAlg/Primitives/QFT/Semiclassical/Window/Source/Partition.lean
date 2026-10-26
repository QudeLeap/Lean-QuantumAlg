/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Selection

/-!
# Selected blocks in a single mathematical binary source

An arbitrary injection selects coordinates of the same finite binary label.
The complementary register records every other source coordinate. These
layouts describe the mathematical observation space only; no physical bank,
Circuit, allocation, permutation instruction or resource assertion is made.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

variable {full active : Nat}

/-- A canonical coordinate layout for a mathematical binary source label. -/
def labelLayout (full : Nat) : QuantumLayout full :=
  (QuantumSignature.qubits full).canonicalPlacement.layout

/-- The selected mathematical source coordinates keep their original position and value. -/
def labelSelectedLayout (positions : Fin active ↪ Fin full) : QuantumLayout active where
  wire := fun index => (labelLayout full).wire (positions index)
  identityInjective := fun _ _ same =>
    positions.injective ((labelLayout full).identityInjective same)

/-- The block is selected from those same mathematical coordinates. -/
def labelEmbedding (positions : Fin active ↪ Fin full) :
    QuantumLayout.Embedding (labelSelectedLayout positions) (labelLayout full) where
  position := positions
  wire_eq := fun _ => rfl

/-- Every mathematical source coordinate outside the selected block remains explicit. -/
def labelRemainder (positions : Fin active ↪ Fin full) : Register :=
  (labelLayout full).complementRegister (labelEmbedding positions).selection

private def selectedPlacement (positions : Fin active ↪ Fin full) :
    QuantumSignature.Placement (QuantumSignature.qubits active) where
  layout := labelSelectedLayout positions
  dimension_eq := fun _ => rfl

/-- Exact selected-block and complement coordinates on the same full source register. -/
def labelPartition (positions : Fin active ↪ Fin full) :
    (Qubits full).Index ≃ (Qubits active).Index × (labelRemainder positions).Index :=
  (BinaryBasis.bigEndianEquiv full).symm.trans
    ((labelEmbedding positions).splitBasis.trans
      (Equiv.prodCongr
        ((selectedPlacement positions).indexEquiv.trans
          (QuantumSignature.qubitsIndexEquiv active)) (Equiv.refl _)))

/-- The selected source bit is exactly the original full label's corresponding bit. -/
lemma window_sourcePartition_coordinate (positions : Fin active ↪ Fin full)
    (label : (Qubits full).Index) (index : Fin active) :
    (BinaryBasis.bigEndianEquiv active).symm (labelPartition positions label).1 index =
      finTwoEquiv.symm (label.val.testBit (positions index).rev.val) := by
  have picked : (labelPartition positions label).1 =
      BinaryBasis.bigEndianEquiv active
        ((selectedPlacement positions).indexEquiv
          ((labelEmbedding positions).splitBasis
            ((BinaryBasis.bigEndianEquiv full).symm label)).1) := rfl
  rw [picked]
  have inverse := congrFun ((BinaryBasis.bigEndianEquiv active).symm_apply_apply
    ((selectedPlacement positions).indexEquiv
      ((labelEmbedding positions).splitBasis
        ((BinaryBasis.bigEndianEquiv full).symm label)).1)) index
  exact inverse.trans (Fin.ext
    (QuantumLayout.Embedding.embedding_splitBasis_selected_value
      (labelEmbedding positions) ((BinaryBasis.bigEndianEquiv full).symm label) index))

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
