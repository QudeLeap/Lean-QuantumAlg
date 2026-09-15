/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stage
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Small.Offset

/-!
# Small-width accumulation stages without borrowed bits

The addressed source bit coherently controls the literal small-width modular
offset. The source and target are the only quantum registers. In width zero
there is no source coordinate and therefore no selected stage to execute.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open Nat.FixedWidth

/-- The standard source bit uses the library's little-endian-to-wire conversion. -/
def sourceBit (width : Nat) (selected : Fin width) :
    EncodedBit (BinaryLabelEncoding.finIdentity width) :=
  BinaryLabelEncoding.finIdentityBit width (WireAddress.littleEndianWire selected)

theorem gidneySourceBit_get (width : Nat) (selected : Fin width) (source : Fin (2 ^ width)) :
    (sourceBit width selected).get source = source.val.testBit selected.val := by
  change source.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire selected)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

/-- The actual source-controlled small offset requires no extra quantum coordinate. -/
def smallStageProgram (width : Nat) (small : width ≤ 2) (selected : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.controlAtEncodedBit (sourceBit width selected)
    (Addition.Gidney.Small.modularOffsetProgram width small modulus constant)

theorem gidneySmallStage_realizes (width : Nat) (small : width ≤ 2) (selected : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (encoding width)
      (smallStageProgram width small selected modulus constant)
      (selectedOutput selected modulus constant) where
  apply_encoded_ket := by
    rintro ⟨source, target⟩
    have hbody := (Addition.Gidney.Small.gidneySmallModularOffset_realizes
      width small modulus constant).apply_encoded_ket target
    have h := UnitaryCircuit.controlAtEncodedBit_applyNormalized_of_eq
      (sourceBit width selected) (BinaryLabelEncoding.finIdentity width)
      (Addition.Gidney.Small.modularOffsetProgram width small modulus constant)
      _ _ hbody source
    rw [gidneySourceBit_get] at h
    change (UnitaryCircuit.controlAtEncodedBit (sourceBit width selected)
      (Addition.Gidney.Small.modularOffsetProgram width small modulus constant)).applyNormalized
        (NormalizedVector.ket (R := Qubits (width + width))
          (prodEquiv (m := width) (n := width) (source, target))) =
      NormalizedVector.ket (R := Qubits (width + width))
        (prodEquiv (m := width) (n := width) (source,
          if source.val.testBit selected.val then modularWordOutput modulus constant target
          else target))
    exact h

theorem gidneySmallStage_physical_range (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (smallStageProgram width small selected modulus constant).physical_idx ⊆
      List.range (2 * width) := by
  have hbody : (Addition.Gidney.Small.modularOffsetProgram
      width small modulus constant).physical_idx ⊆ List.range width := by
    rw [Addition.Gidney.Small.gidneySmallModularOffset_physical]
    exact fun _ h => h
  have h := UnitaryCircuit.controlAtEncodedBit_physical_idx_subset_range
    (sourceBit width selected)
    (Addition.Gidney.Small.modularOffsetProgram width small modulus constant) hbody
  have hwidth : (BinaryLabelEncoding.finIdentity width).width + width = 2 * width := by
    change width + width = 2 * width
    omega
  unfold smallStageProgram
  simpa only [hwidth] using h

/-- Coherent control changes the native coordinate of each executed small-offset event. -/
theorem gidneySmallStage_eventCost (width : Nat) (small : width ≤ 2) (selected : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (smallStageProgram width small selected modulus constant).eventCost =
      ResourcePool.controlForDimension 2
        (Addition.Gidney.Small.modularOffsetProgram width small modulus constant).eventCost := by
  unfold smallStageProgram UnitaryCircuit.controlAtEncodedBit
  change (UnitaryCircuit.prodRight
    (m := UnitaryCircuit.encodedControlPrefixWidth (sourceBit width selected))
    (UnitaryCircuit.controlLeading (UnitaryCircuit.prodRight
      (m := UnitaryCircuit.encodedControlSuffixWidth (sourceBit width selected))
      (Addition.Gidney.Small.modularOffsetProgram width small modulus constant)))).eventCost = _
  rw [UnitaryCircuit.prodRight_eventCost, UnitaryCircuit.controlLeading_eventCost,
    UnitaryCircuit.prodRight_eventCost]

theorem gidneySmallStage_event_count_bound (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (smallStageProgram width small selected modulus constant).eventCost.card ≤ 9 := by
  rw [gidneySmallStage_eventCost]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions, Multiset.card_map]
  exact Addition.Gidney.Small.gidneySmallModularOffset_event_count_bound
    width small modulus constant

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
