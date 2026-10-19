/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.VBECircuit
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Inversion.MK.StructuredWitness
import all QuantumAlg.Primitives.MAU.Inversion.MK.Correction

/-! # Structural resource certificate for inversion correction stages -/

section

namespace QuantumAlg.MAU.Inversion.MK.Correction

noncomputable section

/-! ### Strict gate-count bounds -/

/-- Lifting a fixed-register gate list preserves its primitive-leaf count. -/
@[simp] lemma liftFixedGates_length
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MK.Circuit.encoding tail.succ counterWidth))) :
    (liftFixedGates tail counterWidth gates).length = gates.length := by
  let workGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (MK.Circuit.encoding tail.succ counterWidth)
          (MAU.Multiplication.VBECircuit.encoding tail.succ))) :=
    gates.map (EncodedBit.GateSpec.prodLeft
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
  change
    (workGates.map
      (EncodedBit.GateSpec.prodLeft (wordEncoding tail.succ))).length =
      gates.length
  calc
    _ = workGates.length := by simp only [List.length_map]
    _ = gates.length := by
      simp only [workGates, List.length_map]

/-- Lifting a VBE-workspace gate list preserves its primitive-leaf count. -/
@[simp] lemma liftWorkGates_length
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MAU.Multiplication.VBECircuit.encoding tail.succ))) :
    (liftWorkGates tail counterWidth gates).length = gates.length := by
  let combinedGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (MK.Circuit.encoding tail.succ counterWidth)
          (MAU.Multiplication.VBECircuit.encoding tail.succ))) :=
    gates.map (EncodedBit.GateSpec.prodRight
      (MK.Circuit.encoding tail.succ counterWidth))
  change
    (combinedGates.map
      (EncodedBit.GateSpec.prodLeft (wordEncoding tail.succ))).length =
      gates.length
  calc
    _ = combinedGates.length := by simp only [List.length_map]
    _ = gates.length := by
      simp only [combinedGates, List.length_map]

/-- Product lifting a fixed-register list preserves its complete ordered
primitive-event trace. -/
lemma liftFixedGates_events_eq_source
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MK.Circuit.encoding tail.succ counterWidth))) :
    (liftFixedGates tail counterWidth gates).map
        (EncodedBit.GateSpec.event .empty) =
      gates.map (EncodedBit.GateSpec.event .empty) := by
  unfold liftFixedGates
  exact
    (EncodedBit.GateSpec.map_event_prodLeft
      (wordEncoding tail.succ) _).trans
      (EncodedBit.GateSpec.map_event_prodLeft
        (MAU.Multiplication.VBECircuit.encoding tail.succ) gates)

/-- Product lifting a VBE-workspace list preserves its complete ordered
primitive-event trace. -/
lemma liftWorkGates_events_eq_source
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MAU.Multiplication.VBECircuit.encoding tail.succ))) :
    (liftWorkGates tail counterWidth gates).map
        (EncodedBit.GateSpec.event .empty) =
      gates.map (EncodedBit.GateSpec.event .empty) := by
  unfold liftWorkGates
  exact
    (EncodedBit.GateSpec.map_event_prodLeft
      (wordEncoding tail.succ) _).trans
      (EncodedBit.GateSpec.map_event_prodRight
        (MK.Circuit.encoding tail.succ counterWidth) gates)

/-- Fixed-register lifting preserves the strict CNOT coordinate. -/
@[simp] lemma liftFixedGates_cnotMultiplicity_sum
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MK.Circuit.encoding tail.succ counterWidth))) :
    ((liftFixedGates tail counterWidth gates).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum :=
  EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    .empty
    (liftFixedGates_events_eq_source tail counterWidth gates)

/-- Fixed-register lifting preserves the strict Toffoli coordinate. -/
@[simp] lemma liftFixedGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MK.Circuit.encoding tail.succ counterWidth))) :
    ((liftFixedGates tail counterWidth gates).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum :=
  EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    .empty
    (liftFixedGates_events_eq_source tail counterWidth gates)

/-- VBE-workspace lifting preserves the strict X coordinate. -/
@[simp] lemma liftWorkGates_xMultiplicity_sum
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MAU.Multiplication.VBECircuit.encoding tail.succ))) :
    ((liftWorkGates tail counterWidth gates).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.xMultiplicity).sum :=
  EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
    .empty
    (liftWorkGates_events_eq_source tail counterWidth gates)

/-- VBE-workspace lifting preserves the strict CNOT coordinate. -/
@[simp] lemma liftWorkGates_cnotMultiplicity_sum
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MAU.Multiplication.VBECircuit.encoding tail.succ))) :
    ((liftWorkGates tail counterWidth gates).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum :=
  EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    .empty
    (liftWorkGates_events_eq_source tail counterWidth gates)

/-- VBE-workspace lifting preserves the strict Toffoli coordinate. -/
@[simp] lemma liftWorkGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MAU.Multiplication.VBECircuit.encoding tail.succ))) :
    ((liftWorkGates tail counterWidth gates).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum :=
  EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    .empty
    (liftWorkGates_events_eq_source tail counterWidth gates)

/-- Width-only primitive-leaf bound for one static unit multiplication. -/
def unitMultiplicationGateLengthBound (tail : Nat) : Nat :=
  108 * tail.succ ^ 2 + 105 * tail.succ

/-- Width-only primitive-leaf bound for one counter-controlled unit
multiplication. -/
def counterCorrectionBitGateLengthBound (tail : Nat) : Nat :=
  3 * unitMultiplicationGateLengthBound tail

/-- Width-only primitive-leaf bound for the full correction computation. -/
def correctionComputeGateLengthBound (tail counterWidth : Nat) : Nat :=
  99 * tail.succ + 92 +
    counterWidth * counterCorrectionBitGateLengthBound tail +
      unitMultiplicationGateLengthBound tail

/-- Width-only primitive-leaf bound for the staged public-target addition. -/
def stagedTargetAddGateLengthBound (tail : Nat) : Nat :=
  56 * tail.succ + 45

/-- Width-only CNOT bound for one static unit multiplication. -/
def unitMultiplicationCnotBound (tail : Nat) : Nat :=
  48 * tail.succ ^ 2 + 43 * tail.succ

/-- Exact Toffoli coordinate for one static unit multiplication. -/
def unitMultiplicationToffoliCount (tail : Nat) : Nat :=
  60 * tail.succ ^ 2

/-- Width-only Toffoli bound for one counter-controlled unit
multiplication. -/
def counterCorrectionBitToffoliBound (tail : Nat) : Nat :=
  228 * tail.succ ^ 2 + 43 * tail.succ

/-- Width-only CNOT bound for the full correction computation. -/
def correctionComputeCnotBound (tail counterWidth : Nat) : Nat :=
  39 * tail.succ + 30 + counterWidth * (2 * tail.succ) +
    unitMultiplicationCnotBound tail

/-- Width-only Toffoli bound for the full correction computation. -/
def correctionComputeToffoliBound (tail counterWidth : Nat) : Nat :=
  60 * tail.succ +
    counterWidth * counterCorrectionBitToffoliBound tail +
      unitMultiplicationToffoliCount tail

/-- Width-only CNOT bound for the staged public-target addition. -/
def stagedTargetAddCnotBound (tail : Nat) : Nat :=
  26 * tail.succ + 14

/-- Exact Toffoli coordinate for the staged public-target addition. -/
def stagedTargetAddToffoliCount (tail : Nat) : Nat :=
  30 * tail.succ

/-- The lifted fixed-round compute is bounded by the literal fold ledger. -/
lemma fixedComputeGates_length_le
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (fixedComputeGates tail counterWidth comparisonIndex workIndex).length ≤
      MK.Circuit.foldGateLengthBound tail counterWidth := by
  rw [fixedComputeGates, liftFixedGates_length]
  exact MK.Circuit.foldGates_length_le
    tail counterWidth comparisonIndex workIndex

/-- The lifted fixed-round compute retains the exact fold-ledger CNOT
coordinate. -/
lemma fixedComputeGates_cnotMultiplicity_sum
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ((fixedComputeGates tail counterWidth comparisonIndex workIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * tail.succ * (4 * tail + 13) := by
  rw [fixedComputeGates, liftFixedGates_cnotMultiplicity_sum]
  exact MK.Circuit.foldGates_cnotMultiplicity_sum
    tail counterWidth comparisonIndex workIndex

/-- The lifted fixed-round compute retains the exact fold-ledger Toffoli
coordinate. -/
lemma fixedComputeGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ((fixedComputeGates tail counterWidth comparisonIndex workIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * tail.succ *
        (1114 * tail + 8 * counterWidth +
          72 * (counterWidth - 1) + 801) := by
  rw [fixedComputeGates, liftFixedGates_toffoliMultiplicity_sum]
  exact MK.Circuit.foldGates_toffoliMultiplicity_sum
    tail counterWidth comparisonIndex workIndex

private lemma sourceLiftedModularAddGates_events_eq_source
    (n p : Nat) :
    (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates n p).map
        (EncodedBit.GateSpec.event .empty) =
      (MAU.Addition.VBECircuit.modularAddGates n p).map
        (EncodedBit.GateSpec.event .empty) := by
  simp only [MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates,
    List.map_map]
  apply List.map_congr_left
  intro gate _
  cases gate <;> rfl

private lemma liftedWorkModularAddGates_events_eq_source
    (tail counterWidth p : Nat) :
    (liftedWorkModularAddGates tail counterWidth p).map
        (EncodedBit.GateSpec.event .empty) =
      (MAU.Addition.VBECircuit.modularAddGates tail.succ p).map
        (EncodedBit.GateSpec.event .empty) := by
  unfold liftedWorkModularAddGates
  exact
    (liftWorkGates_events_eq_source tail counterWidth _).trans
      (sourceLiftedModularAddGates_events_eq_source tail.succ p)

/-- The lifted VBE modular-add payload keeps its established linear bound. -/
lemma liftedWorkModularAddGates_length_le
    (tail counterWidth p : Nat) :
    (liftedWorkModularAddGates tail counterWidth p).length ≤
      48 * tail.succ + 45 := by
  rw [liftedWorkModularAddGates, liftWorkGates_length]
  rw [MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates,
    List.length_map]
  exact MAU.Addition.VBECircuit.modularAddGates_length_le tail.succ p

/-- The lifted VBE modular-add payload has the exact established Toffoli
coordinate. -/
lemma liftedWorkModularAddGates_toffoliMultiplicity_sum
    (tail counterWidth p : Nat) :
    ((liftedWorkModularAddGates tail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      stagedTargetAddToffoliCount tail := by
  rw [EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    .empty
    (liftedWorkModularAddGates_events_eq_source tail counterWidth p)]
  exact MAU.Addition.VBECircuit.modularAddGates_toffoliMultiplicity_sum
    tail.succ p

/-- The lifted VBE modular-add payload has the established width-only CNOT
bound. -/
lemma liftedWorkModularAddGates_cnotMultiplicity_sum_le
    (tail counterWidth p : Nat) :
    ((liftedWorkModularAddGates tail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      18 * tail.succ + 14 := by
  rw [EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    .empty
    (liftedWorkModularAddGates_events_eq_source tail counterWidth p)]
  exact MAU.Addition.VBECircuit.modularAddGates_cnotMultiplicity_sum_le
    tail.succ p

/-- Loading and reducing the full runtime pseudo-residue has a width-only
primitive-leaf bound. -/
lemma rawPseudoResidueLoadGates_length_le
    (tail counterWidth p : Nat) :
    (rawPseudoResidueLoadGates tail counterWidth p).length ≤
      99 * tail.succ + 92 := by
  have hcopyRaw := EncodedBit.Word.xorIntoGates_length
    (pseudoResidueWord tail counterWidth)
    (reductionTargetWord tail counterWidth)
    (pseudoResidue_reductionTarget_ne tail counterWidth)
  have hcopyReduced := EncodedBit.Word.xorIntoGates_length
    (reductionTargetLowWord tail counterWidth)
    (correctionValueWord tail counterWidth)
    (reductionTargetLow_correctionValue_ne tail counterWidth)
  have hadd := liftedWorkModularAddGates_length_le tail counterWidth p
  simp only [rawPseudoResidueLoadGates, List.length_append,
    List.length_reverse]
  omega

/-- Loading and reducing the runtime pseudo-residue has a width-only CNOT
bound derived from its two literal copies and two modular-add traversals. -/
lemma rawPseudoResidueLoadGates_cnotMultiplicity_sum_le
    (tail counterWidth p : Nat) :
    ((rawPseudoResidueLoadGates tail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      39 * tail.succ + 30 := by
  have hcopyRaw := EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum
    (pseudoResidueWord tail counterWidth)
    (reductionTargetWord tail counterWidth)
    (pseudoResidue_reductionTarget_ne tail counterWidth)
  have hcopyReduced := EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum
    (reductionTargetLowWord tail counterWidth)
    (correctionValueWord tail counterWidth)
    (reductionTargetLow_correctionValue_ne tail counterWidth)
  have hadd := liftedWorkModularAddGates_cnotMultiplicity_sum_le
    tail counterWidth p
  simp only [rawPseudoResidueLoadGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse]
  omega

/-- Only the two modular-add traversals contribute Toffoli gates to the raw
pseudo-residue loader. -/
lemma rawPseudoResidueLoadGates_toffoliMultiplicity_sum
    (tail counterWidth p : Nat) :
    ((rawPseudoResidueLoadGates tail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      60 * tail.succ := by
  simp only [rawPseudoResidueLoadGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse,
    EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum,
    liftedWorkModularAddGates_toffoliMultiplicity_sum,
    stagedTargetAddToffoliCount]
  omega

/-- A lifted static unit multiplication retains the VBE quadratic gate
bound. -/
lemma liftedUnitMultiplicationGates_length_le
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    (liftedUnitMultiplicationGates tail counterWidth p unit).length ≤
      unitMultiplicationGateLengthBound tail := by
  rw [liftedUnitMultiplicationGates, liftWorkGates_length]
  exact MAU.Multiplication.VBECircuit.multiplicationGates_length_le
    tail.succ p unit

/-- A lifted unit multiplication retains the exact source X coordinate. -/
lemma liftedUnitMultiplicationGates_xMultiplicity_sum
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    ((liftedUnitMultiplicationGates tail counterWidth p unit).map
        EncodedBit.GateSpec.xMultiplicity).sum = 2 * tail.succ := by
  rw [liftedUnitMultiplicationGates, liftWorkGates_xMultiplicity_sum]
  exact MAU.Multiplication.VBECircuit.multiplicationGates_xMultiplicity_sum
    tail.succ p unit

/-- A lifted unit multiplication retains the source width-only CNOT bound. -/
lemma liftedUnitMultiplicationGates_cnotMultiplicity_sum_le
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    ((liftedUnitMultiplicationGates tail counterWidth p unit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      unitMultiplicationCnotBound tail := by
  rw [liftedUnitMultiplicationGates, liftWorkGates_cnotMultiplicity_sum]
  exact MAU.Multiplication.VBECircuit.multiplicationGates_cnotMultiplicity_sum_le
    tail.succ p unit

/-- A lifted unit multiplication retains the exact source Toffoli
coordinate. -/
lemma liftedUnitMultiplicationGates_toffoliMultiplicity_sum
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    ((liftedUnitMultiplicationGates tail counterWidth p unit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      unitMultiplicationToffoliCount tail := by
  rw [liftedUnitMultiplicationGates, liftWorkGates_toffoliMultiplicity_sum]
  exact
    MAU.Multiplication.VBECircuit.multiplicationGates_toffoliMultiplicity_sum
      tail.succ p unit

/-- One counter-bit payload retains the same quadratic bound before its
literal control decomposition. -/
lemma counterCorrectionBitPayloadGates_length_le
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    (counterCorrectionBitPayloadGates
      tail counterWidth p hpOdd bit).length ≤
      unitMultiplicationGateLengthBound tail := by
  rw [counterCorrectionBitPayloadGates, liftWorkGates_length]
  exact MAU.Multiplication.VBECircuit.multiplicationGates_length_le
    tail.succ p (counterBitUnit p hpOdd bit.val)

/-- One counter-bit payload retains the exact source X coordinate. -/
lemma counterCorrectionBitPayloadGates_xMultiplicity_sum
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    ((counterCorrectionBitPayloadGates
      tail counterWidth p hpOdd bit).map
        EncodedBit.GateSpec.xMultiplicity).sum = 2 * tail.succ := by
  rw [counterCorrectionBitPayloadGates, liftWorkGates_xMultiplicity_sum]
  exact MAU.Multiplication.VBECircuit.multiplicationGates_xMultiplicity_sum
    tail.succ p (counterBitUnit p hpOdd bit.val)

/-- One counter-bit payload retains the source width-only CNOT bound. -/
lemma counterCorrectionBitPayloadGates_cnotMultiplicity_sum_le
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    ((counterCorrectionBitPayloadGates
      tail counterWidth p hpOdd bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      unitMultiplicationCnotBound tail := by
  rw [counterCorrectionBitPayloadGates, liftWorkGates_cnotMultiplicity_sum]
  exact MAU.Multiplication.VBECircuit.multiplicationGates_cnotMultiplicity_sum_le
    tail.succ p (counterBitUnit p hpOdd bit.val)

/-- One counter-bit payload retains the exact source Toffoli coordinate. -/
lemma counterCorrectionBitPayloadGates_toffoliMultiplicity_sum
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    ((counterCorrectionBitPayloadGates
      tail counterWidth p hpOdd bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      unitMultiplicationToffoliCount tail := by
  rw [counterCorrectionBitPayloadGates, liftWorkGates_toffoliMultiplicity_sum]
  exact
    MAU.Multiplication.VBECircuit.multiplicationGates_toffoliMultiplicity_sum
      tail.succ p (counterBitUnit p hpOdd bit.val)

/-- Literal clean-work control expands one counter-bit payload by at most a
factor of three. -/
lemma counterCorrectionBitGates_length_le
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    (counterCorrectionBitGates tail counterWidth p hpOdd bit).length ≤
      counterCorrectionBitGateLengthBound tail := by
  have hpayload := counterCorrectionBitPayloadGates_length_le
    tail counterWidth p hpOdd bit
  unfold counterCorrectionBitGates counterCorrectionBitGateLengthBound
  calc
    _ ≤ 3 * (counterCorrectionBitPayloadGates
        tail counterWidth p hpOdd bit).length :=
      EncodedBit.GateSpec.controlledListWithWorkGates_length_le_three_mul
        (paddingCounterBit tail counterWidth bit)
        (correctionControlWorkBit tail counterWidth)
        (counterCorrectionBitPayloadGates tail counterWidth p hpOdd bit)
        (counterCorrectionBitPayload_controlDisjoint
          tail counterWidth p hpOdd bit)
        (counterCorrectionBitPayload_workDisjoint
          tail counterWidth p hpOdd bit)
        (paddingCounter_controlWork_ne tail counterWidth bit)
    _ ≤ 3 * unitMultiplicationGateLengthBound tail :=
      Nat.mul_le_mul_left 3 hpayload

/-- A literal clean-work control turns the payload X coordinate into exactly
two CNOTs per arithmetic bit. -/
lemma counterCorrectionBitGates_cnotMultiplicity_sum
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    ((counterCorrectionBitGates tail counterWidth p hpOdd bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * tail.succ := by
  unfold counterCorrectionBitGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    counterCorrectionBitPayloadGates_xMultiplicity_sum]

/-- A literal clean-work control contributes one Toffoli per payload CNOT and
three per payload Toffoli. -/
lemma counterCorrectionBitGates_toffoliMultiplicity_sum_le
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    ((counterCorrectionBitGates tail counterWidth p hpOdd bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      counterCorrectionBitToffoliBound tail := by
  have hc := counterCorrectionBitPayloadGates_cnotMultiplicity_sum_le
    tail counterWidth p hpOdd bit
  have ht := counterCorrectionBitPayloadGates_toffoliMultiplicity_sum
    tail counterWidth p hpOdd bit
  unfold counterCorrectionBitGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum]
  unfold unitMultiplicationCnotBound at hc
  unfold unitMultiplicationToffoliCount at ht
  unfold counterCorrectionBitToffoliBound
  omega

private lemma flatMap_counterCorrectionBitGates_length_le
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    ∀ bits : List (Fin counterWidth),
      (bits.flatMap
        (counterCorrectionBitGates tail counterWidth p hpOdd)).length ≤
        bits.length * counterCorrectionBitGateLengthBound tail
  | [] => by simp
  | bit :: rest => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hbit := counterCorrectionBitGates_length_le
        tail counterWidth p hpOdd bit
      have hrest := flatMap_counterCorrectionBitGates_length_le
        tail counterWidth p hpOdd rest
      calc
        (counterCorrectionBitGates
            tail counterWidth p hpOdd bit).length +
            (rest.flatMap
              (counterCorrectionBitGates
                tail counterWidth p hpOdd)).length ≤
            counterCorrectionBitGateLengthBound tail +
              rest.length * counterCorrectionBitGateLengthBound tail :=
          Nat.add_le_add hbit hrest
        _ = rest.length.succ *
            counterCorrectionBitGateLengthBound tail := by
          calc
            counterCorrectionBitGateLengthBound tail +
                rest.length * counterCorrectionBitGateLengthBound tail =
                rest.length * counterCorrectionBitGateLengthBound tail +
                  counterCorrectionBitGateLengthBound tail := Nat.add_comm _ _
            _ = rest.length.succ *
                counterCorrectionBitGateLengthBound tail :=
              (Nat.succ_mul rest.length
              (counterCorrectionBitGateLengthBound tail)).symm

private lemma flatMap_counterCorrectionBitGates_cnotMultiplicity_sum
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    ∀ bits : List (Fin counterWidth),
      (((bits.flatMap
        (counterCorrectionBitGates tail counterWidth p hpOdd)).map
          EncodedBit.GateSpec.cnotMultiplicity).sum) =
        bits.length * (2 * tail.succ)
  | [] => by simp
  | bit :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons,
        counterCorrectionBitGates_cnotMultiplicity_sum,
        flatMap_counterCorrectionBitGates_cnotMultiplicity_sum
          tail counterWidth p hpOdd rest]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

private lemma flatMap_counterCorrectionBitGates_toffoliMultiplicity_sum_le
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    ∀ bits : List (Fin counterWidth),
      (((bits.flatMap
        (counterCorrectionBitGates tail counterWidth p hpOdd)).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum) ≤
        bits.length * counterCorrectionBitToffoliBound tail
  | [] => by simp
  | bit :: rest => by
      have hbit := counterCorrectionBitGates_toffoliMultiplicity_sum_le
        tail counterWidth p hpOdd bit
      have hrest :=
        flatMap_counterCorrectionBitGates_toffoliMultiplicity_sum_le
          tail counterWidth p hpOdd rest
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons]
      calc
        _ ≤ counterCorrectionBitToffoliBound tail +
              rest.length * counterCorrectionBitToffoliBound tail :=
          Nat.add_le_add hbit hrest
        _ = rest.length.succ * counterCorrectionBitToffoliBound tail := by
          rw [Nat.succ_mul]
          exact Nat.add_comm _ _

/-- The counter-driven correction ledger has one uniformly bounded literal
controlled payload per physical counter bit. -/
lemma counterCorrectionGates_length_le
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    (counterCorrectionGates tail counterWidth p hpOdd).length ≤
      counterWidth * counterCorrectionBitGateLengthBound tail := by
  have h := flatMap_counterCorrectionBitGates_length_le
    tail counterWidth p hpOdd
    (List.ofFn fun bit : Fin counterWidth => bit)
  simpa only [counterCorrectionGates, List.length_ofFn] using h

/-- The full runtime-counter ledger has exactly two CNOTs per arithmetic bit
for every physical counter bit. -/
lemma counterCorrectionGates_cnotMultiplicity_sum
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    ((counterCorrectionGates tail counterWidth p hpOdd).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      counterWidth * (2 * tail.succ) := by
  have h := flatMap_counterCorrectionBitGates_cnotMultiplicity_sum
    tail counterWidth p hpOdd
    (List.ofFn fun bit : Fin counterWidth => bit)
  simpa only [counterCorrectionGates, List.length_ofFn] using h

/-- The full runtime-counter ledger has the sum of the per-bit controlled
Toffoli bounds. -/
lemma counterCorrectionGates_toffoliMultiplicity_sum_le
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    ((counterCorrectionGates tail counterWidth p hpOdd).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      counterWidth * counterCorrectionBitToffoliBound tail := by
  have h := flatMap_counterCorrectionBitGates_toffoliMultiplicity_sum_le
    tail counterWidth p hpOdd
    (List.ofFn fun bit : Fin counterWidth => bit)
  simpa only [counterCorrectionGates, List.length_ofFn] using h

/-- The static sign correction is one lifted unit multiplication. -/
lemma signCorrectionGates_length_le
    (tail counterWidth p : Nat) :
    (signCorrectionGates tail counterWidth p).length ≤
      unitMultiplicationGateLengthBound tail := by
  simpa only [signCorrectionGates] using
    (liftedUnitMultiplicationGates_length_le
      tail counterWidth p (-1 : (ZMod p)ˣ))

/-- The static sign correction retains the source multiplication CNOT
bound. -/
lemma signCorrectionGates_cnotMultiplicity_sum_le
    (tail counterWidth p : Nat) :
    ((signCorrectionGates tail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      unitMultiplicationCnotBound tail := by
  simpa only [signCorrectionGates] using
    (liftedUnitMultiplicationGates_cnotMultiplicity_sum_le
      tail counterWidth p (-1 : (ZMod p)ˣ))

/-- The static sign correction retains the exact source multiplication
Toffoli coordinate. -/
lemma signCorrectionGates_toffoliMultiplicity_sum
    (tail counterWidth p : Nat) :
    ((signCorrectionGates tail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      unitMultiplicationToffoliCount tail := by
  simpa only [signCorrectionGates] using
    (liftedUnitMultiplicationGates_toffoliMultiplicity_sum
      tail counterWidth p (-1 : (ZMod p)ˣ))

/-- Raw reduction, runtime counter correction, and sign correction together
obey the named width-only bound. -/
lemma correctionComputeGates_length_le
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    (correctionComputeGates tail counterWidth p hpOdd).length ≤
      correctionComputeGateLengthBound tail counterWidth := by
  have hraw := rawPseudoResidueLoadGates_length_le tail counterWidth p
  have hcounter := counterCorrectionGates_length_le
    tail counterWidth p hpOdd
  have hsign := signCorrectionGates_length_le tail counterWidth p
  simp only [correctionComputeGates, correctionComputeGateLengthBound,
    List.length_append]
  omega

/-- Raw reduction, counter correction, and sign correction together obey the
coordinate-specific CNOT bound. -/
lemma correctionComputeGates_cnotMultiplicity_sum_le
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    ((correctionComputeGates tail counterWidth p hpOdd).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      correctionComputeCnotBound tail counterWidth := by
  have hraw := rawPseudoResidueLoadGates_cnotMultiplicity_sum_le
    tail counterWidth p
  have hcounter := counterCorrectionGates_cnotMultiplicity_sum
    tail counterWidth p hpOdd
  have hsign := signCorrectionGates_cnotMultiplicity_sum_le
    tail counterWidth p
  simp only [correctionComputeGates, List.map_append, List.sum_append]
  unfold correctionComputeCnotBound
  omega

/-- Raw reduction, counter correction, and sign correction together obey the
coordinate-specific Toffoli bound. -/
lemma correctionComputeGates_toffoliMultiplicity_sum_le
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    ((correctionComputeGates tail counterWidth p hpOdd).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      correctionComputeToffoliBound tail counterWidth := by
  have hraw := rawPseudoResidueLoadGates_toffoliMultiplicity_sum
    tail counterWidth p
  have hcounter := counterCorrectionGates_toffoliMultiplicity_sum_le
    tail counterWidth p hpOdd
  have hsign := signCorrectionGates_toffoliMultiplicity_sum
    tail counterWidth p
  simp only [correctionComputeGates, List.map_append, List.sum_append]
  unfold correctionComputeToffoliBound
  omega

/-- Swapping the target in, copying the source, adding, and undoing both
transfers obeys the named linear bound. -/
lemma stagedTargetAddGates_length_le
    (tail counterWidth p : Nat) :
    (stagedTargetAddGates tail counterWidth p).length ≤
      stagedTargetAddGateLengthBound tail := by
  have hswap := EncodedBit.Word.swapGates_length
    (publicTargetWord tail counterWidth)
    (reductionTargetLowWord tail counterWidth)
    (publicTarget_reductionTargetLow_ne tail counterWidth)
  have hcopy := EncodedBit.Word.xorIntoGates_length
    (correctionValueWord tail counterWidth)
    (targetAddSourceLowWord tail counterWidth)
    (correctionValue_targetAddSourceLow_ne tail counterWidth)
  have hadd := liftedWorkModularAddGates_length_le tail counterWidth p
  simp only [stagedTargetAddGates, stagedTargetAddGateLengthBound,
    List.length_append, List.length_reverse]
  omega

/-- The staged public-target transfer obeys the coordinate-specific CNOT
bound. -/
lemma stagedTargetAddGates_cnotMultiplicity_sum_le
    (tail counterWidth p : Nat) :
    ((stagedTargetAddGates tail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      stagedTargetAddCnotBound tail := by
  have hswap := EncodedBit.Word.swapGates_cnotMultiplicity_sum
    (publicTargetWord tail counterWidth)
    (reductionTargetLowWord tail counterWidth)
    (publicTarget_reductionTargetLow_ne tail counterWidth)
  have hcopy := EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum
    (correctionValueWord tail counterWidth)
    (targetAddSourceLowWord tail counterWidth)
    (correctionValue_targetAddSourceLow_ne tail counterWidth)
  have hadd := liftedWorkModularAddGates_cnotMultiplicity_sum_le
    tail counterWidth p
  simp only [stagedTargetAddGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse]
  unfold stagedTargetAddCnotBound
  omega

/-- Only the modular-add payload contributes Toffoli gates to the staged
public-target transfer. -/
lemma stagedTargetAddGates_toffoliMultiplicity_sum
    (tail counterWidth p : Nat) :
    ((stagedTargetAddGates tail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      stagedTargetAddToffoliCount tail := by
  simp only [stagedTargetAddGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse,
    EncodedBit.Word.swapGates_toffoliMultiplicity_sum,
    EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum,
    liftedWorkModularAddGates_toffoliMultiplicity_sum]
  omega

end

end QuantumAlg.MAU.Inversion.MK.Correction

end
