/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Program

/-!
# Exact schedules and event bounds for the actual modular accumulator

Every selected stage coherently controls its complete offset body. The shared
selector serializes its native events under the Core control schedule. The
actual prefix sequentially composes those stages, so its unit-duration depth
equals its event cardinality. The explicit envelope is independent of the
compiled coefficient and includes both the small and general width branches.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

private theorem leading_depth_eq_events {width : Nat} (body : UnitaryCircuit (Qubits width)) :
    (UnitaryCircuit.controlLeading body).evaluatedEventDepth (fun _ => 1) =
      (UnitaryCircuit.controlLeading body).eventCost.card := by
  rw [UnitaryCircuit.controlLeading_eventCost]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions, Multiset.card_map]
  calc
    _ = DepthExpr.costEval (fun _ => (1 : Nat))
        (UnitaryCircuit.shiftPhysicalIdx 1 body).eventDepth :=
      UnitaryCircuit.evaluatedEventDepth_controlQubitsAt (fun _ => 1) [0]
        (UnitaryCircuit.shiftPhysicalIdx 1 body) (UnitaryCircuit.leadingControlLayout body)
        (1 : Fin 2)
    _ = body.resourcesFromEventDepth.card := by
      rw [UnitaryCircuit.shiftPhysicalIdx_eventDepth]
      exact DepthExpr.unitCost_eq_eventPool_card _
    _ = body.eventCost.card :=
      congrArg Multiset.card (UnitaryCircuit.resourcesFromEventDepth_eq_eventCost body)

theorem gidneyCanonicalStage_depth_eq_events (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (canonicalProgram extra modulus constant).evaluatedEventDepth (fun _ => 1) =
      (canonicalProgram extra modulus constant).eventCost.card :=
  leading_depth_eq_events (canonicalBody extra modulus constant)

theorem gidneyPlacedStage_depth_eq_events (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (placedStageProgram extra selected modulus constant).evaluatedEventDepth (fun _ => 1) =
      (placedStageProgram extra selected modulus constant).eventCost.card := by
  have h := gidneyPlacedStage_resources extra selected modulus constant (fun _ => 1)
  rw [h.1, h.2]
  exact gidneyCanonicalStage_depth_eq_events extra modulus constant

theorem gidneySmallStage_depth_eq_events (width : Nat) (small : width ≤ 2)
    (selected : Fin width) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (smallStageProgram width small selected modulus constant).evaluatedEventDepth (fun _ => 1) =
      (smallStageProgram width small selected modulus constant).eventCost.card := by
  unfold smallStageProgram UnitaryCircuit.controlAtEncodedBit
  change UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
    (UnitaryCircuit.prodRight
      (m := UnitaryCircuit.encodedControlPrefixWidth (sourceBit width selected))
      (UnitaryCircuit.controlLeading (UnitaryCircuit.prodRight
        (m := UnitaryCircuit.encodedControlSuffixWidth (sourceBit width selected))
        (Addition.Gidney.Small.modularOffsetProgram width small modulus constant)))) =
      (UnitaryCircuit.prodRight
        (m := UnitaryCircuit.encodedControlPrefixWidth (sourceBit width selected))
        (UnitaryCircuit.controlLeading (UnitaryCircuit.prodRight
          (m := UnitaryCircuit.encodedControlSuffixWidth (sourceBit width selected))
          (Addition.Gidney.Small.modularOffsetProgram
            width small modulus constant)))).eventCost.card
  rw [UnitaryCircuit.prodRight_evaluatedEventDepth, UnitaryCircuit.prodRight_eventCost]
  exact leading_depth_eq_events _

theorem gidneyStage_depth_eq_events : (width : Nat) → (selected : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    (stageProgram width selected modulus constant).evaluatedEventDepth (fun _ => 1) =
      (stageProgram width selected modulus constant).eventCost.card
  | 0, selected, _, _ => Fin.elim0 selected
  | 1, selected, modulus, constant =>
      gidneySmallStage_depth_eq_events 1 (by decide) selected modulus constant
  | 2, selected, modulus, constant =>
      gidneySmallStage_depth_eq_events 2 (by decide) selected modulus constant
  | extra + 3, selected, modulus, constant =>
      gidneyPlacedStage_depth_eq_events extra selected modulus constant

theorem gidneyAccumulatePrefix_depth_eq_events (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus coefficient count within).evaluatedEventDepth (fun _ => 1) =
      (prefixProgram width modulus coefficient count within).eventCost.card := by
  induction count with
  | zero => rfl
  | succ index ih =>
      change UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
        ((prefixProgram width modulus coefficient index (by omega)).seq
          (stageProgram width ⟨index, by omega⟩ modulus
            (Nat.FixedWidth.accumulateConstant modulus coefficient index))) =
        ((prefixProgram width modulus coefficient index (by omega)).seq
          (stageProgram width ⟨index, by omega⟩ modulus
            (Nat.FixedWidth.accumulateConstant modulus coefficient index))).eventCost.card
      rw [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.seq_eventCost, Multiset.card_add,
        ih (by omega), gidneyStage_depth_eq_events]

/-- The exact full circuit has one serial unit step per actual native event occurrence. -/
theorem gidneyAccumulate_depth_eq_events (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) =
      (program width modulus coefficient).eventCost.card := by
  unfold program
  rw [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]
  change UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
    (prefixProgram width modulus coefficient width (Nat.le_refl width)) + 0 = _
  rw [Nat.add_zero]
  exact gidneyAccumulatePrefix_depth_eq_events width modulus coefficient width (Nat.le_refl width)

/-- The independent event envelope also bounds the schedule of this actual implementation. -/
theorem gidneyAccumulate_depth_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) ≤
      width * stageEventBound width := by
  rw [gidneyAccumulate_depth_eq_events]
  exact gidneyAccumulate_event_count_bound width modulus coefficient

/-- The actual two-word carrier agrees with its complete declared physical footprint. -/
theorem gidneyAccumulate_qubit_count (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    (encoding width).width = 2 * width ∧
      (program width modulus coefficient).physical_idx.length = 2 * width := by
  constructor
  · change width + width = 2 * width
    omega
  · rw [gidneyAccumulate_physical, List.length_range]

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
