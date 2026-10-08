/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Program
import all QuantumAlg.Primitives.MAU.Addition.HRS.Recursive.Placement
import all QuantumAlg.Primitives.MAU.Addition.HRS.JoinPlacement
import all QuantumAlg.Primitives.MAU.Addition.HRS.Recursive.Arithmetic

/-!
# One actual recursive HRS addition step

The bridge adds the low carry into the high word. Two actual recursive child
programs then add the low and high constant halves, reusing the same dirty bit.
The typed placements and equal-width join retain the original carrier without
an identity declaration or compatibility wrapper [HRS16, paper.tex:232-260].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

/-- Execute one actual bridge and both recursive children on the original carrier. -/
def recursiveStepProgram (width : Nat) (constant : Fin (2 ^ width))
    (lowProgram : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding (lowWidth width)).width).toQuantum)
    (highProgram : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding (highWidth width)).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum :=
  joinProgram width
    (((recursiveBridgeProgram width ((splitWord width) constant).1).seq
      (placeLowChild (lowWidth width) (highWidth width) lowProgram)).seq
      (placeHighChild (lowWidth width) (highWidth width) highProgram))

/-- Exact child additions imply exact full-word addition after the actual carry bridge. -/
theorem hrsRecursiveStep_realizes (width : Nat) (constant : Fin (2 ^ width))
    (lowProgram : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding (lowWidth width)).width).toQuantum)
    (highProgram : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding (highWidth width)).width).toQuantum)
    (hlow : UnitaryCircuit.Realizes (oneDirtyEncoding (lowWidth width)) lowProgram
      (oneDirtyOutput ((splitWord width) constant).1))
    (hhigh : UnitaryCircuit.Realizes (oneDirtyEncoding (highWidth width)) highProgram
      (oneDirtyOutput ((splitWord width) constant).2)) :
    UnitaryCircuit.Realizes (oneDirtyEncoding width)
      (recursiveStepProgram width constant lowProgram highProgram) (oneDirtyOutput constant) := by
  have hbridge := hrsRecursiveBridge_realizes width ((splitWord width) constant).1
  have hleft := hrsPlaceLowChild_realizes (lowWidth width) (highWidth width)
    ((splitWord width) constant).1 lowProgram hlow
  have hright := hrsPlaceHighChild_realizes (lowWidth width) (highWidth width)
    ((splitWord width) constant).2 highProgram hhigh
  have hjoined := hrsJoinProgram_realizes width _ _ ((hbridge.seq hleft).seq hright)
  apply hjoined.congrStep
  rintro ⟨input, dirty⟩
  apply Prod.ext
  · exact hrsJoin_recursive_addition width constant input
  · rfl

/-- The exact event ledger is the sum of the actual bridge and both actual children. -/
theorem hrsRecursiveStep_eventCost (width : Nat) (constant : Fin (2 ^ width))
    (lowProgram : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding (lowWidth width)).width).toQuantum)
    (highProgram : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding (highWidth width)).width).toQuantum) :
    (recursiveStepProgram width constant lowProgram highProgram).eventCost =
      (recursiveBridgeProgram width ((splitWord width) constant).1).eventCost +
        lowProgram.eventCost + highProgram.eventCost := by
  rw [recursiveStepProgram, (hrsJoinProgram_resources _ _ (fun _ => 1)).1]
  simp only [UnitaryCircuit.seq_eventCost,
    (hrsPlaceLowChild_resources _ _ lowProgram (fun _ => 1)).1,
    (hrsPlaceHighChild_resources _ _ highProgram (fun _ => 1)).1]

/-- Evaluated depth records the same three sequential child circuits. -/
theorem hrsRecursiveStep_depth (width : Nat) (constant : Fin (2 ^ width))
    (lowProgram : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding (lowWidth width)).width).toQuantum)
    (highProgram : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (oneDirtyEncoding (highWidth width)).width).toQuantum)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (recursiveStepProgram width constant lowProgram highProgram).evaluatedEventDepth assign =
      (recursiveBridgeProgram width ((splitWord width) constant).1).evaluatedEventDepth assign +
        lowProgram.evaluatedEventDepth assign + highProgram.evaluatedEventDepth assign := by
  rw [recursiveStepProgram, (hrsJoinProgram_resources _ _ assign).2]
  simp only [UnitaryCircuit.evaluatedEventDepth_seq,
    (hrsPlaceLowChild_resources _ _ lowProgram assign).2,
    (hrsPlaceHighChild_resources _ _ highProgram assign).2]

end

end QuantumAlg.MAU.Addition.HRS
