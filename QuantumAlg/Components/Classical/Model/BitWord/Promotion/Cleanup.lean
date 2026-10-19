/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Promotion
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.State.Coordinates

/-!
# Physical cleanup under native bit/word selection

Selecting the classical bit/word language relabels only finite circuit paths.
The actual measurement trace and every complete quantum-reference block remain
available for a restart certificate.
-/

namespace QuantumAlg.BitWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {allowAllocation : Bool} {gates : GateModel} {oracles : OracleModel}
  {pre post : RuntimeCtx .quantum}
  {environment : (.quantum gates oracles model : ExecutionModel).Environment}

private def cleanupHistoryEquiv
    (code : Circuit (.quantum gates oracles) pre post allowAllocation) (H : Type) :
    ((.quantum gates oracles : ExecutionModel).HiddenState × (H × code.Path)) ≃
      ((.quantum gates oracles model : ExecutionModel).HiddenState ×
        (H × (selectForCircuit code).Path)) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl H)
    (selectForCircuitPathEquiv code))

/-- Native bit/word model selection preserves the caller's specified physical
reset label, not merely the existence of some output seed. -/
lemma selectForCircuit_reinitializedAt
    (code : Circuit (.quantum gates oracles) pre post allowAllocation)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt code ⟨environment.quantum, environment.classical⟩ seed) :
    Circuit.ReinitializedAt (selectForCircuit code) environment seed := by
  unfold Circuit.ReinitializedAt at fixed ⊢
  intro Reference H _ state record
  let labels := Equiv.prodCongr (Equiv.refl (Execution.Store post))
    (cleanupHistoryEquiv code H)
  have sameBlock :
      ((selectForCircuit code).execute environment Reference state).block record =
        (code.execute ⟨environment.quantum, environment.classical⟩ Reference state).block
          (labels.symm record) := by
    rw [selectForCircuit_execute]
    unfold Execution.State.mapHistory
    have mapping : (fun value => (value.1, (value.2.1,
        (value.2.2.1, selectForCircuitPathEquiv code value.2.2.2)))) = labels := by
      funext value
      rcases value with ⟨store, hidden, history, path⟩
      rfl
    rw [mapping]
    convert ExecutionState.coordinate_mapClassical_block
      (code.execute ⟨environment.quantum, environment.classical⟩ Reference state) labels record
        using 1
    exact congrArg (fun output : ExecutionState _ _ => output.block record)
      (ExecutionState.executionState_mapClassical_congr_decision
        (code.execute ⟨environment.quantum, environment.classical⟩ Reference state) labels labels
          (fun _ => rfl) _ _)
  rw [sameBlock]
  exact fixed Reference state (labels.symm record)

/-- Physical cleanup survives exact native-language selection when all quantum
wires are owned. The original and selected paths have identical density blocks. -/
lemma selectForCircuit_restartCleanup
    (code : Circuit (.quantum gates oracles) pre post allowAllocation)
    (cleanup : Circuit.RestartCleanup code ⟨environment.quantum, environment.classical⟩)
    (noBorrowed : pre.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (selectForCircuit code) environment where
  measured := by
    intro selectedPath
    let original := (selectForCircuitPathEquiv code).symm selectedPath
    obtain ⟨dimension, present⟩ := cleanup.measured original
    refine ⟨dimension, ?_⟩
    have lifted :
        (Resource.Event.measurement (model := .quantum gates oracles model) dimension) ∈
        (code.eventTrace original).map liftQuantumEvent :=
      List.mem_map.mpr ⟨Resource.Event.measurement
        (model := .quantum gates oracles) dimension, present, rfl⟩
    rw [← selectForCircuit_eventTrace code original] at lifted
    simpa only [original, Equiv.apply_symm_apply] using lifted
  restores := by
    intro Reference H _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum (selectForCircuit code)
      environment noBorrowed Reference state
  reinitialized := by
    obtain ⟨seed, pure⟩ := cleanup.reinitialized
    exact ⟨seed, selectForCircuit_reinitializedAt (environment := environment) code seed pure⟩

end

end QuantumAlg.BitWord
