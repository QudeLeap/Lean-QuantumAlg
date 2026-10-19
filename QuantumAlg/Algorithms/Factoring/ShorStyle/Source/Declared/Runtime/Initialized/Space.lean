/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Space
import all QuantumAlg.Core.Execution.Trace.Preparation

/-!
# Complete live space of initialization and the first declared round

All five persistent cells, the actual preparation bank, each retained source
result and the simultaneous complete native workspace contribute. The
independent allowances preserve the caller and all original auxiliary roles.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Persistent

open Execution

noncomputable section

/-- The five genuine persistent heads contribute their complete encoded shapes. -/
def additionalSpace {kind : ProblemKind} (N : Nat) : SpacePool kind :=
  SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) +
    (SpacePool.ofShape (.product .bit (.unsignedWord (modulusBits N))) +
      (SpacePool.ofShape .bit +
        (SpacePool.ofShape (.unsignedWord (modulusBits N)) + SpacePool.ofShape .bit)))

/-- The true surviving resident frame contains every actual persistent head. -/
lemma context_resident {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).residentSpace = ctx.residentSpace + additionalSpace N := by
  unfold context selectedContext acceptedContext candidateContext resultContext
  simp only [RuntimeCtx.residentSpace_addRetained]
  unfold additionalSpace
  ac_rfl

/-- Allocation and the real latch clear fit the complete persistent resident frame. -/
lemma initialization_resident_le {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (N : Nat)
    (path : (initialization (model := model) ctx N).Path) :
    (initialization (model := model) ctx N).peakResidentSpace path ≤
      (context ctx N).residentSpace := by
  rcases path with ⟨allocationPath, clearPath⟩
  change (Circuit.seq (allocation (model := model) ctx N)
    (BitWord.instruction (execution := model) (NativeFactorScan.clearAcceptedOp
      (cells ctx N)))).peakResidentSpace ⟨allocationPath, clearPath⟩ ≤ _
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · rcases allocationPath with ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
    rw [context_resident]
    simp +instances only [allocation, resultContext, candidateContext, acceptedContext,
      selectedContext, Circuit.peakResidentSpace_seq, Circuit.peakResidentSpace_retain,
      RuntimeCtx.residentSpace_addRetained]
    intro axis
    simp only [SpacePool.max, Pi.add_apply, additionalSpace]
    repeat' apply max_le
    all_goals omega
  · exact (Circuit.peakResidentSpace_classical
      (BitWord.selectedApplication (execution := model)
        (NativeFactorScan.clearAcceptedOp (cells ctx N))) clearPath).le

/-- The true surviving auxiliary frame contains every actual persistent head. -/
lemma context_auxiliary {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).auxiliarySpace = ctx.auxiliarySpace + additionalSpace N := by
  unfold context selectedContext acceptedContext candidateContext resultContext
  simp only [RuntimeCtx.auxiliarySpace_addRetained]
  unfold additionalSpace
  ac_rfl

/-- Allocation and the real latch clear fit the complete persistent auxiliary frame. -/
lemma initialization_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (N : Nat)
    (path : (initialization (model := model) ctx N).Path) :
    (initialization (model := model) ctx N).peakAuxiliarySpace path ≤
      (context ctx N).auxiliarySpace := by
  rcases path with ⟨allocationPath, clearPath⟩
  change (Circuit.seq (allocation (model := model) ctx N)
    (BitWord.instruction (execution := model) (NativeFactorScan.clearAcceptedOp
      (cells ctx N)))).peakAuxiliarySpace ⟨allocationPath, clearPath⟩ ≤ _
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · rcases allocationPath with ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
    rw [context_auxiliary]
    simp +instances only [allocation, resultContext, candidateContext, acceptedContext,
      selectedContext, Circuit.peakAuxiliarySpace_seq, Circuit.peakAuxiliarySpace_retain,
      RuntimeCtx.auxiliarySpace_addRetained]
    intro axis
    simp only [SpacePool.max, Pi.add_apply, additionalSpace]
    repeat' apply max_le
    all_goals omega
  · exact (Circuit.peakAuxiliarySpace_classical
      (BitWord.selectedApplication (execution := model)
        (NativeFactorScan.clearAcceptedOp (cells ctx N))) clearPath).le

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Persistent

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized

open Execution

noncomputable section

/-- Initialization capacity and complete native workspace coexist with the caller. -/
def firstAdditionalSpace (N : Nat) : SpacePool .quantum :=
  Persistent.additionalSpace N + SpacePool.ofQuantumLayout (layout N) +
    completionAdditionalSpace N

/-- The actual prepared bank's resident frame agrees with the independent allocation shapes. -/
lemma bank_resident (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) : (bank base noQuantum N).residentSpace =
      base.residentSpace + (Persistent.additionalSpace N +
        SpacePool.ofQuantumLayout (layout N)) := by
  unfold bank bankContext
  rw [RuntimeCtx.residentSpace_addOwnedLayout, Persistent.context_resident]
  ac_rfl

/-- Actual initialization's resident peak is at most its complete prepared frame. -/
lemma ready_resident_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (path : (ready base noQuantum N).Path) :
    (ready base noQuantum N).peakResidentSpace path ≤
      (bank base noQuantum N).residentSpace := by
  rcases path with ⟨persistentPath, preparationPath⟩
  change (Circuit.seq (Persistent.initialization (model := executionModel N) base N)
    (Sampling.prepare (Persistent.context base N) (noQuantumStorage base noQuantum N) N)
    ).peakResidentSpace ⟨persistentPath, preparationPath⟩ ≤ _
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · exact (Persistent.initialization_resident_le (model := executionModel N) base N
      persistentPath).trans (by
      unfold bank bankContext
      rw [RuntimeCtx.residentSpace_addOwnedLayout]
      exact fun axis => Nat.le_add_left _ _)
  · exact (Circuit.prepare_peakResidentSpace
      (gates := AlgorithmGate.model)
      (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (Persistent.context base N) (Persistent.context base N).canonicalFreshKey (layout N)
      (Persistent.context base N).canonicalFreshKey_fresh
      (allocationDisjoint (Persistent.context base N) (noQuantumStorage base noQuantum N) N)
      preparationPath).le

/-- Every real first-cycle path pays its complete resident peak including initialization. -/
lemma code_resident_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).peakResidentSpace path ≤
      base.residentSpace + firstAdditionalSpace N := by
  rcases path with ⟨readyPath, roundPath⟩
  change (Circuit.seq (ready base noQuantum N)
    (Completion.code (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N))).peakResidentSpace
        ⟨readyPath, roundPath⟩ ≤ _
  rw [Circuit.peakResidentSpace_seq]
  have frame : (bank base noQuantum N).residentSpace + completionAdditionalSpace N =
      base.residentSpace + firstAdditionalSpace N := by
    rw [bank_resident]
    unfold firstAdditionalSpace
    ac_rfl
  apply SpacePool.max_le
  · exact ((ready_resident_le base noQuantum N readyPath).trans
      (fun axis => Nat.le_add_right _ _)).trans_eq frame
  · exact (Completion.code_resident_le (bank base noQuantum N) N input
      (bank_wires base noQuantum N) (cells base noQuantum N) (result base noQuantum N)
      roundPath).trans_eq frame

/-- The actual prepared bank's auxiliary frame agrees with the independent allocation shapes. -/
lemma bank_auxiliary (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) : (bank base noQuantum N).auxiliarySpace =
      base.auxiliarySpace + (Persistent.additionalSpace N +
        SpacePool.ofQuantumLayout (layout N)) := by
  unfold bank bankContext
  rw [RuntimeCtx.auxiliarySpace_addOwnedLayout, Persistent.context_auxiliary]
  ac_rfl

/-- Actual initialization's auxiliary peak is at most its complete prepared frame. -/
lemma ready_auxiliary_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (path : (ready base noQuantum N).Path) :
    (ready base noQuantum N).peakAuxiliarySpace path ≤
      (bank base noQuantum N).auxiliarySpace := by
  rcases path with ⟨persistentPath, preparationPath⟩
  change (Circuit.seq (Persistent.initialization (model := executionModel N) base N)
    (Sampling.prepare (Persistent.context base N) (noQuantumStorage base noQuantum N) N)
    ).peakAuxiliarySpace ⟨persistentPath, preparationPath⟩ ≤ _
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · exact (Persistent.initialization_auxiliary_le (model := executionModel N) base N
      persistentPath).trans (by
      unfold bank bankContext
      rw [RuntimeCtx.auxiliarySpace_addOwnedLayout]
      exact fun axis => Nat.le_add_left _ _)
  · exact (Circuit.prepare_peakAuxiliarySpace
      (gates := AlgorithmGate.model)
      (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (Persistent.context base N) (Persistent.context base N).canonicalFreshKey (layout N)
      (Persistent.context base N).canonicalFreshKey_fresh
      (allocationDisjoint (Persistent.context base N) (noQuantumStorage base noQuantum N) N)
      preparationPath).le

/-- Every real first-cycle path pays its complete auxiliary peak including initialization. -/
lemma code_auxiliary_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).peakAuxiliarySpace path ≤
      base.auxiliarySpace + firstAdditionalSpace N := by
  rcases path with ⟨readyPath, roundPath⟩
  change (Circuit.seq (ready base noQuantum N)
    (Completion.code (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N))).peakAuxiliarySpace
        ⟨readyPath, roundPath⟩ ≤ _
  rw [Circuit.peakAuxiliarySpace_seq]
  have frame : (bank base noQuantum N).auxiliarySpace + completionAdditionalSpace N =
      base.auxiliarySpace + firstAdditionalSpace N := by
    rw [bank_auxiliary]
    unfold firstAdditionalSpace
    ac_rfl
  apply SpacePool.max_le
  · exact ((ready_auxiliary_le base noQuantum N readyPath).trans
      (fun axis => Nat.le_add_right _ _)).trans_eq frame
  · exact (Completion.code_auxiliary_le (bank base noQuantum N) N input
      (bank_wires base noQuantum N) (cells base noQuantum N) (result base noQuantum N)
      roundPath).trans_eq frame

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized
