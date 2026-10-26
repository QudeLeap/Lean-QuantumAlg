/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Exists
import all QuantumAlg.Core.Execution.Instrument.Exists
public import QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Classical.Workspace
public import QuantumAlg.Core.Execution.Instrument.Reference.Support
import all QuantumAlg.Core.Execution.Instrument.Reference.Support

/-!
# Reference support through real classical records and local instruments
This is separate from unitary covariance: each actually unsupported reference
coordinate remains absent. Classical overwrite collisions, service-state
writes and lexical scope release are summed with all original blocks.
-/

namespace QuantumAlg.Execution

noncomputable section

open Instrument

open scoped BigOperators

attribute [local instance] Classical.decEq

variable {ctx : RuntimeCtx .quantum} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- Every actually absent reference coordinate remains absent in every real output record. -/
@[expose] public def ReferenceSupported (code : Circuit (.quantum gates oracles operations services)
  ctx ctx allowAllocation)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment) : Prop :=
  ∀ (Reference : Register) (allowed : Reference.Index → Prop)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    (∀ original basis, ¬allowed basis.2 → (state.block original).matrix basis basis = 0) →
    ∀ result basis, ¬allowed basis.2 →
      ((code.execute environment Reference state).block result).matrix basis basis = 0

/-- Actual classical processing, including overwrite fibers, preserves all quantum support. -/
lemma classical_reference_support {C D : Type} [Fintype C] [Fintype D]
    {Local Reference : Register} {decision : DecidableEq D}
    (state : ExecutionState C (Local.prod Reference))
    (update : C → D) (allowed : Reference.Index → Prop)
    (supported : ∀ original basis, ¬allowed basis.2 →
      (state.block original).matrix basis basis = 0)
    (result : D) (basis : (Local.prod Reference).Index) (absent : ¬allowed basis.2) :
    ((@ExecutionState.mapClassical C D _ _ (Local.prod Reference) decision state update).block
      result).matrix basis basis = 0 := by
  rw [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro original _
  by_cases selected : update original = result
  · simp only [if_pos selected]
    exact supported original basis absent
  · simp only [if_neg selected, Matrix.zero_apply]

/-- The full actual finite local instrument retains every unsupported reference coordinate. -/
lemma HasInstrument.reference_supported
    {code : Circuit (.quantum gates oracles operations services)
      ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles operations
      services).Environment}
    (actual : HasInstrument code environment) : ReferenceSupported code environment := by
  rcases actual with ⟨Outcome, finite, ⟨instrument⟩⟩
  let : Fintype Outcome := finite
  intro Reference allowed History _ state supported result basis absent
  exact retained_reference_support
    (fun current => code.execute environment Reference current)
    (retainedRecord (services := services) instrument.record)
    (fun original outcome => instrument.operator original.1 outcome)
    (by
      intro current selected
      exact (instrument.blocks Reference current selected).trans
        (sum_condition_decisions _ _ _ _)) allowed state supported result basis absent

/-- Actual chronological execution preserves reference support through its two real histories. -/
lemma ReferenceSupported.seq
    {first second : Circuit (.quantum gates oracles operations services)
  ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles operations services).Environment}
    (head : ReferenceSupported first environment) (tail : ReferenceSupported second environment) :
    ReferenceSupported (first.seq second) environment := by
  intro Reference allowed History _ state supported result basis absent
  rw [Circuit.execute_seq]
  dsimp only [State.mapHistory]
  exact classical_reference_support _ _ allowed
    (tail Reference allowed _ (head Reference allowed state supported)) result basis absent

/-- The actual identity embedding retains support of the same unallocated child. -/
lemma ReferenceSupported.embed_identity
    {code : Circuit (.quantum gates oracles operations services)
  ctx ctx false}
    {environment : (ExecutionModel.quantum gates oracles operations
      services).Environment} (actual : ReferenceSupported code environment) :
    ReferenceSupported
      (Circuit.embed (allowAllocation := true) (ContextEmbedding.identity _) code) environment := by
  intro Reference allowed History _ state supported result basis absent
  rw [Circuit.execute_identity_embed]
  exact actual Reference allowed state supported result basis absent

/-- Actual lexical workspace push/body/pop preserves every unsupported reference coordinate. -/
lemma ReferenceSupported.workspace (environment : (ExecutionModel.quantum gates oracles operations
  services).Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh)
      (ctx.addWorkspace key shape fresh) true)
    (actual : ReferenceSupported body environment) :
    ReferenceSupported (Circuit.workspace (model := .quantum gates oracles operations services)
      ctx key shape fresh body) environment := by
  intro Reference allowed History _ state supported result basis absent
  rw [Circuit.execute_workspace]
  dsimp only [State.pushWorkspace, State.popWorkspace]
  exact classical_reference_support _ _ allowed
    (actual Reference allowed _
      (classical_reference_support state _ allowed supported)) result basis absent

end

end QuantumAlg.Execution
