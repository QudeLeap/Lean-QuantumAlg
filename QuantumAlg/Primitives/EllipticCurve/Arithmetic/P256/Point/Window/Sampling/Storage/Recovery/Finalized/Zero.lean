/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Induction
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Observe.Grouping
import all QuantumAlg.Core.Execution.Restart.Sequence
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing.State

/-!
# Complete terminal zero state of the actual three-attempt program

The physical cleanup runs after all three attempts but inside the original
feedback scope. Its zero state survives the identity placement, the preceding
attempts, release of each real classical workspace cell, and the final paid
result pack. Every statement retains arbitrary external references and complete
Store, service, incoming-history and actual-path records.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage.Inputs

noncomputable section

open Execution ClassicalWorkspace ClassicalRoutines

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def zeroSeed (ctx : RuntimeCtx .quantum) :
    (ctx.quantumLayout.selectedRegister Finset.univ).Index :=
  ctx.quantumLayout.restrictSelectedBasis Finset.univ (fun _ => 0)

/-- The complete selected zero-state obligation, sealed during structure construction. -/
private def FullyZeroStatement {services : ClassicalOracleModel}
    {pre post : RuntimeCtx .quantum} {allowAllocation : Bool}
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      pre post allowAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference (services.HiddenState × History))
    (record : Store post × (services.HiddenState × (History × code.Path))),
    (StatePromise.pure (NormalizedVector.ket (R := post.quantumLayout.selectedRegister
      Finset.univ) (zeroSeed post))).Holds
      (DensityOperator.observeSelection post.quantumLayout Finset.univ Reference
        ((code.execute environment Reference state).block record))

/-- One fixed zero ket is present in every complete record of the actual code. -/
private structure FullyZero {services : ClassicalOracleModel} {pre post : RuntimeCtx .quantum}
    {allowAllocation : Bool}
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      pre post allowAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Prop where
  holds : FullyZeroStatement code environment

attribute [local irreducible] FullyZeroStatement Circuit.execute Circuit.pathFintype
  ExecutionState.mapClassical

/-- An identity placement executes the proved whole-bank physical reset itself. -/
private lemma cleanup_identity_fullyZero {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (cleanup : Cleanup.Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    FullyZero (Circuit.embed (allowAllocation := true) (ContextEmbedding.identity ctx)
      (cleanup.circuit (services := services))) environment := by
  suffices full : FullyZeroStatement
      (Circuit.embed (allowAllocation := true) (ContextEmbedding.identity ctx)
        (cleanup.circuit (services := services))) environment from
    FullyZero.mk full
  unfold FullyZeroStatement
  intro Reference History _ state record
  rw [Circuit.execute_identity_embed]
  exact cleanup.circuit_pure_fullSelection environment state record

/-- A history relabeling is a classical map at the original State carrier,
independently of the output equality-decision representation. -/
private lemma mapHistory_eq_mapClassical_read
    {ctx : RuntimeCtx .quantum} (Reference : Register)
    {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (update : H → K)
    (read : Store ctx × H → Store ctx × K)
    (same : ∀ entry : Store ctx × H,
      (entry.1, update entry.2) = read entry)
    (decision : DecidableEq (Store ctx × K)) :
    state.mapHistory update =
      @ExecutionState.mapClassical (Store ctx × H) (Store ctx × K)
        _ _ (Register.prod ctx.register Reference) decision state read := by
  unfold State.mapHistory
  exact ExecutionState.executionState_mapClassical_congr_decision
    state (fun entry => (entry.1, update entry.2)) read same _ decision

/-- Stage full classical grouping of selected pure blocks in its own
generic proof declaration, preserving every record and reference entry. -/
private lemma observeSelected_mapClassical_pure_staged
    {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (Reference : Register)
    {C D : Type} [Fintype C] [Fintype D]
    (state : ExecutionState C (Register.prod layout.register Reference))
    (read : C → D)
    (target : NormalizedVector (layout.selectedRegister selection))
    (held : ∀ entry : C,
      (StatePromise.pure target).Holds
        (DensityOperator.observeSelection layout selection Reference
          (state.block entry)))
    (result : D) :
    (StatePromise.pure target).Holds
      (DensityOperator.observeSelection layout selection Reference
        ((state.mapClassical read).block result)) := by
  let selectedState : ExecutionState C (layout.selectedRegister selection) :=
    ExecutionState.observeSelected layout selection Reference state
  have selectedHeld : ∀ entry : C,
      (StatePromise.pure target).Holds (selectedState.block entry) := held
  have selectedGrouped : (StatePromise.pure target).Holds
      ((selectedState.mapClassical read).block result) := by
    exact ExecutionState.mapClassical_pure selectedState read target
      selectedHeld result
  have observeCommutes :
      DensityOperator.observeSelection layout selection Reference
        ((state.mapClassical read).block result) =
      ((selectedState.mapClassical read).block result) := by
    exact ExecutionState.observeSelected_mapClassical
      layout selection Reference state read result
  exact observeCommutes.symm ▸ selectedGrouped

/-- Pure selected blocks survive a history-only relabeling at its exact
Store × History carrier; all quantum and reference entries are retained. -/
private lemma observeSelected_mapHistory_pure
    {ctx : RuntimeCtx .quantum} (selection : Finset (Fin ctx.systemCount))
    (Reference : Register) {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (update : H → K)
    (target : NormalizedVector (ctx.quantumLayout.selectedRegister selection))
    (held : ∀ entry : Store ctx × H,
      (StatePromise.pure target).Holds
        (DensityOperator.observeSelection ctx.quantumLayout selection Reference
          (state.block entry)))
    (result : Store ctx × K) :
    (StatePromise.pure target).Holds
      (DensityOperator.observeSelection ctx.quantumLayout selection Reference
        ((state.mapHistory update).block result)) := by
  let bodyState : ExecutionState (Store ctx × H)
      (Register.prod ctx.quantumLayout.register Reference) := state
  let read : Store ctx × H → Store ctx × K :=
    fun entry => (entry.1, update entry.2)
  let releasedState : ExecutionState (Store ctx × K)
      (Register.prod ctx.quantumLayout.register Reference) :=
    state.mapHistory update
  have heldBody : ∀ entry : Store ctx × H,
      (StatePromise.pure target).Holds
        (DensityOperator.observeSelection ctx.quantumLayout selection Reference
          (bodyState.block entry)) := held
  have grouped := observeSelected_mapClassical_pure_staged
    ctx.quantumLayout selection Reference bodyState read target heldBody result
  have sameRead : ∀ entry : Store ctx × H,
      (entry.1, update entry.2) = read entry := by
    intro entry
    dsimp only [read]
  have releasedEqState :=
    mapHistory_eq_mapClassical_read (ctx := ctx) (H := H) (K := K)
      Reference state update read sameRead (Classical.decEq _)
  have observedEq := congrArg
    (fun mapped : ExecutionState (Store ctx × K)
      (Register.prod ctx.register Reference) =>
      DensityOperator.observeSelection ctx.quantumLayout selection Reference
        (mapped.block result)) releasedEqState
  exact observedEq.symm ▸ grouped

/-- A final fixed state is independent of every earlier actual instruction. -/
private lemma fullyZero_after {services : ClassicalOracleModel}
    {pre middle post : RuntimeCtx .quantum} {allowAllocation : Bool}
    (first : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      pre middle allowAllocation)
    (second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      middle post allowAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (fixed : FullyZero second environment) :
    FullyZero (first.seq second) environment := by
  suffices full : FullyZeroStatement (first.seq second) environment from
    FullyZero.mk full
  unfold FullyZeroStatement
  intro Reference History _ state record
  rw [Circuit.execute_seq]
  let firstState := first.execute environment Reference state
  let secondState : State post Reference
      (services.HiddenState × ((History × first.Path) × second.Path)) :=
    second.execute environment Reference firstState
  let update : services.HiddenState × ((History × first.Path) × second.Path) →
      services.HiddenState × (History × (first.Path × second.Path)) :=
    fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))
  have fixedComplete := fixed.holds
  unfold FullyZeroStatement at fixedComplete
  have held : ∀ entry : Store post ×
      (services.HiddenState × ((History × first.Path) × second.Path)),
      (StatePromise.pure (NormalizedVector.ket (zeroSeed post))).Holds
        (DensityOperator.observeSelection post.quantumLayout Finset.univ
          Reference (secondState.block entry)) := by
    intro entry
    exact fixedComplete Reference firstState entry
  have grouped :
      (StatePromise.pure (NormalizedVector.ket (zeroSeed post))).Holds
        (DensityOperator.observeSelection post.quantumLayout Finset.univ
          Reference ((secondState.mapHistory update).block record)) := by
    exact observeSelected_mapHistory_pure Finset.univ Reference secondState
      update (NormalizedVector.ket (zeroSeed post)) held record
  exact grouped

/-- The workspace constructor preserves its body's complete path record. -/
private def workspaceBodyRecord {model : ExecutionModel}
    {inner : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (code : Circuit model (inner.addWorkspace key shape fresh)
      (inner.addWorkspace key shape fresh)) {History : Type}
    (record : Store inner × (model.HiddenState ×
      (History × (Circuit.workspace inner key shape fresh code).Path))) :
    Store inner × (model.HiddenState × (History × code.Path)) :=
  (record.1, (record.2.1, (record.2.2.1,
    cast (show (Circuit.workspace inner key shape fresh code).Path = code.Path by rfl)
      record.2.2.2)))

/-- A classical block is independent of how equality on its records is decided. -/
private lemma mapClassical_block_decision {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (state : ExecutionState C R) (read : C → D)
    (first second : DecidableEq D) (result : D) :
    (@ExecutionState.mapClassical C D _ _ R first state read).block result =
      (@ExecutionState.mapClassical C D _ _ R second state read).block result := by
  exact congrArg
    (fun decision : DecidableEq D =>
      (@ExecutionState.mapClassical C D _ _ R decision state read).block result)
    (Subsingleton.elim first second)

/-- Selected pure blocks remain pure for any equality-decision representation. -/
private lemma observeSelected_mapClassical_pure_staged_any_decision
    {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (Reference : Register)
    {C D : Type} [Fintype C] [Fintype D]
    (state : ExecutionState C (Register.prod layout.register Reference))
    (read : C → D)
    (target : NormalizedVector (layout.selectedRegister selection))
    (held : ∀ entry : C,
      (StatePromise.pure target).Holds
        (DensityOperator.observeSelection layout selection Reference
          (state.block entry)))
    (result : D) :
    ∀ decision : DecidableEq D,
      (StatePromise.pure target).Holds
        (DensityOperator.observeSelection layout selection Reference
          ((@ExecutionState.mapClassical C D _ _
            (Register.prod layout.register Reference) decision state read).block result)) := by
  intro decision
  have canonical := observeSelected_mapClassical_pure_staged
    layout selection Reference state read target held result
  have blockEq := mapClassical_block_decision state read
    (Classical.decEq D) decision result
  have observedEq := congrArg
    (fun density : DensityOperator (Register.prod layout.register Reference) =>
      DensityOperator.observeSelection layout selection Reference density)
    blockEq
  exact observedEq ▸ canonical

/-- Releasing an actual workspace identifies each complete output block. -/
private lemma workspace_block_body_record {model : ExecutionModel}
    {inner : RuntimeCtx model.kind}
    (environment : model.Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (code : Circuit model (inner.addWorkspace key shape fresh)
      (inner.addWorkspace key shape fresh))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State inner Reference (model.HiddenState × History))
    (record : Store inner × (model.HiddenState ×
      (History × (Circuit.workspace inner key shape fresh code).Path))) :
    ((Circuit.workspace inner key shape fresh code).execute environment Reference state).block
      record =
    ((code.execute environment Reference (state.pushWorkspace key shape fresh)).mapClassical
      (fun entry => (Store.popWorkspace key shape fresh entry.1, entry.2))).block
        (workspaceBodyRecord key shape fresh code record) := by
  have recordEq : workspaceBodyRecord key shape fresh code record = record := rfl
  rw [recordEq]
  rw [Circuit.execute_workspace]
  rw [State.state_popWorkspace_as_mapClassical key shape fresh Reference
    (code.execute environment Reference (state.pushWorkspace key shape fresh))]
  let bodyState : ExecutionState
      (Store (inner.addWorkspace key shape fresh) ×
        (model.HiddenState × (History × code.Path)))
      (Register.prod inner.register Reference) :=
    code.execute environment Reference (state.pushWorkspace key shape fresh)
  exact mapClassical_block_decision bodyState
    (fun entry => (Store.popWorkspace key shape fresh entry.1, entry.2))
    _ _ record

/-- Releasing one lexical classical cell groups records but keeps their common
complete physical zero state. -/
private lemma fullyZero_workspace {services : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (fixed : FullyZero body environment) :
    FullyZero (Circuit.workspace
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx key shape fresh body) environment := by
  suffices full : FullyZeroStatement
      (Circuit.workspace
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx key shape fresh body) environment from
    FullyZero.mk full
  unfold FullyZeroStatement
  intro Reference History _ state record
  have fixedComplete := fixed.holds
  unfold FullyZeroStatement at fixedComplete
  let bodyState : ExecutionState
      (Store (ctx.addWorkspace key shape fresh) ×
        (services.HiddenState × (History × body.Path)))
      (Register.prod ctx.quantumLayout.register Reference) :=
    body.execute environment Reference (state.pushWorkspace key shape fresh)
  let bodyRecord := workspaceBodyRecord key shape fresh body record
  have held : ∀ entry : Store (ctx.addWorkspace key shape fresh) ×
      (services.HiddenState × (History × body.Path)),
      (StatePromise.pure (NormalizedVector.ket (zeroSeed ctx))).Holds
        (DensityOperator.observeSelection ctx.quantumLayout Finset.univ
          Reference (bodyState.block entry)) := by
    intro entry
    exact fixedComplete Reference (state.pushWorkspace key shape fresh) entry
  have groupedAll := observeSelected_mapClassical_pure_staged_any_decision
    ctx.quantumLayout Finset.univ Reference bodyState
    (fun entry => (Store.popWorkspace key shape fresh entry.1, entry.2))
    (NormalizedVector.ket (zeroSeed ctx)) held bodyRecord
  have blockEq :=
    workspace_block_body_record environment key shape fresh body Reference state record
  have observedEq := congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      DensityOperator.observeSelection ctx.quantumLayout Finset.univ
        Reference density)
    blockEq
  exact observedEq.symm ▸ groupedAll _

/-- All actual feedback-cell allocations and releases preserve a body's
complete zero-state proof, with no constraint on their stored values. -/
private lemma fullyZero_withFrame {services : ClassicalOracleModel}
    (ctx : RuntimeCtx .quantum) (wordWidth parityCount : Nat)
    (body : ∀ {inner : RuntimeCtx .quantum} (transport : Transport ctx inner),
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      (frame : Frame inner wordWidth parityCount) → CallerFree frame transport →
      Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (fixed : ∀ {inner : RuntimeCtx .quantum} (transport : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (frame : Frame inner wordWidth parityCount) (fresh : CallerFree frame transport),
      FullyZero (body transport same frame fresh) environment) :
    FullyZero (withFrame
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx wordWidth parityCount body) environment := by
  unfold withFrame withCellsWithQuantumWires
  exact withCellsWithQuantumWiresFrom_property
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (Transport.id ctx) rfl (shapes wordWidth parityCount)
    (fun cells distinct transport separated same =>
      body transport (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct transport separated))
    (fun {inner} _ _ (code : Circuit
      (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner) =>
      FullyZero code environment)
    (fun _ _ key shape fresh code available =>
      fullyZero_workspace environment key shape fresh code available)
    (fun cells distinct transport separated same =>
      fixed transport (quantumLayout_wires_of_quantumWires same)
        (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct transport separated))

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local irreducible] scopedAttemptsFinalized withFrame

/-- Every complete output record of the three actual attempts followed by the
whole-bank physical reset has the same all-zero quantum state. -/
private lemma scopedAttemptsFinalized_fullyZero (count : Nat) :
    FullyZero (original.scopedAttemptsFinalized (services := services) count) environment := by
  unfold scopedAttemptsFinalized
  apply fullyZero_withFrame
  intro inner lift same frame fresh
  let retained := original.transport (Recovery.persistentTransport ctx)
    (Recovery.persistent_wires ctx)
  let sampler := retained.samplerParameters lift same frame fresh
  let inputs := retained.transport lift same
  let checkers := (Checkers.retained ctx).transport lift
  let cleanup := finalizedCleanup sampler
  exact fullyZero_after
    (Circuit.forRange count fun _ => inputs.attempt (services := services) sampler checkers)
    (Circuit.embed (allowAllocation := true) (ContextEmbedding.identity inner)
      (cleanup.circuit (services := services))) environment
    (cleanup_identity_fullyZero cleanup environment)

/-- On a fully owned bank, the complete all-wire zero statement is the
standard physical reinitialization certificate. -/
private lemma fullyZero_reinitializedAt {services : ClassicalOracleModel}
    {pre post : RuntimeCtx .quantum} {allowAllocation : Bool}
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      pre post allowAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (noBorrowed : post.borrowedQuantumWires = [])
    (fixed : FullyZero code environment) :
    Circuit.ReinitializedAt code environment
      (post.quantumLayout.restrictSelectedBasis post.borrowedSelectionᶜ (fun _ => 0)) := by
  have empty : post.borrowedSelection = ∅ := by
    ext wire
    simp only [RuntimeCtx.mem_borrowedSelection, noBorrowed, List.not_mem_nil,
      Finset.notMem_empty]
  have all : post.borrowedSelectionᶜ = Finset.univ := by
    simp only [empty, Finset.compl_empty]
  unfold Circuit.ReinitializedAt
  rw [all]
  have fixedComplete := fixed.holds
  unfold FullyZeroStatement at fixedComplete
  simpa only [zeroSeed, ExecutionModel.HiddenState,
    ExecutionModel.classicalOracles] using fixedComplete

/-- One fixed physical zero state reaches the complete actual packed output,
after the old retained checker cells and all three actual attempts. -/
lemma runFinalized_reinitializedAt (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (original.runFinalized (services := services)).code environment
      (EllipticCurve.CandidateCheck.Native.finalPackSeed ctx 256 260
        (QuantumLayout.restrictSelectedBasis
          (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).quantumLayout
          (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).borrowedSelectionᶜ
          (fun _ => 0))) := by
  have persistentOwned :
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).borrowedQuantumWires =
        [] :=
    (EllipticCurve.CandidateCheck.Native.persistentCtx_borrowedQuantumWires
      ctx 256 260).trans noBorrowed
  have scopedZero := original.scopedAttemptsFinalized_fullyZero environment 3
  have scopedFixed := fullyZero_reinitializedAt
    (original.scopedAttemptsFinalized (services := services) 3)
    environment persistentOwned scopedZero
  have retainedFixed := Circuit.RestartCleanup.afterAt
    (EllipticCurve.CandidateCheck.Native.retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260)
    (original.scopedAttemptsFinalized (services := services) 3) environment _ scopedFixed
  exact EllipticCurve.CandidateCheck.Native.packedReinitializedAt
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    ctx 256 260 _ _ retainedFixed

end

end Storage.Inputs

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
