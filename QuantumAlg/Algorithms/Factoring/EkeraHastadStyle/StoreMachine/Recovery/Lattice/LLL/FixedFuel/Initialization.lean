/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Input.WideBasis.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Reset.Resources

/-!
# Original wide LLL wiring and actual latch initialization

The original raw-cell wiring connects actual wide sample decoding with the
actual fixed-fuel driver. Its existing two-bit reset uses the same native
Circuit operations and preserves the complete original basis and Gram frame.
The source full-rank and width obligations depend on the actual original samples.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelInitializationMachine

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The common wide raw-word width required by the literal LLL driver. -/
abbrev Width (N : Nat) : Nat :=
  RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)

/-- Caller-owned references shared by the actual wide initializer and driver. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the pair stage. -/
  pair : BatchMachine.PairRefs ctx N
  /-- Nested references for the raw stage. -/
  raw : LatticeLoading.RawOutputRefs ctx (Width N)
  roles : LatticeRepresentation.WorkspaceRoles raw
  /-- Nested references for the driver stage. -/
  driver : LatticeFixedFuelMachine.Refs ctx (Width N)
  basisWiring :
    LatticeRepresentation.basisRefs raw roles = driver.machine.basis

/-- The original terminal pair decoded by the actual wide initializer. -/
def sourceSamples {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (before : Store ctx) :
    RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) ×
      RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) :=
  (BatchMachine.sourceSample N before (BatchMachine.terminalInput refs.pair.first),
    BatchMachine.sourceSample N before (BatchMachine.terminalInput refs.pair.second))

/-- The pure short-log basis selected by the original terminal pair. -/
def sourceBasis {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (before : Store ctx) :
    NumberTheory.IntegerBasis3 :=
  RSA.shortLogLatticeBasis (shortLogBits N) (tradeoffBits N)
    (sourceSamples refs before)

/-- The first-phase mathematical state corresponding to one source basis. -/
def initialLLLState {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (before : Store ctx) :
    NumberTheory.LLLState3 :=
  { basis := sourceBasis refs before
    phase := .first
    steps := [] }

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The original initialization references have the exact wide decoder/basis view. -/
def prefixRefs (refs : Refs ctx N) : LatticeWideInitializationPrefix.Refs ctx N where
  pair := refs.pair
  raw := refs.raw
  roles := refs.roles

/-- Every original two-sample source basis has full rank, independent of any stored workspace. -/
theorem sourceBasis_fullRank (refs : Refs ctx N) (store : Store ctx) :
    (sourceBasis refs store).FullRank :=
  RSA.shortLogLatticeBasis_fullRank _ _ _

/-- The original wide raw width meets the actual fixed-fuel driver's source capacity requirement. -/
theorem sourceBasis_capacity (refs : Refs ctx N) (store : Store ctx) :
    Nat.size (256 * (NumberTheory.lllStateEnvelope3 (sourceBasis refs store) + 1) ^ 8) + 1 ≤
      Width N :=
  LatticeStepBounds.shortLog_coordinateWidth_capacity N (shortLogBits N)
    (tradeoffBits N) (sourceSamples refs store)

/-- Actual wide decoding initializes precisely the original basis view of the mutable LLL driver. -/
theorem prefix_basisRepresents {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N)
    (separation : LatticeWideInitializationPrefix.Separation (prefixRefs refs))
    (store : Store ctx) (zeros : LatticeWideInitializationPrefix.BasisInitialZero store
      (prefixRefs refs)) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store).1
      refs.driver.machine.basis (sourceBasis refs store) := by
  rw [← refs.basisWiring]
  exact LatticeWideInitializationPrefix.decodeBasisInto_metricBasis (prefixRefs refs)
    separation store zeros

/-- The original two-latch reset uses the actual shared native reset implementation. -/
abbrev resetFirstInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) : Circuit model ctx ctx :=
  LatticeFixedFuelMachine.resetFirstInto refs.driver

/-- The actual chronological reset store of the original two machine latches. -/
abbrev resetFirstStore (refs : Refs ctx N) (store : Store ctx) : Store ctx :=
  LatticeFixedFuelMachine.resetFirstStore refs.driver store

/-- The actual original reset retains every incoming state block and its full history. -/
theorem resetFirstInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (resetFirstInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := LatticeFixedFuelMachine.resetFirstStep (model := model) refs.driver entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  LatticeFixedFuelMachine.resetFirstInto_execute refs.driver Reference state

/-- The actual original reset preserves every read outside the two latch identities. -/
theorem resetFirstInto_callerFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (phase : refs.driver.machine.secondPhase.key ∉ other.storageKeys)
    (done : refs.driver.machine.done.key ∉ other.storageKeys) :
    (resetFirstStore refs store).read other = store.read other :=
  LatticeFixedFuelMachine.resetFirstInto_callerFrame refs.driver store other phase done

/-- The actual reset establishes the first phase under the original machine-only separation. -/
theorem resetFirstInto_phase (refs : Refs ctx N) (separation : refs.driver.machine.Separated)
    (store : Store ctx) :
    refs.driver.machine.PhaseRepresents (resetFirstStore refs store) .first := by
  have different : refs.driver.machine.done.key ≠ refs.driver.machine.secondPhase.key := by
    intro equal
    have impossible : LatticeState.MachineCell.done = .secondPhase := separation equal
    cases impossible
  constructor
  · change (((store.applyOp
      (LatticeFixedFuelMachine.clearOp refs.driver.machine.secondPhase)).applyOp
      (LatticeFixedFuelMachine.clearOp refs.driver.machine.done)).read
      (.storage refs.driver.machine.secondPhase.toCStorageRef)).toBool = false
    rw [LatticeFixedFuelMachine.clear_frame _ _ _
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using different)]
    exact LatticeFixedFuelMachine.clear_read _ store
  · exact LatticeFixedFuelMachine.clear_read _ _

/-- Original machine separation keeps each basis coordinate outside either actual latch write. -/
theorem basis_avoids_latch (refs : Refs ctx N) (separation : refs.driver.machine.Separated)
    (cell : LatticeMetricMachine.BasisCell) (target : LatticeState.MachineCell)
    (different : LatticeFixedFuelMachine.basisMachineCell cell ≠ target) :
    refs.driver.machine.keyOf target ∉
      (LatticeMetricMachine.basisCellInput refs.driver.machine.basis cell).storageKeys := by
  have keyNe : refs.driver.machine.keyOf target ≠
      refs.driver.machine.keyOf (LatticeFixedFuelMachine.basisMachineCell cell) := by
    intro equal
    exact different (separation equal).symm
  cases cell <;> simpa only [LatticeMetricMachine.basisCellInput, LatticeState.coordinateInput,
    CInputRef.storageKeys, List.mem_singleton, LatticeFixedFuelMachine.basisMachineCell,
    LatticeState.MachineRefs.keyOf] using keyNe

/-- The actual original reset retains each original mutable basis word. -/
theorem resetFirstInto_basis_callerFrame (refs : Refs ctx N)
    (separation : refs.driver.machine.Separated) (store : Store ctx)
    (cell : LatticeMetricMachine.BasisCell) :
    (resetFirstStore refs store).read
      (LatticeMetricMachine.basisCellInput refs.driver.machine.basis cell)
      = store.read (LatticeMetricMachine.basisCellInput refs.driver.machine.basis cell) :=
  resetFirstInto_callerFrame refs store _
    (basis_avoids_latch refs separation cell .secondPhase (by cases cell <;> decide))
    (basis_avoids_latch refs separation cell .done (by cases cell <;> decide))

/-- The actual original latch reset retains every Gram word and the original Gram scratch. -/
theorem resetFirstInto_metric_callerFrame (refs : Refs ctx N)
    (separation : LatticeFixedFuelMachine.Separation refs.driver) (store : Store ctx)
    (cell : LatticeMetricMachine.MetricCell) :
    (resetFirstStore refs store).read
      (.storage (LatticeMetricMachine.metricCellRef refs.driver.metric cell).toCStorageRef) =
      store.read
        (.storage (LatticeMetricMachine.metricCellRef refs.driver.metric cell).toCStorageRef) :=
  resetFirstInto_callerFrame refs store _
    (LatticeFixedFuelMachine.latch_avoids_metric refs.driver refs.driver.machine.secondPhase
      separation.secondPhaseMetric cell)
    (LatticeFixedFuelMachine.latch_avoids_metric refs.driver refs.driver.machine.done
      separation.doneMetric cell)

/-- The original reset emits exactly two independent native XOR instructions. -/
theorem resetFirstInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (path : (resetFirstInto refs).Path) :
    (resetFirstInto refs).eventTrace path = LatticeFixedFuelMachine.resetFirstTrace :=
  LatticeFixedFuelMachine.resetFirstInto_events refs.driver path

/-- The actual original reset restores borrowed storage jointly with all external references. -/
theorem resetFirstInto_borrowedRestored {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (resetFirstInto refs).BorrowedRestored Reference state
      ((resetFirstInto refs).execute Reference state) :=
  LatticeFixedFuelMachine.resetFirstInto_borrowedRestored refs.driver Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelInitializationMachine
