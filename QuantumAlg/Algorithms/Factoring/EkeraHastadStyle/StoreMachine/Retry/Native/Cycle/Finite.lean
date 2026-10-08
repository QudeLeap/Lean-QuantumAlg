/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.InputProtocol
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Classical
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.ReuseBoundary
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint

/-!
# Complete native factoring cycles for every finite batch count

The independent caller plan follows the real first-batch and recursive reused
batch contexts. Every quantum leaf is one complete sixteen-round factoring
trial with its actual recovery. Its scientific seed domain is established by
the preceding actual output, including persistent service state. Unconditional
physical cleanup proves the owned bank has one fixed seed at every restart.

Zero batches execute only the original classical empty-result allocation. A
positive run includes its actual chronological classical selector. Whole-run
correctness, failure, output-state and resource contracts are unchanged. The
maximum complete-cycle allowance is uniform over positive batch counts and
comes from independent first/reused batch formulas, not the run's depth.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.Finite

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Schedule assembly needs the actual suffix constructors, not the internal batch circuits.
attribute [local irreducible] NativeBatchRecovery.code NativeBatchReuseRecovery.code

variable {N : Nat}

/-- The caller requests the given number of complete further trials on its existing bank. -/
def suffixPlan (input : Input N) : (start : RuntimeCtx .quantum) →
    (wires : start.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires) →
    (count : Nat) → CyclePlan RuntimeRound.model start
      (NativeRetryChain.suffixContext N start count) .unit
  | start, _, 0 => .classical (Idle.problem start)
  | start, wires, count + 1 =>
      .seq (.cycle (InputProtocol.ReuseBatch.problem start wires input))
        (suffixPlan input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires) count)

private theorem liftedDistinct (start : RuntimeCtx .quantum)
    (cells : Fin (measurementBits N) → CWriteRef start (.finite 2))
    (distinct : Function.Injective (fun index => (cells index).key)) :
    Function.Injective (fun index => (NativeRetryChain.reuseWrite N (cells index)).key) := by
  intro left right same
  apply distinct
  exact (NativeRetryChain.reuseWrite_key N (cells left)).symm.trans
    (same.trans (NativeRetryChain.reuseWrite_key N (cells right)))

private theorem nextNoBorrowed (input : Input N) (start : RuntimeCtx .quantum)
    (wires : start.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
    (cells : Fin (measurementBits N) → CWriteRef start (.finite 2))
    (noBorrowed : start.borrowedQuantumWires = []) :
    (NativeBatchReuseRecovery.context start N).borrowedQuantumWires = [] :=
  (NativeBatchReuseRecovery.code start wires cells input).borrowedQuantumWires_preserved.trans
    noBorrowed

/-- Each actual reused output supplies the independently fixed seed domain of the next trial. -/
theorem suffixEntry (input : Input N) (start : RuntimeCtx .quantum)
    (wires : start.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
    (cells : Fin (measurementBits N) → CWriteRef start (.finite 2)) (count : Nat) :
    Circuit.EntryCompatible (.cycle (InputProtocol.ReuseBatch.problem start wires input))
      (suffixPlan input (NativeBatchReuseRecovery.context start N)
        ((NativeBatchReuseRecovery.context_base_wires start N).trans wires) count)
      (NativeBatchReuseRecovery.code start wires cells input) := by
  intro Reference original _admitted
  cases count with
  | zero => exact ⟨True.intro, True.intro⟩
  | succ count =>
      refine ⟨?_, True.intro⟩
      exact nextInput_seedDomain (NativeBatchReuseRecovery.code start wires cells input)
        (ReuseBatch.seed start wires) original
        (reuseBatch_seedBlocks start wires cells input
          (original.state.mapClassical (fun entry => (entry.1, (entry.2, ())))))

/-- The actual recursive suffix executes exactly the caller's independent remaining trials. -/
def suffixSchedule (input : Input N) : (start : RuntimeCtx .quantum) →
    (wires : start.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires) →
    (cells : Fin (measurementBits N) → CWriteRef start (.finite 2)) →
    (distinct : Function.Injective (fun index => (cells index).key)) →
    (noBorrowed : start.borrowedQuantumWires = []) → (count : Nat) →
    Circuit.CycleSchedule (suffixPlan input start wires count)
      (NativeRetryChain.suffixCode input start wires cells count)
  | start, _, _, _, _, 0 => Idle.schedule start
  | start, wires, cells, distinct, noBorrowed, count + 1 =>
      .seq (NativeBatchReuseRecovery.code start wires cells input)
        (NativeRetryChain.suffixCode input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => NativeRetryChain.reuseWrite N (cells index)) count)
        (.complete _
          (InputProtocol.ReuseBatch.complete start wires cells input distinct noBorrowed))
        (suffixSchedule input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => NativeRetryChain.reuseWrite N (cells index))
          (liftedDistinct start cells distinct)
          (nextNoBorrowed input start wires cells noBorrowed) count)
        (suffixEntry input start wires cells count)
        (.inr ⟨reuseBatch_restartCleanup start wires cells input noBorrowed⟩)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- One independently specified first trial precedes the independently requested suffix. -/
def chainPlan (input : Input N) (count : Nat) :
    CyclePlan RuntimeRound.model base (NativeRetryChain.context base noQuantum N count) .unit :=
  .seq (.cycle (InputProtocol.FirstBatch.problem base noQuantum input))
    (suffixPlan input (NativeBatchRecovery.context base noQuantum N)
      (NativeRetryChain.firstWires base noQuantum N) count)

/-- The first actual completed batch establishes the next trial's local seed admission. -/
theorem firstEntry (input : Input N) (count : Nat) :
    Circuit.EntryCompatible (.cycle (InputProtocol.FirstBatch.problem base noQuantum input))
      (suffixPlan input (NativeBatchRecovery.context base noQuantum N)
        (NativeRetryChain.firstWires base noQuantum N) count)
      (NativeBatchRecovery.code base noQuantum input) := by
  intro Reference original _admitted
  cases count with
  | zero => exact ⟨True.intro, True.intro⟩
  | succ count =>
      refine ⟨?_, True.intro⟩
      exact nextInput_seedDomain (NativeBatchRecovery.code base noQuantum input)
        (FirstBatch.seed base noQuantum N) original
        (NativeBatchRecovery.code_seedBlocks base noQuantum input
          (original.state.mapClassical (fun entry => (entry.1, (entry.2, ())))))

/-- The original chain follows the independent first-plus-suffix caller plan. -/
def chainSchedule (input : Input N) (count : Nat) :
    Circuit.CycleSchedule (chainPlan base noQuantum input count)
      (NativeRetryChain.code base noQuantum input count) :=
  .seq _ _ (.complete _ (InputProtocol.FirstBatch.complete base noQuantum input))
    (suffixSchedule input (NativeBatchRecovery.context base noQuantum N)
      (NativeRetryChain.firstWires base noQuantum N) (NativeRetryChain.firstCells base noQuantum N)
      (NativeRetryChain.cells_distinct base noQuantum N 0)
      (NativeBatchRecovery.context_noBorrowedQuantum base noQuantum N) count)
    (firstEntry base noQuantum input count)
    (.inr ⟨firstBatch_restartCleanup base noQuantum input⟩)

/-- Zero trials allocate the actual empty result; positive trials include the actual selector. -/
def plan (model : GoodKeyModel N) : (totalRounds : Nat) →
    CyclePlan RuntimeRound.model base (NativeFiniteRetry.context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => .classical (NativeFiniteRetry.fixedRoundProblem base noQuantum model 0)
  | count + 1 => .seq (chainPlan base noQuantum model.input count)
      (.classical (Selection.problem (NativeRetryChain.resultRefs base noQuantum N count)))

/-- Complete finite factoring with independently fixed complete-batch restart points.

**Input.** Every normalized caller/reference input of the original good-key contract.
**Output.** The original optional declared factor and full joint-state requirement.
**Resource budget.** The unchanged whole-run finite-count formulas; complete-cycle budgets
are the independent first/reused sixteen-round batch and recovery depth formulas.
**Success.** The original finite-count bound, including its genuine zero-trial branch.
**Source.** [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:329-355].
-/
def problem (model : GoodKeyModel N) (totalRounds : Nat) :
    CycleProblem RuntimeRound.model base (NativeFiniteRetry.context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  outcome := NativeFiniteRetry.fixedRoundProblem base noQuantum model totalRounds
  plan := plan base noQuantum model totalRounds

theorem emptyClassical : Circuit.IsClassical (NativeRetryEmpty.code base N) := by
  intro path event present
  rw [NativeRetryEmpty.code_eventTrace] at present
  exact False.elim (List.not_mem_nil present)

/-- The same existing finite execution implements each requested count and real classical tail. -/
def schedule (model : GoodKeyModel N) : (totalRounds : Nat) →
    Circuit.CycleSchedule (plan base noQuantum model totalRounds)
      (NativeFiniteRetry.algorithm base noQuantum model.input totalRounds).run.code
  | 0 => .classical _
      { output := (NativeFiniteRetry.algorithm base noQuantum model.input 0).run.output
        certified := NativeFiniteRetry.algorithm_solves_fixedRound base noQuantum model 0 }
      (emptyClassical base)
  | count + 1 => .seq _ _ (chainSchedule base noQuantum model.input count)
      (Selection.schedule (NativeRetryChain.resultRefs base noQuantum N count))
      (fun _ _ _ => ⟨True.intro, True.intro⟩)
      (.inl (Selection.onlyClassical
        (NativeRetryChain.resultRefs base noQuantum N count)))

/-- Full original correctness and actual entry-compatible cycle execution
for every natural count. -/
def certificate (model : GoodKeyModel N) (totalRounds : Nat) :
    Algorithm.CycleSolves (NativeFiniteRetry.algorithm base noQuantum model.input totalRounds)
      (problem base noQuantum model totalRounds) where
  correctness := NativeFiniteRetry.algorithm_solves_fixedRound base noQuantum model totalRounds
  schedule := schedule base noQuantum model totalRounds
  entry := by
    intro Reference input _admitted
    cases totalRounds <;> exact ⟨True.intro, True.intro⟩

/-- Independent maximum complete-batch allowance for every positive retry count. -/
def batchDepthBound (N : Nat) : Nat :=
  max (NativeBatchRecovery.depthBound N) (NativeBatchReuseRecovery.depthBound N)

/-- Zero trials have no quantum cycle; the positive allowance is independent of batch count. -/
def maximumCycleDepthBound (N : Nat) : Nat → Nat
  | 0 => 0
  | _ + 1 => batchDepthBound N

private theorem suffixMaximum_le (input : Input N) (count : Nat) :
    ∀ (start : RuntimeCtx .quantum)
      (wires : start.quantumWires =
        (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
      (cells : Fin (measurementBits N) → CWriteRef start (.finite 2))
      (distinct : Function.Injective (fun index => (cells index).key))
      (noBorrowed : start.borrowedQuantumWires = [])
      (path : (NativeRetryChain.suffixCode input start wires cells count).Path),
      (suffixSchedule input start wires cells distinct noBorrowed count).maximumCycleDepth
        (fun _ => 1) path ≤ NativeBatchReuseRecovery.depthBound N := by
  induction count with
  | zero =>
      intro start wires cells distinct noBorrowed path
      exact Nat.zero_le _
  | succ count induction =>
      intro start wires cells distinct noBorrowed path
      change max ((NativeBatchReuseRecovery.code start wires cells input).depth
        (fun _ => 1) path.1)
        ((suffixSchedule input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => NativeRetryChain.reuseWrite N (cells index))
          (liftedDistinct start cells distinct)
          (nextNoBorrowed input start wires cells noBorrowed) count).maximumCycleDepth
              (fun _ => 1) path.2) ≤ _
      exact max_le (NativeBatchReuseRecovery.code_depth_le start wires cells input path.1)
        (induction _ _ _ _ _ path.2)

/-- The actual all-input batch chain has a count-independent maximum cycle allowance. -/
theorem chainMaximum_le (input : Input N) (count : Nat)
    (path : (NativeRetryChain.code base noQuantum input count).Path) :
    (chainSchedule base noQuantum input count).maximumCycleDepth (fun _ => 1) path ≤
      batchDepthBound N := by
  change max ((NativeBatchRecovery.code base noQuantum input).depth (fun _ => 1) path.1)
    ((suffixSchedule input (NativeBatchRecovery.context base noQuantum N)
      (NativeRetryChain.firstWires base noQuantum N)
      (NativeRetryChain.firstCells base noQuantum N)
      (NativeRetryChain.cells_distinct base noQuantum N 0)
      (NativeBatchRecovery.context_noBorrowedQuantum base noQuantum N) count).maximumCycleDepth
        (fun _ => 1) path.2) ≤ batchDepthBound N
  exact max_le_max (NativeBatchRecovery.code_depth_le base noQuantum input path.1)
    (suffixMaximum_le input count _ _ _ _ _ path.2)

/-- Every actual path respects the independent uniform maximum complete-batch bound. -/
theorem maximumCycleDepth_le (model : GoodKeyModel N) (totalRounds : Nat)
    (path : (NativeFiniteRetry.algorithm base noQuantum model.input totalRounds).run.code.Path) :
    (certificate base noQuantum model totalRounds).maximumCycleDepth (fun _ => 1) path ≤
      maximumCycleDepthBound N totalRounds := by
  cases totalRounds with
  | zero => exact le_refl 0
  | succ count =>
      change max ((chainSchedule base noQuantum model.input count).maximumCycleDepth
        (fun _ => 1) path.1) 0 ≤ batchDepthBound N
      rw [max_zero]
      exact chainMaximum_le base noQuantum model.input count path.1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.Finite
