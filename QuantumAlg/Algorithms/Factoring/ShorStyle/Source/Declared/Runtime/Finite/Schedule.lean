/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Cleanup
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Geometry
import all QuantumAlg.Core.Execution.CycleSchedule.Identity

/-!
# Exact finite schedule of independently complete declared Shor rounds

The caller requests exactly this many complete sampling/recovery/feedback/reset
computations. Each actual predecessor admits its genuine successor, with
earlier retained cells and the same physical bank preserved. Maximum cycle
depth bounds one complete round; total resources and chronological depth
remain obligations of the whole finite execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite

open Execution

noncomputable section

/-- The independent plan prescribes complete rounds and the actual terminal identity section. -/
def roundPlan (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (cells : NativeFactorScan.Cells ctx N) : (count : Nat) →
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat) →
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) →
    CyclePlan (executionModel (Probability.Input.ofSemiprimeModel model)) ctx
      (context ctx N count) .unit
  | 0, duration, unitQueries => .classical
      (Circuit.identityProblem (model := executionModel (Probability.Input.ofSemiprimeModel model))
        (shape := .unit) ctx duration (fun coordinate => nomatch coordinate) unitQueries)
  | count + 1, duration, unitQueries =>
      .seq (.cycle (Round.problem ctx model cells duration unitQueries))
        (roundPlan (Iteration.context ctx N) model (Completion.cells ctx N cells)
          count duration unitQueries)

/-- The same actual finite body carries its complete protocols, restart and entry certificates. -/
def roundSchedule (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    (noBorrowedQuantum : ctx.borrowedQuantumWires = []) : (count : Nat) →
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat) →
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) →
    Circuit.CycleSchedule (roundPlan ctx model cells count duration unitQueries)
      (body ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells result count)
  | 0, duration, unitQueries =>
      Circuit.identitySchedule (model := executionModel (Probability.Input.ofSemiprimeModel model))
        ctx OutputRead.unit duration (fun coordinate => nomatch coordinate) unitQueries
  | count + 1, duration, unitQueries =>
      .seq (Completion.code ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells result)
        (body (Iteration.context ctx N) N (Probability.Input.ofSemiprimeModel model)
          ((Iteration.quantumWires ctx N).trans sameWires) (Completion.cells ctx N cells)
          (Completion.liftWrite ctx N result) count)
        (.complete _ (Round.completeCycle ctx model sameWires cells result separated
          noBorrowedQuantum duration unitQueries))
        (roundSchedule (Iteration.context ctx N) model
          ((Iteration.quantumWires ctx N).trans sameWires) (Completion.cells ctx N cells)
          (Completion.liftWrite ctx N result) (Completion.separated ctx N cells result separated)
          ((Completion.code ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells
            result).borrowedQuantumWires_preserved.trans noBorrowedQuantum)
          count duration unitQueries)
        (by
          intro Reference original admitted
          cases count with
          | zero => exact ⟨True.intro, True.intro⟩
          | succ count => exact ⟨True.intro,
              Round.nextInput_admitted ctx model sameWires cells result separated
                original admitted.2⟩)
        (Or.inr ⟨Round.restartCleanup ctx N (Probability.Input.ofSemiprimeModel model)
          sameWires cells result noBorrowedQuantum⟩)

/-- Every complete cycle of the actual symbolic finite body obeys one full round allowance. -/
theorem shorDeclared_finite_maximumCycleDepth_le (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    (noBorrowedQuantum : ctx.borrowedQuantumWires = []) (count : Nat)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (body ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result count).Path) :
    (roundSchedule ctx model sameWires cells result separated noBorrowedQuantum
      count duration unitQueries).maximumCycleDepth duration path ≤
        ResourcePool.weightedCount duration
          (completionEnvelope (Probability.Input.ofSemiprimeModel model)) := by
  induction count generalizing ctx with
  | zero => exact Nat.zero_le _
  | succ count induction =>
      change max ((Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
        sameWires cells result).depth duration path.1)
        ((roundSchedule (Iteration.context ctx N) model
          ((Iteration.quantumWires ctx N).trans sameWires) (Completion.cells ctx N cells)
          (Completion.liftWrite ctx N result) (Completion.separated ctx N cells result separated)
          ((Completion.code ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells
            result).borrowedQuantumWires_preserved.trans noBorrowedQuantum)
          count duration unitQueries).maximumCycleDepth duration path.2) ≤ _
      exact max_le
        (Circuit.depth_le_weightedCount_of_pool_le
          (Completion.code ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells result)
          duration (completionEnvelope (Probability.Input.ofSemiprimeModel model)) path.1
          (Completion.code_pool_le ctx N (Probability.Input.ofSemiprimeModel model)
            sameWires cells result path.1))
        (induction (Iteration.context ctx N) ((Iteration.quantumWires ctx N).trans sameWires)
          (Completion.cells ctx N cells) (Completion.liftWrite ctx N result)
          (Completion.separated ctx N cells result separated)
          ((Completion.code ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells
            result).borrowedQuantumWires_preserved.trans noBorrowedQuantum) path.2)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite
