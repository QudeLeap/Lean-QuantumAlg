/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Packing
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Schedule
import all QuantumAlg.Core.Execution.CycleSchedule.Bounds

/-!
# The exact completed finite tail and its sole classical result pack

Every requested quantum round has the complete independent protocol and its
genuine restart/admission certificate. The actual final pack has a certain
independent classical encoding contract. It remains paid in whole execution
events and chronological depth while introducing no additional quantum cycle.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite

open Execution

noncomputable section

/-- The caller prescribes complete rounds followed by the single complete classical encoding. -/
def completionPlan (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (original : NativeFactorScan.Cells ctx N) (count : Nat)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CyclePlan (executionModel (Probability.Input.ofSemiprimeModel model)) ctx
      (context ctx N count) (.option (.unsignedWord (modulusBits N))) :=
  .seq (roundPlan ctx model original count duration unitQueries)
    (.classical (packProblem ctx N (Probability.Input.ofSemiprimeModel model) count original))

/-- Actual zero-bank and sound-latch inputs admit any prescribed finite completion plan. -/
theorem completionPlan_admits_of_domain (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (original : NativeFactorScan.Cells ctx N) (count : Nat)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    {Reference : Register}
    (entered : OracleInput
      (executionModel (Probability.Input.ofSemiprimeModel model)).classicalOracles ctx Reference)
    (admitted : Round.inputDomain ctx model original entered.localState) :
    (completionPlan ctx model original count duration unitQueries).Admits entered := by
  cases count with
  | zero => exact ⟨True.intro, True.intro⟩
  | succ count => exact ⟨True.intro, admitted⟩

/-- The same actual finite circuit carries every complete round and the sole actual pack. -/
def completionSchedule (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated original result)
    (noBorrowedQuantum : ctx.borrowedQuantumWires = []) (count : Nat)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CycleSchedule (completionPlan ctx model original count duration unitQueries)
      (code ctx N (Probability.Input.ofSemiprimeModel model) sameWires count original result) :=
  .seq _ _ (roundSchedule ctx model sameWires original result separated noBorrowedQuantum
    count duration unitQueries)
    (packSchedule ctx N (Probability.Input.ofSemiprimeModel model) count original result)
    (by intro _ _ _; exact ⟨True.intro, True.intro⟩)
    (Or.inl (pack_onlyClassical ctx N (Probability.Input.ofSemiprimeModel model)
      count original result))

/-- Complete quantum cycle depth bounds the same real tail without dropping paid terminal work. -/
theorem completion_maximumCycleDepth_le (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated original result)
    (noBorrowedQuantum : ctx.borrowedQuantumWires = []) (count : Nat)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (code ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires count original result).Path) :
    (completionSchedule ctx model sameWires original result separated noBorrowedQuantum
      count duration unitQueries).maximumCycleDepth duration path ≤
        ResourcePool.weightedCount duration
          (completionEnvelope (Probability.Input.ofSemiprimeModel model)) := by
  change max (_ : Nat) 0 ≤ _
  rw [max_eq_left (Nat.zero_le _)]
  exact shorDeclared_finite_maximumCycleDepth_le ctx model sameWires original result
    separated noBorrowedQuantum count duration unitQueries path.1

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite
