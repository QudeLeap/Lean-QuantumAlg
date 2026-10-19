/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Result
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.Borrowed

/-!
# The actual sole terminal factor encoding has a complete classical contract

The real existing option destination receives the incoming success latch
exactly once. The independent encoding contract has certain output, the
complete borrowed restoration and the same paid native instruction. Every
live caller, source result and owned physical bank remains in both space
ledgers. This terminal work introduces no quantum computation or restart.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (ctx : RuntimeCtx .quantum) (N : Nat) (count : Nat)
  (original : NativeFactorScan.Cells ctx N)
  (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))

/-- Exact encoding of the actual incoming success bit and selected word.

**Input.** Any actual final live store, persistent service state and reference.
**Output.** The incoming success latch encoded in the existing optional result
cell; every original live entry and borrowed observation is retained.
**Resource budget.** One width-indexed native option pack, unchanged complete
resident and auxiliary contexts, and unit dependency depth one.
**Success.** The independently specified incoming latch encoding is returned
with probability one, including an absent latch.
**Source.** The closed `CShape.packOption` semantics and original actual
finite computation's terminal encoding instruction.
-/
def packProblem : Problem (executionModel N) (context ctx N count) (context ctx N count)
    (.option (.unsignedWord (modulusBits N))) where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ before output => output = NativeFactorScan.latchValue
    (cells ctx N count original) before
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => []
  resources :=
    { events := ResourcePool.singleton (.classicalOperation
        (BitWord.selectedCoordinate (execution := executionModel N)
          (.nominalEncoding (.packOption (modulusBits N)))))
      resident := (context ctx N count).residentSpace
      auxiliary := (context ctx N count).auxiliarySpace }
  quantumTimeLimit := 1

/-- Observe the actual sole terminal destination while retaining its complete live manifest. -/
def packAlgorithm : Algorithm (executionModel N) (context ctx N count) (context ctx N count)
    (.option (.unsignedWord (modulusBits N))) where
  run :=
    { code := pack ctx N count original result
      output := Output.all _ (.read (.storage (liftWrite ctx N count result).toCStorageRef)) }

private def packRecord (entry : Store (context ctx N count) × (executionModel N).HiddenState) :
    (packAlgorithm ctx N count original result).run.Record :=
  let actual := BitWord.instructionStep (execution := executionModel N)
    (NativeFactorScan.packOp (cells ctx N count original) (liftWrite ctx N count result)) entry.1
  (actual.1, (entry.2, (entry.1, actual.2)))

variable {environment : (executionModel N).Environment}

private lemma pack_execute {Reference : Register}
    (state : ExecutionState (Store (context ctx N count) × (executionModel N).HiddenState)
      ((context ctx N count).register.prod Reference)) :
    (packAlgorithm ctx N count original result).run.execute environment Reference state =
      state.mapClassical (packRecord ctx N count original result) := by
  unfold AlgorithmRun.execute
  change (BitWord.instruction (execution := executionModel N)
    (NativeFactorScan.packOp (cells ctx N count original)
      (liftWrite ctx N count result))).execute environment Reference
        (state.mapClassical (fun value => (value.1, (value.2, value.1)))) = _
  rw [BitWord.bitWord_instruction_execute]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma pack_relational {Reference : Register}
    (entered : OracleInput (executionModel N).classicalOracles
      (context ctx N count) Reference) :
    (packAlgorithm ctx N count original result).relationalDistribution environment entered =
      (entered.state.toPMF entered.normalized).map (fun entry =>
        (entry.1, NativeFactorScan.latchValue (cells ctx N count original) entry.1)) := by
  have mapped : (packAlgorithm ctx N count original result).run.executionDistribution environment
      entered = (entered.state.toPMF entered.normalized).map
        (packRecord ctx N count original result) := by
    apply PMF.ext
    intro record
    change ENNReal.ofReal
      (((packAlgorithm ctx N count original result).run.execute environment Reference
        entered.state).block record).mass = _
    rw [pack_execute]
    exact congrArg (fun distribution :
      PMF (packAlgorithm ctx N count original result).run.Record => distribution record)
      (ExecutionState.toPMF_mapClassical entered.state entered.normalized
        (packRecord ctx N count original result))
  change ((packAlgorithm ctx N count original result).run.executionDistribution environment
      entered).map _ = _
  rw [mapped, PMF.map_comp]
  apply congrArg ((entered.state.toPMF entered.normalized).map)
  funext entry
  exact congrArg (Prod.mk entry.1) (NativeFactorScan.pack_result
    (cells ctx N count original) (liftWrite ctx N count result) entry.1)

/-- The original paid pack satisfies all seven independent classical protocol obligations. -/
lemma pack_solves : (packAlgorithm ctx N count original result).Solves
    (packProblem ctx N count original) := by
  constructor
  · intro environment _witness Reference entered _valid _admitted
    rw [pack_relational, PMF.toOuterMeasure_map_apply]
    apply le_of_eq
    symm
    exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (fun _ _ => rfl)
  · intro _environment _witness _Reference _entered _valid _admitted _requirement present
    exact False.elim (List.not_mem_nil present)
  · intro environment _witness Reference entered _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := executionModel N)
        (NativeFactorScan.packOp (cells ctx N count original) (liftWrite ctx N count result)))
      state
  · intro _environment _witness _Reference _entered _valid _admitted path _supported
    exact le_rfl
  · intro _environment _witness _Reference _entered _valid _admitted path _supported
    exact (Circuit.peakResidentSpace_classical (model := executionModel N)
      (BitWord.selectedApplication (execution := executionModel N)
        (NativeFactorScan.packOp (cells ctx N count original) (liftWrite ctx N count result)))
      path).le
  · intro _environment _witness _Reference _entered _valid _admitted path _supported
    exact (Circuit.peakAuxiliarySpace_classical (model := executionModel N)
      (BitWord.selectedApplication (execution := executionModel N)
        (NativeFactorScan.packOp (cells ctx N count original) (liftWrite ctx N count result)))
      path).le
  · intro _environment _witness _Reference _entered _valid _admitted path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact le_rfl

/-- The actual sole pack emits only its genuine classical encoding event. -/
lemma pack_onlyClassical : Circuit.IsClassical (pack ctx N count original result) := by
  intro path event present
  have same := List.mem_singleton.mp present
  exact Or.inl ⟨_, same⟩

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite
