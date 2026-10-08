/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Readout distribution across an actual cycle boundary

The successor input forgets path histories while retaining the live store and
persistent service. A read of the live store therefore has the same probability
law immediately before and after this history projection.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Forgetting actual path histories at `nextInput` preserves every readout
distribution of the surviving store, with the service state still correlated. -/
theorem nextInput_readoutDistribution {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post)
    {Reference : Register}
    (original : OracleInput model.classicalOracles pre Reference)
    {Outcome : Type} (read : Store post → Outcome) :
    (((code.nextInput original).state.toPMF
      (code.nextInput original).normalized).map
        (fun entry => read entry.1)) =
      (((code.execute Reference
        (original.state.mapClassical
          (fun entry => (entry.1, (entry.2, ()))))).toPMF
            ((code.execute_mass Reference
              (original.state.mapClassical
                (fun entry => (entry.1, (entry.2, ()))))).trans
              (original.state.mapClassical_normalized original.normalized
                (fun entry => (entry.1, (entry.2, ())))))).map
        (fun record => read record.1)) := by
  let entered := original.state.mapClassical
    (fun entry => (entry.1, (entry.2, ())))
  let final := code.execute Reference entered
  have enteredNormalized : entered.IsNormalized :=
    original.state.mapClassical_normalized original.normalized
      (fun entry => (entry.1, (entry.2, ())))
  have finalNormalized : final.IsNormalized :=
    (code.execute_mass Reference entered).trans enteredNormalized
  have mapped := congrArg
    (fun distribution : PMF (Store post × model.classicalOracles.HiddenState) =>
      distribution.map (fun entry => read entry.1))
    (ExecutionState.toPMF_mapClassical final finalNormalized
      (fun record => (record.1, record.2.1)))
  simpa only [nextInput, PMF.map_comp, Function.comp_def] using mapped

/-- A positive-mass local successor record contributes to the distribution
of every read of its surviving store, even with an external reference. -/
theorem nextInput_local_readout_support {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post)
    {Reference : Register}
    (original : OracleInput model.classicalOracles pre Reference)
    {Outcome : Type} (read : Store post → Outcome)
    (record : Store post × model.classicalOracles.HiddenState)
    (positive : 0 < ((code.nextInput original).localState.block record).mass) :
    read record.1 ∈
      ((((code.nextInput original).state.toPMF
        (code.nextInput original).normalized).map
          (fun entry => read entry.1)).support) := by
  have jointPositive :
      0 < ((code.nextInput original).state.block record).mass := by
    simpa only [OracleInput.oracleInput_localState_block,
      DensityOperator.marginalLeft_mass]
      using positive
  have supported : record ∈
      ((code.nextInput original).state.toPMF
        (code.nextInput original).normalized).support :=
    (ExecutionState.mem_support_toPMF_iff _ _ record).2 jointPositive
  rw [PMF.mem_support_map_iff]
  exact ⟨record, supported, rfl⟩

/-- A positive local block after history grouping has a positive block in the
actual preceding execution, with the same live store and service state. -/
theorem nextInput_local_supported_execution {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post)
    {Reference : Register}
    (original : OracleInput model.classicalOracles pre Reference)
    (record : Store post × model.classicalOracles.HiddenState)
    (positive : 0 < ((code.nextInput original).localState.block record).mass) :
    ∃ result : Store post ×
        (model.classicalOracles.HiddenState × (Unit × code.Path)),
      result.1 = record.1 ∧ result.2.1 = record.2 ∧
      0 < ((code.execute Reference
        (original.state.mapClassical
          (fun entry => (entry.1, (entry.2, ()))))).block result).mass := by
  have jointPositive :
      0 < ((code.nextInput original).state.block record).mass := by
    simpa only [OracleInput.oracleInput_localState_block,
      DensityOperator.marginalLeft_mass] using positive
  obtain ⟨result, same, resultPositive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff
      (code.execute Reference (original.state.mapClassical
        (fun entry => (entry.1, (entry.2, ())))))
      (fun result => (result.1, result.2.1)) record).mp
      (show 0 < (((code.execute Reference (original.state.mapClassical
        (fun entry => (entry.1, (entry.2, ()))))).mapClassical
          (fun result => (result.1, result.2.1))).block record).mass from
        jointPositive)
  exact ⟨result, congrArg Prod.fst same,
    congrArg (fun value => value.2) same, resultPositive⟩

end

end QuantumAlg.Circuit
