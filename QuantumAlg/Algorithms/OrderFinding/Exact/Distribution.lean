/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Mathematics
import all QuantumAlg.Algorithms.OrderFinding.Exact.Context
import all QuantumAlg.Algorithms.OrderFinding.Exact.Execution
import all QuantumAlg.Algorithms.OrderFinding.Exact.DecodeLaws
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Distribution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Execution
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution

/-!
# Exact order-finding probabilities after actual stored-bit decoding

The complete decoder's proved store and path map the actual sampling records.
Its result is the unsigned encoding of those same packed bits. Projecting the
result therefore transports the original Born distribution and exact-grid
support without supplying an independent probabilistic model to execution.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- The mathematical encoding implemented by the real stored-bit decoder. -/
def decodedValue {t : Nat} : CShape.Value (.bits t) → CShape.Value (.unsignedWord t)
  | .bits bits => OrderFinding.encodedOutcome bits

/-- The actual decoder's result agrees with the encoded value of its actual source read. -/
theorem decodedStep_output (t n : Nat) (store : Store (Sampling.post t n)) :
    (decodedStep t n store).1.read (resultRef t n) =
      decodedValue (store.read (packedInput t n)) := by
  cases measured : store.read (packedInput t n) with
  | bits value => exact decodedStep_output_of_bits t n store value measured

/-- Append only the real decoder's store update and interpreter path to a sampling record. -/
def decodedRecord {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (record : (Sampling.run A).Record) : (run A).Record :=
  ((decodedStep t n record.1).1,
    (record.2.1, (record.2.2, (decodedStep t n record.1).2)))

/-- The complete execution maps the very same sampling blocks, preserving all correlations. -/
theorem execute_eq_map {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (Reference : Register)
    (state : ExecutionState (Store Sampling.pre)
      (Register.prod Sampling.pre.register Reference)) :
    (run A).execute Reference state =
      ((Sampling.run A).execute Reference state).mapClassical (decodedRecord A) := by
  change (Circuit.seq (Sampling.code A) (decoderCode t n)).execute Reference
      (state.mapClassical (fun store => (store, store))) =
    ((Sampling.code A).execute Reference
      (state.mapClassical (fun store => (store, store)))).mapClassical (decodedRecord A)
  rw [Circuit.execute_seq, decoderCode_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Read the exact run's complete Output after the actual decoder record transformation. -/
theorem decodedRecord_result {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (record : (Sampling.run A).Record) :
    (run A).result (decodedRecord A record) =
      decodedValue ((Sampling.run A).result record) :=
  decodedStep_output t n record.1

/-- The complete execution distribution is the same sampling distribution with real decoding. -/
theorem executionDistribution_eq_map {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} (input : Execution.Input Sampling.pre Reference) :
    (run A).executionDistribution input =
      ((Sampling.run A).executionDistribution input).map (decodedRecord A) := by
  apply PMF.ext
  intro record
  change ENNReal.ofReal ((((run A).execute Reference input.state).block record).mass) = _
  rw [execute_eq_map]
  exact congrArg (fun distribution : PMF (run A).Record => distribution record)
    (ExecutionState.toPMF_mapClassical ((Sampling.run A).execute Reference input.state)
      ((Sampling.run A).execute_normalized input) (decodedRecord A))

/-- The returned unsigned word is the deterministic decoding of the same actual stored sample. -/
theorem outputDistribution_eq_decode {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} (input : Execution.Input Sampling.pre Reference) :
    (run A).outputDistribution input =
      ((Sampling.run A).outputDistribution input).map decodedValue := by
  change ((run A).executionDistribution input).map (run A).result =
    (((Sampling.run A).executionDistribution input).map (Sampling.run A).result).map decodedValue
  rw [executionDistribution_eq_map, PMF.map_comp, PMF.map_comp]
  congr 1
  funext record
  exact decodedRecord_result A record

/-- The complete native run has the original encoded Born distribution at every width. -/
theorem outputDistribution_eq {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} (input : Execution.Input Sampling.pre Reference) :
    (run A).outputDistribution input =
      ((measurement t n).outcomePMF (BornBridge.evolvedState A)).map
        OrderFinding.encodedOutcome := by
  rw [outputDistribution_eq_decode, Sampling.outputDistribution_eq, PMF.map_comp]
  rfl

/-- Every admissible dyadic instance produces an exact-grid word with probability one. -/
theorem successProbability_eq_one {N x t n r : Nat} (A : ModExpOracleAccess N x t n)
    (hinput : OrderFinding.Input N x r) (dyadic : r ∣ 2 ^ t)
    {Reference : Register} (input : Execution.Input Sampling.pre Reference) :
    ((run A).outputDistribution input).toOuterMeasure
      {output | OrderFinding.SuccessfulOutcome r output} = 1 := by
  rw [outputDistribution_eq, PMF.toOuterMeasure_map_apply]
  have grid : OrderFinding.encodedOutcome ⁻¹'
      {output | OrderFinding.SuccessfulOutcome r output} =
        {outcome | OrderFinding.ExactOutcome r t outcome} := by
    ext outcome
    exact OrderFinding.successful_encodedOutcome_iff outcome
  rw [grid]
  exact BornBridge.exactMeasurementModel hinput A dyadic

end

end QuantumAlg.OrderFinding.Exact
