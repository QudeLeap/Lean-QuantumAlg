/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Reference
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Reference
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# The actual next recovery has the original factor kernel jointly with earlier observations

The full source reference law determines which complete classical records
can have positive mass. This internally supplies the parameter relation used
by the actual deterministic recovery. Zero-mass records carry zero quantum
operators, so substituting the canonical factor preserves both arbitrary
reference coordinates and every protected earlier structural observation.
The resulting kernel is the original sampled batch output PMF, with only its
existing typed optional-factor encoding applied.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] NativeBatchReuse.context NativeBatchReuse.code body tail step
  RuntimeResults.liftInput RuntimeResults.input

private theorem read_mem_support_of_reference
    {C D Outcome : Type} [Fintype C] [Fintype D] [Finite Outcome]
    {R S Reference : Register}
    (initial : ExecutionState C (R.prod Reference))
    (final : ExecutionState D (S.prod Reference)) (read : D → Outcome)
    (distribution : PMF Outcome)
    (observed : ∀ value (leftRef rightRef : Reference.Index),
      ExecutionState.referenceFiberSum final
          (fun entry _ => if read entry = value then 1 else 0) leftRef rightRef =
        ExecutionState.referenceFiberSum initial
          (fun _ _ => ((distribution value).toReal : ℂ)) leftRef rightRef)
    (entry : D) (positive : 0 < (final.block entry).mass) :
    read entry ∈ distribution.support := by
  let : Fintype Outcome := Fintype.ofFinite Outcome
  by_contra absent
  have zero : distribution (read entry) = 0 := by
    simpa only [PMF.mem_support_iff, not_not] using absent
  have blockLe : (final.block entry).mass ≤
      ((final.mapClassical read).block (read entry)).mass := by
    rw [ExecutionState.mapClassical_block_mass]
    have nonnegative : ∀ other ∈ (Finset.univ : Finset D),
        0 ≤ if read other = read entry then (final.block other).mass else 0 := by
      intro other _
      split
      · exact (final.block other).mass_nonneg
      · exact le_rfl
    simpa only [if_true] using Finset.single_le_sum nonnegative (Finset.mem_univ entry)
  have positiveRead := lt_of_lt_of_le positive blockLe
  have massEquation := ExecutionState.mapClassical_block_mass_referenceFiberSum
    final read (read entry)
  have diagonal := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun reference _ => observed (read entry) reference reference)
  have summed := diagonal.trans
    (ExecutionState.referenceFiberSum_sum_constant initial
      ((distribution (read entry)).toReal : ℂ))
  have zeroMass : ((final.mapClassical read).block (read entry)).mass = 0 := by
    simpa only [zero, ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul, Complex.zero_re]
      using massEquation.trans (congrArg Complex.re summed)
  exact (ne_of_gt positiveRead) zeroMass

private theorem reference_eq_on_support
    {C : Type} [Fintype C] {R Reference : Register}
    (state : ExecutionState C (R.prod Reference)) (first second : C → R.Index → ℂ)
    (agree : ∀ entry, 0 < (state.block entry).mass → ∀ basis,
      first entry basis = second entry basis) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state first leftRef rightRef =
      ExecutionState.referenceFiberSum state second leftRef rightRef := by
  unfold ExecutionState.referenceFiberSum
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro entry _
  by_cases positive : 0 < (state.block entry).mass
  · rw [agree entry positive basis]
  · have zeroMass := le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
    rw [state.block_eq_zero_of_mass_eq_zero entry zeroMass, DensityOperator.zero_matrix]
    simp only [Matrix.zero_apply, mul_zero]

variable (base : RuntimeCtx .quantum) {N : Nat}
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

private theorem source_output_mem_support (input : Input N)
    {previousShape : CShape} (previous : CInputRef base previousShape)
    (distinct : Function.Injective (fun index => (originalCells index).key))
    (separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (seeded : RuntimeRound.HasSeedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N state)
    (entry : Store (NativeBatchReuse.context base N) ×
      (History × (NativeBatchReuse.code base N sameWires originalCells).Path))
    (positive : 0 < (((NativeBatchReuse.code base N sameWires originalCells).execute
      Reference state).block entry).mass) :
    (NativeBatchReuse.run base N sameWires originalCells).output.eval entry.1 ∈
      (NativeBatch.sourceDistribution input).support := by
  apply read_mem_support_of_reference state
    ((NativeBatchReuse.code base N sameWires originalCells).execute Reference state)
    (fun record => (NativeBatchReuse.run base N sameWires originalCells).output.eval record.1)
    (NativeBatch.sourceDistribution input) ?_ entry positive
  intro selected leftRef rightRef
  have observed := NativeBatchReuse.nativeBatchReuse_output_weighted_reference
    base N sameWires originalCells input previous distinct separate state seeded
    (fun _ output => if output = selected then 1 else 0) leftRef rightRef
  refine observed.trans ?_
  exact congrArg
    (fun coefficient : ℂ => ExecutionState.referenceFiberSum state
      (fun _ _ => coefficient) leftRef rightRef)
    (PMF.sum_toReal_indicator (NativeBatch.sourceDistribution input) selected)

/-- The actual next factor has the original kernel jointly with a protected earlier operand. -/
theorem nativeBatchReuseRecovery_output_weighted_reference (input : Input N)
    {previousShape : CShape} (previous : CInputRef base previousShape)
    (distinct : Function.Injective (fun index => (originalCells index).key))
    (separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (seeded : RuntimeRound.HasSeedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N state)
    (weight : previousShape.Value → (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((code base sameWires originalCells input).execute Reference state)
        (fun entry _ => weight (entry.1.read (callerInput base N previous))
          ((run base sameWires originalCells input).output.eval entry.1)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            factor).toReal : ℂ) * weight (entry.1.read previous) factor) leftRef rightRef := by
  let sourceState := (NativeBatchReuse.code base N sameWires originalCells).execute Reference state
  have tailLaw := tail_weighted_reference base input
    (NativeBatchReuse.callerInput base N previous) sourceState weight leftRef rightRef
  have recovered := reference_eq_on_support sourceState
    (fun entry _ => weight (entry.1.read (NativeBatchReuse.callerInput base N previous))
      ((step base input entry.1).1.read (.storage (resultRef base N).toCStorageRef)))
    (fun entry _ => weight (entry.1.read (NativeBatchReuse.callerInput base N previous))
      (NativeBatchRecovery.packedValue
        ((NativeBatchReuse.run base N sameWires originalCells).output.eval entry.1)))
    (fun entry positive _ => congrArg
      (weight (entry.1.read (NativeBatchReuse.callerInput base N previous)))
      (output_on_source_support base sameWires originalCells input entry.1
        (source_output_mem_support base sameWires originalCells input previous distinct
          separate state seeded entry positive))) leftRef rightRef
  have sourceLaw := NativeBatchReuse.nativeBatchReuse_output_weighted_reference
    base N sameWires originalCells input previous distinct separate state seeded
    (fun old output => weight old (NativeBatchRecovery.packedValue output)) leftRef rightRef
  have kernel (store : Store base) :
      (∑ output : (NativeBatch.resultShape N).Value,
        ((NativeBatch.sourceDistribution input output).toReal : ℂ) *
          weight (store.read previous) (NativeBatchRecovery.packedValue output)) =
      ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          factor).toReal : ℂ) * weight (store.read previous) factor := by
    have mapped := (PMF.sum_map_toReal_mul (NativeBatch.sourceDistribution input)
      NativeBatchRecovery.packedValue (weight (store.read previous))).symm
    rw [NativeBatchRecovery.sourceDistribution_map_packedValue input] at mapped
    exact mapped
  have mappedLaw := congrArg
    (fun observe : Store base → ℂ => ExecutionState.referenceFiberSum state
      (fun entry _ => observe entry.1) leftRef rightRef) (funext kernel)
  exact (Circuit.referenceFiberSum_execute_seq
    (NativeBatchReuse.code base N sameWires originalCells) (tail base input) state
    (fun store => weight (store.read (callerInput base N previous))
      (store.read (.storage (resultRef base N).toCStorageRef))) leftRef rightRef).trans
    (tailLaw.trans (recovered.trans (sourceLaw.trans mappedLaw)))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery
