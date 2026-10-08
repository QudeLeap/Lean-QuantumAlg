/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Setup.Probability
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# Probability distribution of the actual declared EH sixteen-slot output

The public result PMF traces the same complete execution and reference state
as the physical setup and sixteen-slot joint law. The conditional source
weight is converted to the selected short-DLP mathematical law only here.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] context setup firstBatch code

private theorem vector_indicator (length width : Nat)
    (values : Fin length → (CShape.bits width).Value)
    (outcomes : Fin length → Fin width → Bool) :
    (if CShape.Value.fixedVector values =
      CShape.Value.fixedVector (fun index => CShape.Value.bits (outcomes index))
      then (1 : ℂ) else 0) =
    ∏ index : Fin length,
      if values index = CShape.Value.bits (outcomes index) then 1 else 0 := by
  by_cases allEqual : ∀ index, values index = CShape.Value.bits (outcomes index)
  · have equal := congrArg CShape.Value.fixedVector (funext allEqual)
    simp only [equal, if_true, allEqual, Finset.prod_const_one]
  · obtain ⟨index, different⟩ := not_forall.mp allEqual
    have differentVector : CShape.Value.fixedVector values ≠
        CShape.Value.fixedVector (fun index => CShape.Value.bits (outcomes index)) :=
      fun equal => different (congrFun (CShape.Value.fixedVector.inj equal) index)
    rw [if_neg differentVector]
    exact (Finset.prod_eq_zero (Finset.mem_univ index) (if_neg different)).symm

private theorem source_probability_cast (N : Nat) (input : Input N)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool) :
    (∑ value : Fin (2 ^ residueSamplingBits N),
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
        (∏ index : Fin 16,
          Declared.sourceWeight N input (parameterValue input value) (outcomes index))) =
      ((∑ value : Fin (2 ^ residueSamplingBits N),
        ((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ *
          ∏ index : Fin 16,
            (selectedOutcomePMF (parameterValue input value)
              (outcomes index)).toReal : ℝ) : ℂ) := by
  simp only [Declared.sourceWeight_eq_selected, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_inv]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The actual sixteen retained output cells have the source-mixture joint
distribution of the original selected short-DLP law on every normalized
caller, hidden-service and external-reference state. -/
theorem outputDistribution
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool) :
    (run base noQuantum N input).outputDistribution original
        (.fixedVector fun index => .bits (outcomes index)) =
      ENNReal.ofReal (∑ value : Fin (2 ^ residueSamplingBits N),
        ((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ *
          ∏ index : Fin 16,
            (selectedOutcomePMF (parameterValue input value) (outcomes index)).toReal) := by
  let actual := run base noQuantum N input
  let read := fun record : actual.Record => actual.result record
  let probability : ℝ := ∑ value : Fin (2 ^ residueSamplingBits N),
    ((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ *
      ∏ index : Fin 16,
        (selectedOutcomePMF (parameterValue input value) (outcomes index)).toReal
  have mapped := congrArg
    (fun distribution : PMF (CShape.Value (.fixedVector 16 (.bits (measurementBits N)))) =>
      distribution (.fixedVector fun index => .bits (outcomes index)))
    (ExecutionState.toPMF_mapClassical (actual.execute Reference original.state)
      (actual.execute_normalized original) read).symm
  refine mapped.trans ?_
  rw [ExecutionState.toPMF_apply, ExecutionState.mapClassical_block_mass_referenceFiberSum]
  apply congrArg ENNReal.ofReal
  have full : (∑ reference : Reference.Index,
      ExecutionState.referenceFiberSum (actual.execute Reference original.state)
        (fun entry _ => if read entry =
          CShape.Value.fixedVector (fun index => CShape.Value.bits (outcomes index))
          then 1 else 0) reference reference) = (probability : ℂ) := by
    have entries : ∀ reference : Reference.Index,
        ExecutionState.referenceFiberSum (actual.execute Reference original.state)
          (fun entry _ => if read entry =
            CShape.Value.fixedVector (fun index => CShape.Value.bits (outcomes index))
            then 1 else 0) reference reference =
          ExecutionState.referenceFiberSum original.state (fun _ _ => (probability : ℂ))
            reference reference := by
      intro reference
      have aligned := congrArg
        (fun observe : actual.Record → (context base noQuantum N).register.Index → ℂ =>
          ExecutionState.referenceFiberSum (actual.execute Reference original.state)
            observe reference reference)
        (funext fun entry => funext fun _ => vector_indicator 16 (measurementBits N)
          (fun index => entry.1.read (.storage (terminalRef base noQuantum N index).toCStorageRef))
          outcomes)
      have law := code_joint_reference base noQuantum N input
        (original.state.mapClassical
          (fun entry => (entry.1, (entry.2, entry.1))))
        (fun _ _ => 1) outcomes reference reference
      have scalar := congrArg
        (fun coefficient : ℂ => ExecutionState.referenceFiberSum original.state
          (fun _ _ => coefficient) reference reference)
        (source_probability_cast N input outcomes)
      simp only [one_mul] at law
      exact aligned.trans (law.trans
        ((ExecutionState.referenceFiberSum_mapClassical original.state
          (fun entry => (entry.1, (entry.2, entry.1))) _ reference reference).trans scalar))
    have summed := (Finset.sum_congr rfl (fun reference _ => entries reference)).trans
      (ExecutionState.referenceFiberSum_sum_constant original.state (probability : ℂ))
    have normalized : original.state.mass = 1 := original.normalized
    simpa only [normalized, Complex.ofReal_one, mul_one] using summed
  exact (congrArg Complex.re full).trans (Complex.ofReal_re probability)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
