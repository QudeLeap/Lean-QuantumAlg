/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect
import all QuantumAlg.Core.Measure.Instrument
import all QuantumAlg.Core.Execution.State

/-!
# Positive effects pulled back through retained Z measurement

The pullback uses the projectors of the actual retained measurement instrument.
Its trace identity holds on arbitrary subnormalized density operators, including
coherence with every unmeasured reference coordinate. The instruction identity
also uses the actual Store write and recorded outcome. No new interpreter is
introduced, and this module treats only one measurement instruction.
-/

open scoped ComplexOrder

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ZMeasurement

variable {R : Register} {Outcome : Type}

/-- The retained readout-fiber projector is self-adjoint. -/
@[simp] theorem projector_conjTranspose (readout : R.Index → Outcome) (outcome : Outcome) :
    (projector readout outcome).conjTranspose = projector readout outcome := by
  simp [projector, Matrix.diagonal_conjTranspose]

/-- Applying the actual projector retains precisely the selected basis coordinates. -/
theorem projector_applyVec (readout : R.Index → Outcome) (outcome : Outcome)
    (vector : HilbertVector R) (index : R.Index) :
    (projector readout outcome).applyVec vector index =
      if readout index = outcome then vector index else 0 := by
  change ((Matrix.diagonal _).mulVec vector.ofLp) index = _
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp_all

variable [Fintype Outcome]

/-- The disjoint readout fibers account for the complete squared vector norm. -/
theorem sum_norm_projector_applyVec_sq (readout : R.Index → Outcome)
    (vector : HilbertVector R) :
    ∑ outcome, ‖(projector readout outcome).applyVec vector‖ ^ 2 = ‖vector‖ ^ 2 := by
  simp_rw [EuclideanSpace.norm_sq_eq, projector_applyVec]
  rw [Finset.sum_comm]
  simp only [apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [Fintype Outcome] in
/-- Selecting a readout fiber cannot increase a vector norm. -/
theorem projector_applyVec_norm_le (readout : R.Index → Outcome) (outcome : Outcome)
    (vector : HilbertVector R) :
    ‖(projector readout outcome).applyVec vector‖ ≤ ‖vector‖ := by
  have bound : ‖(projector readout outcome).applyVec vector‖ ^ 2 ≤ ‖vector‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, projector_applyVec]
    apply Finset.sum_le_sum
    intro index _
    split_ifs <;> simp
  nlinarith [norm_nonneg vector, norm_nonneg ((projector readout outcome).applyVec vector)]

/-- The concrete matrix pulled back through the complete retained measurement. -/
def pullbackMatrix (readout : R.Index → Outcome) (effects : Outcome → Effect R) :
    HilbertOperator R :=
  ∑ outcome, projector readout outcome * (effects outcome).matrix *
    (projector readout outcome).conjTranspose

/-- Every output coordinate belongs to its actual readout fiber. -/
theorem pullbackMatrix_applyVec (readout : R.Index → Outcome) (effects : Outcome → Effect R)
    (vector : HilbertVector R) (index : R.Index) :
    (pullbackMatrix readout effects).applyVec vector index =
      (effects (readout index)).matrix.applyVec
        ((projector readout (readout index)).applyVec vector) index := by
  unfold pullbackMatrix
  rw [HilbertOperator.sum_applyVec]
  simp only [HilbertOperator.mul_applyVec, projector_conjTranspose,
    WithLp.ofLp_sum, Finset.sum_apply, projector_applyVec]
  simp

/-- Disjoint retained fibers preserve contractivity of the outcome-dependent effects. -/
theorem pullbackMatrix_contractive (readout : R.Index → Outcome)
    (effects : Outcome → Effect R) (vector : HilbertVector R) :
    ‖(pullbackMatrix readout effects).applyVec vector‖ ≤ ‖vector‖ := by
  have split : ‖(pullbackMatrix readout effects).applyVec vector‖ ^ 2 =
      ∑ outcome, ‖(projector readout outcome).applyVec
        ((effects outcome).matrix.applyVec ((projector readout outcome).applyVec vector))‖ ^ 2 := by
    simp_rw [EuclideanSpace.norm_sq_eq, projector_applyVec, pullbackMatrix_applyVec]
    rw [Finset.sum_comm]
    simp only [apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have bound : ‖(pullbackMatrix readout effects).applyVec vector‖ ^ 2 ≤ ‖vector‖ ^ 2 := by
    rw [split, ← sum_norm_projector_applyVec_sq readout vector]
    apply Finset.sum_le_sum
    intro outcome _
    have contraction := (projector_applyVec_norm_le readout outcome
      ((effects outcome).matrix.applyVec ((projector readout outcome).applyVec vector))).trans
      ((effects outcome).contractive ((projector readout outcome).applyVec vector))
    exact pow_le_pow_left₀ (norm_nonneg _) contraction 2
  nlinarith [norm_nonneg vector,
    norm_nonneg ((pullbackMatrix readout effects).applyVec vector)]

/-- The actual retained measurement pulls positive contractive effects back to one such effect. -/
def pullbackEffect (readout : R.Index → Outcome) (effects : Outcome → Effect R) : Effect R where
  matrix := pullbackMatrix readout effects
  positive := Matrix.posSemidef_sum _ fun outcome _ =>
    (effects outcome).positive.mul_mul_conjTranspose_same (projector readout outcome)
  contractive := pullbackMatrix_contractive readout effects

/-- Exact trace pairing with the actual probability-bearing measurement branches. -/
theorem weight_pullbackEffect (readout : R.Index → Outcome) (effects : Outcome → Effect R)
    (state : DensityOperator R) :
    (pullbackEffect readout effects).weight state =
      ∑ outcome, (effects outcome).weight (branch readout outcome state) := by
  unfold Effect.weight pullbackEffect pullbackMatrix
  simp only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  congr 1
  change ((projector readout outcome * (effects outcome).matrix *
    (projector readout outcome).conjTranspose) * state.matrix).trace =
    ((effects outcome).matrix * (projector readout outcome * state.matrix *
      (projector readout outcome).conjTranspose)).trace
  simp only [projector_conjTranspose]
  calc
    _ = (projector readout outcome * ((effects outcome).matrix *
      (projector readout outcome * state.matrix))).trace := by simp only [Matrix.mul_assoc]
    _ = (((effects outcome).matrix * (projector readout outcome * state.matrix)) *
      projector readout outcome).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end ZMeasurement

namespace ExecutionState

variable {C D : Type} [Fintype C] [Fintype D] {R : Register}

/-- Observe each actual classical block with its corresponding retained-system effect. -/
def effectWeight (state : ExecutionState C R) (effects : C → Effect R) : ℝ :=
  ∑ value, (effects value).weight (state.block value)

/-- A definite classical input selects its own quantum observable. -/
theorem effectWeight_ofValue (value : C) (state : DensityOperator R)
    (effects : C → Effect R) :
    (ofValue value state).effectWeight effects = (effects value).weight state := by
  simp [effectWeight, ofValue_block, Effect.weight, apply_ite]

/-- The actual mass of an observed classical value is the corresponding indicator effect. -/
theorem effectWeight_observed_mass (state : ExecutionState C R) (read : C → D) (value : D) :
    state.effectWeight (fun input => if read input = value then Effect.one R else Effect.zero R) =
      ((state.mapClassical read).block value).mass := by
  change (∑ input, (if read input = value then Effect.one R else Effect.zero R).weight
    (state.block input)) =
    (∑ input, if read input = value then (state.block input).matrix else 0).trace.re
  rw [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro input _
  split_ifs <;> simp [DensityOperator.mass]

/-- Pulling an observation across a classical update uses the actual resulting value. -/
theorem effectWeight_mapClassical (state : ExecutionState C R) (update : C → D)
    (effects : D → Effect R) :
    (state.mapClassical update).effectWeight effects =
      state.effectWeight (fun value => effects (update value)) := by
  change (∑ output, ((effects output).matrix *
    (∑ input, if update input = output then (state.block input).matrix else 0)).trace.re) = _
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  simp only [mul_ite, mul_zero, apply_ite Matrix.trace, Matrix.trace_zero,
    apply_ite Complex.re, Complex.zero_re]
  simp [Effect.weight]

/-- Observe the outcome-dependent quantum poststates of the actual retained measurement. -/
theorem effectWeight_measureZ {Outcome : Type} [Fintype Outcome]
    (state : ExecutionState C R) (readout : R.Index → Outcome)
    (effects : C × Outcome → Effect R) :
    (state.measureZ readout).effectWeight effects =
      state.effectWeight (fun value =>
        ZMeasurement.pullbackEffect readout (fun outcome => effects (value, outcome))) := by
  simp only [effectWeight, Fintype.sum_prod_type, measureZ_block,
    ZMeasurement.weight_pullbackEffect]

/-- A retained measurement followed by its classical write has one exact pullback. -/
theorem effectWeight_measureZ_mapClassical {Outcome : Type} [Fintype Outcome]
    (state : ExecutionState C R) (readout : R.Index → Outcome)
    (update : C × Outcome → D) (effects : D → Effect R) :
    ((state.measureZ readout).mapClassical update).effectWeight effects =
      state.effectWeight (fun value => ZMeasurement.pullbackEffect readout
        (fun outcome => effects (update (value, outcome)))) := by
  rw [effectWeight_mapClassical, effectWeight_measureZ]

end ExecutionState

namespace Execution.State

/-- The pullback follows the real wire measurement, Store write and recorded outcome,
while retaining the complete context register and external reference. -/
theorem effectWeight_measureZ {ctx : RuntimeCtx .quantum} {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference H) (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (effects : (Store ctx × (H × Fin (ctx.quantumLayout.wire wire).dimension)) →
      Effect (Register.prod ctx.register Reference)) :
    (state.measureZ wire output).effectWeight effects =
      state.effectWeight (fun original => ZMeasurement.pullbackEffect
        (fun basis => basis.1 wire) (fun outcome =>
          effects (original.1.write output (.finite outcome), (original.2, outcome)))) := by
  unfold measureZ ExecutionState.effectWeight Effect.weight
  change (∑ result, ((effects result).matrix * (∑ value,
    if (value.1.1.write output (.finite value.2), (value.1.2, value.2)) = result then
      ((ExecutionState.measureZ state (fun basis => basis.1 wire)).block value).matrix
    else 0)).trace.re) = _
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, apply_ite Matrix.trace, Matrix.trace_zero,
    apply_ite Complex.re, Complex.zero_re, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (∑ value, (effects
    (value.1.1.write output (.finite value.2), (value.1.2, value.2))).weight
      ((ExecutionState.measureZ state (fun basis => basis.1 wire)).block value)) =
    ∑ original : Store ctx × H,
      (ZMeasurement.pullbackEffect (R := Register.prod ctx.register Reference)
        (fun basis => basis.1 wire) (fun outcome =>
        effects (original.1.write output (.finite outcome), (original.2, outcome)))).weight
          (state.block original)
  simp only [Fintype.sum_prod_type, ExecutionState.measureZ_block,
    ZMeasurement.weight_pullbackEffect]
  have sameDecision :
      instDecidableEqFin (ctx.quantumLayout.wire wire).dimension =
        Classical.decEq (Fin (ctx.quantumLayout.wire wire).dimension) :=
    Subsingleton.elim _ _
  rw [sameDecision]

end Execution.State

end

end QuantumAlg
