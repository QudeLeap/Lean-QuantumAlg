/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Construction
public import QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Specification
public import QuantumAlg.Primitives.QFT.Semiclassical.Refined.Resources
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Construction
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Specification
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Context
import all QuantumAlg.Primitives.QFT.Semiclassical.Refined.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import Mathlib.Tactic.NormNum

/-!
# Actual live-space bounds for semiclassical Fourier readout

The supplied bank stays resident and mutable. Only the retained measurement
cells are auxiliary. The proof includes each intermediate allocation context
and the complete native adaptive execution, using its original physical bank
and the n distinct real result cells [GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

open Execution

noncomputable section

/-- The supplied bank introduces no auxiliary quantum storage. -/
public lemma qftSemiclassical_input_auxiliary (n : Nat) :
    (inputContext n).auxiliarySpace = 0 := by
  simp only [inputContext, RuntimeCtx.auxiliarySpace_addSuppliedLayout,
    RuntimeCtx.auxiliarySpace_empty]

/-- The final resident context is exactly n supplied qubits plus n real classical bits. -/
public lemma qftSemiclassical_output_resident (n : Nat) :
    (outputContext n).residentSpace = residentBudget n := by
  unfold outputContext
  rw [MeasurementCells.context_residentSpace]
  simp only [inputContext, RuntimeCtx.residentSpace_addSuppliedLayout,
    RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits =>
      change n * CShape.bitWidth (.finite 2) + 0 = n
      norm_num [CShape.bitWidth,
        Nat.clog_eq_one (le_refl 2) (le_refl 2)]
  | quantumSystems dimension =>
      change n * 0 + (bankLayout n).dimensionCount dimension = _
      rw [Nat.mul_zero, Nat.zero_add]
      exact (qubitLayout n).toQuantumLayout_dimensionCount dimension

/-- The final auxiliary context contains exactly the n retained classical results. -/
public lemma qftSemiclassical_output_auxiliary (n : Nat) :
    (outputContext n).auxiliarySpace = auxiliaryBudget n := by
  unfold outputContext
  rw [MeasurementCells.context_auxiliarySpace, qftSemiclassical_input_auxiliary, add_zero]
  funext axis
  cases axis with
  | classicalBits =>
      change n * CShape.bitWidth (.finite 2) = n
      norm_num [CShape.bitWidth,
        Nat.clog_eq_one (le_refl 2) (le_refl 2)]
  | quantumSystems dimension =>
      change n * 0 = 0
      exact Nat.mul_zero n

/-- Every visited allocation and execution frame fits the independently stated resident budget. -/
public lemma qftSemiclassical_complete_resident (inverse : Bool) (n : Nat)
    (path : (completeCode inverse n).Path) :
    (completeCode inverse n).peakResidentSpace path ≤ residentBudget n := by
  change (MeasurementCells.allocate (model := model) (inputContext n) 2 n).Path ×
    (body inverse n).Path at path
  have joined := Circuit.peakResidentSpace_seq
    (MeasurementCells.allocate (model := model) (inputContext n) 2 n)
    (Circuit.embed (ContextEmbedding.identity (outputContext n)) (body inverse n)) path
  apply joined.trans_le
  apply SpacePool.max_le
  · exact (MeasurementCells.allocate_peakResidentSpace (model := model)
      (inputContext n) 2 n path.1).trans (qftSemiclassical_output_resident n).le
  · exact (Circuit.peakResidentSpace_embed (ContextEmbedding.identity (outputContext n))
      (body inverse n) path.2).trans_le (qftSemiclassical_output_resident n).le

/-- The same complete path requires no auxiliary quantum system and at most n classical bits. -/
public lemma qftSemiclassical_complete_auxiliary (inverse : Bool) (n : Nat)
    (path : (completeCode inverse n).Path) :
    (completeCode inverse n).peakAuxiliarySpace path ≤ auxiliaryBudget n := by
  change (MeasurementCells.allocate (model := model) (inputContext n) 2 n).Path ×
    (body inverse n).Path at path
  have joined := Circuit.peakAuxiliarySpace_seq
    (MeasurementCells.allocate (model := model) (inputContext n) 2 n)
    (Circuit.embed (ContextEmbedding.identity (outputContext n)) (body inverse n)) path
  apply joined.trans_le
  apply SpacePool.max_le
  · exact (MeasurementCells.allocate_peakAuxiliarySpace (model := model)
      (inputContext n) 2 n path.1).trans (qftSemiclassical_output_auxiliary n).le
  · exact (Circuit.peakAuxiliarySpace_embed (ContextEmbedding.identity (outputContext n))
      (body inverse n) path.2).trans_le (qftSemiclassical_output_auxiliary n).le

/-- The complete allocated execution obeys the separate independent native event allowances. -/
public lemma qftSemiclassical_complete_events (inverse : Bool) (n : Nat)
    (path : (completeCode inverse n).Path) :
    (completeCode inverse n).resourcePool path ≤ eventBudget n := by
  rw [qftSemiclassical_complete_resourcePool]
  exact Refined.qftSemiclassical_refinedCode_events inverse n (wires n)
    (qftSemiclassical_wires_qubits n) (resultCell n) (bodyPath inverse n path)

/-- The whole allocated execution's original quantum time fits n+n choose 2. -/
public lemma qftSemiclassical_complete_time (inverse : Bool) (n : Nat)
    (path : (completeCode inverse n).Path) :
    (completeCode inverse n).quantumTime path ≤ n + n.choose 2 := by
  rw [qftSemiclassical_complete_quantumTime]
  exact Refined.qftSemiclassical_refinedCode_quantumTime inverse n (wires n)
    (qftSemiclassical_wires_qubits n) (resultCell n) (bodyPath inverse n path)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
