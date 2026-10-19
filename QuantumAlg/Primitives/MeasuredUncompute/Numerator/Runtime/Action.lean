/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Runtime
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact native phase action through runtime placement and an external reference

The already proved per-wire runtime matrix reindexing transports each
native basis-column equation without discarding its complex phase. The
same equation tensored with identity retains every external-reference
basis coordinate. This is an operator-action bridge for the existing
runtime program, not another execution semantics or a resource interface
[LYL+26, sec_point_add/sec_point_add.tex:67-105,119-122].

The native action premise belongs to the actual arithmetic program's
correctness proof. It imposes no separability condition on a later mixed
or entangled input: the full reference-labelled basis equations are
available for linear and density-matrix extension.
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorRuntimeAction

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma native_column (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (nativeInput nativeOutput row : (Qubits (OutputCopy.encoding width).width).Index)
    (phase : ℂ)
    (action : (body.binaryMatrix environment).applyVec
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeInput).vec =
        phase •
          (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeOutput).vec) :
    (body.binaryMatrix environment) row nativeInput = phase *
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeOutput) row := by
  have values := congrArg
    (fun vector : HilbertVector (Qubits (OutputCopy.encoding width).width) => vector row) action
  have column := (HilbertOperator.applyVec_ket
    ((body.binaryMatrix environment) : HilbertOperator (Qubits (OutputCopy.encoding width).width))
    nativeInput row).symm.trans values
  simpa only [PiLp.smul_apply, smul_eq_mul] using column

/-- The actual runtime matrix retains the complete native basis-column phase. -/
lemma runtime_column (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (nativeInput nativeOutput : (Qubits (OutputCopy.encoding width).width).Index)
    (phase : ℂ)
    (action : (body.binaryMatrix environment).applyVec
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeInput).vec =
        phase •
          (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeOutput).vec)
    (row : (context width).register.Index) :
    ((NumeratorRuntime.program width body).matrix environment) row ((frameBasis width).symm
      nativeInput) =
      phase * (NormalizedVector.ket (R := (context width).register)
        ((frameBasis width).symm nativeOutput)) row := by
  have placed := NumeratorRuntime.program_binary_matrix (environment := environment) width body row
    ((frameBasis width).symm nativeInput)
  rw [Equiv.apply_symm_apply] at placed
  refine placed.trans ((native_column width body nativeInput nativeOutput
    (frameBasis width row) phase action).trans ?_)
  have labels : frameBasis width row = nativeOutput ↔
      row = (frameBasis width).symm nativeOutput := by
    constructor
    · intro same
      exact (frameBasis width).injective
        (same.trans ((frameBasis width).apply_symm_apply nativeOutput).symm)
    · intro same
      exact (congrArg (frameBasis width) same).trans
        ((frameBasis width).apply_symm_apply nativeOutput)
  simp only [NormalizedVector.ket_apply, labels]

/-- An arbitrary native phase action survives the actual runtime wire placement exactly. -/
lemma runtime_ket (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (nativeInput nativeOutput : (Qubits (OutputCopy.encoding width).width).Index)
    (phase : ℂ)
    (action : (body.binaryMatrix environment).applyVec
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeInput).vec =
        phase •
          (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeOutput).vec) :
    ((NumeratorRuntime.program width body).applyVec environment)
      (NormalizedVector.ket (R := (context width).register)
        ((frameBasis width).symm nativeInput)).vec =
      phase • (NormalizedVector.ket (R := (context width).register)
        ((frameBasis width).symm nativeOutput)).vec := by
  ext row
  change HilbertOperator.applyVec
    (((NumeratorRuntime.program width body).matrix environment) : HilbertOperator (context
      width).register)
    (NormalizedVector.ket (R := (context width).register)
      ((frameBasis width).symm nativeInput)).vec row = _
  rw [HilbertOperator.applyVec_ket]
  exact runtime_column width body nativeInput nativeOutput phase action row

/-- Tensoring the same placed program with identity keeps every complete reference-labelled ket. -/
lemma reference_ket (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (nativeInput nativeOutput : (Qubits (OutputCopy.encoding width).width).Index)
    (phase : ℂ)
    (action : (body.binaryMatrix environment).applyVec
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeInput).vec =
        phase •
          (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width) nativeOutput).vec)
    {Reference : Register} (reference : Reference.Index) :
    (UnitaryOperator.prodTensor ((NumeratorRuntime.program width body).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
      (NormalizedVector.ket (R := Register.prod (context width).register Reference)
        ((frameBasis width).symm nativeInput, reference)).vec =
      phase • (NormalizedVector.ket (R := Register.prod (context width).register Reference)
        ((frameBasis width).symm nativeOutput, reference)).vec := by
  ext ⟨row, other⟩
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor ((NumeratorRuntime.program width body).matrix environment)
      (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod (context width).register Reference))
    (NormalizedVector.ket (R := Register.prod (context width).register Reference)
      ((frameBasis width).symm nativeInput, reference)).vec (row, other) = _
  rw [HilbertOperator.applyVec_ket, UnitaryOperator.prodTensor_apply,
    runtime_column width body nativeInput nativeOutput phase action row]
  change (phase * (NormalizedVector.ket (R := (context width).register)
      ((frameBasis width).symm nativeOutput)) row) * (if other = reference then 1 else 0) =
    phase * (NormalizedVector.ket (R := Register.prod (context width).register Reference)
      ((frameBasis width).symm nativeOutput, reference)) (row, other)
  rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
  have joint : ((row, other) : (Register.prod (context width).register Reference).Index) =
      ((frameBasis width).symm nativeOutput, reference) ↔
        row = (frameBasis width).symm nativeOutput ∧ other = reference := by
    constructor
    · intro same
      exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    · intro same
      exact Prod.ext same.1 same.2
  simp only [joint]
  by_cases same : row = (frameBasis width).symm nativeOutput <;>
    by_cases refSame : other = reference <;> simp [same, refSame]

end

end QuantumAlg.MeasuredUncompute.NumeratorRuntimeAction
