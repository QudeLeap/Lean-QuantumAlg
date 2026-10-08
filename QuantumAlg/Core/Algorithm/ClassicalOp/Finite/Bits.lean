/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Packing actual binary classical-register values

The closed packing instruction reads an ordered collection of finite binary
values and writes their Boolean encodings. It preserves order and every bit of
information, including the empty collection. The descriptor carries its
width-tagged operation label; the selected execution model determines the
actual native event when the operation runs.
-/

namespace QuantumAlg.ClassicalOp

variable {kind : ProblemKind} (count : Nat) (ctx : RuntimeCtx kind)
  (input : CInputRef ctx (.fixedVector count (.finite 2)))
  (output : CWriteRef ctx (.bits count))

private theorem inputRef_packFiniteBits_proof :
    (packFiniteBits count ctx input output).inputRef = input := rfl

@[simp] public theorem inputRef_packFiniteBits :
    (packFiniteBits count ctx input output).inputRef = input :=
  inputRef_packFiniteBits_proof count ctx input output

private theorem outputRef_packFiniteBits_proof :
    (packFiniteBits count ctx input output).outputRef = output := rfl

@[simp] public theorem outputRef_packFiniteBits :
    (packFiniteBits count ctx input output).outputRef = output :=
  outputRef_packFiniteBits_proof count ctx input output

private theorem eval_packFiniteBits_bit_proof
    (operand : CShape.Value (.fixedVector count (.finite 2))) (index : Fin count) :
    ((packFiniteBits count ctx input output).eval operand).bitGet index =
      .bit (decide ((operand.get index).toFin.val = 1)) := rfl

/-- The written bit is exactly the corresponding stored binary value. -/
public theorem eval_packFiniteBits_bit
    (operand : CShape.Value (.fixedVector count (.finite 2))) (index : Fin count) :
    ((packFiniteBits count ctx input output).eval operand).bitGet index =
      .bit (decide ((operand.get index).toFin.val = 1)) :=
  eval_packFiniteBits_bit_proof count ctx input output operand index

/-- Converting the written Boolean back to a natural number recovers the input. -/
public theorem eval_packFiniteBits_recovers
    (operand : CShape.Value (.fixedVector count (.finite 2))) (index : Fin count) :
    (((packFiniteBits count ctx input output).eval operand).bitGet index).toBool.toNat =
      (operand.get index).toFin.val := by
  rw [eval_packFiniteBits_bit]
  have bound : (operand.get index).toFin.val < 2 := (operand.get index).toFin.isLt
  change (decide ((operand.get index).toFin.val = 1)).toNat = _
  by_cases one : (operand.get index).toFin.val = 1
  · simp [one]
  · have zero : (operand.get index).toFin.val = 0 := by omega
    simp [zero]

private theorem label_packFiniteBits_proof :
    (packFiniteBits count ctx input output).label =
      .nominalEncoding (.packFiniteBits count) := rfl

@[simp] public theorem label_packFiniteBits :
    (packFiniteBits count ctx input output).label =
      .nominalEncoding (.packFiniteBits count) :=
  label_packFiniteBits_proof count ctx input output

end QuantumAlg.ClassicalOp
