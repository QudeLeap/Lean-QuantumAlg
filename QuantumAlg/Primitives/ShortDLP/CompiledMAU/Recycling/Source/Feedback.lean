/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Control
import all QuantumAlg.Core.Base.Classical.Value
import all QuantumAlg.Primitives.QFT.Source
import all Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Pure previous-bit phase selection and phase-block algebra -/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FeedbackCarrier

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma phaseBlock_one {S : Register} :
    ControlKraus.phaseBlock (S := S) 1 = 1 := by
  let block : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ :=
    ControlKraus.phaseBlock (S := S) 1
  change block = (1 : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ)
  ext row column
  by_cases bit : row.1 = column.1 <;> by_cases seed : row.2 = column.2 <;>
    simp [block, ControlKraus.phaseBlock, Matrix.one_apply, Prod.ext_iff, bit, seed]

private lemma phaseBlock_mul {S : Register} (left right : ℂ) :
    ControlKraus.phaseBlock (S := S) left * ControlKraus.phaseBlock right =
      ControlKraus.phaseBlock (left * right) := by
  let block (phase : ℂ) : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ :=
    ControlKraus.phaseBlock (S := S) phase
  have diagonal (phase : ℂ) : block phase =
      Matrix.diagonal (fun entry : Fin 2 × S.Index => if entry.1 = 0 then 1 else phase) := by
    ext row column
    by_cases bit : row.1 = column.1 <;> by_cases seed : row.2 = column.2 <;>
      simp [block, ControlKraus.phaseBlock, Matrix.diagonal_apply, Matrix.one_apply,
        Prod.ext_iff, bit, seed]
  change block left * block right = block (left * right)
  rw [diagonal, diagonal, diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext entry
  by_cases zero : entry.1 = 0 <;> simp [zero]

def selectedAngle (inverse : Bool) (separation : Nat) (value : CShape.Value (.finite 2)) : ℝ :=
  match value with
  | .finite bit => if bit.val = 1 then
      if inverse then -(QuantumFourierTransform.Source.phaseAngle separation)
      else QuantumFourierTransform.Source.phaseAngle separation
    else 0

def selectedScalar (inverse : Bool) (separation : Nat)
    (value : CShape.Value (.finite 2)) : ℂ :=
  Complex.exp ((selectedAngle inverse separation value : ℂ) * Complex.I)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FeedbackCarrier
