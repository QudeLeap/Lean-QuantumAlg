/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Token
public import QuantumAlg.Core.Algorithm.ClassicalOp.Finite
public import Mathlib.Probability.Distributions.Uniform
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Declared probability semantics of bit and word operations

Ordinary instructions retain their existing exact evaluators through point
distributions. Random-bit generation samples all actual width-indexed bit
strings uniformly, including the unique empty string at width zero. No oracle
transition is part of this native instruction catalog.
-/

namespace QuantumAlg.BitWord.Token

noncomputable section

private instance bitStringsNonempty (width : Nat) : Nonempty (CShape.Value (.bits width)) :=
  ⟨.bits fun _ => false⟩

/-- Actual normalized output distribution fixed by the selected operation token. -/
@[implicit_reducible]
public def distribution {input output : CShape} :
    Token input output → input.Value → PMF output.Value
  | .randomBits width, _ => PMF.uniformOfFintype (CShape.Value (.bits width))
  | .bit opcode, value => PMF.pure (opcode.eval value)
  | .wordUnary opcode width, value => PMF.pure (opcode.eval width value)
  | .wordBinary opcode width, value => PMF.pure (opcode.eval width value)
  | .wordResize _ targetWidth, value => PMF.pure (CShape.wordResize targetWidth value)
  | .addCarry width, value => PMF.pure (CShape.addCarry width value)
  | .subBorrow width, value => PMF.pure (CShape.subBorrow width value)
  | .mulFull leftWidth rightWidth, value => PMF.pure (CShape.mulFull leftWidth rightWidth value)
  | .divRem numeratorWidth divisorWidth, value =>
      PMF.pure (CShape.divRem numeratorWidth divisorWidth value)
  | .packFiniteBits count, value => PMF.pure (CShape.packFiniteBits count value)
  | .packProduct _ _, value => PMF.pure (CShape.packProduct value)
  | .packBoundedSignedWord width, value => PMF.pure (CShape.packBoundedSignedWord width value)
  | .packOption _, value => PMF.pure (CShape.packOption value)
  | .unpackOption _, value => PMF.pure (CShape.unpackOption value)
  | .unpackUnitResidue width, value => PMF.pure (CShape.unpackUnitResidue width value)
  | .unpackCanonicalResidue width, value => PMF.pure (CShape.unpackCanonicalResidue width value)
  | .packCanonicalResidue width, value => PMF.pure (CShape.packCanonicalResidue width value)
  | .unpackEllipticCurvePoint width, value => PMF.pure (CShape.unpackEllipticCurvePoint width value)
  | .packEllipticCurvePoint width, value => PMF.pure (CShape.packEllipticCurvePoint width value)
  | .vectorRead _ _ index, value => PMF.pure (value.get index)
  | .vectorWrite _ _ index, .product vector value =>
      PMF.pure (CShape.vectorWrite vector index value)
  | .vectorSwap _ _ left right, value => PMF.pure (CShape.vectorSwap value left right)
  | .vectorRowXor _ _ source destination, value =>
      PMF.pure (CShape.vectorRowXor value source destination)

end

end QuantumAlg.BitWord.Token
