/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Core.Execution.Classical.Native
import all QuantumAlg.Components.Classical.Model.BitWord.Semantics
import all QuantumAlg.Components.Classical.Model.BitWord.Token
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Exact bit and word instruction placement

The existing typed instruction constructors determine a token of the built-in
model. Placement retains their actual references, widths, indices, evaluator
and native coordinate. The declaration remains explicitly selected: this
conversion produces an application of this model only.
-/

namespace QuantumAlg.BitWord

/-- Extract only the declared semantic parameters from an existing typed instruction. -/
@[implicit_reducible]
public def tokenOfClassical {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} : ClassicalOp input output pre post → Token input output
  | .bit opcode _ _ _ => .bit opcode
  | .wordUnary opcode width _ _ _ => .wordUnary opcode width
  | .wordBinary opcode width _ _ _ => .wordBinary opcode width
  | .wordResize sourceWidth targetWidth _ _ _ => .wordResize sourceWidth targetWidth
  | .addCarry width _ _ _ => .addCarry width
  | .subBorrow width _ _ _ => .subBorrow width
  | .mulFull leftWidth rightWidth _ _ _ => .mulFull leftWidth rightWidth
  | .divRem numeratorWidth divisorWidth _ _ _ => .divRem numeratorWidth divisorWidth
  | .packFiniteBits count _ _ _ => .packFiniteBits count
  | .packProduct (left := left) (right := right) _ _ _ => .packProduct left right
  | .packBoundedSignedWord width _ _ _ => .packBoundedSignedWord width
  | .packOption (payload := payload) _ _ _ => .packOption payload
  | .unpackOption (payload := payload) _ _ _ => .unpackOption payload
  | .unpackUnitResidue width _ _ _ => .unpackUnitResidue width
  | .unpackCanonicalResidue width _ _ _ => .unpackCanonicalResidue width
  | .packCanonicalResidue width _ _ _ => .packCanonicalResidue width
  | .unpackEllipticCurvePoint width _ _ _ => .unpackEllipticCurvePoint width
  | .packEllipticCurvePoint width _ _ _ => .packEllipticCurvePoint width
  | .vectorRead length width index _ _ _ => .vectorRead length width index
  | .vectorWrite length width index _ _ _ => .vectorWrite length width index
  | .vectorSwap length width left right _ _ _ => .vectorSwap length width left right
  | .vectorRowXor length width source destination _ _ _ =>
      .vectorRowXor length width source destination

/-- Place an existing typed instruction in the explicitly chosen bit/word model. -/
@[expose, implicit_reducible]
public noncomputable def application {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {input output : CShape} (op : ClassicalOp input output ctx ctx) : model.Application ctx where
  token := ⟨input, output, tokenOfClassical op⟩
  input := op.inputRef
  output := op.outputRef

/-- Migration preserves the exact deterministic value semantics of every existing instruction. -/
public theorem bitWord_application_evaluate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {input output : CShape} (op : ClassicalOp input output ctx ctx) (value : input.Value) :
    model.evaluate (application op).token value = PMF.pure (op.eval value) := by
  cases op <;> first | rfl | (cases value; rfl)

/-- Migration preserves the same width-indexed native coordinate. -/
public theorem bitWord_application_coordinate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {input output : CShape} (op : ClassicalOp input output ctx ctx) :
    model.coordinate (application op).token = op.label := by
  cases op <;> rfl

end QuantumAlg.BitWord
