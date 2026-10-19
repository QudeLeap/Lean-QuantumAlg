/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Complete simultaneous scratch of actual half-power GCD

The actual adjacent and modulus operands each occupy a widened word. While
both remain live, the lexical Euclidean circuit uses its two state words,
condition bit and quotient/remainder pair. Thus the complete additional
capacity is six widened words and one bit, with the existing result already
in the caller's context. Both directions keep every original quantum wire.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Both actual operands and all simultaneous Euclidean scratch contribute to this capacity. -/
def spaceBound (kind : ProblemKind) (N : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (6 * (modulusBits N + 1) + 1))

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private lemma body_resident_le (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (path : (body (model := model) successor halfPower output).Path) :
    (body (model := model) successor halfPower output).peakResidentSpace path ≤
      (context ctx N).residentSpace +
        NumberTheory.GCD.lexicalAdditionalSpace model.kind (modulusBits N + 1) := by
  refine (Circuit.peakResidentSpace_seq
    (NativeAdjacentWord.code (model := model) successor (liftInput halfPower) (adjacentRef ctx N))
    (.seq (ConstantWord.circuit (model := model) (modulusRef ctx N) N) (gcdTail (model := model)
      output)) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeAdjacentWord.code_resident_le successor (liftInput halfPower)
      (adjacentRef ctx N) path.1).trans (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakResidentSpace_seq (ConstantWord.circuit (model := model) (modulusRef ctx
    N) N)
      (gcdTail (model := model) output) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (ConstantWord.constantWord_resident_le (modulusRef ctx N) N path.2.1).trans
        (fun _ => Nat.le_add_right _ _)
    · refine (Circuit.peakResidentSpace_seq (BitWord.instruction (execution := model) (clearOp
      output))
        (NumberTheory.GCD.lexicalBody (model := model) (operands ctx N) (liftWrite output))
          path.2.2).le.trans ?_
      apply SpacePool.max_le
      · exact (Circuit.peakResidentSpace_classical
          (BitWord.selectedApplication (execution := model) (clearOp output)) path.2.2.1).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact NumberTheory.GCD.gcdLexical_resident_le
          (operands ctx N) (liftWrite output) path.2.2.2

private lemma body_auxiliary_le (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (path : (body (model := model) successor halfPower output).Path) :
    (body (model := model) successor halfPower output).peakAuxiliarySpace path ≤
      (context ctx N).auxiliarySpace +
        NumberTheory.GCD.lexicalAdditionalSpace model.kind (modulusBits N + 1) := by
  refine (Circuit.peakAuxiliarySpace_seq
    (NativeAdjacentWord.code (model := model) successor (liftInput halfPower) (adjacentRef ctx N))
    (.seq (ConstantWord.circuit (model := model) (modulusRef ctx N) N) (gcdTail (model := model)
      output)) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeAdjacentWord.code_auxiliary_le successor (liftInput halfPower)
      (adjacentRef ctx N) path.1).trans (fun _ => Nat.le_add_right _ _)
  · refine (Circuit.peakAuxiliarySpace_seq (ConstantWord.circuit (model := model) (modulusRef ctx
    N) N)
      (gcdTail (model := model) output) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (ConstantWord.constantWord_auxiliary_le (modulusRef ctx N) N path.2.1).trans
        (fun _ => Nat.le_add_right _ _)
    · refine (Circuit.peakAuxiliarySpace_seq (BitWord.instruction (execution := model) (clearOp
      output))
        (NumberTheory.GCD.lexicalBody (model := model) (operands ctx N) (liftWrite output))
          path.2.2).le.trans ?_
      apply SpacePool.max_le
      · exact (Circuit.peakAuxiliarySpace_classical
          (BitWord.selectedApplication (execution := model) (clearOp output)) path.2.2.1).le.trans
          (fun _ => Nat.le_add_right _ _)
      · exact NumberTheory.GCD.gcdLexical_auxiliary_le
          (operands ctx N) (liftWrite output) path.2.2.2

section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private lemma adjacent_resident_capacity :
    (adjacentContext ctx N).residentSpace ≤ ctx.residentSpace + spaceBound kind N := by
  intro axis
  cases axis <;> simp [adjacentContext, spaceBound, SpacePool.ofShape]
  omega

private lemma adjacent_auxiliary_capacity :
    (adjacentContext ctx N).auxiliarySpace ≤ ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  cases axis <;> simp [adjacentContext, spaceBound, SpacePool.ofShape]
  omega

private lemma full_resident_capacity :
    (context ctx N).residentSpace +
        NumberTheory.GCD.lexicalAdditionalSpace kind (modulusBits N + 1) ≤
      ctx.residentSpace + spaceBound kind N := by
  intro axis
  cases axis <;> simp [context, adjacentContext, NumberTheory.GCD.lexicalAdditionalSpace,
    spaceBound, SpacePool.ofShape]
  omega

private lemma full_auxiliary_capacity :
    (context ctx N).auxiliarySpace +
        NumberTheory.GCD.lexicalAdditionalSpace kind (modulusBits N + 1) ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  cases axis <;> simp [context, adjacentContext, NumberTheory.GCD.lexicalAdditionalSpace,
    spaceBound, SpacePool.ofShape]
  omega

end

/-- The real resident peak includes both operands and the expanded Euclidean division scratch. -/
lemma code_resident_le (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (path : (code (model := model) successor halfPower output).Path) :
    (code (model := model) successor halfPower output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound model.kind N := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (.workspace (adjacentContext ctx N) (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      (body (model := model) successor halfPower output)) path).le.trans ?_
  apply SpacePool.max_le
  · exact fun _ => Nat.le_add_right _ _
  · refine (Circuit.peakResidentSpace_workspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      (body (model := model) successor halfPower output) path).le.trans ?_
    apply SpacePool.max_le
    · exact adjacent_resident_capacity
    · exact (body_resident_le successor halfPower output path).trans full_resident_capacity

/-- Every actual operand and division cell is auxiliary while its genuine scope remains live. -/
lemma code_auxiliary_le (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (path : (code (model := model) successor halfPower output).Path) :
    (code (model := model) successor halfPower output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound model.kind N := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (.workspace (adjacentContext ctx N) (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      (body (model := model) successor halfPower output)) path).le.trans ?_
  apply SpacePool.max_le
  · exact fun _ => Nat.le_add_right _ _
  · refine (Circuit.peakAuxiliarySpace_workspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      (body (model := model) successor halfPower output) path).le.trans ?_
    apply SpacePool.max_le
    · exact adjacent_auxiliary_capacity
    · exact (body_auxiliary_le successor halfPower output path).trans full_auxiliary_capacity

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
