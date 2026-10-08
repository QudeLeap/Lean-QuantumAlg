/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Order.Input
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Order.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Dispatch.Result
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Selector

/-!
# The actual non-exceptional factor tail returns the original recovered-order selector

The real order-recovery output, including absence, is decoded from its actual
stored option. The same original sampler parameter and canonical base survive
the prefix. The resulting actual priority branch therefore has exactly the
original pure result for that source input and terminal sample.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

private theorem recovered_store (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (recoveredStep (model := model) source parameter phase cells output store).1 =
      (dispatchStep (model := model) source parameter cells output
        (recoveredInputStore (model := model) source parameter phase cells store)).1 := by
  dsimp only [recoveredStep, recoveryTailStep, unpackedDispatchStep, recoveredInputStore,
    BitWord.instructionStep]

/-- The actual stored-base prefix and selected factor branch return the original source result. -/
theorem recovered_result (source : Input N)
    (semantic : ClassicalAlgorithms.OrderRecovery.Input (recoverySpec source))
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (ordinary : ¬ (2 < N ∧ Even N)) (separate : GuardSeparation cells)
    (zeroBase : cells.zero.key ≠ cells.base.key)
    (activeBase : cells.active.key ≠ cells.base.key)
    (positiveBase : cells.positive.key ≠ cells.base.key)
    (orderBase : cells.order.key ≠ cells.base.key)
    (expandedBase : cells.expanded.key ≠ cells.base.key)
    (basePhase : cells.base.key ∉ phase.storageKeys)
    (baseParameter : cells.base.key ∉ parameter.storageKeys)
    (orderParameter : cells.order.key ∉ parameter.storageKeys)
    (expandedParameter : cells.expanded.key ∉ parameter.storageKeys)
    (baseValue : (store.read parameter).first.toNat = semantic.base.val)
    (phaseValue : store.read phase = .bits semantic.terminalBits) :
    (recoveredStep (model := model) source parameter phase cells output store).1.read
      (.storage output.toCStorageRef) =
      encodeOutput (N := N) (outputOfRecoveredResidue (store.read parameter)
        (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
          (recoverySpec source) semantic)) := by
  let incoming := recoveredInputStore (model := model) source parameter phase cells store
  have parameterSame : incoming.read parameter = store.read parameter :=
    recoveredInput_parameter (model := model) source parameter phase cells store
      baseParameter orderParameter expandedParameter
  have baseWord : semantic.baseResidue.toWord = semantic.base := by
    apply Fin.ext
    rfl
  have baseRead : incoming.read (.storage cells.base.toCStorageRef) =
      .canonicalResidue semantic.baseResidue.toWord :=
    (recoveredInput_base (model := model) source semantic parameter phase cells store
      orderBase expandedBase baseValue).trans
      (congrArg CShape.Value.canonicalResidue baseWord.symm)
  have baseProjection : semantic.baseResidue.val = (incoming.read parameter).first.toNat :=
    baseValue.symm.trans (congrArg (fun value => value.first.toNat) parameterSame.symm)
  have expanded := recoveredInput_order (model := model) source semantic parameter phase cells store
    basePhase baseValue phaseValue
  refine (congrArg (fun final : Store ctx => final.read (.storage output.toCStorageRef))
    (recovered_store (model := model) source parameter phase cells output store)).trans ?_
  cases recovered : ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
      (recoverySpec source) semantic with
  | none =>
    let zeroOrder := ClassicalAlgorithms.OrderRecovery.candidateWord (phaseBits N) 0
    have zeroEncoding : CShape.wordOfNat (phaseBits N + 1) 0 =
        CShape.Value.unsignedWord zeroOrder := by
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      rfl
    have expandedZero : incoming.read (expandedRead cells) =
        .product (.bit false) (CShape.wordOfNat (phaseBits N + 1) 0) := by
      simpa only [recovered] using expanded
    have expandedNone : incoming.read (expandedRead cells) =
        .product (.bit false) (.unsignedWord zeroOrder) :=
      expandedZero.trans (congrArg (fun word : CShape.Value (.unsignedWord (phaseBits N + 1)) =>
        CShape.Value.product (.bit false) word) zeroEncoding)
    refine (dispatch_result (model := model) source parameter cells output incoming ordinary
      separate
      zeroBase activeBase positiveBase semantic.baseResidue zeroOrder false baseRead
      baseProjection expandedNone).trans ?_
    rw [parameterSame]
    rfl
  | some order =>
    have expandedSome : incoming.read (expandedRead cells) =
        .product (.bit true) (.unsignedWord order) := by
      simpa only [recovered] using expanded
    refine (dispatch_result (model := model) source parameter cells output incoming ordinary
      separate
      zeroBase activeBase positiveBase semantic.baseResidue order true baseRead
      baseProjection expandedSome).trans ?_
    rw [parameterSame]
    rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
