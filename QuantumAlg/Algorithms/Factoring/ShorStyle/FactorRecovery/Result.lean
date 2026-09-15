/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Order.Result

/-!
# Every original factor-selection branch is the result of the same native tail

The known even-modulus case returns its actually written factor two. All other
inputs use the original sampled base and terminal word in actual order recovery.
The pure residue selector is identified with the original raw-power selector by
the existing mathematical equality, including failure and early-factor priority.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem recovered_even (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (recovered : ClassicalAlgorithms.OrderRecovery.Output
      (modulusBits N) (phaseBits N)) (exceptional : 2 < N ∧ Even N) :
    outputOfRecovered parameter recovered = some 2 := by
  cases recovered <;> simp [outputOfRecovered, outputOf, exceptional]

/-- The actual complete factor tail returns the original pure selector on the original input. -/
theorem result (source : Input N)
    (semantic : ClassicalAlgorithms.OrderRecovery.Input (recoverySpec source))
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (separate : GuardSeparation cells)
    (halfActive : cells.halfPower.key ≠ cells.active.key)
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
    (step source parameter phase cells output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N) (outputOfRecovered (store.read parameter)
        (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
          (recoverySpec source) semantic)) := by
  by_cases exceptional : 2 < N ∧ Even N
  · refine (congrArg (fun final : Store ctx => final.read (.storage output.toCStorageRef))
      (step_even_store source parameter phase cells output store exceptional)).trans ?_
    refine (even_result source cells output store exceptional.1 halfActive).trans ?_
    exact congrArg (encodeOutput (N := N)) (recovered_even _ _ exceptional).symm
  · refine (congrArg (fun final : Store ctx => final.read (.storage output.toCStorageRef))
      (step_recovered_store source parameter phase cells output store exceptional)).trans ?_
    refine (recovered_result source semantic parameter phase cells output store exceptional
      separate zeroBase activeBase positiveBase orderBase expandedBase basePhase
      baseParameter orderParameter expandedParameter baseValue phaseValue).trans ?_
    exact congrArg (encodeOutput (N := N)) (outputOfRecoveredResidue_eq_outputOfRecovered _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
