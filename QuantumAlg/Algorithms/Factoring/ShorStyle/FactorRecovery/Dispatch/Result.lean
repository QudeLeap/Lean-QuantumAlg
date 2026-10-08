/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Guard.Result
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics.Selection
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Selector

/-!
# The actual sampler-priority dispatch has the original source result

The early-factor arm performs its real nominal output write. Otherwise the
actual decoded-order guard and modular-power/GCD suffix return the original
source selection. All values here come from the same actual incoming store.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

private theorem dispatch_read (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (dispatchStep (model := model) source parameter cells output store).1.read (.storage
      output.toCStorageRef) =
      if (store.read parameter).second.first.toBool then
        (store.applyOp (packEarlyOp parameter output)).read (.storage output.toCStorageRef)
      else (checkedStep (model := model) source cells output store).1.read (.storage
        output.toCStorageRef) := by
  simp only [dispatchStep]
  change (dispatchArmStep (model := model) source parameter cells output
    (store.read (.first (.second parameter))) store).1.read (.storage output.toCStorageRef) =
    if (store.read (.first (.second parameter))).toBool then
      (store.applyOp (packEarlyOp parameter output)).read (.storage output.toCStorageRef)
    else (checkedStep (model := model) source cells output store).1.read (.storage
      output.toCStorageRef)
  cases store.read (.first (.second parameter)) with
  | bit value => cases value <;> rfl

/-- The real priority branch agrees exactly with the original residue-facing source selector. -/
theorem dispatch_result (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (ordinary : ¬ (2 < N ∧ Even N)) (separate : GuardSeparation cells)
    (zeroBase : cells.zero.key ≠ cells.base.key)
    (activeBase : cells.active.key ≠ cells.base.key)
    (positiveBase : cells.positive.key ≠ cells.base.key)
    (baseValue : ClassicalAlgorithms.Modular.Residue (modulusSpec source))
    (orderValue : ClassicalAlgorithms.Word (phaseBits N + 1)) (accepted : Bool)
    (baseRead : store.read (.storage cells.base.toCStorageRef) =
      .canonicalResidue baseValue.toWord)
    (baseProjection : baseValue.val = (store.read parameter).first.toNat)
    (expandedValue : store.read (expandedRead cells) =
      .product (.bit accepted) (.unsignedWord orderValue)) :
    (dispatchStep (model := model) source parameter cells output store).1.read (.storage
      output.toCStorageRef) =
      encodeOutput (N := N) (outputOfResidue (store.read parameter) accepted orderValue) := by
  rw [dispatch_read, outputOfResidue_guard _ _ _ ordinary]
  by_cases early : (store.read parameter).second.first.toBool = true
  · simp only [if_pos early]
    rw [packEarly_result]
    simp only [if_pos early]
  · simp only [if_neg early]
    rw [checked_result (model := model) source cells output store separate zeroBase activeBase
      positiveBase
      baseValue orderValue accepted baseRead expandedValue, baseProjection]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
