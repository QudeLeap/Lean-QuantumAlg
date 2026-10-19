/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Independent resources of actual half-order modular powering

The closed native budget adds the actual right shift to the existing full
modular-power envelope. Simultaneous classical scratch is the half-order word
plus all real powering and multiplication workspace, namely `t+8m+3` bits.
Every original quantum wire and classical entry remains live in these peaks.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower

noncomputable section

open ClassicalRoutines

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Independent native events for the real shift and complete modular-power implementation. -/
def eventEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) :
    ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftRight (phaseBits N + 1)))) +
    Modular.NativePower.eventEnvelope model (modulusBits N) (phaseBits N + 1)

/-- Independent allowance for the half-order word and all simultaneous power scratch. -/
def spaceBound (kind : ProblemKind) (N : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (phaseBits N + 8 * modulusBits N + 3))

/-- The actual resource path fits the stated shift plus modular-power native event envelope. -/
lemma code_pool_le (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N)))
    (path : (code (model := model) source base order output).Path) :
    (code (model := model) source base order output).resourcePool path ≤ eventEnvelope model N := by
  refine (congrArg ResourcePool.ofList (code_eventTrace source base order output path)).le.trans ?_
  change ResourcePool.singleton
      (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftRight (phaseBits N + 1)))) +
        (Modular.NativePower.into (model := model) (modulusSpec source) (liftInput base)
          (.storage (halfRef ctx N).toCStorageRef) (liftWrite output)).resourcePool path.2 ≤ _
  exact add_le_add le_rfl
    (Modular.NativePower.nativePower_into_pool_le (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output) path.2)

/-- The actual native unit depth includes the right shift and every power initialization step. -/
lemma code_unitDepth_le (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N)))
    (path : (code (model := model) source base order output).Path) :
    (code (model := model) source base order output).depth (fun _ => 1) path ≤
      1 + (2 * modulusBits N + 5 + 6 * (phaseBits N + 1)) := by
  rcases path with ⟨shiftPath, powerPath⟩
  change ((BitWord.instruction (execution := model) (shiftOp order)).seq
    (Modular.NativePower.into (model := model) (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output))).depth
        (fun _ => 1) (shiftPath, powerPath) ≤ _
  rw [Circuit.depth_seq, BitWord.bitWord_instruction_depth]
  exact Nat.add_le_add_left
    (Modular.NativePower.nativePower_into_unitDepth_le (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output) powerPath) 1

private lemma resident_capacity {kind : ProblemKind} {ctx : RuntimeCtx kind} :
    (context ctx N).residentSpace + Modular.NativePower.powerSpace kind (modulusBits N) ≤
      ctx.residentSpace + spaceBound kind N := by
  intro axis
  cases axis <;> simp [context, Modular.NativePower.powerSpace, spaceBound, SpacePool.ofShape]
  omega

private lemma auxiliary_capacity {kind : ProblemKind} {ctx : RuntimeCtx kind} :
    (context ctx N).auxiliarySpace + Modular.NativePower.powerSpace kind (modulusBits N) ≤
      ctx.auxiliarySpace + spaceBound kind N := by
  intro axis
  cases axis <;> simp [context, Modular.NativePower.powerSpace, spaceBound, SpacePool.ofShape]
  omega

/-- The actual resident peak includes the parent frame, half-order cell and power scratch. -/
lemma code_resident_le (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N)))
    (path : (code (model := model) source base order output).Path) :
    (code (model := model) source base order output).peakResidentSpace path ≤
      ctx.residentSpace + spaceBound model.kind N := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh
    (body (model := model) source base order output) path).le.trans ?_
  apply SpacePool.max_le
  · exact fun _axis => Nat.le_add_right _ _
  · refine (Circuit.peakResidentSpace_seq (BitWord.instruction (execution := model) (shiftOp order))
      (Modular.NativePower.into (model := model) (modulusSpec source) (liftInput base)
        (.storage (halfRef ctx N).toCStorageRef) (liftWrite output)) path).le.trans ?_
    apply SpacePool.max_le
    · refine (Circuit.peakResidentSpace_classical
        (BitWord.selectedApplication (execution := model) (shiftOp order)) path.1).le.trans ?_
      intro axis
      exact (Nat.le_add_right ((context ctx N).residentSpace axis)
        (Modular.NativePower.powerSpace model.kind (modulusBits N) axis)).trans
        (resident_capacity (ctx := ctx) (N := N) axis)
    · exact (Modular.NativePower.nativePower_into_resident_le (modulusSpec source)
        (liftInput base) (.storage (halfRef ctx N).toCStorageRef) (liftWrite output) path.2).trans
        resident_capacity

/-- The same actual trace counts all newly owned scratch in its auxiliary peak. -/
lemma code_auxiliary_le (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N)))
    (path : (code (model := model) source base order output).Path) :
    (code (model := model) source base order output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + spaceBound model.kind N := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh
    (body (model := model) source base order output) path).le.trans ?_
  apply SpacePool.max_le
  · exact fun _axis => Nat.le_add_right _ _
  · refine (Circuit.peakAuxiliarySpace_seq
      (BitWord.instruction (execution := model) (shiftOp order))
      (Modular.NativePower.into (model := model) (modulusSpec source) (liftInput base)
        (.storage (halfRef ctx N).toCStorageRef) (liftWrite output)) path).le.trans ?_
    apply SpacePool.max_le
    · refine (Circuit.peakAuxiliarySpace_classical
        (BitWord.selectedApplication (execution := model) (shiftOp order)) path.1).le.trans ?_
      intro axis
      exact (Nat.le_add_right ((context ctx N).auxiliarySpace axis)
        (Modular.NativePower.powerSpace model.kind (modulusBits N) axis)).trans
        (auxiliary_capacity (ctx := ctx) (N := N) axis)
    · exact (Modular.NativePower.nativePower_into_auxiliary_le (modulusSpec source)
        (liftInput base) (.storage (halfRef ctx N).toCStorageRef) (liftWrite output) path.2).trans
        auxiliary_capacity

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower
