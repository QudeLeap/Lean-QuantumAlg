/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Exact live space of the actual packed and reset measured round

Retained result and vent cells stay in the same caller context. The full
reset scopes additionally hold one binary scalar cell per existing physical
wire, then release those lexical cells. No output or incoming classical cell
is assumed empty [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round

noncomputable section

open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev RoundSpaceCtx := context base noQuantum m ell width

variable {shape : CShape}
  (parameter : CInputRef (RoundSpaceCtx base noQuantum m ell width) shape)
  (wide : 2 ≤ width) (modulus : BitVec width)
  (generator target : shape.Value → (ZMod modulus.toNat)ˣ)

/-- Actual stored-value selection keeps the complete original resident context live. -/
lemma measuredRound_selected_resident
    (path : (selected base noQuantum m ell width parameter wide modulus generator target).Path) :
    (selected base noQuantum m ell width parameter wide modulus generator target).peakResidentSpace
        path = (RoundSpaceCtx base noQuantum m ell width).residentSpace := by
  change (Circuit.embed (allowAllocation := true)
    (ContextEmbedding.identity (RoundSpaceCtx base noQuantum m ell width))
    (member base noQuantum m ell width wide modulus (generator path.1)
      (target path.1))).peakResidentSpace path.2 = _
  exact Circuit.peakResidentSpace_embed
    (ContextEmbedding.identity (RoundSpaceCtx base noQuantum m ell width)) _ path.2

/-- Selection preserves every original auxiliary role without allocating another frame. -/
lemma measuredRound_selected_auxiliary
    (path : (selected base noQuantum m ell width parameter wide modulus generator target).Path) :
    (selected base noQuantum m ell width parameter wide modulus generator target).peakAuxiliarySpace
        path = (RoundSpaceCtx base noQuantum m ell width).auxiliarySpace := by
  change (Circuit.embed (allowAllocation := true)
    (ContextEmbedding.identity (RoundSpaceCtx base noQuantum m ell width))
    (member base noQuantum m ell width wide modulus (generator path.1)
      (target path.1))).peakAuxiliarySpace path.2 = _
  exact Circuit.peakAuxiliarySpace_embed
    (ContextEmbedding.identity (RoundSpaceCtx base noQuantum m ell width)) _ path.2

variable (result : CWriteRef (RoundSpaceCtx base noQuantum m ell width) (.bits (resultBits m ell)))

/-- The real packing destination already belongs to the complete resident context. -/
lemma measuredRound_sampled_resident
    (path : (sampled base noQuantum m ell width parameter wide modulus generator target
      result).Path) :
    (sampled base noQuantum m ell width parameter wide modulus generator target
      result).peakResidentSpace path =
        (RoundSpaceCtx base noQuantum m ell width).residentSpace := by
  have first := measuredRound_selected_resident base noQuantum m ell width parameter wide modulus
    generator target path.1
  have second : (Packing.code base noQuantum m ell width result).peakResidentSpace path.2 =
      (RoundSpaceCtx base noQuantum m ell width).residentSpace :=
    Circuit.peakResidentSpace_classical
      (BitWord.selectedApplication (execution := model)
        (Packing.operation base noQuantum m ell width result)) path.2
  have composed : (sampled base noQuantum m ell width parameter wide modulus generator target
      result).peakResidentSpace path =
      SpacePool.max
        ((selected base noQuantum m ell width parameter wide modulus generator
          target).peakResidentSpace path.1)
        ((Packing.code base noQuantum m ell width result).peakResidentSpace path.2) :=
    Circuit.peakResidentSpace_seq
      (selected base noQuantum m ell width parameter wide modulus generator target)
      (Packing.code base noQuantum m ell width result) (path.1, path.2)
  exact composed.trans ((congrArg₂ SpacePool.max first second).trans (SpacePool.max_self _))

/-- Paid packing retains exactly the caller's original auxiliary storage. -/
lemma measuredRound_sampled_auxiliary
    (path : (sampled base noQuantum m ell width parameter wide modulus generator target
      result).Path) :
    (sampled base noQuantum m ell width parameter wide modulus generator target
      result).peakAuxiliarySpace path =
        (RoundSpaceCtx base noQuantum m ell width).auxiliarySpace := by
  have first := measuredRound_selected_auxiliary base noQuantum m ell width parameter wide modulus
    generator target path.1
  have second : (Packing.code base noQuantum m ell width result).peakAuxiliarySpace path.2 =
      (RoundSpaceCtx base noQuantum m ell width).auxiliarySpace :=
    Circuit.peakAuxiliarySpace_classical
      (BitWord.selectedApplication (execution := model)
        (Packing.operation base noQuantum m ell width result)) path.2
  have composed : (sampled base noQuantum m ell width parameter wide modulus generator target
      result).peakAuxiliarySpace path =
      SpacePool.max
        ((selected base noQuantum m ell width parameter wide modulus generator
          target).peakAuxiliarySpace path.1)
        ((Packing.code base noQuantum m ell width result).peakAuxiliarySpace path.2) :=
    Circuit.peakAuxiliarySpace_seq
      (selected base noQuantum m ell width parameter wide modulus generator target)
      (Packing.code base noQuantum m ell width result) (path.1, path.2)
  exact composed.trans ((congrArg₂ SpacePool.max first second).trans (SpacePool.max_self _))

/-- The complete actual resident peak includes every simultaneous scalar reset cell. -/
lemma measuredRound_resident
    (path : (code base noQuantum m ell width parameter wide modulus generator target result).Path) :
    (code base noQuantum m ell width parameter wide modulus generator target
      result).peakResidentSpace
        path = (2 * width + 4) • SpacePool.ofShape (.finite 2) +
          (RoundSpaceCtx base noQuantum m ell width).residentSpace := by
  have restart : (Reload.resetReload base noQuantum m ell width modulus.toNat).peakResidentSpace
      path.2 = (2 * width + 4) • SpacePool.ofShape (.finite 2) +
        (RoundSpaceCtx base noQuantum m ell width).residentSpace := by
    have composed := Circuit.peakResidentSpace_seq
      (BankReset.code base noQuantum m ell width)
      (Reload.code base noQuantum m ell width modulus.toNat) (path.2.1, path.2.2)
    exact composed.trans
      ((congrArg₂ SpacePool.max
        (BankReset.measuredBankReset_resident base noQuantum m ell width path.2.1)
        (Reload.measuredReload_resident base noQuantum m ell width modulus.toNat path.2.2)).trans
          (SpacePool.max_eq_left (le_add_of_nonneg_left zero_le)))
  have composed : (code base noQuantum m ell width parameter wide modulus generator target
      result).peakResidentSpace path =
      SpacePool.max
        ((sampled base noQuantum m ell width parameter wide modulus generator target
          result).peakResidentSpace path.1)
        ((Reload.resetReload base noQuantum m ell width modulus.toNat).peakResidentSpace path.2) :=
    Circuit.peakResidentSpace_seq
      (sampled base noQuantum m ell width parameter wide modulus generator target result)
      (Reload.resetReload base noQuantum m ell width modulus.toNat) (path.1, path.2)
  exact composed.trans
    ((congrArg₂ SpacePool.max
      (measuredRound_sampled_resident base noQuantum m ell width parameter wide modulus generator
        target result path.1) restart).trans
          (SpacePool.max_eq_right (le_add_of_nonneg_left zero_le)))

/-- The same lexical scratch cells are charged at the full actual auxiliary peak. -/
lemma measuredRound_auxiliary
    (path : (code base noQuantum m ell width parameter wide modulus generator target result).Path) :
    (code base noQuantum m ell width parameter wide modulus generator target
      result).peakAuxiliarySpace
        path = (2 * width + 4) • SpacePool.ofShape (.finite 2) +
          (RoundSpaceCtx base noQuantum m ell width).auxiliarySpace := by
  have restart : (Reload.resetReload base noQuantum m ell width modulus.toNat).peakAuxiliarySpace
      path.2 = (2 * width + 4) • SpacePool.ofShape (.finite 2) +
        (RoundSpaceCtx base noQuantum m ell width).auxiliarySpace := by
    have composed := Circuit.peakAuxiliarySpace_seq
      (BankReset.code base noQuantum m ell width)
      (Reload.code base noQuantum m ell width modulus.toNat) (path.2.1, path.2.2)
    exact composed.trans
      ((congrArg₂ SpacePool.max
        (BankReset.measuredBankReset_auxiliary base noQuantum m ell width path.2.1)
        (Reload.measuredReload_auxiliary base noQuantum m ell width modulus.toNat path.2.2)).trans
          (SpacePool.max_eq_left (le_add_of_nonneg_left zero_le)))
  have composed : (code base noQuantum m ell width parameter wide modulus generator target
      result).peakAuxiliarySpace path =
      SpacePool.max
        ((sampled base noQuantum m ell width parameter wide modulus generator target
          result).peakAuxiliarySpace path.1)
        ((Reload.resetReload base noQuantum m ell width modulus.toNat).peakAuxiliarySpace path.2) :=
    Circuit.peakAuxiliarySpace_seq
      (sampled base noQuantum m ell width parameter wide modulus generator target result)
      (Reload.resetReload base noQuantum m ell width modulus.toNat) (path.1, path.2)
  exact composed.trans
    ((congrArg₂ SpacePool.max
      (measuredRound_sampled_auxiliary base noQuantum m ell width parameter wide modulus generator
        target result path.1) restart).trans
          (SpacePool.max_eq_right (le_add_of_nonneg_left zero_le)))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round
