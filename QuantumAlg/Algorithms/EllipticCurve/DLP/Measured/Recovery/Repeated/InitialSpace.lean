/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Space

/-!
# Live space of the actual selected ECDLP initialization

The original quantum preparation and terminal allocation execute before the
BitWord recovery loop. Model selection must retain their actual visited
contexts and path choices.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p)
  (problem : KnownOrderProblem E.GroupPoint)

/-- The selected initialization retains the original path's resident peak. -/
theorem selectedInitial_peakResident_eq
    (path : (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).Path) :
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).peakResidentSpace path =
      (exponentRepeatedInitial E problem).peakResidentSpace
        ((BitWord.selectForCircuitPathEquiv (exponentRepeatedInitial E problem)).symm path) := by
  let source := exponentRepeatedInitial E problem
  let original := (BitWord.selectForCircuitPathEquiv source).symm path
  have aligned : (BitWord.selectForCircuitPathEquiv source) original = path :=
    (BitWord.selectForCircuitPathEquiv source).apply_symm_apply path
  simpa only [aligned] using BitWord.selectForCircuit_peakResidentSpace source original

/-- The selected initialization retains the original path's auxiliary peak. -/
theorem selectedInitial_peakAuxiliary_eq
    (path : (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).Path) :
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).peakAuxiliarySpace path =
      (exponentRepeatedInitial E problem).peakAuxiliarySpace
        ((BitWord.selectForCircuitPathEquiv (exponentRepeatedInitial E problem)).symm path) := by
  let source := exponentRepeatedInitial E problem
  let original := (BitWord.selectForCircuitPathEquiv source).symm path
  have aligned : (BitWord.selectForCircuitPathEquiv source) original = path :=
    (BitWord.selectForCircuitPathEquiv source).apply_symm_apply path
  simpa only [aligned] using BitWord.selectForCircuit_peakAuxiliarySpace source original

/-- The original one-time initialization reaches the complete terminal resident context. -/
theorem sourceInitial_resident
    (path : (exponentRepeatedInitial E problem).Path) :
    (exponentRepeatedInitial E problem).peakResidentSpace path =
      (PublicInput.terminal E (orderWidth problem)).residentSpace := by
  change (((PublicInput.initializeWork E (orderWidth problem)).seq
    (PublicInput.allocateTerminal E (orderWidth problem))).peakResidentSpace path) = _
  have cells :
      (PublicInput.allocateTerminal E (orderWidth problem)).peakResidentSpace path.2 =
        (PublicInput.terminal E (orderWidth problem)).residentSpace :=
    (MeasurementCells.allocateFramed_peakResidentSpace _ _ _ _ _ _).trans
      (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm
  have bound := (Circuit.input_residentSpace_le_peak
    (PublicInput.allocateTerminal E (orderWidth problem)) path.2).trans_eq cells
  exact (Circuit.peakResidentSpace_seq _ _ path).trans
    ((congrArg₂ SpacePool.max
      (PublicInput.initialization_resident E (orderWidth problem) path.1)
      cells).trans (SpacePool.max_eq_right bound))

/-- The original one-time initialization reaches the complete terminal auxiliary context. -/
theorem sourceInitial_auxiliary
    (path : (exponentRepeatedInitial E problem).Path) :
    (exponentRepeatedInitial E problem).peakAuxiliarySpace path =
      (PublicInput.terminal E (orderWidth problem)).auxiliarySpace := by
  change (((PublicInput.initializeWork E (orderWidth problem)).seq
    (PublicInput.allocateTerminal E (orderWidth problem))).peakAuxiliarySpace path) = _
  have cells :
      (PublicInput.allocateTerminal E (orderWidth problem)).peakAuxiliarySpace path.2 =
        (PublicInput.terminal E (orderWidth problem)).auxiliarySpace :=
    (MeasurementCells.allocateFramed_peakAuxiliarySpace _ _ _ _ _ _).trans
      (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm
  have bound := (Circuit.input_auxiliarySpace_le_peak
    (PublicInput.allocateTerminal E (orderWidth problem)) path.2).trans_eq cells
  exact (Circuit.peakAuxiliarySpace_seq _ _ path).trans
    ((congrArg₂ SpacePool.max
      (PublicInput.initialization_auxiliary E (orderWidth problem) path.1)
      cells).trans (SpacePool.max_eq_right bound))

/-- Model selection preserves the exact complete initialization resident space. -/
theorem selectedInitial_resident
    (path : (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).Path) :
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).peakResidentSpace path =
      (PublicInput.terminal E (orderWidth problem)).residentSpace :=
  (selectedInitial_peakResident_eq E problem path).trans
    (sourceInitial_resident E problem _)

/-- Model selection preserves the exact complete initialization auxiliary space. -/
theorem selectedInitial_auxiliary
    (path : (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).Path) :
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).peakAuxiliarySpace path =
      (PublicInput.terminal E (orderWidth problem)).auxiliarySpace :=
  (selectedInitial_peakAuxiliary_eq E problem path).trans
    (sourceInitial_auxiliary E problem _)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
