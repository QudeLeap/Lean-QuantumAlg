/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident
import Mathlib.Tactic.FinCases

/-!
# Select the original normal flag in the same complete resident inversion frame

Only the static physical roles of C and N change. The actual instructions
are placed at the corresponding original positions; W is the same
arbitrary restored work system. All three original words, pool and
history retain their physical positions. No runtime swap is introduced.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentNormal

noncomputable section

open QuantumAlg.EncodedBit

private def swapFlags : ControlledResidentFrame.Flags ≃ ControlledResidentFrame.Flags where
  toFun flags := (flags.2.1, (flags.1, flags.2.2))
  invFun flags := (flags.2.1, (flags.1, flags.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def flagsWires : Fin ControlledResidentFrame.flagsEncoding.width ≃
    Fin ControlledResidentFrame.flagsEncoding.width := by
  change Fin 3 ≃ Fin 3
  exact Equiv.swap (0 : Fin 3) (1 : Fin 3)

private def flagsLayout : FullPlacement ControlledResidentFrame.flagsEncoding
    ControlledResidentFrame.flagsEncoding :=
  FullPlacement.ofGrouping _ _ swapFlags flagsWires (by
    rintro ⟨first, normal, work⟩ index
    fin_cases index <;> cases first <;> cases normal <;> cases work <;> rfl)

/-- Select N through the actual original wire map, retaining the complete source prefix and W. -/
def layout (width : Nat) : FullPlacement (ControlledResidentFrame.encoding width)
    (ControlledResidentFrame.encoding width) :=
  ((FullPlacement.prodSwap (OutputCopy.encoding width)
    ControlledResidentFrame.flagsEncoding).compose
    (flagsLayout.appendRight (OutputCopy.encoding width))).compose
      (FullPlacement.prodSwap ControlledResidentFrame.flagsEncoding (OutputCopy.encoding width))

lemma layout_grouping (width : Nat) (state : ControlledResidentFrame.Data width) :
    (layout width).grouping state = (state.1, (state.2.2.1, (state.2.1, state.2.2.2))) := rfl

private lemma layout_initial (modulus : Nat) (input numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    (layout modulus.size).grouping.symm
        (ControlledResident.initial modulus input numerator pool (swapFlags flags)) =
      ControlledResident.initial modulus input numerator pool flags := rfl

private lemma layout_result (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (layout modulus.size).grouping.symm
        (ControlledResident.result modulus input positive bounded numerator pool
          (swapFlags flags)) =
      ControlledResident.result modulus input positive bounded numerator pool flags := rfl

def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.encoding modulus.size).width).toQuantum :=
  (layout modulus.size).place (ControlledResident.program modulus nontrivial)

/-- The original normal flag selects the same complete actual forward and original endpoints. -/
lemma program_initial_active (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input numerator : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : ControlledResidentFrame.Flags) (selected : flags.2.1 = true) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode
            (ControlledResident.initial modulus input numerator pool flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode
          (ControlledResident.result modulus input positive bounded numerator pool flags))) := by
  have actual := ControlledResident.program_initial_active modulus nontrivial environment
    input numerator coprime positive bounded pool addressZero prefixZero borrowZero
    (swapFlags flags) selected
  have placed := (layout modulus.size).place_ket_of_eq _ _ _ actual
  simpa only [program, layout_initial, layout_result] using placed

/-- N=false retains arbitrary original source values, zero inputs, numerator and C/W. -/
lemma program_apply_disabled (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (state : ControlledResidentFrame.Data modulus.size)
    (prefixZero : state.1.1.2.2.1 = 0) (addressZero : state.1.1.2.1 = 0)
    (borrowZero : state.1.1.2.2.2 = false) (control : state.1.1.1.control = false)
    (disabled : state.2.2.1 = false) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode state)) := by
  have actual := ControlledResident.program_apply_disabled modulus nontrivial environment
    ((layout modulus.size).grouping state)
    prefixZero addressZero borrowZero control disabled
  have placed := (layout modulus.size).place_ket_of_eq _ _ _ actual
  simpa only [program, Equiv.symm_apply_apply] using placed

lemma program_eventTrace (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).eventTrace =
      (ControlledResident.program modulus nontrivial).eventTrace :=
  (layout modulus.size).place_eventTrace _

lemma program_quantumTime (modulus : Nat) (nontrivial : 1 < modulus) :
    (program modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration =
      (ControlledResident.program modulus nontrivial).evaluatedEventDepth
        Resource.Event.quantumDuration :=
  (layout modulus.size).place_evaluatedEventDepth _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentNormal
