/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Disabled
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Descending source stages by the actual unitary inverse

Only an actual unitary native stream is inverted. The reversed gate order
retains the source's prescribed order within each descending block. The
same full address, clean prefix, and moving-flag positions are restored.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma prefixGates_forward_reverse (width : Nat) (stage : Stage) (count : Nat)
    (state : Data width) :
    GateSpec.stepList (prefixGates width stage count)
      (GateSpec.stepList (prefixGates width stage count).reverse state) = state := by
  simpa only [List.reverse_reverse] using
    GateSpec.stepList_reverse_stepList (prefixGates width stage count).reverse state

/-- The reverse source word retains the same complete pool, even on arbitrary pool labels. -/
lemma prefixGates_reverse_pool (width : Nat) (stage : Stage) (count : Nat) (state : Data width) :
    (GateSpec.stepList (prefixGates width stage count).reverse state).2 = state.2 := by
  have kept := prefixGates_pool width stage count
    (GateSpec.stepList (prefixGates width stage count).reverse state)
  rw [prefixGates_forward_reverse] at kept
  exact kept.symm

/-- Native reverse source arithmetic retains the original control at its exact original position. -/
lemma prefixGates_reverse_control (width : Nat) (stage : Stage) (count : Nat)
    (state : Data width) :
    (GateSpec.stepList (prefixGates width stage count).reverse state).1.control =
      state.1.control := by
  have kept := prefixGates_control width stage count
    (GateSpec.stepList (prefixGates width stage count).reverse state)
  rw [prefixGates_forward_reverse] at kept
  exact kept.symm

/-- The real native inverse reverses the entire forward construction, including flag preparation. -/
def reverseProgram (width : Nat) (stage : Stage) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (forwardProgram width stage).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

private lemma reverseProgram_matrix (width : Nat) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) :
    (reverseProgram width stage).matrix environment =
      ((forwardProgram width stage).matrix environment)⁻¹ := by
  rw [reverseProgram, UnitaryCircuit.dagger_matrix,
    Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
      environment]
  exact Unitary.star_eq_inv _

/-- An inactive reverse stage is identity on every finite address without a range restriction. -/
lemma reverseProgram_apply_disabled (width : Nat) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (reverseProgram width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  have forward := forwardProgram_apply_disabled width stage environment state clean zero disabled
  exact (congrArg ((reverseProgram width stage).applyNormalized environment) forward).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (forwardProgram width stage) (reverseProgram width stage)
      (reverseProgram_matrix width stage environment) _)

/-- The descending native stream executes the literal reversed source prefix on its full frame. -/
lemma reverseProgram_apply_nativePrefix (width : Nat) (positive : 1 ≤ width) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (reverseProgram width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if state.1.control then
          GateSpec.stepList (prefixGates width stage (state.2.1.toNat + 1)).reverse state
          else state))) := by
  cases enabled : state.1.control with
  | false =>
      simpa only [enabled, Bool.false_eq_true, if_false] using
        reverseProgram_apply_disabled width stage environment state clean zero enabled
  | true =>
      let before := GateSpec.stepList
        (prefixGates width stage (state.2.1.toNat + 1)).reverse state
      have pool : before.2 = state.2 := prefixGates_reverse_pool width stage _ state
      have control : before.1.control = true :=
        (prefixGates_reverse_control width stage _ state).trans enabled
      have address : before.2.1 = state.2.1 := congrArg Prod.fst pool
      have beforeClean : before.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
        (congrArg (fun value : Pool width => value.2.1) pool).trans clean
      have beforeZero : before.2.2.2 = false :=
        (congrArg (fun value : Pool width => value.2.2) pool).trans zero
      have beforeWithin : before.2.1.toNat < width + 3 := by rw [address]; exact within
      have forward := forwardProgram_apply_nativePrefix width positive stage environment before
        beforeClean beforeZero beforeWithin
      rw [control, if_pos rfl, address] at forward
      have restored : GateSpec.stepList
          (prefixGates width stage (state.2.1.toNat + 1)) before = state :=
        prefixGates_forward_reverse width stage _ state
      rw [restored] at forward
      have inverse :=
        (congrArg ((reverseProgram width stage).applyNormalized environment) forward).symm.trans
          (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
            (forwardProgram width stage) (reverseProgram width stage)
            (reverseProgram_matrix width stage environment) _)
      simpa only [enabled, if_true] using inverse

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
