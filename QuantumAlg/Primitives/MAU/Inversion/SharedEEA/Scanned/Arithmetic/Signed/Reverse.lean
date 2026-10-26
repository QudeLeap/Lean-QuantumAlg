/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Disabled
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Descending source stages by the actual unitary inverse

Only an actual unitary native stream is inverted. The reversed gate order
retains the source's prescribed order within each descending block. The
same full address, clean prefix, and moving-flag positions are restored.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned

noncomputable section

open EncodedBit NumberTheory.SharedEEA ArithmeticTemplate

private lemma nativeWord_forward_reverse (width : Nat) (kind : ArithmeticTop.Kind) (last : Nat)
    (state : Data width) :
    GateSpec.stepList (nativeWord width kind last)
      (GateSpec.stepList (nativeWord width kind last).reverse state) = state := by
  simpa only [List.reverse_reverse] using
    GateSpec.stepList_reverse_stepList (nativeWord width kind last).reverse state

/-- The reverse source word retains the same complete pool, even on arbitrary pool labels. -/
lemma nativeWord_reverse_pool (width : Nat) (kind : ArithmeticTop.Kind) (last : Nat)
    (state : Data width) :
    (GateSpec.stepList (nativeWord width kind last).reverse state).2 = state.2 := by
  have kept := nativeWord_pool width kind last
    (GateSpec.stepList (nativeWord width kind last).reverse state)
  rw [nativeWord_forward_reverse] at kept
  exact kept.symm

/-- Native reverse source arithmetic retains the original control at its exact original position. -/
lemma nativeWord_reverse_control (width : Nat) (kind : ArithmeticTop.Kind) (last : Nat)
    (state : Data width) :
    (GateSpec.stepList (nativeWord width kind last).reverse state).1.control =
      state.1.control := by
  have kept := nativeWord_control width kind last
    (GateSpec.stepList (nativeWord width kind last).reverse state)
  rw [nativeWord_forward_reverse] at kept
  exact kept.symm

/-- The real native inverse reverses the entire forward construction, including flag preparation. -/
def reverseProgram (width : Nat) (kind : ArithmeticTop.Kind) :
    UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (forwardProgram width kind).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

private lemma reverseProgram_matrix (width : Nat) (kind : ArithmeticTop.Kind)
    (environment : OracleModel.empty.Interpretation) :
    (reverseProgram width kind).matrix environment =
      ((forwardProgram width kind).matrix environment)⁻¹ := by
  rw [reverseProgram, UnitaryCircuit.dagger_matrix,
    Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
      environment]
  exact Unitary.star_eq_inv _

/-- An inactive reverse stage is identity on every finite address without a range restriction. -/
lemma reverseProgram_apply_disabled (width : Nat) (kind : ArithmeticTop.Kind)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (reverseProgram width kind).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  have forward := forwardProgram_apply_disabled width kind environment state clean zero disabled
  exact (congrArg ((reverseProgram width kind).applyNormalized environment) forward).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (forwardProgram width kind) (reverseProgram width kind)
      (reverseProgram_matrix width kind environment) _)

/-- The descending native stream executes the literal reversed source prefix on its full frame. -/
lemma reverseProgram_apply_nativeWord (width : Nat) (positive : 1 ≤ width)
    (kind : ArithmeticTop.Kind)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (reverseProgram width kind).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if state.1.control then
          GateSpec.stepList (nativeWord width kind state.2.1.toNat).reverse state
          else state))) := by
  cases enabled : state.1.control with
  | false =>
      simpa only [enabled, Bool.false_eq_true, if_false] using
        reverseProgram_apply_disabled width kind environment state clean zero enabled
  | true =>
      let before := GateSpec.stepList
        (nativeWord width kind state.2.1.toNat).reverse state
      have pool : before.2 = state.2 := nativeWord_reverse_pool width kind _ state
      have control : before.1.control = true :=
        (nativeWord_reverse_control width kind _ state).trans enabled
      have address : before.2.1 = state.2.1 := congrArg Prod.fst pool
      have beforeClean : before.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
        (congrArg (fun value : Pool width => value.2.1) pool).trans clean
      have beforeZero : before.2.2.2 = false :=
        (congrArg (fun value : Pool width => value.2.2) pool).trans zero
      have beforeWithin : before.2.1.toNat < width + 3 := by rw [address]; exact within
      have forward := forwardProgram_apply_nativeWord width positive kind environment before
        beforeClean beforeZero beforeWithin
      rw [control, if_pos rfl, address] at forward
      have restored : GateSpec.stepList
          (nativeWord width kind state.2.1.toNat) before = state :=
        nativeWord_forward_reverse width kind _ state
      rw [restored] at forward
      have inverse :=
        (congrArg ((reverseProgram width kind).applyNormalized environment) forward).symm.trans
          (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
            (forwardProgram width kind) (reverseProgram width kind)
            (reverseProgram_matrix width kind environment) _)
      simpa only [enabled, if_true] using inverse

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned
