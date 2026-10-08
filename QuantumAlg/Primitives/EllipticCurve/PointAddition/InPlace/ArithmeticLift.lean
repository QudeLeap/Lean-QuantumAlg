/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Layout
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Correction

/-!
# Compact-arithmetic lift for the in-place point carrier

The complete compact Montgomery--Kaliski carrier is the final contiguous
factor of the in-place point representation.  This module lifts literal gate
lists through those product factors and the final semantic relabeling.  The
lift preserves the exact primitive event trace and changes only the embedded
arithmetic state; it does not introduce a second arithmetic workspace.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace ArithmeticLift

noncomputable section

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK

/-- Lift one compact-carrier gate through the two point words, outer control,
and final field-name relabeling. -/
def gate (fieldWidth counterWidth : Nat)
    (source : EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth)) :
    EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth) :=
  EncodedBit.GateSpec.relabel
    (Layout.registerTupleEquiv fieldWidth counterWidth)
    (EncodedBit.GateSpec.prodRight BinaryLabelEncoding.bool
      (EncodedBit.GateSpec.prodRight (MK.wordEncoding fieldWidth)
        (EncodedBit.GateSpec.prodRight (MK.wordEncoding fieldWidth) source)))

/-- Lift a complete literal compact-arithmetic ledger into the point carrier. -/
def gates (fieldWidth counterWidth : Nat)
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth))) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  (((source.map
      (EncodedBit.GateSpec.prodRight (MK.wordEncoding fieldWidth))).map
      (EncodedBit.GateSpec.prodRight (MK.wordEncoding fieldWidth))).map
      (EncodedBit.GateSpec.prodRight BinaryLabelEncoding.bool)).map
      (EncodedBit.GateSpec.relabel
        (Layout.registerTupleEquiv fieldWidth counterWidth))

/-- Pointwise and staged presentations of the arithmetic lift agree. -/
theorem gates_eq_map (fieldWidth counterWidth : Nat)
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth))) :
    gates fieldWidth counterWidth source =
      source.map (gate fieldWidth counterWidth) := by
  simp [gates, gate]

/-- The arithmetic lift preserves every primitive in the strict event trace. -/
theorem gates_map_event (fieldWidth counterWidth : Nat)
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth))) :
    (gates fieldWidth counterWidth source).map (EncodedBit.GateSpec.event .empty) =
      source.map (EncodedBit.GateSpec.event .empty) := by
  simp [gates]

/-- The arithmetic lift preserves literal gate-list length. -/
@[simp] theorem gates_length (fieldWidth counterWidth : Nat)
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth))) :
    (gates fieldWidth counterWidth source).length = source.length := by
  simp [gates]

/-- The lifted ledger changes exactly the compact-arithmetic field. -/
theorem gates_stepList (fieldWidth counterWidth : Nat)
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth)))
    (state : Layout.Registers fieldWidth counterWidth) :
    EncodedBit.GateSpec.stepList (gates fieldWidth counterWidth source) state =
      { state with
        arithmetic := EncodedBit.GateSpec.stepList source state.arithmetic } := by
  rw [gates]
  rw [EncodedBit.GateSpec.stepList_relabel,
    EncodedBit.GateSpec.stepList_prodRight,
    EncodedBit.GateSpec.stepList_prodRight,
    EncodedBit.GateSpec.stepList_prodRight]
  rfl

/-- A lifted gate remains disjoint from the lifted image of any compact bit
that was disjoint from the source gate. -/
theorem bitDisjoint_liftArithmeticBit (fieldWidth counterWidth : Nat)
    (observed : EncodedBit (MK.Compact.encoding fieldWidth counterWidth))
    (source : EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth))
    (hdisjoint : EncodedBit.GateSpec.bitDisjoint observed source) :
    EncodedBit.GateSpec.bitDisjoint
      (Layout.liftArithmeticBit fieldWidth counterWidth observed)
      (gate fieldWidth counterWidth source) := by
  cases source with
  | x target =>
      exact Layout.liftArithmeticBit_wire_ne fieldWidth counterWidth
        target observed hdisjoint
  | cnot control target hct =>
      exact
        ⟨Layout.liftArithmeticBit_wire_ne fieldWidth counterWidth
            control observed hdisjoint.1,
          Layout.liftArithmeticBit_wire_ne fieldWidth counterWidth
            target observed hdisjoint.2⟩
  | toffoli controlA controlB target hab ha hb =>
      exact
        ⟨Layout.liftArithmeticBit_wire_ne fieldWidth counterWidth
            controlA observed hdisjoint.1,
          Layout.liftArithmeticBit_wire_ne fieldWidth counterWidth
            controlB observed hdisjoint.2.1,
          Layout.liftArithmeticBit_wire_ne fieldWidth counterWidth
            target observed hdisjoint.2.2⟩

/-- Every lifted compact gate is disjoint from every mutable-y bit. -/
theorem bitDisjoint_mutableYBit (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth)
    (source : EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth)) :
    EncodedBit.GateSpec.bitDisjoint
      (Layout.mutableYBit fieldWidth counterWidth bit)
      (gate fieldWidth counterWidth source) := by
  cases source with
  | x target =>
      exact (Layout.mutableYBit_wire_ne_liftArithmeticBit
        fieldWidth counterWidth bit target).symm
  | cnot control target hct =>
      exact
        ⟨(Layout.mutableYBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit control).symm,
          (Layout.mutableYBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit target).symm⟩
  | toffoli controlA controlB target hab ha hb =>
      exact
        ⟨(Layout.mutableYBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit controlA).symm,
          (Layout.mutableYBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit controlB).symm,
          (Layout.mutableYBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit target).symm⟩

/-- Every lifted compact gate is disjoint from every lambda bit. -/
theorem bitDisjoint_lambdaBit (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth)
    (source : EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth)) :
    EncodedBit.GateSpec.bitDisjoint
      (Layout.lambdaBit fieldWidth counterWidth bit)
      (gate fieldWidth counterWidth source) := by
  cases source with
  | x target =>
      exact (Layout.lambdaBit_wire_ne_liftArithmeticBit
        fieldWidth counterWidth bit target).symm
  | cnot control target hct =>
      exact
        ⟨(Layout.lambdaBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit control).symm,
          (Layout.lambdaBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit target).symm⟩
  | toffoli controlA controlB target hab ha hb =>
      exact
        ⟨(Layout.lambdaBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit controlA).symm,
          (Layout.lambdaBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit controlB).symm,
          (Layout.lambdaBit_wire_ne_liftArithmeticBit
            fieldWidth counterWidth bit target).symm⟩

/-- Every lifted compact gate is disjoint from the outer point-addition
control bit. -/
theorem bitDisjoint_controlBit (fieldWidth counterWidth : Nat)
    (source : EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth)) :
    EncodedBit.GateSpec.bitDisjoint
      (Layout.controlBit fieldWidth counterWidth)
      (gate fieldWidth counterWidth source) := by
  cases source with
  | x target =>
      exact Layout.liftArithmeticBit_wire_ne_controlBit
        fieldWidth counterWidth target
  | cnot control target hct =>
      exact
        ⟨Layout.liftArithmeticBit_wire_ne_controlBit
            fieldWidth counterWidth control,
          Layout.liftArithmeticBit_wire_ne_controlBit
            fieldWidth counterWidth target⟩
  | toffoli controlA controlB target hab ha hb =>
      exact
        ⟨Layout.liftArithmeticBit_wire_ne_controlBit
            fieldWidth counterWidth controlA,
          Layout.liftArithmeticBit_wire_ne_controlBit
            fieldWidth counterWidth controlB,
          Layout.liftArithmeticBit_wire_ne_controlBit
            fieldWidth counterWidth target⟩
/-- A whole lifted ledger remains disjoint from the lifted image of a compact
bit whenever its source ledger is disjoint from that bit. -/
theorem gates_bitDisjoint_liftArithmeticBit
    (fieldWidth counterWidth : Nat)
    (observed : EncodedBit (MK.Compact.encoding fieldWidth counterWidth))
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth)))
    (hsource : ∀ sourceGate, sourceGate ∈ source →
      EncodedBit.GateSpec.bitDisjoint observed sourceGate) :
    ∀ liftedGate, liftedGate ∈ gates fieldWidth counterWidth source →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.liftArithmeticBit fieldWidth counterWidth observed)
        liftedGate := by
  intro liftedGate hlifted
  rw [gates_eq_map] at hlifted
  rcases List.mem_map.mp hlifted with ⟨sourceGate, hgate, rfl⟩
  exact bitDisjoint_liftArithmeticBit fieldWidth counterWidth observed
    sourceGate (hsource sourceGate hgate)

/-- Every gate in a lifted compact ledger is disjoint from every mutable-y
bit, independently of the source ledger. -/
theorem gates_bitDisjoint_mutableYBit
    (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth)
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth))) :
    ∀ liftedGate, liftedGate ∈ gates fieldWidth counterWidth source →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.mutableYBit fieldWidth counterWidth bit) liftedGate := by
  intro liftedGate hlifted
  rw [gates_eq_map] at hlifted
  rcases List.mem_map.mp hlifted with ⟨sourceGate, _hgate, rfl⟩
  exact bitDisjoint_mutableYBit fieldWidth counterWidth bit sourceGate

/-- Every gate in a lifted compact ledger is disjoint from every persistent
slope bit, independently of the source ledger. -/
theorem gates_bitDisjoint_lambdaBit
    (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth)
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth))) :
    ∀ liftedGate, liftedGate ∈ gates fieldWidth counterWidth source →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldWidth counterWidth bit) liftedGate := by
  intro liftedGate hlifted
  rw [gates_eq_map] at hlifted
  rcases List.mem_map.mp hlifted with ⟨sourceGate, _hgate, rfl⟩
  exact bitDisjoint_lambdaBit fieldWidth counterWidth bit sourceGate

/-- Every gate in a lifted compact ledger is disjoint from the outer
point-addition control bit. -/
theorem gates_bitDisjoint_controlBit
    (fieldWidth counterWidth : Nat)
    (source : List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldWidth counterWidth))) :
    ∀ liftedGate, liftedGate ∈ gates fieldWidth counterWidth source →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.controlBit fieldWidth counterWidth) liftedGate := by
  intro liftedGate hlifted
  rw [gates_eq_map] at hlifted
  rcases List.mem_map.mp hlifted with ⟨sourceGate, _hgate, rfl⟩
  exact bitDisjoint_controlBit fieldWidth counterWidth sourceGate

end
end ArithmeticLift
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
