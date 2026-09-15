/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Components.Control
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Xor
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.Word.CopyValue

/-!
# Semantic realization of controlled encoded circuits

This module connects the checked Core `UnitaryCircuit.controlQubitsAt` constructor to
proof-only encoded-basis semantics.  The controlled circuit remains the source
of both execution and resource accounting; no operator or resource witness is
accepted from a caller.
-/

section

namespace QuantumAlg

noncomputable section

namespace UnitaryCircuit

/-- Physical relabeling by a uniform offset leaves normalized-state semantics
unchanged. -/
@[simp] theorem shiftPhysicalIdx_applyNormalized {R : Register}
    (offset : Nat) (program : UnitaryCircuit R) (state : NormalizedVector R) :
    (UnitaryCircuit.shiftPhysicalIdx offset program).applyNormalized state =
      program.applyNormalized state := by
  apply NormalizedVector.ext
  intro index
  change
    (UnitaryCircuit.shiftPhysicalIdx offset program).applyVec state index =
      program.applyVec state index
  rw [UnitaryCircuit.applyVec, UnitaryCircuit.applyVec, UnitaryCircuit.shiftPhysicalIdx_matrix]

/-- Certified disjoint layout for one leading physical control wire and a
body shifted one wire to the right. -/
theorem leadingControlLayout {n : Nat} (program : UnitaryCircuit (Qubits n)) :
    PhysicalLayout.DisjointMerge [0]
      (UnitaryCircuit.shiftPhysicalIdx 1 program).physical_idx where
  left_nodup := by simp
  right_nodup := (UnitaryCircuit.shiftPhysicalIdx 1 program).physical_idx_nodup
  disjoint := by
    rw [UnitaryCircuit.shiftPhysicalIdx_physical_idx, List.disjoint_left]
    intro index hzero hshifted
    simp only [List.mem_singleton] at hzero
    subst index
    obtain ⟨source, _, equality⟩ := List.mem_map.mp hshifted
    omega

/-- Add one actual leading qubit control, active on `true`, while shifting the
complete body footprint away from the new physical wire zero. -/
def controlLeading {n : Nat} (program : UnitaryCircuit (Qubits n)) :
    UnitaryCircuit (Qubits (1 + n)) :=
  UnitaryCircuit.controlQubitsAt [0] (UnitaryCircuit.shiftPhysicalIdx 1 program)
    (leadingControlLayout program) (1 : Fin 2)

/-- A leading true-control and its shifted body stay inside the canonical
combined physical register whenever the body stays inside its own range. -/
theorem controlLeading_physical_idx_subset_range {n : Nat}
    (program : UnitaryCircuit (Qubits n))
    (contained : program.physical_idx ⊆ List.range n) :
    (controlLeading program).physical_idx ⊆ List.range (1 + n) := by
  unfold controlLeading
  apply UnitaryCircuit.controlQubitsAt_physical_idx_subset
  · intro index hindex
    rw [List.mem_singleton] at hindex
    subst index
    exact List.mem_range.mpr (by omega)
  · exact UnitaryCircuit.shiftPhysicalIdx_physical_idx_subset_range 1 program contained

@[simp] theorem controlLeading_eventCost {n : Nat}
    (program : UnitaryCircuit (Qubits n)) :
    (controlLeading program).eventCost =
      ResourcePool.controlForDimension 2 program.eventCost := by
  simp [controlLeading]

@[simp] theorem controlLeading_eventDepth {n : Nat}
    (program : UnitaryCircuit (Qubits n)) :
    (controlLeading program).eventDepth =
      .controlled "circuit-control"
        (DepthExpr.controlEventsForDimension 2 program.eventDepth) := by
  simp [controlLeading]

/-- A checked leading true-control transports any proved computational-basis
endpoint of the body circuit.  This endpoint form is useful for arithmetic
circuits whose public contract intentionally covers only canonical clean
inputs rather than exposing an artificial total semantic step. -/
theorem controlQubitsAt_applyNormalized_ket_true_of_eq {n : Nat}
    (controlSystemIdx : List Nat) (program : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx program.physical_idx)
    {input output : Fin (2 ^ n)}
    (h : program.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output) :
    (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout (1 : Fin 2)).applyNormalized
        (NormalizedVector.ket (prodEquiv ((1 : Fin 2), input))) =
      NormalizedVector.ket (prodEquiv ((1 : Fin 2), output)) := by
  apply NormalizedVector.ext
  intro index
  have hcontrol :=
    UnitaryOperator.controlledQubits_applyVec_ket1_tensor
      program.matrix
      ((NormalizedVector.ket input : NormalizedVector (Qubits n)) :
        HilbertVector (Qubits n))
  have hbody := congrArg
    (fun state : NormalizedVector (Qubits n) =>
      (state : HilbertVector (Qubits n))) h
  have hinputNormalized :=
    NormalizedVector.tensor_ket (m := 1) (n := n) (1 : Fin 2) input
  have hinput := congrArg
    (fun state : NormalizedVector (Qubits (1 + n)) =>
      (state : HilbertVector (Qubits (1 + n)))) hinputNormalized
  have houtputNormalized :=
    NormalizedVector.tensor_ket (m := 1) (n := n) (1 : Fin 2) output
  have houtput := congrArg
    (fun state : NormalizedVector (Qubits (1 + n)) =>
      (state : HilbertVector (Qubits (1 + n)))) houtputNormalized
  change
    (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout (1 : Fin 2)).applyVec
        (NormalizedVector.ket (prodEquiv ((1 : Fin 2), input)) :
          NormalizedVector (Qubits (1 + n))) index =
      (NormalizedVector.ket (prodEquiv ((1 : Fin 2), output)) :
        NormalizedVector (Qubits (1 + n))) index
  rw [UnitaryCircuit.applyVec, UnitaryCircuit.controlQubitsAt_matrix]
  change
    (UnitaryOperator.controlledQubits program.matrix).applyVec
        (NormalizedVector.ket (prodEquiv ((1 : Fin 2), input)) :
          NormalizedVector (Qubits (1 + n))) index = _
  rw [← hinput]
  have htotal :
      (UnitaryOperator.controlledQubits program.matrix).applyVec
          (HilbertVector.tensor
            ((NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) :
              NormalizedVector (Qubits 1)) : HilbertVector (Qubits 1))
            ((NormalizedVector.ket input : NormalizedVector (Qubits n)) :
              HilbertVector (Qubits n))) =
        (NormalizedVector.ket (prodEquiv ((1 : Fin 2), output)) :
          NormalizedVector (Qubits (1 + n))) := by
    calc
      _ = HilbertVector.tensor
            ((NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) :
              NormalizedVector (Qubits 1)) : HilbertVector (Qubits 1))
            (program.matrix.applyVec
              (NormalizedVector.ket input : NormalizedVector (Qubits n))) :=
        hcontrol
      _ = HilbertVector.tensor
            ((NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) :
              NormalizedVector (Qubits 1)) : HilbertVector (Qubits 1))
            (NormalizedVector.ket output : NormalizedVector (Qubits n)) := by
        exact congrArg
          (fun state : HilbertVector (Qubits n) =>
            HilbertVector.tensor
              ((NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) :
                NormalizedVector (Qubits 1)) : HilbertVector (Qubits 1))
              state) hbody
      _ = _ := houtput
  exact congrArg
    (fun state : HilbertVector (Qubits (1 + n)) => state index) htotal

/-- A checked leading true-control is the identity on a false-control basis
state, independently of the body circuit. -/
theorem controlQubitsAt_applyNormalized_ket_false {n : Nat}
    (controlSystemIdx : List Nat) (program : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx program.physical_idx)
    (input : Fin (2 ^ n)) :
    (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout (1 : Fin 2)).applyNormalized
        (NormalizedVector.ket (prodEquiv ((0 : Fin 2), input))) =
      NormalizedVector.ket (prodEquiv ((0 : Fin 2), input)) := by
  apply NormalizedVector.ext
  intro index
  have hcontrol :=
    UnitaryOperator.controlledQubits_applyVec_ket0_tensor
      program.matrix
      ((NormalizedVector.ket input : NormalizedVector (Qubits n)) :
        HilbertVector (Qubits n))
  have hproductNormalized :=
    NormalizedVector.tensor_ket (m := 1) (n := n) (0 : Fin 2) input
  have hproduct := congrArg
    (fun state : NormalizedVector (Qubits (1 + n)) =>
      (state : HilbertVector (Qubits (1 + n)))) hproductNormalized
  change
    (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout (1 : Fin 2)).applyVec
        (NormalizedVector.ket (prodEquiv ((0 : Fin 2), input)) :
          NormalizedVector (Qubits (1 + n))) index =
      (NormalizedVector.ket (prodEquiv ((0 : Fin 2), input)) :
        NormalizedVector (Qubits (1 + n))) index
  rw [UnitaryCircuit.applyVec, UnitaryCircuit.controlQubitsAt_matrix]
  change
    (UnitaryOperator.controlledQubits program.matrix).applyVec
        (NormalizedVector.ket (prodEquiv ((0 : Fin 2), input)) :
          NormalizedVector (Qubits (1 + n))) index = _
  rw [← hproduct]
  exact congrArg
    (fun state : HilbertVector (Qubits (1 + n)) => state index) hcontrol

/-- A proved body endpoint lifts through the canonical leading true-control. -/
theorem controlLeading_applyNormalized_ket_true_of_eq {n : Nat}
    (program : UnitaryCircuit (Qubits n)) {input output : Fin (2 ^ n)}
    (h : program.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output) :
    (controlLeading program).applyNormalized
        (NormalizedVector.ket (prodEquiv ((1 : Fin 2), input))) =
      NormalizedVector.ket (prodEquiv ((1 : Fin 2), output)) := by
  apply controlQubitsAt_applyNormalized_ket_true_of_eq
  simpa using h

/-- The canonical leading true-control is inactive on every false-control
computational-basis state. -/
theorem controlLeading_applyNormalized_ket_false {n : Nat}
    (program : UnitaryCircuit (Qubits n)) (input : Fin (2 ^ n)) :
    (controlLeading program).applyNormalized
        (NormalizedVector.ket (prodEquiv ((0 : Fin 2), input))) =
      NormalizedVector.ket (prodEquiv ((0 : Fin 2), input)) := by
  exact controlQubitsAt_applyNormalized_ket_false [0]
    (UnitaryCircuit.shiftPhysicalIdx 1 program) (leadingControlLayout program) input

/-- Encoding-level form of the canonical active-control endpoint.  Keeping the
width symbolic prevents fixed-width clients from unfolding a large product
encoding merely to bridge `Bool × Data` to its raw product basis label. -/
theorem controlLeading_applyNormalized_encoded_true_of_eq {Data : Type}
    (encoding : BinaryLabelEncoding Data)
    (program : UnitaryCircuit (Qubits encoding.width)) {input output : Data}
    (h : program.applyNormalized
        (NormalizedVector.ket (encoding.encode input)) =
      NormalizedVector.ket (encoding.encode output)) :
    (controlLeading program).applyNormalized
        (NormalizedVector.ket
          ((BinaryLabelEncoding.prod BinaryLabelEncoding.bool encoding).encode
            (true, input))) =
      NormalizedVector.ket
        ((BinaryLabelEncoding.prod BinaryLabelEncoding.bool encoding).encode
          (true, output)) := by
  change
    (controlLeading program).applyNormalized
        (NormalizedVector.ket
          (prodEquiv ((1 : Fin 2), encoding.encode input))) =
      NormalizedVector.ket
        (prodEquiv ((1 : Fin 2), encoding.encode output))
  exact controlLeading_applyNormalized_ket_true_of_eq program h

/-- Encoding-level form of the canonical inactive-control endpoint. -/
theorem controlLeading_applyNormalized_encoded_false {Data : Type}
    (encoding : BinaryLabelEncoding Data)
    (program : UnitaryCircuit (Qubits encoding.width)) (input : Data) :
    (controlLeading program).applyNormalized
        (NormalizedVector.ket
          ((BinaryLabelEncoding.prod BinaryLabelEncoding.bool encoding).encode
            (false, input))) =
      NormalizedVector.ket
        ((BinaryLabelEncoding.prod BinaryLabelEncoding.bool encoding).encode
          (false, input)) := by
  change
    (controlLeading program).applyNormalized
        (NormalizedVector.ket
          (prodEquiv ((0 : Fin 2), encoding.encode input))) =
      NormalizedVector.ket
        (prodEquiv ((0 : Fin 2), encoding.encode input))
  exact controlLeading_applyNormalized_ket_false program (encoding.encode input)

/-! ## A control bit inside a larger encoded prefix -/

/-- Number of encoded-prefix wires physically preceding an addressed control. -/
def encodedControlPrefixWidth {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding) : Nat :=
  control.wire.val

/-- Number of encoded-prefix wires physically following an addressed control. -/
def encodedControlSuffixWidth {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding) : Nat :=
  encoding.width - 1 - control.wire.val

theorem encodedControl_width_eq {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding) :
    encodedControlPrefixWidth control +
        (1 + encodedControlSuffixWidth control) =
      encoding.width := by
  unfold encodedControlPrefixWidth encodedControlSuffixWidth
  omega

/-- Pack `prefix × control × suffix` into the original encoded-prefix
basis order. -/
def encodedControlPartsEquiv {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding) :
    (Fin (2 ^ encodedControlPrefixWidth control) ×
      (Fin 2 × Fin (2 ^ encodedControlSuffixWidth control))) ≃
        Fin (2 ^ encoding.width) :=
  ((Equiv.prodCongr (Equiv.refl _)
      (prodEquiv (m := 1) (n := encodedControlSuffixWidth control))).trans
    (prodEquiv (m := encodedControlPrefixWidth control)
      (n := 1 + encodedControlSuffixWidth control))).trans
    (finCongr (congrArg (fun width : Nat => 2 ^ width)
      (encodedControl_width_eq control)))

@[simp] theorem encodedControlPartsEquiv_apply {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    (prefixValue : Fin (2 ^ encodedControlPrefixWidth control))
    (enabled : Fin 2)
    (suffix : Fin (2 ^ encodedControlSuffixWidth control)) :
    encodedControlPartsEquiv control (prefixValue, enabled, suffix) =
      finCongr (congrArg (fun width : Nat => 2 ^ width)
        (encodedControl_width_eq control))
        (prodEquiv (prefixValue, prodEquiv (enabled, suffix))) := by
  rfl

/-- Reassociate `prefix × (control × (suffix × body))` into the
canonical `encoded-prefix × body` basis order. -/
def encodedControlReindexEquiv {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    (bodyWidth : Nat) :
    Fin (2 ^ (encodedControlPrefixWidth control +
      (1 + (encodedControlSuffixWidth control + bodyWidth)))) ≃
      Fin (2 ^ (encoding.width + bodyWidth)) :=
  let splitPrefix := prodEquiv
    (m := encodedControlPrefixWidth control)
    (n := 1 + (encodedControlSuffixWidth control + bodyWidth)) |>.symm
  let splitControl := Equiv.prodCongr (Equiv.refl _)
    (prodEquiv (m := 1)
      (n := encodedControlSuffixWidth control + bodyWidth)).symm
  let splitBody := Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.refl _)
      (prodEquiv (m := encodedControlSuffixWidth control)
        (n := bodyWidth)).symm)
  let reassociateBody := Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodAssoc (Fin 2)
      (Fin (2 ^ encodedControlSuffixWidth control))
      (Fin (2 ^ bodyWidth))).symm
  let reassociateAll :=
    (Equiv.prodAssoc (Fin (2 ^ encodedControlPrefixWidth control))
      (Fin 2 × Fin (2 ^ encodedControlSuffixWidth control))
      (Fin (2 ^ bodyWidth))).symm
  splitPrefix |>.trans splitControl |>.trans splitBody |>.trans
    reassociateBody |>.trans reassociateAll |>.trans
    (Equiv.prodCongr (encodedControlPartsEquiv control) (Equiv.refl _)) |>.trans
    (prodEquiv (m := encoding.width) (n := bodyWidth))

@[simp] theorem encodedControlReindexEquiv_apply {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    {bodyWidth : Nat}
    (prefixValue : Fin (2 ^ encodedControlPrefixWidth control))
    (enabled : Fin 2)
    (suffix : Fin (2 ^ encodedControlSuffixWidth control))
    (body : Fin (2 ^ bodyWidth)) :
    encodedControlReindexEquiv control bodyWidth
        (prodEquiv (prefixValue,
          prodEquiv (enabled, prodEquiv (suffix, body)))) =
      prodEquiv
        (encodedControlPartsEquiv control
          (prefixValue, enabled, suffix), body) := by
  simp [encodedControlReindexEquiv]

/-- The middle component of the packed decomposition is exactly the addressed
wire's little-endian basis bit. -/
theorem encodedControlPartsEquiv_testBit {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    (prefixValue : Fin (2 ^ encodedControlPrefixWidth control))
    (enabled : Fin 2)
    (suffix : Fin (2 ^ encodedControlSuffixWidth control)) :
    ((encodedControlPartsEquiv control
        (prefixValue, enabled, suffix)).val.testBit
          (WireAddress.bitIndex control.wire).val).toNat = enabled.val := by
  rw [encodedControlPartsEquiv_apply]
  simp only [finCongr_apply_coe]
  have hindex : (WireAddress.bitIndex control.wire).val =
      encodedControlSuffixWidth control := by
    rfl
  rw [hindex]
  let selected : Fin (1 + encodedControlSuffixWidth control) :=
    ⟨encodedControlSuffixWidth control, by omega⟩
  have hright := prodEquiv_testBit_right
    (m := encodedControlPrefixWidth control)
    (n := 1 + encodedControlSuffixWidth control) prefixValue
    (prodEquiv (m := 1) (n := encodedControlSuffixWidth control)
      (enabled, suffix)) selected
  have hhigh := prodEquiv_testBit_left
    (m := 1) (n := encodedControlSuffixWidth control)
    enabled suffix ⟨0, by omega⟩
  simp only [selected, Nat.add_zero] at hright hhigh
  calc
    _ = ((prodEquiv (m := 1)
          (n := encodedControlSuffixWidth control)
          (enabled, suffix)).val.testBit
          (encodedControlSuffixWidth control)).toNat :=
      congrArg Bool.toNat hright
    _ = (enabled.val.testBit 0).toNat := congrArg Bool.toNat hhigh
    _ = enabled.val := by fin_cases enabled <;> decide

/-- Control an actual body circuit by one addressed bit inside a larger
encoded prefix.  Untouched prefix/suffix wires are carried structurally, while
the body is placed immediately after the complete encoded prefix. -/
def controlAtEncodedBit {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    {n : Nat} (program : UnitaryCircuit (Qubits n)) :
    UnitaryCircuit (Qubits (encoding.width + n)) :=
  let withSuffix := UnitaryCircuit.prodRight
    (m := encodedControlSuffixWidth control) program
  let controlled := UnitaryCircuit.controlLeading withSuffix
  let withPrefix := UnitaryCircuit.prodRight
    (m := encodedControlPrefixWidth control) controlled
  UnitaryCircuit.reindex (encodedControlReindexEquiv control n) withPrefix

/-- If the body uses only its canonical local wires, the positioned control
and shifted body use only the canonical combined prefix/body register. -/
theorem controlAtEncodedBit_physical_idx_subset_range {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    {n : Nat} (program : UnitaryCircuit (Qubits n))
    (hprogram : program.physical_idx ⊆ List.range n) :
    (controlAtEncodedBit control program).physical_idx ⊆
      List.range (encoding.width + n) := by
  intro index hindex
  simp only [controlAtEncodedBit, UnitaryCircuit.prodRight, UnitaryCircuit.controlLeading,
    UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex, UnitaryCircuit.tensor,
    UnitaryCircuit.shiftPhysicalIdx_physical_idx, UnitaryCircuit.controlQubitsAt,
    UnitaryCircuit.controlAt, UnitaryCircuit.identity,
    PhysicalLayout.DisjointMerge.merged_eq_append,
    List.nil_append, List.mem_map, List.mem_append, List.mem_singleton] at hindex
  rcases hindex with ⟨source, hsource, rfl⟩
  rcases hsource with rfl | hsource
  · rw [List.mem_range]
    have hwire := control.wire.isLt
    change encodedControlPrefixWidth control < encoding.width + n
    unfold encodedControlPrefixWidth
    omega
  · obtain ⟨bodyIndex, hbody, rfl⟩ := hsource
    obtain ⟨localIndex, hlocal, rfl⟩ := hbody
    have hlocalBound := List.mem_range.mp (hprogram hlocal)
    rw [List.mem_range]
    have hwidth := encodedControl_width_eq control
    omega

/-- Raw decomposed-basis endpoint of an addressed encoded-prefix control. -/
theorem controlAtEncodedBit_applyNormalized_parts_of_eq {Data Body : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    (bodyEncoding : BinaryLabelEncoding Body)
    (program : UnitaryCircuit (Qubits bodyEncoding.width))
    (input output : Body)
    (h : program.applyNormalized
        (NormalizedVector.ket (bodyEncoding.encode input)) =
      NormalizedVector.ket (bodyEncoding.encode output))
    (prefixValue : Fin (2 ^ encodedControlPrefixWidth control))
    (enabled : Bool)
    (suffix : Fin (2 ^ encodedControlSuffixWidth control)) :
    (controlAtEncodedBit control program).applyNormalized
        (NormalizedVector.ket
          (prodEquiv
            (encodedControlPartsEquiv control
              (prefixValue, BinaryLabelEncoding.bool.encode enabled, suffix),
            bodyEncoding.encode input))) =
      NormalizedVector.ket
        (prodEquiv
          (encodedControlPartsEquiv control
            (prefixValue, BinaryLabelEncoding.bool.encode enabled, suffix),
          bodyEncoding.encode (if enabled then output else input))) := by
  let suffixEncoding := BinaryLabelEncoding.finIdentity
    (encodedControlSuffixWidth control)
  let suffixBodyEncoding := BinaryLabelEncoding.prod suffixEncoding bodyEncoding
  have hbody : (UnitaryCircuit.prodRight
      (m := encodedControlSuffixWidth control) program).applyNormalized
        (NormalizedVector.ket
          (suffixBodyEncoding.encode (suffix, input))) =
      NormalizedVector.ket
        (suffixBodyEncoding.encode (suffix, output)) :=
    UnitaryCircuit.Realizes.prodRight_applyNormalized_encoded_ket_of_eq
      suffixEncoding bodyEncoding program suffix input output h
  have hcontrolled :
      (UnitaryCircuit.controlLeading
        (UnitaryCircuit.prodRight
          (m := encodedControlSuffixWidth control) program)).applyNormalized
          (NormalizedVector.ket
            ((BinaryLabelEncoding.prod BinaryLabelEncoding.bool
              suffixBodyEncoding).encode (enabled, suffix, input))) =
        NormalizedVector.ket
          ((BinaryLabelEncoding.prod BinaryLabelEncoding.bool
            suffixBodyEncoding).encode
            (enabled, suffix, if enabled then output else input)) := by
    cases enabled with
    | false =>
        exact UnitaryCircuit.controlLeading_applyNormalized_encoded_false
          suffixBodyEncoding
          (UnitaryCircuit.prodRight
            (m := encodedControlSuffixWidth control) program)
          (suffix, input)
    | true =>
        exact UnitaryCircuit.controlLeading_applyNormalized_encoded_true_of_eq
          suffixBodyEncoding
          (UnitaryCircuit.prodRight
            (m := encodedControlSuffixWidth control) program) hbody
  let controlledEncoding := BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    suffixBodyEncoding
  have hprefix :=
    UnitaryCircuit.Realizes.prodRight_applyNormalized_encoded_ket_of_eq
      (BinaryLabelEncoding.finIdentity (encodedControlPrefixWidth control))
      controlledEncoding
      (UnitaryCircuit.controlLeading
        (UnitaryCircuit.prodRight
          (m := encodedControlSuffixWidth control) program))
      prefixValue (enabled, suffix, input)
      (enabled, suffix, if enabled then output else input) hcontrolled
  have hreindexed :=
    UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (encodedControlPrefixWidth control +
        (1 + (encodedControlSuffixWidth control + bodyEncoding.width))))
      (S := Qubits (encoding.width + bodyEncoding.width))
      (encodedControlReindexEquiv control bodyEncoding.width)
      (UnitaryCircuit.prodRight (m := encodedControlPrefixWidth control)
        (UnitaryCircuit.controlLeading
          (UnitaryCircuit.prodRight
            (m := encodedControlSuffixWidth control) program)))
      (prodEquiv (prefixValue,
        prodEquiv (BinaryLabelEncoding.bool.encode enabled,
          prodEquiv (suffix, bodyEncoding.encode input))))
      (prodEquiv (prefixValue,
        prodEquiv (BinaryLabelEncoding.bool.encode enabled,
          prodEquiv (suffix,
            bodyEncoding.encode (if enabled then output else input)))))
      hprefix
  rw [encodedControlReindexEquiv_apply control prefixValue
      (BinaryLabelEncoding.bool.encode enabled) suffix
      (bodyEncoding.encode input),
    encodedControlReindexEquiv_apply control prefixValue
      (BinaryLabelEncoding.bool.encode enabled) suffix
      (bodyEncoding.encode (if enabled then output else input))] at hreindexed
  simpa only [controlAtEncodedBit] using hreindexed

/-- Semantic endpoint of an actual body controlled by any bit exposed by a
faithful encoded prefix. -/
theorem controlAtEncodedBit_applyNormalized_of_eq {Data Body : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    (bodyEncoding : BinaryLabelEncoding Body)
    (program : UnitaryCircuit (Qubits bodyEncoding.width))
    (input output : Body)
    (h : program.applyNormalized
        (NormalizedVector.ket (bodyEncoding.encode input)) =
      NormalizedVector.ket (bodyEncoding.encode output))
    (controlValue : Data) :
    (controlAtEncodedBit control program).applyNormalized
        (NormalizedVector.ket
          ((BinaryLabelEncoding.prod encoding bodyEncoding).encode
            (controlValue, input))) =
      NormalizedVector.ket
        ((BinaryLabelEncoding.prod encoding bodyEncoding).encode
          (controlValue, if control.get controlValue then output else input)) := by
  let parts := (encodedControlPartsEquiv control).symm
    (encoding.encode controlValue)
  rcases hparts : parts with ⟨prefixValue, enabled, suffix⟩
  have hpacked :
      encodedControlPartsEquiv control (prefixValue, enabled, suffix) =
        encoding.encode controlValue := by
    rw [← hparts]
    exact (encodedControlPartsEquiv control).apply_symm_apply _
  have hread := congrArg Bool.toNat (control.get_eq controlValue)
  have henabledVal : enabled.val = (control.get controlValue).toNat := by
    rw [← hpacked] at hread
    rw [encodedControlPartsEquiv_testBit] at hread
    exact hread
  have henabled :
      enabled = BinaryLabelEncoding.bool.encode (control.get controlValue) := by
    apply Fin.ext
    cases hget : control.get controlValue
    · rw [hget] at henabledVal
      simp only [BinaryLabelEncoding.bool, Fin.isValue] at henabledVal ⊢
      exact henabledVal
    · rw [hget] at henabledVal
      simp only [BinaryLabelEncoding.bool, Fin.isValue] at henabledVal ⊢
      exact henabledVal
  have hstage := controlAtEncodedBit_applyNormalized_parts_of_eq
    control bodyEncoding program input output h
    prefixValue (control.get controlValue) suffix
  change
    (controlAtEncodedBit control program).applyNormalized
        (NormalizedVector.ket
          (prodEquiv (encoding.encode controlValue, bodyEncoding.encode input))) =
      NormalizedVector.ket
        (prodEquiv (encoding.encode controlValue,
          bodyEncoding.encode
            (if control.get controlValue then output else input)))
  rw [← hpacked, henabled]
  exact hstage

/-- Raw body-label form of `controlAtEncodedBit_applyNormalized_of_eq`.
Keeping the body width symbolic avoids unfolding very large structured
encodings at fixed-width circuit clients. -/
theorem controlAtEncodedBit_applyNormalized_ket_of_eq {Data : Type}
    {encoding : BinaryLabelEncoding Data} (control : EncodedBit encoding)
    {n : Nat} (program : UnitaryCircuit (Qubits n))
    (input output : Fin (2 ^ n))
    (h : program.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output)
    (controlValue : Data) :
    (controlAtEncodedBit control program).applyNormalized
        (NormalizedVector.ket
          (prodEquiv (encoding.encode controlValue, input))) =
      NormalizedVector.ket
        (prodEquiv (encoding.encode controlValue,
          if control.get controlValue then output else input)) := by
  convert
    (controlAtEncodedBit_applyNormalized_of_eq
      control (BinaryLabelEncoding.finIdentity n) program input output h
      controlValue) using 1 <;>
    simp only [BinaryLabelEncoding.prod_encode,
      BinaryLabelEncoding.finIdentity_width,
      BinaryLabelEncoding.finIdentity_encode]

end UnitaryCircuit

namespace UnitaryCircuit.Realizes

/-- Add a leading Boolean control to an actual encoded circuit.  The body is
executed exactly on the `true` branch and the complete state is unchanged on
the `false` branch. -/
theorem controlOnTrue {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    {program : UnitaryCircuit (Qubits encoding.width)} {step : Data → Data}
    (h : UnitaryCircuit.Realizes encoding program step)
    (controlSystemIdx : List Nat)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx program.physical_idx) :
    UnitaryCircuit.Realizes
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool encoding)
      (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout (1 : Fin 2))
      (fun state : Bool × Data =>
        if state.1 then (true, step state.2) else state) where
  apply_encoded_ket := by
    rintro ⟨control, data⟩
    cases control with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        change
          (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout
            (1 : Fin 2)).applyNormalized
              (NormalizedVector.ket
                (prodEquiv ((0 : Fin 2), encoding.encode data)) :
                NormalizedVector (Qubits (1 + encoding.width))) =
            (NormalizedVector.ket
              (prodEquiv ((0 : Fin 2), encoding.encode data)) :
              NormalizedVector (Qubits (1 + encoding.width)))
        apply NormalizedVector.ext
        intro index
        have hcontrol :=
          UnitaryOperator.controlledQubits_applyVec_ket0_tensor
            program.matrix
            ((NormalizedVector.ket (encoding.encode data) :
              NormalizedVector (Qubits encoding.width)) :
                HilbertVector (Qubits encoding.width))
        have hproductNormalized :=
          NormalizedVector.tensor_ket
            (m := 1) (n := encoding.width)
            (0 : Fin 2) (encoding.encode data)
        have hproduct := congrArg
          (fun state : NormalizedVector (Qubits (1 + encoding.width)) =>
            (state : HilbertVector (Qubits (1 + encoding.width))))
          hproductNormalized
        change
          (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout (1 : Fin 2)).applyVec
              (NormalizedVector.ket
                (prodEquiv ((0 : Fin 2), encoding.encode data)) :
                NormalizedVector (Qubits (1 + encoding.width))) index =
            (NormalizedVector.ket
              (prodEquiv ((0 : Fin 2), encoding.encode data)) :
              NormalizedVector (Qubits (1 + encoding.width))) index
        rw [UnitaryCircuit.applyVec, UnitaryCircuit.controlQubitsAt_matrix]
        change
          (UnitaryOperator.controlledQubits program.matrix).applyVec
              (NormalizedVector.ket
                (prodEquiv ((0 : Fin 2), encoding.encode data)) :
                NormalizedVector (Qubits (1 + encoding.width))) index = _
        rw [← hproduct]
        exact congrArg
          (fun state : HilbertVector (Qubits (1 + encoding.width)) =>
            state index) hcontrol
    | true =>
        simp only [↓reduceIte]
        change
          (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout
            (1 : Fin 2)).applyNormalized
              (NormalizedVector.ket
                (prodEquiv ((1 : Fin 2), encoding.encode data)) :
                NormalizedVector (Qubits (1 + encoding.width))) =
            (NormalizedVector.ket
              (prodEquiv ((1 : Fin 2), encoding.encode (step data))) :
              NormalizedVector (Qubits (1 + encoding.width)))
        apply NormalizedVector.ext
        intro index
        have hcontrol :=
          UnitaryOperator.controlledQubits_applyVec_ket1_tensor
            program.matrix
            ((NormalizedVector.ket (encoding.encode data) :
              NormalizedVector (Qubits encoding.width)) :
                HilbertVector (Qubits encoding.width))
        have hbody := h.apply_encoded_ket data
        have hbodyCoe := congrArg
          (fun state : NormalizedVector (Qubits encoding.width) =>
            (state : HilbertVector (Qubits encoding.width))) hbody
        have hinputNormalized :=
          NormalizedVector.tensor_ket
            (m := 1) (n := encoding.width)
            (1 : Fin 2) (encoding.encode data)
        have hinput := congrArg
          (fun state : NormalizedVector (Qubits (1 + encoding.width)) =>
            (state : HilbertVector (Qubits (1 + encoding.width))))
          hinputNormalized
        have houtputNormalized :=
          NormalizedVector.tensor_ket
            (m := 1) (n := encoding.width)
            (1 : Fin 2) (encoding.encode (step data))
        have houtput := congrArg
          (fun state : NormalizedVector (Qubits (1 + encoding.width)) =>
            (state : HilbertVector (Qubits (1 + encoding.width))))
          houtputNormalized
        change
          (UnitaryCircuit.controlQubitsAt controlSystemIdx program layout (1 : Fin 2)).applyVec
              (NormalizedVector.ket
                (prodEquiv ((1 : Fin 2), encoding.encode data)) :
                NormalizedVector (Qubits (1 + encoding.width))) index =
            (NormalizedVector.ket
              (prodEquiv ((1 : Fin 2), encoding.encode (step data))) :
              NormalizedVector (Qubits (1 + encoding.width))) index
        rw [UnitaryCircuit.applyVec, UnitaryCircuit.controlQubitsAt_matrix]
        change
          (UnitaryOperator.controlledQubits program.matrix).applyVec
              (NormalizedVector.ket
                (prodEquiv ((1 : Fin 2), encoding.encode data)) :
                NormalizedVector (Qubits (1 + encoding.width))) index = _
        rw [← hinput]
        have htotal :
            (UnitaryOperator.controlledQubits program.matrix).applyVec
                (HilbertVector.tensor
                  ((NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) :
                    NormalizedVector (Qubits 1)) : HilbertVector (Qubits 1))
                  ((NormalizedVector.ket (encoding.encode data) :
                    NormalizedVector (Qubits encoding.width)) :
                      HilbertVector (Qubits encoding.width))) =
              (NormalizedVector.ket
                (prodEquiv ((1 : Fin 2), encoding.encode (step data))) :
                NormalizedVector (Qubits (1 + encoding.width))) := by
          calc
            _ = HilbertVector.tensor
                  ((NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) :
                    NormalizedVector (Qubits 1)) : HilbertVector (Qubits 1))
                  (program.matrix.applyVec
                    (NormalizedVector.ket (encoding.encode data) :
                      NormalizedVector (Qubits encoding.width))) := hcontrol
            _ = HilbertVector.tensor
                  ((NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) :
                    NormalizedVector (Qubits 1)) : HilbertVector (Qubits 1))
                  (NormalizedVector.ket (encoding.encode (step data)) :
                    NormalizedVector (Qubits encoding.width)) := by
              exact congrArg
                (fun state : HilbertVector (Qubits encoding.width) =>
                  HilbertVector.tensor
                    ((NormalizedVector.ket (R := Qubits 1) (1 : Fin 2) :
                      NormalizedVector (Qubits 1)) : HilbertVector (Qubits 1))
                    state) hbodyCoe
            _ = _ := houtput
        exact congrArg
          (fun state : HilbertVector (Qubits (1 + encoding.width)) =>
            state index) htotal

end UnitaryCircuit.Realizes

end

end QuantumAlg

end
