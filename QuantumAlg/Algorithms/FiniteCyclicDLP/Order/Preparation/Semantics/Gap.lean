/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Intrinsic
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Blocks
public import QuantumAlg.Components.Gates.Hadamard.Action
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Separated.Wire
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Intrinsic
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Blocks
import all QuantumAlg.Components.Gates.Hadamard.Action
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Separated.Wire
import all QuantumAlg.Primitives.WalshHadamard.Mathematics

/-!
# Native semantics inside one positive binary gap

The right-to-left Hadamard sweep carries an explicit raw-vector invariant.
Its factors follow physical big-endian order, so the same vector is consumed
by the literal separated-wire gates in `OrderPreparation.Intrinsic`.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion

noncomputable section

variable {N : Nat}

/-- Physical intrinsic wire carrying one set-bit exponent. -/
@[expose] public def wire (b : PositiveGapExpansion N) (source : Fin (b.gaps + 1)) :
    Fin b.width :=
  WireAddress.littleEndianWire ⟨b.ell source, b.ell_lt_width source⟩

@[simp] public theorem wire_val (b : PositiveGapExpansion N)
    (source : Fin (b.gaps + 1)) :
    (b.wire source).val = b.width - 1 - b.ell source := rfl

/-- The physical source address recovers its logical set-bit exponent. -/
public theorem bitIndex_wire (b : PositiveGapExpansion N)
    (source : Fin (b.gaps + 1)) :
    (WireAddress.bitIndex (b.wire source)).val = b.ell source := by
  exact congrArg Fin.val (WireAddress.bitIndex_littleEndianWire _)

/-- Physical target wire at one increasing logical offset inside a gap. -/
@[expose] public def gapTargetWire (b : PositiveGapExpansion N) (gap : Fin b.gaps)
    (offset : Fin (b.gapWidth gap)) : Fin b.width :=
  WireAddress.littleEndianWire
    ⟨b.ell gap.castSucc + offset.val, by
      have strict := b.ell_strict gap.castSucc_lt_succ
      have offsetBound := offset.isLt
      have upper := b.ell_lt_width gap.succ
      unfold gapWidth at offsetBound
      omega⟩

@[simp] public theorem gapTargetWire_val (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) (offset : Fin (b.gapWidth gap)) :
    (b.gapTargetWire gap offset).val =
      b.width - 1 - (b.ell gap.castSucc + offset.val) := rfl

/-- The next source wire is physically before the preceding source wire. -/
public theorem wire_succ_lt_wire (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) :
    (b.wire gap.succ).val < (b.wire gap.castSucc).val := by
  rw [wire_val, wire_val]
  have strict := b.ell_strict gap.castSucc_lt_succ
  have upper := b.ell_lt_width gap.succ
  omega

/-- The next source wire is physically before every Hadamard target in its
strict binary gap. -/
public theorem wire_succ_lt_gapTargetWire (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) (offset : Fin (b.gapWidth gap)) :
    (b.wire gap.succ).val < (b.gapTargetWire gap offset).val := by
  rw [wire_val, gapTargetWire_val]
  have strict := b.ell_strict gap.castSucc_lt_succ
  have upper := b.ell_lt_width gap.succ
  have offsetBound := offset.isLt
  unfold gapWidth at offsetBound
  omega

/-- Width of the fixed high prefix at a source position. -/
public theorem highWidth_eq_wire_val (b : PositiveGapExpansion N)
    (source : Fin (b.gaps + 1)) :
    b.width - b.ell source - 1 = (b.wire source).val := by
  rw [wire_val]
  have upper := b.ell_lt_width source
  omega

/-- Width of the physical suffix below a source position. -/
public theorem ell_eq_wire_suffixWidth (b : PositiveGapExpansion N)
    (source : Fin (b.gaps + 1)) :
    b.ell source = b.width - (b.wire source).val - 1 := by
  rw [wire_val]
  have upper := b.ell_lt_width source
  omega

/-- Width of the strict gap interior between its two source wires. -/
public theorem gapWidth_pred_eq_wire_sub (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) :
    b.gapWidth gap - 1 =
      (b.wire gap.castSucc).val - (b.wire gap.succ).val - 1 := by
  rw [wire_val, wire_val]
  have strict := b.ell_strict gap.castSucc_lt_succ
  have upper := b.ell_lt_width gap.succ
  unfold gapWidth
  omega

/-- Width of the still-zero middle field at one gap target. -/
public theorem gapRemaining_eq_target_sub (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) (offset : Fin (b.gapWidth gap)) :
    b.gapWidth gap - offset.val - 1 =
      (b.gapTargetWire gap offset).val - (b.wire gap.succ).val - 1 := by
  rw [wire_val, gapTargetWire_val]
  have strict := b.ell_strict gap.castSucc_lt_succ
  have upper := b.ell_lt_width gap.succ
  have offsetBound := offset.isLt
  unfold gapWidth at offsetBound ⊢
  omega

/-- Width of the already-expanded physical suffix at one gap target. -/
public theorem gapProcessed_eq_target_suffixWidth
    (b : PositiveGapExpansion N) (gap : Fin b.gaps)
    (offset : Fin (b.gapWidth gap)) :
    offset.val + b.ell gap.castSucc =
      b.width - (b.gapTargetWire gap offset).val - 1 := by
  rw [gapTargetWire_val]
  have strict := b.ell_strict gap.castSucc_lt_succ
  have upper := b.ell_lt_width gap.succ
  have offsetBound := offset.isLt
  unfold gapWidth at offsetBound
  omega

/-- Raw all-zero computational state at a fixed width. -/
@[expose] public def rawKetZero (width : Nat) : HilbertVector (Qubits width) :=
  basisKetVec (0 : Fin (2 ^ width))

private theorem prodEquiv_value {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) :
    (prodEquiv (m := leftWidth) (n := rightWidth) (left, right)).val =
      right.val + 2 ^ rightWidth * left.val := rfl

/-- The explicit product of already-created `|+>` gap factors. -/
public def gapPlusBlock : (count : Nat) → HilbertVector (Qubits count)
  | 0 => rawKetZero 0
  | count + 1 =>
      UnitaryCircuit.castQubitWidthVec (by omega : 1 + count = count + 1)
        (HilbertVector.tensor (NormalizedVector.ketPlus : HilbertVector (Qubits 1))
          (gapPlusBlock count))

/-- A leading `|+>` extends the raw Walsh-uniform block by one physical
qubit. -/
public theorem ketPlus_tensor_uniform (count : Nat) :
    HilbertVector.tensor (NormalizedVector.ketPlus : HilbertVector (Qubits 1))
        (WalshHadamard.uniformState count : HilbertVector (Qubits count)) =
      (WalshHadamard.uniformState (1 + count) :
        HilbertVector (Qubits (1 + count))) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := 1) (n := count)).surjective index with
    ⟨⟨left, right⟩, rfl⟩
  simp only [HilbertVector.tensor_apply_prod, NormalizedVector.ketPlus_apply,
    WalshHadamard.uniformState_apply]
  rw [show 1 + count = count + 1 by omega,
    WalshHadamard.invSqrtCard_succ]
  ring

/-- The explicit product of `|+>` factors is the ordinary raw
Walsh-uniform state of the same width. -/
public theorem gapPlusBlock_eq_uniform (count : Nat) :
    gapPlusBlock count =
      (WalshHadamard.uniformState count : HilbertVector (Qubits count)) := by
  induction count with
  | zero =>
      apply WithLp.ofLp_injective
      funext index
      fin_cases index
      simp [gapPlusBlock, rawKetZero, basisKetVec,
        WalshHadamard.uniformState_apply, WalshHadamard.invSqrtCard]
  | succ count induction =>
      rw [gapPlusBlock, induction, ketPlus_tensor_uniform]
      apply WithLp.ofLp_injective
      funext index
      rw [UnitaryCircuit.castQubitWidthVec_apply]
      simp only [WalshHadamard.uniformState_apply]
      simp [show 1 + count = count + 1 by omega]

/-- In the fixed high prefix of the current residual, the next source bit is
one and every strict intermediate gap bit is zero. -/
public theorem residualHighLabel_gap_factor (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) :
    b.residualHighLabel gap.castSucc =
      UnitaryCircuit.castQubitWidthIndex (by
        have strict := b.ell_strict gap.castSucc_lt_succ
        have upper := b.ell_lt_width gap.succ
        unfold gapWidth
        omega :
          (b.width - b.ell gap.succ - 1) + b.gapWidth gap =
            b.width - b.ell gap.castSucc - 1)
        (prodEquiv (m := b.width - b.ell gap.succ - 1)
          (n := b.gapWidth gap)
          (b.residualHighLabel gap.succ,
            UnitaryCircuit.castQubitWidthIndex (by
              have strict := b.ell_strict gap.castSucc_lt_succ
              unfold gapWidth
              omega : 1 + (b.gapWidth gap - 1) = b.gapWidth gap)
              (prodEquiv (m := 1) (n := b.gapWidth gap - 1) (1, 0)))) := by
  have strict := b.ell_strict gap.castSucc_lt_succ
  have upper := b.ell_lt_width gap.succ
  have gapPositive : 0 < b.gapWidth gap := by
    unfold gapWidth
    omega
  have ellStep : b.ell gap.succ = b.ell gap.castSucc + b.gapWidth gap := by
    unfold gapWidth
    omega
  have tailStep := b.tailMass_eq_pow_add_tailMass_succ gap
  have nextFactor := b.tailMass_eq_residualHigh_mul gap.succ
  have tailFactor : b.tailMass gap.castSucc =
      2 ^ (b.ell gap.castSucc + 1) *
        (2 ^ b.gapWidth gap * b.residualHigh gap.succ +
          2 ^ (b.gapWidth gap - 1)) := by
    have currentPower :
        2 ^ b.ell gap.succ =
          2 ^ (b.ell gap.castSucc + 1) *
            2 ^ (b.gapWidth gap - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have nextPower :
        2 ^ (b.ell gap.succ + 1) =
          2 ^ (b.ell gap.castSucc + 1) * 2 ^ b.gapWidth gap := by
      rw [← pow_add]
      congr 1
      omega
    rw [tailStep, nextFactor, currentPower, nextPower]
    ring
  have quotient : b.residualHigh gap.castSucc =
      2 ^ b.gapWidth gap * b.residualHigh gap.succ +
        2 ^ (b.gapWidth gap - 1) := by
    change b.tailMass gap.castSucc / 2 ^ (b.ell gap.castSucc + 1) = _
    rw [tailFactor, Nat.mul_div_right _ (Nat.two_pow_pos _)]
  apply Fin.ext
  simp only [residualHighLabel_val,
    UnitaryCircuit.castQubitWidthIndex_val, prodEquiv_value]
  simpa [Nat.add_comm] using quotient

@[simp] public theorem castQubitWidthVec_basisKet
    {source target : Nat} (same : source = target)
    (index : Fin (2 ^ source)) :
    UnitaryCircuit.castQubitWidthVec same (basisKetVec index) =
      basisKetVec (UnitaryCircuit.castQubitWidthIndex same index) := by
  subst target
  rfl

/-- Tensoring two raw basis kets forms their big-endian product label. -/
public theorem tensor_basisKet {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) :
    HilbertVector.tensor (basisKetVec left) (basisKetVec right) =
      basisKetVec (prodEquiv (m := leftWidth) (n := rightWidth) (left, right)) := by
  simpa [basisKetVec] using congrArg
    (fun state : NormalizedVector (Qubits (leftWidth + rightWidth)) =>
      (state : HilbertVector (Qubits (leftWidth + rightWidth))))
    (NormalizedVector.tensor_ket left right)

/-- A tensor of two all-zero raw registers is the all-zero register of their
combined width. -/
public theorem tensor_rawKetZero (leftWidth rightWidth : Nat) :
    HilbertVector.tensor (rawKetZero leftWidth) (rawKetZero rightWidth) =
      rawKetZero (leftWidth + rightWidth) := by
  unfold rawKetZero
  rw [tensor_basisKet]
  congr 1

/-- A zero-width all-zero prefix is a tensor identity on raw vectors. -/
public theorem rawKetZero_zero_tensor_left {width : Nat}
    (state : HilbertVector (Qubits width)) :
    UnitaryCircuit.castQubitWidthVec (Nat.zero_add width)
        (HilbertVector.tensor (rawKetZero 0) state) = state := by
  apply WithLp.ofLp_injective
  funext index
  rw [UnitaryCircuit.castQubitWidthVec_apply]
  have indexSame :
      UnitaryCircuit.castQubitWidthIndex (Nat.zero_add width).symm index =
        prodEquiv (m := 0) (n := width) (0, index) := by
    apply Fin.ext
    rw [UnitaryCircuit.castQubitWidthIndex_val]
    symm
    simpa using
      (prodEquiv_value (0 : Fin (2 ^ 0)) index)
  rw [indexSame, HilbertVector.tensor_apply_prod]
  simp [rawKetZero, basisKetVec, NormalizedVector.ket_apply]

private theorem rawKetZero_tensor_left_of_eq_zero {left width : Nat}
    (empty : left = 0) (state : HilbertVector (Qubits width)) :
    UnitaryCircuit.castQubitWidthVec (by omega : left + width = width)
        (HilbertVector.tensor (rawKetZero left) state) = state := by
  subst left
  simpa using rawKetZero_zero_tensor_left state

/-- A positive-width all-zero register splits into its leading block and one
final zero qubit. -/
public theorem rawKetZero_split_last (width : Nat) (positive : 0 < width) :
    UnitaryCircuit.castQubitWidthVec (by omega : (width - 1) + 1 = width)
        (HilbertVector.tensor (rawKetZero (width - 1))
          (NormalizedVector.ket0 : HilbertVector (Qubits 1))) =
      rawKetZero width := by
  change UnitaryCircuit.castQubitWidthVec _
      (HilbertVector.tensor (basisKetVec (0 : Fin (2 ^ (width - 1))))
        (basisKetVec (0 : Fin (2 ^ 1)))) =
    basisKetVec (0 : Fin (2 ^ width))
  rw [tensor_basisKet, castQubitWidthVec_basisKet]
  congr 1

/-- The current residual block split at the next source bit.  The factors are
in physical order: fixed high prefix, next source one, strict zero gap,
current source zero, and the old low Walsh block. -/
public theorem residualBlock_gap_rotation_tensor (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) :
    b.residualBlock gap.castSucc =
      UnitaryCircuit.castQubitWidthVec (by
        have strict := b.ell_strict gap.castSucc_lt_succ
        have upper := b.ell_lt_width gap.succ
        unfold gapWidth
        omega :
          ((b.width - b.ell gap.succ - 1) +
              (1 + (b.gapWidth gap - 1))) +
              (1 + b.ell gap.castSucc) = b.width)
        (HilbertVector.tensor
          (HilbertVector.tensor
            (basisKetVec (b.residualHighLabel gap.succ))
            (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1))
              (rawKetZero (b.gapWidth gap - 1))))
          (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
            (WalshHadamard.uniformState (b.ell gap.castSucc) :
              HilbertVector (Qubits (b.ell gap.castSucc))))) := by
  have strict := b.ell_strict gap.castSucc_lt_succ
  have upper := b.ell_lt_width gap.succ
  have innerWidth : 1 + (b.gapWidth gap - 1) = b.gapWidth gap := by
    unfold gapWidth
    omega
  have highWidth :
      (b.width - b.ell gap.succ - 1) + b.gapWidth gap =
        b.width - b.ell gap.castSucc - 1 := by
    unfold gapWidth
    omega
  have outerWidth :
      (b.width - b.ell gap.castSucc - 1) +
          (1 + b.ell gap.castSucc) = b.width := by
    omega
  have combinedWidth :
      ((b.width - b.ell gap.succ - 1) + b.gapWidth gap) +
          (1 + b.ell gap.castSucc) = b.width := by
    rw [highWidth]
    exact outerWidth
  have highInnerWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + (b.gapWidth gap - 1)) =
        (b.width - b.ell gap.succ - 1) + b.gapWidth gap := by
    rw [innerWidth]
  have highLabel :
      basisKetVec (b.residualHighLabel gap.castSucc) =
        UnitaryCircuit.castQubitWidthVec highWidth
          (HilbertVector.tensor
            (basisKetVec (b.residualHighLabel gap.succ))
            (UnitaryCircuit.castQubitWidthVec innerWidth
              (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1))
                (rawKetZero (b.gapWidth gap - 1))))) := by
    rw [b.residualHighLabel_gap_factor]
    rw [← castQubitWidthVec_basisKet]
    congr 1
    rw [← tensor_basisKet]
    congr 1
    rw [← castQubitWidthVec_basisKet, ← tensor_basisKet]
    simp [rawKetZero, basisKetVec, NormalizedVector.ket1]
  rw [b.residualBlock_tensor_factor gap.castSucc, highLabel]
  rw [UnitaryCircuit.castQubitWidthVec_tensor_left highWidth outerWidth]
  have innerTensor :
      HilbertVector.tensor
          (basisKetVec (b.residualHighLabel gap.succ))
          (UnitaryCircuit.castQubitWidthVec innerWidth
            (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1))
              (rawKetZero (b.gapWidth gap - 1)))) =
        UnitaryCircuit.castQubitWidthVec highInnerWidth
          (HilbertVector.tensor
            (basisKetVec (b.residualHighLabel gap.succ))
            (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1))
              (rawKetZero (b.gapWidth gap - 1)))) := by
    simpa using
      (UnitaryCircuit.castQubitWidthVec_tensor_right innerWidth rfl
        (basisKetVec (b.residualHighLabel gap.succ))
        (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1))
          (rawKetZero (b.gapWidth gap - 1))))
  rw [innerTensor]
  rw [UnitaryCircuit.castQubitWidthVec_tensor_left highInnerWidth combinedWidth]

/-- The current residual in the exact physical orientation of the
right-controlled source rotation. -/
public theorem residualBlock_eq_rotationSeparated (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) :
    b.residualBlock gap.castSucc =
      UnitaryCircuit.binarySeparatedVec (b.wire gap.succ) (b.wire gap.castSucc)
        (b.wire_succ_lt_wire gap)
        (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1))
          (NormalizedVector.ket0 : HilbertVector (Qubits 1)))
        (UnitaryCircuit.castQubitWidthVec (b.gapWidth_pred_eq_wire_sub gap)
          (rawKetZero (b.gapWidth gap - 1)))
        (UnitaryCircuit.castQubitWidthVec
          (b.ell_eq_wire_suffixWidth gap.castSucc)
          (WalshHadamard.uniformState (b.ell gap.castSucc) :
            HilbertVector (Qubits (b.ell gap.castSucc)))) := by
  let high := basisKetVec (b.residualHighLabel gap.succ)
  let middle := rawKetZero (b.gapWidth gap - 1)
  let suffix :=
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have canonicalWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) = b.width := by
    have strict := b.ell_strict gap.castSucc_lt_succ
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth
    omega
  have leftWidth :
      ((b.width - b.ell gap.succ - 1) +
          (1 + (b.gapWidth gap - 1))) +
          (1 + b.ell gap.castSucc) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by omega
  have rightWidth :
      ((b.width - b.ell gap.succ - 1) +
          ((1 + (b.gapWidth gap - 1)) + 1)) +
          b.ell gap.castSucc =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by omega
  calc
    b.residualBlock gap.castSucc =
        UnitaryCircuit.castQubitWidthVec (by
          have strict := b.ell_strict gap.castSucc_lt_succ
          have upper := b.ell_lt_width gap.succ
          unfold gapWidth
          omega :
            ((b.width - b.ell gap.succ - 1) +
                (1 + (b.gapWidth gap - 1))) +
                (1 + b.ell gap.castSucc) = b.width)
          (HilbertVector.tensor
            (HilbertVector.tensor high
              (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1)) middle))
            (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix)) := by
          simpa [high, middle, suffix] using b.residualBlock_gap_rotation_tensor gap
    _ = UnitaryCircuit.castQubitWidthVec canonicalWidth
          (UnitaryCircuit.castQubitWidthVec leftWidth
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1)) middle))
              (HilbertVector.tensor
                (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix))) := by
          symm
          simpa using UnitaryCircuit.castQubitWidthVec_trans
            leftWidth canonicalWidth
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1)) middle))
              (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix))
    _ = UnitaryCircuit.castQubitWidthVec canonicalWidth
          (UnitaryCircuit.castQubitWidthVec rightWidth
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor
                  (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1)) middle)
                  (NormalizedVector.ket0 : HilbertVector (Qubits 1))))
              suffix)) := by
          congr 1
          exact UnitaryCircuit.castQubitWidthVec_tensor_rebracket5
            high (NormalizedVector.ket1 : HilbertVector (Qubits 1)) middle
              (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix
    _ = UnitaryCircuit.binarySeparatedVec
          (b.wire gap.succ) (b.wire gap.castSucc)
          (b.wire_succ_lt_wire gap)
          (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ) high)
          (HilbertVector.tensor (NormalizedVector.ket1 : HilbertVector (Qubits 1))
            (NormalizedVector.ket0 : HilbertVector (Qubits 1)))
          (UnitaryCircuit.castQubitWidthVec (b.gapWidth_pred_eq_wire_sub gap) middle)
          (UnitaryCircuit.castQubitWidthVec
            (b.ell_eq_wire_suffixWidth gap.castSucc) suffix) := by
          rw [UnitaryCircuit.castQubitWidthVec_trans]
          symm
          simpa using
            (UnitaryCircuit.binarySeparatedVec_tensor_transport
              (b.wire gap.succ) (b.wire gap.castSucc)
              (b.wire_succ_lt_wire gap)
              (b.highWidth_eq_wire_val gap.succ)
              (b.gapWidth_pred_eq_wire_sub gap)
              (b.ell_eq_wire_suffixWidth gap.castSucc)
              high (NormalizedVector.ket1 : HilbertVector (Qubits 1)) middle
              (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix)

/-- Raw branch after `processed` Hadamards of one binary gap. -/
public def gapHPartial (b : PositiveGapExpansion N) (gap : Fin b.gaps)
    (processed : Nat) (bounded : processed ≤ b.gapWidth gap) :
    HilbertVector (Qubits b.width) :=
  UnitaryCircuit.castQubitWidthVec (by
    have strict := b.ell_strict gap.castSucc_lt_succ
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth at bounded ⊢
    omega :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed) +
            (processed + b.ell gap.castSucc))) = b.width)
    (HilbertVector.tensor
      (basisKetVec (b.residualHighLabel gap.succ))
      (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
        (HilbertVector.tensor
          (rawKetZero (b.gapWidth gap - processed))
          (HilbertVector.tensor (gapPlusBlock processed)
            (WalshHadamard.uniformState (b.ell gap.castSucc) :
              HilbertVector (Qubits (b.ell gap.castSucc)))))))

/-- Before the next gap Hadamard, the current target is exposed as an
explicit zero qubit between the unprocessed and processed portions. -/
public theorem gapHPartial_canonical (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) (processed : Nat)
    (notFinished : processed < b.gapWidth gap) :
    b.gapHPartial gap processed (Nat.le_of_lt notFinished) =
      UnitaryCircuit.castQubitWidthVec (by
        have strict := b.ell_strict gap.castSucc_lt_succ
        have upper := b.ell_lt_width gap.succ
        unfold gapWidth at notFinished ⊢
        omega :
          (b.width - b.ell gap.succ - 1) +
            (1 + ((b.gapWidth gap - processed - 1) +
              (1 + (processed + b.ell gap.castSucc)))) = b.width)
        (HilbertVector.tensor
          (basisKetVec (b.residualHighLabel gap.succ))
          (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
            (HilbertVector.tensor
              (rawKetZero (b.gapWidth gap - processed - 1))
              (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
                (HilbertVector.tensor (gapPlusBlock processed)
                  (WalshHadamard.uniformState (b.ell gap.castSucc) :
                    HilbertVector (Qubits (b.ell gap.castSucc)))))))) := by
  let suffixState := HilbertVector.tensor (gapPlusBlock processed)
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have splitWidth :
      (b.gapWidth gap - processed - 1) + 1 =
        b.gapWidth gap - processed := by omega
  have zeroWidth :
      (b.gapWidth gap - processed) + (processed + b.ell gap.castSucc) =
        (b.gapWidth gap - processed - 1) +
          (1 + (processed + b.ell gap.castSucc)) := by omega
  have sourceWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed) +
            (processed + b.ell gap.castSucc))) = b.width := by
    have strict := b.ell_strict gap.castSucc_lt_succ
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth at notFinished ⊢
    omega
  have targetWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed - 1) +
            (1 + (processed + b.ell gap.castSucc)))) = b.width := by
    have strict := b.ell_strict gap.castSucc_lt_succ
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth at notFinished ⊢
    omega
  have zeroState :
      UnitaryCircuit.castQubitWidthVec zeroWidth
        (HilbertVector.tensor
          (rawKetZero (b.gapWidth gap - processed)) suffixState) =
        HilbertVector.tensor
          (rawKetZero (b.gapWidth gap - processed - 1))
          (HilbertVector.tensor
            (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffixState) := by
    rw [← rawKetZero_split_last (b.gapWidth gap - processed) (by omega)]
    rw [UnitaryCircuit.castQubitWidthVec_tensor_left splitWidth zeroWidth]
    simpa using
      (UnitaryCircuit.castQubitWidthVec_tensor_assoc
        (rawKetZero (b.gapWidth gap - processed - 1))
        (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffixState)
  unfold gapHPartial
  change UnitaryCircuit.castQubitWidthVec sourceWidth
      (HilbertVector.tensor
        (basisKetVec (b.residualHighLabel gap.succ))
        (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
          (HilbertVector.tensor
            (rawKetZero (b.gapWidth gap - processed)) suffixState))) = _
  rw [UnitaryCircuit.castQubitWidthVec_tensor_two_right
    zeroWidth sourceWidth targetWidth]
  rw [zeroState]

/-- A not-yet-finished partial gap state in the exact separated-wire shape
consumed by its next literal open-controlled Hadamard. -/
public theorem gapHPartial_eq_hSeparated (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) (processed : Nat)
    (notFinished : processed < b.gapWidth gap) :
    b.gapHPartial gap processed (Nat.le_of_lt notFinished) =
      UnitaryCircuit.binarySeparatedVec (b.wire gap.succ)
        (b.gapTargetWire gap ⟨processed, notFinished⟩)
        (b.wire_succ_lt_gapTargetWire gap ⟨processed, notFinished⟩)
        (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
          (NormalizedVector.ket0 : HilbertVector (Qubits 1)))
        (UnitaryCircuit.castQubitWidthVec
          (b.gapRemaining_eq_target_sub gap ⟨processed, notFinished⟩)
          (rawKetZero (b.gapWidth gap - processed - 1)))
        (UnitaryCircuit.castQubitWidthVec
          (b.gapProcessed_eq_target_suffixWidth gap
            ⟨processed, notFinished⟩)
          (HilbertVector.tensor (gapPlusBlock processed)
            (WalshHadamard.uniformState (b.ell gap.castSucc) :
              HilbertVector (Qubits (b.ell gap.castSucc))))) := by
  let high := basisKetVec (b.residualHighLabel gap.succ)
  let middle := rawKetZero (b.gapWidth gap - processed - 1)
  let suffixState := HilbertVector.tensor (gapPlusBlock processed)
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have canonicalWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed - 1) +
            (1 + (processed + b.ell gap.castSucc)))) = b.width := by
    have strict := b.ell_strict gap.castSucc_lt_succ
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth at notFinished ⊢
    omega
  have separatedWidth :
      ((b.width - b.ell gap.succ - 1) +
          ((1 + (b.gapWidth gap - processed - 1)) + 1)) +
          (processed + b.ell gap.castSucc) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed - 1) +
            (1 + (processed + b.ell gap.castSucc)))) := by omega
  calc
    b.gapHPartial gap processed (Nat.le_of_lt notFinished) =
        UnitaryCircuit.castQubitWidthVec canonicalWidth
          (HilbertVector.tensor high
            (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
              (HilbertVector.tensor middle
                (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
                  suffixState)))) := by
          simpa [high, middle, suffixState] using
            b.gapHPartial_canonical gap processed notFinished
    _ = UnitaryCircuit.castQubitWidthVec canonicalWidth
          (UnitaryCircuit.castQubitWidthVec separatedWidth
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor
                  (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle)
                  (NormalizedVector.ket0 : HilbertVector (Qubits 1))))
              suffixState)) := by
          congr 1
          exact UnitaryCircuit.castQubitWidthVec_tensor_right_to_separated5
            high (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle
              (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffixState
    _ = UnitaryCircuit.binarySeparatedVec (b.wire gap.succ)
          (b.gapTargetWire gap ⟨processed, notFinished⟩)
          (b.wire_succ_lt_gapTargetWire gap ⟨processed, notFinished⟩)
          (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ) high)
          (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
            (NormalizedVector.ket0 : HilbertVector (Qubits 1)))
          (UnitaryCircuit.castQubitWidthVec
            (b.gapRemaining_eq_target_sub gap ⟨processed, notFinished⟩) middle)
          (UnitaryCircuit.castQubitWidthVec
            (b.gapProcessed_eq_target_suffixWidth gap
              ⟨processed, notFinished⟩) suffixState) := by
          rw [UnitaryCircuit.castQubitWidthVec_trans]
          symm
          simpa using
            (UnitaryCircuit.binarySeparatedVec_tensor_transport
              (b.wire gap.succ)
              (b.gapTargetWire gap ⟨processed, notFinished⟩)
              (b.wire_succ_lt_gapTargetWire gap ⟨processed, notFinished⟩)
              (b.highWidth_eq_wire_val gap.succ)
              (b.gapRemaining_eq_target_sub gap ⟨processed, notFinished⟩)
              (b.gapProcessed_eq_target_suffixWidth gap
                ⟨processed, notFinished⟩)
              high (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle
              (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffixState)

/-- Offset zero in a logical gap is the physical wire of its lower source
endpoint. -/
public theorem gapTargetWire_zero (b : PositiveGapExpansion N)
    (gap : Fin b.gaps)
    (positive : 0 < b.gapWidth gap) :
    b.gapTargetWire gap ⟨0, positive⟩ = b.wire gap.castSucc := by
  apply Fin.ext
  simp only [gapTargetWire_val, wire_val]
  omega

/-- The newly opened zero branch of a source rotation has exactly the
separated-wire layout consumed by the following gap-H sweep. -/
public theorem gapHPartial_zero_eq_rotationSeparated
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    b.gapHPartial gap 0 (Nat.zero_le _) =
      UnitaryCircuit.binarySeparatedVec (b.wire gap.succ)
        (b.wire gap.castSucc) (b.wire_succ_lt_wire gap)
        (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
          (NormalizedVector.ket0 : HilbertVector (Qubits 1)))
        (UnitaryCircuit.castQubitWidthVec (b.gapWidth_pred_eq_wire_sub gap)
          (rawKetZero (b.gapWidth gap - 1)))
        (UnitaryCircuit.castQubitWidthVec
          (b.ell_eq_wire_suffixWidth gap.castSucc)
          (WalshHadamard.uniformState (b.ell gap.castSucc) :
            HilbertVector (Qubits (b.ell gap.castSucc)))) := by
  have sourceStrict : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have widthBound : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have positive : 0 < b.gapWidth gap := by
    have strict := b.ell_strict gap.castSucc_lt_succ
    unfold gapWidth
    omega
  let high := basisKetVec (b.residualHighLabel gap.succ)
  let middle := rawKetZero (b.gapWidth gap - 1)
  let suffix :=
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  let innerSource := HilbertVector.tensor
    (NormalizedVector.ket0 : HilbertVector (Qubits 1))
    (HilbertVector.tensor (gapPlusBlock 0) suffix)
  have innerWidth :
      1 + (0 + b.ell gap.castSucc) = 1 + b.ell gap.castSucc := by
    omega
  have zeroTail :
      UnitaryCircuit.castQubitWidthVec
          (Nat.zero_add (b.ell gap.castSucc))
          (HilbertVector.tensor (gapPlusBlock 0) suffix) = suffix := by
    change UnitaryCircuit.castQubitWidthVec
        (Nat.zero_add (b.ell gap.castSucc))
        (HilbertVector.tensor (rawKetZero 0) suffix) = suffix
    exact rawKetZero_zero_tensor_left suffix
  have innerState :
      UnitaryCircuit.castQubitWidthVec innerWidth innerSource =
        HilbertVector.tensor
          (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix := by
    unfold innerSource
    calc
      UnitaryCircuit.castQubitWidthVec
          innerWidth
          (HilbertVector.tensor
            (NormalizedVector.ket0 : HilbertVector (Qubits 1))
            (HilbertVector.tensor (gapPlusBlock 0) suffix)) =
          UnitaryCircuit.castQubitWidthVec rfl
            (HilbertVector.tensor
              (NormalizedVector.ket0 : HilbertVector (Qubits 1))
              (UnitaryCircuit.castQubitWidthVec
                (Nat.zero_add (b.ell gap.castSucc))
                (HilbertVector.tensor (gapPlusBlock 0) suffix))) := by
            symm
            simpa using
              (UnitaryCircuit.castQubitWidthVec_tensor_right
                (Nat.zero_add (b.ell gap.castSucc)) rfl
                (NormalizedVector.ket0 : HilbertVector (Qubits 1))
                (HilbertVector.tensor (gapPlusBlock 0) suffix))
      _ = _ := by rw [zeroTail, UnitaryCircuit.castQubitWidthVec_self]
  have sourceWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + (0 + b.ell gap.castSucc)))) = b.width := by
    unfold gapWidth
    omega
  have canonicalWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) = b.width := by
    unfold gapWidth
    omega
  have separatedWidth :
      ((b.width - b.ell gap.succ - 1) +
          ((1 + (b.gapWidth gap - 1)) + 1)) +
          b.ell gap.castSucc =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by
    omega
  calc
    b.gapHPartial gap 0 (Nat.zero_le _) =
        UnitaryCircuit.castQubitWidthVec sourceWidth
          (HilbertVector.tensor high
            (HilbertVector.tensor
              (NormalizedVector.ket0 : HilbertVector (Qubits 1))
              (HilbertVector.tensor middle innerSource))) := by
          simpa [high, middle, suffix, innerSource] using
            b.gapHPartial_canonical gap 0 positive
    _ = UnitaryCircuit.castQubitWidthVec canonicalWidth
          (HilbertVector.tensor high
            (HilbertVector.tensor
              (NormalizedVector.ket0 : HilbertVector (Qubits 1))
              (HilbertVector.tensor middle
                (HilbertVector.tensor
                  (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix)))) := by
          rw [UnitaryCircuit.castQubitWidthVec_tensor_three_right
            innerWidth sourceWidth canonicalWidth]
          rw [innerState]
    _ = UnitaryCircuit.castQubitWidthVec canonicalWidth
          (UnitaryCircuit.castQubitWidthVec separatedWidth
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor
                  (HilbertVector.tensor
                    (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle)
                  (NormalizedVector.ket0 : HilbertVector (Qubits 1))))
              suffix)) := by
          congr 1
          exact UnitaryCircuit.castQubitWidthVec_tensor_right_to_separated5
            high (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle
              (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix
    _ = UnitaryCircuit.binarySeparatedVec (b.wire gap.succ)
          (b.wire gap.castSucc) (b.wire_succ_lt_wire gap)
          (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ) high)
          (HilbertVector.tensor
            (NormalizedVector.ket0 : HilbertVector (Qubits 1))
            (NormalizedVector.ket0 : HilbertVector (Qubits 1)))
          (UnitaryCircuit.castQubitWidthVec
            (b.gapWidth_pred_eq_wire_sub gap) middle)
          (UnitaryCircuit.castQubitWidthVec
            (b.ell_eq_wire_suffixWidth gap.castSucc) suffix) := by
          rw [UnitaryCircuit.castQubitWidthVec_trans]
          symm
          simpa using
            (UnitaryCircuit.binarySeparatedVec_tensor_transport
              (b.wire gap.succ) (b.wire gap.castSucc)
              (b.wire_succ_lt_wire gap)
              (b.highWidth_eq_wire_val gap.succ)
              (b.gapWidth_pred_eq_wire_sub gap)
              (b.ell_eq_wire_suffixWidth gap.castSucc)
              high (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle
              (NormalizedVector.ket0 : HilbertVector (Qubits 1)) suffix)

/-- Untouched suffix below the source-rotation target, with the prior source
wire retained explicitly as its trailing zero control. -/
public def rotationSuffix (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    HilbertVector (Qubits (b.width - (b.wire gap.succ).val - 1)) :=
  UnitaryCircuit.castQubitWidthVec (by
    have before := b.wire_succ_lt_wire gap
    omega :
      ((b.wire gap.castSucc).val - (b.wire gap.succ).val - 1) +
          (1 + (b.width - (b.wire gap.castSucc).val - 1)) =
        b.width - (b.wire gap.succ).val - 1)
    (HilbertVector.tensor
      (UnitaryCircuit.castQubitWidthVec (b.gapWidth_pred_eq_wire_sub gap)
        (rawKetZero (b.gapWidth gap - 1)))
      (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
        (UnitaryCircuit.castQubitWidthVec
          (b.ell_eq_wire_suffixWidth gap.castSucc)
          (WalshHadamard.uniformState (b.ell gap.castSucc) :
            HilbertVector (Qubits (b.ell gap.castSucc))))))

/-- The aligned residual before a source rotation in the exact one-wire
layout of the first, uncontrolled source rotation. -/
public theorem residualBlock_eq_rotationWire
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    b.residualBlock gap.castSucc =
      UnitaryCircuit.binaryWireVec (b.wire gap.succ)
        (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (NormalizedVector.ket1 : HilbertVector (Qubits 1)) (b.rotationSuffix gap) := by
  rw [b.residualBlock_eq_rotationSeparated gap]
  symm
  unfold rotationSuffix
  exact UnitaryCircuit.binaryWireVec_eq_binarySeparatedVec
    (b.wire gap.succ) (b.wire gap.castSucc) (b.wire_succ_lt_wire gap)
    (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ)
      (basisKetVec (b.residualHighLabel gap.succ)))
    (NormalizedVector.ket1 : HilbertVector (Qubits 1))
    (UnitaryCircuit.castQubitWidthVec (b.gapWidth_pred_eq_wire_sub gap)
      (rawKetZero (b.gapWidth gap - 1)))
    (NormalizedVector.ket0 : HilbertVector (Qubits 1))
    (UnitaryCircuit.castQubitWidthVec
      (b.ell_eq_wire_suffixWidth gap.castSucc)
      (WalshHadamard.uniformState (b.ell gap.castSucc) :
        HilbertVector (Qubits (b.ell gap.castSucc))))

/-- The newly opened zero branch has the same one-wire suffix as the current
residual and differs only at the rotation target. -/
public theorem gapHPartial_zero_eq_rotationWire
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    b.gapHPartial gap 0 (Nat.zero_le _) =
      UnitaryCircuit.binaryWireVec (b.wire gap.succ)
        (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (NormalizedVector.ket0 : HilbertVector (Qubits 1)) (b.rotationSuffix gap) := by
  rw [b.gapHPartial_zero_eq_rotationSeparated gap]
  symm
  unfold rotationSuffix
  exact UnitaryCircuit.binaryWireVec_eq_binarySeparatedVec
    (b.wire gap.succ) (b.wire gap.castSucc) (b.wire_succ_lt_wire gap)
    (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ)
      (basisKetVec (b.residualHighLabel gap.succ)))
    (NormalizedVector.ket0 : HilbertVector (Qubits 1))
    (UnitaryCircuit.castQubitWidthVec (b.gapWidth_pred_eq_wire_sub gap)
      (rawKetZero (b.gapWidth gap - 1)))
    (NormalizedVector.ket0 : HilbertVector (Qubits 1))
    (UnitaryCircuit.castQubitWidthVec
      (b.ell_eq_wire_suffixWidth gap.castSucc)
      (WalshHadamard.uniformState (b.ell gap.castSucc) :
        HilbertVector (Qubits (b.ell gap.castSucc))))

/-- One more explicit `|+>` factor can be moved across an arbitrary low
suffix without changing physical bit order. -/
private theorem gapPlusBlock_succ_tensor_suffix (count suffixWidth : Nat)
    (suffix : HilbertVector (Qubits suffixWidth)) :
    UnitaryCircuit.castQubitWidthVec (by omega :
      (count + 1) + suffixWidth = 1 + (count + suffixWidth))
      (HilbertVector.tensor (gapPlusBlock (count + 1)) suffix) =
      HilbertVector.tensor (NormalizedVector.ketPlus : HilbertVector (Qubits 1))
        (HilbertVector.tensor (gapPlusBlock count) suffix) := by
  rw [gapPlusBlock]
  rw [UnitaryCircuit.castQubitWidthVec_tensor_left
    (by omega : 1 + count = count + 1)
    (by omega : (count + 1) + suffixWidth = 1 + (count + suffixWidth))]
  simpa using
    (UnitaryCircuit.castQubitWidthVec_tensor_assoc
      (NormalizedVector.ketPlus : HilbertVector (Qubits 1)) (gapPlusBlock count) suffix)

/-- Tensoring two raw Walsh-uniform registers produces the Walsh-uniform
register on their concatenated physical wires. -/
private theorem walshUniform_tensor_walshUniform (leftWidth rightWidth : Nat) :
    HilbertVector.tensor
        (WalshHadamard.uniformState leftWidth : HilbertVector (Qubits leftWidth))
        (WalshHadamard.uniformState rightWidth : HilbertVector (Qubits rightWidth)) =
      (WalshHadamard.uniformState (leftWidth + rightWidth) :
        HilbertVector (Qubits (leftWidth + rightWidth))) := by
  have amplitude : WalshHadamard.invSqrtCard leftWidth *
      WalshHadamard.invSqrtCard rightWidth =
        WalshHadamard.invSqrtCard (leftWidth + rightWidth) := by
    unfold WalshHadamard.invSqrtCard
    rw [← mul_inv, ← Complex.ofReal_mul,
      ← Real.sqrt_mul (by positivity : 0 ≤ ((2 ^ leftWidth : Nat) : ℝ)),
      ← Nat.cast_mul, ← pow_add]
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := leftWidth) (n := rightWidth)).surjective index with
    ⟨⟨leftIndex, rightIndex⟩, rfl⟩
  simp only [HilbertVector.tensor_apply_prod,
    WalshHadamard.uniformState_apply]
  exact amplitude

private theorem castQubitWidthVec_walshUniform {source target : Nat}
    (same : source = target) :
    UnitaryCircuit.castQubitWidthVec same
        (WalshHadamard.uniformState source : HilbertVector (Qubits source)) =
      (WalshHadamard.uniformState target : HilbertVector (Qubits target)) := by
  subst target
  rfl

/-- After one literal gap Hadamard, its target has become the next physical
`|+>` factor and the remaining gap wires stay zero. -/
public theorem gapHPartial_succ_eq_hSeparatedPlus
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) (processed : Nat)
    (notFinished : processed < b.gapWidth gap) :
    b.gapHPartial gap (processed + 1) (Nat.succ_le_of_lt notFinished) =
      UnitaryCircuit.binarySeparatedVec (b.wire gap.succ)
        (b.gapTargetWire gap ⟨processed, notFinished⟩)
        (b.wire_succ_lt_gapTargetWire gap ⟨processed, notFinished⟩)
        (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
          (NormalizedVector.ketPlus : HilbertVector (Qubits 1)))
        (UnitaryCircuit.castQubitWidthVec (by
          have remaining := b.gapRemaining_eq_target_sub gap
            ⟨processed, notFinished⟩
          omega : b.gapWidth gap - (processed + 1) =
            (b.gapTargetWire gap ⟨processed, notFinished⟩).val -
              (b.wire gap.succ).val - 1)
          (rawKetZero (b.gapWidth gap - (processed + 1))))
        (UnitaryCircuit.castQubitWidthVec
          (b.gapProcessed_eq_target_suffixWidth gap
            ⟨processed, notFinished⟩)
          (HilbertVector.tensor (gapPlusBlock processed)
            (WalshHadamard.uniformState (b.ell gap.castSucc) :
              HilbertVector (Qubits (b.ell gap.castSucc))))) := by
  let high := basisKetVec (b.residualHighLabel gap.succ)
  let middle := rawKetZero (b.gapWidth gap - (processed + 1))
  let suffixState := HilbertVector.tensor (gapPlusBlock processed)
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  let expanded := HilbertVector.tensor (gapPlusBlock (processed + 1))
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have tailWidth :
      (processed + 1) + b.ell gap.castSucc =
        1 + (processed + b.ell gap.castSucc) := by omega
  have sourceWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - (processed + 1)) +
            ((processed + 1) + b.ell gap.castSucc))) = b.width := by
    have strict := b.ell_strict gap.castSucc_lt_succ
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth at notFinished ⊢
    omega
  have canonicalWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - (processed + 1)) +
            (1 + (processed + b.ell gap.castSucc)))) = b.width := by
    have strict := b.ell_strict gap.castSucc_lt_succ
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth at notFinished ⊢
    omega
  have separatedWidth :
      ((b.width - b.ell gap.succ - 1) +
          ((1 + (b.gapWidth gap - (processed + 1))) + 1)) +
          (processed + b.ell gap.castSucc) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - (processed + 1)) +
            (1 + (processed + b.ell gap.castSucc)))) := by omega
  have expandedState :
      UnitaryCircuit.castQubitWidthVec tailWidth expanded =
        HilbertVector.tensor (NormalizedVector.ketPlus : HilbertVector (Qubits 1)) suffixState := by
    simpa [expanded, suffixState] using
      gapPlusBlock_succ_tensor_suffix processed (b.ell gap.castSucc)
        (WalshHadamard.uniformState (b.ell gap.castSucc) :
          HilbertVector (Qubits (b.ell gap.castSucc)))
  unfold gapHPartial
  change UnitaryCircuit.castQubitWidthVec sourceWidth
      (HilbertVector.tensor high
        (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
          (HilbertVector.tensor middle expanded))) = _
  rw [UnitaryCircuit.castQubitWidthVec_tensor_three_right
    tailWidth sourceWidth canonicalWidth]
  rw [expandedState]
  calc
    UnitaryCircuit.castQubitWidthVec canonicalWidth
        (HilbertVector.tensor high
          (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
            (HilbertVector.tensor middle
              (HilbertVector.tensor (NormalizedVector.ketPlus : HilbertVector (Qubits 1))
                suffixState)))) =
        UnitaryCircuit.castQubitWidthVec canonicalWidth
          (UnitaryCircuit.castQubitWidthVec separatedWidth
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor
                  (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle)
                  (NormalizedVector.ketPlus : HilbertVector (Qubits 1))))
              suffixState)) := by
            congr 1
            exact UnitaryCircuit.castQubitWidthVec_tensor_right_to_separated5
              high (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle
                (NormalizedVector.ketPlus : HilbertVector (Qubits 1)) suffixState
    _ = UnitaryCircuit.binarySeparatedVec (b.wire gap.succ)
          (b.gapTargetWire gap ⟨processed, notFinished⟩)
          (b.wire_succ_lt_gapTargetWire gap ⟨processed, notFinished⟩)
          (UnitaryCircuit.castQubitWidthVec (b.highWidth_eq_wire_val gap.succ) high)
          (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
            (NormalizedVector.ketPlus : HilbertVector (Qubits 1)))
          (UnitaryCircuit.castQubitWidthVec (by
            have remaining := b.gapRemaining_eq_target_sub gap
              ⟨processed, notFinished⟩
            omega : b.gapWidth gap - (processed + 1) =
              (b.gapTargetWire gap ⟨processed, notFinished⟩).val -
                (b.wire gap.succ).val - 1) middle)
          (UnitaryCircuit.castQubitWidthVec
            (b.gapProcessed_eq_target_suffixWidth gap
              ⟨processed, notFinished⟩) suffixState) := by
          rw [UnitaryCircuit.castQubitWidthVec_trans]
          symm
          simpa using
            (UnitaryCircuit.binarySeparatedVec_tensor_transport
              (b.wire gap.succ)
              (b.gapTargetWire gap ⟨processed, notFinished⟩)
              (b.wire_succ_lt_gapTargetWire gap ⟨processed, notFinished⟩)
              (b.highWidth_eq_wire_val gap.succ)
              (by
                have remaining := b.gapRemaining_eq_target_sub gap
                  ⟨processed, notFinished⟩
                omega : b.gapWidth gap - (processed + 1) =
                  (b.gapTargetWire gap ⟨processed, notFinished⟩).val -
                    (b.wire gap.succ).val - 1)
              (b.gapProcessed_eq_target_suffixWidth gap
                ⟨processed, notFinished⟩)
              high (NormalizedVector.ket0 : HilbertVector (Qubits 1)) middle
              (NormalizedVector.ketPlus : HilbertVector (Qubits 1)) suffixState)

/-- Completing every target in one source gap produces exactly the next
aligned residual block. -/
public theorem gapHPartial_final_eq_residualBlock
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    b.gapHPartial gap (b.gapWidth gap) (Nat.le_refl _) =
      b.residualBlock gap.succ := by
  have ellStep : b.gapWidth gap + b.ell gap.castSucc = b.ell gap.succ := by
    have strict := b.ell_strict gap.castSucc_lt_succ
    unfold gapWidth
    omega
  let high := basisKetVec (b.residualHighLabel gap.succ)
  let suffixState := HilbertVector.tensor (gapPlusBlock (b.gapWidth gap))
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have zeroWidth :
      (b.gapWidth gap - b.gapWidth gap) +
          (b.gapWidth gap + b.ell gap.castSucc) =
        b.gapWidth gap + b.ell gap.castSucc := by omega
  have zeroState :
      UnitaryCircuit.castQubitWidthVec zeroWidth
          (HilbertVector.tensor
            (rawKetZero (b.gapWidth gap - b.gapWidth gap)) suffixState) =
        suffixState := by
    exact rawKetZero_tensor_left_of_eq_zero (Nat.sub_self _) suffixState
  have sourceWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - b.gapWidth gap) +
            (b.gapWidth gap + b.ell gap.castSucc))) = b.width := by
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth
    omega
  have targetWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + (b.gapWidth gap + b.ell gap.castSucc)) = b.width := by
    have upper := b.ell_lt_width gap.succ
    unfold gapWidth
    omega
  have residualWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + b.ell gap.succ) = b.width := by
    have upper := b.ell_lt_width gap.succ
    omega
  unfold gapHPartial
  change UnitaryCircuit.castQubitWidthVec sourceWidth
      (HilbertVector.tensor high
        (HilbertVector.tensor (NormalizedVector.ket0 : HilbertVector (Qubits 1))
          (HilbertVector.tensor
            (rawKetZero (b.gapWidth gap - b.gapWidth gap)) suffixState))) = _
  rw [UnitaryCircuit.castQubitWidthVec_tensor_two_right
    zeroWidth sourceWidth targetWidth]
  rw [zeroState]
  unfold suffixState high
  rw [gapPlusBlock_eq_uniform, walshUniform_tensor_walshUniform]
  rw [UnitaryCircuit.castQubitWidthVec_tensor_two_right
    ellStep targetWidth residualWidth]
  rw [castQubitWidthVec_walshUniform]
  simpa using (b.residualBlock_tensor_factor gap.succ).symm

end

end QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion
