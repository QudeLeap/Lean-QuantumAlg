/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Components.Oracle.Common
import all QuantumAlg.Core.Algorithm
import all QuantumAlg.Core.Base.UnitaryCircuit.Family
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Util.NumberTheory.Cyclic.Power
import all QuantumAlg.Util.ResidueEncoding

/-!
# Ekerå–Håstad short-discrete-logarithm circuit

This module implements the reusable quantum stage of the Ekerå–Håstad
algorithm.  The first and second exponent registers have lengths `ell + m` and
`ell`; the workspace stores the group value
`g^a * (x^b)⁻¹`.  Both exponent registers are prepared uniformly, the group
operation is one sealed query leaf, and the two inverse QFTs are applied in
parallel before terminal measurement.

The oracle operator is constructed from an explicit basis permutation.  It is
not accepted as metadata or as an arbitrary unitary.
-/

section

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

namespace ShortDLP

/-- Faithful computational-basis encoding of the multiplicative unit group.

The short-DLP probability argument only needs distinct group elements to
occupy distinct workspace basis states.  It does not require those basis
labels to be the canonical residue representatives.  This distinction is
essential for ancilla-extended arithmetic circuits, whose clean physical
workspace embeds a residue together with restored work registers. -/
structure UnitEncoding (N n : Nat) where
  /-- Workspace basis label assigned to one unit. -/
  encode : (ZMod N)ˣ → Fin (2 ^ n)
  /-- Distinct units receive distinct workspace labels. -/
  encode_injective : Function.Injective encode

namespace UnitEncoding

/-- Canonical residue labels give the elementary unit encoding used by the
sealed-oracle implementation. -/
def ofResidueEncoding {N n : Nat} (encoding : BinaryResidueEncoding N n) :
    UnitEncoding N n where
  encode value := encoding.encode (value : ZMod N)
  encode_injective := by
    intro left right h
    apply Units.ext
    exact encoding.encode_injective h

instance {N n : Nat} :
    Coe (BinaryResidueEncoding N n) (UnitEncoding N n) :=
  ⟨ofResidueEncoding⟩

end UnitEncoding

/-- Public register dimensions for one short-DLP execution. -/
structure RegisterParameters where
  /-- Upper bound on the short logarithm's bit length. -/
  m : Nat
  /-- Tradeoff register length. -/
  ell : Nat
  /-- Binary width of the encoded group workspace. -/
  workspaceBits : Nat

/-- First exponent-register width. -/
@[implicit_reducible]
def firstBits (params : RegisterParameters) : Nat :=
  params.ell + params.m

/-- Total number of qubits in the two exponent registers and workspace. -/
abbrev totalQubits (params : RegisterParameters) : Nat :=
  firstBits params + params.ell + params.workspaceBits

/-- Pack the three consecutive basis registers into the qubit basis. -/
def tripleIndex (params : RegisterParameters)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    Fin (2 ^ totalQubits params) :=
  prodEquiv (prodEquiv (a, b), workspace)

/-- Source group expression `[a]g ⊙ [-b]x`, written multiplicatively. -/
def oracleValue {N : Nat} (g x : (ZMod N)ˣ) (a b : Nat) : (ZMod N)ˣ :=
  g ^ a * (x ^ b)⁻¹

/-- Integer exponent represented by one short-DLP oracle input when the target
is `g^secret`. -/
def oracleExponent (secret a b : Nat) : Int :=
  (a : Int) - ((b * secret : Nat) : Int)

/-- Translate the possibly negative exponent `a-b*secret` into the finite
interval starting at zero. -/
def oracleFiberIndex (params : RegisterParameters) (secret : Nat)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) : Nat :=
  a.val + (2 ^ params.ell - 1 - b.val) * secret

/-- For a fixed second-register index, the canonical integer-fiber index
determines the first-register index uniquely. -/
theorem oracleFiberIndex_injective_first
    (params : RegisterParameters) (secret : Nat)
    (b : Fin (2 ^ params.ell)) :
    Function.Injective (fun a : Fin (2 ^ firstBits params) =>
      oracleFiberIndex params secret a b) := by
  intro left right hindex
  apply Fin.ext
  change left.val + (2 ^ params.ell - 1 - b.val) * secret =
    right.val + (2 ^ params.ell - 1 - b.val) * secret at hindex
  exact Nat.add_right_cancel hindex

/-- Length of the no-wrap exponent interval used by the short-DLP source. -/
def oracleFiberSpan (params : RegisterParameters) (secret : Nat) : Nat :=
  2 ^ firstBits params + (2 ^ params.ell - 1) * secret

/-- A short logarithm `secret < 2^m` makes the complete integer-exponent
interval no longer than twice the first Fourier-register cardinality. -/
theorem oracleFiberSpan_le_two_mul_firstRegister
    (params : RegisterParameters) (secret : Nat)
    (hsecret : secret < 2 ^ params.m) :
    oracleFiberSpan params secret ≤ 2 * 2 ^ firstBits params := by
  have hproduct :
      (2 ^ params.ell - 1) * secret ≤
        2 ^ params.ell * 2 ^ params.m :=
    Nat.mul_le_mul (Nat.sub_le _ _) (Nat.le_of_lt hsecret)
  unfold oracleFiberSpan firstBits
  rw [pow_add]
  omega

/-- Lower-offset magnitude of the source exponent interval. -/
def oracleFiberOffset (params : RegisterParameters) (secret : Nat) : Nat :=
  (2 ^ params.ell - 1) * secret

/-- Canonical integer exponent represented by an index in the complete source
interval `[-offset, 2^(ell+m)-1]`. -/
def oracleExponentAtIndex (params : RegisterParameters) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret)) : Int :=
  (index.val : Int) - (oracleFiberOffset params secret : Int)

/-- Canonical source-interval indices encode distinct integer exponents. -/
theorem oracleExponentAtIndex_injective
    (params : RegisterParameters) (secret : Nat) :
    Function.Injective (oracleExponentAtIndex params secret) := by
  intro left right h
  apply Fin.ext
  unfold oracleExponentAtIndex at h
  omega

theorem oracleExponent_add_lowerOffset
    (params : RegisterParameters) (secret : Nat)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    oracleExponent secret a.val b.val +
        (((2 ^ params.ell - 1) * secret : Nat) : Int) =
      (oracleFiberIndex params secret a b : Nat) := by
  have hb : b.val ≤ 2 ^ params.ell - 1 := Nat.le_pred_of_lt b.isLt
  have hsplitNat :
      (2 ^ params.ell - 1 - b.val) * secret + b.val * secret =
        (2 ^ params.ell - 1) * secret := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hb]
  have hsplitInt :
      (((2 ^ params.ell - 1 - b.val) * secret : Nat) : Int) +
          ((b.val * secret : Nat) : Int) =
        (((2 ^ params.ell - 1) * secret : Nat) : Int) := by
    exact_mod_cast hsplitNat
  unfold oracleExponent oracleFiberIndex
  push_cast
  omega

theorem oracleFiberIndex_lt_span
    (params : RegisterParameters) (secret : Nat)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    oracleFiberIndex params secret a b < oracleFiberSpan params secret := by
  have hb : b.val ≤ 2 ^ params.ell - 1 := Nat.le_pred_of_lt b.isLt
  have hmul :
      (2 ^ params.ell - 1 - b.val) * secret ≤
        (2 ^ params.ell - 1) * secret :=
    Nat.mul_le_mul_right secret (Nat.sub_le _ _)
  unfold oracleFiberIndex oracleFiberSpan
  omega

/-- The canonical interval index of an actual oracle input decodes back to its
integer exponent. -/
theorem oracleExponentAtIndex_oracleFiberIndex
    (params : RegisterParameters) (secret : Nat)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    oracleExponentAtIndex params secret
        ⟨oracleFiberIndex params secret a b,
          oracleFiberIndex_lt_span params secret a b⟩ =
      oracleExponent secret a.val b.val := by
  have h := oracleExponent_add_lowerOffset params secret a b
  change (oracleFiberIndex params secret a b : Int) -
      (oracleFiberOffset params secret : Int) =
    oracleExponent secret a.val b.val
  unfold oracleFiberOffset
  omega

/-- Any canonical interval exponent and any actual oracle exponent differ by
strictly less than the full interval span. -/
theorem oracleExponentAtIndex_sub_abs_lt_span
    (params : RegisterParameters) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret))
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    |oracleExponentAtIndex params secret index -
        oracleExponent secret a.val b.val| <
      (oracleFiberSpan params secret : Int) := by
  let actualIndex : Fin (oracleFiberSpan params secret) :=
    ⟨oracleFiberIndex params secret a b,
      oracleFiberIndex_lt_span params secret a b⟩
  have hfinite := Int.abs_sub_lt_of_lt_lt actualIndex.isLt index.isLt
  change
    |(index.val : Int) - (actualIndex.val : Int)| <
      (oracleFiberSpan params secret : Int) at hfinite
  rw [← oracleExponentAtIndex_oracleFiberIndex params secret a b]
  unfold oracleExponentAtIndex
  simpa only [sub_sub_sub_cancel_right] using hfinite

/-- Two distinct canonical interval exponents differ by strictly less than the
full interval span. -/
theorem oracleExponentAtIndex_sub_abs_lt_span_index
    (params : RegisterParameters) (secret : Nat)
    (left right : Fin (oracleFiberSpan params secret)) :
    |oracleExponentAtIndex params secret left -
        oracleExponentAtIndex params secret right| <
      (oracleFiberSpan params secret : Int) := by
  have hfinite := Int.abs_sub_lt_of_lt_lt right.isLt left.isLt
  change
    |(left.val : Int) - (right.val : Int)| <
      (oracleFiberSpan params secret : Int) at hfinite
  unfold oracleExponentAtIndex
  simpa only [sub_sub_sub_cancel_right] using hfinite

theorem oracleExponent_sub_abs_lt_span
    (params : RegisterParameters) (secret : Nat)
    (leftA : Fin (2 ^ firstBits params))
    (leftB : Fin (2 ^ params.ell))
    (rightA : Fin (2 ^ firstBits params))
    (rightB : Fin (2 ^ params.ell)) :
    |oracleExponent secret leftA.val leftB.val -
        oracleExponent secret rightA.val rightB.val| <
      (oracleFiberSpan params secret : Int) := by
  have hleft := oracleFiberIndex_lt_span params secret leftA leftB
  have hright := oracleFiberIndex_lt_span params secret rightA rightB
  have hfinite := Int.abs_sub_lt_of_lt_lt hright hleft
  rw [← oracleExponent_add_lowerOffset params secret leftA leftB,
    ← oracleExponent_add_lowerOffset params secret rightA rightB] at hfinite
  simpa only [add_sub_add_right_eq_sub] using hfinite

/-- When the target is `g^secret`, the queried group value is the integer
power `g^(a-b*secret)`.  This is the exponent fiber used by the source
probability distribution [E23, arxiv-v5.tex:228-245]. -/
theorem oracleValue_eq_zpow_of_target {N : Nat} (g x : (ZMod N)ˣ)
    (secret a b : Nat) (htarget : x = g ^ secret) :
    oracleValue g x a b = g ^ oracleExponent secret a b := by
  rw [oracleValue, htarget, ← pow_mul]
  rw [← zpow_natCast g a, ← zpow_natCast g (secret * b), ← zpow_neg,
    ← zpow_add]
  unfold oracleExponent
  congr 2
  push_cast
  ring

/-- Under the source's local no-wrap condition, equality of two queried group
values is exactly equality of their integer exponent fibers. -/
theorem oracleValue_eq_oracleValue_iff_exponent_eq_of_abs_sub_lt_orderOf
    {N : Nat} (g x : (ZMod N)ˣ) (secret leftA leftB rightA rightB : Nat)
    (htarget : x = g ^ secret)
    (hsmall :
      |oracleExponent secret leftA leftB -
          oracleExponent secret rightA rightB| < (orderOf g : Int)) :
    oracleValue g x leftA leftB = oracleValue g x rightA rightB ↔
      oracleExponent secret leftA leftB =
        oracleExponent secret rightA rightB := by
  rw [oracleValue_eq_zpow_of_target g x secret leftA leftB htarget,
    oracleValue_eq_zpow_of_target g x secret rightA rightB htarget]
  exact NumberTheory.zpow_eq_zpow_iff_of_abs_sub_lt_orderOf g _ _ hsmall

/-- Under the source order bound, a canonical interval power `g^e` equals an
actual queried value exactly when their integer exponents agree. -/
theorem zpow_at_index_eq_oracleValue_iff_exponent_eq_of_span_le_orderOf
    {N : Nat} {params : RegisterParameters}
    (g x : (ZMod N)ˣ) (secret : Nat)
    (index : Fin (oracleFiberSpan params secret))
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    g ^ oracleExponentAtIndex params secret index =
        oracleValue g x a.val b.val ↔
      oracleExponentAtIndex params secret index =
        oracleExponent secret a.val b.val := by
  rw [oracleValue_eq_zpow_of_target g x secret a.val b.val htarget]
  apply NumberTheory.zpow_eq_zpow_iff_of_abs_sub_lt_orderOf
  exact (oracleExponentAtIndex_sub_abs_lt_span
    params secret index a b).trans_le (by exact_mod_cast horder)

/-- The source order lower bound makes every workspace fiber collision-free
over the complete exponent-register box [E23, arxiv-v5.tex:244-245]. -/
theorem oracleValue_eq_oracleValue_iff_exponent_eq_of_span_le_orderOf
    {N : Nat} {params : RegisterParameters}
    (g x : (ZMod N)ˣ) (secret : Nat)
    (leftA : Fin (2 ^ firstBits params))
    (leftB : Fin (2 ^ params.ell))
    (rightA : Fin (2 ^ firstBits params))
    (rightB : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    oracleValue g x leftA.val leftB.val =
        oracleValue g x rightA.val rightB.val ↔
      oracleExponent secret leftA.val leftB.val =
        oracleExponent secret rightA.val rightB.val := by
  apply oracleValue_eq_oracleValue_iff_exponent_eq_of_abs_sub_lt_orderOf
    g x secret leftA.val leftB.val rightA.val rightB.val htarget
  exact (oracleExponent_sub_abs_lt_span
    params secret leftA leftB rightA rightB).trans_le (by exact_mod_cast horder)

/-- Canonical binary encoding of a unit's residue value. -/
def encodeUnit {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (value : (ZMod N)ˣ) : Fin (2 ^ params.workspaceBits) :=
  encoding.encode value

/-- Canonical workspace encoding does not identify distinct units. -/
theorem encodeUnit_injective {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) :
    Function.Injective (encodeUnit encoding) :=
  encoding.encode_injective

/-- Reversible XOR loading of the selected group value into the workspace. -/
def oracleTarget {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (a : Fin (2 ^ firstBits params))
    (b : Fin (2 ^ params.ell))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    Fin (2 ^ params.workspaceBits) :=
  ⟨Nat.xor workspace.val (encodeUnit encoding (oracleValue g x a.val b.val)).val,
    Nat.xor_lt_two_pow workspace.isLt
      (encodeUnit encoding (oracleValue g x a.val b.val)).isLt⟩

/-- Basis permutation underlying the actual short-DLP group-operation query. -/
def oraclePerm {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    Equiv.Perm
      ((Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) ×
        Fin (2 ^ params.workspaceBits)) where
  toFun input :=
    (input.1, oracleTarget encoding g x input.1.1 input.1.2 input.2)
  invFun input :=
    (input.1, oracleTarget encoding g x input.1.1 input.1.2 input.2)
  left_inv input := by
    ext <;> simp [oracleTarget]
  right_inv input := by
    ext <;> simp [oracleTarget]

@[simp]
theorem oraclePerm_symm {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (oraclePerm encoding g x).symm = oraclePerm encoding g x :=
  rfl

/-- Metadata-free unitary induced by the short-DLP basis permutation. -/
def tripleEquiv (params : RegisterParameters) :
    ((Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) ×
        Fin (2 ^ params.workspaceBits)) ≃
      Fin (2 ^ totalQubits params) :=
  (Equiv.prodCongr
      (prodEquiv (m := firstBits params) (n := params.ell))
      (Equiv.refl (Fin (2 ^ params.workspaceBits)))).trans
    (prodEquiv
      (m := firstBits params + params.ell) (n := params.workspaceBits))

/-- Metadata-free unitary induced by the short-DLP basis permutation. -/
def oracleOperator {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : UnitaryOperator (Qubits (totalQubits params)) :=
  UnitaryOperator.ofPerm
    ((tripleEquiv params).permCongr (oraclePerm encoding g x))

/-- Stable resource label for the short-DLP group-operation query. -/
def oracleLabel (N : Nat) (params : RegisterParameters) :
    QuantumAlg.Resource.SubroutineLabel :=
  shortDLPOracleLabel N params.m params.ell params.workspaceBits



/-- Literal strict event for one short-DLP group-operation query. -/
def oracleEvent (N : Nat) (params : RegisterParameters) :
    Resource.Event .quantum :=
  .quantumSubroutine (oracleLabel N params).quantum

/-- Tensor two canonically placed circuits on consecutive intervals. -/
def tensorConsecutive {leftBits rightBits : Nat}
    (left : UnitaryCircuit (Qubits leftBits))
    (right : UnitaryCircuit (Qubits rightBits))
    (hleft : left.physical_idx = List.range leftBits)
    (hright : right.physical_idx = List.range rightBits) :
    UnitaryCircuit (Qubits (leftBits + rightBits)) := by
  let shifted := UnitaryCircuit.shiftPhysicalIdx leftBits right
  exact UnitaryCircuit.tensorQubits left shifted
    { left_nodup := left.physical_idx_nodup
      right_nodup := shifted.physical_idx_nodup
      disjoint := by
        rw [hleft, UnitaryCircuit.shiftPhysicalIdx_physical_idx, hright,
          List.disjoint_left]
        intro index hindex hshifted
        obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hshifted
        have hindex_lt := List.mem_range.mp hindex
        have hsource_lt := List.mem_range.mp hsource
        omega }

@[simp]
theorem tensorConsecutive_physical_idx {leftBits rightBits : Nat}
    (left : UnitaryCircuit (Qubits leftBits))
    (right : UnitaryCircuit (Qubits rightBits))
    (hleft : left.physical_idx = List.range leftBits)
    (hright : right.physical_idx = List.range rightBits) :
    (tensorConsecutive left right hleft hright).physical_idx =
      List.range (leftBits + rightBits) := by
  simp only [tensorConsecutive, UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex,
    UnitaryCircuit.tensor, PhysicalLayout.DisjointMerge.merged_eq_append,
    UnitaryCircuit.shiftPhysicalIdx_physical_idx, hleft, hright]
  rw [← List.range'_eq_map_range]
  simpa [List.range_eq_range'] using
    (List.range'_append_1 (s := 0) (m := leftBits) (n := rightBits))



@[simp]
theorem tensorConsecutive_eventCost {leftBits rightBits : Nat}
    (left : UnitaryCircuit (Qubits leftBits))
    (right : UnitaryCircuit (Qubits rightBits))
    (hleft : left.physical_idx = List.range leftBits)
    (hright : right.physical_idx = List.range rightBits) :
    (tensorConsecutive left right hleft hright).eventCost =
      left.eventCost + right.eventCost := by
  simp only [tensorConsecutive, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.shiftPhysicalIdx_eventCost]

@[simp]
theorem tensorConsecutive_eventDepth {leftBits rightBits : Nat}
    (left : UnitaryCircuit (Qubits leftBits))
    (right : UnitaryCircuit (Qubits rightBits))
    (hleft : left.physical_idx = List.range leftBits)
    (hright : right.physical_idx = List.range rightBits) :
    (tensorConsecutive left right hleft hright).eventDepth =
      .tensor left.eventDepth right.eventDepth := by
  simp only [tensorConsecutive, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
    UnitaryCircuit.shiftPhysicalIdx_eventDepth]



@[simp]
theorem tensorConsecutive_matrix {leftBits rightBits : Nat}
    (left : UnitaryCircuit (Qubits leftBits))
    (right : UnitaryCircuit (Qubits rightBits))
    (hleft : left.physical_idx = List.range leftBits)
    (hright : right.physical_idx = List.range rightBits) :
    (tensorConsecutive left right hleft hright).matrix =
      UnitaryOperator.tensor left.matrix right.matrix := by
  unfold tensorConsecutive
  simp only [UnitaryCircuit.tensorQubits_matrix,
    UnitaryCircuit.shiftPhysicalIdx_matrix]

/-- Parallel Hadamard preparation on the two exponent registers. -/
def exponentPreparation (params : RegisterParameters) :
    UnitaryCircuit (Qubits (firstBits params + params.ell)) :=
  tensorConsecutive
    (WalshHadamard.hadamardLayer (firstBits params))
    (WalshHadamard.hadamardLayer params.ell)
    (WalshHadamard.hadamardLayer_physical_idx (firstBits params))
    (WalshHadamard.hadamardLayer_physical_idx params.ell)

@[simp]
theorem exponentPreparation_eventDepth (params : RegisterParameters) :
    (exponentPreparation params).eventDepth =
      .tensor
        (WalshHadamard.parallelHadamardEventDepth (firstBits params))
        (WalshHadamard.parallelHadamardEventDepth params.ell) := by
  simp [exponentPreparation]

@[simp]
theorem exponentPreparation_physical_idx (params : RegisterParameters) :
    (exponentPreparation params).physical_idx =
      List.range (firstBits params + params.ell) := by
  simp [exponentPreparation]

/-- Extend an exponent-register circuit by an untouched workspace. -/
def withWorkspace (params : RegisterParameters)
    (body : UnitaryCircuit (Qubits (firstBits params + params.ell)))
    (hbody : body.physical_idx =
      List.range (firstBits params + params.ell)) :
    UnitaryCircuit (Qubits (totalQubits params)) := by
  let workspace := UnitaryCircuit.identity (Qubits params.workspaceBits)
    (List.range' (firstBits params + params.ell) params.workspaceBits)
    List.nodup_range'
  unfold totalQubits
  exact UnitaryCircuit.tensorQubits body workspace
    { left_nodup := body.physical_idx_nodup
      right_nodup := List.nodup_range'
      disjoint := by
        rw [hbody, List.disjoint_left]
        intro index hleft hright
        have hlt := List.mem_range.mp hleft
        have hle := List.left_le_of_mem_range' hright
        omega }

@[simp]
theorem withWorkspace_physical_idx (params : RegisterParameters)
    (body : UnitaryCircuit (Qubits (firstBits params + params.ell)))
    (hbody : body.physical_idx =
      List.range (firstBits params + params.ell)) :
    (withWorkspace params body hbody).physical_idx =
      List.range (totalQubits params) := by
  simp only [withWorkspace, UnitaryCircuit.tensorQubits, UnitaryCircuit.reindex,
    UnitaryCircuit.tensor, UnitaryCircuit.identity,
    PhysicalLayout.DisjointMerge.merged_eq_append, hbody]
  simpa [totalQubits, List.range_eq_range'] using
    (List.range'_append_1
      (s := 0) (m := firstBits params + params.ell)
      (n := params.workspaceBits))



@[simp]
theorem withWorkspace_eventCost (params : RegisterParameters)
    (body : UnitaryCircuit (Qubits (firstBits params + params.ell)))
    (hbody : body.physical_idx =
      List.range (firstBits params + params.ell)) :
    (withWorkspace params body hbody).eventCost = body.eventCost := by
  unfold withWorkspace
  simp only [id_eq, totalQubits, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]

@[simp]
theorem withWorkspace_eventDepth (params : RegisterParameters)
    (body : UnitaryCircuit (Qubits (firstBits params + params.ell)))
    (hbody : body.physical_idx =
      List.range (firstBits params + params.ell)) :
    (withWorkspace params body hbody).eventDepth =
      .tensor body.eventDepth .id := by
  unfold withWorkspace
  rfl



@[simp]
theorem withWorkspace_matrix (params : RegisterParameters)
    (body : UnitaryCircuit (Qubits (firstBits params + params.ell)))
    (hbody : body.physical_idx =
      List.range (firstBits params + params.ell)) :
    (withWorkspace params body hbody).matrix =
      UnitaryOperator.tensor body.matrix
        (1 : UnitaryOperator (Qubits params.workspaceBits)) := by
  unfold withWorkspace
  simp only [id_eq, UnitaryCircuit.tensorQubits_matrix]
  congr 1

/-- Uniform preparation of both exponent registers. -/
def preparationCircuit (params : RegisterParameters) :
    UnitaryCircuit (Qubits (totalQubits params)) :=
  withWorkspace params (exponentPreparation params)
    (exponentPreparation_physical_idx params)

@[simp]
theorem preparationCircuit_physical_idx (params : RegisterParameters) :
    (preparationCircuit params).physical_idx =
      List.range (totalQubits params) := by
  exact withWorkspace_physical_idx params _ _



@[simp]
theorem preparationCircuit_eventCost (params : RegisterParameters) :
    (preparationCircuit params).eventCost =
      ResourcePool.singleton WalshHadamard.hadamardEvent
          (firstBits params) +
        ResourcePool.singleton WalshHadamard.hadamardEvent params.ell := by
  rw [preparationCircuit, withWorkspace_eventCost]
  simp [exponentPreparation]

@[simp]
theorem preparationCircuit_eventDepth (params : RegisterParameters) :
    (preparationCircuit params).eventDepth =
      .tensor
        (.tensor
          (WalshHadamard.parallelHadamardEventDepth (firstBits params))
          (WalshHadamard.parallelHadamardEventDepth params.ell))
        .id := by
  simp [preparationCircuit]

/-- The internally constructed group operation as one sealed query leaf. -/
def oracleLeaf {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : UnitaryLeaf (Qubits (totalQubits params)) :=
  shortDLPOracleLeafAt N params.m params.ell params.workspaceBits
    (oracleOperator encoding g x)
    (List.range (totalQubits params))

/-- The actual short-DLP group operation circuit. -/
def oracleCircuit {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : UnitaryCircuit (Qubits (totalQubits params)) :=
  UnitaryCircuit.ofLeaf (oracleLeaf encoding g x) (by
    simpa only [oracleLeaf, shortDLPOracleLeafAt,
      UnitaryLeaf.subroutine_systemIdx] using
      (List.nodup_range : (List.range (totalQubits params)).Nodup))



@[simp]
theorem oracleLeaf_event {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (oracleLeaf encoding g x).event = oracleEvent N params :=
  rfl

@[simp]
theorem oracleCircuit_physical_idx {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (oracleCircuit encoding g x).physical_idx =
      List.range (totalQubits params) :=
  rfl

/-- Parallel inverse QFTs on the two exponent registers. -/
def exponentReadout (params : RegisterParameters) :
    UnitaryCircuit (Qubits (firstBits params + params.ell)) :=
  tensorConsecutive
    (UnitaryCircuit.dagger (QFTCircuit (firstBits params)))
    (UnitaryCircuit.dagger (QFTCircuit params.ell)) (by simp) (by simp)

@[simp]
theorem exponentReadout_physical_idx (params : RegisterParameters) :
    (exponentReadout params).physical_idx =
      List.range (firstBits params + params.ell) := by
  simp [exponentReadout]

@[simp]
theorem exponentReadout_matrix (params : RegisterParameters) :
    (exponentReadout params).matrix =
      UnitaryOperator.tensor
        (UnitaryCircuit.dagger (QFTCircuit (firstBits params))).matrix
        (UnitaryCircuit.dagger (QFTCircuit params.ell)).matrix := by
  unfold exponentReadout
  rw [tensorConsecutive_matrix]

/-- QFT readout extended by the untouched group workspace. -/
def readoutCircuit (params : RegisterParameters) :
    UnitaryCircuit (Qubits (totalQubits params)) :=
  withWorkspace params (exponentReadout params)
    (exponentReadout_physical_idx params)

@[simp]
theorem readoutCircuit_physical_idx (params : RegisterParameters) :
    (readoutCircuit params).physical_idx =
      List.range (totalQubits params) := by
  exact withWorkspace_physical_idx params _ _

@[simp]
theorem readoutCircuit_matrix (params : RegisterParameters) :
    (readoutCircuit params).matrix =
      UnitaryOperator.tensor (exponentReadout params).matrix
        (1 : UnitaryOperator (Qubits params.workspaceBits)) := by
  unfold readoutCircuit
  rw [withWorkspace_matrix]



@[simp]
theorem readoutCircuit_eventCost (params : RegisterParameters) :
    (readoutCircuit params).eventCost =
      (QFTCircuit (firstBits params)).eventCost +
        (QFTCircuit params.ell).eventCost := by
  rw [readoutCircuit, withWorkspace_eventCost]
  simp only [exponentReadout, tensorConsecutive_eventCost,
    UnitaryCircuit.dagger_eventCost]

@[simp]
theorem readoutCircuit_eventDepth (params : RegisterParameters) :
    (readoutCircuit params).eventDepth =
      .tensor
        (.tensor
          (.inverse (QFTCircuit (firstBits params)).eventDepth)
          (.inverse (QFTCircuit params.ell).eventDepth))
        .id := by
  simp only [readoutCircuit, withWorkspace_eventDepth, exponentReadout,
    tensorConsecutive_eventDepth, UnitaryCircuit.dagger_eventDepth]

/-- Complete prepare-query-readout short-DLP circuit. -/
def circuit {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : UnitaryCircuit (Qubits (totalQubits params)) :=
  UnitaryCircuit.seq (preparationCircuit params)
    (UnitaryCircuit.seq (oracleCircuit encoding g x) (readoutCircuit params))

@[simp]
theorem circuit_physical_idx {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (circuit encoding g x).physical_idx = List.range (totalQubits params) := by
  simp [circuit, UnitaryCircuit.seq]



@[simp]
theorem circuit_eventCost {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (circuit encoding g x).eventCost =
      (preparationCircuit params).eventCost +
        (ResourcePool.singleton (oracleEvent N params) +
          (readoutCircuit params).eventCost) :=
  rfl



@[simp]
theorem circuit_eventDepth {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (circuit encoding g x).eventDepth =
      .seq (preparationCircuit params).eventDepth
      (.seq (.atom (oracleEvent N params))
        (readoutCircuit params).eventDepth) :=
  rfl

/-- Closed unit-weight depth of one structural QFT. -/
def qftUnitDepth (bits : Nat) : Nat :=
  bits + bits * (bits - 1) / 2 + bits / 2

/-- Closed unit-weight critical path of the complete short-DLP circuit. -/
def circuitUnitDepth (params : RegisterParameters) : Nat :=
  max (if firstBits params = 0 then 0 else 1)
      (if params.ell = 0 then 0 else 1) +
    1 + max (qftUnitDepth (firstBits params)) (qftUnitDepth params.ell)









/-- Runtime generator family with strict resource envelopes and one layout. -/
def circuitFamily {Parameter : Type} {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (generator target : Parameter → (ZMod N)ˣ) :
    UnitaryCircuitFamily Parameter (Qubits (totalQubits params)) where
  member parameter := circuit encoding (generator parameter) (target parameter)
  eventEnvelope :=
    (preparationCircuit params).eventCost +
      (ResourcePool.singleton (oracleEvent N params) +
        (readoutCircuit params).eventCost)
  member_eventCost_le parameter :=
    (circuit_eventCost encoding (generator parameter) (target parameter)).le
  depthEnvelope :=
    .seq (preparationCircuit params).eventDepth
      (.seq (.atom (oracleEvent N params))
        (readoutCircuit params).eventDepth)
  member_eventDepth_le parameter assignment := by
    rw [circuit_eventDepth encoding (generator parameter) (target parameter)]
  commonPhysicalIdx := List.range (totalQubits params)
  member_physical_idx parameter :=
    circuit_physical_idx encoding (generator parameter) (target parameter)

/-- Canonical physical layout for the complete circuit. -/
def layout (params : RegisterParameters) : QubitLayout (totalQubits params) where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ h => Fin.ext h

@[simp]
theorem layout_systemIdx (params : RegisterParameters) :
    (layout params).systemIdx = List.range (totalQubits params) := by
  simp [layout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- Canonical all-zero initial state. -/
def inputState (params : RegisterParameters) : QubitLayout.State (layout params) where
  state := PureState.ofNormalized
    (NormalizedVector.ket (R := Qubits (totalQubits params)) 0)
    (layout params).systemIdx
  system_idx_eq := rfl

/-- Terminal measurement of both exponent registers. -/
def measurement (params : RegisterParameters) :
    TerminalZMeasure (layout params) (firstBits params + params.ell) :=
  zMeasureAt (layout params)
    (fun index => ⟨index.val, by unfold totalQubits; omega⟩)
    (fun _ _ h => Fin.ext (Fin.mk.inj h))



/-- Raw measured pair of exponent-register values. -/
abbrev Outcome (params : RegisterParameters) : Type :=
  TerminalZMeasure.Outcome (firstBits params + params.ell)

/-- Decode a terminal outcome into the source pair `(j,k)`. -/
def decodeOutcome (params : RegisterParameters) (outcome : Outcome params) :
    Fin (2 ^ firstBits params) × Fin (2 ^ params.ell) :=
  prodEquiv.symm (TerminalZMeasure.fullRegisterIndex outcome)

end ShortDLP

end

end QuantumAlg

end
