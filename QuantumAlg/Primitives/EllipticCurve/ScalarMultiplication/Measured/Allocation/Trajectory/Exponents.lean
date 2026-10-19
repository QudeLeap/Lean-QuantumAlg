/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Words
import all QuantumAlg.Util.ExceptionalOffsetAveraging

/-!
# Original Boolean exponent inputs on the actual indexed systems

The exponent input assigns each Boolean selection to its actual dimension-two
system. Two original exponent words use the prescribed consecutive big-endian
order: the first word occupies positions below the exponent width, and the
second word occupies the following positions. Actual initialization retains
every one of these physical selections exactly.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

/-- Supplied Boolean controls occupy the original exponent systems in their exact indexed order. -/
def exponentInput (modulus count : Nat) (controls : Fin count → Bool) :
    (exponents modulus.size count).register.Index :=
  (rangeBasis modulus.size count).symm (BinaryLabelEncoding.bool.encode ∘ controls)

/-- Reading all actual exponent systems recovers exactly the supplied Boolean encoding. -/
lemma exponentInput_rangeBasis (modulus count : Nat) (controls : Fin count → Bool) :
    rangeBasis modulus.size count (exponentInput modulus count controls) =
      BinaryLabelEncoding.bool.encode ∘ controls :=
  (rangeBasis modulus.size count).apply_symm_apply _

/-- The original physical system at each range position carries its supplied Boolean value. -/
lemma exponentInput_physical_value (modulus count : Nat) (controls : Fin count → Bool)
    (index : Fin count) :
    (exponentInput modulus count controls (rangePosition modulus.size count index)).val =
      (BinaryLabelEncoding.bool.encode (controls index)).val := by
  rw [← rangeBasis_value, exponentInput_rangeBasis]
  rfl

/-- An original indexed selection is active exactly when its supplied Boolean is true. -/
lemma exponentInput_selected_iff (modulus count : Nat) (controls : Fin count → Bool)
    (index : Fin count) :
    rangeBasis modulus.size count (exponentInput modulus count controls) index = 1 ↔
      controls index = true := by
  rw [exponentInput_rangeBasis]
  change BinaryLabelEncoding.bool.encode (controls index) = 1 ↔ controls index = true
  cases controls index <;> decide

/-- Both actual preparations and every finite-cell retain preserve each supplied selection. -/
lemma initializedReadyBasis_exponentInput (modulus count : Nat)
    (controls : Fin count → Bool) (x y : Fin (2 ^ modulus.size)) (index : Fin count) :
    indexedValue modulus.size count
      (initializedReadyBasis modulus count
        (inputLabel modulus.size count (exponentInput modulus count controls) x y))
      index.castSucc = BinaryLabelEncoding.bool.encode (controls index) := by
  rw [initializedReadyBasis_exponent, exponentInput_rangeBasis]
  rfl

/-- The original trajectory predicate reads exactly the supplied Boolean exponent selections. -/
lemma inputTrajectory_exponentInput_iff {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (controls : Fin count → Bool) (order : List (Fin count)) (x y : Fin (2 ^ p.size)) :
    inputTrajectory E points order
        (inputLabel p.size count (exponentInput p count controls) x y) ↔
      wordTrajectory E points (BinaryLabelEncoding.bool.encode ∘ controls) order (x, y) := by
  rw [inputTrajectory_inputLabel_iff, exponentInput_rangeBasis]
  rfl

/-- Two original exponent words supply their consecutive big-endian physical selections. -/
def pairedExponentInput (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    (exponents modulus.size (2 * exponentWidth)).register.Index :=
  exponentInput modulus (2 * exponentWidth)
    (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)

/-- The paired exponent basis uses exactly the original two-register selection function. -/
lemma pairedExponentInput_rangeBasis (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    rangeBasis modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth branch) =
      BinaryLabelEncoding.bool.encode ∘
        ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch :=
  exponentInput_rangeBasis modulus (2 * exponentWidth) _

/-- Position i of the first original word reads its bit exponentWidth - 1 - i. -/
lemma pairedExponentInput_left (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) (index : Fin exponentWidth) :
    rangeBasis modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth branch)
        ⟨index.val, by omega⟩ =
      BinaryLabelEncoding.bool.encode
        (branch.1.val.testBit (exponentWidth - 1 - index.val)) := by
  rw [pairedExponentInput_rangeBasis]
  simp only [Function.comp_apply, ExceptionalOffsetAveraging.pairedBigEndianSelected,
    index.isLt, dite_true]
  rfl

/-- Position exponentWidth + i reads the same big-endian bit of the second original word. -/
lemma pairedExponentInput_right (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) (index : Fin exponentWidth) :
    rangeBasis modulus.size (2 * exponentWidth)
        (pairedExponentInput modulus exponentWidth branch)
        ⟨exponentWidth + index.val, by omega⟩ =
      BinaryLabelEncoding.bool.encode
        (branch.2.val.testBit (exponentWidth - 1 - index.val)) := by
  rw [pairedExponentInput_rangeBasis]
  have second : ¬exponentWidth + index.val < exponentWidth := by omega
  simp only [Function.comp_apply, ExceptionalOffsetAveraging.pairedBigEndianSelected,
    second, dite_false, Nat.add_sub_cancel_left]
  rfl

/-- The initialized workspace preserves exactly the original paired physical selection function. -/
lemma initializedReadyBasis_pairedExponentInput (modulus exponentWidth : Nat)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (x y : Fin (2 ^ modulus.size)) (index : Fin (2 * exponentWidth)) :
    indexedValue modulus.size (2 * exponentWidth)
      (initializedReadyBasis modulus (2 * exponentWidth)
        (inputLabel modulus.size (2 * exponentWidth)
          (pairedExponentInput modulus exponentWidth branch) x y))
      index.castSucc = BinaryLabelEncoding.bool.encode
        (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index) :=
  initializedReadyBasis_exponentInput modulus (2 * exponentWidth) _ x y index

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
