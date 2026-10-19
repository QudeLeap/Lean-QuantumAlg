/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Framing
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Words
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Words

/-!
# Actual coordinate conversion after the original charged initialization

The actual initialization supplies the fixed arithmetic work and zero selector
beside the complete original exponent register. Pair conversion acts on these
same coordinates and restores that complete initialized basis, so no caller
must provide a prepared-work or selector premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MeasuredUncompute MeasuredPointAddition Allocation

/-- The actual indexed register contains the original exponents followed by the zero selector. -/
def initializedIndexed (modulus count : Nat)
    (exponent : (exponents modulus.size count).register.Index) :
    (indexedContext modulus.size (List.range (count + 1)) List.nodup_range).register.Index :=
  (rangeBasis modulus.size (count + 1)).symm
    (fun index => Fin.lastCases 0 (rangeBasis modulus.size count exponent) index)

/-- The complete initialization equals prepared arithmetic beside the exact indexed input. -/
lemma initializedReadyBasis_preparedLabel (modulus count : Nat)
    (exponent : (exponents modulus.size count).register.Index)
    (x y : Fin (2 ^ modulus.size)) :
    initializedReadyBasis modulus count (inputLabel modulus.size count exponent x y) =
      preparedReadyLabel modulus count x y (initializedIndexed modulus count exponent) := by
  apply readyBasis_ext
  · rw [initializedReadyBasis_shared]
    let assembledBasis := ContextUnion.unionBasisEquiv (NumeratorMeasurement.context modulus.size)
      (indexedContext modulus.size (List.range (count + 1)) List.nodup_range)
      (indexedContext_disjoint modulus.size (List.range (count + 1)) List.nodup_range)
    have assembled := assembledBasis.apply_symm_apply
      (InPlaceTarget.preparedBasis modulus x y, initializedIndexed modulus count exponent)
    exact (congrArg Prod.fst assembled).symm
  · intro index
    have indexed : indexedValue modulus.size count
        (preparedReadyLabel modulus count x y (initializedIndexed modulus count exponent)) index =
        Fin.lastCases 0 (rangeBasis modulus.size count exponent) index := by
      change rangeBasis modulus.size (count + 1)
        ((ContextUnion.unionBasisEquiv (NumeratorMeasurement.context modulus.size)
          (indexedContext modulus.size (List.range (count + 1)) List.nodup_range)
          (indexedContext_disjoint modulus.size (List.range (count + 1)) List.nodup_range))
          ((ContextUnion.unionBasisEquiv (NumeratorMeasurement.context modulus.size)
            (indexedContext modulus.size (List.range (count + 1)) List.nodup_range)
            (indexedContext_disjoint modulus.size (List.range (count + 1)) List.nodup_range)).symm
            (InPlaceTarget.preparedBasis modulus x y,
              initializedIndexed modulus count exponent))).2 index = _
      rw [Equiv.apply_symm_apply]
      exact congrFun ((rangeBasis modulus.size (count + 1)).apply_symm_apply _) index
    rw [indexed]
    refine Fin.lastCases ?_ (fun original => ?_) index
    · rw [initializedReadyBasis_selector, Fin.lastCases_last]
    · rw [initializedReadyBasis_exponent, Fin.lastCases_castSucc]

/-- Actual pair conversion restores the complete initialized basis around its two updated words. -/
lemma pairOperator_initializedReadyBasis (modulus count : Nat) (positive : 0 < modulus)
    (coefficient : (ZMod modulus)ˣ)
    (exponent : (exponents modulus.size count).register.Index)
    (x y : Fin (2 ^ modulus.size)) (xValid : x.val < modulus) (yValid : y.val < modulus)
    {Reference : Register} (reference : Reference.Index) :
    (pairOperator (environment := environment) modulus.size count
      (InPlaceTarget.modulusWord modulus) coefficient Reference).applyVec
      (NormalizedVector.ket (initializedReadyBasis modulus count
        (inputLabel modulus.size count exponent x y), reference)).vec =
      (NormalizedVector.ket (initializedReadyBasis modulus count
        (inputLabel modulus.size count exponent
          (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus)
            positive coefficient x)
          (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus)
            positive coefficient y)),
        reference)).vec := by
  rw [initializedReadyBasis_preparedLabel, initializedReadyBasis_preparedLabel]
  exact pairOperator_prepared modulus count positive coefficient x y xValid yValid
    (initializedIndexed modulus count exponent) reference

/-- Canonical field coordinates undergo exact unit scaling on the actually initialized register. -/
lemma pairOperator_initialized_fieldWords {p : Nat} [Fact p.Prime] (count : Nat)
    (coefficient : (ZMod p)ˣ) (exponent : (exponents p.size count).register.Index)
    (x y : ZMod p) {Reference : Register} (reference : Reference.Index) :
    (pairOperator (environment := environment) p.size count (InPlaceTarget.modulusWord p)
      coefficient Reference).applyVec
      (NormalizedVector.ket (initializedReadyBasis p count
        (inputLabel p.size count exponent (fieldWord x) (fieldWord y)), reference)).vec =
      (NormalizedVector.ket (initializedReadyBasis p count
        (inputLabel p.size count exponent (fieldWord ((coefficient : ZMod p) * x))
          (fieldWord ((coefficient : ZMod p) * y))), reference)).vec := by
  have actual := pairOperator_initializedReadyBasis (environment := environment) p count (Fact.out
    : Nat.Prime p).pos
    coefficient exponent (fieldWord x) (fieldWord y) (ZMod.val_lt x) (ZMod.val_lt y) reference
  rw [unitProductWord_fieldWord, unitProductWord_fieldWord] at actual
  exact actual

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
