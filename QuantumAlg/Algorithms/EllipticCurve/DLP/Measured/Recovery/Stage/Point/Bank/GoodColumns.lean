/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Fibers
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.GoodColumns

/-!
# Actual point-bank columns on the original prepared arithmetic frame

The fixed coherent control selects the original finite-word translation. Each
complete pair of real point outcomes has the same scalar on every allowed
prepared bank column. The entire Reference and the zero selector are retained.
These local column identities are intended for the original good trajectory;
they add no algorithm input certificate and assert no whole success floor.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace PointBankGoodColumns

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- Keep every prescribed arithmetic bit, the selector and the supplied reference label. -/
def preparedBank (p : Nat) (Reference : Register)
    (words : Fin (2 ^ p.size) × Fin (2 ^ p.size)) (reference : Reference.Index) :
    Recovery.Point.Instrument.FiberBank p.size Reference :=
  (InPlaceTarget.preparedBasis p words.1 words.2, (0, reference))

/-- The fixed coherent source control selects the original complete word translation. -/
def nextWords {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (bit : Fin 2) (words : Fin (2 ^ p.size) × Fin (2 ^ p.size)) :
    Fin (2 ^ p.size) × Fin (2 ^ p.size) :=
  if bit = 1 then translationWords E Q words else words

-- Keep the already proved target and fiber coordinate maps opaque in column algebra.
attribute [local irreducible] MeasuredPointAddition.target Recovery.Point.Instrument.fiberBasis

private lemma targetBank_column {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) (bit : Fin 2)
    (words : Fin (2 ^ p.size) × Fin (2 ^ p.size)) (reference : Reference.Index)
    (row : Recovery.Point.Instrument.FiberBank p.size Reference) :
    target E Q Reference
        ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, row))
        ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm
          (bit, preparedBank p Reference words reference)) =
      if row = preparedBank p Reference (nextWords E Q bit words) reference then 1 else 0 := by
  let output : Recovery.Point.Instrument.FiberBank p.size Reference :=
    preparedBank p Reference (nextWords E Q bit words) reference
  have action : (target E Q Reference).applyVec
      (NormalizedVector.ket
        ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm
          (bit, preparedBank p Reference words reference))).vec =
      (NormalizedVector.ket
        ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, output))).vec := by
    simpa only [Recovery.Point.Instrument.fiberBasis_symm, preparedBank, output,
      InPlaceTarget.preparedBasis, nextWords] using
      target_prepared_ket E Q bit 0 words.1 words.2 reference
  have entry := congrArg
    (fun vector : HilbertVector ((context p.size).register.prod Reference) =>
      vector ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, row))) action
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply] at entry
  have same :
      (Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, row) =
          (Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, output) ↔ row =
            output := by
    constructor
    · intro equality
      exact congrArg Prod.snd ((Recovery.Point.Instrument.fiberBasis p.size
        Reference).symm.injective
        equality)
    · intro equality
      rw [equality]
  simpa only [same] using entry

/-- The original local affine domain gives one common scalar on every actual bank column. -/
lemma pointBankBlock_prepared_column {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size)) (bit : Fin 2)
    (words : Fin (2 ^ p.size) × Fin (2 ^ p.size)) (reference : Reference.Index)
    (allowed : bit = 1 → ∃ P : AffinePoint E,
      words.1.val = P.x.val ∧ words.2.val = P.y.val ∧
        P ≠ Q ∧ P ≠ AffinePoint.negate Q)
    (row : Recovery.Point.Instrument.FiberBank p.size Reference) :
    Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
      divisionStore finalStore bit row
        (preparedBank p Reference words reference) =
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) *
        (if row = preparedBank p Reference (nextWords E Q bit words) reference then 1 else 0) := by
  have domain : admissible E Q
      (((Recovery.Point.Instrument.fiberBasis p.size Reference).symm
        (bit, preparedBank p Reference words reference)).1) := by
    rw [Recovery.Point.Instrument.fiberBasis_symm]
    exact ⟨bit, words.1, words.2, rfl, allowed⟩
  have column := Recovery.Point.Instrument.GoodColumns.pointKraus_column
    (environment := environment) E Q Reference divisionStore finalStore
    ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm
      (bit, preparedBank p Reference words reference))
    ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, row)) domain
  exact column.trans (congrArg
    (fun value : ℂ =>
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) * value)
    (targetBank_column E Q Reference bit words reference row))

/-- An inactive source bit fixes all original binary words, including padding labels. -/
lemma pointBankBlock_inactive_column {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size))
    (words : Fin (2 ^ p.size) × Fin (2 ^ p.size)) (reference : Reference.Index)
    (row : Recovery.Point.Instrument.FiberBank p.size Reference) :
    Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
      divisionStore finalStore 0 row
        (preparedBank p Reference words reference) =
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) *
        (if row = preparedBank p Reference words reference then 1 else 0) := by
  simpa only [nextWords, if_neg Fin.zero_ne_one] using
    pointBankBlock_prepared_column E Q Reference divisionStore finalStore 0 words reference
      (fun active => (Fin.zero_ne_one active).elim) row

end

end PointBankGoodColumns
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
