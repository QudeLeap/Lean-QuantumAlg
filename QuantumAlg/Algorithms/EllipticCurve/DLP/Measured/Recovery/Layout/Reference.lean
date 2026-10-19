/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Common.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Fibers
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Core.Execution.Preparation.Empty

/-!
# Explicit removal of the empty quantum result-cell frame from the actual bank

The frame consists of actual classical result-cell entries. Its quantum basis is empty,
but its classical Store is retained without any quotient or subsingleton assumption. The
actual point measurement outcome and the streaming stored point projection stay in every
bank kernel. External Reference, dirty arithmetic and both control values are
unrestricted.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout
namespace Reference

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement
open Recovery.Stage.PointCoordinates

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The original authoritative cell descriptor, with all classical cells. -/
abbrev Frame (width m : Nat) := (Outer width m).frame

/-- The actual result-cell frame has no quantum systems. -/
lemma frame_systemCount_zero (width m : Nat) : (Frame width m).systemCount = 0 := by
  change ((Recovery.Point.cellEntries (readyContext width 2) 2 (2 * m)).flatMap
    RuntimeEntry.quantumWires).length = 0
  rw [Recovery.Point.cellEntries_quantumWires]
  rfl

/-- Uniqueness applies only to the quantum basis, not to the frame Store. -/
lemma frame_basis_unique (width m : Nat) (left right : (Frame width m).register.Index) :
    left = right :=
  emptyContextBasis_unique (Frame width m) (frame_systemCount_zero width m) left right

/-- An explicit basis equivalence witnesses that the quantum factor is empty. -/
def frameBasis (width m : Nat) : (Frame width m).register.Index ≃ Unit where
  toFun _ := ()
  invFun _ := emptyContextBasis (Frame width m) (frame_systemCount_zero width m)
  left_inv basis := frame_basis_unique width m _ basis
  right_inv basis := by cases basis; rfl

/-- Drop the empty quantum factor beside an arbitrary, unchanged Reference. -/
def referenceBasis (width m : Nat) (Reference : Register) :
    (ResidualReference width m Reference).Index ≃ Reference.Index where
  toFun value := value.2
  invFun value := ((frameBasis width m).symm (), value)
  left_inv value := Prod.ext (frame_basis_unique width m _ value.1) rfl
  right_inv _ := rfl

lemma referenceBasis_symm (width m : Nat) (Reference : Register) (reference : Reference.Index) :
    (referenceBasis width m Reference).symm reference =
      ((frameBasis width m).symm (), reference) := rfl

/-- The streaming bank and the original common bank differ by this empty factor only. -/
def bankBasis (width m : Nat) (Reference : Register) :
    Bank width m Reference ≃ Recovery.Reference.Measured.CommonBank.Bank width Reference :=
  (Equiv.refl (NumeratorMeasurement.context width).register.Index).prodCongr
    ((Equiv.refl (Fin 2)).prodCongr (referenceBasis width m Reference))

lemma bankBasis_apply (width m : Nat) (Reference : Register) (bank : Bank width m Reference) :
    bankBasis width m Reference bank = (bank.1, (bank.2.1, bank.2.2.2)) := rfl

lemma bankBasis_symm (width m : Nat) (Reference : Register)
    (bank : Recovery.Reference.Measured.CommonBank.Bank width Reference) :
    (bankBasis width m Reference).symm bank =
      (bank.1, (bank.2.1, ((frameBasis width m).symm (), bank.2.2))) := rfl

/-- The Reference coordinate itself is unchanged by the bank equivalence. -/
lemma bankBasis_reference (width m : Nat) (Reference : Register)
    (bank : Bank width m Reference) :
    (bankBasis width m Reference bank).2.2 = bank.2.2.2 := rfl

/-- This is exactly the nested stored point projection in the actual streaming bankBlock. -/
def streamingPointStore (width m : Nat) (stored : Store (Recovery.Layout.terminal width m)) :
    Store (MeasuredPointAddition.context width) :=
  ((Inner width).store ((Outer width m).store stored).1).1

/-- The actual point instrument loses only an explicitly empty quantum Reference factor. -/
lemma pointKraus_empty_frame {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m : Nat) (Reference : Register)
    (divisionStore finalStore : Store (MeasuredPointAddition.context p.size)) :
    (Recovery.Point.Instrument.pointKraus (environment := environment) E Q (ResidualReference
      p.size m Reference)
        divisionStore finalStore).submatrix
      (fun value : ((MeasuredPointAddition.context p.size).register.prod Reference).Index =>
        (value.1, (referenceBasis p.size m Reference).symm value.2))
      (fun value : ((MeasuredPointAddition.context p.size).register.prod Reference).Index =>
        (value.1, (referenceBasis p.size m Reference).symm value.2)) =
      Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
        divisionStore finalStore := by
  ext row column
  simp only [Matrix.submatrix_apply, referenceBasis_symm]
  rw [Recovery.Point.Instrument.pointKraus_memory_entry]
  erw [if_pos rfl, mul_one]
  rfl

/-- Both literal control blocks of the actual point kernel use the same common bank. -/
lemma pointBankBlock_empty_frame {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m : Nat) (Reference : Register)
    (divisionStore finalStore : Store (MeasuredPointAddition.context p.size)) (control : Fin 2) :
    (Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q (ResidualReference
      p.size m Reference)
        divisionStore finalStore control).submatrix
      (bankBasis p.size m Reference).symm (bankBasis p.size m Reference).symm =
      Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
        divisionStore finalStore control := by
  ext row column
  simp only [Recovery.Point.Instrument.pointBankBlock, Matrix.submatrix_apply,
    Recovery.Point.Instrument.fiberBasis_symm, bankBasis_symm]
  rw [Recovery.Point.Instrument.pointKraus_memory_entry]
  erw [if_pos rfl, mul_one]

/-- Transport the real streaming point factor without changing either stored measurement label. -/
lemma bankBlock_common {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m : Nat) (Reference : Register)
    (divisionStore : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Recovery.Layout.terminal p.size m)) (control : Fin 2) :
    (bankBlock (environment := environment) E Q m Reference divisionStore stored control).submatrix
      (bankBasis p.size m Reference).symm (bankBasis p.size m Reference).symm =
      Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
        divisionStore
        (streamingPointStore p.size m stored) control :=
  pointBankBlock_empty_frame E Q m Reference divisionStore
    (streamingPointStore p.size m stored) control

end

end Reference
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout
