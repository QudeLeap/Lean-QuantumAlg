/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.OperatorAgreement
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.PreparedSupport
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Branch.Sum
import all QuantumAlg.Core.Execution.StoredOperatorSupport

/-!
# Complete joint state of the actual measured arithmetic bodies

Each actual retained-store block has the independent target's supported
columns with the same Hadamard amplitude. The real measurement writes
all result cells, so every block has the same complete incoming quantum
source. Summing the actual stores gives the exact independent unitary
target on the prepared support, including arbitrary mixed-state and
external-reference coherences
[LYL+26, sec_point_add/sec_point_add.tex:45-105,119-122].

The support premise is discharged by the actual fixed preparation in the
complete execution theorem. No branch outcome, branch probability or
arithmetic action is supplied by a caller.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceBodyState

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem division_columns (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} (stored : Store (context modulus.size))
    (basis : (Register.prod (context modulus.size).register Reference).Index)
    (allowed : InPlacePreparedSupport.admissible modulus basis.1)
    (row : (Register.prod (context modulus.size).register Reference).Index) :
    InPlaceDivisionConjugation.operator modulus prime Reference stored row basis =
      WalshHadamard.invSqrtCard modulus.size *
        InPlaceTarget.jointOperator .division modulus prime Reference row basis := by
  obtain ⟨initial, reference⟩ := basis
  obtain ⟨value, numerator, positive, bounded, numeratorBound, same⟩ :=
    InPlacePreparedSupport.admissible_cases modulus initial allowed
  have label : initial = InPlaceTarget.preparedBasis modulus value numerator := same
  rw [label]
  exact InPlaceOperatorAgreement.division_column modulus prime value numerator
    positive bounded numeratorBound stored reference row

private theorem multiplication_columns (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} (stored : Store (context modulus.size))
    (basis : (Register.prod (context modulus.size).register Reference).Index)
    (allowed : InPlacePreparedSupport.admissible modulus basis.1)
    (row : (Register.prod (context modulus.size).register Reference).Index) :
    InPlaceMultiplicationConjugation.operator modulus prime Reference stored row basis =
      WalshHadamard.invSqrtCard modulus.size *
        InPlaceTarget.jointOperator .multiplication modulus prime Reference row basis := by
  obtain ⟨initial, reference⟩ := basis
  obtain ⟨value, numerator, positive, bounded, numeratorBound, same⟩ :=
    InPlacePreparedSupport.admissible_cases modulus initial allowed
  have label : initial = InPlaceTarget.preparedBasis modulus value numerator := same
  rw [label]
  exact InPlaceOperatorAgreement.multiplication_column modulus prime value numerator
    positive bounded numeratorBound stored reference row

/-- Actual division gives the exact independent full joint target on the prepared support. -/
theorem division_density (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference History)
    (support : ∀ basis : (Register.prod (context modulus.size).register Reference).Index,
      ¬InPlacePreparedSupport.admissible modulus basis.1 →
        state.quantumMarginal.matrix basis basis = 0) :
    ((InPlaceDivision.body modulus prime).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary (InPlaceTarget.jointOperator .division modulus prime Reference)
        state.quantumMarginal := by
  apply DensityOperator.ext
  apply full_matrix_of_stored_columns state.quantumMarginal _
    (fun basis => InPlacePreparedSupport.admissible modulus basis.1)
    (InPlaceTarget.jointOperator .division modulus prime Reference)
    (InPlaceDivisionConjugation.operator modulus prime Reference)
    (WalshHadamard.invSqrtCard modulus.size)
    (NumeratorBranchSum.coefficient_normalized modulus.size) support
    (division_columns modulus prime)
  intro stored
  have actual := InPlaceDivisionConjugation.body_matrix modulus prime state stored
  rw [NumeratorStoredFibers.source_eq_marginal] at actual
  exact actual

/-- Actual multiplication gives the same strong full-state result for its independent product. -/
theorem multiplication_density (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference History)
    (support : ∀ basis : (Register.prod (context modulus.size).register Reference).Index,
      ¬InPlacePreparedSupport.admissible modulus basis.1 →
        state.quantumMarginal.matrix basis basis = 0) :
    ((InPlaceMultiplication.body modulus prime).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (InPlaceTarget.jointOperator .multiplication modulus prime Reference)
        state.quantumMarginal := by
  apply DensityOperator.ext
  apply full_matrix_of_stored_columns state.quantumMarginal _
    (fun basis => InPlacePreparedSupport.admissible modulus basis.1)
    (InPlaceTarget.jointOperator .multiplication modulus prime Reference)
    (InPlaceMultiplicationConjugation.operator modulus prime Reference)
    (WalshHadamard.invSqrtCard modulus.size)
    (NumeratorBranchSum.coefficient_normalized modulus.size) support
    (multiplication_columns modulus prime)
  intro stored
  have actual := InPlaceMultiplicationConjugation.body_matrix modulus prime state stored
  rw [NumeratorStoredFibers.source_eq_marginal] at actual
  exact actual

end

end QuantumAlg.MeasuredUncompute.InPlaceBodyState
