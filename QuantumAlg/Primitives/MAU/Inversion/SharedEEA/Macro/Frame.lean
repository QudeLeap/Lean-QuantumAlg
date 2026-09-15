/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.RegisterFrame
import all QuantumAlg.Util.NumberTheory.SharedEEA.Length.Pair

/-!
# Exact mathematical frames at the shared Euclidean boundary

The two packed words and all original finite fields are specified at the
completed arithmetic boundary and after its final word exchange
[LYL+26, sec_EEA/sub_regshare.tex:16-26,306-313]. The values are mathematical
basis specifications; they perform no input-dependent preparation and
contain no execution program or resource witness.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.MacroBoundary

noncomputable section

open NumberTheory.SharedEEA

/-- Exact original physical frame at a macro boundary, including a terminal zero divisor. -/
def frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (iteration : Bool) : Registers modulus.size where
  firstWord := PackingBoundary.firstWord state modulus valid conserved
  secondWord := PackingBoundary.secondWord state modulus valid conserved
  coefficientLength := BitVec.ofNat modulus.size.size state.coefficient.size
  quotientLength := 0
  divisorLength := BitVec.ofNat modulus.size.size state.divisor.size
  shift := 0
  flags := ⟨false, false, false, iteration⟩
  control := false

/-- The retained coefficient length is exact in the original finite counter. -/
theorem frame_coefficientLength (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) (iteration : Bool) :
    (frame state modulus valid conserved iteration).coefficientLength.toNat =
      state.coefficient.size :=
  NumberTheory.SharedEEA.LengthRefresh.encoded_length_toNat state.coefficient modulus
    (Capacity.iteration_fields_le state modulus valid conserved).2.2.1

/-- The retained divisor length is exact, including the terminal value zero. -/
theorem frame_divisorLength (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) (iteration : Bool) :
    (frame state modulus valid conserved iteration).divisorLength.toNat = state.divisor.size :=
  NumberTheory.SharedEEA.LengthRefresh.encoded_length_toNat state.divisor modulus
    (Capacity.iteration_fields_le state modulus valid conserved).2.1

/-- Complete unrotated post-arithmetic frame after the actual zero-shift phase complements. -/
def clearedFrame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) : Registers modulus.size where
  firstWord := PackingBoundary.completedFirstWord state modulus valid conserved
  secondWord := PackingBoundary.completedSecondWord state modulus valid conserved active
  coefficientLength := BitVec.ofNat modulus.size.size state.coefficient.size
  quotientLength := 0
  divisorLength := BitVec.ofNat modulus.size.size state.divisor.size
  shift := 0
  flags := ⟨false, false, false, iteration⟩
  control := false

end

end QuantumAlg.MAU.Inversion.SharedEEA.MacroBoundary
