/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Wrapper
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Constant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Relative
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Unmatched.Resources

/-!
# Complete native execution of four supplied QSVT phase lists

The physical construction includes known constant initialization, the shared
source schedule, the unmatched parity slot, the relative imaginary phase,
and preparation and unpreparation of all three transformation ancillas.
Polynomial phase synthesis is a separate input to this construction.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)

/-- Native phase execution before converting the three plus ancillas to zero ancillas. -/
def complexCore (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false) (layout m n) :=
  (((selectedInitial (UnitarySource.model (m + n) true true false) (m + n)
    realConstant 1 imaginaryConstant 1).seq
      (unmatched (m := m) (n := n) positive phases realAngle imaginaryAngle)).seq
        (relative (UnitarySource.model (m + n) true true false) (1 + (1 + (m + n)))))

/-- The entire native word, including all initialization and all boundary gates. -/
def complexWord (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false) (layout m n) :=
  wrap (complexCore (m := m) (n := n) positive phases realAngle imaginaryAngle realConstant
    imaginaryConstant)

private def initializedBranch (phases : List ℝ) (constant : ℝ) :
    UnitaryOperator (Qubits (1 + (m + n))) :=
  ((KnownZero.circuit (m := m) (n := n) positive true phases).binaryMatrix
    (UnitarySource.interpretation U true true false)) *
    ((Shared.constantInitial (UnitarySource.model (m + n) true true false) (m + n)
      constant).binaryMatrix (UnitarySource.interpretation U true true false))

/-- The complete unwrapped word has the four original branches and the exact relative i. -/
lemma complexCore_matrix (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    (((complexCore (m := m) (n := n) positive phases realAngle imaginaryAngle
      realConstant imaginaryConstant).binaryMatrix
        (UnitarySource.interpretation U true true false)) :
        HilbertOperator (Qubits (1 + (1 + (1 + (m + n)))))) =
      Native.branchMatrix
        (Native.branchMatrix
          (initializedBranch U positive (phases.map fun a => a.1.1) realConstant)
          (initializedBranch U positive (realAngle :: phases.map fun a => a.1.2) 1))
        (Complex.I • Native.branchMatrix
          (initializedBranch U positive (phases.map fun a => a.2.1) imaginaryConstant)
          (initializedBranch U positive (imaginaryAngle :: phases.map fun a => a.2.2) 1)) := by
  rw [complexCore, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  change _ * (_ * _) = _
  rw [fourUnmatched_matrix, fourInitial_matrix]
  repeat rw [Native.branchMatrix_mul]
  rw [relative_branch_matrix]
  rfl

/-- Independent budget includes every selector, relative phase and boundary gate. -/
def complexBudget (L : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false)) :=
  unmatchedBudget (m := m) (n := n) L + 11 • eventPool (m := m) (n := n) true (.gate .singleQubit) +
    6 • eventPool (m := m) (n := n) true (.gate .cnot)

private lemma initial_events (realConstant imaginaryConstant : ℝ) :
    (selectedInitial (UnitarySource.model (m + n) true true false) (m + n)
      realConstant 1 imaginaryConstant 1).eventCost =
      4 • eventPool (m := m) (n := n) true (.gate .singleQubit) + 6 • eventPool (m := m) (n := n)
        true (.gate .cnot) :=
  selector_events (m := m) (n := n) true _ _ _ _

/-- The independent native budget is exactly the event pool of the complete executed word. -/
lemma complexWord_events (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    (complexWord (m := m) (n := n) positive phases realAngle imaginaryAngle
      realConstant imaginaryConstant).eventCost
        = complexBudget (m := m) (n := n) phases.length := by
  rw [complexWord, fourWrapper_events, complexCore, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, initial_events, fourUnmatched_events, relative_native_events]
  simp only [complexBudget, show (11 : Nat) = 4 + 1 + 6 from rfl, add_nsmul, one_nsmul,
    eventPool]
  ac_rfl

/-- Seventeen boundary and initialization steps supplement the complete unmatched source word. -/
lemma complexWord_depth (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    (complexWord (m := m) (n := n) positive phases realAngle imaginaryAngle
      realConstant imaginaryConstant).evaluatedEventDepth (fun _ => 1) =
      (unmatched (m := m) (n := n) positive phases realAngle imaginaryAngle).evaluatedEventDepth
        (fun _ => 1) +
        17 := by
  rw [complexWord, fourWrapper_depth, complexCore, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, fourInitial_depth]
  have relativeDepth : (relative (UnitarySource.model (m + n) true true false)
      (1 + (1 + (m + n)))).evaluatedEventDepth (fun _ => 1) = 1 := rfl
  rw [relativeDepth]
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
