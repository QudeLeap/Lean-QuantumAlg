/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Invariant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Util.Complex

/-!
# Projected source products and boundary cases

These are the original singular-value targets and their degree-zero and degree-one
sanity cases, expressed using intrinsic source operators
[GSLW19, BlockHam.tex:768-887].
-/

section
namespace QuantumAlg.QSP.MultiQubit.QSVT
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The source-level projected block `Π_out U_Φ Π_in` from the singular-value
transformation theorem [GSLW19, BlockHam.tex:768-849]. -/
noncomputable def sourceProjectedBlock {N : Nat} (output input : OrthogonalProjector N)
    (V : UnitaryOperator (Qubits N)) : HilbertOperator (Qubits N) :=
  output.op * V * input.op

/-- Vectors in the input-projector complement are killed by the projected block
`Π_out V Π_in`. -/
theorem sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support {N : Nat}
    (output input : OrthogonalProjector N) (V : UnitaryOperator (Qubits N))
    (ψ : HilbertVector (Qubits N))
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement input) ψ = ψ) :
    HilbertOperator.applyVec (sourceProjectedBlock output input V) ψ = 0 := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self input hpsi]
  simp [HilbertOperator.applyVec]

/-- Applying a Hilbert operator commutes with a list-indexed vector sum. -/
private theorem hilbertOperator_applyVec_list_sum {N : Nat}
    (A : HilbertOperator (Qubits N)) (v : List (HilbertVector (Qubits N))) :
    HilbertOperator.applyVec A v.sum =
      (v.map fun ψ => HilbertOperator.applyVec A ψ).sum := by
  induction v with
  | nil =>
      simp [HilbertOperator.applyVec]
  | cons ψ rest ih =>
      simp [HilbertOperator.applyVec_add, ih]

/-- If two Hilbert operators agree on an indexed family, they agree on every
finite linear combination of that family. -/
private theorem hilbertOperator_applyVec_eq_on_list_linearCombination {N : Nat}
    {ι : Type} (vec : ι -> HilbertVector (Qubits N))
    {A B : HilbertOperator (Qubits N)}
    (h : ∀ i : ι, HilbertOperator.applyVec A (vec i) =
      HilbertOperator.applyVec B (vec i))
    (terms : List (ℂ × ι)) :
    HilbertOperator.applyVec A ((terms.map fun term => term.1 • vec term.2).sum) =
      HilbertOperator.applyVec B ((terms.map fun term => term.1 • vec term.2).sum) := by
  induction terms with
  | nil =>
      simp [HilbertOperator.applyVec]
  | cons term rest ih =>
      rcases term with ⟨c, i⟩
      simp [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul, h i, ih]

namespace SourceLeftKernelSingularBlock

/-- Left-kernel input-side vectors lie in the right-projector complement, hence
the source projected block kills them. -/
theorem sourceProjectedBlock_applyVec_rightPerp_eq_zero {N : Nat}
    {U : UnitaryOperator (Qubits N)} {left right output : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right)
    (V : UnitaryOperator (Qubits N)) :
    HilbertOperator.applyVec (sourceProjectedBlock output right V) block.rightPerp = 0 :=
  sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support output right V
    block.rightPerp block.right_perp_support

end SourceLeftKernelSingularBlock

namespace SourceComplementSingularBlock

/-- Fully complementary input-side vectors lie in the right-projector complement,
hence the source projected block kills them. -/
theorem sourceProjectedBlock_applyVec_rightPerp_eq_zero {N : Nat}
    {U : UnitaryOperator (Qubits N)} {left right output : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right)
    (V : UnitaryOperator (Qubits N)) :
    HilbertOperator.applyVec (sourceProjectedBlock output right V) block.rightPerp = 0 :=
  sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support output right V
    block.rightPerp block.right_perp_support

end SourceComplementSingularBlock

/-- Source-level singular-value correctness target for `U_Φ`, before adding the
one-ancilla controlled implementation used by the public real-polynomial
statement [GSLW19, BlockHam.tex:768-849]. -/
def SourceProjectedQSVTBlockCorrectness {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (L : ℕ) (P : Polynomial ℂ)
    (phases : List ℝ) : Prop :=
  sourceProjectedBlock (projectedOutputProjector left right L) right
      (Native.sourceWord U left right phases) =
    singularValuePolynomial right L P (projectedUnitaryBlock left right U)

/-- Degree-one base case of the source-level projected QSVT theorem.  The
single zero phase realizes the original projected block, corresponding to
`P(X)=X`. -/
theorem sourceProjectedQSVTBlockCorrectness_X_single_zero {N : Nat}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N) :
    SourceProjectedQSVTBlockCorrectness U left right 1 (Polynomial.X : Polynomial ℂ) [0] := by
  unfold SourceProjectedQSVTBlockCorrectness sourceProjectedBlock
  simp [Native.sourceWord, projectedOutputProjector, projectorPhaseOp, projectorPhaseMatrix,
    OrthogonalProjector.complement, singularValuePolynomial_X_one, projectedUnitaryBlock]

/-- Degree-zero source-level projected QSVT sanity case: the empty phase sequence
realizes the constant polynomial `1` on the input projector. -/
theorem sourceProjectedQSVTBlockCorrectness_one_nil {N : Nat}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N) :
    SourceProjectedQSVTBlockCorrectness U left right 0 (Polynomial.C 1 : Polynomial ℂ) [] := by
  unfold SourceProjectedQSVTBlockCorrectness sourceProjectedBlock singularValuePolynomial
    evenSingularValuePolynomial polynomialOperator
  simp [Native.sourceWord, projectedOutputProjector,
    projectedUnitaryBlock, right.idempotent]

/-- Negate every source phase.  The controlled real-polynomial construction uses
the direct sum of `U_Φ` and `U_{-Φ}` [GSLW19, BlockHam.tex:851-887]. -/
def negPhases (phases : List ℝ) : List ℝ :=
  phases.map fun φ => -φ

@[simp]
theorem negPhases_length (phases : List ℝ) :
    (negPhases phases).length = phases.length := by
  simp [negPhases]

theorem singularSignalRProduct_negPhases_zero_zero (phases : List ℝ) (x : ℝ) :
    singularSignalRProduct (negPhases phases) x 0 0 =
      star (singularSignalRProduct phases x 0 0) := by
  simpa [negPhases] using singularSignalRProduct_map_neg_zero_zero phases x

theorem phaseProduct_negPhases (phases : List ℝ) :
    phaseProduct (negPhases phases) = star (phaseProduct phases) := by
  induction phases with
  | nil =>
      simp [negPhases]
  | cons φ phases ih =>
      simp only [negPhases, List.map_cons, phaseProduct_cons]
      change Complex.exp ((-φ : ℝ) * Complex.I) *
          phaseProduct (negPhases phases) =
        star (Complex.exp (φ * Complex.I) * phaseProduct phases)
      rw [ih]
      rw [star_mul]
      rw [mul_comm (star (phaseProduct phases)) (star (Complex.exp (φ * Complex.I)))]
      have hexp :
          star (Complex.exp (φ * Complex.I)) =
            Complex.exp ((-φ : ℝ) * Complex.I) := by
        simpa using conj_exp_I φ
      rw [hexp]

end QuantumAlg.QSP.MultiQubit.QSVT
end
