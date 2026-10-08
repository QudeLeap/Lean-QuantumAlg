/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Phases
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Phases

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Invariant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Pair
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Assembly of projected QSVT source correctness

Singular-sector actions assemble into the original polynomial operator equality
through finite spanning families [GSLW19, BlockHam.tex:583-849].
-/

section
namespace QuantumAlg.QSP.MultiQubit.QSVT
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SourceUnitSingularBlock

/-- Unit singular block, even output side: a nonempty phase certificate drives
the source alternating phase sequence by the scalar `P(1)` on the right vector
[GSLW19, BlockHam.tex:655-671,768-849]. -/
theorem sourceAlternating_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    (Native.sourceWord U left right
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec =
      P.eval (1 : Complex) • block.rightVec := by
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 0 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).1 hlen
  rw [hact, phaseProduct_projectedPhases_eq_certificate_eval_one certificate init last hφs]

/-- Unit singular block, odd output side: a nonempty phase certificate drives
the source alternating phase sequence by the scalar `P(1)` on the left vector
[GSLW19, BlockHam.tex:655-671,768-849]. -/
theorem sourceAlternating_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    (Native.sourceWord U left right
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec =
      P.eval (1 : Complex) • block.leftVec := by
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 1 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).2 hlen
  rw [hact, phaseProduct_projectedPhases_eq_certificate_eval_one certificate init last hφs]

/-- Unit singular block, even output side after the source projected block:
projecting preserves the right-vector component [GSLW19, BlockHam.tex:655-671,
768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (1 : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((Native.sourceWord U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (1 : Complex) • block.rightVec
  rw [block.sourceAlternating_projectedPhases_applyVec_rightVec_even certificate init last hφs hd]
  rw [HilbertOperator.applyVec_smul, block.right_support]

/-- Unit singular block, odd output side after the source projected block:
projecting preserves the left-vector component [GSLW19, BlockHam.tex:655-671,
768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (1 : Complex) • block.leftVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((Native.sourceWord U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (1 : Complex) • block.leftVec
  rw [block.sourceAlternating_projectedPhases_applyVec_rightVec_odd certificate init last hφs hd]
  rw [HilbertOperator.applyVec_smul, block.left_support]

/-- Unit singular block, even output side for the negated projected phase list:
the scalar is `(conjP P)(1)`, matching the second half of the source real
averaging construction [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (1 : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((Native.sourceWord U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (1 : Complex) • block.rightVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 0 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).1 hlen
  rw [hact, phaseProduct_negProjectedPhases_eq_conjP_eval_one certificate init last hφs]
  rw [HilbertOperator.applyVec_smul, block.right_support]

/-- Unit singular block, odd output side for the negated projected phase list
[GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (1 : Complex) • block.leftVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((Native.sourceWord U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (1 : Complex) • block.leftVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 1 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).2 hlen
  rw [hact, phaseProduct_negProjectedPhases_eq_conjP_eval_one certificate init last hφs]
  rw [HilbertOperator.applyVec_smul, block.left_support]

end SourceUnitSingularBlock

namespace SourceTwoDimensionalSingularBlock

/-- Nontrivial singular block, even output side: the projected-QSVT phase list
drives the right singular vector with scalar `P(σ)` on the right-vector
component [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceAlternating_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    (Native.sourceWord U left right
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec =
      P.eval (block.σ : Complex) • block.rightVec +
        singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          block.σ 1 0 • block.rightPerp := by
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 0 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).1 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          block.σ 0 0 =
        P.eval (block.σ : Complex) := by
    rw [hφs]
    rw [singularSignalRProduct_projectedPhases_zero_zero_eq_qspW]
    simpa [hφs] using
      certificate.qspW_zero_zero (x := block.σ) block.sigma_mem_unitInterval
  rw [hentry]

/-- Nontrivial singular block, odd output side: the projected-QSVT phase list
drives the right singular vector with scalar `P(σ)` on the left-vector
component [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceAlternating_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    (Native.sourceWord U left right
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec =
      P.eval (block.σ : Complex) • block.leftVec +
        singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          block.σ 1 0 • block.leftPerp := by
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 1 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).2 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          block.σ 0 0 =
        P.eval (block.σ : Complex) := by
    rw [hφs]
    rw [singularSignalRProduct_projectedPhases_zero_zero_eq_qspW]
    simpa [hφs] using
      certificate.qspW_zero_zero (x := block.σ) block.sigma_mem_unitInterval
  rw [hentry]

/-- Nontrivial singular block, even output side after the source projected block:
the perpendicular component is removed by the output projector, leaving the
desired scalar `P(σ)` action [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (block.σ : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((Native.sourceWord U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (block.σ : Complex) • block.rightVec
  rw [block.sourceAlternating_projectedPhases_applyVec_rightVec_even certificate init last hφs hd]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.right_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      right block.right_perp_support]
  simp

/-- Nontrivial singular block, odd output side after the source projected block:
the perpendicular component is removed by the output projector, leaving the
desired scalar `P(σ)` action [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (block.σ : Complex) • block.leftVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((Native.sourceWord U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (block.σ : Complex) • block.leftVec
  rw [block.sourceAlternating_projectedPhases_applyVec_rightVec_odd certificate init last hφs hd]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.left_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

/-- Nontrivial singular block, even output side for the negated projected phase
list.  The perpendicular component is again removed by the output projector,
leaving `(conjP P)(σ)` [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (block.σ : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((Native.sourceWord U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (block.σ : Complex) • block.rightVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 0 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).1 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          block.σ 0 0 =
        (conjP P).eval (block.σ : Complex) :=
    singularSignalRProduct_negProjectedPhases_zero_zero_eq_conjP
      certificate init last block.σ hφs block.sigma_mem_unitInterval
  rw [hentry]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.right_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      right block.right_perp_support]
  simp

/-- Nontrivial singular block, odd output side for the negated projected phase
list [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (block.σ : Complex) • block.leftVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((Native.sourceWord U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (block.σ : Complex) • block.leftVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 1 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).2 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          block.σ 0 0 =
        (conjP P).eval (block.σ : Complex) :=
    singularSignalRProduct_negProjectedPhases_zero_zero_eq_conjP
      certificate init last block.σ hφs block.sigma_mem_unitInterval
  rw [hentry]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.left_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

end SourceTwoDimensionalSingularBlock

namespace SourceRightKernelSingularBlock

/-- Right-kernel block, even output side after projection: the scalar is the
source QSP value `P(0)` [GSLW19, BlockHam.tex:599-611,655-716,768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (0 : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((Native.sourceWord U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (0 : Complex) • block.rightVec
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 0 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).1 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          0 0 0 =
        P.eval (0 : Complex) := by
    rw [hφs]
    rw [singularSignalRProduct_projectedPhases_zero_zero_eq_qspW]
    simpa [hφs] using certificate.qspW_zero_zero (x := 0) (by norm_num)
  rw [hentry]
  rw [HilbertOperator.applyVec_smul, block.right_support]

/-- Right-kernel block, odd output side after projection: the local vector lies
in the left complement, so the output projector removes it [GSLW19,
BlockHam.tex:599-611,655-716,768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      0 := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((Native.sourceWord U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) = 0
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 1 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).2 hlen
  rw [hact]
  rw [HilbertOperator.applyVec_smul,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

/-- Right-kernel block, even output side for the negated projected phase list:
the scalar is `(conjP P)(0)` [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (0 : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((Native.sourceWord U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (0 : Complex) • block.rightVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 0 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).1 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          0 0 0 =
        (conjP P).eval (0 : Complex) :=
    singularSignalRProduct_negProjectedPhases_zero_zero_eq_conjP
      certificate init last 0 hφs (by norm_num)
  rw [hentry]
  rw [HilbertOperator.applyVec_smul, block.right_support]

/-- Right-kernel block, odd output side for the negated projected phase list:
the local vector lies in the left complement, so the output projector removes
it [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (Native.sourceWord U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      0 := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((Native.sourceWord U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) = 0
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 1 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).2 hlen
  rw [hact]
  rw [HilbertOperator.applyVec_smul,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

theorem projectedUnitaryBlock_applyVec_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U) block.rightVec = 0 := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  change HilbertOperator.applyVec left.op (U.applyVec block.rightVec) = 0
  rw [block.U_right]
  exact OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
    left block.left_perp_support

theorem gram_applyVec_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) :
    HilbertOperator.applyVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U)
        block.rightVec =
      (0 : Complex) • block.rightVec := by
  rw [HilbertOperator.mul_applyVec, block.projectedUnitaryBlock_applyVec_rightVec]
  simp [HilbertOperator.applyVec]

theorem singularValuePolynomial_applyVec_rightVec_of_even {N L : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (0 : Complex) • block.rightVec := by
  unfold singularValuePolynomial evenSingularValuePolynomial
  rw [if_pos hL]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support,
    polynomialOperator_applyVec_of_eigenvector (evenSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      (0 : Complex) block.rightVec block.gram_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.right_support]
  have heven := evenSquareQuotient_eval_sq_of_hasParity hL hP (0 : Complex)
  have heven0 :
      (evenSquareQuotient P).eval (0 : Complex) = P.eval (0 : Complex) := by
    simpa using heven
  rw [heven0]

theorem singularValuePolynomial_applyVec_rightVec_of_odd {N L : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (_hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      0 := by
  unfold singularValuePolynomial oddSingularValuePolynomial
  have hnot : ¬ L % 2 = 0 := by omega
  rw [if_neg hnot]
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      (0 : Complex) block.rightVec block.gram_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.projectedUnitaryBlock_applyVec_rightVec]
  simp

end SourceRightKernelSingularBlock

/- The singular-value theorem will be finished by proving
`SourceProjectedQSVTBlockCorrectness` directly from the source invariant-block
decomposition.  A previous matrix-entry-shaped interface was deliberately
removed here: individual standard-basis entries are not, in general, evaluations
of one singular value. -/

/-- Correct source-facing assembly point for `lemma:singInvDec` followed by
`thm:singValTransformation`: the local singular-block decomposition is recorded
separately from the final block equality.  Unlike a standard matrix-entry
interface, this shape matches the source proof, which works in the invariant
singular-vector blocks before assembling the operator equality [GSLW19,
BlockHam.tex:655-736,768-849]. -/
structure SourceSingularInvariantBlockAssembly {N d : Nat} {P Q : Polynomial ℂ}
    (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate :
      ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) where
  /-- Source singular-invariant decomposition used for the blockwise proof. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  block_correctness :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)

/-- Once the invariant-block assembly proves the projected block equality, it
feeds the source-level QSVT target directly.  The remaining hard work is to
construct the assembly from the blockwise scalar-QSP proof, not from standard
matrix entries [GSLW19, BlockHam.tex:655-736,768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_invariantBlockAssembly {N d : Nat}
    {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate :
      ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (assembly : SourceSingularInvariantBlockAssembly U left right certificate) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  assembly.block_correctness

/-- Extensional assembly contract for the final step of
`thm:singValTransformation`: a source invariant-vector family is sufficient if
it spans by operator action and each vector satisfies the local projected-QSVT
action equality [GSLW19, BlockHam.tex:655-736,768-849]. -/
structure SourceProjectedQSVTSpanningFamily {N d : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (P : Polynomial ℂ) (phases : List ℝ) where
  /-- Index type for source invariant vectors. -/
  ι : Type
  /-- Source invariant vector selected by an index. -/
  vec : ι -> HilbertVector (Qubits N)
  ext :
    ∀ {A B : HilbertOperator (Qubits N)},
      (∀ i : ι, HilbertOperator.applyVec A (vec i) =
        HilbertOperator.applyVec B (vec i)) -> A = B
  action_eq :
    ∀ i : ι,
      HilbertOperator.applyVec
          (sourceProjectedBlock (projectedOutputProjector left right d) right
            (Native.sourceWord U left right phases))
          (vec i) =
        HilbertOperator.applyVec
          (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
          (vec i)

/-- Basis-span form of the source invariant-vector family.  Instead of asking
for an abstract operator-extensionality proof, it records a finite family of
vectors and a decomposition of every Gram-eigenbasis vector into that family.
This is the form closest to `lemma:singInvDec` when zero singular subspaces are
split into projector and complement parts [GSLW19, BlockHam.tex:583-613,
655-736,768-849]. -/
structure SourceProjectedQSVTBasisSpanFamily {N d : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (P : Polynomial ℂ) (phases : List ℝ) where
  /-- Index type for the source vectors spanning the Gram eigenbasis. -/
  ι : Type
  /-- Source vector selected by an index. -/
  vec : ι -> HilbertVector (Qubits N)
  /-- Finite linear combination of source vectors for each Gram-eigenbasis vector. -/
  combination : (Qubits N).Index -> List (ℂ × ι)
  basis_eq :
    ∀ i : (Qubits N).Index,
      (projectedUnitaryBlockGramEigenbasis left right U i :
          HilbertVector (Qubits N)) =
        ((combination i).map fun term => term.1 • vec term.2).sum
  action_eq :
    ∀ i : ι,
      HilbertOperator.applyVec
          (sourceProjectedBlock (projectedOutputProjector left right d) right
            (Native.sourceWord U left right phases))
          (vec i) =
        HilbertOperator.applyVec
          (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
          (vec i)

/-- A basis-span source family gives the abstract spanning-family contract. -/
noncomputable def sourceProjectedQSVTSpanningFamilyOfBasisSpanFamily {N d : Nat}
    {P : Polynomial ℂ} {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    {phases : List ℝ}
    (family : SourceProjectedQSVTBasisSpanFamily (d := d) U left right P phases) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right P phases where
  ι := family.ι
  vec := family.vec
  ext := by
    intro A B h
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis
      (projectedUnitaryBlockGramEigenbasis left right U)
    intro i
    rw [family.basis_eq i]
    exact hilbertOperator_applyVec_eq_on_list_linearCombination family.vec h
      (family.combination i)
  action_eq := family.action_eq

/-- Convert a source invariant-vector spanning family into the global projected
QSVT block equality.  The remaining source work is to build this family from
`lemma:singInvDec`'s unit, nontrivial, kernel, and complement sectors. -/
theorem sourceProjectedQSVTBlockCorrectness_of_spanningFamily {N d : Nat}
    {P : Polynomial ℂ} (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (phases : List ℝ)
    (family : SourceProjectedQSVTSpanningFamily (d := d) U left right P phases) :
    SourceProjectedQSVTBlockCorrectness U left right d P phases := by
  unfold SourceProjectedQSVTBlockCorrectness
  exact family.ext family.action_eq

/-- Basis-span source families prove the global projected-QSVT block equality. -/
theorem sourceProjectedQSVTBlockCorrectness_of_basisSpanFamily {N d : Nat}
    {P : Polynomial ℂ} (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (phases : List ℝ)
    (family : SourceProjectedQSVTBasisSpanFamily (d := d) U left right P phases) :
    SourceProjectedQSVTBlockCorrectness U left right d P phases :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right phases
    (sourceProjectedQSVTSpanningFamilyOfBasisSpanFamily (d := d) family)

/-- The tagged source-side input vectors from `lemma:singInvDec`: right singular
vectors for unit, nontrivial, and right-kernel sectors, and right-complement
vectors for the nontrivial, left-kernel, and fully complementary sectors
[GSLW19, BlockHam.tex:583-613,655-736]. -/
inductive SourceSingularInvariantVector {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (decomposition : SourceSingularInvariantDecomposition U left right) : Type where
  | unit : Fin decomposition.unitBlockCount -> SourceSingularInvariantVector decomposition
  | twoRight :
      Fin decomposition.twoDimensionalBlockCount -> SourceSingularInvariantVector decomposition
  | twoRightPerp :
      Fin decomposition.twoDimensionalBlockCount -> SourceSingularInvariantVector decomposition
  | rightKernel :
      Fin decomposition.rightKernelBlockCount -> SourceSingularInvariantVector decomposition
  | leftKernel :
      Fin decomposition.leftKernelBlockCount -> SourceSingularInvariantVector decomposition
  | complement :
      Fin decomposition.complementBlockCount -> SourceSingularInvariantVector decomposition
deriving Fintype

namespace SourceSingularInvariantVector

/-- The actual source input vector represented by a sector tag. -/
def vec {N : Nat} {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    {decomposition : SourceSingularInvariantDecomposition U left right} :
    SourceSingularInvariantVector decomposition -> NormalizedVector (Qubits N)
  | unit i => (decomposition.unitBlock i).rightVec
  | twoRight i => (decomposition.twoDimensionalBlock i).rightVec
  | twoRightPerp i => (decomposition.twoDimensionalBlock i).rightPerp
  | rightKernel i => (decomposition.rightKernelBlock i).rightVec
  | leftKernel i => (decomposition.leftKernelBlock i).rightPerp
  | complement i => (decomposition.complementBlock i).rightPerp

end SourceSingularInvariantVector

/-- Source-side local invariant vectors, carrying the actual block certificate
instead of a count-indexed decomposition.  This is the direct Lean analogue of
the block list produced by `lemma:singInvDec` [GSLW19, BlockHam.tex:583-613,
655-736]. -/
inductive SourceSingularInvariantLocalVector {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) : Type where
  | unit : SourceUnitSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | twoRight : SourceTwoDimensionalSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | twoRightPerp : SourceTwoDimensionalSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | rightKernel : SourceRightKernelSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | scaledRightKernel (coefficient : ℂ) :
      SourceRightKernelSingularBlock U left right ->
        SourceSingularInvariantLocalVector U left right
  | leftKernel : SourceLeftKernelSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | scaledLeftKernel (coefficient : ℂ) :
      SourceLeftKernelSingularBlock U left right ->
        SourceSingularInvariantLocalVector U left right
  | complement : SourceComplementSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | scaledComplement (coefficient : ℂ) :
      SourceComplementSingularBlock U left right ->
        SourceSingularInvariantLocalVector U left right
  | inputComplement (rightPerp : HilbertVector (Qubits N))
      (right_perp_support :
        HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp =
          rightPerp) :
      SourceSingularInvariantLocalVector U left right
  | zero : SourceSingularInvariantLocalVector U left right

namespace SourceSingularInvariantLocalVector

/-- The source input vector represented by a local block tag. -/
def vec {N : Nat} {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N} :
    SourceSingularInvariantLocalVector U left right -> HilbertVector (Qubits N)
  | unit block => block.rightVec
  | twoRight block => block.rightVec
  | twoRightPerp block => block.rightPerp
  | rightKernel block => block.rightVec
  | scaledRightKernel coefficient block => coefficient • block.rightVec
  | leftKernel block => block.rightPerp
  | scaledLeftKernel coefficient block => coefficient • block.rightPerp
  | complement block => block.rightPerp
  | scaledComplement coefficient block => coefficient • block.rightPerp
  | inputComplement rightPerp _ => rightPerp
  | zero => 0

/-- Forget a count-indexed source sector tag into the corresponding local block
tag.  This lets the source direct-sum theorem feed the later local-sector
coverage interface without duplicating action proofs. -/
def ofDecompositionVector {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    {decomposition : SourceSingularInvariantDecomposition U left right} :
    SourceSingularInvariantVector decomposition ->
      SourceSingularInvariantLocalVector U left right
  | SourceSingularInvariantVector.unit i =>
      SourceSingularInvariantLocalVector.unit (decomposition.unitBlock i)
  | SourceSingularInvariantVector.twoRight i =>
      SourceSingularInvariantLocalVector.twoRight (decomposition.twoDimensionalBlock i)
  | SourceSingularInvariantVector.twoRightPerp i =>
      SourceSingularInvariantLocalVector.twoRightPerp (decomposition.twoDimensionalBlock i)
  | SourceSingularInvariantVector.rightKernel i =>
      SourceSingularInvariantLocalVector.rightKernel (decomposition.rightKernelBlock i)
  | SourceSingularInvariantVector.leftKernel i =>
      SourceSingularInvariantLocalVector.leftKernel (decomposition.leftKernelBlock i)
  | SourceSingularInvariantVector.complement i =>
      SourceSingularInvariantLocalVector.complement (decomposition.complementBlock i)

@[simp]
theorem vec_ofDecompositionVector {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    {decomposition : SourceSingularInvariantDecomposition U left right}
    (tag : SourceSingularInvariantVector decomposition) :
    vec (ofDecompositionVector (U := U) (left := left) (right := right) tag) =
      (SourceSingularInvariantVector.vec tag : HilbertVector (Qubits N)) := by
  cases tag <;> rfl

/-- Local source-sector action equality for every invariant vector in
`lemma:singInvDec`, after the W-to-R phase conversion has produced the projected
phase list [GSLW19, BlockHam.tex:655-736,768-849]. -/
theorem action_eq {N d : Nat} {P Q : Polynomial ℂ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    ∀ tag : SourceSingularInvariantLocalVector U left right,
      HilbertOperator.applyVec
          (sourceProjectedBlock (projectedOutputProjector left right d) right
            (Native.sourceWord U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
          (vec tag) =
        HilbertOperator.applyVec
          (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
          (vec tag) := by
  intro tag
  cases tag with
  | unit block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · rw [
          SourceUnitSingularBlock.sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block P hd hP]
      · have hdodd : d % 2 = 1 := by omega
        rw [
          SourceUnitSingularBlock.sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
            block certificate init last hφs hdodd,
          SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block P hdodd hP]
  | twoRight block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · open SourceTwoDimensionalSingularBlock in
        rw [
          sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block P hd hP]
      · have hdodd : d % 2 = 1 := by omega
        open SourceTwoDimensionalSingularBlock in
        rw [
          sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
            block certificate init last hφs hdodd,
          SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block P hdodd hP]
  | twoRightPerp block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            block.rightPerp = 0 :=
          sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
            (projectedOutputProjector left right d) right
            (Native.sourceWord U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
            block.rightPerp block.right_perp_support
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) P block.right_perp_support]
  | rightKernel block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · open SourceRightKernelSingularBlock in
        rw [
          sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block P hd hP]
      · have hdodd : d % 2 = 1 := by omega
        open SourceRightKernelSingularBlock in
        rw [
          sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd block certificate hdodd,
          SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block P hdodd hP]
  | scaledRightKernel coefficient block =>
      dsimp [vec]
      have hblock :
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightVec =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightVec := by
        by_cases hd : d % 2 = 0
        · open SourceRightKernelSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
              block certificate init last hφs hd,
            SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
              block P hd hP]
        · have hdodd : d % 2 = 1 := by omega
          open SourceRightKernelSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd block certificate hdodd,
            SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
              block P hdodd hP]
      simpa only [HilbertOperator.applyVec_smul] using
        congrArg (fun v : HilbertVector (Qubits N) => coefficient • v) hblock
  | leftKernel block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            block.rightPerp = 0 :=
          SourceLeftKernelSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
            block
            (Native.sourceWord U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) P block.right_perp_support]
  | scaledLeftKernel coefficient block =>
      dsimp [vec]
      have hblock :
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightPerp := by
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp = 0 :=
            SourceLeftKernelSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
              block
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) P block.right_perp_support]
      simpa only [HilbertOperator.applyVec_smul] using
        congrArg (fun v : HilbertVector (Qubits N) => coefficient • v) hblock
  | complement block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            block.rightPerp = 0 :=
          SourceComplementSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
            block
            (Native.sourceWord U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) P block.right_perp_support]
  | scaledComplement coefficient block =>
      dsimp [vec]
      have hblock :
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightPerp := by
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp = 0 :=
            SourceComplementSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
              block
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) P block.right_perp_support]
      simpa only [HilbertOperator.applyVec_smul] using
        congrArg (fun v : HilbertVector (Qubits N) => coefficient • v) hblock
  | inputComplement rightPerp hright_perp =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            rightPerp = 0 :=
          sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
            (projectedOutputProjector left right d) right
            (Native.sourceWord U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
            rightPerp hright_perp
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) P hright_perp]
  | zero =>
      simp [vec, HilbertOperator.applyVec]

/-- Local source-sector action equality for the negated projected phase list.
This is the source-level half of the `U_{-Φ}` branch used in
`cor:matchingParity` [GSLW19, BlockHam.tex:851-887]. -/
theorem action_eq_negProjectedPhases {N d : Nat} {P Q : Polynomial ℂ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    ∀ tag : SourceSingularInvariantLocalVector U left right,
      HilbertOperator.applyVec
          (sourceProjectedBlock (projectedOutputProjector left right d) right
            (Native.sourceWord U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
          (vec tag) =
        HilbertOperator.applyVec
          (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
          (vec tag) := by
  intro tag
  cases tag with
  | unit block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · rw [
          SourceUnitSingularBlock.sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block (conjP P) hd hP.conjP]
      · have hdodd : d % 2 = 1 := by omega
        rw [
          SourceUnitSingularBlock.sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
            block certificate init last hφs hdodd,
          SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block (conjP P) hdodd hP.conjP]
  | twoRight block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · open SourceTwoDimensionalSingularBlock in
        rw [
          sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block (conjP P) hd hP.conjP]
      · have hdodd : d % 2 = 1 := by omega
        open SourceTwoDimensionalSingularBlock in
        rw [
          sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
            block certificate init last hφs hdodd,
          SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block (conjP P) hdodd hP.conjP]
  | twoRightPerp block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
            block.rightPerp = 0 :=
          sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
            (projectedOutputProjector left right d) right
            (Native.sourceWord U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            block.rightPerp block.right_perp_support
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) (conjP P) block.right_perp_support]
  | scaledComplement coefficient block =>
      dsimp [vec]
      have hblock :
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (negPhases
                    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
              block.rightPerp =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P)
                (projectedUnitaryBlock left right U))
              block.rightPerp := by
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (negPhases
                    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
              block.rightPerp = 0 :=
            SourceComplementSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
              block
              (Native.sourceWord U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d (conjP P)
                  (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) (conjP P)
              block.right_perp_support]
      simpa only [HilbertOperator.applyVec_smul] using
        congrArg (fun v : HilbertVector (Qubits N) => coefficient • v) hblock
  | rightKernel block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · open SourceRightKernelSingularBlock in
        rw [
          sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block (conjP P) hd hP.conjP]
      · have hdodd : d % 2 = 1 := by omega
        open SourceRightKernelSingularBlock in
        rw [
          sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd block certificate hdodd,
          SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block (conjP P) hdodd hP.conjP]
  | scaledRightKernel coefficient block =>
      dsimp [vec]
      have hblock :
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (negPhases
                    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
              block.rightVec =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P)
                (projectedUnitaryBlock left right U))
              block.rightVec := by
        by_cases hd : d % 2 = 0
        · open SourceRightKernelSingularBlock in
          rw [
            sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
              block certificate init last hφs hd,
            SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
              block (conjP P) hd hP.conjP]
        · have hdodd : d % 2 = 1 := by omega
          open SourceRightKernelSingularBlock in
          rw [
            sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
              block certificate hdodd,
            SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
              block (conjP P) hdodd hP.conjP]
      simpa only [HilbertOperator.applyVec_smul] using
        congrArg (fun v : HilbertVector (Qubits N) => coefficient • v) hblock
  | leftKernel block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
            block.rightPerp = 0 :=
          SourceLeftKernelSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
            block
            (Native.sourceWord U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) (conjP P) block.right_perp_support]
  | scaledLeftKernel coefficient block =>
      dsimp [vec]
      have hblock :
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (negPhases
                    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
              block.rightPerp =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P)
                (projectedUnitaryBlock left right U))
              block.rightPerp := by
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (negPhases
                    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
              block.rightPerp = 0 :=
            SourceLeftKernelSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
              block
              (Native.sourceWord U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d (conjP P)
                  (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) (conjP P)
              block.right_perp_support]
      simpa only [HilbertOperator.applyVec_smul] using
        congrArg (fun v : HilbertVector (Qubits N) => coefficient • v) hblock
  | complement block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
            block.rightPerp = 0 :=
          SourceComplementSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
            block
            (Native.sourceWord U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) (conjP P) block.right_perp_support]
  | inputComplement rightPerp hright_perp =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
            rightPerp = 0 :=
          sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
            (projectedOutputProjector left right d) right
            (Native.sourceWord U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            rightPerp hright_perp
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
              rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) (conjP P) hright_perp]
  | zero =>
      simp [vec, HilbertOperator.applyVec]

end SourceSingularInvariantLocalVector

/-- Basis-span coverage using directly carried source local blocks. -/
structure SourceSingularInvariantLocalBasisSpanCoverage {N : Nat}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N) where
  /-- Linear-combination coverage of every Gram-eigenbasis vector by local sectors. -/
  combination :
    (Qubits N).Index -> List (ℂ × SourceSingularInvariantLocalVector U left right)
  basis_eq :
    ∀ i : (Qubits N).Index,
      (projectedUnitaryBlockGramEigenbasis left right U i :
          HilbertVector (Qubits N)) =
        ((combination i).map fun term =>
          term.1 • SourceSingularInvariantLocalVector.vec term.2).sum

/-- Coverage by an orthonormal basis whose vectors are all source local sectors.
This is the closest Lean interface to the source proof after the orthogonality
checks in Table 2 and the final orthogonal-complement construction
[GSLW19, BlockHam.tex:615-736]. -/
structure SourceSingularInvariantLocalOrthonormalBasisCoverage {N : Nat}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N) where
  /-- Index type for the orthonormal source-sector basis. -/
  ι : Type
  /-- Finiteness instance for the orthonormal source-sector basis. -/
  fintype : Fintype ι
  /-- Orthonormal basis whose vectors are tagged by source sectors. -/
  basis : OrthonormalBasis ι ℂ (HilbertVector (Qubits N))
  /-- Source-sector tag attached to each basis vector. -/
  tag : ι -> SourceSingularInvariantLocalVector U left right
  tag_vec_eq : ∀ i : ι, SourceSingularInvariantLocalVector.vec (tag i) = basis i

/-- Count-indexed source sectors form an orthonormal direct-sum decomposition.
This is the precise Lean obligation left by the orthogonality table and final
orthogonal-complement paragraph of `lemma:singInvDec` [GSLW19,
BlockHam.tex:615-736]. -/
structure SourceSingularInvariantOrthonormalDecomposition {N : Nat}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N) where
  /-- Count-indexed source singular-invariant sector decomposition. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  orthonormal :
    Orthonormal ℂ
      (fun tag =>
        (SourceSingularInvariantVector.vec (decomposition := decomposition) tag :
          HilbertVector (Qubits N)))
  spans :
    ⊤ ≤ Submodule.span ℂ
      (Set.range
        (fun tag =>
          (SourceSingularInvariantVector.vec (decomposition := decomposition) tag :
            HilbertVector (Qubits N))))

/-- An orthonormal source direct-sum decomposition supplies the local-sector
orthonormal coverage interface used by projected QSVT. -/
noncomputable def SourceSingularInvariantOrthonormalDecomposition.toLocalCoverage
    {N : Nat} {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (coverage :
      SourceSingularInvariantOrthonormalDecomposition U left right) :
    SourceSingularInvariantLocalOrthonormalBasisCoverage U left right where
  ι := SourceSingularInvariantVector coverage.decomposition
  fintype := inferInstance
  basis := OrthonormalBasis.mk coverage.orthonormal coverage.spans
  tag := SourceSingularInvariantLocalVector.ofDecompositionVector
  tag_vec_eq := by
    intro i
    rw [SourceSingularInvariantLocalVector.vec_ofDecompositionVector]
    exact (OrthonormalBasis.coe_mk coverage.orthonormal coverage.spans).symm ▸ rfl

/-- An orthonormal source local-sector basis gives the generic spanning-family
contract for projected QSVT. -/
noncomputable def sourceProjectedQSVTSpanningFamilyOfLocalOrthonormalBasisCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalOrthonormalBasisCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) := by
  letI : Fintype coverage.ι := coverage.fintype
  refine
    { ι := coverage.ι
      vec := fun i => coverage.basis i
      ext := ?_
      action_eq := ?_ }
  · intro A B h
    exact HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis coverage.basis h
  · intro i
    rw [← coverage.tag_vec_eq i]
    exact SourceSingularInvariantLocalVector.action_eq U left right certificate hP
      init last hφs (coverage.tag i)

/-- An orthonormal source local-sector basis proves the source-level projected
QSVT block equality. -/
theorem sourceProjectedQSVTBlockCorrectness_of_localOrthonormalBasisCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalOrthonormalBasisCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right
    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
    (sourceProjectedQSVTSpanningFamilyOfLocalOrthonormalBasisCoverage
      U left right certificate hP coverage init last hφs)

/-- A source orthonormal direct-sum decomposition proves the source-level
projected QSVT block equality.  This is the compact handoff target for
`lemma:singInvDec` [GSLW19, BlockHam.tex:615-736,768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_orthonormalDecomposition
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantOrthonormalDecomposition U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_localOrthonormalBasisCoverage
    U left right certificate hP coverage.toLocalCoverage init last hφs

/-- The same source orthonormal direct-sum decomposition also proves the
negated-phase source-level block equality for the coefficient-conjugate
polynomial.  This is the local-sector lift needed by the averaging step in
`cor:matchingParity` [GSLW19, BlockHam.tex:851-887]. -/
noncomputable def
    sourceProjectedQSVTSpanningFamilyNegProjectedPhasesOfLocalOrthonormalBasisCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalOrthonormalBasisCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) := by
  letI : Fintype coverage.ι := coverage.fintype
  refine
    { ι := coverage.ι
      vec := fun i => coverage.basis i
      ext := ?_
      action_eq := ?_ }
  · intro A B h
    exact HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis coverage.basis h
  · intro i
    rw [← coverage.tag_vec_eq i]
    exact SourceSingularInvariantLocalVector.action_eq_negProjectedPhases
      U left right certificate hP init last hφs (coverage.tag i)

/-- Negated-phase source block equality for a completed orthonormal source
direct-sum decomposition [GSLW19, BlockHam.tex:615-736,851-887]. -/
theorem sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_orthonormalDecomposition
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantOrthonormalDecomposition U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right
    (negPhases
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
    (sourceProjectedQSVTSpanningFamilyNegProjectedPhasesOfLocalOrthonormalBasisCoverage
      U left right certificate hP coverage.toLocalCoverage init last hφs)

/-- The local source-sector vector attached to a nonzero Gram eigenbasis vector:
it is either the unit singular block or the right vector of a two-dimensional
singular block, according to the source `σ=1` / `0<σ<1` split
[GSLW19, BlockHam.tex:583-613,655-735]. -/
noncomputable def sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceSingularInvariantLocalVector U left right :=
  match projectedUnitaryBlockNonzeroClassifiedSingularBlock left right U i hlambda with
  | SourceNonzeroClassifiedSingularBlock.unitBlock block =>
      SourceSingularInvariantLocalVector.unit block
  | SourceNonzeroClassifiedSingularBlock.twoDimensionalBlock block =>
      SourceSingularInvariantLocalVector.twoRight block

/-- The nonzero-sector local vector is definitionally the corresponding Gram
eigenbasis vector. -/
theorem sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis_vec
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceSingularInvariantLocalVector.vec
        (sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
          left right U i hlambda) =
      (projectedUnitaryBlockGramEigenbasis left right U i :
        HilbertVector (Qubits N)) := by
  unfold sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
  unfold projectedUnitaryBlockNonzeroClassifiedSingularBlock
  by_cases hsigma :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ = 1
  · simp [SourceSingularInvariantLocalVector.vec,
      projectedUnitaryBlockUnitSingularBlock,
      projectedUnitaryBlockNonzeroSingularPair,
      projectedUnitaryBlockRightSingularVector,
      show projectedUnitaryBlockSingularValue left right U i = 1 by
        simpa [projectedUnitaryBlockNonzeroSingularPair] using hsigma]
  · simp [SourceSingularInvariantLocalVector.vec,
      projectedUnitaryBlockTwoDimensionalSingularBlock,
      projectedUnitaryBlockNonzeroSingularPair,
      projectedUnitaryBlockRightSingularVector,
      show ¬ projectedUnitaryBlockSingularValue left right U i = 1 by
        intro h
        exact hsigma (by
          simpa [projectedUnitaryBlockNonzeroSingularPair] using h)]

/-- If every Gram eigenvalue is nonzero, the source direct-sum coverage is
generated by the nonzero singular sectors alone.  The zero-eigenvalue version
adds right-kernel, left-kernel, and fully complementary sectors. -/
noncomputable def sourceSingularInvariantLocalBasisSpanCoverageOfNoZeroGramEigenvalues
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (hlambda :
      ∀ i : (Qubits N).Index,
        ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceSingularInvariantLocalBasisSpanCoverage U left right where
  combination := fun i =>
    [(1,
      sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
        left right U i (hlambda i))]
  basis_eq := by
    intro i
    simp [sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis_vec
      left right U i (hlambda i)]

/-- The right-projector component of a zero Gram eigenbasis vector is carried
as either zero or a scalar multiple of a normalized right-kernel sector.  The
projection can vanish, so the local spanning layer must not claim that this raw
component is itself normalized [GSLW19, BlockHam.tex:599-611,655-716]. -/
noncomputable def sourceRightKernelLocalVectorOfZeroGramEigenbasis
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0) :
    SourceSingularInvariantLocalVector U left right :=
  let rightComponent :=
    HilbertOperator.applyVec right.op
      (projectedUnitaryBlockGramEigenbasis left right U i : HilbertVector (Qubits N))
  if hzero : rightComponent = 0 then
    SourceSingularInvariantLocalVector.zero
  else
    have hsupport : HilbertOperator.applyVec right.op rightComponent = rightComponent := by
      dsimp [rightComponent]
      rw [← HilbertOperator.mul_applyVec, right.idempotent]
    have hkernel :
        HilbertOperator.applyVec (projectedUnitaryBlock left right U) rightComponent = 0 := by
      dsimp [rightComponent]
      rw [projectedUnitaryBlock_applyVec_projector_applyVec]
      exact projectedUnitaryBlock_applyVec_rightSingularVector_eq_zero_of_eigenvalue_zero
        left right U i hlambda
    SourceSingularInvariantLocalVector.scaledRightKernel (‖rightComponent‖ : ℂ)
      (sourceRightKernelSingularBlockOfProjectedBlockEqZero U left right
        (NormalizedVector.ofNeZero rightComponent hzero)
        (by
          simpa [NormalizedVector.ofNeZero, HilbertOperator.applyVec_smul] using
            congrArg (fun ψ : HilbertVector (Qubits N) =>
              (‖rightComponent‖ : ℂ)⁻¹ • ψ) hsupport)
        (by
          simpa [NormalizedVector.ofNeZero, HilbertOperator.applyVec_smul] using
            congrArg (fun ψ : HilbertVector (Qubits N) =>
              (‖rightComponent‖ : ℂ)⁻¹ • ψ) hkernel))

/-- The zero-eigenvalue right-kernel local vector is the right-projector
component of the Gram eigenbasis vector. -/
theorem sourceRightKernelLocalVectorOfZeroGramEigenbasis_vec
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0) :
    SourceSingularInvariantLocalVector.vec
        (sourceRightKernelLocalVectorOfZeroGramEigenbasis left right U i hlambda) =
      HilbertOperator.applyVec right.op
        (projectedUnitaryBlockGramEigenbasis left right U i : HilbertVector (Qubits N)) := by
  unfold sourceRightKernelLocalVectorOfZeroGramEigenbasis
  dsimp only
  split_ifs with hzero
  · simpa [SourceSingularInvariantLocalVector.vec] using hzero.symm
  · simpa [SourceSingularInvariantLocalVector.vec,
      sourceRightKernelSingularBlockOfProjectedBlockEqZero] using
        NormalizedVector.norm_smul_coe_ofNeZero
          (HilbertOperator.applyVec right.op
            (projectedUnitaryBlockGramEigenbasis left right U i :
              HilbertVector (Qubits N))) hzero

/-- The left-projector component of a zero output-side Gram eigenbasis vector
is carried as either zero or a scalar multiple of a normalized left-kernel
sector.  The projection may vanish, so the local spanning tag itself remains a
raw-vector carrier [GSLW19, BlockHam.tex:599-611,655-716]. -/
noncomputable def sourceLeftKernelLocalVectorOfZeroLeftGramEigenbasis
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i = 0) :
    SourceSingularInvariantLocalVector U left right :=
  let leftComponent :=
    HilbertOperator.applyVec left.op
      (projectedUnitaryBlockLeftGramEigenbasis left right U i :
        HilbertVector (Qubits N))
  if hzero : leftComponent = 0 then
    SourceSingularInvariantLocalVector.zero
  else
    have hsupport : HilbertOperator.applyVec left.op leftComponent = leftComponent := by
      dsimp [leftComponent]
      rw [← HilbertOperator.mul_applyVec, left.idempotent]
    have hkernel :
        HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
          leftComponent = 0 := by
      dsimp [leftComponent]
      rw [projectedUnitaryBlock_conjTranspose_applyVec_projector_applyVec]
      exact
        projectedUnitaryBlock_conjTranspose_applyVec_leftGramEigenbasis_eq_zero_of_eigenvalue_zero
          left right U i hlambda
    SourceSingularInvariantLocalVector.scaledLeftKernel (‖leftComponent‖ : ℂ)
      (sourceLeftKernelSingularBlockOfProjectedBlockConjTransposeEqZero
        U left right (NormalizedVector.ofNeZero leftComponent hzero)
        (by
          simpa [NormalizedVector.ofNeZero, HilbertOperator.applyVec_smul] using
            congrArg (fun ψ : HilbertVector (Qubits N) =>
              (‖leftComponent‖ : ℂ)⁻¹ • ψ) hsupport)
        (by
          simpa [NormalizedVector.ofNeZero, HilbertOperator.applyVec_smul] using
            congrArg (fun ψ : HilbertVector (Qubits N) =>
              (‖leftComponent‖ : ℂ)⁻¹ • ψ) hkernel))

/-- The zero output-side Gram local vector reconstructs the `U†`-preimage of
the left-projector component, including the vanishing projection case. -/
theorem sourceLeftKernelLocalVectorOfZeroLeftGramEigenbasis_vec
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i = 0) :
    SourceSingularInvariantLocalVector.vec
        (sourceLeftKernelLocalVectorOfZeroLeftGramEigenbasis left right U i hlambda) =
      U.dagger.applyVec
        (HilbertOperator.applyVec left.op
          (projectedUnitaryBlockLeftGramEigenbasis left right U i :
            HilbertVector (Qubits N))) := by
  unfold sourceLeftKernelLocalVectorOfZeroLeftGramEigenbasis
  dsimp only
  split_ifs with hzero
  · rw [hzero]
    change 0 = U.dagger.applyVec (0 : HilbertVector (Qubits N))
    symm
    simpa using
      (UnitaryOperator.applyVec_smul U.dagger (0 : ℂ)
        (0 : HilbertVector (Qubits N)))
  · change
      (‖HilbertOperator.applyVec left.op
          (projectedUnitaryBlockLeftGramEigenbasis left right U i :
            HilbertVector (Qubits N))‖ : ℂ) •
          U.dagger.applyVec
            (NormalizedVector.ofNeZero
              (HilbertOperator.applyVec left.op
                (projectedUnitaryBlockLeftGramEigenbasis left right U i :
                  HilbertVector (Qubits N))) hzero) =
        U.dagger.applyVec
          (HilbertOperator.applyVec left.op
            (projectedUnitaryBlockLeftGramEigenbasis left right U i :
              HilbertVector (Qubits N)))
    rw [← UnitaryOperator.applyVec_smul,
      NormalizedVector.norm_smul_coe_ofNeZero]

/-- A right-complement vector whose image has no left-projector component is a
fully complementary local sector of `lemma:singInvDec` [GSLW19,
BlockHam.tex:607-613,718-735]. -/
noncomputable def sourceComplementLocalVectorOfRightComplementProjectedZero
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (rightPerp : HilbertVector (Qubits N))
    (hright_perp :
      HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp =
        rightPerp)
    (hleft_zero : HilbertOperator.applyVec left.op (U.applyVec rightPerp) = 0) :
    SourceSingularInvariantLocalVector U left right :=
  if hzero : rightPerp = 0 then
    SourceSingularInvariantLocalVector.zero
  else
    SourceSingularInvariantLocalVector.scaledComplement (‖rightPerp‖ : ℂ)
      (sourceComplementSingularBlockOfRightComplementProjectedZero
        U left right (NormalizedVector.ofNeZero rightPerp hzero)
        (by
          simpa [NormalizedVector.ofNeZero, HilbertOperator.applyVec_smul] using
            congrArg (fun ψ : HilbertVector (Qubits N) =>
              (‖rightPerp‖ : ℂ)⁻¹ • ψ) hright_perp)
        (by
          simpa [NormalizedVector.ofNeZero, UnitaryOperator.applyVec_smul,
            HilbertOperator.applyVec_smul] using
            congrArg (fun ψ : HilbertVector (Qubits N) =>
              (‖rightPerp‖ : ℂ)⁻¹ • ψ) hleft_zero))

/-- The fully complementary local vector is definitionally the supplied
right-complement vector. -/
theorem sourceComplementLocalVectorOfRightComplementProjectedZero_vec
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (rightPerp : HilbertVector (Qubits N))
    (hright_perp :
      HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp =
        rightPerp)
    (hleft_zero : HilbertOperator.applyVec left.op (U.applyVec rightPerp) = 0) :
    SourceSingularInvariantLocalVector.vec
        (sourceComplementLocalVectorOfRightComplementProjectedZero
          left right U rightPerp hright_perp hleft_zero) =
      rightPerp := by
  unfold sourceComplementLocalVectorOfRightComplementProjectedZero
  split_ifs with hzero
  · simpa [SourceSingularInvariantLocalVector.vec] using hzero.symm
  · simpa [SourceSingularInvariantLocalVector.vec,
      sourceComplementSingularBlockOfRightComplementProjectedZero] using
        NormalizedVector.norm_smul_coe_ofNeZero rightPerp hzero

/-- Reduce full local coverage to the remaining decomposition of the
right-projector complement in the zero Gram eigenspaces.  Nonzero eigenvectors
are handled by the unit/two-dimensional split, while zero eigenvectors first
contribute their `Π`-supported right-kernel component [GSLW19,
BlockHam.tex:583-613,655-736]. -/
noncomputable def sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementSplit
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (zeroComplementCombination :
      ∀ i : (Qubits N).Index,
        (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 ->
          List (ℂ × SourceSingularInvariantLocalVector U left right))
    (zeroComplement_basis_eq :
      ∀ (i : (Qubits N).Index)
        (hlambda :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0),
        HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (projectedUnitaryBlockGramEigenbasis left right U i :
              HilbertVector (Qubits N)) =
          ((zeroComplementCombination i hlambda).map fun term =>
            term.1 • SourceSingularInvariantLocalVector.vec term.2).sum) :
    SourceSingularInvariantLocalBasisSpanCoverage U left right where
  combination := fun i =>
    if hlambda :
        ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0 then
      [(1,
        sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
          left right U i hlambda)]
    else
      have hzero_complex :
          ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) = 0 :=
        not_not.mp hlambda
      have hzero :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 :=
        Complex.ofReal_eq_zero.mp hzero_complex
      [(1, sourceRightKernelLocalVectorOfZeroGramEigenbasis left right U i hzero)] ++
        zeroComplementCombination i hzero
  basis_eq := by
    intro i
    by_cases hlambda :
        ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0
    · simp [hlambda,
        sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis_vec
          left right U i hlambda]
    · have hzero_complex :
          ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) = 0 :=
        not_not.mp hlambda
      have hzero :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 :=
        Complex.ofReal_eq_zero.mp hzero_complex
      calc
        (projectedUnitaryBlockGramEigenbasis left right U i :
            HilbertVector (Qubits N)) =
            HilbertOperator.applyVec right.op
                (projectedUnitaryBlockGramEigenbasis left right U i :
                  HilbertVector (Qubits N)) +
              HilbertOperator.applyVec (OrthogonalProjector.complement right)
                (projectedUnitaryBlockGramEigenbasis left right U i :
                  HilbertVector (Qubits N)) := by
              exact (orthogonalProjector_applyVec_add_complement_applyVec right
                (projectedUnitaryBlockGramEigenbasis left right U i :
                  HilbertVector (Qubits N))).symm
        _ =
            (([(1,
              sourceRightKernelLocalVectorOfZeroGramEigenbasis left right U i hzero)] ++
                zeroComplementCombination i hzero).map
                  fun term : ℂ × SourceSingularInvariantLocalVector U left right =>
                  term.1 • SourceSingularInvariantLocalVector.vec term.2).sum := by
              simp [sourceRightKernelLocalVectorOfZeroGramEigenbasis_vec
                left right U i hzero, zeroComplement_basis_eq i hzero]
        _ =
            ((if hlambda :
                ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i :
                  ℂ) ≠ 0 then
              [(1,
                sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
                  left right U i hlambda)]
            else
              have hzero_complex :
                  ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i :
                    ℂ) = 0 :=
                not_not.mp hlambda
              have hzero :
                  (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 :=
                Complex.ofReal_eq_zero.mp hzero_complex
              [(1, sourceRightKernelLocalVectorOfZeroGramEigenbasis left right U i hzero)] ++
                zeroComplementCombination i hzero).map
                  fun term : ℂ × SourceSingularInvariantLocalVector U left right =>
                    term.1 • SourceSingularInvariantLocalVector.vec term.2).sum := by
              simp [hlambda]

/-- Projected-QSVT local coverage obtained directly from the Gram eigenbasis.
For a zero Gram eigenvector, only its `Π`-supported part needs the source
right-kernel block.  Its `Πᗮ` part is an input-complement vector, and therefore
both the projected source block and the target `P^{(SV)}` annihilate it.  This
is the projected-theorem specialization of the source direct-sum split in
`lemma:singInvDec` [GSLW19, BlockHam.tex:599-613,655-736]. -/
noncomputable def sourceSingularInvariantLocalBasisSpanCoverageOfProjectorComplementSplit
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    SourceSingularInvariantLocalBasisSpanCoverage U left right :=
  sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementSplit left right U
    (fun i _ =>
      [(1,
        SourceSingularInvariantLocalVector.inputComplement
          (HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (projectedUnitaryBlockGramEigenbasis left right U i :
              HilbertVector (Qubits N)))
          (by
            rw [← HilbertOperator.mul_applyVec, OrthogonalProjector.complement_sq]))])
    (by
      intro i hlambda
      simp [SourceSingularInvariantLocalVector.vec])

/-- Special zero-complement coverage when every zero-eigenvalue
right-complement component is fully complementary.  The general source proof
adds the left-kernel part before applying this fully-complementary case
[GSLW19, BlockHam.tex:607-613,718-735]. -/
noncomputable def sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementFullyComplementary
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (hleft_zero :
      ∀ (i : (Qubits N).Index)
        (_ :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0),
        HilbertOperator.applyVec left.op
            (U.applyVec
              (HilbertOperator.applyVec (OrthogonalProjector.complement right)
                (projectedUnitaryBlockGramEigenbasis left right U i :
                  HilbertVector (Qubits N)))) = 0) :
    SourceSingularInvariantLocalBasisSpanCoverage U left right :=
  sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementSplit left right U
    (fun i hlambda =>
      [(1,
        sourceComplementLocalVectorOfRightComplementProjectedZero left right U
          (HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (projectedUnitaryBlockGramEigenbasis left right U i :
              HilbertVector (Qubits N)))
          (by
            rw [← HilbertOperator.mul_applyVec, OrthogonalProjector.complement_sq])
          (hleft_zero i hlambda))])
    (by
      intro i hlambda
      simp [sourceComplementLocalVectorOfRightComplementProjectedZero_vec])

/-- Direct local-block coverage feeds the generic basis-span family used by the
global projected-QSVT theorem. -/
noncomputable def sourceProjectedQSVTBasisSpanFamilyOfLocalCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBasisSpanFamily (d := d) U left right P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) where
  ι := SourceSingularInvariantLocalVector U left right
  vec := SourceSingularInvariantLocalVector.vec
  combination := coverage.combination
  basis_eq := coverage.basis_eq
  action_eq :=
    SourceSingularInvariantLocalVector.action_eq U left right certificate hP init last hφs

/-- Local-block basis-span coverage proves the source-level projected-QSVT block
equality. -/
theorem sourceProjectedQSVTBlockCorrectness_of_localBasisSpanCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_basisSpanFamily U left right
    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
    (sourceProjectedQSVTBasisSpanFamilyOfLocalCoverage U left right certificate hP
      coverage init last hφs)

/-- Direct local-block coverage for the negated projected phase list.  This is
the local form of the `U_{-\Phi}` branch used in the real-polynomial averaging
step of `cor:matchingParity` [GSLW19, BlockHam.tex:851-887]. -/
noncomputable def sourceProjectedQSVTBasisSpanFamilyNegProjectedPhasesOfLocalCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBasisSpanFamily (d := d) U left right (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) where
  ι := SourceSingularInvariantLocalVector U left right
  vec := SourceSingularInvariantLocalVector.vec
  combination := coverage.combination
  basis_eq := coverage.basis_eq
  action_eq :=
    SourceSingularInvariantLocalVector.action_eq_negProjectedPhases
      U left right certificate hP init last hφs

/-- Local-block basis-span coverage proves the negated-phase source-level
projected-QSVT block equality. -/
theorem sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_localBasisSpanCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :=
  sourceProjectedQSVTBlockCorrectness_of_basisSpanFamily U left right
    (negPhases
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
    (sourceProjectedQSVTBasisSpanFamilyNegProjectedPhasesOfLocalCoverage
      U left right certificate hP coverage init last hφs)

/-- Source projected-QSVT in the special case where the Gram spectrum has no
zero eigenvalues.  This packages the nonzero part of `lemma:singInvDec`; the
general theorem adds the zero-sector right-kernel, left-kernel, and fully
complementary blocks [GSLW19, BlockHam.tex:583-613,655-736,768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_noZeroGramEigenvalues
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (hlambda :
      ∀ i : (Qubits N).Index,
        ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_localBasisSpanCoverage U left right
    certificate hP
    (sourceSingularInvariantLocalBasisSpanCoverageOfNoZeroGramEigenvalues
      left right U hlambda)
    init last hφs

/-- Source projected-QSVT reduced to the final zero-complement decomposition
piece of `lemma:singInvDec`. -/
theorem sourceProjectedQSVTBlockCorrectness_of_zeroComplementSplit
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (zeroComplementCombination :
      ∀ i : (Qubits N).Index,
        (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 ->
          List (ℂ × SourceSingularInvariantLocalVector U left right))
    (zeroComplement_basis_eq :
      ∀ (i : (Qubits N).Index)
        (hlambda :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0),
        HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (projectedUnitaryBlockGramEigenbasis left right U i :
              HilbertVector (Qubits N)) =
          ((zeroComplementCombination i hlambda).map fun term =>
            term.1 • SourceSingularInvariantLocalVector.vec term.2).sum)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_localBasisSpanCoverage U left right
    certificate hP
    (sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementSplit
      left right U zeroComplementCombination zeroComplement_basis_eq)
    init last hφs

/-- Coverage contract for the source invariant decomposition: the tagged
source-side vectors are extensionally complete for operator equalities.  This
is the direct-sum/spanning obligation left by `lemma:singInvDec`
[GSLW19, BlockHam.tex:583-613,655-736]. -/
structure SourceSingularInvariantCoverage {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Source singular-invariant sector decomposition used by the coverage proof. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  ext :
    ∀ {A B : HilbertOperator (Qubits N)},
      (∀ tag : SourceSingularInvariantVector decomposition,
        HilbertOperator.applyVec A
            (SourceSingularInvariantVector.vec tag : HilbertVector (Qubits N)) =
          HilbertOperator.applyVec B
            (SourceSingularInvariantVector.vec tag : HilbertVector (Qubits N))) ->
      A = B

/-- A concrete way to prove `SourceSingularInvariantCoverage`: classify every
Gram-eigenbasis vector into one of the source singular-invariant sector tags.
This is the Lean form of the source direct-sum classification in
`lemma:singInvDec` [GSLW19, BlockHam.tex:583-613,655-736]. -/
structure SourceSingularInvariantBasisCoverage {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Source singular-invariant sector decomposition used by the basis classification. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  /-- Sector tag assigned to each Gram-eigenbasis vector. -/
  tagOfBasis :
    (Qubits N).Index -> SourceSingularInvariantVector decomposition
  tag_vec_eq :
    ∀ i : (Qubits N).Index,
      (SourceSingularInvariantVector.vec (tagOfBasis i) : HilbertVector (Qubits N)) =
        (projectedUnitaryBlockGramEigenbasis left right U i :
          HilbertVector (Qubits N))

namespace SourceSingularInvariantBasisCoverage

/-- A Gram-eigenbasis sector classification gives the extensional source
coverage required by the projected-QSVT assembly theorem. -/
noncomputable def toCoverage {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (coverage : SourceSingularInvariantBasisCoverage U left right) :
    SourceSingularInvariantCoverage U left right where
  decomposition := coverage.decomposition
  ext := by
    intro A B h
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis
      (projectedUnitaryBlockGramEigenbasis left right U)
    intro i
    rw [← coverage.tag_vec_eq i]
    exact h (coverage.tagOfBasis i)

end SourceSingularInvariantBasisCoverage

/-- A flexible basis-level coverage witness: each Gram-eigenbasis vector may be
a finite linear combination of source singular-invariant sector vectors.  This
matches the source direct-sum construction in the zero-singular-value sectors,
where a Gram basis vector is split into its right-projector and complementary
parts [GSLW19, BlockHam.tex:583-613,655-736]. -/
structure SourceSingularInvariantBasisSpanCoverage {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Source singular-invariant sector decomposition used by the span coverage. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  /-- Linear combination of source-sector vectors for each Gram-eigenbasis vector. -/
  combination :
    (Qubits N).Index -> List (ℂ × SourceSingularInvariantVector decomposition)
  basis_eq :
    ∀ i : (Qubits N).Index,
      (projectedUnitaryBlockGramEigenbasis left right U i :
          HilbertVector (Qubits N)) =
        ((combination i).map fun term =>
          term.1 • (SourceSingularInvariantVector.vec term.2 :
            HilbertVector (Qubits N))).sum

namespace SourceSingularInvariantBasisSpanCoverage

private theorem applyVec_eq_on_combination {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    {decomposition : SourceSingularInvariantDecomposition U left right}
    {A B : HilbertOperator (Qubits N)}
    (h :
      ∀ tag : SourceSingularInvariantVector decomposition,
        HilbertOperator.applyVec A
            (SourceSingularInvariantVector.vec tag : HilbertVector (Qubits N)) =
          HilbertOperator.applyVec B
            (SourceSingularInvariantVector.vec tag : HilbertVector (Qubits N)))
    (terms : List (ℂ × SourceSingularInvariantVector decomposition)) :
    HilbertOperator.applyVec A
        ((terms.map fun term => term.1 • (SourceSingularInvariantVector.vec term.2 :
          HilbertVector (Qubits N))).sum) =
      HilbertOperator.applyVec B
        ((terms.map fun term => term.1 • (SourceSingularInvariantVector.vec term.2 :
          HilbertVector (Qubits N))).sum) := by
  induction terms with
  | nil =>
      simp [HilbertOperator.applyVec]
  | cons term rest ih =>
      rcases term with ⟨c, tag⟩
      simp [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul, h tag, ih]

/-- A finite linear-combination classification of every Gram-eigenbasis vector
gives the extensional source coverage required by the projected-QSVT assembly
theorem. -/
noncomputable def toCoverage {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right) :
    SourceSingularInvariantCoverage U left right where
  decomposition := coverage.decomposition
  ext := by
    intro A B h
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis
      (projectedUnitaryBlockGramEigenbasis left right U)
    intro i
    rw [coverage.basis_eq i]
    exact applyVec_eq_on_combination h (coverage.combination i)

end SourceSingularInvariantBasisSpanCoverage

/-- A source invariant decomposition with extensional coverage supplies the
spanning family required for the global `thm:singValTransformation` equality,
provided each source sector is evaluated by the local block lemmas
[GSLW19, BlockHam.tex:655-736,768-849]. -/
noncomputable def sourceProjectedQSVTSpanningFamilyOfCoverage {N d : Nat}
    {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) := by
  refine
    { ι := SourceSingularInvariantVector coverage.decomposition
      vec := fun tag =>
        (SourceSingularInvariantVector.vec tag : HilbertVector (Qubits N))
      ext := ?_
      action_eq := ?_ }
  · intro A B h
    exact coverage.ext h
  · intro tag
    cases tag with
    | unit i =>
        let block := coverage.decomposition.unitBlock i
        dsimp [SourceSingularInvariantVector.vec]
        by_cases hd : d % 2 = 0
        · rw [
            SourceUnitSingularBlock.sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
              block certificate init last hφs hd,
            SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
              block P hd hP]
        · have hdodd : d % 2 = 1 := by omega
          rw [
            SourceUnitSingularBlock.sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
              block certificate init last hφs hdodd,
            SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
              block P hdodd hP]
    | twoRight i =>
        let block := coverage.decomposition.twoDimensionalBlock i
        dsimp [SourceSingularInvariantVector.vec]
        by_cases hd : d % 2 = 0
        · open SourceTwoDimensionalSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
              block certificate init last hφs hd,
            SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
              block P hd hP]
        · have hdodd : d % 2 = 1 := by omega
          open SourceTwoDimensionalSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
              block certificate init last hφs hdodd,
            SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
              block P hdodd hP]
    | twoRightPerp i =>
        let block := coverage.decomposition.twoDimensionalBlock i
        dsimp [SourceSingularInvariantVector.vec]
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp = 0 :=
            sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
              (projectedOutputProjector left right d) right
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
              block.rightPerp block.right_perp_support
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) P block.right_perp_support]
    | rightKernel i =>
        let block := coverage.decomposition.rightKernelBlock i
        dsimp [SourceSingularInvariantVector.vec]
        by_cases hd : d % 2 = 0
        · open SourceRightKernelSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
              block certificate init last hφs hd,
            SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
              block P hd hP]
        · have hdodd : d % 2 = 1 := by omega
          open SourceRightKernelSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd block certificate hdodd,
            SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
              block P hdodd hP]
    | leftKernel i =>
        let block := coverage.decomposition.leftKernelBlock i
        dsimp [SourceSingularInvariantVector.vec]
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp = 0 :=
            SourceLeftKernelSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
              block
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) P block.right_perp_support]
    | complement i =>
        let block := coverage.decomposition.complementBlock i
        dsimp [SourceSingularInvariantVector.vec]
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (Native.sourceWord U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp = 0 :=
            SourceComplementSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
              block
              (Native.sourceWord U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) P block.right_perp_support]

/-- Coverage plus the source sector-local action lemmas prove the global
source-level projected-QSVT block equality.  The remaining source obligation is
to construct `SourceSingularInvariantCoverage` from the spectral direct-sum
decomposition of `lemma:singInvDec` [GSLW19, BlockHam.tex:583-613,655-736,
768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_coverage {N d : Nat}
    {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right
    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
    (sourceProjectedQSVTSpanningFamilyOfCoverage U left right certificate hP
      coverage init last hφs)

/-- Basis-level sector classification is enough to prove the source-level
projected-QSVT block equality. -/
theorem sourceProjectedQSVTBlockCorrectness_of_basisCoverage {N d : Nat}
    {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantBasisCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_coverage U left right certificate hP
    (SourceSingularInvariantBasisCoverage.toCoverage coverage) init last hφs

/-- Span-level sector classification is enough to prove the source-level
projected-QSVT block equality.  This is the interface used by the source
direct-sum proof because zero-singular-value Gram basis vectors split into
projector and complementary pieces [GSLW19, BlockHam.tex:583-613,655-736,
768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_basisSpanCoverage {N d : Nat}
    {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_coverage U left right certificate hP
    (SourceSingularInvariantBasisSpanCoverage.toCoverage coverage) init last hφs

/-- Coverage plus the local negated-phase action lemmas proves the
coefficient-conjugate source-level projected-QSVT block equality.  This is the
coverage-level `U_{-\Phi}` branch used by the averaging proof of
`cor:matchingParity` [GSLW19, BlockHam.tex:655-736,851-887]. -/
noncomputable def sourceProjectedQSVTSpanningFamilyNegProjectedPhasesOfCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) := by
  refine
    { ι := SourceSingularInvariantVector coverage.decomposition
      vec := fun tag =>
        (SourceSingularInvariantVector.vec tag : HilbertVector (Qubits N))
      ext := ?_
      action_eq := ?_ }
  · intro A B h
    exact coverage.ext h
  · intro tag
    rw [← SourceSingularInvariantLocalVector.vec_ofDecompositionVector tag]
    exact SourceSingularInvariantLocalVector.action_eq_negProjectedPhases
      U left right certificate hP init last hφs
      (SourceSingularInvariantLocalVector.ofDecompositionVector tag)

/-- Coverage-level negated-phase source block equality for the
coefficient-conjugate polynomial [GSLW19, BlockHam.tex:655-736,851-887]. -/
theorem sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_coverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right
    (negPhases
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
    (sourceProjectedQSVTSpanningFamilyNegProjectedPhasesOfCoverage
      U left right certificate hP coverage init last hφs)

/-- Span-level sector classification is also enough for the negated-phase
branch used in the real-polynomial averaging proof. -/
theorem sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_basisSpanCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :=
  sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_coverage
    U left right certificate hP
    (SourceSingularInvariantBasisSpanCoverage.toCoverage coverage)
    init last hφs


end QuantumAlg.QSP.MultiQubit.QSVT
end
