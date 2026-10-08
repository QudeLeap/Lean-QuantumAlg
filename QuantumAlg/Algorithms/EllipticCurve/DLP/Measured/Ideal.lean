/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support.Preparation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Program
import all QuantumAlg.Core.Base.Gate.Effect.Extension
import all QuantumAlg.Core.Base.Gate.Effect.Unitary
import all QuantumAlg.Core.Execution.Measurement.Effect

/-!
# The original full-group target as a certified mathematical effect

Each original exponent pair retains its exact full-group output label. The
label register is the finite image of those outputs, so it includes the group
identity whenever that is an output and requires neither a discrete logarithm
nor a finite enumeration of the whole group. The original inverse Fourier
readout acts only on the exponents, beside the retained group and reference.

Compression to the input branches gives a positive contractive observable.
Zero extension places it on the supplied Montgomery seed subspace, and the
original preparation pulls it back to the actual input coordinates. These
are mathematical effects and operators, not new executable circuits or gates.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding
open FiniteCyclicDLP ConcreteCircuitAccess
open scoped ComplexOrder

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The source keeps the two original Fourier labels as an explicit ordered pair. -/
def idealBranchRegister (problem : KnownOrderProblem E.GroupPoint) : Register :=
  (Qubits (orderWidth problem)).prod (Qubits (orderWidth problem))

/-- The original full-group target includes every exponent pair, including source padding. -/
def idealGroupOutput (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (branch : (idealBranchRegister problem).Index) : E.GroupPoint :=
  seed.toGroupPoint * problem.toSourceScope.oracleMultiplier branch.1.val branch.2.val

/-- Only exact output group values are needed for the finite mathematical label register. -/
def idealGroupLabels (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E) :
    Finset E.GroupPoint :=
  Finset.univ.image (idealGroupOutput problem seed)

/-- The finite image carries actual group values, including the identity where applicable. -/
def idealGroupRegister (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E) :
    Register where
  Index := {value // value ∈ idealGroupLabels problem seed}
  fintype := inferInstance
  decEq := inferInstance

/-- This label contains exactly the original group's oracle result. -/
def idealGroupLabel (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (branch : (idealBranchRegister problem).Index) :
    (idealGroupRegister problem seed).Index :=
  ⟨idealGroupOutput problem seed branch, Finset.mem_image.mpr ⟨branch, Finset.mem_univ _, rfl⟩⟩

/-- Pack the original exponent pair beside its full-group target and the unchanged reference. -/
def idealOracleEmbedding (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (Reference : Register) :
    ((idealBranchRegister problem).prod Reference).Index →
      (((Qubits (orderWidth problem + orderWidth problem)).prod
        (idealGroupRegister problem seed)).prod Reference).Index :=
  fun label => ((prodEquiv label.1, idealGroupLabel problem seed label.1), label.2)

/-- Exponents remain in the output, so the group action need not itself be injective. -/
theorem idealOracleEmbedding_injective (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (Reference : Register) :
    Function.Injective (idealOracleEmbedding problem seed Reference) := by
  intro left right same
  have referenceSame := congrArg (fun label => label.2) same
  apply Prod.ext
  · exact prodEquiv.injective (congrArg (fun label => label.1.1) same)
  · exact referenceSame

/-- The original two inverse Fourier transforms act beside both retained label factors. -/
def idealReadoutOperator (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (Reference : Register) :
    UnitaryOperator (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference) :=
  UnitaryOperator.prodTensor
    (UnitaryOperator.prodTensor (exponentReadoutCircuit problem).binaryMatrix
      (1 : UnitaryOperator (idealGroupRegister problem seed))) (1 : UnitaryOperator Reference)

/-- Decode the original ordered big-endian exponent event without reading retained labels. -/
def idealReadoutEvent (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register) :
    (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference).Index → Bool :=
  fun label => event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
    (prodEquiv.symm label.1.1))

/-- Observe the original big-endian exponent event, retaining every group and reference label. -/
def idealReadoutEffect (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register) :
    Effect (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference) where
  matrix := @ZMeasurement.projector
    (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference) Bool (Classical.decEq Bool)
    (idealReadoutEvent problem seed event Reference) true
  positive := Matrix.PosSemidef.diagonal (by
    intro label
    dsimp only [Pi.zero_apply]
    split_ifs <;> simp)
  contractive vector := ZMeasurement.projector_applyVec_norm_le
    (R := ((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference)
    (idealReadoutEvent problem seed event Reference) true vector

/-- Pull the original group-target readout effect back to the full coherent branch space. -/
def idealBranchEffect (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) (Reference : Register) :
    Effect ((idealBranchRegister problem).prod Reference) :=
  Effect.compress (idealOracleEmbedding problem seed Reference)
    (idealOracleEmbedding_injective problem seed Reference)
    (Effect.pullbackUnitary (idealReadoutOperator problem seed Reference)
      (idealReadoutEffect problem seed event Reference))

private theorem extension_inner_right {R S : Register} (embedding : S.Index → R.Index)
    (vector : HilbertVector S) (other : HilbertVector R) :
    inner ℂ (Effect.extensionVector embedding vector) other =
      inner ℂ vector (WithLp.toLp 2 (fun index => other (embedding index))) := by
  classical
  simp only [Effect.extensionVector, sum_inner, inner_smul_left]
  simp [PiLp.inner_apply, RCLike.inner_apply, NormalizedVector.ket_apply, mul_comm]

private theorem compress_weight_subnormalized {R S : Register}
    (embedding : S.Index → R.Index) (injective : Function.Injective embedding)
    (effect : Effect R) (vector : HilbertVector S) (bounded : ‖vector‖ ≤ 1) :
    (Effect.compress embedding injective effect).weight
        (DensityOperator.ofSubnormalizedVector vector bounded) =
      effect.weight (DensityOperator.ofSubnormalizedVector
        (Effect.extensionVector embedding vector)
        (by rw [Effect.norm_extensionVector embedding injective]; exact bounded)) := by
  rw [Effect.weight_ofSubnormalizedVector, Effect.weight_ofSubnormalizedVector]
  unfold HilbertOperator.quadraticWeight
  rw [Effect.compress_matrix, Effect.submatrix_applyVec]
  exact congrArg Complex.re (extension_inner_right embedding vector
    (effect.matrix.applyVec (Effect.extensionVector embedding vector))).symm

/-- The complete coherent branch effect is exactly the original group-label readout weight. -/
theorem idealBranchEffect_weight (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register) (vector : HilbertVector ((idealBranchRegister problem).prod Reference))
    (bounded : ‖vector‖ ≤ 1) :
    (idealBranchEffect problem seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector vector bounded) =
      (idealReadoutEffect problem seed event Reference).weight
        (DensityOperator.applyUnitary (idealReadoutOperator problem seed Reference)
          (DensityOperator.ofSubnormalizedVector
            (Effect.extensionVector (idealOracleEmbedding problem seed Reference) vector)
            (by rw [Effect.norm_extensionVector _
                  (idealOracleEmbedding_injective problem seed Reference)]; exact bounded))) := by
  unfold idealBranchEffect
  rw [compress_weight_subnormalized, Effect.weight_pullbackUnitary]

variable [Fact p.Prime]

/-- Place precisely the supplied Montgomery seed and unchanged reference beside each branch. -/
def idealMontgomeryEmbedding (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) (Reference : Register) :
    ((idealBranchRegister problem).prod Reference).Index →
      ((before p.size (2 * orderWidth problem)).register.prod Reference).Index :=
  fun label => (pairedMontgomeryInput fieldTail (orderWidth problem)
    sameWidth fits seed label.1, label.2)

/-- The actual paired exponent labels make the fixed-seed physical embedding injective. -/
theorem idealMontgomeryEmbedding_injective (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) (Reference : Register) :
    Function.Injective
      (idealMontgomeryEmbedding problem fieldTail sameWidth fits seed Reference) := by
  intro left right same
  have referenceSame := congrArg (fun label => label.2) same
  apply Prod.ext
  · exact pairedMontgomeryInput_injective fieldTail (orderWidth problem) sameWidth fits seed
      (congrArg Prod.fst same)
  · exact referenceSame

/-- Extend the mathematical branch observable by zero outside the supplied seed subspace. -/
def idealPreparedEffect (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register) :
    Effect ((before p.size (2 * orderWidth problem)).register.prod Reference) :=
  Effect.extend (idealMontgomeryEmbedding problem fieldTail sameWidth fits seed Reference)
    (idealMontgomeryEmbedding_injective problem fieldTail sameWidth fits seed Reference)
    (idealBranchEffect problem seed event Reference)

/-- Zero extension preserves the whole coherent branch density, including zero good mass. -/
theorem idealPreparedEffect_weight (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register) (vector : HilbertVector ((idealBranchRegister problem).prod Reference))
    (bounded : ‖vector‖ ≤ 1) :
    (idealPreparedEffect problem fieldTail sameWidth fits seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector
          (Effect.extensionVector
            (idealMontgomeryEmbedding problem fieldTail sameWidth fits seed Reference) vector)
          (by rw [Effect.norm_extensionVector _
                (idealMontgomeryEmbedding_injective problem fieldTail sameWidth fits
                  seed Reference)]; exact bounded)) =
      (idealBranchEffect problem seed event Reference).weight
        (DensityOperator.ofSubnormalizedVector vector bounded) :=
  Effect.extend_weight_ofSubnormalizedVector _ _ _ vector bounded

/-- Pull the same certified observable back through the actual original exponent preparation. -/
def idealInputEffect (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register) :
    Effect ((before p.size (2 * orderWidth problem)).register.prod Reference) :=
  Effect.pullbackUnitary
    (beforeExponentOperator p (orderWidth problem) (exponentPreparationCircuit problem)
      Reference)
    (idealPreparedEffect problem fieldTail sameWidth fits seed event Reference)

/-- The original input-coordinate effect is exactly paired with the complete prepared density. -/
theorem idealInputEffect_weight (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (Reference : Register)
    (state : DensityOperator ((before p.size (2 * orderWidth problem)).register.prod Reference)) :
    (idealInputEffect problem fieldTail sameWidth fits seed event Reference).weight state =
      (idealPreparedEffect problem fieldTail sameWidth fits seed event Reference).weight
        (exponentPreparedDensity E problem Reference state) :=
  Effect.weight_pullbackUnitary _ _ state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
