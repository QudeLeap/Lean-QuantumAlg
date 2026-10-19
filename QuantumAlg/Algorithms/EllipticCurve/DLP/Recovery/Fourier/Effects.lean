/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Exponents
import all QuantumAlg.Util.EllipticCurve
import all QuantumAlg.Util.ExceptionalOffsetAveraging
import all QuantumAlg.Core.Base.Gate.Effect.Embedding
import all QuantumAlg.Core.Base.Gate.Effect.Support
import all QuantumAlg.Core.Base.Gate.Effect.Extension
import all QuantumAlg.Core.Base.Gate.Effect.Unitary
import all QuantumAlg.Core.Execution.Measurement.Effect

/-!
# Original full-group branch effects and retained Fourier readout

The original exponent pairs, including source padding, map to their exact
full-group values. Their finite image includes the identity whenever it is an
output; the action itself is not assumed injective. The ordered exponent labels
and arbitrary reference are retained. The certified effect and its complete
subnormalized weight identity are unchanged mathematical declarations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

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
lemma idealOracleEmbedding_injective (problem : KnownOrderProblem E.GroupPoint)
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
    (UnitaryOperator.prodTensor ((exponentReadoutCircuit problem).binaryMatrix
      OracleModel.emptyInterpretation)
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

private lemma extension_inner_right {R S : Register} (embedding : S.Index → R.Index)
    (vector : HilbertVector S) (other : HilbertVector R) :
    inner ℂ (Effect.extensionVector embedding vector) other =
      inner ℂ vector (WithLp.toLp 2 (fun index => other (embedding index))) := by
  classical
  simp only [Effect.extensionVector, sum_inner, inner_smul_left]
  simp [PiLp.inner_apply, RCLike.inner_apply, NormalizedVector.ket_apply, mul_comm]

private lemma compress_weight_subnormalized {R S : Register}
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
lemma idealBranchEffect_weight (problem : KnownOrderProblem E.GroupPoint)
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

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
