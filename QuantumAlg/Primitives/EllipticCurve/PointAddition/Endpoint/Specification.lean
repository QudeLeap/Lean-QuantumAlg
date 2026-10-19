/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Context
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Context
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Construction
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Input
import Mathlib.Logic.Equiv.Fintype

/-!
# Independent clean-domain ECADD problem data

The admissible local density is supported on the clean encodings of affine
points other than the fixed addend and its inverse. It may have arbitrary
coherences and arbitrary mixed/reference extensions. The prescribed columns
are the mathematical controlled group translation. A finite permutation
extension supplies a normalized target outside the promised domain without
making any claim about the implementation there. Its choice uses only the
injectivity of affine encoding and cancellation in the elliptic-curve group.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ControlledPointAddition.Execution
noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
variable [params : Arithmetic.VariableModularMul.Parameters]
local instance : NeZero params.modulus.val := ⟨Nat.ne_of_gt params.modulusPos⟩
variable (E : PrimeFieldShortWeierstrass params.modulus.val) [Fact params.modulus.val.Prime]

/-- The unchanged generic active-addition domain, including either control value. -/
def Legal (Q : AffinePoint E) := Bool × {P : AffinePoint E // P ≠ Q ∧ P ≠ AffinePoint.negate Q}

private instance (Q : AffinePoint E) : Finite (Legal E Q) := by
  unfold Legal
  infer_instance

/-- An actual clean physical basis label, using the fixed product encoding. -/
def cleanLabel (control : Bool) (P : AffinePoint E) : (rawLayout (params := params)).Basis :=
  (QubitLayout.canonical
    GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width).basisEquiv.symm
    (GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode (cleanBoundary control P))

omit [Fact params.modulus.val.Prime] in
lemma cleanLabel_injective : Function.Injective (fun value : Bool × AffinePoint E =>
    cleanLabel E value.1 value.2) := by
  intro left right same
  have registers := GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode_injective
    ((QubitLayout.canonical
      GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width).basisEquiv.symm.injective
      same)
  have control : left.1 = right.1 := congrArg (fun r => r.1.1) registers
  have words : GenericPointAddition.Pipeline.pointWords left.2 =
      GenericPointAddition.Pipeline.pointWords right.2 := congrArg (fun r => r.1.2.1.1.1) registers
  have x : left.2.x = right.2.x :=
    ZMod.val_injective params.modulus.val (congrArg (fun p => p.1.val) words)
  have y : left.2.y = right.2.y :=
    ZMod.val_injective params.modulus.val (congrArg (fun p => p.2.val) words)
  exact Prod.ext control (AffinePoint.ext_coordinates _ _ x y)

/-- The legal incoming label at its original physical wires. -/
def incoming (Q : AffinePoint E) (value : Legal E Q) : (context params.width).register.Index :=
  rawBasis (cleanLabel E value.1 value.2.1)

/-- Independent controlled group-shift label, with all auxiliary fields zero again. -/
def outgoing (Q : AffinePoint E) (value : Legal E Q) : (context params.width).register.Index :=
  rawBasis (cleanLabel E value.1
    (controlledResultPoint E Q value.1 value.2.1 value.2.2.1 value.2.2.2))

attribute [local irreducible] rawBasis cleanLabel

omit [Fact params.modulus.val.Prime] in
lemma incoming_injective (Q : AffinePoint E) : Function.Injective (incoming E Q) := by
  intro left right same
  change rawBasis (cleanLabel E left.1 left.2.1) =
    rawBasis (cleanLabel E right.1 right.2.1) at same
  have pair : (left.1, left.2.1) = (right.1, right.2.1) :=
    cleanLabel_injective E ((rawBasis (params := params)).injective same)
  exact Prod.ext (congrArg (fun value : Bool × AffinePoint E => value.1) pair)
    (Subtype.ext (congrArg (fun value : Bool × AffinePoint E => value.2) pair))

lemma outgoing_injective (Q : AffinePoint E) : Function.Injective (outgoing E Q) := by
  intro left right same
  change rawBasis (cleanLabel E left.1
      (controlledResultPoint E Q left.1 left.2.1 left.2.2.1 left.2.2.2)) =
    rawBasis (cleanLabel E right.1
      (controlledResultPoint E Q right.1 right.2.1 right.2.2.1 right.2.2.2)) at same
  have pair :
      (left.1, controlledResultPoint E Q left.1 left.2.1 left.2.2.1 left.2.2.2) =
        (right.1, controlledResultPoint E Q right.1 right.2.1 right.2.2.1 right.2.2.2) :=
    cleanLabel_injective E ((rawBasis (params := params)).injective same)
  have control : left.1 = right.1 := congrArg (fun value : Bool × AffinePoint E => value.1) pair
  have result := congrArg (fun value : Bool × AffinePoint E => value.2.toMathlib) pair
  rw [controlledResultPoint_group_law, controlledResultPoint_group_law, control] at result
  have point := WeierstrassCurve.Affine.Point.some.inj (add_right_cancel result)
  exact Prod.ext control (Subtype.ext (AffinePoint.ext_coordinates _ _ point.1 point.2))

/-- The finite extension depends solely on the two mathematically prescribed
injective label maps. -/
def semanticPermutation (Q : AffinePoint E) : Equiv.Perm (context params.width).register.Index :=
  Classical.choose (Equiv.Perm.exists_extending_pair (incoming E Q) (outgoing E Q)
    (incoming_injective E Q) (outgoing_injective E Q))

lemma semanticPermutation_incoming (Q : AffinePoint E) (value : Legal E Q) :
    semanticPermutation E Q (incoming E Q value) = outgoing E Q value :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair (incoming E Q) (outgoing E Q)
    (incoming_injective E Q) (outgoing_injective E Q)) value

/-- Metadata-free mathematical target; no program operator or event projection occurs here. -/
public def semanticOperator (Q : AffinePoint E) : UnitaryOperator (context params.width).register :=
  UnitaryOperator.ofPerm (semanticPermutation E Q).symm

/-- Every superposition/mixed state in the legal clean span is admissible. -/
public def valid (Q : AffinePoint E)
    (state : ExecutionState (QuantumAlg.Execution.Store (context params.width))
      (context params.width).register) : Prop :=
  ∀ basis, basis ∉ Set.range (incoming E Q) → state.quantumMarginal.matrix basis basis = 0

/-- Uniform source-width event bounds. The published Toffoli polynomial is retained exactly. -/
@[expose] public def resources : ResourceBudget model where
  events := publishedToffoliCountBound (Nat.clog 2 params.modulus.val) •
      ResourcePool.singleton (model := model) (.gate .toffoli) +
    circuitDepthBound params.width • ResourcePool.singleton (model := model) (.gate .cnot)
  resident := QuantumAlg.Execution.SuppliedQubits.space (logicalQubitCount params.width)
  auxiliary := QuantumAlg.Execution.SuppliedQubits.space (auxiliaryQubitCount params.width)

end
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ControlledPointAddition.Execution
