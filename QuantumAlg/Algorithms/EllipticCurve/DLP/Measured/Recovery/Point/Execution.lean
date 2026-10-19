/-
The seven definitions construct literal fixed-context instructions without inspecting,
converting or recompiling a true-index Circuit.
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Encoding
import all QuantumAlg.Core.Execution.Unitary.StoreFilter

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original H, actual ordered Z writes, and original stored-result X member. -/
def numeratorReset (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (NumeratorMeasurement.context width)
      (NumeratorMeasurement.context width) false :=
  (Circuit.unitary (NumeratorRuntime.program width (NumeratorReset.hadamardMember width))).seq
    ((Circuit.measurementSequence (allowAllocation := false)
      (NumeratorMeasurement.readouts width)).seq
        (.branch (NumeratorMeasurement.input width) (fun value =>
          .unitary (NumeratorRuntime.program width (NumeratorReset.member width value)))))

/-- The existing complete placed controlled-arithmetic native word. -/
def controlledNative (width : Nat) (native : InPlaceControlled.NativeCircuit width) :
    Circuit (.quantum AlgorithmGate.model .empty) (InPlaceControlled.context width)
      (InPlaceControlled.context width) false :=
  .unitary (InPlaceControlled.runtimeProgram width native)

/-- The same owned supplied C is the physical resident complement of the real reset. -/
def controlledReset (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (InPlaceControlled.context width)
      (InPlaceControlled.context width) false :=
  .embed (ContextEmbedding.alongUnion (NumeratorMeasurement.context width)
    (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width))
      (numeratorReset width)

/-- Original prefix, actual reset, then the suffix selected by the same finite Store read. -/
def controlledBody (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty) (InPlaceControlled.context modulus.size)
      (InPlaceControlled.context modulus.size) false :=
  (controlledNative modulus.size (InPlaceControlled.beforeReset operation modulus prime)).seq
    ((controlledReset modulus.size).seq
      (.branch (InPlaceControlled.resultInput modulus.size) (fun value =>
        controlledNative modulus.size (InPlaceControlled.suffix operation modulus prime value))))

/-- The existing complete point native word at its unchanged physical coordinates. -/
def pointNative (width : Nat) (native : MeasuredPointAddition.NativeCircuit width) :
    Circuit (.quantum AlgorithmGate.model .empty) (MeasuredPointAddition.context width)
      (MeasuredPointAddition.context width) false :=
  .unitary (MeasuredPointAddition.runtimeProgram width native)

/-- Actual embedding retains the original resident N beside the complete arithmetic child. -/
def pointArithmetic (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) :
    Circuit (.quantum AlgorithmGate.model .empty) (MeasuredPointAddition.context modulus.size)
      (MeasuredPointAddition.context modulus.size) false :=
  .embed (ContextEmbedding.alongUnion (InPlaceControlled.context modulus.size)
    (MeasuredPointAddition.selectorContext modulus.size)
    (MeasuredPointAddition.selector_disjoint modulus.size))
      (controlledBody operation modulus prime)

/-- The literal five stages retain their order and reuse the same actual arithmetic cells. -/
def pointBody {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    Circuit (.quantum AlgorithmGate.model .empty) (MeasuredPointAddition.context p.size)
      (MeasuredPointAddition.context p.size) false :=
  (pointNative p.size (MeasuredPointAddition.beforeDivision Q)).seq
    ((pointArithmetic .division p Fact.out).seq
      ((pointNative p.size (MeasuredPointAddition.beforeMultiplication Q)).seq
        ((pointArithmetic .multiplication p Fact.out).seq
          (pointNative p.size (MeasuredPointAddition.afterMultiplication E Q)))))

/-- Each fixed native stage has precisely the existing nativeJoint stored conjugation. -/
lemma pointNative_store_matrix (width : Nat)
    (native : MeasuredPointAddition.NativeCircuit width) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (MeasuredPointAddition.context width)) :
    (((pointNative width native).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      (MeasuredPointAddition.nativeJoint (environment := environment) width Reference native :
        HilbertOperator ((MeasuredPointAddition.context width).register.prod Reference)) *
          (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix *
            (MeasuredPointAddition.nativeJoint (environment := environment) width Reference native :
              HilbertOperator ((MeasuredPointAddition.context width).register.prod
                Reference)).conjTranspose := by
  exact (congrArg DensityOperator.matrix
    (Circuit.unitary_store_filter (environment := environment) (allowAllocation := false)
      (operations := .empty) (services := .empty)
      (MeasuredPointAddition.runtimeProgram width native) state
      (fun original => original = stored))).trans
        (DensityOperator.applyUnitary_matrix _ _)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
