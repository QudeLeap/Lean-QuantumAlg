/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Native
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Runtime

/-!
# Actual measured affine point-addition execution

Both measured arithmetic calls execute their original H/Z/store/reset
instructions in the same allocated context and reuse the same finite cells.
The internal selector is physically framed beside those instructions.
Every other stage executes its actual placed native circuit; neither control
is measured [LYL+26, sec_point_add/sec_point_add.tex:52-121].
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution ContextUnion MeasuredUncompute

/-- Execute the complete native word at its unchanged physical identities in the real context. -/
def runtimeProgram (width : Nat) (native : NativeCircuit width) :
    UnitaryCircuit AlgorithmGate.model .empty (context width).quantumLayout :=
  UnitaryCircuit.placeAt (nativeLayout width).toQuantum (context width).quantumLayout
    (nativePosition width) (nativePosition_dimensions width) native

/-- Exact matrix entries read the complete original physical placement. -/
lemma runtimeProgram_matrix (width : Nat) (native : NativeCircuit width)
    (row column : (context width).register.Index) :
    ((runtimeProgram width native).matrix environment) row column =
      (native.matrix environment) (nativeBasis width row) (nativeBasis width column) := by
  rw [runtimeProgram, UnitaryCircuit.placeAt_matrix]
  exact UnitaryCircuit.operatorAt_entry_of_surjective _ _ _ _
    (nativePosition_surjective width) _ row column

/-- Binary matrix entries use the original all-label frame grouping at every runtime coordinate. -/
lemma runtimeProgram_binary_matrix (width : Nat) (native : NativeCircuit width)
    (row column : (context width).register.Index) :
    ((runtimeProgram width native).matrix environment) row column =
      (native.binaryMatrix environment) (basis width row) (basis width column) := by
  rw [runtimeProgram_matrix, pointNativeBasis_eq_basis, pointNativeBasis_eq_basis]
  rfl

/-- Physical placement preserves the ordered actual native trace. -/
lemma runtimeProgram_trace (width : Nat) (native : NativeCircuit width) :
    (runtimeProgram width native).eventTrace = native.eventTrace :=
  UnitaryCircuit.placeAt_eventTrace _ _ _ _ _

/-- Every actual native coordinate keeps exactly its original multiplicity. -/
lemma runtimeProgram_cost (width : Nat) (native : NativeCircuit width) :
    (runtimeProgram width native).eventCost = native.eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

/-- The typed unitary instruction executes exactly the physically placed native word. -/
def nativeCode (width : Nat) (native : NativeCircuit width) (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context width) (context width) allowAllocation :=
  .unitary (runtimeProgram width native)

/-- The same accepted measured arithmetic body retains N as one real owned resident qubit. -/
def arithmetic (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context modulus.size) (context modulus.size)
      allowAllocation :=
  .embed (ContextEmbedding.alongUnion (InPlaceControlled.context modulus.size)
    (selectorContext modulus.size) (selector_disjoint modulus.size))
      (InPlaceControlled.body operation modulus prime (allowAllocation := false))

/-- The actual body performs division, reachable-arm multiplication, and full native cleanup. -/
def body {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context p.size) (context p.size)
      allowAllocation :=
  .seq (nativeCode p.size (beforeDivision Q) allowAllocation)
    (.seq (arithmetic .division p Fact.out allowAllocation)
      (.seq (nativeCode p.size (beforeMultiplication Q) allowAllocation)
        (.seq (arithmetic .multiplication p Fact.out allowAllocation)
          (nativeCode p.size (afterMultiplication E Q) allowAllocation))))

/-- The original five stages keep exactly the complete already allocated point context. -/
lemma body_visited {allowAllocation : Bool} {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (path : (body E Q allowAllocation).Path) :
    (body E Q allowAllocation).visitedContexts path =
      [context p.size, context p.size, context p.size, context p.size, context p.size] := rfl

/-- The complete listing includes both real controls and all reused classical result cells. -/
def output (width : Nat) : Output (context width) (.fixedVector width (.finite 2)) :=
  Output.all (context width) (.read (resultInput width))

lemma output_listing (width : Nat) : (output width).listing = (context width).keys :=
  Output.all_listing _ _

lemma output_read (width : Nat) (store : Store (context width)) :
    (output width).eval store = store.read (resultInput width) :=
  Output.all_eval _ _ _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
