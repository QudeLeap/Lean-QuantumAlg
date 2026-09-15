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

open Execution ContextUnion MeasuredUncompute

/-- The native matrix follows the actual Frame/C/N basis and complete resident footprint. -/
def runtimeProgram (width : Nat) (native : UnitaryCircuit (Qubits (encoding width).width)) :
    UnitaryCircuit (context width).register :=
  (UnitaryCircuit.reindex (basis width).symm native).seq
    (.identity (context width).register (context width).physicalIdx (context width).identitiesNodup)

theorem runtimeProgram_physical (width : Nat)
    (native : UnitaryCircuit (Qubits (encoding width).width))
    (within : native.physical_idx ⊆ List.range (encoding width).width) :
    (runtimeProgram width native).physical_idx = (context width).physicalIdx := by
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  intro wire present
  exact native_contained width (within present)

theorem runtimeProgram_matrix (width : Nat)
    (native : UnitaryCircuit (Qubits (encoding width).width))
    (row column : (context width).register.Index) :
    (runtimeProgram width native).matrix row column =
      native.matrix (basis width row) (basis width column) := by
  have matrix : ((runtimeProgram width native).matrix : HilbertOperator (context width).register) =
      Matrix.reindex (basis width).symm (basis width).symm
        (native.matrix : HilbertOperator (Qubits (encoding width).width)) := by
    change (1 : HilbertOperator (context width).register) * _ = _
    exact Matrix.one_mul _
  rw [matrix]
  rfl

theorem runtimeProgram_trace (width : Nat)
    (native : UnitaryCircuit (Qubits (encoding width).width)) :
    (runtimeProgram width native).eventTrace = native.eventTrace := by
  rw [runtimeProgram, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.reindex_eventTrace]
  exact List.append_nil _

theorem runtimeProgram_cost (width : Nat)
    (native : UnitaryCircuit (Qubits (encoding width).width)) :
    (runtimeProgram width native).eventCost = native.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, runtimeProgram_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- One actual unitary instruction executes exactly the placed native body. -/
def nativeCode (width : Nat) (native : UnitaryCircuit (Qubits (encoding width).width))
    (within : native.physical_idx ⊆ List.range (encoding width).width) :
    Circuit (context width) (context width) :=
  .unitary (runtimeProgram width native) (runtimeProgram_physical width native within)

/-- The same accepted measured arithmetic body retains N as one real owned resident qubit. -/
def arithmetic (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus) :
    Circuit (context modulus.size) (context modulus.size) :=
  frameLocal (InPlaceControlled.body operation modulus prime)
    (InPlaceControlled.body_isLocal operation modulus prime)
    (selectorContext modulus.size) (selector_disjoint modulus.size)

theorem arithmetic_isLocal (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) : (arithmetic operation modulus prime).IsLocal :=
  frameLocal_isLocal _ _ _ _

/-- The actual body performs division, reachable-arm multiplication, and full native cleanup. -/
def body {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    Circuit (context p.size) (context p.size) :=
  .seq (nativeCode p.size (beforeDivision Q) (beforeDivision_within Q))
    (.seq (arithmetic .division p Fact.out)
      (.seq (nativeCode p.size (beforeMultiplication Q) (beforeMultiplication_within Q))
        (.seq (arithmetic .multiplication p Fact.out)
          (nativeCode p.size (afterMultiplication E Q) (afterMultiplication_within E Q)))))

/-- No stage allocates or discards a quantum bank or a finite outcome cell. -/
theorem body_isLocal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : (body E Q).IsLocal :=
  ⟨trivial, arithmetic_isLocal _ _ _, trivial, arithmetic_isLocal _ _ _, trivial⟩

/-- The complete listing includes both real controls and all reused classical result cells. -/
def output (width : Nat) : Output (context width) (.fixedVector width (.finite 2)) :=
  Output.all (context width) (.read (resultInput width))

theorem output_listing (width : Nat) : (output width).listing = (context width).keys :=
  Output.all_listing _ _

theorem output_read (width : Nat) (store : Store (context width)) :
    (output width).eval store = store.read (resultInput width) :=
  Output.all_eval _ _ _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
