/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Final.Correctness
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Lookup

/-!
# The actual native runtime lookup reads the five words constructed in the same Store

The runtime source is the original real array cell. Its two-part full
address and nominal word decoding select exactly the canonical group word
at that address. The native lookup matrix therefore gives the original
dirty-target XOR on arbitrary coherent external-reference families.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.EllipticCurve
open EncodedBit.WindowLookup
open scoped BigOperators

noncomputable section

variable {ctx : RuntimeCtx .quantum} {wordWidth addressWidth : Nat}
  (frame : TableFrame ctx wordWidth (2 ^ (addressWidth + 1)))

/-- A runtime query reads precisely the existing constructed physical column. -/
def runtimeSource (column : Fin 5) : CInputRef ctx
    (.fixedVector (2 ^ (addressWidth + 1)) (.unsignedWord wordWidth)) :=
  .storage (frame.finishColumns column).toCStorageRef

/-- Independent original group-word specification at the full untruncated runtime address. -/
def pointWordTable (curve : CurveSpec wordWidth) (point : Point curve) (column : Fin 5)
    (top : Bool) (address : Fin (2 ^ addressWidth)) : Fin (2 ^ wordWidth) :=
  RuntimeTable.wordEncoding
    (pointFiveWords curve ((RuntimeTable.index top address).val • point) column)

/-- The same actual stored column supplies the canonical requested point word at every address. -/
lemma runtimeTableValue_eq_pointWord (curve : CurveSpec wordWidth) (point : Point curve)
    (store : Store ctx) (values : TableValue curve frame point store)
    (column : Fin 5) (top : Bool) (address : Fin (2 ^ addressWidth)) :
    RuntimeTable.tableValue (store.read (frame.runtimeSource column)) top address =
      pointWordTable curve point column top address := by
  rw [RuntimeTable.tableValue_read]
  exact congrArg RuntimeTable.wordEncoding (values (RuntimeTable.index top address) column)

/-- The complete runtime table function is attached to this same real constructed Store. -/
lemma runtimeTableValue_eq_pointWords (curve : CurveSpec wordWidth) (point : Point curve)
    (store : Store ctx) (values : TableValue curve frame point store) (column : Fin 5) :
    RuntimeTable.tableValue (store.read (frame.runtimeSource column)) =
      pointWordTable curve point column := by
  funext top address
  exact frame.runtimeTableValue_eq_pointWord curve point store values column top address

/-- The actual selected native matrix loads those same original group words by dirty-target XOR. -/
lemma constructedLookup_coherent_reference (curve : CurveSpec wordWidth) (point : Point curve)
    (store : Store ctx) (values : TableValue curve frame point store) (column : Fin 5)
    {Data : Type} {encoding : BinaryLabelEncoding Data} {oracles : OracleModel}
    (selector : SelectorFrame encoding addressWidth) (target : LookupTarget selector wordWidth)
    (physical : QubitLayout encoding.width) (height : Nat) (covered : wordWidth ≤ 2 ^ height)
    (environment : oracles.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (clean : ∀ label, selector.CleanFrom 0 (state label))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (splitLookupReferenceOperator selector physical oracles target
      (RuntimeTable.tableValue (store.read (frame.runtimeSource column))) height environment
        Reference).applyVec
      (∑ label, amplitude label •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (state label)), reference label)).vec) =
      ∑ label, amplitude label •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode
            (splitLookupStep selector target (pointWordTable curve point column) (state label))),
              reference label)).vec := by
  have actual := RuntimeTable.lookupBranch_coherent_reference (frame.runtimeSource column) store
    selector target physical height covered environment state clean reference amplitude
  have same := frame.runtimeTableValue_eq_pointWords curve point store values column
  rw [same] at actual ⊢
  exact actual

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
