/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
public import QuantumAlg.Core.Base.Layout.Qubit
public import QuantumAlg.Core.Base.Layout.Signature
public import QuantumAlg.Util.FinPow
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Equal-width regrouping of canonical qubit circuits

Changing the arithmetic expression for the same width retains the actual
construction and physical wire identities. The binary matrix changes only by
the corresponding finite-index cast; no gate, query or workspace is added.
-/

namespace QuantumAlg.UnitaryCircuit
noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {source target : Nat}

/-- Regroup an equal number of canonical physical qubits without changing the construction. -/
public def castQubitWidth (same : source = target)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout) :
    UnitaryCircuit gates oracles (QuantumSignature.qubits target).canonicalPlacement.layout :=
  same ▸ body

/-- The regrouped binary view transports unchanged integer basis labels by the width equality. -/
public theorem castQubitWidth_binaryMatrix (same : source = target)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout) :
    (body.castQubitWidth same).binaryMatrix =
      UnitaryOperator.reindex (finCongr (congrArg (fun width => 2 ^ width) same))
        body.binaryMatrix := by
  subst target
  apply Subtype.ext
  rfl

/-- Equal-width regrouping transports the result of binary operator action
only along the supplied equality of widths. -/
public theorem castQubitWidth_binaryMatrix_apply (same : source = target)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout)
    (state : NormalizedVector (Qubits source)) :
    (body.castQubitWidth same).binaryMatrix.apply (same ▸ state) =
      same ▸ body.binaryMatrix.apply state := by
  subst target
  rfl

/-- Transport a raw binary vector along an equality of qubit widths. -/
@[expose] public def castQubitWidthVec (same : source = target)
    (state : HilbertVector (Qubits source)) : HilbertVector (Qubits target) :=
  same ▸ state

/-- Transport a canonical binary basis label along an equality of widths. -/
@[expose] public def castQubitWidthIndex (same : source = target)
    (index : Fin (2 ^ source)) : Fin (2 ^ target) :=
  finCongr (congrArg (fun width => 2 ^ width) same) index

@[simp] public theorem castQubitWidthIndex_val (same : source = target)
    (index : Fin (2 ^ source)) :
    (castQubitWidthIndex same index).val = index.val := by
  subst target
  rfl

@[simp] public theorem castQubitWidthIndex_symm (same : source = target)
    (index : Fin (2 ^ target)) :
    castQubitWidthIndex same (castQubitWidthIndex same.symm index) = index := by
  subst target
  rfl

/-- Equal-width regrouping commutes with action on arbitrary raw vectors. -/
public theorem castQubitWidth_binaryMatrix_applyVec (same : source = target)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout)
    (state : HilbertVector (Qubits source)) :
    (body.castQubitWidth same).binaryMatrix.applyVec
        (castQubitWidthVec same state) =
      castQubitWidthVec same (body.binaryMatrix.applyVec state) := by
  subst target
  rfl

/-- Raw-vector width transport evaluates at the inverse transported basis
index. -/
public theorem castQubitWidthVec_apply (same : source = target)
    (state : HilbertVector (Qubits source)) (index : Fin (2 ^ target)) :
    castQubitWidthVec same state index =
      state (castQubitWidthIndex same.symm index) := by
  subst target
  rfl

@[simp] public theorem castQubitWidthVec_self
    (state : HilbertVector (Qubits source)) :
    castQubitWidthVec rfl state = state := rfl

/-- Width transport maps a raw computational ket to the correspondingly
transported canonical binary label. -/
public theorem castQubitWidthVec_ket (same : source = target)
    (index : Fin (2 ^ source)) :
    castQubitWidthVec same
        (NormalizedVector.ket (R := Qubits source) index :
          HilbertVector (Qubits source)) =
      (NormalizedVector.ket (R := Qubits target)
        (castQubitWidthIndex same index) : HilbertVector (Qubits target)) := by
  subst target
  rfl

@[simp] public theorem castQubitWidthVec_add (same : source = target)
    (left right : HilbertVector (Qubits source)) :
    castQubitWidthVec same (left + right) =
      castQubitWidthVec same left + castQubitWidthVec same right := by
  subst target
  rfl

@[simp] public theorem castQubitWidthVec_smul (same : source = target)
    (scalar : ℂ) (state : HilbertVector (Qubits source)) :
    castQubitWidthVec same (scalar • state) =
      scalar • castQubitWidthVec same state := by
  subst target
  rfl

/-- Consecutive raw-vector width transports compose. -/
public theorem castQubitWidthVec_trans {middle : Nat}
    (first : source = middle) (second : middle = target)
    (state : HilbertVector (Qubits source)) :
    castQubitWidthVec second (castQubitWidthVec first state) =
      castQubitWidthVec (first.trans second) state := by
  subst middle
  subst target
  rfl

/-- Width transports distribute through a raw tensor when both factor
widths are transported independently. -/
public theorem castQubitWidthVec_tensor
    {leftSource leftTarget rightSource rightTarget : Nat}
    (leftSame : leftSource = leftTarget)
    (rightSame : rightSource = rightTarget)
    (left : HilbertVector (Qubits leftSource))
    (right : HilbertVector (Qubits rightSource)) :
    castQubitWidthVec (by
      subst leftTarget
      subst rightTarget
      rfl : leftSource + rightSource = leftTarget + rightTarget)
        (HilbertVector.tensor left right) =
      HilbertVector.tensor (castQubitWidthVec leftSame left)
        (castQubitWidthVec rightSame right) := by
  subst leftTarget
  subst rightTarget
  rfl

/-- Transporting the left tensor factor before assembly is the same as
transporting the assembled vector. -/
public theorem castQubitWidthVec_tensor_left
    {leftSource leftTarget rightWidth finalWidth : Nat}
    (leftSame : leftSource = leftTarget)
    (finalSame : leftTarget + rightWidth = finalWidth)
    (left : HilbertVector (Qubits leftSource))
    (right : HilbertVector (Qubits rightWidth)) :
    castQubitWidthVec finalSame
        (HilbertVector.tensor (castQubitWidthVec leftSame left) right) =
      castQubitWidthVec (by
        subst leftTarget
        exact finalSame : leftSource + rightWidth = finalWidth)
        (HilbertVector.tensor left right) := by
  subst leftTarget
  rfl

/-- Transporting the right tensor factor before assembly is the same as
transporting the assembled vector. -/
public theorem castQubitWidthVec_tensor_right
    {leftWidth rightSource rightTarget finalWidth : Nat}
    (rightSame : rightSource = rightTarget)
    (finalSame : leftWidth + rightTarget = finalWidth)
    (left : HilbertVector (Qubits leftWidth))
    (right : HilbertVector (Qubits rightSource)) :
    castQubitWidthVec finalSame
        (HilbertVector.tensor left (castQubitWidthVec rightSame right)) =
      castQubitWidthVec (by
        subst rightTarget
        exact finalSame : leftWidth + rightSource = finalWidth)
        (HilbertVector.tensor left right) := by
  subst rightTarget
  rfl

/-- Two surrounding right-associated tensor factors preserve an inner width
transport. -/
public theorem castQubitWidthVec_tensor_two_right
    {outerWidth innerLeftWidth sourceWidth targetWidth finalWidth : Nat}
    (innerSame : sourceWidth = targetWidth)
    (sourceSame : outerWidth + (innerLeftWidth + sourceWidth) = finalWidth)
    (targetSame : outerWidth + (innerLeftWidth + targetWidth) = finalWidth)
    (outer : HilbertVector (Qubits outerWidth))
    (innerLeft : HilbertVector (Qubits innerLeftWidth))
    (sourceState : HilbertVector (Qubits sourceWidth)) :
    castQubitWidthVec sourceSame
        (HilbertVector.tensor outer
          (HilbertVector.tensor innerLeft sourceState)) =
      castQubitWidthVec targetSame
        (HilbertVector.tensor outer
          (HilbertVector.tensor innerLeft
            (castQubitWidthVec innerSame sourceState))) := by
  subst targetWidth
  rfl

/-- Three surrounding right-associated tensor factors preserve an inner
width transport. -/
public theorem castQubitWidthVec_tensor_three_right
    {outerWidth firstWidth middleWidth sourceWidth targetWidth finalWidth : Nat}
    (innerSame : sourceWidth = targetWidth)
    (sourceSame : outerWidth + (firstWidth + (middleWidth + sourceWidth)) = finalWidth)
    (targetSame : outerWidth + (firstWidth + (middleWidth + targetWidth)) = finalWidth)
    (outer : HilbertVector (Qubits outerWidth))
    (first : HilbertVector (Qubits firstWidth))
    (middle : HilbertVector (Qubits middleWidth))
    (sourceState : HilbertVector (Qubits sourceWidth)) :
    castQubitWidthVec sourceSame
        (HilbertVector.tensor outer
          (HilbertVector.tensor first
            (HilbertVector.tensor middle sourceState))) =
      castQubitWidthVec targetSame
        (HilbertVector.tensor outer
          (HilbertVector.tensor first
            (HilbertVector.tensor middle
              (castQubitWidthVec innerSame sourceState)))) := by
  subst targetWidth
  rfl

public theorem prodEquiv_value {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) :
    (prodEquiv (m := leftWidth) (n := rightWidth) (left, right)).val =
      right.val + 2 ^ rightWidth * left.val := rfl

/-- Raw binary tensors are associative after transporting the equal total
width; the physical basis order is unchanged. -/
public theorem castQubitWidthVec_tensor_assoc {m n p : Nat}
    (left : HilbertVector (Qubits m))
    (middle : HilbertVector (Qubits n))
    (right : HilbertVector (Qubits p)) :
    castQubitWidthVec (by omega : (m + n) + p = m + (n + p))
        (HilbertVector.tensor (HilbertVector.tensor left middle) right) =
      HilbertVector.tensor left (HilbertVector.tensor middle right) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := m) (n := n + p)).surjective index with
    ⟨⟨leftIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := n) (n := p)).surjective tailIndex with
    ⟨⟨middleIndex, rightIndex⟩, rfl⟩
  have indexSame :
      castQubitWidthIndex (by omega : m + (n + p) = (m + n) + p)
          (prodEquiv (m := m) (n := n + p)
            (leftIndex,
              prodEquiv (m := n) (n := p) (middleIndex, rightIndex))) =
        prodEquiv (m := m + n) (n := p)
          (prodEquiv (m := m) (n := n) (leftIndex, middleIndex), rightIndex) := by
    apply Fin.ext
    simp only [castQubitWidthIndex_val, prodEquiv_value, pow_add]
    ring
  rw [castQubitWidthVec_apply]
  change
    (HilbertVector.tensor (HilbertVector.tensor left middle) right)
        (castQubitWidthIndex (by omega : m + (n + p) = (m + n) + p)
          (prodEquiv (m := m) (n := n + p)
            (leftIndex,
              prodEquiv (m := n) (n := p) (middleIndex, rightIndex)))) = _
  rw [indexSame]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- Rebracket five ordered physical factors without permuting any binary
basis coordinate. -/
public theorem castQubitWidthVec_tensor_rebracket5
    {highWidth middleWidth suffixWidth : Nat}
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    castQubitWidthVec (by omega :
      (highWidth + (1 + middleWidth)) + (1 + suffixWidth) =
        highWidth + (1 + (middleWidth + (1 + suffixWidth))))
      (HilbertVector.tensor
        (HilbertVector.tensor high (HilbertVector.tensor first middle))
        (HilbertVector.tensor second suffix)) =
      castQubitWidthVec (by omega :
        (highWidth + ((1 + middleWidth) + 1)) + suffixWidth =
          highWidth + (1 + (middleWidth + (1 + suffixWidth))))
        (HilbertVector.tensor
          (HilbertVector.tensor high
            (HilbertVector.tensor (HilbertVector.tensor first middle) second))
          suffix) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := highWidth)
    (n := 1 + (middleWidth + (1 + suffixWidth)))).surjective index with
    ⟨⟨highIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))).surjective
      tailIndex with ⟨⟨firstIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := middleWidth) (n := 1 + suffixWidth)).surjective
      tailIndex with ⟨⟨middleIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := suffixWidth)).surjective tailIndex with
    ⟨⟨secondIndex, suffixIndex⟩, rfl⟩
  have leftIndexSame :
      castQubitWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + (1 + middleWidth)) + (1 + suffixWidth))
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + (1 + middleWidth))
          (n := 1 + suffixWidth)
          ((prodEquiv (m := highWidth) (n := 1 + middleWidth)
            (highIndex, prodEquiv (m := 1) (n := middleWidth)
              (firstIndex, middleIndex))),
            prodEquiv (m := 1) (n := suffixWidth)
              (secondIndex, suffixIndex)) := by
    apply Fin.ext
    simp only [castQubitWidthIndex_val, prodEquiv_value, pow_add]
    ring
  have rightIndexSame :
      castQubitWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + ((1 + middleWidth) + 1)) + suffixWidth)
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + ((1 + middleWidth) + 1))
          (n := suffixWidth)
          ((prodEquiv (m := highWidth) (n := (1 + middleWidth) + 1)
            (highIndex,
              prodEquiv (m := 1 + middleWidth) (n := 1)
                (prodEquiv (m := 1) (n := middleWidth)
                  (firstIndex, middleIndex), secondIndex))),
            suffixIndex) := by
    apply Fin.ext
    simp only [castQubitWidthIndex_val, prodEquiv_value, pow_add]
    ring
  rw [castQubitWidthVec_apply, leftIndexSame,
    castQubitWidthVec_apply, rightIndexSame]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- Rebracket a fully right-associated five-factor vector into the concrete
shape used by separated-wire assembly, without permuting basis coordinates. -/
public theorem castQubitWidthVec_tensor_right_to_separated5
    {highWidth middleWidth suffixWidth : Nat}
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    HilbertVector.tensor high
        (HilbertVector.tensor first
          (HilbertVector.tensor middle
            (HilbertVector.tensor second suffix))) =
      castQubitWidthVec (by omega :
        (highWidth + ((1 + middleWidth) + 1)) + suffixWidth =
          highWidth + (1 + (middleWidth + (1 + suffixWidth))))
        (HilbertVector.tensor
          (HilbertVector.tensor high
            (HilbertVector.tensor (HilbertVector.tensor first middle) second))
          suffix) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := highWidth)
    (n := 1 + (middleWidth + (1 + suffixWidth)))).surjective index with
    ⟨⟨highIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))).surjective
      tailIndex with ⟨⟨firstIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := middleWidth) (n := 1 + suffixWidth)).surjective
      tailIndex with ⟨⟨middleIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := suffixWidth)).surjective tailIndex with
    ⟨⟨secondIndex, suffixIndex⟩, rfl⟩
  have indexSame :
      castQubitWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + ((1 + middleWidth) + 1)) + suffixWidth)
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + ((1 + middleWidth) + 1))
          (n := suffixWidth)
          ((prodEquiv (m := highWidth) (n := (1 + middleWidth) + 1)
            (highIndex,
              prodEquiv (m := 1 + middleWidth) (n := 1)
                (prodEquiv (m := 1) (n := middleWidth)
                  (firstIndex, middleIndex), secondIndex))),
            suffixIndex) := by
    apply Fin.ext
    simp only [castQubitWidthIndex_val, prodEquiv_value, pow_add]
    ring
  rw [castQubitWidthVec_apply, indexSame]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- Transporting a normalized binary state along a width equality evaluates
at the inverse transported basis index. -/
public theorem castQubitWidth_state_apply (same : source = target)
    (state : NormalizedVector (Qubits source)) (index : Fin (2 ^ target)) :
    (same ▸ state) index =
      state ((finCongr (congrArg (fun width => 2 ^ width) same)).symm index) := by
  subst target
  rfl

/-- A transported computational-basis ket is the ket at the transported
binary label. -/
public theorem castQubitWidth_ket (same : source = target)
    (index : Fin (2 ^ source)) :
    same ▸ (NormalizedVector.ket (R := Qubits source) index) =
      NormalizedVector.ket
        (R := Qubits target)
        (finCongr (congrArg (fun width => 2 ^ width) same) index) := by
  subst target
  rfl

/-- Regrouping transports normalized states only by the width equality; the
actual circuit action is unchanged. -/
public theorem castQubitWidth_applyNormalized (same : source = target)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout)
    (state : NormalizedVector
      (QuantumSignature.qubits source).canonicalPlacement.layout.register) :
    (body.castQubitWidth same).applyNormalized (same ▸ state) =
      same ▸ body.applyNormalized state := by
  subst target
  rfl

/-- Regrouping retains the full actual occurrence sequence. -/
public theorem castQubitWidth_eventTrace (same : source = target)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout) :
    (body.castQubitWidth same).eventTrace = body.eventTrace := by
  subst target
  rfl

/-- Regrouping retains the complete native and query resource pool. -/
public theorem castQubitWidth_eventCost (same : source = target)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout) :
    (body.castQubitWidth same).eventCost = body.eventCost := by
  subst target
  rfl

/-- Every dependency is retained when the equal-width interface is regrouped. -/
public theorem castQubitWidth_evaluatedEventDepth (same : source = target)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits source).canonicalPlacement.layout)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (body.castQubitWidth same).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  subst target
  rfl

/-- Regroup an equal-width circuit whose public carrier is expressed through
the canonical typed-qubit layout. -/
public def castCanonicalQubitWidth (same : source = target)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source).toQuantum) :
    UnitaryCircuit gates oracles (QubitLayout.canonical target).toQuantum :=
  same ▸ body

/-- Equal-width canonical-layout regrouping transports normalized states. -/
public theorem castCanonicalQubitWidth_applyNormalized (same : source = target)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source).toQuantum)
    (state : NormalizedVector (QubitLayout.canonical source).toQuantum.register) :
    (body.castCanonicalQubitWidth same).applyNormalized (same ▸ state) =
      same ▸ body.applyNormalized state := by
  subst target
  rfl

/-- Transporting a canonical physical basis ket changes only its certified
binary width and retains the corresponding integer label. -/
public theorem castCanonicalQubitWidth_ket (same : source = target)
    (index : Fin (2 ^ source)) :
    same ▸ NormalizedVector.ket
        ((QubitLayout.canonical source).basisEquiv.symm index) =
      NormalizedVector.ket
        ((QubitLayout.canonical target).basisEquiv.symm
          (castQubitWidthIndex same index)) := by
  subst target
  rfl

/-- Equal-width canonical-layout regrouping retains the full event pool. -/
public theorem castCanonicalQubitWidth_eventCost (same : source = target)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source).toQuantum) :
    (body.castCanonicalQubitWidth same).eventCost = body.eventCost := by
  subst target
  rfl

/-- Equal-width canonical-layout regrouping retains the ordered native events. -/
public theorem castCanonicalQubitWidth_eventTrace (same : source = target)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source).toQuantum) :
    (body.castCanonicalQubitWidth same).eventTrace = body.eventTrace := by
  subst target
  rfl

/-- Equal-width canonical-layout regrouping retains dependency depth. -/
public theorem castCanonicalQubitWidth_evaluatedEventDepth (same : source = target)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical source).toQuantum)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (body.castCanonicalQubitWidth same).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  subst target
  rfl

end
end QuantumAlg.UnitaryCircuit
