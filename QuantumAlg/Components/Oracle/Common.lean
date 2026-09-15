/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf
public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Kets

/-!
# Common oracle components

Reusable Components-layer oracle components. Oracles exposed from this file are
metadata-free `UnitaryOperator`s or sealed oracle `UnitaryCircuit` leaves; genuinely
non-unitary projectors and blocks remain raw `HilbertOperator`s in other modules.
-/

section

namespace QuantumAlg

noncomputable section

/-- Strict event coordinate for the `(n + 1)`-qubit XOR-subroutine family. -/
def xorOracleSubroutineLabel (n : Nat) : Resource.SubroutineLabel :=
  { family := "QuantumAlg.Components.Oracle.Common"
    name := "xor"
    parameters := [n] }

/-- Stable query-coordinate name for the `(n + 1)`-qubit XOR-oracle family.
It reuses the canonical subroutine coordinate rather than defining a second
resource coordinate. -/
def xorOracleLabel (n : Nat) : Resource.SubroutineLabel :=
  xorOracleSubroutineLabel n

/-- Strict event coordinate for the `n`-qubit phase-subroutine family. -/
def phaseOracleSubroutineLabel (n : Nat) : Resource.SubroutineLabel :=
  { family := "QuantumAlg.Components.Oracle.Common"
    name := "phase"
    parameters := [n] }

/-- Stable query-coordinate name for the `n`-qubit phase-oracle family. It
reuses the canonical subroutine coordinate for marked predicates of width `n`. -/
def phaseOracleLabel (n : Nat) : Resource.SubroutineLabel :=
  phaseOracleSubroutineLabel n

namespace QSP.MultiQubit

/-! ### QPP unitary-family declarations -/

/-- Stable opaque-subroutine family for an `n`-qubit QPP signal unitary. -/
def qppOracleLabel (n : ℕ) : Resource.SubroutineLabel where
  family := "qpp"
  name := "qpp-unitary"
  parameters := [n]



/-- Literal strict event for one QPP signal-unitary query. -/
def qppOracleEvent (n : ℕ) : Resource.Event .quantum :=
  .quantumSubroutine (qppOracleLabel n).quantum

/-- Declare one QPP family member at a caller-supplied placement.

This is an explicit opaque-family trust boundary: the caller supplies the
certified semantics, while this declaration owns the fixed QPP label. -/
def qppOracleLeafAt {n : ℕ} (U : UnitaryOperator (Qubits n))
    (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.subroutine (qppOracleLabel n) systemIdx U

/-- Seal a QPP family-member operator on its canonical local placement. -/
def qppOracleLeaf {n : ℕ} (U : UnitaryOperator (Qubits n)) :
    UnitaryLeaf (Qubits n) :=
  qppOracleLeafAt U (List.range n)

end QSP.MultiQubit

namespace ShortDLP

/-- Canonical component label for one short-DLP group-operation family
member. -/
def shortDLPOracleLabel (N m ell workspaceBits : Nat) :
    Resource.SubroutineLabel :=
  { family := "short-dlp"
    name := "ekera-hastad-short-dlp-group-operation"
    parameters := [N, m, ell, workspaceBits] }

/-- Seal one short-DLP family member at a caller-supplied placement.

This Components declaration is the auditable opaque-family pairing boundary;
the caller explicitly supplies the coordinate parameters and certified
semantics, while this declaration owns their unique label construction. -/
def shortDLPOracleLeafAt {R : Register} (modulus m ell workspaceBits : Nat)
    (U : UnitaryOperator R)
    (systemIdx : List Nat) : UnitaryLeaf R :=
  UnitaryLeaf.subroutine
    (shortDLPOracleLabel modulus m ell workspaceBits) systemIdx U

end ShortDLP

variable {n : Nat}

/-! ### XOR oracles -/

/-- The basis involution underlying the XOR oracle:
`(x, b) ↦ (x, b ⊕ f x)`, with the bit flip written as `Fin.rev`. -/
def xorPerm (f : Fin (2 ^ n) -> Bool) :
    Equiv.Perm (Fin (2 ^ n) × Fin (2 ^ 1)) where
  toFun p := (p.1, if f p.1 then p.2.rev else p.2)
  invFun p := (p.1, if f p.1 then p.2.rev else p.2)
  left_inv p := by by_cases h : f p.1 <;> simp [h]
  right_inv p := by by_cases h : f p.1 <;> simp [h]

@[simp]
theorem xorPerm_apply (f : Fin (2 ^ n) -> Bool) (p : Fin (2 ^ n) × Fin (2 ^ 1)) :
    xorPerm f p = (p.1, if f p.1 then p.2.rev else p.2) :=
  rfl

/-- The XOR oracle is an involution. -/
@[simp]
theorem xorPerm_symm (f : Fin (2 ^ n) -> Bool) : (xorPerm f).symm = xorPerm f :=
  rfl

/-- The metadata-free XOR (bit-flip) oracle of `f`. -/
public def xorOracleOp (f : Fin (2 ^ n) -> Bool) : UnitaryOperator (Qubits (n + 1)) :=
  UnitaryOperator.ofPerm (prodEquiv.permCongr (xorPerm f))

theorem xorOracleOp_apply (f : Fin (2 ^ n) -> Bool)
    (ψ : HilbertVector (Qubits (n + 1))) (i : Fin (2 ^ (n + 1))) :
    (xorOracleOp f).applyVec ψ i =
      ψ (prodEquiv (xorPerm f (prodEquiv.symm i))) := by
  rw [xorOracleOp, UnitaryOperator.ofPerm_applyVec, Equiv.permCongr_apply]

/-- Action on normalized basis kets: `U_f |x⟩|b⟩ = |x⟩|b ⊕ f(x)⟩`. -/
@[simp]
theorem xorOracleOp_apply_ket (f : Fin (2 ^ n) -> Bool) (x : Fin (2 ^ n))
    (b : Fin (2 ^ 1)) :
    (xorOracleOp f).apply
        (NormalizedVector.ket (R := Qubits (n + 1)) (prodEquiv (x, b))) =
      NormalizedVector.ket (R := Qubits (n + 1))
        (prodEquiv (x, if f x then b.rev else b)) := by
  rw [xorOracleOp, UnitaryOperator.ofPerm_apply_ket]
  congr 1
  change prodEquiv ((xorPerm f).symm (prodEquiv.symm (prodEquiv (x, b)))) = _
  rw [Equiv.symm_apply_apply, xorPerm_symm, xorPerm_apply]

/-- On a `|+⟩` target the metadata-free XOR oracle acts trivially. -/
theorem xorOracleOp_apply_tensor_ketPlus (f : Fin (2 ^ n) -> Bool)
    (x : Fin (2 ^ n)) :
    (xorOracleOp f).apply
        ((NormalizedVector.ket x).tensor NormalizedVector.ketPlus) =
      (NormalizedVector.ket x).tensor NormalizedVector.ketPlus := by
  apply NormalizedVector.ext
  intro i
  change (xorOracleOp f).applyVec
      (((NormalizedVector.ket x).tensor NormalizedVector.ketPlus :
        NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1))) i =
    (((NormalizedVector.ket x).tensor NormalizedVector.ketPlus :
      NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1))) i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨y, b⟩, rfl⟩
  rw [xorOracleOp_apply, NormalizedVector.tensor_apply_prod,
    NormalizedVector.tensor_apply_prod]
  simp only [Equiv.symm_apply_apply, xorPerm_apply]
  by_cases hy : y = x
  · subst y
    by_cases h : f x <;> fin_cases b <;>
      simp [h, NormalizedVector.ketPlus_apply]
  · by_cases h : f y <;> fin_cases b <;>
      simp [h, hy, NormalizedVector.ket_apply]

namespace Gate

/-- Sealed declaration of one XOR-subroutine family member at a caller-supplied
physical placement. -/
def xorOracleLeafAt (f : Fin (2 ^ n) -> Bool) (systemIdx : List Nat) :
    UnitaryLeaf (Qubits (n + 1)) :=
  UnitaryLeaf.subroutine (xorOracleSubroutineLabel n) systemIdx (xorOracleOp f)

/-- Sealed declaration of one XOR-subroutine family member on its canonical
register placement. -/
def xorOracleLeaf (f : Fin (2 ^ n) -> Bool) : UnitaryLeaf (Qubits (n + 1)) :=
  xorOracleLeafAt f (List.range (n + 1))

/-- Resource-derived XOR oracle at a caller-supplied duplicate-free placement. -/
def xorOracleAt (f : Fin (2 ^ n) -> Bool) (systemIdx : List Nat)
    (systemIdxNodup : systemIdx.Nodup) : UnitaryCircuit (Qubits (n + 1)) :=
  UnitaryCircuit.ofLeaf (xorOracleLeafAt f systemIdx) systemIdxNodup

/-- Resource-derived implementation of the XOR oracle. -/
def xorOracle (f : Fin (2 ^ n) -> Bool) : UnitaryCircuit (Qubits (n + 1)) :=
  UnitaryCircuit.ofLeaf (xorOracleLeaf f) List.nodup_range

@[simp]
theorem xorOracle_matrix (f : Fin (2 ^ n) -> Bool) :
    (xorOracle f).matrix = xorOracleOp f :=
  rfl





@[simp]
theorem xorOracle_eventCost (f : Fin (2 ^ n) -> Bool) :
    (xorOracle f).eventCost =
      ResourcePool.singleton
        (.quantumSubroutine (xorOracleSubroutineLabel n).quantum) :=
  rfl

@[simp]
theorem xorOracle_eventDepth (f : Fin (2 ^ n) -> Bool) :
    (xorOracle f).eventDepth =
      .atom (.quantumSubroutine (xorOracleSubroutineLabel n).quantum) :=
  rfl

end Gate

variable {n : Nat}

/-! ### Phase oracles -/

/-- The concrete diagonal phase-oracle operator, certified independently of
implementation metadata. -/
def phaseOracleOp {n : Nat} (marked : Fin (2 ^ n) -> Bool) :
    UnitaryOperator (Qubits n) :=
  let op : HilbertOperator (Qubits n) :=
    fun i j => if i = j then (if marked j then -1 else 1 : ℂ) else 0
  UnitaryOperator.ofMatrix op
    (by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j
      rw [Matrix.mul_apply]
      by_cases hij : i = j
      · subst j
        by_cases hm : marked i <;>
          simp [op, Matrix.conjTranspose, Matrix.transpose, hm]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [op, Matrix.conjTranspose, Matrix.transpose, hij, hji])

/-- Sealed declaration of one phase-subroutine family member at a caller-supplied
physical placement. -/
def phaseOracleLeafAt {n : Nat} (marked : Fin (2 ^ n) -> Bool)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.subroutine (phaseOracleSubroutineLabel n) systemIdx
    (phaseOracleOp marked)

/-- Sealed declaration of one phase-subroutine family member on its canonical
register placement. -/
def phaseOracleLeaf {n : Nat} (marked : Fin (2 ^ n) -> Bool) :
    UnitaryLeaf (Qubits n) :=
  phaseOracleLeafAt marked (List.range n)

/-- The phase-oracle circuit at a caller-supplied duplicate-free placement. -/
def phaseOracleAt {n : Nat} (marked : Fin (2 ^ n) -> Bool)
    (systemIdx : List Nat) (systemIdxNodup : systemIdx.Nodup) : UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf (phaseOracleLeafAt marked systemIdx) systemIdxNodup

/-- The reusable phase-oracle circuit for a marked-set predicate. -/
def phaseOracle {n : Nat} (marked : Fin (2 ^ n) -> Bool) : UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf (phaseOracleLeaf marked) List.nodup_range

@[simp]
theorem phaseOracle_matrix {n : Nat} (marked : Fin (2 ^ n) -> Bool) :
    (phaseOracle marked).matrix = phaseOracleOp marked :=
  rfl





@[simp]
theorem phaseOracle_eventCost {n : Nat} (marked : Fin (2 ^ n) -> Bool) :
    (phaseOracle marked).eventCost =
      ResourcePool.singleton
        (.quantumSubroutine (phaseOracleSubroutineLabel n).quantum) :=
  rfl

@[simp]
theorem phaseOracle_eventDepth {n : Nat} (marked : Fin (2 ^ n) -> Bool) :
    (phaseOracle marked).eventDepth =
      .atom (.quantumSubroutine (phaseOracleSubroutineLabel n).quantum) :=
  rfl

theorem phaseOracle_apply_ket {n : Nat}
    (marked : Fin (2 ^ n) -> Bool) (j : Fin (2 ^ n)) :
    ((phaseOracleOp marked).apply (NormalizedVector.ket (R := Qubits n) j) :
        HilbertVector (Qubits n)) =
      ((if marked j then -1 else 1 : ℂ) •
        (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n))) := by
  by_cases hm : marked j
  · rw [if_pos hm]
    simp only [neg_smul, one_smul]
    apply WithLp.ofLp_injective
    funext i
    rw [show (((phaseOracleOp marked).apply
            (NormalizedVector.ket (R := Qubits n) j) : HilbertVector (Qubits n))).ofLp i =
          (phaseOracleOp marked).applyVec
            (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)) i from rfl,
      show ((-(NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n))).ofLp i) =
          (-(NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n))) i from rfl,
      UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracleOp, UnitaryOperator.ofMatrix, hm,
        NormalizedVector.ket_apply]
    · simp [phaseOracleOp, UnitaryOperator.ofMatrix,
        NormalizedVector.ket_apply, hij]
  · rw [if_neg hm]
    simp only [one_smul]
    apply WithLp.ofLp_injective
    funext i
    rw [show (((phaseOracleOp marked).apply
            (NormalizedVector.ket (R := Qubits n) j) : HilbertVector (Qubits n))).ofLp i =
          (phaseOracleOp marked).applyVec
            (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)) i from rfl,
      show ((NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)).ofLp i) =
          (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)) i from rfl,
      UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracleOp, UnitaryOperator.ofMatrix, hm,
        NormalizedVector.ket_apply]
    · simp [phaseOracleOp, UnitaryOperator.ofMatrix,
        NormalizedVector.ket_apply, hij]

end

end QuantumAlg

end
