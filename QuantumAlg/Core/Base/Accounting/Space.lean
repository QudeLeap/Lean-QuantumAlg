/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Kind
public import QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.Accounting.Shape
public import QuantumAlg.Core.Base.Layout.Quantum

/-!
# Kind-indexed live-space pools

`SpacePool kind` is separate from the event ledger. Classical storage enters
through a closed `CShape` and contributes its encoded bit width. Quantum
storage enters through an actual `QuantumLayout` and counts its systems
separately at each positive dimension. Dimension two counts qubits; one
qutrit contributes only to the dimension-three coordinate.

Physical identities and their uniqueness belong to the layout. The native
space pool has one system-count coordinate per dimension and contains no
fault-tolerant or routing conversion.

IEC byte units are lossless display conversions only.  They never become event
or space coordinates, and a non-integral byte quantity retains its remainder
in bits.
-/

section

namespace QuantumAlg

/-- Live capacity indexed by the axes admitted for a problem kind. -/
public abbrev SpacePool (kind : ProblemKind) := SpaceAxis kind → Nat

namespace SpacePool

/-- Read one exact proof-level capacity coordinate. -/
@[expose]
public def count {kind : ProblemKind} (axis : SpaceAxis kind) (pool : SpacePool kind) : Nat :=
  pool axis

/-- Build a visible kind-indexed space budget from its native axis values. -/
def ofAxes {kind : ProblemKind} (f : SpaceAxis kind → Nat) : SpacePool kind :=
  f

/-- Pointwise maximum, used by sequential and alternative control flow. -/
@[expose] public def max {kind : ProblemKind} (left right : SpacePool kind) : SpacePool kind :=
  fun axis => Nat.max (left axis) (right axis)

@[ext] lemma ext {kind : ProblemKind} {left right : SpacePool kind}
    (equal : ∀ axis, left axis = right axis) : left = right :=
  funext equal

@[simp] lemma count_zero {kind : ProblemKind} (axis : SpaceAxis kind) :
    count axis (0 : SpacePool kind) = 0 := rfl

@[simp] lemma count_add {kind : ProblemKind} (axis : SpaceAxis kind)
    (left right : SpacePool kind) :
    count axis (left + right) = count axis left + count axis right := rfl

@[simp] lemma count_ofAxes {kind : ProblemKind} (axis : SpaceAxis kind)
    (f : SpaceAxis kind → Nat) :
    count axis (ofAxes f) = f axis := rfl

/-- Space-pool order is exactly natural-number order at every native axis. -/
lemma le_iff_count {kind : ProblemKind} {left right : SpacePool kind} :
    left ≤ right ↔ ∀ axis, count axis left ≤ count axis right :=
  Iff.rfl

@[simp] lemma ofAxes_le_iff {kind : ProblemKind}
    (f : SpaceAxis kind → Nat) (pool : SpacePool kind) :
    ofAxes f ≤ pool ↔ ∀ axis, f axis ≤ count axis pool :=
  Iff.rfl

@[simp] lemma le_ofAxes_iff {kind : ProblemKind}
    (pool : SpacePool kind) (f : SpaceAxis kind → Nat) :
    pool ≤ ofAxes f ↔ ∀ axis, count axis pool ≤ f axis :=
  Iff.rfl

@[simp] lemma count_max {kind : ProblemKind} (axis : SpaceAxis kind)
    (left right : SpacePool kind) :
    count axis (max left right) = Nat.max (count axis left) (count axis right) := rfl

/-- Either input is bounded by its pointwise maximum. -/
lemma le_max_left {kind : ProblemKind} (left right : SpacePool kind) :
    left ≤ max left right :=
  fun axis => Nat.le_max_left (left axis) (right axis)

/-- Either input is bounded by its pointwise maximum. -/
lemma le_max_right {kind : ProblemKind} (left right : SpacePool kind) :
    right ≤ max left right :=
  fun axis => Nat.le_max_right (left axis) (right axis)

/-- Pointwise maximum is the least common upper bound. -/
lemma max_le {kind : ProblemKind} {left right upper : SpacePool kind}
    (leftBound : left ≤ upper) (rightBound : right ≤ upper) :
    max left right ≤ upper :=
  fun axis => Nat.max_le.mpr ⟨leftBound axis, rightBound axis⟩

/-- A pointwise maximum reduces to its right argument when the left pool is
already bounded by it. -/
lemma max_eq_right {kind : ProblemKind} {left right : SpacePool kind}
    (bound : left ≤ right) : max left right = right := by
  ext axis
  exact Nat.max_eq_right (bound axis)

/-- A pointwise maximum reduces to its left argument when the right pool is
already bounded by it. -/
lemma max_eq_left {kind : ProblemKind} {left right : SpacePool kind}
    (bound : right ≤ left) : max left right = left := by
  ext axis
  exact Nat.max_eq_left (bound axis)

@[simp] lemma max_self {kind : ProblemKind} (pool : SpacePool kind) :
    max pool pool = pool := by
  ext axis
  simp [max]

lemma max_comm {kind : ProblemKind} (left right : SpacePool kind) :
    max left right = max right left := by
  ext axis
  exact Nat.max_comm (left axis) (right axis)

lemma max_assoc {kind : ProblemKind} (first second third : SpacePool kind) :
    max (max first second) third = max first (max second third) := by
  ext axis
  exact Nat.max_assoc (first axis) (second axis) (third axis)

@[simp] lemma max_zero {kind : ProblemKind} (pool : SpacePool kind) :
    max pool 0 = pool := by
  ext axis
  simp [max]

@[simp] lemma zero_max {kind : ProblemKind} (pool : SpacePool kind) :
    max 0 pool = pool := by
  ext axis
  simp [max]

/-- A closed classical shape contributes only to the classical-bit axis. -/
public def ofShape {kind : ProblemKind} (shape : CShape) : SpacePool kind :=
  fun axis =>
    match axis with
    | .classicalBits => shape.bitWidth
    | .quantumSystems _ => 0

@[simp] public lemma count_classicalBits_ofShape {kind : ProblemKind} (shape : CShape) :
    count (.classicalBits : SpaceAxis kind) (ofShape shape) = shape.bitWidth := by rfl

@[simp] public lemma count_quantumSystems_ofShape (shape : CShape) (dimension : ℕ+) :
    count (.quantumSystems dimension) (ofShape shape : SpacePool .quantum) = 0 := by rfl

/-- Embed classical live capacity without relabeling it as quantum storage. -/
def liftClassical (pool : SpacePool .classical) : SpacePool .quantum
  | .classicalBits => pool .classicalBits
  | .quantumSystems _ => 0

@[simp] lemma count_classicalBits_liftClassical (pool : SpacePool .classical) :
    count .classicalBits (liftClassical pool) = count .classicalBits pool := rfl

@[simp] lemma count_quantumSystems_liftClassical (pool : SpacePool .classical)
    (dimension : ℕ+) :
    count (.quantumSystems dimension) (liftClassical pool) = 0 := rfl

@[simp] lemma liftClassical_zero :
    liftClassical (0 : SpacePool .classical) = 0 := by
  ext axis
  cases axis <;> simp [liftClassical]

@[simp] lemma liftClassical_add (left right : SpacePool .classical) :
    liftClassical (left + right) = liftClassical left + liftClassical right := by
  ext axis
  cases axis <;> rfl

@[simp] lemma liftClassical_max (left right : SpacePool .classical) :
    liftClassical (max left right) = max (liftClassical left) (liftClassical right) := by
  ext axis
  cases axis <;> rfl

/-- Classical lifting reflects the pointwise capacity order exactly. -/
@[simp] lemma liftClassical_le_liftClassical_iff
    {left right : SpacePool .classical} :
    liftClassical left ≤ liftClassical right ↔ left ≤ right := by
  constructor
  · intro bound axis
    cases axis
    exact bound .classicalBits
  · intro bound axis
    cases axis with
    | classicalBits => exact bound .classicalBits
    | quantumSystems _ => exact Nat.le_refl 0

/-- Native live space derived from the dimensions of the actual layout wires. -/
@[expose]
public def ofQuantumLayout {systemCount : Nat}
    (layout : QuantumLayout systemCount) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => layout.dimensionCount dimension

@[simp] public lemma count_classicalBits_ofQuantumLayout {systemCount : Nat}
    (layout : QuantumLayout systemCount) :
    count .classicalBits (ofQuantumLayout layout) = 0 := rfl

@[simp] public lemma count_quantumSystems_ofQuantumLayout {systemCount : Nat}
    (layout : QuantumLayout systemCount) (dimension : ℕ+) :
    count (.quantumSystems dimension) (ofQuantumLayout layout) =
      layout.dimensionCount dimension := rfl

/-- Combining disjoint physical layouts adds every native space coordinate. -/
@[simp] public lemma ofQuantumLayout_append {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    ofQuantumLayout (left.append right disjoint) =
      ofQuantumLayout left + ofQuantumLayout right := by
  apply ext
  intro axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact QuantumLayout.dimensionCount_append left right disjoint dimension

/-- A uniform layout occupies exactly its own dimension's coordinate. -/
public lemma count_quantumSystems_ofQuantumLayout_uniform
    (systemCount : Nat) (dimension query : ℕ+)
    (identity : Fin systemCount → Nat) (distinct : Function.Injective identity) :
    count (.quantumSystems query)
        (ofQuantumLayout (QuantumLayout.uniform systemCount dimension identity distinct)) =
      if dimension = query then systemCount else 0 :=
  QuantumLayout.dimensionCount_uniform systemCount dimension query identity distinct

end SpacePool

/-- Exact IEC units available for human-readable display. -/
public inductive IECUnit where
  | byte
  | KiB
  | MiB
  | GiB
  | TiB
  | PiB
deriving DecidableEq

namespace IECUnit

/-- Number of bits in one display unit, using IEC powers of 1024. -/
def bitsPerUnit : IECUnit → Nat
  | .byte => 8
  | .KiB => 8 * 1024
  | .MiB => 8 * 1024 ^ 2
  | .GiB => 8 * 1024 ^ 3
  | .TiB => 8 * 1024 ^ 4
  | .PiB => 8 * 1024 ^ 5

/-- Exact bit magnitude of an integral IEC display quantity. -/
def toBits (unit : IECUnit) (amount : Nat) : Nat :=
  amount * unit.bitsPerUnit

/-- Lossless display decomposition into whole IEC units and remaining bits. -/
def decomposeBits (unit : IECUnit) (bits : Nat) : Nat × Nat :=
  (bits / unit.bitsPerUnit, bits % unit.bitsPerUnit)

lemma bitsPerUnit_pos (unit : IECUnit) : 0 < unit.bitsPerUnit := by
  cases unit <;> decide

/-- Decomposing a bit count for display loses no proof-level capacity. -/
lemma decomposeBits_reconstruct (unit : IECUnit) (bits : Nat) :
    (unit.decomposeBits bits).1 * unit.bitsPerUnit +
        (unit.decomposeBits bits).2 = bits := by
  simp only [decomposeBits]
  simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div bits unit.bitsPerUnit

lemma decomposeBits_remainder_lt (unit : IECUnit) (bits : Nat) :
    (unit.decomposeBits bits).2 < unit.bitsPerUnit := by
  exact Nat.mod_lt bits unit.bitsPerUnit_pos

@[simp] lemma bitsPerUnit_byte : IECUnit.byte.bitsPerUnit = 8 := rfl
@[simp] lemma bitsPerUnit_KiB : IECUnit.KiB.bitsPerUnit = 8 * 1024 := rfl
@[simp] lemma bitsPerUnit_MiB : IECUnit.MiB.bitsPerUnit = 8 * 1024 ^ 2 := rfl
@[simp] lemma bitsPerUnit_GiB : IECUnit.GiB.bitsPerUnit = 8 * 1024 ^ 3 := rfl
@[simp] lemma bitsPerUnit_TiB : IECUnit.TiB.bitsPerUnit = 8 * 1024 ^ 4 := rfl
@[simp] lemma bitsPerUnit_PiB : IECUnit.PiB.bitsPerUnit = 8 * 1024 ^ 5 := rfl

/-- One KiB is exactly 1024 bytes. -/
lemma oneKiB_eq_1024_bytes : IECUnit.KiB.toBits 1 = IECUnit.byte.toBits 1024 := by
  decide

lemma oneMiB_eq_1024_KiB : IECUnit.MiB.toBits 1 = IECUnit.KiB.toBits 1024 := by
  decide

lemma oneGiB_eq_1024_MiB : IECUnit.GiB.toBits 1 = IECUnit.MiB.toBits 1024 := by
  decide

lemma oneTiB_eq_1024_GiB : IECUnit.TiB.toBits 1 = IECUnit.GiB.toBits 1024 := by
  decide

lemma onePiB_eq_1024_TiB : IECUnit.PiB.toBits 1 = IECUnit.TiB.toBits 1024 := by
  decide

end IECUnit

namespace AccountingSpaceFixtures

/-- Classical shapes occupy only the bit coordinate. -/
example : SpacePool.count .classicalBits
    (SpacePool.ofShape (.option (.unsignedWord 8)) : SpacePool .classical) = 9 := rfl

/-- Quantum pools keep classical bits, qubits, and qutrits distinct. -/
example (pool : SpacePool .quantum) : Nat × Nat × Nat :=
  (pool .classicalBits, pool (.quantumSystems 2), pool (.quantumSystems 3))

/-- A real uniform qutrit layout contributes no qubits. -/
example (systemCount : Nat) (identity : Fin systemCount → Nat)
    (distinct : Function.Injective identity) :
    SpacePool.count (.quantumSystems 2)
        (SpacePool.ofQuantumLayout
          (QuantumLayout.uniform systemCount 3 identity distinct)) = 0 := by
  rw [SpacePool.count_quantumSystems_ofQuantumLayout_uniform]
  exact if_neg (by decide : (3 : ℕ+) ≠ 2)

/-- Its dimension-three coordinate counts every actual qutrit. -/
example (systemCount : Nat) (identity : Fin systemCount → Nat)
    (distinct : Function.Injective identity) :
    SpacePool.count (.quantumSystems 3)
        (SpacePool.ofQuantumLayout (QuantumLayout.uniform systemCount 3 identity distinct)) =
      systemCount := by
  rw [SpacePool.count_quantumSystems_ofQuantumLayout_uniform, if_pos rfl]

/-- Nine bits display as one byte plus one remaining bit. -/
example : IECUnit.byte.decomposeBits 9 = (1, 1) := by decide

/-- error: Application type mismatch -/
#guard_msgs(error, substring := true) in
example (pool : SpacePool .classical) : Nat := pool (.quantumSystems 3)

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check SpacePool.ofFootprint

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check SpaceAxis.byte

end AccountingSpaceFixtures

end QuantumAlg

end
