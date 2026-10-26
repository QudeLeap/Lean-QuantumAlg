/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word17Chunk0 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word17State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word17Step0 :
    word17Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word17State1 := by decide +kernel

private def word17Chunk1 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word17State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word17Step1 :
    word17Chunk1.foldl (fun acc a => a.applyPacked acc)
      word17State1 = word17State2 := by decide +kernel

private def word17Chunk2 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word17State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word17Step2 :
    word17Chunk2.foldl (fun acc a => a.applyPacked acc)
      word17State2 = word17State3 := by decide +kernel

private def word17Chunk3 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word17State4 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩⟩
private lemma word17Step3 :
    word17Chunk3.foldl (fun acc a => a.applyPacked acc)
      word17State3 = word17State4 := by decide +kernel

private def word17Chunk4 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word17State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 5)⟩,
       ⟨((-11 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word17Step4 :
    word17Chunk4.foldl (fun acc a => a.applyPacked acc)
      word17State4 = word17State5 := by decide +kernel

private def word17Chunk5 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word17State6 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-7 : Dyadic) * half ^ 6)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((29 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((17 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-17 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((29 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-7 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word17Step5 :
    word17Chunk5.foldl (fun acc a => a.applyPacked acc)
      word17State5 = word17State6 := by decide +kernel

private def word17Chunk6 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word17State7 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((49 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((-27 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word17Step6 :
    word17Chunk6.foldl (fun acc a => a.applyPacked acc)
      word17State6 = word17State7 := by decide +kernel

private def word17Chunk7 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word17State8 : PackedMat2 :=
    ⟨⟨⟨((15 : Dyadic) * half ^ 5),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-27 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((29 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 6),
        ((29 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((27 : Dyadic) * half ^ 7)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((21 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word17Step7 :
    word17Chunk7.foldl (fun acc a => a.applyPacked acc)
      word17State7 = word17State8 := by decide +kernel

private def word17Chunk8 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word17State9 : PackedMat2 :=
    ⟨⟨⟨((79 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 7)⟩,
       ⟨((-23 : Dyadic) * half ^ 6),
        ((25 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-55 : Dyadic) * half ^ 7),
        ((-7 : Dyadic) * half ^ 8)⟩,
       ⟨((59 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 7),
        ((-57 : Dyadic) * half ^ 7)⟩,
       ⟨((1 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 6),
        ((-125 : Dyadic) * half ^ 8)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((33 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word17Step8 :
    word17Chunk8.foldl (fun acc a => a.applyPacked acc)
      word17State8 = word17State9 := by decide +kernel

private def word17Chunk9 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word17State10 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 8),
        ((101 : Dyadic) * half ^ 9)⟩,
       ⟨((35 : Dyadic) * half ^ 7),
        ((-73 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-145 : Dyadic) * half ^ 8),
        ((-135 : Dyadic) * half ^ 9)⟩,
       ⟨((-49 : Dyadic) * half ^ 7),
        ((161 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-49 : Dyadic) * half ^ 7),
        ((161 : Dyadic) * half ^ 9)⟩,
       ⟨((-145 : Dyadic) * half ^ 8),
        ((-135 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 7),
        ((73 : Dyadic) * half ^ 9)⟩,
       ⟨((-13 : Dyadic) * half ^ 8),
        ((-101 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word17Step9 :
    word17Chunk9.foldl (fun acc a => a.applyPacked acc)
      word17State9 = word17State10 := by decide +kernel

private def word17Chunk10 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word17State11 : PackedMat2 :=
    ⟨⟨⟨((-117 : Dyadic) * half ^ 9),
        ((13 : Dyadic) * half ^ 8)⟩,
       ⟨((-73 : Dyadic) * half ^ 9),
        ((121 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 7),
        ((-197 : Dyadic) * half ^ 9)⟩,
       ⟨((15 : Dyadic) * half ^ 8),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((321 : Dyadic) * half ^ 9),
        ((47 : Dyadic) * half ^ 9)⟩,
       ⟨((73 : Dyadic) * half ^ 9),
        ((77 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((67 : Dyadic) * half ^ 7),
        ((-95 : Dyadic) * half ^ 9)⟩,
       ⟨((-27 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word17Step10 :
    word17Chunk10.foldl (fun acc a => a.applyPacked acc)
      word17State10 = word17State11 := by decide +kernel

private def word17Chunk11 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word17State12 : PackedMat2 :=
    ⟨⟨⟨((95 : Dyadic) * half ^ 10),
        ((-235 : Dyadic) * half ^ 10)⟩,
       ⟨((491 : Dyadic) * half ^ 10),
        ((75 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-497 : Dyadic) * half ^ 10),
        ((121 : Dyadic) * half ^ 9)⟩,
       ⟨((-489 : Dyadic) * half ^ 10),
        ((-141 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-497 : Dyadic) * half ^ 10),
        ((121 : Dyadic) * half ^ 9)⟩,
       ⟨((489 : Dyadic) * half ^ 10),
        ((141 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-95 : Dyadic) * half ^ 10),
        ((235 : Dyadic) * half ^ 10)⟩,
       ⟨((491 : Dyadic) * half ^ 10),
        ((75 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word17Step11 :
    word17Chunk11.foldl (fun acc a => a.applyPacked acc)
      word17State11 = word17State12 := by decide +kernel

private def word17Chunk12 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word17State13 : PackedMat2 :=
    ⟨⟨⟨((-493 : Dyadic) * half ^ 11),
        ((-171 : Dyadic) * half ^ 9)⟩,
       ⟨((15 : Dyadic) * half ^ 11),
        ((969 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 11),
        ((143 : Dyadic) * half ^ 10)⟩,
       ⟨((695 : Dyadic) * half ^ 11),
        ((-495 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 11),
        ((-143 : Dyadic) * half ^ 10)⟩,
       ⟨((695 : Dyadic) * half ^ 11),
        ((-495 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-493 : Dyadic) * half ^ 11),
        ((-171 : Dyadic) * half ^ 9)⟩,
       ⟨((-15 : Dyadic) * half ^ 11),
        ((-969 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word17Step12 :
    word17Chunk12.foldl (fun acc a => a.applyPacked acc)
      word17State12 = word17State13 := by decide +kernel

private def word17Chunk13 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word17State14 : PackedMat2 :=
    ⟨⟨⟨((-125 : Dyadic) * half ^ 11),
        ((-803 : Dyadic) * half ^ 11)⟩,
       ⟨((15 : Dyadic) * half ^ 7),
        ((517 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-219 : Dyadic) * half ^ 11),
        ((1799 : Dyadic) * half ^ 12)⟩,
       ⟨((-49 : Dyadic) * half ^ 11),
        ((1121 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((49 : Dyadic) * half ^ 11),
        ((-1121 : Dyadic) * half ^ 12)⟩,
       ⟨((219 : Dyadic) * half ^ 11),
        ((-1799 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 7),
        ((517 : Dyadic) * half ^ 11)⟩,
       ⟨((-125 : Dyadic) * half ^ 11),
        ((-803 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word17Step13 :
    word17Chunk13.foldl (fun acc a => a.applyPacked acc)
      word17State13 = word17State14 := by decide +kernel

private def word17Chunk14 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word17State15 : PackedMat2 :=
    ⟨⟨⟨((209 : Dyadic) * half ^ 12),
        ((-4845 : Dyadic) * half ^ 13)⟩,
       ⟨((-981 : Dyadic) * half ^ 12),
        ((333 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 10),
        ((1013 : Dyadic) * half ^ 12)⟩,
       ⟨((1051 : Dyadic) * half ^ 12),
        ((641 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-93 : Dyadic) * half ^ 10),
        ((1055 : Dyadic) * half ^ 13)⟩,
       ⟨((827 : Dyadic) * half ^ 11),
        ((1047 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2589 : Dyadic) * half ^ 12),
        ((595 : Dyadic) * half ^ 12)⟩,
       ⟨((141 : Dyadic) * half ^ 8),
        ((193 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word17Step14 :
    word17Chunk14.foldl (fun acc a => a.applyPacked acc)
      word17State14 = word17State15 := by decide +kernel

private def word17Chunk15 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word17State16 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 9),
        ((-3201 : Dyadic) * half ^ 13)⟩,
       ⟨((-1969 : Dyadic) * half ^ 12),
        ((69 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-4895 : Dyadic) * half ^ 13),
        ((135 : Dyadic) * half ^ 12)⟩,
       ⟨((-957 : Dyadic) * half ^ 13),
        ((-857 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((4895 : Dyadic) * half ^ 13),
        ((-135 : Dyadic) * half ^ 12)⟩,
       ⟨((-957 : Dyadic) * half ^ 13),
        ((-857 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 9),
        ((-3201 : Dyadic) * half ^ 13)⟩,
       ⟨((1969 : Dyadic) * half ^ 12),
        ((-69 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word17Step15 :
    word17Chunk15.foldl (fun acc a => a.applyPacked acc)
      word17State15 = word17State16 := by decide +kernel

private def word17Chunk16 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word17State17 : PackedMat2 :=
    ⟨⟨⟨((627 : Dyadic) * half ^ 11),
        ((-871 : Dyadic) * half ^ 12)⟩,
       ⟨((-1553 : Dyadic) * half ^ 11),
        ((419 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-3025 : Dyadic) * half ^ 14),
        ((-1967 : Dyadic) * half ^ 14)⟩,
       ⟨((-4725 : Dyadic) * half ^ 14),
        ((-3541 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1377 : Dyadic) * half ^ 12),
        ((-3875 : Dyadic) * half ^ 14)⟩,
       ⟨((787 : Dyadic) * half ^ 13),
        ((425 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((3065 : Dyadic) * half ^ 14),
        ((463 : Dyadic) * half ^ 11)⟩,
       ⟨((3903 : Dyadic) * half ^ 14),
        ((-545 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word17Step16 :
    word17Chunk16.foldl (fun acc a => a.applyPacked acc)
      word17State16 = word17State17 := by decide +kernel

private def word17Chunk17 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word17State18 : PackedMat2 :=
    ⟨⟨⟨((2383 : Dyadic) * half ^ 13),
        ((1337 : Dyadic) * half ^ 15)⟩,
       ⟨((-415 : Dyadic) * half ^ 9),
        ((1723 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((899 : Dyadic) * half ^ 13),
        ((893 : Dyadic) * half ^ 12)⟩,
       ⟨((6169 : Dyadic) * half ^ 14),
        ((297 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((6169 : Dyadic) * half ^ 14),
        ((297 : Dyadic) * half ^ 14)⟩,
       ⟨((899 : Dyadic) * half ^ 13),
        ((893 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((415 : Dyadic) * half ^ 9),
        ((-1723 : Dyadic) * half ^ 15)⟩,
       ⟨((-2383 : Dyadic) * half ^ 13),
        ((-1337 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word17Step17 :
    word17Chunk17.foldl (fun acc a => a.applyPacked acc)
      word17State17 = word17State18 := by decide +kernel

private def word17Chunk18 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word17State19 : PackedMat2 :=
    ⟨⟨⟨((6095 : Dyadic) * half ^ 14),
        ((22953 : Dyadic) * half ^ 16)⟩,
       ⟨((22851 : Dyadic) * half ^ 15),
        ((-13271 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-3111 : Dyadic) * half ^ 14),
        ((-3595 : Dyadic) * half ^ 16)⟩,
       ⟨((-309 : Dyadic) * half ^ 15),
        ((-3529 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((1781 : Dyadic) * half ^ 14),
        ((6531 : Dyadic) * half ^ 16)⟩,
       ⟨((33 : Dyadic) * half ^ 15),
        ((5913 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((4841 : Dyadic) * half ^ 15),
        ((35041 : Dyadic) * half ^ 16)⟩,
       ⟨((283 : Dyadic) * half ^ 9),
        ((-10661 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word17Step18 :
    word17Chunk18.foldl (fun acc a => a.applyPacked acc)
      word17State18 = word17State19 := by decide +kernel

private def word17Chunk19 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word17State20 : PackedMat2 :=
    ⟨⟨⟨((-10707 : Dyadic) * half ^ 16),
        ((-4187 : Dyadic) * half ^ 15)⟩,
       ⟨((-6129 : Dyadic) * half ^ 16),
        ((8467 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((73 : Dyadic) * half ^ 8),
        ((6041 : Dyadic) * half ^ 15)⟩,
       ⟨((-16163 : Dyadic) * half ^ 15),
        ((3337 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((15419 : Dyadic) * half ^ 16),
        ((-6819 : Dyadic) * half ^ 16)⟩,
       ⟨((8745 : Dyadic) * half ^ 16),
        ((25507 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-12747 : Dyadic) * half ^ 15),
        ((4209 : Dyadic) * half ^ 15)⟩,
       ⟨((21121 : Dyadic) * half ^ 15),
        ((2289 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word17Step19 :
    word17Chunk19.foldl (fun acc a => a.applyPacked acc)
      word17State19 = word17State20 := by decide +kernel

private def word17Chunk20 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word17State21 : PackedMat2 :=
    ⟨⟨⟨((-42945 : Dyadic) * half ^ 17),
        ((-20619 : Dyadic) * half ^ 16)⟩,
       ⟨((75717 : Dyadic) * half ^ 17),
        ((-2421 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((62619 : Dyadic) * half ^ 17),
        ((-18517 : Dyadic) * half ^ 17)⟩,
       ⟨((36069 : Dyadic) * half ^ 17),
        ((-5935 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((6647 : Dyadic) * half ^ 17),
        ((-13275 : Dyadic) * half ^ 17)⟩,
       ⟨((-30387 : Dyadic) * half ^ 17),
        ((771 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-38817 : Dyadic) * half ^ 17),
        ((-59331 : Dyadic) * half ^ 17)⟩,
       ⟨((43659 : Dyadic) * half ^ 17),
        ((-8193 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word17Step20 :
    word17Chunk20.foldl (fun acc a => a.applyPacked acc)
      word17State20 = word17State21 := by decide +kernel

private def word17Chunk21 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word17State22 : PackedMat2 :=
    ⟨⟨⟨((-161069 : Dyadic) * half ^ 18),
        ((-65277 : Dyadic) * half ^ 18)⟩,
       ⟨((19073 : Dyadic) * half ^ 18),
        ((-5545 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((106571 : Dyadic) * half ^ 18),
        ((-99563 : Dyadic) * half ^ 18)⟩,
       ⟨((48803 : Dyadic) * half ^ 18),
        ((3155 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((106571 : Dyadic) * half ^ 18),
        ((-99563 : Dyadic) * half ^ 18)⟩,
       ⟨((-48803 : Dyadic) * half ^ 18),
        ((-3155 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((161069 : Dyadic) * half ^ 18),
        ((65277 : Dyadic) * half ^ 18)⟩,
       ⟨((19073 : Dyadic) * half ^ 18),
        ((-5545 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word17Step21 :
    word17Chunk21.foldl (fun acc a => a.applyPacked acc)
      word17State21 = word17State22 := by decide +kernel

private def word17Chunk22 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word17State23 : PackedMat2 :=
    ⟨⟨⟨((-3795 : Dyadic) * half ^ 13),
        ((-18073 : Dyadic) * half ^ 17)⟩,
       ⟨((-144561 : Dyadic) * half ^ 18),
        ((-2165 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-85781 : Dyadic) * half ^ 18),
        ((171259 : Dyadic) * half ^ 19)⟩,
       ⟨((86689 : Dyadic) * half ^ 18),
        ((39311 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-32987 : Dyadic) * half ^ 17),
        ((86235 : Dyadic) * half ^ 18)⟩,
       ⟨((105285 : Dyadic) * half ^ 18),
        ((227 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-13743 : Dyadic) * half ^ 17),
        ((23121 : Dyadic) * half ^ 19)⟩,
       ⟨((22403 : Dyadic) * half ^ 17),
        ((266001 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word17Step22 :
    word17Chunk22.foldl (fun acc a => a.applyPacked acc)
      word17State22 = word17State23 := by decide +kernel

private def word17Chunk23 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word17State24 : PackedMat2 :=
    ⟨⟨⟨((-1689 : Dyadic) * half ^ 16),
        ((-54301 : Dyadic) * half ^ 20)⟩,
       ⟨((-225449 : Dyadic) * half ^ 19),
        ((-400725 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((103005 : Dyadic) * half ^ 18),
        ((-138581 : Dyadic) * half ^ 20)⟩,
       ⟨((-191031 : Dyadic) * half ^ 19),
        ((327317 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((191031 : Dyadic) * half ^ 19),
        ((-327317 : Dyadic) * half ^ 20)⟩,
       ⟨((-103005 : Dyadic) * half ^ 18),
        ((138581 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-225449 : Dyadic) * half ^ 19),
        ((-400725 : Dyadic) * half ^ 20)⟩,
       ⟨((-1689 : Dyadic) * half ^ 16),
        ((-54301 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word17Step23 :
    word17Chunk23.foldl (fun acc a => a.applyPacked acc)
      word17State23 = word17State24 := by decide +kernel

private def word17Chunk24 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word17State25 : PackedMat2 :=
    ⟨⟨⟨((150801 : Dyadic) * half ^ 18),
        ((169823 : Dyadic) * half ^ 20)⟩,
       ⟨((-110793 : Dyadic) * half ^ 19),
        ((61511 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-473377 : Dyadic) * half ^ 20),
        ((-48105 : Dyadic) * half ^ 19)⟩,
       ⟨((477897 : Dyadic) * half ^ 20),
        ((-126305 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-87205 : Dyadic) * half ^ 18),
        ((565 : Dyadic) * half ^ 18)⟩,
       ⟨((9775 : Dyadic) * half ^ 16),
        ((-475637 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-292845 : Dyadic) * half ^ 20),
        ((-190809 : Dyadic) * half ^ 20)⟩,
       ⟨((-46801 : Dyadic) * half ^ 20),
        ((-412395 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word17Step24 :
    word17Chunk24.foldl (fun acc a => a.applyPacked acc)
      word17State24 = word17State25 := by decide +kernel

private def word17Chunk25 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word17State26 : PackedMat2 :=
    ⟨⟨⟨((1466455 : Dyadic) * half ^ 21),
        ((117675 : Dyadic) * half ^ 20)⟩,
       ⟨((178417 : Dyadic) * half ^ 21),
        ((356087 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1007249 : Dyadic) * half ^ 21),
        ((349469 : Dyadic) * half ^ 21)⟩,
       ⟨((-105079 : Dyadic) * half ^ 21),
        ((134803 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((189743 : Dyadic) * half ^ 21),
        ((451085 : Dyadic) * half ^ 21)⟩,
       ⟨((888681 : Dyadic) * half ^ 21),
        ((-139041 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-120737 : Dyadic) * half ^ 21),
        ((644019 : Dyadic) * half ^ 21)⟩,
       ⟨((-591437 : Dyadic) * half ^ 21),
        ((-205609 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word17Step25 :
    word17Chunk25.foldl (fun acc a => a.applyPacked acc)
      word17State25 = word17State26 := by decide +kernel

private def word17Chunk26 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word17State27 : PackedMat2 :=
    ⟨⟨⟨((2463895 : Dyadic) * half ^ 22),
        ((-100627 : Dyadic) * half ^ 22)⟩,
       ⟨((-720443 : Dyadic) * half ^ 22),
        ((318381 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((659011 : Dyadic) * half ^ 22),
        ((582653 : Dyadic) * half ^ 22)⟩,
       ⟨((-435649 : Dyadic) * half ^ 22),
        ((-896893 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((659011 : Dyadic) * half ^ 22),
        ((582653 : Dyadic) * half ^ 22)⟩,
       ⟨((435649 : Dyadic) * half ^ 22),
        ((896893 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-2463895 : Dyadic) * half ^ 22),
        ((100627 : Dyadic) * half ^ 22)⟩,
       ⟨((-720443 : Dyadic) * half ^ 22),
        ((318381 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word17Step26 :
    word17Chunk26.foldl (fun acc a => a.applyPacked acc)
      word17State26 = word17State27 := by decide +kernel

private def word17Chunk27 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word17State28 : PackedMat2 :=
    ⟨⟨⟨((-1081615 : Dyadic) * half ^ 23),
        ((1131389 : Dyadic) * half ^ 22)⟩,
       ⟨((1821217 : Dyadic) * half ^ 23),
        ((4196793 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3510807 : Dyadic) * half ^ 23),
        ((-207351 : Dyadic) * half ^ 20)⟩,
       ⟨((-1494455 : Dyadic) * half ^ 23),
        ((-420179 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-3510807 : Dyadic) * half ^ 23),
        ((207351 : Dyadic) * half ^ 20)⟩,
       ⟨((-1494455 : Dyadic) * half ^ 23),
        ((-420179 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1081615 : Dyadic) * half ^ 23),
        ((1131389 : Dyadic) * half ^ 22)⟩,
       ⟨((-1821217 : Dyadic) * half ^ 23),
        ((-4196793 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word17Step27 :
    word17Chunk27.foldl (fun acc a => a.applyPacked acc)
      word17State27 = word17State28 := by decide +kernel

private def word17Chunk28 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word17State29 : PackedMat2 :=
    ⟨⟨⟨((-773053 : Dyadic) * half ^ 21),
        ((-6252179 : Dyadic) * half ^ 24)⟩,
       ⟨((515571 : Dyadic) * half ^ 22),
        ((-1984393 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1084149 : Dyadic) * half ^ 22),
        ((1711099 : Dyadic) * half ^ 22)⟩,
       ⟨((552529 : Dyadic) * half ^ 23),
        ((-2213623 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((5635821 : Dyadic) * half ^ 23),
        ((-2720827 : Dyadic) * half ^ 24)⟩,
       ⟨((-1208575 : Dyadic) * half ^ 23),
        ((1615769 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2133893 : Dyadic) * half ^ 23),
        ((2061677 : Dyadic) * half ^ 23)⟩,
       ⟨((-2059143 : Dyadic) * half ^ 22),
        ((-1030535 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word17Step28 :
    word17Chunk28.foldl (fun acc a => a.applyPacked acc)
      word17State28 = word17State29 := by decide +kernel

private def word17Chunk29 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word17State30 : PackedMat2 :=
    ⟨⟨⟨((-5115023 : Dyadic) * half ^ 24),
        ((-11044427 : Dyadic) * half ^ 25)⟩,
       ⟨((-1131019 : Dyadic) * half ^ 22),
        ((-8617141 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3199655 : Dyadic) * half ^ 24),
        ((-6161529 : Dyadic) * half ^ 25)⟩,
       ⟨((-3813343 : Dyadic) * half ^ 23),
        ((9933847 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-3813343 : Dyadic) * half ^ 23),
        ((9933847 : Dyadic) * half ^ 25)⟩,
       ⟨((3199655 : Dyadic) * half ^ 24),
        ((-6161529 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1131019 : Dyadic) * half ^ 22),
        ((8617141 : Dyadic) * half ^ 25)⟩,
       ⟨((5115023 : Dyadic) * half ^ 24),
        ((11044427 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word17Step29 :
    word17Chunk29.foldl (fun acc a => a.applyPacked acc)
      word17State29 = word17State30 := by decide +kernel

private def word17Chunk30 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word17State31 : PackedMat2 :=
    ⟨⟨⟨((1527337 : Dyadic) * half ^ 25),
        ((-6219623 : Dyadic) * half ^ 25)⟩,
       ⟨((-11846005 : Dyadic) * half ^ 25),
        ((-12259805 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((125757 : Dyadic) * half ^ 24),
        ((-1031371 : Dyadic) * half ^ 24)⟩,
       ⟨((11482143 : Dyadic) * half ^ 24),
        ((-5887901 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-125757 : Dyadic) * half ^ 24),
        ((1031371 : Dyadic) * half ^ 24)⟩,
       ⟨((11482143 : Dyadic) * half ^ 24),
        ((-5887901 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1527337 : Dyadic) * half ^ 25),
        ((-6219623 : Dyadic) * half ^ 25)⟩,
       ⟨((11846005 : Dyadic) * half ^ 25),
        ((12259805 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word17Step30 :
    word17Chunk30.foldl (fun acc a => a.applyPacked acc)
      word17State30 = word17State31 := by decide +kernel

private def word17Chunk31 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word17State32 : PackedMat2 :=
    ⟨⟨⟨((-341727 : Dyadic) * half ^ 26),
        ((732775 : Dyadic) * half ^ 22)⟩,
       ⟨((-45956559 : Dyadic) * half ^ 26),
        ((-12177727 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-28617107 : Dyadic) * half ^ 26),
        ((6179519 : Dyadic) * half ^ 25)⟩,
       ⟨((-23370293 : Dyadic) * half ^ 26),
        ((8641739 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((3717299 : Dyadic) * half ^ 26),
        ((-2623407 : Dyadic) * half ^ 26)⟩,
       ⟨((-21000777 : Dyadic) * half ^ 26),
        ((6498425 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-23902127 : Dyadic) * half ^ 26),
        ((-2850927 : Dyadic) * half ^ 23)⟩,
       ⟨((-453327 : Dyadic) * half ^ 26),
        ((-23149143 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word17Step31 :
    word17Chunk31.foldl (fun acc a => a.applyPacked acc)
      word17State31 = word17State32 := by decide +kernel

private def word17Chunk32 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word17State33 : PackedMat2 :=
    ⟨⟨⟨((1665565 : Dyadic) * half ^ 27),
        ((14775707 : Dyadic) * half ^ 25)⟩,
       ⟨((2098319 : Dyadic) * half ^ 27),
        ((-31462905 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-65903283 : Dyadic) * half ^ 27),
        ((-15367215 : Dyadic) * half ^ 27)⟩,
       ⟨((24558479 : Dyadic) * half ^ 27),
        ((-21279215 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((65903283 : Dyadic) * half ^ 27),
        ((15367215 : Dyadic) * half ^ 27)⟩,
       ⟨((24558479 : Dyadic) * half ^ 27),
        ((-21279215 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((1665565 : Dyadic) * half ^ 27),
        ((14775707 : Dyadic) * half ^ 25)⟩,
       ⟨((-2098319 : Dyadic) * half ^ 27),
        ((31462905 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word17Step32 :
    word17Chunk32.foldl (fun acc a => a.applyPacked acc)
      word17State32 = word17State33 := by decide +kernel

private def word17Chunk33 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word17State34 : PackedMat2 :=
    ⟨⟨⟨((1324345 : Dyadic) * half ^ 27),
        ((135006105 : Dyadic) * half ^ 28)⟩,
       ⟨((-10449283 : Dyadic) * half ^ 27),
        ((43223515 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-2285767 : Dyadic) * half ^ 22),
        ((-6236023 : Dyadic) * half ^ 26)⟩,
       ⟨((-33435227 : Dyadic) * half ^ 27),
        ((362563 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((33435227 : Dyadic) * half ^ 27),
        ((-362563 : Dyadic) * half ^ 21)⟩,
       ⟨((2285767 : Dyadic) * half ^ 22),
        ((6236023 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-10449283 : Dyadic) * half ^ 27),
        ((43223515 : Dyadic) * half ^ 28)⟩,
       ⟨((1324345 : Dyadic) * half ^ 27),
        ((135006105 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word17Step33 :
    word17Chunk33.foldl (fun acc a => a.applyPacked acc)
      word17State33 = word17State34 := by decide +kernel

private def word17Chunk34 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word17State35 : PackedMat2 :=
    ⟨⟨⟨((-3133213 : Dyadic) * half ^ 25),
        ((-55664593 : Dyadic) * half ^ 29)⟩,
       ⟨((41211659 : Dyadic) * half ^ 26),
        ((3080383 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-160333067 : Dyadic) * half ^ 28),
        ((2510943 : Dyadic) * half ^ 25)⟩,
       ⟨((12878123 : Dyadic) * half ^ 27),
        ((88101583 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((68014039 : Dyadic) * half ^ 28),
        ((186089313 : Dyadic) * half ^ 29)⟩,
       ⟨((108189127 : Dyadic) * half ^ 28),
        ((-134576821 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-3671561 : Dyadic) * half ^ 25),
        ((-47478085 : Dyadic) * half ^ 27)⟩,
       ⟨((26292105 : Dyadic) * half ^ 28),
        ((-34945233 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word17Step34 :
    word17Chunk34.foldl (fun acc a => a.applyPacked acc)
      word17State34 = word17State35 := by decide +kernel

private def word17Chunk35 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word17State36 : PackedMat2 :=
    ⟨⟨⟨((-81098393 : Dyadic) * half ^ 27),
        ((215612777 : Dyadic) * half ^ 30)⟩,
       ⟨((237167459 : Dyadic) * half ^ 29),
        ((323417443 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-104192291 : Dyadic) * half ^ 29),
        ((-130823967 : Dyadic) * half ^ 30)⟩,
       ⟨((-47967635 : Dyadic) * half ^ 28),
        ((212555227 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-20432815 : Dyadic) * half ^ 28),
        ((200127561 : Dyadic) * half ^ 30)⟩,
       ⟨((171689597 : Dyadic) * half ^ 29),
        ((8257021 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((134757555 : Dyadic) * half ^ 28),
        ((-87226113 : Dyadic) * half ^ 30)⟩,
       ⟨((-53902333 : Dyadic) * half ^ 29),
        ((-561561031 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word17Step35 :
    word17Chunk35.foldl (fun acc a => a.applyPacked acc)
      word17State35 = word17State36 := by decide +kernel

private def word17Chunk36 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word17State37 : PackedMat2 :=
    ⟨⟨⟨((7011157 : Dyadic) * half ^ 27),
        ((-116880915 : Dyadic) * half ^ 31)⟩,
       ⟨((603185319 : Dyadic) * half ^ 30),
        ((-63912945 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((95019397 : Dyadic) * half ^ 30),
        ((405339881 : Dyadic) * half ^ 31)⟩,
       ⟨((-414083141 : Dyadic) * half ^ 29),
        ((-7959709 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-414083141 : Dyadic) * half ^ 29),
        ((-7959709 : Dyadic) * half ^ 31)⟩,
       ⟨((95019397 : Dyadic) * half ^ 30),
        ((405339881 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-603185319 : Dyadic) * half ^ 30),
        ((63912945 : Dyadic) * half ^ 31)⟩,
       ⟨((-7011157 : Dyadic) * half ^ 27),
        ((116880915 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word17Step36 :
    word17Chunk36.foldl (fun acc a => a.applyPacked acc)
      word17State36 = word17State37 := by decide +kernel

private def word17Chunk37 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word17State38 : PackedMat2 :=
    ⟨⟨⟨((-130344037 : Dyadic) * half ^ 29),
        ((-139263857 : Dyadic) * half ^ 30)⟩,
       ⟨((99413053 : Dyadic) * half ^ 30),
        ((1006337701 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1323903093 : Dyadic) * half ^ 31),
        ((-57659509 : Dyadic) * half ^ 29)⟩,
       ⟨((113543673 : Dyadic) * half ^ 31),
        ((-175974155 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((291293173 : Dyadic) * half ^ 30),
        ((-718723383 : Dyadic) * half ^ 31)⟩,
       ⟨((-60655137 : Dyadic) * half ^ 30),
        ((-302589855 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((727809987 : Dyadic) * half ^ 31),
        ((-161275021 : Dyadic) * half ^ 31)⟩,
       ⟨((-1284865415 : Dyadic) * half ^ 31),
        ((-360101127 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word17Step37 :
    word17Chunk37.foldl (fun acc a => a.applyPacked acc)
      word17State37 = word17State38 := by decide +kernel

private def word17Chunk38 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word17State39 : PackedMat2 :=
    ⟨⟨⟨((-2079784627 : Dyadic) * half ^ 32),
        ((-1297075813 : Dyadic) * half ^ 32)⟩,
       ⟨((1604842927 : Dyadic) * half ^ 32),
        ((-215824959 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1096195893 : Dyadic) * half ^ 32),
        ((1397323689 : Dyadic) * half ^ 32)⟩,
       ⟨((421180367 : Dyadic) * half ^ 32),
        ((-8776813 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1096195893 : Dyadic) * half ^ 32),
        ((1397323689 : Dyadic) * half ^ 32)⟩,
       ⟨((-421180367 : Dyadic) * half ^ 32),
        ((8776813 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2079784627 : Dyadic) * half ^ 32),
        ((1297075813 : Dyadic) * half ^ 32)⟩,
       ⟨((1604842927 : Dyadic) * half ^ 32),
        ((-215824959 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word17Step38 :
    word17Chunk38.foldl (fun acc a => a.applyPacked acc)
      word17State38 = word17State39 := by decide +kernel

private def word17Chunk39 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word17State40 : PackedMat2 :=
    ⟨⟨⟨((-2236443089 : Dyadic) * half ^ 32),
        ((-655313473 : Dyadic) * half ^ 32)⟩,
       ⟨((-682980027 : Dyadic) * half ^ 30),
        ((266613811 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((20148165 : Dyadic) * half ^ 28),
        ((-210234679 : Dyadic) * half ^ 33)⟩,
       ⟨((-1052121479 : Dyadic) * half ^ 31),
        ((-23809721 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1052121479 : Dyadic) * half ^ 31),
        ((-23809721 : Dyadic) * half ^ 33)⟩,
       ⟨((20148165 : Dyadic) * half ^ 28),
        ((-210234679 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((682980027 : Dyadic) * half ^ 30),
        ((-266613811 : Dyadic) * half ^ 31)⟩,
       ⟨((2236443089 : Dyadic) * half ^ 32),
        ((655313473 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word17Step39 :
    word17Chunk39.foldl (fun acc a => a.applyPacked acc)
      word17State39 = word17State40 := by decide +kernel

private def word17Chunk40 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word17State41 : PackedMat2 :=
    ⟨⟨⟨((440692015 : Dyadic) * half ^ 30),
        ((-5515531701 : Dyadic) * half ^ 34)⟩,
       ⟨((-1492358485 : Dyadic) * half ^ 33),
        ((-6564232483 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-837911829 : Dyadic) * half ^ 33),
        ((1735006245 : Dyadic) * half ^ 34)⟩,
       ⟨((-968941085 : Dyadic) * half ^ 32),
        ((-5729347541 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((249646331 : Dyadic) * half ^ 30),
        ((2775793999 : Dyadic) * half ^ 34)⟩,
       ⟨((-3732176893 : Dyadic) * half ^ 33),
        ((-1099970341 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1509970523 : Dyadic) * half ^ 31),
        ((2033177635 : Dyadic) * half ^ 34)⟩,
       ⟨((524350391 : Dyadic) * half ^ 33),
        ((5017894605 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word17Step40 :
    word17Chunk40.foldl (fun acc a => a.applyPacked acc)
      word17State40 = word17State41 := by decide +kernel

private def word17Chunk41 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word17State42 : PackedMat2 :=
    ⟨⟨⟨((-253250321 : Dyadic) * half ^ 31),
        ((8195549361 : Dyadic) * half ^ 34)⟩,
       ⟨((-846359157 : Dyadic) * half ^ 31),
        ((-2400054753 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-2366993677 : Dyadic) * half ^ 34),
        ((3043350759 : Dyadic) * half ^ 34)⟩,
       ⟨((-6042908979 : Dyadic) * half ^ 34),
        ((1438568255 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-2366993677 : Dyadic) * half ^ 34),
        ((3043350759 : Dyadic) * half ^ 34)⟩,
       ⟨((6042908979 : Dyadic) * half ^ 34),
        ((-1438568255 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((253250321 : Dyadic) * half ^ 31),
        ((-8195549361 : Dyadic) * half ^ 34)⟩,
       ⟨((-846359157 : Dyadic) * half ^ 31),
        ((-2400054753 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word17Step41 :
    word17Chunk41.foldl (fun acc a => a.applyPacked acc)
      word17State41 = word17State42 := by decide +kernel

private def word17Chunk42 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word17State43 : PackedMat2 :=
    ⟨⟨⟨((23397317195 : Dyadic) * half ^ 35),
        ((203738285 : Dyadic) * half ^ 33)⟩,
       ⟨((3658391529 : Dyadic) * half ^ 35),
        ((12802172283 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-2980973707 : Dyadic) * half ^ 35),
        ((-5016396707 : Dyadic) * half ^ 35)⟩,
       ⟨((11553274171 : Dyadic) * half ^ 35),
        ((-437412921 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1982210029 : Dyadic) * half ^ 35),
        ((7267123939 : Dyadic) * half ^ 35)⟩,
       ⟨((-12015003443 : Dyadic) * half ^ 35),
        ((535768779 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-11987219143 : Dyadic) * half ^ 35),
        ((9869462833 : Dyadic) * half ^ 35)⟩,
       ⟨((-13617125423 : Dyadic) * half ^ 35),
        ((-6763927181 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word17Step42 :
    word17Chunk42.foldl (fun acc a => a.applyPacked acc)
      word17State42 = word17State43 := by decide +kernel

private def word17Chunk43 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word17State44 : PackedMat2 :=
    ⟨⟨⟨((-10993019861 : Dyadic) * half ^ 36),
        ((19634361851 : Dyadic) * half ^ 36)⟩,
       ⟨((3832369255 : Dyadic) * half ^ 36),
        ((5930533489 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((10334257547 : Dyadic) * half ^ 36),
        ((-13437034041 : Dyadic) * half ^ 35)⟩,
       ⟨((-24107083713 : Dyadic) * half ^ 36),
        ((-16702662945 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-10171405137 : Dyadic) * half ^ 36),
        ((8610335315 : Dyadic) * half ^ 35)⟩,
       ⟨((43576731027 : Dyadic) * half ^ 36),
        ((6886413083 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((4087772105 : Dyadic) * half ^ 36),
        ((3706347279 : Dyadic) * half ^ 35)⟩,
       ⟨((43356495807 : Dyadic) * half ^ 36),
        ((-3580325303 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word17Step43 :
    word17Chunk43.foldl (fun acc a => a.applyPacked acc)
      word17State43 = word17State44 := by decide +kernel

private def word17Chunk44 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word17State45 : PackedMat2 :=
    ⟨⟨⟨((12632474655 : Dyadic) * half ^ 36),
        ((-17494483187 : Dyadic) * half ^ 37)⟩,
       ⟨((40013989539 : Dyadic) * half ^ 36),
        ((30353144189 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-12776640173 : Dyadic) * half ^ 36),
        ((17224807525 : Dyadic) * half ^ 36)⟩,
       ⟨((2535678433 : Dyadic) * half ^ 34),
        ((-27280738549 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((2535678433 : Dyadic) * half ^ 34),
        ((-27280738549 : Dyadic) * half ^ 36)⟩,
       ⟨((-12776640173 : Dyadic) * half ^ 36),
        ((17224807525 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-40013989539 : Dyadic) * half ^ 36),
        ((-30353144189 : Dyadic) * half ^ 37)⟩,
       ⟨((-12632474655 : Dyadic) * half ^ 36),
        ((17494483187 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word17Step44 :
    word17Chunk44.foldl (fun acc a => a.applyPacked acc)
      word17State44 = word17State45 := by decide +kernel

private def word17Chunk45 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word17State46 : PackedMat2 :=
    ⟨⟨⟨((-41374855455 : Dyadic) * half ^ 37),
        ((-30439695607 : Dyadic) * half ^ 37)⟩,
       ⟨((8568988461 : Dyadic) * half ^ 36),
        ((60465829219 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((28969517211 : Dyadic) * half ^ 37),
        ((-89561318701 : Dyadic) * half ^ 38)⟩,
       ⟨((41066552489 : Dyadic) * half ^ 37),
        ((-48624773655 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-41066552489 : Dyadic) * half ^ 37),
        ((48624773655 : Dyadic) * half ^ 38)⟩,
       ⟨((-28969517211 : Dyadic) * half ^ 37),
        ((89561318701 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((8568988461 : Dyadic) * half ^ 36),
        ((60465829219 : Dyadic) * half ^ 37)⟩,
       ⟨((-41374855455 : Dyadic) * half ^ 37),
        ((-30439695607 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word17Step45 :
    word17Chunk45.foldl (fun acc a => a.applyPacked acc)
      word17State45 = word17State46 := by decide +kernel

private def word17Chunk46 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word17State47 : PackedMat2 :=
    ⟨⟨⟨((-36950815647 : Dyadic) * half ^ 38),
        ((-252306143003 : Dyadic) * half ^ 39)⟩,
       ⟨((54263160097 : Dyadic) * half ^ 37),
        ((-116164756071 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-9235365507 : Dyadic) * half ^ 34),
        ((-14367850361 : Dyadic) * half ^ 39)⟩,
       ⟨((21719599011 : Dyadic) * half ^ 38),
        ((53451177491 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((19541663565 : Dyadic) * half ^ 38),
        ((-126046249101 : Dyadic) * half ^ 39)⟩,
       ⟨((-16954756963 : Dyadic) * half ^ 37),
        ((-169485447123 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((184235449537 : Dyadic) * half ^ 38),
        ((-71575504547 : Dyadic) * half ^ 39)⟩,
       ⟨((34035346733 : Dyadic) * half ^ 37),
        ((145477135841 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word17Step46 :
    word17Chunk46.foldl (fun acc a => a.applyPacked acc)
      word17State46 = word17State47 := by decide +kernel

private def word17Chunk47 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word17State48 : PackedMat2 :=
    ⟨⟨⟨((45382679589 : Dyadic) * half ^ 39),
        ((-367534776787 : Dyadic) * half ^ 40)⟩,
       ⟨((-4885135375 : Dyadic) * half ^ 33),
        ((-38877085479 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-53954857131 : Dyadic) * half ^ 38),
        ((335173085809 : Dyadic) * half ^ 40)⟩,
       ⟨((129165803913 : Dyadic) * half ^ 39),
        ((315046822477 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-129165803913 : Dyadic) * half ^ 39),
        ((-315046822477 : Dyadic) * half ^ 40)⟩,
       ⟨((53954857131 : Dyadic) * half ^ 38),
        ((-335173085809 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-4885135375 : Dyadic) * half ^ 33),
        ((-38877085479 : Dyadic) * half ^ 40)⟩,
       ⟨((45382679589 : Dyadic) * half ^ 39),
        ((-367534776787 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word17Step47 :
    word17Chunk47.foldl (fun acc a => a.applyPacked acc)
      word17State47 = word17State48 := by decide +kernel

private def word17Chunk48 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word17State49 : PackedMat2 :=
    ⟨⟨⟨((-64949244453 : Dyadic) * half ^ 40),
        ((22919872677 : Dyadic) * half ^ 37)⟩,
       ⟨((331615548253 : Dyadic) * half ^ 40),
        ((-30361750473 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((20839218121 : Dyadic) * half ^ 39),
        ((-43208726853 : Dyadic) * half ^ 39)⟩,
       ⟨((102585759837 : Dyadic) * half ^ 38),
        ((430385339023 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((20839218121 : Dyadic) * half ^ 39),
        ((-43208726853 : Dyadic) * half ^ 39)⟩,
       ⟨((-102585759837 : Dyadic) * half ^ 38),
        ((-430385339023 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((64949244453 : Dyadic) * half ^ 40),
        ((-22919872677 : Dyadic) * half ^ 37)⟩,
       ⟨((331615548253 : Dyadic) * half ^ 40),
        ((-30361750473 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word17Step48 :
    word17Chunk48.foldl (fun acc a => a.applyPacked acc)
      word17State48 = word17State49 := by decide +kernel

private def word17Chunk49 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word17State50 : PackedMat2 :=
    ⟨⟨⟨((76780850821 : Dyadic) * half ^ 41),
        ((334421309409 : Dyadic) * half ^ 41)⟩,
       ⟨((-1446868298937 : Dyadic) * half ^ 41),
        ((42294595323 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-518228702307 : Dyadic) * half ^ 41),
        ((-572065884197 : Dyadic) * half ^ 41)⟩,
       ⟨((1234064662541 : Dyadic) * half ^ 41),
        ((-80931210963 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((410203462271 : Dyadic) * half ^ 41),
        ((109518335303 : Dyadic) * half ^ 38)⟩,
       ⟨((-733928306123 : Dyadic) * half ^ 41),
        ((357917980117 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((249832118763 : Dyadic) * half ^ 41),
        ((761824574879 : Dyadic) * half ^ 41)⟩,
       ⟨((-419010500055 : Dyadic) * half ^ 41),
        ((342521862029 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word17Step49 :
    word17Chunk49.foldl (fun acc a => a.applyPacked acc)
      word17State49 = word17State50 := by decide +kernel

private def word17Chunk50 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word17State51 : PackedMat2 :=
    ⟨⟨⟨((713496057355 : Dyadic) * half ^ 40),
        ((90475826449 : Dyadic) * half ^ 41)⟩,
       ⟨((712215473753 : Dyadic) * half ^ 41),
        ((-251819372373 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((20051804777 : Dyadic) * half ^ 38),
        ((-226807566947 : Dyadic) * half ^ 42)⟩,
       ⟨((-40046914403 : Dyadic) * half ^ 36),
        ((-386706791563 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((40046914403 : Dyadic) * half ^ 36),
        ((386706791563 : Dyadic) * half ^ 42)⟩,
       ⟨((-20051804777 : Dyadic) * half ^ 38),
        ((226807566947 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((712215473753 : Dyadic) * half ^ 41),
        ((-251819372373 : Dyadic) * half ^ 40)⟩,
       ⟨((713496057355 : Dyadic) * half ^ 40),
        ((90475826449 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word17Step50 :
    word17Chunk50.foldl (fun acc a => a.applyPacked acc)
      word17State50 = word17State51 := by decide +kernel

private def word17Chunk51 : List Letter := [.h, .s]
private def word17State52 : PackedMat2 :=
    ⟨⟨⟨((567658444461 : Dyadic) * half ^ 42),
        ((1354246687803 : Dyadic) * half ^ 41)⟩,
       ⟨((-780469922545 : Dyadic) * half ^ 42),
        ((551801035537 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-1234085056439 : Dyadic) * half ^ 42),
        ((872629911969 : Dyadic) * half ^ 42)⟩,
       ⟨((-205755138665 : Dyadic) * half ^ 42),
        ((72745426907 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((1234085056439 : Dyadic) * half ^ 42),
        ((-872629911969 : Dyadic) * half ^ 42)⟩,
       ⟨((-205755138665 : Dyadic) * half ^ 42),
        ((72745426907 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((567658444461 : Dyadic) * half ^ 42),
        ((1354246687803 : Dyadic) * half ^ 41)⟩,
       ⟨((780469922545 : Dyadic) * half ^ 42),
        ((-551801035537 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word17Step51 :
    word17Chunk51.foldl (fun acc a => a.applyPacked acc)
      word17State51 = word17State52 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word17_check : check word17 17 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word17 = word17State52.toMatrix := by
    unfold evalRingPacked
    change ((
      word17Chunk0 ++ word17Chunk1 ++ word17Chunk2 ++ word17Chunk3 ++
      word17Chunk4 ++ word17Chunk5 ++ word17Chunk6 ++ word17Chunk7 ++
      word17Chunk8 ++ word17Chunk9 ++ word17Chunk10 ++ word17Chunk11 ++
      word17Chunk12 ++ word17Chunk13 ++ word17Chunk14 ++ word17Chunk15 ++
      word17Chunk16 ++ word17Chunk17 ++ word17Chunk18 ++ word17Chunk19 ++
      word17Chunk20 ++ word17Chunk21 ++ word17Chunk22 ++ word17Chunk23 ++
      word17Chunk24 ++ word17Chunk25 ++ word17Chunk26 ++ word17Chunk27 ++
      word17Chunk28 ++ word17Chunk29 ++ word17Chunk30 ++ word17Chunk31 ++
      word17Chunk32 ++ word17Chunk33 ++ word17Chunk34 ++ word17Chunk35 ++
      word17Chunk36 ++ word17Chunk37 ++ word17Chunk38 ++ word17Chunk39 ++
      word17Chunk40 ++ word17Chunk41 ++ word17Chunk42 ++ word17Chunk43 ++
      word17Chunk44 ++ word17Chunk45 ++ word17Chunk46 ++ word17Chunk47 ++
      word17Chunk48 ++ word17Chunk49 ++ word17Chunk50 ++ word17Chunk51
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word17Step0, word17Step1, word17Step2, word17Step3, word17Step4,
      word17Step5, word17Step6, word17Step7, word17Step8, word17Step9,
      word17Step10, word17Step11, word17Step12, word17Step13, word17Step14,
      word17Step15, word17Step16, word17Step17, word17Step18, word17Step19,
      word17Step20, word17Step21, word17Step22, word17Step23, word17Step24,
      word17Step25, word17Step26, word17Step27, word17Step28, word17Step29,
      word17Step30, word17Step31, word17Step32, word17Step33, word17Step34,
      word17Step35, word17Step36, word17Step37, word17Step38, word17Step39,
      word17Step40, word17Step41, word17Step42, word17Step43, word17Step44,
      word17Step45, word17Step46, word17Step47, word17Step48, word17Step49,
      word17Step50, word17Step51]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
