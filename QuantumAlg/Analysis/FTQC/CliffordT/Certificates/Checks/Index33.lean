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
private def word33Chunk0 : List Letter := [.s, .s, .h, .s, .t, .h, .t, .h]
private def word33State1 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word33Step0 :
    word33Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word33State1 := by decide +kernel

private def word33Chunk1 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word33State2 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word33Step1 :
    word33Chunk1.foldl (fun acc a => a.applyPacked acc)
      word33State1 = word33State2 := by decide +kernel

private def word33Chunk2 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word33State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word33Step2 :
    word33Chunk2.foldl (fun acc a => a.applyPacked acc)
      word33State2 = word33State3 := by decide +kernel

private def word33Chunk3 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word33State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word33Step3 :
    word33Chunk3.foldl (fun acc a => a.applyPacked acc)
      word33State3 = word33State4 := by decide +kernel

private def word33Chunk4 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word33State5 : PackedMat2 :=
    ⟨⟨⟨((-19 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-21 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word33Step4 :
    word33Chunk4.foldl (fun acc a => a.applyPacked acc)
      word33State4 = word33State5 := by decide +kernel

private def word33Chunk5 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word33State6 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((19 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 6)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word33Step5 :
    word33Chunk5.foldl (fun acc a => a.applyPacked acc)
      word33State5 = word33State6 := by decide +kernel

private def word33Chunk6 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word33State7 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 4),
        ((11 : Dyadic) * half ^ 7)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-47 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 6),
        ((61 : Dyadic) * half ^ 7)⟩,
       ⟨((-13 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((37 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((29 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word33Step6 :
    word33Chunk6.foldl (fun acc a => a.applyPacked acc)
      word33State6 = word33State7 := by decide +kernel

private def word33Chunk7 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word33State8 : PackedMat2 :=
    ⟨⟨⟨((59 : Dyadic) * half ^ 7),
        ((37 : Dyadic) * half ^ 8)⟩,
       ⟨((-11 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 7),
        ((-63 : Dyadic) * half ^ 8)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 8)⟩,
       ⟨((-45 : Dyadic) * half ^ 7),
        ((63 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 8)⟩,
       ⟨((59 : Dyadic) * half ^ 7),
        ((37 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word33Step7 :
    word33Chunk7.foldl (fun acc a => a.applyPacked acc)
      word33State7 = word33State8 := by decide +kernel

private def word33Chunk8 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word33State9 : PackedMat2 :=
    ⟨⟨⟨((105 : Dyadic) * half ^ 8),
        ((67 : Dyadic) * half ^ 8)⟩,
       ⟨((95 : Dyadic) * half ^ 8),
        ((-101 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 8),
        ((23 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 8),
        ((-35 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((19 : Dyadic) * half ^ 8)⟩,
       ⟨((29 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 7),
        ((-25 : Dyadic) * half ^ 6)⟩,
       ⟨((-21 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word33Step8 :
    word33Chunk8.foldl (fun acc a => a.applyPacked acc)
      word33State8 = word33State9 := by decide +kernel

private def word33Chunk9 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word33State10 : PackedMat2 :=
    ⟨⟨⟨((259 : Dyadic) * half ^ 9),
        ((-31 : Dyadic) * half ^ 7)⟩,
       ⟨((203 : Dyadic) * half ^ 9),
        ((19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-173 : Dyadic) * half ^ 9),
        ((57 : Dyadic) * half ^ 9)⟩,
       ⟨((-191 : Dyadic) * half ^ 9),
        ((-139 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((191 : Dyadic) * half ^ 9),
        ((139 : Dyadic) * half ^ 9)⟩,
       ⟨((173 : Dyadic) * half ^ 9),
        ((-57 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((203 : Dyadic) * half ^ 9),
        ((19 : Dyadic) * half ^ 7)⟩,
       ⟨((259 : Dyadic) * half ^ 9),
        ((-31 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word33Step9 :
    word33Chunk9.foldl (fun acc a => a.applyPacked acc)
      word33State9 = word33State10 := by decide +kernel

private def word33Chunk10 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word33State11 : PackedMat2 :=
    ⟨⟨⟨((-471 : Dyadic) * half ^ 10),
        ((215 : Dyadic) * half ^ 10)⟩,
       ⟨((181 : Dyadic) * half ^ 10),
        ((-13 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((763 : Dyadic) * half ^ 10),
        ((167 : Dyadic) * half ^ 10)⟩,
       ⟨((195 : Dyadic) * half ^ 10),
        ((-55 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((57 : Dyadic) * half ^ 10),
        ((479 : Dyadic) * half ^ 10)⟩,
       ⟨((277 : Dyadic) * half ^ 10),
        ((71 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-189 : Dyadic) * half ^ 10),
        ((145 : Dyadic) * half ^ 10)⟩,
       ⟨((-241 : Dyadic) * half ^ 10),
        ((163 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word33Step10 :
    word33Chunk10.foldl (fun acc a => a.applyPacked acc)
      word33State10 = word33State11 := by decide +kernel

private def word33Chunk11 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word33State12 : PackedMat2 :=
    ⟨⟨⟨((147 : Dyadic) * half ^ 9),
        ((-9 : Dyadic) * half ^ 9)⟩,
       ⟨((-93 : Dyadic) * half ^ 10),
        ((95 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-435 : Dyadic) * half ^ 10),
        ((93 : Dyadic) * half ^ 9)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((541 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((435 : Dyadic) * half ^ 10),
        ((-93 : Dyadic) * half ^ 9)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((541 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((147 : Dyadic) * half ^ 9),
        ((-9 : Dyadic) * half ^ 9)⟩,
       ⟨((93 : Dyadic) * half ^ 10),
        ((-95 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word33Step11 :
    word33Chunk11.foldl (fun acc a => a.applyPacked acc)
      word33State11 = word33State12 := by decide +kernel

private def word33Chunk12 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word33State13 : PackedMat2 :=
    ⟨⟨⟨((-425 : Dyadic) * half ^ 11),
        ((-973 : Dyadic) * half ^ 11)⟩,
       ⟨((-593 : Dyadic) * half ^ 11),
        ((319 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1047 : Dyadic) * half ^ 11),
        ((19 : Dyadic) * half ^ 7)⟩,
       ⟨((303 : Dyadic) * half ^ 11),
        ((155 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-307 : Dyadic) * half ^ 10),
        ((93 : Dyadic) * half ^ 9)⟩,
       ⟨((3 : Dyadic) * half ^ 10),
        ((675 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-327 : Dyadic) * half ^ 10),
        ((-509 : Dyadic) * half ^ 11)⟩,
       ⟨((-323 : Dyadic) * half ^ 9),
        ((21 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word33Step12 :
    word33Chunk12.foldl (fun acc a => a.applyPacked acc)
      word33State12 = word33State13 := by decide +kernel

private def word33Chunk13 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word33State14 : PackedMat2 :=
    ⟨⟨⟨((-1639 : Dyadic) * half ^ 12),
        ((-401 : Dyadic) * half ^ 11)⟩,
       ⟨((-1393 : Dyadic) * half ^ 12),
        ((-47 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-3089 : Dyadic) * half ^ 12),
        ((583 : Dyadic) * half ^ 12)⟩,
       ⟨((-593 : Dyadic) * half ^ 12),
        ((63 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-593 : Dyadic) * half ^ 12),
        ((63 : Dyadic) * half ^ 12)⟩,
       ⟨((-3089 : Dyadic) * half ^ 12),
        ((583 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1393 : Dyadic) * half ^ 12),
        ((47 : Dyadic) * half ^ 9)⟩,
       ⟨((1639 : Dyadic) * half ^ 12),
        ((401 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word33Step13 :
    word33Chunk13.foldl (fun acc a => a.applyPacked acc)
      word33State13 = word33State14 := by decide +kernel

private def word33Chunk14 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word33State15 : PackedMat2 :=
    ⟨⟨⟨((991 : Dyadic) * half ^ 12),
        ((493 : Dyadic) * half ^ 11)⟩,
       ⟨((-733 : Dyadic) * half ^ 11),
        ((203 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-819 : Dyadic) * half ^ 10),
        ((53 : Dyadic) * half ^ 12)⟩,
       ⟨((447 : Dyadic) * half ^ 12),
        ((-233 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-519 : Dyadic) * half ^ 12),
        ((3723 : Dyadic) * half ^ 13)⟩,
       ⟨((-413 : Dyadic) * half ^ 12),
        ((-2829 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((145 : Dyadic) * half ^ 10),
        ((2457 : Dyadic) * half ^ 13)⟩,
       ⟨((-87 : Dyadic) * half ^ 8),
        ((475 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word33Step14 :
    word33Chunk14.foldl (fun acc a => a.applyPacked acc)
      word33State14 = word33State15 := by decide +kernel

private def word33Chunk15 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word33State16 : PackedMat2 :=
    ⟨⟨⟨((2919 : Dyadic) * half ^ 13),
        ((4893 : Dyadic) * half ^ 14)⟩,
       ⟨((695 : Dyadic) * half ^ 12),
        ((-3789 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((239 : Dyadic) * half ^ 13),
        ((-3163 : Dyadic) * half ^ 14)⟩,
       ⟨((-175 : Dyadic) * half ^ 8),
        ((1475 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((175 : Dyadic) * half ^ 8),
        ((-1475 : Dyadic) * half ^ 14)⟩,
       ⟨((-239 : Dyadic) * half ^ 13),
        ((3163 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((695 : Dyadic) * half ^ 12),
        ((-3789 : Dyadic) * half ^ 14)⟩,
       ⟨((2919 : Dyadic) * half ^ 13),
        ((4893 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word33Step15 :
    word33Chunk15.foldl (fun acc a => a.applyPacked acc)
      word33State15 = word33State16 := by decide +kernel

private def word33Chunk16 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word33State17 : PackedMat2 :=
    ⟨⟨⟨((-2097 : Dyadic) * half ^ 14),
        ((5551 : Dyadic) * half ^ 14)⟩,
       ⟨((-631 : Dyadic) * half ^ 14),
        ((2255 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1047 : Dyadic) * half ^ 14),
        ((349 : Dyadic) * half ^ 12)⟩,
       ⟨((-1205 : Dyadic) * half ^ 14),
        ((-2407 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1029 : Dyadic) * half ^ 11),
        ((-79 : Dyadic) * half ^ 14)⟩,
       ⟨((689 : Dyadic) * half ^ 10),
        ((563 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-3903 : Dyadic) * half ^ 13),
        ((341 : Dyadic) * half ^ 12)⟩,
       ⟨((-103 : Dyadic) * half ^ 9),
        ((733 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word33Step16 :
    word33Chunk16.foldl (fun acc a => a.applyPacked acc)
      word33State16 = word33State17 := by decide +kernel

private def word33Chunk17 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word33State18 : PackedMat2 :=
    ⟨⟨⟨((-4815 : Dyadic) * half ^ 15),
        ((1263 : Dyadic) * half ^ 14)⟩,
       ⟨((13105 : Dyadic) * half ^ 15),
        ((399 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((5517 : Dyadic) * half ^ 15),
        ((10207 : Dyadic) * half ^ 15)⟩,
       ⟨((3731 : Dyadic) * half ^ 15),
        ((-17439 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-3731 : Dyadic) * half ^ 15),
        ((17439 : Dyadic) * half ^ 15)⟩,
       ⟨((-5517 : Dyadic) * half ^ 15),
        ((-10207 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((13105 : Dyadic) * half ^ 15),
        ((399 : Dyadic) * half ^ 13)⟩,
       ⟨((-4815 : Dyadic) * half ^ 15),
        ((1263 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word33Step17 :
    word33Chunk17.foldl (fun acc a => a.applyPacked acc)
      word33State17 = word33State18 := by decide +kernel

private def word33Chunk18 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word33State19 : PackedMat2 :=
    ⟨⟨⟨((19593 : Dyadic) * half ^ 16),
        ((-2759 : Dyadic) * half ^ 15)⟩,
       ⟨((5609 : Dyadic) * half ^ 16),
        ((11007 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((15753 : Dyadic) * half ^ 16),
        ((7979 : Dyadic) * half ^ 14)⟩,
       ⟨((-25239 : Dyadic) * half ^ 16),
        ((18083 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((49999 : Dyadic) * half ^ 16),
        ((-4743 : Dyadic) * half ^ 16)⟩,
       ⟨((13833 : Dyadic) * half ^ 16),
        ((1281 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-5489 : Dyadic) * half ^ 16),
        ((-12601 : Dyadic) * half ^ 16)⟩,
       ⟨((16525 : Dyadic) * half ^ 16),
        ((-437 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word33Step18 :
    word33Chunk18.foldl (fun acc a => a.applyPacked acc)
      word33State18 = word33State19 := by decide +kernel

private def word33Chunk19 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word33State20 : PackedMat2 :=
    ⟨⟨⟨((-1591 : Dyadic) * half ^ 17),
        ((1207 : Dyadic) * half ^ 13)⟩,
       ⟨((45391 : Dyadic) * half ^ 17),
        ((45453 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-32601 : Dyadic) * half ^ 17),
        ((26283 : Dyadic) * half ^ 16)⟩,
       ⟨((59945 : Dyadic) * half ^ 17),
        ((-5317 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-47249 : Dyadic) * half ^ 17),
        ((-1709 : Dyadic) * half ^ 14)⟩,
       ⟨((-57883 : Dyadic) * half ^ 17),
        ((46273 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((64765 : Dyadic) * half ^ 17),
        ((5475 : Dyadic) * half ^ 15)⟩,
       ⟨((-26141 : Dyadic) * half ^ 17),
        ((-23491 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word33Step19 :
    word33Chunk19.foldl (fun acc a => a.applyPacked acc)
      word33State19 = word33State20 := by decide +kernel

private def word33Chunk20 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word33State21 : PackedMat2 :=
    ⟨⟨⟨((-20537 : Dyadic) * half ^ 17),
        ((3705 : Dyadic) * half ^ 18)⟩,
       ⟨((-10993 : Dyadic) * half ^ 15),
        ((13607 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-26059 : Dyadic) * half ^ 17),
        ((43073 : Dyadic) * half ^ 18)⟩,
       ⟨((14249 : Dyadic) * half ^ 14),
        ((15763 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-14249 : Dyadic) * half ^ 14),
        ((-15763 : Dyadic) * half ^ 18)⟩,
       ⟨((26059 : Dyadic) * half ^ 17),
        ((-43073 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-10993 : Dyadic) * half ^ 15),
        ((13607 : Dyadic) * half ^ 18)⟩,
       ⟨((-20537 : Dyadic) * half ^ 17),
        ((3705 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word33Step20 :
    word33Chunk20.foldl (fun acc a => a.applyPacked acc)
      word33State20 = word33State21 := by decide +kernel

private def word33Chunk21 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word33State22 : PackedMat2 :=
    ⟨⟨⟨((-66315 : Dyadic) * half ^ 18),
        ((-17611 : Dyadic) * half ^ 17)⟩,
       ⟨((19129 : Dyadic) * half ^ 18),
        ((-7957 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-114891 : Dyadic) * half ^ 18),
        ((-27137 : Dyadic) * half ^ 18)⟩,
       ⟨((-30833 : Dyadic) * half ^ 18),
        ((137381 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((27561 : Dyadic) * half ^ 16),
        ((-36431 : Dyadic) * half ^ 17)⟩,
       ⟨((-82259 : Dyadic) * half ^ 17),
        ((-42029 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((49439 : Dyadic) * half ^ 17),
        ((23593 : Dyadic) * half ^ 18)⟩,
       ⟨((-14217 : Dyadic) * half ^ 17),
        ((21361 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word33Step21 :
    word33Chunk21.foldl (fun acc a => a.applyPacked acc)
      word33State21 = word33State22 := by decide +kernel

private def word33Chunk22 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word33State23 : PackedMat2 :=
    ⟨⟨⟨((-199817 : Dyadic) * half ^ 19),
        ((70203 : Dyadic) * half ^ 19)⟩,
       ⟨((-29109 : Dyadic) * half ^ 19),
        ((1621 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-122319 : Dyadic) * half ^ 19),
        ((-275865 : Dyadic) * half ^ 19)⟩,
       ⟨((188305 : Dyadic) * half ^ 19),
        ((-25173 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((122319 : Dyadic) * half ^ 19),
        ((275865 : Dyadic) * half ^ 19)⟩,
       ⟨((188305 : Dyadic) * half ^ 19),
        ((-25173 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-199817 : Dyadic) * half ^ 19),
        ((70203 : Dyadic) * half ^ 19)⟩,
       ⟨((29109 : Dyadic) * half ^ 19),
        ((-1621 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word33Step22 :
    word33Chunk22.foldl (fun acc a => a.applyPacked acc)
      word33State22 = word33State23 := by decide +kernel

private def word33Chunk23 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word33State24 : PackedMat2 :=
    ⟨⟨⟨((49619 : Dyadic) * half ^ 20),
        ((432615 : Dyadic) * half ^ 20)⟩,
       ⟨((775039 : Dyadic) * half ^ 20),
        ((-18497 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-154659 : Dyadic) * half ^ 20),
        ((-178713 : Dyadic) * half ^ 20)⟩,
       ⟨((-106595 : Dyadic) * half ^ 20),
        ((-19321 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-255997 : Dyadic) * half ^ 20),
        ((-130627 : Dyadic) * half ^ 20)⟩,
       ⟨((-101429 : Dyadic) * half ^ 20),
        ((-751 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-358627 : Dyadic) * half ^ 20),
        ((-412329 : Dyadic) * half ^ 20)⟩,
       ⟨((-506603 : Dyadic) * half ^ 20),
        ((181355 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word33Step23 :
    word33Chunk23.foldl (fun acc a => a.applyPacked acc)
      word33State23 = word33State24 := by decide +kernel

private def word33Chunk24 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word33State25 : PackedMat2 :=
    ⟨⟨⟨((-16117 : Dyadic) * half ^ 19),
        ((-27553 : Dyadic) * half ^ 20)⟩,
       ⟨((4119 : Dyadic) * half ^ 20),
        ((642469 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-150225 : Dyadic) * half ^ 20),
        ((-254995 : Dyadic) * half ^ 20)⟩,
       ⟨((116453 : Dyadic) * half ^ 19),
        ((-2807 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((150225 : Dyadic) * half ^ 20),
        ((254995 : Dyadic) * half ^ 20)⟩,
       ⟨((116453 : Dyadic) * half ^ 19),
        ((-2807 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-16117 : Dyadic) * half ^ 19),
        ((-27553 : Dyadic) * half ^ 20)⟩,
       ⟨((-4119 : Dyadic) * half ^ 20),
        ((-642469 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word33Step24 :
    word33Chunk24.foldl (fun acc a => a.applyPacked acc)
      word33State24 = word33State25 := by decide +kernel

private def word33Chunk25 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word33State26 : PackedMat2 :=
    ⟨⟨⟨((-33643 : Dyadic) * half ^ 19),
        ((-1732537 : Dyadic) * half ^ 22)⟩,
       ⟨((1687347 : Dyadic) * half ^ 21),
        ((-129549 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-36437 : Dyadic) * half ^ 20),
        ((95199 : Dyadic) * half ^ 22)⟩,
       ⟨((105395 : Dyadic) * half ^ 21),
        ((-72293 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((41873 : Dyadic) * half ^ 20),
        ((-178269 : Dyadic) * half ^ 22)⟩,
       ⟨((-11453 : Dyadic) * half ^ 21),
        ((-32521 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((400747 : Dyadic) * half ^ 20),
        ((1821919 : Dyadic) * half ^ 22)⟩,
       ⟨((-931043 : Dyadic) * half ^ 21),
        ((1552775 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word33Step25 :
    word33Chunk25.foldl (fun acc a => a.applyPacked acc)
      word33State25 = word33State26 := by decide +kernel

private def word33Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word33State27 : PackedMat2 :=
    ⟨⟨⟨((-1867 : Dyadic) * half ^ 22),
        ((-4429437 : Dyadic) * half ^ 23)⟩,
       ⟨((-433233 : Dyadic) * half ^ 21),
        ((2102849 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1913381 : Dyadic) * half ^ 22),
        ((663855 : Dyadic) * half ^ 23)⟩,
       ⟨((107475 : Dyadic) * half ^ 19),
        ((632205 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-15825 : Dyadic) * half ^ 22),
        ((-1053581 : Dyadic) * half ^ 23)⟩,
       ⟨((324015 : Dyadic) * half ^ 21),
        ((2773181 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-3266143 : Dyadic) * half ^ 22),
        ((864599 : Dyadic) * half ^ 23)⟩,
       ⟨((581647 : Dyadic) * half ^ 21),
        ((868333 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word33Step26 :
    word33Chunk26.foldl (fun acc a => a.applyPacked acc)
      word33State26 = word33State27 := by decide +kernel

private def word33Chunk27 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word33State28 : PackedMat2 :=
    ⟨⟨⟨((-824795 : Dyadic) * half ^ 22),
        ((-180341 : Dyadic) * half ^ 21)⟩,
       ⟨((620591 : Dyadic) * half ^ 22),
        ((-3397287 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-97039 : Dyadic) * half ^ 22),
        ((3811997 : Dyadic) * half ^ 23)⟩,
       ⟨((104945 : Dyadic) * half ^ 19),
        ((140197 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-6055149 : Dyadic) * half ^ 23),
        ((-742521 : Dyadic) * half ^ 23)⟩,
       ⟨((-1568845 : Dyadic) * half ^ 23),
        ((936599 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-4118651 : Dyadic) * half ^ 23),
        ((-51051 : Dyadic) * half ^ 21)⟩,
       ⟨((2675923 : Dyadic) * half ^ 23),
        ((-722693 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word33Step27 :
    word33Chunk27.foldl (fun acc a => a.applyPacked acc)
      word33State27 = word33State28 := by decide +kernel

private def word33Chunk28 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word33State29 : PackedMat2 :=
    ⟨⟨⟨((164311 : Dyadic) * half ^ 21),
        ((-3527919 : Dyadic) * half ^ 23)⟩,
       ⟨((-107439 : Dyadic) * half ^ 23),
        ((-2311823 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-428677 : Dyadic) * half ^ 23),
        ((-1632705 : Dyadic) * half ^ 24)⟩,
       ⟨((6377823 : Dyadic) * half ^ 23),
        ((289215 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1054275 : Dyadic) * half ^ 24),
        ((2974573 : Dyadic) * half ^ 23)⟩,
       ⟨((-2211135 : Dyadic) * half ^ 24),
        ((-1701625 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((9367661 : Dyadic) * half ^ 24),
        ((-549805 : Dyadic) * half ^ 24)⟩,
       ⟨((4744015 : Dyadic) * half ^ 24),
        ((-764683 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word33Step28 :
    word33Chunk28.foldl (fun acc a => a.applyPacked acc)
      word33State28 = word33State29 := by decide +kernel

private def word33Chunk29 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word33State30 : PackedMat2 :=
    ⟨⟨⟨((-6700979 : Dyadic) * half ^ 25),
        ((8499639 : Dyadic) * half ^ 25)⟩,
       ⟨((-20593941 : Dyadic) * half ^ 25),
        ((-149145 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-15423915 : Dyadic) * half ^ 25),
        ((1303613 : Dyadic) * half ^ 25)⟩,
       ⟨((-14882153 : Dyadic) * half ^ 25),
        ((356547 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((15423915 : Dyadic) * half ^ 25),
        ((-1303613 : Dyadic) * half ^ 25)⟩,
       ⟨((-14882153 : Dyadic) * half ^ 25),
        ((356547 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-6700979 : Dyadic) * half ^ 25),
        ((8499639 : Dyadic) * half ^ 25)⟩,
       ⟨((20593941 : Dyadic) * half ^ 25),
        ((149145 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word33Step29 :
    word33Chunk29.foldl (fun acc a => a.applyPacked acc)
      word33State29 = word33State30 := by decide +kernel

private def word33Chunk30 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word33State31 : PackedMat2 :=
    ⟨⟨⟨((20275941 : Dyadic) * half ^ 26),
        ((16933033 : Dyadic) * half ^ 26)⟩,
       ⟨((-14361727 : Dyadic) * half ^ 26),
        ((-196799 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-41700301 : Dyadic) * half ^ 26),
        ((8872145 : Dyadic) * half ^ 26)⟩,
       ⟨((37614555 : Dyadic) * half ^ 26),
        ((101905 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((9279765 : Dyadic) * half ^ 26),
        ((-2042873 : Dyadic) * half ^ 26)⟩,
       ⟨((8464525 : Dyadic) * half ^ 26),
        ((-9914357 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-16145837 : Dyadic) * half ^ 26),
        ((-2957107 : Dyadic) * half ^ 26)⟩,
       ⟨((-17720229 : Dyadic) * half ^ 26),
        ((-8659417 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word33Step30 :
    word33Chunk30.foldl (fun acc a => a.applyPacked acc)
      word33State30 = word33State31 := by decide +kernel

private def word33Chunk31 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word33State32 : PackedMat2 :=
    ⟨⟨⟨((19829279 : Dyadic) * half ^ 27),
        ((875309 : Dyadic) * half ^ 21)⟩,
       ⟨((-15025247 : Dyadic) * half ^ 27),
        ((-12382925 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((3844121 : Dyadic) * half ^ 27),
        ((-27358439 : Dyadic) * half ^ 26)⟩,
       ⟨((23557471 : Dyadic) * half ^ 27),
        ((-46123371 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((100840249 : Dyadic) * half ^ 27),
        ((-3425199 : Dyadic) * half ^ 25)⟩,
       ⟨((8593507 : Dyadic) * half ^ 27),
        ((9856675 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((43636851 : Dyadic) * half ^ 27),
        ((75063 : Dyadic) * half ^ 22)⟩,
       ⟨((68402701 : Dyadic) * half ^ 27),
        ((17427263 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word33Step31 :
    word33Chunk31.foldl (fun acc a => a.applyPacked acc)
      word33State31 = word33State32 := by decide +kernel

private def word33Chunk32 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word33State33 : PackedMat2 :=
    ⟨⟨⟨((75311135 : Dyadic) * half ^ 27),
        ((-13911167 : Dyadic) * half ^ 28)⟩,
       ⟨((-546225 : Dyadic) * half ^ 27),
        ((-13722349 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-29491495 : Dyadic) * half ^ 26),
        ((62350417 : Dyadic) * half ^ 28)⟩,
       ⟨((-27057975 : Dyadic) * half ^ 26),
        ((-87179183 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-29491495 : Dyadic) * half ^ 26),
        ((62350417 : Dyadic) * half ^ 28)⟩,
       ⟨((27057975 : Dyadic) * half ^ 26),
        ((87179183 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-75311135 : Dyadic) * half ^ 27),
        ((13911167 : Dyadic) * half ^ 28)⟩,
       ⟨((-546225 : Dyadic) * half ^ 27),
        ((-13722349 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word33Step32 :
    word33Chunk32.foldl (fun acc a => a.applyPacked acc)
      word33State32 = word33State33 := by decide +kernel

private def word33Chunk33 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word33State34 : PackedMat2 :=
    ⟨⟨⟨((-133842309 : Dyadic) * half ^ 28),
        ((165841293 : Dyadic) * half ^ 29)⟩,
       ⟨((14519569 : Dyadic) * half ^ 25),
        ((161755275 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((112552605 : Dyadic) * half ^ 28),
        ((33872893 : Dyadic) * half ^ 29)⟩,
       ⟨((-278557 : Dyadic) * half ^ 22),
        ((22708311 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-5582291 : Dyadic) * half ^ 28),
        ((-130380253 : Dyadic) * half ^ 29)⟩,
       ⟨((14145301 : Dyadic) * half ^ 27),
        ((94724957 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((2043009 : Dyadic) * half ^ 28),
        ((-249998861 : Dyadic) * half ^ 29)⟩,
       ⟨((-40949571 : Dyadic) * half ^ 26),
        ((17685757 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word33Step33 :
    word33Chunk33.foldl (fun acc a => a.applyPacked acc)
      word33State33 = word33State34 := by decide +kernel

private def word33Chunk34 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word33State35 : PackedMat2 :=
    ⟨⟨⟨((14146475 : Dyadic) * half ^ 29),
        ((-353987841 : Dyadic) * half ^ 29)⟩,
       ⟨((-57909975 : Dyadic) * half ^ 29),
        ((40562609 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-87099657 : Dyadic) * half ^ 29),
        ((-44049953 : Dyadic) * half ^ 28)⟩,
       ⟨((-5127429 : Dyadic) * half ^ 29),
        ((120679 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((5127429 : Dyadic) * half ^ 29),
        ((-120679 : Dyadic) * half ^ 20)⟩,
       ⟨((87099657 : Dyadic) * half ^ 29),
        ((44049953 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-57909975 : Dyadic) * half ^ 29),
        ((40562609 : Dyadic) * half ^ 29)⟩,
       ⟨((14146475 : Dyadic) * half ^ 29),
        ((-353987841 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word33Step34 :
    word33Chunk34.foldl (fun acc a => a.applyPacked acc)
      word33State34 = word33State35 := by decide +kernel

private def word33Chunk35 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word33State36 : PackedMat2 :=
    ⟨⟨⟨((13384987 : Dyadic) * half ^ 26),
        ((-116579885 : Dyadic) * half ^ 28)⟩,
       ⟨((-298610275 : Dyadic) * half ^ 29),
        ((-1636433 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((119245679 : Dyadic) * half ^ 29),
        ((83470807 : Dyadic) * half ^ 28)⟩,
       ⟨((45406373 : Dyadic) * half ^ 28),
        ((12667959 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((154273655 : Dyadic) * half ^ 29),
        ((28432933 : Dyadic) * half ^ 30)⟩,
       ⟨((-179609573 : Dyadic) * half ^ 29),
        ((-210058425 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((110034153 : Dyadic) * half ^ 28),
        ((-405690171 : Dyadic) * half ^ 30)⟩,
       ⟨((-123125617 : Dyadic) * half ^ 28),
        ((-191530379 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word33Step35 :
    word33Chunk35.foldl (fun acc a => a.applyPacked acc)
      word33State35 = word33State36 := by decide +kernel

private def word33Chunk36 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word33State37 : PackedMat2 :=
    ⟨⟨⟨((38120461 : Dyadic) * half ^ 30),
        ((224851589 : Dyadic) * half ^ 30)⟩,
       ⟨((-199697107 : Dyadic) * half ^ 28),
        ((369629 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-28831899 : Dyadic) * half ^ 27),
        ((238287199 : Dyadic) * half ^ 30)⟩,
       ⟨((-474810087 : Dyadic) * half ^ 30),
        ((-100191121 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((28831899 : Dyadic) * half ^ 27),
        ((-238287199 : Dyadic) * half ^ 30)⟩,
       ⟨((-474810087 : Dyadic) * half ^ 30),
        ((-100191121 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((38120461 : Dyadic) * half ^ 30),
        ((224851589 : Dyadic) * half ^ 30)⟩,
       ⟨((199697107 : Dyadic) * half ^ 28),
        ((-369629 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word33Step36 :
    word33Chunk36.foldl (fun acc a => a.applyPacked acc)
      word33State36 = word33State37 := by decide +kernel

private def word33Chunk37 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word33State38 : PackedMat2 :=
    ⟨⟨⟨((455006643 : Dyadic) * half ^ 30),
        ((-170871005 : Dyadic) * half ^ 32)⟩,
       ⟨((179173571 : Dyadic) * half ^ 31),
        ((-1853338957 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((587378779 : Dyadic) * half ^ 30),
        ((575980747 : Dyadic) * half ^ 32)⟩,
       ⟨((-657367539 : Dyadic) * half ^ 31),
        ((287622191 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((72089639 : Dyadic) * half ^ 30),
        ((1832125097 : Dyadic) * half ^ 32)⟩,
       ⟨((-431801469 : Dyadic) * half ^ 31),
        ((-517390019 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-105154247 : Dyadic) * half ^ 28),
        ((-730839715 : Dyadic) * half ^ 32)⟩,
       ⟨((-1012104981 : Dyadic) * half ^ 31),
        ((1089186857 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word33Step37 :
    word33Chunk37.foldl (fun acc a => a.applyPacked acc)
      word33State37 = word33State38 := by decide +kernel

private def word33Chunk38 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word33State39 : PackedMat2 :=
    ⟨⟨⟨((307322963 : Dyadic) * half ^ 32),
        ((1692871669 : Dyadic) * half ^ 32)⟩,
       ⟨((-2118083229 : Dyadic) * half ^ 32),
        ((-194252305 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1412521857 : Dyadic) * half ^ 32),
        ((13034623 : Dyadic) * half ^ 29)⟩,
       ⟨((2372393035 : Dyadic) * half ^ 32),
        ((-113703167 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((2372393035 : Dyadic) * half ^ 32),
        ((-113703167 : Dyadic) * half ^ 30)⟩,
       ⟨((1412521857 : Dyadic) * half ^ 32),
        ((13034623 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((2118083229 : Dyadic) * half ^ 32),
        ((194252305 : Dyadic) * half ^ 32)⟩,
       ⟨((-307322963 : Dyadic) * half ^ 32),
        ((-1692871669 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word33Step38 :
    word33Chunk38.foldl (fun acc a => a.applyPacked acc)
      word33State38 = word33State39 := by decide +kernel

private def word33Chunk39 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word33State40 : PackedMat2 :=
    ⟨⟨⟨((5153290883 : Dyadic) * half ^ 33),
        ((1197016357 : Dyadic) * half ^ 32)⟩,
       ⟨((477908005 : Dyadic) * half ^ 33),
        ((-905147149 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-3662458431 : Dyadic) * half ^ 33),
        ((1386357329 : Dyadic) * half ^ 32)⟩,
       ⟨((-1384227453 : Dyadic) * half ^ 33),
        ((1263966923 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-4036681581 : Dyadic) * half ^ 33),
        ((1261671471 : Dyadic) * half ^ 32)⟩,
       ⟨((-1508747735 : Dyadic) * half ^ 33),
        ((1139115489 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1488885565 : Dyadic) * half ^ 33),
        ((703899861 : Dyadic) * half ^ 31)⟩,
       ⟨((3299179863 : Dyadic) * half ^ 33),
        ((2337691439 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word33Step39 :
    word33Chunk39.foldl (fun acc a => a.applyPacked acc)
      word33State39 = word33State40 := by decide +kernel

private def word33Chunk40 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word33State41 : PackedMat2 :=
    ⟨⟨⟨((1275118753 : Dyadic) * half ^ 31),
        ((3591436365 : Dyadic) * half ^ 34)⟩,
       ⟨((480095845 : Dyadic) * half ^ 31),
        ((-1987921363 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((134782519 : Dyadic) * half ^ 33),
        ((-3830194651 : Dyadic) * half ^ 34)⟩,
       ⟨((-4927306741 : Dyadic) * half ^ 33),
        ((2838105631 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((134782519 : Dyadic) * half ^ 33),
        ((-3830194651 : Dyadic) * half ^ 34)⟩,
       ⟨((4927306741 : Dyadic) * half ^ 33),
        ((-2838105631 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1275118753 : Dyadic) * half ^ 31),
        ((-3591436365 : Dyadic) * half ^ 34)⟩,
       ⟨((480095845 : Dyadic) * half ^ 31),
        ((-1987921363 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word33Step40 :
    word33Chunk40.foldl (fun acc a => a.applyPacked acc)
      word33State40 = word33State41 := by decide +kernel

private def word33Chunk41 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word33State42 : PackedMat2 :=
    ⟨⟨⟨((2982709305 : Dyadic) * half ^ 34),
        ((850101881 : Dyadic) * half ^ 34)⟩,
       ⟨((1059710841 : Dyadic) * half ^ 33),
        ((2731202785 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-6227806223 : Dyadic) * half ^ 33),
        ((1795559489 : Dyadic) * half ^ 34)⟩,
       ⟨((-7526192963 : Dyadic) * half ^ 34),
        ((-1096443523 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((6227806223 : Dyadic) * half ^ 33),
        ((-1795559489 : Dyadic) * half ^ 34)⟩,
       ⟨((-7526192963 : Dyadic) * half ^ 34),
        ((-1096443523 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((2982709305 : Dyadic) * half ^ 34),
        ((850101881 : Dyadic) * half ^ 34)⟩,
       ⟨((-1059710841 : Dyadic) * half ^ 33),
        ((-2731202785 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word33Step41 :
    word33Chunk41.foldl (fun acc a => a.applyPacked acc)
      word33State41 = word33State42 := by decide +kernel

private def word33Chunk42 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word33State43 : PackedMat2 :=
    ⟨⟨⟨((139949023 : Dyadic) * half ^ 34),
        ((-24941197939 : Dyadic) * half ^ 36)⟩,
       ⟨((16799523457 : Dyadic) * half ^ 35),
        ((1009627643 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((2402402245 : Dyadic) * half ^ 34),
        ((-27820468833 : Dyadic) * half ^ 36)⟩,
       ⟨((-10036195803 : Dyadic) * half ^ 35),
        ((-12324554571 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((10036195803 : Dyadic) * half ^ 35),
        ((12324554571 : Dyadic) * half ^ 36)⟩,
       ⟨((-2402402245 : Dyadic) * half ^ 34),
        ((27820468833 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((16799523457 : Dyadic) * half ^ 35),
        ((1009627643 : Dyadic) * half ^ 36)⟩,
       ⟨((139949023 : Dyadic) * half ^ 34),
        ((-24941197939 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word33Step42 :
    word33Chunk42.foldl (fun acc a => a.applyPacked acc)
      word33State42 = word33State43 := by decide +kernel

private def word33Chunk43 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word33State44 : PackedMat2 :=
    ⟨⟨⟨((-311947581 : Dyadic) * half ^ 31),
        ((6321668099 : Dyadic) * half ^ 36)⟩,
       ⟨((-5184363357 : Dyadic) * half ^ 34),
        ((-5928101093 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-7241175483 : Dyadic) * half ^ 35),
        ((4504090325 : Dyadic) * half ^ 33)⟩,
       ⟨((-2275865525 : Dyadic) * half ^ 33),
        ((-18623465493 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-2275865525 : Dyadic) * half ^ 33),
        ((-18623465493 : Dyadic) * half ^ 36)⟩,
       ⟨((-7241175483 : Dyadic) * half ^ 35),
        ((4504090325 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((5184363357 : Dyadic) * half ^ 34),
        ((5928101093 : Dyadic) * half ^ 35)⟩,
       ⟨((311947581 : Dyadic) * half ^ 31),
        ((-6321668099 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word33Step43 :
    word33Chunk43.foldl (fun acc a => a.applyPacked acc)
      word33State43 = word33State44 := by decide +kernel

private def word33Chunk44 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word33State45 : PackedMat2 :=
    ⟨⟨⟨((30690722105 : Dyadic) * half ^ 37),
        ((-1927841497 : Dyadic) * half ^ 35)⟩,
       ⟨((-9261754217 : Dyadic) * half ^ 37),
        ((38850704875 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((108082916687 : Dyadic) * half ^ 37),
        ((-230673019 : Dyadic) * half ^ 33)⟩,
       ⟨((31116152933 : Dyadic) * half ^ 37),
        ((31989882411 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-28299114107 : Dyadic) * half ^ 37),
        ((-34799767405 : Dyadic) * half ^ 36)⟩,
       ⟨((35680650715 : Dyadic) * half ^ 37),
        ((-38483381877 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((31139338887 : Dyadic) * half ^ 37),
        ((1339310493 : Dyadic) * half ^ 34)⟩,
       ⟨((-46562070863 : Dyadic) * half ^ 37),
        ((19976238161 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word33Step44 :
    word33Chunk44.foldl (fun acc a => a.applyPacked acc)
      word33State44 = word33State45 := by decide +kernel

private def word33Chunk45 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word33State46 : PackedMat2 :=
    ⟨⟨⟨((12477587587 : Dyadic) * half ^ 37),
        ((23829899641 : Dyadic) * half ^ 38)⟩,
       ⟨((108237524271 : Dyadic) * half ^ 37),
        ((-20663888509 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-7308983831 : Dyadic) * half ^ 36),
        ((37242329401 : Dyadic) * half ^ 38)⟩,
       ⟨((35342989851 : Dyadic) * half ^ 36),
        ((35136750617 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((65799337 : Dyadic) * half ^ 33),
        ((-21325986841 : Dyadic) * half ^ 36)⟩,
       ⟨((-36189540009 : Dyadic) * half ^ 37),
        ((-7008501505 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-22246894075 : Dyadic) * half ^ 37),
        ((23939984171 : Dyadic) * half ^ 36)⟩,
       ⟨((791502783 : Dyadic) * half ^ 36),
        ((60357555929 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word33Step45 :
    word33Chunk45.foldl (fun acc a => a.applyPacked acc)
      word33State45 = word33State46 := by decide +kernel

private def word33Chunk46 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word33State47 : PackedMat2 :=
    ⟨⟨⟨((-14604805789 : Dyadic) * half ^ 38),
        ((-12082146281 : Dyadic) * half ^ 36)⟩,
       ⟨((59618445819 : Dyadic) * half ^ 37),
        ((4533730849 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-36381954209 : Dyadic) * half ^ 36),
        ((18565914449 : Dyadic) * half ^ 37)⟩,
       ⟨((177136068585 : Dyadic) * half ^ 38),
        ((11734754119 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((36381954209 : Dyadic) * half ^ 36),
        ((-18565914449 : Dyadic) * half ^ 37)⟩,
       ⟨((177136068585 : Dyadic) * half ^ 38),
        ((11734754119 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-14604805789 : Dyadic) * half ^ 38),
        ((-12082146281 : Dyadic) * half ^ 36)⟩,
       ⟨((-59618445819 : Dyadic) * half ^ 37),
        ((-4533730849 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word33Step46 :
    word33Chunk46.foldl (fun acc a => a.applyPacked acc)
      word33State46 = word33State47 := by decide +kernel

private def word33Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word33State48 : PackedMat2 :=
    ⟨⟨⟨((-134283699439 : Dyadic) * half ^ 39),
        ((-285446078997 : Dyadic) * half ^ 39)⟩,
       ⟨((151301055365 : Dyadic) * half ^ 39),
        ((-115323072637 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-34029946361 : Dyadic) * half ^ 39),
        ((46391141293 : Dyadic) * half ^ 38)⟩,
       ⟨((132398729181 : Dyadic) * half ^ 39),
        ((-4183593021 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((20546347043 : Dyadic) * half ^ 38),
        ((-24592195705 : Dyadic) * half ^ 38)⟩,
       ⟨((-113328629629 : Dyadic) * half ^ 38),
        ((83214337771 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-200384575817 : Dyadic) * half ^ 38),
        ((8508677963 : Dyadic) * half ^ 39)⟩,
       ⟨((-21265375795 : Dyadic) * half ^ 36),
        ((-71396188701 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word33Step47 :
    word33Chunk47.foldl (fun acc a => a.applyPacked acc)
      word33State47 = word33State48 := by decide +kernel

private def word33Chunk48 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word33State49 : PackedMat2 :=
    ⟨⟨⟨((-153110415925 : Dyadic) * half ^ 40),
        ((82597245823 : Dyadic) * half ^ 39)⟩,
       ⟨((-553955177257 : Dyadic) * half ^ 40),
        ((-295489305069 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-5995223001 : Dyadic) * half ^ 40),
        ((-163783861341 : Dyadic) * half ^ 39)⟩,
       ⟨((-358822424993 : Dyadic) * half ^ 40),
        ((391164723305 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-5995223001 : Dyadic) * half ^ 40),
        ((-163783861341 : Dyadic) * half ^ 39)⟩,
       ⟨((358822424993 : Dyadic) * half ^ 40),
        ((-391164723305 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((153110415925 : Dyadic) * half ^ 40),
        ((-82597245823 : Dyadic) * half ^ 39)⟩,
       ⟨((-553955177257 : Dyadic) * half ^ 40),
        ((-295489305069 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word33Step48 :
    word33Chunk48.foldl (fun acc a => a.applyPacked acc)
      word33State48 = word33State49 := by decide +kernel

private def word33Chunk49 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word33State50 : PackedMat2 :=
    ⟨⟨⟨((445169691775 : Dyadic) * half ^ 40),
        ((234973305913 : Dyadic) * half ^ 40)⟩,
       ⟨((-68931965691 : Dyadic) * half ^ 37),
        ((1202018847 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-56177929537 : Dyadic) * half ^ 38),
        ((-57991363665 : Dyadic) * half ^ 39)⟩,
       ⟨((665144700433 : Dyadic) * half ^ 40),
        ((-195450421303 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-79467693973 : Dyadic) * half ^ 40),
        ((889856418581 : Dyadic) * half ^ 41)⟩,
       ⟨((-311433148633 : Dyadic) * half ^ 40),
        ((440432982285 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((116885643533 : Dyadic) * half ^ 39),
        ((996625417303 : Dyadic) * half ^ 41)⟩,
       ⟨((-29521915595 : Dyadic) * half ^ 37),
        ((106286033753 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word33Step49 :
    word33Chunk49.foldl (fun acc a => a.applyPacked acc)
      word33State49 = word33State50 := by decide +kernel

private def word33Chunk50 : List Letter := [.h, .s, .t, .h, .t, .h, .t]
private def word33State51 : PackedMat2 :=
    ⟨⟨⟨((941934643381 : Dyadic) * half ^ 41),
        ((1777791764437 : Dyadic) * half ^ 42)⟩,
       ⟨((34035145209 : Dyadic) * half ^ 39),
        ((-192531856945 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-663338868027 : Dyadic) * half ^ 41),
        ((938102823613 : Dyadic) * half ^ 42)⟩,
       ⟨((-425893942757 : Dyadic) * half ^ 40),
        ((1204609979959 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((663338868027 : Dyadic) * half ^ 41),
        ((-938102823613 : Dyadic) * half ^ 42)⟩,
       ⟨((-425893942757 : Dyadic) * half ^ 40),
        ((1204609979959 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((941934643381 : Dyadic) * half ^ 41),
        ((1777791764437 : Dyadic) * half ^ 42)⟩,
       ⟨((-34035145209 : Dyadic) * half ^ 39),
        ((192531856945 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word33Step50 :
    word33Chunk50.foldl (fun acc a => a.applyPacked acc)
      word33State50 = word33State51 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word33_check : check word33 33 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word33 = word33State51.toMatrix := by
    unfold evalRingPacked
    change ((
      word33Chunk0 ++ word33Chunk1 ++ word33Chunk2 ++ word33Chunk3 ++
      word33Chunk4 ++ word33Chunk5 ++ word33Chunk6 ++ word33Chunk7 ++
      word33Chunk8 ++ word33Chunk9 ++ word33Chunk10 ++ word33Chunk11 ++
      word33Chunk12 ++ word33Chunk13 ++ word33Chunk14 ++ word33Chunk15 ++
      word33Chunk16 ++ word33Chunk17 ++ word33Chunk18 ++ word33Chunk19 ++
      word33Chunk20 ++ word33Chunk21 ++ word33Chunk22 ++ word33Chunk23 ++
      word33Chunk24 ++ word33Chunk25 ++ word33Chunk26 ++ word33Chunk27 ++
      word33Chunk28 ++ word33Chunk29 ++ word33Chunk30 ++ word33Chunk31 ++
      word33Chunk32 ++ word33Chunk33 ++ word33Chunk34 ++ word33Chunk35 ++
      word33Chunk36 ++ word33Chunk37 ++ word33Chunk38 ++ word33Chunk39 ++
      word33Chunk40 ++ word33Chunk41 ++ word33Chunk42 ++ word33Chunk43 ++
      word33Chunk44 ++ word33Chunk45 ++ word33Chunk46 ++ word33Chunk47 ++
      word33Chunk48 ++ word33Chunk49 ++ word33Chunk50
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word33Step0, word33Step1, word33Step2, word33Step3, word33Step4,
      word33Step5, word33Step6, word33Step7, word33Step8, word33Step9,
      word33Step10, word33Step11, word33Step12, word33Step13, word33Step14,
      word33Step15, word33Step16, word33Step17, word33Step18, word33Step19,
      word33Step20, word33Step21, word33Step22, word33Step23, word33Step24,
      word33Step25, word33Step26, word33Step27, word33Step28, word33Step29,
      word33Step30, word33Step31, word33Step32, word33Step33, word33Step34,
      word33Step35, word33Step36, word33Step37, word33Step38, word33Step39,
      word33Step40, word33Step41, word33Step42, word33Step43, word33Step44,
      word33Step45, word33Step46, word33Step47, word33Step48, word33Step49,
      word33Step50]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
