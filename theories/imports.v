From Coq Require Export ssreflect ssrbool.
From Coq Require Export Logic.PropExtensionality
  (propositional_extensionality) Program.Basics (const) FunInd.
From Equations Require Export Equations.
From Hammer Require Export Tactics.
From stdpp Require Export relations (rtc, rtc_transitive, rtc_once, rtc_inv, rtc(..), diamond, confluent, diamond_confluent, sn) base(sum_relation(..)).
Require Export Psatz.

Global Set Warnings "-notation-overridden".
Require Export Autosubst2.syntax Autosubst2.core Autosubst2.unscoped.
Export CombineNotations.

Notation "s [ sigmatm ]" := (subst_Term sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_Term xitm s) (at level 7, left associativity) : subst_scope.
Global Disable Notation "s '..'" : subst_scope.
Global Disable Notation "'var'" : subst_scope.
Global Disable Notation "↑".
Notation "s '…'" := (scons s ids) (at level 70) : subst_scope.
Global Open Scope subst_scope.
