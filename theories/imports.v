From Coq Require Export ssreflect ssrbool.
From Coq Require Export Logic.PropExtensionality
  (propositional_extensionality) Program.Basics (const) FunInd.
From Equations Require Export Equations.
Require Export Autosubst2.syntax Autosubst2.core Autosubst2.unscoped.
Export CombineNotations.
Derive NoConfusion for Ty.
Derive NoConfusion for Ki.
Derive NoConfusion for Tm.


From Hammer Require Export Tactics.
From stdpp Require Export relations (rtc, rtc_transitive, rtc_once, rtc_inv, rtc(..), diamond, confluent, diamond_confluent, sn) base(sum_relation(..)).
Require Export Psatz.

Global Set Warnings "-notation-overridden".

(* Notation "s [ sigmatm ]" := (subst_Term sigmatm s) (at level 7, left associativity) : subst_scope. *)
(* Notation "s ⟨ xitm ⟩" := (ren_Term xitm s) (at level 7, left associativity) : subst_scope. *)
Global Disable Notation "'var'" (all) : subst_scope.
Notation "s '…'" := (scons s ids) (at level 70) : subst_scope.
Global Open Scope subst_scope.
Global Open Scope list_scope.
Export List.
