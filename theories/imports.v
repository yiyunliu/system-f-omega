From Coq Require Export ssreflect ssrbool.
From Coq Require Export Logic.PropExtensionality
  (propositional_extensionality) Program.Basics (const).
From Equations Require Export Equations.
Require Export Autosubst2.syntax Autosubst2.core Autosubst2.unscoped.
Export CombineNotations.
Derive NoConfusion for Ty.
Derive NoConfusion for Ki.
Derive NoConfusion for Tm.


From Hammer Require Export Tactics.
Require Export Psatz.

Global Set Warnings "-notation-overridden".

Global Disable Notation "'var'" (all) : subst_scope.
Notation "s '…'" := (scons s ids) (at level 70) : subst_scope.
Global Open Scope subst_scope.
Global Open Scope list_scope.
Export List.
