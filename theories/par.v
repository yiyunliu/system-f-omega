Require Export imports.
From Ltac2 Require Import Ltac2.
Import Ltac2.Constr.
Import Ltac2.Constr.Unsafe.
Require Ltac2.Control.
Set Default Proof Mode "Classic".

Inductive TyPar : Ty -> Ty -> Type :=
| TP_Var i :
  TyPar (VarTy i) (VarTy i)
| TP_Abs k A0 A1 a0 a1 :
  TyPar A0 A1 ->
  TyPar a0 a1 ->
  (* ------------------- *)
  TyPar (TyAbs k a0) (TyAbs k a1)
| TP_App b0 b1 a0 a1 :
  TyPar b0 b1 ->
  TyPar a0 a1 ->
  (* ---------------------------- *)
  TyPar (TyApp b0 a0) (TyApp b1 a1)
| TP_AppAbs k b0 b1 a0 a1 :
  TyPar b0 b1 ->
  TyPar a0 a1 ->
  (* ---------------------------- *)
  TyPar (TyApp (TyAbs k b0) a0) (subst_Ty (a1…) b1)
| TP_Fun b0 b1 a0 a1 :
  TyPar b0 b1 ->
  TyPar a0 a1 ->
  (* -------------------------------- *)
  TyPar (TyFun b0 a0) (TyFun b1 a1)

| TP_Forall k a0 a1 :
  TyPar a0 a1 ->
  (* -------------------------------------- *)
  TyPar (TyForall k a0) (TyForall k a1).

#[export]Hint Constructors TyPar : par.

Inductive RTC  : Ty -> Ty -> Type :=
| RTC_Refl A :
  RTC A A
| RTC_Step A B C :
  TyPar A B ->
  RTC B C ->
  RTC A C.

Definition ICoherent A0 A1 : Type :=
  { B : Ty &  prod (RTC A0 B) (RTC A1 B)}.

(* Based on https://poplmark-reloaded.github.io/coq/well-scoped/PR.sn_defs.html *)
Inductive SN : Tm -> Prop :=
| S_Neu a : SNe a -> SN a
| S_Abs a : SN a -> SN (TmAbs a)
| S_Red a0 a1 : SNRed a0 a1 -> SN a1 -> SN a0
with SNe : Tm -> Prop :=
| S_Var i : SNe (VarTm i)
| S_App a b : SNe a -> SN b -> SNe (TmApp a b)
with SNRed : Tm -> Tm -> Prop :=
| S_AppL a0 a1 b :
  SNRed a0 a1 ->
  SNRed (TmApp a0 b) (TmApp a1 b)
| S_AppAbs a b :
  SN b ->
  SNRed (TmApp (TmAbs a) b) (subst_Tm (b…) a).

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2 := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.

Record CR (S : Tm -> Prop) : Prop := CR_intro
  { CR1 : forall a, S a -> SN a
  ; CR2 : forall a b, SNRed a b -> S b -> S a
  ; CR3 : forall a, SNe a -> S a }.

Hint Constructors CR SN SNRed SNe : rdb.

Module red_props.

  Lemma antirenaming :
          (forall a, SN a -> forall ξ b, a = ren_Tm ξ b -> SN b) /\
          (forall a, SNe a -> forall ξ b, a = ren_Tm ξ b -> SNe b) /\
            (forall a b, SNRed a b -> forall ξ a', a = ren_Tm ξ a' -> exists b', b = ren_Tm ξ b' /\ SNRed a' b').
  Proof.
    apply SN_multind.
    - qauto use:S_Neu.
    - move => a h ih ξ []//.
      qauto use:S_Abs.
    - qauto db:rdb.
    - qauto use:S_Var inv:Tm.
    - move => a b ha iha hb ihb ξ []//.
      qauto db:rdb.
    - move => a0 a1 b ha iha ξ []// a' b' [*]. subst.
      specialize iha with (1 := eq_refl).
      move : iha => [b0 [? ?]]. subst.
      exists (TmApp b0 b'). split => //=.
      by apply S_AppL.
    - move => a b h ih ξ []// []// a' b' [*]. subst.
      specialize ih with (1 := eq_refl).
      exists (subst_Tm (b'…) a').
      split. by asimpl.
      by apply S_AppAbs.
  Qed.

  Lemma ext (a : Tm) i :
    SN (TmApp a (VarTm i)) ->
    SN a.
  Proof.
    move E : (TmApp a (VarTm i)) => v h.
    move : i a E.
    elim : v /h => //=.
    - hauto lq:on inv:SNe use:S_Neu.
    - move => a0 a1 ha0 ha1 ih.
      move => i a ?. subst.
      inversion ha0; subst.
      hauto lq:on inv:SN, SNe ctrs:SN.
      apply S_Abs.
      move : ha1.
      have -> : subst_Tm (VarTm i…) a0 = ren_Tm (i…) a0 by substify; asimpl.
      qauto use:antirenaming.
  Qed.

  Lemma CR_Prod s0 s1 : CR s0 -> CR s1 -> CR (fun b => forall a, s0 a -> s1 (TmApp b a)).
  Proof.
    move=>*.
    apply CR_intro.
    - hauto q:on use:CR1, CR3, S_Var, ext.
    - hauto lq:on ctrs:SNRed inv:CR.
    - hauto lq:on ctrs:SNe inv:CR.
  Qed.

  Lemma CR_SN : CR SN.
  Proof.
    apply CR_intro; eauto with rdb.
  Qed.

  Lemma CR_Forall {A} (x : A) (P : A -> Prop) (_ : P x) F : (forall a : A, P a -> CR (F a)) -> CR (fun b => forall a, P a -> F a b).
  Proof.
    move => hF.
    apply CR_intro; firstorder.
  Qed.

End red_props.
