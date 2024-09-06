Require Export imports.
From stdpp Require Import relations (rtc(..) , sn).

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

Definition isAbs a :=
  match a with
  | TmAbs _ => true
  | _ => false
  end.

Fixpoint nf a :=
  match a with
  | VarTm _ => true
  | TmApp b a => ne b && nf a
  | TmAbs b => nf b
  end
with ne a :=
  match a with
  | VarTm _ => true
  | TmApp b a => ne b && nf a
  | TmAbs _ => false
  end.

Inductive Red : Tm -> Tm -> Prop :=
| R_AppAbs b a  :
  Red (TmApp (TmAbs b) a) (subst_Tm (a…) b)
| R_App0 b0 b1 a :
  ~~ isAbs b0 ->
  Red b0 b1 ->
  Red (TmApp b0 a) (TmApp b1 a)
| R_App1 b a0 a1 :
  ne b ->
  Red a0 a1 ->
  Red (TmApp b a0) (TmApp b a1)
| R_Abs b0 b1 :
  Red b0 b1 ->
  Red (TmAbs b0) (TmAbs b1).

Inductive FRed : Tm -> Tm -> Prop :=
| F_AppAbs b a  :
  FRed (TmApp (TmAbs b) a) (subst_Tm (a…) b)
| F_App0 b0 b1 a :
  FRed b0 b1 ->
  FRed (TmApp b0 a) (TmApp b1 a)
| F_App1 b a0 a1 :
  FRed a0 a1 ->
  FRed (TmApp b a0) (TmApp b a1)
| F_Abs b0 b1 :
  FRed b0 b1 ->
  FRed (TmAbs b0) (TmAbs b1).

Lemma ne_nf : forall a, ne a -> nf a.
Proof.
  elim => //=.
Qed.

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

  Lemma Rs_Abs a0 a1 :
    rtc Red a0 a1 ->
    rtc Red (TmAbs a0) (TmAbs a1).
  Proof.
    induction 1; qauto ctrs:rtc use:R_Abs.
  Qed.

  Lemma Red_IsAbs a0 a1 :
    rtc Red a0 a1 ->
    isAbs a0 -> isAbs a1.
    induction 1 => //=.
    - hauto lq:on inv:Red ctrs:rtc.
  Qed.

  Lemma Rs_App b0 b1 a0 a1 :
    rtc Red b0 b1 ->
    rtc Red a0 a1 ->
    ne b1 ->
    rtc Red (TmApp b0 a0) (TmApp b1 a1).
    move => h. move : a0 a1. elim : b0 b1 /h.
    - move => + a0 a1 h.
      elim : a0 a1 /h; hauto lq:on ctrs:rtc, Red.
    - move => b0 b1 b2 hb hb' ih a0 a1 ha hb2.
      apply rtc_l with (y := (TmApp b1 a0)); eauto.
      apply R_App0; eauto. apply /negP => h.
      have : isAbs b2 by hauto lq:on use:Red_IsAbs ctrs:rtc.
      move : hb2; clear. case : b2 => //=.
  Qed.

  Lemma sn_red :
    (forall a, SN a -> exists b, nf b /\ rtc Red a b) /\
    (forall a, SNe a -> exists b, ne b /\ rtc Red a b) /\
      (forall a b, SNRed a b -> Red a b).
    apply SN_multind.
    - sfirstorder use:ne_nf.
    - sfirstorder use:Rs_Abs.
    - hauto q:on ctrs:rtc.
    - move => i.
      exists (VarTm i).
      eauto using rtc_refl.
    - move => a b ha [a0 ha0] hb [b0 hb0].
      exists (TmApp a0 b0).
      split => /=.
      sfirstorder b:on.
      sfirstorder use:Rs_App.
    - hauto lq:on rew:off inv:SNRed ctrs:Red.
    - qauto use:R_AppAbs.
  Qed.

  Fixpoint redf a : option Tm :=
    match a with
    | VarTm _ => None
    | TmAbs a => match redf a with
                | Some a => Some (TmAbs a)
                | None => None
                end
    | TmApp (TmAbs b) a => Some (subst_Tm (a…) b)
    | TmApp b a => match redf b with
                  | Some b => Some (TmApp b a)
                  | None => match redf a with
                           | Some a => Some (TmApp b a)
                           | None => None
                           end
                  end
    end.

  Lemma nf_ne_red a :
    ne a \/ nf a -> redf a = None.
    elim : a => //=; hauto lqb:on.
  Qed.

  Lemma Red_red a b : Red a b -> redf a = Some b.
  Proof.
    move => h. elim : a b /h.
    - done.
    - hauto lq:on rew:off.
    - hauto lq:on rew:off use:nf_ne_red.
    - hauto lq:on.
  Qed.

  Polymorphic Inductive IsAbs {A : Type} (a : Tm) (b1 : A) (F : Tm -> A) : A -> Tm -> Prop :=
  | IsAbsTrue a0 :  IsAbs a b1 F (F a0) (TmAbs a0)
  | isAbsFalse  : ~~ isAbs a -> IsAbs a b1 F b1 a.

  Polymorphic Lemma IsAbsP {A : Type} a (b1 : A) F :
    let e := match a with
             | TmAbs a => F a
             | _ => b1
             end in
    IsAbs a b1 F e a.
  Proof. hauto lq:on ctrs:IsAbs inv:Tm. Qed.

  Lemma red_FRed a b : redf a = Some b -> FRed a b.
  Proof.
    elim : a b => //=.
    - hauto q:on ctrs:FRed.
    - hauto lq:on rew:off inv:Tm ctrs:FRed.
  Qed.

  Lemma SN_red_sn a : SN a -> sn (fun a b => redf a = Some b) a.
  Proof.
    move => h. apply sn_red in h.
    move : h => [v [hv hr]].
    move : hv.
    elim : a v / hr.
    - hauto q:on ctrs:Acc use:nf_ne_red.
    - move => a b c h0 h1 ih hc.
      apply Acc_intro => /= a'.
      move /Red_red in h0.
      move => ?. have ? : a' = b by congruence. subst.
      by apply ih.
  Qed.

  Definition normalize a : SN a -> {x : Tm | rtc FRed a x}.
    intros h.
    apply SN_red_sn in h.
    induction h as [x h ih].
    destruct (redf x) as [x0 | ] eqn:eq.
    destruct (ih x0 eq) as [x1 h1].
    - exists x1. apply : rtc_l; eauto. apply red_FRed. apply eq.
    - exists x. apply rtc_refl.
  Defined.

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
