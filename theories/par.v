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
  TyPar (TyApp (TyAbs k b0) a0) (subst_Ty (a1…) b1).


Reserved Infix "⇒" (at level 70, no associativity).
Inductive Par : Tm -> Tm -> Prop :=
| P_Var i :
  VarTm i ⇒ VarTm i
| P_Abs a0 a1 :
  a0 ⇒ a1 ->
  (* ------------------- *)
  TmAbs a0 ⇒ TmAbs a1
| P_App a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  TmApp a0 b0 ⇒ TmApp a1 b1
| P_AppAbs a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* ---------------------------------- *)
  TmApp (TmAbs a0) b0 ⇒ subst_Tm (b1…) a1
(* | P_Forall a0 a1 : *)
(*   a0 ⇒ a1 -> *)
(*   (* ------------------------------- *) *)
(*   TmForall a0 ⇒ TmForall a1 *)

where "a ⇒ b" := (Par a b).

#[export]Hint Constructors Par TyPar : par.

Infix "⇒*" := (rtc Par) (at level 70, no associativity).

Inductive RTC  : Ty -> Ty -> Type :=
| RTC_Refl A :
  RTC A A
| RTC_Step A B C :
  TyPar A B ->
  RTC B C ->
  RTC A C.

Definition ICoherent A0 A1 : Type :=
  { B : Ty &  prod (RTC A0 B) (RTC A1 B)}.

Lemma par_refl a : a ⇒ a.
Proof. elim : a; eauto with par. Qed.

Ltac2 binder_map (f : constr -> constr) (b : binder) : binder :=
  Binder.make (Binder.name b) (f (Binder.type b)).

Local Ltac2 map_invert (f : constr -> constr) (iv : case_invert) : case_invert :=
  match iv with
  | NoInvert => NoInvert
  | CaseInvert indices => CaseInvert (Array.map f indices)
  end.

Ltac2 map (f : constr -> constr) (c : constr) : constr :=
  match Unsafe.kind c with
  | Rel _ | Meta _ | Var _ | Sort _ | Constant _ _ | Ind _ _
  | Constructor _ _ | Uint63 _ | Float _  => c
  | Cast c k t =>
      let c := f c
      with t := f t in
      make (Cast c k t)
  | Prod b c =>
      let b := binder_map f b
      with c := f c in
      make (Prod b c)
  | Lambda b c =>
      let b := binder_map f b
      with c := f c in
      make (Lambda b c)
  | LetIn b t c =>
      let b := binder_map f b
      with t := f t
      with c := f c in
      make (LetIn b t c)
  | App c l =>
      let c := f c
      with l := Array.map f l in
      make (App c l)
  | Evar e l =>
      let l := Array.map f l in
      make (Evar e l)
  | Case info x iv y bl =>
      let x := match x with (x,x') => (f x, x') end
      with iv := map_invert f iv
      with y := f y
      with bl := Array.map f bl in
      make (Case info x iv y bl)
  | Proj p r c =>
      let c := f c in
      make (Proj p r c)
  | Fix structs which tl bl =>
      let tl := Array.map (binder_map f) tl
      with bl := Array.map f bl in
      make (Fix structs which tl bl)
  | CoFix which tl bl =>
      let tl := Array.map (binder_map f) tl
      with bl := Array.map f bl in
      make (CoFix which tl bl)
  | Array u t def ty =>
      let ty := f ty
      with t := Array.map f t
      with def := f def in
      make (Array u t def ty)
  end.

Ltac2 par_cong_rel c r :=
  let rec go c :=
    lazy_match! c with
    | Par => r
    | _ => map go c
    end in go (type c).

Ltac revert_all_terms :=
  repeat (progress
            (match goal with
               [_x : Tm |- _] => (revert _x)
             end)).

Ltac2 Notation "gen_cong" x(constr) r(constr) := Control.refine (fun _ => par_cong_rel x r).

Ltac solve_s_rec :=
  move => *; eapply rtc_l; eauto;
         hauto lq:on ctrs:Par use:par_refl.

Ltac solve_pars_cong :=
  repeat (  let x := fresh "x" in
            intros * x;
            revert_all_terms;
            induction x; last by solve_s_rec);
  auto using rtc_refl.

Lemma PS_App : ltac2:(gen_cong P_App (rtc Par)).
Proof. solve_pars_cong. Qed.

Lemma P_AppAbs' a0 a1 b0 b1 u :
  u = subst_Tm (b1…) a1 ->
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* -------------------- *)
  TmApp (TmAbs a0) b0 ⇒ u.
Proof. move =>> ->. apply P_AppAbs. Qed.

Lemma par_renaming a b ξ :
  a ⇒ b ->
  ren_Tm ξ a ⇒ ren_Tm ξ b.
Proof.
  move => h. move : ξ. elim : a b/h => //=; eauto with par.
  (* Abs *)
  - move => *. apply : P_AppAbs'; eauto. by asimpl.
Qed.

Lemma par_ρ_ext a b ρ0 ρ1 :
  a ⇒ b ->
  (forall i, ρ0 i ⇒ ρ1 i) ->
  (forall i, (a .: ρ0) i ⇒ (b .: ρ1) i).
Proof. qauto l:on inv:nat. Qed.

Lemma par_ρ_id ρ :
  forall (i : nat), ρ i ⇒ ρ i.
Proof. eauto using par_refl. Qed.

Lemma par_ρ_up ρ0 ρ1 :
  (forall i, ρ0 i ⇒ ρ1 i) ->
  (forall i, (up_Tm_Tm ρ0) i ⇒ (up_Tm_Tm ρ1) i).
Proof. hauto l:on use:par_renaming, par_ρ_ext, P_Var unfold:up_Tm_Tm. Qed.

Lemma par_morphing a b ρ0 ρ1 :
  (forall i, ρ0 i ⇒ ρ1 i) ->
  a ⇒ b ->
  subst_Tm ρ0 a ⇒ subst_Tm ρ1 b.
Proof.
  move => + h. move : ρ0 ρ1.
  elim : a b /h=>//=; eauto using par_ρ_up with par.
  (* App *)
  - move => *.
    apply : P_AppAbs'; eauto using par_ρ_up. by asimpl.
Qed.

Lemma pars_morphing a b ρ0 ρ1 :
  (forall i, ρ0 i ⇒ ρ1 i) ->
  a ⇒* b ->
  subst_Tm ρ0 a ⇒* subst_Tm ρ1 b.
Proof.
  move => h.
  move => h0.
  elim : a b /h0=>//=;
    eauto using par_morphing, par_refl, rtc_once, rtc_l.
Qed.

Function tstar a :=
  match a with
  | VarTm _ => a
  | TmAbs a => TmAbs (tstar a)
  | TmApp (TmAbs a) b => subst_Tm (tstar b …)(tstar a)
  | TmApp a b => TmApp (tstar a) (tstar b)
  (* | TmForall a => TmForall (tstar a) *)
  end.

Lemma par_cong a0 a1 b0 b1 (h : a0 ⇒ a1) (h1 : b0 ⇒ b1) :
  subst_Tm (b0…) a0 ⇒ subst_Tm (b1…) a1.
Proof. auto using par_morphing, par_ρ_ext, par_ρ_id. Qed.

Local Ltac solve_triangle := qauto use:par_refl, par_cong ctrs:Par inv:Par.

Lemma par_triangle a b : a ⇒ b -> b ⇒ tstar a.
Proof.
  move : b. apply tstar_ind;
    hauto lq:on use:par_refl, par_cong ctrs:Par inv:Par.
Qed.

Lemma par_diamond a b c : a ⇒ b -> a ⇒ c -> b ⇒ tstar a /\ c ⇒ tstar a.
Proof. auto using par_triangle. Qed.

Lemma pars_diamond : confluent Par.
Proof.
  hauto lq:on use:par_diamond, @diamond_confluent unfold:confluent, diamond.
Qed.

Lemma pars_renaming a b ξ :
  a ⇒* b ->
  ren_Tm ξ a ⇒* ren_Tm ξ b.
Proof.
  induction 1; hauto lq:on ctrs:rtc use:par_renaming.
Qed.

Lemma par_subst a b ρ :
  a ⇒ b ->
  subst_Tm ρ a ⇒ subst_Tm ρ b.
Proof.
  auto using par_refl, par_morphing.
Qed.

Lemma pars_subst a b ρ :
  a ⇒* b ->
  subst_Tm ρ a ⇒* subst_Tm ρ b.
Proof.
  induction 1; hauto lq:on ctrs:rtc use:par_subst.
Qed.

Definition Coherent a b := exists c, a ⇒* c /\ b ⇒* c.
Infix "⇔" := Coherent (at level 70, no associativity).


Lemma coherent_renaming a b ξ :
  a ⇔ b ->
  ren_Tm ξ a ⇔ ren_Tm ξ b.
Proof. hauto lq:on use:pars_renaming unfold:Coherent. Qed.

Lemma coherent_subst a b ρ :
  a ⇔ b ->
  subst_Tm ρ a ⇔ subst_Tm ρ b.
Proof. hauto lq:on use:pars_subst unfold:Coherent. Qed.

Lemma coherent_refl : forall a, a ⇔ a.
Proof. hauto lq:on use:rtc_refl unfold:Coherent. Qed.

Lemma coherent_sym : forall a b, a ⇔ b -> b ⇔ a.
Proof. rewrite /Coherent. firstorder. Qed.

Lemma coherent_trans : forall a b c, a ⇔ b -> b ⇔ c -> a ⇔ c.
Proof.
  rewrite /Coherent.
  have h := pars_diamond. rewrite /confluent /diamond in h.
  move => a b c [ab [ha0 hb0]] [bc [ha1 hb1]].
  have [abc [hab hbc]] : exists abc, ab ⇒* abc /\ bc ⇒* abc by firstorder.
  exists abc. eauto using rtc_transitive.
Qed.

Lemma C_App : ltac2:(gen_cong P_App Coherent).
Proof. hauto lq:on use:PS_App unfold:Coherent. Qed.


(* Lemma pars_pi_inv A B U : *)
(*   Pi A B ⇒* U -> exists A0 B0, U = Pi A0 B0 /\ A ⇒* A0 /\ B ⇒* B0. *)
(* Proof. *)
(*   move E : (Pi A B) => T h. *)
(*   move : A B E. *)
(*   elim : T U/h. *)
(*   hauto lq:on ctrs:rtc, Par. *)
(*   hauto lq:on rew:off inv:Par ctrs:Par,rtc. *)
(* Qed. *)

(* Lemma pars_sort_inv s U : *)
(*   ISort s ⇒* U -> U = ISort s. *)
(* Proof. *)
(*   move E : (ISort s) => T h. *)
(*   move : s E. *)
(*   elim : T U/h. *)
(*   hauto lq:on ctrs:rtc, Par. *)
(*   hauto lq:on rew:off inv:Par ctrs:Par,rtc. *)
(* Qed. *)

(* Lemma coherent_pi_inj A0 A1 B0 B1 : *)
(*   Pi A0 B0 ⇔ Pi A1 B1 -> *)
(*   A0 ⇔ A1 /\ *)
(*   B0 ⇔ B1. *)
(* Proof. hauto l:on inv:eq rew:off  ctrs:rtc use:pars_pi_inv unfold:Coherent. Qed. *)

(* Lemma coherent_sort_inj s0 s1 : *)
(*   ISort s0 ⇔ ISort s1 -> *)
(*   s0 = s1. *)
(* Proof. *)
(*   move => [u][/pars_sort_inv h0 /pars_sort_inv h1]. *)
(*   congruence. *)
(* Qed. *)

(* Based on https://poplmark-reloaded.github.io/coq/well-scoped/PR.sn_defs.html *)
(* Inductive SN : Term -> Prop := *)
(* | S_Neu a : SNe a -> SN a *)
(* | S_Abs A a : SN A -> SN a -> SN (Abs A a) *)
(* | S_Sort s : SN (ISort s) *)
(* | S_Pi A B : SN A -> SN B -> SN (Pi A B) *)
(* | S_Red a0 a1 : SNRed a0 a1 -> SN a1 -> SN a0 *)
(* with SNe : Term -> Prop := *)
(* | S_Var i : SNe (VarTm i) *)
(* | S_App a b : SNe a -> SN b -> SNe (App a b) *)
(* with SNRed : Term -> Term -> Prop := *)
(* | S_AppL a0 a1 b : *)
(*   SNRed a0 a1 -> *)
(*   SNRed (App a0 b) (App a1 b) *)
(* | S_AppAbs A a b : *)
(*   SN A -> *)
(*   SN b -> *)
(*   SNRed (App (Abs A a) b) a[b…]. *)

(* Scheme SN_ind_2 := Minimality for SN Sort Prop *)
(*                    with SNe_ind_2 := Minimality for SNe Sort Prop *)
(*                     with redSN_ind_2 := Minimality for SNRed Sort Prop. *)
(* Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2. *)
