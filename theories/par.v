Require Export imports.

Reserved Infix "⇒" (at level 70, no associativity).
Inductive Par : Term -> Term -> Prop :=
| P_Var i :
  VarTm i ⇒ VarTm i
| P_Sort s :
  ISort s ⇒ ISort s
| P_Abs A0 A1 a0 a1 :
  A0 ⇒ A1 ->
  a0 ⇒ a1 ->
  (* ------------------- *)
  Abs A0 a0 ⇒ Abs A1 a1
| P_Pi A0 A1 B0 B1 :
  A0 ⇒ A1 ->
  B0 ⇒ B1 ->
  (* ------------------- *)
  Pi A0 B0 ⇒ Pi A1 B1
| P_App a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  App a0 b0 ⇒ App a1 b1
| P_AppAbs A a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* -------------------- *)
  App (Abs A a0) b0 ⇒ a1[b1…]

where "a ⇒ b" := (Par a b).

#[export]Hint Constructors Par : par.

Infix "⇒*" := (rtc Par) (at level 70, no associativity).

Lemma par_refl a : a ⇒ a.
Proof. elim : a; eauto with par. Qed.

Lemma P_AppAbs' A a0 a1 b0 b1 u :
  u = a1[b1…] ->
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* -------------------- *)
  App (Abs A a0) b0 ⇒ u.
Proof. move =>> ->. apply P_AppAbs. Qed.

Lemma par_renaming a b ξ :
  a ⇒ b ->
  a⟨ξ⟩ ⇒ b⟨ξ⟩.
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
  (forall i, (up_Term_Term ρ0) i ⇒ (up_Term_Term ρ1) i).
Proof. hauto l:on use:par_renaming, par_ρ_ext, P_Var unfold:up_Term_Term. Qed.

Lemma par_morphing a b ρ0 ρ1 :
  (forall i, ρ0 i ⇒ ρ1 i) ->
  a ⇒ b ->
  a[ρ0] ⇒ b[ρ1].
Proof.
  move => + h. move : ρ0 ρ1.
  elim : a b /h=>//=; eauto using par_ρ_up with par.
  (* App *)
  - move => *.
    apply : P_AppAbs'; eauto using par_ρ_up. by asimpl.
Qed.

Function tstar a :=
  match a with
  | ISort _ => a
  | VarTm _ => a
  | Abs A a => Abs (tstar A) (tstar a)
  | Pi A B => Pi (tstar A) (tstar B)
  | App (Abs A a) b => (tstar a)[tstar b …]
  | App a b => App (tstar a) (tstar b)
  end.

Lemma par_cong a0 a1 b0 b1 (h : a0 ⇒ a1) (h1 : b0 ⇒ b1) :
  a0 [b0…] ⇒ a1 [b1…].
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
  a⟨ξ⟩ ⇒* b⟨ξ⟩.
Proof.
  induction 1; hauto lq:on ctrs:rtc use:par_renaming.
Qed.

Lemma par_subst a b ρ :
  a ⇒ b ->
  a[ρ] ⇒ b[ρ].
Proof.
  auto using par_refl, par_morphing.
Qed.

Lemma pars_subst a b ρ :
  a ⇒* b ->
  a[ρ] ⇒* b[ρ].
Proof.
  induction 1; hauto lq:on ctrs:rtc use:par_subst.
Qed.

Definition Coherent a b := exists c, a ⇒* c /\ b ⇒* c.
Infix "⇔" := Coherent (at level 70, no associativity).

Lemma coherent_renaming a b ξ :
  a ⇔ b ->
  a⟨ξ⟩ ⇔ b⟨ξ⟩.
Proof. hauto lq:on use:pars_renaming unfold:Coherent. Qed.

Lemma coherent_subst a b ρ :
  a ⇔ b ->
  a[ρ] ⇔ b[ρ].
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

(* Based on https://poplmark-reloaded.github.io/coq/well-scoped/PR.sn_defs.html *)
Inductive SN : Term -> Prop :=
| S_Neu a : SNe a -> SN a
| S_Abs A a : SN A -> SN a -> SN (Abs A a)
| S_Sort s : SN (ISort s)
| S_Pi A B : SN A -> SN B -> SN (Pi A B)
| S_Red a0 a1 : SNRed a0 a1 -> SN a1 -> SN a0
with SNe : Term -> Prop :=
| S_Var i : SNe (VarTm i)
| S_App a b : SNe a -> SN b -> SNe (App a b)
with SNRed : Term -> Term -> Prop :=
| S_AppL a0 a1 b :
  SNRed a0 a1 ->
  SNRed (App a0 b) (App a1 b)
| S_AppAbs A a b :
  SN A ->
  SN b ->
  SNRed (App (Abs A a) b) a[b…].

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2 := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.
