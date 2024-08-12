Require Export typing par syntactic.

Inductive D :=
| D_Sort : Sort -> D
| D_Prod : D -> D -> D
| D_Ne : DNe -> D
| D_Set : (Term -> Prop) -> D
| D_Clos : (nat -> D) -> Term -> D
with DNe :=
| DN_Var : nat -> DNe
| DN_App : DNe -> D -> DNe.

Inductive Eval_D : (nat -> D) -> Term -> D -> Prop :=
| E_Var ρ i :
  Eval_D ρ (VarTm i) (ρ i)

| E_Sort ρ s :
  Eval_D ρ (ISort s) (D_Sort s)

| E_App ρ a b d0 d1 d :
  Eval_D ρ a d0 ->
  Eval_D ρ b d1 ->
  Ap_D d0 d1 d ->
  Eval_D ρ (App a b) d

| E_Pi ρ A B d0  :
  Eval_D ρ A d0 ->
  Eval_D ρ (Pi A B) (D_Prod d0 (D_Clos ρ B))

with Ap_D : D -> D -> D -> Prop :=
| Ap_Clos ρ a d d0 :
  Eval_D (d .: ρ) a d0 ->
  Ap_D (D_Clos ρ a) d d0

| Ap_Ne d0 d1 :
  Ap_D (D_Ne d0) d1 (D_Ne (DN_App d0 d1)).

Definition is_dset d :=
  match d with
  | D_Set _ => true
  | _ => false
  end.

Inductive V_D : D -> (D -> Prop) -> Prop :=
| V_Sort s :
  V_D (D_Sort s) is_dset

| V_Ne e :
  V_D (D_Ne e) (fun d => d = D_Set SN)

| V_Prod D0 D1 D1' (P0 P1 : D -> Prop) :
  V_D D0 P0 ->
  (forall d, Ap_D D1 d D1') ->
  V_D D1' P1 ->
  V_D (D_Prod D0 D1) (fun d1 => forall d0, P0 d0 -> exists d, Ap_D d1 d0 d /\ P1 d).

Definition InterSpace (P0 : D -> Prop) (ID : D -> (Term -> Prop) -> Prop) a: Prop :=
  forall d S, P0 d -> ID d S -> S a.

Definition ProdSpace (S0 S1 : Term -> Prop) b := forall a, S0 a -> S1 (App b a).

Inductive I_D : D -> (Term -> Prop) -> Prop :=
| I_Sort s :
  I_D (D_Sort s) SN

| I_Ne e :
  I_D (D_Ne e) SN

| I_Prod D0 D1 S0 P0 I_D1 :
  I_D D0 S0 ->
  V_D D0 P0 ->
  (forall d0, P0 d0 -> exists S, I_D d0 S) ->
  (forall d0 d1 S, Ap_D D1 d0 d1 -> I_D1 d0 S -> I_D d1 S) ->
  (* -------------------------------------------- *)
  I_D (D_Prod D0 D1) (ProdSpace S0 (InterSpace P0 I_D1)).

Definition V_Term A ρ P :=
  exists D, Eval_D ρ A D /\ V_D D P.

Definition I_Term A ρ S :=
  exists D, Eval_D ρ A D /\ I_D D S.

Definition ρξ_ok ρ ξ Γ :=
  forall i A S,
    Lookup i Γ A ->
    I_Term A[ξ] ρ S ->
    S (ξ i).

Definition SemWt Γ a A :=
  forall ρ ξ, ρξ_ok ρ ξ Γ ->
           exists S, I_Term A[ξ] ρ S /\ S a[ξ].

Lemma soundness Γ a A : Wt Γ a A -> SemWt Γ a A.
Proof.
  move => h.
  elim : Γ a A /h.
  - admit.
  - move => Γ hΓ.
    rewrite /SemWt.
    move => ρ ξ hρξ.
    simpl.
    sauto lq:on.
  - move => Γ A s1 a B s2 hA ihA ha iha hB ihB.
    rewrite /SemWt /I_Term in ihB.
    simpl in ihB.
    rewrite /SemWt.
    rewrite /SemWt in ihA.
    simpl.
    move => ρ ξ /[dup] hρ.
    move /ihA.

Admitted.


Inductive Skel : Set :=
| SK_Unit : Skel
| SK_Star : Skel
| SK_Arr : Skel -> Skel -> Skel.

Fixpoint kind_int A :=
  match A with
  | ISort _ => SK_Star
  | Pi A B =>
      match kind_int B with
      | SK_Unit => SK_Unit
      | _ => SK_Arr (kind_int A) (kind_int B)
      end
  | _ => SK_Unit
  end.

Fixpoint infer_sig ρ A :=
  match A with
  | VarTm i => ρ i
  | Abs A a => SK_Arr (kind_int A) (infer_sig (kind_int A .: ρ) a)
  | App b a => match infer_sig ρ b with
              | SK_Arr _ sk => sk
              | _ => SK_Unit
              end
  | Pi A B => SK_Star
  | ISort _ => SK_Star
  end.

Fixpoint skel_int a : Type :=
  match a with
  | SK_Unit => unit
  | SK_Star => Term -> Prop
  | SK_Arr S0 S1 =>
      skel_int S0 -> skel_int S1
  end.

Fixpoint default_int (s : Skel) : skel_int s :=
  match s as s return (skel_int s) with
  | SK_Unit => tt
  | SK_Star => SN
  | SK_Arr s1 s2 => fun _ => default_int s2
  end.

Scheme Equality for Skel.

Definition ProdSpace (S0 S1 : Term -> Prop) b : Prop := forall a, S0 a -> S1 (App b a).
(* TODO: define cand *)
Definition InterSpace {A : Type} (S : A -> (Term -> Prop)) (b : Term) : Prop := forall a, S a b.

Definition ρξ_lookup (ρ : nat -> Skel) (ξ : forall i, skel_int (ρ i))
  (i : nat) (sk : Skel) : skel_int sk.
  pose (ξ i) as r.
  destruct (Skel_eq_dec (ρ i) sk).
  - rewrite <- e. apply r.
  - apply default_int.
Defined.

Definition ξ_ext (ρ : nat -> Skel) (ξ : forall i, skel_int (ρ i))
  (sk : Skel) (r : skel_int sk) :
  (forall i, skel_int ((sk .: ρ) i)).
  destruct i as [|i].
  apply r.
  apply ξ.
Defined.

Fixpoint int_type_with_sig (ρ : nat -> Skel) (ξ : forall i, skel_int (ρ i))
  (sk : Skel) (A : Term) : skel_int sk :=
      match A with
      | VarTm i => ρξ_lookup ρ ξ i sk
      | ISort _ => default_int sk
      | Abs A a => match sk as s return (skel_int s) with
                  | SK_Arr sk0 sk1 =>
                      fun (v : skel_int sk0) =>
                        int_type_with_sig (sk0 .: ρ) (ξ_ext ρ ξ sk0 v) sk1 a
                  | SK_Unit => tt
                  | SK_Star => default_int SK_Star
                  end
      | App b a => let sk0 := infer_sig ρ a in
                    int_type_with_sig ρ ξ (SK_Arr sk0 sk) b
                      (int_type_with_sig ρ ξ sk0 a)
      | Pi A B => match sk as s return (skel_int s) with
                 | SK_Star =>
                     ProdSpace (int_type_with_sig ρ ξ SK_Star A)

                       (InterSpace (fun (v : skel_int (kind_int A)) =>
                                      int_type_with_sig (kind_int A .: ρ)
                                        (ξ_ext ρ ξ _ v) SK_Star B))
                 | SK_Unit => tt
                 | SK_Arr sk0 sk1 => default_int (SK_Arr sk0 sk1)
                 end
      end.

Fixpoint b2s Γ :=
  match Γ with
  | nil => fun _ => SK_Unit
  | A :: Γ => kind_int A .: b2s Γ
  end.

Inductive kind_case Γ U : Prop :=
| S_Sort : U = ISort Star -> kind_case Γ U
| S_PiTm A B : U = Pi A B -> Γ ⊢ A ∈ ISort Star ->
               A :: Γ ⊢ B ∈ ISort Kind -> kind_case Γ U
| S_PiKd A B : U = Pi A B -> Γ ⊢ A ∈ ISort Kind ->
               A :: Γ ⊢ B ∈ ISort Kind -> kind_case Γ U.

#[export]Hint Constructors kind_case : kcase.

Lemma app_kind_imp Γ b a :
  ~ Γ ⊢ App b a ∈ ISort Kind.
Proof.
  move /wt_inv => //=.
  move => [A0][B][hb][ha]he.
  move /regularity : hb => []//=.
  move => [s]/wt_inv => //=.
  move => [s1][s2][hA0][hB]hc.
  have ? : s2 = s by eauto using coherent'_forget, coherent_sort_inj. subst.
  have {}hB: Γ ⊢ B[a…] ∈ ISort s by sfirstorder use:wt_subst_sort.
  inversion he; subst;
  hauto q:on use:kind_imp.
Qed.

Lemma kind_caseP Γ U : Γ ⊢ U ∈ ISort Kind -> kind_case Γ U.
Proof.
  move E : (ISort Kind) => T h.
  move : E. case : Γ U T/h.
  - hauto lq:on use:wf_lookup, kind_imp, T_Var.
  - eauto using S_Sort.
  - congruence.
  - move => Γ a b A B ha hb h.
    have : Γ ⊢ App b a ∈ B[a…] by eauto using T_App.
    rewrite -h.
    by move /app_kind_imp.
  - move => Γ A s1 B s2 hA  hB [?]. subst.
    case : s1 hA; eauto with kcase.
  - qauto using kind_imp.
Qed.

Lemma kind_sort : kind_int (ISort Star) = SK_Star.
Proof. done. Qed.

Lemma kind_int_typ Γ A :
  Γ ⊢ A ∈ ISort Star ->
  kind_int A = SK_Unit.
Proof.
  elim : A Γ => //=.
  - case => //=;
    move => Γ /wt_inv //=.
    hauto q:on use:coherent'_forget, coherent_sort_inj.
  - move => A ihA B ihB Γ.
    move /wt_inv => //=.
    move => [s1[s2 [hA [hB hE]]]].
    case : s2 hB hE => //=.
    + hauto q:on use:coherent'_forget, coherent_sort_inj.
    + hauto lq:on.
Qed.

Lemma kind_has_interp Γ A :
  Γ ⊢ A ∈ ISort Kind ->
  kind_int A <> SK_Unit.
Proof.
  elim : A Γ =>//=; hauto q:on inv:kind_case use:kind_caseP.
Qed.

Lemma kind_pi_tm Γ Δ A B :
  Δ ⊢ B ∈ ISort Kind ->
  Γ ⊢ A ∈ ISort Star -> kind_int (Pi A B) = SK_Arr SK_Unit (kind_int B).
Proof.
  hauto lq:on rew:off use:kind_has_interp, kind_int_typ.
Qed.

Lemma kind_pi_kind Γ Δ A B :
  Δ ⊢ B ∈ ISort Kind ->
  Γ ⊢ A ∈ ISort Kind -> kind_int (Pi A B) = SK_Arr (kind_int A) (kind_int B).
Proof. hauto q:on use:kind_has_interp. Qed.

Lemma kind_int_renaming A ξ :
  kind_int A = kind_int A ⟨ξ⟩.
Proof.
  elim : A ξ => //=; qauto l:on.
Qed.

Lemma lookup_kind_int i Γ A : Lookup i Γ A -> kind_int A = b2s Γ i.
Proof.
  move => h.
  elim : i Γ A /h=>//=.
  - eauto using kind_int_renaming.
  - move => n Γ A _ hn <-.
    eauto using kind_int_renaming.
Qed.

Derive Inversion kcase_inv with (forall Γ A, kind_case Γ A).
Derive Inversion par_inv with (forall A B, A ⇒ B).

Lemma kind_int_morphing A Γ Δ ρ :
  ⊢ Δ ->
  ρ_ok ρ Γ Δ ->
  Γ ⊢ A ∈ ISort Kind ->
  kind_int A = kind_int A[ρ].
Proof.
  elim : A Γ Δ ρ => //.
  - hauto q:on use:kind_caseP inv:kind_case.
  - move => A ihA B ihB Γ Δ ρ hΔ hρ.
    move /kind_caseP.
    elim /kcase_inv => //_.
    + move => A0 B0 [*]. subst.
      rewrite [kind_int]lock /= -lock.
      have ? : Δ ⊢ A0[ρ] ∈ ISort Star by eauto using morphing_sort.
      have ? : ⊢ A0[ρ]::Δ by eauto with wf.
      have ? : ρ_ok (up_Term_Term ρ) (A0::Γ) (A0[ρ]::Δ) by hauto l:on use:ρ_up.
      qauto l:on use:kind_pi_tm.
    + move => A0 B0 [*]. subst.
      rewrite [kind_int]lock /= -lock.
      have ? : Δ ⊢ A0[ρ] ∈ ISort Kind by eauto using morphing_sort.
      have ? : ⊢ A0[ρ]::Δ by eauto with wf.
      have ? : ρ_ok (up_Term_Term ρ) (A0::Γ) (A0[ρ]::Δ) by hauto l:on use:ρ_up.
      have ? :  A0[ρ]::Δ ⊢ B0 [up_Term_Term ρ] ∈ ISort Kind by eauto using morphing_sort.
      hauto lq:on use:kind_pi_kind.
Qed.

Lemma kind_int_subst Γ a A B :
  ⊢ Γ ->
  A::Γ ⊢ B ∈ ISort Kind ->
  Γ ⊢ a ∈ A ->
  kind_int B = kind_int B[a…].
Proof.
  move => hΓ hB ha.
  apply : kind_int_morphing; eauto.
  apply ρ_ext. by asimpl.
  by apply ρ_ok_id.
Qed.

Lemma kind_int_preservation Γ a b :
  Γ ⊢ a ∈ ISort Kind  -> a ⇒ b ->
  kind_int a = kind_int b.
Proof.
  elim : a Γ b.
  - hauto q:on inv:kind_case use:kind_caseP.
  - hauto q:on inv:kind_case, Par use:kind_caseP.
  - hauto q:on inv:kind_case use:kind_caseP.
  - hauto q:on inv:kind_case use:kind_caseP.
  - move => A ihA B ihB Γ T /kind_caseP.
    elim /kcase_inv=>//_.
    + move => A0 B0 [? ?] hA0 hB0. subst.
      elim/par_inv => //_.
      move => A1 A2 B1 B2 h0 h1 [*]. subst.
      have ? : Γ ⊢ A2 ∈ ISort Star by eauto using subject_reduction.
      have ? : (A0::Γ) ⊢ B2 ∈ ISort Kind by eauto using subject_reduction.
      do 2 (erewrite kind_pi_tm; eauto).
      qauto.
    + move => A0 B0 [? ?] hA0 hB0.
      elim /par_inv=>//_.
      move => A1 A2 B1 B2 h0 h1 [*]. subst.
      have ? : Γ ⊢ A2 ∈ ISort Kind by eauto using subject_reduction.
      have ? : (A0::Γ) ⊢ B2 ∈ ISort Kind by eauto using subject_reduction.
      do 2 (erewrite kind_pi_kind; eauto).
      qauto.
Qed.

Lemma kind_int_preservation_star Γ a b :
  Γ ⊢ a ∈ ISort Kind  -> a ⇒* b ->
  kind_int a = kind_int b.
Proof.
  move => + h.
  elim : a b / h => //=.
  - hauto lq:on ctrs:rtc use:subject_reduction, kind_int_preservation.
Qed.

Lemma kind_int_coherent Γ a b :
  Γ ⊢ a ∈ ISort Kind ->
  Γ ⊢ b ∈ ISort Kind ->
  a ⇔ b ->
  kind_int a = kind_int b.
Proof.
  rewrite /Coherent.
  hauto lq:on use:kind_int_preservation_star.
Qed.

Lemma coherent_term Γ a A b B :
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ B ->
  Coherent a b -> Coherent A B.
Proof.
  qauto l:on use:subject_reduction_star, wt_unique.
Qed.

Lemma coherent_sort Γ B s A' B' :
  Γ ⊢ B ∈ ISort s ->
  Coherent B B' ->
  Γ ⊢ A' ∈  B' ->
  Γ ⊢ B' ∈ ISort s.
Proof.
  move => hB /coherent_sym hT /regularity.
  case.
  - move => [s0 hB'].
    have /coherent_sort_inj ? : Coherent (ISort s) (ISort s0) by hauto lq:on use:coherent_term.
    by subst.
  - move => ?. subst.
    rewrite /Coherent in hT.
    move : hT => [c]?.
    have ? : c = ISort Kind by qauto use:pars_sort_inv. subst.
    qauto use:subject_reduction_star.
Qed.

Lemma infer_sig_sound Γ a A (h : Γ ⊢ a ∈ A) :
  Γ ⊢ A ∈ ISort Kind ->
  infer_sig (b2s Γ) a = kind_int A.
Proof.
  elim : a Γ A h => //=.
  - move => n Γ A /wt_inv /=.
    move => [A0 [hA0 hE]] hA.
    suff : kind_int A = kind_int A0 by qauto use:lookup_kind_int.
    have ? : ⊢ Γ by eauto with wf.
    have [s hA1]  : exists s, Γ ⊢ A0 ∈ ISort s by qauto use:wf_lookup.
    have : Coherent (ISort Kind) (ISort s) by hauto q:on use:coherent_term, coherent'_forget.
    move /coherent_sort_inj => ?. subst.
    hauto q:on use: kind_int_coherent, coherent'_forget.
  - move => s Γ A /wt_inv //=.
    case : s => //=.
    move /coherent'_forget => [c] ?.
    have ? : c = ISort Kind  by qauto use:pars_sort_inv. subst.
    hauto lq:on use:subject_reduction_star, kind_imp.
  - move => a iha b ihb Γ A ha hA.
    rewrite [kind_int]lock.
    move /wt_inv : ha => //.
    move => [B][s1][s2][ha0][hb0][hB]hE.
    move /kind_caseP : hA => //.
    elim /kcase_inv => //_.
    (* consistency *)
    + hauto lq:on use:coherent'_forget, pars_pi_inv, pars_sort_inv.
    + move => A0 B0 ?. subst.
      move => hA0 hB0.
      rewrite -lock.
      erewrite kind_pi_tm; eauto.
      move /coherent'_forget in hE.
      have [? ?] : Coherent  a A0 /\ Coherent B B0 by hauto l:on use:coherent_pi_inj.
      f_equal.
      * have ? : s1 = Star by hauto lq:on rew:off use:coherent_term, coherent_sort_inj. subst.
        eauto using kind_int_typ.
      * move /(_ (a :: Γ) B0) in ihb.
        rewrite ihb=>//.
        ** apply : context_equiv; eauto.
           apply : T_Conv; eauto.
           apply : context_equiv; eauto using coherent_sym.
        ** apply : coherent_sort; eauto.
           have ? : a :: Γ ⊢ B0 ∈ ISort Kind by hauto l:on use:context_equiv.
           have ? : s2 = Kind by hauto lq:on rew:off use:coherent_term, coherent_sort_inj. subst.
           exact.
           apply : T_Conv. apply hb0.
           apply : context_equiv; eauto.
           exact.
    + move => A0 B0 ?. subst.
      rewrite -lock.
      have [? ?] : Coherent  a A0 /\ Coherent B B0 by hauto l:on use:coherent_pi_inj, coherent'_forget.
      move => hA0 hB0.
      have ? : s1 =  Kind by hauto lq:on rew:off use:coherent_term, coherent_sort_inj. subst.
      have ? : a :: Γ ⊢ B0 ∈ ISort Kind by hauto l:on use:context_equiv.
      have ? : s2 =  Kind by hauto lq:on rew:off use:coherent_term, coherent_sort_inj. subst.
      erewrite kind_pi_kind; eauto.
      move => [:ha].
      f_equal.
      abstract : ha.
      hauto l:on use:kind_int_coherent.
      hauto q:on use:kind_int_coherent.
  - move => b ihb a iha Γ A hba hA.
    move /wt_inv : hba => //=.
    move => [A0][B][hb][ha]hE.
    have h : Γ ⊢ Pi A0 B ∈ ISort Kind.

    move /regularity : hb.
    case => //=.
    move => [s hP].
    move /wt_inv : (hP) => //=.
    move => [s1][s2][?][hB0]?.
    have ? : s2 = s by qauto use:coherent_sort_inj, coherent'_forget. subst.
    have : Γ ⊢ B[a…] ∈ ISort s by eauto using wt_subst_sort.
    move => h.
    have ? : s = Kind by
      hauto lq:on rew:off use:coherent_term, coherent'_forget, coherent_sym, coherent_sort_inj. subst.
    done.

    move : ihb (h)(hb); repeat move /[apply].
    move => ->/=.
    suff : kind_int B = kind_int A by qauto l:on use:kind_has_interp.
    move /wt_inv : h=>//=.
    move => [s1][s2][hA0][hB]hE'.
    have ? : s2 = Kind by qauto use:coherent'_forget, coherent_sort_inj. subst.
    have ? : Γ ⊢ B[a…] ∈ ISort Kind by eauto using wt_subst_sort.
    have ? : kind_int B[a…] = kind_int A by qauto use:coherent'_forget, kind_int_coherent.
    transitivity (kind_int B[a…])=>//.
    apply : kind_int_subst; eauto.
    eauto with wf.
  - move => A ihA B ihB Γ U hA hU.
    move /wt_inv : hA => //=.
    move => [s1][s2][hA][hB]/coherent'_forget hE.
    move /kind_caseP : hU.
    elim /kcase_inv=> _ *; subst.
    + done.
    + hauto l:on use:pars_pi_inv, pars_sort_inv unfold:Coherent.
    + hauto l:on use:pars_pi_inv, pars_sort_inv unfold:Coherent.
Qed.

(* Definition ρ_ok_kind (ρ : nat ->  {A : Skel & skel_int A}) Γ := *)
(*   forall i (A : Term), Lookup i Γ A -> exists Sk S, kind_int A = Sk /\ ρ i = (existT Sk S). *)

(* Fixpoint type_int (Γ : Basis) *)
(*   (ρ : nat -> option {A : Skel & skel_int A}) (a : Term): *)
(*   option {A : Skel & skel_int A}. *)
(*   refine ( *)
(*       match a with *)
(*       | ISort s => Some (existT SK_Star SN) *)
(*       | VarTm i => ρ i *)
(*       | App a b => *)
(*           match type_int Γ ρ a, type_int Γ ρ b with *)
(*           | Some (existT sk1 S1), Some (existT sk2 S2) => _ *)
(*           | r, _ => r *)
(*           end *)
(*       | Abs A a => *)
(*           match kind_int A with *)
(*           | Some sk => *)

(*           | None => _ *)
(*           end *)
(*       | _ => _ *)
(*       end *)
(*     ). *)

Inductive type_interp (Γ : Basis) (ρ : nat -> option {A : Skel & skel_int A}) : Term -> forall (A : Skel), skel_int A -> Prop :=
| TI_Star s :
  type_interp Γ ρ (ISort s) SK_Star SN

| TI_Var i Sk1 S :
  Some (existT Sk1 S) = ρ i ->
  type_interp Γ ρ (VarTm i) Sk1 S

| TI_App P Q Sk1 Sk2 S1 S2 F :
  type_interp Γ ρ P (SK_Arr Sk1 Sk2) F ->
  type_interp Γ ρ Q Sk1 S1 ->
  F S1 S2 ->
  (* -------------------- *)
  type_interp Γ ρ (App P Q) Sk2 S2

| TI_AppTm Sk P t A S  :
  type_interp Γ ρ P Sk S ->
  Γ ⊢ t ∈ A ->
  Γ ⊢ A ∈ ISort Star ->
  (* ------------------------------- *)
  type_interp Γ ρ (App P t) Sk S

| TI_Abs A B Sk1 Sk2 PF :
  kind_int A = Some Sk1 ->
  (forall a, exists S, PF a S) ->
  (forall a S, PF a S -> type_interp (A::Γ) (Some (existT Sk1 a) .: ρ) B  Sk2 S) ->
  (* ------------------------------ *)
  type_interp Γ ρ (Abs A B) (SK_Arr Sk1 Sk2) PF

| TI_AbsTm A B Sk S :
  kind_int A = None ->
  type_interp (A::Γ) (None .: ρ) B Sk S ->
  (* ------------------------------------ *)
  type_interp Γ ρ (Abs A B) Sk S

| TI_Pi A B S1 S2:
  kind_int A = None ->
  type_interp Γ ρ A SK_Star S1 ->
  type_interp (A::Γ) (None .: ρ) B SK_Star S2 ->
  (* ------------------------------------------------------------- *)
  type_interp Γ ρ (Pi A B) SK_Star (ProdSpace S1 S2)

| TI_PiKind A Sk B S PF :
  kind_int A = Some Sk ->
  type_interp Γ ρ A SK_Star S  ->
  (forall a, exists S, PF a S) ->
  (forall a S, PF a S -> type_interp (A::Γ) (Some (existT Sk a) .: ρ) B SK_Star S) ->
  type_interp Γ ρ (Pi A B) SK_Star (ProdSpace S (InterSpace PF)).


Lemma kind_has_interp Γ A :
  Γ ⊢ A ∈ ISort Kind -> exists V, kind_interp Γ A V.
Proof.
  move E : (ISort Kind) => U h.
  move : E.
  elim : Γ A U /h=>//=.
  - hauto lq:on use: wf_lookup, kind_imp.
  - eauto using KI_Star.
  - move => Γ a b A B ha _ hb _ E.
    have : Γ ⊢ App b a ∈ B[a…] by  eauto using T_App.
    case /regularity : hb=>//.
    move => [s]/wt_inv /=.
    move => [s1][s2]hA.
    have ? : s2 = s by hauto l:on use:coherent_sort_inj. subst.
    have : Γ ⊢ B[a…] ∈ ISort s by firstorder using wt_subst_sort.
    rewrite -E.
    firstorder using kind_imp.
  - move => Γ A s1 B s2 hA ihA hB ihB [?]. subst.
    specialize ihB with (1 := eq_refl).
    case : s1 hA ihA; hauto lq:on ctrs:kind_interp.
  - (* Impossible *)
    move => Γ a A B s ha iha hB ihB heq ?. subst.
    firstorder using kind_imp.
Qed.

Lemma kind_interp_not_star Γ A S :
  kind_interp Γ A S ->
  ~ Γ ⊢ A ∈ ISort Star.
Proof.
  move => h. elim : Γ A S /h.
  - hauto l:on use:wt_inv, coherent_sort_inj.
  - hauto lq:on rew:off use:wt_inv, coherent_sort_inj.
  - hauto lq:on rew:off use:wt_inv, coherent_sort_inj.
Qed.

Lemma kind_interp_functionality Γ A S0 S1 :
  kind_interp Γ A S0 -> kind_interp Γ A S1 -> S0 = S1.
Proof.
  move => h. move : S1. elim : Γ A S0 / h.
  - hauto lq:on inv:kind_interp.
  - move => Γ A B SA0 SB0 hA ihA hB ihB S.
    inversion 1; subst.
    sfirstorder.
    firstorder using kind_interp_not_star.
  - move => Γ A B S hA ihA hB S0.
    inversion 1.
    by firstorder using kind_interp_not_star.
    sfirstorder.
Qed.

Lemma type_has_interp Γ A T Sk:
  Γ ⊢ A ∈ T -> kind_interp Γ T Sk ->
  forall ρ, ρ_ok_kind ρ Γ -> forall Sk0 S, type_interp Γ ρ A Sk0 S -> Sk = Sk0.
Proof.
  move => + + ρ + Sk0 S h.
  move : Sk T.
  elim : Γ ρ A Sk0 S /h.
  - move => Γ ρ s Sk T /wt_inv_sort.
    move => [? ?]. subst.
    inversion 1.
  - move => Γ ρ i sk S hi sk0 T hA hT hρ.
    rewrite /ρ_ok_kind in hρ.
    move /wt_inv : hA => /=.
    move => [A0][hA0 ?].
    move : hρ hA0 => /[apply].
    move => [sk1]/=[S0][h0 h1].
    rewrite h1 in hi.
    case : hi => ?.
    move => h. subst.
    admit.
  - move => Γ ρ P Q Sk1 Sk2 S1 S2.
    rewrite -/interp_skel in S2 *.
    best.
