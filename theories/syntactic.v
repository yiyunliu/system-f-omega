Require Export typing.

Lemma Here' : forall A Γ T, T = A ⟨shift⟩ ->  Lookup 0 (A :: Γ) T.
Proof. move => > ->. by apply Here. Qed.

Lemma There' : forall n A Γ B T, T = A ⟨shift⟩ ->
    Lookup n Γ A -> Lookup (S n) (B :: Γ) T.
Proof. move => > ->. by apply There. Qed.

Lemma T_App' Γ a b A B u :
  u = B[a…] ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ Pi A B ->
  (* --------------- *)
  Γ ⊢ App b a ∈ u.
Proof. move => ->. apply T_App. Qed.

Definition ξ_ok ξ Γ Δ := forall i A, Lookup i Γ A -> Lookup (ξ i) Δ A⟨ξ⟩.

Lemma ξ_ok_id Γ : ξ_ok ids Γ Γ.
Proof.
  rewrite /ξ_ok. by asimpl.
Qed.

Lemma ξ_ok_up ξ Γ Δ A :
  ξ_ok ξ Γ Δ -> ξ_ok (upRen_Term_Term ξ) (A::Γ) (A⟨ξ⟩::Δ).
Proof.
  rewrite /ξ_ok => h.
  inversion 1; subst.
  - apply LookupIff=>//=. by asimpl.
  - apply : There'; last by eauto. by asimpl.
Qed.

Lemma renaming Γ a A (h : Γ ⊢ a ∈ A) :
  forall ξ Δ, ⊢ Δ -> ξ_ok ξ Γ Δ -> Δ ⊢ a⟨ξ⟩ ∈ A⟨ξ⟩.
Proof.
  elim : Γ a A /h.
  - qauto use:T_Var unfold:ξ_ok.
  - auto using T_Star.
  - hauto q:on use:T_Abs, Wf_Cons use:ξ_ok_up.
  - move => * /=.
    apply : T_App'; eauto.
    rewrite -/ren_Term. by asimpl.
  - hauto q:on use:T_Pi, Wf_Cons use:ξ_ok_up.
  - hauto l:on use:T_Conv use:coherent_renaming.
Qed.

Lemma renaming_sort
  Γ A s (h : Γ ⊢ A ∈ ISort s) : forall Δ ξ,
    ξ_ok ξ Γ Δ ->
    ⊢ Δ ->  Δ ⊢ A⟨ξ⟩  ∈ ISort s.
Proof. qauto use:renaming. Qed.

Lemma wt_wf Γ a A (h : Γ ⊢ a ∈ A) : ⊢ Γ.
Proof. elim : Γ a A / h => //. Qed.

#[export]Hint Resolve wt_wf : wf.
#[export]Hint Constructors Wf : wf.

Lemma weakening Γ a A B s
  (h0 : Γ ⊢ B ∈ ISort s)
  (h1 : Γ ⊢ a  ∈ A) :
  (B :: Γ) ⊢ a ⟨S⟩ ∈ A ⟨S⟩.
Proof.
  apply : renaming; eauto with wf.
  hauto lq:on ctrs:Lookup unfold:ξ_ok.
Qed.

Lemma weakening_sort Γ a B s s0
  (h0 : Γ ⊢ B ∈ ISort s)
  (h1 : Γ ⊢ a  ∈ ISort s0) :
  (B :: Γ) ⊢ a ⟨S⟩ ∈ ISort s0.
Proof.
  change (ISort s0) with (ISort s0) ⟨ S ⟩.
  eauto using weakening.
Qed.

Definition ρ_ok ρ Γ Δ :=
  forall i A, Lookup i Γ A -> Δ ⊢ ρ i ∈ A [ ρ ].

Lemma ρ_ok_id Γ : ⊢ Γ -> ρ_ok ids Γ Γ.
Proof. hauto l:on use:T_Var unfold:ρ_ok simp+:asimpl. Qed.

Lemma ρ_ext ρ Γ Δ a A :
  Δ ⊢ a ∈ A[ρ] ->
  ρ_ok ρ Γ Δ ->
  ρ_ok (a.:ρ) (A::Γ) Δ.
Proof.
  hauto q:on inv:Lookup, Wf unfold:ρ_ok db:wf simp+:asimpl.
Qed.

Lemma ρ_ξ_comp ρ ξ Γ Δ Ξ
  (hρ : ρ_ok ρ Γ Δ)
  (hξ : ξ_ok ξ Δ Ξ)
  (hΞ : ⊢ Ξ) :
  ρ_ok (ρ >> ren_Term ξ) Γ Ξ.
Proof.
  move => i A hA.
  suff : Ξ ⊢ (ρ i)⟨ξ⟩ ∈ A[ρ]⟨ξ⟩ by asimpl.
  rewrite /ρ_ok /ξ_ok.
  eauto using renaming.
Qed.

Lemma ρ_suc ρ Γ Δ A s
  (h : ρ_ok ρ Γ Δ) (hA : Δ ⊢ A ∈ ISort s) :
  ρ_ok (ρ >> ren_Term S) Γ (A :: Δ).
Proof.
  apply : ρ_ξ_comp; eauto with wf.
  rewrite /ξ_ok.
  hauto lq:on ctrs:Lookup.
Qed.

Lemma ρ_up ρ Γ Δ A s :
  ρ_ok ρ Γ Δ ->
  Δ ⊢ A[ρ] ∈ ISort s ->
  ρ_ok (up_Term ρ) (A :: Γ) (A[ρ] :: Δ).
Proof.
  move => hρ hA.
  apply ρ_ext.
  apply : T_Var; eauto with wf.
  apply LookupIff=>//=. by asimpl.
  eauto using ρ_suc.
Qed.

Lemma morphing Γ a A (h : Γ ⊢ a ∈ A) : forall Δ ρ,
    ρ_ok ρ Γ Δ ->
    ⊢ Δ ->
    Δ ⊢ a[ρ] ∈ A[ρ].
Proof.
  elim : Γ a A /h.
  - qauto use:T_Var unfold:ρ_ok.
  - qauto use:T_Star.
  - hauto q:on use:ρ_up, T_Abs db:wf.
  - move => *.
    apply : T_App'; eauto. rewrite -/subst_Term. by asimpl.
  - hauto q:on use:ρ_up, T_Pi db:wf.
  - hauto q:on use:coherent_subst, T_Conv.
Qed.

Lemma wt_subst Γ a A b B
  (h : Γ ⊢ a ∈ A )
  (h0 : A :: Γ ⊢ b ∈ B) :
  Γ ⊢ b[a…] ∈ B[a…].
Proof.
  apply : morphing; eauto with wf.
  apply ρ_ext. by asimpl.
  apply ρ_ok_id; eauto with wf.
Qed.

Lemma wt_subst_sort Γ a A b s
  (h : Γ ⊢ a ∈ A )
  (h0 : A :: Γ ⊢ b ∈ ISort s) :
  Γ ⊢ b[a…] ∈ ISort s.
Proof.
  change (ISort s) with (ISort s)[a…].
  eauto using wt_subst.
Qed.

Definition inv_spec Γ a A : Prop :=
  match a with
  | ISort Kind => False
  | ISort Star => ISort Kind ⇔ A
  | VarTm i => exists A0, Lookup i Γ A0 /\ A0 ⇔ A
  | Abs A0 a => exists B s1 s2, Γ ⊢ A0 ∈ ISort s1 /\ A0 :: Γ ⊢ a ∈ B /\ A0 :: Γ ⊢ B ∈ ISort s2 /\ Pi A0 B ⇔ A
  | App b a => exists A0 B, Γ ⊢ b ∈ Pi A0 B /\ Γ ⊢ a ∈ A0 /\ B[a…] ⇔ A
  | Pi A0 B => exists s1 s2, Γ ⊢ A0 ∈ ISort s1 /\ A0::Γ ⊢ B ∈ ISort s2 /\ ISort s2 ⇔ A
  end.

Lemma inv_spec_conv Γ a A B : inv_spec Γ a A -> A ⇔ B -> inv_spec Γ a B.
Proof.
  case : a => //=; hauto lq:on rew:off use:coherent_trans.
Qed.

Lemma wt_inv Γ a A (h : Γ ⊢ a ∈ A) : inv_spec Γ a A.
Proof.
  elim : Γ a A /h=>//=; eauto 10 using coherent_refl, inv_spec_conv.
Qed.

Lemma kind_imp Γ A :
  ~ Γ ⊢ ISort Kind ∈ A.
Proof. firstorder using wt_inv. Qed.

Lemma wt_unique Γ t T U :
  Γ ⊢ t ∈ T ->
  Γ ⊢ t ∈ U ->
  T ⇔ U.
Proof.
  move => h. move : U.
  elim : Γ t T /h.
  - move => Γ i A hΓ hi U /wt_inv //=.
    move => [A0][hA0]?.
    suff : A = A0 by congruence.
    eauto using lookup_functional.
  - qauto use:wt_inv.
  - move => Γ A s1 a B s2 hA ihA ha iha hB ihB U /wt_inv/=.
    move => [B0][s3][s4][hA'][ha'][hB0]hU.
    eauto using C_Pi, coherent_refl, coherent_trans.
  - move => Γ a b A B ha iha hb ihb U /wt_inv/=.
    move => [A0][B0][?][?]?.
    apply : coherent_trans; eauto.
    apply coherent_subst.
    hauto lq:on use:coherent_pi_inj.
  - move => Γ A s1 B s2 hA ihA hB ihB U /wt_inv/=.
    move => [s3][s4][hA0][hB0]h.
    suff : ISort s2 ⇔ ISort s4 by eauto using coherent_trans.
    firstorder.
  - eauto using coherent_trans, coherent_sym.
Qed.

Lemma wf_lookup i Γ A : Lookup i Γ A -> ⊢ Γ -> exists s, Γ ⊢ A ∈ ISort s.
Proof.
  induction 1.
  - hauto lq:on inv:Wf use:weakening_sort.
  - inversion 1; subst.
    hauto lq:on use:weakening_sort db:wf.
Qed.

Lemma regularity Γ a A  (h : Γ ⊢ a ∈ A) :
  (exists s, Γ ⊢ A ∈ ISort s) \/ (A = ISort Kind).
Proof.
  elim : Γ a A /h.
  - firstorder using wf_lookup.
  - tauto.
  - qauto use:T_Pi.
  - move => Γ a b A B ha iha hb ihb.
    case : ihb => //=.
    move => [s]/wt_inv/=.
    move => [s1][s2][hA][hB]/coherent_sort_inj ?. subst.
    eauto using wt_subst_sort.
  - move => Γ A s1 B s2 hA ihA hB ihB.
    case : ihB; last by tauto.
    move => [s hs].
    left.
    move /wt_inv : hs => /=.
    case  : {hB} s2 => //= h.
    eauto using T_Star with wf.
  - qauto use:coherent_sort_inj.
Qed.
