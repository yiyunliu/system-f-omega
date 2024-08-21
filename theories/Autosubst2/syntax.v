Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive CSort : Type :=
  | CStar : CSort
  | CKind : CSort.

Lemma congr_CStar : CStar = CStar.
Proof.
exact (eq_refl).
Qed.

Lemma congr_CKind : CKind = CKind.
Proof.
exact (eq_refl).
Qed.

Inductive CTm : Type :=
  | VarCTm : nat -> CTm
  | CTmAbs : CTm -> CTm
  | CTmApp : CTm -> CTm -> CTm
  | CTmForall : CTm -> CTm -> CTm
  | CTmSort : CSort -> CTm.

Lemma congr_CTmAbs {s0 : CTm} {t0 : CTm} (H0 : s0 = t0) :
  CTmAbs s0 = CTmAbs t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => CTmAbs x) H0)).
Qed.

Lemma congr_CTmApp {s0 : CTm} {s1 : CTm} {t0 : CTm} {t1 : CTm} (H0 : s0 = t0)
  (H1 : s1 = t1) : CTmApp s0 s1 = CTmApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => CTmApp x s1) H0))
         (ap (fun x => CTmApp t0 x) H1)).
Qed.

Lemma congr_CTmForall {s0 : CTm} {s1 : CTm} {t0 : CTm} {t1 : CTm}
  (H0 : s0 = t0) (H1 : s1 = t1) : CTmForall s0 s1 = CTmForall t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => CTmForall x s1) H0))
         (ap (fun x => CTmForall t0 x) H1)).
Qed.

Lemma congr_CTmSort {s0 : CSort} {t0 : CSort} (H0 : s0 = t0) :
  CTmSort s0 = CTmSort t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => CTmSort x) H0)).
Qed.

Lemma upRen_CTm_CTm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_CTm (xi_CTm : nat -> nat) (s : CTm) {struct s} : CTm :=
  match s with
  | VarCTm s0 => VarCTm (xi_CTm s0)
  | CTmAbs s0 => CTmAbs (ren_CTm (upRen_CTm_CTm xi_CTm) s0)
  | CTmApp s0 s1 => CTmApp (ren_CTm xi_CTm s0) (ren_CTm xi_CTm s1)
  | CTmForall s0 s1 =>
      CTmForall (ren_CTm xi_CTm s0) (ren_CTm (upRen_CTm_CTm xi_CTm) s1)
  | CTmSort s0 => CTmSort s0
  end.

Lemma up_CTm_CTm (sigma : nat -> CTm) : nat -> CTm.
Proof.
exact (scons (VarCTm var_zero) (funcomp (ren_CTm shift) sigma)).
Defined.

Fixpoint subst_CTm (sigma_CTm : nat -> CTm) (s : CTm) {struct s} : CTm :=
  match s with
  | VarCTm s0 => sigma_CTm s0
  | CTmAbs s0 => CTmAbs (subst_CTm (up_CTm_CTm sigma_CTm) s0)
  | CTmApp s0 s1 => CTmApp (subst_CTm sigma_CTm s0) (subst_CTm sigma_CTm s1)
  | CTmForall s0 s1 =>
      CTmForall (subst_CTm sigma_CTm s0)
        (subst_CTm (up_CTm_CTm sigma_CTm) s1)
  | CTmSort s0 => CTmSort s0
  end.

Lemma upId_CTm_CTm (sigma : nat -> CTm) (Eq : forall x, sigma x = VarCTm x) :
  forall x, up_CTm_CTm sigma x = VarCTm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_CTm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_CTm (sigma_CTm : nat -> CTm)
(Eq_CTm : forall x, sigma_CTm x = VarCTm x) (s : CTm) {struct s} :
subst_CTm sigma_CTm s = s :=
  match s with
  | VarCTm s0 => Eq_CTm s0
  | CTmAbs s0 =>
      congr_CTmAbs
        (idSubst_CTm (up_CTm_CTm sigma_CTm) (upId_CTm_CTm _ Eq_CTm) s0)
  | CTmApp s0 s1 =>
      congr_CTmApp (idSubst_CTm sigma_CTm Eq_CTm s0)
        (idSubst_CTm sigma_CTm Eq_CTm s1)
  | CTmForall s0 s1 =>
      congr_CTmForall (idSubst_CTm sigma_CTm Eq_CTm s0)
        (idSubst_CTm (up_CTm_CTm sigma_CTm) (upId_CTm_CTm _ Eq_CTm) s1)
  | CTmSort s0 => congr_CTmSort (eq_refl s0)
  end.

Lemma upExtRen_CTm_CTm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_CTm_CTm xi x = upRen_CTm_CTm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_CTm (xi_CTm : nat -> nat) (zeta_CTm : nat -> nat)
(Eq_CTm : forall x, xi_CTm x = zeta_CTm x) (s : CTm) {struct s} :
ren_CTm xi_CTm s = ren_CTm zeta_CTm s :=
  match s with
  | VarCTm s0 => ap (VarCTm) (Eq_CTm s0)
  | CTmAbs s0 =>
      congr_CTmAbs
        (extRen_CTm (upRen_CTm_CTm xi_CTm) (upRen_CTm_CTm zeta_CTm)
           (upExtRen_CTm_CTm _ _ Eq_CTm) s0)
  | CTmApp s0 s1 =>
      congr_CTmApp (extRen_CTm xi_CTm zeta_CTm Eq_CTm s0)
        (extRen_CTm xi_CTm zeta_CTm Eq_CTm s1)
  | CTmForall s0 s1 =>
      congr_CTmForall (extRen_CTm xi_CTm zeta_CTm Eq_CTm s0)
        (extRen_CTm (upRen_CTm_CTm xi_CTm) (upRen_CTm_CTm zeta_CTm)
           (upExtRen_CTm_CTm _ _ Eq_CTm) s1)
  | CTmSort s0 => congr_CTmSort (eq_refl s0)
  end.

Lemma upExt_CTm_CTm (sigma : nat -> CTm) (tau : nat -> CTm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_CTm_CTm sigma x = up_CTm_CTm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_CTm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_CTm (sigma_CTm : nat -> CTm) (tau_CTm : nat -> CTm)
(Eq_CTm : forall x, sigma_CTm x = tau_CTm x) (s : CTm) {struct s} :
subst_CTm sigma_CTm s = subst_CTm tau_CTm s :=
  match s with
  | VarCTm s0 => Eq_CTm s0
  | CTmAbs s0 =>
      congr_CTmAbs
        (ext_CTm (up_CTm_CTm sigma_CTm) (up_CTm_CTm tau_CTm)
           (upExt_CTm_CTm _ _ Eq_CTm) s0)
  | CTmApp s0 s1 =>
      congr_CTmApp (ext_CTm sigma_CTm tau_CTm Eq_CTm s0)
        (ext_CTm sigma_CTm tau_CTm Eq_CTm s1)
  | CTmForall s0 s1 =>
      congr_CTmForall (ext_CTm sigma_CTm tau_CTm Eq_CTm s0)
        (ext_CTm (up_CTm_CTm sigma_CTm) (up_CTm_CTm tau_CTm)
           (upExt_CTm_CTm _ _ Eq_CTm) s1)
  | CTmSort s0 => congr_CTmSort (eq_refl s0)
  end.

Lemma up_ren_ren_CTm_CTm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_CTm_CTm zeta) (upRen_CTm_CTm xi) x = upRen_CTm_CTm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_CTm (xi_CTm : nat -> nat) (zeta_CTm : nat -> nat)
(rho_CTm : nat -> nat)
(Eq_CTm : forall x, funcomp zeta_CTm xi_CTm x = rho_CTm x) (s : CTm) {struct
 s} : ren_CTm zeta_CTm (ren_CTm xi_CTm s) = ren_CTm rho_CTm s :=
  match s with
  | VarCTm s0 => ap (VarCTm) (Eq_CTm s0)
  | CTmAbs s0 =>
      congr_CTmAbs
        (compRenRen_CTm (upRen_CTm_CTm xi_CTm) (upRen_CTm_CTm zeta_CTm)
           (upRen_CTm_CTm rho_CTm) (up_ren_ren _ _ _ Eq_CTm) s0)
  | CTmApp s0 s1 =>
      congr_CTmApp (compRenRen_CTm xi_CTm zeta_CTm rho_CTm Eq_CTm s0)
        (compRenRen_CTm xi_CTm zeta_CTm rho_CTm Eq_CTm s1)
  | CTmForall s0 s1 =>
      congr_CTmForall (compRenRen_CTm xi_CTm zeta_CTm rho_CTm Eq_CTm s0)
        (compRenRen_CTm (upRen_CTm_CTm xi_CTm) (upRen_CTm_CTm zeta_CTm)
           (upRen_CTm_CTm rho_CTm) (up_ren_ren _ _ _ Eq_CTm) s1)
  | CTmSort s0 => congr_CTmSort (eq_refl s0)
  end.

Lemma up_ren_subst_CTm_CTm (xi : nat -> nat) (tau : nat -> CTm)
  (theta : nat -> CTm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_CTm_CTm tau) (upRen_CTm_CTm xi) x = up_CTm_CTm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_CTm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_CTm (xi_CTm : nat -> nat) (tau_CTm : nat -> CTm)
(theta_CTm : nat -> CTm)
(Eq_CTm : forall x, funcomp tau_CTm xi_CTm x = theta_CTm x) (s : CTm) {struct
 s} : subst_CTm tau_CTm (ren_CTm xi_CTm s) = subst_CTm theta_CTm s :=
  match s with
  | VarCTm s0 => Eq_CTm s0
  | CTmAbs s0 =>
      congr_CTmAbs
        (compRenSubst_CTm (upRen_CTm_CTm xi_CTm) (up_CTm_CTm tau_CTm)
           (up_CTm_CTm theta_CTm) (up_ren_subst_CTm_CTm _ _ _ Eq_CTm) s0)
  | CTmApp s0 s1 =>
      congr_CTmApp (compRenSubst_CTm xi_CTm tau_CTm theta_CTm Eq_CTm s0)
        (compRenSubst_CTm xi_CTm tau_CTm theta_CTm Eq_CTm s1)
  | CTmForall s0 s1 =>
      congr_CTmForall (compRenSubst_CTm xi_CTm tau_CTm theta_CTm Eq_CTm s0)
        (compRenSubst_CTm (upRen_CTm_CTm xi_CTm) (up_CTm_CTm tau_CTm)
           (up_CTm_CTm theta_CTm) (up_ren_subst_CTm_CTm _ _ _ Eq_CTm) s1)
  | CTmSort s0 => congr_CTmSort (eq_refl s0)
  end.

Lemma up_subst_ren_CTm_CTm (sigma : nat -> CTm) (zeta_CTm : nat -> nat)
  (theta : nat -> CTm)
  (Eq : forall x, funcomp (ren_CTm zeta_CTm) sigma x = theta x) :
  forall x,
  funcomp (ren_CTm (upRen_CTm_CTm zeta_CTm)) (up_CTm_CTm sigma) x =
  up_CTm_CTm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_CTm shift (upRen_CTm_CTm zeta_CTm)
                (funcomp shift zeta_CTm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_CTm zeta_CTm shift (funcomp shift zeta_CTm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_CTm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_CTm (sigma_CTm : nat -> CTm) (zeta_CTm : nat -> nat)
(theta_CTm : nat -> CTm)
(Eq_CTm : forall x, funcomp (ren_CTm zeta_CTm) sigma_CTm x = theta_CTm x)
(s : CTm) {struct s} :
ren_CTm zeta_CTm (subst_CTm sigma_CTm s) = subst_CTm theta_CTm s :=
  match s with
  | VarCTm s0 => Eq_CTm s0
  | CTmAbs s0 =>
      congr_CTmAbs
        (compSubstRen_CTm (up_CTm_CTm sigma_CTm) (upRen_CTm_CTm zeta_CTm)
           (up_CTm_CTm theta_CTm) (up_subst_ren_CTm_CTm _ _ _ Eq_CTm) s0)
  | CTmApp s0 s1 =>
      congr_CTmApp (compSubstRen_CTm sigma_CTm zeta_CTm theta_CTm Eq_CTm s0)
        (compSubstRen_CTm sigma_CTm zeta_CTm theta_CTm Eq_CTm s1)
  | CTmForall s0 s1 =>
      congr_CTmForall
        (compSubstRen_CTm sigma_CTm zeta_CTm theta_CTm Eq_CTm s0)
        (compSubstRen_CTm (up_CTm_CTm sigma_CTm) (upRen_CTm_CTm zeta_CTm)
           (up_CTm_CTm theta_CTm) (up_subst_ren_CTm_CTm _ _ _ Eq_CTm) s1)
  | CTmSort s0 => congr_CTmSort (eq_refl s0)
  end.

Lemma up_subst_subst_CTm_CTm (sigma : nat -> CTm) (tau_CTm : nat -> CTm)
  (theta : nat -> CTm)
  (Eq : forall x, funcomp (subst_CTm tau_CTm) sigma x = theta x) :
  forall x,
  funcomp (subst_CTm (up_CTm_CTm tau_CTm)) (up_CTm_CTm sigma) x =
  up_CTm_CTm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_CTm shift (up_CTm_CTm tau_CTm)
                (funcomp (up_CTm_CTm tau_CTm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_CTm tau_CTm shift
                      (funcomp (ren_CTm shift) tau_CTm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_CTm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_CTm (sigma_CTm : nat -> CTm) (tau_CTm : nat -> CTm)
(theta_CTm : nat -> CTm)
(Eq_CTm : forall x, funcomp (subst_CTm tau_CTm) sigma_CTm x = theta_CTm x)
(s : CTm) {struct s} :
subst_CTm tau_CTm (subst_CTm sigma_CTm s) = subst_CTm theta_CTm s :=
  match s with
  | VarCTm s0 => Eq_CTm s0
  | CTmAbs s0 =>
      congr_CTmAbs
        (compSubstSubst_CTm (up_CTm_CTm sigma_CTm) (up_CTm_CTm tau_CTm)
           (up_CTm_CTm theta_CTm) (up_subst_subst_CTm_CTm _ _ _ Eq_CTm) s0)
  | CTmApp s0 s1 =>
      congr_CTmApp (compSubstSubst_CTm sigma_CTm tau_CTm theta_CTm Eq_CTm s0)
        (compSubstSubst_CTm sigma_CTm tau_CTm theta_CTm Eq_CTm s1)
  | CTmForall s0 s1 =>
      congr_CTmForall
        (compSubstSubst_CTm sigma_CTm tau_CTm theta_CTm Eq_CTm s0)
        (compSubstSubst_CTm (up_CTm_CTm sigma_CTm) (up_CTm_CTm tau_CTm)
           (up_CTm_CTm theta_CTm) (up_subst_subst_CTm_CTm _ _ _ Eq_CTm) s1)
  | CTmSort s0 => congr_CTmSort (eq_refl s0)
  end.

Lemma renRen_CTm (xi_CTm : nat -> nat) (zeta_CTm : nat -> nat) (s : CTm) :
  ren_CTm zeta_CTm (ren_CTm xi_CTm s) = ren_CTm (funcomp zeta_CTm xi_CTm) s.
Proof.
exact (compRenRen_CTm xi_CTm zeta_CTm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_CTm_pointwise (xi_CTm : nat -> nat) (zeta_CTm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_CTm zeta_CTm) (ren_CTm xi_CTm))
    (ren_CTm (funcomp zeta_CTm xi_CTm)).
Proof.
exact (fun s => compRenRen_CTm xi_CTm zeta_CTm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_CTm (xi_CTm : nat -> nat) (tau_CTm : nat -> CTm) (s : CTm) :
  subst_CTm tau_CTm (ren_CTm xi_CTm s) = subst_CTm (funcomp tau_CTm xi_CTm) s.
Proof.
exact (compRenSubst_CTm xi_CTm tau_CTm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_CTm_pointwise (xi_CTm : nat -> nat) (tau_CTm : nat -> CTm) :
  pointwise_relation _ eq (funcomp (subst_CTm tau_CTm) (ren_CTm xi_CTm))
    (subst_CTm (funcomp tau_CTm xi_CTm)).
Proof.
exact (fun s => compRenSubst_CTm xi_CTm tau_CTm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_CTm (sigma_CTm : nat -> CTm) (zeta_CTm : nat -> nat) (s : CTm)
  :
  ren_CTm zeta_CTm (subst_CTm sigma_CTm s) =
  subst_CTm (funcomp (ren_CTm zeta_CTm) sigma_CTm) s.
Proof.
exact (compSubstRen_CTm sigma_CTm zeta_CTm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_CTm_pointwise (sigma_CTm : nat -> CTm) (zeta_CTm : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_CTm zeta_CTm) (subst_CTm sigma_CTm))
    (subst_CTm (funcomp (ren_CTm zeta_CTm) sigma_CTm)).
Proof.
exact (fun s => compSubstRen_CTm sigma_CTm zeta_CTm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_CTm (sigma_CTm : nat -> CTm) (tau_CTm : nat -> CTm)
  (s : CTm) :
  subst_CTm tau_CTm (subst_CTm sigma_CTm s) =
  subst_CTm (funcomp (subst_CTm tau_CTm) sigma_CTm) s.
Proof.
exact (compSubstSubst_CTm sigma_CTm tau_CTm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_CTm_pointwise (sigma_CTm : nat -> CTm)
  (tau_CTm : nat -> CTm) :
  pointwise_relation _ eq (funcomp (subst_CTm tau_CTm) (subst_CTm sigma_CTm))
    (subst_CTm (funcomp (subst_CTm tau_CTm) sigma_CTm)).
Proof.
exact (fun s => compSubstSubst_CTm sigma_CTm tau_CTm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_CTm_CTm (xi : nat -> nat) (sigma : nat -> CTm)
  (Eq : forall x, funcomp (VarCTm) xi x = sigma x) :
  forall x, funcomp (VarCTm) (upRen_CTm_CTm xi) x = up_CTm_CTm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_CTm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_CTm (xi_CTm : nat -> nat) (sigma_CTm : nat -> CTm)
(Eq_CTm : forall x, funcomp (VarCTm) xi_CTm x = sigma_CTm x) (s : CTm)
{struct s} : ren_CTm xi_CTm s = subst_CTm sigma_CTm s :=
  match s with
  | VarCTm s0 => Eq_CTm s0
  | CTmAbs s0 =>
      congr_CTmAbs
        (rinst_inst_CTm (upRen_CTm_CTm xi_CTm) (up_CTm_CTm sigma_CTm)
           (rinstInst_up_CTm_CTm _ _ Eq_CTm) s0)
  | CTmApp s0 s1 =>
      congr_CTmApp (rinst_inst_CTm xi_CTm sigma_CTm Eq_CTm s0)
        (rinst_inst_CTm xi_CTm sigma_CTm Eq_CTm s1)
  | CTmForall s0 s1 =>
      congr_CTmForall (rinst_inst_CTm xi_CTm sigma_CTm Eq_CTm s0)
        (rinst_inst_CTm (upRen_CTm_CTm xi_CTm) (up_CTm_CTm sigma_CTm)
           (rinstInst_up_CTm_CTm _ _ Eq_CTm) s1)
  | CTmSort s0 => congr_CTmSort (eq_refl s0)
  end.

Lemma rinstInst'_CTm (xi_CTm : nat -> nat) (s : CTm) :
  ren_CTm xi_CTm s = subst_CTm (funcomp (VarCTm) xi_CTm) s.
Proof.
exact (rinst_inst_CTm xi_CTm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_CTm_pointwise (xi_CTm : nat -> nat) :
  pointwise_relation _ eq (ren_CTm xi_CTm)
    (subst_CTm (funcomp (VarCTm) xi_CTm)).
Proof.
exact (fun s => rinst_inst_CTm xi_CTm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_CTm (s : CTm) : subst_CTm (VarCTm) s = s.
Proof.
exact (idSubst_CTm (VarCTm) (fun n => eq_refl) s).
Qed.

Lemma instId'_CTm_pointwise : pointwise_relation _ eq (subst_CTm (VarCTm)) id.
Proof.
exact (fun s => idSubst_CTm (VarCTm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_CTm (s : CTm) : ren_CTm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_CTm s) (rinstInst'_CTm id s)).
Qed.

Lemma rinstId'_CTm_pointwise : pointwise_relation _ eq (@ren_CTm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_CTm s) (rinstInst'_CTm id s)).
Qed.

Lemma varL'_CTm (sigma_CTm : nat -> CTm) (x : nat) :
  subst_CTm sigma_CTm (VarCTm x) = sigma_CTm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_CTm_pointwise (sigma_CTm : nat -> CTm) :
  pointwise_relation _ eq (funcomp (subst_CTm sigma_CTm) (VarCTm)) sigma_CTm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_CTm (xi_CTm : nat -> nat) (x : nat) :
  ren_CTm xi_CTm (VarCTm x) = VarCTm (xi_CTm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_CTm_pointwise (xi_CTm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_CTm xi_CTm) (VarCTm))
    (funcomp (VarCTm) xi_CTm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive Ki : Type :=
  | Star : Ki
  | Arr : Ki -> Ki -> Ki.

Lemma congr_Star : Star = Star.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Arr {s0 : Ki} {s1 : Ki} {t0 : Ki} {t1 : Ki} (H0 : s0 = t0)
  (H1 : s1 = t1) : Arr s0 s1 = Arr t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Arr x s1) H0))
         (ap (fun x => Arr t0 x) H1)).
Qed.

Inductive Tm : Type :=
  | VarTm : nat -> Tm
  | TmAbs : Tm -> Tm
  | TmApp : Tm -> Tm -> Tm.

Lemma congr_TmAbs {s0 : Tm} {t0 : Tm} (H0 : s0 = t0) : TmAbs s0 = TmAbs t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => TmAbs x) H0)).
Qed.

Lemma congr_TmApp {s0 : Tm} {s1 : Tm} {t0 : Tm} {t1 : Tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : TmApp s0 s1 = TmApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TmApp x s1) H0))
         (ap (fun x => TmApp t0 x) H1)).
Qed.

Lemma upRen_Tm_Tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_Tm (xi_Tm : nat -> nat) (s : Tm) {struct s} : Tm :=
  match s with
  | VarTm s0 => VarTm (xi_Tm s0)
  | TmAbs s0 => TmAbs (ren_Tm (upRen_Tm_Tm xi_Tm) s0)
  | TmApp s0 s1 => TmApp (ren_Tm xi_Tm s0) (ren_Tm xi_Tm s1)
  end.

Lemma up_Tm_Tm (sigma : nat -> Tm) : nat -> Tm.
Proof.
exact (scons (VarTm var_zero) (funcomp (ren_Tm shift) sigma)).
Defined.

Fixpoint subst_Tm (sigma_Tm : nat -> Tm) (s : Tm) {struct s} : Tm :=
  match s with
  | VarTm s0 => sigma_Tm s0
  | TmAbs s0 => TmAbs (subst_Tm (up_Tm_Tm sigma_Tm) s0)
  | TmApp s0 s1 => TmApp (subst_Tm sigma_Tm s0) (subst_Tm sigma_Tm s1)
  end.

Lemma upId_Tm_Tm (sigma : nat -> Tm) (Eq : forall x, sigma x = VarTm x) :
  forall x, up_Tm_Tm sigma x = VarTm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_Tm (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = VarTm x) (s : Tm) {struct s} :
subst_Tm sigma_Tm s = s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | TmAbs s0 =>
      congr_TmAbs (idSubst_Tm (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s0)
  | TmApp s0 s1 =>
      congr_TmApp (idSubst_Tm sigma_Tm Eq_Tm s0)
        (idSubst_Tm sigma_Tm Eq_Tm s1)
  end.

Lemma upExtRen_Tm_Tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Tm_Tm xi x = upRen_Tm_Tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat)
(Eq_Tm : forall x, xi_Tm x = zeta_Tm x) (s : Tm) {struct s} :
ren_Tm xi_Tm s = ren_Tm zeta_Tm s :=
  match s with
  | VarTm s0 => ap (VarTm) (Eq_Tm s0)
  | TmAbs s0 =>
      congr_TmAbs
        (extRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upExtRen_Tm_Tm _ _ Eq_Tm) s0)
  | TmApp s0 s1 =>
      congr_TmApp (extRen_Tm xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  end.

Lemma upExt_Tm_Tm (sigma : nat -> Tm) (tau : nat -> Tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_Tm_Tm sigma x = up_Tm_Tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : Tm) {struct s} :
subst_Tm sigma_Tm s = subst_Tm tau_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | TmAbs s0 =>
      congr_TmAbs
        (ext_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s0)
  | TmApp s0 s1 =>
      congr_TmApp (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  end.

Lemma up_ren_ren_Tm_Tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_Tm_Tm zeta) (upRen_Tm_Tm xi) x = upRen_Tm_Tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat)
(rho_Tm : nat -> nat) (Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x)
(s : Tm) {struct s} : ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm rho_Tm s :=
  match s with
  | VarTm s0 => ap (VarTm) (Eq_Tm s0)
  | TmAbs s0 =>
      congr_TmAbs
        (compRenRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upRen_Tm_Tm rho_Tm) (up_ren_ren _ _ _ Eq_Tm) s0)
  | TmApp s0 s1 =>
      congr_TmApp (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  end.

Lemma up_ren_subst_Tm_Tm (xi : nat -> nat) (tau : nat -> Tm)
  (theta : nat -> Tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_Tm_Tm tau) (upRen_Tm_Tm xi) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_Tm (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Tm) {struct s} :
subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | TmAbs s0 =>
      congr_TmAbs
        (compRenSubst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_ren_subst_Tm_Tm _ _ _ Eq_Tm) s0)
  | TmApp s0 s1 =>
      congr_TmApp (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  end.

Lemma up_subst_ren_Tm_Tm (sigma : nat -> Tm) (zeta_Tm : nat -> nat)
  (theta : nat -> Tm)
  (Eq : forall x, funcomp (ren_Tm zeta_Tm) sigma x = theta x) :
  forall x,
  funcomp (ren_Tm (upRen_Tm_Tm zeta_Tm)) (up_Tm_Tm sigma) x =
  up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_Tm shift (upRen_Tm_Tm zeta_Tm)
                (funcomp shift zeta_Tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_Tm zeta_Tm shift (funcomp shift zeta_Tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_Tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_Tm (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x) 
(s : Tm) {struct s} :
ren_Tm zeta_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | TmAbs s0 =>
      congr_TmAbs
        (compSubstRen_Tm (up_Tm_Tm sigma_Tm) (upRen_Tm_Tm zeta_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_ren_Tm_Tm _ _ _ Eq_Tm) s0)
  | TmApp s0 s1 =>
      congr_TmApp (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  end.

Lemma up_subst_subst_Tm_Tm (sigma : nat -> Tm) (tau_Tm : nat -> Tm)
  (theta : nat -> Tm)
  (Eq : forall x, funcomp (subst_Tm tau_Tm) sigma x = theta x) :
  forall x,
  funcomp (subst_Tm (up_Tm_Tm tau_Tm)) (up_Tm_Tm sigma) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_Tm shift (up_Tm_Tm tau_Tm)
                (funcomp (up_Tm_Tm tau_Tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_Tm tau_Tm shift
                      (funcomp (ren_Tm shift) tau_Tm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_Tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Tm) {struct s} :
subst_Tm tau_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | TmAbs s0 =>
      congr_TmAbs
        (compSubstSubst_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s0)
  | TmApp s0 s1 =>
      congr_TmApp (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  end.

Lemma renRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat) (s : Tm) :
  ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Tm_pointwise (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (ren_Tm xi_Tm))
    (ren_Tm (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm) (s : Tm) :
  subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm_pointwise (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (ren_Tm xi_Tm))
    (subst_Tm (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat) (s : Tm) :
  ren_Tm zeta_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm_pointwise (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) (s : Tm) :
  subst_Tm tau_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm_pointwise (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Tm_Tm (xi : nat -> nat) (sigma : nat -> Tm)
  (Eq : forall x, funcomp (VarTm) xi x = sigma x) :
  forall x, funcomp (VarTm) (upRen_Tm_Tm xi) x = up_Tm_Tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_Tm (xi_Tm : nat -> nat) (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (VarTm) xi_Tm x = sigma_Tm x) (s : Tm) {struct s}
   : ren_Tm xi_Tm s = subst_Tm sigma_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | TmAbs s0 =>
      congr_TmAbs
        (rinst_inst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm sigma_Tm)
           (rinstInst_up_Tm_Tm _ _ Eq_Tm) s0)
  | TmApp s0 s1 =>
      congr_TmApp (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  end.

Lemma rinstInst'_Tm (xi_Tm : nat -> nat) (s : Tm) :
  ren_Tm xi_Tm s = subst_Tm (funcomp (VarTm) xi_Tm) s.
Proof.
exact (rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Tm_pointwise (xi_Tm : nat -> nat) :
  pointwise_relation _ eq (ren_Tm xi_Tm) (subst_Tm (funcomp (VarTm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm (s : Tm) : subst_Tm (VarTm) s = s.
Proof.
exact (idSubst_Tm (VarTm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm_pointwise : pointwise_relation _ eq (subst_Tm (VarTm)) id.
Proof.
exact (fun s => idSubst_Tm (VarTm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Tm (s : Tm) : ren_Tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma rinstId'_Tm_pointwise : pointwise_relation _ eq (@ren_Tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma varL'_Tm (sigma_Tm : nat -> Tm) (x : nat) :
  subst_Tm sigma_Tm (VarTm x) = sigma_Tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Tm_pointwise (sigma_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm sigma_Tm) (VarTm)) sigma_Tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Tm (xi_Tm : nat -> nat) (x : nat) :
  ren_Tm xi_Tm (VarTm x) = VarTm (xi_Tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Tm_pointwise (xi_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm xi_Tm) (VarTm))
    (funcomp (VarTm) xi_Tm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive Ty : Type :=
  | VarTy : nat -> Ty
  | TyAbs : Ki -> Ty -> Ty
  | TyApp : Ty -> Ty -> Ty
  | TyForall : Ki -> Ty -> Ty
  | TyFun : Ty -> Ty -> Ty.

Lemma congr_TyAbs {s0 : Ki} {s1 : Ty} {t0 : Ki} {t1 : Ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : TyAbs s0 s1 = TyAbs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TyAbs x s1) H0))
         (ap (fun x => TyAbs t0 x) H1)).
Qed.

Lemma congr_TyApp {s0 : Ty} {s1 : Ty} {t0 : Ty} {t1 : Ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : TyApp s0 s1 = TyApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TyApp x s1) H0))
         (ap (fun x => TyApp t0 x) H1)).
Qed.

Lemma congr_TyForall {s0 : Ki} {s1 : Ty} {t0 : Ki} {t1 : Ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : TyForall s0 s1 = TyForall t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TyForall x s1) H0))
         (ap (fun x => TyForall t0 x) H1)).
Qed.

Lemma congr_TyFun {s0 : Ty} {s1 : Ty} {t0 : Ty} {t1 : Ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : TyFun s0 s1 = TyFun t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TyFun x s1) H0))
         (ap (fun x => TyFun t0 x) H1)).
Qed.

Lemma upRen_Ty_Ty (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_Ty (xi_Ty : nat -> nat) (s : Ty) {struct s} : Ty :=
  match s with
  | VarTy s0 => VarTy (xi_Ty s0)
  | TyAbs s0 s1 => TyAbs s0 (ren_Ty (upRen_Ty_Ty xi_Ty) s1)
  | TyApp s0 s1 => TyApp (ren_Ty xi_Ty s0) (ren_Ty xi_Ty s1)
  | TyForall s0 s1 => TyForall s0 (ren_Ty (upRen_Ty_Ty xi_Ty) s1)
  | TyFun s0 s1 => TyFun (ren_Ty xi_Ty s0) (ren_Ty xi_Ty s1)
  end.

Lemma up_Ty_Ty (sigma : nat -> Ty) : nat -> Ty.
Proof.
exact (scons (VarTy var_zero) (funcomp (ren_Ty shift) sigma)).
Defined.

Fixpoint subst_Ty (sigma_Ty : nat -> Ty) (s : Ty) {struct s} : Ty :=
  match s with
  | VarTy s0 => sigma_Ty s0
  | TyAbs s0 s1 => TyAbs s0 (subst_Ty (up_Ty_Ty sigma_Ty) s1)
  | TyApp s0 s1 => TyApp (subst_Ty sigma_Ty s0) (subst_Ty sigma_Ty s1)
  | TyForall s0 s1 => TyForall s0 (subst_Ty (up_Ty_Ty sigma_Ty) s1)
  | TyFun s0 s1 => TyFun (subst_Ty sigma_Ty s0) (subst_Ty sigma_Ty s1)
  end.

Lemma upId_Ty_Ty (sigma : nat -> Ty) (Eq : forall x, sigma x = VarTy x) :
  forall x, up_Ty_Ty sigma x = VarTy x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_Ty (sigma_Ty : nat -> Ty)
(Eq_Ty : forall x, sigma_Ty x = VarTy x) (s : Ty) {struct s} :
subst_Ty sigma_Ty s = s :=
  match s with
  | VarTy s0 => Eq_Ty s0
  | TyAbs s0 s1 =>
      congr_TyAbs (eq_refl s0)
        (idSubst_Ty (up_Ty_Ty sigma_Ty) (upId_Ty_Ty _ Eq_Ty) s1)
  | TyApp s0 s1 =>
      congr_TyApp (idSubst_Ty sigma_Ty Eq_Ty s0)
        (idSubst_Ty sigma_Ty Eq_Ty s1)
  | TyForall s0 s1 =>
      congr_TyForall (eq_refl s0)
        (idSubst_Ty (up_Ty_Ty sigma_Ty) (upId_Ty_Ty _ Eq_Ty) s1)
  | TyFun s0 s1 =>
      congr_TyFun (idSubst_Ty sigma_Ty Eq_Ty s0)
        (idSubst_Ty sigma_Ty Eq_Ty s1)
  end.

Lemma upExtRen_Ty_Ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Ty_Ty xi x = upRen_Ty_Ty zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_Ty (xi_Ty : nat -> nat) (zeta_Ty : nat -> nat)
(Eq_Ty : forall x, xi_Ty x = zeta_Ty x) (s : Ty) {struct s} :
ren_Ty xi_Ty s = ren_Ty zeta_Ty s :=
  match s with
  | VarTy s0 => ap (VarTy) (Eq_Ty s0)
  | TyAbs s0 s1 =>
      congr_TyAbs (eq_refl s0)
        (extRen_Ty (upRen_Ty_Ty xi_Ty) (upRen_Ty_Ty zeta_Ty)
           (upExtRen_Ty_Ty _ _ Eq_Ty) s1)
  | TyApp s0 s1 =>
      congr_TyApp (extRen_Ty xi_Ty zeta_Ty Eq_Ty s0)
        (extRen_Ty xi_Ty zeta_Ty Eq_Ty s1)
  | TyForall s0 s1 =>
      congr_TyForall (eq_refl s0)
        (extRen_Ty (upRen_Ty_Ty xi_Ty) (upRen_Ty_Ty zeta_Ty)
           (upExtRen_Ty_Ty _ _ Eq_Ty) s1)
  | TyFun s0 s1 =>
      congr_TyFun (extRen_Ty xi_Ty zeta_Ty Eq_Ty s0)
        (extRen_Ty xi_Ty zeta_Ty Eq_Ty s1)
  end.

Lemma upExt_Ty_Ty (sigma : nat -> Ty) (tau : nat -> Ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_Ty_Ty sigma x = up_Ty_Ty tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_Ty (sigma_Ty : nat -> Ty) (tau_Ty : nat -> Ty)
(Eq_Ty : forall x, sigma_Ty x = tau_Ty x) (s : Ty) {struct s} :
subst_Ty sigma_Ty s = subst_Ty tau_Ty s :=
  match s with
  | VarTy s0 => Eq_Ty s0
  | TyAbs s0 s1 =>
      congr_TyAbs (eq_refl s0)
        (ext_Ty (up_Ty_Ty sigma_Ty) (up_Ty_Ty tau_Ty) (upExt_Ty_Ty _ _ Eq_Ty)
           s1)
  | TyApp s0 s1 =>
      congr_TyApp (ext_Ty sigma_Ty tau_Ty Eq_Ty s0)
        (ext_Ty sigma_Ty tau_Ty Eq_Ty s1)
  | TyForall s0 s1 =>
      congr_TyForall (eq_refl s0)
        (ext_Ty (up_Ty_Ty sigma_Ty) (up_Ty_Ty tau_Ty) (upExt_Ty_Ty _ _ Eq_Ty)
           s1)
  | TyFun s0 s1 =>
      congr_TyFun (ext_Ty sigma_Ty tau_Ty Eq_Ty s0)
        (ext_Ty sigma_Ty tau_Ty Eq_Ty s1)
  end.

Lemma up_ren_ren_Ty_Ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_Ty_Ty zeta) (upRen_Ty_Ty xi) x = upRen_Ty_Ty rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_Ty (xi_Ty : nat -> nat) (zeta_Ty : nat -> nat)
(rho_Ty : nat -> nat) (Eq_Ty : forall x, funcomp zeta_Ty xi_Ty x = rho_Ty x)
(s : Ty) {struct s} : ren_Ty zeta_Ty (ren_Ty xi_Ty s) = ren_Ty rho_Ty s :=
  match s with
  | VarTy s0 => ap (VarTy) (Eq_Ty s0)
  | TyAbs s0 s1 =>
      congr_TyAbs (eq_refl s0)
        (compRenRen_Ty (upRen_Ty_Ty xi_Ty) (upRen_Ty_Ty zeta_Ty)
           (upRen_Ty_Ty rho_Ty) (up_ren_ren _ _ _ Eq_Ty) s1)
  | TyApp s0 s1 =>
      congr_TyApp (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s0)
        (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s1)
  | TyForall s0 s1 =>
      congr_TyForall (eq_refl s0)
        (compRenRen_Ty (upRen_Ty_Ty xi_Ty) (upRen_Ty_Ty zeta_Ty)
           (upRen_Ty_Ty rho_Ty) (up_ren_ren _ _ _ Eq_Ty) s1)
  | TyFun s0 s1 =>
      congr_TyFun (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s0)
        (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s1)
  end.

Lemma up_ren_subst_Ty_Ty (xi : nat -> nat) (tau : nat -> Ty)
  (theta : nat -> Ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_Ty_Ty tau) (upRen_Ty_Ty xi) x = up_Ty_Ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_Ty (xi_Ty : nat -> nat) (tau_Ty : nat -> Ty)
(theta_Ty : nat -> Ty)
(Eq_Ty : forall x, funcomp tau_Ty xi_Ty x = theta_Ty x) (s : Ty) {struct s} :
subst_Ty tau_Ty (ren_Ty xi_Ty s) = subst_Ty theta_Ty s :=
  match s with
  | VarTy s0 => Eq_Ty s0
  | TyAbs s0 s1 =>
      congr_TyAbs (eq_refl s0)
        (compRenSubst_Ty (upRen_Ty_Ty xi_Ty) (up_Ty_Ty tau_Ty)
           (up_Ty_Ty theta_Ty) (up_ren_subst_Ty_Ty _ _ _ Eq_Ty) s1)
  | TyApp s0 s1 =>
      congr_TyApp (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s1)
  | TyForall s0 s1 =>
      congr_TyForall (eq_refl s0)
        (compRenSubst_Ty (upRen_Ty_Ty xi_Ty) (up_Ty_Ty tau_Ty)
           (up_Ty_Ty theta_Ty) (up_ren_subst_Ty_Ty _ _ _ Eq_Ty) s1)
  | TyFun s0 s1 =>
      congr_TyFun (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s1)
  end.

Lemma up_subst_ren_Ty_Ty (sigma : nat -> Ty) (zeta_Ty : nat -> nat)
  (theta : nat -> Ty)
  (Eq : forall x, funcomp (ren_Ty zeta_Ty) sigma x = theta x) :
  forall x,
  funcomp (ren_Ty (upRen_Ty_Ty zeta_Ty)) (up_Ty_Ty sigma) x =
  up_Ty_Ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_Ty shift (upRen_Ty_Ty zeta_Ty)
                (funcomp shift zeta_Ty) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_Ty zeta_Ty shift (funcomp shift zeta_Ty)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_Ty shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_Ty (sigma_Ty : nat -> Ty) (zeta_Ty : nat -> nat)
(theta_Ty : nat -> Ty)
(Eq_Ty : forall x, funcomp (ren_Ty zeta_Ty) sigma_Ty x = theta_Ty x) 
(s : Ty) {struct s} :
ren_Ty zeta_Ty (subst_Ty sigma_Ty s) = subst_Ty theta_Ty s :=
  match s with
  | VarTy s0 => Eq_Ty s0
  | TyAbs s0 s1 =>
      congr_TyAbs (eq_refl s0)
        (compSubstRen_Ty (up_Ty_Ty sigma_Ty) (upRen_Ty_Ty zeta_Ty)
           (up_Ty_Ty theta_Ty) (up_subst_ren_Ty_Ty _ _ _ Eq_Ty) s1)
  | TyApp s0 s1 =>
      congr_TyApp (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s0)
        (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s1)
  | TyForall s0 s1 =>
      congr_TyForall (eq_refl s0)
        (compSubstRen_Ty (up_Ty_Ty sigma_Ty) (upRen_Ty_Ty zeta_Ty)
           (up_Ty_Ty theta_Ty) (up_subst_ren_Ty_Ty _ _ _ Eq_Ty) s1)
  | TyFun s0 s1 =>
      congr_TyFun (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s0)
        (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s1)
  end.

Lemma up_subst_subst_Ty_Ty (sigma : nat -> Ty) (tau_Ty : nat -> Ty)
  (theta : nat -> Ty)
  (Eq : forall x, funcomp (subst_Ty tau_Ty) sigma x = theta x) :
  forall x,
  funcomp (subst_Ty (up_Ty_Ty tau_Ty)) (up_Ty_Ty sigma) x = up_Ty_Ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_Ty shift (up_Ty_Ty tau_Ty)
                (funcomp (up_Ty_Ty tau_Ty) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_Ty tau_Ty shift
                      (funcomp (ren_Ty shift) tau_Ty) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_Ty shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_Ty (sigma_Ty : nat -> Ty) (tau_Ty : nat -> Ty)
(theta_Ty : nat -> Ty)
(Eq_Ty : forall x, funcomp (subst_Ty tau_Ty) sigma_Ty x = theta_Ty x)
(s : Ty) {struct s} :
subst_Ty tau_Ty (subst_Ty sigma_Ty s) = subst_Ty theta_Ty s :=
  match s with
  | VarTy s0 => Eq_Ty s0
  | TyAbs s0 s1 =>
      congr_TyAbs (eq_refl s0)
        (compSubstSubst_Ty (up_Ty_Ty sigma_Ty) (up_Ty_Ty tau_Ty)
           (up_Ty_Ty theta_Ty) (up_subst_subst_Ty_Ty _ _ _ Eq_Ty) s1)
  | TyApp s0 s1 =>
      congr_TyApp (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s1)
  | TyForall s0 s1 =>
      congr_TyForall (eq_refl s0)
        (compSubstSubst_Ty (up_Ty_Ty sigma_Ty) (up_Ty_Ty tau_Ty)
           (up_Ty_Ty theta_Ty) (up_subst_subst_Ty_Ty _ _ _ Eq_Ty) s1)
  | TyFun s0 s1 =>
      congr_TyFun (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s1)
  end.

Lemma renRen_Ty (xi_Ty : nat -> nat) (zeta_Ty : nat -> nat) (s : Ty) :
  ren_Ty zeta_Ty (ren_Ty xi_Ty s) = ren_Ty (funcomp zeta_Ty xi_Ty) s.
Proof.
exact (compRenRen_Ty xi_Ty zeta_Ty _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Ty_pointwise (xi_Ty : nat -> nat) (zeta_Ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Ty zeta_Ty) (ren_Ty xi_Ty))
    (ren_Ty (funcomp zeta_Ty xi_Ty)).
Proof.
exact (fun s => compRenRen_Ty xi_Ty zeta_Ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Ty (xi_Ty : nat -> nat) (tau_Ty : nat -> Ty) (s : Ty) :
  subst_Ty tau_Ty (ren_Ty xi_Ty s) = subst_Ty (funcomp tau_Ty xi_Ty) s.
Proof.
exact (compRenSubst_Ty xi_Ty tau_Ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Ty_pointwise (xi_Ty : nat -> nat) (tau_Ty : nat -> Ty) :
  pointwise_relation _ eq (funcomp (subst_Ty tau_Ty) (ren_Ty xi_Ty))
    (subst_Ty (funcomp tau_Ty xi_Ty)).
Proof.
exact (fun s => compRenSubst_Ty xi_Ty tau_Ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Ty (sigma_Ty : nat -> Ty) (zeta_Ty : nat -> nat) (s : Ty) :
  ren_Ty zeta_Ty (subst_Ty sigma_Ty s) =
  subst_Ty (funcomp (ren_Ty zeta_Ty) sigma_Ty) s.
Proof.
exact (compSubstRen_Ty sigma_Ty zeta_Ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Ty_pointwise (sigma_Ty : nat -> Ty) (zeta_Ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Ty zeta_Ty) (subst_Ty sigma_Ty))
    (subst_Ty (funcomp (ren_Ty zeta_Ty) sigma_Ty)).
Proof.
exact (fun s => compSubstRen_Ty sigma_Ty zeta_Ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Ty (sigma_Ty : nat -> Ty) (tau_Ty : nat -> Ty) (s : Ty) :
  subst_Ty tau_Ty (subst_Ty sigma_Ty s) =
  subst_Ty (funcomp (subst_Ty tau_Ty) sigma_Ty) s.
Proof.
exact (compSubstSubst_Ty sigma_Ty tau_Ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Ty_pointwise (sigma_Ty : nat -> Ty) (tau_Ty : nat -> Ty) :
  pointwise_relation _ eq (funcomp (subst_Ty tau_Ty) (subst_Ty sigma_Ty))
    (subst_Ty (funcomp (subst_Ty tau_Ty) sigma_Ty)).
Proof.
exact (fun s => compSubstSubst_Ty sigma_Ty tau_Ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Ty_Ty (xi : nat -> nat) (sigma : nat -> Ty)
  (Eq : forall x, funcomp (VarTy) xi x = sigma x) :
  forall x, funcomp (VarTy) (upRen_Ty_Ty xi) x = up_Ty_Ty sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_Ty (xi_Ty : nat -> nat) (sigma_Ty : nat -> Ty)
(Eq_Ty : forall x, funcomp (VarTy) xi_Ty x = sigma_Ty x) (s : Ty) {struct s}
   : ren_Ty xi_Ty s = subst_Ty sigma_Ty s :=
  match s with
  | VarTy s0 => Eq_Ty s0
  | TyAbs s0 s1 =>
      congr_TyAbs (eq_refl s0)
        (rinst_inst_Ty (upRen_Ty_Ty xi_Ty) (up_Ty_Ty sigma_Ty)
           (rinstInst_up_Ty_Ty _ _ Eq_Ty) s1)
  | TyApp s0 s1 =>
      congr_TyApp (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s0)
        (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s1)
  | TyForall s0 s1 =>
      congr_TyForall (eq_refl s0)
        (rinst_inst_Ty (upRen_Ty_Ty xi_Ty) (up_Ty_Ty sigma_Ty)
           (rinstInst_up_Ty_Ty _ _ Eq_Ty) s1)
  | TyFun s0 s1 =>
      congr_TyFun (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s0)
        (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s1)
  end.

Lemma rinstInst'_Ty (xi_Ty : nat -> nat) (s : Ty) :
  ren_Ty xi_Ty s = subst_Ty (funcomp (VarTy) xi_Ty) s.
Proof.
exact (rinst_inst_Ty xi_Ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Ty_pointwise (xi_Ty : nat -> nat) :
  pointwise_relation _ eq (ren_Ty xi_Ty) (subst_Ty (funcomp (VarTy) xi_Ty)).
Proof.
exact (fun s => rinst_inst_Ty xi_Ty _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Ty (s : Ty) : subst_Ty (VarTy) s = s.
Proof.
exact (idSubst_Ty (VarTy) (fun n => eq_refl) s).
Qed.

Lemma instId'_Ty_pointwise : pointwise_relation _ eq (subst_Ty (VarTy)) id.
Proof.
exact (fun s => idSubst_Ty (VarTy) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Ty (s : Ty) : ren_Ty id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Ty s) (rinstInst'_Ty id s)).
Qed.

Lemma rinstId'_Ty_pointwise : pointwise_relation _ eq (@ren_Ty id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Ty s) (rinstInst'_Ty id s)).
Qed.

Lemma varL'_Ty (sigma_Ty : nat -> Ty) (x : nat) :
  subst_Ty sigma_Ty (VarTy x) = sigma_Ty x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Ty_pointwise (sigma_Ty : nat -> Ty) :
  pointwise_relation _ eq (funcomp (subst_Ty sigma_Ty) (VarTy)) sigma_Ty.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Ty (xi_Ty : nat -> nat) (x : nat) :
  ren_Ty xi_Ty (VarTy x) = VarTy (xi_Ty x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Ty_pointwise (xi_Ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Ty xi_Ty) (VarTy))
    (funcomp (VarTy) xi_Ty).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_Ty X Y :=
    up_Ty : X -> Y.

Class Up_Tm X Y :=
    up_Tm : X -> Y.

Class Up_CTm X Y :=
    up_CTm : X -> Y.

#[global]Instance Subst_Ty : (Subst1 _ _ _) := @subst_Ty.

#[global]Instance Up_Ty_Ty : (Up_Ty _ _) := @up_Ty_Ty.

#[global]Instance Ren_Ty : (Ren1 _ _ _) := @ren_Ty.

#[global]Instance VarInstance_Ty : (Var _ _) := @VarTy.

#[global]Instance Subst_Tm : (Subst1 _ _ _) := @subst_Tm.

#[global]Instance Up_Tm_Tm : (Up_Tm _ _) := @up_Tm_Tm.

#[global]Instance Ren_Tm : (Ren1 _ _ _) := @ren_Tm.

#[global]Instance VarInstance_Tm : (Var _ _) := @VarTm.

#[global]Instance Subst_CTm : (Subst1 _ _ _) := @subst_CTm.

#[global]Instance Up_CTm_CTm : (Up_CTm _ _) := @up_CTm_CTm.

#[global]Instance Ren_CTm : (Ren1 _ _ _) := @ren_CTm.

#[global]
Instance VarInstance_CTm : (Var _ _) := @VarCTm.

Notation "[ sigma_Ty ]" := (subst_Ty sigma_Ty)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_Ty ]" := (subst_Ty sigma_Ty s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Ty" := up_Ty (only printing)  : subst_scope.

Notation "↑__Ty" := up_Ty_Ty (only printing)  : subst_scope.

Notation "⟨ xi_Ty ⟩" := (ren_Ty xi_Ty)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_Ty ⟩" := (ren_Ty xi_Ty s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := VarTy ( at level 1, only printing)  : subst_scope.

Notation "x '__Ty'" := (@ids _ _ VarInstance_Ty x)
( at level 5, format "x __Ty", only printing)  : subst_scope.

Notation "x '__Ty'" := (VarTy x) ( at level 5, format "x __Ty")  :
subst_scope.

Notation "[ sigma_Tm ]" := (subst_Tm sigma_Tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_Tm ]" := (subst_Tm sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm (only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm_Tm (only printing)  : subst_scope.

Notation "⟨ xi_Tm ⟩" := (ren_Tm xi_Tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Tm xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := VarTm ( at level 1, only printing)  : subst_scope.

Notation "x '__Tm'" := (@ids _ _ VarInstance_Tm x)
( at level 5, format "x __Tm", only printing)  : subst_scope.

Notation "x '__Tm'" := (VarTm x) ( at level 5, format "x __Tm")  :
subst_scope.

Notation "[ sigma_CTm ]" := (subst_CTm sigma_CTm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_CTm ]" := (subst_CTm sigma_CTm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__CTm" := up_CTm (only printing)  : subst_scope.

Notation "↑__CTm" := up_CTm_CTm (only printing)  : subst_scope.

Notation "⟨ xi_CTm ⟩" := (ren_CTm xi_CTm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_CTm ⟩" := (ren_CTm xi_CTm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := VarCTm ( at level 1, only printing)  : subst_scope.

Notation "x '__CTm'" := (@ids _ _ VarInstance_CTm x)
( at level 5, format "x __CTm", only printing)  : subst_scope.

Notation "x '__CTm'" := (VarCTm x) ( at level 5, format "x __CTm")  :
subst_scope.

#[global]
Instance subst_Ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Ty)).
Proof.
exact (fun f_Ty g_Ty Eq_Ty s t Eq_st =>
       eq_ind s (fun t' => subst_Ty f_Ty s = subst_Ty g_Ty t')
         (ext_Ty f_Ty g_Ty Eq_Ty s) t Eq_st).
Qed.

#[global]
Instance subst_Ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Ty)).
Proof.
exact (fun f_Ty g_Ty Eq_Ty s => ext_Ty f_Ty g_Ty Eq_Ty s).
Qed.

#[global]
Instance ren_Ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_Ty)).
Proof.
exact (fun f_Ty g_Ty Eq_Ty s t Eq_st =>
       eq_ind s (fun t' => ren_Ty f_Ty s = ren_Ty g_Ty t')
         (extRen_Ty f_Ty g_Ty Eq_Ty s) t Eq_st).
Qed.

#[global]
Instance ren_Ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Ty)).
Proof.
exact (fun f_Ty g_Ty Eq_Ty s => extRen_Ty f_Ty g_Ty Eq_Ty s).
Qed.

#[global]
Instance subst_Tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Tm f_Tm s = subst_Tm g_Tm t')
         (ext_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Tm f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Tm f_Tm s = ren_Tm g_Tm t')
         (extRen_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Tm f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_CTm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_CTm)).
Proof.
exact (fun f_CTm g_CTm Eq_CTm s t Eq_st =>
       eq_ind s (fun t' => subst_CTm f_CTm s = subst_CTm g_CTm t')
         (ext_CTm f_CTm g_CTm Eq_CTm s) t Eq_st).
Qed.

#[global]
Instance subst_CTm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_CTm)).
Proof.
exact (fun f_CTm g_CTm Eq_CTm s => ext_CTm f_CTm g_CTm Eq_CTm s).
Qed.

#[global]
Instance ren_CTm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_CTm)).
Proof.
exact (fun f_CTm g_CTm Eq_CTm s t Eq_st =>
       eq_ind s (fun t' => ren_CTm f_CTm s = ren_CTm g_CTm t')
         (extRen_CTm f_CTm g_CTm Eq_CTm s) t Eq_st).
Qed.

#[global]
Instance ren_CTm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_CTm)).
Proof.
exact (fun f_CTm g_CTm Eq_CTm s => extRen_CTm f_CTm g_CTm Eq_CTm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_CTm, Var, ids, Ren_CTm, Ren1, ren1,
                      Up_CTm_CTm, Up_CTm, up_CTm, Subst_CTm, Subst1, subst1,
                      VarInstance_Tm, Var, ids, Ren_Tm, Ren1, ren1, Up_Tm_Tm,
                      Up_Tm, up_Tm, Subst_Tm, Subst1, subst1, VarInstance_Ty,
                      Var, ids, Ren_Ty, Ren1, ren1, Up_Ty_Ty, Up_Ty, up_Ty,
                      Subst_Ty, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_CTm, Var, ids,
                                            Ren_CTm, Ren1, ren1, Up_CTm_CTm,
                                            Up_CTm, up_CTm, Subst_CTm,
                                            Subst1, subst1, VarInstance_Tm,
                                            Var, ids, Ren_Tm, Ren1, ren1,
                                            Up_Tm_Tm, Up_Tm, up_Tm, Subst_Tm,
                                            Subst1, subst1, VarInstance_Ty,
                                            Var, ids, Ren_Ty, Ren1, ren1,
                                            Up_Ty_Ty, Up_Ty, up_Ty, Subst_Ty,
                                            Subst1, subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_Ty_pointwise
                 | progress setoid_rewrite substSubst_Ty
                 | progress setoid_rewrite substRen_Ty_pointwise
                 | progress setoid_rewrite substRen_Ty
                 | progress setoid_rewrite renSubst_Ty_pointwise
                 | progress setoid_rewrite renSubst_Ty
                 | progress setoid_rewrite renRen'_Ty_pointwise
                 | progress setoid_rewrite renRen_Ty
                 | progress setoid_rewrite substSubst_Tm_pointwise
                 | progress setoid_rewrite substSubst_Tm
                 | progress setoid_rewrite substRen_Tm_pointwise
                 | progress setoid_rewrite substRen_Tm
                 | progress setoid_rewrite renSubst_Tm_pointwise
                 | progress setoid_rewrite renSubst_Tm
                 | progress setoid_rewrite renRen'_Tm_pointwise
                 | progress setoid_rewrite renRen_Tm
                 | progress setoid_rewrite substSubst_CTm_pointwise
                 | progress setoid_rewrite substSubst_CTm
                 | progress setoid_rewrite substRen_CTm_pointwise
                 | progress setoid_rewrite substRen_CTm
                 | progress setoid_rewrite renSubst_CTm_pointwise
                 | progress setoid_rewrite renSubst_CTm
                 | progress setoid_rewrite renRen'_CTm_pointwise
                 | progress setoid_rewrite renRen_CTm
                 | progress setoid_rewrite varLRen'_Ty_pointwise
                 | progress setoid_rewrite varLRen'_Ty
                 | progress setoid_rewrite varL'_Ty_pointwise
                 | progress setoid_rewrite varL'_Ty
                 | progress setoid_rewrite rinstId'_Ty_pointwise
                 | progress setoid_rewrite rinstId'_Ty
                 | progress setoid_rewrite instId'_Ty_pointwise
                 | progress setoid_rewrite instId'_Ty
                 | progress setoid_rewrite varLRen'_Tm_pointwise
                 | progress setoid_rewrite varLRen'_Tm
                 | progress setoid_rewrite varL'_Tm_pointwise
                 | progress setoid_rewrite varL'_Tm
                 | progress setoid_rewrite rinstId'_Tm_pointwise
                 | progress setoid_rewrite rinstId'_Tm
                 | progress setoid_rewrite instId'_Tm_pointwise
                 | progress setoid_rewrite instId'_Tm
                 | progress setoid_rewrite varLRen'_CTm_pointwise
                 | progress setoid_rewrite varLRen'_CTm
                 | progress setoid_rewrite varL'_CTm_pointwise
                 | progress setoid_rewrite varL'_CTm
                 | progress setoid_rewrite rinstId'_CTm_pointwise
                 | progress setoid_rewrite rinstId'_CTm
                 | progress setoid_rewrite instId'_CTm_pointwise
                 | progress setoid_rewrite instId'_CTm
                 | progress
                    unfold up_Ty_Ty, upRen_Ty_Ty, up_Tm_Tm, upRen_Tm_Tm,
                     up_CTm_CTm, upRen_CTm_CTm, up_ren
                 | progress
                    cbn[subst_Ty ren_Ty subst_Tm ren_Tm subst_CTm ren_CTm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_CTm, Var, ids, Ren_CTm, Ren1, ren1,
                  Up_CTm_CTm, Up_CTm, up_CTm, Subst_CTm, Subst1, subst1,
                  VarInstance_Tm, Var, ids, Ren_Tm, Ren1, ren1, Up_Tm_Tm,
                  Up_Tm, up_Tm, Subst_Tm, Subst1, subst1, VarInstance_Ty,
                  Var, ids, Ren_Ty, Ren1, ren1, Up_Ty_Ty, Up_Ty, up_Ty,
                  Subst_Ty, Subst1, subst1 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_Ty_pointwise;
                  try setoid_rewrite rinstInst'_Ty;
                  try setoid_rewrite rinstInst'_Tm_pointwise;
                  try setoid_rewrite rinstInst'_Tm;
                  try setoid_rewrite rinstInst'_CTm_pointwise;
                  try setoid_rewrite rinstInst'_CTm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_Ty_pointwise;
                  try setoid_rewrite_left rinstInst'_Ty;
                  try setoid_rewrite_left rinstInst'_Tm_pointwise;
                  try setoid_rewrite_left rinstInst'_Tm;
                  try setoid_rewrite_left rinstInst'_CTm_pointwise;
                  try setoid_rewrite_left rinstInst'_CTm.

End Core.

Module Extra.

Import Core.

#[global]Hint Opaque subst_Ty: rewrite.

#[global]Hint Opaque ren_Ty: rewrite.

#[global]Hint Opaque subst_Tm: rewrite.

#[global]Hint Opaque ren_Tm: rewrite.

#[global]Hint Opaque subst_CTm: rewrite.

#[global]Hint Opaque ren_CTm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

