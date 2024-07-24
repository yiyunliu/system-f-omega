Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive Sort : Type :=
  | Kind : Sort
  | Star : Sort.

Lemma congr_Kind : Kind = Kind.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Star : Star = Star.
Proof.
exact (eq_refl).
Qed.

Inductive Term : Type :=
  | VarTm : nat -> Term
  | ISort : Sort -> Term
  | Abs : Term -> Term -> Term
  | App : Term -> Term -> Term
  | Pi : Term -> Term -> Term.

Lemma congr_ISort {s0 : Sort} {t0 : Sort} (H0 : s0 = t0) :
  ISort s0 = ISort t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ISort x) H0)).
Qed.

Lemma congr_Abs {s0 : Term} {s1 : Term} {t0 : Term} {t1 : Term}
  (H0 : s0 = t0) (H1 : s1 = t1) : Abs s0 s1 = Abs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Abs x s1) H0))
         (ap (fun x => Abs t0 x) H1)).
Qed.

Lemma congr_App {s0 : Term} {s1 : Term} {t0 : Term} {t1 : Term}
  (H0 : s0 = t0) (H1 : s1 = t1) : App s0 s1 = App t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => App x s1) H0))
         (ap (fun x => App t0 x) H1)).
Qed.

Lemma congr_Pi {s0 : Term} {s1 : Term} {t0 : Term} {t1 : Term} (H0 : s0 = t0)
  (H1 : s1 = t1) : Pi s0 s1 = Pi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Pi x s1) H0))
         (ap (fun x => Pi t0 x) H1)).
Qed.

Lemma upRen_Term_Term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_Term (xi_Term : nat -> nat) (s : Term) {struct s} : Term :=
  match s with
  | VarTm s0 => VarTm (xi_Term s0)
  | ISort s0 => ISort s0
  | Abs s0 s1 =>
      Abs (ren_Term xi_Term s0) (ren_Term (upRen_Term_Term xi_Term) s1)
  | App s0 s1 => App (ren_Term xi_Term s0) (ren_Term xi_Term s1)
  | Pi s0 s1 =>
      Pi (ren_Term xi_Term s0) (ren_Term (upRen_Term_Term xi_Term) s1)
  end.

Lemma up_Term_Term (sigma : nat -> Term) : nat -> Term.
Proof.
exact (scons (VarTm var_zero) (funcomp (ren_Term shift) sigma)).
Defined.

Fixpoint subst_Term (sigma_Term : nat -> Term) (s : Term) {struct s} : 
Term :=
  match s with
  | VarTm s0 => sigma_Term s0
  | ISort s0 => ISort s0
  | Abs s0 s1 =>
      Abs (subst_Term sigma_Term s0)
        (subst_Term (up_Term_Term sigma_Term) s1)
  | App s0 s1 => App (subst_Term sigma_Term s0) (subst_Term sigma_Term s1)
  | Pi s0 s1 =>
      Pi (subst_Term sigma_Term s0) (subst_Term (up_Term_Term sigma_Term) s1)
  end.

Lemma upId_Term_Term (sigma : nat -> Term) (Eq : forall x, sigma x = VarTm x)
  : forall x, up_Term_Term sigma x = VarTm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_Term (sigma_Term : nat -> Term)
(Eq_Term : forall x, sigma_Term x = VarTm x) (s : Term) {struct s} :
subst_Term sigma_Term s = s :=
  match s with
  | VarTm s0 => Eq_Term s0
  | ISort s0 => congr_ISort (eq_refl s0)
  | Abs s0 s1 =>
      congr_Abs (idSubst_Term sigma_Term Eq_Term s0)
        (idSubst_Term (up_Term_Term sigma_Term) (upId_Term_Term _ Eq_Term) s1)
  | App s0 s1 =>
      congr_App (idSubst_Term sigma_Term Eq_Term s0)
        (idSubst_Term sigma_Term Eq_Term s1)
  | Pi s0 s1 =>
      congr_Pi (idSubst_Term sigma_Term Eq_Term s0)
        (idSubst_Term (up_Term_Term sigma_Term) (upId_Term_Term _ Eq_Term) s1)
  end.

Lemma upExtRen_Term_Term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Term_Term xi x = upRen_Term_Term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_Term (xi_Term : nat -> nat) (zeta_Term : nat -> nat)
(Eq_Term : forall x, xi_Term x = zeta_Term x) (s : Term) {struct s} :
ren_Term xi_Term s = ren_Term zeta_Term s :=
  match s with
  | VarTm s0 => ap (VarTm) (Eq_Term s0)
  | ISort s0 => congr_ISort (eq_refl s0)
  | Abs s0 s1 =>
      congr_Abs (extRen_Term xi_Term zeta_Term Eq_Term s0)
        (extRen_Term (upRen_Term_Term xi_Term) (upRen_Term_Term zeta_Term)
           (upExtRen_Term_Term _ _ Eq_Term) s1)
  | App s0 s1 =>
      congr_App (extRen_Term xi_Term zeta_Term Eq_Term s0)
        (extRen_Term xi_Term zeta_Term Eq_Term s1)
  | Pi s0 s1 =>
      congr_Pi (extRen_Term xi_Term zeta_Term Eq_Term s0)
        (extRen_Term (upRen_Term_Term xi_Term) (upRen_Term_Term zeta_Term)
           (upExtRen_Term_Term _ _ Eq_Term) s1)
  end.

Lemma upExt_Term_Term (sigma : nat -> Term) (tau : nat -> Term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_Term_Term sigma x = up_Term_Term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_Term (sigma_Term : nat -> Term) (tau_Term : nat -> Term)
(Eq_Term : forall x, sigma_Term x = tau_Term x) (s : Term) {struct s} :
subst_Term sigma_Term s = subst_Term tau_Term s :=
  match s with
  | VarTm s0 => Eq_Term s0
  | ISort s0 => congr_ISort (eq_refl s0)
  | Abs s0 s1 =>
      congr_Abs (ext_Term sigma_Term tau_Term Eq_Term s0)
        (ext_Term (up_Term_Term sigma_Term) (up_Term_Term tau_Term)
           (upExt_Term_Term _ _ Eq_Term) s1)
  | App s0 s1 =>
      congr_App (ext_Term sigma_Term tau_Term Eq_Term s0)
        (ext_Term sigma_Term tau_Term Eq_Term s1)
  | Pi s0 s1 =>
      congr_Pi (ext_Term sigma_Term tau_Term Eq_Term s0)
        (ext_Term (up_Term_Term sigma_Term) (up_Term_Term tau_Term)
           (upExt_Term_Term _ _ Eq_Term) s1)
  end.

Lemma up_ren_ren_Term_Term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_Term_Term zeta) (upRen_Term_Term xi) x =
  upRen_Term_Term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_Term (xi_Term : nat -> nat) (zeta_Term : nat -> nat)
(rho_Term : nat -> nat)
(Eq_Term : forall x, funcomp zeta_Term xi_Term x = rho_Term x) (s : Term)
{struct s} : ren_Term zeta_Term (ren_Term xi_Term s) = ren_Term rho_Term s :=
  match s with
  | VarTm s0 => ap (VarTm) (Eq_Term s0)
  | ISort s0 => congr_ISort (eq_refl s0)
  | Abs s0 s1 =>
      congr_Abs (compRenRen_Term xi_Term zeta_Term rho_Term Eq_Term s0)
        (compRenRen_Term (upRen_Term_Term xi_Term)
           (upRen_Term_Term zeta_Term) (upRen_Term_Term rho_Term)
           (up_ren_ren _ _ _ Eq_Term) s1)
  | App s0 s1 =>
      congr_App (compRenRen_Term xi_Term zeta_Term rho_Term Eq_Term s0)
        (compRenRen_Term xi_Term zeta_Term rho_Term Eq_Term s1)
  | Pi s0 s1 =>
      congr_Pi (compRenRen_Term xi_Term zeta_Term rho_Term Eq_Term s0)
        (compRenRen_Term (upRen_Term_Term xi_Term)
           (upRen_Term_Term zeta_Term) (upRen_Term_Term rho_Term)
           (up_ren_ren _ _ _ Eq_Term) s1)
  end.

Lemma up_ren_subst_Term_Term (xi : nat -> nat) (tau : nat -> Term)
  (theta : nat -> Term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_Term_Term tau) (upRen_Term_Term xi) x = up_Term_Term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_Term (xi_Term : nat -> nat) (tau_Term : nat -> Term)
(theta_Term : nat -> Term)
(Eq_Term : forall x, funcomp tau_Term xi_Term x = theta_Term x) (s : Term)
{struct s} :
subst_Term tau_Term (ren_Term xi_Term s) = subst_Term theta_Term s :=
  match s with
  | VarTm s0 => Eq_Term s0
  | ISort s0 => congr_ISort (eq_refl s0)
  | Abs s0 s1 =>
      congr_Abs (compRenSubst_Term xi_Term tau_Term theta_Term Eq_Term s0)
        (compRenSubst_Term (upRen_Term_Term xi_Term) (up_Term_Term tau_Term)
           (up_Term_Term theta_Term) (up_ren_subst_Term_Term _ _ _ Eq_Term)
           s1)
  | App s0 s1 =>
      congr_App (compRenSubst_Term xi_Term tau_Term theta_Term Eq_Term s0)
        (compRenSubst_Term xi_Term tau_Term theta_Term Eq_Term s1)
  | Pi s0 s1 =>
      congr_Pi (compRenSubst_Term xi_Term tau_Term theta_Term Eq_Term s0)
        (compRenSubst_Term (upRen_Term_Term xi_Term) (up_Term_Term tau_Term)
           (up_Term_Term theta_Term) (up_ren_subst_Term_Term _ _ _ Eq_Term)
           s1)
  end.

Lemma up_subst_ren_Term_Term (sigma : nat -> Term) (zeta_Term : nat -> nat)
  (theta : nat -> Term)
  (Eq : forall x, funcomp (ren_Term zeta_Term) sigma x = theta x) :
  forall x,
  funcomp (ren_Term (upRen_Term_Term zeta_Term)) (up_Term_Term sigma) x =
  up_Term_Term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_Term shift (upRen_Term_Term zeta_Term)
                (funcomp shift zeta_Term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_Term zeta_Term shift (funcomp shift zeta_Term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_Term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_Term (sigma_Term : nat -> Term)
(zeta_Term : nat -> nat) (theta_Term : nat -> Term)
(Eq_Term : forall x, funcomp (ren_Term zeta_Term) sigma_Term x = theta_Term x)
(s : Term) {struct s} :
ren_Term zeta_Term (subst_Term sigma_Term s) = subst_Term theta_Term s :=
  match s with
  | VarTm s0 => Eq_Term s0
  | ISort s0 => congr_ISort (eq_refl s0)
  | Abs s0 s1 =>
      congr_Abs
        (compSubstRen_Term sigma_Term zeta_Term theta_Term Eq_Term s0)
        (compSubstRen_Term (up_Term_Term sigma_Term)
           (upRen_Term_Term zeta_Term) (up_Term_Term theta_Term)
           (up_subst_ren_Term_Term _ _ _ Eq_Term) s1)
  | App s0 s1 =>
      congr_App
        (compSubstRen_Term sigma_Term zeta_Term theta_Term Eq_Term s0)
        (compSubstRen_Term sigma_Term zeta_Term theta_Term Eq_Term s1)
  | Pi s0 s1 =>
      congr_Pi (compSubstRen_Term sigma_Term zeta_Term theta_Term Eq_Term s0)
        (compSubstRen_Term (up_Term_Term sigma_Term)
           (upRen_Term_Term zeta_Term) (up_Term_Term theta_Term)
           (up_subst_ren_Term_Term _ _ _ Eq_Term) s1)
  end.

Lemma up_subst_subst_Term_Term (sigma : nat -> Term) (tau_Term : nat -> Term)
  (theta : nat -> Term)
  (Eq : forall x, funcomp (subst_Term tau_Term) sigma x = theta x) :
  forall x,
  funcomp (subst_Term (up_Term_Term tau_Term)) (up_Term_Term sigma) x =
  up_Term_Term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_Term shift (up_Term_Term tau_Term)
                (funcomp (up_Term_Term tau_Term) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_Term tau_Term shift
                      (funcomp (ren_Term shift) tau_Term) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_Term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_Term (sigma_Term : nat -> Term)
(tau_Term : nat -> Term) (theta_Term : nat -> Term)
(Eq_Term : forall x,
           funcomp (subst_Term tau_Term) sigma_Term x = theta_Term x)
(s : Term) {struct s} :
subst_Term tau_Term (subst_Term sigma_Term s) = subst_Term theta_Term s :=
  match s with
  | VarTm s0 => Eq_Term s0
  | ISort s0 => congr_ISort (eq_refl s0)
  | Abs s0 s1 =>
      congr_Abs
        (compSubstSubst_Term sigma_Term tau_Term theta_Term Eq_Term s0)
        (compSubstSubst_Term (up_Term_Term sigma_Term)
           (up_Term_Term tau_Term) (up_Term_Term theta_Term)
           (up_subst_subst_Term_Term _ _ _ Eq_Term) s1)
  | App s0 s1 =>
      congr_App
        (compSubstSubst_Term sigma_Term tau_Term theta_Term Eq_Term s0)
        (compSubstSubst_Term sigma_Term tau_Term theta_Term Eq_Term s1)
  | Pi s0 s1 =>
      congr_Pi
        (compSubstSubst_Term sigma_Term tau_Term theta_Term Eq_Term s0)
        (compSubstSubst_Term (up_Term_Term sigma_Term)
           (up_Term_Term tau_Term) (up_Term_Term theta_Term)
           (up_subst_subst_Term_Term _ _ _ Eq_Term) s1)
  end.

Lemma renRen_Term (xi_Term : nat -> nat) (zeta_Term : nat -> nat) (s : Term)
  :
  ren_Term zeta_Term (ren_Term xi_Term s) =
  ren_Term (funcomp zeta_Term xi_Term) s.
Proof.
exact (compRenRen_Term xi_Term zeta_Term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Term_pointwise (xi_Term : nat -> nat) (zeta_Term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_Term zeta_Term) (ren_Term xi_Term))
    (ren_Term (funcomp zeta_Term xi_Term)).
Proof.
exact (fun s => compRenRen_Term xi_Term zeta_Term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Term (xi_Term : nat -> nat) (tau_Term : nat -> Term)
  (s : Term) :
  subst_Term tau_Term (ren_Term xi_Term s) =
  subst_Term (funcomp tau_Term xi_Term) s.
Proof.
exact (compRenSubst_Term xi_Term tau_Term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Term_pointwise (xi_Term : nat -> nat) (tau_Term : nat -> Term)
  :
  pointwise_relation _ eq (funcomp (subst_Term tau_Term) (ren_Term xi_Term))
    (subst_Term (funcomp tau_Term xi_Term)).
Proof.
exact (fun s => compRenSubst_Term xi_Term tau_Term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Term (sigma_Term : nat -> Term) (zeta_Term : nat -> nat)
  (s : Term) :
  ren_Term zeta_Term (subst_Term sigma_Term s) =
  subst_Term (funcomp (ren_Term zeta_Term) sigma_Term) s.
Proof.
exact (compSubstRen_Term sigma_Term zeta_Term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Term_pointwise (sigma_Term : nat -> Term)
  (zeta_Term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_Term zeta_Term) (subst_Term sigma_Term))
    (subst_Term (funcomp (ren_Term zeta_Term) sigma_Term)).
Proof.
exact (fun s => compSubstRen_Term sigma_Term zeta_Term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Term (sigma_Term : nat -> Term) (tau_Term : nat -> Term)
  (s : Term) :
  subst_Term tau_Term (subst_Term sigma_Term s) =
  subst_Term (funcomp (subst_Term tau_Term) sigma_Term) s.
Proof.
exact (compSubstSubst_Term sigma_Term tau_Term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Term_pointwise (sigma_Term : nat -> Term)
  (tau_Term : nat -> Term) :
  pointwise_relation _ eq
    (funcomp (subst_Term tau_Term) (subst_Term sigma_Term))
    (subst_Term (funcomp (subst_Term tau_Term) sigma_Term)).
Proof.
exact (fun s =>
       compSubstSubst_Term sigma_Term tau_Term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Term_Term (xi : nat -> nat) (sigma : nat -> Term)
  (Eq : forall x, funcomp (VarTm) xi x = sigma x) :
  forall x, funcomp (VarTm) (upRen_Term_Term xi) x = up_Term_Term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_Term (xi_Term : nat -> nat) (sigma_Term : nat -> Term)
(Eq_Term : forall x, funcomp (VarTm) xi_Term x = sigma_Term x) (s : Term)
{struct s} : ren_Term xi_Term s = subst_Term sigma_Term s :=
  match s with
  | VarTm s0 => Eq_Term s0
  | ISort s0 => congr_ISort (eq_refl s0)
  | Abs s0 s1 =>
      congr_Abs (rinst_inst_Term xi_Term sigma_Term Eq_Term s0)
        (rinst_inst_Term (upRen_Term_Term xi_Term) (up_Term_Term sigma_Term)
           (rinstInst_up_Term_Term _ _ Eq_Term) s1)
  | App s0 s1 =>
      congr_App (rinst_inst_Term xi_Term sigma_Term Eq_Term s0)
        (rinst_inst_Term xi_Term sigma_Term Eq_Term s1)
  | Pi s0 s1 =>
      congr_Pi (rinst_inst_Term xi_Term sigma_Term Eq_Term s0)
        (rinst_inst_Term (upRen_Term_Term xi_Term) (up_Term_Term sigma_Term)
           (rinstInst_up_Term_Term _ _ Eq_Term) s1)
  end.

Lemma rinstInst'_Term (xi_Term : nat -> nat) (s : Term) :
  ren_Term xi_Term s = subst_Term (funcomp (VarTm) xi_Term) s.
Proof.
exact (rinst_inst_Term xi_Term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Term_pointwise (xi_Term : nat -> nat) :
  pointwise_relation _ eq (ren_Term xi_Term)
    (subst_Term (funcomp (VarTm) xi_Term)).
Proof.
exact (fun s => rinst_inst_Term xi_Term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Term (s : Term) : subst_Term (VarTm) s = s.
Proof.
exact (idSubst_Term (VarTm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Term_pointwise :
  pointwise_relation _ eq (subst_Term (VarTm)) id.
Proof.
exact (fun s => idSubst_Term (VarTm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Term (s : Term) : ren_Term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Term s) (rinstInst'_Term id s)).
Qed.

Lemma rinstId'_Term_pointwise : pointwise_relation _ eq (@ren_Term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_Term s) (rinstInst'_Term id s)).
Qed.

Lemma varL'_Term (sigma_Term : nat -> Term) (x : nat) :
  subst_Term sigma_Term (VarTm x) = sigma_Term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Term_pointwise (sigma_Term : nat -> Term) :
  pointwise_relation _ eq (funcomp (subst_Term sigma_Term) (VarTm))
    sigma_Term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Term (xi_Term : nat -> nat) (x : nat) :
  ren_Term xi_Term (VarTm x) = VarTm (xi_Term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Term_pointwise (xi_Term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Term xi_Term) (VarTm))
    (funcomp (VarTm) xi_Term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_Term X Y :=
    up_Term : X -> Y.

#[global]Instance Subst_Term : (Subst1 _ _ _) := @subst_Term.

#[global]Instance Up_Term_Term : (Up_Term _ _) := @up_Term_Term.

#[global]Instance Ren_Term : (Ren1 _ _ _) := @ren_Term.

#[global]
Instance VarInstance_Term : (Var _ _) := @VarTm.

Notation "[ sigma_Term ]" := (subst_Term sigma_Term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_Term ]" := (subst_Term sigma_Term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Term" := up_Term (only printing)  : subst_scope.

Notation "↑__Term" := up_Term_Term (only printing)  : subst_scope.

Notation "⟨ xi_Term ⟩" := (ren_Term xi_Term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_Term ⟩" := (ren_Term xi_Term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := VarTm ( at level 1, only printing)  : subst_scope.

Notation "x '__Term'" := (@ids _ _ VarInstance_Term x)
( at level 5, format "x __Term", only printing)  : subst_scope.

Notation "x '__Term'" := (VarTm x) ( at level 5, format "x __Term")  :
subst_scope.

#[global]
Instance subst_Term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Term)).
Proof.
exact (fun f_Term g_Term Eq_Term s t Eq_st =>
       eq_ind s (fun t' => subst_Term f_Term s = subst_Term g_Term t')
         (ext_Term f_Term g_Term Eq_Term s) t Eq_st).
Qed.

#[global]
Instance subst_Term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Term)).
Proof.
exact (fun f_Term g_Term Eq_Term s => ext_Term f_Term g_Term Eq_Term s).
Qed.

#[global]
Instance ren_Term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Term)).
Proof.
exact (fun f_Term g_Term Eq_Term s t Eq_st =>
       eq_ind s (fun t' => ren_Term f_Term s = ren_Term g_Term t')
         (extRen_Term f_Term g_Term Eq_Term s) t Eq_st).
Qed.

#[global]
Instance ren_Term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Term)).
Proof.
exact (fun f_Term g_Term Eq_Term s => extRen_Term f_Term g_Term Eq_Term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_Term, Var, ids, Ren_Term, Ren1, ren1,
                      Up_Term_Term, Up_Term, up_Term, Subst_Term, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_Term, Var, ids,
                                            Ren_Term, Ren1, ren1,
                                            Up_Term_Term, Up_Term, up_Term,
                                            Subst_Term, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_Term_pointwise
                 | progress setoid_rewrite substSubst_Term
                 | progress setoid_rewrite substRen_Term_pointwise
                 | progress setoid_rewrite substRen_Term
                 | progress setoid_rewrite renSubst_Term_pointwise
                 | progress setoid_rewrite renSubst_Term
                 | progress setoid_rewrite renRen'_Term_pointwise
                 | progress setoid_rewrite renRen_Term
                 | progress setoid_rewrite varLRen'_Term_pointwise
                 | progress setoid_rewrite varLRen'_Term
                 | progress setoid_rewrite varL'_Term_pointwise
                 | progress setoid_rewrite varL'_Term
                 | progress setoid_rewrite rinstId'_Term_pointwise
                 | progress setoid_rewrite rinstId'_Term
                 | progress setoid_rewrite instId'_Term_pointwise
                 | progress setoid_rewrite instId'_Term
                 | progress unfold up_Term_Term, upRen_Term_Term, up_ren
                 | progress cbn[subst_Term ren_Term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_Term, Var, ids, Ren_Term, Ren1, ren1,
                  Up_Term_Term, Up_Term, up_Term, Subst_Term, Subst1, subst1
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_Term_pointwise;
                  try setoid_rewrite rinstInst'_Term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_Term_pointwise;
                  try setoid_rewrite_left rinstInst'_Term.

End Core.

Module Extra.

Import Core.

#[global]Hint Opaque subst_Term: rewrite.

#[global]Hint Opaque ren_Term: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

