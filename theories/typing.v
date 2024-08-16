Require Export par.

Definition TyBasis := list Ki.

Definition lookup {T} n (Δ : list T) :=
  nth_error Δ n.

Inductive Lookup {T} : nat -> list T -> T -> Type :=
| Here A Γ : Lookup 0 (A :: Γ) A
| There n Γ A B : Lookup n Γ A ->
                     Lookup (S n) (cons B Γ) A.

Lemma LookupIff {T} n (Γ : list T) A : Lookup n Γ A -> lookup n Γ = Some A.
Proof.
  elim; hauto lq:on.
Qed.

Inductive TyWt Δ : Ty -> Ki -> Type :=
| TyT_Var i k :
  Lookup i Δ k ->
  TyWt Δ (VarTy i) k

| TyT_Abs A k0 k1 :
  TyWt (k0 :: Δ) A k1 ->
  TyWt Δ (TyAbs k0 A) (Arr k0 k1)

| TyT_App b a k0 k1 :
  TyWt Δ b (Arr k0 k1) ->
  TyWt Δ a k0 ->
  TyWt Δ (TyApp b a) k1

| TyT_Fun A B :
  TyWt Δ A Star ->
  TyWt Δ B Star ->
  TyWt Δ (TyFun A B) Star

| TyT_Forall k A :
  TyWt (k :: Δ) A Star ->
  TyWt Δ (TyForall k A) Star.

Definition TmBasis := list Ty.

Lemma lookup_functional {U} n (Γ : list U) A B : Lookup n Γ A -> Lookup n Γ B -> A = B.
Proof. hauto l:on inv:Lookup use:LookupIff. Qed.

Derive Inversion lookup_inv with (forall {U} i (Γ : list U) A, Lookup i Γ A) Sort Prop.

Definition BasisWf Δ Γ := forall i A, Lookup i Γ A -> TyWt Δ A Star.

Fixpoint up_Basis Γ :=
  match Γ with
  | nil => nil
  | A :: Γ => ren_Ty S A :: up_Basis Γ
  end.

Inductive Wt Δ Γ : Tm -> Ty -> Type :=
| T_Var i A :
  BasisWf Δ Γ ->
  Lookup i Γ A ->
  (* ----------- *)
  Wt Δ Γ (VarTm i) A

| T_Abs A a B :
  TyWt Δ A Star ->
  Wt Δ (A :: Γ) a B ->
  (* -------------------- *)
  Wt Δ Γ (TmAbs a) (TyFun A B)

| T_App a b A B :
  Wt Δ Γ a A ->
  Wt Δ Γ b (TyFun A B) ->
  (* --------------- *)
  Wt Δ Γ (TmApp b a) B

| T_Forall k a A :
  Wt (k :: Δ) (up_Basis Γ) a A ->
  (* --------------------------- *)
  Wt Δ Γ a (TyForall k A)

| T_Inst k a A B :
  TyWt Δ B k ->
  Wt Δ Γ a (TyForall k A) ->
  (* ------------------------ *)
  Wt Δ Γ a (subst_Ty (B…) A)

| T_Conv a A B :
  Wt Δ Γ a A ->
  TyWt Δ B Star ->
  ICoherent A B ->
  (* ------------ *)
  Wt Δ Γ a B.
