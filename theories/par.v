Require Export imports.

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

Inductive Red : Tm -> Tm -> Prop :=
| R_App a0 a1 b :
  Red a0 a1 ->
  Red (TmApp a0 b) (TmApp a1 b)
| R_AppAbs a b :
  Red (TmApp (TmAbs b) a) (subst_Tm (a …) b).

Record CR (R : Tm -> Tm -> Prop) : Prop := CR_intro
  { CR1a : forall a0 a1 b, Red a0 a1 -> R a1 b -> R a0 b
  ; CR1b : forall a b0 b1, Red b0 b1 -> R a b1 -> R a b0
  ; CR2 : forall a a' b b', R a a' -> R b b' -> R b a' -> R a b'}.

Lemma CR1 R : CR R -> forall a0 a1 b0 b1, Red a0 a1 -> Red b0 b1 -> R a1 b1 -> R a0 b0.
Proof. hauto lq:on inv:CR. Qed.

Hint Constructors CR Red : rdb.

Module red_props.

  Lemma CR_Op R0 R1 : (forall a b, R0 a b <-> R1 b a) -> CR R0 -> CR R1.
  Proof. hauto lq:on rew:off ctrs:CR inv:CR. Qed.

  Lemma CR_Prod R0 R1 : CR R0 -> CR R1 ->
         CR (fun b0 b1 => forall a0 a1, R0 a0 a1 -> R1 (TmApp b0 a0) (TmApp b1 a1)).
  Proof.
    hauto l:on ctrs:CR inv:CR.
  Qed.

  Lemma CR_Forall {A} (x : A) (P : A -> Prop) (_ : P x) F : (forall a : A, P a -> CR (F a)) -> CR (fun b0 b1 => forall a, P a -> F a b0 b1).
  Proof.
    hauto q:on ctrs:CR inv:CR.
  Qed.

End red_props.
