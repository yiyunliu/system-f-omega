Require Import coctyping imports.


Fixpoint compile_kind_error a  :=
  match a with
  | CTmSort CStar => Some Star
  | CTmForall A B =>
      match compile_kind_error A, compile_kind_error B with
      | Some k0, Some k1 => Some (Arr k0 k1)
      | None, Some k => Some k
      | _ , _ => None
      end
  | _ => None
  end.

Definition compile_kind a := ssrfun.Option.default Star (compile_kind_error a).

Definition KindP Γ U := Wt Γ U (CTmSort CKind).

Definition TypeP Γ A := Wt Γ A (CTmSort CStar).

Definition TyConP Γ A := exists U, Wt Γ A U /\ KindP Γ U.

Definition ObjectP Γ a := exists A, Wt Γ a A /\ TypeP Γ A.


Inductive CompileKind : CTm -> Ki -> Prop :=
| CK_Star :
  CompileKind (CTmSort CStar) Star
| CK_ForallKi A k0 B k1:
  CompileKind A k0 ->
  CompileKind B k1 ->
  CompileKind (CTmForall A B) (Arr k0 k1)
| CK_ForallTy Γ A B k:
  TypeP Γ A ->
  CompileKind B k ->
  CompileKind (CTmForall A B) k.

Hint Unfold compile_kind : core.

Hint Constructors CompileKind : ck.

Inductive CompileTyCon Γ ξ : CTm -> Ty -> Prop :=
| CT_Var i :
  CompileTyCon Γ ξ (VarCTm i) (VarTy (ξ i))

| CT_ForallKi A k B T :
  CompileKind A k ->
  CompileTyCon (A :: Γ) (upRen_Ty_Ty ξ) B T ->
  CompileTyCon Γ ξ (CTmForall A B) (TyForall k T)

| CT_ForallTy A B T0 T1 :
  CompileTyCon Γ ξ A T0 ->
  CompileTyCon (A :: Γ) (0 .: ξ) B T1 ->
  CompileTyCon Γ ξ (CTmForall A B) (TyFun T0 T1)

| CT_AbsKi a A k B T :
  Wt (A :: Γ) a B ->
  CompileKind A k ->
  CompileTyCon (A :: Γ) (upRen_Ty_Ty ξ) a T ->
  CompileTyCon Γ ξ (CTmAbs a) (TyAbs k T).
