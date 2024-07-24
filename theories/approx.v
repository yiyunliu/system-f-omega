Require Export imports.

Inductive Skel : Set :=
| SK_Star : Skel
| SK_Arr : Skel -> Skel -> Skel.

Inductive Cls : Set :=
| C_Kind : Skel -> Cls
| C_Type : Skel -> Cls
| C_Term : Cls.

Fixpoint cl_term Σ a : Cls :=
  match a with
  | ISort _ => C_Kind SK_Star
  | VarTm i => match nth_error Σ i with
              | Some (C_Kind sk) => C_Type sk
              | _ => C_Term
              end
  | Abs A a => match cl_term Σ A , cl_term (cl_term Σ A :: Σ) a with
              | _, C_Kind _ => C_Kind SK_Star
              | C_Kind sk1, C_Type sk2 => C_Type (SK_Arr sk1 sk2)
              | _, c => c
              end
  | App a b => match cl_term Σ a, cl_term Σ b with
              | C_Kind _, _ => C_Kind SK_Star
              | C_Type (SK_Arr sk1 sk2), C_Type _ => C_Type sk2
              | c, _ => c
              end
  | Pi A B => match cl_term Σ A, cl_term (cl_term Σ A::Σ) B with
             | C_Kind sk1, C_Kind sk2 => C_Kind (SK_Arr sk1 sk2)
             | _, c => c
             end
  end.
