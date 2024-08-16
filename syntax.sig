Tm(VarTm) : Type
Ty(VarTy) : Type
Ki : Type

TmAbs : (bind Tm in Tm) -> Tm
TmApp : Tm -> Tm -> Tm

TyAbs : (bind Ty in Ty) -> Ty
TyApp : Ty -> Ty -> Ty
TyForall : Ki -> (bind Ty in Ty) -> Ty
TyFun : Ty -> Ty -> Ty

Star : Ki
Arr : Ki -> Ki -> Ki
