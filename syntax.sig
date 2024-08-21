Tm(VarTm) : Type
Ty(VarTy) : Type
CTm(VarCTm) : Type

Ki : Type
CSort : Type

TmAbs : (bind Tm in Tm) -> Tm
TmApp : Tm -> Tm -> Tm

TyAbs : Ki -> (bind Ty in Ty) -> Ty
TyApp : Ty -> Ty -> Ty
TyForall : Ki -> (bind Ty in Ty) -> Ty
TyFun : Ty -> Ty -> Ty

Star : Ki
Arr : Ki -> Ki -> Ki

CStar : CSort
CKind : CSort

CTmAbs : (bind CTm in CTm) -> CTm
CTmApp : CTm -> CTm -> CTm
CTmForall : CTm -> (bind CTm in CTm) -> CTm
CTmSort : CSort -> CTm