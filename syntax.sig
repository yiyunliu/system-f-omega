Sort : Type
Term(VarTm) : Type

Kind : Sort
Star : Sort

ISort : Sort -> Term
Abs : Term -> (bind Term in Term) -> Term
App : Term -> Term -> Term
Pi : Term -> (bind Term in Term) -> Term