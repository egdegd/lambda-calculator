import Data.List

type Symb = String 
infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)


freeVars :: Expr -> [Symb]
freeVars (Var s) = [s]
freeVars (e1 :@ e2) = union (freeVars e1) (freeVars e2)
freeVars (Lam x e) = delete x (freeVars e) 


subst :: Symb -> Expr -> Expr -> Expr 
subst v n (Var s) = if (s == v) then n else (Var s)
subst v n (e1 :@ e2) = (subst v n e1) :@ (subst v n e2)
subst v n (Lam x e) | v == x                = (subst v n (replace_for_smth (Lam x e)))
                    | (elem x (freeVars n)) = (subst v n (replace_for_smth (Lam x e))) 
                    | otherwise             = (Lam x (subst v n e))

replace_for :: Expr -> Symb -> Expr
replace_for (Lam x e) s = (Lam (s) (subst x (Var (s) ) e))


replace_for_smth :: Expr -> Expr
replace_for_smth (Lam x e) = replace_for (Lam x e) (x ++ "'")

infix 1 `alphaEq`

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var s1) (Var s2) = s1 == s2
alphaEq (e1 :@ e2) (e3 :@ e4) = ((e1 `alphaEq` e3) && (e2 `alphaEq` e4)) || ((e1 `alphaEq` e4) && (e2 `alphaEq` e3))
alphaEq (Lam x e1) (Lam y e2) | x == y = e1 `alphaEq` e2
                              | otherwise = ((Lam x e1) `alphaEq` new_e2) && ((Lam y e2) `alphaEq` new_e3) 
                                where new_e2 = replace_for (Lam y e2) x
                                      new_e3 = replace_for (Lam x e1) y
alphaEq _ _ = False


expr:: (Maybe Expr) -> Expr
expr (Just e) = e

reduceOnce :: Expr ->  Maybe Expr
reduceOnce (Var s) = Nothing
reduceOnce ((Lam x e1) :@ e2) = Just (subst x e2 e1)
reduceOnce (Lam x e) = if (reduceOnce e == Nothing) then Nothing else Just (Lam x (expr (reduceOnce e)))
reduceOnce (e1 :@ e2) | reduceOnce e1 == Nothing && reduceOnce e2 == Nothing = Nothing
                      | reduceOnce e1 == Nothing                             = Just $ e1 :@ expr (reduceOnce e2)
                      | otherwise                                            = Just $ expr (reduceOnce e1) :@ e2


nf :: Expr -> Expr 
nf e = if (reduceOnce e == Nothing) then e else nf (expr (reduceOnce e))


infix 1 `betaEq`

betaEq :: Expr -> Expr -> Bool 
betaEq e1 e2 = (nf e1) `alphaEq` (nf e2)
