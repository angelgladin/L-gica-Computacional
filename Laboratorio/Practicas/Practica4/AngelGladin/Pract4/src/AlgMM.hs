module AlgMM where

import LPO
import LPOSust
import Data.List

-- | simpSus. Función que elimina los pares con componentes iguales correspon-
-- dientes de la forma x := x.
simpSus :: Subst -> Subst
simpSus = foldl (\acc x -> if not $ eq' (fst x) (snd x) then x : acc else acc) []
  where eq' x (V ind)
          | x == ind = True
          | otherwise = False
        eq' x _ = False

-- | compSus. Función que dads dos sustituciones devuelve la composición.
compSus :: Subst -> Subst -> Subst 
compSus s1 s2 = simpSus [(x, apsubT t s2) | (x,t) <- s1] ++
                [(x2, t2) | (x2,t2) <- s2, notElem x2 [fst s | s <- s1]]

-- | unifica. Función que dados dos términos devuelve una lista de sustituciones
-- de tal forma que: 
-- Si t1, t2 no son unificables, la lista es vacía.
-- En caso contrario, la lista contiene como único elemento al unificador correspondiente.
unifica :: Term -> Term -> [Subst]
unifica (V x1) (V x2) = if x1 == x2 then [] else [[(x1,V x2)]] 
unifica (V x) t = if notElem x (varT t) then [[(x,t)]] else []
unifica t (V x) = unifica (V x) t
unifica (F f1 t1) (F f2 t2) = [t | f1 == f2, t <- unificaListas t1 t2]
        
-- | unificaListas. Función que sirve para cuando t1 y t2 son funciones, unifique los
-- términos de ellas de la misma longitud.
unificaListas :: [Term] -> [Term] -> [Subst]
unificaListas [] [] = [[]]
unificaListas [] xs = [[]]
unificaListas xs [] = [[]]
unificaListas (x:xs) (y:ys) = [compSus t r | r <- unifica x y, t <- unificaListas [apsubT t1 r | t1 <- xs] [apsubT t2 r | t2 <- ys]]

-- | unificaConj. Función que hace lo mismo que `unifica` sólo que de forma más general. 
unificaConj :: [Term] -> [Subst]
unificaConj [] = [[]]
unificaConj [x] = [[]]
unificaConj ts = nub $ concat [unifica t1 t2| t1 /= t2, t1 <- ts, t2 <- ts]

-- | unificaLit. Función que unifica dos literales.
unificaLit :: Form -> Form -> [Subst]
unificaLit (Pr n1 t1) (Pr n2 t2) = if n1 == n2 then unificaListas t1 t2 else []
