{-
 -Logica Computacional 2017-2
 -Tema : Implementacion de la sustitución.
 -Profesor: Lourdes del Carmen Gonzaléz Huesca
 -Ayudante: Roberto Monroy Argumedo
 -Laboratorio: Fernando A. Galicia Mendoza
-}
module LPOSust where

import LPO
import Data.List

-- | Subst. Tipo que representa una sustitución de variables en términos.
type Subst = [(Ind,Term)]

-- | elimRep. Función que elimina los elementos repetidos de una lista.
elimRep :: Eq a => [a] -> [a]
elimRep l = eR_aux l [] where
  eR_aux [] c = c
  eR_aux (x:xs) c
    | elem x c = eR_aux xs c
    | otherwise = eR_aux xs (c++[x])

-- | verifSus. Función que verifica una sustitución.
verifSus :: Subst -> Bool
verifSus s = elimRep [i | (i,t) <- s] == [i | (i,t) <- s]

-- | apsubTaux. Función auxiliar que aplica una sustitución de variables en términos
-- en un término.
apsubTaux :: Term -> Subst -> Term
apsubTaux (V x) sus = case sus of
  [] -> V x
  (s:ss) -> if fst s == x then snd s else apsubTaux (V x) ss
apsubTaux (F c []) _ = F c []
apsubTaux (F f ts) s = F f (apsubTL_aux ts s) where
  apsubTL_aux [] s = []
  apsubTL_aux (t:ts) s = ((apsubTaux t s):apsubTL_aux ts s)
  
-- | apsubT. Función que aplica una sustitución de variables de variables en términos
-- en un término dado.
apsubT :: Term -> Subst -> Term
apsubT t s = if verifSus s then apsubTaux t s else error "Sustitución no legal."

--Ejemplos:

--Considerese los siguientes terminos.
t1 = F "f" [V 1,F "c" [],V 3]
t2 = F "g" [t1,V 2]
t3 = F "d" []
t4 = F "h" [V 6,V 1]

--Se realizan las siguientes sustituciones validas.
sust1 = apsubT t2 [(2,t3),(1,t4)]
sust2 = apsubT t4 [(1,t1)]
sust3 = apsubT t2 [(1,t2)]

--La siguiente sustitución es inválida.
sustInv1 = apsubT t2 [(2,t3),(2,t4)]
sustInv2 = apsubT t3 [(1,V 1),(2,V 3),(1,V 4)]
