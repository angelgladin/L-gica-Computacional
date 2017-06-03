-- Dadas las variables x1,...,xm y v1,...,vn elementos del universo U el estado o modificado en x1,...,xm
-- esta definido en x1,...,xm esta definido por:
-- sigma[x`/v`](y)={ sigma(y) si y esta en A 	&	 mi si y=xi
module LPOSem where

import LPO

-- | IntF. Tipo que representa una interpretacion de funciones.
type IntF a = Nombre -> [a] -> a
-- | IntR. Tipo que representa una interpretacion de relaciones.
type IntR a = Nombre -> [a] -> Bool
-- | Estado. Tipo que representa el estado de una variable del universo.
type Estado a = Ind -> a
-- | Mundo. Tipo que representa un mundo.
type Mundo a = (Estado a, IntF a, IntR a)

actEstados:: Estado a -> Ind -> a -> Estado a
actEstados e x v y  
				| x == y  = v
				| otherwise = e x

iTerm :: Term -> Estado a -> IntF a -> a
iTerm (V x) e i = e x
iTerm (F c []) e i = i c []
iTerm (F f ts) e i = i f (aux e i ts) where 
											aux _ _ [] = []
											aux e i (t:ts)= (iTerm t e i):(aux e i ts)

-- | Dado una formula, un mundo en un universo, regresa la interpretación de la formula en el mundo dado.
iForm :: Eq a => [a] -> Mundo a -> Form  -> Bool
iForm _ _ TrueF = True
iForm _ _ FalseF = False
iForm u (e, iF, iR) (Pr nom ts) = iR nom (aux ts) where
														aux [] = []
														aux (x:xs) = iTerm x e iF:(aux xs)
iForm u (e, iF, iR) (Neg f) = not (iForm u (e, iF, iR) f) 
iForm u (e, iF, iR) (Conj f1 f2) = (iForm u (e, iF, iR) f1) && (iForm (e, iF, iR) m f2)
iForm u (e, iF, iR) (Disy f1 f2) = (iForm u (e, iF, iR) f1) || (iForm (e, iF, iR) m f2)
iForm u (e, iF, iR) (Imp f1 f2) = (not(iForm u (e, iF, iR) f1)) ||(iForm (e, iF, iR) m f2)
iForm u (e, iF, iR) (Equi f1 f2) = (iForm u (e, iF, iR) (Imp f1 f2)) && (iForm (e, iF, iR) m (Imp f1 f2))
iForm u (e, iF, iR) (All x f) = and[iForm u (actEstados e x v, iF, iR ) (f) | v <- u]
iForm u (e, iF, iR) (Ex x f) = or[iForm u (actEstados e x v, iF, iR ) (f) | v <- u] 

