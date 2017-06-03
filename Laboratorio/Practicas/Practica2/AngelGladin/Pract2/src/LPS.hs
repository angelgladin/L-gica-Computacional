{-
- Logica Computacional 2017-2
- Implementación de la semántica de lógica proposicional.
- Práctica 2: LP en Haskell
- Profesor: Dra. Lourdes del Carmen Gonzalez Huesca
- Ayudante: Roberto Monroy Argumedo
- Laboratorio: Fernando A. Galicia Mendoza
- Integrantes:
- Ángel Iván Gladín García
-   313112470
-   angelgladin@ciencias.unam.mx
- María Fernanda González Chávez
-   313036367
-   fernandagch@ciencias.unam.mx
-}

module LPS where

import LProp
import LConj

-- | Estado. Tipo que representa un estado de variables.
type Estado = [VarP]

-- | i. Implementación de la función de interpretación.
i :: Estado -> Prop -> Bool
i _ TTrue = True
i _ FFalse = False
i e (V x) = x `elem` e
i e (Neg p) = not (i e p)
i e (Conj p1 p2) = (i e p1) && (i e p2)
i e (Disy p1 p2) = (i e p1) || (i e p2)
i e (Imp p1 p2) = (not (i e p1)) || (i e p2)
i e (Equiv p1 p2) = (i e (Imp p1 p2)) && (i e (Imp p2 p1))

-- | vars. Función que devuelve el conjunto de variables proposicionales de una
-- fórmula.
vars :: Prop -> [VarP]
vars (V x) = [x]
vars (Neg p) = vars p
vars (Conj p1 p2) = union (vars p1) (vars p2)
vars (Disy p1 p2) = union (vars p1) (vars p2)
vars (Imp p1 p2) = union (vars p1) (vars p2)
vars (Equiv p1 p2) = union (vars p1) (vars p2)
vars _ = []

-- | estados. Función que devuelve todos los posibles estados de una fórmula.
estados :: Prop -> [Estado]
estados p = subconj $ vars p

-- | modelos. Función que devuelve todos los posibles modelos de una fórmula.
modelos :: Prop -> [Estado]
modelos p = [e | e <- estados p, i e p]

-- | tautologia. Función que indica si una fórmula es una tautología.
tautologia :: Prop -> Bool
tautologia p = equivL (estados p) (modelos p)

-- | satisfen. Función que determina si una fórmula es satisfacible en un
-- estado dado.
satisfen :: Estado -> Prop -> Bool
satisfen e p = i e p

-- | satisf. Función que determina si una fórmula es satisfacible.
satisf :: Prop -> Bool
satisf p = modelos p /= []

-- | insatisfen. Función que determina si una fórmula es insatisfacible en un
-- estado dado.
insatisfen :: Estado -> Prop -> Bool
insatisfen e p = not $ satisfen e p

-- | satisf. Función que determina si una fórmula es una contradicción.
contrad :: Prop -> Bool
contrad p = not $ satisf p

-- | equiv. Función que determina si dos fórmulas son equivalentes.
equiv :: Prop -> Prop -> Bool
equiv p1 p2 = tautologia (Equiv p1 p2)

-- | estadosConj. Función que recibe un conjunto de fórmulas <Prop>.
--				  Devuelve el conjunto de todos los posibles estados del
--				  conjunto de fórmulas.
estadosConj :: [Prop] ->[Estado]
estadosConj [] = []
estadosConj ( p : ps ) = union ( estados p ) ( estadosConj ps ) 

-- | modelosConj. Función que recibe un conjunto de fórmulas <Prop>.
--				  Devuelve el conjunto de todos los posibles modelos del
--				  conjunto de fórmulas.
modelosConj :: [Prop] -> [Estado]
modelosConj [] = []
modelosConj ( p : ps ) = union ( modelos p ) ( modelosConj ps ) 

-- | satisfenConj. Función que recibe una interpretación <e> y un 
--				   conjunto de fórmulas <Prop>.
--				   Devuelve <True> en caso de que el conjunto de
--				   fórmulas sea satisfacible en el estado dado.
satisfenConj :: Estado -> [Prop] -> Bool
satisfenConj e ( p : ps )  = (satisfen e p) && (satisfenConj e ps)

-- | satisfConj. Función que recibe un conjunto de fórmulas <Prop>.
--				 Devuelve <True> en caso de que el conjunto de
--				 fórmulas sea satisfacible.
satisfConj :: [Prop] -> Bool
satisfConj ( p : ps )  = ( satisf p )&&( satisfConj ps )

-- | insatisfenConj. Función que recibe una interpretación <e> y un 
--					 conjunto de fórmulas <Prop>.
--				     Devuelve <True> en caso de que el conjunto de
--				     fórmulas sea insatisfacible en el estado dado.
insatisfenConj :: Estado -> [Prop] -> Bool
insatisfenConj e ( p : ps )  = ( insatisfen e p )&&( insatisfenConj e ps  )

-- | insatisfConj. Función que recibe un conjunto de fórmulas <Prop>.
--			   Devuelve <True> en caso de que el conjunto de
--			   fórmulas sea insatisfacible.
insatisfConj :: [Prop] -> Bool
insatisfConj ( p : ps )  = ( not(satisf p ) )&&(insatisfConj ps )

