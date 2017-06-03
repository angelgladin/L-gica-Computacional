{-
- Logica Computacional 2017-2
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

module FNC where

import LProp


-- | nN. Función que recibe una fórmula proposicional <Prop>.
--		 Devuelve el número de negaciones aplicadas a fórmulas
--		 distintas de variables proposicionales y constantes
--		 booleanas.
nN :: Prop -> Int
nN TTrue = 0
nN FFalse = 0
nN (V x) = 0
nN (Neg p) = if peso p == 0 then 0 else 1 + nN(p)
nN (Conj p1 p2 ) = nN(p1)+nN(p2)
nN (Disy p1 p2 ) = nN(p1)+nN(p2)
nN (Imp p1 p2 ) = nN(p1)+nN(p2)
nN (Equiv p1 p2 ) = nN(p1)+nN(p2)


-- | fnn. Función que recibe una fórmula proposicional <Prop>.
--		  Devuelve úna fórmula equivalente tal que este en forma
--		  normal negativa.
fnn :: Prop -> Prop
fnn p = aplicaNeg( elimIE(p) )

-- <AUX>
-- | aplicaNeg. Función que recibe una fórmula proposicional <Prop>.
--				Devuelve una fórmula proposicional tal que la negación
--				solo se aplique a fórmulas atómicas.
aplicaNeg :: Prop -> Prop
aplicaNeg (TTrue) = TTrue
aplicaNeg (FFalse) = FFalse
aplicaNeg (V x) = ( V x )
aplicaNeg (Conj p1 p2) = ( Conj (aplicaNeg(p1)) (aplicaNeg(p2)) )
aplicaNeg (Disy p1 p2) = ( Disy (aplicaNeg(p1)) (aplicaNeg(p2)) )
aplicaNeg (Neg TTrue) = FFalse
aplicaNeg (Neg FFalse) = TTrue
aplicaNeg (Neg (V x) ) = ( Neg (V x) )
aplicaNeg (Neg (Neg p)) = aplicaNeg(p)
aplicaNeg (Neg ( Conj p1 p2 ) ) = ( Disy (aplicaNeg(Neg p1)) (aplicaNeg(Neg p2)) )
aplicaNeg (Neg ( Disy p1 p2 ) ) = ( Conj (aplicaNeg(Neg p1)) (aplicaNeg(Neg p2)) )


-- | cnf. Función que recibe una fórmula proposicional <Prop>.
--		  Devuelve una fórmula equivalente tal que esta en forma
--		  normal conjuntiva.
cnf :: Prop -> Prop
cnf p = sacarConj( fnn(p) )

-- <AUX>
-- | sacarConj. Función que recibe una fórmula proposicional <Prop>.
--				Devuelve una fórmula proposicional con conjunciones
--				como conectivos principales.
sacarConj :: Prop -> Prop
sacarConj (Disy p1 (Conj p2 p3) ) = ( Conj (sacarConj(Disy p1 p2)) (sacarConj(Disy p1 p3)) )
sacarConj (Disy (Conj p1 p2) p3 ) = ( Conj (sacarConj(Disy p1 p3)) (sacarConj(Disy p2 p3)) )