{-
- Logica Computacional 2017-2
- Práctica 1: Introducción a Haskell
- Profesor: Dra. Lourdes del Carmen Gonzalez Huesca
- Ayudante: Roberto Monroy Argumedo
- Laboratorio: Fernando A. Galicia Mendoza
- Integrantes:
- Ángel Iván Gladín García
-   313112470
-   angelgladin@ciencias.unam.mx
-}

-- | C. Tipo de dato que representa los números complejos.
type C = (Double, Double)

-- | P2. Tipo que representa los polinomios de segundo grado 
-- en el campo de los numeros reales, es decir,
-- (a,b,c) representa ax^2+bx+c.
type P2 = (Double,Double,Double)

-- | R. Tipo que representa las dos posibles raices de un 
-- polinomio de segundo grado.
type R = (C,C)

-- | tieneRaicesReales. Función que recibe un polinomio de 
-- segundo grado y devuelve un valor booleano si tiene
-- raices reales.
-- --> soluciones (1, 4, -21) = True
-- --> soluciones (1,-4 , 13) = False
tieneRaicesReales :: P2 -> Bool
tieneRaicesReales (a, b, c)
    | (b^2) - (4*a*c) > 0 = True
    | otherwise           = False

-- | soluciones. Función que recibe un polinomio de
-- segundo grado y devulve un par consistente en las dos 
-- posibles raíces de un polinomio de segundo grado.
-- --> soluciones (1, 4, -21) = ((3.0,0.0),(-7.0,0.0))
-- --> soluciones (1,-4 , 13) = ((2.0,3.0),(2.0,-3.0))
soluciones :: P2 -> R
soluciones (a, b, c)
    | tieneRaicesReales (a, b, c) =
        ((raizPositiva (a, b, c), 0), (raizNegativa (a, b, c), 0))
    | otherwise = 
        ((parteReal, parteImaginaria), (parteReal, -parteImaginaria))
    where raizPositiva (a, b, c) = (-b + sqrt discriminante) / (2*a)
          raizNegativa (a, b, c) = (-b - sqrt discriminante) / (2*a)
          discriminante          = (b^2) - (4*a*c)
          parteReal              = (-b) / (2*a)
          parteImaginaria        = (sqrt $ abs discriminante) / (2*a)