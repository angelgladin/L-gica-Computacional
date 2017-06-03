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

module Binario
( sucesor
, suma
, prod
) where

-- | BinarioPos. Tipo que representa un número binario. Es una 
-- estructura de dato recursiva que contine el número uno o 
-- el número que tiene hasta su derecha el primer número Cero
-- o Uno junto con un BinarioPos.
data BinarioPos = U 
                | Cero BinarioPos
                | Uno BinarioPos

-- Haciendo `instance Show BinarioPos` se logra que el tipo
-- de dato pueda ser representado de una forma más legible
-- en formato de una cadena que contiene o 1s ó 0s.
instance Show BinarioPos where
    show U        = "1"
    show (Cero x) = (show x) ++ "0"
    show (Uno x)  = (show x) ++ "1"

-- | sucesor. Función que dado un número binario regresa el
-- sucesor de dicho número.
-- --> sucesor $ Uno $ Uno U  = 1000
-- --> sucesor $ Cero $ Uno U = 1111
sucesor :: BinarioPos -> BinarioPos
sucesor U        = Cero U
sucesor (Cero x) = Uno x
sucesor (Uno x)  = Cero $ sucesor x

-- | suma. Función que dado dos números binarios regresa el
-- la suma de ambos números.
-- --> suma (Uno $ Uno $ Uno U) (Cero $ Uno U) = 10101
-- --> suma (Uno $ Uno U)       (Uno $ Uno U)  = 1110
suma :: BinarioPos -> BinarioPos -> BinarioPos
suma U U        = Cero U
suma (Cero x) U = Uno x
suma U (Cero x) = Uno x
suma (Uno x) U  = Cero $ suma x U
suma U (Uno x)  = Cero $ suma x U
suma (Cero x) (Uno y)  = Uno $ suma x y
suma (Uno x)  (Cero y) = Uno $ suma x y
suma (Cero x) (Cero y) = Cero $ suma x y
suma (Uno x)  (Uno y)  = Cero $ suma (suma x U) y

-- | prod. Función que dado dos números binarios regresa el
-- la producto de ambos números.
-- --> prod (Cero $ Uno $ Cero U) (Cero $ Uno $ Cero U) = 1100100
-- --> prod (Uno $ Uno U)         (Cero $ Cero U)       = 11100
prod :: BinarioPos -> BinarioPos -> BinarioPos
prod x U = x
prod U y = y
prod (Cero x) (Uno y)  = suma (Cero x) (aux (Cero $ Cero x) y)
prod (Uno x)  (Cero y) = prod (Cero y) (Uno x)
prod (Cero x) (Cero y) = Cero (prod (Cero x) (y))
prod (Uno x)  (Uno y)  = suma (Uno x) (aux (Cero $ Uno x) y)

-- | suma. Función auxiliar usada en la función `prod` que 
-- dado dos números binarios regresa una "suma recursiva".
aux :: BinarioPos -> BinarioPos -> BinarioPos
aux (Cero x) (Uno y)  = suma (Cero x) (aux (Cero $ Cero x) y)
aux (Cero x) (Cero y) = aux (Cero $ Cero x) y
aux (Cero x)  U       = Cero x
