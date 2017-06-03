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

module Cesar where

import Data.Char

-- | alf. Función que recibe una letra mayúscula y devuelve el entero
-- correspondiente a la posición del alfabeto latino.
-- --> alf 'A' = 0
-- --> alf 'Z' = 25
alf :: Char -> Int
alf char
    | num >= 65 && num <= 90 = num - 65
    | otherwise              = error "Sólo debe recibir mayúsculas" 
    where num = ord char

-- | hashDeSuetonio. Función que recibe un entero que representa la
-- posición de una letra de acuerdo al alfabeto latino y devuelve
-- la posición de acuerdo a la función hash descrita por Suetonio.
-- --> hashDeSuetonio 4 = 7
-- --> hashDeSuetonio 0 = 3
hashDeSuetonio :: Int -> Int
hashDeSuetonio n = (n + 3) `mod` 25

-- | cifra. Función que recibe una cadena y devuelve una
-- cadena con el texto cifrado.
-- Esta función fue currificada ya que la función `foldr` recibe
-- una función, un acumulador y una lista, y haciendo la función
-- `cifra` currifucada se aplica esta función a una lista dada.
-- Se hizo el uso de pliegues para poder recorrer la lista y 
-- acumular "el resultado" en un acumulador.
-- Se hizo el uso de lambdas (el primer parámetro de `foldr`).
-- Se utilizó `.` para hacer composición de funciones y
-- `$` para dar menor orden de precedencia.
-- --> cifra "Logica computacional" = "ORJLFD FRPSXWDFLRQDO"
-- --> cifra ['a'..'z']             = "DEFGHIJKLMNOPQRSTUVWXYABCD"
cifra :: String -> String
cifra = foldr (\x acc -> if isAlpha x
                               then convierteLetra x : acc
                               else x : acc) []
    where convierteLetra x = chr $ (hashDeSuetonio . alf $ toUpper x) + 65
