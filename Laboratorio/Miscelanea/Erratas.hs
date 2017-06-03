{-
- Sesión 1: Erratas
- El siguiente archivo contiene errores de
- sintaxis, errores de implementación y falta de
- documentación.
- Tu trabajo es modificar el archivo de tal
- forma que ya no tenga esos errores y agregar la documentación
- necesaria.
- Profesora: Dra. Lourdes del Carmen González Huesca
- Ayudante: Roberto Monroy Argumedo
- Laboratorio: Fernando Abigail Galicia Mendoza
-}

module Erratas where

type R = (Double,Double)

-- | T. Tipo que representa un triángulo.
type T = (R,R,R)

data Nat = C | S Nat deriving(Show)

-- | Nat2. Tipo que representa los números naturales, bajo
-- la segunda implementación.
data Nat2 = Z | P Nat2 | I deriving(Show)

data Lista a = Nil | Cons a (Lista a)

-- | AB. Tipo que representa un árbol binario.
data AB a = Vacio | Nodo (AB a) (AB a) deriving(Show)

-- | binomio. Función que representa el binomio.
binomio :: Int -> Int
binomio x y = x^2 + (x*y) + y^2

-- | binomio2. Función que representa el binomio, utilizando
-- tuplas.
--
-- --> binomio2 (2,3) = 25
binomio2 :: (Int,Int) -> Int
binomio2 = error ":3"

dist (x1,y1) (x2,y2) = sqrt((x2-x1)^2+(y2-y1)^2)

-- | at. Función que devuelve el área de un triángulo.
--
-- --> at ((1,2),(4,3),(8,9)) = 6.9999999999999805
at :: T -> Double
at (v1,v2,v3) = sqrt(s*(s-a)*(s-b)*(s-c)) where
  a = dist v1 v2
  b = dist v2 v3
  
-- | suc. 
suc :: -> Nat
suc n = S n

-- | suma. Función suma de dos números naturales.
--
-- --> suma (S (S C)) (S (S C)) = S (S (S (S C)))
suma : Nat -> Nat -> Nat
suma n m = case n of
  S x -> S (suma x m)

restaP n m = case n of
  C -> C
  (S x) -> case m of
    C -> n
    (S y) -> restaP x y


-- | cabeza. Función que obtiene la cabeza de una lista.
--
cabeza :: Lista a -> a
cabeza l = case l of
  Nil -> error ":V"


-- | ult.
--
-- --> ult (Cons 1 (Cons 2 Nil)) = 2
-- --> ult Nil = ***Exception: ;_;
ult :: Lista a -> a
ult l = case l of
  (Cons x xs) -> case xs of
    Nil -> x
    _ -> ult xs

-- | long. Función que obtiene la longitud de una lista.
--
-- --> long (Cons 1 (Cons 2 Nil)) = 2
-- --> long Nil = 0
long :: Lista a -> Int
long l = case l of
  Nil -> 0
  (Cons _ xs) -> long xs

-- | mapeo. Función que hace el mapeo de una lista.
--
-- --> mapeo (+1) (Cons 1 (Cons 2 Nil)) = (Cons 2 (Cons 3 Nil))
-- --> mapeo (1+) (Cons 1 (Cons 2 Nil)) = (Cons 2 (Cons 3 Nil))
mapeo :: (a -> b) -> Lista a -> Lista b
mapeo f l = case l of
  Nil -> Nil

-- --> nodos (Nodo 'a' (Nodo 'b' Vacio Vacio) (Nodo 'c' (Nodo 'd' Vacio Vacio) Vacio)) = 4
nodos :: AB a -> Int
nodos b = case b of
  Vacio -> 0
  Nodo _ i d -> 1 + nodos i + nodos d

-- | preorden. Función que obtiene la lista que consiste en el recorrido
-- de peorden de un árbol binario.
--
-- --> preorden (Nodo 'R' (Nodo 'F' Vacio Vacio) (Nodo 'M' Vacio Vacio)) = "RFM"
