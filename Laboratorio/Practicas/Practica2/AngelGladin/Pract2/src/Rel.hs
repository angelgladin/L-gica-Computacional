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

module Rel
  ( invR
  , total
  , refl
  , symm
  ) where

-- | U. Lista que representa un conjunto.
type U a = [a]

-- | R. Lista que representa una relación binaria.
type R a = [(a, a)]

-- | invR. Función que dada un relación devuelve su inversa.
-- --> invR [(0,1)] = [(1,0)]
-- --> invR [(1,2),(3,4)] = [(2,1),(4,3)]
invR :: R a -> R a
invR xs = [(b, a) | (a, b) <- xs]

-- | total. Función que dado un conjunto regresa la relación
-- binaria total, es decir, relacionar todos los elemetos con todos.
-- --> total [1,2] = [(1,1),(2,2),(1,2),(2,1)]
-- --> total [1,2,3] = [(1,1),(2,2),(3,3),(1,2),(1,3),(2,3),(2,1),(3,1),(3,2)]
total :: U a -> R a
total [] = []
total xs =
  let sim = [(x, x) | x <- xs]
      cmb = combSinRep xs
      cmbRefl = invR cmb
  in sim ++ cmb ++ cmbRefl

-- combSinRep. Función auxiliar que dado un conjunto devuelve
-- todas las combinaciones de dos en dos del conjuntos.
-- Es usada para la función `total`.
combSinRep :: U a -> R a
combSinRep [] = []
combSinRep (x:xs) = (sub x xs) ++ combSinRep xs
  where sub x [] = []
        sub x (y:ys) = (x, y) : sub x ys

-- | refl. Fución que dada un relación decide si dicha relación
-- es un relación reflexiva.
-- Por definición de relación reflexiva se tiene que
-- ∀x ∊ A, xRx.
-- --> refl [(1,1),(2,2),(3,3),(4,4)] = True
-- --> refl [(1,1),(2,2),(1,2),(7,9)] = False
refl :: Eq a => R a -> Bool
refl xs = 
  let simetrL = [(x, x) | x <- elementosRelacion xs]
  in estaEnRel simetrL xs
  where estaEnRel [] [] = True
        estaEnRel [] ys = True
        estaEnRel (x:xs) ys = x `elem` ys && estaEnRel xs ys

-- elementosRelacion. Función auxiliar que dada una relación, devuelve
-- un conjutno con cada uno de los elementos de cada relación, además
-- por defición de conjunto, esta lista no tiene repeticiones.
elementosRelacion :: Eq a => R a -> U a
elementosRelacion xs = 
  let auxL = foldr (\(a, b) acc -> a : b : acc) []
      sinRep = foldr (\x acc -> if x `elem` acc then acc else x : acc) []
  in  sinRep $ auxL xs

-- | symm. Función que dada una relación devuelve un valor
-- booleano si la relación es simétrica.
-- ∀x, y ∊ A: xRy ⟹ yRx.
-- --> symm [(0,1),(1,0),(2,3),(3,2)] = True
-- --> symm [(0,1),(2,3),(5,4)] = False
symm :: Eq a => R a -> Bool
symm xs = aux xs xs
  where aux [] [] = True
        aux ys [] = True
        aux xs ((a, b):ys) = (b, a) `elem` xs && aux xs ys
