{-
- Logica Computacional 2017-2
- Profesor: Dra. Lourdes del Carmen Gonzalez Huesca
- Ayudante: Roberto Monroy Argumedo
- Laboratorio: Fernando A. Galicia Mendoza
- Integrantes:
- Ángel Iván Gladín García
-   313112470
-   angelgladin@ciencias.unam.mx
-}

-- | map'. Función alternativa a `map` utilizando
-- pliegue derecho.
-- Toma como primer "parámetro" una función que
-- transfoma algo de tipo 'a' a tipo 'b'. Y de
-- segundo una lista de tipo a. Y regresa una
-- lista de tipo b.
-- Se utilizó pliegue derecho ya que como se van
-- se pegando a la lista es conveniento porque si
-- se hiciera con derecho se pondría al revés.
map' :: (a -> b) -> [a] -> [b]
map' f = foldr (\x acc -> f x : acc) []

-- | concat. Función alternativa a `concat` utilizando
-- pliegue derecho.
-- Para cada lista de usa la función `++` para irla
-- pegando al acumulador.
concat' :: Foldable t => t [a] -> [a]
concat' = foldr (++) []
