{-
 -Logica Computacional 2017-2
 -Ejemplo de semántica de LPO: Enteros módulo 10.
 -Profesor: Lourdes del Carmen Gonzaléz Huesca
 -Ayudante: Roberto Monroy Argumedo
 -Laboratorio: Fernando A. Galicia Mendoza
-}

--Importamos los módulos necesarios de LPO.
import LPO
import LPOSust
import LPOSem

--Universo : Z10, es decir, los enteros módulo 10
m :: [Int]
m = [0..9]

--Un estado de las variables 'x' e 'y'.
est :: Estado Int
est 1 = 1
est 2 = 2
est _ = 0

--Asignamos una interpretación a las constantes {0,...,9} y las
--funciones: identidad, suma, resta, producto y división.
iF :: IntF Int
iF s [] = case s of
  "0" -> 0
  "1" -> 1
  "2" -> 2
  "3" -> 3
  "4" -> 4
  "5" -> 5
  "6" -> 6
  "7" -> 7
  "8" -> 8
  "9" -> 9
  _ -> 0
iF "id" [n] = n
iF "+" [n1,n2] = (mod n1 10)+(mod n2 10)
iF "-" [n1,n2] = (mod n1 10)-(mod n2 10)
iF "*" [n1,n2] = (mod n1 10)*(mod n2 10)
iF "/" [n1,n2] = div (mod n1 10) (mod n2 10)

--Asignamos una interpretación a las relaciones de menor o igual e igualdad.
iM :: IntR Int
iM "<=" [n1,n2] = n1 <= n2
iM "=" [n1,n2] = n1 == n2

--Ejemplos de interpretación de términos.
--id 1 = 1
ejemplo1 = iTerm est iF (F "id" [F "1" []])

--1+2 = 3
ejemplo2 = iTerm est iF (F "+" [F "1" [],F "2" []])

--3 / 0 = 0
ejemplo3 = iTerm est iF (F "/" [F "0" [],F "3" []])

ej n m = iTerm est iF (F "+" [F (show n) [],F (show m) []]) 

--Ejemplos de intrepretación de teoremas.

--Para todo x en Z10, 0 <= x
--Resultado: True
ejemplo4 = iForm m (est,iF,iM) (All 1 (Pr "<=" [F "0" [],V 1]))

--Para todo x en Z10, existe un y en Z10 tal que x <= y
--Resultado: True
ejemplo5 = iForm m (est,iF,iM) (All 1 (Ex 2 (Pr "<=" [V 1, V 2])))

--Para todo x en Z10, 0 = x
--Resultado: False
ejemplo6 = iForm m (est,iF,iM) (All 1 (Pr "=" [F "0" [], V 1]))

--Para todo x en Z10, 0 = x - x
--Resultado: True
ejemplo7 = iForm m (est,iF,iM) (All 1 (Pr "=" [F "0" [], F "-" [V 1, V 1]]))

--Para todo x en Z10, x = id(x)
--Resultado: True
ejemplo8 = iForm m (est,iF,iM) (All 1 (Pr "=" [V 1, F "id" [V 1]]))

--Para todo x en Z10, existe un y en Z10, tal que x = y + y
--Resultado: False
ejemplo9 = iForm m (est,iF,iM) (All 1 (Ex 2 (Pr "=" [V 1, F "+" [V 2,V 2]])))
