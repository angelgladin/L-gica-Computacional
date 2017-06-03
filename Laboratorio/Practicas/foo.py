'''
Script que cree para hacer toda la estructura de una
práctica.
Para ejecutar
python3 foo.py
Y luego poner el número de la práctica.
'''

import os

prac = 'Practica'
n = input('Ingresa el número de práctica: ')
name = 'AngelGladin'

path = '{}/{}/Pract{}/src'.format(prac + n, name, n)
os.makedirs(path)

f = open(path[:len(path)-4] +'/readme.txt', 'w+')
f.close()

print('Estructura del proyecto creada :v')
