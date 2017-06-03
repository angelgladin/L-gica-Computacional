╔════════════════════════════════════════════════╗ 
║ Lógica Computacional 2017-2                    ║ 
║ Práctica 6: Coq como lenguaje de programación  ║ 
╚════════════════════════════════════════════════╝

╔════════════════╗ 
║ Integrantes    ║ 
╚════════════════╝
● Ángel Iván Gladín García
  313040131

╔══════════════════════════════════╗ 
║ Breve Descripción de la práctica ║ 
╚══════════════════════════════════╝
La práctica consiste de 1 programa hecho en Coq:
   ● IntroCoq.v
     ——Programa el cuál se hacen todos los ejercicios
     dados en el especificación de la práctica.

╔═══════════════╗ 
║ Para ejecutar ║ 
╚═══════════════╝
Para ejecutar (en mi caso) se abrirá el archivo de Coq con CoqIde, que
está situado en.

AngelGladin
    └── Pract6
    	├── readme.txt
	└── src
            └── archivos.v

Y luego escribir para interactuar con el programa se usarán las flechas
de navegación en la parte superior del programa.

╔══════════════╗ 
║ Conclusiones ║ 
╚══════════════╝
La verdad si me costó trabajo porque cada vez que quería checar en internet
ejemplos venían algo complejos y la documentación la encontré medio difícil.
Creo que lo que me sigue cuesta más trabajo aún es la programación logica
y definir las relaciones por ejemplo la de par, impar y member.
---------------------------------------------------------------------
2.1 Programación funcional vs lógica
    Para `par` lo dividí en dos axiomas, básicamente dividí el caso
    cuando es 0 que significa "El cero es par" y para el segundo
    si para todo natural se tiene que el sucesor del sucesor de ese
    número también es par, ósea de la forma 2k.
    Para `impar` lo dividí en un axioma que dice lo siguiente;
    para todo número natural que es par (de la forma 2k) entonces
    el sucesor de ese número será impar, ósea 2k+1.
---------------------------------------------------------------------
2.2 Programación funcional vs lógica
3.  Los pros de la programación funcional (al menos para mí) la implementación
    funcional es mucho más fácil de implementar y más intuitiva que la
    programación lógica.
    Los contras es que necesitas tener más madurez (desde mi punto de vista)
    para la programación lógica.
   
╔═══════════════╗ 
║ Bibliografía  ║ 
╚═══════════════╝
Lo que se enseñó en la ayudantía.


\`*-.                    
)  _`-.                 
.  : `. .                
: _   '  \               
; *` _.   `*-._          
`-.-'          `-.       
;       `       `.     
:.       .        \    
. \  .   :   .-'   .   
'  `+.;  ;  '      :   
:  '  |    ;       ;-. 
; '   : :`-:     _.`* ;
*' /  .*' ; .*`- +'  `*' 
*-*   `*-*  `*-*'   

╔════════════════════════════════════════════════╗ 
║ El software es como las catedrales, primero lo ║
║ construimos y luego le rezamos. -Anónimo.      ║
╚════════════════════════════════════════════════╝
