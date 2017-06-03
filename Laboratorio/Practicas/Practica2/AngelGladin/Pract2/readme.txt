=== Práctica 2: LP en Haskell ===
Logica Computacional 2017-2
Práctica 2: LP en Haskell
Profesor: Dra. Lourdes del Carmen Gonzalez Huesca
Ayudante: Roberto Monroy Argumedo
Laboratorio: Fernando A. Galicia Mendoza
Integrantes:
Ángel Iván Gladín García
    313112470
    angelgladin@ciencias.unam.mx
María Fernanda González Chávez
  313036367
  fernandagch@ciencias.unam.mx

== Breve descripción de como se realizó la práctica. ==
La práctica se dividió en cuatro partes:
La primera es acerca del archivo LProp el cual se le crearon
tres instancias de clase respectivamente: Show (para poder
visualizar la proposición como una cadena), Eq (para decidir
si dadas proposiciones son sintácticamente iguales) y 
finalmente Ord (la cual dice que hace que sea capaz de 
comparar proposiciones de acuerdo de el pesos de éstas).
La segunda es ampliar el módulo de LPS añadiendo funciones.
La tercera es crear un archivo llamado Rel el cual
tiene funciones y tipos relacionados con conjuntos y relaciones.
Y la cuarta es de la forma normal conjuntiva.

== Forma de ejecución de su programa ==
Para ejecutar el programa se deberá abrir una terminal
en donde se encuentra el código (en la directorio /src)
y se ejecutará el interprete de Haskell:
    ghci
Y dentro de el intérprete poner
    :l <ruta_Archivo>
O si se quiere cargar un archivo al intérprete basta poner:
    ghci <ruta_Archivo>

== Conclusiones ==
La práctica fue muy entretenida y además se repasaron las
funciones vistas en clase, también en la función
fnn y cnf estuvo divertida porque al principio vi casos
que no consideré pero después agregé.

== Bibliografia ==
Miran Lipovača. (2011). Learn You a Haskell for Great Good! : No Starch Press.


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

——————————————
                         _
                        | \
                        | |
                        | |
   |\                   | |
  /, ~\                / /
 X     `-.....-------./ /
  ~-. ~  ~              |
     \             /    |
      \  /_     ___\   /
      | /\ ~~~~~   \ |
      | | \        || |
      | |\ \       || )
     (_/ (_/      ((_/