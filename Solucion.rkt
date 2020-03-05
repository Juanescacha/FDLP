#lang eopl
(require racket/string)

; Integrantes:
; Juan Esteban Camargo Chacon - 1924984
; Brayan
; Sebastian

; COMENTARIO por PROCEDIMIENTO QUE EXPLIQUE que realiza y PARA QUE lo realiza

; 1) Disenar interpretador con la siguiente gramatica, operaciones notacion infija
; 2) Definir ambiente inicial y modificar la funcion evaluar-expresion para que acepte el ambiente
;    Disenar una funcion llamada buscar-variable
; 3) Implementar los booleanos
; 4) Extender la gramatica con condicionales (if)
; 5) Implementar Declaracion de Variables Locales (let)
; 6) Extender la Gramatica para crear procedimientos ... proc-val
; 7) Extender la Gramatica para evaluar Procedimientos
; 8) Extender la Gramatica para incluir llamados recursivos
; B9) Dibuje el arbol de sintaxis abstracta de los ejerciicios del punto 7
; B10) Dibujar el diagrama de ambientes de los ejercicios del punto 7 ( tener en cuenta el ambiente inical del punto 1)
; Utilizacion del lenguaje;
; 11)
;     Ba) Escribir un programa en su lenguaje de programacion que contenga un procedimiento que permita calcular el area de un circulo dado un radio ( a = pi * r^2 ) debe incluir valores flotantes en el lenguaje

;     b) Escribir un programa en su lenguaje que contenga un procedimiento que permita calcular el factorial de un numero n

;     c) Escribir un programa que contenga un procedimiento que permita calcular una multiplicacion de forma recursiva a traves de sumas

;     d) Escribir un programa recursivo que permita sumar, restar , multiplicar dos numeros haciendo uso solamente dee add1 y sub1



;<programa> :=  <expresion>
;
;               un-programa (exp)
;
;
;<expresion> := <numero>
;               numero-lit (num)
;
;            := "\"" <texto> "\""
;               texto-lit (txt)
;
;            := <identificador>
;               var-exp (id)
;
;            := (expresion <primitiva-binaria> expresion)
;               primapp-bin-exp (exp1 exp2)
;
;            := <primitiva-unaria> (expresion)
;               primapp-un-exp (exp)
;
;            := if <expresion> then <expresion> else <expresion>
;               if-exp (exp1 exp2 exp3)
;
;            := let ( <indentificador> = <expresion> )* in <expresion>
;               <let-exp (ids rands body)>
;
;            := proc ( {<indentificador>}*(,)) <expresion>
;               proc-exp (ids body)
;
;            := [ <expresion> {<expresion>}* ]
;               <app-exp proc rands>
;
;
;<primitiva-binaria> :=  + (primitiva-suma)
;
;                    :=  ~ (primitiva-resta)
;
;                    :=  / (primitiva-div)
;
;                    :=  * (primitiva-multi)
;
;                    :=  concat (primitiva-concat)
;
;
;<primitiva-unaria>:=  longitud (primitiva-longitud)
;
;                  :=  add1 (primitiva-add1)
;
;                  :=  sub1 (primitiva-sub1)

;***********************************************************************************

(define lexica
  '(
    (espacios (whitespace) skip)
    (cometarios ("%" (arbno (not #\newline))) skip)
    (identificador ("@" letter (arbno (or letter digit "?"))) symbol)
    ;(texto ((or letter digit) (arbno (or letter digit))) symbol)
    
    ; Enteros
    (numero (digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)) number)
    
    ; Decimales
    (numero (digit (arbno digit) "." digit (arbno digit)) number)
    (numero ("-" digit (arbno digit) "." digit (arbno digit)) number)

    ; Texto
    (text ("\"" (or letter whitespace) (arbno (or letter digit whitespace ":" "?" "=" "'" )) "\"") string)
    )
  )

(define gramatica
  '(
    ; programa
    (programa (expresion) un-programa)
    
    ; expresion
    (expresion (numero) numero-lit)
    (expresion (text) texto-lit)
    (expresion (identificador) var-exp)
    (expresion ( "(" expresion primitiva-binaria expresion ")" ) primapp-bin-exp)
    (expresion (primitiva-unaria expresion) primapp-un-exp)
    (expresion ( "if" expresion "then" expresion "else" expresion) if-exp)
    (expresion ("let" "(" (arbno identificador "=" expresion) ")" "in" expresion) let-exp)
    (expresion ("proc" "(" (separated-list identificador ",") ")" expresion) proc-exp)
    (expresion ( "[" expresion (arbno expresion) "]" ) app-exp)
    (expresion ( "letrec" (arbno identificador "(" (separated-list identificador ",") ")" "=" expresion) "in" expresion) letrec-exp)
    
    
    ; primitiva-binaria
    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("-") primitiva-resta)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("concat") primitiva-concat)
    
    ; primitiva-unaria
    (primitiva-unaria ("longitud") primitiva-longitud)
    (primitiva-unaria ("add1") primitiva-add1)
    (primitiva-unaria ("sub1") primitiva-sub1)
    )
  )

;***********************************************************************************

; Definicion Construccion automatica con SLLGEN

(sllgen:make-define-datatypes lexica gramatica)

(define mostrar-datatypes
  (lambda ()
    (sllgen:list-define-datatypes lexica gramatica)))

;***********************************************************************************

; Parser

(define scan&parse
  (sllgen:make-string-parser lexica gramatica))

; Scanner
(define just-scan
  (sllgen:make-string-scanner lexica gramatica))

; Interpretador
(define interpretador
  (sllgen:make-rep-loop "C:/"
                        (lambda (pgm) (eval-program pgm))
                        (sllgen:make-stream-parser lexica gramatica)))

;***********************************************************************************

; El Interprete

(define eval-program
  (lambda (pgm)
    (cases programa pgm
      (un-programa (body)
                   (eval-expression body (init-env))))))


(define eval-expression
  (lambda (exp env)
    (cases expresion exp
      
      (numero-lit (numero) numero)
      
      (var-exp (id) (buscar-variable env id))
      
      (primapp-bin-exp (exp1 pBinaria exp2) (apply-primapp-bin (eval-expression exp1 env) pBinaria (eval-expression exp2 env)))
      
      (primapp-un-exp (pUnaria exp1) (apply-primapp-un pUnaria exp1))
      
      (texto-lit (text) (string-trim text "\"" ))

      (if-exp (test true false) (if (true-value? (eval-expression test env))
                                    (eval-expression true env)
                                    (eval-expression false env)))
      
      (let-exp (ids rands body) (let ((args (eval-rands rands env))) (eval-expression body (extend-env ids args env))))
      
      (proc-exp (ids body) (closure ids body env))
      
      (app-exp (rator rands) (let
                                 ((proc (eval-expression rator env))
                                  (args (eval-rands rands env)))
                                 (if (procval? proc)
                                     (apply-procedure proc args)
                                     (eopl:error 'eval-expression "Intento aplicar a un no precidimiento ~s" proc))))

      (letrec-exp (proc-names ids bodies letrec-body)
                  (eval-expression letrec-body
                                   (extend-env-recursively proc-names ids bodies env)))
      )))

;***********************************************************************************

(define apply-primapp-bin
  (lambda (a operador b)
    (cases primitiva-binaria operador
      (primitiva-suma  () (+ a b))
      (primitiva-resta () (- a b))
      (primitiva-multi () (* a b))
      (primitiva-div   () (/ a b))
      (primitiva-concat () (cons a (cons b '())))
      )))

(define apply-primapp-un
  (lambda (operador a)
    (cases primitiva-unaria operador
      (primitiva-longitud () (length (eval-expression a)))
      (primitiva-add1     () (+ (eval-expression a) 1))
      (primitiva-sub1     () (- (eval-expression a) 1))
       )))

;***********************************************************************************

; Ambientes

; Definimos el tipo de dato ambiente

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record (syms (list-of symbol?))
                      (vals (list-of scheme-value?))
                      (env environment?))
  (recursively-extended-env-record (proc-names (list-of symbol?))
                                   (ids (list-of (list-of symbol?)))
                                   (bodies (list-of expresion?))
                                   (env environment?)))

(define scheme-value? (lambda (v) #t))

; empty-env: -> environment
; funcion que crea un ambiente vacio

(define empty-env
  (lambda ()
    (empty-env-record))) ;llamada al constructor de ambiente vacio

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define extend-env-recursively
  (lambda (proc-names ids bodies old-env)
    (recursively-extended-env-record proc-names ids bodies old-env)))

; Ambiente Inicial

(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e)
     '(1 2 3 "hola" "FLP")
     (empty-env))))

; Definimos buscar-variable

(define buscar-variable
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'apply-env "No se encontro ~s" sym))
      
      (extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (buscar-variable env sym))))
      
      (recursively-extended-env-record (proc-names ids bodies old-env)
                                       (let ((pos (list-find-position sym proc-names)))
                                         (if (number? pos)
                                             (closure (list-ref ids pos)
                                                      (list-ref bodies pos)
                                                      env)
                                             (buscar-variable old-env sym)))))))


;***********************************************************************************

; Funciones Auxiliares
;
; Nos seriviran para encontrar la posicion de
; un simbolo en la lista de simbolos de un ambiente

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
            (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

; Nos serviran para aplicar eval-expression a cada elemento de una lista de operandos (expresiones)

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))

; true-value?: determina si un valor dado corresponde a un valor booleano falso o verdadero

(define true-value?
  (lambda (x)
    (not (zero? x))))

;***********************************************************************************

; PROCEDIMIENTOS

; Definimos el tipo de dato Closure

(define-datatype procval procval?
  (closure
   (ids (list-of symbol?))
   (body expresion?)
   (env environment?)))

; Definimos apply-procedure que evalua el cuerpo de un procedimiento en el ambiente extendido correspondiente

(define apply-procedure
  (lambda (proc args)
    (cases procval proc
      (closure (ids body env) (eval-expression body (extend-env ids args env)))
      )))