#lang eopl

;;;;;;;;;;;;;;;;;;;; Lexical specification ;;;;;;;;;;;;;;;;;;;;;;;;
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

;;;;;;;;;;;;;;;;;;;;;;;;; Grammar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define the-grammar
  '((program (expression) a-program)
    
    (expression (number) const-exp)
    
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("lazy let" identifier "=" expression "in" expression)
     lazy-let-exp)

    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)
    
    (letrec-binding
     (identifier "(" identifier ")" "=" expression)
     binding-exp)

    (expression
     ("letrec" (arbno identifier "(" identifier ")" "=" expression)
               "in" expression)
     letrec-exp)

    (expression
     ("set" identifier "=" expression)
     assign-exp)
    
    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)))

;;;;;;;;;;;;;;;;;;;;;; SLLGEN boilerplate ;;;;;;;;;;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes)
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;;;;;;;; Expressible values ;;;;;;;;;;;;;;;;;;;;;;;;

; procedure : Var -> ExpVal -> Env -> Proc
(define (procedure var body env)
  (lambda (val)
    (value-of body (extend-env var val env))))

; apply-procedure : Proc -> ExpVal -> ExpVal
(define (apply-procedure f x) (f x))

; ExpVal = Int + Bool + Proc
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc procedure?)))

; expval->num : ExpVal -> Int
(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (eopl:error 'expval->num "~s is not a number" val))))

; expval->bool : ExpVal -> Bool
(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (eopl:error 'expval->bool "~s is not a boolean" val))))

; expval->proc : ExpVal -> Proc
(define (expval->proc val)
  (cases expval val
    (proc-val (p) p)
    (else (eopl:error 'expval->proc "~s is not a procedure" val))))

; expval->any : ExpVal -> SchemeVal
(define (expval->any val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)))

;;;;;;;;;;;;;;;;;;;;;;;;; Environments ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; identifier? : SchemeVal -> Bool
(define identifier? symbol?)

; Env =
;     | empty-env
;     | extend-env Ident Ref Env
;     | extend-env-rec (List Ident) (List Ident) (List ExpVal) Env
(define-datatype env env?
  (empty-env)
  (extend-env (k identifier?) (ref reference?) (e env?))
  (extend-env-rec
   (fs (list-of identifier?))
   (xs (list-of identifier?))
   (bodies (list-of expression?))
   (e env?)))

; report-no-binding-found : String -> Error
(define (report-no-binding-found k)
  (eopl:error 'apply-env "No binding for ~s" k))

; location : Sym -> List Sym -> Maybe Int
(define location
  (lambda (sym syms)
    (cond
      ((null? syms) #f)
      ((eqv? sym (car syms)) 0)
      ((location sym (cdr syms))
       => (lambda (n) 
            (+ n 1)))
      (else #f))))

; apply-env : Identifier -> Env -> ExpVal
(define (apply-env k e)
  (cases env e
    (empty-env () (report-no-binding-found k))
    (extend-env (k2 v e1) (if (eqv? k k2) v (apply-env k e1)))
    (extend-env-rec (fs xs bodies e1)
                    (let ((n (location k fs)))
                      (if n
                          (newref
                           (proc-val
                            (procedure
                             (list-ref xs n)
                             (list-ref bodies n)
                             e)))
                          (apply-env k e1))))))

; init-env : () -> Env
(define (init-env) (empty-env))

;;;;;;;;;;;;;;;;;;;;;;;;;;;; The store ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; empty-store : Unit -> Store
(define (empty-store) '())

; the-store : Store
(define the-store 'uninitialized)

; get-store : Unit -> Store
(define (get-store) the-store)

; initialize-store! : Unit -> Unit
(define (initialize-store!)
  (set! the-store (empty-store)))

;;;;;;;;;;;;;;;;;;;;;;;; Denotable values ;;;;;;;;;;;;;;;;;;;;;;;;;

; DenVal = Ref (ExpVal + Thunk)

; Thunk = Expression × Environment
(define-datatype thunk thunk?
  (a-thunk
   (e expression?)
   (env env?)))

; reference? : Ref -> Bool
(define reference? integer?)

; newref : ExpVal -> Ref
(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

; deref : Ref -> ExpVal
(define (deref ref)
  (list-ref the-store ref))

; report-invalid-reference : Ref -> Store -> Error
(define (report-invalid-reference ref store)
  (eopl:error 'setref! "Invalid reference ~s in the store ~s"
              ref store))

; setref! : Ref -> ExpVal -> Unit
(define (setref! ref val)
  (set! the-store
        (letrec
            ((setref-inner
              (lambda (store1 ref1)
                (cond
                  [(null? store1)
                   report-invalid-reference ref the-store]
                  [(zero? ref1)
                   (cons val (cdr store1))]
                  [else
                   (cons
                    (car store1)
                    (setref-inner
                     (cdr store1)
                     (- ref1 1)))]))))
          (setref-inner the-store ref))))

;;;;;;;;;;;;;;;;;;;;;;;;;; Interpreter ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; run : String -> ExpVal
(define (run string)
  (expval->any (value-of-program (scan&parse string))))

; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (initialize-store!)
  (cases program pgm
    (a-program (e) (value-of e (init-env)))))

; value-of : Exp -> Env -> ExpVal
(define (value-of exp env)
  (cases expression exp
    
    (const-exp (num)
               (num-val num))
    
    (var-exp (var)
             (let ((w (deref (apply-env var env))))
               (if (expval? w)
                   w
                   (value-of-thunk w))))

    (diff-exp (exp1 exp2)
              (num-val (-
                        (expval->num (value-of exp1 env))
                        (expval->num (value-of exp2 env)))))
    
    (zero?-exp (exp)
               (if (= 0 (expval->num (value-of exp env)))
                   (bool-val #t)
                   (bool-val #f)))
    
    (if-exp (exp1 exp2 exp3)
            (if (eqv? #t (expval->bool (value-of exp1 env)))
                (value-of exp2 env)
                (value-of exp3 env)))
    
    (let-exp (var e body)
             (let ((val (value-of e env)))
               (value-of body
                         (extend-env var (newref val) env))))

    (lazy-let-exp (var e body)
             (let ((val (value-of-operand e env)))
               (value-of body
                         (extend-env var val env))))
    
    (proc-exp (var body)
              (proc-val (procedure var body env)))
    
    (call-exp (e1 e2)
              (apply-procedure
               (expval->proc (value-of e1 env))
               (value-of-operand e2 env)))
    
    (letrec-exp (fs xs bodies body)
                (value-of body (extend-env-rec fs xs bodies env)))
    
    (assign-exp (var e)
                (begin
                  (setref!
                   (apply-env var env)
                   (value-of e env))
                  (num-val 42)))
    
    (begin-exp (e es) (value-of-begin (cons e es) env))))

; value-of-begin : List ExpVal -> Env -> ExpVal
(define (value-of-begin es env)
  (cond
    [(null? (cdr es)) (value-of (car es) env)]
    [else
     (value-of (car es) env)
     (value-of-begin (cdr es) env)]))

; value-of-operand : Expression -> Env -> ExpVal
(define (value-of-operand e env)
  (cases expression e
    (var-exp (var) (apply-env var env))
    (else (newref (a-thunk e env)))))

; value-of-thunk : Thunk -> ExpVal
(define (value-of-thunk th)
  (cases thunk th
    (a-thunk (e env)
             (value-of e env))))