#lang eopl

;;;;;;;;;;;;;;;;;;;; Lexical specification ;;;;;;;;;;;;;;;;;;;;;;;;;
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

;;;;;;;;;;;;;;;;;;;;;;;;; Grammar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;; Expressible values ;;;;;;;;;;;;;;;;;;;;;;;;;

; procedure : Var * ExpVal * Env * Cont -> Proc
(define (procedure var body env)
  (lambda (val cont)
    (value-of/k body (extend-env var (newref val) env) cont)))

; apply-procedure : Proc * ExpVal -> ExpVal
(define (apply-procedure f x cont) (f x cont))

; ExpVal = Int + Bool + Proc + List
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

;;;;;;;;;;;;;;;;;;;;;;;;; Environments ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ident = Symbol
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

; location : Sym * List Sym -> Maybe Int
(define location
  (lambda (sym syms)
    (cond
      ((null? syms) #f)
      ((eqv? sym (car syms)) 0)
      ((location sym (cdr syms))
       => (lambda (n) 
            (+ n 1)))
      (else #f))))

; apply-env : Env * Identifier -> ExpVal
(define (apply-env e k)
  (cases env e
    (empty-env () (report-no-binding-found k))
    (extend-env (k2 v e1) (if (eqv? k k2) v (apply-env e1 k)))
    (extend-env-rec (fs xs bodies e1)
                    (let ((n (location k fs)))
                      (if n
                          (newref
                           (proc-val
                            (procedure
                             (list-ref xs n)
                             (list-ref bodies n)
                             e)))
                          (apply-env e1 k))))))

; init-env : () -> Env
(define (init-env) (empty-env))

;;;;;;;;;;;;;;;;;;;;;;;;;;;; The store ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; Ref = Int
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

; report-invalid-reference : Ref * Store -> Error
(define (report-invalid-reference ref store)
  (eopl:error 'setref! "Invalid reference ~s in the store ~s"
              ref store))

; setref! : Ref * ExpVal -> Unit
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

;;;;;;;;;;;;;;;;;;;;;;; Continuations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FinalAnswer = ExpVal
; Cont = ExpVal -> ExpVal

; apply-cont : Cont * ExpVal -> FinalAnswer
(define (apply-cont cont val) (cont val))

; end-cont : () -> Cont
(define (end-cont)
  (lambda (val)
    (begin
      (eopl:printf "End of computation.~%")
      val)))

; zero1 : Cont * ExpVal -> ExpVal
(define (zero1-cont cont)
  (lambda (val)
    (apply-cont cont (bool-val (zero? (expval->num val))))))

; let-exp-cont : Var * Exp * Env * Cont -> Cont
(define (let-exp-cont var body env cont)
  (lambda (val)
    (value-of/k body (extend-env var (newref val) env) cont)))

; if-test-cont : Exp * Exp * Env * Cont -> Cont
(define (if-test-cont expt expf env cont)
  (lambda (val)
    (if (expval->bool val)
        (value-of/k expt env cont)
        (value-of/k expf env cont))))

; diff1-cont : Exp * Env * Cont -> Cont
(define (diff1-cont exp env cont)
  (lambda (val)
    (value-of/k exp env (diff2-cont val cont))))

; diff2-cont : ExpVal * Cont -> Cont
(define (diff2-cont v1 cont)
  (lambda (v2)
    (apply-cont cont
                (num-val (- (expval->num v1) (expval->num v2))))))

; rator-cont : Exp * Env * Cont -> Cont
(define (rator-cont exp env cont)
  (lambda (f)
    (value-of/k exp env (rand-cont f cont))))

; rand-cont : Proc * Cont -> Cont
(define (rand-cont f cont)
  (lambda (x)
    (apply-procedure (expval->proc f) x cont)))

; assign-cont : Ref * Cont -> Cont
(define (assign-cont ref cont)
  (lambda (val)
    (apply-cont cont
                (begin
                  (setref! ref val)
                  (num-val 42)))))

; value-of-begin : List ExpVal * Env -> ExpVal
(define (begin-cont exps env cont)
  (lambda (val)
    (cond
      [(null? exps) (apply-cont cont val)]
      [else
       (value-of/k (car exps) env
                   (begin-cont (cdr exps) env cont))])))

;;;;;;;;;;;;;;;;;;;;;;;;;; Interpreter ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; run : String -> ExpVal
(define (run string)
  (expval->any (value-of-program (scan&parse string))))

; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (initialize-store!)
  (cases program pgm
    (a-program (e) (value-of/k e (init-env) (end-cont)))))

; value-of/k : Exp * Env * Cont -> ExpVal
(define (value-of/k exp env cont)
  (cases expression exp
    
    (const-exp (num)
      (apply-cont cont (num-val num)))
    
    (var-exp (var)
      (apply-cont cont (deref (apply-env env var))))
    
    (diff-exp (exp1 exp2)
      (value-of/k exp1 env (diff1-cont exp2 env cont)))

    (zero?-exp (exp)
      (value-of/k exp env (zero1-cont cont)))
    
    (if-exp (exp1 exp2 exp3)
      (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))

    (let-exp (var exp body)
      (value-of/k exp env (let-exp-cont var body env cont)))
    
    (proc-exp (var body)
      (apply-cont cont (proc-val (procedure var body env))))

    (call-exp (e1 e2)
      (value-of/k e1 env (rator-cont e2 env cont)))

    (letrec-exp (fs xs bodies letrec-body)
      (value-of/k letrec-body
                  (extend-env-rec fs xs bodies env)
                  cont))
    
    (assign-exp (var e)
      (value-of/k e env (assign-cont (apply-env env var) cont)))
    
    (begin-exp (e exps)
      (value-of/k e env (begin-cont exps env cont)))))