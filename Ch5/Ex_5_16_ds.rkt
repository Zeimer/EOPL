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
  '((program
     (statement)
     a-program)

    (statement
     (identifier "=" expression)
     asgn-stmt)

    (statement
     ("print" expression)
     print-stmt)

    (statement
     ("{" (separated-list statement ";") "}")
     seq-stmt)

    (statement
     ("if" expression statement statement)
     if-stmt)

    (statement
     ("while" expression statement)
     while-stmt)
    
    (init
     ()
     init-empty)

    (init
     ("=" expression)
     init-nonempty)
    
    (statement
     ("var" (separated-list identifier init ",") ";" statement)
     var-stmt)
    
    (statement
     ("read" identifier)
     read-stmt)

    (statement
     ("do" statement "while" expression)
     do-while-stmt)
    
    (expression
     (number)
     const-exp)

    (expression
     ("+" "(" expression "," expression ")")
     plus-exp)
    
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    (expression
     ("*" "(" expression "," expression ")")
     mult-exp)

    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("not" "(" expression ")")
     not-exp)
    
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

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;;;;;;;; Expressible values ;;;;;;;;;;;;;;;;;;;;;;;;;

; procedure : Var -> ExpVal -> Env -> Proc
(define (procedure var body env)
  (lambda (val) (value-of body (extend-env var (newref val) env))))

; apply-procedure : Proc -> ExpVal -> ExpVal
(define (apply-procedure f x) (f x))

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

; expval->any : ExpVal -> Any
(define (expval->any val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)))

; any->expval : Any -> ExpVal
(define (any->expval v)
  (cond
    [(integer? v) (num-val v)]
    [(boolean? v) (bool-val v)]
    [(procedure? v) (proc-val v)]
    [else
     eopl:error 'any->expval "~s can't be made into an ExpVal." v]))

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
;(define (init-env) (empty-env))

; init-env : () -> Env
(define (init-env)
  (extend-env
   'i (newref (num-val 1))
   (extend-env
    'v (newref (num-val 5))
    (extend-env
     'x (newref (num-val 10))
     (empty-env)))))

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
;;;;;;;;;;;;;;;;;;;;;;; Exp continuations ;;;;;;;;;;;;;;;;;;;;;;;;;;

; FinalAnswer = ExpVal
; Cont = ExpVal -> ExpVal

; apply-cont : Cont * ExpVal -> FinalAnswer
(define (apply-cont cont val) (cont val))

; end-cont : () -> Cont
(define (end-cont)
  (lambda (val) val))

; let-exp-cont : Var * Exp * Env * Cont -> Cont
(define (let-exp-cont var body env cont)
  (lambda (val)
    (value-of/k body (extend-env var (newref val) env) cont)))

; binop1-cont : Binop * Exp * Env * Cont -> Cont
(define (binop1-cont op e env cont)
  (lambda (v)
    (value-of/k e env (binop2-cont op v cont))))

; binop2-cont : BniaryOperator * ExpVal * Cont -> Cont
(define (binop2-cont op v1 cont)
  (lambda (v2)
    (apply-cont cont
      (any->expval (op (expval->any v1) (expval->any v2))))))

; unop : UnaryOperator * Cont -> Cont
(define (unop-cont op cont)
  (lambda (v)
    (apply-cont cont (any->expval (op (expval->any v))))))

; if-test-cont : Exp * Exp * Env * Cont -> Cont
(define (if-test-cont expt expf env cont)
  (lambda (val)
    (if (expval->bool val)
        (value-of/k expt env cont)
        (value-of/k expf env cont))))

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

;;;;;;;;;;;;;;;;;;;; Statement continuations ;;;;;;;;;;;;;;;;;;;;;;;

; StmtCont = end-stmt-cont
;          | asgn-stmt-cont Var Exp Env StmtCont
;          | print-stmt-cont Exp Env Cont
;          | read-stmt-cont Var Env Cont
;          | seq-stmt-cont (List Stmt) Env Cont
;          | if-stmt-cont Exp Stmt Stmt Env Cont
;          | while-stmt-cont Exp Stmt Env Cont
(define-datatype stmt-cont stmt-cont?
  (end-stmt-cont)
  (asgn-stmt-cont
    (var identifier?) (e expression?) (env env?) (cont stmt-cont?))
  (print-stmt-cont
    (exp expression?) (env env?) (cont stmt-cont?))
  (read-stmt-cont
    (var identifier?) (env env?) (cot stmt-cont?))
  (seq-stmt-cont
    (stmts list?) (env env?) (cont stmt-cont?))
  (if-stmt-cont
    (exp expression?) (s1 statement?) (s2 statement?) (env env?)
    (cont stmt-cont?))
  (while-stmt-cont
    (exp expression?) (s statement?) (env env?) (cont stmt-cont?)))

; apply-stmt-cont :  StmtCont -> ()
(define (apply-stmt-cont cont)
  (cases stmt-cont cont
    
    (end-stmt-cont () '())
    
    (asgn-stmt-cont (var exp env cont)
      (setref! (apply-env env var) (value-of exp env))
      (apply-stmt-cont cont))

    (print-stmt-cont (exp env cont)
      (write (expval->any (value-of exp env)))
      (display "\n")
      (apply-stmt-cont cont))

    (read-stmt-cont (var env cont)
      (setref! (apply-env env var) (num-val (read)))
      (apply-stmt-cont cont))

    (seq-stmt-cont (stmts env cont)
      (cond
        [(null? stmts) (apply-stmt-cont cont)]
        [else
         (exec-stmt (car stmts) env
                    (seq-stmt-cont (cdr stmts) env cont))]))

    (if-stmt-cont (e s1 s2 env cont)
      (if (expval->bool (value-of e env))
          (exec-stmt s1 env cont)
          (exec-stmt s2 env cont)))

    (while-stmt-cont (e s env cont)
      (if (expval->bool (value-of e env))
          (exec-stmt s env (while-stmt-cont e s env cont))
          (apply-stmt-cont cont)))))

;;;;;;;;;;;;;;;;;;;;;;;;;; Interpreter ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; run : String -> ()
(define (run str)
  (exec-program (scan&parse str)))

; exec-program : Program -> ()
(define (exec-program p)
  (initialize-store!)
  (cases program p
    (a-program (stmt)
               (exec-stmt stmt (init-env) (end-stmt-cont)))))

; exec-stmt : Statement * Env * Stmt-Cont -> ()
(define (exec-stmt stmt env cont)
  (cases statement stmt

    (asgn-stmt (var exp)
      (apply-stmt-cont (asgn-stmt-cont var exp env cont)))

    (print-stmt (exp)
      (apply-stmt-cont (print-stmt-cont exp env cont)))

    (read-stmt (var)
      (apply-stmt-cont (read-stmt-cont var env cont)))

    (seq-stmt (stmts)
      (apply-stmt-cont (seq-stmt-cont stmts env cont)))

    (if-stmt (e s1 s2)
      (apply-stmt-cont (if-stmt-cont e s1 s2 env cont)))

    (while-stmt (e s)
      (apply-stmt-cont (while-stmt-cont e s env cont)))

    (do-while-stmt (s e)
      (exec-stmt s env (while-stmt-cont e s env cont)))
    
    (var-stmt (vars inits s)
      (exec-stmt s (extend-env-var-stmt vars inits env) cont))))

; extend-env-decls : List Decl * Env -> Env
(define (extend-env-var-stmt vars inits env)
  (cond
    [(null? vars) env]
    [else
     (cases init (car inits)
       (init-empty ()
         (extend-env
           (car vars)
           (newref (num-val 42))
           (extend-env-var-stmt (cdr vars) (cdr inits) env)))
       (init-nonempty (exp)
         (extend-env
           (car vars)
           (newref (value-of exp env))
           (extend-env-var-stmt (cdr vars) (cdr inits) env))))]))

; value-of : Exp * Env -> ExpVal
(define (value-of exp env)
  (value-of/k exp env (end-cont)))

; value-of/k : Exp * Env * Cont -> ExpVal
(define (value-of/k exp env cont)
  (cases expression exp
    
    (const-exp (num)
      (apply-cont cont (num-val num)))
    
    (var-exp (var)
      (apply-cont cont (deref (apply-env env var))))

    (plus-exp (e1 e2)
      (value-of/k e1 env (binop1-cont + e2 env cont)))
    
    (diff-exp (e1 e2)
      (value-of/k e1 env (binop1-cont - e2 env cont)))

    (mult-exp (e1 e2)
      (value-of/k e1 env (binop1-cont * e2 env cont)))

    (zero?-exp (e)
      (value-of/k e env (unop-cont zero? cont)))

    (not-exp (e)
     (value-of/k e env (unop-cont not cont)))
    
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