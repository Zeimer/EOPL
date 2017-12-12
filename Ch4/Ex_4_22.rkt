#lang eopl

; TODO : napisz specyfikację.

; Lexical specification.
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

; Grammar.
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

    (decl
     (identifier)
     noinit-decl)

    (decl
     ("'" identifier "=" expression)
     init-decl)
    
    (statement
     ("var" (separated-list decl ",") ";" statement)
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

; SLLGEN boilerplate.
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

; Expressible values.
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

; expval->any : ExpVal -> SchemeVal
(define (expval->any val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)))

; The environment.
(define identifier? symbol?)

(define-datatype env env?
  (empty-env)
  (extend-env (k identifier?) (ref reference?) (e env?))
  (extend-env-rec
   (fs (list-of identifier?))
   (xs (list-of identifier?))
   (bodies (list-of expression?))
   (e env?)))

; report-no-binding-found : Var -> Error
(define (report-no-binding-found k)
  (eopl:error 'apply-env "No binding for ~s" k))

 ;; location : Sym -> Listof(Sym) -> Maybe(Int)
(define (location sym syms)
  (cond
    ((null? syms) #f)
    ((eqv? sym (car syms)) 0)
    ((location sym (cdr syms))
     => (lambda (n)
          (+ n 1)))
    (else #f)))

; apply-env : Var -> Env -> ExpVal + Error
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

; The initial environment.
; init-env : () -> Env
(define (init-env)
  (extend-env
   'i (newref (num-val 1))
   (extend-env
    'v (newref (num-val 5))
    (extend-env
     'x (newref (num-val 10))
     (empty-env)))))

; The store.
(define reference? integer?)

; empty-store : () -> Store
(define (empty-store) '())

; the-store : Store
(define the-store 'uninitialized)

; get-store : () -> Store
(define (get-store) the-store)

; initialize-store! : () -> ()
(define (initialize-store!)
  (set! the-store (empty-store)))

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

; setref! : Ref -> ExpVal -> ()
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

; Interpreter.
; run : String -> ()
(define (run str)
  (exec-program (scan&parse str)))

; exec-program : Program -> ()
(define (exec-program p)
  (initialize-store!)
  (cases program p
    (a-program (stmt) (exec-stmt stmt (init-env)))))

; exec-stmt : Statement -> Env -> ()
(define (exec-stmt stmt env)
  (cases statement stmt

    (asgn-stmt (var exp)
               (begin
                 (setref!
                  (apply-env var env)
                  (value-of exp env))))
    
    (print-stmt (exp)
                (write (expval->any (value-of exp env)))
                (display "\n"))
    
    (seq-stmt (stmts)
              (cond
                [(null? stmts) '()]
                [else
                 (exec-stmt (car stmts) env)
                 (exec-stmt (seq-stmt (cdr stmts)) env)]))

    (if-stmt (exp s1 s2)
             (if (value-of exp env)
                 (exec-stmt s1 env)
                 (exec-stmt s2 env)))

    (while-stmt (exp s)
                (if (value-of exp env)
                    (begin
                      (exec-stmt s env)
                      (exec-stmt (while-stmt exp s) env))
                    '()))

    (var-stmt (decls s)
      (cond
        [(null? decls) (exec-stmt s env)]
        [else
         (exec-stmt
          (var-stmt (cdr decls) s)
          (cases decl (car decls)
           (noinit-decl (var)
             (extend-env var (newref (num-val 42)) env))
           (init-decl (var exp)
             (extend-env var (newref (value-of exp env)) env))))]))
            
    (read-stmt (var)
               (begin
                 (setref!
                  (apply-env var env)
                  (num-val (read)))))

    (do-while-stmt (s e)
                   (exec-stmt s env)
                   (if (value-of e env)
                       (exec-stmt (do-while-stmt s e) env)
                       '()))))

; value-of : Exp -> Env -> ExpVal
(define (value-of exp env)
  (cases expression exp
    
    (const-exp (num)
               (num-val num))
    
    (var-exp (var)
             (deref (apply-env var env)))

    (plus-exp (e1 e2)
              (num-val (+
                        (expval->num (value-of e1 env))
                        (expval->num (value-of e2 env)))))

    (mult-exp (e1 e2)
              (num-val (*
                        (expval->num (value-of e1 env))
                        (expval->num (value-of e2 env)))))
    
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

    (not-exp (e)
              (not (expval->bool (value-of e env))))
    
    (let-exp (var e body)
             (let ((val (value-of e env)))
               (value-of body
                         (extend-env var (newref val) env))))
    
    (proc-exp (var body)
              (proc-val (procedure var body env)))
    
    (call-exp (e1 e2)
              (apply-procedure
               (expval->proc (value-of e1 env))
               (value-of e2 env)))
    
    (letrec-exp (fs xs bodies body)
                 (value-of body (extend-env-rec fs xs bodies env)))
    
    (assign-exp (var e)
                (begin
                  (setref!
                   (apply-env var env)
                   (value-of e env))
                  (num-val 42)))
    
    (begin-exp (e es) (value-of-begin (cons e es) env))))

(define (value-of-begin es env)
  (cond
    [(null? (cdr es)) (value-of (car es) env)]
    [else
     (value-of (car es) env)
     (value-of-begin (cdr es) env)]))