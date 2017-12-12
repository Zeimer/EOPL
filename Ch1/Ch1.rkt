#lang eopl

; in-S? : N -> Bool
; usage: (in-S? n) = #t if n is in the set S (definition 1.1.1.from
; EoPL)
(define (in-S? n)
  (if (= n 0) #t
      (if (<= n 2) #f
          (in-S? (- n 3)))))

; list-length : List -> Int
; usage: (list-length l) = the length of l
(define (list-length l)
  (if (null? l) 0 (+ 1 (list-length (cdr l)))))

; nth-element : List * Int -> SchemeVal
; usage: (nth-element l n) = the nth element of l
(define (nth-element l n)
  (if (null? l)
      (report-list-too-short n)
      (if (= n 0)
          (car l)
          (nth-element (cdr l) (- n 1)))))

(define (nth-element2 l n)
  (cond
    [(null? l) (report-list-too-short n)]
    [(= n 0) (car l)]
    [else (nth-element2 (cdr l) (- n 1))]))

(define (report-list-too-short n)
  (eopl:error 'nth-element "List to short by ~s elements.~%" (+ n 1)))

; Ex. 1.7
; index : List * Int -> SchemeVal
; usage: (index l n) = nth element of l or error if the list is
;        too short
(define (index l n)
  (define index-error
    (eopl:error 'index "List ~s doesn't have ~s elements.\n"
                l n))
  (define (aux acc l n)
    (cond
      [(null? l) index-error]
      [(= n 0) (car l)]
      [else (aux acc (cdr l) (- n 1))]))
  (aux l l n))

; remove-first : SchemeVal * List -> List
; usage: (remove-first x l) = l without the first occurrence of x.
(define (remove-first x l)
  (cond
    [(null? l) l]
    [(equal? x (car l)) (cdr l)]
    [else (cons (car l) (remove-first x (cdr l)))]))

; remove : SchemeVal * List -> List
; usage: (remove x l) = l without the occurrences of x.
(define (remove x l)
  (cond
    [(null? l) l]
    [(equal? x (car l)) (remove x (cdr l))]
    [else (cons (car l) (remove x (cdr l)))]))

; occurs-free? : Sym * LcExp -> Bool
; usage: returns #t if the symbol var occurs free in exp. Otherwise
;        returns #f.
(define (occurs-free? x e)
  (cond
    [(symbol? e) (eqv? x e)]
    [(eqv? (car e) 'lambda)
     (and (not (equal? (caadr e) x)) (occurs-free? x (caddr e)))]
    [else (or (occurs-free? x (car e)) (occurs-free? x (cadr e)))]))

; subst : Sym * Sym * S-list -> S-list
(define (subst new old l)
  (cond
    [(null? l) l]
    [else (cons (subst-in-sexp new old (car l)) (subst new old (cdr l)))]))

(define (subst-in-sexp new old e)
  (cond
    [(symbol? e) (if (eqv? old e) new e)]
    [else (subst new old e)]))

; Exercise 1.12
; subst-inline : Sym * Sym * S-list -> S-list
(define (subst-inline new old l)
  (cond
    [(null? l) l]
    [(symbol? l) (if (eqv? old l) new l)]
    [else (cons
           (subst-inline new old (car l))
           (subst-inline new old (cdr l)))]))

; Exercise 1.13
(define (subst-map new old l)
  (cond
    [(symbol? l) (if (eqv? old l) new l)]
    [else (map (lambda (e) (subst-in-sexp new old e)) l)]))

(define (subst-in-sexp-map new old l)
  (cond
    [(symbol? l) (if (eqv? old l) new l)]
    [else (subst-map new old l)]))

(define (number-elements-from n l)
  (cond
    [(null? l) '()]
    [else (cons (list n (car l)) (number-elements-from (+ n 1) (cdr l)))]))

(define (number-elements l)
  (number-elements-from 0 l))

(define (list-sum l)
  (cond
    [(null? l) 0]
    [else (+ (car l) (list-sum (cdr l)))]))

(define (partial-vector-sum n v)
  (cond
    [(= 0 n) (vector-ref v 0)]
    [else (+ (vector-ref v n) (partial-vector-sum (- n 1) v))]))

(define (vector-sum v)
  (cond
    [(= 0 (vector-length v)) 0]
    [else (partial-vector-sum (- (vector-length v) 1) v)]))

; Exercise 1.15
(define (duple n x)
  (cond
    [(= n 0) '()]
    [else (cons x (duple (- n 1) x))]))

; Exercise 1.16
(define (invert l)
  (map (lambda (p) (reverse p)) l))

; Exercise 1.17
(define (down l)
  (map (lambda (x) (cons x '())) l))

; Exercise 1.18
(define (swapper a b l)
  (define (swap a b x)
    (cond
      [(eqv? a x) b]
      [(eqv? b x) a]
      [else x]))
  (cond
    [(symbol? l) (swap a b l)]
    [else (map (lambda (x) (swapper a b x)) l)]))

; Exercise 1.19
(define (list-set l n x)
  (define (index-error)
    (eopl:error 'list-set "List ~s doesn't have ~s elements.\n"
                l (+ n 1)))
  (define (aux l n x)
    (cond
      [(< n 0) l]
      [(null? l) (index-error)]
      [(<= n 0) (cons x (cdr l))]
      [else (cons (car l) (aux (cdr l) (- n 1) x))]))
  (aux l n x))

; Exercise 1.20
(define (count-occurrences s l)
  (cond
    [(symbol? l) (if (eqv? s l) 1 0)]
    [(null? l) 0]
    [else (+
           (count-occurrences s (car l))
           (count-occurrences s (cdr l)))]))

; Exercise 1.21
(define (bind l f)
  (cond
    [(null? l) '()]
    [else (append (f (car l)) (bind (cdr l) f))]))

(define (product l1 l2)
  (bind l1 (lambda (x)
          (bind l2 (lambda (y) (list (list x y)))))))

; Exercise 1.22
(define (filter-in f l)
  (cond
    [(null? l) '()]
    [else (if (f (car l))
              (cons (car l) (filter-in f (cdr l)))
              (filter-in f (cdr l)))]))

; Exercise 1.23
(define (list-index f l)
  (cond
    [(null? l) #f]
    [else (let ([n (list-index f (cdr l))])
            (cond
              [(f (car l)) 0]
              [else (if n (+ n 1) #f)]))]))

; Exercise 1.24
(define (every? f l)
  (cond
    [(null? l) #t]
    [else (and (f (car l)) (every? f (cdr l)))]))

; Exercise 1.25
(define (exists? f l)
  (cond
    [(null? l) #f]
    [else (or (f (car l)) (exists? f (cdr l)))]))

; Exercise 1.26
(define (up l)
  (cond
    [(null? l) '()]
    [(list? (car l)) (append (car l) (up (cdr l)))]
    [else (append (list (car l)) (up (cdr l)))]))

; Exercise 1.27
(define (flatten l)
  (cond
    [(null? l) l]
    [(symbol? l) (list l)]
    [else (append (flatten (car l)) (flatten (cdr l)))]))

; Exercise 1.28
(define (merge l1 l2)
  (cond
    [(null? l1) l2]
    [(null? l2) l1]
    [else (if (<= (car l1) (car l2))
              (cons (car l1) (merge (cdr l1) l2))
              (cons (car l2) (merge l1 (cdr l2))))]))

; Exercise 1.29
(define (ins x l)
  (cond
    [(null? l) (list x)]
    [else (if (<= x (car l)) (cons x l) (cons (car l) (ins x (cdr l))))]))

(define (sort l)
  (cond
    [(null? l) '()]
    [else (ins (car l) (sort (cdr l)))]))

; Exercise 1.30
(define (sort/predicate cmp l)
  (define (ins x l)
    (cond
      [(null? l) (list x)]
      [else (if (cmp x (car l))
                (cons x l)
                (cons (car l) (ins x (cdr l))))]))
  (cond
    [(null? l) '()]
    [else (ins (car l) (sort/predicate cmp (cdr l)))]))

; Exercise 1.31
(define (leaf x) x)

(define (interior-node v l r) (list v l r))

(define (leaf? t) (or (not (list? t)) (not (= 3 (length t)))))

(define (lson t)
  (define (lson-error)
    (eopl:error "Leaf has no left son."))
  (cond
    [(leaf? t) (lson-error)]
    [else (cadr t)]))

(define (rson t)
  (define (rson-error)
    (eopl:error "Leaf has no right son."))
  (cond
    [(leaf? t) (rson-error)]
    [else (caddr t)]))

(define (contents-of t)
  (cond
    [(leaf? t) t]
    [else (car t)]))

; Exercise 1.32
(define (double-tree t)
  (cond
    [(leaf? t) (* 2 t)]
    [(integer? (contents-of t))
     (interior-node
      (* 2 (contents-of t))
      (double-tree (lson t))
      (double-tree (rson t)))]
    [else (interior-node
           (contents-of t)
           (double-tree (lson t))
           (double-tree (rson t)))]))

; Exercise 1.33
(define (mark-leaves-with-red-depth t)
  (define (aux n t)
    (cond
      [(leaf? t) n]
      [else (if (eqv? 'red (contents-of t))
                (interior-node
                 (contents-of t)
                 (aux (+ n 1) (lson t))
                 (aux (+ n 1) (rson t)))
                (interior-node
                 (contents-of t)
                 (aux n (lson t))
                 (aux n (rson t))))]))
  (aux 0 t))

; Exercise 1.34
(define (path n t)
  (cond
    [(leaf? t) (if (and (integer? t) (= n t)) '() #f)]
    [else (let* ([l (path n (lson t))] [r (path n (rson t))])
            (cond
              [(= n (contents-of t)) '()]
              [l (cons 'left l)]
              [r (cons' right r)]
              [else #f]))]))

; Exercise 1.35
(define (number-leaves t)
  (define (aux n t)
    (cond
      [(leaf? t) (cons (leaf n) (+ n 1))]
      [else (letrec
                ([l (aux n (lson t))]
                 [r (aux (cdr l) (rson t))])
              (cons
               (interior-node (contents-of t) (car l) (car r))
               (cdr r)))]))
  (car (aux 0 t)))

; Exercise 1.36
(define (nl lst)
  (define (g a b)
    (if (eqv? b '()) 0 (+ 1 (g (car b) (cdr b)))))
  (if (null? lst) '()
      (g (list 0 (car lst)) (nl (cdr lst)))))