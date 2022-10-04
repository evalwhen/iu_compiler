#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (cond
         [(assoc x env) => (lambda (v) (Var (cdr v)))]
         [else (error "unkown var name")])]
      [(Int n) (Int n)]
      [(Let x e body)
       (let* ([newx (gensym)]
              [newenv (cons (cons x newx) env)])
         (println newenv)
         (Let newx ((uniquify-exp env) e) ((uniquify-exp newenv) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    ;; [(Program info e) (Program info (rco_exp2 e (lambda (x) x)))]
    [(Program info e) (Program info (rco_exp2 e))]
    ))

(define (atom? e)
  (match e
    [(Var _) true]
    [(Int _) true]
    [else false]))

(define (complex? e)
  (not (atom? e)))

(define (rco_atom e ctx)
  (match e
    [(Prim op (list (? atom? e1) (? atom? e2)))
     (ctx e)]
    [(Prim op (list (? complex? e1) (? atom? e2)))
     (rco_exp e1 (lambda (ee1)
                   (let ([n (gensym)])
                     (ctx (Let n ee1 (Prim op (list (Var n) e2)))))))]
    [(Prim op (list (? atom? e1) (? complex? e2)))
     (rco_exp e2 (lambda (ee2)
                   (let ([n (gensym)])
                     (ctx (Let n ee2 (Prim op (list e1 (Var n))))))))]
    [(Prim op (list (? complex? e1) (? complex? e2)))
     (rco_exp e1 (lambda (ee1)
                   (rco_exp e2 (lambda (ee2)
                                 (let ([n1 (gensym)]
                                       [n2 (gensym)])
                                   (ctx (Let n1 ee1 (Let n2 ee2 (Prim op (list (Var n1) (Var n2)))))))))))]
    [(Prim op (list (? atom? e1)))
     (ctx e)]
    [(Prim op (list (? complex? e1)))
     (rco_exp e1 (lambda (ee1)
                  (let ([n1 (gensym)])
                    (ctx (Let n1 ee1 (Prim op (list (Var n1))))))))]
    [else (error "unkown exp")]))

(define (rco_exp e ctx)
  (match e
      [(Var x)
       (ctx e)]
      [(Int n) (ctx e)]
      [(Let x ep body)
       (rco_exp ep (lambda (e1)
                     (rco_exp body (lambda (e2)
                                     (ctx (Let x e1 e2))))))]
      [(Prim _ _)
       (rco_atom e ctx)]))

(define (rco_atom2 e)
  (let ([n (gensym)])
    (values n (list (cons n (rco_exp2 e))))))

(define (rco_exp2 e)
  (match e
      [(Var x) e]
      [(Int n) e]
      [(Let x ep body)
       (Let x (rco_exp2 ep) (rco_exp2 body))]
      [(Prim op es)
       (let-values ([(args envs) (for/fold ([args '()]
                                            [newenv '()])
                                           ([e es])
                                   (if (complex? e)
                                       (let-values ([(var en) (rco_atom2 e)])
                                         (values (cons (Var var) args)
                                                 (append en newenv)))
                                       (values (cons e args)
                                               newenv)))])
         (println envs)
         (build_lets envs (Prim op args)))]))

(define (build_lets envs body)
  (if (null? envs)
      body
      (Let (car (car envs))
           (cdr (car envs))
           (build_lets (cdr envs) body))))

(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e sym cont)
  (match e
    [(Var x) (Seq (Assign (Var sym) (Var x)) cont)]
    [(Int n) (Seq (Assign (Var sym) (Int n)) cont)]
    [(Let y rhs (? Var? _)) (explicate_assign rhs sym cont)];; optimize: the body of Let is a variable
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body sym cont))]
    [(Prim _ _) (Seq (Assign (Var sym) e) cont)]
    [else (error "explicate_assign unhandled case" e)]))

(define (explicate-control p)
  (match p
    [(Program info body) (CProgram '()  (list (cons 'start (explicate_tail body))))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
