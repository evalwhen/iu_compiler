(let ([y (let ([x 20])
           (+ x (let ([x 22]) x)))])
  y)

;; (CProgram
;;  '((locals-types
;;     (g12997 . Integer)
;;     (g13000 . Integer)
;;     (g12999 . Integer)
;;     (g12998 . Integer)))
;;  (list
;;   (cons
;;    'start
;;    (Seq
;;     (Assign (Var 'g12998) (Int 20))
;;     (Seq
;;      (Assign (Var 'g12999) (Int 22))
;;      (Seq
;;       (Assign (Var 'g13000) (Var 'g12999)) // TODO: remove this.
;;       (Seq
;;        (Assign (Var 'g12997) (Prim '+ (list (Var 'g13000) (Var 'g12998))))
;;        (Return (Var 'g12997)))))))))
