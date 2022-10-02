(let ([x (+ 42 (- 10))])
  (+ x 10))

;; (Program
;;  '()
;;  (Let
;;   'g12956
;;   (Let
;;    'g12957
;;    (Prim '- (list (Int 10)))
;;    (Prim '+ (list (Int 42) (Var 'g12957))))
;;   (Prim '+ (list (Var 'g12956) (Int 10)))))
