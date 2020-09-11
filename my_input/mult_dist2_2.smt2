(declare-fun G (Int Int Int Int Int Int) Bool)
(declare-fun Dual_Mult (Int Int Int) Bool)
(declare-fun Mult (Int Int Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int) (y Int) (z Int) (r Int) (r1 Int) (r2 Int))
  (G x y z r r1 r2)))

(assert (forall ((x Int) (y Int) (z Int) (r Int) (r1 Int) (r2 Int))
  (= (G x y z r r1 r2)
    (or (Dual_Mult (+ x y) z r) (Dual_Mult z x r1) (Dual_Mult z y r2) (= (+ r1 r2) r)))))

(assert (and nu (forall ((x Int) (y Int) (r Int))
  (= (Dual_Mult x y r) (and
    (or (not (= y 0)) (not (= r 0)))
    (or (= y 0) (Dual_Mult x (- y 1) (- r x))))))))

(assert (and mu (forall ((x Int) (y Int) (r Int))
  (= (Mult x y r) (or
    (and (= y 0) (= r 0))
    (and (not (= y 0)) (Mult x (- y 1) (- r x))))))))



