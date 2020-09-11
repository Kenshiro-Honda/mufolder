(declare-fun G (Int Int Int Int) Bool)
(declare-fun Dual_Mult (Int Int Int) Bool)
(declare-fun Mult (Int Int Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int) (y Int) (z Int) (r Int))
  (G x y z r)))

(assert (forall ((x Int) (y Int) (z Int) (r Int))
  (= (G x y z r)
    (or 
      (Dual_Mult x (+ y z) r) 
      (exists ((s Int)) 
        (and 
          (Mult x y s)
          (Mult x z (- r s))))))))

(assert (and nu (forall ((x Int) (y Int) (r Int))
  (= (Dual_Mult x y r) (and
    (or (not (= y 0)) (not (= r 0)))
    (or (= y 0) (Dual_Mult x (- y 1) (- r x))))))))

(assert (and mu (forall ((x Int) (y Int) (r Int))
  (= (Mult x y r) (or
    (and (= y 0) (= r 0))
    (and (not (= y 0)) (Mult x (- y 1) (- r x))))))))



