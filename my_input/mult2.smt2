(declare-fun G (Int Int Int Int) Bool)
(declare-fun Dual_Mult (Int Int Int) Bool)
(declare-fun Mult (Int Int Int) Bool)
(declare-fun Dual_Mult2 (Int Int Int) Bool)
(declare-fun Mult2 (Int Int Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((a Int) (b Int) (c Int) (r Int))
  (G a b c r)))

(assert (forall ((a Int) (b Int) (c Int) (r Int))
  (= (G a b c r)
    (or 
      (Dual_Mult2 a b r)
      (Mult a b r)))))

(assert (and nu (forall ((x Int) (y Int) (r Int))
  (= (Dual_Mult x y r) (and
    (or (not (= y 0)) (not (= r 0)))
    (or (= y 0) (Dual_Mult x (- y 1) (- r x))))))))

(assert (and nu (forall ((x Int) (y Int) (r Int))
  (= (Dual_Mult2 x y r) (and
    (or (not (= y 0)) (not (= r 0)))
    (or (= y 0) (Dual_Mult2 x (- y 2) (- r (* 2 x)))))))))

(assert (and mu (forall ((x Int) (y Int) (r Int))
  (= (Mult x y r) (or
    (and (= y 0) (= r 0))
    (and (not (= y 0)) (Mult x (- y 1) (- r x))))))))


