(declare-fun G (Int Int Int Int) Bool)
(declare-fun Dual_Mult (Int Int Int) Bool)
(declare-fun Mult (Int Int Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int) (y Int) (s1 Int) (s2 Int))
  (G x y s1 s2)))

(assert (forall ((x Int) (y Int) (s1 Int) (s2 Int))
  (= (G x y s1 s2)
    (or (Dual_Mult x y s1) (Dual_Mult x y s2) (= s1 s2)))))

(assert (and nu (forall ((x Int) (y Int) (r Int))
  (= (Dual_Mult x y r) (and
    (or (not (= y 0)) (not (= r 0)))
    (or (= y 0) (Dual_Mult x (- y 1) (- r x))))))))

(assert (and mu (forall ((x Int) (y Int) (r Int))
  (= (Mult x y r) (or
    (and (= y 0) (= r 0))
    (and (not (= y 0)) (Mult x (- y 1) (- r x))))))))

(check-sat)

