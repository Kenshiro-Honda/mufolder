(declare-fun G (Int Int Int Int) Bool)
(declare-fun Dplus (Int Int Int) Bool)
(declare-fun Plus (Int Int Int) Bool)
(declare-fun mu () Bool)
(declare-fun nu () Bool)

(assert (forall ((x Int) (y Int) (z Int) (r Int)) (G x y z r)))

(assert (forall ((x Int) (y Int) (z Int) (r Int))
  (= (G x y z r) (or
    (Dplus (+ x y) z r)
    (exists ((s Int)) (Plus x z s))))))

(assert (and nu (forall ((x Int) (y Int) (r Int))
  (= (Dplus x y r) (and
    (or (not (= y 0)) (not (= r x)))
    (or (= y 0) (Dplus x (- y 1) (- r 1))))))))

(assert (and mu (forall ((x Int) (y Int) (r Int))
  (= (Plus x y r) (or
    (and (= y 0) (= r x))
    (and (not (= y 0)) (Plus x (- y 1) (- r 1))))))))

(check-sat)
