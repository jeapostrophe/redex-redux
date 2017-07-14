#lang at-exp racket/base
(require redex-redux)

(redex lang
 set
 x ::= identifier

 set
 n ::= number
 
 set
 e ::= (λ (x) e)
       (e e)
       (+ e e)
       n
       x
       #:bindings
       (λ (x) e #:refers-to x))

(redex lang-ex #:extends lang
 terms : e
 zero := (λ (s) (λ (z) z))
 one := (λ (s) (λ (z) (s z)))
 two := (λ (s) (λ (z) (s (s z))))
 succ := (λ (n) (λ (s) (λ (z) (s ((n s) z)))))
 plus := (λ (m) (λ (n) (λ (s) (λ (z) ((m s) ((n s) z))))))

 to-nat := (λ (cn) ((cn (λ (n) (+ 1 n))) 0)))

(redex domains #:extends lang
 set : e                       ;; xxx could use ⊆ but long to type
 v ::= (λ (x) e)
       n
       
 set
 E ::= hole
       (E e)
       (v E)
       (+ E e)
       (+ v E))

(define plus
  (redex-lambda
   (n_x n_y -> n)
   (+ n_x n_y)))
;; xxx expands to
(define (raw-plus xt yt)
  (with-redex domains
    (redex-define n_x xt)
    (redex-define n_y yt)
    (redex-parse n (+ n_x n_y))))

(redex semantics #:extends domains
 rel e --> e #:is (I O)

 (in-hole E ((λ (x) e_body) e_arg)) -->
 (in-hole E (subst x e_arg e_body))

 (in-hole E (+ n_lhs n_rhs)) -->
 (in-hole E (,plus n_lhs n_rhs))          ;; xxx do we need to know type?

 fun subst : x e -> e
 (subst x_1 e_x (λ (x_1) e_1)) = (λ (x_1) e_1)
 (subst x_1 e_x (λ (x_2) e_1)) = (λ (x_2) (subst x_1 e_x e_1))
 (subst x_1 e_x (e_1 e_2)) = ((subst x_1 e_x e_1) (subst x_1 e_x e_2))
 (subst x_1 e_x (+ e_1 e_2)) = (+ (subst x_1 e_x e_1) (subst x_1 e_x e_2))
 (subst x_1 e_x n) = n
 (subst x_1 e_x x_1) = e_x
 (subst x_1 e_x x_2) = x_2

 rel* e -->* e #:is e --> e
 ;; xxx expands to
 rel e RTC--> e #:is (I O)

 e RTC--> e                 ;; xxx look at newline!
 
 e_0 --> e_1
 e_1 RTC--> e_2
 --------------- [trans]    ;; xxx any number of - more than 2? (newline!)
 e_0 RTC--> e_2
 ;; </rel*>
 
 fun eval : e -> e
 (eval e_0) = e_n
 #:where e_0 -->* e_n)

(redex sem-ex
 ;; xxx we extend two things! (sometimes that's not possible)
 #:extends semantics #:extends lang-ex
 fun let : (x e) e -> e
 (let (x e_arg) e_body) = ((λ (x) e_body) e_arg)

 facts
 (to-nat (let (x (succ one)) ((plus x) x))) -->* 2
 (eval (to-nat ((plus (succ one)) two))) = 4

 pred-succ :=
  forall n
   (to-nat (+ (+ n 1) -1)) = n)

(redex-check #:with sem-ex
             pred-succ
             #:attempts 1000)

(traces #:with sem-ex
        ((plus (succ one)) (succ (succ zero))))

;; xxx add types
