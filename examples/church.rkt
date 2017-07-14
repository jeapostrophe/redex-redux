#lang racket/base
(require redex-redux)

;; xxx pict rendering api (lots of customization)
;; xxx syntax properties for coloring in DrR

;; xxx angle brackets for default tuple form?

;; xxx reflect each thing into a well-known racket type

;; xxx need #lang for demos

;; `redex` is like a single figure in a paper
(redex lang
 rtg
 x ::= identifier

 rtg
 n ::= number
 
 rtg
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
 ;; we can say that one rtg is a subset of another (for dealing with non-overlap)
 rtg
 v ⊆ e ::= (λ (x) e)
           n

 rtg
 E ::= hole
       (E e)
       (v E)
       (+ E e)
       (+ v E))

;; redex values are opaque, so we need to eject/inject them for racket
;; interop
(define plus
  (redex-lambda
   #:with domains
   (n_x n_y -> n)
   (+ n_x n_y)))
;; expands to
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
 ;; comma is NOT in the scope of the redex system and returns a term
 ;; or a function when to the right of (
 (in-hole E (,plus n_lhs n_rhs))
 ;; xxx do we need to know type?

 fun subst : x e -> e
 (subst x_1 e_x (λ (x_1) e_1)) = (λ (x_1) e_1)
 (subst x_1 e_x (λ (x_2) e_1)) = (λ (x_2) (subst x_1 e_x e_1))
 (subst x_1 e_x (e_1 e_2)) = ((subst x_1 e_x e_1) (subst x_1 e_x e_2))
 (subst x_1 e_x (+ e_1 e_2)) = (+ (subst x_1 e_x e_1) (subst x_1 e_x e_2))
 (subst x_1 e_x n) = n
 (subst x_1 e_x x_1) = e_x
 (subst x_1 e_x x_2) = x_2

 rel* e -->* e #:of e --> e
 ;; expands to
 rel e RTC--> e #:is (I O)

 e RTC--> e                 ;; NOTE look at newline!
 
 e_0 --> e_1
 e_1 RTC--> e_2
 --------------- [trans]    ;; NOTE any number of - more than 2? (newline!)
 e_0 RTC--> e_2
 ;; </rel*>

 relnf eval #:of e --> e)

(redex sem-ex
 ;; NOTE we extend two things! (sometimes that's not possible)
 #:extends (semantics lang-ex)
 fun let : (x e) e -> e
 (let (x e_arg) e_body) = ((λ (x) e_body) e_arg)

 facts
 (to-nat (let (x (succ one)) ((plus x) x))) -->* 2
 (eval (to-nat ((plus (succ one)) two))) = 4

 pred-succ :=
  ∀ n ->
   (eval (to-nat (+ (+ n 1) -1))) = n)

(redex-check #:with sem-ex
             pred-succ
             #:attempts 1000)

(redex tylang
 rtg
 x ::= identifier

 rtg
 n ::= number
 
 rtg
 e ::= (λ (x : T) e)
       (e e)
       (+ e e)
       n
       x
       #:bindings
       (λ (x) e #:refers-to x)

 rtg
 T ::= num
       (T -> T))

(redex static #:extends tylang
 ;; map defines an efficient map
 map Γ : x -> T

 rel Γ ⊢ e : T #:is (I I O)

 (Γ x T_arg) ⊢ e : T_body
 -----------------------------------------
 Γ ⊢ (λ (x : T_arg) e) : (T_arg -> T_body)

 Γ ⊢ e_fun : (T_arg -> T_body)
 Γ ⊢ e_arg : T_arg
 --------------------------
 Γ ⊢ (e_fun e_arg) : T_body

 Γ ⊢ e_lhs : num
 Γ ⊢ e_rhs : num
 -------------------------
 Γ ⊢ (+ e_lhs e_rhs) : num

 Γ ⊢ n : num

 Γ ⊢ x : (Γ x))

;; xxx typed examples
(redex ty-exs #:extends static)

(define ty-plus
  (redex-lambda
   #:with static
   (n_x n_y -> n)
   (+ n_x n_y)))

(redex ty-runtime #:extends static
 rtg
 v ⊆ e ::= (λ (x : T) e)
           n
       
 rtg
 E ::= hole
       (E e)
       (v E)
       (+ E e)
       (+ v E)

 rel e --> e #:is (I O)
 (in-hole E ((λ (x : T) e_body) e_arg)) -->
 (in-hole E (substitute x e_arg e_body))

 (in-hole E (+ n_lhs n_rhs)) -->
 (in-hole E (,ty-plus n_lhs n_rhs))

 rel* e -->* e #:of e --> e
 relnf eval #:of e --> e
 )

(redex soundness #:extends ty-runtime
 facts
 progress :=
 ∀ e_0 -> T -> e_1 ->
   (Γ) ⊢ e_0 : T ->
   (or (v = e_0)
       (∃ e_1 e_0 --> e_1))
       
 preservation :=
  ∀ e_0 -> T -> e_1 ->
    (Γ) ⊢ e_0 : T ->
    e_0 --> e_1 ->
    (Γ) ⊢ e_1 : T)
