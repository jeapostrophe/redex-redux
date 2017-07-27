#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     ;; xxx
                     racket/pretty)
         racket/stxparam)

(begin-for-syntax
  (struct static-redex-block-data (deps) #:prefab)

  (define (initial-static-redex-block-data deps)
    (static-redex-block-data deps))

  (define-syntax-class redex-block
    #:attributes (value)
    (pattern x
             #:declare x (static static-redex-block-data? "redex block")
             #:attr value (attribute x.value)))
  (define-syntax-class redex-set
    ;; xxx
    (pattern x:id))

  (define-splicing-syntax-class redex-extends
    #:no-delimit-cut
    #:attributes (deps)
    (pattern (~seq #:extends ~! x:redex-block ...)
             #:attr deps (attribute x.value))))

(begin-for-syntax
  (struct redex-form-handler (id do)
    #:property prop:procedure
    (λ (rfh stx)
      (define csrd (syntax-parameter-value #'current-static-redex-block))
      (if csrd
        ((redex-form-handler-do rfh) csrd stx)
        (raise-syntax-error (redex-form-handler-id rfh)
                            "illegal outside redex"
                            stx))))
  (define-syntax-class redex-form
    #:attributes (value)
    (pattern x
             #:declare x (static redex-form-handler? "redex form")
             #:attr value (attribute x.value))))

(define-syntax-parameter current-static-redex-block #f)
(define-syntax (redex stx)
  (syntax-parse stx
    [(_ x:id
        (~optional e:redex-extends
                   #:defaults ([e.deps (list)]))
        . body)
     (define (recur a-body)
       (syntax-parse a-body
         [() '()]
         [(rf:redex-form (~and rf-arg (~not _:redex-form)) ... . more-body)
          ;; xxx give it access to the next thing?
          (cons (syntax/loc a-body (rf rf-arg ...))
                (recur #'more-body))]))
     (quasisyntax/loc stx
       (begin
         (define-syntax x #,(initial-static-redex-block-data (attribute e.deps)))
         (let ()
           (syntax-parameterize ([current-static-redex-block #'x])
             #,@(recur #'body)))))]))

(begin-for-syntax
  (define-syntax-class redex-subset-sym
    (pattern (~literal :))
    (pattern (~literal ⊆))))

(define-syntax (define-redex-form stx)
  (syntax-parse stx
    [(_ x:id f:expr)
     (syntax/loc stx (define-syntax x (redex-form-handler 'x f)))]
    [(_ (x:id tr:id st:id) body ...+)
     (syntax/loc stx
       (define-redex-form x (λ (tr st) body ...)))]))

(define-redex-form (regular-tree-grammar the-rbd stx)
  (syntax-parse stx
    [(_ lhs:id (~optional (~seq _:redex-subset-sym parent:id))
        (~literal ::=)
        rhs:expr ...
        (~optional (~seq #:bindings binds:expr ...)))
     (pretty-print (vector 'XXX-rtg #'lhs (attribute parent) #'(rhs ...)
                           (attribute binds)))
     #''XXX]))

(define-syntax-rule (define-pattern-keyword kw)
  (define-syntax (kw stx) (raise-syntax-error 'kw "Illegal outside redex" stx)))
(define-syntax-rule (define-pattern-keywords kw ...)
  (begin (define-pattern-keyword kw) ...
         (provide kw ...)))
(define-pattern-keywords identifier number hole in-hole)

(define-redex-form (term the-rbd stx)
  (syntax-parse stx
    [(_ x:id _:redex-subset-sym s:id (~literal :=) e:expr)
     (pretty-print (vector 'XXX-term #'x #'s #'e))
     #''XXX]))

(define-redex-form (terms rbd stx)
  (syntax-parse stx
    [(_ _:redex-subset-sym s:id
        (~seq (~and x:id (~not _:redex-form)) (~literal :=) e:expr) ...)
     (syntax/loc stx
       (begin (term x : s := e) ...))]))

(begin-for-syntax
  (define-syntax-class relation-mode
    (pattern (~datum I))
    (pattern (~datum O))))
(define-redex-form (relation rbd stx)
  (syntax-parse stx
    [(_ (~and in (~not #:is)) ... #:is (m:relation-mode ...)
        . rel-body)
     (pretty-print (vector 'XXX-rel #'(in ...) #'(m ...) #'rel-body))
     #''XXX]))

(define-redex-form (function rbd stx)
  (syntax-parse stx))
;; XXX

(define-redex-form (define-map rbd stx)
  (syntax-parse stx))
;; XXX

(define-redex-form (fact rbd stx)
  (syntax-parse stx))
;; XXX

(define-redex-form (facts rbd stx)
  (syntax-parse stx))
;; XXX

(define-redex-form (relation-reflexive-transitive-closure rbd stx)
  (syntax-parse stx))
;; XXX

(define-redex-form (relation-normal-form rbd stx)
  (syntax-parse stx))
;; XXX

(provide redex
         regular-tree-grammar
         (rename-out [regular-tree-grammar rtg]
                     [regular-tree-grammar grammar])
         terms
         term
         relation
         (rename-out [relation rel])
         function
         (rename-out [function metafunction]
                     [function fun])
         define-map
         (rename-out [define-map defmap])
         fact
         facts
         relation-reflexive-transitive-closure
         (rename-out [relation-reflexive-transitive-closure rel*])
         relation-normal-form
         (rename-out [relation-normal-form relnf]))

(define-syntax (with-redex stx)
  #''XXX)
(define-syntax (redex-define stx)
  #''XXX)
(define-syntax (redex-parse stx)
  #''XXX)

(define-syntax (redex-lambda stx)
  (syntax-parse stx
    #:datum-literals (->)
    [(_ #:with l:redex-block
        (i:redex-set ... -> o:redex-set)
        body ...+)
     (with-syntax ([(it ...) (generate-temporaries #'(i ...))])
       (syntax/loc stx
         (lambda (it ...)
           (with-redex l
             (redex-define i it) ...
             (define v
               (let () body ...))
             (redex-parse o v)))))]))

(provide redex-lambda
         with-redex
         redex-define
         redex-parse)

(define-syntax (redex-check stx)
  #''XXX)
(provide redex-check)
