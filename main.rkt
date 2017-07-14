#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     ;; xxx
                     racket/pretty))

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
    (pattern (~seq #:extends ~! x:redex-block)
             #:attr deps (list (attribute x.value)))
    (pattern (~seq #:extends ~! (x:redex-block ...))
             #:attr deps (attribute x.value))))

(define-syntax (redex stx)
  (syntax-parse stx
    [(_ x:id
        (~optional e:redex-extends
                   #:defaults ([e.deps (list)]))
        . body)
     (parameterize ([current-syntax-context stx])
       (do-redex #'x
                 (initial-static-redex-block-data (attribute e.deps))
                 #'body))]))
(begin-for-syntax
  (struct redex-form-handler (id do)
    #:property prop:procedure
    (λ (rfh . _)
      (raise-syntax-error (redex-form-handler-id rfh)
                          "illegal outside redex")))
  (define-syntax-class redex-form
    #:attributes (value)
    (pattern x
             #:declare x (static redex-form-handler? "redex form")
             #:attr value (attribute x.value)))
  (define (do-redex final-id the-rbd body)
    (syntax-parse body
      [(rf:redex-form . _)
       ((redex-form-handler-do (attribute rf.value))
        do-redex final-id the-rbd body)]
      [()
       (quasisyntax/loc (current-syntax-context)
         (define-syntax #,final-id #,the-rbd))])))

(begin-for-syntax
  (define-syntax-class redex-subset-sym
    (pattern (~literal :))
    (pattern (~literal ⊆))))

(define-syntax (define-redex-form stx)
  (syntax-parse stx
    [(_ x:id f:expr)
     (syntax/loc stx (define-syntax x (redex-form-handler 'x f)))]
    [(_ (x:id dr:id fi:id tr:id b:id) body ...+)
     (syntax/loc stx
       (define-redex-form x (λ (dr fi tr b) body ...)))]))

(define-redex-form (regular-tree-grammar do-redex final-id the-rbd body)
  (syntax-parse body
    [(_ lhs:id (~optional (~seq _:redex-subset-sym parent:id))
        (~literal ::=)
        (~and rhs:expr (~not _:redex-form)) ...
        (~optional (~seq #:bindings
                         (~and binds:expr (~not _:redex-form)) ...))
        . rest-body)
     (pretty-print (vector 'XXX-rtg #'lhs (attribute parent) #'(rhs ...)
                           (attribute binds)))
     (do-redex final-id the-rbd #'rest-body)]))

(define-syntax-rule (define-pattern-keyword kw)
  (define-syntax (kw stx) (raise-syntax-error 'kw "Illegal outside redex" stx)))
(define-syntax-rule (define-pattern-keywords kw ...)
  (begin (define-pattern-keyword kw) ...
         (provide kw ...)))
(define-pattern-keywords identifier number hole in-hole)

(define-redex-form (term do-redex final-id the-rbd body)
  (syntax-parse body
    [(_ x:id _:redex-subset-sym s:id (~literal :=) e:expr . rest-body)
     (pretty-print (vector 'XXX-term #'x #'s #'e))
     (do-redex final-id the-rbd #'rest-body)]))

(define-syntax (define-redex-form-macro stx)
  (syntax-parse stx
    [(_ x:id f:expr)
     (syntax/loc stx
       (define-redex-form (x do-redex final-id the-rbd body)
         (do-redex final-id the-rbd (f body))))]
    [(_ (x:id s:id) body ...+)
     (syntax/loc stx
       (define-redex-form-macro x (λ (s) body ...)))]))

(define-redex-form-macro (terms body)
  (syntax-parse body
    [(_ _:redex-subset-sym s:id
        (~seq (~and x:id (~not _:redex-form)) (~literal :=) e:expr) ... . rest-body)
     (local-require syntax/parse/experimental/template)
     (template
      ((?@ term x : s := e) ... . rest-body))]))

(provide redex
         regular-tree-grammar
         (rename-out [regular-tree-grammar rtg]
                     [regular-tree-grammar grammar])
         terms
         term)

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
